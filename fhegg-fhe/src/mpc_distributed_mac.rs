//! Split-custody authenticated-bit formation for the `FHTRI005` cut.
//!
//! `FHTRI004` samples each complete binary MAC key in one trusted process. Here
//! party `i` samples only `alpha_i`; the mathematical key is
//! `alpha = XOR_i alpha_i`, but this module deliberately has no reconstruction
//! function and secret custody is neither `Clone`, `Debug`, nor serializable.
//!
//! Cross terms are load-bearing. For `x = XOR_j x_j`, authentication requires
//!
//! `XOR_i gamma_i = alpha*x = XOR_(i,j) alpha_i*x_j`.
//!
//! A local `alpha_i*x_i` alone is therefore invalid. For every ordered pair
//! `i != j`, party `i` supplies chosen-message OT inputs `(r, r+alpha_i)` and
//! party `j` chooses with `x_j`. The sender adds `r`, the receiver adds the
//! selected output, and their XOR is exactly `alpha_i*x_j`. Every diagonal and
//! cross term is covered once before a party row can finalize.
//!
//! This is an executable protocol substrate, not yet the live PartyMPC source.
//! Production must put each [`MacKeyShareCustody`] in a separate process and
//! replace the test-only ideal transfer with malicious-secure PQ OT/VOLE (or
//! threshold-BFV product sharing). Public manifest/certificate/check wires are
//! strict and context-bound but unsigned; the live FHTRI formation transcript
//! must authenticate their roots. They do not prove an OT adapter was honest.

use std::collections::HashSet;
use std::fmt;

use rand::{CryptoRng, RngCore};
use sha2::{Digest, Sha512};

pub const DISTRIBUTED_MAC_LANES: usize = 2;
pub const MAX_DISTRIBUTED_MAC_PARTIES: u32 = 64;
pub const MAX_DISTRIBUTED_MAC_VALUES: u32 = 16 * 1024 * 1024;

const MANIFEST_MAGIC: &[u8; 8] = b"FHDMM005";
const CERTIFICATE_MAGIC: &[u8; 8] = b"FHDMC005";
const OT_BINDING_MAGIC: &[u8; 8] = b"FHDOT005";
const CHECK_SET_MAGIC: &[u8; 8] = b"FHDCK005";
const MANIFEST_DOMAIN: &[u8] = b"fhegg/party-mpc/distributed-mac/manifest/v5";
const KEY_COMMIT_DOMAIN: &[u8] = b"fhegg/party-mpc/distributed-mac/key-commit/v5";
const SETUP_DOMAIN: &[u8] = b"fhegg/party-mpc/distributed-mac/setup/v5";
const OT_DOMAIN: &[u8] = b"fhegg/party-mpc/distributed-mac/ot-batch/v5";
const OPENED_DOMAIN: &[u8] = b"fhegg/party-mpc/distributed-mac/opened/v5";
const CHALLENGE_DOMAIN: &[u8] = b"fhegg/party-mpc/distributed-mac/challenge/v5";
const CHECK_COMMIT_DOMAIN: &[u8] = b"fhegg/party-mpc/distributed-mac/check-commit/v5";
const CHECK_SET_DOMAIN: &[u8] = b"fhegg/party-mpc/distributed-mac/check-set/v5";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DistributedMacError {
    InvalidParameters(&'static str),
    AllocationCeiling,
    ArithmeticOverflow,
    NonCanonicalWire,
    TruncatedWire,
    ContextMismatch,
    InvalidParty { party: u32, parties: u32 },
    DuplicateParty(u32),
    MissingContribution { sender: u32, receiver: u32 },
    DuplicateContribution { sender: u32, receiver: u32 },
    ShapeMismatch,
    CommitmentMismatch { party: u32 },
    CheckRejected { lane: usize },
}

impl fmt::Display for DistributedMacError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "distributed MAC error: {self:?}")
    }
}
impl std::error::Error for DistributedMacError {}
pub type Result<T> = std::result::Result<T, DistributedMacError>;

#[derive(Clone, Copy, Default, PartialEq, Eq)]
struct Gf128(u128);
impl Gf128 {
    const ZERO: Self = Self(0);
    fn from_bit(bit: u8) -> Result<Self> {
        match bit {
            0 => Ok(Self::ZERO),
            1 => Ok(Self(1)),
            _ => Err(DistributedMacError::InvalidParameters("value is not a bit")),
        }
    }
    fn from_bytes(bytes: [u8; 16]) -> Self {
        Self(u128::from_be_bytes(bytes))
    }
    fn to_bytes(self) -> [u8; 16] {
        self.0.to_be_bytes()
    }
    fn add(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }
    fn mul(self, rhs: Self) -> Self {
        let (mut out, mut a, mut b) = (0u128, self.0, rhs.0);
        for _ in 0..128 {
            out ^= a & 0u128.wrapping_sub(b & 1);
            a = (a << 1) ^ (0x87 & 0u128.wrapping_sub(a >> 127));
            b >>= 1;
        }
        Self(out)
    }
    fn is_zero(self) -> bool {
        self.0 == 0
    }
}

#[derive(Clone, Copy, Default, PartialEq, Eq)]
struct MacTag([Gf128; DISTRIBUTED_MAC_LANES]);
impl MacTag {
    fn add_assign(&mut self, rhs: Self) {
        for lane in 0..DISTRIBUTED_MAC_LANES {
            self.0[lane] = self.0[lane].add(rhs.0[lane]);
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DistributedMacManifest {
    session: [u8; 32],
    candidate_manifest: [u8; 64],
    roster: Vec<[u8; 32]>,
    values: u32,
    digest: [u8; 64],
}

impl DistributedMacManifest {
    pub fn new(
        session: [u8; 32],
        candidate_manifest: [u8; 64],
        roster: Vec<[u8; 32]>,
        values: u32,
    ) -> Result<Self> {
        validate_manifest(session, candidate_manifest, &roster, values)?;
        let digest = manifest_digest(session, candidate_manifest, &roster, values);
        Ok(Self {
            session,
            candidate_manifest,
            roster,
            values,
            digest,
        })
    }
    pub fn digest(&self) -> [u8; 64] {
        self.digest
    }
    pub fn session(&self) -> [u8; 32] {
        self.session
    }
    pub fn candidate_manifest(&self) -> [u8; 64] {
        self.candidate_manifest
    }
    pub fn roster(&self) -> &[[u8; 32]] {
        &self.roster
    }
    pub fn parties(&self) -> u32 {
        self.roster.len() as u32
    }
    pub fn values(&self) -> u32 {
        self.values
    }

    pub fn to_canonical_bytes(&self) -> Result<Vec<u8>> {
        let len = 184usize
            .checked_add(
                self.roster
                    .len()
                    .checked_mul(32)
                    .ok_or(DistributedMacError::ArithmeticOverflow)?,
            )
            .ok_or(DistributedMacError::ArithmeticOverflow)?;
        let mut out = Vec::with_capacity(len);
        out.extend_from_slice(MANIFEST_MAGIC);
        put_u32(&mut out, usize_u32(len)?);
        out.extend_from_slice(&self.session);
        out.extend_from_slice(&self.candidate_manifest);
        put_u32(&mut out, self.values);
        put_u32(&mut out, self.parties());
        put_u32(&mut out, DISTRIBUTED_MAC_LANES as u32);
        for id in &self.roster {
            out.extend_from_slice(id);
        }
        out.extend_from_slice(&self.digest);
        debug_assert_eq!(out.len(), len);
        Ok(out)
    }

    pub fn from_canonical_bytes(bytes: &[u8]) -> Result<Self> {
        let mut c = Cursor::new(bytes);
        if c.take::<8>()? != *MANIFEST_MAGIC || c.u32()? as usize != bytes.len() {
            return Err(DistributedMacError::NonCanonicalWire);
        }
        let session = c.take()?;
        let candidate = c.take()?;
        let values = c.u32()?;
        let parties = c.u32()?;
        let lanes = c.u32()?;
        if !(2..=MAX_DISTRIBUTED_MAC_PARTIES).contains(&parties) || lanes != 2 {
            return Err(DistributedMacError::NonCanonicalWire);
        }
        let mut roster = Vec::with_capacity(parties as usize);
        for _ in 0..parties {
            roster.push(c.take()?);
        }
        let claimed = c.take()?;
        c.finish()?;
        let value = Self::new(session, candidate, roster, values)?;
        if value.digest != claimed || value.to_canonical_bytes()?.as_slice() != bytes {
            return Err(DistributedMacError::NonCanonicalWire);
        }
        Ok(value)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KeyContribution {
    manifest: [u8; 64],
    party: u32,
    commitment: [u8; 64],
}
impl KeyContribution {
    pub fn party(&self) -> u32 {
        self.party
    }
    pub fn commitment(&self) -> [u8; 64] {
        self.commitment
    }
}

/// Party-local secret key share. No API combines two of these values.
pub struct MacKeyShareCustody {
    manifest: [u8; 64],
    party: u32,
    alpha: [Gf128; 2],
    commitment: [u8; 64],
}
impl Drop for MacKeyShareCustody {
    fn drop(&mut self) {
        self.alpha.fill(Gf128::ZERO);
    }
}

pub fn generate_key_share<R: RngCore + CryptoRng>(
    manifest: &DistributedMacManifest,
    party: u32,
    rng: &mut R,
) -> Result<(KeyContribution, MacKeyShareCustody)> {
    valid_party(manifest, party)?;
    let alpha = std::array::from_fn(|_| random_nonzero(rng));
    let mut salt = [0u8; 32];
    rng.fill_bytes(&mut salt);
    if salt == [0; 32] {
        salt[0] = 1;
    }
    let commitment = key_commitment(manifest.digest, party, salt, alpha);
    Ok((
        KeyContribution {
            manifest: manifest.digest,
            party,
            commitment,
        },
        MacKeyShareCustody {
            manifest: manifest.digest,
            party,
            alpha,
            commitment,
        },
    ))
}

/// Unsigned public certificate fixing every roster-indexed key-share
/// commitment before pairwise multiplication. The live formation transcript
/// must authenticate its root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DistributedMacCertificate {
    manifest: DistributedMacManifest,
    commitments: Vec<[u8; 64]>,
    setup_root: [u8; 64],
}
impl DistributedMacCertificate {
    pub fn seal(
        manifest: DistributedMacManifest,
        contributions: Vec<KeyContribution>,
    ) -> Result<Self> {
        if contributions.len() != manifest.parties() as usize {
            return Err(DistributedMacError::ShapeMismatch);
        }
        let mut commitments = Vec::with_capacity(contributions.len());
        for (expected, c) in contributions.into_iter().enumerate() {
            if c.party != expected as u32 {
                return Err(DistributedMacError::DuplicateParty(c.party));
            }
            if c.manifest != manifest.digest {
                return Err(DistributedMacError::ContextMismatch);
            }
            commitments.push(c.commitment);
        }
        let setup_root = setup_digest(manifest.digest, &commitments);
        Ok(Self {
            manifest,
            commitments,
            setup_root,
        })
    }
    pub fn manifest(&self) -> &DistributedMacManifest {
        &self.manifest
    }
    pub fn setup_root(&self) -> [u8; 64] {
        self.setup_root
    }
    pub fn key_commitments(&self) -> &[[u8; 64]] {
        &self.commitments
    }
    fn validate_key(&self, key: &MacKeyShareCustody, party: u32) -> Result<()> {
        valid_party(&self.manifest, party)?;
        if key.party != party
            || key.manifest != self.manifest.digest
            || key.commitment != self.commitments[party as usize]
        {
            return Err(DistributedMacError::ContextMismatch);
        }
        Ok(())
    }
    pub fn to_canonical_bytes(&self) -> Result<Vec<u8>> {
        let manifest = self.manifest.to_canonical_bytes()?;
        let len = 84usize
            .checked_add(manifest.len())
            .and_then(|n| n.checked_add(self.commitments.len() * 64))
            .ok_or(DistributedMacError::ArithmeticOverflow)?;
        let mut out = Vec::with_capacity(len);
        out.extend_from_slice(CERTIFICATE_MAGIC);
        put_u32(&mut out, usize_u32(len)?);
        put_u32(&mut out, usize_u32(manifest.len())?);
        out.extend_from_slice(&manifest);
        put_u32(&mut out, self.manifest.parties());
        for commitment in &self.commitments {
            out.extend_from_slice(commitment);
        }
        out.extend_from_slice(&self.setup_root);
        Ok(out)
    }
    pub fn from_canonical_bytes(bytes: &[u8]) -> Result<Self> {
        let mut c = Cursor::new(bytes);
        if c.take::<8>()? != *CERTIFICATE_MAGIC || c.u32()? as usize != bytes.len() {
            return Err(DistributedMacError::NonCanonicalWire);
        }
        let mlen = c.u32()?;
        if mlen > 16 * 1024 {
            return Err(DistributedMacError::AllocationCeiling);
        }
        let manifest = DistributedMacManifest::from_canonical_bytes(c.bytes(mlen as usize)?)?;
        let count = c.u32()?;
        if count != manifest.parties() {
            return Err(DistributedMacError::NonCanonicalWire);
        }
        let mut commitments = Vec::with_capacity(count as usize);
        for _ in 0..count {
            commitments.push(c.take()?);
        }
        let claimed = c.take()?;
        c.finish()?;
        let setup_root = setup_digest(manifest.digest, &commitments);
        if setup_root != claimed {
            return Err(DistributedMacError::NonCanonicalWire);
        }
        let value = Self {
            manifest,
            commitments,
            setup_root,
        };
        if value.to_canonical_bytes()?.as_slice() != bytes {
            return Err(DistributedMacError::NonCanonicalWire);
        }
        Ok(value)
    }
}

pub struct PartyBitShares {
    setup_root: [u8; 64],
    party: u32,
    values: Vec<u8>,
}
impl PartyBitShares {
    pub fn new(
        certificate: &DistributedMacCertificate,
        party: u32,
        values: Vec<u8>,
    ) -> Result<Self> {
        valid_party(&certificate.manifest, party)?;
        if values.len() != certificate.manifest.values as usize || values.iter().any(|b| *b > 1) {
            return Err(DistributedMacError::ShapeMismatch);
        }
        Ok(Self {
            setup_root: certificate.setup_root,
            party,
            values,
        })
    }
    pub fn party(&self) -> u32 {
        self.party
    }
    pub fn receiver_choices(&self, sender: u32) -> Result<PairwiseOtReceiverChoices<'_>> {
        if sender == self.party {
            return Err(DistributedMacError::InvalidParameters(
                "OT endpoints must differ",
            ));
        }
        Ok(PairwiseOtReceiverChoices {
            setup_root: self.setup_root,
            sender,
            receiver: self.party,
            values: &self.values,
        })
    }
}

/// Sender-private OT inputs. It is consumed exactly once by
/// [`drive_sender`](Self::drive_sender), and is neither cloneable nor
/// serializable. The driver is part of the sender's isolated process: message
/// differences reveal this sender's one key share by design, so a deployment
/// must never multiplex several parties through one driver process.
pub struct PairwiseOtSenderBatch {
    setup_root: [u8; 64],
    sender: u32,
    receiver: u32,
    transfer_id: [u8; 64],
    messages: Vec<[[Gf128; 2]; 2]>,
}
impl PairwiseOtSenderBatch {
    pub fn setup_root(&self) -> [u8; 64] {
        self.setup_root
    }
    pub fn sender(&self) -> u32 {
        self.sender
    }
    pub fn receiver(&self) -> u32 {
        self.receiver
    }
    pub fn transfer_id(&self) -> [u8; 64] {
        self.transfer_id
    }
    pub fn transfers(&self) -> usize {
        self.messages.len() * 2
    }
    /// Consume this batch into a sender-endpoint OT driver. There is no
    /// receiver-choice parameter or receiver output on this side of the API.
    pub fn drive_sender<D: PairwiseOtSenderDriver>(
        self,
        driver: &mut D,
    ) -> std::result::Result<(), D::Error> {
        driver.begin(
            self.setup_root,
            self.sender,
            self.receiver,
            self.transfer_id,
            self.messages.len(),
        )?;
        let mut this = self;
        for (value, row) in this.messages.iter_mut().enumerate() {
            for (lane, pair) in row.iter_mut().enumerate() {
                driver.send_pair(value, lane, [pair[0].to_bytes(), pair[1].to_bytes()])?;
                *pair = [Gf128::ZERO; 2];
            }
        }
        driver.finish()
    }
}

impl Drop for PairwiseOtSenderBatch {
    fn drop(&mut self) {
        for row in &mut self.messages {
            for pair in row {
                *pair = [Gf128::ZERO; 2];
            }
        }
    }
}

/// Sender-process boundary for malicious-secure chosen-message OT. Implementors
/// receive both messages, as an OT sender must, but never receive choices or
/// selected outputs. One driver instance must belong to exactly one roster
/// party and authenticate the supplied context before sending.
pub trait PairwiseOtSenderDriver {
    type Error;

    fn begin(
        &mut self,
        setup_root: [u8; 64],
        sender: u32,
        receiver: u32,
        transfer_id: [u8; 64],
        values: usize,
    ) -> std::result::Result<(), Self::Error>;

    fn send_pair(
        &mut self,
        value: usize,
        lane: usize,
        messages: [[u8; 16]; 2],
    ) -> std::result::Result<(), Self::Error>;

    fn finish(&mut self) -> std::result::Result<(), Self::Error>;
}
pub struct PairwiseOtReceiverChoices<'a> {
    setup_root: [u8; 64],
    sender: u32,
    receiver: u32,
    values: &'a [u8],
}
impl PairwiseOtReceiverChoices<'_> {
    pub fn setup_root(&self) -> [u8; 64] {
        self.setup_root
    }
    pub fn sender(&self) -> u32 {
        self.sender
    }
    pub fn receiver(&self) -> u32 {
        self.receiver
    }
    pub fn len(&self) -> usize {
        self.values.len()
    }
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }
    pub fn choice(&self, index: usize) -> Result<u8> {
        self.values
            .get(index)
            .copied()
            .ok_or(DistributedMacError::ShapeMismatch)
    }
}

pub struct SenderMacContribution {
    setup_root: [u8; 64],
    sender: u32,
    receiver: u32,
    transfer_id: [u8; 64],
    tags: Vec<MacTag>,
}
pub struct ReceiverMacContribution {
    setup_root: [u8; 64],
    sender: u32,
    receiver: u32,
    transfer_id: [u8; 64],
    tags: Vec<MacTag>,
}

/// Public routing statement for one ordered OT batch. An authenticated
/// transport must sign/frame these bytes; the structure carries no signature.
/// It binds outputs to the exact setup/endpoints without exposing messages or
/// choices.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairwiseOtBinding {
    setup_root: [u8; 64],
    sender: u32,
    receiver: u32,
    transfer_id: [u8; 64],
    values: u32,
}

impl PairwiseOtBinding {
    pub fn setup_root(&self) -> [u8; 64] {
        self.setup_root
    }
    pub fn sender(&self) -> u32 {
        self.sender
    }
    pub fn receiver(&self) -> u32 {
        self.receiver
    }
    pub fn transfer_id(&self) -> [u8; 64] {
        self.transfer_id
    }

    pub fn to_canonical_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(152);
        out.extend_from_slice(OT_BINDING_MAGIC);
        put_u32(&mut out, 152);
        out.extend_from_slice(&self.setup_root);
        put_u32(&mut out, self.sender);
        put_u32(&mut out, self.receiver);
        out.extend_from_slice(&self.transfer_id);
        put_u32(&mut out, self.values);
        out
    }

    pub fn from_canonical_bytes(
        certificate: &DistributedMacCertificate,
        bytes: &[u8],
    ) -> Result<Self> {
        let mut c = Cursor::new(bytes);
        if c.take::<8>()? != *OT_BINDING_MAGIC || c.u32()? != 152 || bytes.len() != 152 {
            return Err(DistributedMacError::NonCanonicalWire);
        }
        let setup_root = c.take()?;
        let sender = c.u32()?;
        let receiver = c.u32()?;
        let transfer_id = c.take()?;
        let values = c.u32()?;
        c.finish()?;
        if setup_root != certificate.setup_root
            || transfer_id == [0; 64]
            || values != certificate.manifest.values
        {
            return Err(DistributedMacError::ContextMismatch);
        }
        valid_pair(certificate, sender, receiver)?;
        let value = Self {
            setup_root,
            sender,
            receiver,
            transfer_id,
            values,
        };
        if value.to_canonical_bytes().as_slice() != bytes {
            return Err(DistributedMacError::NonCanonicalWire);
        }
        Ok(value)
    }
}

pub fn prepare_pairwise_ot<R: RngCore + CryptoRng>(
    certificate: &DistributedMacCertificate,
    key: &MacKeyShareCustody,
    receiver: u32,
    rng: &mut R,
) -> Result<(
    PairwiseOtBinding,
    PairwiseOtSenderBatch,
    SenderMacContribution,
)> {
    certificate.validate_key(key, key.party)?;
    valid_pair(certificate, key.party, receiver)?;
    let mut messages = Vec::with_capacity(certificate.manifest.values as usize);
    let mut tags = Vec::with_capacity(messages.capacity());
    for _ in 0..certificate.manifest.values {
        let mut row = [[Gf128::ZERO; 2]; 2];
        let mut tag = MacTag::default();
        for lane in 0..2 {
            let r = random_field(rng);
            row[lane] = [r, r.add(key.alpha[lane])];
            tag.0[lane] = r;
        }
        messages.push(row);
        tags.push(tag);
    }
    let transfer_id = ot_digest(certificate.setup_root, key.party, receiver, &messages);
    Ok((
        PairwiseOtBinding {
            setup_root: certificate.setup_root,
            sender: key.party,
            receiver,
            transfer_id,
            values: certificate.manifest.values,
        },
        PairwiseOtSenderBatch {
            setup_root: certificate.setup_root,
            sender: key.party,
            receiver,
            transfer_id,
            messages,
        },
        SenderMacContribution {
            setup_root: certificate.setup_root,
            sender: key.party,
            receiver,
            transfer_id,
            tags,
        },
    ))
}

/// Accept selected outputs from the receiver-side OT adapter. Correct selection
/// is the explicit malicious-OT assumption of this substrate.
pub fn accept_ot_delivery(
    certificate: &DistributedMacCertificate,
    binding: &PairwiseOtBinding,
    selected: Vec<[[u8; 16]; 2]>,
) -> Result<ReceiverMacContribution> {
    valid_pair(certificate, binding.sender, binding.receiver)?;
    if binding.setup_root != certificate.setup_root
        || binding.transfer_id == [0; 64]
        || binding.values != certificate.manifest.values
        || selected.len() != certificate.manifest.values as usize
    {
        return Err(DistributedMacError::ShapeMismatch);
    }
    let tags = selected
        .into_iter()
        .map(|row| MacTag(std::array::from_fn(|lane| Gf128::from_bytes(row[lane]))))
        .collect();
    Ok(ReceiverMacContribution {
        setup_root: certificate.setup_root,
        sender: binding.sender,
        receiver: binding.receiver,
        transfer_id: binding.transfer_id,
        tags,
    })
}

/// Per-party tag assembler. It refuses omission or duplicate coverage of any
/// ordered pair incident on this party.
pub struct PartyTagBuilder {
    setup_root: [u8; 64],
    party: u32,
    bits: Vec<u8>,
    tags: Vec<MacTag>,
    outgoing: Vec<bool>,
    incoming: Vec<bool>,
}
impl PartyTagBuilder {
    pub fn new(
        certificate: &DistributedMacCertificate,
        key: &MacKeyShareCustody,
        bits: PartyBitShares,
    ) -> Result<Self> {
        certificate.validate_key(key, bits.party)?;
        if bits.setup_root != certificate.setup_root {
            return Err(DistributedMacError::ContextMismatch);
        }
        let mut tags = vec![MacTag::default(); bits.values.len()];
        for (tag, bit) in tags.iter_mut().zip(&bits.values) {
            let bit = Gf128::from_bit(*bit)?;
            for lane in 0..2 {
                tag.0[lane] = key.alpha[lane].mul(bit);
            }
        }
        let n = certificate.manifest.parties() as usize;
        let mut outgoing = vec![false; n];
        let mut incoming = vec![false; n];
        outgoing[bits.party as usize] = true;
        incoming[bits.party as usize] = true;
        Ok(Self {
            setup_root: certificate.setup_root,
            party: bits.party,
            bits: bits.values,
            tags,
            outgoing,
            incoming,
        })
    }
    pub fn absorb_sender(&mut self, part: SenderMacContribution) -> Result<()> {
        if part.setup_root != self.setup_root
            || part.sender != self.party
            || part.transfer_id == [0; 64]
        {
            return Err(DistributedMacError::ContextMismatch);
        }
        let peer = part.receiver as usize;
        if peer >= self.outgoing.len() {
            return Err(DistributedMacError::InvalidParty {
                party: part.receiver,
                parties: self.outgoing.len() as u32,
            });
        }
        if self.outgoing[peer] {
            return Err(DistributedMacError::DuplicateContribution {
                sender: self.party,
                receiver: part.receiver,
            });
        }
        add_tags(&mut self.tags, part.tags)?;
        self.outgoing[peer] = true;
        Ok(())
    }
    pub fn absorb_receiver(&mut self, part: ReceiverMacContribution) -> Result<()> {
        if part.setup_root != self.setup_root
            || part.receiver != self.party
            || part.transfer_id == [0; 64]
        {
            return Err(DistributedMacError::ContextMismatch);
        }
        let peer = part.sender as usize;
        if peer >= self.incoming.len() {
            return Err(DistributedMacError::InvalidParty {
                party: part.sender,
                parties: self.incoming.len() as u32,
            });
        }
        if self.incoming[peer] {
            return Err(DistributedMacError::DuplicateContribution {
                sender: part.sender,
                receiver: self.party,
            });
        }
        add_tags(&mut self.tags, part.tags)?;
        self.incoming[peer] = true;
        Ok(())
    }
    pub fn finalize(self) -> Result<PartyAuthenticatedRow> {
        for peer in 0..self.outgoing.len() {
            if !self.outgoing[peer] {
                return Err(DistributedMacError::MissingContribution {
                    sender: self.party,
                    receiver: peer as u32,
                });
            }
            if !self.incoming[peer] {
                return Err(DistributedMacError::MissingContribution {
                    sender: peer as u32,
                    receiver: self.party,
                });
            }
        }
        Ok(PartyAuthenticatedRow {
            setup_root: self.setup_root,
            party: self.party,
            bits: self.bits,
            tags: self.tags,
        })
    }
}

pub struct PartyAuthenticatedRow {
    setup_root: [u8; 64],
    party: u32,
    bits: Vec<u8>,
    tags: Vec<MacTag>,
}

/// Exact public vector already fixed by FHTRI's value-opening barrier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenedMacValues {
    setup_root: [u8; 64],
    source_opening: [u8; 64],
    values: Vec<u8>,
    digest: [u8; 64],
}
impl OpenedMacValues {
    pub fn bind(
        certificate: &DistributedMacCertificate,
        source_opening: [u8; 64],
        values: Vec<u8>,
    ) -> Result<Self> {
        if source_opening == [0; 64]
            || values.len() != certificate.manifest.values as usize
            || values.iter().any(|b| *b > 1)
        {
            return Err(DistributedMacError::ShapeMismatch);
        }
        let digest = opened_digest(certificate.setup_root, source_opening, &values);
        Ok(Self {
            setup_root: certificate.setup_root,
            source_opening,
            values,
            digest,
        })
    }
    pub fn digest(&self) -> [u8; 64] {
        self.digest
    }
    pub fn source_opening(&self) -> [u8; 64] {
        self.source_opening
    }
}

pub struct MacCheckChallenge {
    setup_root: [u8; 64],
    opened: [u8; 64],
    digest: [u8; 64],
    coefficients: [Vec<Gf128>; 2],
}
impl MacCheckChallenge {
    pub fn derive(
        certificate: &DistributedMacCertificate,
        opened: &OpenedMacValues,
        joint_beacon: [u8; 64],
    ) -> Result<Self> {
        if joint_beacon == [0; 64] || opened.setup_root != certificate.setup_root {
            return Err(DistributedMacError::ContextMismatch);
        }
        let coefficients = std::array::from_fn(|lane| {
            (0..certificate.manifest.values)
                .map(|index| {
                    let mut h = Sha512::new();
                    h.update(domain(CHALLENGE_DOMAIN));
                    h.update(certificate.setup_root);
                    h.update(opened.digest);
                    h.update(joint_beacon);
                    h.update((lane as u32).to_be_bytes());
                    h.update(index.to_be_bytes());
                    let bytes: [u8; 64] = h.finalize().into();
                    Gf128::from_bytes(bytes[..16].try_into().expect("fixed"))
                })
                .collect()
        });
        let mut h = Sha512::new();
        h.update(domain(CHALLENGE_DOMAIN));
        h.update(certificate.setup_root);
        h.update(opened.digest);
        h.update(joint_beacon);
        h.update(2u32.to_be_bytes());
        Ok(Self {
            setup_root: certificate.setup_root,
            opened: opened.digest,
            digest: h.finalize().into(),
            coefficients,
        })
    }
    pub fn digest(&self) -> [u8; 64] {
        self.digest
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MacCheckCommitment {
    setup_root: [u8; 64],
    challenge: [u8; 64],
    party: u32,
    digest: [u8; 64],
}
pub struct PendingMacCheck {
    setup_root: [u8; 64],
    challenge: [u8; 64],
    party: u32,
    salt: [u8; 32],
    sigma: [Gf128; 2],
    commitment: [u8; 64],
}

impl PartyAuthenticatedRow {
    pub fn prepare_check(
        &self,
        certificate: &DistributedMacCertificate,
        key: &MacKeyShareCustody,
        opened: &OpenedMacValues,
        challenge: &MacCheckChallenge,
        salt: [u8; 32],
    ) -> Result<(MacCheckCommitment, PendingMacCheck)> {
        certificate.validate_key(key, self.party)?;
        if salt == [0; 32]
            || self.setup_root != certificate.setup_root
            || opened.setup_root != certificate.setup_root
            || challenge.setup_root != certificate.setup_root
            || challenge.opened != opened.digest
            || self.bits.len() != opened.values.len()
            || self.tags.len() != opened.values.len()
        {
            return Err(DistributedMacError::ContextMismatch);
        }
        let mut sigma = [Gf128::ZERO; 2];
        for index in 0..self.tags.len() {
            let bit = Gf128::from_bit(opened.values[index])?;
            for lane in 0..2 {
                let local = self.tags[index].0[lane].add(key.alpha[lane].mul(bit));
                sigma[lane] = sigma[lane].add(challenge.coefficients[lane][index].mul(local));
            }
        }
        let digest = check_commitment(
            certificate.setup_root,
            challenge.digest,
            self.party,
            salt,
            sigma,
        );
        Ok((
            MacCheckCommitment {
                setup_root: certificate.setup_root,
                challenge: challenge.digest,
                party: self.party,
                digest,
            },
            PendingMacCheck {
                setup_root: certificate.setup_root,
                challenge: challenge.digest,
                party: self.party,
                salt,
                sigma,
                commitment: digest,
            },
        ))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MacCheckCommitmentSet {
    setup_root: [u8; 64],
    challenge: [u8; 64],
    commitments: Vec<[u8; 64]>,
    root: [u8; 64],
}
impl MacCheckCommitmentSet {
    pub fn seal(
        certificate: &DistributedMacCertificate,
        challenge: &MacCheckChallenge,
        inputs: Vec<MacCheckCommitment>,
    ) -> Result<Self> {
        if challenge.setup_root != certificate.setup_root
            || inputs.len() != certificate.manifest.parties() as usize
        {
            return Err(DistributedMacError::ContextMismatch);
        }
        let mut commitments = Vec::with_capacity(inputs.len());
        for (expected, input) in inputs.into_iter().enumerate() {
            if input.party != expected as u32 {
                return Err(DistributedMacError::DuplicateParty(input.party));
            }
            if input.setup_root != certificate.setup_root || input.challenge != challenge.digest {
                return Err(DistributedMacError::ContextMismatch);
            }
            commitments.push(input.digest);
        }
        let root = check_set_digest(certificate.setup_root, challenge.digest, &commitments);
        Ok(Self {
            setup_root: certificate.setup_root,
            challenge: challenge.digest,
            commitments,
            root,
        })
    }
    pub fn root(&self) -> [u8; 64] {
        self.root
    }
    pub fn to_canonical_bytes(&self) -> Result<Vec<u8>> {
        let len = 208usize
            .checked_add(
                self.commitments
                    .len()
                    .checked_mul(64)
                    .ok_or(DistributedMacError::ArithmeticOverflow)?,
            )
            .ok_or(DistributedMacError::ArithmeticOverflow)?;
        let mut out = Vec::with_capacity(len);
        out.extend_from_slice(CHECK_SET_MAGIC);
        put_u32(&mut out, usize_u32(len)?);
        out.extend_from_slice(&self.setup_root);
        out.extend_from_slice(&self.challenge);
        put_u32(&mut out, usize_u32(self.commitments.len())?);
        for c in &self.commitments {
            out.extend_from_slice(c);
        }
        out.extend_from_slice(&self.root);
        Ok(out)
    }
    pub fn from_canonical_bytes(
        certificate: &DistributedMacCertificate,
        challenge: &MacCheckChallenge,
        bytes: &[u8],
    ) -> Result<Self> {
        let mut c = Cursor::new(bytes);
        if c.take::<8>()? != *CHECK_SET_MAGIC
            || c.u32()? as usize != bytes.len()
            || c.take::<64>()? != certificate.setup_root
            || c.take::<64>()? != challenge.digest
        {
            return Err(DistributedMacError::NonCanonicalWire);
        }
        let count = c.u32()?;
        if count != certificate.manifest.parties() {
            return Err(DistributedMacError::NonCanonicalWire);
        }
        let mut commitments = Vec::with_capacity(count as usize);
        for _ in 0..count {
            commitments.push(c.take()?);
        }
        let claimed = c.take()?;
        c.finish()?;
        let root = check_set_digest(certificate.setup_root, challenge.digest, &commitments);
        if claimed != root {
            return Err(DistributedMacError::NonCanonicalWire);
        }
        let value = Self {
            setup_root: certificate.setup_root,
            challenge: challenge.digest,
            commitments,
            root,
        };
        if value.to_canonical_bytes()?.as_slice() != bytes {
            return Err(DistributedMacError::NonCanonicalWire);
        }
        Ok(value)
    }
}

pub struct MacCheckReveal {
    setup_root: [u8; 64],
    challenge: [u8; 64],
    set_root: [u8; 64],
    party: u32,
    salt: [u8; 32],
    sigma: [Gf128; 2],
}
impl PendingMacCheck {
    pub fn reveal(self, set: &MacCheckCommitmentSet) -> Result<MacCheckReveal> {
        if self.setup_root != set.setup_root
            || self.challenge != set.challenge
            || self.party as usize >= set.commitments.len()
            || set.commitments[self.party as usize] != self.commitment
        {
            return Err(DistributedMacError::CommitmentMismatch { party: self.party });
        }
        Ok(MacCheckReveal {
            setup_root: self.setup_root,
            challenge: self.challenge,
            set_root: set.root,
            party: self.party,
            salt: self.salt,
            sigma: self.sigma,
        })
    }
}

pub struct VerifiedDistributedMacOpening {
    setup_root: [u8; 64],
    opened: [u8; 64],
}
impl VerifiedDistributedMacOpening {
    pub fn setup_root(&self) -> [u8; 64] {
        self.setup_root
    }
    pub fn opened_digest(&self) -> [u8; 64] {
        self.opened
    }
}

pub fn verify_mac_check(
    certificate: &DistributedMacCertificate,
    opened: &OpenedMacValues,
    challenge: &MacCheckChallenge,
    set: &MacCheckCommitmentSet,
    reveals: Vec<MacCheckReveal>,
) -> Result<VerifiedDistributedMacOpening> {
    if opened.setup_root != certificate.setup_root
        || challenge.setup_root != certificate.setup_root
        || challenge.opened != opened.digest
        || set.setup_root != certificate.setup_root
        || set.challenge != challenge.digest
        || reveals.len() != certificate.manifest.parties() as usize
    {
        return Err(DistributedMacError::ContextMismatch);
    }
    let mut aggregate = [Gf128::ZERO; 2];
    for (expected, reveal) in reveals.into_iter().enumerate() {
        if reveal.party != expected as u32 {
            return Err(DistributedMacError::DuplicateParty(reveal.party));
        }
        if reveal.setup_root != certificate.setup_root
            || reveal.challenge != challenge.digest
            || reveal.set_root != set.root
        {
            return Err(DistributedMacError::ContextMismatch);
        }
        if check_commitment(
            certificate.setup_root,
            challenge.digest,
            reveal.party,
            reveal.salt,
            reveal.sigma,
        ) != set.commitments[expected]
        {
            return Err(DistributedMacError::CommitmentMismatch {
                party: reveal.party,
            });
        }
        for lane in 0..2 {
            aggregate[lane] = aggregate[lane].add(reveal.sigma[lane]);
        }
    }
    for (lane, value) in aggregate.into_iter().enumerate() {
        if !value.is_zero() {
            return Err(DistributedMacError::CheckRejected { lane });
        }
    }
    Ok(VerifiedDistributedMacOpening {
        setup_root: certificate.setup_root,
        opened: opened.digest,
    })
}

fn validate_manifest(
    session: [u8; 32],
    candidate: [u8; 64],
    roster: &[[u8; 32]],
    values: u32,
) -> Result<()> {
    if session == [0; 32] || candidate == [0; 64] {
        return Err(DistributedMacError::InvalidParameters("zero context"));
    }
    if roster.len() < 2 || roster.len() > MAX_DISTRIBUTED_MAC_PARTIES as usize {
        return Err(DistributedMacError::InvalidParameters(
            "roster outside profile",
        ));
    }
    if values == 0 || values > MAX_DISTRIBUTED_MAC_VALUES {
        return Err(DistributedMacError::AllocationCeiling);
    }
    let mut seen = HashSet::with_capacity(roster.len());
    if roster.iter().any(|id| *id == [0; 32] || !seen.insert(*id)) {
        return Err(DistributedMacError::InvalidParameters(
            "roster identities not unique",
        ));
    }
    let cells = (roster.len() as u64)
        .checked_mul(values as u64)
        .and_then(|x| x.checked_mul(2))
        .ok_or(DistributedMacError::ArithmeticOverflow)?;
    if cells > 1u64 << 30 {
        return Err(DistributedMacError::AllocationCeiling);
    }
    Ok(())
}
fn valid_party(manifest: &DistributedMacManifest, party: u32) -> Result<()> {
    if party >= manifest.parties() {
        Err(DistributedMacError::InvalidParty {
            party,
            parties: manifest.parties(),
        })
    } else {
        Ok(())
    }
}
fn valid_pair(certificate: &DistributedMacCertificate, sender: u32, receiver: u32) -> Result<()> {
    valid_party(&certificate.manifest, sender)?;
    valid_party(&certificate.manifest, receiver)?;
    if sender == receiver {
        Err(DistributedMacError::InvalidParameters(
            "OT endpoints must differ",
        ))
    } else {
        Ok(())
    }
}
fn add_tags(target: &mut [MacTag], values: Vec<MacTag>) -> Result<()> {
    if target.len() != values.len() {
        return Err(DistributedMacError::ShapeMismatch);
    }
    for (target, value) in target.iter_mut().zip(values) {
        target.add_assign(value);
    }
    Ok(())
}
fn random_field<R: RngCore + CryptoRng>(rng: &mut R) -> Gf128 {
    let mut b = [0; 16];
    rng.fill_bytes(&mut b);
    Gf128::from_bytes(b)
}
fn random_nonzero<R: RngCore + CryptoRng>(rng: &mut R) -> Gf128 {
    loop {
        let x = random_field(rng);
        if !x.is_zero() {
            return x;
        }
    }
}
fn domain(bytes: &[u8]) -> [u8; 64] {
    Sha512::digest(bytes).into()
}

fn manifest_digest(
    session: [u8; 32],
    candidate: [u8; 64],
    roster: &[[u8; 32]],
    values: u32,
) -> [u8; 64] {
    let mut h = Sha512::new();
    h.update(domain(MANIFEST_DOMAIN));
    h.update(session);
    h.update(candidate);
    h.update(values.to_be_bytes());
    h.update((roster.len() as u32).to_be_bytes());
    h.update(2u32.to_be_bytes());
    for id in roster {
        h.update(id);
    }
    h.finalize().into()
}
fn key_commitment(manifest: [u8; 64], party: u32, salt: [u8; 32], alpha: [Gf128; 2]) -> [u8; 64] {
    let mut h = Sha512::new();
    h.update(domain(KEY_COMMIT_DOMAIN));
    h.update(manifest);
    h.update(party.to_be_bytes());
    h.update(salt);
    for x in alpha {
        h.update(x.to_bytes());
    }
    h.finalize().into()
}
fn setup_digest(manifest: [u8; 64], commitments: &[[u8; 64]]) -> [u8; 64] {
    let mut h = Sha512::new();
    h.update(domain(SETUP_DOMAIN));
    h.update(manifest);
    h.update((commitments.len() as u32).to_be_bytes());
    for c in commitments {
        h.update(c);
    }
    h.finalize().into()
}
fn ot_digest(root: [u8; 64], sender: u32, receiver: u32, rows: &[[[Gf128; 2]; 2]]) -> [u8; 64] {
    let mut h = Sha512::new();
    h.update(domain(OT_DOMAIN));
    h.update(root);
    h.update(sender.to_be_bytes());
    h.update(receiver.to_be_bytes());
    h.update((rows.len() as u32).to_be_bytes());
    for row in rows {
        for pair in row {
            h.update(pair[0].to_bytes());
            h.update(pair[1].to_bytes());
        }
    }
    h.finalize().into()
}
fn opened_digest(root: [u8; 64], source: [u8; 64], values: &[u8]) -> [u8; 64] {
    let mut h = Sha512::new();
    h.update(domain(OPENED_DOMAIN));
    h.update(root);
    h.update(source);
    h.update((values.len() as u32).to_be_bytes());
    h.update(values);
    h.finalize().into()
}
fn check_commitment(
    root: [u8; 64],
    challenge: [u8; 64],
    party: u32,
    salt: [u8; 32],
    sigma: [Gf128; 2],
) -> [u8; 64] {
    let mut h = Sha512::new();
    h.update(domain(CHECK_COMMIT_DOMAIN));
    h.update(root);
    h.update(challenge);
    h.update(party.to_be_bytes());
    h.update(salt);
    for x in sigma {
        h.update(x.to_bytes());
    }
    h.finalize().into()
}
fn check_set_digest(root: [u8; 64], challenge: [u8; 64], commitments: &[[u8; 64]]) -> [u8; 64] {
    let mut h = Sha512::new();
    h.update(domain(CHECK_SET_DOMAIN));
    h.update(root);
    h.update(challenge);
    h.update((commitments.len() as u32).to_be_bytes());
    for c in commitments {
        h.update(c);
    }
    h.finalize().into()
}
fn put_u32(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_be_bytes());
}
fn usize_u32(value: usize) -> Result<u32> {
    u32::try_from(value).map_err(|_| DistributedMacError::ArithmeticOverflow)
}

struct Cursor<'a> {
    bytes: &'a [u8],
    offset: usize,
}
impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }
    fn bytes(&mut self, len: usize) -> Result<&'a [u8]> {
        let end = self
            .offset
            .checked_add(len)
            .ok_or(DistributedMacError::ArithmeticOverflow)?;
        let value = self
            .bytes
            .get(self.offset..end)
            .ok_or(DistributedMacError::TruncatedWire)?;
        self.offset = end;
        Ok(value)
    }
    fn take<const N: usize>(&mut self) -> Result<[u8; N]> {
        self.bytes(N)?
            .try_into()
            .map_err(|_| DistributedMacError::TruncatedWire)
    }
    fn u32(&mut self) -> Result<u32> {
        Ok(u32::from_be_bytes(self.take()?))
    }
    fn finish(self) -> Result<()> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(DistributedMacError::NonCanonicalWire)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};

    fn manifest(tag: u8, values: u32) -> DistributedMacManifest {
        DistributedMacManifest::new(
            [tag; 32],
            [tag + 1; 64],
            vec![[11; 32], [22; 32], [33; 32]],
            values,
        )
        .unwrap()
    }
    fn setup(
        tag: u8,
        shares: Vec<Vec<u8>>,
    ) -> (
        DistributedMacCertificate,
        Vec<MacKeyShareCustody>,
        Vec<PartyBitShares>,
    ) {
        let m = manifest(tag, shares[0].len() as u32);
        let mut rng = StdRng::seed_from_u64(tag as u64 + 900);
        let mut contributions = vec![];
        let mut keys = vec![];
        for party in 0..m.parties() {
            let (c, k) = generate_key_share(&m, party, &mut rng).unwrap();
            contributions.push(c);
            keys.push(k);
        }
        let cert = DistributedMacCertificate::seal(m, contributions).unwrap();
        let rows = shares
            .into_iter()
            .enumerate()
            .map(|(p, row)| PartyBitShares::new(&cert, p as u32, row).unwrap())
            .collect();
        (cert, keys, rows)
    }

    /// Algebra-only ideal OT for tests. It co-locates exactly one sender share
    /// and one receiver choice vector; production must not use it.
    fn ideal_ot(
        cert: &DistributedMacCertificate,
        binding: PairwiseOtBinding,
        batch: PairwiseOtSenderBatch,
        choices: PairwiseOtReceiverChoices<'_>,
    ) -> ReceiverMacContribution {
        assert_eq!(batch.setup_root, choices.setup_root);
        assert_eq!(batch.sender, choices.sender);
        assert_eq!(batch.receiver, choices.receiver);
        let selected = (0..choices.len())
            .map(|index| {
                let bit = choices.choice(index).unwrap() as usize;
                std::array::from_fn(|lane| batch.messages[index][lane][bit].to_bytes())
            })
            .collect();
        assert_eq!(binding.transfer_id, batch.transfer_id);
        accept_ot_delivery(cert, &binding, selected).unwrap()
    }

    fn authenticate(
        cert: &DistributedMacCertificate,
        keys: &[MacKeyShareCustody],
        rows: Vec<PartyBitShares>,
    ) -> Vec<PartyAuthenticatedRow> {
        let n = keys.len();
        let mut rng = StdRng::seed_from_u64(77);
        let mut builders = rows
            .into_iter()
            .enumerate()
            .map(|(p, row)| PartyTagBuilder::new(cert, &keys[p], row).unwrap())
            .collect::<Vec<_>>();
        for sender in 0..n {
            for receiver in 0..n {
                if sender == receiver {
                    continue;
                }
                let (binding, batch, send) =
                    prepare_pairwise_ot(cert, &keys[sender], receiver as u32, &mut rng).unwrap();
                let choices = PairwiseOtReceiverChoices {
                    setup_root: cert.setup_root,
                    sender: sender as u32,
                    receiver: receiver as u32,
                    values: &builders[receiver].bits,
                };
                let receive = ideal_ot(cert, binding, batch, choices);
                builders[sender].absorb_sender(send).unwrap();
                builders[receiver].absorb_receiver(receive).unwrap();
            }
        }
        builders
            .into_iter()
            .map(|b| b.finalize().unwrap())
            .collect()
    }

    fn verify(
        cert: &DistributedMacCertificate,
        keys: &[MacKeyShareCustody],
        rows: &[PartyAuthenticatedRow],
        opened_values: Vec<u8>,
    ) -> Result<VerifiedDistributedMacOpening> {
        let opened = OpenedMacValues::bind(cert, [88; 64], opened_values)?;
        let challenge = MacCheckChallenge::derive(cert, &opened, [99; 64])?;
        let mut commits = vec![];
        let mut pending = vec![];
        for party in 0..keys.len() {
            let (c, p) = rows[party].prepare_check(
                cert,
                &keys[party],
                &opened,
                &challenge,
                [party as u8 + 1; 32],
            )?;
            commits.push(c);
            pending.push(p);
        }
        let set = MacCheckCommitmentSet::seal(cert, &challenge, commits)?;
        let wire = set.to_canonical_bytes()?;
        let set = MacCheckCommitmentSet::from_canonical_bytes(cert, &challenge, &wire)?;
        let reveals = pending
            .into_iter()
            .map(|p| p.reveal(&set))
            .collect::<Result<Vec<_>>>()?;
        verify_mac_check(cert, &opened, &challenge, &set, reveals)
    }

    #[test]
    fn cross_terms_authenticate_without_global_key_api() {
        let shares = vec![
            vec![1, 0, 1, 1, 0, 0, 1],
            vec![0, 1, 1, 0, 1, 0, 1],
            vec![1, 1, 0, 0, 0, 1, 1],
        ];
        let opened = (0..shares[0].len())
            .map(|i| shares.iter().fold(0, |x, row| x ^ row[i]))
            .collect();
        let (cert, keys, rows) = setup(7, shares);
        let auth = authenticate(&cert, &keys, rows);
        let proof = verify(&cert, &keys, &auth, opened).unwrap();
        assert_eq!(proof.setup_root(), cert.setup_root());
        assert_eq!(cert.key_commitments().len(), 3);
        assert!(cert.validate_key(&keys[0], 0).is_ok());
    }

    #[test]
    fn diagonal_only_tags_do_not_authenticate_global_product() {
        // x shares (1,1,0) open to zero. Diagonal-only tags sum to
        // alpha_0 + alpha_1, whereas the required global alpha*x is zero.
        let (cert, keys, rows) = setup(6, vec![vec![1], vec![1], vec![0]]);
        let diagonal_only = rows
            .into_iter()
            .enumerate()
            .map(|(party, row)| {
                let mut builder = PartyTagBuilder::new(&cert, &keys[party], row).unwrap();
                // Test-only bypass of the coverage gate isolates the algebraic
                // tooth: merely pretending cross terms arrived must still fail
                // the actual batched MAC relation.
                builder.outgoing.fill(true);
                builder.incoming.fill(true);
                builder.finalize().unwrap()
            })
            .collect::<Vec<_>>();
        assert!(matches!(
            verify(&cert, &keys, &diagonal_only, vec![0]),
            Err(DistributedMacError::CheckRejected { .. })
        ));
    }

    #[test]
    fn omission_duplicate_and_share_swap_refuse() {
        let (cert, keys, rows) = setup(8, vec![vec![1, 0], vec![0, 1], vec![1, 1]]);
        let mut builders = rows
            .into_iter()
            .enumerate()
            .map(|(p, row)| PartyTagBuilder::new(&cert, &keys[p], row).unwrap())
            .collect::<Vec<_>>();
        assert!(matches!(
            builders.remove(0).finalize(),
            Err(DistributedMacError::MissingContribution { .. })
        ));
        let mut rng = StdRng::seed_from_u64(12);
        let (_, _, wrong) = prepare_pairwise_ot(&cert, &keys[2], 0, &mut rng).unwrap();
        assert!(matches!(
            builders[0].absorb_sender(wrong),
            Err(DistributedMacError::ContextMismatch)
        ));
        let (binding, batch, _) = prepare_pairwise_ot(&cert, &keys[2], 1, &mut rng).unwrap();
        let duplicate_choices = builders[0].bits.clone();
        let choices = PairwiseOtReceiverChoices {
            setup_root: cert.setup_root,
            sender: 2,
            receiver: 1,
            values: &duplicate_choices,
        };
        let receive = ideal_ot(&cert, binding, batch, choices);
        builders[0].absorb_receiver(receive).unwrap();
        let (binding, batch, _) = prepare_pairwise_ot(&cert, &keys[2], 1, &mut rng).unwrap();
        let duplicate_choices = builders[0].bits.clone();
        let choices = PairwiseOtReceiverChoices {
            setup_root: cert.setup_root,
            sender: 2,
            receiver: 1,
            values: &duplicate_choices,
        };
        assert!(matches!(
            builders[0].absorb_receiver(ideal_ot(&cert, binding, batch, choices)),
            Err(DistributedMacError::DuplicateContribution { .. })
        ));
    }

    #[test]
    fn mutation_and_false_opening_refuse() {
        let shares = vec![vec![1, 0, 1], vec![0, 1, 1], vec![1, 1, 0]];
        let (cert, keys, rows) = setup(9, shares);
        let mut auth = authenticate(&cert, &keys, rows);
        auth[1].tags[2].0[0].0 ^= 1;
        assert!(matches!(
            verify(&cert, &keys, &auth, vec![0, 0, 0]),
            Err(DistributedMacError::CheckRejected { lane: 0 })
        ));
        let shares = vec![vec![1, 0, 1], vec![0, 1, 1], vec![1, 1, 0]];
        let (cert, keys, rows) = setup(10, shares);
        let auth = authenticate(&cert, &keys, rows);
        assert!(matches!(
            verify(&cert, &keys, &auth, vec![1, 0, 0]),
            Err(DistributedMacError::CheckRejected { .. })
        ));
    }

    #[test]
    fn wires_and_context_substitution_refuse() {
        let m = manifest(12, 4);
        let wire = m.to_canonical_bytes().unwrap();
        assert_eq!(
            DistributedMacManifest::from_canonical_bytes(&wire).unwrap(),
            m
        );
        let mut trailing = wire.clone();
        trailing.push(0);
        assert!(DistributedMacManifest::from_canonical_bytes(&trailing).is_err());
        assert!(DistributedMacManifest::from_canonical_bytes(&wire[..wire.len() - 1]).is_err());
        let mut changed = wire;
        changed[16] ^= 1;
        assert!(DistributedMacManifest::from_canonical_bytes(&changed).is_err());
        let (a, keys, rows) = setup(20, vec![vec![0, 1], vec![1, 0], vec![0, 0]]);
        let (b, _, _) = setup(21, vec![vec![0, 1], vec![1, 0], vec![0, 0]]);
        assert!(b.validate_key(&keys[0], 0).is_err());
        assert!(PartyTagBuilder::new(&b, &keys[0], rows.into_iter().next().unwrap()).is_err());
        assert_ne!(a.setup_root(), b.setup_root());
        let cert_wire = a.to_canonical_bytes().unwrap();
        assert_eq!(
            DistributedMacCertificate::from_canonical_bytes(&cert_wire).unwrap(),
            a
        );
        let mut corrupt = cert_wire;
        let last = corrupt.len() - 1;
        corrupt[last] ^= 1;
        assert!(DistributedMacCertificate::from_canonical_bytes(&corrupt).is_err());

        let mut rng = StdRng::seed_from_u64(55);
        let (binding, _, _) = prepare_pairwise_ot(&a, &keys[0], 1, &mut rng).unwrap();
        let binding_wire = binding.to_canonical_bytes();
        assert_eq!(
            PairwiseOtBinding::from_canonical_bytes(&a, &binding_wire).unwrap(),
            binding
        );
        assert!(PairwiseOtBinding::from_canonical_bytes(&b, &binding_wire).is_err());
        let mut trailing = binding_wire;
        trailing.push(0);
        assert!(PairwiseOtBinding::from_canonical_bytes(&a, &trailing).is_err());
    }

    #[test]
    fn reordered_and_duplicate_roster_contributions_refuse() {
        let m = manifest(22, 2);
        let mut rng = StdRng::seed_from_u64(44);
        let mut c = vec![];
        for party in 0..m.parties() {
            c.push(generate_key_share(&m, party, &mut rng).unwrap().0);
        }
        c.swap(0, 1);
        assert!(DistributedMacCertificate::seal(m, c).is_err());
        assert!(DistributedMacManifest::new([1; 32], [2; 64], vec![[3; 32], [3; 32]], 2).is_err());
    }
}
