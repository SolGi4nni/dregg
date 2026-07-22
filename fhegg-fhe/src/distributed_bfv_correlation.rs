//! Distributed BFV correlation factory: the first executable `FHTRI005` cut.
//!
//! Two independently custodied parties contribute packed encryptions of their
//! private XOR shares `a_i`, `b_i`, and `r_i` under the collective BFV key.
//! The public worker evaluates the exact Boolean identities
//!
//! ```text
//! a = a_0 XOR a_1       b = b_0 XOR b_1
//! c = a AND b           r = r_0 XOR r_1
//! z = c XOR r
//! ```
//!
//! with `x XOR y = x + y - 2xy`, using the party-owned multiparty
//! relinearization key.  Threshold decryption opens only `z`; party zero emits
//! `c_0 = z XOR r_0`, party one emits `c_1 = r_1`.  Thus the returned private
//! rows reconstruct genuine GF(2) Beaver candidates without any process ever
//! receiving `(a,b,c)` or both parties' shares.  Thousands of candidates ride
//! the BFV SIMD slots in one ceremony.
//!
//! The restriction to exactly two parties is deliberate: on the deployed
//! degree-4096 fold parameters this circuit is multiplication depth three.
//! More-party parity raises the depth and is refused until a larger proven
//! parameter set or a lower-depth threshold/PBS backend exists.
//!
//! ## Security boundary (do not compress this scope)
//!
//! This removes the *single triple dealer* under the one-honest-party,
//! honest-encryption/decryption premise.  It is not yet malicious-secure:
//! ML-DSA authenticates each exact contribution, but there is no transferable
//! lattice proof that its ciphertext plaintexts are bits or that a custodian's
//! BFV decryption share equals `c1*s_i +` in-range smudge.  The n-of-n DKG and
//! relinearization protocols are the real `fhe.rs` multiparty protocols, not an
//! assembled-key simulation, but their hidden shortness/correctness proofs are
//! likewise open.  `dregg-pq` supplies ML-DSA-65 authentication (post-quantum;
//! its verified-core install policy still applies); BFV security is lattice
//! based.  SHA-256/BLAKE3 transcript commitments retain 128-bit quantum
//! collision security.  Feed the private candidate rows through the existing
//! authenticated sacrifice before treating them as live preprocessing.

use std::collections::BTreeMap;
use std::fmt;

use dregg_pq::{ml_dsa_verify, MlDsaKey, ML_DSA_PK_LEN, ML_DSA_SIG_LEN};
use fhe::bfv::{Ciphertext, Encoding, Plaintext, RelinearizationKey};
use fhe_traits::{DeserializeParametrized, FheEncoder, FheEncrypter, Serialize as FheSerialize};
use sha2::{Digest, Sha256};

use crate::bfv_lean::LeanCiphertext;
use crate::bfv_mul::{BoundedCiphertext, MulEngine};
use crate::mpc_party::sacrifice::BinaryTripleShare;
use crate::threshold::relin::RelinKeySession;
use crate::threshold::{
    self, BfvParams, CollectivePublicKey, DecryptShare, KeygenCoordinator, KeygenSession,
    PublicKeyContribution, ThresholdParty, MIN_SMUDGE_BITS,
};

// Globally distinct from the FHTBC005 joint-beacon transcript and every
// FHTRI00x PartyMPC custody carrier. Type confusion must fail at byte zero.
const CONTRIBUTION_MAGIC: &[u8; 8] = b"FHBIC005";
const TRANSCRIPT_MAGIC: &[u8; 8] = b"FHBIT005";
const CERTIFICATE_MAGIC: &[u8; 8] = b"FHBIR005";
const VERSION: u8 = 1;
const SIGNATURE_CONTEXT: &[u8] = b"fhegg/fhtri005/bfv-correlation/contribution/v1";
const SESSION_DOMAIN: &[u8] = b"fhegg/fhtri005/bfv-correlation/session/v1";
const DKG_DOMAIN: &[u8] = b"fhegg/fhtri005/bfv-correlation/dkg/v1";
const CONTRIBUTION_DOMAIN: &[u8] = b"fhegg/fhtri005/bfv-correlation/contribution/v1";
const OUTPUT_DOMAIN: &[u8] = b"fhegg/fhtri005/bfv-correlation/output/v1";
const CERTIFICATE_DOMAIN: &[u8] = b"fhegg/fhtri005/bfv-correlation/certificate/v1";
const CHECKSUM_DOMAIN: &[u8] = b"fhegg/fhtri005/bfv-correlation/wire-checksum/v1";

/// This first depth-three cut intentionally supports one two-party roster.
pub const DISTRIBUTED_BFV_PARTIES: usize = 2;
/// One candidate per SIMD slot on the deployed fold parameter set.
pub const MAX_DISTRIBUTED_BFV_TRIPLES: usize = 4096;
/// Allocation ceiling for one signed contribution (three BFV ciphertexts).
pub const MAX_CORRELATION_CONTRIBUTION_BYTES: usize = 8 * 1024 * 1024;
/// Allocation ceiling for the public replay transcript.
pub const MAX_CORRELATION_TRANSCRIPT_BYTES: usize = 64 * 1024 * 1024;
/// Fixed public certificate size for the two-party cut.
pub const CORRELATION_CERTIFICATE_BYTES: usize = 401;

pub type Result<T> = std::result::Result<T, CorrelationError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CorrelationError {
    InvalidParameters(&'static str),
    UnsupportedPartyCount {
        have: usize,
        supported: usize,
    },
    InvalidParty {
        party: usize,
    },
    ShapeMismatch,
    NonBit {
        party: usize,
        vector: &'static str,
        index: usize,
    },
    DkgMismatch,
    RelinMismatch,
    SessionMismatch,
    DuplicateParty {
        party: usize,
    },
    MissingParty {
        party: usize,
    },
    InvalidSignature {
        party: usize,
    },
    MalformedWire(&'static str),
    AllocationCeiling,
    Crypto(&'static str),
    InvalidMaskedOpening,
    OutputCommitmentMismatch {
        party: usize,
    },
}

impl fmt::Display for CorrelationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "distributed BFV correlation refused: {self:?}")
    }
}

impl std::error::Error for CorrelationError {}

/// Exact public context of one correlation factory invocation.
#[derive(Clone)]
pub struct CorrelationSession {
    nonce: [u8; 32],
    keygen: KeygenSession,
    dkg_digest: [u8; 32],
    collective_key_digest: [u8; 32],
    relin_session_id: [u8; 32],
    relin_key_digest: [u8; 32],
    roster: Vec<Vec<u8>>,
    triples: usize,
    digest: [u8; 32],
}

impl CorrelationSession {
    /// Bind an exact, independently supplied DKG transcript, collective key,
    /// multiparty relinearization ceremony/key, ML-DSA roster, and batch size.
    /// The DKG contributions are replayed through [`KeygenCoordinator`]; a
    /// caller cannot merely assert that `collective` came from this roster.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        nonce: [u8; 32],
        keygen: &KeygenSession,
        dkg_contribution_wires: &[Vec<u8>],
        collective: &CollectivePublicKey,
        relin_session: &RelinKeySession,
        relin_key: &RelinearizationKey,
        roster: Vec<Vec<u8>>,
        triples: usize,
        params: &BfvParams,
    ) -> Result<Self> {
        if nonce == [0; 32] {
            return Err(CorrelationError::InvalidParameters("session nonce is zero"));
        }
        if keygen.n_parties() != DISTRIBUTED_BFV_PARTIES {
            return Err(CorrelationError::UnsupportedPartyCount {
                have: keygen.n_parties(),
                supported: DISTRIBUTED_BFV_PARTIES,
            });
        }
        if triples == 0 || triples > params.degree() || triples > MAX_DISTRIBUTED_BFV_TRIPLES {
            return Err(CorrelationError::InvalidParameters(
                "triple count exceeds the deployed SIMD batch",
            ));
        }
        validate_roster(&roster)?;
        if dkg_contribution_wires.len() != DISTRIBUTED_BFV_PARTIES {
            return Err(CorrelationError::DkgMismatch);
        }

        let mut coordinator = KeygenCoordinator::new(keygen.clone(), params.clone());
        let mut dkg_hasher = Sha256::new();
        dkg_hasher.update(DKG_DOMAIN);
        dkg_hasher.update((dkg_contribution_wires.len() as u64).to_be_bytes());
        for (expected_party, wire) in dkg_contribution_wires.iter().enumerate() {
            if wire.len() > MAX_CORRELATION_CONTRIBUTION_BYTES {
                return Err(CorrelationError::AllocationCeiling);
            }
            let contribution = PublicKeyContribution::from_wire_bytes(wire)
                .map_err(|_| CorrelationError::DkgMismatch)?;
            if contribution.party() != expected_party
                || contribution.session() != keygen
                || contribution.to_wire_bytes() != *wire
            {
                return Err(CorrelationError::DkgMismatch);
            }
            dkg_hasher.update((wire.len() as u64).to_be_bytes());
            dkg_hasher.update(hash_bytes(wire));
            coordinator
                .accept(contribution)
                .map_err(|_| CorrelationError::DkgMismatch)?;
        }
        let replayed = coordinator
            .finish()
            .map_err(|_| CorrelationError::DkgMismatch)?;
        let collective_bytes = collective.pk.to_bytes();
        if replayed.pk.to_bytes() != collective_bytes
            || relin_session.keygen_session() != keygen
            || relin_session.collective_public_key_digest()
                != threshold_relin_public_key_digest(&collective_bytes)
        {
            return Err(CorrelationError::DkgMismatch);
        }

        let dkg_digest: [u8; 32] = dkg_hasher.finalize().into();
        let collective_key_digest = hash_bytes(&collective_bytes);
        let relin_key_digest = hash_bytes(&relin_key.to_bytes());
        let relin_session_id = relin_session.session_id();
        let digest = session_digest(
            nonce,
            keygen,
            dkg_digest,
            collective_key_digest,
            relin_session_id,
            relin_key_digest,
            &roster,
            triples,
            params,
        );
        Ok(Self {
            nonce,
            keygen: keygen.clone(),
            dkg_digest,
            collective_key_digest,
            relin_session_id,
            relin_key_digest,
            roster,
            triples,
            digest,
        })
    }

    pub fn digest(&self) -> [u8; 32] {
        self.digest
    }

    pub fn nonce(&self) -> [u8; 32] {
        self.nonce
    }

    pub fn dkg_digest(&self) -> [u8; 32] {
        self.dkg_digest
    }

    pub fn relin_key_digest(&self) -> [u8; 32] {
        self.relin_key_digest
    }

    pub fn collective_key_digest(&self) -> [u8; 32] {
        self.collective_key_digest
    }

    pub fn relin_session_id(&self) -> [u8; 32] {
        self.relin_session_id
    }

    pub fn triples(&self) -> usize {
        self.triples
    }

    pub fn keygen_session(&self) -> &KeygenSession {
        &self.keygen
    }
}

fn validate_roster(roster: &[Vec<u8>]) -> Result<()> {
    if roster.len() != DISTRIBUTED_BFV_PARTIES {
        return Err(CorrelationError::UnsupportedPartyCount {
            have: roster.len(),
            supported: DISTRIBUTED_BFV_PARTIES,
        });
    }
    if roster.iter().any(|key| key.len() != ML_DSA_PK_LEN)
        || roster[0] == roster[1]
        || roster.iter().any(|key| key.iter().all(|byte| *byte == 0))
    {
        return Err(CorrelationError::InvalidParameters(
            "ML-DSA roster keys must be canonical, nonzero, and unique",
        ));
    }
    Ok(())
}

/// Party-local clear shares retained across the public BFV computation.
/// Deliberately neither `Clone` nor `Debug`.
pub struct CorrelationPartyState {
    session_digest: [u8; 32],
    party: usize,
    a: Vec<u8>,
    b: Vec<u8>,
    mask: Vec<u8>,
}

/// Authenticated encryptions of one party's candidate and mask shares.
#[derive(Clone)]
pub struct EncryptedBitContribution {
    session_digest: [u8; 32],
    party: usize,
    a: LeanCiphertext,
    b: LeanCiphertext,
    mask: LeanCiphertext,
    signature: Vec<u8>,
}

impl EncryptedBitContribution {
    /// Encrypt independently supplied canonical bit shares.  This producer
    /// checks bitness locally; the missing *transferable* encrypted-bitness
    /// proof remains explicit in the module security boundary.
    #[allow(clippy::too_many_arguments)]
    pub fn prepare(
        session: &CorrelationSession,
        party: usize,
        a: Vec<u8>,
        b: Vec<u8>,
        mask: Vec<u8>,
        params: &BfvParams,
        collective: &CollectivePublicKey,
        signing_key: &MlDsaKey,
    ) -> Result<(CorrelationPartyState, Self)> {
        if party >= DISTRIBUTED_BFV_PARTIES {
            return Err(CorrelationError::InvalidParty { party });
        }
        if signing_key.public_bytes() != session.roster[party] {
            return Err(CorrelationError::InvalidSignature { party });
        }
        validate_private_bits(party, "a", &a, session.triples)?;
        validate_private_bits(party, "b", &b, session.triples)?;
        validate_private_bits(party, "mask", &mask, session.triples)?;

        let a_ct = encrypt_bits(&a, params, collective)?;
        let b_ct = encrypt_bits(&b, params, collective)?;
        let mask_ct = encrypt_bits(&mask, params, collective)?;
        let message = contribution_signing_message(session.digest, party, &a_ct, &b_ct, &mask_ct);
        let signature = signing_key
            .try_sign_deterministic(SIGNATURE_CONTEXT, &message)
            .ok_or(CorrelationError::Crypto("ML-DSA signing"))?;
        if signature.len() != ML_DSA_SIG_LEN {
            return Err(CorrelationError::Crypto("ML-DSA signature length"));
        }
        let state = CorrelationPartyState {
            session_digest: session.digest,
            party,
            a,
            b,
            mask,
        };
        Ok((
            state,
            Self {
                session_digest: session.digest,
                party,
                a: a_ct,
                b: b_ct,
                mask: mask_ct,
                signature,
            },
        ))
    }

    pub fn party(&self) -> usize {
        self.party
    }

    pub fn to_wire_bytes(&self) -> Result<Vec<u8>> {
        let a = self.a.to_fhe_bytes();
        let b = self.b.to_fhe_bytes();
        let mask = self.mask.to_fhe_bytes();
        let capacity =
            8 + 1 + 32 + 8 + 3 * 8 + a.len() + b.len() + mask.len() + ML_DSA_SIG_LEN + 32;
        if capacity > MAX_CORRELATION_CONTRIBUTION_BYTES {
            return Err(CorrelationError::AllocationCeiling);
        }
        let mut out = Vec::with_capacity(capacity);
        out.extend_from_slice(CONTRIBUTION_MAGIC);
        out.push(VERSION);
        out.extend_from_slice(&self.session_digest);
        put_usize(&mut out, self.party)?;
        put_bytes(&mut out, &a)?;
        put_bytes(&mut out, &b)?;
        put_bytes(&mut out, &mask)?;
        out.extend_from_slice(&self.signature);
        out.extend_from_slice(&wire_checksum(&out));
        Ok(out)
    }

    pub fn from_wire_bytes(
        bytes: &[u8],
        session: &CorrelationSession,
        params: &BfvParams,
    ) -> Result<Self> {
        if bytes.len() < 8 + 1 + 32 + 8 + 3 * 8 + ML_DSA_SIG_LEN + 32
            || bytes.len() > MAX_CORRELATION_CONTRIBUTION_BYTES
        {
            return Err(CorrelationError::AllocationCeiling);
        }
        let content_end = bytes.len() - 32;
        if bytes[content_end..] != wire_checksum(&bytes[..content_end]) {
            return Err(CorrelationError::MalformedWire("contribution checksum"));
        }
        let mut input = Reader::new(&bytes[..content_end]);
        if input.array::<8>()? != *CONTRIBUTION_MAGIC || input.u8()? != VERSION {
            return Err(CorrelationError::MalformedWire("contribution version"));
        }
        let session_digest = input.array::<32>()?;
        if session_digest != session.digest {
            return Err(CorrelationError::SessionMismatch);
        }
        let party = input.usize()?;
        if party >= DISTRIBUTED_BFV_PARTIES {
            return Err(CorrelationError::InvalidParty { party });
        }
        let a = parse_ciphertext(input.bytes(MAX_CORRELATION_CONTRIBUTION_BYTES)?, params)?;
        let b = parse_ciphertext(input.bytes(MAX_CORRELATION_CONTRIBUTION_BYTES)?, params)?;
        let mask = parse_ciphertext(input.bytes(MAX_CORRELATION_CONTRIBUTION_BYTES)?, params)?;
        let signature = input.take(ML_DSA_SIG_LEN)?.to_vec();
        input.finish()?;
        let message = contribution_signing_message(session_digest, party, &a, &b, &mask);
        if !ml_dsa_verify(
            &session.roster[party],
            SIGNATURE_CONTEXT,
            &message,
            &signature,
        ) {
            return Err(CorrelationError::InvalidSignature { party });
        }
        let contribution = Self {
            session_digest,
            party,
            a,
            b,
            mask,
            signature,
        };
        if contribution.to_wire_bytes()? != bytes {
            return Err(CorrelationError::MalformedWire("noncanonical contribution"));
        }
        Ok(contribution)
    }
}

fn validate_private_bits(
    party: usize,
    vector: &'static str,
    bits: &[u8],
    expected: usize,
) -> Result<()> {
    if bits.len() != expected {
        return Err(CorrelationError::ShapeMismatch);
    }
    if let Some((index, _)) = bits.iter().enumerate().find(|(_, bit)| **bit > 1) {
        return Err(CorrelationError::NonBit {
            party,
            vector,
            index,
        });
    }
    Ok(())
}

fn encrypt_bits(
    bits: &[u8],
    params: &BfvParams,
    collective: &CollectivePublicKey,
) -> Result<LeanCiphertext> {
    let mut slots = vec![0u64; params.degree()];
    for (slot, bit) in slots.iter_mut().zip(bits) {
        *slot = u64::from(*bit);
    }
    let pt = Plaintext::try_encode(&slots, Encoding::simd(), params.arc())
        .map_err(|_| CorrelationError::Crypto("BFV bit encoding"))?;
    let mut rng = rand_09::rng();
    let ct = collective
        .pk
        .try_encrypt(&pt, &mut rng)
        .map_err(|_| CorrelationError::Crypto("BFV bit encryption"))?;
    parse_ciphertext(&ct.to_bytes(), params)
}

fn parse_ciphertext(bytes: &[u8], params: &BfvParams) -> Result<LeanCiphertext> {
    let lean = LeanCiphertext::from_fhe_bytes(bytes, params.moduli(), params.degree(), 1)
        .map_err(|_| CorrelationError::MalformedWire("BFV ciphertext"))?;
    if lean.to_fhe_bytes() != bytes {
        return Err(CorrelationError::MalformedWire(
            "noncanonical BFV ciphertext",
        ));
    }
    Ciphertext::from_bytes(bytes, params.arc())
        .map_err(|_| CorrelationError::MalformedWire("BFV ciphertext parameters"))?;
    Ok(lean)
}

/// Public-only correlation worker. It accepts no plaintext share or party state.
pub struct CorrelationCoordinator {
    session: CorrelationSession,
    params: BfvParams,
    contributions: BTreeMap<usize, (EncryptedBitContribution, Vec<u8>)>,
}

impl CorrelationCoordinator {
    pub fn new(session: CorrelationSession, params: BfvParams) -> Self {
        Self {
            session,
            params,
            contributions: BTreeMap::new(),
        }
    }

    pub fn accept_wire(&mut self, wire: Vec<u8>) -> Result<()> {
        let contribution =
            EncryptedBitContribution::from_wire_bytes(&wire, &self.session, &self.params)?;
        let party = contribution.party;
        if self
            .contributions
            .insert(party, (contribution, wire))
            .is_some()
        {
            return Err(CorrelationError::DuplicateParty { party });
        }
        Ok(())
    }

    /// Evaluate the exact encrypted Boolean circuit and return its masked
    /// ciphertext. No threshold share or plaintext opening exists yet.
    pub fn finish(self, relin_key: &RelinearizationKey) -> Result<PendingCorrelation> {
        if hash_bytes(&relin_key.to_bytes()) != self.session.relin_key_digest {
            return Err(CorrelationError::RelinMismatch);
        }
        for party in 0..DISTRIBUTED_BFV_PARTIES {
            if !self.contributions.contains_key(&party) {
                return Err(CorrelationError::MissingParty { party });
            }
        }
        let ordered = self.contributions.into_values().collect::<Vec<_>>();
        let engine = MulEngine::new(relin_key, self.params.arc())
            .map_err(|_| CorrelationError::Crypto("BFV multiplicator"))?;
        let two = plaintext_constant(2, &self.params)?;
        let a = xor_encrypted(
            &ordered[0].0.a,
            &ordered[1].0.a,
            &engine,
            &two,
            &self.params,
        )?;
        let b = xor_encrypted(
            &ordered[0].0.b,
            &ordered[1].0.b,
            &engine,
            &two,
            &self.params,
        )?;
        let c = engine
            .multiply(&a, &b)
            .map_err(|_| CorrelationError::Crypto("encrypted Beaver product"))?;
        let r = xor_encrypted(
            &ordered[0].0.mask,
            &ordered[1].0.mask,
            &engine,
            &two,
            &self.params,
        )?;
        let z = xor_bounded(&c, &r, &engine, &two)?;
        let target = parse_ciphertext(&z.ct.to_bytes(), &self.params)?;
        Ok(PendingCorrelation {
            session: self.session,
            params: self.params,
            contribution_wires: ordered.into_iter().map(|(_, wire)| wire).collect(),
            target,
        })
    }
}

fn plaintext_constant(value: u64, params: &BfvParams) -> Result<Plaintext> {
    Plaintext::try_encode(
        &vec![value; params.degree()],
        Encoding::simd(),
        params.arc(),
    )
    .map_err(|_| CorrelationError::Crypto("BFV plaintext constant"))
}

fn xor_encrypted(
    lhs: &LeanCiphertext,
    rhs: &LeanCiphertext,
    engine: &MulEngine,
    two: &Plaintext,
    params: &BfvParams,
) -> Result<BoundedCiphertext> {
    let lhs = Ciphertext::from_bytes(&lhs.to_fhe_bytes(), params.arc())
        .map_err(|_| CorrelationError::MalformedWire("left XOR ciphertext"))?;
    let rhs = Ciphertext::from_bytes(&rhs.to_fhe_bytes(), params.arc())
        .map_err(|_| CorrelationError::MalformedWire("right XOR ciphertext"))?;
    xor_bounded(
        &BoundedCiphertext::new(lhs, 1),
        &BoundedCiphertext::new(rhs, 1),
        engine,
        two,
    )
}

fn xor_bounded(
    lhs: &BoundedCiphertext,
    rhs: &BoundedCiphertext,
    engine: &MulEngine,
    two: &Plaintext,
) -> Result<BoundedCiphertext> {
    let product = engine
        .multiply(lhs, rhs)
        .map_err(|_| CorrelationError::Crypto("encrypted XOR product"))?;
    let twice_product = &product.ct * two;
    let sum = &lhs.ct + &rhs.ct;
    Ok(BoundedCiphertext::new(&sum - &twice_product, 1))
}

/// Encrypted masked product awaiting exact roster decryption shares.
pub struct PendingCorrelation {
    session: CorrelationSession,
    params: BfvParams,
    contribution_wires: Vec<Vec<u8>>,
    target: LeanCiphertext,
}

impl PendingCorrelation {
    pub fn target(&self) -> &LeanCiphertext {
        &self.target
    }

    /// Convenience party-side action; only the party-owned threshold state is
    /// accepted, and only its smudged public share leaves this call.
    pub fn decryption_share(&self, party: &ThresholdParty) -> Result<Vec<u8>> {
        if party.party() >= DISTRIBUTED_BFV_PARTIES {
            return Err(CorrelationError::InvalidParty {
                party: party.party(),
            });
        }
        party
            .partial_decrypt(&self.target, MIN_SMUDGE_BITS)
            .map(|share| share.to_wire_bytes())
            .map_err(|_| CorrelationError::Crypto("threshold decryption share"))
    }

    /// Combine exactly one canonical share per roster member and expose only
    /// the padded bit vector `z = c XOR r`.
    pub fn open(self, share_wires: Vec<Vec<u8>>) -> Result<OpenedCorrelation> {
        if share_wires.len() != DISTRIBUTED_BFV_PARTIES {
            return Err(CorrelationError::ShapeMismatch);
        }
        let mut shares = Vec::with_capacity(DISTRIBUTED_BFV_PARTIES);
        for (expected_party, wire) in share_wires.iter().enumerate() {
            if wire.len() > MAX_CORRELATION_TRANSCRIPT_BYTES {
                return Err(CorrelationError::AllocationCeiling);
            }
            let share = DecryptShare::from_wire_bytes(wire, &self.params)
                .map_err(|_| CorrelationError::MalformedWire("decrypt share"))?;
            if share.party() != expected_party || share.ciphertext() != &self.target {
                return Err(CorrelationError::SessionMismatch);
            }
            shares.push(share);
        }
        let opened = threshold::combine(&shares, &self.params)
            .map_err(|_| CorrelationError::InvalidMaskedOpening)?;
        if opened[..self.session.triples]
            .iter()
            .any(|value| *value > 1)
            || opened[self.session.triples..]
                .iter()
                .any(|value| *value != 0)
        {
            return Err(CorrelationError::InvalidMaskedOpening);
        }
        Ok(OpenedCorrelation {
            session: self.session,
            contribution_wires: self.contribution_wires,
            target: self.target,
            share_wires,
            masked_bits: opened[..shares[0].ciphertext().degree.min(opened.len())].to_vec(),
        })
    }
}

/// Public masked opening plus the replayable public cryptographic transcript.
pub struct OpenedCorrelation {
    session: CorrelationSession,
    contribution_wires: Vec<Vec<u8>>,
    target: LeanCiphertext,
    share_wires: Vec<Vec<u8>>,
    masked_bits: Vec<u64>,
}

impl OpenedCorrelation {
    pub fn masked_bits(&self) -> &[u64] {
        &self.masked_bits[..self.session.triples]
    }

    pub fn session_digest(&self) -> [u8; 32] {
        self.session.digest
    }

    /// Seal the public transcript only after each party has locally derived
    /// and committed its secret output row.
    pub fn seal(
        self,
        commitments: &[PartyOutputCommitment],
    ) -> Result<(CorrelationTranscript, CorrelationCertificate)> {
        if commitments.len() != DISTRIBUTED_BFV_PARTIES {
            return Err(CorrelationError::ShapeMismatch);
        }
        for (expected, commitment) in commitments.iter().enumerate() {
            if commitment.session_digest != self.session.digest
                || commitment.party != expected
                || commitment.digest == [0; 32]
            {
                return Err(CorrelationError::OutputCommitmentMismatch { party: expected });
            }
        }
        let contribution_digests = array_digests(&self.contribution_wires)?;
        let opening_share_digests = array_digests(&self.share_wires)?;
        let masked_ciphertext_digest = hash_bytes(&self.target.to_fhe_bytes());
        let masked_opening_digest = hash_u64_slice(self.masked_bits());
        let output_commitments = [commitments[0].digest, commitments[1].digest];
        let mut certificate = CorrelationCertificate {
            session_digest: self.session.digest,
            dkg_digest: self.session.dkg_digest,
            relin_key_digest: self.session.relin_key_digest,
            contribution_digests,
            masked_ciphertext_digest,
            opening_share_digests,
            masked_opening_digest,
            output_commitments,
            triples: self.session.triples,
            transcript_digest: [0; 32],
        };
        certificate.transcript_digest = certificate_digest(&certificate);
        let transcript = CorrelationTranscript {
            contribution_wires: self.contribution_wires,
            masked_ciphertext: self.target,
            share_wires: self.share_wires,
            certificate: certificate.clone(),
        };
        // Re-run the cheap structural portion before releasing the certificate.
        certificate.validate(&self.session)?;
        Ok((transcript, certificate))
    }
}

impl CorrelationPartyState {
    /// Derive this party's private Beaver row from the public masked opening.
    /// The salt remains with the party and is required to open the public row
    /// commitment when the existing sacrifice adapter consumes the candidates.
    pub fn derive_output(
        self,
        opening: &OpenedCorrelation,
        salt: [u8; 32],
    ) -> Result<CorrelationPartyOutput> {
        if self.session_digest != opening.session.digest || salt == [0; 32] {
            return Err(CorrelationError::SessionMismatch);
        }
        let mut triples = Vec::with_capacity(opening.session.triples);
        for index in 0..opening.session.triples {
            let z = u8::try_from(opening.masked_bits[index])
                .map_err(|_| CorrelationError::InvalidMaskedOpening)?;
            let c = if self.party == 0 {
                z ^ self.mask[index]
            } else {
                self.mask[index]
            };
            triples.push(
                BinaryTripleShare::new(self.a[index], self.b[index], c)
                    .map_err(|_| CorrelationError::InvalidMaskedOpening)?,
            );
        }
        let digest = output_commitment(self.session_digest, self.party, salt, &triples)?;
        Ok(CorrelationPartyOutput {
            session_digest: self.session_digest,
            party: self.party,
            salt,
            triples,
            digest,
        })
    }
}

/// Party-owned secret candidate row. No `Clone`/`Debug` and no serialization.
pub struct CorrelationPartyOutput {
    session_digest: [u8; 32],
    party: usize,
    salt: [u8; 32],
    triples: Vec<BinaryTripleShare>,
    digest: [u8; 32],
}

impl CorrelationPartyOutput {
    pub fn commitment(&self) -> PartyOutputCommitment {
        PartyOutputCommitment {
            session_digest: self.session_digest,
            party: self.party,
            digest: self.digest,
        }
    }

    /// Consume the private row at the sacrifice adapter boundary.
    pub fn into_candidate_parts(self) -> ([u8; 32], Vec<BinaryTripleShare>) {
        (self.salt, self.triples)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartyOutputCommitment {
    session_digest: [u8; 32],
    party: usize,
    digest: [u8; 32],
}

/// Compact public certificate for the exact replay transcript and hidden rows.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CorrelationCertificate {
    session_digest: [u8; 32],
    dkg_digest: [u8; 32],
    relin_key_digest: [u8; 32],
    contribution_digests: [[u8; 32]; DISTRIBUTED_BFV_PARTIES],
    masked_ciphertext_digest: [u8; 32],
    opening_share_digests: [[u8; 32]; DISTRIBUTED_BFV_PARTIES],
    masked_opening_digest: [u8; 32],
    output_commitments: [[u8; 32]; DISTRIBUTED_BFV_PARTIES],
    triples: usize,
    transcript_digest: [u8; 32],
}

impl CorrelationCertificate {
    pub fn transcript_digest(&self) -> [u8; 32] {
        self.transcript_digest
    }

    pub fn output_commitment(&self, party: usize) -> Option<[u8; 32]> {
        self.output_commitments.get(party).copied()
    }

    pub fn validate(&self, session: &CorrelationSession) -> Result<()> {
        if self.session_digest != session.digest
            || self.dkg_digest != session.dkg_digest
            || self.relin_key_digest != session.relin_key_digest
            || self.triples != session.triples
            || self
                .contribution_digests
                .iter()
                .any(|digest| *digest == [0; 32])
            || self.masked_ciphertext_digest == [0; 32]
            || self
                .opening_share_digests
                .iter()
                .any(|digest| *digest == [0; 32])
            || self.masked_opening_digest == [0; 32]
            || self
                .output_commitments
                .iter()
                .any(|digest| *digest == [0; 32])
            || self.transcript_digest != certificate_digest(self)
        {
            return Err(CorrelationError::SessionMismatch);
        }
        Ok(())
    }

    pub fn to_wire_bytes(&self) -> Result<Vec<u8>> {
        let mut out = Vec::with_capacity(CORRELATION_CERTIFICATE_BYTES);
        out.extend_from_slice(CERTIFICATE_MAGIC);
        out.push(VERSION);
        encode_certificate_fields(&mut out, self)?;
        out.extend_from_slice(&self.transcript_digest);
        if out.len() != CORRELATION_CERTIFICATE_BYTES {
            return Err(CorrelationError::MalformedWire("certificate size"));
        }
        Ok(out)
    }

    pub fn from_wire_bytes(bytes: &[u8], session: &CorrelationSession) -> Result<Self> {
        if bytes.len() != CORRELATION_CERTIFICATE_BYTES {
            return Err(CorrelationError::MalformedWire("certificate size"));
        }
        let mut input = Reader::new(bytes);
        if input.array::<8>()? != *CERTIFICATE_MAGIC || input.u8()? != VERSION {
            return Err(CorrelationError::MalformedWire("certificate version"));
        }
        let certificate = Self {
            session_digest: input.array()?,
            dkg_digest: input.array()?,
            relin_key_digest: input.array()?,
            contribution_digests: [input.array()?, input.array()?],
            masked_ciphertext_digest: input.array()?,
            opening_share_digests: [input.array()?, input.array()?],
            masked_opening_digest: input.array()?,
            output_commitments: [input.array()?, input.array()?],
            triples: input.usize()?,
            transcript_digest: input.array()?,
        };
        input.finish()?;
        certificate.validate(session)?;
        if certificate.to_wire_bytes()? != bytes {
            return Err(CorrelationError::MalformedWire("noncanonical certificate"));
        }
        Ok(certificate)
    }
}

/// Complete public replay material. It contains no bit share, mask, or output salt.
pub struct CorrelationTranscript {
    contribution_wires: Vec<Vec<u8>>,
    masked_ciphertext: LeanCiphertext,
    share_wires: Vec<Vec<u8>>,
    certificate: CorrelationCertificate,
}

impl CorrelationTranscript {
    pub fn certificate(&self) -> &CorrelationCertificate {
        &self.certificate
    }

    /// Recompute the encrypted circuit, exact masked ciphertext, threshold
    /// opening, and every certificate digest. This does not add the two missing
    /// malicious-share proofs named in the module documentation.
    pub fn verify(
        &self,
        session: &CorrelationSession,
        params: &BfvParams,
        relin_key: &RelinearizationKey,
    ) -> Result<()> {
        self.certificate.validate(session)?;
        if hash_bytes(&relin_key.to_bytes()) != session.relin_key_digest {
            return Err(CorrelationError::RelinMismatch);
        }
        if array_digests(&self.contribution_wires)? != self.certificate.contribution_digests
            || array_digests(&self.share_wires)? != self.certificate.opening_share_digests
            || hash_bytes(&self.masked_ciphertext.to_fhe_bytes())
                != self.certificate.masked_ciphertext_digest
        {
            return Err(CorrelationError::SessionMismatch);
        }

        let mut coordinator = CorrelationCoordinator::new(session.clone(), params.clone());
        for wire in &self.contribution_wires {
            coordinator.accept_wire(wire.clone())?;
        }
        let pending = coordinator.finish(relin_key)?;
        if pending.target != self.masked_ciphertext {
            return Err(CorrelationError::SessionMismatch);
        }
        let shares = self
            .share_wires
            .iter()
            .map(|wire| {
                DecryptShare::from_wire_bytes(wire, params)
                    .map_err(|_| CorrelationError::MalformedWire("decrypt share"))
            })
            .collect::<Result<Vec<_>>>()?;
        if shares.len() != DISTRIBUTED_BFV_PARTIES {
            return Err(CorrelationError::ShapeMismatch);
        }
        for (party, share) in shares.iter().enumerate() {
            if share.party() != party || share.ciphertext() != &self.masked_ciphertext {
                return Err(CorrelationError::SessionMismatch);
            }
        }
        let opened = threshold::combine(&shares, params)
            .map_err(|_| CorrelationError::InvalidMaskedOpening)?;
        if opened[..session.triples].iter().any(|value| *value > 1)
            || opened[session.triples..].iter().any(|value| *value != 0)
            || hash_u64_slice(&opened[..session.triples]) != self.certificate.masked_opening_digest
        {
            return Err(CorrelationError::InvalidMaskedOpening);
        }
        Ok(())
    }

    pub fn to_wire_bytes(&self) -> Result<Vec<u8>> {
        let target = self.masked_ciphertext.to_fhe_bytes();
        let cert = self.certificate.to_wire_bytes()?;
        let mut out = Vec::new();
        out.extend_from_slice(TRANSCRIPT_MAGIC);
        out.push(VERSION);
        out.extend_from_slice(&self.certificate.session_digest);
        put_usize(&mut out, self.contribution_wires.len())?;
        for wire in &self.contribution_wires {
            put_bytes(&mut out, wire)?;
        }
        put_bytes(&mut out, &target)?;
        put_usize(&mut out, self.share_wires.len())?;
        for wire in &self.share_wires {
            put_bytes(&mut out, wire)?;
        }
        put_bytes(&mut out, &cert)?;
        if out
            .len()
            .checked_add(32)
            .is_none_or(|len| len > MAX_CORRELATION_TRANSCRIPT_BYTES)
        {
            return Err(CorrelationError::AllocationCeiling);
        }
        out.extend_from_slice(&wire_checksum(&out));
        Ok(out)
    }

    pub fn from_wire_bytes(
        bytes: &[u8],
        session: &CorrelationSession,
        params: &BfvParams,
        relin_key: &RelinearizationKey,
    ) -> Result<Self> {
        if bytes.len() < 8 + 1 + 32 + 8 * 5 + 32 || bytes.len() > MAX_CORRELATION_TRANSCRIPT_BYTES {
            return Err(CorrelationError::AllocationCeiling);
        }
        let content_end = bytes.len() - 32;
        if bytes[content_end..] != wire_checksum(&bytes[..content_end]) {
            return Err(CorrelationError::MalformedWire("transcript checksum"));
        }
        let mut input = Reader::new(&bytes[..content_end]);
        if input.array::<8>()? != *TRANSCRIPT_MAGIC || input.u8()? != VERSION {
            return Err(CorrelationError::MalformedWire("transcript version"));
        }
        if input.array::<32>()? != session.digest {
            return Err(CorrelationError::SessionMismatch);
        }
        if input.usize()? != DISTRIBUTED_BFV_PARTIES {
            return Err(CorrelationError::ShapeMismatch);
        }
        let mut contribution_wires = Vec::with_capacity(DISTRIBUTED_BFV_PARTIES);
        for _ in 0..DISTRIBUTED_BFV_PARTIES {
            contribution_wires.push(input.bytes(MAX_CORRELATION_CONTRIBUTION_BYTES)?.to_vec());
        }
        let target_bytes = input.bytes(MAX_CORRELATION_CONTRIBUTION_BYTES)?;
        let masked_ciphertext = parse_ciphertext(target_bytes, params)?;
        if input.usize()? != DISTRIBUTED_BFV_PARTIES {
            return Err(CorrelationError::ShapeMismatch);
        }
        let mut share_wires = Vec::with_capacity(DISTRIBUTED_BFV_PARTIES);
        for _ in 0..DISTRIBUTED_BFV_PARTIES {
            share_wires.push(input.bytes(MAX_CORRELATION_TRANSCRIPT_BYTES)?.to_vec());
        }
        let certificate = CorrelationCertificate::from_wire_bytes(
            input.bytes(CORRELATION_CERTIFICATE_BYTES)?,
            session,
        )?;
        input.finish()?;
        let transcript = Self {
            contribution_wires,
            masked_ciphertext,
            share_wires,
            certificate,
        };
        transcript.verify(session, params, relin_key)?;
        if transcript.to_wire_bytes()? != bytes {
            return Err(CorrelationError::MalformedWire("noncanonical transcript"));
        }
        Ok(transcript)
    }
}

fn contribution_signing_message(
    session_digest: [u8; 32],
    party: usize,
    a: &LeanCiphertext,
    b: &LeanCiphertext,
    mask: &LeanCiphertext,
) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(CONTRIBUTION_DOMAIN);
    hash.update(session_digest);
    hash.update((party as u64).to_be_bytes());
    for ciphertext in [a, b, mask] {
        let wire = ciphertext.to_fhe_bytes();
        hash.update((wire.len() as u64).to_be_bytes());
        hash.update(hash_bytes(&wire));
    }
    hash.finalize().into()
}

#[allow(clippy::too_many_arguments)]
fn session_digest(
    nonce: [u8; 32],
    keygen: &KeygenSession,
    dkg_digest: [u8; 32],
    collective_key_digest: [u8; 32],
    relin_session_id: [u8; 32],
    relin_key_digest: [u8; 32],
    roster: &[Vec<u8>],
    triples: usize,
    params: &BfvParams,
) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(SESSION_DOMAIN);
    hash.update(nonce);
    hash.update((keygen.n_parties() as u64).to_be_bytes());
    hash.update(keygen.crp_seed());
    hash.update(dkg_digest);
    hash.update(collective_key_digest);
    hash.update(relin_session_id);
    hash.update(relin_key_digest);
    hash.update((roster.len() as u64).to_be_bytes());
    for key in roster {
        hash.update((key.len() as u64).to_be_bytes());
        hash.update(key);
    }
    hash.update((triples as u64).to_be_bytes());
    hash.update((params.degree() as u64).to_be_bytes());
    hash.update(params.plaintext_modulus().to_be_bytes());
    hash.update((params.moduli().len() as u64).to_be_bytes());
    for modulus in params.moduli() {
        hash.update(modulus.to_be_bytes());
    }
    hash.finalize().into()
}

fn threshold_relin_public_key_digest(public_key_bytes: &[u8]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(b"fhegg/threshold/relin-public-key/v1");
    hash.update(public_key_bytes);
    hash.finalize().into()
}

fn output_commitment(
    session_digest: [u8; 32],
    party: usize,
    salt: [u8; 32],
    triples: &[BinaryTripleShare],
) -> Result<[u8; 32]> {
    let mut hash = Sha256::new();
    hash.update(OUTPUT_DOMAIN);
    hash.update(session_digest);
    hash.update((party as u64).to_be_bytes());
    hash.update((triples.len() as u64).to_be_bytes());
    hash.update(salt);
    for triple in triples.iter().copied() {
        hash.update(triple.into_bits());
    }
    Ok(hash.finalize().into())
}

fn certificate_digest(certificate: &CorrelationCertificate) -> [u8; 32] {
    let mut fields = Vec::with_capacity(CORRELATION_CERTIFICATE_BYTES - 32);
    fields.extend_from_slice(CERTIFICATE_DOMAIN);
    encode_certificate_fields(&mut fields, certificate)
        .expect("validated certificate fields fit canonical integers");
    hash_bytes(&fields)
}

fn encode_certificate_fields(
    out: &mut Vec<u8>,
    certificate: &CorrelationCertificate,
) -> Result<()> {
    out.extend_from_slice(&certificate.session_digest);
    out.extend_from_slice(&certificate.dkg_digest);
    out.extend_from_slice(&certificate.relin_key_digest);
    for digest in &certificate.contribution_digests {
        out.extend_from_slice(digest);
    }
    out.extend_from_slice(&certificate.masked_ciphertext_digest);
    for digest in &certificate.opening_share_digests {
        out.extend_from_slice(digest);
    }
    out.extend_from_slice(&certificate.masked_opening_digest);
    for digest in &certificate.output_commitments {
        out.extend_from_slice(digest);
    }
    put_usize(out, certificate.triples)?;
    Ok(())
}

fn array_digests(wires: &[Vec<u8>]) -> Result<[[u8; 32]; DISTRIBUTED_BFV_PARTIES]> {
    if wires.len() != DISTRIBUTED_BFV_PARTIES {
        return Err(CorrelationError::ShapeMismatch);
    }
    Ok([hash_bytes(&wires[0]), hash_bytes(&wires[1])])
}

fn hash_bytes(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn hash_u64_slice(values: &[u64]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update((values.len() as u64).to_be_bytes());
    for value in values {
        hash.update(value.to_be_bytes());
    }
    hash.finalize().into()
}

fn wire_checksum(content: &[u8]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(CHECKSUM_DOMAIN);
    hash.update((content.len() as u64).to_be_bytes());
    hash.update(content);
    hash.finalize().into()
}

fn put_usize(out: &mut Vec<u8>, value: usize) -> Result<()> {
    out.extend_from_slice(
        &u64::try_from(value)
            .map_err(|_| CorrelationError::MalformedWire("integer exceeds u64"))?
            .to_be_bytes(),
    );
    Ok(())
}

fn put_bytes(out: &mut Vec<u8>, bytes: &[u8]) -> Result<()> {
    put_usize(out, bytes.len())?;
    out.extend_from_slice(bytes);
    Ok(())
}

struct Reader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

#[cfg(test)]
mod tests {
    use std::process::Command;
    use std::time::Duration;

    use super::*;
    use crate::joint_beacon::{
        finalize_beacon, prepare_commitment, seal_commitments, JointBeaconContext,
        JointBeaconTranscript,
    };
    use crate::threshold::relin::{generate_relinearization_key, RelinKeySession};

    const CHILD_ENV: &str = "DREGG_FHTRI005_BFV_CHILD";

    struct Fixture {
        params: BfvParams,
        keygen: KeygenSession,
        dkg_wires: Vec<Vec<u8>>,
        collective: CollectivePublicKey,
        threshold_parties: Vec<ThresholdParty>,
        relin_session: RelinKeySession,
        relin_key: RelinearizationKey,
        signing_keys: Vec<MlDsaKey>,
    }

    fn fixture() -> Fixture {
        let params = BfvParams::fold_set();
        let keygen =
            KeygenSession::from_seed(DISTRIBUTED_BFV_PARTIES, [0x41; 32]).expect("keygen session");
        let mut dkg_wires = Vec::new();
        let mut threshold_parties = Vec::new();
        let mut keygen_coordinator = KeygenCoordinator::new(keygen.clone(), params.clone());
        for party in 0..DISTRIBUTED_BFV_PARTIES {
            let mut custody = [0x51 + party as u8; 32];
            custody[31] ^= party as u8;
            let (state, contribution) =
                ThresholdParty::join_seeded(&keygen, party, &params, &custody).expect("party DKG");
            dkg_wires.push(contribution.to_wire_bytes());
            keygen_coordinator
                .accept(contribution)
                .expect("DKG contribution");
            threshold_parties.push(state);
        }
        let collective = keygen_coordinator.finish().expect("collective key");
        let relin_session = RelinKeySession::from_public_entropy(
            &keygen,
            &collective,
            [0x61; 32],
            Duration::from_secs(120),
        )
        .expect("relin session");
        let relin_key =
            generate_relinearization_key(&relin_session, &params, &collective, &threshold_parties)
                .expect("multiparty relin key");
        let signing_keys = (0..DISTRIBUTED_BFV_PARTIES)
            .map(|party| MlDsaKey::from_ed25519_seed(&[0x71 + party as u8; 32]))
            .collect();
        Fixture {
            params,
            keygen,
            dkg_wires,
            collective,
            threshold_parties,
            relin_session,
            relin_key,
            signing_keys,
        }
    }

    fn session(fx: &Fixture, nonce: u8, triples: usize) -> CorrelationSession {
        CorrelationSession::new(
            [nonce; 32],
            &fx.keygen,
            &fx.dkg_wires,
            &fx.collective,
            &fx.relin_session,
            &fx.relin_key,
            fx.signing_keys.iter().map(MlDsaKey::public_bytes).collect(),
            triples,
            &fx.params,
        )
        .expect("correlation session")
    }

    /// Default test entry runs the cryptographic worker in a child with the
    /// repository's explicit fallback acknowledgement. Deployed archive-linked
    /// hosts install the Lean ML-DSA cores instead; the child override is test-only.
    #[test]
    fn distributed_bfv_correlation_end_to_end_and_hostile_replay_suite() {
        let status = Command::new(std::env::current_exe().expect("current test binary"))
            .arg("--exact")
            .arg("distributed_bfv_correlation::tests::distributed_bfv_correlation_worker")
            .arg("--nocapture")
            .env(CHILD_ENV, "1")
            .env("DREGG_ALLOW_UNAUDITED_PQ", "1")
            .status()
            .expect("spawn acknowledged ML-DSA worker");
        assert!(status.success(), "FHTRI005 BFV worker failed");
    }

    #[test]
    fn distributed_bfv_correlation_worker() {
        if std::env::var_os(CHILD_ENV).is_none() {
            return;
        }
        assert_eq!(
            std::env::var_os("DREGG_ALLOW_UNAUDITED_PQ").as_deref(),
            Some(std::ffi::OsStr::new("1")),
            "the isolated child must explicitly acknowledge the test-only ML-DSA fallback"
        );
        let fx = fixture();
        let active_session = session(&fx, 0x81, 8);

        let mut reordered_dkg = fx.dkg_wires.clone();
        reordered_dkg.swap(0, 1);
        assert!(matches!(
            CorrelationSession::new(
                [0x80; 32],
                &fx.keygen,
                &reordered_dkg,
                &fx.collective,
                &fx.relin_session,
                &fx.relin_key,
                fx.signing_keys.iter().map(MlDsaKey::public_bytes).collect(),
                8,
                &fx.params,
            ),
            Err(CorrelationError::DkgMismatch)
        ));

        let a0 = vec![0, 0, 1, 1, 0, 1, 0, 1];
        let a1 = vec![0, 1, 0, 1, 1, 0, 1, 0];
        let b0 = vec![0, 1, 0, 1, 1, 0, 0, 1];
        let b1 = vec![0, 0, 1, 1, 0, 1, 1, 0];
        let r0 = vec![1, 0, 1, 0, 1, 0, 1, 0];
        let r1 = vec![0, 1, 1, 0, 0, 1, 0, 1];

        let bad = EncryptedBitContribution::prepare(
            &active_session,
            0,
            vec![0, 0, 1, 2, 0, 1, 0, 1],
            b0.clone(),
            r0.clone(),
            &fx.params,
            &fx.collective,
            &fx.signing_keys[0],
        );
        assert!(matches!(
            bad,
            Err(CorrelationError::NonBit { index: 3, .. })
        ));
        assert!(matches!(
            EncryptedBitContribution::prepare(
                &active_session,
                0,
                a0.clone(),
                b0.clone(),
                r0.clone(),
                &fx.params,
                &fx.collective,
                &fx.signing_keys[1],
            ),
            Err(CorrelationError::InvalidSignature { party: 0 })
        ));

        let (state0, contribution0) = EncryptedBitContribution::prepare(
            &active_session,
            0,
            a0,
            b0,
            r0,
            &fx.params,
            &fx.collective,
            &fx.signing_keys[0],
        )
        .expect("party zero contribution");
        let (state1, contribution1) = EncryptedBitContribution::prepare(
            &active_session,
            1,
            a1,
            b1,
            r1,
            &fx.params,
            &fx.collective,
            &fx.signing_keys[1],
        )
        .expect("party one contribution");
        let wire0 = contribution0.to_wire_bytes().expect("wire zero");
        let wire1 = contribution1.to_wire_bytes().expect("wire one");

        // A contribution is exact-session bound and cannot be replayed under
        // another nonce/roster context.
        let replay_session = session(&fx, 0x82, 8);
        assert!(matches!(
            EncryptedBitContribution::from_wire_bytes(&wire0, &replay_session, &fx.params),
            Err(CorrelationError::SessionMismatch)
        ));

        let mut tampered = wire0.clone();
        tampered[80] ^= 1;
        assert!(
            EncryptedBitContribution::from_wire_bytes(&tampered, &active_session, &fx.params)
                .is_err()
        );
        let mut trailed = wire0.clone();
        trailed.push(0);
        assert!(
            EncryptedBitContribution::from_wire_bytes(&trailed, &active_session, &fx.params)
                .is_err()
        );

        let mut duplicate = CorrelationCoordinator::new(active_session.clone(), fx.params.clone());
        duplicate
            .accept_wire(wire0.clone())
            .expect("first party zero");
        assert!(matches!(
            duplicate.accept_wire(wire0.clone()),
            Err(CorrelationError::DuplicateParty { party: 0 })
        ));
        let omitted = duplicate.finish(&fx.relin_key);
        assert!(matches!(
            omitted,
            Err(CorrelationError::MissingParty { party: 1 })
        ));

        let mut coordinator =
            CorrelationCoordinator::new(active_session.clone(), fx.params.clone());
        coordinator
            .accept_wire(wire1)
            .expect("party one out of order");
        coordinator
            .accept_wire(wire0)
            .expect("party zero out of order");
        let pending = coordinator
            .finish(&fx.relin_key)
            .expect("encrypted circuit");
        let share0 = pending
            .decryption_share(&fx.threshold_parties[0])
            .expect("share zero");
        let share1 = pending
            .decryption_share(&fx.threshold_parties[1])
            .expect("share one");

        // Exact party order and exact ciphertext are checked before opening.
        let mut coordinator =
            CorrelationCoordinator::new(active_session.clone(), fx.params.clone());
        coordinator
            .accept_wire(contribution0.to_wire_bytes().expect("wire zero again"))
            .expect("zero again");
        coordinator
            .accept_wire(contribution1.to_wire_bytes().expect("wire one again"))
            .expect("one again");
        let swapped = coordinator.finish(&fx.relin_key).expect("second pending");
        assert!(matches!(
            swapped.open(vec![share1.clone(), share0.clone()]),
            Err(CorrelationError::SessionMismatch)
        ));

        let opened = pending
            .open(vec![share0, share1])
            .expect("masked threshold opening");
        assert!(opened.masked_bits().iter().all(|bit| *bit <= 1));
        let output0 = state0.derive_output(&opened, [0x91; 32]).expect("row zero");
        let output1 = state1.derive_output(&opened, [0x92; 32]).expect("row one");
        let commitments = [output0.commitment(), output1.commitment()];
        let (transcript, certificate) = opened.seal(&commitments).expect("seal transcript");
        assert_eq!(
            certificate.to_wire_bytes().expect("certificate wire").len(),
            CORRELATION_CERTIFICATE_BYTES
        );
        transcript
            .verify(&active_session, &fx.params, &fx.relin_key)
            .expect("public replay");
        let transcript_wire = transcript.to_wire_bytes().expect("transcript wire");
        CorrelationTranscript::from_wire_bytes(
            &transcript_wire,
            &active_session,
            &fx.params,
            &fx.relin_key,
        )
        .expect("strict transcript roundtrip");

        // Protocol type separation is global, not merely contextual: neither
        // FHTRI005 parser accepts the other's valid transcript carrier.
        let beacon_context = JointBeaconContext::new(
            [0xa1; 32],
            vec![[0xa2; 32], [0xa3; 32]],
            [0xa4; 64],
            [0xa5; 64],
        )
        .expect("beacon context");
        let (beacon_commit0, beacon_pending0) =
            prepare_commitment(&beacon_context, 0, [0xa6; 64]).expect("beacon commit zero");
        let (beacon_commit1, beacon_pending1) =
            prepare_commitment(&beacon_context, 1, [0xa7; 64]).expect("beacon commit one");
        let beacon_set = seal_commitments(&beacon_context, &[beacon_commit0, beacon_commit1])
            .expect("beacon commitment barrier");
        let beacon_reveal0 = beacon_pending0
            .reveal(&beacon_set)
            .expect("beacon reveal zero");
        let beacon_reveal1 = beacon_pending1
            .reveal(&beacon_set)
            .expect("beacon reveal one");
        let beacon = finalize_beacon(
            &beacon_context,
            &beacon_set,
            &[beacon_reveal0, beacon_reveal1],
        )
        .expect("joint beacon");
        let beacon_wire = beacon.to_canonical_bytes().expect("joint beacon wire");
        assert!(CorrelationTranscript::from_wire_bytes(
            &beacon_wire,
            &active_session,
            &fx.params,
            &fx.relin_key,
        )
        .is_err());
        assert!(JointBeaconTranscript::from_canonical_bytes(&transcript_wire).is_err());

        assert!(CorrelationTranscript::from_wire_bytes(
            &transcript_wire,
            &replay_session,
            &fx.params,
            &fx.relin_key,
        )
        .is_err());

        let (_, row0) = output0.into_candidate_parts();
        let (_, row1) = output1.into_candidate_parts();
        assert_eq!(row0.len(), active_session.triples());
        for gate in 0..active_session.triples() {
            let [a0, b0, c0] = row0[gate].into_bits();
            let [a1, b1, c1] = row1[gate].into_bits();
            let a = a0 ^ a1;
            let b = b0 ^ b1;
            let c = c0 ^ c1;
            assert_eq!(c, a & b, "gate {gate} is not a GF(2) Beaver triple");
        }

        let mut certificate_wire = certificate.to_wire_bytes().expect("certificate wire");
        certificate_wire[200] ^= 1;
        assert!(
            CorrelationCertificate::from_wire_bytes(&certificate_wire, &active_session).is_err()
        );
    }
}

impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn take(&mut self, len: usize) -> Result<&'a [u8]> {
        let end = self
            .offset
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or(CorrelationError::MalformedWire("truncated field"))?;
        let value = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(value)
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N]> {
        self.take(N)?
            .try_into()
            .map_err(|_| CorrelationError::MalformedWire("fixed field"))
    }

    fn u8(&mut self) -> Result<u8> {
        Ok(self.array::<1>()?[0])
    }

    fn usize(&mut self) -> Result<usize> {
        usize::try_from(u64::from_be_bytes(self.array()?))
            .map_err(|_| CorrelationError::MalformedWire("integer exceeds usize"))
    }

    fn bytes(&mut self, max: usize) -> Result<&'a [u8]> {
        let len = self.usize()?;
        if len > max {
            return Err(CorrelationError::AllocationCeiling);
        }
        self.take(len)
    }

    fn finish(self) -> Result<()> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(CorrelationError::MalformedWire("trailing bytes"))
        }
    }
}
