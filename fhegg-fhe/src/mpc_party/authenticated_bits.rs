//! SPDZ-style authentication and batched opening checks for binary shares.
//!
//! Binary PartyMPC values are embedded into `GF(2^128)` and authenticated under
//! two independent additively shared global MAC keys. For every bit `x`, tag
//! shares reconstruct to `alpha*x`. Opening is a commit/reveal protocol; after
//! the opening vector is fixed, an external beacon derives independent field
//! coefficients for each MAC lane. Parties then commit and reveal one batched
//! check share per lane. The verifier accepts only when both lane sums vanish.
//!
//! The two independent 128-bit lanes are intended to retain a 128-bit
//! post-quantum-shaped brute-force floor.  This module pins the algebra and the
//! transcript barriers; it does **not** claim a concrete adversarial reduction
//! for their joint soundness.  This is a portable constant-work reference
//! backend. Carry-less multiply hardware may replace [`Gf128::mul`] only behind
//! exact differential tests.
//!
//! # Exact trust boundary
//!
//! [`trusted_mac_setup_for_bits`] sees the reconstructed bits and both global
//! MAC keys. It is deliberately named trusted setup. Security additionally
//! requires at least one honest party to keep its key share and check opening
//! secret until all check commitments are fixed, commitment binding, and a
//! beacon unpredictable before value-opening commitments are fixed. This
//! module supplies those commit/reveal typestates but not a network, signatures,
//! rollback resistance, or a proof that remote code followed the local API.
//! `FHTRI004` composes this layer with binary sacrifice; the trusted setup and
//! missing quantified reduction remain explicit in that live binding.

use std::fmt;

use rand::{CryptoRng, RngCore};
use sha2::{Digest, Sha512};

/// Two independent 128-bit MAC lanes retain a 128-bit Grover-shaped floor.
pub const AUTHENTICATED_BIT_MAC_LANES: usize = 2;
pub const MAX_AUTHENTICATED_BITS: usize = 16 * 1024 * 1024;

const SETUP_DOMAIN: &[u8] = b"fhegg/party-mpc/authenticated-bits/setup/v1";
const OPENING_COMMIT_DOMAIN: &[u8] = b"fhegg/party-mpc/authenticated-bits/opening-commit/v1";
const OPENING_SET_DOMAIN: &[u8] = b"fhegg/party-mpc/authenticated-bits/opening-set/v1";
const OPENED_DOMAIN: &[u8] = b"fhegg/party-mpc/authenticated-bits/opened/v1";
const CHALLENGE_DOMAIN: &[u8] = b"fhegg/party-mpc/authenticated-bits/challenge/v1";
const CHALLENGE_DIGEST_DOMAIN: &[u8] = b"fhegg/party-mpc/authenticated-bits/challenge-digest/v1";
const CHECK_COMMIT_DOMAIN: &[u8] = b"fhegg/party-mpc/authenticated-bits/check-commit/v1";
const CHECK_SET_DOMAIN: &[u8] = b"fhegg/party-mpc/authenticated-bits/check-set/v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuthenticatedBitError {
    InvalidParameters(&'static str),
    ShapeMismatch,
    InvalidParty { party: usize, n_parties: usize },
    SetupMismatch,
    OpeningCommitmentMismatch { party: usize },
    OpeningSetMismatch,
    ChallengeMismatch,
    CheckCommitmentMismatch { party: usize },
    CheckRejected { lane: usize },
    ArithmeticOverflow,
}

impl fmt::Display for AuthenticatedBitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "authenticated binary share error: {self:?}")
    }
}

impl std::error::Error for AuthenticatedBitError {}

pub type Result<T> = std::result::Result<T, AuthenticatedBitError>;

/// `GF(2^128)` in the polynomial basis modulo
/// `x^128 + x^7 + x^2 + x + 1` (the GHASH polynomial). The representation is
/// internal so byte-order choices cannot leak into a protocol ABI accidentally.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
struct Gf128(u128);

impl Gf128 {
    const ZERO: Self = Self(0);
    const ONE: Self = Self(1);

    fn from_bit(bit: u8) -> Result<Self> {
        match bit {
            0 => Ok(Self::ZERO),
            1 => Ok(Self::ONE),
            _ => Err(AuthenticatedBitError::InvalidParameters(
                "authenticated values must be canonical bits",
            )),
        }
    }

    fn add(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }

    /// Fixed 128-step, branch-free carry-less multiply and polynomial reduce.
    fn mul(self, rhs: Self) -> Self {
        let mut product = 0u128;
        let mut multiplicand = self.0;
        let mut multiplier = rhs.0;
        for _ in 0..128 {
            let multiplier_mask = 0u128.wrapping_sub(multiplier & 1);
            product ^= multiplicand & multiplier_mask;
            let carry_mask = 0u128.wrapping_sub(multiplicand >> 127);
            multiplicand = (multiplicand << 1) ^ (0x87 & carry_mask);
            multiplier >>= 1;
        }
        Self(product)
    }

    fn from_bytes(bytes: [u8; 16]) -> Self {
        Self(u128::from_be_bytes(bytes))
    }

    fn to_bytes(self) -> [u8; 16] {
        self.0.to_be_bytes()
    }

    fn is_zero(self) -> bool {
        self == Self::ZERO
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct MacTag([Gf128; AUTHENTICATED_BIT_MAC_LANES]);

impl MacTag {
    fn zero() -> Self {
        Self([Gf128::ZERO; AUTHENTICATED_BIT_MAC_LANES])
    }

    fn add(self, rhs: Self) -> Self {
        Self(std::array::from_fn(|lane| self.0[lane].add(rhs.0[lane])))
    }

    fn scale(self, bit: u8) -> Result<Self> {
        let scalar = Gf128::from_bit(bit)?;
        Ok(Self(std::array::from_fn(|lane| self.0[lane].mul(scalar))))
    }
}

/// Public identity and shape of one trusted MAC setup.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuthenticatedBitManifest {
    context: [u8; 64],
    setup_root: [u8; 64],
    n_parties: usize,
    values: usize,
}

impl AuthenticatedBitManifest {
    pub fn context(&self) -> [u8; 64] {
        self.context
    }

    pub fn setup_root(&self) -> [u8; 64] {
        self.setup_root
    }

    pub fn n_parties(&self) -> usize {
        self.n_parties
    }

    pub fn values(&self) -> usize {
        self.values
    }

    pub fn mac_lanes(&self) -> usize {
        AUTHENTICATED_BIT_MAC_LANES
    }

    /// Reuse one authenticated setup for a shorter row obtained exclusively
    /// through public linear operations on its source shares.
    ///
    /// The hidden MAC keys and setup root stay unchanged.  Opening transcripts
    /// still bind the exact derived length, so a mask row and a check row cannot
    /// be substituted for one another.  This does not authenticate a fresh
    /// arbitrary row: [`AuthenticatedBitRow::from_linear_shares`] remains the
    /// only constructor for the corresponding custody value.
    pub fn linear_view(&self, values: usize) -> Result<Self> {
        if values == 0 || values > self.values || values > MAX_AUTHENTICATED_BITS {
            return Err(AuthenticatedBitError::InvalidParameters(
                "derived authenticated view has an invalid length",
            ));
        }
        let mut view = self.clone();
        view.values = values;
        Ok(view)
    }
}

/// One authenticated binary share. It can only be created by trusted setup or
/// public linear operations on an existing authenticated share.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct AuthenticatedBitShare {
    setup_root: [u8; 64],
    party: usize,
    value: u8,
    tag: MacTag,
}

impl AuthenticatedBitShare {
    pub fn party(&self) -> usize {
        self.party
    }

    pub fn value_share(&self) -> u8 {
        self.value
    }

    pub fn xor(self, rhs: Self) -> Result<Self> {
        if self.setup_root != rhs.setup_root || self.party != rhs.party {
            return Err(AuthenticatedBitError::SetupMismatch);
        }
        Ok(Self {
            setup_root: self.setup_root,
            party: self.party,
            value: self.value ^ rhs.value,
            tag: self.tag.add(rhs.tag),
        })
    }

    pub fn scale_public(self, bit: u8) -> Result<Self> {
        let _ = Gf128::from_bit(bit)?;
        Ok(Self {
            setup_root: self.setup_root,
            party: self.party,
            value: self.value & bit,
            tag: self.tag.scale(bit)?,
        })
    }
}

/// Party-local authenticated row. Neither values nor tags implement `Debug`.
pub struct AuthenticatedBitRow {
    setup_root: [u8; 64],
    party: usize,
    shares: Vec<AuthenticatedBitShare>,
}

impl AuthenticatedBitRow {
    pub fn party(&self) -> usize {
        self.party
    }

    pub fn len(&self) -> usize {
        self.shares.len()
    }

    pub fn is_empty(&self) -> bool {
        self.shares.is_empty()
    }

    pub fn share(&self, index: usize) -> Option<AuthenticatedBitShare> {
        self.shares.get(index).copied()
    }

    /// Assemble a derived row from values obtained only through authenticated
    /// linear operations. Arbitrary tag construction remains impossible.
    pub fn from_linear_shares(shares: Vec<AuthenticatedBitShare>) -> Result<Self> {
        let Some(first) = shares.first() else {
            return Err(AuthenticatedBitError::InvalidParameters(
                "authenticated row must be nonempty",
            ));
        };
        if shares
            .iter()
            .any(|share| share.setup_root != first.setup_root || share.party != first.party)
        {
            return Err(AuthenticatedBitError::SetupMismatch);
        }
        Ok(Self {
            setup_root: first.setup_root,
            party: first.party,
            shares,
        })
    }

    pub fn prepare_opening(
        &self,
        manifest: &AuthenticatedBitManifest,
        salt: [u8; 32],
    ) -> Result<(BitOpeningCommitment, PendingBitOpening)> {
        validate_row(manifest, self, self.party)?;
        if salt == [0; 32] {
            return Err(AuthenticatedBitError::InvalidParameters(
                "opening commitment salt must be nonzero",
            ));
        }
        let values = self
            .shares
            .iter()
            .map(|share| share.value)
            .collect::<Vec<_>>();
        let digest = opening_commitment_digest(manifest.setup_root, self.party, salt, &values)?;
        Ok((
            BitOpeningCommitment {
                setup_root: manifest.setup_root,
                party: self.party,
                digest,
            },
            PendingBitOpening {
                setup_root: manifest.setup_root,
                party: self.party,
                salt,
                values,
                commitment: digest,
            },
        ))
    }
}

/// Party-local share of the two hidden global MAC keys.
pub struct MacKeyShare {
    setup_root: [u8; 64],
    party: usize,
    alpha: [Gf128; AUTHENTICATED_BIT_MAC_LANES],
}

/// Output of explicit trusted setup.
pub struct TrustedAuthenticatedBitSetup {
    manifest: AuthenticatedBitManifest,
    rows: Vec<AuthenticatedBitRow>,
    key_shares: Vec<MacKeyShare>,
}

impl TrustedAuthenticatedBitSetup {
    pub fn manifest(&self) -> &AuthenticatedBitManifest {
        &self.manifest
    }

    pub fn into_parts(
        self,
    ) -> (
        AuthenticatedBitManifest,
        Vec<AuthenticatedBitRow>,
        Vec<MacKeyShare>,
    ) {
        (self.manifest, self.rows, self.key_shares)
    }
}

/// Trusted dealer authentication of already-additively-shared bits. The input
/// is `[party][value]`; rows must be canonical and equal length.
pub fn trusted_mac_setup_for_bits<R: RngCore + CryptoRng>(
    context: [u8; 64],
    value_shares: Vec<Vec<u8>>,
    rng: &mut R,
) -> Result<TrustedAuthenticatedBitSetup> {
    if context == [0; 64] || value_shares.len() < 2 {
        return Err(AuthenticatedBitError::InvalidParameters(
            "trusted MAC setup requires a nonzero context and at least two parties",
        ));
    }
    let values = value_shares[0].len();
    if values == 0
        || value_shares.iter().any(|row| row.len() != values)
        || value_shares.iter().flatten().any(|bit| *bit > 1)
    {
        return Err(AuthenticatedBitError::ShapeMismatch);
    }
    let total = values
        .checked_mul(value_shares.len())
        .ok_or(AuthenticatedBitError::ArithmeticOverflow)?;
    if total > MAX_AUTHENTICATED_BITS {
        return Err(AuthenticatedBitError::InvalidParameters(
            "authenticated bit batch exceeds allocation ceiling",
        ));
    }

    let mut setup_nonce = [0u8; 64];
    rng.fill_bytes(&mut setup_nonce);
    if setup_nonce == [0; 64] {
        setup_nonce[0] = 1;
    }
    let setup_root = setup_root(context, value_shares.len(), values, setup_nonce)?;
    let manifest = AuthenticatedBitManifest {
        context,
        setup_root,
        n_parties: value_shares.len(),
        values,
    };

    let alpha: [Gf128; AUTHENTICATED_BIT_MAC_LANES] =
        std::array::from_fn(|_| random_nonzero_field(rng));
    let mut alpha_shares = vec![[Gf128::ZERO; AUTHENTICATED_BIT_MAC_LANES]; value_shares.len()];
    for lane in 0..AUTHENTICATED_BIT_MAC_LANES {
        let mut aggregate = Gf128::ZERO;
        for shares in alpha_shares.iter_mut().take(value_shares.len() - 1) {
            let share = random_field(rng);
            shares[lane] = share;
            aggregate = aggregate.add(share);
        }
        alpha_shares[value_shares.len() - 1][lane] = alpha[lane].add(aggregate);
    }

    let reconstructed = (0..values)
        .map(|index| {
            value_shares
                .iter()
                .fold(0u8, |value, row| value ^ row[index])
        })
        .collect::<Vec<_>>();
    let mut tags = vec![vec![MacTag::zero(); values]; value_shares.len()];
    for (index, value) in reconstructed.iter().copied().enumerate() {
        let embedded = Gf128::from_bit(value)?;
        for lane in 0..AUTHENTICATED_BIT_MAC_LANES {
            let target = alpha[lane].mul(embedded);
            let mut aggregate = Gf128::ZERO;
            for party_tags in tags.iter_mut().take(value_shares.len() - 1) {
                let share = random_field(rng);
                party_tags[index].0[lane] = share;
                aggregate = aggregate.add(share);
            }
            tags[value_shares.len() - 1][index].0[lane] = target.add(aggregate);
        }
    }

    let rows = value_shares
        .into_iter()
        .zip(tags)
        .enumerate()
        .map(|(party, (values, tags))| AuthenticatedBitRow {
            setup_root,
            party,
            shares: values
                .into_iter()
                .zip(tags)
                .map(|(value, tag)| AuthenticatedBitShare {
                    setup_root,
                    party,
                    value,
                    tag,
                })
                .collect(),
        })
        .collect::<Vec<_>>();
    let key_shares = alpha_shares
        .into_iter()
        .enumerate()
        .map(|(party, alpha)| MacKeyShare {
            setup_root,
            party,
            alpha,
        })
        .collect();
    Ok(TrustedAuthenticatedBitSetup {
        manifest,
        rows,
        key_shares,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitOpeningCommitment {
    setup_root: [u8; 64],
    party: usize,
    digest: [u8; 64],
}

pub struct PendingBitOpening {
    setup_root: [u8; 64],
    party: usize,
    salt: [u8; 32],
    values: Vec<u8>,
    commitment: [u8; 64],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitOpeningCommitmentSet {
    setup_root: [u8; 64],
    root: [u8; 64],
    commitments: Vec<[u8; 64]>,
}

pub fn seal_opening_commitments(
    manifest: &AuthenticatedBitManifest,
    commitments: &[BitOpeningCommitment],
) -> Result<BitOpeningCommitmentSet> {
    if commitments.len() != manifest.n_parties {
        return Err(AuthenticatedBitError::ShapeMismatch);
    }
    let mut ordered = Vec::with_capacity(commitments.len());
    for (party, commitment) in commitments.iter().enumerate() {
        if commitment.party != party {
            return Err(AuthenticatedBitError::InvalidParty {
                party: commitment.party,
                n_parties: manifest.n_parties,
            });
        }
        if commitment.setup_root != manifest.setup_root {
            return Err(AuthenticatedBitError::SetupMismatch);
        }
        ordered.push(commitment.digest);
    }
    let root = commitment_set_root(OPENING_SET_DOMAIN, manifest.setup_root, &ordered)?;
    Ok(BitOpeningCommitmentSet {
        setup_root: manifest.setup_root,
        root,
        commitments: ordered,
    })
}

pub struct BitOpeningReveal {
    setup_root: [u8; 64],
    commitment_set_root: [u8; 64],
    party: usize,
    salt: [u8; 32],
    values: Vec<u8>,
}

impl PendingBitOpening {
    pub fn reveal(self, set: &BitOpeningCommitmentSet) -> Result<BitOpeningReveal> {
        if self.setup_root != set.setup_root
            || self.party >= set.commitments.len()
            || self.commitment != set.commitments[self.party]
        {
            return Err(AuthenticatedBitError::OpeningSetMismatch);
        }
        Ok(BitOpeningReveal {
            setup_root: self.setup_root,
            commitment_set_root: set.root,
            party: self.party,
            salt: self.salt,
            values: self.values,
        })
    }
}

/// Public reconstructed values after all precommitted opening shares reveal.
pub struct OpenedAuthenticatedBits {
    setup_root: [u8; 64],
    commitment_set_root: [u8; 64],
    values: Vec<u8>,
    digest: [u8; 64],
}

impl OpenedAuthenticatedBits {
    pub fn values(&self) -> &[u8] {
        &self.values
    }

    pub fn digest(&self) -> [u8; 64] {
        self.digest
    }
}

pub fn reconstruct_opened_bits(
    manifest: &AuthenticatedBitManifest,
    set: &BitOpeningCommitmentSet,
    reveals: &[BitOpeningReveal],
) -> Result<OpenedAuthenticatedBits> {
    if set.setup_root != manifest.setup_root
        || reveals.len() != manifest.n_parties
        || set.commitments.len() != manifest.n_parties
    {
        return Err(AuthenticatedBitError::OpeningSetMismatch);
    }
    let mut values = vec![0u8; manifest.values];
    for (party, reveal) in reveals.iter().enumerate() {
        if reveal.party != party {
            return Err(AuthenticatedBitError::InvalidParty {
                party: reveal.party,
                n_parties: manifest.n_parties,
            });
        }
        if reveal.setup_root != manifest.setup_root
            || reveal.commitment_set_root != set.root
            || reveal.values.len() != manifest.values
            || reveal.values.iter().any(|bit| *bit > 1)
        {
            return Err(AuthenticatedBitError::OpeningSetMismatch);
        }
        let digest =
            opening_commitment_digest(manifest.setup_root, party, reveal.salt, &reveal.values)?;
        if digest != set.commitments[party] {
            return Err(AuthenticatedBitError::OpeningCommitmentMismatch { party });
        }
        for (opened, share) in values.iter_mut().zip(&reveal.values) {
            *opened ^= *share;
        }
    }
    let digest = opened_digest(manifest.setup_root, set.root, &values)?;
    Ok(OpenedAuthenticatedBits {
        setup_root: manifest.setup_root,
        commitment_set_root: set.root,
        values,
        digest,
    })
}

pub struct MacBatchChallenge {
    setup_root: [u8; 64],
    opened_digest: [u8; 64],
    digest: [u8; 64],
    coefficients: [Vec<Gf128>; AUTHENTICATED_BIT_MAC_LANES],
}

impl MacBatchChallenge {
    pub fn derive(
        manifest: &AuthenticatedBitManifest,
        opened: &OpenedAuthenticatedBits,
        beacon: [u8; 64],
    ) -> Result<Self> {
        validate_opened(manifest, opened)?;
        if beacon == [0; 64] {
            return Err(AuthenticatedBitError::InvalidParameters(
                "MAC batch beacon must be nonzero",
            ));
        }
        let total = manifest
            .values
            .checked_mul(AUTHENTICATED_BIT_MAC_LANES)
            .ok_or(AuthenticatedBitError::ArithmeticOverflow)?;
        let mut flat = Vec::with_capacity(total);
        let mut counter = 0u64;
        while flat.len() < total {
            let mut hash = Sha512::new();
            hash.update(canonical_domain(CHALLENGE_DOMAIN));
            hash.update(manifest.setup_root);
            hash.update(opened.digest);
            hash.update(beacon);
            hash.update(counter.to_be_bytes());
            let block = hash.finalize();
            for chunk in block.chunks_exact(16) {
                if flat.len() == total {
                    break;
                }
                let bytes: [u8; 16] = chunk
                    .try_into()
                    .map_err(|_| AuthenticatedBitError::ArithmeticOverflow)?;
                flat.push(Gf128::from_bytes(bytes));
            }
            counter = counter
                .checked_add(1)
                .ok_or(AuthenticatedBitError::ArithmeticOverflow)?;
        }
        let coefficients = std::array::from_fn(|lane| {
            let start = lane * manifest.values;
            flat[start..start + manifest.values].to_vec()
        });
        let mut digest = Sha512::new();
        digest.update(canonical_domain(CHALLENGE_DIGEST_DOMAIN));
        digest.update(manifest.setup_root);
        digest.update(opened.digest);
        digest.update(beacon);
        digest.update(checked_u64(manifest.values)?.to_be_bytes());
        for coefficient in &flat {
            digest.update(coefficient.to_bytes());
        }
        Ok(Self {
            setup_root: manifest.setup_root,
            opened_digest: opened.digest,
            digest: digest.finalize().into(),
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
    challenge_digest: [u8; 64],
    party: usize,
    digest: [u8; 64],
}

pub struct PendingMacCheck {
    setup_root: [u8; 64],
    challenge_digest: [u8; 64],
    party: usize,
    salt: [u8; 32],
    sigma: [Gf128; AUTHENTICATED_BIT_MAC_LANES],
    commitment: [u8; 64],
}

pub fn prepare_mac_check(
    manifest: &AuthenticatedBitManifest,
    row: &AuthenticatedBitRow,
    key: &MacKeyShare,
    opened: &OpenedAuthenticatedBits,
    challenge: &MacBatchChallenge,
    salt: [u8; 32],
) -> Result<(MacCheckCommitment, PendingMacCheck)> {
    validate_row(manifest, row, row.party)?;
    validate_key(manifest, key, row.party)?;
    validate_opened(manifest, opened)?;
    validate_challenge(manifest, opened, challenge)?;
    if salt == [0; 32] {
        return Err(AuthenticatedBitError::InvalidParameters(
            "MAC check commitment salt must be nonzero",
        ));
    }
    let mut sigma = [Gf128::ZERO; AUTHENTICATED_BIT_MAC_LANES];
    for lane in 0..AUTHENTICATED_BIT_MAC_LANES {
        for index in 0..manifest.values {
            let opened_value = Gf128::from_bit(opened.values[index])?;
            let local = row.shares[index].tag.0[lane].add(key.alpha[lane].mul(opened_value));
            sigma[lane] = sigma[lane].add(challenge.coefficients[lane][index].mul(local));
        }
    }
    let digest = check_commitment_digest(
        manifest.setup_root,
        challenge.digest,
        row.party,
        salt,
        sigma,
    )?;
    Ok((
        MacCheckCommitment {
            setup_root: manifest.setup_root,
            challenge_digest: challenge.digest,
            party: row.party,
            digest,
        },
        PendingMacCheck {
            setup_root: manifest.setup_root,
            challenge_digest: challenge.digest,
            party: row.party,
            salt,
            sigma,
            commitment: digest,
        },
    ))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MacCheckCommitmentSet {
    setup_root: [u8; 64],
    challenge_digest: [u8; 64],
    root: [u8; 64],
    commitments: Vec<[u8; 64]>,
}

pub fn seal_mac_check_commitments(
    manifest: &AuthenticatedBitManifest,
    challenge: &MacBatchChallenge,
    commitments: &[MacCheckCommitment],
) -> Result<MacCheckCommitmentSet> {
    if challenge.setup_root != manifest.setup_root || commitments.len() != manifest.n_parties {
        return Err(AuthenticatedBitError::ChallengeMismatch);
    }
    let mut ordered = Vec::with_capacity(commitments.len());
    for (party, commitment) in commitments.iter().enumerate() {
        if commitment.party != party {
            return Err(AuthenticatedBitError::InvalidParty {
                party: commitment.party,
                n_parties: manifest.n_parties,
            });
        }
        if commitment.setup_root != manifest.setup_root
            || commitment.challenge_digest != challenge.digest
        {
            return Err(AuthenticatedBitError::ChallengeMismatch);
        }
        ordered.push(commitment.digest);
    }
    let mut hash = Sha512::new();
    hash.update(canonical_domain(CHECK_SET_DOMAIN));
    hash.update(manifest.setup_root);
    hash.update(challenge.digest);
    hash.update(checked_u64(ordered.len())?.to_be_bytes());
    for digest in &ordered {
        hash.update(digest);
    }
    Ok(MacCheckCommitmentSet {
        setup_root: manifest.setup_root,
        challenge_digest: challenge.digest,
        root: hash.finalize().into(),
        commitments: ordered,
    })
}

pub struct MacCheckReveal {
    setup_root: [u8; 64],
    challenge_digest: [u8; 64],
    commitment_set_root: [u8; 64],
    party: usize,
    salt: [u8; 32],
    sigma: [Gf128; AUTHENTICATED_BIT_MAC_LANES],
}

impl PendingMacCheck {
    pub fn reveal(self, set: &MacCheckCommitmentSet) -> Result<MacCheckReveal> {
        if self.setup_root != set.setup_root
            || self.challenge_digest != set.challenge_digest
            || self.party >= set.commitments.len()
            || self.commitment != set.commitments[self.party]
        {
            return Err(AuthenticatedBitError::OpeningSetMismatch);
        }
        Ok(MacCheckReveal {
            setup_root: self.setup_root,
            challenge_digest: self.challenge_digest,
            commitment_set_root: set.root,
            party: self.party,
            salt: self.salt,
            sigma: self.sigma,
        })
    }
}

/// Opaque proof-of-check capability for one public bit vector.
pub struct VerifiedAuthenticatedOpening {
    setup_root: [u8; 64],
    opened_digest: [u8; 64],
    values: Vec<u8>,
}

impl VerifiedAuthenticatedOpening {
    pub fn setup_root(&self) -> [u8; 64] {
        self.setup_root
    }

    pub fn opened_digest(&self) -> [u8; 64] {
        self.opened_digest
    }

    pub fn values(&self) -> &[u8] {
        &self.values
    }
}

pub fn verify_mac_check(
    manifest: &AuthenticatedBitManifest,
    opened: &OpenedAuthenticatedBits,
    challenge: &MacBatchChallenge,
    set: &MacCheckCommitmentSet,
    reveals: &[MacCheckReveal],
) -> Result<VerifiedAuthenticatedOpening> {
    validate_opened(manifest, opened)?;
    validate_challenge(manifest, opened, challenge)?;
    if set.setup_root != manifest.setup_root
        || set.challenge_digest != challenge.digest
        || reveals.len() != manifest.n_parties
        || set.commitments.len() != manifest.n_parties
    {
        return Err(AuthenticatedBitError::OpeningSetMismatch);
    }
    let mut aggregate = [Gf128::ZERO; AUTHENTICATED_BIT_MAC_LANES];
    for (party, reveal) in reveals.iter().enumerate() {
        if reveal.party != party {
            return Err(AuthenticatedBitError::InvalidParty {
                party: reveal.party,
                n_parties: manifest.n_parties,
            });
        }
        if reveal.setup_root != manifest.setup_root
            || reveal.challenge_digest != challenge.digest
            || reveal.commitment_set_root != set.root
        {
            return Err(AuthenticatedBitError::OpeningSetMismatch);
        }
        let digest = check_commitment_digest(
            manifest.setup_root,
            challenge.digest,
            party,
            reveal.salt,
            reveal.sigma,
        )?;
        if digest != set.commitments[party] {
            return Err(AuthenticatedBitError::CheckCommitmentMismatch { party });
        }
        for lane in 0..AUTHENTICATED_BIT_MAC_LANES {
            aggregate[lane] = aggregate[lane].add(reveal.sigma[lane]);
        }
    }
    for (lane, value) in aggregate.into_iter().enumerate() {
        if !value.is_zero() {
            return Err(AuthenticatedBitError::CheckRejected { lane });
        }
    }
    Ok(VerifiedAuthenticatedOpening {
        setup_root: manifest.setup_root,
        opened_digest: opened.digest,
        values: opened.values.clone(),
    })
}

fn validate_row(
    manifest: &AuthenticatedBitManifest,
    row: &AuthenticatedBitRow,
    expected_party: usize,
) -> Result<()> {
    if row.setup_root != manifest.setup_root
        || row.party != expected_party
        || row.party >= manifest.n_parties
        || row.shares.len() != manifest.values
        || row.shares.iter().any(|share| {
            share.setup_root != manifest.setup_root || share.party != row.party || share.value > 1
        })
    {
        return Err(AuthenticatedBitError::SetupMismatch);
    }
    Ok(())
}

fn validate_key(
    manifest: &AuthenticatedBitManifest,
    key: &MacKeyShare,
    expected_party: usize,
) -> Result<()> {
    if key.setup_root != manifest.setup_root
        || key.party != expected_party
        || key.party >= manifest.n_parties
    {
        return Err(AuthenticatedBitError::SetupMismatch);
    }
    Ok(())
}

fn validate_opened(
    manifest: &AuthenticatedBitManifest,
    opened: &OpenedAuthenticatedBits,
) -> Result<()> {
    if opened.setup_root != manifest.setup_root
        || opened.values.len() != manifest.values
        || opened.values.iter().any(|bit| *bit > 1)
    {
        return Err(AuthenticatedBitError::SetupMismatch);
    }
    let digest = opened_digest(
        manifest.setup_root,
        opened.commitment_set_root,
        &opened.values,
    )?;
    if digest != opened.digest {
        return Err(AuthenticatedBitError::OpeningSetMismatch);
    }
    Ok(())
}

fn validate_challenge(
    manifest: &AuthenticatedBitManifest,
    opened: &OpenedAuthenticatedBits,
    challenge: &MacBatchChallenge,
) -> Result<()> {
    if challenge.setup_root != manifest.setup_root
        || challenge.opened_digest != opened.digest
        || challenge
            .coefficients
            .iter()
            .any(|lane| lane.len() != manifest.values)
    {
        return Err(AuthenticatedBitError::ChallengeMismatch);
    }
    Ok(())
}

fn random_field<R: RngCore + CryptoRng>(rng: &mut R) -> Gf128 {
    let mut bytes = [0u8; 16];
    rng.fill_bytes(&mut bytes);
    Gf128::from_bytes(bytes)
}

fn random_nonzero_field<R: RngCore + CryptoRng>(rng: &mut R) -> Gf128 {
    loop {
        let value = random_field(rng);
        if !value.is_zero() {
            return value;
        }
    }
}

fn setup_root(
    context: [u8; 64],
    n_parties: usize,
    values: usize,
    nonce: [u8; 64],
) -> Result<[u8; 64]> {
    let mut hash = Sha512::new();
    hash.update(canonical_domain(SETUP_DOMAIN));
    hash.update(context);
    hash.update(checked_u64(n_parties)?.to_be_bytes());
    hash.update(checked_u64(values)?.to_be_bytes());
    hash.update(checked_u64(AUTHENTICATED_BIT_MAC_LANES)?.to_be_bytes());
    hash.update(nonce);
    Ok(hash.finalize().into())
}

fn opening_commitment_digest(
    setup_root: [u8; 64],
    party: usize,
    salt: [u8; 32],
    values: &[u8],
) -> Result<[u8; 64]> {
    let mut hash = Sha512::new();
    hash.update(canonical_domain(OPENING_COMMIT_DOMAIN));
    hash.update(setup_root);
    hash.update(checked_u64(party)?.to_be_bytes());
    hash.update(checked_u64(values.len())?.to_be_bytes());
    hash.update(salt);
    hash.update(values);
    Ok(hash.finalize().into())
}

fn commitment_set_root(
    domain: &[u8],
    setup_root: [u8; 64],
    commitments: &[[u8; 64]],
) -> Result<[u8; 64]> {
    let mut hash = Sha512::new();
    hash.update(canonical_domain(domain));
    hash.update(setup_root);
    hash.update(checked_u64(commitments.len())?.to_be_bytes());
    for commitment in commitments {
        hash.update(commitment);
    }
    Ok(hash.finalize().into())
}

fn opened_digest(
    setup_root: [u8; 64],
    commitment_set_root: [u8; 64],
    values: &[u8],
) -> Result<[u8; 64]> {
    let mut hash = Sha512::new();
    hash.update(canonical_domain(OPENED_DOMAIN));
    hash.update(setup_root);
    hash.update(commitment_set_root);
    hash.update(checked_u64(values.len())?.to_be_bytes());
    hash.update(values);
    Ok(hash.finalize().into())
}

fn check_commitment_digest(
    setup_root: [u8; 64],
    challenge_digest: [u8; 64],
    party: usize,
    salt: [u8; 32],
    sigma: [Gf128; AUTHENTICATED_BIT_MAC_LANES],
) -> Result<[u8; 64]> {
    let mut hash = Sha512::new();
    hash.update(canonical_domain(CHECK_COMMIT_DOMAIN));
    hash.update(setup_root);
    hash.update(challenge_digest);
    hash.update(checked_u64(party)?.to_be_bytes());
    hash.update(salt);
    for lane in sigma {
        hash.update(lane.to_bytes());
    }
    Ok(hash.finalize().into())
}

fn checked_u64(value: usize) -> Result<u64> {
    u64::try_from(value).map_err(|_| AuthenticatedBitError::ArithmeticOverflow)
}

fn canonical_domain(domain: &[u8]) -> Vec<u8> {
    let mut encoded = Vec::with_capacity(8 + domain.len());
    encoded.extend_from_slice(&(domain.len() as u64).to_be_bytes());
    encoded.extend_from_slice(domain);
    encoded
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};

    fn setup(
        shares: Vec<Vec<u8>>,
    ) -> (
        AuthenticatedBitManifest,
        Vec<AuthenticatedBitRow>,
        Vec<MacKeyShare>,
    ) {
        trusted_mac_setup_for_bits([0x31; 64], shares, &mut StdRng::from_seed([0x41; 32]))
            .unwrap()
            .into_parts()
    }

    fn open(
        manifest: &AuthenticatedBitManifest,
        rows: &[AuthenticatedBitRow],
    ) -> OpenedAuthenticatedBits {
        let prepared = rows
            .iter()
            .enumerate()
            .map(|(party, row)| {
                row.prepare_opening(manifest, [(party + 1) as u8; 32])
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let commitments = prepared
            .iter()
            .map(|(commitment, _)| commitment.clone())
            .collect::<Vec<_>>();
        let set = seal_opening_commitments(manifest, &commitments).unwrap();
        let reveals = prepared
            .into_iter()
            .map(|(_, pending)| pending.reveal(&set).unwrap())
            .collect::<Vec<_>>();
        reconstruct_opened_bits(manifest, &set, &reveals).unwrap()
    }

    fn check(
        manifest: &AuthenticatedBitManifest,
        rows: &[AuthenticatedBitRow],
        keys: &[MacKeyShare],
        opened: &OpenedAuthenticatedBits,
    ) -> Result<VerifiedAuthenticatedOpening> {
        let challenge = MacBatchChallenge::derive(manifest, opened, [0x71; 64]).unwrap();
        let prepared = rows
            .iter()
            .zip(keys)
            .enumerate()
            .map(|(party, (row, key))| {
                prepare_mac_check(
                    manifest,
                    row,
                    key,
                    opened,
                    &challenge,
                    [(party + 11) as u8; 32],
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let commitments = prepared
            .iter()
            .map(|(commitment, _)| commitment.clone())
            .collect::<Vec<_>>();
        let set = seal_mac_check_commitments(manifest, &challenge, &commitments).unwrap();
        let reveals = prepared
            .into_iter()
            .map(|(_, pending)| pending.reveal(&set).unwrap())
            .collect::<Vec<_>>();
        verify_mac_check(manifest, opened, &challenge, &set, &reveals)
    }

    #[test]
    fn gf128_reference_multiply_has_field_teeth() {
        let a = Gf128(0x1234_5678_9abc_def0_1122_3344_5566_7788);
        let b = Gf128(0xfedc_ba98_7654_3210_8877_6655_4433_2211);
        let c = Gf128(0xaaaa_5555_aaaa_5555_0123_4567_89ab_cdef);
        assert!(a.mul(Gf128::ONE) == a);
        assert!(a.mul(Gf128::ZERO) == Gf128::ZERO);
        assert!(a.mul(b) == b.mul(a));
        assert!(a.mul(b.add(c)) == a.mul(b).add(a.mul(c)));
        assert!(a.mul(b) != Gf128::ZERO);
    }

    #[test]
    fn honest_authenticated_batch_opens_and_checks() {
        let (manifest, rows, keys) = setup(vec![vec![1, 0, 1], vec![0, 1, 1]]);
        let opened = open(&manifest, &rows);
        assert_eq!(opened.values(), &[1, 1, 0]);
        let verified = check(&manifest, &rows, &keys, &opened).unwrap();
        assert_eq!(verified.values(), opened.values());
        assert_eq!(verified.setup_root(), manifest.setup_root());
    }

    #[test]
    fn authenticated_linear_operations_preserve_tags() {
        let (manifest, rows, keys) = setup(vec![vec![1, 0], vec![0, 1]]);
        let derived = rows
            .iter()
            .map(|row| {
                AuthenticatedBitRow::from_linear_shares(vec![
                    row.share(0).unwrap().xor(row.share(1).unwrap()).unwrap(),
                    row.share(0).unwrap().scale_public(0).unwrap(),
                ])
                .unwrap()
            })
            .collect::<Vec<_>>();
        let derived_manifest = AuthenticatedBitManifest {
            values: 2,
            ..manifest.clone()
        };
        let opened = open(&derived_manifest, &derived);
        assert_eq!(opened.values(), &[0, 0]);
        check(&derived_manifest, &derived, &keys, &opened).unwrap();
    }

    #[test]
    fn forged_binary_sacrifice_tau_is_caught_by_authenticated_opening() {
        // Global kept triple (1,1,0) is malformed; global sacrifice (1,0,0)
        // is valid. Rows are [a,b,c,f,g,h].
        let (manifest, source, keys) = setup(vec![vec![1, 0, 1, 0, 1, 0], vec![0, 1, 1, 1, 1, 0]]);
        let challenge_bit = 1u8;

        // First sacrifice response: rho = r*a+f, sigma = b+g. Pad the
        // authenticated response back to the setup row width with linear zero
        // shares so the isolated setup manifest remains unchanged.
        let mask_rows = source
            .iter()
            .map(|row| {
                let zero = row.share(0).unwrap().scale_public(0).unwrap();
                let rho = row
                    .share(0)
                    .unwrap()
                    .scale_public(challenge_bit)
                    .unwrap()
                    .xor(row.share(3).unwrap())
                    .unwrap();
                let sigma = row.share(1).unwrap().xor(row.share(4).unwrap()).unwrap();
                AuthenticatedBitRow::from_linear_shares(vec![rho, sigma, zero, zero, zero, zero])
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let opened_masks = open(&manifest, &mask_rows);
        check(&manifest, &mask_rows, &keys, &opened_masks).unwrap();
        assert_eq!(&opened_masks.values()[..2], &[0, 1]);
        let rho = opened_masks.values()[0];
        let sigma = opened_masks.values()[1];

        // Honest tau reconstructs to one, so the sacrifice equation rejects.
        // Party zero instead commits a self-consistent lie making public tau
        // zero (which would cancel rho*sigma and fool the bare sacrifice
        // checker). The hidden SPDZ MAC catches that exact former hole.
        let tau_rows = source
            .iter()
            .map(|row| {
                let zero = row.share(0).unwrap().scale_public(0).unwrap();
                let tau = row
                    .share(2)
                    .unwrap()
                    .scale_public(challenge_bit)
                    .unwrap()
                    .xor(row.share(5).unwrap())
                    .unwrap()
                    .xor(row.share(3).unwrap().scale_public(sigma).unwrap())
                    .unwrap()
                    .xor(row.share(4).unwrap().scale_public(rho).unwrap())
                    .unwrap();
                AuthenticatedBitRow::from_linear_shares(vec![tau, zero, zero, zero, zero, zero])
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let mut prepared = tau_rows
            .iter()
            .enumerate()
            .map(|(party, row)| {
                row.prepare_opening(&manifest, [(party + 31) as u8; 32])
                    .unwrap()
            })
            .collect::<Vec<_>>();
        prepared[0].1.values[0] ^= 1;
        let forged_digest = opening_commitment_digest(
            manifest.setup_root,
            0,
            prepared[0].1.salt,
            &prepared[0].1.values,
        )
        .unwrap();
        prepared[0].0.digest = forged_digest;
        prepared[0].1.commitment = forged_digest;
        let commitments = prepared
            .iter()
            .map(|(commitment, _)| commitment.clone())
            .collect::<Vec<_>>();
        let set = seal_opening_commitments(&manifest, &commitments).unwrap();
        let reveals = prepared
            .into_iter()
            .map(|(_, pending)| pending.reveal(&set).unwrap())
            .collect::<Vec<_>>();
        let forged_tau = reconstruct_opened_bits(&manifest, &set, &reveals).unwrap();
        assert_eq!(forged_tau.values()[0], rho & sigma);
        assert!(matches!(
            check(&manifest, &tau_rows, &keys, &forged_tau),
            Err(AuthenticatedBitError::CheckRejected { .. })
        ));
    }

    #[test]
    fn self_consistent_lying_value_opening_is_rejected_by_mac() {
        let (manifest, rows, keys) = setup(vec![vec![1, 0], vec![0, 1]]);
        let mut prepared = rows
            .iter()
            .enumerate()
            .map(|(party, row)| {
                row.prepare_opening(&manifest, [(party + 1) as u8; 32])
                    .unwrap()
            })
            .collect::<Vec<_>>();

        // Party zero lies before the commit barrier, then honestly commits that
        // lie. The commitment layer alone therefore accepts it; the MAC must not.
        prepared[0].1.values[0] ^= 1;
        let forged_digest = opening_commitment_digest(
            manifest.setup_root,
            0,
            prepared[0].1.salt,
            &prepared[0].1.values,
        )
        .unwrap();
        prepared[0].0.digest = forged_digest;
        prepared[0].1.commitment = forged_digest;

        let commitments = prepared
            .iter()
            .map(|(commitment, _)| commitment.clone())
            .collect::<Vec<_>>();
        let set = seal_opening_commitments(&manifest, &commitments).unwrap();
        let reveals = prepared
            .into_iter()
            .map(|(_, pending)| pending.reveal(&set).unwrap())
            .collect::<Vec<_>>();
        let opened = reconstruct_opened_bits(&manifest, &set, &reveals).unwrap();
        assert_eq!(opened.values(), &[0, 1]);
        assert!(matches!(
            check(&manifest, &rows, &keys, &opened),
            Err(AuthenticatedBitError::CheckRejected { .. })
        ));
    }

    #[test]
    fn forged_check_committed_before_reveal_is_rejected() {
        let (manifest, rows, keys) = setup(vec![vec![1, 0], vec![0, 1]]);
        let mut opened = open(&manifest, &rows);
        // Model the same self-consistent false public opening as the previous
        // test without reopening the setup.
        opened.values[0] ^= 1;
        opened.digest = opened_digest(
            manifest.setup_root,
            opened.commitment_set_root,
            &opened.values,
        )
        .unwrap();
        let challenge = MacBatchChallenge::derive(&manifest, &opened, [0x72; 64]).unwrap();
        let mut prepared = rows
            .iter()
            .zip(&keys)
            .enumerate()
            .map(|(party, (row, key))| {
                prepare_mac_check(
                    &manifest,
                    row,
                    key,
                    &opened,
                    &challenge,
                    [(party + 21) as u8; 32],
                )
                .unwrap()
            })
            .collect::<Vec<_>>();

        // The liar chooses zero before seeing the honest check reveal and
        // commits it consistently. It cannot cancel the hidden honest residual.
        prepared[0].1.sigma = [Gf128::ZERO; AUTHENTICATED_BIT_MAC_LANES];
        let forged_digest = check_commitment_digest(
            manifest.setup_root,
            challenge.digest,
            0,
            prepared[0].1.salt,
            prepared[0].1.sigma,
        )
        .unwrap();
        prepared[0].0.digest = forged_digest;
        prepared[0].1.commitment = forged_digest;

        let commitments = prepared
            .iter()
            .map(|(commitment, _)| commitment.clone())
            .collect::<Vec<_>>();
        let set = seal_mac_check_commitments(&manifest, &challenge, &commitments).unwrap();
        let reveals = prepared
            .into_iter()
            .map(|(_, pending)| pending.reveal(&set).unwrap())
            .collect::<Vec<_>>();
        assert!(matches!(
            verify_mac_check(&manifest, &opened, &challenge, &set, &reveals),
            Err(AuthenticatedBitError::CheckRejected { .. })
        ));
    }

    #[test]
    fn reveal_mutation_and_party_reordering_are_refused() {
        let (manifest, rows, _) = setup(vec![vec![1, 0], vec![0, 1]]);
        let prepared = rows
            .iter()
            .enumerate()
            .map(|(party, row)| {
                row.prepare_opening(&manifest, [(party + 1) as u8; 32])
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let commitments = prepared
            .iter()
            .map(|(commitment, _)| commitment.clone())
            .collect::<Vec<_>>();
        let set = seal_opening_commitments(&manifest, &commitments).unwrap();
        let mut reveals = prepared
            .into_iter()
            .map(|(_, pending)| pending.reveal(&set).unwrap())
            .collect::<Vec<_>>();
        reveals[0].values[0] ^= 1;
        assert!(matches!(
            reconstruct_opened_bits(&manifest, &set, &reveals),
            Err(AuthenticatedBitError::OpeningCommitmentMismatch { party: 0 })
        ));
        reveals[0].values[0] ^= 1;
        reveals.swap(0, 1);
        assert!(matches!(
            reconstruct_opened_bits(&manifest, &set, &reveals),
            Err(AuthenticatedBitError::InvalidParty { .. })
        ));
    }
}
