//! Experimental lattice-style additive commitments for distributed-prover shares.
//!
//! This is the smallest executable replacement rung for the Ristretto vector
//! commitment algebra used by the distributed BFV prover:
//!
//! ```text
//! Com(m, r) = M * m + R * r  (mod q)
//! Com(m1, r1) + Com(m2, r2) = Com(m1 + m2, r1 + r2)
//! ```
//!
//! `q` is BabyBear, so the commitment is native to the existing AIR field.
//! Each key is bound to a public session context and logical vector slot.  The
//! matrices are deterministically expanded from a public 256-bit seed with
//! SHA-512 and rejection sampling; openings use canonical centered integers,
//! so an accepted opening has one exact integer representation rather than an
//! arbitrary representative modulo `q`.
//!
//! # Security status: a real algebraic rung, not a parameter claim
//!
//! The prototype profile uses 13 output felts (403 bits), the minimum generic
//! 128-bit quantum-collision width if a BHT-style cube-root attack is credited,
//! and 704 independent binary blinding coordinates.  For a genuinely random
//! linear family, 704 bits leave a 301-bit entropy surplus over the 403-bit
//! output.  Neither fact establishes SIS binding or hiding for this concrete,
//! wide, SHA-derived matrix.  In particular, infinity-norm SIS estimates are
//! width-sensitive.  Deployment must select and estimator-check dimensions for
//! its maximum value width, share count, and opening bounds.  This module does
//! **not** claim full post-quantum security.
//!
//! The live distributed prover currently forms essentially uniform Ristretto
//! scalar shares. Those are not short BabyBear message coordinates: a faithful
//! limb encoding would make the message-coordinate bound dominate the extracted
//! SIS `beta`. Consequently this rung cannot replace that live commitment by a
//! type-only substitution. The share representation and its maximum centered
//! limb bound must be selected first, then estimated together with matrix width.
//!
//! The Lean companion `Dregg2.Crypto.PqShareCommitment` proves the additive,
//! opening, rerandomization, and link/extraction semantics for arbitrary linear
//! maps.  A small explicit-matrix KAT is pinned on both sides to catch drift in
//! centered reduction and row/column order.

use std::fmt;

use rand::{CryptoRng, RngCore};
use sha2::{Digest, Sha256, Sha512};

/// Native field shared with the BabyBear AIR.
pub const PQ_SHARE_COMMITMENT_MODULUS: u64 = 2_013_265_921;
/// Experimental generic quantum-collision floor: 13 * 31 = 403 bits.
pub const PQ_SHARE_COMMITMENT_PROTOTYPE_DIGEST_WIDTH: usize = 13;
/// Binary randomizer width. 704 - 13*31 = 301 bits of entropy surplus.
pub const PQ_SHARE_COMMITMENT_PROTOTYPE_BLINDING_WIDTH: usize = 704;
/// Resource ceiling, not a supported security parameter.  The q0 BFV profile
/// below needs three radix-2^15 coordinates for each of 4,096 coefficients.
pub const MAX_PQ_SHARE_VALUE_WIDTH: usize = 16_384;
/// Resource ceiling, not a supported security parameter.
pub const MAX_PQ_SHARE_DIGEST_WIDTH: usize = 64;
/// Resource ceiling, not a supported security parameter.
pub const MAX_PQ_SHARE_BLINDING_WIDTH: usize = 4_096;
/// Canonical centered representative interval is `[-(q-1)/2, +(q-1)/2]`.
pub const MAX_CENTERED_COEFFICIENT: i64 = ((PQ_SHARE_COMMITMENT_MODULUS - 1) / 2) as i64;

const MATRIX_DOMAIN: &[u8] = b"fhegg/pq-share-commitment/matrix/v1";
const KEY_ID_DOMAIN: &[u8] = b"fhegg/pq-share-commitment/key-id/v1";
#[cfg(test)]
const EXPLICIT_KEY_ID_DOMAIN: &[u8] = b"fhegg/pq-share-commitment/explicit-key-id/v1";
const COMMITMENT_WIRE_MAGIC: &[u8; 8] = b"FHPQSC01";
const BFV_Q0_CONTEXT_DOMAIN: &[u8] = b"fhegg/pq-share-commitment/bfv-q0-context/v1";

/// First production BFV RNS modulus, matching the Lean/FhEgg q0 family.
pub const BFV_Q0_MODULUS: u64 = 68_719_403_009;
/// Production ring degree.
pub const BFV_Q0_DEGREE: usize = 4_096;
/// A q0 residue is faithfully represented by three radix-2^15 limbs.
pub const BFV_Q0_LIMBS_PER_COEFFICIENT: usize = 3;
pub const BFV_Q0_VALUE_WIDTH: usize = BFV_Q0_DEGREE * BFV_Q0_LIMBS_PER_COEFFICIENT;
const BFV_Q0_LIMB_RADIX: u64 = 1 << 15;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PqShareCommitmentError {
    InvalidParameters(&'static str),
    ShapeMismatch,
    NonCanonicalOpening,
    ArithmeticOverflow,
    KeyMismatch,
    MalformedCommitmentWire,
    /// The executable algebra/KAT profile has no approved concrete SIS/hiding
    /// parameter record and must never satisfy a production-PQ policy.
    ProductionParametersUnvalidated,
}

impl fmt::Display for PqShareCommitmentError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PQ share commitment error: {self:?}")
    }
}

impl std::error::Error for PqShareCommitmentError {}

pub type Result<T> = std::result::Result<T, PqShareCommitmentError>;

/// Public dimensions of one commitment key.
///
/// These dimensions describe an executable experiment. They carry no security
/// level; callers must bind them into policy and estimator-check the resulting
/// `(n, m, q, beta)` tuple before a deployment claim.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PqShareCommitmentParams {
    value_width: usize,
    digest_width: usize,
    blinding_width: usize,
}

/// Honest status marker exposed to hosts and policy code. There is deliberately
/// no `ProductionPostQuantum` variant until a checked parameter record lands.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PqShareCommitmentSecurityStatus {
    ExperimentalAlgebraAndKatOnly,
}

impl PqShareCommitmentParams {
    pub fn new(value_width: usize, digest_width: usize, blinding_width: usize) -> Result<Self> {
        if value_width == 0 || value_width > MAX_PQ_SHARE_VALUE_WIDTH {
            return Err(PqShareCommitmentError::InvalidParameters(
                "value width is outside the resource envelope",
            ));
        }
        if digest_width == 0 || digest_width > MAX_PQ_SHARE_DIGEST_WIDTH {
            return Err(PqShareCommitmentError::InvalidParameters(
                "digest width is outside the resource envelope",
            ));
        }
        if blinding_width == 0 || blinding_width > MAX_PQ_SHARE_BLINDING_WIDTH {
            return Err(PqShareCommitmentError::InvalidParameters(
                "blinding width is outside the resource envelope",
            ));
        }
        Ok(Self {
            value_width,
            digest_width,
            blinding_width,
        })
    }

    /// The deliberately unparameterized first integration rung.
    pub fn experimental_v1(value_width: usize) -> Result<Self> {
        Self::new(
            value_width,
            PQ_SHARE_COMMITMENT_PROTOTYPE_DIGEST_WIDTH,
            PQ_SHARE_COMMITMENT_PROTOTYPE_BLINDING_WIDTH,
        )
    }

    /// Exact-width experimental profile for one production q0 secret-share
    /// row.  This is an algebra/integration profile only; it deliberately
    /// inherits the fail-closed production-PQ policy below.
    pub fn experimental_bfv_q0_v1() -> Result<Self> {
        Self::experimental_v1(BFV_Q0_VALUE_WIDTH)
    }

    pub const fn value_width(self) -> usize {
        self.value_width
    }

    pub const fn digest_width(self) -> usize {
        self.digest_width
    }

    pub const fn blinding_width(self) -> usize {
        self.blinding_width
    }

    /// Total SIS-domain width for one logical vector slot.
    pub const fn sis_width(self) -> usize {
        self.value_width + self.blinding_width
    }

    /// Public commitment size without its wire header/key id.
    pub const fn commitment_bytes(self) -> usize {
        self.digest_width * 4
    }

    pub const fn security_status(self) -> PqShareCommitmentSecurityStatus {
        PqShareCommitmentSecurityStatus::ExperimentalAlgebraAndKatOnly
    }

    /// Executable fail-closed policy tooth: no current parameter tuple is
    /// approved for a production post-quantum claim.
    pub const fn require_production_post_quantum(self) -> Result<()> {
        Err(PqShareCommitmentError::ProductionParametersUnvalidated)
    }
}

/// One public, position-bound linear commitment key.
#[derive(Clone)]
pub struct PqShareCommitmentKey {
    params: PqShareCommitmentParams,
    context: [u8; 32],
    slot: u64,
    seed: [u8; 32],
    key_id: [u8; 32],
    value_matrix: Vec<u32>,
    blinding_matrix: Vec<u32>,
}

impl fmt::Debug for PqShareCommitmentKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PqShareCommitmentKey")
            .field("params", &self.params)
            .field("context", &self.context)
            .field("slot", &self.slot)
            .field("key_id", &self.key_id)
            .finish_non_exhaustive()
    }
}

impl PqShareCommitmentKey {
    /// Expand a public key from a session context, logical slot, and public seed.
    pub fn derive(
        params: PqShareCommitmentParams,
        context: [u8; 32],
        slot: u64,
        seed: [u8; 32],
    ) -> Result<Self> {
        // Revalidate in case a future representation stops making invalid
        // dimensions unconstructable inside this crate.
        let params = PqShareCommitmentParams::new(
            params.value_width,
            params.digest_width,
            params.blinding_width,
        )?;
        let value_len = params
            .digest_width
            .checked_mul(params.value_width)
            .ok_or(PqShareCommitmentError::ArithmeticOverflow)?;
        let blinding_len = params
            .digest_width
            .checked_mul(params.blinding_width)
            .ok_or(PqShareCommitmentError::ArithmeticOverflow)?;
        let mut value_matrix = Vec::with_capacity(value_len);
        let mut blinding_matrix = Vec::with_capacity(blinding_len);
        for row in 0..params.digest_width {
            for column in 0..params.value_width {
                value_matrix.push(derive_matrix_entry(&seed, &context, slot, 0, row, column));
            }
            for column in 0..params.blinding_width {
                blinding_matrix.push(derive_matrix_entry(&seed, &context, slot, 1, row, column));
            }
        }
        let key_id = derived_key_id(params, context, slot, seed);
        Ok(Self {
            params,
            context,
            slot,
            seed,
            key_id,
            value_matrix,
            blinding_matrix,
        })
    }

    pub const fn params(&self) -> PqShareCommitmentParams {
        self.params
    }

    pub const fn context(&self) -> [u8; 32] {
        self.context
    }

    pub const fn slot(&self) -> u64 {
        self.slot
    }

    pub const fn seed(&self) -> [u8; 32] {
        self.seed
    }

    pub const fn key_id(&self) -> [u8; 32] {
        self.key_id
    }

    /// Commit an exact canonical centered opening.
    pub fn commit(&self, opening: &PqShareOpening) -> Result<PqShareCommitment> {
        opening.validate(self.params)?;
        let mut coordinates = Vec::with_capacity(self.params.digest_width);
        for row in 0..self.params.digest_width {
            let mut accumulator = 0u64;
            let value_start = row * self.params.value_width;
            for (&matrix, &coefficient) in self.value_matrix
                [value_start..value_start + self.params.value_width]
                .iter()
                .zip(&opening.values)
            {
                accumulator = add_product_mod(accumulator, matrix, centered_to_felt(coefficient));
            }
            let blinding_start = row * self.params.blinding_width;
            for (&matrix, &coefficient) in self.blinding_matrix
                [blinding_start..blinding_start + self.params.blinding_width]
                .iter()
                .zip(&opening.blinding)
            {
                accumulator = add_product_mod(accumulator, matrix, centered_to_felt(coefficient));
            }
            coordinates.push(accumulator as u32);
        }
        Ok(PqShareCommitment {
            key_id: self.key_id,
            coordinates,
        })
    }

    /// Exact opening check. Malformed shapes are errors, not false statements.
    pub fn verify_opening(
        &self,
        commitment: &PqShareCommitment,
        opening: &PqShareOpening,
    ) -> Result<bool> {
        commitment.validate_for(self)?;
        Ok(self.commit(opening)? == *commitment)
    }

    /// Public additive link used by a coordinator that must never see openings.
    pub fn verify_public_link(
        &self,
        owner: &PqShareCommitment,
        shares: &[PqShareCommitment],
    ) -> Result<bool> {
        owner.validate_for(self)?;
        Ok(sum_commitments(self, shares)? == *owner)
    }

    /// Strong local audit: every supplied opening verifies, the exact centered
    /// openings add without modular aliasing, and the public commitments link.
    pub fn verify_opened_link(
        &self,
        owner_commitment: &PqShareCommitment,
        owner_opening: &PqShareOpening,
        shares: &[(&PqShareCommitment, &PqShareOpening)],
    ) -> Result<bool> {
        if shares.is_empty() || !self.verify_opening(owner_commitment, owner_opening)? {
            return Ok(false);
        }
        let mut share_openings = Vec::with_capacity(shares.len());
        let mut share_commitments = Vec::with_capacity(shares.len());
        for &(commitment, opening) in shares {
            if !self.verify_opening(commitment, opening)? {
                return Ok(false);
            }
            share_openings.push(opening.clone());
            share_commitments.push(commitment.clone());
        }
        let combined = combine_openings(&share_openings)?;
        Ok(combined == *owner_opening
            && self.verify_public_link(owner_commitment, &share_commitments)?)
    }

    #[cfg(test)]
    fn from_explicit_matrices(
        value_width: usize,
        blinding_width: usize,
        digest_width: usize,
        value_matrix: Vec<u32>,
        blinding_matrix: Vec<u32>,
    ) -> Result<Self> {
        let params = PqShareCommitmentParams::new(value_width, digest_width, blinding_width)?;
        if value_matrix.len() != value_width * digest_width
            || blinding_matrix.len() != blinding_width * digest_width
            || value_matrix
                .iter()
                .chain(&blinding_matrix)
                .any(|&entry| u64::from(entry) >= PQ_SHARE_COMMITMENT_MODULUS)
        {
            return Err(PqShareCommitmentError::ShapeMismatch);
        }
        let mut hash = Sha256::new();
        hash.update((EXPLICIT_KEY_ID_DOMAIN.len() as u64).to_be_bytes());
        hash.update(EXPLICIT_KEY_ID_DOMAIN);
        hash.update((value_width as u64).to_be_bytes());
        hash.update((digest_width as u64).to_be_bytes());
        hash.update((blinding_width as u64).to_be_bytes());
        for entry in value_matrix.iter().chain(&blinding_matrix) {
            hash.update(entry.to_be_bytes());
        }
        Ok(Self {
            params,
            context: [0u8; 32],
            slot: 0,
            seed: [0u8; 32],
            key_id: hash.finalize().into(),
            value_matrix,
            blinding_matrix,
        })
    }
}

/// Secret opening. It intentionally has no wire codec or `Debug` implementation.
#[derive(Clone, PartialEq, Eq)]
pub struct PqShareOpening {
    values: Vec<i64>,
    blinding: Vec<i64>,
}

impl PqShareOpening {
    pub fn new(values: Vec<i64>, blinding: Vec<i64>) -> Result<Self> {
        let opening = Self { values, blinding };
        opening.validate_coefficients()?;
        Ok(opening)
    }

    /// Sample one independent binary (`-1/+1`) blinding vector.
    pub fn randomized<R: CryptoRng + RngCore>(
        values: Vec<i64>,
        blinding_width: usize,
        rng: &mut R,
    ) -> Result<Self> {
        if blinding_width == 0 || blinding_width > MAX_PQ_SHARE_BLINDING_WIDTH {
            return Err(PqShareCommitmentError::InvalidParameters(
                "blinding width is outside the resource envelope",
            ));
        }
        let mut blinding = Vec::with_capacity(blinding_width);
        let mut random_word = 0u64;
        let mut remaining = 0u8;
        for _ in 0..blinding_width {
            if remaining == 0 {
                random_word = rng.next_u64();
                remaining = 64;
            }
            blinding.push(if random_word & 1 == 0 { -1 } else { 1 });
            random_word >>= 1;
            remaining -= 1;
        }
        Self::new(values, blinding)
    }

    pub fn values(&self) -> &[i64] {
        &self.values
    }

    pub fn blinding(&self) -> &[i64] {
        &self.blinding
    }

    /// Coefficient infinity norm used when passing this concrete opening to an
    /// SIS estimator/reduction.
    pub fn linf_norm(&self) -> u64 {
        self.values
            .iter()
            .chain(&self.blinding)
            .map(|value| value.unsigned_abs())
            .max()
            .unwrap_or(0)
    }

    fn validate(&self, params: PqShareCommitmentParams) -> Result<()> {
        self.validate_coefficients()?;
        if self.values.len() != params.value_width || self.blinding.len() != params.blinding_width {
            return Err(PqShareCommitmentError::ShapeMismatch);
        }
        Ok(())
    }

    fn validate_coefficients(&self) -> Result<()> {
        if self.values.is_empty()
            || self.blinding.is_empty()
            || self
                .values
                .iter()
                .chain(&self.blinding)
                .any(|value| value.unsigned_abs() > MAX_CENTERED_COEFFICIENT as u64)
        {
            return Err(PqShareCommitmentError::NonCanonicalOpening);
        }
        Ok(())
    }
}

/// Secret opening for one exact q0 BFV party-share row.
///
/// Construction is restricted to canonical q0 residues and binary
/// randomizers.  The resulting linear opening has 12,288 value coordinates:
/// three little-endian radix-2^15 limbs for each of 4,096 coefficients.  It
/// intentionally has no wire codec or `Debug` implementation.
#[derive(Clone, PartialEq, Eq)]
pub struct ExperimentalBfvQ0ShareOpening {
    inner: PqShareOpening,
}

impl ExperimentalBfvQ0ShareOpening {
    pub fn randomized<R: CryptoRng + RngCore>(residues: &[u64], rng: &mut R) -> Result<Self> {
        let values = encode_bfv_q0_residues(residues)?;
        Ok(Self {
            inner: PqShareOpening::randomized(
                values,
                PQ_SHARE_COMMITMENT_PROTOTYPE_BLINDING_WIDTH,
                rng,
            )?,
        })
    }

    /// Private witness coordinates consumed by a future HidingFRI opening
    /// proof.  Exposing this borrowed view does not serialize or publish the
    /// opening; callers remain responsible for secret-memory hygiene.
    pub fn linear_opening(&self) -> &PqShareOpening {
        &self.inner
    }

    /// Exact party-local typestate tooth: the limb opening must encode the
    /// same canonical residue row retained by that party.  This is not a
    /// publicly verifiable equality proof against the VSS/Ristretto anchor.
    pub fn matches_residues(&self, residues: &[u64]) -> Result<bool> {
        Ok(self.inner.values() == encode_bfv_q0_residues(residues)?)
    }
}

/// Experimental, session-bound commitment key for one q0 BFV party-share row.
///
/// The key context faithfully includes both the verified DKG digest and the
/// exact collective public-key digest; the logical slot is the custody party.
/// This prevents a valid opening from being replayed across setup/key/party
/// domains.  It does *not* by itself prove that the opened row is the same row
/// admitted by today's Ristretto VSS commitments.  That cross-commitment
/// same-opening proof is the explicit remaining bridge.
#[derive(Clone)]
pub struct ExperimentalBfvQ0ShareCommitmentKey {
    inner: PqShareCommitmentKey,
    dkg_digest: [u8; 32],
    collective_key_digest: [u8; 32],
    party: usize,
}

impl fmt::Debug for ExperimentalBfvQ0ShareCommitmentKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ExperimentalBfvQ0ShareCommitmentKey")
            .field("key_id", &self.inner.key_id())
            .field("dkg_digest", &self.dkg_digest)
            .field("collective_key_digest", &self.collective_key_digest)
            .field("party", &self.party)
            .finish_non_exhaustive()
    }
}

impl ExperimentalBfvQ0ShareCommitmentKey {
    pub fn derive(
        dkg_digest: [u8; 32],
        collective_key_digest: [u8; 32],
        party: usize,
        seed: [u8; 32],
    ) -> Result<Self> {
        let slot = u64::try_from(party)
            .map_err(|_| PqShareCommitmentError::InvalidParameters("party does not fit u64"))?;
        let context = bfv_q0_commitment_context(dkg_digest, collective_key_digest);
        let inner = PqShareCommitmentKey::derive(
            PqShareCommitmentParams::experimental_bfv_q0_v1()?,
            context,
            slot,
            seed,
        )?;
        Ok(Self {
            inner,
            dkg_digest,
            collective_key_digest,
            party,
        })
    }

    pub fn key_id(&self) -> [u8; 32] {
        self.inner.key_id()
    }

    pub const fn dkg_digest(&self) -> [u8; 32] {
        self.dkg_digest
    }

    pub const fn collective_key_digest(&self) -> [u8; 32] {
        self.collective_key_digest
    }

    pub const fn party(&self) -> usize {
        self.party
    }

    pub fn commit(&self, opening: &ExperimentalBfvQ0ShareOpening) -> Result<PqShareCommitment> {
        self.inner.commit(&opening.inner)
    }

    pub fn verify_opening(
        &self,
        commitment: &PqShareCommitment,
        opening: &ExperimentalBfvQ0ShareOpening,
    ) -> Result<bool> {
        self.inner.verify_opening(commitment, &opening.inner)
    }

    /// No current q0 tuple is estimator-approved for a production-PQ claim.
    pub const fn require_production_post_quantum(&self) -> Result<()> {
        self.inner.params().require_production_post_quantum()
    }
}

fn encode_bfv_q0_residues(residues: &[u64]) -> Result<Vec<i64>> {
    if residues.len() != BFV_Q0_DEGREE {
        return Err(PqShareCommitmentError::ShapeMismatch);
    }
    let mut values = Vec::with_capacity(BFV_Q0_VALUE_WIDTH);
    for &residue in residues {
        if residue >= BFV_Q0_MODULUS {
            return Err(PqShareCommitmentError::NonCanonicalOpening);
        }
        let mut value = residue;
        for _ in 0..BFV_Q0_LIMBS_PER_COEFFICIENT {
            values.push((value % BFV_Q0_LIMB_RADIX) as i64);
            value /= BFV_Q0_LIMB_RADIX;
        }
        debug_assert_eq!(value, 0);
    }
    Ok(values)
}

fn bfv_q0_commitment_context(dkg_digest: [u8; 32], collective_key_digest: [u8; 32]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update((BFV_Q0_CONTEXT_DOMAIN.len() as u64).to_be_bytes());
    hash.update(BFV_Q0_CONTEXT_DOMAIN);
    hash.update(BFV_Q0_MODULUS.to_be_bytes());
    hash.update((BFV_Q0_DEGREE as u64).to_be_bytes());
    hash.update((BFV_Q0_LIMBS_PER_COEFFICIENT as u64).to_be_bytes());
    hash.update(dkg_digest);
    hash.update(collective_key_digest);
    hash.finalize().into()
}

/// Public additive commitment. Coordinates are canonical BabyBear elements.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PqShareCommitment {
    key_id: [u8; 32],
    coordinates: Vec<u32>,
}

impl PqShareCommitment {
    pub const fn key_id(&self) -> [u8; 32] {
        self.key_id
    }

    pub fn coordinates(&self) -> &[u32] {
        &self.coordinates
    }

    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(8 + 32 + 4 + 4 * self.coordinates.len());
        out.extend_from_slice(COMMITMENT_WIRE_MAGIC);
        out.extend_from_slice(&self.key_id);
        out.extend_from_slice(&(self.coordinates.len() as u32).to_be_bytes());
        for coordinate in &self.coordinates {
            out.extend_from_slice(&coordinate.to_be_bytes());
        }
        out
    }

    pub fn from_wire_bytes(expected_key: &PqShareCommitmentKey, bytes: &[u8]) -> Result<Self> {
        let expected_len = 8usize
            .checked_add(32 + 4)
            .and_then(|length| {
                expected_key
                    .params
                    .digest_width
                    .checked_mul(4)
                    .and_then(|coordinates| length.checked_add(coordinates))
            })
            .ok_or(PqShareCommitmentError::ArithmeticOverflow)?;
        if bytes.len() != expected_len || bytes.get(..8) != Some(COMMITMENT_WIRE_MAGIC) {
            return Err(PqShareCommitmentError::MalformedCommitmentWire);
        }
        let key_id: [u8; 32] = bytes[8..40]
            .try_into()
            .map_err(|_| PqShareCommitmentError::MalformedCommitmentWire)?;
        if key_id != expected_key.key_id {
            return Err(PqShareCommitmentError::KeyMismatch);
        }
        let width = u32::from_be_bytes(
            bytes[40..44]
                .try_into()
                .map_err(|_| PqShareCommitmentError::MalformedCommitmentWire)?,
        ) as usize;
        if width != expected_key.params.digest_width {
            return Err(PqShareCommitmentError::MalformedCommitmentWire);
        }
        let mut coordinates = Vec::with_capacity(width);
        for chunk in bytes[44..].chunks_exact(4) {
            let coordinate = u32::from_be_bytes(
                chunk
                    .try_into()
                    .map_err(|_| PqShareCommitmentError::MalformedCommitmentWire)?,
            );
            if u64::from(coordinate) >= PQ_SHARE_COMMITMENT_MODULUS {
                return Err(PqShareCommitmentError::MalformedCommitmentWire);
            }
            coordinates.push(coordinate);
        }
        Ok(Self {
            key_id,
            coordinates,
        })
    }

    fn validate_for(&self, key: &PqShareCommitmentKey) -> Result<()> {
        if self.key_id != key.key_id {
            return Err(PqShareCommitmentError::KeyMismatch);
        }
        if self.coordinates.len() != key.params.digest_width
            || self
                .coordinates
                .iter()
                .any(|&coordinate| u64::from(coordinate) >= PQ_SHARE_COMMITMENT_MODULUS)
        {
            return Err(PqShareCommitmentError::ShapeMismatch);
        }
        Ok(())
    }
}

/// Exact checked sum of centered openings. Failure on overflow avoids silently
/// changing the SIS bound or creating a modular alias.
pub fn combine_openings(openings: &[PqShareOpening]) -> Result<PqShareOpening> {
    let first = openings
        .first()
        .ok_or(PqShareCommitmentError::ShapeMismatch)?;
    let mut values = vec![0i64; first.values.len()];
    let mut blinding = vec![0i64; first.blinding.len()];
    for opening in openings {
        if opening.values.len() != values.len() || opening.blinding.len() != blinding.len() {
            return Err(PqShareCommitmentError::ShapeMismatch);
        }
        for (sum, &value) in values.iter_mut().zip(&opening.values) {
            *sum = sum
                .checked_add(value)
                .ok_or(PqShareCommitmentError::ArithmeticOverflow)?;
        }
        for (sum, &value) in blinding.iter_mut().zip(&opening.blinding) {
            *sum = sum
                .checked_add(value)
                .ok_or(PqShareCommitmentError::ArithmeticOverflow)?;
        }
    }
    PqShareOpening::new(values, blinding)
}

/// Componentwise commitment sum. Different session/slot/key domains never mix.
pub fn sum_commitments(
    key: &PqShareCommitmentKey,
    commitments: &[PqShareCommitment],
) -> Result<PqShareCommitment> {
    if commitments.is_empty() {
        return Err(PqShareCommitmentError::ShapeMismatch);
    }
    let mut coordinates = vec![0u32; key.params.digest_width];
    for commitment in commitments {
        commitment.validate_for(key)?;
        for (sum, &coordinate) in coordinates.iter_mut().zip(&commitment.coordinates) {
            *sum = ((u64::from(*sum) + u64::from(coordinate)) % PQ_SHARE_COMMITMENT_MODULUS) as u32;
        }
    }
    Ok(PqShareCommitment {
        key_id: key.key_id,
        coordinates,
    })
}

fn centered_to_felt(value: i64) -> u32 {
    value.rem_euclid(PQ_SHARE_COMMITMENT_MODULUS as i64) as u32
}

fn add_product_mod(accumulator: u64, matrix: u32, coefficient: u32) -> u64 {
    ((u128::from(accumulator) + u128::from(matrix) * u128::from(coefficient))
        % u128::from(PQ_SHARE_COMMITMENT_MODULUS)) as u64
}

fn derive_matrix_entry(
    seed: &[u8; 32],
    context: &[u8; 32],
    slot: u64,
    lane: u8,
    row: usize,
    column: usize,
) -> u32 {
    let rejection_limit = (u64::MAX / PQ_SHARE_COMMITMENT_MODULUS) * PQ_SHARE_COMMITMENT_MODULUS;
    for retry in 0u32.. {
        let mut hash = Sha512::new();
        hash.update((MATRIX_DOMAIN.len() as u64).to_be_bytes());
        hash.update(MATRIX_DOMAIN);
        hash.update(seed);
        hash.update(context);
        hash.update(slot.to_be_bytes());
        hash.update([lane]);
        hash.update((row as u64).to_be_bytes());
        hash.update((column as u64).to_be_bytes());
        hash.update(retry.to_be_bytes());
        let digest = hash.finalize();
        let candidate = u64::from_be_bytes(digest[..8].try_into().expect("fixed SHA-512 output"));
        if candidate < rejection_limit {
            return (candidate % PQ_SHARE_COMMITMENT_MODULUS) as u32;
        }
    }
    unreachable!("u32 retry space cannot exhaust before a rejection sample")
}

fn derived_key_id(
    params: PqShareCommitmentParams,
    context: [u8; 32],
    slot: u64,
    seed: [u8; 32],
) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update((KEY_ID_DOMAIN.len() as u64).to_be_bytes());
    hash.update(KEY_ID_DOMAIN);
    hash.update(PQ_SHARE_COMMITMENT_MODULUS.to_be_bytes());
    hash.update((params.value_width as u64).to_be_bytes());
    hash.update((params.digest_width as u64).to_be_bytes());
    hash.update((params.blinding_width as u64).to_be_bytes());
    hash.update(context);
    hash.update(slot.to_be_bytes());
    hash.update(seed);
    hash.finalize().into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::SeedableRng;

    fn lean_kat_key() -> PqShareCommitmentKey {
        // Row-major matrices duplicated in `Dregg2.Crypto.PqShareCommitment`.
        PqShareCommitmentKey::from_explicit_matrices(
            3,
            4,
            3,
            vec![1, 2, 3, 5, 7, 11, 13, 17, 19],
            vec![23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71],
        )
        .unwrap()
    }

    #[test]
    fn lean_cross_side_kat_and_additive_link_are_bit_exact() {
        let key = lean_kat_key();
        let owner = PqShareOpening::new(vec![3, -2, 5], vec![1, -1, 1, -1]).unwrap();
        let share_a = PqShareOpening::new(vec![1, -3, 2], vec![1, -1, 1, 1]).unwrap();
        let share_b = PqShareOpening::new(vec![2, 1, 3], vec![0, 0, 0, -2]).unwrap();
        let owner_commitment = key.commit(&owner).unwrap();
        let a_commitment = key.commit(&share_a).unwrap();
        let b_commitment = key.commit(&share_b).unwrap();

        assert_eq!(owner_commitment.coordinates(), &[2, 48, 94]);
        assert_eq!(a_commitment.coordinates(), &[63, 104, 136]);
        assert_eq!(
            b_commitment.coordinates(),
            &[2_013_265_860, 2_013_265_865, 2_013_265_879]
        );
        assert!(combine_openings(&[share_a.clone(), share_b.clone()]).unwrap() == owner);
        assert!(key
            .verify_opened_link(
                &owner_commitment,
                &owner,
                &[(&a_commitment, &share_a), (&b_commitment, &share_b)],
            )
            .unwrap());
    }

    #[test]
    fn randomized_openings_link_and_wrong_openings_refuse() {
        let params = PqShareCommitmentParams::experimental_v1(4).unwrap();
        let key = PqShareCommitmentKey::derive(params, [0x51; 32], 7, [0x61; 32]).unwrap();
        let mut rng = StdRng::seed_from_u64(0x7172);
        let share_a = PqShareOpening::randomized(vec![3, -2, 7, 9], 704, &mut rng).unwrap();
        let share_b = PqShareOpening::randomized(vec![-1, 4, 2, -5], 704, &mut rng).unwrap();
        let owner = combine_openings(&[share_a.clone(), share_b.clone()]).unwrap();
        let a_commitment = key.commit(&share_a).unwrap();
        let b_commitment = key.commit(&share_b).unwrap();
        let owner_commitment = key.commit(&owner).unwrap();
        assert!(key
            .verify_public_link(
                &owner_commitment,
                &[a_commitment.clone(), b_commitment.clone()]
            )
            .unwrap());

        let wrong = PqShareOpening::new(
            vec![
                owner.values()[0] + 1,
                owner.values()[1],
                owner.values()[2],
                owner.values()[3],
            ],
            owner.blinding().to_vec(),
        )
        .unwrap();
        assert!(!key.verify_opening(&owner_commitment, &wrong).unwrap());
        assert!(!key
            .verify_opened_link(
                &owner_commitment,
                &wrong,
                &[(&a_commitment, &share_a), (&b_commitment, &share_b)],
            )
            .unwrap());
    }

    #[test]
    fn session_slot_wire_and_canonicality_fail_closed() {
        let params = PqShareCommitmentParams::experimental_v1(2).unwrap();
        assert_eq!(
            params.security_status(),
            PqShareCommitmentSecurityStatus::ExperimentalAlgebraAndKatOnly
        );
        assert_eq!(
            params.require_production_post_quantum(),
            Err(PqShareCommitmentError::ProductionParametersUnvalidated)
        );
        let key = PqShareCommitmentKey::derive(params, [0x81; 32], 4, [0x82; 32]).unwrap();
        let other_slot = PqShareCommitmentKey::derive(params, [0x81; 32], 5, [0x82; 32]).unwrap();
        let opening = PqShareOpening::new(vec![8, -3], vec![1; 704]).unwrap();
        let commitment = key.commit(&opening).unwrap();
        let wire = commitment.to_wire_bytes();
        assert_eq!(
            PqShareCommitment::from_wire_bytes(&key, &wire).unwrap(),
            commitment
        );
        assert!(matches!(
            PqShareCommitment::from_wire_bytes(&other_slot, &wire),
            Err(PqShareCommitmentError::KeyMismatch)
        ));

        let mut noncanonical = wire.clone();
        noncanonical[44..48].copy_from_slice(&(PQ_SHARE_COMMITMENT_MODULUS as u32).to_be_bytes());
        assert!(matches!(
            PqShareCommitment::from_wire_bytes(&key, &noncanonical),
            Err(PqShareCommitmentError::MalformedCommitmentWire)
        ));
        assert!(PqShareCommitment::from_wire_bytes(&key, &wire[..wire.len() - 1]).is_err());
        assert!(PqShareOpening::new(vec![MAX_CENTERED_COEFFICIENT + 1], vec![1]).is_err());
    }

    #[test]
    fn bfv_q0_profile_is_faithful_context_bound_and_zero_row_hostile() {
        let mut rng = StdRng::seed_from_u64(0xb0f0_4096);
        let dkg_digest = [0x91; 32];
        let collective_key_digest = [0xa2; 32];
        let key = ExperimentalBfvQ0ShareCommitmentKey::derive(
            dkg_digest,
            collective_key_digest,
            3,
            [0xb3; 32],
        )
        .unwrap();
        let mut residues = vec![0u64; BFV_Q0_DEGREE];
        residues[0] = BFV_Q0_MODULUS - 1;
        residues[1] = 32_768;
        residues[BFV_Q0_DEGREE - 1] = 0x1_2345_6789;
        let opening = ExperimentalBfvQ0ShareOpening::randomized(&residues, &mut rng).unwrap();
        assert_eq!(opening.linear_opening().values().len(), BFV_Q0_VALUE_WIDTH);
        assert_eq!(
            &opening.linear_opening().values()[..3],
            &[24_576, 32_765, 63]
        );
        let commitment = key.commit(&opening).unwrap();
        assert!(key.verify_opening(&commitment, &opening).unwrap());

        // Substitute an all-zero row while retaining this exact q0
        // commitment.  It cannot open the commitment.  This test does not
        // establish linkage to the separate VSS/Ristretto commitment.
        let zero_opening =
            ExperimentalBfvQ0ShareOpening::randomized(&vec![0u64; BFV_Q0_DEGREE], &mut rng)
                .unwrap();
        assert!(!key.verify_opening(&commitment, &zero_opening).unwrap());

        for (other_dkg, other_collective, other_party) in [
            ([0x92; 32], collective_key_digest, 3),
            (dkg_digest, [0xa3; 32], 3),
            (dkg_digest, collective_key_digest, 4),
        ] {
            let other = ExperimentalBfvQ0ShareCommitmentKey::derive(
                other_dkg,
                other_collective,
                other_party,
                [0xb3; 32],
            )
            .unwrap();
            assert!(matches!(
                other.verify_opening(&commitment, &opening),
                Err(PqShareCommitmentError::KeyMismatch)
            ));
        }
        assert_eq!(
            key.require_production_post_quantum(),
            Err(PqShareCommitmentError::ProductionParametersUnvalidated)
        );
    }

    #[test]
    fn bfv_q0_profile_refuses_shape_and_noncanonical_residues() {
        let mut rng = StdRng::seed_from_u64(0xbad0_4096);
        assert!(matches!(
            ExperimentalBfvQ0ShareOpening::randomized(&vec![0u64; BFV_Q0_DEGREE - 1], &mut rng,),
            Err(PqShareCommitmentError::ShapeMismatch)
        ));
        let mut residues = vec![0u64; BFV_Q0_DEGREE];
        residues[17] = BFV_Q0_MODULUS;
        assert!(matches!(
            ExperimentalBfvQ0ShareOpening::randomized(&residues, &mut rng),
            Err(PqShareCommitmentError::NonCanonicalOpening)
        ));
    }
}
