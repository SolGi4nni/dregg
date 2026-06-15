//! Per-agent ECVRF sortition — RFC 9381 ECVRF-EDWARDS25519-SHA512-TAI
//! (suite string `0x03`, RFC 9381 §5.5) over the curve already in this tree
//! (`curve25519-dalek`, the same group `ed25519-dalek` signs on).
//!
//! # What this is
//!
//! A verifiable random function: the holder of a secret key evaluates
//! `VRF_sk(alpha) → (beta, pi)` where `beta` is a 64-byte pseudorandom output
//! and `pi` is a proof that ANYONE holding the public key can check. Two
//! properties carry the protocol weight (RFC 9381 §3):
//!
//! * **Uniqueness** (§3.1): for a fixed `(pk, alpha)` there is exactly one
//!   `beta` that verifies — a prover cannot grind among candidate outputs.
//! * **Pseudorandomness** (§3.3): without `sk`, `beta` is indistinguishable
//!   from random — nobody can compute another agent's output before that
//!   agent reveals it.
//!
//! # The use: targeting-resistant juries (sortition)
//!
//! [`beacon::select_jury`](crate::beacon::select_jury) is the committee
//! fallback: it draws `k` distinct indices from a PUBLIC pool,
//! deterministically from the beacon randomness. That gives an exact-size,
//! canonical jury — but the moment the beacon lands, EVERYONE can compute the
//! roster, so an adversary can begin targeting (bribing, DoSing, coercing)
//! the jurors before they ever act.
//!
//! VRF sortition inverts the reveal order. Each candidate PRIVATELY evaluates
//!
//! ```text
//! (beta, pi) = VRF_sk( SORTITION_DOMAIN ‖ beacon_randomness ‖ role )
//! ```
//!
//! and is selected iff a 64-bit prefix of `beta` falls below a public
//! threshold ([`SortitionThreshold`]). Until a selected member chooses to
//! reveal their [`SortitionTicket`], nobody else can enumerate the jury
//! (pseudorandomness); once revealed, anybody can verify membership
//! ([`verify_sortition`]) and nobody could have lied their way in
//! (uniqueness + the beacon's unbiasability). The trade against
//! `select_jury` is exactness: sortition yields a BINOMIAL jury size with
//! expectation `pool · p` (pick `SortitionThreshold::from_ratio(k, pool)`
//! for an expected size `k`), not an exact `k` — protocols that need a hard
//! quorum keep `select_jury` as the fallback or over-provision the
//! threshold. The two compose on the same beacon output: the SAME
//! `randomness` field of [`beacon::BeaconOutput`](crate::beacon::BeaconOutput)
//! is the `beacon_randomness` here, so the unbiasability analysis is shared.
//!
//! # Key class — composition with identity-cell pre-rotation
//!
//! A VRF key is a CURRENT-key-class member of an agent's identity cell, the
//! same class as the device signing keys: its 32-byte public key rides in the
//! identity cell's `key_set_commitment` (committed in
//! `CURRENT_KEYS_COMMIT_SLOT`), and the NEXT epoch's VRF public key is
//! pre-committed, unexposed, under `next_keys_digest` — so KERI-shaped
//! rotation covers sortition keys exactly as it covers signing keys, and a
//! thief who exfiltrates the current VRF secret loses it at the next
//! rotation without being able to block that rotation. ECVRF-EDWARDS25519
//! key generation IS RFC 8032 Ed25519 key generation (RFC 9381 §5.5 cites
//! RFC 8032 §5.1.5), so the SDK derives/commits these keys with
//! `ed25519-dalek` alone — see `dregg-sdk`'s `identity::vrf_public_key`;
//! the agreement is pinned by `keygen_agrees_with_ed25519_dalek` below.
//!
//! # Implementation notes (RFC section map)
//!
//! * Prove: §5.1. Verify: §5.3. Proof-to-hash: §5.2. Proof decode: §5.4.4
//!   (non-canonical `s` is REJECTED via `Scalar::from_canonical_bytes`).
//! * Encode-to-curve: §5.4.1.1 (try-and-increment), salt = the public key
//!   string, cofactor-cleared, identity rejected.
//! * Nonce: §5.4.2.2 (RFC 8032-style, deterministic — no RNG at prove time).
//! * Challenge: §5.4.3, truncated to `cLen = 16` bytes.
//! * Key validation: §5.4.5 / §5.6.1 — small-order (hence also identity)
//!   public keys are refused at decode, closing the §5.6.1 untrusted-key
//!   caveat for tickets arriving off the wire.
//! * Integer ↔ string conversions are little-endian per the edwards25519
//!   suites (§5.5 points at RFC 8032 conventions).
//!
//! All hashing is SHA-512 as the suite demands; the sortition ALPHA framing
//! is domain-separated under [`SORTITION_DOMAIN`] (audited against the
//! domain-tag census in [`crate::beacon`]'s module docs — collides with
//! none, prefix of none).

use curve25519_dalek::edwards::{CompressedEdwardsY, EdwardsPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::IsIdentity;
use sha2::{Digest, Sha512};

/// RFC 9381 §5.5: the ECVRF-EDWARDS25519-SHA512-TAI suite string.
pub const SUITE: u8 = 0x03;

/// Proof length `ptLen + cLen + qLen = 32 + 16 + 32` (RFC 9381 §5.5).
pub const PROOF_LEN: usize = 80;

/// Output (`beta_string`) length `hLen = 64` — SHA-512 (RFC 9381 §5.5).
pub const OUTPUT_LEN: usize = 64;

/// Challenge length `cLen = 16` (RFC 9381 §5.5).
const C_LEN: usize = 16;

/// Domain tag prefixing every sortition ALPHA. Distinct from every signed
/// domain tag in this crate (see the audit in [`crate::beacon`]).
pub const SORTITION_DOMAIN: &[u8] = b"dregg-vrf-sortition-v1";

/// The 64-byte VRF output (`beta_string`).
pub type VrfOutput = [u8; OUTPUT_LEN];

// =============================================================================
// Errors
// =============================================================================

/// Errors from the VRF layer. Every refusal is fail-closed: an `Err` ticket
/// confers NO membership.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VrfError {
    /// Public key bytes do not decode to a curve point, or decode to a
    /// small-order point (RFC 9381 §5.4.5 validate_key — required for keys
    /// arriving off the wire, §5.6.1).
    InvalidPublicKey,
    /// Proof bytes are the wrong length, `Gamma` does not decode to a curve
    /// point, or `s` is non-canonical (`s ≥ q`) — RFC 9381 §5.4.4 steps 2–6.
    InvalidProof,
    /// The §5.3 verification equation failed: recomputed challenge `c' ≠ c`.
    VerificationFailed,
    /// Try-and-increment exhausted all 256 counters (§5.4.1.1) — probability
    /// ≈ 2⁻²⁵⁶; surfaced rather than unwrapped so the caller's refusal path
    /// is total.
    EncodeToCurveFailed,
    /// A [`SortitionTicket`] verified as a VRF proof but its output is not
    /// under the threshold (or disagrees with the ticket's claimed output).
    NotSelected,
}

impl std::fmt::Display for VrfError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VrfError::InvalidPublicKey => write!(f, "invalid or small-order VRF public key"),
            VrfError::InvalidProof => write!(f, "malformed VRF proof encoding"),
            VrfError::VerificationFailed => write!(f, "VRF proof failed verification"),
            VrfError::EncodeToCurveFailed => write!(f, "encode_to_curve exhausted counters"),
            VrfError::NotSelected => write!(f, "VRF output not under the sortition threshold"),
        }
    }
}

impl std::error::Error for VrfError {}

// =============================================================================
// Suite primitives (RFC 9381 §5.4)
// =============================================================================

/// ECVRF_encode_to_curve, try-and-increment (RFC 9381 §5.4.1.1):
/// `hash_string = Hash(suite ‖ 0x01 ‖ salt ‖ alpha ‖ ctr ‖ 0x00)`, first 32
/// bytes interpreted as a compressed point (RFC 8032 decoding), cofactor
/// cleared, identity rejected. `salt` is the prover's compressed public key
/// (§5.4.1.1 with `encode_to_curve_salt = PK_string`).
fn encode_to_curve_tai(salt: &[u8; 32], alpha: &[u8]) -> Result<EdwardsPoint, VrfError> {
    for ctr in 0u8..=255 {
        let mut hasher = Sha512::new();
        hasher.update([SUITE, 0x01]); // suite_string ‖ encode_to_curve_domain_separator_front
        hasher.update(salt);
        hasher.update(alpha);
        hasher.update([ctr, 0x00]); // ctr_string ‖ encode_to_curve_domain_separator_back
        let digest = hasher.finalize();
        let candidate: [u8; 32] = digest[..32].try_into().expect("SHA-512 yields 64 bytes");
        if let Some(point) = CompressedEdwardsY(candidate).decompress() {
            // §5.4.1.1 step "H = cofactor * H": clear the cofactor so H lies
            // in the prime-order subgroup; reject the identity.
            let h = point.mul_by_cofactor();
            if !h.is_identity() {
                return Ok(h);
            }
        }
    }
    Err(VrfError::EncodeToCurveFailed)
}

/// ECVRF_challenge_generation (RFC 9381 §5.4.3):
/// `c = Hash(suite ‖ 0x02 ‖ PT(P1)‖…‖PT(P5) ‖ 0x00)[..cLen]`
/// with `(P1..P5) = (Y, H, Gamma, U, V)`.
fn challenge(points: [&[u8; 32]; 5]) -> [u8; C_LEN] {
    let mut hasher = Sha512::new();
    hasher.update([SUITE, 0x02]); // suite_string ‖ challenge_generation_domain_separator_front
    for p in points {
        hasher.update(p);
    }
    hasher.update([0x00]); // challenge_generation_domain_separator_back
    let digest = hasher.finalize();
    digest[..C_LEN].try_into().expect("SHA-512 yields 64 bytes")
}

/// The challenge as a scalar: `string_to_int` is little-endian for the
/// edwards25519 suites (RFC 9381 §5.5 / RFC 8032), and `c < 2¹²⁸ < q` so the
/// embedding is exact.
fn challenge_scalar(c: &[u8; C_LEN]) -> Scalar {
    let mut wide = [0u8; 32];
    wide[..C_LEN].copy_from_slice(c);
    Scalar::from_bytes_mod_order(wide)
}

// =============================================================================
// Keys
// =============================================================================

/// A VRF public key: a non-small-order point on edwards25519.
///
/// Key class: a CURRENT-key-class member of the holding agent's identity
/// cell (committed via `key_set_commitment`; the next epoch's key sits
/// pre-committed under `next_keys_digest`) — see the module docs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VrfPublicKey {
    point: EdwardsPoint,
    bytes: [u8; 32],
}

impl VrfPublicKey {
    /// Decode and VALIDATE a public key (RFC 9381 §5.4.5, full check):
    /// refuses non-points and small-order points. Always use this for keys
    /// arriving off the wire (§5.6.1).
    pub fn from_bytes(bytes: &[u8; 32]) -> Result<Self, VrfError> {
        let point = CompressedEdwardsY(*bytes)
            .decompress()
            .ok_or(VrfError::InvalidPublicKey)?;
        if point.is_small_order() {
            return Err(VrfError::InvalidPublicKey);
        }
        Ok(Self {
            point,
            bytes: *bytes,
        })
    }

    /// The compressed-point encoding (RFC 8032 §5.1.2) — byte-identical to
    /// the Ed25519 verifying key of the same seed.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.bytes
    }

    /// ECVRF_verify (RFC 9381 §5.3): recompute `H`, then
    /// `U = s·B − c·Y`, `V = s·H − c·Gamma`, and accept iff the recomputed
    /// challenge over `(Y, H, Gamma, U, V)` equals the proof's `c`.
    /// Returns the (unique) output `beta` on success.
    ///
    /// Variable-time group arithmetic is deliberate: every input here is
    /// public verifier-side data.
    pub fn verify(&self, alpha: &[u8], proof: &VrfProof) -> Result<VrfOutput, VrfError> {
        let h = encode_to_curve_tai(&self.bytes, alpha)?;
        let c = challenge_scalar(&proof.c);
        // U = s·B − c·Y  (computed as (−c)·Y + s·B)
        let u = EdwardsPoint::vartime_double_scalar_mul_basepoint(&-c, &self.point, &proof.s);
        // V = s·H − c·Gamma
        let v = h * proof.s - proof.gamma * c;
        let c_prime = challenge([
            &self.bytes,
            &h.compress().to_bytes(),
            &proof.gamma.compress().to_bytes(),
            &u.compress().to_bytes(),
            &v.compress().to_bytes(),
        ]);
        if c_prime == proof.c {
            Ok(proof.output())
        } else {
            Err(VrfError::VerificationFailed)
        }
    }
}

/// A VRF secret key, expanded from a 32-byte seed exactly as RFC 8032 §5.1.5
/// expands an Ed25519 seed (RFC 9381 §5.5: the ECVRF key pair IS an Ed25519
/// key pair). Holds the clamped scalar and the nonce-derivation half of the
/// seed hash.
#[derive(Clone)]
pub struct VrfSecretKey {
    /// Clamped secret scalar `x` (RFC 8032 §5.1.5 step 2), reduced mod `q`
    /// — sound because every point it multiplies here lies in the
    /// prime-order subgroup (`B` by definition, `H` by cofactor clearing).
    x: Scalar,
    /// The second 32 bytes of `SHA-512(seed)` — the §5.4.2.2 nonce key.
    nonce_key: [u8; 32],
    public: VrfPublicKey,
}

impl std::fmt::Debug for VrfSecretKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VrfSecretKey")
            .field("public", &hex::encode(self.public.bytes))
            .finish_non_exhaustive()
    }
}

impl VrfSecretKey {
    /// Expand a 32-byte seed (RFC 8032 §5.1.5): `h = SHA-512(seed)`;
    /// `x` = clamp(`h[0..32]`); nonce key = `h[32..64]`; `Y = x·B`.
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        let h = Sha512::digest(seed);
        let mut x_bytes: [u8; 32] = h[..32].try_into().expect("SHA-512 yields 64 bytes");
        // RFC 8032 §5.1.5 clamping.
        x_bytes[0] &= 248;
        x_bytes[31] &= 127;
        x_bytes[31] |= 64;
        let x = Scalar::from_bytes_mod_order(x_bytes);
        let mut nonce_key = [0u8; 32];
        nonce_key.copy_from_slice(&h[32..]);
        let point = EdwardsPoint::mul_base(&x);
        let bytes = point.compress().to_bytes();
        Self {
            x,
            nonce_key,
            public: VrfPublicKey { point, bytes },
        }
    }

    /// Fresh key from OS entropy.
    pub fn generate() -> Self {
        let mut seed = [0u8; 32];
        getrandom::fill(&mut seed).expect("OS entropy unavailable");
        Self::from_seed(&seed)
    }

    /// The corresponding public key.
    pub fn public(&self) -> &VrfPublicKey {
        &self.public
    }

    /// ECVRF_prove (RFC 9381 §5.1): returns `(beta, pi)`. Deterministic —
    /// the nonce is §5.4.2.2 (hash-derived), so proving never touches an
    /// RNG and repeated calls yield byte-identical proofs.
    pub fn prove(&self, alpha: &[u8]) -> Result<(VrfOutput, VrfProof), VrfError> {
        // §5.1 step 2: H = encode_to_curve(salt = PK_string, alpha).
        let h = encode_to_curve_tai(&self.public.bytes, alpha)?;
        let h_bytes = h.compress().to_bytes();
        // Step 4: Gamma = x·H.
        let gamma = h * self.x;
        // Step 5 via §5.4.2.2: k = SHA-512(nonce_key ‖ h_string) mod q.
        let mut hasher = Sha512::new();
        hasher.update(self.nonce_key);
        hasher.update(h_bytes);
        let mut wide = [0u8; 64];
        wide.copy_from_slice(&hasher.finalize());
        let k = Scalar::from_bytes_mod_order_wide(&wide);
        // Step 6: c = challenge(Y, H, Gamma, k·B, k·H).
        let u = EdwardsPoint::mul_base(&k);
        let v = h * k;
        let c = challenge([
            &self.public.bytes,
            &h_bytes,
            &gamma.compress().to_bytes(),
            &u.compress().to_bytes(),
            &v.compress().to_bytes(),
        ]);
        // Step 7: s = (k + c·x) mod q.
        let s = k + challenge_scalar(&c) * self.x;
        let proof = VrfProof { gamma, c, s };
        Ok((proof.output(), proof))
    }
}

// =============================================================================
// Proofs
// =============================================================================

/// An ECVRF proof `pi = (Gamma, c, s)`; wire form is the 80-byte
/// `point_to_string(Gamma) ‖ int_to_string(c, 16) ‖ int_to_string(s, 32)`
/// (RFC 9381 §5.1 step 8).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VrfProof {
    gamma: EdwardsPoint,
    c: [u8; C_LEN],
    s: Scalar,
}

impl VrfProof {
    /// ECVRF_decode_proof (RFC 9381 §5.4.4): refuses wrong lengths,
    /// non-point `Gamma`, and non-canonical `s ≥ q` (step 6 — REQUIRED; a
    /// malleable `s` would break uniqueness).
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, VrfError> {
        if bytes.len() != PROOF_LEN {
            return Err(VrfError::InvalidProof);
        }
        let gamma_bytes: [u8; 32] = bytes[..32].try_into().expect("length checked");
        let gamma = CompressedEdwardsY(gamma_bytes)
            .decompress()
            .ok_or(VrfError::InvalidProof)?;
        let c: [u8; C_LEN] = bytes[32..48].try_into().expect("length checked");
        let s_bytes: [u8; 32] = bytes[48..].try_into().expect("length checked");
        let s = Option::<Scalar>::from(Scalar::from_canonical_bytes(s_bytes))
            .ok_or(VrfError::InvalidProof)?;
        Ok(Self { gamma, c, s })
    }

    /// The 80-byte wire encoding (§5.1 step 8).
    pub fn to_bytes(&self) -> [u8; PROOF_LEN] {
        let mut out = [0u8; PROOF_LEN];
        out[..32].copy_from_slice(self.gamma.compress().as_bytes());
        out[32..48].copy_from_slice(&self.c);
        out[48..].copy_from_slice(&self.s.to_bytes());
        out
    }

    /// ECVRF_proof_to_hash (RFC 9381 §5.2):
    /// `beta = Hash(suite ‖ 0x03 ‖ PT(cofactor·Gamma) ‖ 0x00)`.
    pub fn output(&self) -> VrfOutput {
        let point = self.gamma.mul_by_cofactor();
        let mut hasher = Sha512::new();
        hasher.update([SUITE, 0x03]); // suite_string ‖ proof_to_hash_domain_separator_front
        hasher.update(point.compress().as_bytes());
        hasher.update([0x00]); // proof_to_hash_domain_separator_back
        let mut beta = [0u8; OUTPUT_LEN];
        beta.copy_from_slice(&hasher.finalize());
        beta
    }
}

// =============================================================================
// Sortition
// =============================================================================

/// The ALPHA string a sortition evaluation signs over:
/// `SORTITION_DOMAIN ‖ beacon_randomness ‖ role`. The domain tag and the
/// beacon field are fixed-width, so the framing is unambiguous without
/// length prefixes; `role` names the duty being drawn for (e.g.
/// `b"equivocation-court/epoch-7"`), keeping one beacon output reusable
/// across roles without cross-role replay.
pub fn sortition_alpha(beacon_randomness: &[u8; 32], role: &[u8]) -> Vec<u8> {
    let mut alpha = Vec::with_capacity(SORTITION_DOMAIN.len() + 32 + role.len());
    alpha.extend_from_slice(SORTITION_DOMAIN);
    alpha.extend_from_slice(beacon_randomness);
    alpha.extend_from_slice(role);
    alpha
}

/// A public selection bar: an agent is selected iff the BIG-ENDIAN `u64`
/// prefix of its `beta` output is strictly below the bar. Internally the
/// bar lives in `[0, 2⁶⁴]` (one past `u64::MAX`, so probability 1 is
/// representable exactly).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SortitionThreshold(u128);

impl SortitionThreshold {
    /// Selects nobody.
    pub const NEVER: Self = Self(0);
    /// Selects everybody.
    pub const ALWAYS: Self = Self(1u128 << 64);

    /// The bar for per-agent selection probability `num/den`:
    /// `⌊2⁶⁴·num/den⌋`. For an EXPECTED jury of size `k` from a pool of `n`
    /// candidates, use `from_ratio(k, n)`. `None` iff `den == 0` or
    /// `num > den`. Floor rounding under-selects by less than 2⁻⁶⁴ —
    /// negligible against the binomial variance.
    pub fn from_ratio(num: u64, den: u64) -> Option<Self> {
        if den == 0 || num > den {
            return None;
        }
        Some(Self(((num as u128) << 64) / den as u128))
    }

    /// Does `output` fall under the bar?
    pub fn admits(&self, output: &VrfOutput) -> bool {
        let prefix = u64::from_be_bytes(output[..8].try_into().expect("beta is 64 bytes"));
        (prefix as u128) < self.0
    }
}

/// A revealed claim of sortition membership: the claimant's VRF public key
/// (which the verifier must bind to an admitted identity — the identity
/// cell's `key_set_commitment` opening is that binding), the proof, and the
/// claimed output. Wire form: [`SortitionTicket::to_bytes`] (176 bytes;
/// higher-level serde is the transport layer's concern).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SortitionTicket {
    /// The claimant's VRF public key (CURRENT-key-class; see module docs).
    pub public_key: [u8; 32],
    /// The 80-byte ECVRF proof over [`sortition_alpha`].
    pub proof: [u8; PROOF_LEN],
    /// The claimed `beta` (redundant with `proof` — verification recomputes
    /// and refuses disagreement; carried so relays can sort/deduplicate
    /// without doing curve work).
    pub output: VrfOutput,
}

impl SortitionTicket {
    /// `public_key ‖ proof ‖ output` — 176 bytes.
    pub fn to_bytes(&self) -> [u8; 32 + PROOF_LEN + OUTPUT_LEN] {
        let mut out = [0u8; 32 + PROOF_LEN + OUTPUT_LEN];
        out[..32].copy_from_slice(&self.public_key);
        out[32..32 + PROOF_LEN].copy_from_slice(&self.proof);
        out[32 + PROOF_LEN..].copy_from_slice(&self.output);
        out
    }

    /// Inverse of [`Self::to_bytes`]. Purely structural — call
    /// [`verify_sortition`] before believing anything about the contents.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, VrfError> {
        if bytes.len() != 32 + PROOF_LEN + OUTPUT_LEN {
            return Err(VrfError::InvalidProof);
        }
        Ok(Self {
            public_key: bytes[..32].try_into().expect("length checked"),
            proof: bytes[32..32 + PROOF_LEN]
                .try_into()
                .expect("length checked"),
            output: bytes[32 + PROOF_LEN..].try_into().expect("length checked"),
        })
    }
}

/// Self-selection: evaluate the VRF privately over
/// `sortition_alpha(beacon_randomness, role)` and, iff the output clears
/// `threshold`, return the revealable [`SortitionTicket`]. `Ok(None)` means
/// honestly not selected this round — there is nothing to grind, because
/// for this `(sk, beacon, role)` the output is UNIQUE.
///
/// `beacon_randomness` is the `randomness` field of a verified
/// [`crate::beacon::BeaconOutput`] — unbiasable, so a coalition cannot steer
/// the seed toward its own tickets.
pub fn sortition_select(
    beacon_randomness: &[u8; 32],
    sk: &VrfSecretKey,
    role: &[u8],
    threshold: SortitionThreshold,
) -> Result<Option<SortitionTicket>, VrfError> {
    let alpha = sortition_alpha(beacon_randomness, role);
    let (output, proof) = sk.prove(&alpha)?;
    Ok(threshold.admits(&output).then(|| SortitionTicket {
        public_key: sk.public().to_bytes(),
        proof: proof.to_bytes(),
        output,
    }))
}

/// Verify a revealed ticket: full key validation (§5.4.5), full proof
/// verification (§5.3) over the SAME alpha framing the prover used, the
/// ticket's claimed output must be the recomputed one, and the output must
/// clear `threshold`. Returns the verified `beta` (usable downstream as a
/// tie-break / ordering weight among selected members).
///
/// This checks the CRYPTOGRAPHIC claim only; the caller still binds
/// `ticket.public_key` to an admitted identity (the identity cell's current
/// key-set opening) before seating the juror.
pub fn verify_sortition(
    beacon_randomness: &[u8; 32],
    role: &[u8],
    threshold: SortitionThreshold,
    ticket: &SortitionTicket,
) -> Result<VrfOutput, VrfError> {
    let pk = VrfPublicKey::from_bytes(&ticket.public_key)?;
    let proof = VrfProof::from_bytes(&ticket.proof)?;
    let alpha = sortition_alpha(beacon_randomness, role);
    let output = pk.verify(&alpha, &proof)?;
    if output != ticket.output || !threshold.admits(&output) {
        return Err(VrfError::NotSelected);
    }
    Ok(output)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn seed_from_hex(s: &str) -> [u8; 32] {
        hex::decode(s).unwrap().try_into().unwrap()
    }

    // ── RFC 9381 Appendix B.3 vectors (ECVRF-EDWARDS25519-SHA512-TAI) ──────
    // (SK, PK, alpha_hex, pi_string, beta_string) — Examples 16, 17, 18.
    // The SK/PK pairs are the RFC 8032 §7.1 TEST 1–3 Ed25519 vectors, which
    // independently pins keygen agreement.
    const B3_VECTORS: [(&str, &str, &str, &str, &str); 3] = [
        (
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
            "",
            "8657106690b5526245a92b003bb079ccd1a92130477671f6fc01ad16f26f723f26f8a57ccaed74ee1b190bed1f479d9727d2d0f9b005a6e456a35d4fb0daab1268a1b0db10836d9826a528ca76567805",
            "90cf1df3b703cce59e2a35b925d411164068269d7b2d29f3301c03dd757876ff66b71dda49d2de59d03450451af026798e8f81cd2e333de5cdf4f3e140fdd8ae",
        ),
        (
            "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
            "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
            "72",
            "f3141cd382dc42909d19ec5110469e4feae18300e94f304590abdced48aed5933bf0864a62558b3ed7f2fea45c92a465301b3bbf5e3e54ddf2d935be3b67926da3ef39226bbc355bdc9850112c8f4b02",
            "eb4440665d3891d668e7e0fcaf587f1b4bd7fbfe99d0eb2211ccec90496310eb5e33821bc613efb94db5e5b54c70a848a0bef4553a41befc57663b56373a5031",
        ),
        (
            "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7",
            "fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025",
            "af82",
            "9bc0f79119cc5604bf02d23b4caede71393cedfbb191434dd016d30177ccbf8096bb474e53895c362d8628ee9f9ea3c0e52c7a5c691b6c18c9979866568add7a2d41b00b05081ed0f58ee5e31b3a970e",
            "645427e5d00c62a23fb703732fa5d892940935942101e456ecca7bb217c61c452118fec1219202a0edcf038bb6373241578be7217ba85a2687f7a0310b2df19f",
        ),
    ];

    #[test]
    fn rfc9381_b3_vectors_prove_and_verify() {
        for (sk_hex, pk_hex, alpha_hex, pi_hex, beta_hex) in B3_VECTORS {
            let sk = VrfSecretKey::from_seed(&seed_from_hex(sk_hex));
            assert_eq!(hex::encode(sk.public().to_bytes()), pk_hex, "keygen");
            let alpha = hex::decode(alpha_hex).unwrap();
            let (beta, proof) = sk.prove(&alpha).unwrap();
            assert_eq!(hex::encode(proof.to_bytes()), pi_hex, "pi_string");
            assert_eq!(hex::encode(beta), beta_hex, "beta_string");
            // Round-trip the wire form and verify from the public side only.
            let pk = VrfPublicKey::from_bytes(&sk.public().to_bytes()).unwrap();
            let decoded = VrfProof::from_bytes(&proof.to_bytes()).unwrap();
            assert_eq!(pk.verify(&alpha, &decoded).unwrap(), beta, "verify");
        }
    }

    /// ECVRF-EDWARDS25519 keygen IS RFC 8032 keygen — the weld the SDK's
    /// `identity::vrf_public_key` (which uses ed25519-dalek alone) rides on.
    #[test]
    fn keygen_agrees_with_ed25519_dalek() {
        for seed_byte in [0u8, 1, 7, 42, 255] {
            let seed = [seed_byte; 32];
            let vrf_pk = VrfSecretKey::from_seed(&seed).public().to_bytes();
            let ed_pk = ed25519_dalek::SigningKey::from_bytes(&seed)
                .verifying_key()
                .to_bytes();
            assert_eq!(vrf_pk, ed_pk);
        }
    }

    // ── Determinism + uniqueness ───────────────────────────────────────────

    #[test]
    fn proving_is_deterministic() {
        let sk = VrfSecretKey::from_seed(&[9u8; 32]);
        let (b1, p1) = sk.prove(b"alpha").unwrap();
        let (b2, p2) = sk.prove(b"alpha").unwrap();
        assert_eq!(b1, b2);
        assert_eq!(p1.to_bytes(), p2.to_bytes());
    }

    /// Uniqueness as enforced surface: the output is a function of Gamma
    /// alone, and the verifier recomputes it — a prover cannot present a
    /// second beta for the same (pk, alpha) without forging a second
    /// verifying proof, which the tamper tests below refuse byte-by-byte.
    #[test]
    fn outputs_are_distinct_across_keys_and_alphas() {
        let mut seen = std::collections::HashSet::new();
        for i in 0u8..16 {
            let sk = VrfSecretKey::from_seed(&[i; 32]);
            for alpha in [b"role-a".as_slice(), b"role-b".as_slice()] {
                let (beta, _) = sk.prove(alpha).unwrap();
                assert!(seen.insert(beta.to_vec()), "collision at key {i}");
            }
        }
    }

    // ── Verify refuses tamper ──────────────────────────────────────────────

    #[test]
    fn verify_refuses_every_single_bit_flip_in_the_proof() {
        let sk = VrfSecretKey::from_seed(&[3u8; 32]);
        let alpha = b"the-jury-draw";
        let (_, proof) = sk.prove(alpha).unwrap();
        let pk = VrfPublicKey::from_bytes(&sk.public().to_bytes()).unwrap();
        let pi = proof.to_bytes();
        for byte in 0..PROOF_LEN {
            for bit in 0..8 {
                let mut tampered = pi;
                tampered[byte] ^= 1 << bit;
                // Either the encoding is refused (gamma off-curve /
                // non-canonical s) or the §5.3 equation fails — never Ok.
                let refused = match VrfProof::from_bytes(&tampered) {
                    Err(_) => true,
                    Ok(p) => pk.verify(alpha, &p).is_err(),
                };
                assert!(refused, "tampered bit {bit} of byte {byte} accepted");
            }
        }
    }

    #[test]
    fn verify_refuses_wrong_alpha_and_wrong_key() {
        let sk = VrfSecretKey::from_seed(&[4u8; 32]);
        let (_, proof) = sk.prove(b"intended-context").unwrap();
        let pk = VrfPublicKey::from_bytes(&sk.public().to_bytes()).unwrap();
        assert_eq!(
            pk.verify(b"other-context", &proof),
            Err(VrfError::VerificationFailed)
        );
        let other = VrfSecretKey::from_seed(&[5u8; 32]);
        let other_pk = VrfPublicKey::from_bytes(&other.public().to_bytes()).unwrap();
        assert_eq!(
            other_pk.verify(b"intended-context", &proof),
            Err(VrfError::VerificationFailed)
        );
    }

    #[test]
    fn proof_decode_refuses_noncanonical_s_and_bad_lengths() {
        let sk = VrfSecretKey::from_seed(&[6u8; 32]);
        let (_, proof) = sk.prove(b"x").unwrap();
        let mut pi = proof.to_bytes();
        // Force s ≥ q: set the top bytes of the little-endian s limb high.
        for b in &mut pi[48..] {
            *b = 0xff;
        }
        assert_eq!(VrfProof::from_bytes(&pi), Err(VrfError::InvalidProof));
        assert_eq!(
            VrfProof::from_bytes(&[0u8; 79]),
            Err(VrfError::InvalidProof)
        );
        assert_eq!(
            VrfProof::from_bytes(&[0u8; 81]),
            Err(VrfError::InvalidProof)
        );
    }

    #[test]
    fn small_order_public_key_is_refused() {
        // The identity's compressed encoding: y = 1.
        let mut identity = [0u8; 32];
        identity[0] = 1;
        assert_eq!(
            VrfPublicKey::from_bytes(&identity),
            Err(VrfError::InvalidPublicKey)
        );
    }

    // ── Sortition ──────────────────────────────────────────────────────────

    #[test]
    fn threshold_endpoints_and_ratio() {
        assert_eq!(
            SortitionThreshold::from_ratio(1, 1),
            Some(SortitionThreshold::ALWAYS)
        );
        assert_eq!(
            SortitionThreshold::from_ratio(0, 7),
            Some(SortitionThreshold::NEVER)
        );
        assert_eq!(SortitionThreshold::from_ratio(2, 1), None);
        assert_eq!(SortitionThreshold::from_ratio(1, 0), None);
        assert!(SortitionThreshold::from_ratio(1, 2) < SortitionThreshold::from_ratio(2, 3));
    }

    #[test]
    fn sortition_select_and_verify_round_trip() {
        let beacon = [0xabu8; 32];
        let role = b"equivocation-court/epoch-7";
        let sk = VrfSecretKey::from_seed(&[11u8; 32]);
        let ticket = sortition_select(&beacon, &sk, role, SortitionThreshold::ALWAYS)
            .unwrap()
            .expect("ALWAYS selects");
        let beta = verify_sortition(&beacon, role, SortitionThreshold::ALWAYS, &ticket).unwrap();
        assert_eq!(beta, ticket.output);
        // Wire round-trip.
        let again = SortitionTicket::from_bytes(&ticket.to_bytes()).unwrap();
        assert_eq!(again, ticket);
        // NEVER selects nobody, and refuses the same ticket.
        assert_eq!(
            sortition_select(&beacon, &sk, role, SortitionThreshold::NEVER).unwrap(),
            None
        );
        assert_eq!(
            verify_sortition(&beacon, role, SortitionThreshold::NEVER, &ticket),
            Err(VrfError::NotSelected)
        );
    }

    #[test]
    fn sortition_verify_refuses_tampered_tickets() {
        let beacon = [0x55u8; 32];
        let role = b"role";
        let sk = VrfSecretKey::from_seed(&[12u8; 32]);
        let ticket = sortition_select(&beacon, &sk, role, SortitionThreshold::ALWAYS)
            .unwrap()
            .unwrap();
        // Claimed-output tamper (proof still valid): refused.
        let mut lied = ticket;
        lied.output[0] ^= 1;
        assert!(verify_sortition(&beacon, role, SortitionThreshold::ALWAYS, &lied).is_err());
        // Different beacon / role: refused (no replay across draws).
        assert!(verify_sortition(&[0u8; 32], role, SortitionThreshold::ALWAYS, &ticket).is_err());
        assert!(
            verify_sortition(&beacon, b"other-role", SortitionThreshold::ALWAYS, &ticket).is_err()
        );
        // Substituted public key: refused.
        let mut stolen = ticket;
        stolen.public_key = VrfSecretKey::from_seed(&[13u8; 32]).public().to_bytes();
        assert!(verify_sortition(&beacon, role, SortitionThreshold::ALWAYS, &stolen).is_err());
    }

    /// Selection rate tracks the threshold (loose binomial bounds:
    /// 64 candidates at p = 1/2; P(outside [16, 48]) < 10⁻⁴).
    #[test]
    fn sortition_rate_tracks_threshold() {
        let beacon = [0x77u8; 32];
        let role = b"rate-check";
        let half = SortitionThreshold::from_ratio(1, 2).unwrap();
        let mut selected = 0usize;
        for i in 0u8..64 {
            let sk = VrfSecretKey::from_seed(&[i; 32]);
            if sortition_select(&beacon, &sk, role, half)
                .unwrap()
                .is_some()
            {
                selected += 1;
            }
        }
        assert!(
            (16..=48).contains(&selected),
            "selection rate wildly off: {selected}/64 at p=1/2"
        );
    }

    /// Nobody can enumerate the jury before reveal — operationally: the
    /// ticket is computable only with the secret key (here: the public key
    /// alone gives no selection oracle; we check the public surface exposes
    /// verify-of-a-claim, not evaluate). This is the pseudorandomness
    /// property (RFC 9381 §3.3); the test pins the API shape that carries it.
    #[test]
    fn selection_requires_the_secret_key_api_shape() {
        let beacon = [0x99u8; 32];
        let sk = VrfSecretKey::from_seed(&[21u8; 32]);
        let ticket = sortition_select(&beacon, &sk, b"r", SortitionThreshold::ALWAYS)
            .unwrap()
            .unwrap();
        // A verifier learns membership only AFTER the holder reveals: the
        // only public-side operation over (pk, alpha) is verify(ticket).
        assert!(verify_sortition(&beacon, b"r", SortitionThreshold::ALWAYS, &ticket).is_ok());
    }
}
