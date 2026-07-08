//! FROST (threshold-Schnorr) quorum certificates — the ADDITIVE alternative to
//! the BLS path in [`crate::threshold`], per `docs/FROST-MIGRATION.md`.
//!
//! The Lean spec is `metatheory/Dregg2/Crypto/Frost.lean`
//! (`frost_cert_verifies_under_group_key`): a t-of-n FROST certificate IS a
//! single ordinary Schnorr signature `(R, z)` verified by the single-signer
//! verifier `z·g = R + e·pk` under the federation's GROUP public key —
//! constant-size regardless of committee size, resting only on the
//! discrete-log carrier (the same ed25519 curve every vote signature already
//! uses), with NO pairing and NO trusted KZG setup.
//!
//! # What lives here (additive stage — BLS is untouched)
//!
//! * [`FrostQC`] — the certificate: exactly one 64-byte ed25519-shaped Schnorr
//!   signature `(R ‖ z)`. Compare `threshold::ThresholdQC` (BLS aggregate +
//!   SNARK proof, arkworks-serialized, ~4x larger and pairing-verified).
//! * [`verify_frost_quorum`] — the group-key verify: RFC 8032 ed25519
//!   `verify_strict` under the group [`PublicKey`]. This is byte-for-byte the
//!   verifier a FROST(Ed25519, SHA-512) signing ceremony (RFC 9591) targets,
//!   so a later cutover to a vetted `frost-ed25519` signing stack changes
//!   NOTHING on the verify side.
//! * [`QuorumScheme`] — the scheme selector over the opaque
//!   `dregg_types::ThresholdQC` bytes carried in `AttestedRoot.threshold_qc` /
//!   wire messages, so a verifier holding either a BLS committee or a FROST
//!   group key dispatches without the carried types changing shape.
//! * [`FrostTestDealer`] / [`frost_sign`] — a TRUSTED-DEALER Shamir keygen and
//!   a single-ceremony signing helper that realizes the Lean theorem's exact
//!   algebra (Lagrange-combined partial responses `z_i = k_i + e·λ_i·x_i`).
//! * [`HybridQC`] / [`verify_hybrid_quorum`] — the HYBRID certificate: the
//!   FROST aggregate AND per-signer FIPS 204 ML-DSA-65 signatures, accepted
//!   only when BOTH halves verify (the Lean `hybridVerify = classical ∧ pq`),
//!   so the quorum survives a quantum adversary that breaks the discrete-log
//!   half (`hybrid_survives_classical_break`). Additive and staged behind
//!   [`QuorumScheme::Hybrid`], not wired into live consensus.
//!
//! # Production-signing boundary (read before wiring signers)
//!
//! [`frost_sign`] omits RFC 9591's per-signer binding factors (the two-nonce
//! `ρ` mechanism that defeats the Drijvers/ROS concurrent-session attack) and
//! [`FrostTestDealer`] centralizes the group secret in a dealer. Both are fit
//! for tests, differentials against the Lean spec, and single-ceremony
//! fixtures — NOT for live concurrent signing. The migration plan's signing
//! stage adopts the vetted `frost-ed25519` crate (Zcash Foundation, audited)
//! for nonce generation/aggregation and ports `crate::dkg`'s JF-DKG to the
//! edwards group for dealerless keygen; the verify side below is already the
//! final one.

use curve25519_dalek::edwards::EdwardsPoint;
use curve25519_dalek::scalar::Scalar;
use fips204::ml_dsa_65;
use fips204::traits::{KeyGen as _, SerDes as _, Signer as _, Verifier as _};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha512};

use dregg_types::{PublicKey, Signature};

/// Size in bytes of a serialized [`FrostQC`]: one Schnorr signature `(R ‖ z)`.
pub const FROST_QC_BYTES: usize = 64;

// =============================================================================
// FrostQC — the certificate
// =============================================================================

/// A FROST quorum certificate: ONE ordinary Schnorr signature under the
/// federation's group public key.
///
/// Constant-size for any committee size and any signing subset — the verifier
/// cannot even tell which t-subset signed (`frost_cert_verifies_under_group_key`
/// has no dependence on `t`, `n`, or `parts`). Threshold enforcement is a
/// SIGNING-side fact: fewer than `t` Shamir shares cannot Lagrange-reconstruct
/// the group secret's response, so no sub-threshold subset can produce a
/// verifying certificate (see `sub_threshold_subset_cannot_forge` below).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrostQC {
    /// The Schnorr signature `(R ‖ z)`: 32-byte compressed nonce point,
    /// 32-byte response scalar — the ed25519 wire shape.
    pub signature: Signature,
}

impl FrostQC {
    /// Serialize: exactly the 64 signature bytes.
    pub fn to_bytes(&self) -> Vec<u8> {
        self.signature.0.to_vec()
    }

    /// Deserialize from exactly [`FROST_QC_BYTES`] bytes.
    ///
    /// A BLS `threshold::ThresholdQC` serialization is larger (aggregate +
    /// SNARK proof), so the two schemes' opaque bytes cannot be confused by
    /// length alone; [`QuorumScheme`] still dispatches explicitly.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let arr: [u8; FROST_QC_BYTES] = bytes.try_into().ok()?;
        Some(Self {
            signature: Signature(arr),
        })
    }
}

// =============================================================================
// The group-key verify — the Lean `SchnorrVerifies` relation
// =============================================================================

/// Verify a FROST quorum certificate under the federation's group public key.
///
/// This is the single-signer Schnorr verifier the Lean spec reuses verbatim
/// (`SchnorrVerifies g pk R e z ↔ z·g = R + e·pk`), instantiated at ed25519:
/// `e = SHA-512(R ‖ A ‖ M) mod ℓ` and the check is `z·B = R + e·A`, exactly
/// RFC 8032 — via `verify_strict` (no cofactor slack, R and A must be
/// canonical), so a certificate that verifies here verifies as a plain
/// ed25519 signature everywhere else too.
pub fn verify_frost_quorum(group_key: &PublicKey, message: &[u8], qc: &FrostQC) -> bool {
    let Ok(vk) = ed25519_dalek::VerifyingKey::from_bytes(&group_key.0) else {
        return false;
    };
    let sig = ed25519_dalek::Signature::from_bytes(&qc.signature.0);
    vk.verify_strict(message, &sig).is_ok()
}

// =============================================================================
// QuorumScheme — the additive selector over opaque QC bytes
// =============================================================================

/// Which threshold-signature scheme a quorum certificate's opaque bytes carry.
///
/// The transition seam: `AttestedRoot.threshold_qc`, the wire
/// `AttestedRoot{,Push}` messages, and `persist`'s `StoredAttestedRoot` all
/// carry `dregg_types::ThresholdQC(Vec<u8>)` — scheme-opaque bytes. During the
/// migration BOTH schemes are valid; a verifier holds whichever context it has
/// and dispatches here. BLS verification is delegated unchanged to
/// [`crate::threshold::FederationCommittee::verify`].
pub enum QuorumScheme<'a> {
    /// The incumbent weighted-threshold BLS path (`hints`, pairing + KZG).
    Bls(&'a crate::threshold::FederationCommittee),
    /// The FROST path: everything the verifier needs is ONE 32-byte group key.
    Frost {
        /// The federation's group public key (Shamir secret in the exponent).
        group_key: PublicKey,
    },
    /// The HYBRID path: the FROST group key AND the committee's ML-DSA-65
    /// public keys. A certificate is a quorum only if BOTH halves verify —
    /// the classical aggregate under `group_key` and ≥ `threshold` distinct
    /// ML-DSA signatures under `ml_dsa_pubkeys` (the PQ half re-imposes the
    /// threshold explicitly, since ML-DSA has no threshold aggregation).
    Hybrid {
        /// The federation's group public key (the classical half).
        group_key: PublicKey,
        /// One ML-DSA-65 public key per committee member, member `i` at
        /// position `i` (the post-quantum half).
        ml_dsa_pubkeys: &'a [MlDsaPublicKey],
        /// Minimum count of distinct, valid ML-DSA signatures required.
        threshold: usize,
    },
}

impl QuorumScheme<'_> {
    /// Verify opaque quorum-certificate bytes (as carried in
    /// `AttestedRoot.threshold_qc` and the wire messages) against `message`
    /// under this scheme.
    pub fn verify_opaque_qc(&self, qc_bytes: &[u8], message: &[u8]) -> bool {
        match self {
            QuorumScheme::Bls(committee) => {
                match crate::threshold::ThresholdQC::from_bytes(qc_bytes) {
                    Some(qc) => committee.verify(&qc, message).is_ok(),
                    None => false,
                }
            }
            QuorumScheme::Frost { group_key } => match FrostQC::from_bytes(qc_bytes) {
                Some(qc) => verify_frost_quorum(group_key, message, &qc),
                None => false,
            },
            QuorumScheme::Hybrid {
                group_key,
                ml_dsa_pubkeys,
                threshold,
            } => match HybridQC::from_bytes(qc_bytes) {
                Some(qc) => {
                    verify_hybrid_quorum(group_key, ml_dsa_pubkeys, message, &qc, *threshold)
                }
                None => false,
            },
        }
    }
}

// =============================================================================
// Trusted-dealer keygen + single-ceremony signing (the Lean theorem's algebra)
// =============================================================================

/// One member's Shamir share of the group secret, dealt by [`FrostTestDealer`].
#[derive(Clone)]
pub struct FrostShare {
    /// 1-based Shamir evaluation index (x-coordinate; 0 is the group secret).
    pub index: u64,
    /// The share scalar `f(index)`.
    share: Scalar,
}

impl FrostShare {
    /// This member's share verification key `x_i·B` (for future
    /// partial-signature audit; unused by the certificate verifier).
    pub fn share_public(&self) -> PublicKey {
        PublicKey(EdwardsPoint::mul_base(&self.share).compress().to_bytes())
    }
}

/// Trusted-dealer Shamir keygen over the ed25519 scalar field.
///
/// The dealer transiently knows the group secret — exactly the property the
/// production DKG stage removes (port of `crate::dkg`'s JF-DKG, where
/// `f(0) = Σ f_i(0)` never exists in one place). Fit for tests and fixtures.
pub struct FrostTestDealer {
    /// The group public key `A = f(0)·B`.
    pub group_key: PublicKey,
    /// The signing threshold `t` (shares needed to reconstruct at 0).
    pub threshold: u64,
    /// All dealt shares, index `i+1` at position `i`.
    pub shares: Vec<FrostShare>,
}

impl FrostTestDealer {
    /// Deal an `n`-member committee with threshold `t` from caller-supplied
    /// polynomial-coefficient entropy (64 wide bytes per coefficient).
    ///
    /// Deterministic in `coeff_seed` for reproducible fixtures; pass OS
    /// entropy (`getrandom::fill`) for non-fixture use.
    pub fn deal(n: u64, t: u64, coeff_seed: &[[u8; 64]]) -> Option<Self> {
        if t == 0 || t > n || (coeff_seed.len() as u64) < t {
            return None;
        }
        // f(x) = a_0 + a_1 x + … + a_{t-1} x^{t-1}
        let coeffs: Vec<Scalar> = coeff_seed[..t as usize]
            .iter()
            .map(Scalar::from_bytes_mod_order_wide)
            .collect();
        let eval = |x: Scalar| -> Scalar {
            // Horner
            coeffs.iter().rev().fold(Scalar::ZERO, |acc, c| acc * x + c)
        };
        let group_secret = coeffs[0];
        let group_key = PublicKey(EdwardsPoint::mul_base(&group_secret).compress().to_bytes());
        let shares = (1..=n)
            .map(|i| FrostShare {
                index: i,
                share: eval(Scalar::from(i)),
            })
            .collect();
        Some(Self {
            group_key,
            threshold: t,
            shares,
        })
    }

    /// Deal from OS entropy.
    pub fn deal_random(n: u64, t: u64) -> Option<Self> {
        let mut seeds = vec![[0u8; 64]; t as usize];
        for s in seeds.iter_mut() {
            getrandom::fill(s).expect("OS entropy unavailable");
        }
        Self::deal(n, t, &seeds)
    }
}

/// The Lagrange coefficient at 0 for participant `i` over the index set `parts`.
fn lagrange_at_zero(i: u64, parts: &[u64]) -> Scalar {
    let xi = Scalar::from(i);
    let mut num = Scalar::ONE;
    let mut den = Scalar::ONE;
    for &j in parts {
        if j == i {
            continue;
        }
        let xj = Scalar::from(j);
        num *= xj; // (0 - x_j) products; signs cancel between num and den
        den *= xj - xi;
    }
    num * den.invert()
}

/// The ed25519 challenge `e = SHA-512(R ‖ A ‖ M) mod ℓ`.
fn ed25519_challenge(r_compressed: &[u8; 32], group_key: &PublicKey, message: &[u8]) -> Scalar {
    let mut h = Sha512::new();
    h.update(r_compressed);
    h.update(group_key.0);
    h.update(message);
    Scalar::from_bytes_mod_order_wide(&h.finalize().into())
}

/// Produce a FROST quorum certificate from a signing subset — the Lean
/// theorem's algebra, executably.
///
/// Each participant `i ∈ parts` contributes nonce `k_i` (from
/// `nonce_seed[idx]`) with commitment `R_i = k_i·B`; the ceremony forms
/// `R = Σ R_i`, the ed25519 challenge `e = H(R ‖ A ‖ M)`, partial responses
/// `z_i = k_i + e·(λ_i·x_i)`, and the certificate `(R, z = Σ z_i)` — which
/// [`verify_frost_quorum`] accepts iff `parts` carries ≥ t genuine shares
/// (`frost_cert_verifies_under_group_key` with `hrecon` from Shamir).
///
/// SINGLE-CEREMONY ONLY: no RFC 9591 binding factors — see the module doc.
/// `nonce_seed` must be fresh, independent entropy per ceremony (nonce reuse
/// leaks shares, as for any Schnorr).
pub fn frost_sign(
    group_key: &PublicKey,
    signers: &[&FrostShare],
    nonce_seed: &[[u8; 64]],
    message: &[u8],
) -> Option<FrostQC> {
    if signers.is_empty() || nonce_seed.len() < signers.len() {
        return None;
    }
    let parts: Vec<u64> = signers.iter().map(|s| s.index).collect();
    // Distinct indices only (a duplicated signer is a caller bug, not a quorum).
    {
        let mut seen = std::collections::HashSet::new();
        if !parts.iter().all(|i| seen.insert(*i)) {
            return None;
        }
    }

    // Round 1: nonces + commitments.
    let nonces: Vec<Scalar> = nonce_seed[..signers.len()]
        .iter()
        .map(Scalar::from_bytes_mod_order_wide)
        .collect();
    let r_point: EdwardsPoint = nonces.iter().map(EdwardsPoint::mul_base).sum();
    let r_compressed = r_point.compress().to_bytes();

    // Challenge under the GROUP key.
    let e = ed25519_challenge(&r_compressed, group_key, message);

    // Round 2: Lagrange-weighted partial responses, summed.
    let z: Scalar = signers
        .iter()
        .zip(nonces.iter())
        .map(|(s, k)| k + e * (lagrange_at_zero(s.index, &parts) * s.share))
        .sum();

    let mut sig = [0u8; 64];
    sig[..32].copy_from_slice(&r_compressed);
    sig[32..].copy_from_slice(z.as_bytes());
    Some(FrostQC {
        signature: Signature(sig),
    })
}

/// Sign with fresh OS entropy for the nonces.
pub fn frost_sign_random(
    group_key: &PublicKey,
    signers: &[&FrostShare],
    message: &[u8],
) -> Option<FrostQC> {
    let mut seeds = vec![[0u8; 64]; signers.len()];
    for s in seeds.iter_mut() {
        getrandom::fill(s).expect("OS entropy unavailable");
    }
    frost_sign(group_key, signers, &seeds, message)
}

// =============================================================================
// HYBRID quorum certificates — FROST/ed25519 AND FIPS 204 ML-DSA-65
// =============================================================================

/// Domain-separation context for the ML-DSA half of a hybrid QC (FIPS 204
/// `ctx`, bound into every signature). Sign and verify must agree on it.
pub const HYBRID_PQ_CTX: &[u8] = b"dregg-hybrid-qc-v1";

/// An ML-DSA-65 public key, as its FIPS 204 serialized bytes
/// ([`ml_dsa_65::PK_LEN`] = 1952). Validated (`try_from_bytes`) at verify
/// time; an undecodable key rejects any certificate that names it.
#[derive(Clone, PartialEq, Eq)]
pub struct MlDsaPublicKey(pub [u8; ml_dsa_65::PK_LEN]);

/// A HYBRID quorum certificate: the classical FROST aggregate PLUS one
/// ML-DSA-65 signature per participating signer.
///
/// The Lean `hybridVerify = classical ∧ pq`: [`verify_hybrid_quorum`] accepts
/// only when BOTH halves verify, so forging a hybrid quorum requires breaking
/// ed25519 discrete log AND module-lattice SIS/LWE simultaneously
/// (`hybrid_survives_classical_break`). The PQ half carries explicit
/// per-signer signatures — ML-DSA has no threshold aggregation — so unlike
/// [`FrostQC`] the certificate size grows with the signing subset
/// (~3.3 KiB per signer) and the verifier CAN see which subset signed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HybridQC {
    /// The classical half: the FROST Schnorr aggregate under the group key.
    pub frost: FrostQC,
    /// The post-quantum half: `(committee position, ML-DSA-65 signature
    /// bytes)` per participating signer. Positions are 0-based into the
    /// verifier's `ml_dsa_pubkeys` slice.
    pub pq_sigs: Vec<(usize, Vec<u8>)>,
}

impl HybridQC {
    /// Serialize to the opaque-bytes convention (`dregg_types::ThresholdQC`):
    /// `frost(64) ‖ count(u32 LE) ‖ [index(u32 LE) ‖ sig_len(u32 LE) ‖ sig]*`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = self.frost.to_bytes();
        out.extend_from_slice(&(self.pq_sigs.len() as u32).to_le_bytes());
        for (index, sig) in &self.pq_sigs {
            out.extend_from_slice(&(*index as u32).to_le_bytes());
            out.extend_from_slice(&(sig.len() as u32).to_le_bytes());
            out.extend_from_slice(sig);
        }
        out
    }

    /// Deserialize; `None` on any framing violation (short header, short
    /// entry, trailing bytes).
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let frost = FrostQC::from_bytes(bytes.get(..FROST_QC_BYTES)?)?;
        let mut rest = bytes.get(FROST_QC_BYTES..)?;
        let take_u32 = |rest: &mut &[u8]| -> Option<u32> {
            let (head, tail) = rest.split_at_checked(4)?;
            *rest = tail;
            Some(u32::from_le_bytes(head.try_into().ok()?))
        };
        let count = take_u32(&mut rest)?;
        // `count` is attacker-controlled: cap the preallocation by what the
        // remaining bytes could possibly frame (≥ 8 bytes per entry).
        let mut pq_sigs = Vec::with_capacity((count as usize).min(rest.len() / 8));
        for _ in 0..count {
            let index = take_u32(&mut rest)? as usize;
            let sig_len = take_u32(&mut rest)? as usize;
            let (sig, tail) = rest.split_at_checked(sig_len)?;
            rest = tail;
            pq_sigs.push((index, sig.to_vec()));
        }
        if !rest.is_empty() {
            return None;
        }
        Some(Self { frost, pq_sigs })
    }
}

/// Verify a hybrid quorum certificate: the Lean `hybridVerify = classical ∧ pq`.
///
/// Accepts iff BOTH:
/// * (classical) [`verify_frost_quorum`] accepts `qc.frost` under `group_key`;
/// * (post-quantum) `qc.pq_sigs` carries at least `threshold` entries, EVERY
///   entry names a distinct in-range committee position, and EVERY entry's
///   signature ML-DSA-65-verifies over `message` (with [`HYBRID_PQ_CTX`])
///   against that position's key in `ml_dsa_pubkeys`.
///
/// STRICT on the PQ half: any invalid, duplicate, or out-of-range entry
/// rejects the WHOLE certificate (not merely "doesn't count") — a valid
/// quorum has no reason to carry junk, and refusing it kills malleability
/// slop. `threshold == 0` is refused outright: it would make the PQ half
/// vacuous and the "hybrid" a plain FROST cert in disguise.
pub fn verify_hybrid_quorum(
    group_key: &PublicKey,
    ml_dsa_pubkeys: &[MlDsaPublicKey],
    message: &[u8],
    qc: &HybridQC,
    threshold: usize,
) -> bool {
    if threshold == 0 {
        return false;
    }
    // Classical half.
    if !verify_frost_quorum(group_key, message, &qc.frost) {
        return false;
    }
    // Post-quantum half.
    let mut seen = std::collections::HashSet::new();
    for (index, sig_bytes) in &qc.pq_sigs {
        let Some(pk_bytes) = ml_dsa_pubkeys.get(*index) else {
            return false;
        };
        if !seen.insert(*index) {
            return false;
        }
        let Ok(sig) = <[u8; ml_dsa_65::SIG_LEN]>::try_from(sig_bytes.as_slice()) else {
            return false;
        };
        let Ok(vk) = ml_dsa_65::PublicKey::try_from_bytes(pk_bytes.0) else {
            return false;
        };
        if !vk.verify(message, &sig, HYBRID_PQ_CTX) {
            return false;
        }
    }
    qc.pq_sigs.len() >= threshold
}

/// Trusted-dealer keygen for the HYBRID committee: a [`FrostTestDealer`]
/// Shamir sharing PLUS an independent ML-DSA-65 keypair per member (member
/// `i` holds FROST share index `i+1` and PQ keypair position `i`).
///
/// Same fitness boundary as [`FrostTestDealer`]: tests, differentials, and
/// single-ceremony fixtures — the production stage deals FROST shares by DKG
/// and has each member generate its own ML-DSA keypair locally (nothing about
/// the PQ half needs a dealer at all; keys here are dealt only so fixtures
/// are one call).
pub struct HybridTestDealer {
    /// The classical half's dealer (group key, threshold, Shamir shares).
    pub frost: FrostTestDealer,
    /// Each member's ML-DSA-65 public key, member `i` at position `i` —
    /// exactly the slice [`verify_hybrid_quorum`] takes.
    pub ml_dsa_pubkeys: Vec<MlDsaPublicKey>,
    /// Each member's ML-DSA-65 signing key (dealer-held; test-only).
    ml_dsa_keys: Vec<ml_dsa_65::PrivateKey>,
}

impl HybridTestDealer {
    /// Deal an `n`-member hybrid committee with threshold `t`:
    /// `coeff_seed` feeds the Shamir polynomial (as [`FrostTestDealer::deal`]),
    /// `pq_seed` feeds FIPS 204 `keygen_from_seed` (one 32-byte `ξ` per
    /// member). Deterministic in both seeds for reproducible fixtures.
    pub fn deal(n: u64, t: u64, coeff_seed: &[[u8; 64]], pq_seed: &[[u8; 32]]) -> Option<Self> {
        if (pq_seed.len() as u64) < n {
            return None;
        }
        let frost = FrostTestDealer::deal(n, t, coeff_seed)?;
        let mut ml_dsa_pubkeys = Vec::with_capacity(n as usize);
        let mut ml_dsa_keys = Vec::with_capacity(n as usize);
        for xi in &pq_seed[..n as usize] {
            let (pk, sk) = ml_dsa_65::KG::keygen_from_seed(xi);
            ml_dsa_pubkeys.push(MlDsaPublicKey(pk.into_bytes()));
            ml_dsa_keys.push(sk);
        }
        Some(Self {
            frost,
            ml_dsa_pubkeys,
            ml_dsa_keys,
        })
    }

    /// Deal from OS entropy.
    pub fn deal_random(n: u64, t: u64) -> Option<Self> {
        let mut coeff_seed = vec![[0u8; 64]; t as usize];
        for s in coeff_seed.iter_mut() {
            getrandom::fill(s).expect("OS entropy unavailable");
        }
        let mut pq_seed = vec![[0u8; 32]; n as usize];
        for s in pq_seed.iter_mut() {
            getrandom::fill(s).expect("OS entropy unavailable");
        }
        Self::deal(n, t, &coeff_seed, &pq_seed)
    }
}

/// Produce a HYBRID quorum certificate: one FROST ceremony over the signing
/// subset PLUS each signer's individual ML-DSA-65 signature over the same
/// `message` (under [`HYBRID_PQ_CTX`]).
///
/// `signer_positions` are 0-based committee positions (FROST share `p+1`,
/// PQ keypair `p`). Same single-ceremony boundary as [`frost_sign`], and
/// `nonce_seed` has the same freshness obligation; the ML-DSA half signs
/// hedged from OS entropy (FIPS 204 `try_sign`).
pub fn hybrid_sign(
    dealer: &HybridTestDealer,
    signer_positions: &[usize],
    nonce_seed: &[[u8; 64]],
    message: &[u8],
) -> Option<HybridQC> {
    let signers: Vec<&FrostShare> = signer_positions
        .iter()
        .map(|&p| dealer.frost.shares.get(p))
        .collect::<Option<_>>()?;
    let frost = frost_sign(&dealer.frost.group_key, &signers, nonce_seed, message)?;
    let mut pq_sigs = Vec::with_capacity(signer_positions.len());
    for &p in signer_positions {
        let sig = dealer
            .ml_dsa_keys
            .get(p)?
            .try_sign(message, HYBRID_PQ_CTX)
            .ok()?;
        pq_sigs.push((p, sig.to_vec()));
    }
    Some(HybridQC { frost, pq_sigs })
}

/// Decompress a `CompressedEdwardsY` public key — used by tests to sanity-check
/// dealt keys are canonical points.
#[cfg(test)]
fn decompress_pk(pk: &PublicKey) -> Option<EdwardsPoint> {
    curve25519_dalek::edwards::CompressedEdwardsY(pk.0).decompress()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn seeds(n: usize, tag: u8) -> Vec<[u8; 64]> {
        (0..n)
            .map(|i| {
                let mut s = [0u8; 64];
                s[0] = tag;
                s[1] = i as u8;
                s[2] = 0x5a;
                s
            })
            .collect()
    }

    fn dealer_4_of_3() -> FrostTestDealer {
        FrostTestDealer::deal(4, 3, &seeds(3, 1)).unwrap()
    }

    #[test]
    fn frost_qc_signs_and_verifies_under_group_key() {
        let d = dealer_4_of_3();
        assert!(decompress_pk(&d.group_key).is_some());
        let message = b"dregg-federation-vote-v1:frost";
        let signers: Vec<&FrostShare> = d.shares[0..3].iter().collect();
        let qc = frost_sign(&d.group_key, &signers, &seeds(3, 2), message).unwrap();
        assert!(verify_frost_quorum(&d.group_key, message, &qc));
    }

    #[test]
    fn wrong_message_fails() {
        let d = dealer_4_of_3();
        let signers: Vec<&FrostShare> = d.shares[0..3].iter().collect();
        let qc = frost_sign(&d.group_key, &signers, &seeds(3, 3), b"correct").unwrap();
        assert!(!verify_frost_quorum(&d.group_key, b"wrong", &qc));
    }

    #[test]
    fn sub_threshold_subset_cannot_forge() {
        // 2 shares of a t=3 sharing Lagrange-interpolate a DIFFERENT degree-1
        // polynomial's value at 0, not the group secret: the cert must fail.
        let d = dealer_4_of_3();
        let signers: Vec<&FrostShare> = d.shares[0..2].iter().collect();
        let qc = frost_sign(&d.group_key, &signers, &seeds(2, 4), b"m").unwrap();
        assert!(!verify_frost_quorum(&d.group_key, b"m", &qc));
    }

    #[test]
    fn any_t_subset_verifies_and_certificate_is_subset_independent_in_size() {
        let d = dealer_4_of_3();
        let message = b"subset independence";
        let s013: Vec<&FrostShare> = [0, 1, 3].iter().map(|&i| &d.shares[i]).collect();
        let s123: Vec<&FrostShare> = [1, 2, 3].iter().map(|&i| &d.shares[i]).collect();
        let all: Vec<&FrostShare> = d.shares.iter().collect();
        let qc_a = frost_sign(&d.group_key, &s013, &seeds(3, 5), message).unwrap();
        let qc_b = frost_sign(&d.group_key, &s123, &seeds(3, 6), message).unwrap();
        let qc_c = frost_sign(&d.group_key, &all, &seeds(4, 7), message).unwrap();
        for qc in [&qc_a, &qc_b, &qc_c] {
            assert!(verify_frost_quorum(&d.group_key, message, qc));
            assert_eq!(qc.to_bytes().len(), FROST_QC_BYTES);
        }
        // Different ceremonies, different certs — but the verifier can't tell
        // which subset signed.
        assert_ne!(qc_a, qc_b);
    }

    #[test]
    fn frost_qc_is_a_plain_ed25519_signature() {
        // The dregg_types verifier path (used everywhere for vote sigs)
        // accepts the FROST certificate as-is under the group key.
        let d = dealer_4_of_3();
        let message = b"plain ed25519 compatibility";
        let signers: Vec<&FrostShare> = d.shares[1..4].iter().collect();
        let qc = frost_sign(&d.group_key, &signers, &seeds(3, 8), message).unwrap();
        assert!(d.group_key.verify(message, &qc.signature));
    }

    #[test]
    fn serialization_round_trips() {
        let d = dealer_4_of_3();
        let message = b"round trip";
        let signers: Vec<&FrostShare> = d.shares[0..3].iter().collect();
        let qc = frost_sign(&d.group_key, &signers, &seeds(3, 9), message).unwrap();
        let qc2 = FrostQC::from_bytes(&qc.to_bytes()).unwrap();
        assert_eq!(qc, qc2);
        assert!(verify_frost_quorum(&d.group_key, message, &qc2));
        assert!(FrostQC::from_bytes(&[0u8; 63]).is_none());
        assert!(FrostQC::from_bytes(&[0u8; 65]).is_none());
    }

    #[test]
    fn scheme_selector_dispatches_frost_and_rejects_cross_scheme_bytes() {
        let d = dealer_4_of_3();
        let message = b"selector";
        let signers: Vec<&FrostShare> = d.shares[0..3].iter().collect();
        let qc = frost_sign(&d.group_key, &signers, &seeds(3, 10), message).unwrap();
        let opaque = dregg_types::ThresholdQC(qc.to_bytes());

        let scheme = QuorumScheme::Frost {
            group_key: d.group_key,
        };
        assert!(scheme.verify_opaque_qc(&opaque.0, message));
        assert!(!scheme.verify_opaque_qc(&opaque.0, b"other message"));

        // BLS-shaped bytes (wrong length / garbage) under the Frost arm: reject.
        assert!(!scheme.verify_opaque_qc(&[0xAB; 48], message));
    }

    #[test]
    fn scheme_selector_bls_arm_still_verifies_bls() {
        // Both schemes valid side by side: the SAME opaque-bytes seam
        // dispatches to the incumbent BLS committee verify unchanged.
        let (committee, members) = crate::threshold::generate_test_committee(4, 3).unwrap();
        let message = b"bls via selector";
        let shares: Vec<(usize, crate::threshold::PartialSignature)> = members[0..3]
            .iter()
            .map(|m| (m.index, committee.sign_share(m, message)))
            .collect();
        let bls_qc = committee.aggregate(&shares, message).unwrap();
        let opaque = dregg_types::ThresholdQC(bls_qc.to_bytes());

        let scheme = QuorumScheme::Bls(&committee);
        assert!(scheme.verify_opaque_qc(&opaque.0, message));
        assert!(!scheme.verify_opaque_qc(&opaque.0, b"tampered"));

        // FROST bytes under the BLS arm: reject.
        let d = dealer_4_of_3();
        let signers: Vec<&FrostShare> = d.shares[0..3].iter().collect();
        let fqc = frost_sign(&d.group_key, &signers, &seeds(3, 11), message).unwrap();
        assert!(!scheme.verify_opaque_qc(&fqc.to_bytes(), message));
    }

    #[test]
    fn nonce_seed_shorter_than_signers_is_refused() {
        let d = dealer_4_of_3();
        let signers: Vec<&FrostShare> = d.shares[0..3].iter().collect();
        assert!(frost_sign(&d.group_key, &signers, &seeds(2, 12), b"m").is_none());
    }

    #[test]
    fn duplicate_signer_is_refused() {
        let d = dealer_4_of_3();
        let signers: Vec<&FrostShare> = vec![&d.shares[0], &d.shares[0], &d.shares[1]];
        assert!(frost_sign(&d.group_key, &signers, &seeds(3, 13), b"m").is_none());
    }

    // =========================================================================
    // HYBRID (FROST + ML-DSA-65) tests
    // =========================================================================

    fn pq_seeds(n: usize, tag: u8) -> Vec<[u8; 32]> {
        (0..n)
            .map(|i| {
                let mut s = [0u8; 32];
                s[0] = tag;
                s[1] = i as u8;
                s[2] = 0xa5;
                s
            })
            .collect()
    }

    fn hybrid_dealer_4_of_3() -> HybridTestDealer {
        HybridTestDealer::deal(4, 3, &seeds(3, 20), &pq_seeds(4, 21)).unwrap()
    }

    /// The simulated QUANTUM ADVERSARY: solve the group key's discrete log
    /// (stood in for by Lagrange-reconstructing the secret from `t` shares —
    /// the test is omniscient so it can realize exactly what Shor's would
    /// yield: the group secret scalar) and single-signer Schnorr-sign any
    /// message of the attacker's choosing. The output PASSES
    /// [`verify_frost_quorum`] — a genuine break of the classical half.
    fn quantum_break_forge_frost(d: &FrostTestDealer, message: &[u8]) -> FrostQC {
        let t = d.threshold as usize;
        let parts: Vec<u64> = d.shares[..t].iter().map(|s| s.index).collect();
        let group_secret: Scalar = d.shares[..t]
            .iter()
            .map(|s| lagrange_at_zero(s.index, &parts) * s.share)
            .sum();
        let k = Scalar::from_bytes_mod_order_wide(&{
            let mut s = [0u8; 64];
            s[0] = 0xfe;
            s
        });
        let r_compressed = EdwardsPoint::mul_base(&k).compress().to_bytes();
        let e = ed25519_challenge(&r_compressed, &d.group_key, message);
        let z = k + e * group_secret;
        let mut sig = [0u8; 64];
        sig[..32].copy_from_slice(&r_compressed);
        sig[32..].copy_from_slice(z.as_bytes());
        FrostQC {
            signature: Signature(sig),
        }
    }

    #[test]
    fn hybrid_honest_qc_verifies_both_halves() {
        let d = hybrid_dealer_4_of_3();
        let message = b"dregg-federation-vote-v1:hybrid";
        let qc = hybrid_sign(&d, &[0, 1, 2], &seeds(3, 22), message).unwrap();
        // The classical half alone verifies…
        assert!(verify_frost_quorum(&d.frost.group_key, message, &qc.frost));
        // …and so does the whole hybrid certificate.
        assert!(verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            message,
            &qc,
            3
        ));
        // Neither half accepts a different message.
        assert!(!verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            b"other",
            &qc,
            3
        ));
    }

    #[test]
    fn hybrid_corrupted_frost_half_is_rejected() {
        let d = hybrid_dealer_4_of_3();
        let message = b"corrupt the classical half";
        let mut qc = hybrid_sign(&d, &[1, 2, 3], &seeds(3, 23), message).unwrap();
        qc.frost.signature.0[40] ^= 0x01; // flip one bit of z
        assert!(!verify_frost_quorum(&d.frost.group_key, message, &qc.frost));
        // The PQ half is untouched and honest — the QC must STILL be rejected.
        assert!(!verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            message,
            &qc,
            3
        ));
    }

    #[test]
    fn hybrid_corrupted_or_missing_ml_dsa_sig_is_rejected() {
        let d = hybrid_dealer_4_of_3();
        let message = b"corrupt the pq half";
        let qc = hybrid_sign(&d, &[0, 1, 3], &seeds(3, 24), message).unwrap();

        // Corrupted: one flipped byte in one ML-DSA signature.
        let mut corrupted = qc.clone();
        corrupted.pq_sigs[1].1[100] ^= 0x01;
        assert!(!verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            message,
            &corrupted,
            3
        ));

        // Missing: one signature dropped leaves 2 < threshold 3.
        let mut missing = qc.clone();
        missing.pq_sigs.remove(2);
        assert!(!verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            message,
            &missing,
            3
        ));

        // Wrong-length signature bytes.
        let mut truncated = qc;
        truncated.pq_sigs[0].1.truncate(ml_dsa_65::SIG_LEN - 1);
        assert!(!verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            message,
            &truncated,
            3
        ));
    }

    #[test]
    fn hybrid_survives_classical_break() {
        // THE QUANTUM-SAFETY TEST (the Lean `hybrid_survives_classical_break`):
        // an adversary who fully breaks ed25519 forges a VALID FROST half on a
        // malicious message and grafts on the only ML-DSA signatures in
        // existence — honest ones over the honest message. The PQ half catches
        // the substitution and the hybrid certificate is REJECTED.
        let d = hybrid_dealer_4_of_3();
        let honest_msg = b"honest state root";
        let malicious_msg = b"attacker's state root";
        let honest_qc = hybrid_sign(&d, &[0, 1, 2], &seeds(3, 25), honest_msg).unwrap();

        let forged_frost = quantum_break_forge_frost(&d.frost, malicious_msg);
        // The classical break is GENUINE: the forged half verifies under the
        // group key on the attacker's message.
        assert!(verify_frost_quorum(
            &d.frost.group_key,
            malicious_msg,
            &forged_frost
        ));

        let forged_qc = HybridQC {
            frost: forged_frost,
            pq_sigs: honest_qc.pq_sigs.clone(),
        };
        // …but the hybrid verifier still refuses it: no ML-DSA signature over
        // the malicious message exists.
        assert!(!verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            malicious_msg,
            &forged_qc,
            3
        ));
    }

    #[test]
    fn hybrid_sub_threshold_pq_count_is_rejected() {
        let d = hybrid_dealer_4_of_3();
        let message = b"sub-threshold pq";
        let qc = hybrid_sign(&d, &[0, 1, 2], &seeds(3, 26), message).unwrap();
        // Keep only 2 of the 3 (all still individually VALID) — below t=3.
        let mut sub = qc.clone();
        sub.pq_sigs.truncate(2);
        assert!(!verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            message,
            &sub,
            3
        ));
        // A duplicate cannot pad the count back up.
        let mut padded = sub.clone();
        padded.pq_sigs.push(padded.pq_sigs[0].clone());
        assert!(!verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            message,
            &padded,
            3
        ));
        // Nor can an out-of-range index.
        let mut oob = sub;
        oob.pq_sigs.push((7, vec![0u8; ml_dsa_65::SIG_LEN]));
        assert!(!verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            message,
            &oob,
            3
        ));
        // And threshold 0 (a vacuous PQ half) is refused outright.
        assert!(!verify_hybrid_quorum(
            &d.frost.group_key,
            &d.ml_dsa_pubkeys,
            message,
            &qc,
            0
        ));
    }

    #[test]
    fn hybrid_serialization_round_trips_and_selector_dispatches() {
        let d = hybrid_dealer_4_of_3();
        let message = b"hybrid selector";
        let qc = hybrid_sign(&d, &[1, 2, 3], &seeds(3, 27), message).unwrap();

        // Opaque-bytes round trip.
        let bytes = qc.to_bytes();
        let qc2 = HybridQC::from_bytes(&bytes).unwrap();
        assert_eq!(qc, qc2);

        // Framing violations reject.
        assert!(HybridQC::from_bytes(&bytes[..bytes.len() - 1]).is_none());
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(HybridQC::from_bytes(&trailing).is_none());
        assert!(HybridQC::from_bytes(&[0u8; 63]).is_none());

        // The scheme selector dispatches the hybrid arm over the same
        // opaque-bytes seam as BLS and FROST.
        let opaque = dregg_types::ThresholdQC(bytes);
        let scheme = QuorumScheme::Hybrid {
            group_key: d.frost.group_key,
            ml_dsa_pubkeys: &d.ml_dsa_pubkeys,
            threshold: 3,
        };
        assert!(scheme.verify_opaque_qc(&opaque.0, message));
        assert!(!scheme.verify_opaque_qc(&opaque.0, b"other message"));
        // A bare FROST cert's bytes are NOT a hybrid cert.
        let fqc = frost_sign(
            &d.frost.group_key,
            &d.frost.shares[0..3].iter().collect::<Vec<_>>(),
            &seeds(3, 28),
            message,
        )
        .unwrap();
        assert!(!scheme.verify_opaque_qc(&fqc.to_bytes(), message));
    }
}
