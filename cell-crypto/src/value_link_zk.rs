//! Experimental Ristretto value-link sigma proofs — NOT wired into production.
//!
//! # Integrity status (2026-07-21)
//!
//! No non-test caller of this module exists at HEAD. Its sigma protocols are over
//! Ristretto/Pedersen and therefore rely on DLog; they are not post-quantum.
//! More importantly, the current `value_binding` felt is merely folded into the
//! Fiat–Shamir challenge. That prevents replaying one proof under a different PI,
//! but it does **not** constrain the hidden 64-bit value proved by the sigma to be
//! a preimage of that PI. A prover can produce the per-bit proof for any chosen
//! value while treating any supplied `value_binding` as transcript context.
//!
//! The implemented proofs establish, under DLog/Fiat–Shamir:
//!
//! 1. `link_leg` opens to one hidden 64-bit value whose committed bits are Boolean;
//! 2. `link_leg` and a transfer `value_leg` open to the same hidden value; and
//! 3. both proofs are bound to a supplied transcript and `value_binding` PI.
//!
//! They do not establish that the hidden value hashes to the PI or comes from the
//! STARK leaf. Closing that relation requires proving the hash preimage in the
//! same proof system, or exposing STARK-constrained bit commitments and checking
//! those commitments here. Neither exists in this module. The production PQ
//! direction instead removes this curve bridge: faithfully encode value/asset in
//! a wide in-AIR hash commitment and enforce no-mint in AIR. Function/type names
//! below are retained for compatibility with this module's local tests.

use crate::value_commitment::{ValueCommitment, randomness_generator, value_generator};
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::Identity;
use dregg_circuit::field::BabyBear;

/// Sample a uniformly random Ristretto scalar (64-byte wide reduction).
fn random_scalar() -> Scalar {
    let mut bytes = [0u8; 64];
    getrandom::fill(&mut bytes).expect("getrandom failed");
    Scalar::from_bytes_mod_order_wide(&bytes)
}

/// Fiat-Shamir challenge binding both legs, the nonce, and the STARK's
/// `value_binding` PI bytes (so the ZK link cannot be replayed against a
/// different leaf / context).
fn link_challenge(
    value_leg: &RistrettoPoint,
    link_leg: &RistrettoPoint,
    nonce: &RistrettoPoint,
    value_binding_pi: &[u8],
    message: &[u8],
) -> Scalar {
    let mut h = blake3::Hasher::new_derive_key("dregg-value-link-zk-challenge v1");
    h.update(&randomness_generator().compress().to_bytes());
    h.update(&value_leg.compress().to_bytes());
    h.update(&link_leg.compress().to_bytes());
    h.update(&nonce.compress().to_bytes());
    h.update(value_binding_pi);
    h.update(message);
    let mut wide = [0u8; 64];
    wide[..32].copy_from_slice(h.finalize().as_bytes());
    Scalar::from_bytes_mod_order_wide(&wide)
}

/// A zero-knowledge proof that two Pedersen legs (`value_leg`, `link_leg`) commit
/// to the SAME hidden value. Step (B) of the linker: a Chaum-Pedersen
/// equal-message argument realized as a Schnorr proof of knowledge of the
/// R-exponent of `value_leg − link_leg` (= `(r1 − r2)·R`, with no V-component iff
/// the values are equal).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkValueLinkProof {
    /// Schnorr nonce commitment `k·R` (compressed).
    pub nonce: [u8; 32],
    /// Schnorr response `s = k + e·(r1 − r2)` (canonical scalar bytes).
    pub response: [u8; 32],
}

/// Errors from the ZK value-link verifier (fail-closed on every malformed input).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ZkValueLinkError {
    /// A leg / nonce point is not a valid Ristretto encoding.
    InvalidPoint,
    /// The response scalar is non-canonical.
    InvalidResponse,
    /// A sigma equation failed. For step B this means the two Pedersen legs do
    /// not share a value; it says nothing by itself about a STARK leaf.
    LinkFailed,
}

/// Prove (step B) that `value_leg = value·V + r1·R` and
/// `link_leg = value·V + r2·R` share the same hidden `value`. The prover supplies
/// `delta_r = r1 − r2` (the only witness needed — `value` itself never enters the
/// proof, hence zero-knowledge over the amount).
///
/// `value_binding_pi` is folded into Fiat–Shamir as transcript context. This
/// does not prove either Pedersen opening is a preimage of that PI.
pub fn prove_zk_value_link(
    value_leg: &ValueCommitment,
    link_leg: &ValueCommitment,
    delta_r: &Scalar,
    value_binding_pi: &[u8],
    message: &[u8],
) -> ZkValueLinkProof {
    let r_gen = randomness_generator();
    let k = random_scalar();
    let nonce = k * r_gen;
    let e = link_challenge(
        &value_leg.point,
        &link_leg.point,
        &nonce,
        value_binding_pi,
        message,
    );
    let s = k + e * delta_r;
    ZkValueLinkProof {
        nonce: nonce.compress().to_bytes(),
        response: s.to_bytes(),
    }
}

/// Verify (step B). Returns `Ok(())` iff `value_leg` and `link_leg` provably
/// commit to the SAME hidden value. Checks `s·R == nonce + e·(value_leg −
/// link_leg)`: this holds iff the difference is a pure `R`-multiple, i.e. the
/// `V`-components (the values) cancel.
///
/// This verifies step (B) only and ties two Pedersen legs to each other. The
/// current [`LinkLegBindingProof`] does not add a checked hash-preimage relation
/// to a STARK leaf; see the module integrity notice.
pub fn verify_zk_value_link(
    value_leg_bytes: &[u8; 32],
    link_leg_bytes: &[u8; 32],
    proof: &ZkValueLinkProof,
    value_binding_pi: &[u8],
    message: &[u8],
) -> Result<(), ZkValueLinkError> {
    fn pt(b: &[u8; 32]) -> Result<RistrettoPoint, ZkValueLinkError> {
        CompressedRistretto::from_slice(b)
            .map_err(|_| ZkValueLinkError::InvalidPoint)?
            .decompress()
            .ok_or(ZkValueLinkError::InvalidPoint)
    }
    let value_leg = pt(value_leg_bytes)?;
    let link_leg = pt(link_leg_bytes)?;
    let nonce = pt(&proof.nonce)?;

    let s_ct = Scalar::from_canonical_bytes(proof.response);
    let s: Scalar = if s_ct.is_some().into() {
        s_ct.unwrap()
    } else {
        return Err(ZkValueLinkError::InvalidResponse);
    };

    let e = link_challenge(&value_leg, &link_leg, &nonce, value_binding_pi, message);
    let diff = value_leg - link_leg;
    let lhs = s * randomness_generator();
    let rhs = nonce + e * diff;
    if lhs == rhs {
        Ok(())
    } else {
        Err(ZkValueLinkError::LinkFailed)
    }
}

/// Canonical serialization of the STARK's `value_binding` felt for folding into
/// every Fiat-Shamir transcript in this module. Matches
/// `dregg_cell::commitment::felt_to_bytes32`'s low-4-byte little-endian layout
/// (a `BabyBear` is a single 31-bit limb), so the ZK link is bound to the SAME
/// felt encoding the rest of the protocol uses.
pub fn value_binding_pi_bytes(value_binding: BabyBear) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[0..4].copy_from_slice(&value_binding.as_u32().to_le_bytes());
    out
}

// ─── Step (A): link-leg ↔ leaf value binding (per-bit Pedersen sigma) ─────────
//
// This proves `link_leg = value·V + r_link·R` for some hidden 64-bit value,
// using Boolean bit commitments. `value_binding` influences the Fiat–Shamir
// challenges but no equation checks `value_binding == hash_fact(value, …)`.
// Consequently this is a transcript-associated opening proof, not a cross-field
// leaf↔leg relation. The sigma is honest-verifier ZK over the value (the per-bit
// responses are `nonce + e·witness` with uniform nonces).
//
// # Construction
//
// For each bit position `j ∈ [0, 64)` the prover commits `B_j = b_j·V_j + s_j·R`
// where `V_j = 2^j·V` and `b_j ∈ {0,1}`, and proves the OR statement
// `B_j opens to 0` OR `B_j − V_j opens to 0` (a textbook 1-of-2 Chaum-Pedersen
// disjunction on the `R`-exponent). Aggregation: `Σ_j B_j = value·V + (Σ_j s_j)·R`,
// and the prover proves this aggregate equals `link_leg` via a single equal-message
// Schnorr on the `R`-exponent of `link_leg − Σ_j B_j` (= `(r_link − Σ s_j)·R`).

/// The number of value bits bound (matches the bulletproof / leaf range: `[0, 2^64)`).
pub const VALUE_BITS: usize = 64;

/// A per-bit OR-proof that a bit commitment `B_j = b_j·(2^j·V) + s_j·R` opens to a
/// bit `b_j ∈ {0,1}` — a 1-of-2 Chaum-Pedersen disjunction on the `R`-exponent of
/// `B_j` (branch 0: `B_j = s_j·R`) vs `B_j − 2^j·V` (branch 1). Standard simulated
/// non-chosen branch so the transcript is ZK over which bit it is.
#[derive(Clone, Debug, PartialEq, Eq)]
struct BitOrProof {
    /// Commitment `B_j` (compressed).
    commitment: [u8; 32],
    /// Branch-0 announcement `A0` (compressed).
    a0: [u8; 32],
    /// Branch-1 announcement `A1` (compressed).
    a1: [u8; 32],
    /// Branch-0 sub-challenge (the other is `e − e0`).
    e0: [u8; 32],
    /// Branch-0 response.
    z0: [u8; 32],
    /// Branch-1 response.
    z1: [u8; 32],
}

/// A zero-knowledge proof (step A) that `link_leg` is a Pedersen commitment to the
/// SAME 64-bit value the STARK bound into `value_binding`, via the bit-decomposition
/// bridge. Reveals nothing about the value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinkLegBindingProof {
    /// One OR-proof per value bit (length [`VALUE_BITS`]).
    bits: Vec<BitOrProof>,
    /// Schnorr nonce for the aggregate equal-message tie `link_leg − ΣB_j`.
    agg_nonce: [u8; 32],
    /// Schnorr response for the aggregate tie: `z = k + e·(r_link − Σ s_j)`.
    agg_response: [u8; 32],
}

fn bit_generator(j: usize) -> RistrettoPoint {
    // 2^j · V. j < 64 so the doubling chain is cheap and exact.
    let mut p = value_generator();
    for _ in 0..j {
        p = p + p;
    }
    p
}

fn random_scalar_local() -> Scalar {
    random_scalar()
}

/// Fiat-Shamir challenge for one bit's OR-proof, bound to the bit position, both
/// announcements, the commitment, and the value-binding felt.
fn bit_challenge(
    j: usize,
    commitment: &RistrettoPoint,
    a0: &RistrettoPoint,
    a1: &RistrettoPoint,
    value_binding_pi: &[u8],
    message: &[u8],
) -> Scalar {
    let mut h = blake3::Hasher::new_derive_key("dregg-value-link-bit-or v1");
    h.update(&(j as u64).to_le_bytes());
    h.update(&value_generator().compress().to_bytes());
    h.update(&randomness_generator().compress().to_bytes());
    h.update(&commitment.compress().to_bytes());
    h.update(&a0.compress().to_bytes());
    h.update(&a1.compress().to_bytes());
    h.update(value_binding_pi);
    h.update(message);
    let mut wide = [0u8; 64];
    wide[..32].copy_from_slice(h.finalize().as_bytes());
    Scalar::from_bytes_mod_order_wide(&wide)
}

fn agg_challenge(
    link_leg: &RistrettoPoint,
    sum_bits: &RistrettoPoint,
    nonce: &RistrettoPoint,
    value_binding_pi: &[u8],
    message: &[u8],
) -> Scalar {
    let mut h = blake3::Hasher::new_derive_key("dregg-value-link-agg v1");
    h.update(&randomness_generator().compress().to_bytes());
    h.update(&link_leg.compress().to_bytes());
    h.update(&sum_bits.compress().to_bytes());
    h.update(&nonce.compress().to_bytes());
    h.update(value_binding_pi);
    h.update(message);
    let mut wide = [0u8; 64];
    wide[..32].copy_from_slice(h.finalize().as_bytes());
    Scalar::from_bytes_mod_order_wide(&wide)
}

fn pt(b: &[u8; 32]) -> Result<RistrettoPoint, ZkValueLinkError> {
    CompressedRistretto::from_slice(b)
        .map_err(|_| ZkValueLinkError::InvalidPoint)?
        .decompress()
        .ok_or(ZkValueLinkError::InvalidPoint)
}

fn scalar_canonical(b: &[u8; 32]) -> Result<Scalar, ZkValueLinkError> {
    let ct = Scalar::from_canonical_bytes(*b);
    if ct.is_some().into() {
        Ok(ct.unwrap())
    } else {
        Err(ZkValueLinkError::InvalidResponse)
    }
}

/// Prove that `link_leg` commits to one hidden 64-bit value, binding the supplied
/// `value_binding` felt into the transcript as context. This does not prove that
/// the hidden value hashes to that felt or comes from a STARK leaf.
///
/// # Panics
/// Panics if `link_leg != value·V + r_link·R` (the caller must pass a real opening),
/// or if `getrandom` fails.
pub fn prove_link_leg_binding(
    value: u64,
    r_link: &Scalar,
    value_binding: BabyBear,
    message: &[u8],
) -> (ValueCommitment, LinkLegBindingProof) {
    let v_gen = value_generator();
    let r_gen = randomness_generator();
    let link_leg = ValueCommitment::commit(value, r_link);
    let vb_pi = value_binding_pi_bytes(value_binding);

    let mut bits = Vec::with_capacity(VALUE_BITS);
    let mut bit_blindings = Vec::with_capacity(VALUE_BITS);
    let mut sum_bit_blinding = Scalar::ZERO;

    for j in 0..VALUE_BITS {
        let bit = ((value >> j) & 1) == 1;
        let vj = bit_generator(j);
        let s_j = random_scalar_local();
        sum_bit_blinding += s_j;
        bit_blindings.push(s_j);
        // B_j = b_j·V_j + s_j·R
        let b_point = if bit { vj + s_j * r_gen } else { s_j * r_gen };

        // 1-of-2 OR on the R-exponent: branch 0 proves B_j = s_j·R (bit 0);
        // branch 1 proves B_j − V_j = s_j·R (bit 1). Simulate the false branch.
        let (a0, a1, e0, z0, z1);
        if !bit {
            // Real branch 0; simulate branch 1.
            let k0 = random_scalar_local();
            let real_a0 = k0 * r_gen;
            let e1 = random_scalar_local();
            let z1s = random_scalar_local();
            // A1 = z1·R − e1·(B_j − V_j)
            let sim_a1 = z1s * r_gen - e1 * (b_point - vj);
            let e = bit_challenge(j, &b_point, &real_a0, &sim_a1, &vb_pi, message);
            let e0s = e - e1;
            let z0s = k0 + e0s * s_j;
            a0 = real_a0;
            a1 = sim_a1;
            e0 = e0s;
            z0 = z0s;
            z1 = z1s;
        } else {
            // Real branch 1; simulate branch 0.
            let k1 = random_scalar_local();
            let real_a1 = k1 * r_gen;
            let e0s = random_scalar_local();
            let z0s = random_scalar_local();
            // A0 = z0·R − e0·B_j
            let sim_a0 = z0s * r_gen - e0s * b_point;
            let e = bit_challenge(j, &b_point, &sim_a0, &real_a1, &vb_pi, message);
            let e1 = e - e0s;
            let z1s = k1 + e1 * s_j;
            a0 = sim_a0;
            a1 = real_a1;
            e0 = e0s;
            z0 = z0s;
            z1 = z1s;
        }

        bits.push(BitOrProof {
            commitment: b_point.compress().to_bytes(),
            a0: a0.compress().to_bytes(),
            a1: a1.compress().to_bytes(),
            e0: e0.to_bytes(),
            z0: z0.to_bytes(),
            z1: z1.to_bytes(),
        });
    }

    // Aggregate tie: Σ B_j = value·V + (Σ s_j)·R, so link_leg − ΣB_j =
    // (r_link − Σ s_j)·R. Schnorr proof of knowledge of that R-exponent.
    let sum_bits = bits.iter().fold(RistrettoPoint::identity(), |acc, b| {
        acc + CompressedRistretto::from_slice(&b.commitment)
            .unwrap()
            .decompress()
            .unwrap()
    });
    let delta = r_link - sum_bit_blinding;
    let k = random_scalar_local();
    let agg_nonce = k * r_gen;
    let e = agg_challenge(&link_leg.point, &sum_bits, &agg_nonce, &vb_pi, message);
    let z = k + e * delta;
    let _ = v_gen; // V used only via bit generators

    (
        link_leg,
        LinkLegBindingProof {
            bits,
            agg_nonce: agg_nonce.compress().to_bytes(),
            agg_response: z.to_bytes(),
        },
    )
}

/// Verify (step A): returns `Ok(())` iff `link_leg` provably commits to some
/// Boolean-composed 64-bit value and the proof transcript includes
/// `value_binding`. It does not prove that value hashes to the felt. Reveals
/// nothing about the value and fails closed on malformed input.
pub fn verify_link_leg_binding(
    link_leg_bytes: &[u8; 32],
    value_binding: BabyBear,
    proof: &LinkLegBindingProof,
    message: &[u8],
) -> Result<(), ZkValueLinkError> {
    if proof.bits.len() != VALUE_BITS {
        return Err(ZkValueLinkError::LinkFailed);
    }
    let link_leg = pt(link_leg_bytes)?;
    let r_gen = randomness_generator();
    let vb_pi = value_binding_pi_bytes(value_binding);

    let mut sum_bits = RistrettoPoint::identity();
    for (j, b) in proof.bits.iter().enumerate() {
        let b_point = pt(&b.commitment)?;
        let a0 = pt(&b.a0)?;
        let a1 = pt(&b.a1)?;
        let e0 = scalar_canonical(&b.e0)?;
        let z0 = scalar_canonical(&b.z0)?;
        let z1 = scalar_canonical(&b.z1)?;

        let e = bit_challenge(j, &b_point, &a0, &a1, &vb_pi, message);
        let e1 = e - e0;
        let vj = bit_generator(j);

        // Branch 0: z0·R == A0 + e0·B_j   (B_j = s·R, bit 0)
        if z0 * r_gen != a0 + e0 * b_point {
            return Err(ZkValueLinkError::LinkFailed);
        }
        // Branch 1: z1·R == A1 + e1·(B_j − V_j)   (B_j − V_j = s·R, bit 1)
        if z1 * r_gen != a1 + e1 * (b_point - vj) {
            return Err(ZkValueLinkError::LinkFailed);
        }
        sum_bits += b_point;
    }

    // Aggregate: link_leg − ΣB_j == (r_link − Σ s_j)·R.
    let agg_nonce = pt(&proof.agg_nonce)?;
    let z = scalar_canonical(&proof.agg_response)?;
    let e = agg_challenge(&link_leg, &sum_bits, &agg_nonce, &vb_pi, message);
    let diff = link_leg - sum_bits;
    if z * r_gen != agg_nonce + e * diff {
        return Err(ZkValueLinkError::LinkFailed);
    }
    Ok(())
}

// ─── End-to-end ZK leaf↔leg linker (step A ∘ step B) ──────────────────────────

/// Experimental composition of the per-bit `link_leg` proof and the equal-message
/// Pedersen proof. It binds both to the supplied transcript/PI but does not prove
/// that the hidden value is a preimage of the STARK `value_binding`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkLeafLegLink {
    /// Transcript-associated link leg `value·V + r_link·R` (compressed).
    pub link_leg: [u8; 32],
    /// Step (A): `link_leg` commits to a hidden 64-bit value; the PI is context.
    pub leg_binding: LinkLegBindingProof,
    /// Step (B): the transfer `value_leg` and `link_leg` commit to the same value.
    pub equal_message: ZkValueLinkProof,
}

/// Prove the experimental composed Pedersen relation. `value_binding` is
/// transcript context; callers must not treat this as a proved hash-preimage link.
pub fn prove_zk_leaf_leg_link(
    value: u64,
    r_value: &Scalar,
    value_binding: BabyBear,
    message: &[u8],
) -> (ValueCommitment, ZkLeafLegLink) {
    let r_link = random_scalar_local();
    let (link_leg, leg_binding) = prove_link_leg_binding(value, &r_link, value_binding, message);
    let value_leg = ValueCommitment::commit(value, r_value);
    let vb_pi = value_binding_pi_bytes(value_binding);
    let delta_r = r_value - r_link;
    let equal_message = prove_zk_value_link(&value_leg, &link_leg, &delta_r, &vb_pi, message);
    (
        value_leg,
        ZkLeafLegLink {
            link_leg: link_leg.to_bytes().0,
            leg_binding,
            equal_message,
        },
    )
}

/// Verify both experimental sigma components. Success proves the two Pedersen
/// legs share a hidden value and that the proof transcript includes the supplied
/// PI; it does not prove the hidden value hashes to that PI.
pub fn verify_zk_leaf_leg_link(
    value_leg_bytes: &[u8; 32],
    value_binding: BabyBear,
    link: &ZkLeafLegLink,
    message: &[u8],
) -> Result<(), ZkValueLinkError> {
    let vb_pi = value_binding_pi_bytes(value_binding);
    // Step (A): link_leg opens to a Boolean-composed value; PI is transcript context.
    verify_link_leg_binding(&link.link_leg, value_binding, &link.leg_binding, message)?;
    // Step (B): value_leg ↔ link_leg.
    verify_zk_value_link(
        value_leg_bytes,
        &link.link_leg,
        &link.equal_message,
        &vb_pi,
        message,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scalar(seed: u8) -> Scalar {
        let mut b = [0u8; 64];
        b[0] = seed;
        b[1] = seed.wrapping_mul(31).wrapping_add(7);
        Scalar::from_bytes_mod_order_wide(&b)
    }

    /// POSITIVE polarity: equal-value legs link in ZK. Build `value_leg` and
    /// `link_leg` over the SAME value with DIFFERENT blindings; the proof accepts
    /// and the verifier never sees the value.
    #[test]
    fn zk_link_accepts_equal_value() {
        let value: u64 = 4242;
        let r1 = scalar(1);
        let r2 = scalar(2);
        let value_leg = ValueCommitment::commit(value, &r1);
        let link_leg = ValueCommitment::commit(value, &r2);
        let delta_r = r1 - r2;

        let vb_pi = b"fake-value-binding-felt";
        let msg = b"tx-context";
        let proof = prove_zk_value_link(&value_leg, &link_leg, &delta_r, vb_pi, msg);

        assert_eq!(
            verify_zk_value_link(
                &value_leg.to_bytes().0,
                &link_leg.to_bytes().0,
                &proof,
                vb_pi,
                msg
            ),
            Ok(())
        );
    }

    /// NEGATIVE polarity: two Pedersen legs committing to different values are
    /// rejected. This tests equal-message soundness only, not relation to a leaf.
    /// The prover knows `delta_r = r1 − r2` but
    /// the values differ, so `value_leg − link_leg` has a nonzero V-component and the
    /// Schnorr-on-R equation cannot hold.
    #[test]
    fn zk_link_rejects_value_mismatch() {
        let r1 = scalar(3);
        let r2 = scalar(4);
        let value_leg = ValueCommitment::commit(100, &r1); // leaf value
        let link_leg = ValueCommitment::commit(101, &r2); // mismatched leg value
        let delta_r = r1 - r2;

        let vb_pi = b"fake-value-binding-felt";
        let msg = b"tx-context";
        // Honest prover for the WRONG statement: it can only prove the R-exponent
        // of the difference, but the difference carries (100-101)·V ≠ 0.
        let proof = prove_zk_value_link(&value_leg, &link_leg, &delta_r, vb_pi, msg);

        assert_eq!(
            verify_zk_value_link(
                &value_leg.to_bytes().0,
                &link_leg.to_bytes().0,
                &proof,
                vb_pi,
                msg
            ),
            Err(ZkValueLinkError::LinkFailed)
        );
    }

    /// NEGATIVE polarity: Fiat-Shamir binds the `value_binding` PI. A proof made
    /// for one leaf does NOT verify when re-pointed at a different leaf's binding
    /// (replay across contexts is rejected).
    #[test]
    fn zk_link_is_bound_to_value_binding_pi() {
        let value: u64 = 7;
        let r1 = scalar(5);
        let r2 = scalar(6);
        let value_leg = ValueCommitment::commit(value, &r1);
        let link_leg = ValueCommitment::commit(value, &r2);
        let delta_r = r1 - r2;

        let proof = prove_zk_value_link(&value_leg, &link_leg, &delta_r, b"leaf-A", b"ctx");
        // Same legs, DIFFERENT value_binding PI → challenge differs → reject.
        assert_eq!(
            verify_zk_value_link(
                &value_leg.to_bytes().0,
                &link_leg.to_bytes().0,
                &proof,
                b"leaf-B",
                b"ctx"
            ),
            Err(ZkValueLinkError::LinkFailed)
        );
    }

    // ─── REAL-PATH tests: the genuine STARK `value_binding` felt ──────────────
    //
    // These exercise the felt an honest shielded-spend witness publishes
    // (`ShieldedSpendWitness::value_binding()` == `value_link_binding(value,
    // asset_type, randomness)`), not a fixture string. They check honest-value
    // compatibility only; they do not establish the missing hash-preimage relation.

    use crate::value_commitment::value_link_binding;
    use dregg_circuit::field::BabyBear;
    use dregg_circuit_prove::shielded::spend_circuit::ShieldedSpendWitness;

    /// Build a real shielded-spend witness and return its genuine `(value,
    /// value_binding felt)` — the SAME felt the STARK publishes as PI[VALUE_BINDING].
    fn real_leaf(value: u64, randomness_seed: u32) -> (u64, BabyBear) {
        let randomness = BabyBear::new(randomness_seed);
        let w = ShieldedSpendWitness {
            value: BabyBear::new((value % ((1u64 << 31) as u64)) as u32),
            asset_type: BabyBear::new(1),
            owner: BabyBear::new(7),
            randomness,
            key: [
                BabyBear::new(11),
                BabyBear::new(13),
                BabyBear::new(17),
                BabyBear::new(19),
            ],
            siblings: vec![],
            positions: vec![],
        };
        let vb_circuit = w.value_binding();
        // The cell-side re-derivation MUST equal the circuit's published felt (the
        // witness above uses asset_type = 1).
        let vb_cell = value_link_binding(value, 1, randomness);
        assert_eq!(
            vb_circuit, vb_cell,
            "cell re-derivation must match the STARK PI"
        );
        (value, vb_circuit)
    }

    /// POSITIVE honest-input case: the proof accepts with the matching PI as context.
    #[test]
    fn link_leg_binding_accepts_real_value() {
        let (value, vb) = real_leaf(123_456_789, 9999);
        let r_link = scalar(21);
        let (link_leg, proof) = prove_link_leg_binding(value, &r_link, vb, b"tx");
        assert_eq!(
            verify_link_leg_binding(&link_leg.to_bytes().0, vb, &proof, b"tx"),
            Ok(())
        );
    }

    /// NEGATIVE (step A): a `link_leg` opening a DIFFERENT value than the one the
    /// proof's bits encode is rejected. We build the proof honestly for `value`,
    /// then verify against a link_leg re-committed to `value+1` — the aggregate
    /// tie `link_leg − ΣB_j` no longer has a pure R-exponent (the V-component of
    /// the off-by-one leaks in) and verification fails closed.
    #[test]
    fn link_leg_binding_rejects_wrong_leg() {
        let (value, vb) = real_leaf(1000, 4242);
        let r_link = scalar(22);
        let (_good_leg, proof) = prove_link_leg_binding(value, &r_link, vb, b"tx");
        // A leg committing to value+1 under the same r_link.
        let bad_leg = ValueCommitment::commit(value + 1, &r_link);
        assert_eq!(
            verify_link_leg_binding(&bad_leg.to_bytes().0, vb, &proof, b"tx"),
            Err(ZkValueLinkError::LinkFailed)
        );
    }

    /// NEGATIVE (step A): changing the PI changes Fiat–Shamir challenges and
    /// rejects transcript replay. This does not prove a hash-preimage relation.
    #[test]
    fn link_leg_binding_bound_to_real_felt() {
        let (value, vb_a) = real_leaf(555, 100);
        let (_v2, vb_b) = real_leaf(555, 200); // same value, DIFFERENT randomness → different felt
        assert_ne!(
            vb_a, vb_b,
            "different randomness must give a different binding felt"
        );
        let r_link = scalar(23);
        let (link_leg, proof) = prove_link_leg_binding(value, &r_link, vb_a, b"tx");
        assert_eq!(
            verify_link_leg_binding(&link_leg.to_bytes().0, vb_b, &proof, b"tx"),
            Err(ZkValueLinkError::LinkFailed)
        );
    }

    /// POSITIVE honest-input composition: both Pedersen sigma components verify.
    #[test]
    fn zk_leaf_leg_link_accepts_genuine() {
        let (value, vb) = real_leaf(2_000_000, 31337);
        let r_value = scalar(24);
        let (value_leg, link) = prove_zk_leaf_leg_link(value, &r_value, vb, b"transfer-ctx");
        assert_eq!(
            verify_zk_leaf_leg_link(&value_leg.to_bytes().0, vb, &link, b"transfer-ctx"),
            Ok(())
        );
    }

    /// NEGATIVE composition: swapping in a Pedersen leg for a different value is
    /// rejected by step B. This remains independent of the missing PI-preimage link.
    #[test]
    fn zk_leaf_leg_link_rejects_value_mismatch() {
        let (value, vb) = real_leaf(7_777, 55);
        let r_value = scalar(25);
        let (_honest_leg, link) = prove_zk_leaf_leg_link(value, &r_value, vb, b"ctx");
        // The attacker publishes a value_leg for a DIFFERENT amount under the same
        // proof (this is the malleability the linker exists to stop).
        let forged_leg = ValueCommitment::commit(value + 500, &r_value);
        assert_eq!(
            verify_zk_leaf_leg_link(&forged_leg.to_bytes().0, vb, &link, b"ctx"),
            Err(ZkValueLinkError::LinkFailed)
        );
    }

    /// NEGATIVE composition: tampering with the link_leg (step A) is caught even
    /// if step (B) would pass — the binding proof no longer matches the substituted
    /// leg. Guards against an attacker who keeps a valid equal-message proof but
    /// swaps the transcript-associated leg.
    #[test]
    fn zk_leaf_leg_link_rejects_tampered_link_leg() {
        let (value, vb) = real_leaf(42, 8);
        let r_value = scalar(26);
        let (value_leg, mut link) = prove_zk_leaf_leg_link(value, &r_value, vb, b"ctx");
        // Replace the link leg with a commitment to a different value.
        link.link_leg = ValueCommitment::commit(value + 9, &scalar(99)).to_bytes().0;
        assert_eq!(
            verify_zk_leaf_leg_link(&value_leg.to_bytes().0, vb, &link, b"ctx"),
            Err(ZkValueLinkError::LinkFailed)
        );
    }
}
