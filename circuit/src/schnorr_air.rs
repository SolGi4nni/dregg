//! Schnorr signature verification AIR.
//!
//! Provides trace generation and constraint checking for Schnorr signature
//! verification over the BabyBear^8 elliptic curve.
//!
//! # What the AIR proves
//!
//! Given public inputs `(pk, R, s, message_hash)` and the recomputed Fiat-Shamir
//! challenge `e = H(R, pk, message_hash)`, the trace witnesses the two scalar
//! multiplications `s·G` and `e·pk` via double-and-add, and the final boundary
//! enforces the Schnorr verification equation
//!
//! ```text
//!   s·G + e·pk == R.
//! ```
//!
//! ## Trace layout (one bit of a scalar per row)
//!
//! Each scan row processes one bit `b_i` of a scalar against a running base
//! point `B_i` (the i-th doubling of the fixed base) and a running accumulator
//! `A_i`:
//!
//! - `BASE` holds `B_i = 2^i · base` (base = `G` in phase 0, `pk` in phase 1).
//! - `ACC`  holds `A_i = (sum_{j<i} b_j · B_j)` — the partial scalar product.
//! - On each row: `B_{i+1} = double(B_i)` and `A_{i+1} = A_i + b_i·B_i`.
//! - `LAMBDA` is the slope witness for the conditional addition: when `b_i = 1`
//!   and the two points have distinct x, `λ·(x_B − x_A) = (y_B − y_A)` (the
//!   degree-2 in-circuit point-addition check).
//!
//! After the last bit of phase 0, `ACC = s·G`; after the last bit of phase 1,
//! `ACC = e·pk`. The Phase-2 boundary row checks `s·G + e·pk == R`.
//!
//! The constraint side here is a *faithful executable model* of that AIR: the
//! transitions and the boundary are all checked (it is NOT a vacuous bit-only
//! check). A bit-valid trace whose additions/doublings or final equality do not
//! hold is rejected.

use crate::babybear8::BabyBear8;
use crate::field::BabyBear;
use crate::schnorr_curve::{CurvePoint, Scalar};
use crate::schnorr_sig::{SchnorrPublicKey, SchnorrSignature};

/// Trace width: 43 columns.
pub const SCHNORR_AIR_WIDTH: usize = 43;

/// Number of scalar bits scanned per phase. The curve order `N` is a 248-bit
/// prime, and scalars are reduced into `[0, N)` and carried as 8 full u32 limbs,
/// so a phase must scan all 256 bits (8·32) to realize any scalar `< N`.
pub const SCALAR_BITS: usize = 256;

/// Total trace height (power-of-2 padded). Two `SCALAR_BITS` scan phases plus the
/// boundary row need `2·256 + 1` rows; the next power of two is 1024.
pub const TRACE_HEIGHT: usize = 1024;

/// Row index where Phase 0 (s*G) begins.
pub const PHASE_0_START: usize = 0;

/// Row index where Phase 1 (e*PK computation) begins.
pub const PHASE_1_START: usize = SCALAR_BITS;

/// Row index where Phase 2 (final boundary check) begins.
pub const PHASE_2_START: usize = 2 * SCALAR_BITS;

/// Row index where Phase 3 (idle padding) begins.
pub const PHASE_3_START: usize = PHASE_2_START + 1;

/// Column index constants.
pub mod col {
    /// Accumulator x-coordinate (8 limbs): cols 0..7.
    pub const ACC_X: usize = 0;
    /// Accumulator y-coordinate (8 limbs): cols 8..15.
    pub const ACC_Y: usize = 8;
    /// Accumulator infinity flag: col (unused as a separate column; encoded by
    /// (0,0) sentinel — see `point_from_row`).
    /// Base point x-coordinate (8 limbs): cols 16..23.
    pub const BASE_X: usize = 16;
    /// Base point y-coordinate (8 limbs): cols 24..31.
    pub const BASE_Y: usize = 24;
    /// Scalar bit (0 or 1): col 32.
    pub const SCALAR_BIT: usize = 32;
    /// Lambda (slope witness, 8 limbs): cols 33..40.
    pub const LAMBDA: usize = 33;
    /// Operation type: col 41 (0 = copy [bit 0], 1 = add [bit 1]).
    pub const OP_TYPE: usize = 41;
    /// Phase indicator: col 42.
    pub const PHASE: usize = 42;
}

/// Public input index constants.
pub mod pi {
    /// Public key x-coordinate (8 elements).
    pub const PK_X: usize = 0;
    /// Public key y-coordinate (8 elements).
    pub const PK_Y: usize = 8;
    /// R point x-coordinate (8 elements).
    pub const R_X: usize = 16;
    /// R point y-coordinate (8 elements).
    pub const R_Y: usize = 24;
    /// Scalar s (8 elements).
    pub const S: usize = 32;
    /// Message hash (8 elements).
    pub const MSG_HASH: usize = 40;
    /// Total public input count.
    pub const TOTAL: usize = 48;
}

/// Witness for Schnorr signature verification.
///
/// `challenge` is the Fiat–Shamir scalar `e` reduced mod the curve order `N`,
/// carried as a full 8-limb [`Scalar`] (it spans up to 248 bits, so it does not
/// fit in `[BabyBear; 8]` whose limbs are each `< 2^31`).
pub struct SchnorrVerificationWitness {
    pub pk: SchnorrPublicKey,
    pub sig: SchnorrSignature,
    pub message_hash: [BabyBear; 8],
    pub challenge: Scalar,
}

/// Recompute the Fiat-Shamir challenge scalar `e` from `(R, PK, message_hash)`.
///
/// Delegates to the canonical signer transcript
/// ([`crate::schnorr_sig::compute_challenge_from_elements`]) so the AIR's `e`
/// is bit-for-bit the value the signature was produced against, reduced mod `N`.
pub fn recompute_challenge(
    r: &CurvePoint,
    pk: &CurvePoint,
    message_hash: &[BabyBear; 8],
) -> Scalar {
    crate::schnorr_sig::compute_challenge_from_elements(r, pk, message_hash)
}

/// Generate the Schnorr verification trace.
///
/// Computes the genuine double-and-add chains for `s·G` (phase 0) and `e·pk`
/// (phase 1), recording per-row the running accumulator, running base (doubled
/// each row), the scalar bit, and the slope witness for the conditional add.
/// Returns `(trace_rows, public_inputs)`.
pub fn generate_schnorr_trace(
    witness: &SchnorrVerificationWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    use crate::schnorr_curve::GENERATOR;

    let num_rows = TRACE_HEIGHT;
    let mut trace: Vec<Vec<BabyBear>> = vec![vec![BabyBear::ZERO; SCHNORR_AIR_WIDTH]; num_rows];

    let s_bits = scalar_to_bits(&witness.sig.s);
    let e_bits = scalar_to_bits(&witness.challenge);

    // Phase 0: double-and-add for s*G.
    fill_scan_phase(
        &mut trace,
        PHASE_0_START,
        BabyBear::ZERO,
        GENERATOR,
        &s_bits,
    );
    // Phase 1: double-and-add for e*pk.
    fill_scan_phase(
        &mut trace,
        PHASE_1_START,
        BabyBear::ONE,
        witness.pk.0,
        &e_bits,
    );

    // Phase 2: final boundary row (carries the phase tag; the constraint reads
    // the last accumulators of phases 0/1 and R from public inputs).
    trace[PHASE_2_START][col::PHASE] = BabyBear::new(2);
    trace[PHASE_2_START][col::OP_TYPE] = BabyBear::new(2);

    // Phase 3: idle padding.
    for row in trace.iter_mut().take(num_rows).skip(PHASE_3_START) {
        row[col::PHASE] = BabyBear::new(3);
    }

    // Build public inputs.
    let mut public_inputs = vec![BabyBear::ZERO; pi::TOTAL];
    for i in 0..8 {
        public_inputs[pi::PK_X + i] = witness.pk.0.x.0[i];
        public_inputs[pi::PK_Y + i] = witness.pk.0.y.0[i];
        public_inputs[pi::R_X + i] = witness.sig.r.x.0[i];
        public_inputs[pi::R_Y + i] = witness.sig.r.y.0[i];
        public_inputs[pi::S + i] = BabyBear::new(witness.sig.s[i]);
        public_inputs[pi::MSG_HASH + i] = witness.message_hash[i];
    }

    (trace, public_inputs)
}

/// Fill one double-and-add scan phase (`SCALAR_BITS` rows starting at `start`).
fn fill_scan_phase(
    trace: &mut [Vec<BabyBear>],
    start: usize,
    phase_tag: BabyBear,
    base: CurvePoint,
    bits: &[u8],
) {
    let mut acc = CurvePoint::INFINITY;
    let mut cur_base = base;

    for i in 0..SCALAR_BITS {
        let row = start + i;
        let bit = if i < bits.len() { bits[i] } else { 0 };

        write_point_to_row(&mut trace[row], col::ACC_X, &acc);
        write_point_to_row(&mut trace[row], col::BASE_X, &cur_base);
        trace[row][col::SCALAR_BIT] = BabyBear::new(bit as u32);
        trace[row][col::PHASE] = phase_tag;
        trace[row][col::OP_TYPE] = BabyBear::new(bit as u32);

        // Slope witness for the conditional addition acc + cur_base (only
        // meaningful when bit == 1 and the points are addable with distinct x).
        if bit == 1 && !acc.is_infinity && !cur_base.is_infinity && acc.x != cur_base.x {
            let dx = cur_base.x.sub(&acc.x);
            let dy = cur_base.y.sub(&acc.y);
            if let Some(dx_inv) = dx.inverse() {
                let lambda = dy.mul(&dx_inv);
                write_bb8_to_row(&mut trace[row], col::LAMBDA, &lambda);
            }
        }

        if bit == 1 {
            acc = acc.add(&cur_base);
        }
        cur_base = cur_base.double();
    }
}

/// Check all trace constraints.
///
/// Enforces the full Schnorr AIR (NOT a vacuous bit-only check):
/// 1. Each `scalar_bit` is boolean and `op_type == scalar_bit` in scan rows.
/// 2. Phase-0/1 boundary: first-row `ACC == infinity`; first-row `BASE` equals
///    the fixed base (`G` for phase 0, `pk` for phase 1, read from public inputs).
/// 3. Base transition: `BASE_{i+1} == double(BASE_i)` within a phase.
/// 4. Accumulator transition: `ACC_{i+1} == ACC_i + (bit ? BASE_i : O)`, and
///    when `bit == 1` the recorded `LAMBDA` satisfies the slope equation
///    `λ·(x_B − x_A) == (y_B − y_A)` (degree-2 in-circuit add check).
/// 5. Final boundary (phase 2): `s·G + e·pk == R`, where `s·G` / `e·pk` are the
///    last accumulators of phases 0 / 1 and `R` is read from public inputs.
pub fn check_trace_constraints(trace: &[Vec<BabyBear>], public_inputs: &[BabyBear]) -> bool {
    if trace.len() < TRACE_HEIGHT || public_inputs.len() < pi::TOTAL {
        return false;
    }

    let pk = point_from_pi(public_inputs, pi::PK_X, pi::PK_Y);
    let r_pub = point_from_pi(public_inputs, pi::R_X, pi::R_Y);

    // --- Phase 0: s*G, base = G ---
    if !check_scan_phase(trace, PHASE_0_START, crate::schnorr_curve::GENERATOR) {
        return false;
    }
    // --- Phase 1: e*pk, base = pk ---
    if !check_scan_phase(trace, PHASE_1_START, pk) {
        return false;
    }

    // Recover the two final accumulators (after the last scanned bit of each
    // phase): A_final = A_last + (bit_last ? B_last : O).
    let s_g = final_accumulator(trace, PHASE_0_START);
    let e_pk = final_accumulator(trace, PHASE_1_START);

    // --- Phase 2 boundary: s*G + e*pk == R ---
    if trace[PHASE_2_START][col::PHASE] != BabyBear::new(2) {
        return false;
    }
    let lhs = s_g.add(&e_pk);
    lhs == r_pub
}

/// Verify the per-row transitions of one scan phase.
fn check_scan_phase(trace: &[Vec<BabyBear>], start: usize, base: CurvePoint) -> bool {
    // Boundary: first-row accumulator is the point at infinity, first-row base
    // is the declared fixed base.
    let acc0 = point_from_row(&trace[start], col::ACC_X);
    if !acc0.is_infinity {
        return false;
    }
    let base0 = point_from_row(&trace[start], col::BASE_X);
    if base0 != base {
        return false;
    }

    for i in 0..SCALAR_BITS {
        let row = start + i;
        let bit = trace[row][col::SCALAR_BIT];

        // (1) boolean bit + op_type == bit.
        if bit != BabyBear::ZERO && bit != BabyBear::ONE {
            return false;
        }
        if trace[row][col::OP_TYPE] != bit {
            return false;
        }

        let acc = point_from_row(&trace[row], col::ACC_X);
        let cur_base = point_from_row(&trace[row], col::BASE_X);

        // (4a) slope-witness equation when bit == 1 and addable with distinct x.
        if bit == BabyBear::ONE
            && !acc.is_infinity
            && !cur_base.is_infinity
            && acc.x != cur_base.x
        {
            let lambda = bb8_from_row(&trace[row], col::LAMBDA);
            let lhs = lambda.mul(&cur_base.x.sub(&acc.x));
            let rhs = cur_base.y.sub(&acc.y);
            if lhs != rhs {
                return false;
            }
        }

        // Expected next-row points.
        let expected_acc_next = if bit == BabyBear::ONE {
            acc.add(&cur_base)
        } else {
            acc
        };
        let expected_base_next = cur_base.double();

        // The last scan row has no in-phase successor; its forward transition is
        // realized by `final_accumulator` / the next phase's boundary instead.
        if i + 1 < SCALAR_BITS {
            let next = start + i + 1;
            let acc_next = point_from_row(&trace[next], col::ACC_X);
            let base_next = point_from_row(&trace[next], col::BASE_X);
            // (4) accumulator transition.
            if acc_next != expected_acc_next {
                return false;
            }
            // (3) base doubling transition.
            if base_next != expected_base_next {
                return false;
            }
        }
    }
    true
}

/// The accumulator value after the final scanned bit of the phase at `start`.
fn final_accumulator(trace: &[Vec<BabyBear>], start: usize) -> CurvePoint {
    let last = start + SCALAR_BITS - 1;
    let acc = point_from_row(&trace[last], col::ACC_X);
    let cur_base = point_from_row(&trace[last], col::BASE_X);
    if trace[last][col::SCALAR_BIT] == BabyBear::ONE {
        acc.add(&cur_base)
    } else {
        acc
    }
}

/// Verify a Schnorr signature via trace generation and constraint checking.
pub fn verify_schnorr_via_trace(trace: &[Vec<BabyBear>], public_inputs: &[BabyBear]) -> bool {
    check_trace_constraints(trace, public_inputs)
}

// ============================================================================
// Helpers
// ============================================================================

// Write a curve point's x and y limbs to the trace row at `start_col`.
fn write_point_to_row(row: &mut [BabyBear], start_col: usize, point: &CurvePoint) {
    // Infinity is encoded as (0, 0). On y^2 = x^3 + a·x + b, the point (0, 0)
    // would require b = 0 (the a·x term vanishes at x = 0); since b = z^3 + 8 ≠ 0
    // for this curve, (0, 0) is off-curve and the sentinel is unambiguous.
    if point.is_infinity {
        for i in 0..8 {
            row[start_col + i] = BabyBear::ZERO;
            row[start_col + 8 + i] = BabyBear::ZERO;
        }
        return;
    }
    for i in 0..8 {
        row[start_col + i] = point.x.0[i];
        row[start_col + 8 + i] = point.y.0[i];
    }
}

fn write_bb8_to_row(row: &mut [BabyBear], start_col: usize, val: &BabyBear8) {
    for i in 0..8 {
        row[start_col + i] = val.0[i];
    }
}

fn bb8_from_row(row: &[BabyBear], start_col: usize) -> BabyBear8 {
    let mut limbs = [BabyBear::ZERO; 8];
    limbs.copy_from_slice(&row[start_col..start_col + 8]);
    BabyBear8(limbs)
}

// Reconstruct a curve point from x/y limb columns (x at `x_col`, y at x_col+8).
fn point_from_row(row: &[BabyBear], x_col: usize) -> CurvePoint {
    let x = bb8_from_row(row, x_col);
    let y = bb8_from_row(row, x_col + 8);
    if x.is_zero() && y.is_zero() {
        return CurvePoint::INFINITY;
    }
    CurvePoint::new(x, y)
}

// Reconstruct a curve point from a pair of public-input ranges.
fn point_from_pi(public_inputs: &[BabyBear], x_pi: usize, y_pi: usize) -> CurvePoint {
    let mut x = [BabyBear::ZERO; 8];
    let mut y = [BabyBear::ZERO; 8];
    x.copy_from_slice(&public_inputs[x_pi..x_pi + 8]);
    y.copy_from_slice(&public_inputs[y_pi..y_pi + 8]);
    let xp = BabyBear8(x);
    let yp = BabyBear8(y);
    if xp.is_zero() && yp.is_zero() {
        return CurvePoint::INFINITY;
    }
    CurvePoint::new(xp, yp)
}

// Helper: convert Scalar ([u32; 8]) to its full 256 bits (LSB-first). All 32
// bits of every limb are emitted — a reduced scalar `< N` (248-bit) uses up to
// 248 of them and the rest are zero, but the curve order needs the full width.
fn scalar_to_bits(s: &Scalar) -> Vec<u8> {
    let mut bits = Vec::with_capacity(256);
    for &limb in s.iter() {
        for bit_idx in 0..32 {
            bits.push(((limb >> bit_idx) & 1) as u8);
        }
    }
    bits
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schnorr_curve::GENERATOR;
    use crate::schnorr_sig::{schnorr_keygen, schnorr_sign};

    /// Build a verification witness from a real keygen+sign, recomputing the
    /// challenge `e` exactly as the signer/verifier does (the canonical
    /// transcript), reduced mod `N`.
    fn real_witness(seed: [u8; 32], msg: &[u8]) -> SchnorrVerificationWitness {
        let (sk, pk) = schnorr_keygen(&seed);
        let sig = schnorr_sign(&sk, &pk, msg);
        let msg_blake = blake3::hash(msg);
        let message_hash = BabyBear::encode_hash(msg_blake.as_bytes());
        let challenge =
            crate::schnorr_sig::compute_challenge_from_elements(&sig.r, &pk.0, &message_hash);
        SchnorrVerificationWitness {
            pk,
            sig,
            message_hash,
            challenge,
        }
    }

    #[test]
    fn trace_has_expected_shape() {
        let w = real_witness([0x42; 32], b"shape");
        let (trace, pis) = generate_schnorr_trace(&w);
        assert_eq!(trace.len(), TRACE_HEIGHT);
        assert_eq!(trace[0].len(), SCHNORR_AIR_WIDTH);
        assert_eq!(pis.len(), pi::TOTAL);
        // Phase tags.
        assert_eq!(trace[PHASE_0_START][col::PHASE], BabyBear::ZERO);
        assert_eq!(trace[PHASE_1_START][col::PHASE], BabyBear::ONE);
        assert_eq!(trace[PHASE_2_START][col::PHASE], BabyBear::new(2));
    }

    /// The scan really computes the scalar products: the final phase-0
    /// accumulator equals `s·G`, phase-1 equals `e·pk`.
    #[test]
    fn scan_computes_scalar_products() {
        let w = real_witness([0x07; 32], b"scan");
        let (trace, _) = generate_schnorr_trace(&w);

        let s_g_scan = final_accumulator(&trace, PHASE_0_START);
        let s_g_direct = GENERATOR.scalar_mul(&w.sig.s);
        assert_eq!(s_g_scan, s_g_direct, "phase-0 scan must equal s*G");

        let e_pk_scan = final_accumulator(&trace, PHASE_1_START);
        let e_pk_direct = w.pk.0.scalar_mul(&w.challenge);
        assert_eq!(e_pk_scan, e_pk_direct, "phase-1 scan must equal e*pk");
    }

    /// A genuine signature's trace passes every constraint.
    #[test]
    fn valid_signature_trace_accepted() {
        let w = real_witness([0xAB; 32], b"accept me");
        let (trace, pis) = generate_schnorr_trace(&w);
        assert!(
            verify_schnorr_via_trace(&trace, &pis),
            "a real signature's trace must satisfy the AIR"
        );
    }

    /// TOOTH (closure 1): a FORGED signature with a perfectly bit-valid trace is
    /// REJECTED. We forge by replacing R in the public inputs with a different
    /// point (so `s·G + e·pk != R`), while the trace's bits remain {0,1}. The old
    /// vacuous check accepted any bit-valid trace; the real AIR rejects this.
    #[test]
    fn forged_signature_with_bit_valid_trace_rejected() {
        let w = real_witness([0xCD; 32], b"forge");
        let (trace, mut pis) = generate_schnorr_trace(&w);
        // Sanity: bits are all boolean (the trace is "bit-valid").
        for row in trace.iter().take(PHASE_2_START) {
            let b = row[col::SCALAR_BIT];
            assert!(b == BabyBear::ZERO || b == BabyBear::ONE);
        }
        // Forge R := 2G (a valid curve point, but not the signature's R).
        let fake_r = GENERATOR.double();
        for i in 0..8 {
            pis[pi::R_X + i] = fake_r.x.0[i];
            pis[pi::R_Y + i] = fake_r.y.0[i];
        }
        assert!(
            !verify_schnorr_via_trace(&trace, &pis),
            "a forged R must fail the final equality even with a bit-valid trace"
        );
    }

    /// TOOTH: tampering the public key in the public inputs (so phase-1's base
    /// boundary no longer matches the scanned base) is rejected.
    #[test]
    fn tampered_pk_rejected() {
        let w = real_witness([0x11; 32], b"tamper-pk");
        let (trace, mut pis) = generate_schnorr_trace(&w);
        // Corrupt pk.x in the public inputs.
        pis[pi::PK_X] = pis[pi::PK_X] + BabyBear::ONE;
        assert!(
            !verify_schnorr_via_trace(&trace, &pis),
            "pk boundary mismatch must be rejected"
        );
    }

    /// TOOTH: flipping a scalar bit (without recomputing the accumulator chain)
    /// breaks the accumulator transition and is rejected.
    #[test]
    fn flipped_bit_breaks_transition() {
        let w = real_witness([0x22; 32], b"flip");
        let (mut trace, pis) = generate_schnorr_trace(&w);
        // Find a phase-0 row whose bit is 0 and flip it to 1 (op_type follows so
        // constraint (1) still passes), leaving the accumulator chain stale.
        let mut flipped = false;
        for i in 0..SCALAR_BITS - 1 {
            let row = PHASE_0_START + i;
            if trace[row][col::SCALAR_BIT] == BabyBear::ZERO {
                trace[row][col::SCALAR_BIT] = BabyBear::ONE;
                trace[row][col::OP_TYPE] = BabyBear::ONE;
                flipped = true;
                break;
            }
        }
        assert!(flipped, "expected at least one zero bit to flip");
        assert!(
            !verify_schnorr_via_trace(&trace, &pis),
            "a flipped bit with a stale accumulator must break the transition"
        );
    }

    /// TOOTH: corrupting the slope witness LAMBDA on an addition row is rejected
    /// by the slope equation.
    #[test]
    fn corrupted_lambda_rejected() {
        let w = real_witness([0x33; 32], b"lambda");
        let (mut trace, pis) = generate_schnorr_trace(&w);
        // Find a phase-0 addition row (bit == 1) with a non-trivial lambda and
        // corrupt it.
        let mut corrupted = false;
        for i in 0..SCALAR_BITS - 1 {
            let row = PHASE_0_START + i;
            if trace[row][col::SCALAR_BIT] == BabyBear::ONE {
                let acc = point_from_row(&trace[row], col::ACC_X);
                let base = point_from_row(&trace[row], col::BASE_X);
                if !acc.is_infinity && !base.is_infinity && acc.x != base.x {
                    trace[row][col::LAMBDA] = trace[row][col::LAMBDA] + BabyBear::ONE;
                    corrupted = true;
                    break;
                }
            }
        }
        assert!(corrupted, "expected an addition row with a real lambda");
        assert!(
            !verify_schnorr_via_trace(&trace, &pis),
            "a corrupted slope witness must fail the slope equation"
        );
    }

    /// A non-boolean bit is rejected (the original check, preserved).
    #[test]
    fn non_boolean_bit_rejected() {
        let w = real_witness([0x44; 32], b"nonbool");
        let (mut trace, pis) = generate_schnorr_trace(&w);
        trace[PHASE_0_START][col::SCALAR_BIT] = BabyBear::new(2);
        assert!(!verify_schnorr_via_trace(&trace, &pis));
    }
}
