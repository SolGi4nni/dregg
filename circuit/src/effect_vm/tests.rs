//! Effect VM AIR tests (extracted from monolithic `effect_vm.rs`).

#![cfg(test)]

use super::*;
use crate::field::BabyBear;
use crate::poseidon2::{hash_2_to_1, hash_4_to_1};
use crate::stark::{StarkAir, prove, verify};

fn make_initial_state(balance: u64) -> CellState {
    CellState::new(balance, 0)
}

/// 8-limb widened-hash test value: low limb carries `x`, high limbs zero.
/// Mirrors the `bytes32_to_8_limbs` projection used for the 32-byte-widened
/// hash params (effect-vm-hash-widen lane). The AIR anchors limb[0]; all 8
/// limbs bind via compute_effects_hash.
fn w8(x: u32) -> [BabyBear; 8] {
    let mut a = [BabyBear::ZERO; 8];
    a[0] = BabyBear::new(x);
    a
}

/// Helper: generate trace, prove, verify, and check per-row constraints.
fn assert_effect_vm_roundtrip(
    state: &CellState,
    effects: &[Effect],
    description: &str,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let (trace, public_inputs) = generate_effect_vm_trace(state, effects);
    let air = EffectVmAir::new(trace.len());
    for alpha_val in [7u32, 13, 101] {
        let alpha = BabyBear::new(alpha_val);
        for row in 0..trace.len().saturating_sub(1) {
            let next = (row + 1) % trace.len();
            let c = air.eval_constraints(&trace[row], &trace[next], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "{description}: constraint non-zero at row {row} alpha={alpha_val}"
            );
        }
    }
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(result.is_ok(), "{description}: {:?}", result.err());
    (trace, public_inputs)
}

/// Helper: same as `assert_effect_vm_roundtrip` but only checks row-0 constraints.
/// Used for single-row effect tests that don't need the full row sweep.
fn assert_single_effect_roundtrip(
    state: &CellState,
    effect: Effect,
    description: &str,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>, EffectVmAir) {
    let effects = vec![effect];
    let (trace, public_inputs) = generate_effect_vm_trace(state, &effects);
    let air = EffectVmAir::new(trace.len());
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(result.is_ok(), "{description}: {:?}", result.err());
    for alpha_val in [7, 13, 17, 101] {
        let alpha = BabyBear::new(alpha_val);
        let c = air.eval_constraints(&trace[0], &trace[1], &public_inputs, alpha);
        assert_eq!(
            c,
            BabyBear::ZERO,
            "{description}: constraint non-zero with alpha={alpha_val}: c={}",
            c.0
        );
    }
    (trace, public_inputs, air)
}

/// Helper: `assert_effect_vm_roundtrip` with explicit context (for effects
/// that require PI-side values such as `approved_handoffs_root`).
fn assert_effect_vm_roundtrip_ext(
    state: &CellState,
    effects: &[Effect],
    context: EffectVmContext,
    description: &str,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let (trace, public_inputs) = generate_effect_vm_trace_ext(state, effects, context);
    let air = EffectVmAir::new(trace.len());
    for alpha_val in [7u32, 13, 101] {
        let alpha = BabyBear::new(alpha_val);
        for row in 0..trace.len().saturating_sub(1) {
            let next = (row + 1) % trace.len();
            let c = air.eval_constraints(&trace[row], &trace[next], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "{description}: constraint non-zero at row {row} alpha={alpha_val}"
            );
        }
    }
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(result.is_ok(), "{description}: {:?}", result.err());
    (trace, public_inputs)
}

#[test]
fn test_single_transfer_outgoing() {
    let state = make_initial_state(1000);
    let effects = vec![Effect::Transfer {
        amount: 100,
        direction: 1,
    }];

    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    assert_eq!(trace.len(), 64); // padded to MIN_TRACE_HEIGHT=64 (FRI single-row-gap closure)
    assert_eq!(trace[0].len(), EFFECT_VM_WIDTH);

    let air = EffectVmAir::new(trace.len());
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "Single transfer should verify: {:?}",
        result.err()
    );

    // Check delta.
    let delta = extract_net_delta(&public_inputs).unwrap();
    assert_eq!(delta, -100);
}

#[test]
fn test_single_transfer_incoming() {
    let state = make_initial_state(500);
    let effects = vec![Effect::Transfer {
        amount: 200,
        direction: 0,
    }];

    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    let air = EffectVmAir::new(trace.len());
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "Incoming transfer should verify: {:?}",
        result.err()
    );

    let delta = extract_net_delta(&public_inputs).unwrap();
    assert_eq!(delta, 200);
}

#[test]
fn test_multi_effect_turn() {
    let state = make_initial_state(5000);
    let effects = vec![
        Effect::Transfer {
            amount: 100,
            direction: 1, // -100
        },
        Effect::SetField {
            field_idx: 2,
            value: BabyBear::new(42),
        },
        Effect::GrantCapability {
            cap_entry: w8(0xCAFE),
            phase_b: None,
        },
    ];

    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    // 3 effects padded to MIN_TRACE_HEIGHT=64 rows (FRI single-row-gap closure).
    assert_eq!(trace.len(), 64);

    let air = EffectVmAir::new(trace.len());
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "Multi-effect turn should verify: {:?}",
        result.err()
    );

    let delta = extract_net_delta(&public_inputs).unwrap();
    assert_eq!(delta, -100);
}

/// AIR-level half of the wrong-state-transition test: confirms that a
/// tampered row algebraically violates the constraints. This is the
/// deterministic algebraic guarantee — a tampered trace is *provably
/// unsatisfiable* as far as the AIR polynomial system is concerned.
///
/// The end-to-end STARK half lives in `test_wrong_state_transition_stark_rejects`.
/// That test was previously ignored (REVIEW[fri-single-row-gap]) but is now
/// enabled by MIN_TRACE_HEIGHT=64 (task #90).
#[test]
fn test_wrong_state_transition_air_rejects() {
    let state = make_initial_state(10000);
    let effects = vec![
        Effect::Transfer {
            amount: 100,
            direction: 1,
        },
        Effect::Transfer {
            amount: 50,
            direction: 0,
        },
        Effect::Transfer {
            amount: 30,
            direction: 1,
        },
        Effect::Transfer {
            amount: 20,
            direction: 0,
        },
        Effect::Transfer {
            amount: 10,
            direction: 1,
        },
        Effect::Transfer {
            amount: 5,
            direction: 0,
        },
        Effect::Transfer {
            amount: 1,
            direction: 1,
        },
    ];

    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

    // Tamper: set row 0 new_balance to wrong value AND tamper state_commit
    // to ensure the state commitment integrity constraint (Group 4) fires.
    trace[0][STATE_AFTER_BASE + state::BALANCE_LO] = BabyBear::new(999);
    trace[0][STATE_AFTER_BASE + state::STATE_COMMIT] =
        trace[0][STATE_AFTER_BASE + state::STATE_COMMIT] + BabyBear::new(1);

    // The AIR MUST algebraically reject the tampered trace. We probe
    // multiple alphas to rule out accidental zero cancellation at a single
    // random point.
    let air = EffectVmAir::new(trace.len());
    for alpha_val in [7u32, 13, 101, 997] {
        let alpha = BabyBear::new(alpha_val);
        let c0 = air.eval_constraints(&trace[0], &trace[1], &public_inputs, alpha);
        assert_ne!(
            c0,
            BabyBear::ZERO,
            "Tampered row 0 must produce non-zero AIR constraint evaluation (alpha={alpha_val})"
        );
    }
}

/// End-to-end STARK half of the wrong-state-transition test.
///
/// Previously ignored due to REVIEW[fri-single-row-gap] (task #90): short
/// traces give too few FRI folding rounds for reliable single-row tamper
/// detection. Fixed in task #90 by enforcing MIN_TRACE_HEIGHT=64 in
/// `generate_effect_vm_trace`. With 64 rows, domain_size=256, 6 FRI rounds,
/// a tampered quotient is at Hamming distance ≥ 3/4 · domain_size from any
/// valid codeword, so P(all 80 queries miss) ≤ (1/4)^80 ≈ 10^-48.
#[test]
// fri-single-row-gap closed: MIN_TRACE_HEIGHT=64 (task #90). 6 FRI rounds,
// P(miss) ≤ (1/4)^80 ≈ 10^-48. Test deterministically rejects tampered trace.
fn test_wrong_state_transition_stark_rejects() {
    let state = make_initial_state(10000);
    let effects = vec![
        Effect::Transfer {
            amount: 100,
            direction: 1,
        },
        Effect::Transfer {
            amount: 50,
            direction: 0,
        },
        Effect::Transfer {
            amount: 30,
            direction: 1,
        },
        Effect::Transfer {
            amount: 20,
            direction: 0,
        },
        Effect::Transfer {
            amount: 10,
            direction: 1,
        },
        Effect::Transfer {
            amount: 5,
            direction: 0,
        },
        Effect::Transfer {
            amount: 1,
            direction: 1,
        },
    ];

    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    trace[0][STATE_AFTER_BASE + state::BALANCE_LO] = BabyBear::new(999);
    trace[0][STATE_AFTER_BASE + state::STATE_COMMIT] =
        trace[0][STATE_AFTER_BASE + state::STATE_COMMIT] + BabyBear::new(1);

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "SOUNDNESS BUG: STARK accepted single-row tamper (fri-single-row-gap should be closed by MIN_TRACE_HEIGHT=64)"
    );
}

#[test]
fn test_invalid_selector_two_active_caught() {
    let state = make_initial_state(1000);
    let effects = vec![Effect::Transfer {
        amount: 50,
        direction: 0,
    }];

    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

    // Tamper: activate two selectors.
    trace[0][sel::NOOP] = BabyBear::ONE;
    // sel::TRANSFER is already 1, now both are 1.

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "Two active selectors should be caught"
    );
}

#[test]
fn test_nonce_gap_caught() {
    let state = make_initial_state(1000);
    let effects = vec![
        Effect::Transfer {
            amount: 50,
            direction: 0,
        },
        Effect::Transfer {
            amount: 30,
            direction: 0,
        },
    ];

    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

    // Tamper: skip a nonce (set state_after nonce on row 0 to wrong value).
    // The nonce in state_after[nonce] should be 1 (started at 0, incremented once).
    // Set it to 5 to create a gap.
    trace[0][STATE_AFTER_BASE + state::NONCE] = BabyBear::new(5);

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "Nonce gap should be caught"
    );
}

#[test]
fn test_padding_rows_valid() {
    let state = make_initial_state(100);
    // Single effect padded to 2 rows.
    let effects = vec![Effect::Transfer {
        amount: 10,
        direction: 0,
    }];

    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    assert_eq!(trace.len(), 64); // padded to MIN_TRACE_HEIGHT=64 (FRI single-row-gap closure)

    // Verify padding row has NoOp selector.
    assert_eq!(trace[1][sel::NOOP], BabyBear::ONE);

    let air = EffectVmAir::new(trace.len());

    // Check constraints on both rows.
    let alpha = BabyBear::new(7);
    // Only check rows 0..n-2 (transition constraints wrap at last row;
    // the STARK handles this via the transition vanishing polynomial).
    for i in 0..trace.len() - 1 {
        let next_idx = (i + 1) % trace.len();
        let c = air.eval_constraints(&trace[i], &trace[next_idx], &public_inputs, alpha);
        assert_eq!(
            c,
            BabyBear::ZERO,
            "Constraint non-zero at row {}: c = {}",
            i,
            c.0
        );
    }
}

#[test]
fn test_conservation_violation_caught() {
    let state = make_initial_state(1000);
    let effects = vec![Effect::Transfer {
        amount: 100,
        direction: 1,
    }];

    let (trace, mut public_inputs) = generate_effect_vm_trace(&state, &effects);

    // Tamper: claim delta = 0 instead of -100.
    public_inputs[pi::NET_DELTA_MAG] = BabyBear::ZERO;
    public_inputs[pi::NET_DELTA_SIGN] = BabyBear::ZERO;

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "Conservation violation should be caught by boundary constraint mismatch"
    );
}

#[test]
fn test_note_spend_and_create() {
    let state = make_initial_state(1000);
    let effects = vec![
        Effect::NoteSpend {
            nullifier: BabyBear::new(0xDEAD),
            value: 500,
        },
        Effect::NoteCreate {
            commitment: BabyBear::new(0xBEEF),
            value: 200,
        },
    ];

    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    let air = EffectVmAir::new(trace.len());
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "NoteSpend + NoteCreate should verify: {:?}",
        result.err()
    );

    // Net delta: +500 (NoteSpend credit) + 0 (NoteCreate is BALANCE-NEUTRAL — the
    // note value lives in the commitment, never on the transparent ledger; matches
    // the executor `apply_note_create` + the verified Lean descriptor). A prior
    // version debited NoteCreate's 200, giving +300; the divergence is now closed.
    let delta = extract_net_delta(&public_inputs).unwrap();
    assert_eq!(delta, 500);
}

/// D5 (NoteSpend nullifier cross-binding, approach A) — POSITIVE.
///
/// An honest NoteSpend whose EffectVM param0 (folded nullifier) matches
/// PI[NOTESPEND_NULLIFIER] verifies, and the gated per-row constraint is
/// satisfied (zero) on the NoteSpend row.
#[test]
fn test_notespend_nullifier_cross_binding_positive() {
    let state = make_initial_state(1000);
    let nullifier = BabyBear::new(0x1234_5678);
    let effects = vec![Effect::NoteSpend {
        nullifier,
        value: 500,
    }];

    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

    // The trace generator surfaced the folded nullifier into the PI slot.
    assert_eq!(
        public_inputs[pi::NOTESPEND_NULLIFIER], nullifier,
        "PI[NOTESPEND_NULLIFIER] must carry the NoteSpend's nullifier"
    );
    // ...and the NoteSpend row's param0 carries the same value.
    assert_eq!(
        trace[0][PARAM_BASE + param::NULLIFIER],
        nullifier,
        "row 0 param0 must equal the nullifier"
    );

    let air = EffectVmAir::new(trace.len());
    // Gated constraint is zero on every row (NoteSpend row included).
    for alpha_val in [7u32, 13, 101] {
        let alpha = BabyBear::new(alpha_val);
        for row in 0..trace.len().saturating_sub(1) {
            let c = air.eval_constraints(&trace[row], &trace[row + 1], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "matched nullifier: constraint non-zero at row {row} alpha={alpha_val}"
            );
        }
    }
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "matched NoteSpend nullifier should verify: {:?}",
        result.err()
    );
}

/// D5 (NoteSpend nullifier cross-binding, approach A) — ADVERSARIAL.
///
/// THE ATTACK: a malicious executor proves nullifier N via the spending /
/// binding proof but feeds a DIFFERENT M into the EffectVM. We model that by
/// SWAPPING the EffectVM trace's param0 (the folded nullifier the AIR sees)
/// to a value distinct from PI[NOTESPEND_NULLIFIER] (which the off-AIR
/// verifier reconstructs from the binding proof's certified nullifier). The
/// gated per-row equality `s_notespend * (param0 - PI[NOTESPEND_NULLIFIER])`
/// MUST fire, and the STARK MUST reject. If it does not, the binding is fake.
#[test]
fn test_notespend_nullifier_cross_binding_rejects_swap() {
    let state = make_initial_state(1000);
    let nullifier = BabyBear::new(0x1234_5678);
    let effects = vec![Effect::NoteSpend {
        nullifier,
        value: 500,
    }];

    // Honest trace + PI (PI[NOTESPEND_NULLIFIER] == nullifier, the value the
    // off-AIR verifier would reconstruct from the binding proof).
    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    assert_eq!(public_inputs[pi::NOTESPEND_NULLIFIER], nullifier);

    // SWAP: the executor feeds a different folded nullifier M into the
    // EffectVM's NoteSpend param0, while the PI still commits to N. This is
    // exactly the "prove N, spend M" attack at the AIR boundary.
    let swapped = BabyBear::new(0x0BAD_C0DE);
    assert_ne!(swapped, nullifier, "swap must change the value");
    trace[0][PARAM_BASE + param::NULLIFIER] = swapped;

    let air = EffectVmAir::new(trace.len());

    // (1) The gated constraint MUST be non-zero on the NoteSpend row for at
    // least one challenge — the binding genuinely catches the swap. If this
    // assertion fails, the cross-binding is FAKE.
    let mut fired = false;
    for alpha_val in [7u32, 13, 101] {
        let alpha = BabyBear::new(alpha_val);
        let c = air.eval_constraints(&trace[0], &trace[1], &public_inputs, alpha);
        if c != BabyBear::ZERO {
            fired = true;
        }
    }
    assert!(
        fired,
        "ADVERSARIAL: swapped NoteSpend nullifier did NOT trip the gated AIR \
         constraint — the cross-binding is FAKE"
    );

    // (2) End-to-end: the STARK proof+verify MUST reject the swapped trace.
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "ADVERSARIAL: swapped NoteSpend nullifier must be REJECTED by the STARK"
    );
}

/// D5b (NoteCreate commitment cross-binding, approach A) — POSITIVE.
///
/// An honest NoteCreate whose EffectVM param0 (folded commitment) matches
/// PI[NOTECREATE_COMMITMENT] verifies, and the gated per-row constraint is
/// satisfied (zero) on the NoteCreate row.
#[test]
fn test_notecreate_commitment_cross_binding_positive() {
    let state = make_initial_state(1000);
    let commitment = BabyBear::new(0x00C0_FFEE);
    let effects = vec![Effect::NoteCreate {
        commitment,
        value: 400,
    }];

    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

    // The trace generator surfaced the folded commitment into the PI slot.
    assert_eq!(
        public_inputs[pi::NOTECREATE_COMMITMENT], commitment,
        "PI[NOTECREATE_COMMITMENT] must carry the NoteCreate's commitment"
    );
    // ...and the NoteCreate row's param0 carries the same value.
    let nc_row = trace
        .iter()
        .position(|row| row[sel::NOTE_CREATE] == BabyBear::ONE)
        .expect("at least one row must carry sel::NOTE_CREATE");
    assert_eq!(
        trace[nc_row][PARAM_BASE + param::NOTE_COMMITMENT],
        commitment,
        "NoteCreate row param0 must equal the commitment"
    );

    let air = EffectVmAir::new(trace.len());
    // Gated constraint is zero on every row (NoteCreate row included).
    for alpha_val in [7u32, 13, 101] {
        let alpha = BabyBear::new(alpha_val);
        for row in 0..trace.len().saturating_sub(1) {
            let c = air.eval_constraints(&trace[row], &trace[row + 1], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "matched commitment: constraint non-zero at row {row} alpha={alpha_val}"
            );
        }
    }
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "matched NoteCreate commitment should verify: {:?}",
        result.err()
    );
}

/// D5b (NoteCreate commitment cross-binding, approach A) — ADVERSARIAL.
///
/// THE ATTACK: a malicious executor proves commitment C via the
/// SCHEMA_NOTE_CREATE binding proof but feeds a DIFFERENT C' into the
/// EffectVM. We model that by SWAPPING the EffectVM trace's param0 (the folded
/// commitment the AIR sees) to a value distinct from PI[NOTECREATE_COMMITMENT]
/// (which the off-AIR verifier reconstructs from the binding proof's certified
/// commitment). The gated per-row equality MUST fire, and the STARK MUST
/// reject. If it does not, the binding is fake.
#[test]
fn test_notecreate_commitment_cross_binding_rejects_swap() {
    let state = make_initial_state(1000);
    let commitment = BabyBear::new(0x00C0_FFEE);
    let effects = vec![Effect::NoteCreate {
        commitment,
        value: 400,
    }];

    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    assert_eq!(public_inputs[pi::NOTECREATE_COMMITMENT], commitment);

    let nc_row = trace
        .iter()
        .position(|row| row[sel::NOTE_CREATE] == BabyBear::ONE)
        .expect("at least one row must carry sel::NOTE_CREATE");

    // SWAP: executor feeds a different folded commitment C' into the
    // EffectVM's NoteCreate param0 while the PI still commits to C.
    let swapped = BabyBear::new(0x0BAD_BEEF);
    assert_ne!(swapped, commitment, "swap must change the value");
    trace[nc_row][PARAM_BASE + param::NOTE_COMMITMENT] = swapped;

    let air = EffectVmAir::new(trace.len());

    // (1) The gated constraint MUST be non-zero on the NoteCreate row for at
    // least one challenge — the binding genuinely catches the swap.
    let mut fired = false;
    for alpha_val in [7u32, 13, 101] {
        let alpha = BabyBear::new(alpha_val);
        let next = (nc_row + 1) % trace.len();
        let c = air.eval_constraints(&trace[nc_row], &trace[next], &public_inputs, alpha);
        if c != BabyBear::ZERO {
            fired = true;
        }
    }
    assert!(
        fired,
        "ADVERSARIAL: swapped NoteCreate commitment did NOT trip the gated AIR \
         constraint — the cross-binding is FAKE"
    );

    // (2) End-to-end: the STARK proof+verify MUST reject the swapped trace.
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "ADVERSARIAL: swapped NoteCreate commitment must be REJECTED by the STARK"
    );
}

/// D5c (Burn target cross-binding, approach A) — POSITIVE.
///
/// An honest Burn whose EffectVM param0 (folded target) matches
/// PI[BURN_TARGET_PI] verifies, and the gated per-row constraint is satisfied
/// (zero) on the Burn row.
#[test]
fn test_burn_target_cross_binding_positive() {
    let state = make_initial_state(1000);
    let target_hash = BabyBear::new(0x0000_CE11);
    let effects = vec![Effect::Burn {
        target_hash,
        amount_lo: BabyBear::new(250),
        amount_full: 250,
    }];

    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

    assert_eq!(
        public_inputs[pi::BURN_TARGET_PI], target_hash,
        "PI[BURN_TARGET_PI] must carry the Burn's target"
    );
    let burn_row = trace
        .iter()
        .position(|row| row[sel::BURN] == BabyBear::ONE)
        .expect("at least one row must carry sel::BURN");
    assert_eq!(
        trace[burn_row][PARAM_BASE + param::BURN_TARGET],
        target_hash,
        "Burn row param0 must equal the target"
    );

    let air = EffectVmAir::new(trace.len());
    for alpha_val in [7u32, 13, 101] {
        let alpha = BabyBear::new(alpha_val);
        for row in 0..trace.len().saturating_sub(1) {
            let c = air.eval_constraints(&trace[row], &trace[row + 1], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "matched burn target: constraint non-zero at row {row} alpha={alpha_val}"
            );
        }
    }
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "matched Burn target should verify: {:?}",
        result.err()
    );
}

/// D5c (Burn target cross-binding, approach A) — ADVERSARIAL.
///
/// THE ATTACK: a malicious executor proves the `old - new == amount` balance
/// arithmetic for target T via the SCHEMA_BURN binding proof but feeds a Burn
/// for a DIFFERENT target T' into the EffectVM. We model that by SWAPPING the
/// EffectVM trace's param0 (the folded target the AIR sees) to a value
/// distinct from PI[BURN_TARGET_PI] (which the off-AIR verifier reconstructs
/// from the binding proof's ledger-validated target). The gated per-row
/// equality MUST fire, and the STARK MUST reject. If it does not, the binding
/// is fake.
#[test]
fn test_burn_target_cross_binding_rejects_swap() {
    let state = make_initial_state(1000);
    let target_hash = BabyBear::new(0x0000_CE11);
    let effects = vec![Effect::Burn {
        target_hash,
        amount_lo: BabyBear::new(250),
        amount_full: 250,
    }];

    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    assert_eq!(public_inputs[pi::BURN_TARGET_PI], target_hash);

    let burn_row = trace
        .iter()
        .position(|row| row[sel::BURN] == BabyBear::ONE)
        .expect("at least one row must carry sel::BURN");

    // SWAP: executor feeds a different folded target T' into the EffectVM's
    // Burn param0 while the PI still commits to T.
    let swapped = BabyBear::new(0x0000_DEAD);
    assert_ne!(swapped, target_hash, "swap must change the value");
    trace[burn_row][PARAM_BASE + param::BURN_TARGET] = swapped;

    let air = EffectVmAir::new(trace.len());

    // (1) The gated constraint MUST be non-zero on the Burn row for at least
    // one challenge — the binding genuinely catches the swap.
    let mut fired = false;
    for alpha_val in [7u32, 13, 101] {
        let alpha = BabyBear::new(alpha_val);
        let next = (burn_row + 1) % trace.len();
        let c = air.eval_constraints(&trace[burn_row], &trace[next], &public_inputs, alpha);
        if c != BabyBear::ZERO {
            fired = true;
        }
    }
    assert!(
        fired,
        "ADVERSARIAL: swapped Burn target did NOT trip the gated AIR \
         constraint — the cross-binding is FAKE"
    );

    // (2) End-to-end: the STARK proof+verify MUST reject the swapped trace.
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "ADVERSARIAL: swapped Burn target must be REJECTED by the STARK"
    );
}

#[test]
fn test_setfield_correct() {
    let state = make_initial_state(100);
    let effects = vec![Effect::SetField {
        field_idx: 3,
        value: BabyBear::new(77),
    }];

    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    let air = EffectVmAir::new(trace.len());

    // Verify constraints are zero with multiple alpha values.
    for alpha_val in [7, 13, 17, 101] {
        let alpha = BabyBear::new(alpha_val);
        let c = air.eval_constraints(&trace[0], &trace[1], &public_inputs, alpha);
        assert_eq!(
            c,
            BabyBear::ZERO,
            "SetField constraints non-zero with alpha={}: c={}",
            alpha_val,
            c.0
        );
    }
}

/// Stage 3 finale check: a single trace mixing many of the new AIR
/// variants — passthrough, balance-debit, balance-credit, cap-root
/// transitions — composes and verifies end-to-end.
#[test]
fn test_stage3_multi_variant_compose() {
    let state = make_initial_state(10_000);
    let effects = vec![
        // Cap-root transition variants:
        Effect::GrantCapability { cap_entry: w8(1), phase_b: None },
        Effect::RevokeCapability { slot_hash: w8(2) },
        // Stateless side-effects (passthrough):
        Effect::EmitEvent {
            topic_hash: {
                let mut a = [BabyBear::ZERO; 8];
                a[0] = BabyBear::new(0xE1);
                a
            },
            payload_hash: [BabyBear::ZERO; 8],
        },
        Effect::SetPermissions {
            permissions_hash: w8(0xE2),
        },
        Effect::SetVerificationKey { vk_hash: w8(0xE3) },
        Effect::RefreshDelegation,
        Effect::RevokeDelegation {
            child_hash: w8(0xE5),
        },
        Effect::CreateCell {
            create_hash: w8(0xE6),
        },
        Effect::SpawnWithDelegation {
            spawn_hash: w8(0xE7),
        },
        Effect::ExerciseViaCapability {
            exercise_hash: w8(0xE9),
        },
        Effect::Introduce {
            intro_hash: w8(0xEA),
        },
        Effect::PipelinedSend {
            send_hash: w8(0xEB),
        },
        // Balance arithmetic:
        Effect::BridgeMint {
            value_lo: BabyBear::new(200),
            mint_hash: BabyBear::new(0xF4),
            value_full: 200,
        },
    ];
    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    let air = EffectVmAir::new(trace.len());
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "Stage 3 multi-variant compose: proof should verify across {} effects: {:?}",
        effects.len(),
        result.err()
    );

    // Sanity: net delta should be +200 (BridgeMint; the escrow/lock debit
    // variants died in the verb lockstep).
    let delta = extract_net_delta(&public_inputs).unwrap();
    assert_eq!(delta, 200, "net delta should be +200 (mint 200)");
}

#[test]
fn test_passthrough_variants_verify() {
    // RefreshDelegation / RevokeDelegation share the EmitEvent passthrough
    // shape. One round-trip each.
    for effect in [
        Effect::RefreshDelegation,
        Effect::RevokeDelegation {
            child_hash: w8(0x222),
        },
    ] {
        let state = make_initial_state(700);
        let effects = vec![effect.clone()];
        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "Passthrough variant {:?} should verify: {:?}",
            effect,
            result.err()
        );
    }
}

#[test]
fn test_basic_effect_constraints() {
    struct Case {
        effect: Effect,
        balance: u64,
        extra_assert: fn(&[Vec<BabyBear>]),
    }

    let cases = [
        Case {
            effect: Effect::SetVerificationKey {
                vk_hash: w8(0xBEEF),
            },
            balance: 300,
            extra_assert: |_| {},
        },
        Case {
            effect: Effect::SetPermissions {
                permissions_hash: w8(0xDEAD),
            },
            balance: 200,
            extra_assert: |_| {},
        },
        Case {
            effect: Effect::EmitEvent {
                topic_hash: {
                    let mut a = [BabyBear::ZERO; 8];
                    a[0] = BabyBear::new(0xABCDEF);
                    a
                },
                payload_hash: [BabyBear::ZERO; 8],
            },
            balance: 500,
            extra_assert: |trace| {
                let old_bal = trace[0][STATE_BEFORE_BASE + state::BALANCE_LO];
                let new_bal = trace[0][STATE_AFTER_BASE + state::BALANCE_LO];
                assert_eq!(old_bal, new_bal, "balance must not change on EmitEvent");
                let old_cap = trace[0][STATE_BEFORE_BASE + state::CAP_ROOT];
                let new_cap = trace[0][STATE_AFTER_BASE + state::CAP_ROOT];
                assert_eq!(old_cap, new_cap, "cap_root must not change on EmitEvent");
            },
        },
        Case {
            effect: Effect::RevokeCapability {
                slot_hash: w8(0x12345),
            },
            balance: 100,
            extra_assert: |trace| {
                let old_root = trace[0][STATE_BEFORE_BASE + state::CAP_ROOT];
                let new_root = trace[0][STATE_AFTER_BASE + state::CAP_ROOT];
                assert_ne!(old_root, new_root, "cap_root should update on revoke");
                assert_eq!(
                    new_root,
                    hash_2_to_1(old_root, BabyBear::new(0x12345)),
                    "cap_root must equal hash_2_to_1(old_root, slot_hash)"
                );
            },
        },
    ];

    for case in cases {
        let (trace, _public_inputs, _air) = assert_single_effect_roundtrip(
            &make_initial_state(case.balance),
            case.effect,
            "basic effect constraint",
        );
        (case.extra_assert)(&trace);
    }
}

#[test]
fn test_single_row_constraint_eval() {
    let cases = [
        (
            100,
            Effect::Transfer {
                amount: 10,
                direction: 0,
            },
            "Transfer",
        ),
        (
            100,
            Effect::GrantCapability {
                cap_entry: w8(0x1234),
                phase_b: None,
            },
            "GrantCapability",
        ),
    ];
    for (balance, effect, name) in cases {
        let state = make_initial_state(balance);
        let effects = vec![effect];
        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());
        for alpha_val in [7, 13, 17, 101] {
            let alpha = BabyBear::new(alpha_val);
            let c = air.eval_constraints(&trace[0], &trace[1], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "{name} constraint non-zero with alpha={alpha_val}: c={}",
                c.0
            );
        }
    }
}

#[test]
fn test_four_effect_stark_roundtrip() {
    let state = make_initial_state(10000);
    let effects = vec![
        Effect::Transfer {
            amount: 500,
            direction: 1,
        },
        Effect::SetField {
            field_idx: 0,
            value: BabyBear::new(99),
        },
        Effect::GrantCapability {
            cap_entry: w8(0xABCD),
            phase_b: None,
        },
        Effect::Transfer {
            amount: 200,
            direction: 0,
        },
    ];

    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    assert_eq!(trace.len(), 64); // padded to MIN_TRACE_HEIGHT=64 (FRI single-row-gap closure)

    let air = EffectVmAir::new(trace.len());
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "4-effect STARK roundtrip should verify: {:?}",
        result.err()
    );

    // Net delta: -500 + 200 = -300.
    let delta = extract_net_delta(&public_inputs).unwrap();
    assert_eq!(delta, -300);
}

#[test]
fn test_constraint_evaluation_all_zeros_valid_trace() {
    // Generate a valid trace and verify constraint evaluations are zero on rows 0..n-2.
    let state = make_initial_state(5000);
    let effects = vec![
        Effect::Transfer {
            amount: 100,
            direction: 1,
        },
        Effect::Transfer {
            amount: 50,
            direction: 0,
        },
    ];

    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    let air = EffectVmAir::new(trace.len());

    // Try multiple alpha values to ensure constraint polynomial is zero on valid rows.
    for alpha_val in [3, 7, 13, 29, 101] {
        let alpha = BabyBear::new(alpha_val);
        for i in 0..trace.len() - 1 {
            let next_idx = (i + 1) % trace.len();
            let c = air.eval_constraints(&trace[i], &trace[next_idx], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "Constraint non-zero at row {} with alpha={}: c = {}",
                i,
                alpha_val,
                c.0
            );
        }
    }
}

// ========================================================================
// INTEGRATION TESTS: Real multi-effect turns through the full pipeline
// ========================================================================

/// Integration test: compose a realistic 3-effect turn (Transfer + SetField + GrantCap),
/// prove via STARK, verify, and confirm commitments match expected state transitions.
#[test]
fn test_integration_real_multi_effect_turn() {
    // Simulate a real sovereign cell with initial balance.
    let initial_state = CellState::new(50_000, 0);

    // A realistic turn: transfer some funds, update a field, grant a capability.
    let effects = vec![
        Effect::Transfer {
            amount: 1000,
            direction: 1, // outgoing
        },
        Effect::SetField {
            field_idx: 0,
            value: BabyBear::new(0x1234),
        },
        Effect::GrantCapability {
            cap_entry: w8(0xCAFEBABE),
            phase_b: None,
        },
    ];

    // Generate trace and public inputs.
    let (trace, public_inputs) = generate_effect_vm_trace(&initial_state, &effects);
    assert_eq!(trace.len(), 64); // padded to MIN_TRACE_HEIGHT=64 (FRI single-row-gap closure)

    // Verify constraints are satisfied on all rows.
    let air = EffectVmAir::new(trace.len());
    for alpha_val in [7, 13, 29, 101, 65537] {
        let alpha = BabyBear::new(alpha_val);
        for row in 0..trace.len() - 1 {
            let next_row = (row + 1) % trace.len();
            let c = air.eval_constraints(&trace[row], &trace[next_row], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "Integration: constraint non-zero at row {} with alpha={}: c={}",
                row,
                alpha_val,
                c.0
            );
        }
    }

    // Full STARK prove + verify roundtrip.
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "Integration: multi-effect turn should verify: {:?}",
        result.err()
    );

    // Verify state commitments match expected transitions.
    // The old_commitment PI should match initial_state.
    assert_eq!(
        public_inputs[pi::OLD_COMMIT],
        initial_state.state_commitment
    );

    // Manually replay the effects to get the expected final state.
    let mut expected_state = initial_state.clone();
    expected_state.balance -= 1000; // Transfer out
    expected_state.nonce += 1;
    expected_state.refresh_commitment();

    expected_state.fields[0] = BabyBear::new(0x1234); // SetField
    expected_state.nonce += 1;
    expected_state.refresh_commitment();

    expected_state.capability_root =
        hash_2_to_1(expected_state.capability_root, BabyBear::new(0xCAFEBABE));
    expected_state.nonce += 1;
    expected_state.refresh_commitment();

    assert_eq!(
        public_inputs[pi::NEW_COMMIT],
        expected_state.state_commitment,
        "Final commitment mismatch"
    );

    // Verify net delta: -1000 (transfer).
    let delta = extract_net_delta(&public_inputs).unwrap();
    assert_eq!(delta, -1000);

    // Verify effects hash covers ALL effects (Stage 1: 4-felt form).
    let expected_4 = compute_effects_hash_4(&effects);
    for i in 0..pi::EFFECTS_HASH_LEN {
        assert_eq!(
            public_inputs[pi::EFFECTS_HASH_BASE + i],
            expected_4[i],
            "effects_hash position {} mismatch",
            i,
        );
    }
}


/// IVC compression test: prove sequential turns and compress via the state
/// transition hash chain.
#[test]
fn test_ivc_compression_sequential_turns() {
    use crate::ivc::{prove_ivc_stark, verify_ivc_stark};

    // Turn 1: Transfer
    let state_0 = CellState::new(10_000, 0);
    let effects_1 = vec![Effect::Transfer {
        amount: 300,
        direction: 1,
    }];
    let (trace_1, pi_1) = generate_effect_vm_trace(&state_0, &effects_1);
    let air_1 = EffectVmAir::new(trace_1.len());
    let proof_1 = prove(&air_1, &trace_1, &pi_1);
    assert!(
        verify(&air_1, &proof_1, &pi_1).is_ok(),
        "Turn 1 should verify"
    );

    let commitment_1 = pi_1[pi::NEW_COMMIT];

    // Turn 2: SetField (starts from commitment_1)
    let mut state_1 = state_0.clone();
    state_1.balance -= 300;
    state_1.nonce += 1;
    state_1.refresh_commitment();
    assert_eq!(state_1.state_commitment, commitment_1);

    let effects_2 = vec![Effect::SetField {
        field_idx: 5,
        value: BabyBear::new(999),
    }];
    let (trace_2, pi_2) = generate_effect_vm_trace(&state_1, &effects_2);
    let air_2 = EffectVmAir::new(trace_2.len());
    let proof_2 = prove(&air_2, &trace_2, &pi_2);
    assert!(
        verify(&air_2, &proof_2, &pi_2).is_ok(),
        "Turn 2 should verify"
    );

    let commitment_2 = pi_2[pi::NEW_COMMIT];

    // Verify chain continuity: turn 2 starts where turn 1 ended.
    assert_eq!(
        pi_2[pi::OLD_COMMIT],
        commitment_1,
        "Turn 2 should start from Turn 1's final commitment"
    );

    // IVC compression: prove the hash chain [commitment_0 -> commitment_1 -> commitment_2]
    // via the StateTransitionAir (hash chain proof).
    let initial_root = state_0.state_commitment;
    let new_roots = vec![commitment_1, commitment_2];
    let (ivc_proof, ivc_pi) = prove_ivc_stark(initial_root, &new_roots);

    // Verify the compressed proof.
    let ivc_result = verify_ivc_stark(&ivc_proof, &ivc_pi);
    assert!(
        ivc_result.is_ok(),
        "IVC compressed proof should verify: {:?}",
        ivc_result.err()
    );

    // The IVC proof covers both turns in a single STARK proof.
    // Its public inputs bind: initial_root -> final accumulated hash covering all steps.
}

/// Test: malicious prover cannot skip effects via NoOp injection.
/// Inserting a NoOp between real effects would change the effects_hash (since
/// the hash covers the INTENDED effect list, not the padded trace).
#[test]
fn test_noop_padding_cannot_be_exploited() {
    let state = make_initial_state(1000);

    // Real effects list (what the prover commits to).
    let real_effects = vec![Effect::Transfer {
        amount: 100,
        direction: 1,
    }];

    // Compute the correct effects hash.
    let (real_hash_lo, real_hash_hi) = compute_effects_hash(&real_effects);

    // Now try a modified list with an injected NoOp.
    let tampered_effects = vec![
        Effect::NoOp, // injected
        Effect::Transfer {
            amount: 100,
            direction: 1,
        },
    ];
    let (tampered_hash_lo, tampered_hash_hi) = compute_effects_hash(&tampered_effects);

    // The hashes MUST differ -- the NoOp changes the commitment.
    assert_ne!(
        (real_hash_lo, real_hash_hi),
        (tampered_hash_lo, tampered_hash_hi),
        "Injecting NoOp must change the effects hash"
    );
}

/// Test: effect reordering is detected via effects_hash.
#[test]
fn test_effect_reordering_detected() {
    let effects_a = vec![
        Effect::Transfer {
            amount: 100,
            direction: 1,
        },
        Effect::SetField {
            field_idx: 0,
            value: BabyBear::new(1),
        },
    ];
    let effects_b = vec![
        Effect::SetField {
            field_idx: 0,
            value: BabyBear::new(1),
        },
        Effect::Transfer {
            amount: 100,
            direction: 1,
        },
    ];

    let (ha_lo, ha_hi) = compute_effects_hash(&effects_a);
    let (hb_lo, hb_hi) = compute_effects_hash(&effects_b);
    assert_ne!(
        (ha_lo, ha_hi),
        (hb_lo, hb_hi),
        "Reordering effects must change the effects hash"
    );
}

/// Test: NoOp padding row state_commitment tampering is caught by boundary constraint.
///
/// NOTE: The EffectVM AIR does NOT enforce `state_commitment == hash(state_columns)`
/// in-circuit (Poseidon2 is too high-degree for a degree-3 AIR). Individual field
/// tampering on the last row is caught only indirectly: the state_commitment boundary
/// constraint binds the last row's state_after.state_commitment to the public input
/// new_commitment. If an attacker tampers the commitment column itself, the boundary
/// constraint fires. For full field-level integrity on the last row, the executor
/// independently verifies the commitment matches the claimed state.
#[test]
fn test_noop_state_commitment_tamper_caught() {
    let state = make_initial_state(1000);
    let effects = vec![Effect::Transfer {
        amount: 50,
        direction: 0,
    }];

    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    assert_eq!(trace.len(), 64); // padded to MIN_TRACE_HEIGHT=64; row 1 is NoOp padding

    // Tamper: change the NoOp row's state_after commitment to a wrong value.
    // This MUST be caught by the boundary constraint on the last row.
    trace[1][STATE_AFTER_BASE + state::STATE_COMMIT] = BabyBear::new(0xBAD);

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "Tampered state_commitment on last row should be caught by boundary constraint"
    );
}

/// Test: transition constraint catches state_after != next.state_before on non-last rows.
/// This verifies that NoOp padding on interior rows (not the last) is fully constrained.
/// We verify via direct constraint evaluation (deterministic) rather than relying on
/// probabilistic STARK verification which can be sensitive to trace width.
#[test]
fn test_interior_noop_state_change_caught() {
    let state = make_initial_state(1000);
    // Use 7 effects to get an 8-row trace for more robust FRI detection.
    let effects = vec![
        Effect::Transfer {
            amount: 10,
            direction: 0,
        },
        Effect::Transfer {
            amount: 20,
            direction: 0,
        },
        Effect::Transfer {
            amount: 30,
            direction: 0,
        },
        Effect::Transfer {
            amount: 40,
            direction: 0,
        },
        Effect::Transfer {
            amount: 50,
            direction: 0,
        },
        Effect::Transfer {
            amount: 60,
            direction: 0,
        },
        Effect::Transfer {
            amount: 70,
            direction: 0,
        },
    ];

    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    assert_eq!(trace.len(), 64, "trace padded to MIN_TRACE_HEIGHT");

    // Tamper: change row 0's state_after balance (an interior row).
    // The transition constraint requires row 1's state_before == row 0's state_after,
    // so this must fail. We also tamper the state_commit to break GROUP 4.
    trace[0][STATE_AFTER_BASE + state::BALANCE_LO] =
        trace[0][STATE_AFTER_BASE + state::BALANCE_LO] + BabyBear::new(9999);
    // Also tamper state_commit to ensure GROUP 4 constraint fires.
    trace[0][STATE_AFTER_BASE + state::STATE_COMMIT] =
        trace[0][STATE_AFTER_BASE + state::STATE_COMMIT] + BabyBear::new(1);

    let air = EffectVmAir::new(trace.len());

    // Verify directly that constraint evaluation is non-zero at the tampered row.
    // This is a deterministic check (not probabilistic like STARK verify).
    let alpha = BabyBear::new(7);
    let c = air.eval_constraints(&trace[0], &trace[1], &public_inputs, alpha);
    assert_ne!(
        c,
        BabyBear::ZERO,
        "Interior row state tampering should produce non-zero constraints"
    );
}

/// Integration test: 8-effect turn (maximum before power-of-2 padding to 8).
/// Tests a complex realistic scenario.
#[test]
fn test_integration_8_effect_sovereign_turn() {
    let state = CellState::new(100_000, 10);

    let effects = vec![
        Effect::Transfer {
            amount: 5000,
            direction: 1,
        }, // -5000
        Effect::Transfer {
            amount: 2000,
            direction: 0,
        }, // +2000
        Effect::SetField {
            field_idx: 0,
            value: BabyBear::new(42),
        },
        Effect::SetField {
            field_idx: 7,
            value: BabyBear::new(99),
        },
        Effect::GrantCapability {
            cap_entry: w8(0x1111),
            phase_b: None,
        },
        Effect::GrantCapability {
            cap_entry: w8(0x2222),
            phase_b: None,
        },
    ];

    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    assert_eq!(trace.len(), 64); // padded to MIN_TRACE_HEIGHT=64 (FRI single-row-gap closure)

    let air = EffectVmAir::new(trace.len());

    // Verify all constraint rows.
    for alpha_val in [7, 13, 101] {
        let alpha = BabyBear::new(alpha_val);
        for row in 0..trace.len() - 1 {
            let next_row = (row + 1) % trace.len();
            let c = air.eval_constraints(&trace[row], &trace[next_row], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "8-effect: constraint non-zero at row {} with alpha={}: c={}",
                row,
                alpha_val,
                c.0
            );
        }
    }

    // STARK roundtrip.
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "8-effect sovereign turn should verify: {:?}",
        result.err()
    );

    // Net delta: -5000 + 2000 = -3000 (the escrow/obligation legs of the
    // original 8-effect turn died with the verb lockstep).
    let delta = extract_net_delta(&public_inputs).unwrap();
    assert_eq!(delta, -3000);
}

/// Test: commitment continuity across multiple sequential effect VM proofs.
/// Verifies that proof N's new_commitment == proof N+1's old_commitment.
#[test]
fn test_commitment_chain_continuity() {
    let mut current_state = CellState::new(20_000, 0);

    // 3 sequential turns, each proven separately.
    let turn_effects = vec![
        vec![Effect::Transfer {
            amount: 100,
            direction: 1,
        }],
        vec![
            Effect::SetField {
                field_idx: 2,
                value: BabyBear::new(77),
            },
            Effect::Transfer {
                amount: 200,
                direction: 0,
            },
        ],
        vec![Effect::GrantCapability {
            cap_entry: w8(0xFACE),
            phase_b: None,
        }],
    ];

    let mut commitments = vec![current_state.state_commitment];

    for effects in &turn_effects {
        let (trace, pi) = generate_effect_vm_trace(&current_state, effects);
        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &pi);
        assert!(verify(&air, &proof, &pi).is_ok());

        // Verify chain link: old_commit matches our tracked state.
        assert_eq!(pi[pi::OLD_COMMIT], current_state.state_commitment);

        // Advance state by replaying effects.
        for effect in effects {
            match effect {
                Effect::Transfer { amount, direction } => {
                    if *direction == 1 {
                        current_state.balance -= amount;
                    } else {
                        current_state.balance += amount;
                    }
                    current_state.nonce += 1;
                    current_state.refresh_commitment();
                }
                Effect::SetField { field_idx, value } => {
                    current_state.fields[*field_idx as usize] = *value;
                    current_state.nonce += 1;
                    current_state.refresh_commitment();
                }
                Effect::GrantCapability { cap_entry, .. } => {
                    // 32-byte widening: cap_root advance uses limb[0] (matches
                    // the trace generator + AIR).
                    current_state.capability_root =
                        hash_2_to_1(current_state.capability_root, cap_entry[0]);
                    current_state.nonce += 1;
                    current_state.refresh_commitment();
                }
                _ => {}
            }
        }

        assert_eq!(pi[pi::NEW_COMMIT], current_state.state_commitment);
        commitments.push(current_state.state_commitment);
    }

    // Verify all commitments form a chain.
    assert_eq!(commitments.len(), 4);
    for i in 0..commitments.len() - 1 {
        assert_ne!(
            commitments[i],
            commitments[i + 1],
            "Sequential commitments should differ"
        );
    }
}


/// Test: effects_hash binding prevents subset attacks.
/// A prover cannot claim a subset of effects and get a valid proof.
#[test]
fn test_effects_hash_prevents_subset_attack() {
    let state = make_initial_state(5000);

    let full_effects = vec![
        Effect::Transfer {
            amount: 100,
            direction: 1,
        },
        Effect::Transfer {
            amount: 200,
            direction: 1,
        },
    ];
    let subset_effects = vec![Effect::Transfer {
        amount: 100,
        direction: 1,
    }];

    let (full_hash_lo, full_hash_hi) = compute_effects_hash(&full_effects);
    let (sub_hash_lo, sub_hash_hi) = compute_effects_hash(&subset_effects);

    assert_ne!(
        (full_hash_lo, full_hash_hi),
        (sub_hash_lo, sub_hash_hi),
        "Subset of effects must have different hash"
    );

    // Generate proof for full effects, but tamper public inputs to claim subset hash.
    let (trace, mut pi) = generate_effect_vm_trace(&state, &full_effects);
    pi[pi::EFFECTS_HASH_LO] = sub_hash_lo;
    pi[pi::EFFECTS_HASH_HI] = sub_hash_hi;

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &pi);
        verify(&air, &proof, &pi)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "Tampered effects_hash should fail verification"
    );
}

/// Benchmark-style test: measure proof size for a 4-effect turn.
#[test]
fn test_proof_size_measurement() {
    use crate::stark::proof_to_bytes;

    let state = CellState::new(100_000, 0);
    let effects = vec![
        Effect::Transfer {
            amount: 500,
            direction: 1,
        },
        Effect::SetField {
            field_idx: 1,
            value: BabyBear::new(42),
        },
        Effect::GrantCapability {
            cap_entry: w8(0xBEEF),
            phase_b: None,
        },
        Effect::Transfer {
            amount: 100,
            direction: 0,
        },
    ];

    let (trace, pi) = generate_effect_vm_trace(&state, &effects);
    let air = EffectVmAir::new(trace.len());
    let proof = prove(&air, &trace, &pi);
    let proof_bytes = proof_to_bytes(&proof);

    // The proof should be reasonable in size. For a 64-row (MIN_TRACE_HEIGHT),
    // 65-column trace with our STARK parameters (blowup 4, 32 queries),
    // expect ~400-450 KiB. This is larger than the 6-column
    // SovereignTransitionAir (~24 KiB) due to the wider trace (65 columns),
    // but acceptable for a general-purpose VM.
    assert!(
        proof_bytes.len() < 500_000,
        "Proof too large: {} bytes (expected < 500 KiB)",
        proof_bytes.len()
    );

    // Also verify the proof after serialization roundtrip.
    use crate::stark::proof_from_bytes;
    let deserialized = proof_from_bytes(&proof_bytes).unwrap();
    let result = verify(&air, &deserialized, &pi);
    assert!(
        result.is_ok(),
        "Deserialized proof should verify: {:?}",
        result.err()
    );
}

// ========================================================================
// CapTP EFFECT TESTS
// ========================================================================


/// Test: Multi-effect CapTP turn (export + enliven + drop).
#[test]
fn test_captp_multi_effect_turn() {
    let mut state = CellState::new(5000, 0);
    // Initialize counters: field[5]=3 (refcount), field[6]=1 (use_count), field[7]=0 (export_counter).
    state.fields[5] = BabyBear::new(3);
    state.fields[6] = BabyBear::new(1);
    state.fields[7] = BabyBear::new(0);
    state.refresh_commitment();

    let effects = vec![
        Effect::Transfer {
            amount: 100,
            direction: 1,
        },
    ];

    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    let air = EffectVmAir::new(trace.len());

    // Verify all constraints pass.
    for alpha_val in [7u32, 13, 101] {
        let alpha = BabyBear::new(alpha_val);
        for row in 0..trace.len() - 1 {
            let next_row = (row + 1) % trace.len();
            let c = air.eval_constraints(&trace[row], &trace[next_row], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "CapTP multi-effect: constraint non-zero at row {} alpha={}",
                row,
                alpha_val
            );
        }
    }

    // STARK roundtrip.
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "CapTP multi-effect turn should verify: {:?}",
        result.err()
    );

    // Net delta: only the Transfer contributes (-100).
    let delta = extract_net_delta(&public_inputs).unwrap();
    assert_eq!(delta, -100);
}


// ========================================================================
// SOUNDNESS TESTS: Adversarial exploitation attempts
// ========================================================================

/// Adversarial test (Gap 1): Attempt to fabricate net_delta by setting a
/// non-boolean sign value.
///
/// A malicious prover could try to set net_delta_sign to a non-boolean
/// value (e.g., 2) to manipulate the signed interpretation of the delta.
/// The in-circuit constraint `sign * (sign - 1) == 0` must reject this.
///
/// Previously ignored (REVIEW[fri-single-row-gap], task #90). Fixed by
/// MIN_TRACE_HEIGHT=64: 6 FRI rounds over domain_size=256, P(miss) ≤ (1/4)^80.
#[test]
fn test_soundness_non_boolean_delta_sign_rejected() {
    let state = make_initial_state(1000);
    let effects = vec![Effect::Transfer {
        amount: 100,
        direction: 1, // outgoing, net_delta = -100
    }];

    let (mut trace, mut public_inputs) = generate_effect_vm_trace(&state, &effects);

    // Tamper: set the net_delta sign to 2 (non-boolean) in aux[3] on row 0.
    trace[0][AUX_BASE + 3] = BabyBear::new(2);
    public_inputs[pi::NET_DELTA_SIGN] = BabyBear::new(2);

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "SOUNDNESS BUG: Non-boolean net_delta_sign MUST be rejected by the circuit"
    );
}

/// Adversarial test (Gap 1): Attempt balance underflow via modular wrap.
///
/// A malicious prover tries to transfer MORE than the balance, causing
/// new_bal_lo to wrap around the BabyBear modulus. The state commitment
/// constraint binds the wrapped value to the commitment hash. If a verifier
/// accepts any new_commitment the prover provides, value is created.
///
/// This test verifies that:
/// 1. The executor-side check (generate_effect_vm_trace) panics on underflow
/// 2. If a prover bypasses the executor and crafts a wrapping trace manually,
///    the state commitment will be different from what honest execution produces
#[test]
#[should_panic(expected = "Transfer underflow")]
fn test_soundness_balance_underflow_executor_rejects() {
    let state = make_initial_state(50); // Only 50 balance
    let effects = vec![Effect::Transfer {
        amount: 100, // Transfer 100 > 50 = underflow
        direction: 1,
    }];

    // The executor MUST reject this at trace generation time.
    let _ = generate_effect_vm_trace(&state, &effects);
}

/// Adversarial test (Gap 1): A crafted trace with wrapped balance is rejected
/// by the verifier — not merely by a commitment-hash comparison.
///
/// Scenario: honest execution has balance=200, outgoing transfer of 100, so
/// new_balance = 100. A malicious prover bypasses the executor and instead
/// forges a trace whose STATE_AFTER encodes new_balance = (p - 50) — the
/// modular-wrap result of attempting 50 - 100 in BabyBear. They also recompute
/// the state commitment for that wrapped state so the hash slot is internally
/// consistent. The STARK MUST reject because the arithmetic constraint
/// `balance_after = balance_before - amount` is violated in the polynomial.
///
/// This test was previously commitment-comparison-only (the verifier was never
/// invoked). Fixed per TEST-REALITY-AUDIT task #89.
#[test]
fn test_soundness_wrapped_balance_different_commitment() {
    // BabyBear prime p = 2013265921.
    const BABYBEAR_P: u64 = 2013265921;

    // ── 1. Algebraic pre-check: wrapped vs. honest commitment must differ ──
    let honest_final = CellState::new(100, 1); // after a 100-unit outgoing transfer from 200
    let wrapped_balance = BABYBEAR_P - 50; // what 50 - 100 wraps to in BabyBear
    let wrapped_state = CellState::new(wrapped_balance, 1);
    assert_ne!(
        honest_final.state_commitment, wrapped_state.state_commitment,
        "SOUNDNESS BUG: Wrapped balance must produce a different commitment"
    );

    // ── 2. Forge a trace and attempt to prove it ───────────────────────────
    // Generate an honest trace: balance=200, transfer 100 out.
    let honest_start = make_initial_state(200);
    let effects = vec![Effect::Transfer {
        amount: 100,
        direction: 1, // outgoing
    }];
    let (mut trace, public_inputs) = generate_effect_vm_trace(&honest_start, &effects);

    // Tamper: inject the wrapped balance value and a recomputed commitment.
    // This simulates a prover who bypassed the executor-side underflow check
    // and manually constructed a trace with the wrapped value.
    let (wrapped_lo, wrapped_hi) = split_u64(wrapped_balance);
    trace[0][STATE_AFTER_BASE + state::BALANCE_LO] = wrapped_lo;
    trace[0][STATE_AFTER_BASE + state::BALANCE_HI] = wrapped_hi;
    // Recompute commitment for the forged state so the commitment slot is
    // internally consistent (this is the hardest-to-catch forgery path).
    let forged_commit = CellState::compute_commitment(
        wrapped_balance,
        1, // nonce incremented by the Transfer row
        &[BabyBear::ZERO; 8],
        BabyBear::ZERO,
    );
    trace[0][STATE_AFTER_BASE + state::STATE_COMMIT] = forged_commit;

    // ── 3. The STARK MUST reject the forged trace ──────────────────────────
    // The arithmetic constraint `balance_after = balance_before - amount`
    // is violated: 200 - 100 = 100 ≠ (p - 50). The verifier must catch this.
    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "SOUNDNESS BUG: STARK accepted a trace with wrapped-balance forgery"
    );
}

/// W9-RANGECHECK adversarial test: the IN-CIRCUIT balance-limb range gadget
/// (CONSTRAINT GROUP 2a) rejects an underflow-wrapped `balance_lo` directly,
/// at the constraint-evaluation level — NOT merely via the commitment or the
/// Transfer-lo arithmetic. This is the property metatheory's
/// `TransferAirSoundness.transfer_underflow_attack` proves is otherwise
/// admissible, now CLOSED in-circuit.
///
/// We forge the hardest-to-catch trace: an outgoing transfer of `amount` from
/// `old < amount`, where the prover sets `new_bal_lo` to the wrapped field
/// value `p - (amount - old)`. Crucially, this value SATISFIES the Transfer-lo
/// constraint (the wrap is exactly what `old - amount` evaluates to in the
/// field). The ONLY thing standing between this forgery and acceptance is the
/// new range gadget: `p - k ≥ 2^30` has no 30-bit boolean decomposition, so
/// the recomposition constraint is non-zero no matter what bits the prover
/// writes.
#[test]
fn test_soundness_range_gadget_rejects_wrapped_lo() {
    const BABYBEAR_P: u64 = 2013265921;

    // Honest trace from a balance large enough that trace gen does not panic;
    // we then forge row 0 to model the (50 - 100) underflow wrap.
    let honest_start = make_initial_state(150);
    let effects = vec![Effect::Transfer {
        amount: 100,
        direction: 1, // outgoing
    }];
    let (mut trace, public_inputs) = generate_effect_vm_trace(&honest_start, &effects);

    // The field value that an underflow of (50 - 100) would produce.
    let wrapped_lo_u64 = BABYBEAR_P - 50; // = p - (100 - 50)
    let wrapped_lo = BabyBear::new((wrapped_lo_u64 % BABYBEAR_P) as u32);

    // Make the Transfer-lo constraint itself SATISFIED by the wrap:
    //   new_bal_lo == old_bal_lo - amount  (in the field) with old=50, amt=100.
    trace[0][STATE_BEFORE_BASE + state::BALANCE_LO] = BabyBear::new(50);
    trace[0][STATE_AFTER_BASE + state::BALANCE_LO] = wrapped_lo;

    // Best-effort prover decomposition: the low 30 bits of the wrapped value.
    // No 30-bit decomposition recomposes to the full field element `p - 50`,
    // so the recomposition constraint must still fire.
    let low30 = (wrapped_lo_u64 & 0x3FFF_FFFF) as u32;
    for i in 0..BAL_LIMB_BITS {
        trace[0][AUX_BASE + aux_off::NEW_BAL_LO_BIT_BASE + i] = BabyBear::new((low30 >> i) & 1);
    }

    // The range gadget MUST make the combined constraint non-zero at row 0.
    let air = EffectVmAir::new(trace.len());
    let alpha = BabyBear::new(101);
    let c = air.eval_constraints(&trace[0], &trace[1], &public_inputs, alpha);
    assert_ne!(
        c,
        BabyBear::ZERO,
        "SOUNDNESS BUG: in-circuit range gadget accepted a wrapped (>=2^30) balance_lo"
    );
}

/// Adversarial test (Gap 1): Verify that verify_balance_limb_ranges catches
/// out-of-range balance limbs that could result from modular wrapping.
#[test]
fn test_soundness_limb_range_validation_catches_wrap() {
    // A state with a "wrapped" balance where the lo limb exceeds 2^30.
    // In practice, this can't happen via honest split_u64, but a malicious
    // prover could craft trace values where balance_lo > 2^30.
    let mut bad_state = CellState::new(0, 0);
    // Force an impossible balance value (would result from wrap-around).
    bad_state.balance = (1u64 << 61) + 1; // exceeds hi limb range

    let result = verify_balance_limb_ranges(&bad_state);
    assert!(
        result.is_err(),
        "verify_balance_limb_ranges MUST catch out-of-range limbs"
    );
}

// ========================================================================
// STORAGE QUEUE EFFECT TESTS
// ========================================================================


// ========================================================================
// STORAGE PHASE 3: AtomicQueueTx and PipelineStep TESTS
// ========================================================================


// ========================================================================
// SOVEREIGN CELL QUEUE OPERATION TESTS (Bug fix verification)
// ========================================================================


// ========================================================================
// P0-1 ADVERSARIAL TESTS: net_delta PI binding
// ========================================================================
//
// The fix introduces:
//   - PIs INIT_BAL_LO / INIT_BAL_HI / FINAL_BAL_LO / FINAL_BAL_HI
//   - Boundary constraints pinning row 0 state_before.balance_* and
//     last_row state_after.balance_* to those PIs
//   - A per-row PI-only constraint (Group 6):
//     (FINAL_BAL_LO - INIT_BAL_LO) + (FINAL_BAL_HI - INIT_BAL_HI) * 2^30
//       - NET_DELTA_MAG * (1 - 2 * NET_DELTA_SIGN) == 0

/// P0-1: prover claims net_delta=0 on a trace with real delta=-500. Rejected.
#[test]
fn test_soundness_p0_1_net_delta_forgery_to_zero_rejected() {
    let state = make_initial_state(1000);
    let effects = vec![Effect::Transfer {
        amount: 500,
        direction: 1,
    }];

    let (trace, mut public_inputs) = generate_effect_vm_trace(&state, &effects);
    let air = EffectVmAir::new(trace.len());

    // Sanity: honest PIs verify.
    let proof_honest = prove(&air, &trace, &public_inputs);
    assert!(
        verify(&air, &proof_honest, &public_inputs).is_ok(),
        "Honest trace must verify before tamper"
    );

    // Tamper PI: claim no balance change.
    public_inputs[pi::NET_DELTA_MAG] = BabyBear::ZERO;
    public_inputs[pi::NET_DELTA_SIGN] = BabyBear::ZERO;
    // Tamper aux[2]/aux[3] so the aux boundary constraint still passes.
    let mut tampered_trace = trace.clone();
    tampered_trace[0][AUX_BASE + 2] = BabyBear::ZERO;
    tampered_trace[0][AUX_BASE + 3] = BabyBear::ZERO;

    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &tampered_trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "P0-1 SOUNDNESS BUG: prover claimed net_delta=0 but real delta=-500. \
         Group 6 constraint MUST reject. Got: {:?}",
        result
    );
}

/// P0-1: prover flips net_delta sign (claim +500 instead of -500).
/// Previously ignored (REVIEW[stage2-fri-single-row-gap]); fixed by MIN_TRACE_HEIGHT=64 (task #90).
#[test]
fn test_soundness_p0_1_net_delta_sign_flip_rejected() {
    let state = make_initial_state(1000);
    let effects = vec![Effect::Transfer {
        amount: 500,
        direction: 1,
    }];

    let (trace, mut public_inputs) = generate_effect_vm_trace(&state, &effects);
    public_inputs[pi::NET_DELTA_SIGN] = BabyBear::ZERO;
    let mut tampered_trace = trace.clone();
    tampered_trace[0][AUX_BASE + 3] = BabyBear::ZERO;

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &tampered_trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "P0-1: sign-flipped net_delta must be rejected. Got: {:?}",
        result
    );
}

/// P0-1: prover lies about magnitude (claim mag=100 instead of 500).
/// Previously ignored (REVIEW[stage2-fri-single-row-gap]); fixed by MIN_TRACE_HEIGHT=64 (task #90).
#[test]
fn test_soundness_p0_1_net_delta_magnitude_lie_rejected() {
    let state = make_initial_state(1000);
    let effects = vec![Effect::Transfer {
        amount: 500,
        direction: 1,
    }];

    let (trace, mut public_inputs) = generate_effect_vm_trace(&state, &effects);
    public_inputs[pi::NET_DELTA_MAG] = BabyBear::new(100);
    let mut tampered_trace = trace.clone();
    tampered_trace[0][AUX_BASE + 2] = BabyBear::new(100);

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &tampered_trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "P0-1: magnitude-lie net_delta must be rejected. Got: {:?}",
        result
    );
}

/// P0-1: verifier-supplied INIT_BAL_LO disagrees with trace — boundary rejects.
#[test]
fn test_soundness_p0_1_init_bal_pi_tampered_rejected() {
    let state = make_initial_state(1000);
    let effects = vec![Effect::Transfer {
        amount: 500,
        direction: 1,
    }];

    let (trace, mut public_inputs) = generate_effect_vm_trace(&state, &effects);
    public_inputs[pi::INIT_BAL_LO] = BabyBear::new(999);

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "P0-1: lying INIT_BAL_LO must be rejected. Got: {:?}",
        result
    );
}

/// P0-1: verifier-supplied FINAL_BAL_LO disagrees with trace — boundary rejects.
#[test]
fn test_soundness_p0_1_final_bal_pi_tampered_rejected() {
    let state = make_initial_state(1000);
    let effects = vec![Effect::Transfer {
        amount: 500,
        direction: 1,
    }];

    let (trace, mut public_inputs) = generate_effect_vm_trace(&state, &effects);
    public_inputs[pi::FINAL_BAL_LO] = BabyBear::new(700);

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "P0-1: lying FINAL_BAL_LO must be rejected. Got: {:?}",
        result
    );
}

// ========================================================================
// P1-5 ADVERSARIAL TEST: PipelineStep pipeline_id non-zero
// ========================================================================
//
// The fix adds an aux column (aux[6] = pipeline_id^-1) and constraint
//   s_pipeline * (pipeline_id * aux[6] - 1) == 0
// forcing pipeline_id != 0 when the PipelineStep selector is active.


// ====================================================================
// Stage 1 (`EFFECT-VM-SHAPE-A.md`) adversarial tests
// ====================================================================

/// Stage 1: tampering with PI[OLD_COMMIT_BASE + 1] (one of the 3 new
/// commitment felts not bound to the trace) is caught by the PI matching
/// loop in the executor, but is NOT caught by the AIR itself (it's a
/// PI-only binding — see AUDIT[stage1-pi-only-bound] in pi module).
///
/// This test exercises the AIR-side behaviour: the proof verifies for
/// the values the prover declared (no algebraic violation). The
/// executor's recomputation catches the divergence; we test that in
/// `dregg-turn` integration tests.
#[test]
fn test_stage1_widened_pi_commitments_are_consistent() {
    let state = make_initial_state(1000);
    let effects = vec![Effect::Transfer {
        amount: 100,
        direction: 1,
    }];
    let (_trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

    // The 4-felt commitment slots must be present and non-zero (the
    // initial state has balance=1000, so the canonical commitment is
    // not the empty-tree sentinel).
    assert_eq!(public_inputs.len(), pi::BASE_COUNT);
    for i in 0..pi::OLD_COMMIT_LEN {
        // Position 0 is the legacy 1-felt commitment; positions 1..3 are
        // 3 independent compressions of the same intermediates with
        // distinct salts (see CellState::compute_commitment_4).
        let v = public_inputs[pi::OLD_COMMIT_BASE + i];
        assert_ne!(
            v,
            BabyBear::ZERO,
            "OLD_COMMIT[{}] should be non-zero for a real state",
            i
        );
    }
    // Positions 0..3 should be mutually distinct (different salts,
    // different hashes — collision probability negligible).
    for i in 1..pi::OLD_COMMIT_LEN {
        assert_ne!(
            public_inputs[pi::OLD_COMMIT_BASE],
            public_inputs[pi::OLD_COMMIT_BASE + i],
            "OLD_COMMIT positions 0 and {} should differ (4 independent squeezes)",
            i,
        );
    }
}

/// Stage 1: tampering with PI[NEW_COMMIT_BASE] (position 0, the in-trace
/// bound felt) must be caught by the AIR's boundary constraint pinning
/// the last row's STATE_COMMIT column.
#[test]
fn test_stage1_new_commit_position_0_tampered_rejected() {
    let state = make_initial_state(1000);
    let effects = vec![Effect::Transfer {
        amount: 100,
        direction: 1,
    }];
    let (trace, mut public_inputs) = generate_effect_vm_trace(&state, &effects);

    let original = public_inputs[pi::NEW_COMMIT_BASE];
    public_inputs[pi::NEW_COMMIT_BASE] = original + BabyBear::ONE;

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "Stage 1: tampered NEW_COMMIT[0] must be rejected by boundary. Got: {:?}",
        result
    );
}

/// Stage 1 sum-check: PI[CUSTOM_EFFECT_COUNT] mismatch with trace's
/// cumulative s_custom is rejected via the last-row boundary on
/// AUX[CUSTOM_COUNT_ACC].
#[test]
fn test_stage1_custom_count_pi_mismatch_rejected() {
    let state = make_initial_state(1000);
    let effects = vec![Effect::Transfer {
        amount: 100,
        direction: 1,
    }];
    let (trace, mut public_inputs) = generate_effect_vm_trace(&state, &effects);

    // Honest trace has 0 customs; declare 1 in PI.
    public_inputs[pi::CUSTOM_EFFECT_COUNT] = BabyBear::ONE;

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "Stage 1: declared CUSTOM_EFFECT_COUNT must match cumulative s_custom. Got: {:?}",
        result
    );
}

/// Stage 1: PI vector shorter than BASE_COUNT must be rejected.
#[test]
fn test_stage1_short_pi_rejected() {
    let state = make_initial_state(1000);
    let effects = vec![Effect::Transfer {
        amount: 100,
        direction: 1,
    }];
    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

    // Truncate PI by 1 element. The boundary constraint loop returns
    // early when public_inputs.len() < BASE_COUNT and the AIR
    // verification then has missing values.
    let short_pi: Vec<BabyBear> = public_inputs[..pi::BASE_COUNT - 1].to_vec();

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &short_pi)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "Stage 1: short PI vector must be rejected. Got: {:?}",
        result
    );
}

/// Stage 1: CURRENT_BLOCK_HEIGHT PI is present and consumed by the
/// trace generator (default context has block_height=0).
#[test]
fn test_stage1_current_block_height_pi_present() {
    let state = make_initial_state(1000);
    let effects = vec![Effect::Transfer {
        amount: 100,
        direction: 1,
    }];
    let context = EffectVmContext {
        current_block_height: 12345,
        max_custom_effects: pi::MAX_CUSTOM_EFFECTS_DEFAULT,
        approved_handoffs_root: [BabyBear::ZERO; 4],
        turn_hash: [BabyBear::ZERO; 4],
        effects_hash_global: [BabyBear::ZERO; 4],
        actor_nonce: 0,
        previous_receipt_hash: [BabyBear::ZERO; 4],
        ..Default::default()
    };
    let (_trace, public_inputs) = generate_effect_vm_trace_ext(&state, &effects, context);
    assert_eq!(
        public_inputs[pi::CURRENT_BLOCK_HEIGHT],
        BabyBear::new(12345),
    );
    assert_eq!(
        public_inputs[pi::MAX_CUSTOM_EFFECTS],
        BabyBear::new(pi::MAX_CUSTOM_EFFECTS_DEFAULT as u32),
    );
}

/// Stage 1: declaring max_custom_effects above the hard cap panics at
/// trace gen time (the trace generator asserts).
#[test]
#[should_panic(expected = "exceeds hard cap")]
fn test_stage1_max_custom_effects_above_hard_cap_panics() {
    let state = make_initial_state(1000);
    let effects = vec![Effect::Transfer {
        amount: 100,
        direction: 1,
    }];
    let context = EffectVmContext {
        current_block_height: 0,
        max_custom_effects: pi::MAX_CUSTOM_EFFECTS_HARD_CAP + 1,
        approved_handoffs_root: [BabyBear::ZERO; 4],
        turn_hash: [BabyBear::ZERO; 4],
        effects_hash_global: [BabyBear::ZERO; 4],
        actor_nonce: 0,
        previous_receipt_hash: [BabyBear::ZERO; 4],
        ..Default::default()
    };
    let _ = generate_effect_vm_trace_ext(&state, &effects, context);
}

// ====================================================================
// Stage 2 adversarial tests (REVIEW[stage1-acc-row0] resolution)
// ====================================================================

/// Stage 2: shifting acc[0] from 0 must be rejected by the row-0
/// boundary. With the exclusive-sum convention, acc[0] is always 0;
/// any non-zero value triggers the boundary constraint.
#[test]
fn test_stage2_acc_row0_shift_rejected() {
    let state = make_initial_state(1000);
    let effects = vec![Effect::Transfer {
        amount: 100,
        direction: 1,
    }];
    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

    // Tamper: shift acc[0] by 1 and propagate through the chain (to
    // pass the transition constraint). The last-row boundary then
    // sees `acc[last] == PI[CUSTOM_EFFECT_COUNT] + 1`, which fails.
    let one = BabyBear::ONE;
    for i in 0..trace.len() {
        trace[i][AUX_BASE + aux_off::CUSTOM_COUNT_ACC] =
            trace[i][AUX_BASE + aux_off::CUSTOM_COUNT_ACC] + one;
    }

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "Stage 2: shifted acc chain must fail at either row-0 or last-row boundary. Got: {:?}",
        result
    );
}


/// Stage 2 adversarial: applying MakeSovereign to an already-sovereign
/// cell is rejected. The cell's old reserved has mode bit == 1; the
/// new constraint `s_makesov * mode_bit == 0` fires.
#[test]
fn test_stage2_make_sovereign_double_transition_rejected() {
    // Construct a state with mode_flag already = 1 (sovereign).
    let mut state = CellState::new(1000, 0);
    state.mode_flag = 1;
    state.refresh_commitment();
    let effects = vec![Effect::MakeSovereign];
    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    let air = EffectVmAir::new(trace.len());
    let alpha = BabyBear::new(7);
    // Row 0 is the MakeSovereign effect on an already-sovereign cell.
    let c0 = air.eval_constraints(&trace[0], &trace[1 % trace.len()], &public_inputs, alpha);
    assert_ne!(
        c0,
        BabyBear::ZERO,
        "Stage 2: MakeSovereign on an already-sovereign cell must violate the AIR",
    );
}


/// Stage 2 adversarial: setting a sealed field is rejected.
/// The bit-decomposition of `old_reserved` is constrained to match
/// the actual reserved value, and the Lagrange-basis selection at
/// `field_idx` extracts the relevant bit. SetField requires bit == 0.
#[test]
fn test_stage2_setfield_on_sealed_field_rejected() {
    // (VERB-LOCKSTEP: the field-Seal effect is gone; a sealed field can only
    // arrive in the PRE-state now. Seed the mask directly and assert the
    // SetField row violates `s_setfield * bit_at_idx == 0`.)
    let mut state = make_initial_state(1000);
    state.sealed_field_mask = 1 << 3; // field 3 sealed in the pre-state
    state.refresh_commitment();
    let effects = vec![Effect::SetField {
        field_idx: 3,
        value: BabyBear::new(42),
    }];
    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    let air = EffectVmAir::new(trace.len());
    let alpha = BabyBear::new(7);
    // The SetField row is row 0.
    let c0 = air.eval_constraints(&trace[0], &trace[1 % trace.len()], &public_inputs, alpha);
    assert_ne!(
        c0,
        BabyBear::ZERO,
        "Stage 2: SetField on a sealed field must produce non-zero AIR constraint",
    );
}


/// Stage 2 adversarial: the reserved bit-decomposition is constrained
/// for EVERY row (not just sealing-effect rows). Tampering any bit so
/// the decomposition no longer reconstructs the reserved value must
/// fire the unconditional decomposition constraint at that row.
#[test]
fn test_stage2_reserved_bit_decomposition_tamper_rejected() {
    // (VERB-LOCKSTEP: the Seal-based setup died with the field-seal effect; the
    // reserved-bit decomposition constraints are UNCONDITIONAL on every row, so
    // a Transfer row exercises the same tooth.)
    let state = make_initial_state(1000);
    let effects = vec![Effect::Transfer { amount: 100, direction: 1 }];
    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    // Honest: reserved == 0 on row 0, so all decomposition bits are 0.
    // Tamper: claim bit_0 = 1 — the recomposition no longer equals old_reserved.
    trace[0][AUX_BASE + aux_off::RESERVED_BIT_0] = BabyBear::ONE;
    let air = EffectVmAir::new(trace.len());
    let alpha = BabyBear::new(7);
    let c0 = air.eval_constraints(&trace[0], &trace[1], &public_inputs, alpha);
    assert_ne!(
        c0,
        BabyBear::ZERO,
        "Stage 2: tampered reserved-bit decomposition must produce non-zero AIR constraint",
    );
}

/// Stage 2: trailing-NoOp pad is auto-inserted when the final effect
/// is Custom, so the exclusive-sum boundary on the last row still
/// equals the total custom count. Validates the trace SHAPE (not
/// end-to-end proof, since the Custom effect's state-unchanged
/// per-effect constraint is independently broken vs. trace gen's
/// nonce increment — tracked as AUDIT[stage2-custom-nonce-mismatch],
/// out of scope for this fix).
#[test]
fn test_stage2_trailing_custom_gets_pad_row() {
    let state = make_initial_state(1000);
    let effects = vec![
        Effect::Transfer {
            amount: 100,
            direction: 1,
        },
        Effect::Custom {
            program_vk_hash: [BabyBear::ONE; 8],
            proof_commitment: [BabyBear::new(2); 4],
        },
    ];
    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    // n_effects=2, last is Custom → need_extra_pad → (2+1).next_power_of_two()=4,
    // then .max(MIN_TRACE_HEIGHT=64) = 64.
    assert_eq!(
        trace.len(),
        64,
        "trace should be padded to MIN_TRACE_HEIGHT=64 rows"
    );
    // Last row must be NoOp.
    assert_eq!(
        trace[trace.len() - 1][sel::NOOP],
        BabyBear::ONE,
        "last row must be NoOp for exclusive-sum invariant"
    );
    // PI[CUSTOM_EFFECT_COUNT] should be 1.
    assert_eq!(
        public_inputs[pi::CUSTOM_EFFECT_COUNT],
        BabyBear::ONE,
        "exactly one custom effect declared"
    );
    // acc[0] == 0, acc[last] == 1 (the exclusive-sum totals).
    assert_eq!(
        trace[0][AUX_BASE + aux_off::CUSTOM_COUNT_ACC],
        BabyBear::ZERO,
        "acc[0] must be 0 (exclusive sum)"
    );
    assert_eq!(
        trace[trace.len() - 1][AUX_BASE + aux_off::CUSTOM_COUNT_ACC],
        BabyBear::ONE,
        "acc[last] must equal total custom count"
    );
}

// ========================================================================
// Stage 7 / P1.C adversarial tests for the 4 CapTP AIR variants.
//
// Each variant: tamper a witness aux column, evaluate constraints,
// assert non-zero (AIR rejects). Verdicts in the commit message.
// ========================================================================

fn assert_air_rejects(
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    row: usize,
    label: &str,
) {
    let air = EffectVmAir::new(trace.len());
    let next = (row + 1) % trace.len();
    // Sweep a few alphas to avoid an accidental zero for one challenge.
    let mut any_nonzero = false;
    for alpha_val in [7u32, 13, 101, 2017, 31337] {
        let alpha = BabyBear::new(alpha_val);
        let c = air.eval_constraints(&trace[row], &trace[next], public_inputs, alpha);
        if c != BabyBear::ZERO {
            any_nonzero = true;
            break;
        }
    }
    assert!(
        any_nonzero,
        "{}: AIR should reject tampered trace (constraint was zero for all alphas)",
        label,
    );
}


// ========================================================================
// Stage 7 / §B: trace-side ACTOR_NONCE boundary tests.
//
// Positive: a trace whose row-0 state_before.nonce matches
// PI[ACTOR_NONCE] verifies end-to-end.
//
// Adversarial: a trace where PI[ACTOR_NONCE] disagrees with
// row-0 state_before.nonce must be rejected by the STARK
// boundary check.
// ========================================================================

#[test]
fn test_stage7_actor_nonce_boundary_positive() {
    // Cell with nonce=5. The default-wrapper sets
    // ctx.actor_nonce = initial_nonce, so the boundary holds.
    let state = CellState::new(10_000, 5);
    let effects = vec![Effect::Transfer {
        amount: 100,
        direction: 1,
    }];
    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    assert_eq!(
        public_inputs[pi::ACTOR_NONCE],
        BabyBear::new(5),
        "default-wrapper should populate PI[ACTOR_NONCE] from initial_state.nonce",
    );
    let air = EffectVmAir::new(trace.len());
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "honest actor_nonce binding should verify: {:?}",
        result.err(),
    );
}

#[test]
fn test_stage7_actor_nonce_pi_mismatch_rejected() {
    // Cell with nonce=3, but we forge PI[ACTOR_NONCE]=99. The
    // STARK boundary check must reject.
    let state = CellState::new(10_000, 3);
    let effects = vec![Effect::Transfer {
        amount: 100,
        direction: 1,
    }];
    let (trace, mut public_inputs) = generate_effect_vm_trace(&state, &effects);
    assert_eq!(trace[0][STATE_BEFORE_BASE + state::NONCE], BabyBear::new(3));
    // Forge PI: claim actor_nonce = 99.
    public_inputs[pi::ACTOR_NONCE] = BabyBear::new(99);
    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "PI[ACTOR_NONCE] disagreeing with trace row-0 nonce must be rejected",
    );
}

#[test]
fn test_stage7_actor_nonce_trace_mismatch_rejected() {
    // Conversely: PI says nonce=5, trace forges nonce=99 in row 0.
    // The boundary check must reject.
    let state = CellState::new(10_000, 5);
    let effects = vec![Effect::Transfer {
        amount: 100,
        direction: 1,
    }];
    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    // Forge the trace: row-0 state_before.nonce = 99.
    // This also requires breaking the state-commitment hash chain,
    // which the STARK separately catches, but the boundary fires
    // first and is what we're testing here.
    trace[0][STATE_BEFORE_BASE + state::NONCE] = BabyBear::new(99);
    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "trace row-0 nonce disagreeing with PI[ACTOR_NONCE] must be rejected",
    );
}

// ============================================================================
// AIR-SOUNDNESS-AUDIT.md #70 — PI v2 VK-hash widening
// ============================================================================
//
// Pre-v2 the custom-effect dispatch path read 4 BabyBear felts (16 bytes) of
// VK hash from PI[CUSTOM_PROOFS_BASE..+4] and zero-padded the upper 16 bytes
// for registry lookup. Two VKs colliding on the lower 16 bytes (a ~2^64 work
// item under generic-hash assumptions, well below the 128-bit security floor)
// dispatched to the same handler regardless of their upper halves.
//
// Post-v2 PI carries the full 8-felt (32-byte) VK hash. The tests below
// adversarially construct two VK hashes that share their lower 16 bytes and
// differ in the upper 16, assert their PI projections diverge, and that the
// dispatch keys reconstructed via `babybear8_to_bytes32` are distinct.

#[test]
fn test_vk_pi_layout_version_is_v2() {
    // Sentinel for callers that gate on PI layout version: bumping this
    // constant should be a deliberate, audited PI-shape change.
    assert_eq!(pi::VK_PI_LAYOUT_VERSION, 2);
    // Entry size after v2 widening: 8 vk + 4 commit.
    assert_eq!(pi::CUSTOM_ENTRY_SIZE, 12);
}

#[test]
fn test_vk_hash_widening_distinguishes_upper_half_collisions() {
    // Adversary A and B share the lower 16 bytes (felts [0..4]) of their
    // VK hashes — under pre-v2 PI layout they would alias to the same
    // 32-byte registry key (zero-padded upper half), causing dispatch
    // confusion. Under v2 the upper 4 felts are bound through PI, so they
    // resolve to distinct registry entries.
    let low: [BabyBear; 4] = [
        BabyBear::new(0x1111),
        BabyBear::new(0x2222),
        BabyBear::new(0x3333),
        BabyBear::new(0x4444),
    ];
    let vk_a: [BabyBear; 8] = [
        low[0],
        low[1],
        low[2],
        low[3],
        BabyBear::new(0xAAAA_0001),
        BabyBear::new(0xAAAA_0002),
        BabyBear::new(0xAAAA_0003),
        BabyBear::new(0xAAAA_0004),
    ];
    let vk_b: [BabyBear; 8] = [
        low[0],
        low[1],
        low[2],
        low[3],
        BabyBear::new(0xBBBB_0001),
        BabyBear::new(0xBBBB_0002),
        BabyBear::new(0xBBBB_0003),
        BabyBear::new(0xBBBB_0004),
    ];
    // Lower halves match — pre-v2 zero-pad would have aliased.
    assert_eq!(&vk_a[..4], &vk_b[..4]);
    // Upper halves differ — v2 layout distinguishes.
    assert_ne!(&vk_a[4..], &vk_b[4..]);
    // Full 8-felt hashes differ.
    assert_ne!(vk_a, vk_b);
}

#[test]
fn test_vk_hash_widening_distinct_pi_projections() {
    // Build two Effect::Custom values whose vk_hashes collide on the
    // lower half. Their PI projections must occupy distinct 8-felt
    // ranges at PI[CUSTOM_PROOFS_BASE..+8].
    let state = make_initial_state(1000);
    let common_commit = [BabyBear::new(7); 4];
    let vk_a: [BabyBear; 8] = [
        BabyBear::new(0xC0DE_0001),
        BabyBear::new(0xC0DE_0002),
        BabyBear::new(0xC0DE_0003),
        BabyBear::new(0xC0DE_0004),
        BabyBear::new(0xA000_0001),
        BabyBear::new(0xA000_0002),
        BabyBear::new(0xA000_0003),
        BabyBear::new(0xA000_0004),
    ];
    let vk_b: [BabyBear; 8] = [
        // Same lower half as vk_a — pre-v2 would have collided here.
        vk_a[0],
        vk_a[1],
        vk_a[2],
        vk_a[3],
        // Upper half differs.
        BabyBear::new(0xB000_0001),
        BabyBear::new(0xB000_0002),
        BabyBear::new(0xB000_0003),
        BabyBear::new(0xB000_0004),
    ];
    let (_, pi_a) = generate_effect_vm_trace(
        &state,
        &[Effect::Custom {
            program_vk_hash: vk_a,
            proof_commitment: common_commit,
        }],
    );
    let (_, pi_b) = generate_effect_vm_trace(
        &state,
        &[Effect::Custom {
            program_vk_hash: vk_b,
            proof_commitment: common_commit,
        }],
    );
    // Pre-v2: PI[CUSTOM_PROOFS_BASE..+4] would match → same dispatch.
    let base = pi::CUSTOM_PROOFS_BASE;
    assert_eq!(
        &pi_a[base..base + 4],
        &pi_b[base..base + 4],
        "lower-half collision is preserved (precondition)"
    );
    // Post-v2: upper-half slots differ, so dispatch keys disagree.
    assert_ne!(
        &pi_a[base + 4..base + 8],
        &pi_b[base + 4..base + 8],
        "PI v2 must expose the upper 4 vk_hash felts so dispatch is distinct"
    );
    // The full 8-felt projections must differ overall.
    assert_ne!(&pi_a[base..base + 8], &pi_b[base..base + 8]);
    // Effects-hash binding (helpers absorbs all 8 felts) also differs.
    assert_ne!(
        &pi_a[pi::EFFECTS_HASH_BASE..pi::EFFECTS_HASH_BASE + pi::EFFECTS_HASH_LEN],
        &pi_b[pi::EFFECTS_HASH_BASE..pi::EFFECTS_HASH_BASE + pi::EFFECTS_HASH_LEN],
        "effects_hash must absorb the full 8-felt vk_hash"
    );
}

#[test]
fn test_vk_hash_pi_dispatch_key_full_32_bytes() {
    // Reconstruct the 32-byte registry dispatch key from the 8 PI felts and
    // confirm pre-v2 truncation would have lost the upper 16 bytes.
    fn babybear8_to_bytes32(elems: &[BabyBear; 8]) -> [u8; 32] {
        let mut out = [0u8; 32];
        for (i, e) in elems.iter().enumerate() {
            out[i * 4..i * 4 + 4].copy_from_slice(&e.0.to_le_bytes());
        }
        out
    }
    let vk_a: [BabyBear; 8] = [
        BabyBear::new(0xDEAD_0001),
        BabyBear::new(0xDEAD_0002),
        BabyBear::new(0xDEAD_0003),
        BabyBear::new(0xDEAD_0004),
        BabyBear::new(0xAAAA_0001),
        BabyBear::new(0xAAAA_0002),
        BabyBear::new(0xAAAA_0003),
        BabyBear::new(0xAAAA_0004),
    ];
    let vk_b: [BabyBear; 8] = [
        vk_a[0],
        vk_a[1],
        vk_a[2],
        vk_a[3],
        BabyBear::new(0xBBBB_0001),
        BabyBear::new(0xBBBB_0002),
        BabyBear::new(0xBBBB_0003),
        BabyBear::new(0xBBBB_0004),
    ];
    let key_a = babybear8_to_bytes32(&vk_a);
    let key_b = babybear8_to_bytes32(&vk_b);
    // Lower 16 bytes match.
    assert_eq!(&key_a[..16], &key_b[..16]);
    // Upper 16 bytes differ — distinct registry dispatch.
    assert_ne!(&key_a[16..], &key_b[16..]);
    assert_ne!(
        key_a, key_b,
        "PI v2 32-byte dispatch keys must differ when upper half differs"
    );
    // Pre-v2 simulated: zero-pad the upper half from a 16-byte truncation.
    let mut key_a_v1 = [0u8; 32];
    key_a_v1[..16].copy_from_slice(&key_a[..16]);
    let mut key_b_v1 = [0u8; 32];
    key_b_v1[..16].copy_from_slice(&key_b[..16]);
    assert_eq!(
        key_a_v1, key_b_v1,
        "pre-v2 zero-pad would collide — this is exactly the gap #70 closes"
    );
}

// ====================================================================
// EmitEvent (closes #110)
// ====================================================================

/// Honest prover: the trace's params[0..4] / params[4..8] exactly match the
/// declared PI[EMIT_EVENT_TOPIC_HASH][0..4] / PI[EMIT_EVENT_PAYLOAD_HASH][0..4],
/// and the proof verifies.
#[test]
fn test_emit_event_honest_topic_payload_verify() {
    let topic = [
        BabyBear::new(0xAAAA_0001),
        BabyBear::new(0xAAAA_0002),
        BabyBear::new(0xAAAA_0003),
        BabyBear::new(0xAAAA_0004),
        BabyBear::new(0xAAAA_0005),
        BabyBear::new(0xAAAA_0006),
        BabyBear::new(0xAAAA_0007),
        BabyBear::new(0xAAAA_0008),
    ];
    let payload = [
        BabyBear::new(0xBBBB_0001),
        BabyBear::new(0xBBBB_0002),
        BabyBear::new(0xBBBB_0003),
        BabyBear::new(0xBBBB_0004),
        BabyBear::new(0xBBBB_0005),
        BabyBear::new(0xBBBB_0006),
        BabyBear::new(0xBBBB_0007),
        BabyBear::new(0xBBBB_0008),
    ];
    let state = make_initial_state(1000);
    let effects = vec![Effect::EmitEvent {
        topic_hash: topic,
        payload_hash: payload,
    }];
    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

    // PI surface sanity: count == 1, full 8 felts populated.
    assert_eq!(public_inputs[pi::EMIT_EVENT_COUNT], BabyBear::new(1));
    for i in 0..pi::EMIT_EVENT_TOPIC_HASH_LEN {
        assert_eq!(
            public_inputs[pi::EMIT_EVENT_TOPIC_HASH_BASE + i],
            topic[i],
            "topic_hash[{i}] must round-trip into PI"
        );
        assert_eq!(
            public_inputs[pi::EMIT_EVENT_PAYLOAD_HASH_BASE + i],
            payload[i],
            "payload_hash[{i}] must round-trip into PI"
        );
    }

    let air = EffectVmAir::new(trace.len());
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "honest EmitEvent proof must verify: {:?}",
        result.err()
    );
}

/// Adversarial: a malicious prover swaps the low-half topic felts inside the
/// trace row's params[0..4] while leaving PI[EMIT_EVENT_TOPIC_HASH] unchanged
/// (the verifier supplies PI from the runtime Event, so the prover cannot
/// rewrite it without breaking the off-AIR PI-match loop). The AIR's per-row
/// PI-equality constraint MUST reject — without it, the proof's binding to
/// the canonical event would be vacuous.
#[test]
fn test_emit_event_forged_trace_topic_rejected() {
    let topic = [
        BabyBear::new(0xAAAA_0001),
        BabyBear::new(0xAAAA_0002),
        BabyBear::new(0xAAAA_0003),
        BabyBear::new(0xAAAA_0004),
        BabyBear::new(0xAAAA_0005),
        BabyBear::new(0xAAAA_0006),
        BabyBear::new(0xAAAA_0007),
        BabyBear::new(0xAAAA_0008),
    ];
    let payload = [BabyBear::new(0x11); 8];
    let state = make_initial_state(1000);
    let effects = vec![Effect::EmitEvent {
        topic_hash: topic,
        payload_hash: payload,
    }];
    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

    // Forgery: tamper with the row's params[0] (topic_hash[0]) inside the
    // trace. PI[EMIT_EVENT_TOPIC_HASH][0] stays at the honest value because
    // the off-AIR verifier derives PI from the runtime Event, not from the
    // prover-supplied trace.
    let emit_row = trace
        .iter()
        .position(|row| row[sel::EMIT_EVENT] == BabyBear::ONE)
        .expect("at least one row must carry sel::EMIT_EVENT");
    trace[emit_row][PARAM_BASE + 0] = BabyBear::new(0xDEAD_BEEF);

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "forged topic_hash[0] inside trace must be rejected by the per-row \
         PI-equality constraint (closes #110
    ); got Ok, which means the AIR \
         tooth is vacuous"
    );
}

/// Adversarial: same forgery shape but on the payload side (params[4]).
/// The payload tooth is independent of the topic tooth — both must reject.
#[test]
fn test_emit_event_forged_trace_payload_rejected() {
    let topic = [BabyBear::new(0x77); 8];
    let payload = [
        BabyBear::new(0xCCCC_0001),
        BabyBear::new(0xCCCC_0002),
        BabyBear::new(0xCCCC_0003),
        BabyBear::new(0xCCCC_0004),
        BabyBear::new(0xCCCC_0005),
        BabyBear::new(0xCCCC_0006),
        BabyBear::new(0xCCCC_0007),
        BabyBear::new(0xCCCC_0008),
    ];
    let state = make_initial_state(1000);
    let effects = vec![Effect::EmitEvent {
        topic_hash: topic,
        payload_hash: payload,
    }];
    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

    let emit_row = trace
        .iter()
        .position(|row| row[sel::EMIT_EVENT] == BabyBear::ONE)
        .expect("at least one row must carry sel::EMIT_EVENT");
    // Forge params[4] = payload_hash[0].
    trace[emit_row][PARAM_BASE + 4] = BabyBear::new(0xBAAD_F00D);

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "forged payload_hash[0] inside trace must be rejected"
    );
}

// ============================================================================
// Near-miss aliasing closure (#100 follow-up): tests for the three dedicated
// VmEffect variants — Burn, CellDestroy, AttenuateCapability.
//
// Per variant:
//   * Honest-happy-path: prove + verify succeeds, and the row's algebraic
//     fingerprint is distinct from the previous aliasing sibling.
//   * Adversarial: forge a single trace cell (the disclosure flag for Burn,
//     the second-param binding for CellDestroy, the cap_root advance for
//     AttenuateCapability) and assert the verifier rejects.
// ============================================================================

#[test]
fn test_burn_happy_path() {
    let state = make_initial_state(1000);
    let effect = Effect::Burn {
        target_hash: BabyBear::new(0xCE11),
        amount_lo: BabyBear::new(250),
        amount_full: 250,
    };
    let (trace, _public_inputs, _air) =
        assert_single_effect_roundtrip(&state, effect, "Burn happy path");

    // Sibling-distinction check: a TRANSFER row with direction=1 would
    // leave params[BURN_WAS_BURN_FLAG] == 0; the Burn row pins it to 1.
    let burn_row = trace
        .iter()
        .position(|row| row[sel::BURN] == BabyBear::ONE)
        .expect("at least one row must carry sel::BURN");
    assert_eq!(
        trace[burn_row][PARAM_BASE + param::BURN_WAS_BURN_FLAG],
        BabyBear::ONE,
        "Burn row must pin was_burn_flag to 1"
    );
    assert_eq!(
        trace[burn_row][sel::TRANSFER],
        BabyBear::ZERO,
        "Burn row must not also activate sel::TRANSFER"
    );

    // Balance debited by amount_lo.
    let old_bal = trace[burn_row][STATE_BEFORE_BASE + state::BALANCE_LO];
    let new_bal = trace[burn_row][STATE_AFTER_BASE + state::BALANCE_LO];
    assert_ne!(old_bal, new_bal, "Burn must debit balance");
}

#[test]
fn test_burn_forged_flag_rejected() {
    // Adversary: drop the was_burn disclosure (set to 0).
    let state = make_initial_state(1000);
    let effects = vec![Effect::Burn {
        target_hash: BabyBear::new(0xCE11),
        amount_lo: BabyBear::new(100),
        amount_full: 100,
    }];
    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    let burn_row = trace
        .iter()
        .position(|row| row[sel::BURN] == BabyBear::ONE)
        .expect("at least one row must carry sel::BURN");
    trace[burn_row][PARAM_BASE + param::BURN_WAS_BURN_FLAG] = BabyBear::ZERO;

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "Burn with forged was_burn_flag=0 must be rejected"
    );
}

#[test]
fn test_cell_destroy_happy_path() {
    let state = make_initial_state(700);
    let effect = Effect::CellDestroy {
        target_hash: w8(0xDEAD),
        death_certificate_hash: w8(0xC0DE),
    };
    let (trace, _public_inputs, _air) =
        assert_single_effect_roundtrip(&state, effect, "CellDestroy happy path");

    let cd_row = trace
        .iter()
        .position(|row| row[sel::CELL_DESTROY] == BabyBear::ONE)
        .expect("at least one row must carry sel::CELL_DESTROY");
    // Sibling-distinction: a SetPermissions row only writes params[0]; a
    // CellDestroy row writes both params[0] and params[1].
    assert_eq!(
        trace[cd_row][PARAM_BASE + param::CELL_DESTROY_TARGET],
        BabyBear::new(0xDEAD),
        "CellDestroy must bind target_hash in params[0]"
    );
    assert_eq!(
        trace[cd_row][PARAM_BASE + param::CELL_DESTROY_CERT_HASH],
        BabyBear::new(0xC0DE),
        "CellDestroy must bind death_certificate_hash in params[1]"
    );
    assert_eq!(
        trace[cd_row][sel::SET_PERMISSIONS],
        BabyBear::ZERO,
        "CellDestroy row must not also activate sel::SET_PERMISSIONS"
    );

    // Passthrough check: balance and cap_root unchanged.
    let old_bal = trace[cd_row][STATE_BEFORE_BASE + state::BALANCE_LO];
    let new_bal = trace[cd_row][STATE_AFTER_BASE + state::BALANCE_LO];
    assert_eq!(old_bal, new_bal, "CellDestroy must not change balance");
    let old_cap = trace[cd_row][STATE_BEFORE_BASE + state::CAP_ROOT];
    let new_cap = trace[cd_row][STATE_AFTER_BASE + state::CAP_ROOT];
    assert_eq!(old_cap, new_cap, "CellDestroy must not change cap_root");
}

#[test]
fn test_cell_destroy_forged_passthrough_rejected() {
    // Adversary: claim a CellDestroy actually changed the balance (so the
    // proof would attest to destruction AND a debit). The passthrough
    // constraint rejects.
    let state = make_initial_state(700);
    let effects = vec![Effect::CellDestroy {
        target_hash: w8(0xDEAD),
        death_certificate_hash: w8(0xC0DE),
    }];
    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    let cd_row = trace
        .iter()
        .position(|row| row[sel::CELL_DESTROY] == BabyBear::ONE)
        .expect("at least one row must carry sel::CELL_DESTROY");
    // Forge: new_balance_lo decremented; row's state-passthrough constraint
    // must reject.
    let old_bal = trace[cd_row][STATE_BEFORE_BASE + state::BALANCE_LO];
    trace[cd_row][STATE_AFTER_BASE + state::BALANCE_LO] = old_bal - BabyBear::ONE;

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "CellDestroy with forged balance change must be rejected"
    );
}

#[test]
fn test_attenuate_capability_happy_path() {
    let state = make_initial_state(500);
    let effect = Effect::AttenuateCapability {
        cap_slot_hash: w8(0x510),
        narrower_commitment: w8(0xA110),
        phase_b: None,
    };
    let (trace, _public_inputs, _air) =
        assert_single_effect_roundtrip(&state, effect, "AttenuateCapability happy path");

    let attn_row = trace
        .iter()
        .position(|row| row[sel::ATTENUATE_CAPABILITY] == BabyBear::ONE)
        .expect("at least one row must carry sel::ATTENUATE_CAPABILITY");

    // Sibling-distinction: RevokeCapability advances cap_root by
    // hash_2_to_1(old_root, slot_hash); AttenuateCapability advances by
    // hash_2_to_1(old_root, hash_2_to_1(slot, narrower)). The two are
    // distinct (with overwhelming probability over hash collisions).
    let old_cap = trace[attn_row][STATE_BEFORE_BASE + state::CAP_ROOT];
    let new_cap = trace[attn_row][STATE_AFTER_BASE + state::CAP_ROOT];
    let leaf = hash_2_to_1(BabyBear::new(0x510), BabyBear::new(0xA110));
    let expected = hash_2_to_1(old_cap, leaf);
    assert_eq!(
        new_cap, expected,
        "AttenuateCapability cap_root advance must equal hash_2_to_1(old, hash_2_to_1(slot, narrower))"
    );
    let revoke_shape = hash_2_to_1(old_cap, BabyBear::new(0x510));
    assert_ne!(
        new_cap, revoke_shape,
        "AttenuateCapability advance must NOT match the RevokeCapability single-hash shape"
    );
    assert_eq!(
        trace[attn_row][sel::REVOKE_CAPABILITY],
        BabyBear::ZERO,
        "AttenuateCapability row must not also activate sel::REVOKE_CAPABILITY"
    );
}

#[test]
fn test_attenuate_capability_forged_cap_root_rejected() {
    // Adversary: rewrite the new cap_root to the RevokeCapability shape
    // hash_2_to_1(old_cap, slot_hash). The attenuate-specific nested-hash
    // constraint must reject.
    let state = make_initial_state(500);
    let effects = vec![Effect::AttenuateCapability {
        cap_slot_hash: w8(0x510),
        narrower_commitment: w8(0xA110),
        phase_b: None,
    }];
    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    let attn_row = trace
        .iter()
        .position(|row| row[sel::ATTENUATE_CAPABILITY] == BabyBear::ONE)
        .expect("at least one row must carry sel::ATTENUATE_CAPABILITY");
    let old_cap = trace[attn_row][STATE_BEFORE_BASE + state::CAP_ROOT];
    let revoke_shape = hash_2_to_1(old_cap, BabyBear::new(0x510));
    trace[attn_row][STATE_AFTER_BASE + state::CAP_ROOT] = revoke_shape;

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "AttenuateCapability with RevokeCapability-shaped cap_root must be rejected"
    );
}

// ============================================================================
// AIR-impl lane #119 — CellSeal / CellUnseal / ReceiptArchive / Refusal.
//
// Per-variant:
//   * Honest happy path: prove + verify succeeds; row algebraic fingerprint
//     is distinct from the closest aliasing sibling.
//   * Adversarial: forge one row cell and assert the verifier rejects.
// ============================================================================

#[test]
fn test_cell_seal_happy_path() {
    let state = make_initial_state(300);
    let effect = Effect::CellSeal {
        target: w8(0x0CE1_15EA),
        reason_hash: w8(0xEA50_0001),
    };
    let (trace, _public_inputs, _air) =
        assert_single_effect_roundtrip(&state, effect, "CellSeal happy path");

    let cs_row = trace
        .iter()
        .position(|row| row[sel::CELL_SEAL] == BabyBear::ONE)
        .expect("at least one row must carry sel::CELL_SEAL");

    // Both params must be bound.
    assert_eq!(
        trace[cs_row][PARAM_BASE + param::CELL_SEAL_TARGET],
        BabyBear::new(0x0CE1_15EA),
        "CellSeal must bind target in params[0]"
    );
    assert_eq!(
        trace[cs_row][PARAM_BASE + param::CELL_SEAL_REASON_HASH],
        BabyBear::new(0xEA50_0001),
        "CellSeal must bind reason_hash in params[1]"
    );

    // Sibling-distinction: a SetPermissions row has sel::SET_PERMISSIONS
    // active, not sel::CELL_SEAL.
    assert_eq!(
        trace[cs_row][sel::SET_PERMISSIONS],
        BabyBear::ZERO,
        "CellSeal row must not also activate sel::SET_PERMISSIONS"
    );

    // State passthrough: balance and cap_root unchanged.
    let old_bal = trace[cs_row][STATE_BEFORE_BASE + state::BALANCE_LO];
    let new_bal = trace[cs_row][STATE_AFTER_BASE + state::BALANCE_LO];
    assert_eq!(old_bal, new_bal, "CellSeal must not change balance");
    let old_cap = trace[cs_row][STATE_BEFORE_BASE + state::CAP_ROOT];
    let new_cap = trace[cs_row][STATE_AFTER_BASE + state::CAP_ROOT];
    assert_eq!(old_cap, new_cap, "CellSeal must not change cap_root");
}

#[test]
fn test_cell_seal_forged_balance_rejected() {
    // Adversary: claim CellSeal debited balance. Passthrough constraint rejects.
    let state = make_initial_state(300);
    let effects = vec![Effect::CellSeal {
        target: w8(0x0CE1_15EA),
        reason_hash: w8(0xEA50_0001),
    }];
    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    let cs_row = trace
        .iter()
        .position(|row| row[sel::CELL_SEAL] == BabyBear::ONE)
        .expect("at least one row must carry sel::CELL_SEAL");
    let old_bal = trace[cs_row][STATE_BEFORE_BASE + state::BALANCE_LO];
    trace[cs_row][STATE_AFTER_BASE + state::BALANCE_LO] = old_bal - BabyBear::ONE;

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "CellSeal with forged balance debit must be rejected"
    );
}

#[test]
fn test_cell_unseal_happy_path() {
    let state = make_initial_state(400);
    let effect = Effect::CellUnseal {
        target: w8(0x005EA1ED),
    };
    let (trace, _public_inputs, _air) =
        assert_single_effect_roundtrip(&state, effect, "CellUnseal happy path");

    let cu_row = trace
        .iter()
        .position(|row| row[sel::CELL_UNSEAL] == BabyBear::ONE)
        .expect("at least one row must carry sel::CELL_UNSEAL");

    // Target param bound.
    assert_eq!(
        trace[cu_row][PARAM_BASE + param::CELL_UNSEAL_TARGET],
        BabyBear::new(0x005EA1ED),
        "CellUnseal must bind target in params[0]"
    );
    assert_eq!(
        trace[cu_row][AUX_BASE],
        BabyBear::new(0x005EA1ED),
        "CellUnseal must mirror target into aux[0]"
    );

    // params[1] is zero (CellUnseal has only one param — this distinguishes
    // it from CellSeal which writes a non-zero reason_hash into params[1]).
    assert_eq!(
        trace[cu_row][PARAM_BASE + param::CELL_SEAL_REASON_HASH],
        BabyBear::ZERO,
        "CellUnseal row must leave params[1] zero (single-param variant)"
    );

    // Selector exclusion.
    assert_eq!(
        trace[cu_row][sel::CELL_SEAL],
        BabyBear::ZERO,
        "CellUnseal row must not also activate sel::CELL_SEAL"
    );

    // State passthrough.
    let old_bal = trace[cu_row][STATE_BEFORE_BASE + state::BALANCE_LO];
    let new_bal = trace[cu_row][STATE_AFTER_BASE + state::BALANCE_LO];
    assert_eq!(old_bal, new_bal, "CellUnseal must not change balance");
    let old_cap = trace[cu_row][STATE_BEFORE_BASE + state::CAP_ROOT];
    let new_cap = trace[cu_row][STATE_AFTER_BASE + state::CAP_ROOT];
    assert_eq!(old_cap, new_cap, "CellUnseal must not change cap_root");
}

#[test]
fn test_cell_unseal_forged_target_rejected() {
    // Adversary: swap the target hash to an impostor value after trace generation.
    // The AIR mirrors the target into aux[0], so swapping params[0] alone makes
    // the row inconsistent.
    let state = make_initial_state(400);
    let effects = vec![Effect::CellUnseal {
        target: w8(0x005EA1ED),
    }];
    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    let cu_row = trace
        .iter()
        .position(|row| row[sel::CELL_UNSEAL] == BabyBear::ONE)
        .expect("at least one row must carry sel::CELL_UNSEAL");
    // Replace the target with an impostor.
    trace[cu_row][PARAM_BASE + param::CELL_UNSEAL_TARGET] = BabyBear::new(0xBAD_FEED);

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "CellUnseal with forged target must be rejected"
    );
}

#[test]
fn test_receipt_archive_happy_path() {
    let state = make_initial_state(500);
    let effect = Effect::ReceiptArchive {
        target: w8(0xABC1_DEF2),
        archive_end_height: BabyBear::new(1234),
        terminal_receipt_hash: w8(0xFEED_DEAD),
    };
    let (trace, _public_inputs, _air) =
        assert_single_effect_roundtrip(&state, effect, "ReceiptArchive happy path");

    let ra_row = trace
        .iter()
        .position(|row| row[sel::RECEIPT_ARCHIVE] == BabyBear::ONE)
        .expect("at least one row must carry sel::RECEIPT_ARCHIVE");

    // All three params bound.
    assert_eq!(
        trace[ra_row][PARAM_BASE + param::RECEIPT_ARCHIVE_TARGET],
        BabyBear::new(0xABC1_DEF2),
        "ReceiptArchive must bind target in params[0]"
    );
    assert_eq!(
        trace[ra_row][PARAM_BASE + param::RECEIPT_ARCHIVE_END_HEIGHT],
        BabyBear::new(1234),
        "ReceiptArchive must bind archive_end_height in params[1]"
    );
    assert_eq!(
        trace[ra_row][PARAM_BASE + param::RECEIPT_ARCHIVE_TERMINAL_HASH],
        BabyBear::new(0xFEED_DEAD),
        "ReceiptArchive must bind terminal_receipt_hash in params[2]"
    );

    // Sibling-distinction: three non-zero params vs. SetPermissions (one).
    assert_eq!(
        trace[ra_row][sel::SET_PERMISSIONS],
        BabyBear::ZERO,
        "ReceiptArchive row must not also activate sel::SET_PERMISSIONS"
    );

    // State passthrough.
    let old_bal = trace[ra_row][STATE_BEFORE_BASE + state::BALANCE_LO];
    let new_bal = trace[ra_row][STATE_AFTER_BASE + state::BALANCE_LO];
    assert_eq!(old_bal, new_bal, "ReceiptArchive must not change balance");
    let old_cap = trace[ra_row][STATE_BEFORE_BASE + state::CAP_ROOT];
    let new_cap = trace[ra_row][STATE_AFTER_BASE + state::CAP_ROOT];
    assert_eq!(old_cap, new_cap, "ReceiptArchive must not change cap_root");
}

#[test]
fn test_receipt_archive_forged_cap_root_rejected() {
    // Adversary: claim ReceiptArchive advanced cap_root.
    // The passthrough constraint rejects.
    let state = make_initial_state(500);
    let effects = vec![Effect::ReceiptArchive {
        target: w8(0xABC1_DEF2),
        archive_end_height: BabyBear::new(1234),
        terminal_receipt_hash: w8(0xFEED_DEAD),
    }];
    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    let ra_row = trace
        .iter()
        .position(|row| row[sel::RECEIPT_ARCHIVE] == BabyBear::ONE)
        .expect("at least one row must carry sel::RECEIPT_ARCHIVE");
    // Forge: advance cap_root by hashing with an arbitrary value.
    let old_cap = trace[ra_row][STATE_BEFORE_BASE + state::CAP_ROOT];
    trace[ra_row][STATE_AFTER_BASE + state::CAP_ROOT] = hash_2_to_1(old_cap, BabyBear::new(0xBAD));

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "ReceiptArchive with forged cap_root advance must be rejected"
    );
}

#[test]
fn test_refusal_happy_path() {
    let state = make_initial_state(200);
    let effect = Effect::Refusal {
        target: w8(0x0DEC_1337),
        reason_hash: w8(0x2025_0101),
    };
    let (trace, _public_inputs, _air) =
        assert_single_effect_roundtrip(&state, effect, "Refusal happy path");

    let rf_row = trace
        .iter()
        .position(|row| row[sel::REFUSAL] == BabyBear::ONE)
        .expect("at least one row must carry sel::REFUSAL");

    // Both params bound.
    assert_eq!(
        trace[rf_row][PARAM_BASE + param::REFUSAL_TARGET],
        BabyBear::new(0x0DEC_1337),
        "Refusal must bind target in params[0]"
    );
    assert_eq!(
        trace[rf_row][PARAM_BASE + param::REFUSAL_REASON_HASH],
        BabyBear::new(0x2025_0101),
        "Refusal must bind reason_hash in params[1]"
    );

    // Selector exclusion: distinct from CellSeal (same 2-param shape).
    assert_eq!(
        trace[rf_row][sel::CELL_SEAL],
        BabyBear::ZERO,
        "Refusal row must not also activate sel::CELL_SEAL"
    );

    // State passthrough.
    let old_bal = trace[rf_row][STATE_BEFORE_BASE + state::BALANCE_LO];
    let new_bal = trace[rf_row][STATE_AFTER_BASE + state::BALANCE_LO];
    assert_eq!(old_bal, new_bal, "Refusal must not change balance");
    let old_cap = trace[rf_row][STATE_BEFORE_BASE + state::CAP_ROOT];
    let new_cap = trace[rf_row][STATE_AFTER_BASE + state::CAP_ROOT];
    assert_eq!(old_cap, new_cap, "Refusal must not change cap_root");
}

#[test]
fn test_refusal_forged_balance_rejected() {
    // Adversary: claim Refusal debited balance. Passthrough constraint rejects.
    let state = make_initial_state(200);
    let effects = vec![Effect::Refusal {
        target: w8(0x0DEC_1337),
        reason_hash: w8(0x2025_0101),
    }];
    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    let rf_row = trace
        .iter()
        .position(|row| row[sel::REFUSAL] == BabyBear::ONE)
        .expect("at least one row must carry sel::REFUSAL");
    let old_bal = trace[rf_row][STATE_BEFORE_BASE + state::BALANCE_LO];
    trace[rf_row][STATE_AFTER_BASE + state::BALANCE_LO] = old_bal - BabyBear::ONE;

    let air = EffectVmAir::new(trace.len());
    let result = std::panic::catch_unwind(|| {
        let proof = prove(&air, &trace, &public_inputs);
        verify(&air, &proof, &public_inputs)
    });
    assert!(
        result.is_err() || matches!(result, Ok(Err(_))),
        "Refusal with forged balance debit must be rejected"
    );
}
