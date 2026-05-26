//! Preflight: substrate caveat surface sanity checks.
//!
//! Layer: lightweight — these are pre-flight checks that must pass before
//! any heavier substrate test is worth running. Each check exercises a
//! single fact about the cell-side `StateConstraint` evaluator or the
//! γ.2 canonical id preimage shape; failure indicates a regression in
//! `cell/src/program.rs` or the γ.2 design.

use dregg_cell::id::CellId;
use dregg_cell::predicate::WitnessedPredicate;
use dregg_cell::program::{CustomDescriptor, DeltaRelation, ReadSet};
use dregg_cell::{CellProgram, CellState, InputRef, ProgramError, StateConstraint, field_from_u64};

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("field_equals_accepts_match", check_field_equals_positive),
        run_check("field_equals_rejects_mismatch", check_field_equals_negative),
        run_check("monotonic_rejects_decrease", check_monotonic_decrease),
        run_check("immutable_rejects_change", check_immutable_change),
        run_check(
            "temporal_predicate_returns_sentinel",
            check_temporal_predicate_sentinel,
        ),
        run_check("witnessed_returns_sentinel", check_witnessed_sentinel),
        run_check("custom_returns_sentinel", check_custom_sentinel),
        run_check("bound_delta_returns_sentinel", check_bound_delta_sentinel),
        run_check(
            "gamma2_transfer_id_preimage_injective_in_amount",
            check_gamma2_transfer_id_preimage_injective_in_amount,
        ),
        run_check(
            "gamma2_intro_id_preimage_includes_permissions_bits",
            check_gamma2_intro_id_includes_permissions_bits,
        ),
    ]
}

fn state_with(field_values: &[(usize, u64)]) -> CellState {
    let mut s = CellState::default();
    for (idx, val) in field_values {
        s.fields[*idx] = field_from_u64(*val);
    }
    s
}

fn check_field_equals_positive() -> Result<(), String> {
    let p = CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: 0,
        value: field_from_u64(42),
    }]);
    let state = state_with(&[(0, 42)]);
    p.evaluate(&state, None, None).map_err(|e| format!("{e:?}"))
}

fn check_field_equals_negative() -> Result<(), String> {
    let p = CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: 0,
        value: field_from_u64(42),
    }]);
    let state = state_with(&[(0, 43)]);
    match p.evaluate(&state, None, None) {
        Err(ProgramError::ConstraintViolated { .. }) => Ok(()),
        other => Err(format!("expected ConstraintViolated, got {other:?}")),
    }
}

fn check_monotonic_decrease() -> Result<(), String> {
    let p = CellProgram::Predicate(vec![StateConstraint::Monotonic { index: 0 }]);
    let old = state_with(&[(0, 5)]);
    let new = state_with(&[(0, 4)]);
    match p.evaluate(&new, Some(&old), None) {
        Err(_) => Ok(()),
        Ok(_) => Err("Monotonic must reject decrease".into()),
    }
}

fn check_immutable_change() -> Result<(), String> {
    let p = CellProgram::Predicate(vec![StateConstraint::Immutable { index: 1 }]);
    let old = state_with(&[(1, 5)]);
    let new = state_with(&[(1, 6)]);
    match p.evaluate(&new, Some(&old), None) {
        Err(_) => Ok(()),
        Ok(_) => Err("Immutable must reject change".into()),
    }
}

fn check_temporal_predicate_sentinel() -> Result<(), String> {
    let p = CellProgram::Predicate(vec![StateConstraint::TemporalPredicate {
        witness_index: 0,
        dsl_hash: [0u8; 32],
    }]);
    match p.evaluate(&CellState::default(), None, None) {
        Err(ProgramError::TemporalPredicateWitnessMissing { .. }) => Ok(()),
        other => Err(format!(
            "expected TemporalPredicateWitnessMissing, got {other:?}"
        )),
    }
}

fn check_witnessed_sentinel() -> Result<(), String> {
    let p = CellProgram::Predicate(vec![StateConstraint::Witnessed {
        wp: WitnessedPredicate::dfa([0u8; 32], InputRef::Sender, 0),
    }]);
    match p.evaluate(&CellState::default(), None, None) {
        Err(ProgramError::WitnessedPredicateRequiresExecutor { .. }) => Ok(()),
        other => Err(format!(
            "expected WitnessedPredicateRequiresExecutor, got {other:?}"
        )),
    }
}

fn check_custom_sentinel() -> Result<(), String> {
    let p = CellProgram::Predicate(vec![StateConstraint::Custom {
        ir_hash: [0u8; 32],
        descriptor: CustomDescriptor::default(),
        reads: ReadSet::default(),
    }]);
    match p.evaluate(&CellState::default(), None, None) {
        Err(ProgramError::CustomConstraintUnevaluable { .. }) => Ok(()),
        other => Err(format!(
            "expected CustomConstraintUnevaluable, got {other:?}"
        )),
    }
}

fn check_bound_delta_sentinel() -> Result<(), String> {
    let p = CellProgram::Predicate(vec![StateConstraint::BoundDelta {
        local_slot: 0,
        peer_cell: CellId([0u8; 32]),
        peer_slot: 0,
        delta_relation: DeltaRelation::EqualAndOpposite,
    }]);
    match p.evaluate(&CellState::default(), None, None) {
        Err(ProgramError::BoundDeltaNotWired { .. }) => Ok(()),
        other => Err(format!("expected BoundDeltaNotWired, got {other:?}")),
    }
}

// γ.2 canonical id preimage sanity (pure function — should be stable
// across substrate revisions; if it changes, the design doc and tests
// must change in lockstep).

fn transfer_pre(from: &CellId, to: &CellId, amount: u64, sender_nonce: u64) -> Vec<u8> {
    let mut v = Vec::with_capacity(128);
    v.extend_from_slice(b"dregg-transfer-id-v1");
    v.extend_from_slice(&from.0);
    v.extend_from_slice(&to.0);
    v.extend_from_slice(&amount.to_be_bytes());
    v.extend_from_slice(&sender_nonce.to_be_bytes());
    v
}

fn intro_pre(
    introducer: &CellId,
    recipient: &CellId,
    target: &CellId,
    perms: u32,
    nonce: u64,
) -> Vec<u8> {
    let mut v = Vec::with_capacity(160);
    v.extend_from_slice(b"dregg-intro-id-v1");
    v.extend_from_slice(&introducer.0);
    v.extend_from_slice(&recipient.0);
    v.extend_from_slice(&target.0);
    v.extend_from_slice(&perms.to_be_bytes());
    v.extend_from_slice(&nonce.to_be_bytes());
    v
}

fn check_gamma2_transfer_id_preimage_injective_in_amount() -> Result<(), String> {
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    let pre_10 = transfer_pre(&a, &b, 10, 0);
    let pre_11 = transfer_pre(&a, &b, 11, 0);
    if pre_10 == pre_11 {
        Err("γ.2 transfer_id preimage must change with amount".into())
    } else {
        Ok(())
    }
}

fn check_gamma2_intro_id_includes_permissions_bits() -> Result<(), String> {
    let i = CellId([1u8; 32]);
    let r = CellId([2u8; 32]);
    let t = CellId([3u8; 32]);
    let pre_0 = intro_pre(&i, &r, &t, 0, 0);
    let pre_1 = intro_pre(&i, &r, &t, 1, 0);
    if pre_0 == pre_1 {
        Err("γ.2 intro_id preimage must change with permissions_bits".into())
    } else {
        Ok(())
    }
}
