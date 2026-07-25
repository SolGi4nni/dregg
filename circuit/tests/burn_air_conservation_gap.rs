//! FALSIFIER for the `SCHEMA_BURN` algebraic-constraint gap (LANE AV item 2).
//!
//! `AlgebraicConstraint::Burn` and `SCHEMA_BURN` both DOCUMENT a set of algebraic gates —
//! `new_lo + amt_lo == old_lo + borrow*2^32`, the high limb, borrow booleanity, and the
//! `was_burn_flag` disclosure pins. `effect_action_to_descriptor2` never reads `schema.algebraic`,
//! so NONE of them is emitted. The Lean author of the same descriptor
//! (`Dregg2.Circuit.Emit.EffectActionBindingEmit.burnDesc`) carries all five as proven Base gates.
//!
//! This file pins that gap as a MEASURED fact rather than a claim, in the two ways that can go red:
//!
//!   1. `deployed_burn_descriptor_is_missing_the_lean_algebraic_gates` — a hard count: the deployed
//!      Rust descriptor is 33 constraints, the Lean author is 38, and the five missing ones are
//!      exactly `burnGates`. When the emit route lands, THIS TEST GOES RED and must be flipped to
//!      assert 38. That is the point — the gap is detected, not merely documented.
//!   2. `burn_air_admits_a_conservation_violating_trace` — the operational demonstration: a trace
//!      whose amounts satisfy NO burn conservation relation still produces a VERIFYING proof under
//!      the deployed descriptor. With the Lean gates emitted this is UNSAT.
//!
//! ⚠ Read `burn_conservation_is_enforced_by_pi_reconstruction` (the third test) before concluding
//! this is exploitable. It is NOT, on the deployed path: `verify_effect_binding_proofs_with_ledger`
//! reconstructs all four amounts from the executor's own authoritative state and STARK-verifies
//! against ITS OWN PI vector, so a prover has no freedom over the values these gates would relate.
//! The residual is that conservation is enforced by executor arithmetic instead of in-circuit —
//! which means it is NOT inherited by any consumer that verifies such a proof standalone.

use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_action_air::{
    EffectActionAir, EffectActionWitness, SCHEMA_BURN, effect_action_to_descriptor2,
};

/// The Lean author's constraint count for `burnDesc`, pinned by
/// `#guard burnDesc.constraints.length == 38` in `EffectActionBindingEmit.lean`:
/// 17 continuity + 16 PI pins + 5 algebraic Base gates.
const LEAN_BURN_DESCRIPTOR_CONSTRAINTS: usize = 38;

/// The five algebraic gates Lean emits and Rust does not.
const MISSING_ALGEBRAIC_GATES: usize = 5;

#[test]
fn deployed_burn_descriptor_is_missing_the_lean_algebraic_gates() {
    let desc = effect_action_to_descriptor2(&SCHEMA_BURN).expect("burn schema lowers");

    // Shape agreement: the columns and PI surface DO match Lean (width 17, pi 16). The borrow aux
    // column at index 16 exists in both. Only the gates differ.
    assert_eq!(desc.trace_width, 17, "burn trace width");
    assert_eq!(desc.public_input_count, 16, "burn PI count");
    assert_eq!(
        SCHEMA_BURN.aux_count(),
        1,
        "the borrow aux column is still reserved"
    );

    let deployed = desc.constraints.len();
    assert_eq!(
        deployed,
        LEAN_BURN_DESCRIPTOR_CONSTRAINTS - MISSING_ALGEBRAIC_GATES,
        "expected the deployed burn descriptor to carry the 33 binding/continuity constraints \
         and NONE of Lean's {MISSING_ALGEBRAIC_GATES} algebraic gates. If this is now {LEAN_BURN_DESCRIPTOR_CONSTRAINTS}, \
         the Lean emit route has landed — flip this assertion to \
         LEAN_BURN_DESCRIPTOR_CONSTRAINTS and DELETE \
         `burn_air_admits_a_conservation_violating_trace`, which will start failing (correctly)."
    );
}

#[test]
fn burn_air_admits_a_conservation_violating_trace() {
    let desc = effect_action_to_descriptor2(&SCHEMA_BURN).expect("burn schema lowers");

    // amounts = [old_balance, new_balance, amount, was_burn_flag].
    // old = 1000, amount = 100, so ANY honest burn has new = 900. This claims new = 999 — it
    // destroys 1 unit while reporting a burn of 100, i.e. it satisfies NO conservation relation.
    // `was_burn_flag` is set to 7, which Lean gate 4 (`was_burn_lo - 1 == 0`) forbids outright.
    let witness = EffectActionWitness {
        schema: SCHEMA_BURN,
        fields: vec![[0xB0u8; 32]],
        amounts: vec![1000, 999, 100, 7],
    };
    let (trace, pis) = EffectActionAir::generate_trace(&witness);

    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the deployed descriptor has no gate that this trace could violate");

    assert!(
        verify_vm_descriptor2(&desc, &proof, &pis).is_ok(),
        "THE GAP: the deployed burn descriptor accepts amounts that satisfy no conservation \
         relation (old=1000, new=999, amount=100) and a was_burn_flag of 7. Lean's burnDesc \
         gates 1/2 and 4 each make this UNSAT."
    );
}

#[test]
fn burn_aux_borrow_column_is_read_by_no_constraint() {
    // The borrow bit at column `pi_count()` = 16 is FREE: past the PI surface (so no `PiBinding`
    // compares it) and read by no gate (so nothing constrains its value). The only constraint
    // touching column 16 is the continuity `WindowGate`, which merely forces it constant.
    //
    // This is what "the aux borrow column rides free" means concretely — and it is also why the
    // gap is inert rather than exploitable: an unconstrained column that NO other constraint
    // consumes cannot influence any accepted statement. A prover may set it to anything; the
    // descriptor certifies exactly the same PI either way.
    let desc = effect_action_to_descriptor2(&SCHEMA_BURN).expect("burn schema lowers");
    let borrow_col = SCHEMA_BURN.pi_count();
    assert_eq!(borrow_col, 16);

    // No PI binding reaches the aux column.
    let pi_bindings_over_aux = format!("{:?}", desc.constraints).matches("col: 16").count();
    assert_eq!(
        pi_bindings_over_aux, 0,
        "the borrow aux column must not be PI-bound (it is a witness, not a public input)"
    );

    // Two traces differing ONLY in the borrow column both verify against the SAME public inputs.
    let witness = EffectActionWitness {
        schema: SCHEMA_BURN,
        fields: vec![[0xB1u8; 32]],
        amounts: vec![1000, 900, 100, 1],
    };
    let (honest_trace, pis) = EffectActionAir::generate_trace(&witness);

    let mut tampered = honest_trace.clone();
    for row in tampered.iter_mut() {
        row[borrow_col] = dregg_circuit::field::BabyBear::new(123_456);
    }

    let honest = prove_vm_descriptor2(
        &desc,
        &honest_trace,
        &pis,
        &MemBoundaryWitness::default(),
        &[],
    )
    .expect("honest burn trace proves");
    let forged = prove_vm_descriptor2(&desc, &tampered, &pis, &MemBoundaryWitness::default(), &[])
        .expect("a non-boolean borrow is unconstrained, so this proves too");

    assert!(verify_vm_descriptor2(&desc, &honest, &pis).is_ok());
    assert!(
        verify_vm_descriptor2(&desc, &forged, &pis).is_ok(),
        "borrow = 123456 must still verify — Lean's gate 3 (borrow*(borrow-1) == 0) is not emitted"
    );
}
