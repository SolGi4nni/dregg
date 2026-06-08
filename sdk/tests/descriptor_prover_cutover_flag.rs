//! Integration test for the EFFECT-VM CUTOVER FLAG (`DREGG_DESCRIPTOR_PROVER=1`) at the
//! real production prove path `sdk::full_turn_proof::prove_turn_self_sovereign`.
//!
//! Runs in its OWN test binary (separate process), so toggling the process-global flag
//! cannot race the lib unit tests.
//!
//! With the flag set, a single-Transfer self-sovereign turn is proven through the
//! verified-by-construction Lean DESCRIPTOR INTERPRETER (`EffectVmDescriptorAir`, fed the
//! registry's transfer descriptor) instead of the hand-written `EffectVmP3Air`, and STILL
//! verifies end-to-end through the flag-aware verifier (`verify_full_turn` → the
//! descriptor verify arm). This is the real cutover swap, exercised end-to-end. The
//! equivalence to the hand-AIR is guarded by the circuit-level differential harness
//! (`circuit/tests/effect_vm_descriptor_cutover_harness.rs`).

use dregg_circuit::effect_vm::{CellState, Effect as VmEffect};
use dregg_circuit::field::BabyBear;
use dregg_sdk::full_turn_proof::{prove_turn_self_sovereign, verify_full_turn};

/// The flagged production swap: a transfer turn, proven+verified through the descriptor
/// interpreter, end-to-end.
#[test]
fn cutover_flag_routes_transfer_through_descriptor_and_still_verifies() {
    let initial = CellState::new(1000, 0);
    let effects = vec![VmEffect::Transfer { amount: 100, direction: 1 }];
    let turn_hash = [0xABu8; 32];

    // SAFETY: own-process test binary; no other thread reads/writes this env var.
    unsafe {
        std::env::set_var("DREGG_DESCRIPTOR_PROVER", "1");
    }

    let proof = prove_turn_self_sovereign(&initial, &effects, turn_hash)
        .expect("descriptor-prover transfer proof should generate");
    assert!(proof.components.has_state_transition);

    let old_commit = initial.state_commitment;
    let mut expected_final = initial.clone();
    expected_final.balance = 900;
    expected_final.nonce = 1;
    expected_final.refresh_commitment();
    let new_commit = expected_final.state_commitment;

    // The flag stays SET across verify: a descriptor proof binds a different AIR than the
    // hand-AIR, so the verifier must take the descriptor arm.
    let verify_result = verify_full_turn(&proof, old_commit, new_commit);

    // SAFETY: own-process test binary.
    unsafe {
        std::env::remove_var("DREGG_DESCRIPTOR_PROVER");
    }

    verify_result.expect("descriptor-prover transfer proof must verify through the descriptor arm");
}

/// The flagged production swap, GRADUATED ECONOMIC effect: a single `Burn` turn, proven +
/// verified through the descriptor interpreter end-to-end. Exercises the widened
/// `cutover_ready_selector` (Burn = selector 46) and the widened verify arm.
#[test]
fn cutover_flag_routes_burn_through_descriptor_and_still_verifies() {
    let initial = CellState::new(1000, 0);
    let effects = vec![VmEffect::Burn {
        target_hash: BabyBear::new(0xB0B),
        amount_lo: BabyBear::new(100),
        amount_full: 100,
    }];
    let turn_hash = [0xCDu8; 32];

    // SAFETY: own-process test binary; no other thread reads/writes this env var.
    unsafe {
        std::env::set_var("DREGG_DESCRIPTOR_PROVER", "1");
    }

    let proof = prove_turn_self_sovereign(&initial, &effects, turn_hash)
        .expect("descriptor-prover burn proof should generate");
    assert!(proof.components.has_state_transition);

    let old_commit = initial.state_commitment;
    let mut expected_final = initial.clone();
    expected_final.balance = 900; // burn debits 100
    expected_final.nonce = 1; // non-NoOp row ticks the nonce
    expected_final.refresh_commitment();
    let new_commit = expected_final.state_commitment;

    let verify_result = verify_full_turn(&proof, old_commit, new_commit);

    // SAFETY: own-process test binary.
    unsafe {
        std::env::remove_var("DREGG_DESCRIPTOR_PROVER");
    }

    verify_result.expect("descriptor-prover burn proof must verify through the descriptor arm");
}

/// Control: with the flag UNSET (default), the SAME transfer turn proves through the
/// hand-AIR and verifies through the hand-AIR arm — the default production path is
/// unchanged.
#[test]
fn default_path_uses_hand_air_and_still_verifies() {
    // Ensure the flag is not set in this process.
    // SAFETY: own-process test binary.
    unsafe {
        std::env::remove_var("DREGG_DESCRIPTOR_PROVER");
    }

    let initial = CellState::new(1000, 0);
    let effects = vec![VmEffect::Transfer { amount: 100, direction: 1 }];
    let turn_hash = [0xABu8; 32];

    let proof = prove_turn_self_sovereign(&initial, &effects, turn_hash)
        .expect("hand-AIR transfer proof should generate");

    let old_commit = initial.state_commitment;
    let mut expected_final = initial.clone();
    expected_final.balance = 900;
    expected_final.nonce = 1;
    expected_final.refresh_commitment();
    let new_commit = expected_final.state_commitment;

    verify_full_turn(&proof, old_commit, new_commit)
        .expect("hand-AIR transfer proof must verify (default path)");
}
