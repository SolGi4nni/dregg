//! Integration test for the EFFECT-VM DESCRIPTOR CUTOVER at the real production prove
//! path `sdk::full_turn_proof::prove_turn_self_sovereign`.
//!
//! THE DEFAULT IS THE DESCRIPTOR PROVER: with no env var set, every graduated turn shape
//! is proven through the verified-by-construction Lean DESCRIPTOR INTERPRETER
//! (`EffectVmDescriptorAir`, fed the registry's Lean-emitted JSON) instead of the
//! hand-written `EffectVmP3Air`. `DREGG_DESCRIPTOR_PROVER=0` is the opt-OUT that forces
//! the legacy hand-AIR for comparison. VERIFICATION IS SHAPE-DRIVEN AND ENV-INDEPENDENT:
//! `verify_full_turn` accepts proofs from either engine regardless of the flag — a peer
//! must never reject a sound proof because of its own environment.
//!
//! Runs in its OWN test binary (separate process), so toggling the process-global flag
//! cannot race the lib unit tests. The descriptor ⟺ hand-AIR equivalence itself is
//! guarded by the circuit-level differential harness
//! (`circuit/tests/effect_vm_descriptor_cutover_harness.rs`).

use dregg_circuit::effect_vm::{CellState, Effect as VmEffect};
use dregg_circuit::field::BabyBear;
use dregg_sdk::full_turn_proof::{prove_turn_self_sovereign, verify_full_turn};
use std::sync::Mutex;

/// Process-global lock that SERIALIZES the env-var-mutating tests in this binary.
/// `DREGG_DESCRIPTOR_PROVER` is process-global; each test holds this guard for its whole
/// set→prove→verify→remove window, so the flag is stable per test. Poison is irrelevant
/// (each test sets the flag state it needs on entry).
static FLAG_LOCK: Mutex<()> = Mutex::new(());

fn expected_after_transfer_out(initial: &CellState, amount: u64) -> (BabyBear, BabyBear) {
    let old_commit = initial.state_commitment;
    let mut expected_final = initial.clone();
    expected_final.balance -= amount;
    expected_final.nonce += 1;
    expected_final.refresh_commitment();
    (old_commit, expected_final.state_commitment)
}

/// THE NEW DEFAULT: with NO env var set, a single-Transfer self-sovereign turn routes
/// through the descriptor prover and verifies end-to-end.
#[test]
fn default_routes_transfer_through_descriptor_and_verifies() {
    let _g = FLAG_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    // SAFETY: own-process test binary; serialized by FLAG_LOCK.
    unsafe {
        std::env::remove_var("DREGG_DESCRIPTOR_PROVER");
    }

    let initial = CellState::new(1000, 0);
    let effects = vec![VmEffect::Transfer {
        amount: 100,
        direction: 1,
    }];
    let proof = prove_turn_self_sovereign(&initial, &effects, [0xABu8; 32])
        .expect("default (descriptor-prover) transfer proof should generate");
    assert!(proof.components.has_state_transition);

    let (old_commit, new_commit) = expected_after_transfer_out(&initial, 100);
    verify_full_turn(&proof, old_commit, new_commit)
        .expect("default descriptor-prover transfer proof must verify");
}

/// The default, GRADUATED ECONOMIC effect: a single `Burn` turn through the descriptor
/// prover end-to-end (exercises `cutover_route` beyond the transfer beachhead).
#[test]
fn default_routes_burn_through_descriptor_and_verifies() {
    let _g = FLAG_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    // SAFETY: own-process test binary; serialized by FLAG_LOCK.
    unsafe {
        std::env::remove_var("DREGG_DESCRIPTOR_PROVER");
    }

    let initial = CellState::new(1000, 0);
    let effects = vec![VmEffect::Burn {
        target_hash: BabyBear::new(0xB0B),
        amount_lo: BabyBear::new(100),
        amount_full: 100,
    }];
    let proof = prove_turn_self_sovereign(&initial, &effects, [0xCDu8; 32])
        .expect("default (descriptor-prover) burn proof should generate");
    assert!(proof.components.has_state_transition);

    let (old_commit, new_commit) = expected_after_transfer_out(&initial, 100); // burn debits 100
    verify_full_turn(&proof, old_commit, new_commit)
        .expect("default descriptor-prover burn proof must verify");
}

/// MULTI-EFFECT ROUTING: a HOMOGENEOUS two-Transfer turn (all effects the same
/// multi-effect-ready selector) routes through the single transfer descriptor over the
/// multi-row trace and verifies end-to-end — the cutover covers multi-effect turns.
#[test]
fn default_routes_homogeneous_multi_effect_turn_through_descriptor() {
    let _g = FLAG_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    // SAFETY: own-process test binary; serialized by FLAG_LOCK.
    unsafe {
        std::env::remove_var("DREGG_DESCRIPTOR_PROVER");
    }

    let initial = CellState::new(1000, 0);
    let effects = vec![
        VmEffect::Transfer {
            amount: 100,
            direction: 1,
        },
        VmEffect::Transfer {
            amount: 50,
            direction: 1,
        },
    ];
    let proof = prove_turn_self_sovereign(&initial, &effects, [0xD0u8; 32])
        .expect("homogeneous multi-effect descriptor proof should generate");

    let old_commit = initial.state_commitment;
    let mut expected_final = initial.clone();
    expected_final.balance = 850; // 1000 - 100 - 50
    expected_final.nonce = 2; // both non-NoOp rows tick
    expected_final.refresh_commitment();
    verify_full_turn(&proof, old_commit, expected_final.state_commitment)
        .expect("homogeneous multi-effect descriptor proof must verify");
}

/// THE NAMED HETEROGENEOUS FALLBACK: a mixed transfer+burn turn (both selectors
/// graduated, but different) falls back to the hand-AIR (the
/// `CutoverFallback::HeterogeneousSelectors` condition — no Lean-emitted conjunction
/// descriptor for selector sets) and STILL proves + verifies end-to-end. The fallback is
/// automatic and the proof remains sound.
#[test]
fn heterogeneous_turn_falls_back_to_hand_air_and_verifies() {
    let _g = FLAG_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    // SAFETY: own-process test binary; serialized by FLAG_LOCK.
    unsafe {
        std::env::remove_var("DREGG_DESCRIPTOR_PROVER");
    }

    let initial = CellState::new(1000, 0);
    let effects = vec![
        VmEffect::Transfer {
            amount: 100,
            direction: 1,
        },
        VmEffect::Burn {
            target_hash: BabyBear::new(0xB0B),
            amount_lo: BabyBear::new(50),
            amount_full: 50,
        },
    ];
    let proof = prove_turn_self_sovereign(&initial, &effects, [0xD1u8; 32])
        .expect("heterogeneous turn must prove via the automatic hand-AIR fallback");

    let old_commit = initial.state_commitment;
    let mut expected_final = initial.clone();
    expected_final.balance = 850; // 1000 - 100 - 50
    expected_final.nonce = 2;
    expected_final.refresh_commitment();
    verify_full_turn(&proof, old_commit, expected_final.state_commitment)
        .expect("heterogeneous hand-AIR-fallback proof must verify");
}

/// THE OPT-OUT: `DREGG_DESCRIPTOR_PROVER=0` forces the legacy hand-AIR prover for the
/// SAME transfer turn — and the proof still verifies (the comparison path stays alive).
#[test]
fn opt_out_zero_uses_hand_air_and_still_verifies() {
    let _g = FLAG_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    // SAFETY: own-process test binary; serialized by FLAG_LOCK.
    unsafe {
        std::env::set_var("DREGG_DESCRIPTOR_PROVER", "0");
    }

    let initial = CellState::new(1000, 0);
    let effects = vec![VmEffect::Transfer {
        amount: 100,
        direction: 1,
    }];
    let proof = prove_turn_self_sovereign(&initial, &effects, [0xABu8; 32]);

    // SAFETY: own-process test binary.
    unsafe {
        std::env::remove_var("DREGG_DESCRIPTOR_PROVER");
    }

    let proof = proof.expect("opt-out hand-AIR transfer proof should generate");
    let (old_commit, new_commit) = expected_after_transfer_out(&initial, 100);
    verify_full_turn(&proof, old_commit, new_commit)
        .expect("opt-out hand-AIR transfer proof must verify");
}

/// PEER-VERIFY DECOUPLING (the cutover's interop tooth): a proof produced under the
/// DEFAULT (descriptor prover) must verify even when the VERIFIER's environment has the
/// flag forced OFF — and a hand-AIR proof (produced under the opt-out) must verify with
/// no flag set. Verification is shape-driven; `DREGG_DESCRIPTOR_PROVER` only ever picks
/// the prover.
#[test]
fn verification_is_env_independent_both_directions() {
    let _g = FLAG_LOCK.lock().unwrap_or_else(|p| p.into_inner());

    let initial = CellState::new(1000, 0);
    let effects = vec![VmEffect::Transfer {
        amount: 100,
        direction: 1,
    }];
    let (old_commit, new_commit) = expected_after_transfer_out(&initial, 100);

    // Direction 1: prove with the DEFAULT (descriptor prover) …
    // SAFETY: own-process test binary; serialized by FLAG_LOCK.
    unsafe {
        std::env::remove_var("DREGG_DESCRIPTOR_PROVER");
    }
    let descriptor_proof = prove_turn_self_sovereign(&initial, &effects, [0xE1u8; 32])
        .expect("descriptor proof generates");
    // … then VERIFY with the flag forced OFF (a hand-AIR-preferring peer).
    // SAFETY: own-process test binary.
    unsafe {
        std::env::set_var("DREGG_DESCRIPTOR_PROVER", "0");
    }
    let r1 = verify_full_turn(&descriptor_proof, old_commit, new_commit);

    // Direction 2: prove with the opt-out (hand-AIR) …
    let hand_air_proof = prove_turn_self_sovereign(&initial, &effects, [0xE2u8; 32])
        .expect("hand-AIR proof generates");
    // … then VERIFY with no flag set (a default-environment peer).
    // SAFETY: own-process test binary.
    unsafe {
        std::env::remove_var("DREGG_DESCRIPTOR_PROVER");
    }
    let r2 = verify_full_turn(&hand_air_proof, old_commit, new_commit);

    r1.expect(
        "a DESCRIPTOR proof must verify on a peer whose env opts the PROVER out — \
         verification must be shape-driven, not env-driven",
    );
    r2.expect(
        "a HAND-AIR proof must verify on a default-environment peer — the fallback \
         engine's proofs stay accepted",
    );
}

/// NON-GRADUATED SHAPE: a turn whose effect has no graduated descriptor (SetField,
/// selector 2 — no Lean emit module) falls back to the hand-AIR under the default and
/// still proves + verifies. The automatic fallback keeps every survivor verb provable.
#[test]
fn non_graduated_effect_falls_back_and_verifies() {
    let _g = FLAG_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    // SAFETY: own-process test binary; serialized by FLAG_LOCK.
    unsafe {
        std::env::remove_var("DREGG_DESCRIPTOR_PROVER");
    }

    let initial = CellState::new(1000, 0);
    let effects = vec![VmEffect::SetField {
        field_idx: 0,
        value: BabyBear::new(0x42),
    }];
    let proof = prove_turn_self_sovereign(&initial, &effects, [0xF1u8; 32])
        .expect("non-graduated SetField turn must prove via the hand-AIR fallback");

    let eff = proof
        .composed
        .sub_proofs
        .iter()
        .find(|sp| sp.label == "effect-vm")
        .expect("effect-vm sub-proof present");
    let old_commit = initial.state_commitment;
    let new_commit = eff.sub_public_inputs[dregg_circuit::effect_vm::pi::NEW_COMMIT];
    verify_full_turn(&proof, old_commit, new_commit)
        .expect("hand-AIR fallback proof for a non-graduated effect must verify");
}
