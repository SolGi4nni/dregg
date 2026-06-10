//! Integration tests: Effect VM prove-then-verify, covering every major schema.
//!
//! Each test builds a real witness, generates a STARK proof, and runs the
//! verifier end-to-end.  Assertions check *what* the proof attests (balance
//! delta, commitment chain, public inputs) — not just that `verify` returned
//! `Ok`.
//!
//! These are integration tests, not unit tests: the full `stark::prove` /
//! `stark::verify` pipeline runs every time.

mod common;

use dregg_circuit::{
    BabyBear, CellState, Effect, EffectVmAir,
    effect_vm::{
        EffectVmContext,
        columns::{STATE_AFTER_BASE, STATE_BEFORE_BASE, state},
        extract_net_delta, generate_effect_vm_trace, generate_effect_vm_trace_ext, pi,
    },
    poseidon2::hash_2_to_1,
    stark::{self, StarkAir, proof_from_bytes, proof_to_bytes},
};

/// 8-limb widened-hash test value: low limb carries `x`, high limbs zero.
/// Mirrors the `bytes32_to_8_limbs` shape used by the projectors for the
/// 32-byte-widened hash params (effect-vm-hash-widen lane).
fn w8(x: u32) -> [BabyBear; 8] {
    let mut a = [BabyBear::ZERO; 8];
    a[0] = BabyBear::new(x);
    a
}

// ─────────────────────────────────────────────────────────────────────────────
// 1. All-schemas smoke: every distinct effect variant verifies solo.
// ─────────────────────────────────────────────────────────────────────────────

/// For every Effect variant that the trace-generator handles without
/// external context, prove-then-verify individually.
///
/// This is the broadest coverage sweep: if trace generation or the AIR
/// breaks for a variant, this test catches it.
#[test]
fn all_schema_variants_prove_and_verify() {
    let balance = 100_000u64;

    let cases: &[(&str, Effect)] = &[
        ("NoOp", Effect::NoOp),
        (
            "Transfer out",
            Effect::Transfer {
                amount: 50,
                direction: 1,
            },
        ),
        (
            "Transfer in",
            Effect::Transfer {
                amount: 50,
                direction: 0,
            },
        ),
        (
            "SetField",
            Effect::SetField {
                field_idx: 2,
                value: BabyBear::new(0x42),
            },
        ),
        (
            "GrantCapability",
            Effect::GrantCapability {
                cap_entry: w8(0xCAFE),
                phase_b: None,
            },
        ),
        (
            "RevokeCapability",
            Effect::RevokeCapability {
                slot_hash: w8(0xDEAD),
            },
        ),
        (
            "EmitEvent",
            Effect::EmitEvent {
                topic_hash: [
                    BabyBear::new(0xEEEE),
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                ],
                payload_hash: [BabyBear::ZERO; 8],
            },
        ),
        (
            "SetPermissions",
            Effect::SetPermissions {
                permissions_hash: w8(0xAAAA),
            },
        ),
        (
            "SetVerificationKey",
            Effect::SetVerificationKey {
                vk_hash: w8(0xBBBB),
            },
        ),
        ("RefreshDelegation", Effect::RefreshDelegation),
        (
            "RevokeDelegation",
            Effect::RevokeDelegation {
                child_hash: w8(0xDDDD),
            },
        ),
        (
            "CreateCell",
            Effect::CreateCell {
                create_hash: w8(0x1111),
            },
        ),
        (
            "SpawnWithDelegation",
            Effect::SpawnWithDelegation {
                spawn_hash: w8(0x2222),
            },
        ),
        (
            "ExerciseViaCapability",
            Effect::ExerciseViaCapability {
                exercise_hash: w8(0x4444),
            },
        ),
        (
            "Introduce",
            Effect::Introduce {
                intro_hash: w8(0x5555),
            },
        ),
        (
            "PipelinedSend",
            Effect::PipelinedSend {
                send_hash: w8(0x6666),
            },
        ),
        (
            "NoteSpend",
            Effect::NoteSpend {
                nullifier: BabyBear::new(0x1234),
                value: 100,
            },
        ),
        (
            "NoteCreate",
            Effect::NoteCreate {
                commitment: BabyBear::new(0x5678),
                value: 50,
            },
        ),
        (
            "BridgeMint",
            Effect::BridgeMint {
                value_lo: BabyBear::new(200),
                mint_hash: BabyBear::new(0xF4),
                value_full: 200,
            },
        ),
    ];

    for (label, effect) in cases {
        let state = CellState::new(balance, 0);
        let effects = vec![effect.clone()];
        let (trace, pi) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());

        // Constraint sweep: row-0 must be zero for several alphas.
        for alpha_val in [7u32, 13, 101, 997] {
            let alpha = BabyBear::new(alpha_val);
            let c = air.eval_constraints(&trace[0], &trace[1 % trace.len()], &pi, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "{label}: constraint non-zero at row 0, alpha={alpha_val}, c={:?}",
                c
            );
        }

        // Full STARK prove + verify.
        let proof = stark::prove(&air, &trace, &pi);
        let result = stark::verify(&air, &proof, &pi);
        assert!(
            result.is_ok(),
            "{label}: proof must verify, got {:?}",
            result.err()
        );

        // Also verify the proof survives serialisation.
        let proof_bytes = proof_to_bytes(&proof);
        let proof2 = proof_from_bytes(&proof_bytes).expect("{label}: proof_from_bytes failed");
        let result2 = stark::verify(&air, &proof2, &pi);
        assert!(
            result2.is_ok(),
            "{label}: deserialized proof must verify, got {:?}",
            result2.err()
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. Commitment chain: multi-turn sequential proofs, each starts where the last ended.
// ─────────────────────────────────────────────────────────────────────────────

/// Prove three sequential turns, each starting from the prior proof's
/// `NEW_COMMIT` public input.  Asserts the chain is sound end-to-end.
///
/// This is not merely `test_commitment_chain_continuity` from the
/// internal test module: it additionally:
///   - Verifies PI[OLD_COMMIT] == prior PI[NEW_COMMIT] (strict link)
///   - Confirms that a swapped proof (proof from turn 3 served as turn 2)
///     is caught by the PI mismatch.
#[test]
fn commitment_chain_three_turns_verifies_and_swap_detected() {
    let initial = CellState::new(50_000, 0);

    let turns: &[&[Effect]] = &[
        &[Effect::Transfer {
            amount: 100,
            direction: 1,
        }],
        &[Effect::SetField {
            field_idx: 0,
            value: BabyBear::new(77),
        }],
        &[Effect::GrantCapability {
            cap_entry: w8(0xFACE),
            phase_b: None,
        }],
    ];

    let mut current = initial.clone();
    let mut prev_new_commit: Option<BabyBear> = None;
    let mut all_proofs: Vec<(Vec<u8>, Vec<u32>)> = Vec::new();

    for (i, effects) in turns.iter().enumerate() {
        let (trace, pi) = generate_effect_vm_trace(&current, effects);
        let air = EffectVmAir::new(trace.len());

        // Chain link invariant: turn N's OLD_COMMIT == turn N-1's NEW_COMMIT.
        if let Some(prev) = prev_new_commit {
            assert_eq!(
                pi[pi::OLD_COMMIT],
                prev,
                "Turn {i}: OLD_COMMIT must equal prior NEW_COMMIT"
            );
        }

        let proof = stark::prove(&air, &trace, &pi);
        assert!(
            stark::verify(&air, &proof, &pi).is_ok(),
            "Turn {i} must verify"
        );

        prev_new_commit = Some(pi[pi::NEW_COMMIT]);

        // Advance state (simplified replay — enough for commitment chaining).
        match effects[0] {
            Effect::Transfer { amount, direction } => {
                if direction == 1 {
                    current.balance -= amount as u64;
                } else {
                    current.balance += amount as u64;
                }
                current.nonce += 1;
                current.refresh_commitment();
            }
            Effect::SetField { field_idx, value } => {
                current.fields[field_idx as usize] = value;
                current.nonce += 1;
                current.refresh_commitment();
            }
            Effect::GrantCapability { cap_entry, .. } => {
                current.capability_root = hash_2_to_1(current.capability_root, cap_entry[0]);
                current.nonce += 1;
                current.refresh_commitment();
            }
            _ => {}
        }

        all_proofs.push((
            proof_to_bytes(&proof),
            pi.iter().map(|b| b.as_u32()).collect(),
        ));
    }

    // Sanity: all three turns produced distinct NEW_COMMIT values.
    let commits: Vec<u32> = all_proofs
        .iter()
        .map(|(_, pi)| pi[pi::NEW_COMMIT])
        .collect();
    assert_eq!(commits.len(), 3);
    // All distinct.
    for i in 0..commits.len() {
        for j in (i + 1)..commits.len() {
            assert_ne!(
                commits[i], commits[j],
                "Turn {i} and {j} must have different NEW_COMMIT"
            );
        }
    }

    // Swap detection: use turn 2's proof bytes with turn 1's PI.
    // The serialised verifier must reject this (PI won't match the proof's trace).
    let (proof_bytes_2, _) = &all_proofs[2]; // turn 3's proof
    let (_, pi_u32_1) = &all_proofs[1]; // turn 2's PI
    let pi_bb: Vec<BabyBear> = pi_u32_1
        .iter()
        .map(|&v| BabyBear::new_canonical(v))
        .collect();
    let proof_2 = proof_from_bytes(proof_bytes_2).expect("proof_from_bytes failed");
    let air = EffectVmAir::new(proof_2.trace_len);
    let swapped = stark::verify(&air, &proof_2, &pi_bb);
    assert!(
        swapped.is_err(),
        "Swapped proof (proof from turn 3 with PI from turn 2) must be rejected"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. Net-delta PI binding: tamper INIT/FINAL_BAL and NET_DELTA and confirm rejection.
// ─────────────────────────────────────────────────────────────────────────────

/// Prove a valid transfer, then lie about the net delta in the public
/// inputs.  The STARK must reject all three flavours of lie.
#[test]
fn net_delta_pi_forgery_rejected_end_to_end() {
    let state = CellState::new(10_000, 0);
    let effects = vec![Effect::Transfer {
        amount: 500,
        direction: 1,
    }];

    let (trace, pi_orig) = generate_effect_vm_trace(&state, &effects);
    let air = EffectVmAir::new(trace.len());
    let proof = stark::prove(&air, &trace, &pi_orig);

    // Confirm the honest proof verifies and carries the right delta.
    assert!(stark::verify(&air, &proof, &pi_orig).is_ok());
    let delta = extract_net_delta(&pi_orig).unwrap();
    assert_eq!(delta, -500);

    // Lie 1: claim delta = 0.
    let mut pi_lie1 = pi_orig.clone();
    pi_lie1[pi::NET_DELTA_MAG] = BabyBear::ZERO;
    pi_lie1[pi::NET_DELTA_SIGN] = BabyBear::ZERO;
    assert!(
        stark::verify(&air, &proof, &pi_lie1).is_err(),
        "Lying NET_DELTA to 0 must be rejected"
    );

    // Lie 2: flip the sign (claim +500 instead of -500).
    let mut pi_lie2 = pi_orig.clone();
    pi_lie2[pi::NET_DELTA_SIGN] = BabyBear::ZERO; // 0 = positive
    assert!(
        stark::verify(&air, &proof, &pi_lie2).is_err(),
        "Flipping NET_DELTA_SIGN must be rejected"
    );

    // Lie 3: corrupt FINAL_BAL_LO (makes the balance-binding constraint fail).
    let mut pi_lie3 = pi_orig.clone();
    pi_lie3[pi::FINAL_BAL_LO] = pi_lie3[pi::FINAL_BAL_LO] + BabyBear::new(1);
    assert!(
        stark::verify(&air, &proof, &pi_lie3).is_err(),
        "Corrupted FINAL_BAL_LO must be rejected"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 6. Effects hash: reordering and subset attacks produce distinct hashes.
// ─────────────────────────────────────────────────────────────────────────────

/// Prove a 2-effect turn; then prove a permuted version; assert the two proofs
/// have different EFFECTS_HASH PIs and neither proof verifies against the
/// other's PI.
///
/// This is an end-to-end reordering-attack test (the unit-level hash-comparison
/// test already exists; this adds the STARK verification step).
#[test]
fn effects_hash_reordering_produces_different_pi_rejected_cross_verify() {
    let state = CellState::new(10_000, 0);

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

    let (trace_a, pi_a) = generate_effect_vm_trace(&state, &effects_a);
    let (trace_b, pi_b) = generate_effect_vm_trace(&state, &effects_b);

    let air_a = EffectVmAir::new(trace_a.len());
    let air_b = EffectVmAir::new(trace_b.len());

    let proof_a = stark::prove(&air_a, &trace_a, &pi_a);
    let proof_b = stark::prove(&air_b, &trace_b, &pi_b);

    // Both honest proofs verify.
    assert!(stark::verify(&air_a, &proof_a, &pi_a).is_ok());
    assert!(stark::verify(&air_b, &proof_b, &pi_b).is_ok());

    // Effects hashes must differ.
    assert_ne!(
        pi_a[pi::EFFECTS_HASH_LO],
        pi_b[pi::EFFECTS_HASH_LO],
        "Reordered effects must produce different EFFECTS_HASH_LO"
    );

    // Cross-verify: proof_a with pi_b must be rejected.
    assert!(
        stark::verify(&air_a, &proof_a, &pi_b).is_err(),
        "proof_a verified against pi_b must fail (different effects hash)"
    );
    // And proof_b with pi_a.
    assert!(
        stark::verify(&air_b, &proof_b, &pi_a).is_err(),
        "proof_b verified against pi_a must fail"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 7. ValidateHandoff: honest proof verifies, wrong PI root rejected.
// ─────────────────────────────────────────────────────────────────────────────

