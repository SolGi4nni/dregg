//! Proof generation and verification checks:
//! STARK (MerklePoseidon2), derivation, temporal predicate, effect VM.

use dregg_bridge::present::{BridgePresentationBuilder, bytes_to_babybear, hash_index};
use dregg_circuit::derivation_air::{BodyAtomPattern, CircuitRule, DerivationWitness};
use dregg_circuit::ivc::{FoldDelta, IvcVerification, prove_ivc, verify_ivc};
use dregg_circuit::multi_step_air::{ALLOW_PREDICATE, build_multi_step_witness};
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit::{
    BabyBear, BodyFactMerkleProof, prove_authorization_with_membership,
    verify_authorization_with_membership,
};
use dregg_commit::poseidon2_tree::Poseidon2MerkleTree;
use dregg_token::{Attenuation, AuthRequest, MacaroonToken};

use crate::report::{CheckResult, run_check};

fn test_key(name: &str) -> [u8; 32] {
    *blake3::hash(format!("preflight-proofs:{name}").as_bytes()).as_bytes()
}

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("stark", check_stark_proof),
        run_check("derivation", check_derivation_proof),
        run_check("effect_vm", check_effect_vm_proof),
        run_check("ivc", check_ivc_proof),
        run_check("ivc_wrong_root", check_ivc_wrong_initial_root),
    ]
}

/// Compute the synthetic Poseidon2 federation root for an issuer key.
/// Same logic as the full_pipeline tests.
fn compute_federation_root_poseidon2(issuer_key: &[u8; 32]) -> BabyBear {
    use dregg_circuit::poseidon2;
    let issuer_hash = bytes_to_babybear(issuer_key);
    let depth = 8;
    let mut current = issuer_hash;
    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new(hash_index(i, 0, issuer_key)),
            BabyBear::new(hash_index(i, 1, issuer_key)),
            BabyBear::new(hash_index(i, 2, issuer_key)),
        ];
        let mut children = [BabyBear::ZERO; 4];
        let mut sib_idx = 0;
        for j in 0..4u8 {
            if j == position {
                children[j as usize] = current;
            } else {
                children[j as usize] = siblings[sib_idx];
                sib_idx += 1;
            }
        }
        current = poseidon2::hash_4_to_1(&children);
    }
    current
}

fn bb_to_bytes(bb: BabyBear) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    bytes[..4].copy_from_slice(&bb.0.to_le_bytes());
    bytes
}

fn check_stark_proof() -> Result<(), String> {
    // Build a real Merkle membership STARK proof and verify it.
    let issuer_key = test_key("issuer-stark");
    let federation_root_bb = compute_federation_root_poseidon2(&issuer_key);
    let federation_root_bytes = bb_to_bytes(federation_root_bb);

    // Create a presentation builder with proper federation root
    let mut builder = BridgePresentationBuilder::new_with_root_bb(
        issuer_key,
        federation_root_bytes,
        federation_root_bb,
    );
    let root_token = MacaroonToken::mint(issuer_key, b"stark-kid", "compute.dregg.fg-goose.online");
    builder.set_root_token(root_token);

    let att = Attenuation {
        services: vec![("compute".into(), "rw".into())],
        ..Default::default()
    };
    if !builder.add_attenuation(&att) {
        return Err("attenuation should succeed".into());
    }

    let request = AuthRequest {
        service: Some("compute".into()),
        action: Some("r".into()),
        now: Some(1700000000),
        ..Default::default()
    };

    let proof = builder
        .prove(&request)
        .map_err(|e| format!("prove failed: {e:?}"))?;

    if !proof.has_real_stark_proof() {
        return Err("proof should contain a real STARK".into());
    }

    // Verify the STARK proof
    let stark_result = proof.verify_issuer_stark();
    match stark_result {
        Some(Ok(())) => {}
        Some(Err(e)) => return Err(format!("STARK verification failed: {e:?}")),
        None => return Err("no STARK proof to verify".into()),
    }

    // Sanity on the emitted artifact: a real membership STARK is well over 1 KiB.
    let proof_bytes = proof
        .issuer_proof_bytes()
        .ok_or("should have proof bytes")?;
    if proof_bytes.len() < 1000 {
        return Err(format!(
            "real STARK proof should be > 1KB, got {} bytes",
            proof_bytes.len()
        ));
    }

    Ok(())
}

fn check_derivation_proof() -> Result<(), String> {
    // Build a Datalog derivation witness with body facts and prove via STARK.
    let mut tree = Poseidon2MerkleTree::with_depth(4);

    let has_cap_pred = BabyBear::new(100);
    let alice = BabyBear::new(1000);
    let app1 = BabyBear::new(2000);
    let read_perm = BabyBear::new(3000);
    let body_fact_hash = hash_fact(has_cap_pred, &[alice, app1, read_perm, BabyBear::ZERO]);
    let fact_pos = tree.append(body_fact_hash);

    // Add filler leaves
    for i in 1..8u32 {
        tree.append(BabyBear::new(i * 9999));
    }

    let mut tree_for_root = tree.clone();
    let state_root = tree_for_root.root();

    let allow_pred = BabyBear::new(ALLOW_PREDICATE);
    let request_hash = BabyBear::new(42);

    let step = DerivationWitness {
        rule: CircuitRule {
            id: 1,
            num_body_atoms: 1,
            num_variables: 3,
            head_predicate: allow_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (true, BabyBear::new(1)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: has_cap_pred,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (true, BabyBear::new(2)),
                ],
            }],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
            lt_check: None,
        },
        state_root,
        body_fact_hashes: vec![body_fact_hash],
        substitution: vec![alice, app1, read_perm],
        derived_predicate: allow_pred,
        derived_terms: [alice, app1, BabyBear::ZERO, BabyBear::ZERO],
        not_after_height: BabyBear::ZERO,
        org_id_hash: BabyBear::ZERO,
        budget_remaining: BabyBear::ZERO,
    };

    let witness = build_multi_step_witness(state_root, request_hash, vec![step]);
    if witness.conclusion() != BabyBear::ONE {
        return Err("witness should conclude ALLOW".into());
    }

    // Generate membership proof for the body fact
    let mp = tree
        .prove_membership(fact_pos)
        .expect("fact must be in tree");
    let body_proof = BodyFactMerkleProof {
        fact_hash: mp.leaf,
        siblings: mp.siblings,
        positions: mp.positions,
    };

    // Generate the STARK proof for the derivation
    let stark_proof = prove_authorization_with_membership(&witness, &[body_proof]);
    if stark_proof.derivation_proof.trace_len == 0 {
        return Err("derivation proof trace should be non-empty".into());
    }

    // Verify
    let conclusion = witness.conclusion();
    let accumulated_hash = witness.final_accumulated_hash();
    let body_hashes: Vec<BabyBear> = witness
        .steps
        .iter()
        .flat_map(|s| s.body_fact_hashes.clone())
        .collect();
    let verify_result = verify_authorization_with_membership(
        &stark_proof,
        conclusion,
        accumulated_hash,
        &body_hashes,
    );
    verify_result.map_err(|e| format!("derivation proof verification failed: {e}"))?;

    Ok(())
}

fn check_effect_vm_proof() -> Result<(), String> {
    // Prove a single-Transfer turn through the LIVE verified-by-construction
    // path: the Lean-emitted EffectVM DESCRIPTOR interpreted by
    // `prove_vm_descriptor` / `verify_vm_descriptor` over the same
    // `generate_effect_vm_trace` witness the executor produces. Under the
    // `recursion` build (default) the v1 hand-AIR `prove_effect_vm_p3` is the
    // wasm floor; the descriptor-interpreter is the path the rotated commit
    // tower descends from, so this is the gate that exercises a real, currently
    // live proof (constraint enforcement ≠ trace success).
    use dregg_circuit::effect_vm::{CellState, Effect as VmEffect, compute_effects_hash, pi};
    use dregg_circuit::effect_vm_descriptors::descriptor_for_selector;
    use dregg_circuit::generate_effect_vm_trace;
    use dregg_circuit::lean_descriptor_air::{
        parse_vm_descriptor, prove_vm_descriptor, verify_vm_descriptor,
    };

    let initial_state = CellState::new(1000, 0);
    // selector 1 = TRANSFER — the validated descriptor; one Transfer effect.
    let effects = vec![VmEffect::Transfer {
        amount: 100,
        direction: 1,
    }];

    let (effects_hash_lo, effects_hash_hi) = compute_effects_hash(&effects);

    let (trace, public_inputs) = generate_effect_vm_trace(&initial_state, &effects);
    if trace.is_empty() {
        return Err("effect VM trace should not be empty".into());
    }
    if effects_hash_lo == BabyBear::ZERO && effects_hash_hi == BabyBear::ZERO {
        return Err("effects hash should not be zero for non-empty effects".into());
    }

    let json = descriptor_for_selector(1)
        .ok_or_else(|| "no TRANSFER (selector 1) descriptor registered".to_string())?;
    let desc = parse_vm_descriptor(json).map_err(|e| format!("parse transfer descriptor: {e}"))?;
    let dpis = public_inputs[..desc.public_input_count].to_vec();

    // PROVE + VERIFY through the descriptor interpreter — the real live proof.
    let proof = prove_vm_descriptor(&desc, &trace, &dpis)
        .map_err(|e| format!("effect VM descriptor prove failed: {e}"))?;
    verify_vm_descriptor(&desc, &proof, &dpis)
        .map_err(|e| format!("effect VM descriptor verify rejected an honest proof: {e}"))?;

    // ANTI-GHOST TOOTH: a forged post-state commitment MUST be rejected.
    let mut forged = dpis.clone();
    forged[pi::NEW_COMMIT] += BabyBear::new(1);
    if verify_vm_descriptor(&desc, &proof, &forged).is_ok() {
        return Err("effect VM descriptor verifier ACCEPTED a forged post-state commitment".into());
    }

    Ok(())
}

fn check_ivc_proof() -> Result<(), String> {
    // Generate a 3-step IVC proof and verify it.
    use dregg_circuit::fold_air::{FoldWitness, compute_test_checks_commitment};

    let initial_root = BabyBear::new(12345);

    let deltas: Vec<FoldDelta> = (0..3)
        .map(|i| {
            let fold = FoldWitness {
                old_root: BabyBear::new(12345 + i),
                new_root: BabyBear::new(12345 + i + 1),
                removed_facts: vec![],
                num_added_checks: 1,
                added_checks_commitment: compute_test_checks_commitment(1),
            };
            FoldDelta::new(fold)
        })
        .collect();

    let proof = prove_ivc(initial_root, deltas).ok_or("IVC proof generation failed")?;

    if proof.step_count != 3 {
        return Err(format!("expected 3 IVC steps, got {}", proof.step_count));
    }

    // Verify the IVC proof
    let verification = verify_ivc(&proof, Some(initial_root));
    match verification {
        IvcVerification::Valid => {}
        other => return Err(format!("IVC verification failed: {:?}", other)),
    }

    Ok(())
}

/// Adversarial: IVC proof verified against WRONG initial root must be rejected.
fn check_ivc_wrong_initial_root() -> Result<(), String> {
    use dregg_circuit::fold_air::{FoldWitness, compute_test_checks_commitment};

    let real_root = BabyBear::new(55555);
    let wrong_root = BabyBear::new(99999);

    let deltas: Vec<FoldDelta> = (0..2)
        .map(|i| {
            let fold = FoldWitness {
                old_root: BabyBear::new(55555 + i),
                new_root: BabyBear::new(55555 + i + 1),
                removed_facts: vec![],
                num_added_checks: 1,
                added_checks_commitment: compute_test_checks_commitment(1),
            };
            FoldDelta::new(fold)
        })
        .collect();

    let proof = prove_ivc(real_root, deltas).ok_or("IVC proof gen failed")?;

    // Verify with the CORRECT root: should succeed.
    let good = verify_ivc(&proof, Some(real_root));
    if !matches!(good, IvcVerification::Valid) {
        return Err(format!("correct root should verify, got {:?}", good));
    }

    // Verify with WRONG root: should FAIL.
    let bad = verify_ivc(&proof, Some(wrong_root));
    match bad {
        IvcVerification::Valid => {
            return Err(
                "IVC proof should be REJECTED when verified against wrong initial root".into(),
            );
        }
        _ => {
            // Good: wrong root correctly rejected.
        }
    }

    Ok(())
}
