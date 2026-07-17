//! Proof generation and verification checks:
//! STARK (MerklePoseidon2), derivation, temporal predicate, effect VM.

use dregg_bridge::present::{
    BridgePresentationBuilder, bytes_to_babybear, hash_index, verify_presentation_bb,
};
use dregg_circuit::derivation_air::{BodyAtomPattern, CircuitRule, DerivationWitness};
use dregg_circuit::multi_step_witness::ALLOW_PREDICATE;
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit::{BabyBear, BodyFactMerkleProof};
use dregg_commit::poseidon2_tree::Poseidon2MerkleTree;
use dregg_token::{Attenuation, AuthRequest, MacaroonToken};

use crate::checks::derivation_descriptor::{
    forged_conclusion_is_refused, prove_verify_step_with_membership,
};
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

    // MIGRATED verification: the legacy opaque issuer-STARK accessors
    // (`verify_issuer_stark` / `issuer_proof_bytes`) were removed on the
    // `StarkProof` → `Ir2BatchProof` wire flip (stark-kill). The retained
    // cryptographic verifier is `verify_presentation_bb`, which checks BOTH
    // committed descriptor wires (bound-presentation + blinded ring-membership)
    // and binds them to the EXTERNAL federation root.
    if !verify_presentation_bb(&proof, federation_root_bb) {
        return Err("presentation proof failed cryptographic verification".into());
    }

    // ADVERSARIAL tooth: the same proof MUST be refused against a WRONG federation
    // root — else the root binding is not actually enforced (non-vacuity).
    let wrong_root = federation_root_bb + BabyBear::ONE;
    if verify_presentation_bb(&proof, wrong_root) {
        return Err("presentation verifier ACCEPTED a wrong federation root".into());
    }

    // Sanity on the emitted artifact: the two committed descriptor blobs are well over 1 KiB.
    let real = proof
        .real_stark_proof
        .as_ref()
        .ok_or("should have a real STARK proof")?;
    let proof_bytes = real.total_proof_size_bytes();
    if proof_bytes < 1000 {
        return Err(format!(
            "real descriptor proofs should be > 1KB, got {proof_bytes} bytes"
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
    // The `dregg-derivation-v1` descriptor recomputes and pins the body fact hash over the
    // rule's 3 body-atom term slots, so the tree leaf must match that exact felt.
    let body_fact_hash = hash_fact(has_cap_pred, &[alice, app1, read_perm]);
    let fact_pos = tree.append(body_fact_hash);

    // Add filler leaves
    for i in 1..8u32 {
        tree.append(BabyBear::new(i * 9999));
    }

    let mut tree_for_root = tree.clone();
    let state_root = tree_for_root.root();

    let allow_pred = BabyBear::new(ALLOW_PREDICATE);

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

    // Generate membership proof for the body fact.
    let mp = tree
        .prove_membership(fact_pos)
        .expect("fact must be in tree");
    let body_proof = BodyFactMerkleProof {
        fact_hash: mp.leaf,
        siblings: mp.siblings,
        positions: mp.positions,
    };

    // Prove + verify the derivation + Merkle-membership composite on the deployed descriptor
    // prover (the migrated successor of the stark-killed
    // `prove_authorization_with_membership`).
    let bytes = prove_verify_step_with_membership(&step, &[body_proof])?;
    if bytes == 0 {
        return Err("descriptor proofs should be non-empty".into());
    }

    // ADVERSARIAL tooth: a forged conclusion pin must be refused (non-vacuity).
    forged_conclusion_is_refused(&step)?;

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

/// An HONEST whole-chain proof accepts through the REAL recursive verifier (the
/// simulated `dregg_circuit::ivc` hash-chain was PURGED from this check
/// 2026-07-16): the shared honest 2-turn fold over genuinely minted rotated
/// turns (`crate::checks::ivc_real`) round-trips its wire byte envelope and
/// verifies via `verify_whole_chain_proof_bytes` against the fold's own VK
/// fingerprint. The adversarial teeth live in `check_ivc_wrong_initial_root`
/// below plus the composition/backends/sovereign IVC checks (wrong genesis,
/// relabeled count, tampered digest, tampered final root, wrong VK, forged
/// chain).
fn check_ivc_proof() -> Result<(), String> {
    use dregg_circuit_prove::ivc_turn_chain::verify_whole_chain_proof_bytes;

    use crate::checks::ivc_real::honest_chain_proof;

    let chain = honest_chain_proof()?;
    if chain.num_turns != 2 {
        return Err(format!("expected 2 folded turns, got {}", chain.num_turns));
    }
    verify_whole_chain_proof_bytes(&chain.bytes, &chain.vk)
        .map_err(|e| format!("verifier rejected an HONEST whole-chain proof: {e}"))
}

/// ADVERSARIAL: a whole-chain proof claiming the WRONG initial (genesis) root
/// must be REJECTED by the REAL recursive verifier. Both a scalar-lane and a
/// wide-lane forgery are tried: lane 0 is pinned by the Lean-emitted binding
/// descriptor's scalar publics AND the root-exposed segment; lanes 1..8 are
/// pinned ONLY by the root-exposed 8-felt segment claim, so the second leg
/// proves the WIDE anchor binding bites on its own.
fn check_ivc_wrong_initial_root() -> Result<(), String> {
    use dregg_circuit_prove::ivc_turn_chain::{
        WholeChainProofBytes, verify_whole_chain_proof_bytes,
    };

    use crate::checks::ivc_real::honest_chain_proof;

    let chain = honest_chain_proof()?;

    // With the CORRECT (carried) genesis root the envelope verifies.
    verify_whole_chain_proof_bytes(&chain.bytes, &chain.vk)
        .map_err(|e| format!("correct genesis root should verify, got: {e}"))?;

    // WRONG initial root, scalar lane: refused.
    let mut wrong = WholeChainProofBytes::from_postcard(&chain.bytes)
        .map_err(|e| format!("envelope re-decode failed: {e}"))?;
    wrong.genesis_root[0] ^= 1;
    if verify_whole_chain_proof_bytes(&wrong.to_postcard(), &chain.vk).is_ok() {
        return Err(
            "MOCK-GRADE verifier: a whole-chain proof claiming a WRONG genesis root \
             (scalar lane) was ACCEPTED — the initial-state anchor is not bound"
                .into(),
        );
    }

    // WRONG initial root, wide lane (untouched by the scalar binding publics):
    // only the root-exposed 8-felt segment claim can refuse this one.
    let mut wide = WholeChainProofBytes::from_postcard(&chain.bytes)
        .map_err(|e| format!("envelope re-decode failed: {e}"))?;
    wide.genesis_root[7] ^= 1;
    if verify_whole_chain_proof_bytes(&wide.to_postcard(), &chain.vk).is_ok() {
        return Err(
            "MOCK-GRADE verifier: a whole-chain proof claiming a WRONG genesis root \
             (wide lane 7) was ACCEPTED — the 8-felt genesis anchor is not bound"
                .into(),
        );
    }

    Ok(())
}
