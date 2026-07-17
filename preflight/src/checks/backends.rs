//! Cross-backend checks: the derivation + Merkle-membership composite, proven on the
//! deployed Lean-emitted descriptor prover, plus IVC recursion.
//!
//! The legacy custom-STARK vs Plonky3 backend comparison these checks named is gone: the
//! stark-kill campaign (`f04b2dd1e`) DELETED the hand-rolled STARK engine and its
//! `prove_authorization_with_membership` composite. Every production consumer now runs on
//! the single descriptor prover (`prove_vm_descriptor2` / `verify_vm_descriptor2`), so there
//! is no longer a second backend to cross-check against — the "custom" and "plonky3" paths
//! are the SAME prover. These checks therefore exercise the deployed composite
//! (`crate::checks::derivation_descriptor`) and assert it accepts an honest proof AND refuses
//! a forged conclusion.

use dregg_circuit::derivation_air::{BodyAtomPattern, CircuitRule, DerivationWitness};
use dregg_circuit::multi_step_witness::ALLOW_PREDICATE;
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit::{BabyBear, BodyFactMerkleProof};
use dregg_commit::poseidon2_tree::Poseidon2MerkleTree;

use crate::checks::derivation_descriptor::{
    forged_conclusion_is_refused, prove_verify_step_with_membership,
};
use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("descriptor-composite", check_descriptor_composite),
        run_check("descriptor-forged-refused", check_forged_conclusion_refused),
        run_check("ivc-recursive", check_ivc_recursive),
    ]
}

/// Build one honest firing derivation step (`derived(t0,t1)` from `body(t0,t1)`) whose body
/// fact hash is the exact felt the `dregg-derivation-v1` descriptor recomputes and pins, plus
/// a depth-4 Poseidon2 tree containing that leaf and its position. Constructed the way
/// `dregg_circuit::derivation_witness`'s in-tree honest witness is, so the descriptor's
/// exported body-fact pin equals `step.body_fact_hashes[0]` (== the inserted leaf).
fn build_honest_step() -> (DerivationWitness, Poseidon2MerkleTree, usize) {
    let body_pred = BabyBear::new(500);
    let alice = BabyBear::new(1000);
    let app = BabyBear::new(2000);
    // The descriptor recomputes the body fact hash over the 3 body-atom term slots.
    let body_hash = hash_fact(body_pred, &[alice, app, BabyBear::ZERO]);

    let mut tree = Poseidon2MerkleTree::with_depth(4);
    let fact_pos = tree.append(body_hash);
    for i in 1..8u32 {
        tree.append(BabyBear::new(i * 3333));
    }
    let mut tree_for_root = tree.clone();
    let state_root = tree_for_root.root();
    let allow_pred = BabyBear::new(ALLOW_PREDICATE);

    let step = DerivationWitness {
        rule: CircuitRule {
            id: 1,
            num_body_atoms: 1,
            num_variables: 2,
            head_predicate: allow_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (true, BabyBear::new(1)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: body_pred,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (false, BabyBear::ZERO),
                ],
            }],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
            lt_check: None,
        },
        state_root,
        body_fact_hashes: vec![body_hash],
        substitution: vec![alice, app],
        derived_predicate: allow_pred,
        derived_terms: [alice, app, BabyBear::ZERO, BabyBear::ZERO],
        not_after_height: BabyBear::ZERO,
        org_id_hash: BabyBear::ZERO,
        budget_remaining: BabyBear::ZERO,
    };
    (step, tree, fact_pos)
}

fn make_membership_proof(tree: &Poseidon2MerkleTree, position: usize) -> BodyFactMerkleProof {
    let mp = tree
        .prove_membership(position)
        .expect("fact must be in tree");
    BodyFactMerkleProof {
        fact_hash: mp.leaf,
        siblings: mp.siblings,
        positions: mp.positions,
    }
}

/// The derivation + Merkle-membership composite proves and verifies on the deployed
/// descriptor prover — the single prover every production consumer now runs (the "custom
/// STARK vs plonky3" backend comparison this file once made is moot: they are the same
/// prover after stark-kill).
fn check_descriptor_composite() -> Result<(), String> {
    let (step, tree, fact_pos) = build_honest_step();
    let body_proofs = vec![make_membership_proof(&tree, fact_pos)];
    let bytes = prove_verify_step_with_membership(&step, &body_proofs)?;
    if bytes < 1000 {
        return Err(format!(
            "real descriptor proofs should exceed 1 KiB, got {bytes} bytes"
        ));
    }
    Ok(())
}

/// ADVERSARIAL: the `dregg-derivation-v1` descriptor must REFUSE a forged conclusion pin.
/// Without this tooth the composite check above could not distinguish a real verifier from
/// an unconditional `Ok(())`.
fn check_forged_conclusion_refused() -> Result<(), String> {
    let (step, _tree, _pos) = build_honest_step();
    forged_conclusion_is_refused(&step)
}

/// IVC recursion through the REAL whole-chain recursive prover (the simulated
/// `dregg_circuit::ivc` hash-chain was PURGED from this check 2026-07-16): the
/// shared honest 2-turn fold over genuinely minted rotated turns verifies
/// through `verify_whole_chain_proof_bytes`, and the recursion's ordered-history
/// DIGEST is genuinely bound — a tampered `chain_digest` lane (claiming a
/// different middle history between the same endpoints) must be REFUSED.
fn check_ivc_recursive() -> Result<(), String> {
    use dregg_circuit_prove::ivc_turn_chain::{
        WholeChainProofBytes, verify_whole_chain_proof_bytes,
    };

    use crate::checks::ivc_real::honest_chain_proof;

    let chain = honest_chain_proof()?;

    // REAL verification of the honest whole-chain byte envelope.
    verify_whole_chain_proof_bytes(&chain.bytes, &chain.vk)
        .map_err(|e| format!("verifier rejected an HONEST whole-chain proof: {e}"))?;

    // ── TOOTH: the 8-felt ordered-history digest is a bound public of the
    // recursive fold. An envelope claiming a different chain digest over the
    // same proof must be refused.
    let mut tampered = WholeChainProofBytes::from_postcard(&chain.bytes)
        .map_err(|e| format!("envelope re-decode failed: {e}"))?;
    tampered.chain_digest[0] ^= 1;
    if verify_whole_chain_proof_bytes(&tampered.to_postcard(), &chain.vk).is_ok() {
        return Err(
            "MOCK-GRADE verifier: a whole-chain envelope with a TAMPERED ordered-history \
             digest was ACCEPTED — the recursion's chain digest is not bound to the proof"
                .into(),
        );
    }

    Ok(())
}
