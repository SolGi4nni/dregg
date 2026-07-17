//! Proof composition checks: composing multiple derivation+membership proofs, IVC chaining.
//!
//! ## Migration note (stark-kill)
//!
//! These checks previously drove `dregg_circuit::prove_authorization_with_membership` — a
//! MULTI-step composite over `MultiStepDerivationAir` that chained derivation steps by an
//! accumulated hash. The stark-kill campaign (`f04b2dd1e`) DELETED that composite and the
//! hand engine under it. Its successors in the descriptor world
//! (`crate::checks::derivation_descriptor`) are the emitted `dregg-derivation-v1`
//! (single-step) + 4-ary Merkle-membership descriptors.
//!
//! **No emitted descriptor for the multi-step accumulated-hash chain exists** — the
//! registry (`descriptor_by_name`) carries only a single-step `dregg-derivation-v1`. So
//! "composition" here proves each derivation step INDIVIDUALLY through the descriptor
//! composite, each bound to the shared committed `state_root` by its own pi[0] pin. The
//! in-circuit accumulated-hash chaining ACROSS steps is NOT re-proven by these checks; that
//! is the honest residual of the migration (the deleted multi-step AIR had no emitted twin).
//! The IVC fold-chain check is unaffected — `prove_ivc`/`verify_ivc` survived intact.

use dregg_circuit::derivation_air::{BodyAtomPattern, CircuitRule, DerivationWitness};
use dregg_circuit::ivc::{FoldDelta, IvcVerification, prove_ivc, verify_ivc};
use dregg_circuit::multi_step_witness::ALLOW_PREDICATE;
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit::{BabyBear, BodyFactMerkleProof};
use dregg_commit::poseidon2_tree::Poseidon2MerkleTree;

use crate::checks::derivation_descriptor::prove_verify_step_with_membership;
use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("compose", check_compose_two_derivations),
        run_check("chain", check_ivc_chain),
        run_check("aggregate", check_proof_aggregation),
    ]
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

/// Build an honest 2-variable firing step deriving `ALLOW(v0,v1)` from `body_pred(v0,v1)`,
/// whose body fact hash is the felt the `dregg-derivation-v1` descriptor recomputes and pins
/// (over the 3 body-atom term slots, the third padded to zero). `state_root` is threaded in
/// so multiple steps can share one committed state.
fn honest_step(
    body_pred: BabyBear,
    v0: BabyBear,
    v1: BabyBear,
    state_root: BabyBear,
) -> (DerivationWitness, BabyBear) {
    let body_hash = hash_fact(body_pred, &[v0, v1, BabyBear::ZERO]);
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
        substitution: vec![v0, v1],
        derived_predicate: allow_pred,
        derived_terms: [v0, v1, BabyBear::ZERO, BabyBear::ZERO],
        not_after_height: BabyBear::ZERO,
        org_id_hash: BabyBear::ZERO,
        budget_remaining: BabyBear::ZERO,
    };
    (step, body_hash)
}

/// Compose TWO independent derivation+membership proofs over a shared committed state root:
/// each step's body fact is a leaf of the same tree, and each descriptor proof pins that
/// shared root. (The multi-step accumulated-hash chain the deleted composite proved has no
/// emitted descriptor — see the module note.)
fn check_compose_two_derivations() -> Result<(), String> {
    let pred_a = BabyBear::new(200);
    let pred_b = BabyBear::new(201);
    let alice = BabyBear::new(1000);
    let app = BabyBear::new(2000);

    let fact_a = hash_fact(pred_a, &[alice, app, BabyBear::ZERO]);
    let fact_b = hash_fact(pred_b, &[alice, app, BabyBear::ZERO]);

    let mut tree = Poseidon2MerkleTree::with_depth(4);
    let pos_a = tree.append(fact_a);
    let pos_b = tree.append(fact_b);
    for i in 2..8u32 {
        tree.append(BabyBear::new(i * 7777));
    }
    let mut tree_for_root = tree.clone();
    let state_root = tree_for_root.root();

    let (step_a, _) = honest_step(pred_a, alice, app, state_root);
    let (step_b, _) = honest_step(pred_b, alice, app, state_root);

    prove_verify_step_with_membership(&step_a, &[make_membership_proof(&tree, pos_a)])?;
    prove_verify_step_with_membership(&step_b, &[make_membership_proof(&tree, pos_b)])?;
    Ok(())
}

fn check_ivc_chain() -> Result<(), String> {
    use dregg_circuit::dsl::fold::{FoldWitness, compute_test_checks_commitment};

    let initial_root = BabyBear::new(50000);

    let deltas: Vec<FoldDelta> = (0..3)
        .map(|i| {
            let fold = FoldWitness {
                old_root: BabyBear::new(50000 + i),
                new_root: BabyBear::new(50000 + i + 1),
                removed_facts: vec![],
                num_added_checks: 1,
                added_checks_commitment: compute_test_checks_commitment(1),
            };
            FoldDelta::new(fold)
        })
        .collect();

    let proof = prove_ivc(initial_root, deltas).ok_or("IVC chain proof failed")?;

    if proof.step_count != 3 {
        return Err(format!("expected 3 steps, got {}", proof.step_count));
    }

    let verification = verify_ivc(&proof, Some(initial_root));
    match verification {
        IvcVerification::Valid => {}
        other => return Err(format!("IVC chain verification failed: {:?}", other)),
    }

    if proof.final_root != BabyBear::new(50003) {
        return Err(format!(
            "expected final_root=50003, got {:?}",
            proof.final_root
        ));
    }

    Ok(())
}

/// Prove + verify FOUR independent derivation+membership proofs, each over a distinct body
/// fact in a shared committed state — the descriptor-world analog of the old "aggregation"
/// (which proved N derivations independently, not a recursive aggregate proof).
fn check_proof_aggregation() -> Result<(), String> {
    let alice = BabyBear::new(1000);
    let preds: Vec<BabyBear> = (0..4).map(|i| BabyBear::new(400 + i)).collect();

    let mut tree = Poseidon2MerkleTree::with_depth(4);
    let mut fact_positions = Vec::new();
    for i in 0..4u32 {
        let fact = hash_fact(
            preds[i as usize],
            &[alice, BabyBear::new(i + 2000), BabyBear::ZERO],
        );
        fact_positions.push(tree.append(fact));
    }
    for i in 4..8u32 {
        tree.append(BabyBear::new(i * 5555));
    }
    let mut tree_for_root = tree.clone();
    let state_root = tree_for_root.root();

    for i in 0..4u32 {
        let (step, _) = honest_step(
            preds[i as usize],
            alice,
            BabyBear::new(i + 2000),
            state_root,
        );
        prove_verify_step_with_membership(
            &step,
            &[make_membership_proof(&tree, fact_positions[i as usize])],
        )
        .map_err(|e| format!("aggregated proof {i} failed: {e}"))?;
    }
    Ok(())
}
