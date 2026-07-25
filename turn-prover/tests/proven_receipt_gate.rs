//! The `TurnProven` adversarial gate over a GENUINE minted proof.
//!
//! These were `#[cfg(feature = "prover")]` tests inside `turn/src/conditional.rs`.
//! The RESOLVER they exercise (`dregg_turn::conditional::resolve_condition`) is
//! unconditional core; the MINT that feeds it real STARK material is
//! [`dregg_turn_prover::mint_transfer_proven_receipt`], so the test lives with the
//! mint. Heavy: each test mints one real wide rotated proof.

use std::collections::HashSet;

use dregg_turn::conditional::{
    ConditionProof, ConditionalResult, DEFAULT_MAX_ROOT_AGE, ProofCondition, resolve_condition,
};
use dregg_turn::turn::TurnReceipt;
use dregg_turn_prover::mint_transfer_proven_receipt;

fn nullifiers() -> HashSet<[u8; 32]> {
    HashSet::new()
}

fn receipt_for(turn_hash: [u8; 32]) -> TurnReceipt {
    TurnReceipt {
        turn_hash,
        ..Default::default()
    }
}

/// Mint the genuine wide rotated EffectVM STARK material for the adversarial gate, via the
/// production-shared [`dregg_turn_prover::mint_transfer_proven_receipt`] (the SINGLE proving recipe the downstream
/// proof-carrying features reuse). Returns the raw material for the per-forgery mutations.
fn genuine_effect_vm_turn_proof(
    turn_hash: [u8; 32],
    amount: u64,
) -> (Vec<u8>, Vec<u32>, [u8; 32], [u8; 32]) {
    let pr = mint_transfer_proven_receipt(turn_hash, amount);
    (
        pr.effect_vm_proof_bytes,
        pr.effect_vm_public_inputs,
        pr.pre_commitment,
        pr.post_commitment,
    )
}

/// The [`dregg_turn::ProvenReceipt`] convenience API is coherent end-to-end: a minted proof's
/// `turn_proven_condition()` is RESOLVED by its own `effect_vm_proof()` on the real resolver.
/// (Heavy: mints one real wide rotated proof.)
#[test]
fn proven_receipt_condition_resolves_its_own_proof() {
    let turn_hash = [0x77u8; 32];
    let proven = mint_transfer_proven_receipt(turn_hash, 5);
    let condition = proven.turn_proven_condition();
    let proof = proven.effect_vm_proof();
    assert!(matches!(condition, ProofCondition::TurnProven { .. }));
    assert!(matches!(proof, ConditionProof::EffectVmProof { .. }));
    let mut n = nullifiers();
    assert_eq!(
        resolve_condition(
            &condition,
            &proof,
            10,
            100,
            &[],
            DEFAULT_MAX_ROOT_AGE,
            &mut n,
            &[]
        ),
        ConditionalResult::Resolved,
        "a ProvenReceipt's own condition must resolve its own proof"
    );
}

/// THE GATE, adversarial: a `TurnProven` condition RESOLVES for a genuine EffectVM STARK bound
/// to the turn, and REJECTS (a) a proof for a DIFFERENT turn (wrong `turn_hash`), (b) a wrong
/// expected pre/post commitment (a proof of a different state transition), (c) a mutated proof
/// blob (the mutation canary), and (d) tampered public inputs. Heavy: mints one real wide
/// rotated proof.
#[test]
fn turn_proven_gate_accepts_genuine_and_rejects_forgeries() {
    let turn_hash = [0x5Au8; 32];
    let (proof_bytes, public_inputs, expected_pre, expected_post) =
        genuine_effect_vm_turn_proof(turn_hash, 7);

    let condition = ProofCondition::TurnProven {
        turn_hash,
        expected_pre_commitment: expected_pre,
        expected_post_commitment: expected_post,
    };
    let good_proof = ConditionProof::EffectVmProof {
        receipt: Box::new(receipt_for(turn_hash)),
        proof_bytes: proof_bytes.clone(),
        public_inputs: public_inputs.clone(),
    };

    // (accept) genuine proof bound to the turn resolves.
    let mut n = nullifiers();
    let ok = resolve_condition(
        &condition,
        &good_proof,
        10,
        100,
        &[],
        DEFAULT_MAX_ROOT_AGE,
        &mut n,
        &[],
    );
    assert_eq!(
        ok,
        ConditionalResult::Resolved,
        "genuine proof must resolve"
    );

    // (a) a proof for a DIFFERENT turn: the condition names another turn_hash, the receipt's
    // turn_hash mismatches AND PI[TURN_HASH] no longer matches.
    let other_condition = ProofCondition::TurnProven {
        turn_hash: [0xC3u8; 32],
        expected_pre_commitment: expected_pre,
        expected_post_commitment: expected_post,
    };
    let other_receipt_proof = ConditionProof::EffectVmProof {
        receipt: Box::new(receipt_for([0xC3u8; 32])),
        proof_bytes: proof_bytes.clone(),
        public_inputs: public_inputs.clone(),
    };
    let mut n = nullifiers();
    assert!(
        matches!(
            resolve_condition(&other_condition, &other_receipt_proof, 10, 100, &[], DEFAULT_MAX_ROOT_AGE, &mut n, &[]),
            ConditionalResult::InvalidProof(ref m) if m.contains("TURN_HASH")
        ),
        "a genuine proof relabelled onto a different turn must be rejected"
    );

    // (b) wrong expected post-commitment (a proof of a different transition).
    let mut bad_post = expected_post;
    bad_post[0] ^= 0x01;
    let wrong_endpoint = ProofCondition::TurnProven {
        turn_hash,
        expected_pre_commitment: expected_pre,
        expected_post_commitment: bad_post,
    };
    let mut n = nullifiers();
    assert!(
        matches!(
            resolve_condition(&wrong_endpoint, &good_proof, 10, 100, &[], DEFAULT_MAX_ROOT_AGE, &mut n, &[]),
            ConditionalResult::InvalidProof(ref m) if m.contains("NEW_COMMIT")
        ),
        "a wrong post-state endpoint must be rejected"
    );

    // (c) MUTATION CANARY: flip a byte of the proof blob → the STARK no longer verifies under
    // any cohort descriptor.
    let mut mutated = proof_bytes.clone();
    let mid = mutated.len() / 2;
    mutated[mid] ^= 0x01;
    let mutated_proof = ConditionProof::EffectVmProof {
        receipt: Box::new(receipt_for(turn_hash)),
        proof_bytes: mutated,
        public_inputs: public_inputs.clone(),
    };
    let mut n = nullifiers();
    assert!(
        matches!(
            resolve_condition(
                &condition,
                &mutated_proof,
                10,
                100,
                &[],
                DEFAULT_MAX_ROOT_AGE,
                &mut n,
                &[]
            ),
            ConditionalResult::InvalidProof(_)
        ),
        "a mutated proof blob must be rejected (mutation canary)"
    );

    // (d) tampered PUBLIC INPUTS: bump the wide NEW anchor felt → Fiat–Shamir / anchor binding
    // rejects.
    let mut bad_pi = public_inputs.clone();
    let last = bad_pi.len() - 1;
    bad_pi[last] = bad_pi[last].wrapping_add(1);
    let bad_pi_proof = ConditionProof::EffectVmProof {
        receipt: Box::new(receipt_for(turn_hash)),
        proof_bytes: proof_bytes.clone(),
        public_inputs: bad_pi,
    };
    let mut n = nullifiers();
    assert!(
        matches!(
            resolve_condition(
                &condition,
                &bad_pi_proof,
                10,
                100,
                &[],
                DEFAULT_MAX_ROOT_AGE,
                &mut n,
                &[]
            ),
            ConditionalResult::InvalidProof(_)
        ),
        "tampered public inputs must be rejected"
    );
}
