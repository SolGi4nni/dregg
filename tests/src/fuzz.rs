//! Property-based fuzzing tests.
//!
//! Uses deterministic randomness (getrandom seeded from iteration index)
//! to generate random inputs and verify system invariants hold.

use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::poseidon2::{hash_2_to_1, hash_4_to_1, hash_fact, hash_many};
use dregg_commit::Fact as CommitFact;
use dregg_commit::{FactSet, FieldElement, FoldDeltaBuilder, TokenState, verify_fold_chain};
use dregg_trace::policy::minimal_policy;
use dregg_trace::types::*;
use dregg_trace::{Evaluator, symbol_from_str, verify_trace};

// =============================================================================
// Deterministic random number generation
// =============================================================================

/// A simple PRNG for test determinism (xorshift64)
struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self {
            state: seed.wrapping_add(1),
        } // avoid zero state
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }

    fn next_u32(&mut self) -> u32 {
        (self.next_u64() >> 16) as u32
    }

    fn next_field(&mut self) -> BabyBear {
        BabyBear::new(self.next_u32())
    }

    fn next_bytes(&mut self) -> [u8; 32] {
        let mut buf = [0u8; 32];
        for chunk in buf.chunks_mut(8) {
            let val = self.next_u64().to_le_bytes();
            chunk.copy_from_slice(&val[..chunk.len()]);
        }
        buf
    }
}

// =============================================================================
// 1. BabyBear field axioms
// =============================================================================

#[test]
fn field_addition_commutative() {
    let mut rng = Rng::new(1);
    for _ in 0..10000 {
        let a = rng.next_field();
        let b = rng.next_field();
        assert_eq!(
            a + b,
            b + a,
            "Addition must be commutative: {} + {} != {} + {}",
            a,
            b,
            b,
            a
        );
    }
}

#[test]
fn field_addition_associative() {
    let mut rng = Rng::new(2);
    for _ in 0..10000 {
        let a = rng.next_field();
        let b = rng.next_field();
        let c = rng.next_field();
        assert_eq!((a + b) + c, a + (b + c), "Addition must be associative");
    }
}

#[test]
fn field_multiplication_commutative() {
    let mut rng = Rng::new(3);
    for _ in 0..10000 {
        let a = rng.next_field();
        let b = rng.next_field();
        assert_eq!(a * b, b * a, "Multiplication must be commutative");
    }
}

#[test]
fn field_multiplication_associative() {
    let mut rng = Rng::new(4);
    for _ in 0..10000 {
        let a = rng.next_field();
        let b = rng.next_field();
        let c = rng.next_field();
        assert_eq!(
            (a * b) * c,
            a * (b * c),
            "Multiplication must be associative"
        );
    }
}

#[test]
fn field_distributive() {
    let mut rng = Rng::new(5);
    for _ in 0..10000 {
        let a = rng.next_field();
        let b = rng.next_field();
        let c = rng.next_field();
        assert_eq!(a * (b + c), a * b + a * c, "Distributive law must hold");
    }
}

#[test]
fn field_additive_identity() {
    let mut rng = Rng::new(6);
    for _ in 0..10000 {
        let a = rng.next_field();
        assert_eq!(a + BabyBear::ZERO, a);
        assert_eq!(BabyBear::ZERO + a, a);
    }
}

#[test]
fn field_multiplicative_identity() {
    let mut rng = Rng::new(7);
    for _ in 0..10000 {
        let a = rng.next_field();
        assert_eq!(a * BabyBear::ONE, a);
        assert_eq!(BabyBear::ONE * a, a);
    }
}

#[test]
fn field_additive_inverse() {
    let mut rng = Rng::new(8);
    for _ in 0..10000 {
        let a = rng.next_field();
        let neg_a = -a;
        assert_eq!(a + neg_a, BabyBear::ZERO, "a + (-a) must equal 0");
    }
}

#[test]
fn field_multiplicative_inverse() {
    let mut rng = Rng::new(9);
    for _ in 0..1000 {
        let a = rng.next_field();
        if a == BabyBear::ZERO {
            continue;
        }
        let inv = a.inverse().unwrap();
        assert_eq!(a * inv, BabyBear::ONE, "a * a^(-1) must equal 1");
    }
}

#[test]
fn field_no_overflow_on_max_values() {
    let max = BabyBear::new(BABYBEAR_P - 1);
    let result = max + BabyBear::ONE;
    assert_eq!(result, BabyBear::ZERO, "(p-1) + 1 must wrap to 0");

    let result2 = max * max;
    assert!(result2.0 < BABYBEAR_P, "Product must be reduced mod p");
}

// =============================================================================
// 2. Poseidon2 collision resistance
// =============================================================================

#[test]
fn poseidon2_hash_4_to_1_no_collision_10k() {
    let mut rng = Rng::new(100);
    let mut seen = std::collections::HashSet::new();

    for _ in 0..10000 {
        let input = [
            rng.next_field(),
            rng.next_field(),
            rng.next_field(),
            rng.next_field(),
        ];
        let h = hash_4_to_1(&input);
        assert!(
            seen.insert(h),
            "Poseidon2 collision found (astronomically unlikely)"
        );
    }
}

#[test]
fn poseidon2_hash_2_to_1_no_collision_10k() {
    let mut rng = Rng::new(101);
    let mut seen = std::collections::HashSet::new();

    for _ in 0..10000 {
        let a = rng.next_field();
        let b = rng.next_field();
        let h = hash_2_to_1(a, b);
        assert!(seen.insert(h), "hash_2_to_1 collision found");
    }
}

#[test]
fn poseidon2_hash_many_no_collision_10k() {
    let mut rng = Rng::new(102);
    let mut seen = std::collections::HashSet::new();

    for i in 0..10000 {
        let len = (i % 8) + 1;
        let inputs: Vec<BabyBear> = (0..len).map(|_| rng.next_field()).collect();
        let h = hash_many(&inputs);
        assert!(seen.insert(h), "hash_many collision found");
    }
}

#[test]
fn poseidon2_hash_fact_no_collision_10k() {
    let mut rng = Rng::new(103);
    let mut seen = std::collections::HashSet::new();

    for _ in 0..10000 {
        let pred = rng.next_field();
        let terms = [rng.next_field(), rng.next_field(), rng.next_field()];
        let h = hash_fact(pred, &terms);
        assert!(seen.insert(h), "hash_fact collision found");
    }
}

#[test]
fn poseidon2_not_commutative() {
    let mut rng = Rng::new(104);
    let mut violations = 0;

    for _ in 0..1000 {
        let a = rng.next_field();
        let b = rng.next_field();
        if a == b {
            continue;
        }
        let h1 = hash_2_to_1(a, b);
        let h2 = hash_2_to_1(b, a);
        if h1 != h2 {
            violations += 1;
        }
    }

    // With overwhelming probability, hash is not commutative
    assert!(
        violations > 900,
        "hash_2_to_1 should not be commutative (found {violations}/1000 non-commutative pairs)"
    );
}

// =============================================================================
// 3. Fold delta invariant: new subset of old
// =============================================================================

#[test]
fn random_fold_deltas_preserve_subset_invariant() {
    let mut rng = Rng::new(200);

    for trial in 0..100 {
        // Create a state with random facts
        let num_facts = (rng.next_u32() % 10 + 3) as u64;
        let mut state = TokenState::new();
        let mut facts = Vec::new();

        for i in 0..num_facts {
            let fact = CommitFact::binary(
                FieldElement::from_u64(trial * 100 + i),
                FieldElement::from_u64(i * 7 + 1),
                FieldElement::from_u64(i * 13 + 2),
            );
            state.add_fact(fact);
            facts.push(fact);
        }

        // Remove a random subset
        let num_to_remove = (rng.next_u32() as u64 % num_facts).max(1);
        let mut builder = FoldDeltaBuilder::new(state.clone());
        let mut removed = Vec::new();

        for i in 0..num_to_remove {
            let idx = (rng.next_u32() as usize) % facts.len();
            if !removed.contains(&facts[idx]) {
                builder = builder.remove_fact(facts[idx]);
                removed.push(facts[idx]);
            }
        }

        if let Some(delta) = builder.build() {
            assert!(
                delta.apply_and_verify(),
                "Valid fold delta must verify (trial {trial})"
            );

            // Verify subset invariant: new state is a subset of old state
            if let Some(new_state) = delta.reconstruct_new_state(&state) {
                for fact in &facts {
                    if !removed.contains(fact) {
                        assert!(
                            new_state.contains(fact),
                            "Non-removed fact must survive attenuation (trial {trial})"
                        );
                    }
                }
                for fact in &removed {
                    assert!(
                        !new_state.contains(fact),
                        "Removed fact must be absent (trial {trial})"
                    );
                }
            }
        }
    }
}

#[test]
fn random_fold_chain_verifies() {
    let mut rng = Rng::new(201);

    for trial in 0..50 {
        // Create initial state
        let num_facts = 8u64;
        let mut state = TokenState::new();
        let mut facts: Vec<CommitFact> = Vec::new();

        for i in 0..num_facts {
            let fact = CommitFact::unary(
                FieldElement::from_u64(trial * 100 + i),
                FieldElement::from_u64(i + 1),
            );
            state.add_fact(fact);
            facts.push(fact);
        }

        // Build a chain of 2-4 fold steps
        let chain_len = (rng.next_u32() % 3 + 2) as usize;
        let mut deltas = Vec::new();
        let mut current_state = state;
        let mut remaining_facts = facts.clone();

        for _step in 0..chain_len {
            if remaining_facts.is_empty() {
                break;
            }

            let idx = rng.next_u32() as usize % remaining_facts.len();
            let to_remove = remaining_facts.remove(idx);

            if let Some(delta) = FoldDeltaBuilder::new(current_state.clone())
                .remove_fact(to_remove)
                .build()
            {
                if let Some(next_state) = delta.reconstruct_new_state(&current_state) {
                    current_state = next_state;
                    deltas.push(delta);
                } else {
                    break;
                }
            } else {
                break;
            }
        }

        if deltas.len() >= 2 {
            assert!(
                verify_fold_chain(&deltas),
                "Random fold chain must verify (trial {trial})"
            );
        }
    }
}

// =============================================================================
// 4. Trace evaluation/verification agreement
// =============================================================================

#[test]
fn evaluate_and_verify_agree_on_random_requests() {
    let rules = minimal_policy();
    let mut rng = Rng::new(300);

    // Fixed set of app names and actions
    let apps = ["app1", "app2", "app3", "app4", "app5"];
    let actions = ["read", "write", "delete", "admin", "view"];

    for trial in 0..200 {
        // Random facts: some apps with some actions
        let num_facts = (rng.next_u32() % 4 + 1) as usize;
        let mut facts = Vec::new();
        for _ in 0..num_facts {
            let app_idx = rng.next_u32() as usize % apps.len();
            let act_idx = rng.next_u32() as usize % actions.len();
            facts.push(Fact::new(
                symbol_from_str("app"),
                vec![
                    Term::Const(symbol_from_str(apps[app_idx])),
                    Term::Const(symbol_from_str(actions[act_idx])),
                ],
            ));
        }

        // Random request
        let req_app_idx = rng.next_u32() as usize % apps.len();
        let req_act_idx = rng.next_u32() as usize % actions.len();
        let request = AuthorizationRequest {
            app_id: Some(symbol_from_str(apps[req_app_idx])),
            service: None,
            action: Some(symbol_from_str(actions[req_act_idx])),
            features: vec![],
            user_id: None,
            now: 1000 + trial as i64,
        };

        let eval = Evaluator::new(facts.clone(), rules.clone());
        let trace = eval.evaluate(&request);

        // The trace from evaluate() must always verify
        assert!(
            verify_trace(&facts, &rules, &trace),
            "Evaluator-produced trace must always verify (trial {trial})"
        );
    }
}

#[test]
fn random_tampered_traces_never_verify() {
    let rules = minimal_policy();
    let mut rng = Rng::new(301);

    let facts = vec![Fact::new(
        symbol_from_str("app"),
        vec![
            Term::Const(symbol_from_str("myapp")),
            Term::Const(symbol_from_str("read,write")),
        ],
    )];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = AuthorizationRequest {
        app_id: Some(symbol_from_str("myapp")),
        service: None,
        action: Some(symbol_from_str("read")),
        features: vec![],
        user_id: None,
        now: 1000,
    };

    let base_trace = eval.evaluate(&request);
    assert!(verify_trace(&facts, &rules, &base_trace));

    // Apply random tampering and verify it's always detected
    for trial in 0..100 {
        let mut tampered = base_trace.clone();

        let tamper_type = rng.next_u32() % 5;
        match tamper_type {
            0 => {
                // Tamper conclusion
                tampered.conclusion = Conclusion::Deny;
            }
            1 => {
                // Tamper rule_id
                if let Some(step) = tampered.steps.first_mut() {
                    step.rule_id = rng.next_u32() % 1000 + 50;
                }
            }
            2 => {
                // Tamper body_fact_indices
                if let Some(step) = tampered.steps.first_mut() {
                    if !step.body_fact_indices.is_empty() {
                        step.body_fact_indices[0] = 999;
                    }
                }
            }
            3 => {
                // Tamper derived_fact predicate
                if let Some(step) = tampered.steps.first_mut() {
                    step.derived_fact.predicate = symbol_from_str("FAKE");
                }
            }
            4 => {
                // Remove all steps but claim allow
                tampered.steps.clear();
            }
            _ => unreachable!(),
        }

        assert!(
            !verify_trace(&facts, &rules, &tampered),
            "Tampered trace must not verify (trial {trial}, tamper_type {tamper_type})"
        );
    }
}

// =============================================================================
// 5. BLAKE3 leaf hash collision resistance
// =============================================================================

#[test]
fn blake3_leaf_hash_no_collision_10k() {
    use dregg_commit::hash_leaf;
    let mut rng = Rng::new(400);
    let mut seen = std::collections::HashSet::new();

    for _ in 0..10000 {
        let data: Vec<u8> = (0..32).map(|_| rng.next_u32() as u8).collect();
        let h = hash_leaf(&data);
        assert!(seen.insert(h), "BLAKE3 leaf hash collision found");
    }
}

#[test]
fn blake3_node_hash_no_collision_10k() {
    use dregg_commit::hash_node;
    let mut rng = Rng::new(401);
    let mut seen = std::collections::HashSet::new();

    for _ in 0..10000 {
        let children = [
            rng.next_bytes(),
            rng.next_bytes(),
            rng.next_bytes(),
            rng.next_bytes(),
        ];
        let h = hash_node(&children);
        assert!(seen.insert(h), "BLAKE3 node hash collision found");
    }
}

// =============================================================================
// 6. FactSet membership proof soundness under random operations
// =============================================================================

#[test]
fn factset_random_inserts_all_provable() {
    let mut rng = Rng::new(500);
    let mut fs = FactSet::new();
    let mut facts = Vec::new();

    for i in 0..100 {
        let fact = CommitFact::binary(
            FieldElement::from_u64(rng.next_u64() % 1000),
            FieldElement::from_u64(rng.next_u64() % 1000),
            FieldElement::from_u64(i),
        );
        fs.insert(fact);
        facts.push(fact);
    }

    let root = fs.root();
    for (i, fact) in facts.iter().enumerate() {
        let proof = fs.membership_proof(fact);
        assert!(
            proof.is_some(),
            "Inserted fact {i} must have membership proof"
        );
        assert!(
            FactSet::verify_membership(&root, fact, &proof.unwrap()),
            "Membership proof for fact {i} must verify"
        );
    }
}

#[test]
fn factset_random_removes_correctly_invalidate() {
    let mut rng = Rng::new(501);
    let mut fs = FactSet::new();
    let mut facts = Vec::new();

    for i in 0..50 {
        let fact = CommitFact::unary(
            FieldElement::from_u64(i),
            FieldElement::from_u64(rng.next_u64() % 500),
        );
        fs.insert(fact);
        facts.push(fact);
    }

    // Remove half randomly
    let mut removed = Vec::new();
    for _ in 0..25 {
        let idx = rng.next_u32() as usize % facts.len();
        let fact = facts.remove(idx);
        fs.remove(&fact);
        removed.push(fact);
    }

    let root = fs.root();

    // Remaining facts should still have valid proofs
    for fact in &facts {
        let proof = fs.membership_proof(fact).unwrap();
        assert!(FactSet::verify_membership(&root, fact, &proof));
    }

    // Removed facts should NOT have membership proofs
    for fact in &removed {
        assert!(fs.membership_proof(fact).is_none());
    }
}
