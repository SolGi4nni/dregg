//! Rust witness builder for the emitted **Datalog derivation** descriptor
//! (`dregg-derivation-v1`, authored in `metatheory/Dregg2/Circuit/Emit/DerivationEmit.lean` as
//! `derivationDesc`).
//!
//! ## What this closes
//!
//! The StarkProof→descriptor-prover migration flips the last hand-STARK derivation consumer
//! (`cross_state_derivation.rs`) off the hand engine (`crate::stark` /
//! `crate::derivation_air::verify_derivation_stark`) onto the committed, byte-pinned emitted
//! descriptor served by [`crate::descriptor_by_name::descriptor_by_name`]`("dregg-derivation-v1")`.
//! Until now the only Rust producer of a descriptor-matching derivation trace lived inside
//! `circuit-prove/tests/derivation_emit_gate.rs`; there was NO production witness builder (the
//! analog of [`crate::presentation_descriptor_witness`] /
//! [`crate::membership_descriptor_4ary::membership_witness_4ary`]). This module is that builder.
//!
//! ## The trace + public inputs
//!
//! The trace is the DEPLOYED 379-col derivation trace produced by the real generator
//! ([`crate::dsl::derivation::generate_derivation_trace_dsl`], NOT a reconstruction). The descriptor
//! prover ([`crate::descriptor_ir2::prove_vm_descriptor2`]) extends each row to 386 cols and fills
//! the 7 C4 `hash_fact` chip lanes itself, so this builder returns the 379-col trace verbatim.
//!
//! The emitted descriptor pins THIRTEEN public inputs (`derivationDesc.piCount = 13`), via its
//! `pi_binding` constraints (`DerivationEmit.lean` §C6/C6b/C6c + boundaries):
//!
//! | PI       | column                         | meaning                                              |
//! |----------|--------------------------------|------------------------------------------------------|
//! | pi\[0\]    | `BODY_ROOT_START` (col 31)     | the committed `state_root` (the state-binding tooth) |
//! | pi\[1\]    | `DERIVED_HASH` (col 22)        | the published conclusion `hash_fact(head)`           |
//! | pi\[2..4\] | (unbound)                      | carried faithfully (`not_after`, `org_id`, `budget`) |
//! | pi\[5..12\]| `BODY_HASH_START + i` (cols 1..8) | the EIGHT exported body-fact hashes (C6b/C6c)      |
//!
//! The deployed generator ([`generate_derivation_trace_dsl`]) returns 6 PIs (its pre-c6c shape:
//! `[state_root, derived_hash, not_after, org_id, budget, body_hash0]`). This builder EXTENDS that to
//! the descriptor's 13 by reading all eight body-hash columns straight off row 0 — exactly the
//! columns the descriptor's C6b/C6c pins bind. A forged conclusion, state root, or body-fact hash is
//! therefore UNSAT under `verify_vm_descriptor2` (proven by the mutation canaries in
//! `derivation_emit_gate.rs` and reproduced here).

use crate::derivation_air::{DerivationWitness, MAX_BODY_ATOMS, col};
use crate::dsl::derivation::generate_derivation_trace_dsl;
use crate::field::BabyBear;

/// The emitted descriptor's dispatch key ([`crate::descriptor_by_name::descriptor_by_name`]).
pub const DERIVATION_NAME: &str = "dregg-derivation-v1";

/// The emitted descriptor's public-input count (`derivationDesc.piCount`): the state-root pin, the
/// conclusion pin, three carried slots, and the eight exported body-fact hashes.
pub const DERIVATION_PI_COUNT: usize = 13;

/// Build the **derivation** trace + the 13 public inputs the emitted `dregg-derivation-v1` descriptor
/// pins, from a [`DerivationWitness`].
///
/// The trace is the deployed 379-col DSL trace verbatim (the descriptor prover extends it to 386 and
/// fills the C4 chip lanes). The PIs are `[state_root, derived_hash, not_after, org_id, budget]`
/// followed by the eight `BODY_HASH_START..+8` columns off row 0 (pi\[5..12\]), the exact felts the
/// descriptor's C6b/C6c pins bind — so this builder is mechanical and does NOT pre-judge the
/// derivation (the descriptor's constraints are the judge).
pub fn derivation_descriptor_witness(
    witness: &DerivationWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let (trace, base_pis) = generate_derivation_trace_dsl(witness);
    debug_assert!(base_pis.len() >= 5, "the deployed generator emits >= 5 PIs");

    let mut pis = Vec::with_capacity(DERIVATION_PI_COUNT);
    // pi[0..5]: state_root, derived_hash, not_after, org_id, budget (carried faithfully).
    pis.extend_from_slice(&base_pis[..5]);
    // pi[5..13]: the eight exported body-fact hashes, read straight off the trace columns the
    // descriptor's C6b (slot 0) + C6c (slots 1..7) pins bind (cols BODY_HASH_START..+8).
    for i in 0..MAX_BODY_ATOMS {
        pis.push(trace[0][col::BODY_HASH_START + i]);
    }
    debug_assert_eq!(pis.len(), DERIVATION_PI_COUNT);
    (trace, pis)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::derivation_air::{BodyAtomPattern, CircuitRule};
    use crate::descriptor_by_name::descriptor_by_name;
    use crate::descriptor_ir2::{
        EffectVmDescriptor2, MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
    };
    use crate::poseidon2::hash_fact;
    use std::panic::AssertUnwindSafe;

    /// A simple honest firing rule: derive `derived_pred(t0, t1)` from `body_pred(t0, t1, 0)`.
    fn honest_witness() -> DerivationWitness {
        let body_pred = BabyBear::new(100);
        let derived_pred = BabyBear::new(200);
        let t0 = BabyBear::new(1000);
        let t1 = BabyBear::new(2000);
        let body_hash = hash_fact(body_pred, &[t0, t1, BabyBear::ZERO]);
        DerivationWitness {
            rule: CircuitRule {
                id: 7,
                num_body_atoms: 1,
                num_variables: 2,
                head_predicate: derived_pred,
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
            state_root: BabyBear::new(99999),
            body_fact_hashes: vec![body_hash],
            substitution: vec![t0, t1],
            derived_predicate: derived_pred,
            derived_terms: [t0, t1, BabyBear::ZERO, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        }
    }

    fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
            let proof =
                prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
            verify_vm_descriptor2(desc, &proof, pis)
        }));
        !matches!(r, Ok(Ok(())))
    }

    /// STEP 0 — dispatch serves a decodable descriptor with the expected shape.
    #[test]
    fn dispatch_serves_the_golden() {
        let desc = descriptor_by_name(DERIVATION_NAME).expect("derivation descriptor dispatches");
        assert_eq!(desc.name, DERIVATION_NAME);
        assert_eq!(desc.trace_width, 386);
        assert_eq!(desc.public_input_count, DERIVATION_PI_COUNT);
    }

    /// STEP 1 — THE POSITIVE POLE: the honest firing derivation proves through the DISPATCHED
    /// descriptor and re-verifies against the builder's 13 public inputs.
    #[test]
    fn honest_derivation_proves_and_verifies_via_dispatch() {
        let desc = descriptor_by_name(DERIVATION_NAME).expect("dispatch");
        let w = honest_witness();
        let (trace, pis) = derivation_descriptor_witness(&w);
        assert_eq!(pis.len(), DERIVATION_PI_COUNT);
        assert_eq!(pis[0], w.state_root, "pi[0] is the committed state_root");
        assert_eq!(pis[1], w.derived_hash(), "pi[1] is the conclusion");
        assert_eq!(
            pis[5], w.body_fact_hashes[0],
            "pi[5] exports body atom 0's fact hash"
        );
        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .expect("the honest derivation must prove through the dispatched descriptor");
        verify_vm_descriptor2(&desc, &proof, &pis).expect("the honest proof must re-verify");
    }

    /// STEP 2 — MUTATION CANARY (C6 conclusion pin): a forged `pi[1]` ≠ the trace's derived_hash is
    /// UNSAT. Non-vacuous against STEP 1 (the honest proof accepts).
    #[test]
    fn forged_conclusion_pi_refuses() {
        let desc = descriptor_by_name(DERIVATION_NAME).expect("dispatch");
        let (trace, pis) = derivation_descriptor_witness(&honest_witness());
        assert!(
            !rejects(&desc, &trace, &pis),
            "honest accepted (non-vacuity)"
        );
        let mut bad = pis.clone();
        bad[1] += BabyBear::ONE;
        assert!(
            rejects(&desc, &trace, &bad),
            "a forged conclusion (pi[1] != derived_hash) must be REJECTED (the C6 pin)"
        );
    }

    /// STEP 3 — MUTATION CANARY (C6b body-fact pin): a forged `pi[5]` ≠ the consumed body-fact hash
    /// is UNSAT (the body↔membership-leaf binding tooth).
    #[test]
    fn forged_body_fact_pi_refuses() {
        let desc = descriptor_by_name(DERIVATION_NAME).expect("dispatch");
        let (trace, pis) = derivation_descriptor_witness(&honest_witness());
        assert!(
            !rejects(&desc, &trace, &pis),
            "honest accepted (non-vacuity)"
        );
        let mut bad = pis.clone();
        bad[5] += BabyBear::ONE;
        assert!(
            rejects(&desc, &trace, &bad),
            "a forged body-fact hash (pi[5] != BODY_HASH_START) must be REJECTED (the C6b pin)"
        );
    }
}
