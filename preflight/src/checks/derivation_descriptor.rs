//! The MIGRATED derivation+membership composite — preflight's replacement for the
//! deleted `dregg_circuit::{prove,verify}_authorization_with_membership`.
//!
//! ## What was deleted, and what replaces it
//!
//! `prove_authorization_with_membership` (`circuit/src/body_membership.rs`, removed by
//! the stark-kill campaign — `f04b2dd1e`, "DELETE the hand-rolled STARK engine") composed
//! two legs on the hand engine (`crate::stark`, gone):
//!
//!   1. a derivation STARK over `MultiStepDerivationAir`, and
//!   2. one Merkle-membership STARK per body fact, under the shared `state_root`,
//!      plus the binding that every claimed body-fact hash carries a membership proof.
//!
//! Both legs have REAL successors in the descriptor world the campaign moved to — the
//! Lean-emitted, byte-pinned descriptors served by `descriptor_by_name`, proven by
//! `prove_vm_descriptor2` / checked by `verify_vm_descriptor2`:
//!
//!   1. `dregg-derivation-v1` (`metatheory/Dregg2/Circuit/Emit/DerivationEmit.lean`),
//!      driven by the production witness builder
//!      [`dregg_circuit::derivation_witness::derivation_descriptor_witness`]. Its 13 pinned
//!      public inputs are `[state_root, derived_hash, not_after, org_id, budget,
//!      body_hash0..7]` — so the state root, the conclusion, AND every consumed body-fact
//!      hash are pinned in-circuit (C6/C6b/C6c).
//!   2. `merkle-membership::poseidon2-4ary-general-depth{N}`
//!      ([`dregg_circuit::membership_descriptor_4ary`]), whose public inputs are
//!      `[leaf, root]`.
//!
//! [`prove_verify_step_with_membership`] rebuilds the composite from those two: it proves
//! and verifies the step's derivation descriptor, then for each body fact proves and
//! verifies its 4-ary membership descriptor and BINDS the two — the membership `leaf` must
//! equal the derivation's exported `body_hash{i}` pin and the membership `root` must equal
//! the derivation's `state_root` pin. That is the same tooth the deleted composite
//! verifier enforced, now over cryptographic descriptor proofs instead of the hand engine.
//!
//! ## What is NOT reconstructed (named, not faked)
//!
//! The deleted composite's derivation leg ran over `MultiStepDerivationAir` — a MULTI-step
//! AIR that chained steps by an accumulated hash. **No emitted descriptor for that chaining
//! exists** (`circuit/src/descriptor_by_name.rs` registers a single-step
//! `dregg-derivation-v1`; there is no multi-step twin). So a multi-step check here proves
//! each step INDIVIDUALLY, bound to the shared `state_root` by each step's own pi[0] pin.
//! The in-circuit accumulated-hash chain across steps is NOT proven by this helper, and no
//! caller may claim it is. The remaining non-cryptographic multi-step surface
//! (`multi_step_witness::prove_authorization` → `ConstraintProof`) is a trace digest, not a
//! proof (its own module doc says so), so it is deliberately NOT used here.

use dregg_circuit::BodyFactMerkleProof;
use dregg_circuit::derivation_air::DerivationWitness;
use dregg_circuit::derivation_witness::{
    DERIVATION_NAME, DERIVATION_PI_COUNT, derivation_descriptor_witness,
};
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::membership_descriptor_4ary::{
    PI_LEAF, PI_ROOT, membership_descriptor_of_depth_4ary, membership_witness_4ary,
};

/// pi index of the derivation descriptor's `state_root` pin.
const PI_STATE_ROOT: usize = 0;
/// pi index of the derivation descriptor's conclusion (`hash_fact(head)`) pin.
const PI_DERIVED_HASH: usize = 1;
/// pi index of the derivation descriptor's first exported body-fact hash (C6b); slots
/// `PI_BODY_HASH_START + i` export body atom `i` (C6c).
const PI_BODY_HASH_START: usize = 5;

/// Prove + verify ONE derivation step through the emitted `dregg-derivation-v1` descriptor,
/// and prove + verify a 4-ary Merkle-membership descriptor for each body fact it consumes,
/// binding each membership `[leaf, root]` to the derivation's exported body-fact pin and
/// state-root pin.
///
/// Returns the total proof size in bytes across all descriptor proofs.
pub fn prove_verify_step_with_membership(
    step: &DerivationWitness,
    body_proofs: &[BodyFactMerkleProof],
) -> Result<usize, String> {
    let desc = descriptor_by_name(DERIVATION_NAME)
        .ok_or_else(|| format!("no `{DERIVATION_NAME}` descriptor registered"))?;
    if desc.public_input_count != DERIVATION_PI_COUNT {
        return Err(format!(
            "`{DERIVATION_NAME}` pi count drifted: descriptor says {}, builder says {DERIVATION_PI_COUNT}",
            desc.public_input_count
        ));
    }

    let (trace, pis) = derivation_descriptor_witness(step);
    if pis.len() != DERIVATION_PI_COUNT {
        return Err(format!(
            "derivation witness produced {} PIs, expected {DERIVATION_PI_COUNT}",
            pis.len()
        ));
    }
    if pis[PI_STATE_ROOT] != step.state_root {
        return Err("derivation pi[0] is not the witness state_root".into());
    }
    if pis[PI_DERIVED_HASH] != step.derived_hash() {
        return Err("derivation pi[1] is not the witness conclusion hash".into());
    }

    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .map_err(|e| format!("honest derivation failed to prove via `{DERIVATION_NAME}`: {e}"))?;
    verify_vm_descriptor2(&desc, &proof, &pis)
        .map_err(|e| format!("`{DERIVATION_NAME}` verifier rejected an honest proof: {e}"))?;
    let mut total_bytes = postcard::to_allocvec(&proof)
        .map_err(|e| format!("encode derivation proof: {e}"))?
        .len();

    // Every body fact the step consumes must carry a membership proof whose leaf is the
    // derivation's EXPORTED body-fact pin and whose root is the derivation's state root.
    for (i, &fact_hash) in step.body_fact_hashes.iter().enumerate() {
        let pinned = *pis
            .get(PI_BODY_HASH_START + i)
            .ok_or_else(|| format!("body atom {i} exceeds the descriptor's exported pins"))?;
        if pinned != fact_hash {
            return Err(format!(
                "body atom {i}: descriptor pin {} != witness body fact hash {}",
                pinned.0, fact_hash.0
            ));
        }

        let mp = body_proofs
            .iter()
            .find(|p| p.fact_hash == fact_hash)
            .ok_or_else(|| {
                format!(
                    "no Merkle proof provided for body fact hash {}",
                    fact_hash.0
                )
            })?;

        total_bytes += prove_verify_membership(mp, pis[PI_STATE_ROOT], pinned)?;
    }

    Ok(total_bytes)
}

/// Prove + verify one 4-ary Merkle-membership descriptor proof, asserting its `[leaf, root]`
/// public inputs are exactly `(expected_leaf, expected_root)`.
fn prove_verify_membership(
    mp: &BodyFactMerkleProof,
    expected_root: BabyBear,
    expected_leaf: BabyBear,
) -> Result<usize, String> {
    let depth = mp.siblings.len();
    let (trace, pis) = membership_witness_4ary(mp.fact_hash, &mp.siblings, &mp.positions)
        .map_err(|e| format!("membership witness for fact {}: {e}", mp.fact_hash.0))?;
    if pis[PI_LEAF] != expected_leaf {
        return Err(format!(
            "membership leaf {} != the derivation's exported body-fact pin {}",
            pis[PI_LEAF].0, expected_leaf.0
        ));
    }
    if pis[PI_ROOT] != expected_root {
        return Err(format!(
            "membership root {} != the derivation's state_root pin {} — the fact is not in the \
             proven state",
            pis[PI_ROOT].0, expected_root.0
        ));
    }

    let desc = membership_descriptor_of_depth_4ary(depth);
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .map_err(|e| format!("honest depth-{depth} membership failed to prove: {e}"))?;
    verify_vm_descriptor2(&desc, &proof, &pis)
        .map_err(|e| format!("depth-{depth} membership verifier rejected an honest proof: {e}"))?;
    Ok(postcard::to_allocvec(&proof)
        .map_err(|e| format!("encode membership proof: {e}"))?
        .len())
}

/// ADVERSARIAL tooth: the derivation descriptor must REFUSE a forged conclusion pin.
///
/// Proves the step honestly (non-vacuity), then re-checks with `pi[1]` (the C6 conclusion
/// pin) incremented and asserts the prove-or-verify path refuses. A preflight gate that
/// only ever shows honest-accept cannot tell a real verifier from `Ok(())`.
pub fn forged_conclusion_is_refused(step: &DerivationWitness) -> Result<(), String> {
    let desc = descriptor_by_name(DERIVATION_NAME)
        .ok_or_else(|| format!("no `{DERIVATION_NAME}` descriptor registered"))?;
    let (trace, pis) = derivation_descriptor_witness(step);

    let mut forged = pis.clone();
    forged[PI_DERIVED_HASH] += BabyBear::ONE;
    let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let p = prove_vm_descriptor2(&desc, &trace, &forged, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(&desc, &p, &forged)
    }));
    if matches!(refused, Ok(Ok(()))) {
        return Err(
            "`dregg-derivation-v1` ACCEPTED a forged conclusion pin (pi[1] != derived_hash)".into(),
        );
    }
    Ok(())
}
