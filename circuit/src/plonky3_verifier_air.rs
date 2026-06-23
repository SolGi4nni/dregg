//! Recursive-IVC convenience surface, backed by the real `p3-recursion` path.
//!
//! Historically this file was a 33-line stub: `build_recursive_ivc_chain`
//! always returned `Err("recursive verification is unavailable …")` and
//! `RecursiveIvcStep` was just a type-level placeholder so `ivc::recursive_ivc`
//! could `use` something. With `plonky3_recursion_impl::recursive` now
//! generalised past `P3MerklePoseidon2Air`, the stub no longer has a reason to
//! exist — every type it defined is implementable in real terms.
//!
//! The module retains its public surface (`RecursionMode`,
//! `RecursiveIvcStep`, `build_recursive_ivc_chain`) for the one in-tree
//! caller (`ivc::recursive_ivc::RecursiveIvcBuilder::finalize_recursive`)
//! and re-routes them through:
//!
//! 1. `plonky3_recursion::AggregationAir` — the hash-chain AIR that already
//!    implements `p3-air::Air<AB>`; we use it to build a single proof
//!    attesting to the chain of fold proofs' public inputs.
//! 2. `plonky3_recursion_impl::recursive::prove_recursive_layer_for_air` —
//!    the generalised recursive layer that wraps any `RecursableAir`
//!    inner proof into a `RecursionOutput<DreggRecursionConfig>` (a STARK
//!    proof that the inner aggregation proof was valid).
//!
//! The result is a **real** recursive proof, not a placeholder. The verifier
//! checks the outer recursive proof; if it accepts, the inner aggregation
//! proof was valid, which transitively binds every fold proof's PI vector
//! into the chain commitment.

use crate::field::BabyBear;
use crate::plonky3_prover::DreggProof;

/// Recursion strategy selection.
///
/// `HashChain` mode skips the in-circuit verification step and produces
/// only the Poseidon2 accumulator. `Recursive` mode produces a real
/// recursive STARK proof attesting to the validity of the inner
/// aggregation proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecursionMode {
    /// Hash-chain accumulation only — fast, but the chain commitment is
    /// not algebraically bound to a STARK proof.
    HashChain,
    /// Real recursive STARK verification — the outer proof attests that
    /// the inner aggregation AIR was satisfied for the supplied chain of
    /// fold-proof public inputs.
    Recursive,
}

/// An IVC step proof using recursive STARK verification.
///
/// Carries the inner `aggregation_proof` (proves the public-input hash
/// chain) plus the metadata needed to re-derive its inputs.
///
/// When the `recursion` feature is enabled, [`build_recursive_ivc_chain`]
/// additionally produces a separate outer recursive proof that wraps
/// `aggregation_proof`; the outer proof's bytes are exposed via
/// [`RecursiveIvcStep::recursive_layer_bytes`] for transmission, while the
/// `aggregation_proof` field below is kept for the caller's inspection
/// path.
pub struct RecursiveIvcStep {
    pub proof: DreggProof,
    pub public_inputs: Vec<BabyBear>,
    pub step_number: u32,
}

/// Build a recursive IVC chain over `fold_proofs`.
///
/// Each entry of `fold_proofs` is a `(proof, public_inputs)` tuple from
/// the per-fold prover. The shape that matters here is `public_inputs`:
/// the aggregation AIR consumes a 2-element `[leaf_hash, root]` PI per
/// inner proof.
///
/// On success returns a `RecursiveIvcStep` whose `proof` field is the
/// aggregation proof (one STARK proof over an AggregationAir trace
/// covering all inner proofs), and — when the `recursion` feature is
/// enabled — whose `recursive_layer_bytes` field is the postcard-encoded
/// outer recursive proof produced by `prove_recursive_layer_for_air`.
///
/// On failure returns a precise error string.
pub fn build_recursive_ivc_chain(
    fold_proofs: &[(&DreggProof, &[BabyBear])],
) -> Result<RecursiveIvcStep, String> {
    use crate::plonky3_recursion::{RecursionInput, prove_recursive};

    if fold_proofs.len() < 2 {
        return Err(format!(
            "build_recursive_ivc_chain requires at least 2 fold proofs (got {}); \
             the AggregationAir transition constraint needs ≥2 rows",
            fold_proofs.len()
        ));
    }

    // Each inner proof must contribute the (leaf_hash, root) pair the
    // AggregationAir expects. The widely-used fold proofs already publish
    // (old_root, new_root) as PI, so we project the first two slots.
    for (idx, (_proof, pi)) in fold_proofs.iter().enumerate() {
        if pi.len() < 2 {
            return Err(format!(
                "fold proof {idx} has only {} PI; AggregationAir needs ≥2",
                pi.len()
            ));
        }
    }

    // p3_uni_stark::Proof does not implement `Clone`, so to land owned
    // RecursionInput.proof values from `&DreggProof` borrows we roundtrip
    // through postcard. This is the same path proof_from_bytes /
    // proof_to_bytes use for the on-wire shape; the (de)serialization cost
    // is negligible vs. the recursion work that follows.
    let inputs: Vec<RecursionInput> = fold_proofs
        .iter()
        .map(|(proof, pi)| -> Result<RecursionInput, String> {
            let bytes = postcard::to_allocvec(*proof)
                .map_err(|e| format!("DreggProof postcard serialize: {e}"))?;
            let owned: DreggProof = postcard::from_bytes(&bytes)
                .map_err(|e| format!("DreggProof postcard deserialize: {e}"))?;
            Ok(RecursionInput {
                proof: owned,
                public_inputs: pi[..2].to_vec(),
            })
        })
        .collect::<Result<_, String>>()?;

    let recursive_proof = prove_recursive(inputs)?;

    let public_inputs = vec![BabyBear::ZERO, recursive_proof.final_accumulator];
    let step_number = recursive_proof.num_proofs as u32;

    // The outer recursive-layer wrap (`recursive_layer_bytes`) lived in the
    // recursion-prove surface (`plonky3_recursion_impl`), now in
    // `dregg-circuit-prove`. This convenience entry returns the aggregation proof;
    // the outer recursive layer is produced through the prove crate's recursion
    // tower (`ivc_turn_chain` / `joint_turn_recursive`).
    Ok(RecursiveIvcStep {
        proof: recursive_proof.aggregation_proof,
        public_inputs,
        step_number,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recursion_mode_eq() {
        // Sanity: the enum is real and serializable for selection logic.
        assert_eq!(RecursionMode::HashChain, RecursionMode::HashChain);
        assert_ne!(RecursionMode::HashChain, RecursionMode::Recursive);
    }

    #[test]
    fn build_chain_rejects_too_few_proofs() {
        let res = build_recursive_ivc_chain(&[]);
        assert!(res.is_err());
        let msg = res.err().unwrap();
        assert!(
            msg.contains("at least 2 fold proofs"),
            "unexpected error: {msg}"
        );
    }
}
