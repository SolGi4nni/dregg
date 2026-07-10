//! # R3 — the whole-history STARK leg, wired to the Lean-proven verifier.
//!
//! R0–R2 (in [`crate`]) make a hosted session tamper-evident, renter-anchored, and
//! kernel-linked — but still TRUST the executor host that produced and committed the
//! turns. R3 removes that trust for a grain's WHOLE history: fold the session's
//! finalized turns into ONE constant-size recursive-STARK aggregate
//! ([`prove_turn_chain_recursive_without_host_gate`]), light-verify it
//! ([`verify_whole_chain_proof_bytes`]), and let the LEAN-PROVEN R3 verify core
//! render the accept decision — a lying host cannot serve a fabricated or truncated
//! history under an honest-looking anchored head.
//!
//! ## The decision is the Lean-proven object, not this Rust
//!
//! The accept/reject is NOT decided here. Rust does the heavy lifting — the fold and
//! the succinct-aggregate verify — and marshals two facts onto a wire:
//!   1. the whole-chain STARK verifier's **verified-status** (did the aggregate
//!      verify), from [`verify_whole_chain_proof_bytes`]; and
//!   2. the **aggregate's committed head** (`final_root`'s head lane) vs the
//!      **R1-anchored head** the caller supplies.
//!
//! Those go to `Dregg2.Grain.R3Verify.r3VerifyFFI` (the `@[export] dregg_grain_r3_verify`
//! entry, reached via [`dregg_lean_ffi::shadow_grain_r3_verify`]) — the extracted,
//! `#assert_axioms`-clean `r3VerifyCore` (`aggregateVerified && aggregateHead ==
//! anchoredHead`). Its `"1"` IS the R3-accept, and its soundness is the PROVED
//! `r3_unfoolable` (the whole history is execution-integrity-sound AND complete, with
//! the anchored head pinned to its genuine fold).
//!
//! ## Honest scope — REDUCED to `EngineSound`, not closed
//!
//! `r3_unfoolable` is a genuine *reduction plus head-binding*, not an unconditional
//! proof of unfoolability: it reduces the grain's [`crate::WHOLE_HISTORY_GAP`] to the
//! named `RecursiveAggregation.EngineSound` boundary (the FRI/recursion legs proved
//! *outside* Lean, plus the single-turn apex's still-open reconciliation). GIVEN that
//! soundness, R3 accepts only genuinely-executed, correctly-ordered, non-truncated
//! histories bound to THIS grain's head. So R3 here is the maximal real subset *above*
//! the STARK floor — the floor itself is the carried, honest hypothesis, not a claim
//! this rung discharges.
//!
//! The producer self-anchors the light-client VK exactly as
//! `dregg_lightclient::fold_and_attest` does (the trust anchor is minted from the
//! producer's own fold); a *remote* verifier with a distributed VK anchor is the
//! light-client path, orthogonal to the R3 accept decision this renders.

use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, TurnChainError, prove_turn_chain_recursive_without_host_gate,
    verify_whole_chain_proof_bytes,
};
use dregg_circuit_prove::joint_turn_aggregation::verify_descriptor_participant;

/// **What a renter learns from a passing [`r3_verify`]** — the whole history behind
/// `anchored_head` is unfoolable (execution-integrity-sound + complete + anchored),
/// under the named `EngineSound` STARK floor, with NO host trust in the accept
/// decision (it is the Lean-proven `r3VerifyCore`'s `"1"`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R3Verified {
    /// The number of finalized turns folded into the aggregate.
    pub num_turns: usize,
    /// The R1-anchored head the caller pinned — the aggregate's committed head equals
    /// it (the head-binding tooth), so the sound history is about THIS grain's THIS
    /// head, not a swapped one.
    pub anchored_head: u32,
    /// The aggregate's committed head (`final_root` head lane) — equal to
    /// `anchored_head` on a pass.
    pub aggregate_head: u32,
}

/// Why a grain's whole history did not R3-verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum R3Error {
    /// The chain was empty — nothing to fold (the whole-chain fold needs ≥ 1 turn;
    /// the recursive aggregation needs ≥ 2 for a non-trivial tree).
    EmptyChain,
    /// The LEAN-PROVEN R3 verify core (`dregg_grain_r3_verify`) is not in the linked
    /// archive — the decision cannot be rendered by the verified object. Carries the
    /// FFI error. (Rebuild `dregg-lean-ffi` so the archive splices
    /// `Dregg2.Grain.R3Verify`.) R3 has NO Rust fallback for the accept decision by
    /// design: the decision is the Lean-proven one or it is not made.
    LeanCoreUnavailable(String),
    /// The Lean-proven R3 decision REJECTED. Either the whole-chain aggregate did not
    /// verify (`aggregate_verified == false`: a forged/dropped/reordered history has no
    /// satisfying leaf), or the aggregate's committed head is not the anchored head
    /// (the anti-ghost tooth: a valid whole-history proof cannot be re-pointed at a
    /// foreign anchor). This is the Lean-proven verifier's fail-closed verdict.
    Rejected {
        /// Whether the whole-chain STARK aggregate verified.
        aggregate_verified: bool,
        /// The aggregate's committed head (the fold's `final_root` head lane; `0` when
        /// the fold itself failed, so no head exists).
        aggregate_head: u32,
        /// The R1-anchored head the caller supplied.
        anchored_head: u32,
    },
}

impl core::fmt::Display for R3Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            R3Error::EmptyChain => {
                write!(f, "grain(R3): empty finalized-turn chain — nothing to fold")
            }
            R3Error::LeanCoreUnavailable(e) => write!(
                f,
                "grain(R3): the Lean-proven R3 verify core is not linked (rebuild dregg-lean-ffi to splice Dregg2.Grain.R3Verify): {e}"
            ),
            R3Error::Rejected {
                aggregate_verified,
                aggregate_head,
                anchored_head,
            } => write!(
                f,
                "grain(R3): the Lean-proven verifier REJECTED (aggregate_verified={aggregate_verified}, aggregate_head={aggregate_head}, anchored_head={anchored_head}) — a fabricated/truncated history or a foreign anchor"
            ),
        }
    }
}

impl std::error::Error for R3Error {}

/// The whole-chain fold + succinct-aggregate verify, producing the two facts the Lean
/// decision reads: the verified-status Bool and the aggregate's committed head. A fold
/// or verify FAILURE is not an accept — it returns `(false, 0)`, which the Lean core
/// then fail-closed rejects, so the Lean-proven verifier stays the SINGLE accept gate.
fn fold_and_status(finalized: &[FinalizedTurn]) -> (bool, u32) {
    let attempt = || -> Result<(bool, u32), TurnChainError> {
        // Selector claim from each participant's descriptor. This is the prover's
        // CLAIMED selector (which descriptor AIR to re-prove per turn), NOT a host
        // admission gate: we read the selector, we do NOT abort on a rejected
        // descriptor — a bad turn flows through as verified = false below. The
        // load-bearing check is the in-circuit leaf re-proof surfaced as the
        // verified-status, exactly why the UNGATED prover is used.
        let mut selectors = Vec::with_capacity(finalized.len());
        for (i, t) in finalized.iter().enumerate() {
            let s = verify_descriptor_participant(&t.participant)
                .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
            selectors.push(s);
        }
        // Fold WITHOUT the host gate — a forged turn has no satisfying witness at the
        // in-circuit leaf wrap, so the fold fails and no verifying root exists.
        let proof = prove_turn_chain_recursive_without_host_gate(finalized, &selectors)?;
        // The verified-status: run the whole-chain STARK verifier over the byte
        // envelope, self-anchored to the fold's own root VK (the producer mints the
        // anchor exactly as `fold_and_attest`). This IS `verify agg.root` in the model.
        let bytes = proof.to_bytes();
        let vk = proof.root_vk_fingerprint();
        let verified = verify_whole_chain_proof_bytes(&bytes, &vk).is_ok();
        // The aggregate's committed head = the final-root head lane (the scalar root
        // the whole history folds to).
        let aggregate_head = proof.final_root[0].as_u32();
        Ok((verified, aggregate_head))
    };
    attempt().unwrap_or((false, 0))
}

/// **R3 — verify a grain's WHOLE history is unfoolable, with the Lean-proven verifier
/// rendering the accept decision.**
///
/// Folds the grain's `finalized` turns into ONE recursive-STARK aggregate (ungated),
/// light-verifies it, and routes `(verified-status, aggregate head, anchored head)` to
/// the extracted, `#assert_axioms`-clean Lean `r3VerifyCore` — whose `"1"` is the
/// R3-accept, PROVED sound (reduced to the named `EngineSound` STARK floor + the R1
/// head binding, see the module doc's honest scope).
///
/// `anchored_head` is the grain's R1-anchored head (the head lane of the committed
/// final root the renter anchored). On a pass the aggregate's committed head equals it
/// — the anti-ghost tooth binds the sound history to THIS grain.
///
/// Errors: [`R3Error::Rejected`] when the Lean verifier fail-closed rejects (a
/// fabricated/truncated history, or a foreign anchor); [`R3Error::LeanCoreUnavailable`]
/// when the archive lacks the verified core (no Rust fallback — the decision is the
/// Lean-proven one or it is not made); [`R3Error::EmptyChain`] on an empty chain.
pub fn r3_verify(finalized: &[FinalizedTurn], anchored_head: u32) -> Result<R3Verified, R3Error> {
    if finalized.is_empty() {
        return Err(R3Error::EmptyChain);
    }

    // Rust does the heavy lifting: fold + succinct-aggregate verify → the two facts.
    let (verified, aggregate_head) = fold_and_status(finalized);

    // THE DECISION — the LEAN-PROVEN r3VerifyCore over the wire
    // "aggregateVerified aggregateHead anchoredHead". "1" ⟹ accept. Rust never decides
    // accept; it marshals to the verified object.
    let wire = format!("{} {} {}", verified as u8, aggregate_head, anchored_head);
    let out =
        dregg_lean_ffi::shadow_grain_r3_verify(&wire).map_err(R3Error::LeanCoreUnavailable)?;

    if out == "1" {
        Ok(R3Verified {
            num_turns: finalized.len(),
            anchored_head,
            aggregate_head,
        })
    } else {
        Err(R3Error::Rejected {
            aggregate_verified: verified,
            aggregate_head,
            anchored_head,
        })
    }
}
