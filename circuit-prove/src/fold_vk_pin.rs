//! ⚑⚑ **THE CHILD-VK IDENTITY PIN, AT EVERY 2-TO-1 FOLD IN THIS CRATE.**
//!
//! ⚠ **LABEL FIRST.** This is recursion *wiring* — `alloc_const` + `connect` over targets the
//! child verifier already allocated. It authors **no AIR** (House Law #1 holds: every AIR under
//! these towers comes out of Lean). It "proves on a box", which is **not verified and not sound**:
//! it inherits the undischarged FRI/STARK floor. The tests that exercise it are Rust case-tests —
//! not translation validation, not refinement, not verification.
//!
//! ⚑ **IT WAS CALLED `mina_fold_vk_pin` AND IT WAS NEVER MINA-SPECIFIC.** The four Mina folds were
//! only where the defect was closed first (`685a62a32`). Sixty-six further `into_recursion_input`
//! call sites carried the same hole — the leaf adapters, the joint-turn binding nodes, the cohort
//! spine, the solvency union, the accumulator, the wide K-fold tree and both apex shrinks — and all
//! of them now take this pin. The Mina-scoped name is gone rather than aliased.
//!
//! ⚑ **THE CLASSIFICATION, MEASURED.** Two call shapes exist and only one is in the hole:
//!
//! * A **leaf wrap** builds [`p3_recursion::RecursionInput::NativeBatchStark`] — the descriptor's
//!   own AIRs are handed to the verifier circuit, so its constants compile into the wrap's static
//!   op list and reach the wrap's preprocessed commitment. A leaf wrap therefore **already**
//!   separates two same-shape/different-constants descriptors, and pinning one buys nothing. It
//!   does not call `into_recursion_input` at all.
//! * A **fold** (and a single-child re-wrap) builds `RecursionInput::BatchStark` — the child is
//!   re-verified through the FIXED `CircuitTablesAir` reconstruction, so only its `CommonData`
//!   SHAPE reaches the parent's op list while its preprocessed commitment rides as a **runtime
//!   public input**, and `PublicAir`'s value columns are main-trace only. Every
//!   `into_recursion_input` site is this arm.
//!
//! Measured for the Mina pair in `circuit-prove/tests/mina_fold_vk_pin.rs` and independently, in a
//! tower with no Pasta in it, in `circuit-prove/tests/predicate_fold_vk_pin.rs` (the `≥`/`≤`/`>`
//! bridge-predicate relations: leaf wraps separate, unpinned folds do not).
//!
//! # THE HOLE THIS CLOSES, AND THE OBJECT EACH CLAIM IS ABOUT
//!
//! [`RecursionOutput::into_recursion_input`] passes `expected_preprocessed_commit: None`
//! (`recursion/src/recursion.rs` at the pinned fork rev `fc3c6df`). The field's own docblock says
//! what that costs:
//!
//! > *"without this pin its VALUE is unconstrained — a from-scratch prover could fold a proof of a
//! > DIFFERENT circuit."*
//!
//! The parent circuit's **shape** is still derived from each child's `CommonData`, so a child with
//! different *table shapes* moves the parent's `RecursionVk` and a consumer's fingerprint pin
//! refuses it. What is **not** excluded without the pin is a child of **identical table shape and
//! different preprocessed CONTENT** — and `ConstAir` puts a constant's VALUE in the preprocessed
//! commitment at this rev (`circuit-prover/src/air/const_air.rs`, whose `eval` constrains
//! `main.value[i] == prep.value[i]`; measured in `circuit-prove/tests/const_pin_probe.rs`, not read
//! off a docblock). So a descriptor with the same constraint structure and **different round
//! constants** was accepted at every fold.
//!
//! That substitution is **not hypothetical in this tree.** `dregg-pasta-fp-chainlink::v1` and
//! `dregg-pasta-fq-chainlink::v1` are byte-identical in shape (469 trace columns, 256 public
//! inputs, 922 constraints, the same five tables with the same arities and semantics) and differ
//! **only** in numeric literals — `fp_kimchi`'s constants where `fq_kimchi`'s should be, in 660 of
//! the 2 048 `pasta_program_rom` rows and 52 of the 922 constraints. Both have real Lean-emitted
//! witnesses on disk. `circuit-prove/tests/mina_fold_vk_pin.rs` builds exactly that adversary.
//!
//! # ⚑ WHAT THE PIN BUYS, STATED AT THE RESOLUTION IT HOLDS AT
//!
//! The pin `connect`s the child's preprocessed-commitment targets to `alloc_const`s of the expected
//! commitment. Two consequences, and they are different claims about different objects:
//!
//! 1. **The parent circuit is UNSAT for a child whose commitment differs from the pinned value.**
//!    There is no satisfying witness, so there is no parent proof. This is the *circuit's* refusal:
//!    no host pre-flight compares the two, deliberately, because a host check that fires first
//!    would make the in-circuit constraint untested.
//! 2. **The pinned VALUE reaches the parent's [`RecursionVk`] fingerprint.** `alloc_const`'s value
//!    is a preprocessed column at this rev, and `recursion_vk_fingerprint` hashes
//!    `preprocessed_commitment`. So a prover who pins a *different* child VK does not get the same
//!    parent VK, and a consumer holding the honest fingerprint anchor refuses the root.
//!
//! ⚑ (2) is why [`FoldVkPins::tracked`] is not a tautology even though it reads the expectation off
//! the very children being folded. Read alone, a tracked pin says only *"this parent folded the
//! children it folded"*. Read together with a consumer's fingerprint anchor it says *"this parent
//! folded children whose circuits are the ones the anchored VK was minted over"* — which is the
//! property that was missing. `Accumulator::pinned_running_vk` takes the same position and says why
//! a *frozen* pin would be wrong there: the running aggregation VK passes through a finite
//! transient before it reaches its fixed point, so a frozen constant would falsely refuse honest
//! folds at low depth.
//!
//! ⚠ **What a tracked pin does NOT do:** it does not, by itself, name WHICH circuit. Naming is the
//! consumer's fingerprint comparison. A caller that wants the pin to name a circuit *inside* the
//! fold passes [`FoldVkPins::new`] with a recorded commitment instead.
//!
//! # ⚑ MEASURED 2026-08-07, release, on the Fq/Fp chain-link pair
//!
//! `circuit-prove/tests/mina_fold_vk_pin.rs`, both teeth green:
//!
//! ```text
//!   §0  descriptors: trace_width 469 · PIs 256 · constraints 922 · ROM rows 2048 — IDENTICAL
//!       DIFFER: 660/2048 ROM rows, 52/922 constraints (JSON skeletons agree up to literals)
//!   §1                                              run A        run B
//!       CONTROL   (Fp children, Fp pins)  LANDED   20 607 ms   10 454 ms
//!       ADVERSARY (Fp children, Fq pins)  REFUSED     558 ms      452 ms
//!       HONEST    (Fq children, Fq pins)  LANDED   19 515 ms    9 879 ms
//! ```
//!
//! ⚠ **TWO RUNS, TWENTY MINUTES APART, A FACTOR OF TWO.** Run A shared the box with several sibling
//! cargo jobs (load ~40); run B did not. Quote the BAND or re-measure — a single number off this
//! tree has been wrong in both directions.
//!
//! The refusal is `WitnessConflict { witness_id: WitnessId(472), … }` out of the aggregation
//! layer's witness solver — the circuit, not a host pre-flight — and it costs ~5% of an honest fold
//! because it fails during witness generation rather than in the prover.
//!
//! ⚑ **AND ONE MEASUREMENT THAT CORRECTS THE STORY.** A *leaf-wrap* `RecursionVk` fingerprint DOES
//! separate the two descriptors (`705a99b1…` vs `a4c22d13…`) — the leaf-wrap circuit compiles the
//! inner AIR's constants into its own op list, so they land in its preprocessed commitment. It is
//! the *fold's parent* VK that does not separate them unpinned: the child's commitment rides as a
//! runtime PUBLIC input, and `PublicAir`'s value columns are main-trace only. So the hole was never
//! "nothing anywhere can tell an Fp leaf from an Fq one"; it was "**a fold cannot**, and a fold root
//! is what a consumer anchors." With the pins in, the two folds' parent VKs differ
//! (`e5bcc49a…` vs `78788d92…`).

use p3_commit::Pcs;
use p3_recursion::RecursionOutput;
use p3_uni_stark::StarkGenericConfig;

use crate::plonky3_recursion_impl::recursive::{DIGEST_ELEMS, DreggRecursionConfig};

/// The runtime preprocessed-commitment value type for the recursion config — a child proof's
/// VK-identity core (a Merkle cap). This is what the in-band pin constrains.
pub type RecursionCommit = <<DreggRecursionConfig as StarkGenericConfig>::Pcs as Pcs<
    <DreggRecursionConfig as StarkGenericConfig>::Challenge,
    <DreggRecursionConfig as StarkGenericConfig>::Challenger,
>>::Commitment;

/// The number of field elements one child's VK pin costs: one `alloc_const` **and** one `connect`
/// per element of the child's preprocessed Merkle commitment. A 2-to-1 fold pays this twice.
///
/// Stated as a constant because "what does the pin cost" is the first question a reader has and the
/// answer should not require counting a loop in a vendored crate
/// (`recursion/src/verifier/batch_stark.rs`, `pin_preprocessed_commit`).
pub const VK_PIN_FELTS_PER_CHILD: usize = DIGEST_ELEMS;

/// The expected child VK commitments a 2-to-1 fold pins its two children to.
///
/// There is deliberately **no** `Option` and no "unpinned" variant. A fold that cannot say which
/// circuit its children came from is the hole this type exists to close, and keeping a no-op
/// alternative would leave the next reader a way back into it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoldVkPins {
    /// The expected preprocessed commitment of the LEFT child.
    pub left: RecursionCommit,
    /// The expected preprocessed commitment of the RIGHT child.
    pub right: RecursionCommit,
}

impl FoldVkPins {
    /// Pin to two RECORDED commitments — the strong form. The pin then names a circuit inside the
    /// fold rather than deferring the naming to a consumer's fingerprint comparison.
    pub fn new(left: RecursionCommit, right: RecursionCommit) -> Self {
        Self { left, right }
    }

    /// ⚑ **TRACKED** pins, read off the two children being folded — the form an honest driver uses
    /// when it has no recorded anchor to hand.
    ///
    /// Read in isolation this is a tautology and the name says so. Its content comes from the
    /// module header's consequence (2): the pinned values land in the parent's `RecursionVk`, so a
    /// substituted child yields a DIFFERENT parent VK and a consumer's anchor refuses the root.
    /// Without any pin the parent VK is byte-identical under the substitution, which is the whole
    /// defect.
    ///
    /// Fails closed if either child carries no preprocessed commitment: an unpinnable child is
    /// refused rather than folded unpinned.
    pub fn tracked(
        left: &RecursionOutput<DreggRecursionConfig>,
        right: &RecursionOutput<DreggRecursionConfig>,
    ) -> Result<Self, String> {
        Ok(Self {
            left: child_vk_commit(left, "left child")?,
            right: child_vk_commit(right, "right child")?,
        })
    }
}

/// A child's genuine preprocessed commitment (its VK-identity core), or an error naming the role.
///
/// ⚠ Fail-closed on `None`. A recursion layer always has preprocessed columns; a child that has
/// none is a shape this tower does not produce, and folding it unpinned would silently restore the
/// hole for exactly the proof that is strangest.
pub fn child_vk_commit(
    output: &RecursionOutput<DreggRecursionConfig>,
    role: &str,
) -> Result<RecursionCommit, String> {
    output.running_preprocessed_commit().ok_or_else(|| {
        format!(
            "{role} carries no preprocessed commitment, so its VK identity cannot be pinned; \
             refusing to fold it unpinned"
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The pin's width is the digest width, and it is not zero — a zero-width pin would connect
    /// nothing and this module would be decoration.
    #[test]
    fn the_pin_is_one_const_and_one_connect_per_digest_element() {
        assert_eq!(VK_PIN_FELTS_PER_CHILD, 8);
        assert_eq!(VK_PIN_FELTS_PER_CHILD, DIGEST_ELEMS);
        assert!(VK_PIN_FELTS_PER_CHILD > 0);
    }
}
