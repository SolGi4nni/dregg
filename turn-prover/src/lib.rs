//! `dregg-turn-prover`: proof PRODUCTION for dregg turns.
//!
//! # Why this is a CRATE and not a `feature = "prover"`
//!
//! A `#[cfg(feature = "prover")]` arm inside a shared `match` (or a `#[cfg]`
//! struct field) goes non-exhaustive / shape-divergent the moment a new enum
//! variant is added — but the omission compiles **green** in `cargo build -p
//! dregg-turn`, because cargo type-checks the crate under *one* resolved
//! feature set and never looks at the arms it did not select. The breakage
//! surfaces only in whatever downstream crate's feature resolution happens to
//! light that path up (this campaign started from a `ShieldedNoteInserted`
//! match gap that first appeared four crates away, in `dreggnet-game-board`'s
//! test target).
//!
//! This crate is **always compiled as itself**. There is no `prover` feature
//! here and nothing in it is `#[cfg]`-gated on one. A shape change in
//! `dregg-turn` or `dregg-circuit-prove` is therefore a compile error *at the
//! source*, inside `cargo build -p dregg-turn-prover`.
//!
//! # Dependency direction
//!
//! `dregg-turn-prover → dregg-turn` (its **public** interface only) `+
//! dregg-circuit-prove + dregg-circuit`. **`dregg-turn` must never depend on
//! `dregg-turn-prover`.** Core `turn` stays prover-free: it is the wasm/zkvm
//! card and the seL4 verifier-PD floor. Where the executor needs prover
//! behavior it takes an injected implementation of a trait defined in core and
//! **fails closed when nothing is injected** (see
//! `docs/reference/TURN-PROVER-CRATE-EXTRACTION-DESIGN.md` §2).
//!
//! # What lives here (PR1)
//!
//! - [`aggregate_bilateral_prover`] — the Stage 7-γ.2 joint bilateral
//!   aggregation prover/verifier, the cross-side-existence leg, and the
//!   bundle tree-fold.
//! - [`descent_census_custom`], [`private_preference_custom`],
//!   [`private_graph_rewrite_custom`], [`private_graph_rewrite_history`] —
//!   the proof-carrying `Custom`-leaf effect verifiers and the private
//!   graph-rewrite receipt history. Self-contained wrappers over
//!   `dregg-circuit-prove` cells; they touch no `dregg-turn` internals.
//!
//! # What PR2 added — the two WOVEN groups
//!
//! These are code the core executor *calls into* mid-`apply`, so they could not
//! simply relocate. They ride the executor's dependency-inversion seam instead —
//! the trait is defined in core `dregg-turn`, the implementation is here, and the
//! node/SDK injects it at startup. **Nothing injected ⇒ the effect fails closed**,
//! the same behavior the old `#[cfg(not(feature = "prover"))]` stubs gave.
//!
//! - [`shielded_transfer_verifier`] — the shielded-transfer hiding uni-STARK +
//!   Pedersen conservation/range gates. VERIFY-RETURNS-VALUE: it never receives
//!   the `LedgerJournal`, so `JournalEntry` stays `pub(crate)` in core.
//! - [`faithful_note_spend_exact_v3_verifier`] / [`faithful_note_spend_verifier`]
//!   — the predicate-specific HidingFRI verifiers. The exact-v3 one is installed
//!   as the process proof authority by
//!   [`install_code_owned_exact_fnsp_v3_verifier`]; the acceptance TOKEN and the
//!   executor admission slot are unconditional core state.
//!
//! # What PR3 added — and the DELETION it enabled
//!
//! The last four prover surfaces moved here, after which `dregg-turn`'s `prover`
//! feature and its `dregg-circuit-prove` dependency edge were **deleted**: core
//! `dregg-turn` now links no prove crate at all and carries zero
//! `#[cfg(feature = "prover")]` sites.
//!
//! - [`rotation_witness`] (Group A) — the seven per-turn rotated/welded leg
//!   MINTING recipes. They ride `dregg_turn::rotation_witness`'s public
//!   derivation (`produce`, `empty_revoked_root_8`, `sender_membership_teeth`)
//!   plus the `umem` projection module; nothing private was exposed.
//! - [`recursive_bundle`] (Group C) — the Golden-Vision recursive compression
//!   PRODUCER. The `WitnessedReceipt` / `WitnessBundle` / `RecursiveProofVariant`
//!   TYPES stay in core; the producer reaches core through
//!   [`install_recursive_witness_producer`], and nothing installed ⇒ no recursive
//!   variant attached (fail-closed by absence).
//! - [`proven_receipt`] — `mint_transfer_proven_receipt`, the shared single
//!   proving recipe for a genuine `EffectVmProof`. The `ProvenReceipt` type and
//!   the whole `TurnProven` RESOLVER stay in core.
//! - [`custom_program_proofs`] — `Turn::with_custom_program_proofs`, now the
//!   [`TurnCustomProofsExt`] extension trait (the `custom_program_proofs` FIELD
//!   and the `CustomProgramProof` wire type stay in core).

use std::sync::Arc;

pub mod aggregate_bilateral_prover;
pub mod custom_program_proofs;
pub mod descent_census_custom;
pub mod faithful_note_spend_exact_v3_verifier;
pub mod faithful_note_spend_verifier;
pub mod private_graph_rewrite_custom;
pub mod private_graph_rewrite_history;
pub mod private_preference_custom;
pub mod proven_receipt;
pub mod recursive_bundle;
pub mod rotation_witness;
pub mod shielded_transfer_verifier;

pub use aggregate_bilateral_prover::{
    AggregatedBundle, AggregatedTree, CrossSideExistenceProof, prove_aggregated_bundle,
    prove_aggregated_tree, prove_cross_side_existence, verify_aggregated_bundle,
    verify_aggregated_tree, verify_cross_side_existence,
};
pub use custom_program_proofs::TurnCustomProofsExt;
pub use faithful_note_spend_exact_v3_verifier::FaithfulNoteSpendExactV3Verifier;
pub use faithful_note_spend_verifier::FaithfulNoteSpendVerifier;
pub use proven_receipt::mint_transfer_proven_receipt;
pub use recursive_bundle::{
    CircuitRecursiveWitnessProducer, from_components_strict_recursive, produce_recursive_variant,
};
pub use shielded_transfer_verifier::CircuitShieldedTransferVerifier;

/// Install the code-owned exact FNSP-v3 verifier as this process's ONE proof
/// authority, so `dregg_turn::verify_faithful_note_spend_exact_v3_acceptance` can
/// mint acceptance tokens.
///
/// Idempotent: a second call (or a call after some other authority was installed)
/// returns `Err` and changes nothing — the core slot is install-once by design, so
/// no later crate can downgrade proof authority mid-run. A node that never calls
/// this cannot mint an exact-v3 acceptance at all, and the executor's exact-v3
/// `NoteSpend` route therefore refuses every carrier: FAIL-CLOSED.
pub fn install_code_owned_exact_fnsp_v3_verifier()
-> Result<(), dregg_turn::ExactFnspV3ProofAuthorityAlreadyInstalled> {
    dregg_turn::install_exact_fnsp_v3_proof_authority(Arc::new(
        FaithfulNoteSpendExactV3Verifier::new(),
    ))
}

/// Install the Golden-Vision recursive-compression producer for this process, so
/// `WitnessedReceipt::from_components_with_compression(.., recursive_compress =
/// true)` actually attaches a [`RecursiveProofVariant`](dregg_turn::witnessed_receipt::RecursiveProofVariant).
///
/// Install-once, like the exact-v3 proof authority: a second call returns `Err`
/// and changes nothing. A process that never calls this simply emits
/// Silver-Vision (inline-trace) receipts — the identical behavior to the deleted
/// `#[cfg(not(feature = "prover"))]` build. Callers that REQUIRE the Golden form
/// use [`from_components_strict_recursive`], which needs no installation.
pub fn install_recursive_witness_producer()
-> Result<(), dregg_turn::RecursiveWitnessProducerAlreadyInstalled> {
    dregg_turn::install_recursive_witness_producer(Arc::new(CircuitRecursiveWitnessProducer::new()))
}
