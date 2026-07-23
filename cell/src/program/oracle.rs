//! The CONSTRAINT-ORACLE seam — a runtime-installed decision procedure for the Lean-evaluated
//! `StateConstraint` / `HeapAtom` subset (the PURE arms, the bounded CONTEXT arms, and the
//! `AnyOf` / `AllOf` combinators over them), so the deployed node routes
//! per-constraint admission through the verified Lean `dregg_constraint_admits`
//! (`Dregg2.Exec.DeployedConstraint.admits`) instead of the hand-authored Rust `match` in
//! [`eval`](super::eval). This closes the game-proof LARP-audit's reality-gate: the deployed
//! admission decision for the subset is COMPUTED BY the Lean source, not a parallel-disconnected copy.
//!
//! ## Why a runtime seam (and not a direct FFI call in `eval.rs`)
//!
//! `dregg-cell` compiles to **wasm32** AND the **SP1 zkVM guest** (`circuit/sp1-guest`), neither of
//! which can link `libdregg_lean.a`. So `cell` CANNOT call the Lean FFI directly (a hard link would
//! break both builds). This is the same trait-seam architecture the tree already uses for
//! [`intent::IntentVerifiedGate`]: the crates that DO link the archive (`dregg-exec-lean`, installed
//! by `dregg-node` at startup) install the Lean backend; `cell`'s own builds (and wasm / zkVM) keep
//! the Rust guest-path evaluator in [`eval`](super::eval). A differential gate
//! (`dregg-lean-ffi::tests::deployed_constraint_probe` + `deployed_constraint_differential`) pins the
//! Lean decision equal to the Rust one across the subset (including the two boundaries the audit found
//! divergent); the reality-gate canary proves the node's live decision is the Lean source.

use std::sync::OnceLock;

use super::{ProgramError, StateConstraint, TransitionMeta};
use crate::preconditions::EvalContext;
use crate::state::CellState;

/// A decision procedure for the Lean-evaluated constraint subset.
///
/// [`admits`](ConstraintOracle::admits) returns `Some(decision)` for the variants it handles
/// (routing them through the verified Lean evaluator) and `None` for variants OUTSIDE the subset,
/// which the caller then evaluates in Rust. This lets the collapse land the decidable subset without
/// stranding the witness/crypto variants.
///
/// ## The three classes (`metatheory/Dregg2/Exec/DeployedConstraint.lean`)
///
/// * **(a) PURE** — reads only `(old, new)` registers / heap / balance. Lean-evaluated.
/// * **(b) CONTEXT** — additionally reads the SMALL, TYPED slice
///   `{ block_height, sender, delegation_epoch }` of [`EvalContext`] / [`TransitionMeta`]. That slice
///   is marshalled EXPLICITLY (each absence is a first-class wire token), so an absent context
///   produces the deployed `MissingContextField` verdict — fail-closed, never a silent admit.
///   Lean-evaluated.
/// * **(c) WITNESS / CRYPTO / EXECUTOR-STATE** — dispatches to a hash, a proof verifier, a DSL
///   runtime, a peer cell, or an executor-side counter. NOT Lean-evaluated: this is the NAMED
///   TRUSTED-RUST SLOT, enumerated exhaustively (no wildcard) in
///   `dregg-exec-lean::constraint_oracle::encode_constraint`, so a NEW `StateConstraint` variant
///   fails the BUILD until it is classified.
pub trait ConstraintOracle: Send + Sync {
    /// Decide `constraint` against `(old_state, new_state)` with the turn's evaluation context and
    /// transition meta in scope. `Some(Ok(()))` admits, `Some(Err(_))` refuses with the deployed
    /// [`ProgramError`] variant, `None` = "not my subset — evaluate in Rust".
    fn admits(
        &self,
        constraint: &StateConstraint,
        new_state: &CellState,
        old_state: Option<&CellState>,
        ctx: Option<&EvalContext>,
        meta: &TransitionMeta,
    ) -> Option<Result<(), ProgramError>>;
}

static ORACLE: OnceLock<Box<dyn ConstraintOracle>> = OnceLock::new();

/// Install the process-wide constraint oracle (once). Called by `dregg-exec-lean` / `dregg-node` at
/// startup with the Lean-backed backend so the deployed executor's pure-subset admission is computed
/// by `dregg_constraint_admits`. Returns `Err` if an oracle is already installed.
pub fn install_constraint_oracle(oracle: Box<dyn ConstraintOracle>) -> Result<(), &'static str> {
    ORACLE
        .set(oracle)
        .map_err(|_| "constraint oracle already installed")
}

/// The installed oracle, if any. `None` on `cell`'s own / wasm / zkVM builds (no Lean backend linked),
/// where [`eval`](super::eval)'s Rust evaluator is the path.
#[inline]
pub(crate) fn installed_oracle() -> Option<&'static dyn ConstraintOracle> {
    ORACLE.get().map(|b| b.as_ref())
}

/// Whether a constraint oracle is installed (the deployed node routes the pure subset through Lean).
/// Used by the reality-gate tests to confirm the collapse is armed.
pub fn constraint_oracle_installed() -> bool {
    ORACLE.get().is_some()
}
