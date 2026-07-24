//! The CROSS-CELL CONSERVATION-ORACLE seam — a runtime-installed decision procedure for the per-asset
//! `Σδ = 0` value-conservation gate, so the deployed executor routes conservation through the verified,
//! Lean-authored `dregg_cross_cell_conserves` (`Dregg2.Circuit.CrossCellConserveDecision.conservesFFI`)
//! instead of the hand-written Rust `dregg_circuit::block_conservation::BlockConservation` twin. This is
//! House Law #1 for the inflation boundary: the deployed conservation decision is COMPUTED BY the Lean
//! source — proved EQUAL to the committed `Dregg2.Circuit.CrossCellConservation` AIR boundary
//! (`creditSum = debitSum` per asset) by `CrossCellConserveRefine.decision_conserves_iff_air_boundary` /
//! `satisfied_imp_decision_conserves` — not a parallel-disconnected Rust copy that can drift (it already
//! drifted once into the asset-blind inflation bug).
//!
//! ## Why a runtime seam (and not a direct FFI call in `atomic.rs`)
//!
//! `dregg-turn` compiles to **wasm32** AND the **zkVM guest**, neither of which can link
//! `libdregg_lean.a`. So `turn` CANNOT call the Lean FFI directly (a hard link would break both builds).
//! This is the same trait-seam architecture the tree uses for the `ConstraintOracle`
//! (`dregg_cell::program::oracle`) and the distributed gates: the crate that DOES link the archive
//! (`dregg-exec-lean`, installed by `dregg-node` at startup) installs the Lean backend; `turn`'s own
//! builds (and wasm / zkVM) keep the labeled Rust fallback in [`super::atomic`].
//!
//! ## Fallback posture (stated plainly)
//!
//! * **Oracle installed** (deployed native node via `dregg-exec-lean`): the verified Lean decision is
//!   authoritative — the executor NEVER decides conservation in Rust.
//! * **No oracle, wasm / zkVM guest** (cannot link Lean): the per-asset boundary is decided by the
//!   LABELED, NON-VERIFIED Rust arithmetic in [`super::atomic`] — a degradation, not "the check".
//! * **No oracle, native (stale archive / startup did not register)**: currently the same labeled Rust
//!   fallback runs (the interim). Flipping this to fail-CLOSED (and deleting the Rust `BlockConservation`
//!   decision outright) is the final step, gated on verifying the archive relink fires the oracle.

use std::sync::OnceLock;

/// A per-asset conservation decision procedure over the turn's `(asset, signed_delta)` rows plus
/// declared mint/burn supply rows (a mint is `+mag`, a burn `-mag`).
///
/// [`conserves`](ConservationOracle::conserves) returns `Ok(())` when EVERY asset's signed delta sum is
/// zero (the block conserves — ADMIT) and `Err((asset, imbalance))` for the FIRST imbalanced asset in
/// ascending key order (the same order as the Rust twin's `BTreeMap`, so a routed
/// [`AtomicTurnError::PerAssetConservationViolation`](super::atomic::AtomicTurnError) is byte-identical
/// to the pre-route path).
pub trait ConservationOracle: Send + Sync {
    /// Decide per-asset conservation. `rows`: `(asset_class, signed_net_delta)` per verified per-cell
    /// contribution. `supply`: `(asset_class, signed_declared_supply_change)`. `Ok(())` admits;
    /// `Err((asset, imbalance))` refuses with the first imbalanced asset.
    fn conserves(&self, rows: &[(u32, i64)], supply: &[(u32, i64)]) -> Result<(), (u32, i64)>;
}

static ORACLE: OnceLock<Box<dyn ConservationOracle>> = OnceLock::new();

/// Install the process-wide conservation oracle (once). Called by `dregg-exec-lean` / `dregg-node` at
/// startup with the Lean-backed backend so the deployed executor's per-asset `Σδ=0` decision is computed
/// by `dregg_cross_cell_conserves`. Returns `Err` if an oracle is already installed.
pub fn install_conservation_oracle(
    oracle: Box<dyn ConservationOracle>,
) -> Result<(), &'static str> {
    ORACLE
        .set(oracle)
        .map_err(|_| "conservation oracle already installed")
}

/// The installed oracle, if any. `None` on `turn`'s own / wasm / zkVM builds (no Lean backend linked),
/// where [`super::atomic`]'s labeled Rust fallback is the path.
#[inline]
pub(crate) fn installed_conservation_oracle() -> Option<&'static dyn ConservationOracle> {
    ORACLE.get().map(|b| b.as_ref())
}

/// Whether a conservation oracle is installed (the deployed node routes the per-asset `Σδ=0` gate through
/// the verified Lean decision). Used by reality-gate tests to confirm the route-through is armed.
pub fn conservation_oracle_installed() -> bool {
    ORACLE.get().is_some()
}
