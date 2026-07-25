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

/// Whether THIS build expects a Lean-backed conservation oracle to be installed.
///
/// `true` on **native** (full-Lean) builds — the deployed node links `libdregg_lean.a` via
/// `dregg-exec-lean` and MUST route the per-asset `Σδ=0` decision through the verified Lean
/// `conservesFFI`. `false` on the **wasm32 / zkVM guest**, which cannot link the archive and
/// legitimately decides with the labeled Rust fallback in [`super::atomic`]. The only cfg the
/// crate actually distinguishes is `target_arch = "wasm32"`; the zkVM guest is compiled for a
/// non-host target the same way, so "native" == "not wasm32".
#[inline]
pub const fn native_build_requires_oracle() -> bool {
    cfg!(not(target_arch = "wasm32"))
}

/// FAIL-CLOSED startup check: on a native full-Lean build the conservation oracle MUST be
/// installed. Returns `Err` when it is absent so the deployed node can REFUSE to boot instead of
/// silently deciding conservation with the UNVERIFIED Rust `BlockConservation` fallback — the twin
/// that drifted once into the asset-blind inflation bug.
///
/// The hole this closes: without it, a **missing or stale** Lean archive (whose startup install
/// path never fired) leaves `installed_conservation_oracle()` returning `None`, and
/// [`super::atomic::TurnExecutor::check_per_asset_conservation_by_asset`] silently falls through to
/// the drifting Rust twin — the same asset-blind decision the whole oracle seam exists to retire.
/// A native node that calls this at startup (see `dregg-exec-lean`) can no longer boot in that
/// state, so the twin can never run on a deployed node.
///
/// On the wasm32 / zkVM guest (no archive, no Lean) this is a **no-op** `Ok(())`: the labeled Rust
/// fallback is that build's legitimate, documented no-Lean path.
pub fn ensure_conservation_oracle_installed() -> Result<(), &'static str> {
    if native_build_requires_oracle() && !conservation_oracle_installed() {
        return Err(
            "native full-Lean build expects the verified conservation oracle but none is installed \
             (missing/stale libdregg_lean.a, or the startup install did not fire) — refusing to \
             decide per-asset conservation with the unverified Rust twin",
        );
    }
    Ok(())
}

/// Panicking variant of [`ensure_conservation_oracle_installed`] for the deployed node's startup
/// path: aborts boot with a loud message rather than running the unverified twin.
pub fn assert_conservation_oracle_installed() {
    if let Err(e) = ensure_conservation_oracle_installed() {
        panic!("{e}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// #2 fail-closed reality gate: on a **native** build with NO oracle installed the executor
    /// must REFUSE (here: the startup check errors), never silently accept via the drifting Rust
    /// twin. `dregg-turn`'s own test binary can never link the Lean archive, so it never installs
    /// an oracle — making this the exact "missing Lean archive" state on a native build. On the
    /// wasm32 / zkVM guest the fallback is legitimate and the check is a no-op.
    #[test]
    fn native_no_oracle_fails_closed() {
        if native_build_requires_oracle() {
            // No Lean backend is (or can be) installed in this test binary.
            assert!(
                !conservation_oracle_installed(),
                "dregg-turn's own test binary cannot link libdregg_lean.a; no oracle should be installed"
            );
            assert!(
                ensure_conservation_oracle_installed().is_err(),
                "native build with no oracle MUST fail closed, not run the unverified twin"
            );
        } else {
            // Guest build: the labeled Rust fallback is the legitimate no-Lean path.
            assert!(ensure_conservation_oracle_installed().is_ok());
        }
    }
}
