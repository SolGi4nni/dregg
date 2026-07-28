//! The Lean-backed CONSERVATION ORACLE — routes the deployed executor's per-asset `Σδ = 0` gate
//! through the verified, Lean-authored `dregg_cross_cell_conserves`
//! (`Dregg2.Circuit.CrossCellConserveDecision.conservesFFI`) instead of the hand-written Rust
//! `dregg_circuit::block_conservation::BlockConservation` twin.
//!
//! House Law #1 for the inflation boundary: the deployed conservation decision is COMPUTED BY the Lean
//! source, proved EQUAL to the committed `Dregg2.Circuit.CrossCellConservation` AIR boundary
//! (`creditSum = debitSum` per asset) by `CrossCellConserveRefine.decision_conserves_iff_air_boundary` /
//! `satisfied_imp_decision_conserves` — so the route-through and the proof the prover commits to cannot
//! drift. `dregg-turn` cannot link `libdregg_lean.a` (wasm32 + zkVM guest), so — like the
//! `ConstraintOracle` — this backend lives here (the crate that DOES link the archive) and is installed
//! by `dregg-node` at native startup.

use dregg_turn::executor::ConservationOracle;

/// The deployed-node backend: routes the per-asset conservation decision through the verified Lean
/// `dregg_cross_cell_conserves`.
pub struct LeanConservationOracle;

impl ConservationOracle for LeanConservationOracle {
    fn conserves(&self, rows: &[(u32, i64)]) -> Result<(), (u32, i64)> {
        match dregg_lean_ffi::shadow_cross_cell_conserves(rows) {
            Ok(dregg_lean_ffi::CrossCellVerdict::Conserves) => Ok(()),
            Ok(dregg_lean_ffi::CrossCellVerdict::Imbalanced { asset, imbalance }) => {
                Err((asset, imbalance))
            }
            // FFI unavailable/failed (not expected once installed). Fail CLOSED: report a refusal so the
            // executor rejects the turn rather than silently admitting an unverified block. The generic
            // `(0, 0)` marks "could not verify" — a deployed node whose archive exports the decision
            // never reaches here (the install is gated on `cross_cell_conserves_available`).
            Err(_) => Err((0, 0)),
        }
    }
}

/// Install the Lean-backed conservation oracle into `dregg_turn` (call once at native node startup, only
/// when the archive exports `dregg_cross_cell_conserves`). After this, the deployed executor's per-asset
/// `Σδ=0` decision is computed by the PROVEN Lean `conservesFFI` — the executor no longer decides
/// conservation in Rust on a full node. Returns `true` when installed.
pub fn register_conservation_oracle() -> bool {
    if !dregg_lean_ffi::cross_cell_conserves_available() {
        return false;
    }
    dregg_turn::executor::install_conservation_oracle(Box::new(LeanConservationOracle)).is_ok()
}
