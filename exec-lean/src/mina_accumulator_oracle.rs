//! The Lean-backed **MINA DEFERRED-IPA-ACCUMULATOR ORACLE** — the backend for
//! `dregg_turn::executor::mina_accumulator_oracle`.
//!
//! House Law #1, said out loud: **nothing here is an AIR.** Halo/Pickles never evaluate the SRS
//! multi-scalar multiplication in-circuit — the deferral IS the innovation — so the real check is
//! native group arithmetic (`dregg_circuit::pasta_msm`) whose resulting BIT is then routed through
//! the Lean-authored decision `dregg_mina_deferral_ok`
//! (`Dregg2.Circuit.Emit.PastaIpaDeferral` §5). This module authors no constraint and no gadget.
//!
//! `dregg-turn` cannot link `libdregg_lean.a` (wasm32 + SP1 zkVM guest) and cannot carry the 4 MB
//! Vesta SRS, and `dregg-bridge` — where the discharge lives — depends ON `dregg-turn`, so a direct
//! call would also be a dependency cycle. Exactly like [`crate::conservation_oracle`], the backend
//! therefore lives in this crate and `dregg-node` installs it at native startup.
//!
//! ## ⚑ WHY THIS CACHES, and it is not an optimisation
//!
//! Measured 2026-08-05 on the seven real block claims at full width: **40.2 s** for a batch of
//! seven, against **454.6 s** one-at-a-time — batching is **11.3×**, and a single claim is ~65 s of
//! native Pasta arithmetic. A turn's acceptance cannot synchronously pay 65 s, and paying it again
//! for a claim already discharged would be paying it for nothing. The amortisation is the entire
//! reason Halo defers this leg, so the backend keeps a discharged-set: a claim is discharged ONCE
//! and subsequent turns naming the same claim hit the memo.
//!
//! ⚠ The memo is keyed on the FULL claim — commitment coordinates and all sixteen challenges. It is
//! a cache of "this exact claim's MSM vanished", never of "an accumulator was checked recently".

use std::collections::HashSet;
use std::sync::Mutex;

use dregg_bridge::mina_accumulator_discharge as acc;
use dregg_circuit::pasta_windowed_witness::{Pt, U256};
use dregg_turn::executor::{MinaAccumulatorOracle, WireAccumulatorClaim};

/// The batching scalar `r` the fold uses. Any reduced non-zero scalar is sound — `r` only
/// randomises the linear combination across a batch, and a single-claim batch does not depend on
/// it at all. Fixed rather than sampled so a discharge is REPRODUCIBLE: an operator re-running the
/// check on the same claim must get the same verdict.
const BATCH_R: u64 = 0x5EED_1DEA_ACC0_0001;

/// Decode a 32-byte little-endian canonical integer into the discharge's `U256`.
fn le_u256(b: &[u8; 32]) -> U256 {
    let mut l = [0u64; 4];
    for (i, chunk) in b.chunks_exact(8).enumerate() {
        l[i] = u64::from_le_bytes(chunk.try_into().expect("chunks_exact(8) yields 8 bytes"));
    }
    U256(l)
}

/// The native-MSM + verified-Lean-gate backend.
pub struct LeanMinaAccumulatorOracle {
    /// Claims whose MSM has already been evaluated and found to vanish, keyed on the full wire
    /// claim. Only ever holds DISCHARGED claims — a refusal is never memoised, so a claim that
    /// failed is re-evaluated rather than remembered as bad.
    discharged: Mutex<HashSet<WireAccumulatorClaim>>,
}

impl LeanMinaAccumulatorOracle {
    /// Build the backend. Does not load the SRS — that happens on the first discharge, so node
    /// startup does not pay 355 ms and 4 MB for a node that may never see a Mina head.
    pub fn new() -> Self {
        Self {
            discharged: Mutex::new(HashSet::new()),
        }
    }
}

impl Default for LeanMinaAccumulatorOracle {
    fn default() -> Self {
        Self::new()
    }
}

impl MinaAccumulatorOracle for LeanMinaAccumulatorOracle {
    fn discharged(&self, claim: &WireAccumulatorClaim) -> Result<(), String> {
        // A poisoned memo must not decide anything: fall through to a real discharge rather than
        // treating the lock error as either an accept or a refusal.
        if let Ok(seen) = self.discharged.lock()
            && seen.contains(claim)
        {
            return Ok(());
        }

        let srs = acc::vesta_srs_g(256).map_err(|e| {
            format!("the pinned Vesta SRS did not load, so no discharge is possible: {e}")
        })?;

        let native = acc::AccumulatorClaim {
            label: "wire".to_string(),
            height: "wire".to_string(),
            comm: Pt {
                x: le_u256(&claim.comm_x),
                y: le_u256(&claim.comm_y),
                z: U256::ONE,
            },
            chals: claim.chals.iter().map(le_u256).collect(),
        };

        // `acc::discharge` evaluates the MSM, builds the §5b wire from the RESULT, asks the
        // verified Lean gate over that wire, and refuses on any disagreement. Every arm of its
        // error type is a refusal — including "the archive does not export the gate", which is
        // "we could not ask" and is not an accept.
        acc::discharge(
            &srs,
            std::slice::from_ref(&native),
            &U256::from_u64(BATCH_R),
        )
        .map_err(|e| e.to_string())?;

        if let Ok(mut seen) = self.discharged.lock() {
            seen.insert(claim.clone());
        }
        Ok(())
    }
}

/// Install the Lean-backed Mina accumulator oracle into `dregg_turn` (call once at native node
/// startup, only when the archive exports `dregg_mina_deferral_ok`). Returns `true` when installed.
///
/// ⚑ Gated on the export being present, like [`crate::conservation_oracle::register_conservation_oracle`].
/// When the archive lacks it this is a NO-OP and every Mina anchored-head turn then REFUSES — which
/// is the correct disposition, not a degrade: a node that cannot discharge the accumulator cannot
/// know whether the terminal opening is vacuous.
pub fn register_mina_accumulator_oracle() -> bool {
    if !acc::verified_gate_available() {
        return false;
    }
    dregg_turn::executor::install_mina_accumulator_oracle(
        Box::new(LeanMinaAccumulatorOracle::new()),
    )
    .is_ok()
}
