//! BLOCK / BATCH-level cross-cell value-conservation COLLECTOR (Σδ=0 per asset).
//!
//! ## The gap this closes (the DEEPER half of foolable gap #6)
//!
//! The committed [`crate::cross_cell_conservation_air`] proves the per-asset `Σδ=0` AIR over a LIST
//! of signed deltas — but it certifies ONE asset's list given to it. The DEPLOYED proving path
//! produces PER-CELL-ISOLATED proofs: a transfer's debit (cell A, `−10`) and credit (cell B, `+10`)
//! are SEPARATE per-cell rotated proofs, each individually valid, each publishing only its OWN
//! signed `NET_DELTA` PI (`crate::effect_vm::pi::{NET_DELTA_MAG, NET_DELTA_SIGN}`). NOTHING in the
//! deployed path collects ≥2 cells' deltas together. So a light client verifying a BLOCK of
//! individually-valid per-cell proofs cannot conclude `Σδ = 0` across the block: a prover could
//! publish cell A `−10` and cell B `+999` (no declared mint), both per-cell-valid, and mint `+989`
//! out of nothing.
//!
//! This module is the COLLECTOR that closes that: given a BLOCK = the set of verified per-cell
//! proofs (each carrying its published `(NET_DELTA, asset)`) + the block's declared mint/burn supply
//! changes, it (a) extracts each proof's signed delta via
//! [`crate::cross_cell_conservation_air::CrossCellDelta::from_net_delta_pi`], (b) groups by asset
//! (AssetId := issuer-cell), (c) runs the PROVEN per-asset AIR
//! ([`crate::cross_cell_conservation_air::verify_cross_cell_conservation`]) on each group, and
//! (d) ACCEPTS the block iff EVERY asset balances to zero (incl. its declared ±supply rows), else
//! REJECTS — with NO trust beyond the per-cell proofs (which are individually valid). This is the
//! cross-cell light-client bite the per-cell path structurally cannot give.
//!
//! ## The per-asset partition is the soundness floor
//!
//! Each asset's `Σδ=0` is checked INDEPENDENTLY (one proven AIR run per asset class). Cross-asset
//! borrowing — "pay one asset's deficit with another asset's surplus" — is impossible: asset 7's
//! deltas can never enter asset 8's balance (the per-asset proof's `pi[asset]` partition pin, the
//! committed AIR's `assetPinFirst/Last`). A block that nets to zero ACROSS assets but is unbalanced
//! WITHIN an asset is correctly REJECTED.
//!
//! ## Mint / burn are NOT a hole
//!
//! Disclosed supply changes enter as explicit signed rows ([`DeclaredSupplyChange`]): a mint of
//! `+989` is a `+989` credit row paired against the corresponding burn/issuer accounting, exactly
//! the `Generative`/`Annihilative` disclosed non-conservation of `Dregg2.Spec.Conservation`. The
//! conserved sum is over the FULL row set including them, so a HIDDEN mint (a `+999` credit with no
//! matching declared supply row) is precisely what the per-asset boundary catches.
//!
//! ## ADDITIVE — the live-wire seam (NOT wired here)
//!
//! This collector is BUILT + TESTED here over REAL multi-cell proofs, ADDITIVE. It is NOT invoked by
//! the deployed verifier. The live-wire is the serialized handoff. The DEPLOYED path ALREADY
//! collects the proven per-cell deltas — it just sums them OFF-AIR, single-asset:
//!
//! > **`turn/src/executor/atomic.rs::Executor::execute_atomic_sovereign`** is the exact seam. After
//! > verifying each per-cell proof, it reads that proof's PROVEN signed delta
//! > (`dregg_circuit::extract_net_delta(&public_inputs)`, the `(NET_DELTA_MAG, NET_DELTA_SIGN)` PI
//! > pair) into `proven_deltas`, then enforces `proven_deltas.iter().sum::<i64>() == 0` else
//! > `AtomicTurnError::ConservationViolation`. That scalar sum is the OFF-AIR, NOT-per-asset,
//! > NOT-in-circuit version of THIS collector. The live-wire replaces it: pair each `public_inputs`
//! > with its cell's asset class (AssetId := issuer-cell, from `entry.cell_id`), feed
//! > [`PerCellContribution::from_proof_pi`] into a [`BlockConservation`], add the turn's declared
//! > mint/burn rows, and require [`BlockConservation::prove_and_verify`] (or, on the light-client
//! > side, [`BlockConservation::verify_with_proofs`] over the published per-asset proofs). The
//! > block-rejection path is the existing `Err(AtomicTurnError::ConservationViolation)` (now carrying
//! > the per-asset imbalance) — "On failure … no state changes" (the function's atomic-commit
//! > contract is unchanged).
//! >
//! > The same handoff applies at the bundle layer:
//! > `turn/src/executor/proof_verify.rs::verify_proof_carrying_turn_bundle` receives
//! > `bundle_pis: &[Vec<BabyBear>]` (the verified per-cell PIs) after the per-proof STARK verify and
//! > the cross-bundle shared-PI loop — the collector slots in right after that loop, before `Ok(())`.
//! > In `node/src/turn_proving.rs` the `FullTurnWitness.conservation: None` slot becomes the
//! > per-asset proof set the collector certifies.
//!
//! The Lean twin is `metatheory/Dregg2/Circuit/CrossCellConservation.lean` (the per-asset AIR + its
//! rejection teeth); the block-level aggregation is the proven per-asset AIR run once per asset.

use crate::cross_cell_conservation_air::{
    CrossCellDelta, build_cross_cell_conservation_trace, cross_cell_balance,
    verify_cross_cell_conservation,
};
use crate::field::BabyBear;
use std::collections::BTreeMap;

/// Fold a 32-byte `token_id` to a single asset-class field element (dregg3:
/// AssetId := issuer-cell). This is the canonical fold the per-asset
/// conservation partition keys on AND the value the prover surfaces into
/// `PI[v3::ASSET_CLASS]` — defining it HERE (in `dregg_circuit`) keeps the
/// prover, the executor, and the light-client/bundle path byte-identical.
///
/// The distinct-token-ids-stay-distinct property is what the partition needs; a
/// domain-separated BLAKE3 reduction gives a stable, collision-resistant-to-the-
/// field-modulus class. The native / computron asset (the zero token_id) folds
/// to a stable class, matching the `PI[v3::ASSET_CLASS]` zero-default posture.
pub fn fold_token_id_to_asset(token_id: &[u8; 32]) -> BabyBear {
    let h = blake3::derive_key("dregg-asset-class-from-token-id-v1", token_id);
    let v = u32::from_le_bytes([h[0], h[1], h[2], h[3]]);
    BabyBear::new_canonical(v)
}

/// A declared mint / burn supply-change row for one asset, disclosed by the block. Enters the
/// per-asset conservation sum as an explicit signed delta exactly like a per-cell delta — so a
/// disclosed mint balances, but an UNdisclosed one (no matching row) does not.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DeclaredSupplyChange {
    /// The asset / issuer-cell class whose supply changes.
    pub asset: BabyBear,
    /// The magnitude of the supply change.
    pub magnitude: u32,
    /// `true` = mint (a `+mag` credit injected into circulation); `false` = burn (a `−mag` debit).
    /// The conserved sum is over per-cell deltas + these rows, so a mint must be matched by the
    /// per-cell credits it funds (and vice versa) for the asset to balance.
    pub mint: bool,
}

impl DeclaredSupplyChange {
    /// As a [`CrossCellDelta`] over the same asset partition (a mint is a credit, a burn a debit).
    fn as_delta(&self) -> CrossCellDelta {
        CrossCellDelta {
            asset: self.asset,
            magnitude: self.magnitude,
            credit: self.mint,
        }
    }
}

/// One verified per-cell proof's contribution to the block: its published signed `NET_DELTA` PI pair
/// (read straight from the proof's public inputs at `pi::NET_DELTA_MAG` / `pi::NET_DELTA_SIGN`) and
/// the asset / issuer-cell class that delta moves (AssetId := issuer-cell, supplied off-AIR by the
/// verifier from the turn's effect schedule). The collector trusts NOTHING here beyond the
/// per-cell proof: `mag_pi`/`sign_pi` are exactly the values the per-cell proof bound in-circuit
/// and range-checked; `asset` is the partition the verifier already knows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PerCellContribution {
    /// The asset / issuer-cell class this per-cell proof's net delta moves.
    pub asset: BabyBear,
    /// `pi[NET_DELTA_MAG]` from the verified per-cell proof.
    pub net_delta_mag: BabyBear,
    /// `pi[NET_DELTA_SIGN]` from the verified per-cell proof (0 = credit, 1 = debit).
    pub net_delta_sign: BabyBear,
}

impl PerCellContribution {
    /// Read a contribution directly from a verified per-cell proof's published public-input vector.
    /// `asset` is the issuer-cell partition the verifier supplies off-AIR. Returns `None` if the PI
    /// vector is too short to carry the `NET_DELTA` slots (a malformed proof — fail-closed at the
    /// call site).
    pub fn from_proof_pi(asset: BabyBear, proof_pi: &[BabyBear]) -> Option<Self> {
        use crate::effect_vm::pi;
        if proof_pi.len() <= pi::NET_DELTA_SIGN {
            return None;
        }
        Some(PerCellContribution {
            asset,
            net_delta_mag: proof_pi[pi::NET_DELTA_MAG],
            net_delta_sign: proof_pi[pi::NET_DELTA_SIGN],
        })
    }

    /// The signed cross-cell delta this contribution carries.
    fn as_delta(&self) -> CrossCellDelta {
        CrossCellDelta::from_net_delta_pi(self.asset, self.net_delta_mag, self.net_delta_sign)
    }
}

/// Why a block failed the cross-cell conservation collector.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BlockConservationError {
    /// Asset `asset` does not conserve: the signed sum of its per-cell deltas + declared supply rows
    /// is `imbalance ≠ 0` (e.g. a hidden mint). The block is REJECTED.
    AssetImbalanced { asset: BabyBear, imbalance: i64 },
    /// The proven per-asset AIR rejected asset `asset`'s aggregation proof (the in-circuit
    /// `balance[last]==0` boundary). Carries the underlying verifier error.
    AssetProofRejected { asset: BabyBear, reason: String },
}

impl std::fmt::Display for BlockConservationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BlockConservationError::AssetImbalanced { asset, imbalance } => write!(
                f,
                "block cross-cell conservation FAILED: asset {:?} nets to {} (≠ 0) — a hidden \
                 mint/burn across cells with no matching declared supply row",
                asset, imbalance
            ),
            BlockConservationError::AssetProofRejected { asset, reason } => write!(
                f,
                "block cross-cell conservation FAILED: per-asset Σδ=0 proof rejected for asset \
                 {:?}: {}",
                asset, reason
            ),
        }
    }
}

impl std::error::Error for BlockConservationError {}

/// The BLOCK-level cross-cell conservation collector: a set of verified per-cell proof
/// contributions + the block's declared mint/burn supply changes. Grouped by asset and checked
/// per-asset through the PROVEN AIR.
#[derive(Clone, Debug, Default)]
pub struct BlockConservation {
    contributions: Vec<PerCellContribution>,
    supply_changes: Vec<DeclaredSupplyChange>,
}

impl BlockConservation {
    /// An empty block (no contributing per-cell proofs). An empty block trivially conserves.
    pub fn new() -> Self {
        BlockConservation::default()
    }

    /// Add one verified per-cell proof's contribution (its published `NET_DELTA` + asset).
    pub fn add_contribution(&mut self, c: PerCellContribution) -> &mut Self {
        self.contributions.push(c);
        self
    }

    /// Add one declared mint/burn supply-change row.
    pub fn add_supply_change(&mut self, s: DeclaredSupplyChange) -> &mut Self {
        self.supply_changes.push(s);
        self
    }

    /// Group every contribution + declared supply row by asset, in a deterministic asset order (the
    /// `BabyBear` canonical value). Each group is the full signed-delta list one per-asset proof
    /// certifies. Padding-collector convention from the committed AIR: a group with a single delta
    /// still proves (the trace builder pads to ≥2 rows).
    fn groups_by_asset(&self) -> BTreeMap<u32, Vec<CrossCellDelta>> {
        let mut groups: BTreeMap<u32, Vec<CrossCellDelta>> = BTreeMap::new();
        for c in &self.contributions {
            groups.entry(c.asset.0).or_default().push(c.as_delta());
        }
        for s in &self.supply_changes {
            groups.entry(s.asset.0).or_default().push(s.as_delta());
        }
        groups
    }

    /// The per-asset signed imbalance map (a verifier-side pre-flight): asset → `Σ sign·mag`. A
    /// block conserves iff every entry is zero. This mirrors the committed
    /// [`cross_cell_balance`] pre-flight that the trace builder's prefix sum forces into
    /// `balance[last]`.
    pub fn per_asset_balances(&self) -> BTreeMap<u32, i64> {
        self.groups_by_asset()
            .into_iter()
            .map(|(asset, deltas)| (asset, cross_cell_balance(&deltas)))
            .collect()
    }

    /// PRE-FLIGHT accept check (prover-free): the block conserves iff EVERY asset's signed delta sum
    /// (per-cell + declared supply) is zero. Returns the first imbalanced asset as the rejection.
    /// This is the arithmetic the per-asset proven AIR's `balance[last]==0` boundary forces; the
    /// live verifier runs this before [`Self::prove_and_verify`] (the debug batch prover panics on an
    /// unsatisfiable trace, so the pre-flight is the clean fail-closed gate).
    pub fn check(&self) -> Result<(), BlockConservationError> {
        for (asset, imbalance) in self.per_asset_balances() {
            if imbalance != 0 {
                return Err(BlockConservationError::AssetImbalanced {
                    asset: BabyBear::new(asset),
                    imbalance,
                });
            }
        }
        Ok(())
    }

    /// THE FULL COLLECTOR (prover): for EVERY asset class touched by the block, build the per-asset
    /// conservation trace from its grouped signed deltas, PROVE it through the committed Lean
    /// descriptor AIR, and require the proof to VERIFY. ACCEPTS the block iff every asset's per-asset
    /// `Σδ=0` proof verifies; REJECTS on the first asset that does not balance (the prover refuses an
    /// unsatisfiable trace — caught and surfaced as [`BlockConservationError::AssetProofRejected`]).
    ///
    /// This is the in-circuit realization of the block-level `Σδ=0`: the trust is ONLY the per-cell
    /// proofs (whose published `NET_DELTA` PIs feed the trace) plus the per-asset AIR — no off-AIR
    /// reconstruction of the cross-cell pairing.
    pub fn prove_and_verify(&self) -> Result<(), BlockConservationError> {
        use crate::cross_cell_conservation_air::prove_cross_cell_conservation;

        for (asset, deltas) in self.groups_by_asset() {
            let asset_felt = BabyBear::new(asset);

            // Pre-flight: an unbalanced asset is rejected up front (the proven AIR boundary would
            // also reject, but the debug batch prover panics on an unsatisfiable trace — so gate it).
            let imbalance = cross_cell_balance(&deltas);
            if imbalance != 0 {
                return Err(BlockConservationError::AssetImbalanced {
                    asset: asset_felt,
                    imbalance,
                });
            }

            let (trace, pi) = build_cross_cell_conservation_trace(&deltas);
            let proof = prove_cross_cell_conservation(&trace, &pi).map_err(|e| {
                BlockConservationError::AssetProofRejected {
                    asset: asset_felt,
                    reason: e,
                }
            })?;
            verify_cross_cell_conservation(&proof, &pi).map_err(|e| {
                BlockConservationError::AssetProofRejected {
                    asset: asset_felt,
                    reason: e,
                }
            })?;
        }
        Ok(())
    }

    /// VERIFIER-side collector (prover-free): for EVERY asset, require a supplied per-asset
    /// aggregation proof to verify against the committed AIR + the asset's `[asset]` PI. A light
    /// client runs THIS over the block's accompanying per-asset conservation proofs. `proofs` is the
    /// asset → proof map the prover published; an asset with no proof, or whose proof does not
    /// verify, REJECTS the block.
    pub fn verify_with_proofs(
        &self,
        proofs: &BTreeMap<
            u32,
            crate::descriptor_ir2::Ir2BatchProof<crate::descriptor_ir2::DreggStarkConfig>,
        >,
    ) -> Result<(), BlockConservationError> {
        for asset in self.groups_by_asset().keys() {
            let asset_felt = BabyBear::new(*asset);
            let pi = vec![asset_felt];
            let proof = proofs.get(asset).ok_or_else(|| {
                BlockConservationError::AssetProofRejected {
                    asset: asset_felt,
                    reason: "block carries no per-asset conservation proof for this asset".into(),
                }
            })?;
            verify_cross_cell_conservation(proof, &pi).map_err(|e| {
                BlockConservationError::AssetProofRejected {
                    asset: asset_felt,
                    reason: e,
                }
            })?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::effect_vm::pi;
    use crate::effect_vm::{CellState, Effect, generate_effect_vm_trace};

    /// Generate a REAL per-cell transfer proof's published PI vector: run the genuine Effect-VM
    /// trace generator over a one-`Transfer`-effect turn (direction 1 = debit/outflow, 0 =
    /// credit/inflow). The returned PI vector carries the `NET_DELTA_MAG/SIGN` the per-cell proof
    /// binds in-circuit (Constraint Group 5 + the after-balance range rib). This is exactly the
    /// published output the collector consumes — no off-AIR fabrication.
    fn real_per_cell_transfer_pi(pre_balance: u64, amount: u64, direction: u32) -> Vec<BabyBear> {
        let state = CellState::new(pre_balance, 0);
        let effects = vec![Effect::Transfer { amount, direction }];
        let (_trace, pi) = generate_effect_vm_trace(&state, &effects);
        pi
    }

    /// Sanity: a real debit transfer publishes `NET_DELTA = −amount`; a real credit publishes
    /// `+amount` — the genuine per-cell signed delta the collector groups.
    #[test]
    fn real_per_cell_transfer_publishes_signed_net_delta() {
        let debit = real_per_cell_transfer_pi(100, 10, 1);
        assert_eq!(debit[pi::NET_DELTA_MAG], BabyBear::new(10));
        assert_eq!(debit[pi::NET_DELTA_SIGN], BabyBear::ONE, "debit sign = 1");

        let credit = real_per_cell_transfer_pi(100, 10, 0);
        assert_eq!(credit[pi::NET_DELTA_MAG], BabyBear::new(10));
        assert_eq!(credit[pi::NET_DELTA_SIGN], BabyBear::ZERO, "credit sign = 0");
    }

    /// THE REAL MULTI-CELL TOOTH (pre-flight half). A BLOCK built from TWO REAL per-cell transfer
    /// proofs — cell A's debit (`−10`) + cell B's credit (`+10`) of the SAME asset — BALANCES, so
    /// [`BlockConservation::check`] accepts. NO trust beyond the per-cell proofs: the deltas are read
    /// from their genuine published `NET_DELTA` PIs.
    #[test]
    fn honest_transfer_block_conserves() {
        let asset = BabyBear::new(7);
        let debit_pi = real_per_cell_transfer_pi(100, 10, 1); // cell A: −10
        let credit_pi = real_per_cell_transfer_pi(0, 10, 0); // cell B: +10

        let mut block = BlockConservation::new();
        block
            .add_contribution(PerCellContribution::from_proof_pi(asset, &debit_pi).unwrap())
            .add_contribution(PerCellContribution::from_proof_pi(asset, &credit_pi).unwrap());

        assert_eq!(block.per_asset_balances().get(&7), Some(&0));
        block
            .check()
            .expect("honest A−10,B+10 block conserves per asset");
    }

    /// THE FORGED-MINT TOOTH (pre-flight half). A BLOCK from cell A's REAL `−10` debit proof + cell
    /// B's REAL `+999` credit proof of the SAME asset, with NO declared mint, nets to `+989 ≠ 0`, so
    /// [`BlockConservation::check`] REJECTS the block — even though BOTH per-cell proofs are
    /// individually valid. This is the cross-cell light-client bite the per-cell path cannot give.
    #[test]
    fn forged_mint_block_rejected() {
        let asset = BabyBear::new(7);
        let debit_pi = real_per_cell_transfer_pi(100, 10, 1); // cell A: −10  (valid per-cell proof)
        let credit_pi = real_per_cell_transfer_pi(0, 999, 0); // cell B: +999 (valid per-cell proof)

        let mut block = BlockConservation::new();
        block
            .add_contribution(PerCellContribution::from_proof_pi(asset, &debit_pi).unwrap())
            .add_contribution(PerCellContribution::from_proof_pi(asset, &credit_pi).unwrap());

        assert_eq!(
            block.per_asset_balances().get(&7),
            Some(&989),
            "forged A−10,B+999 (no declared mint) nets to +989"
        );
        match block.check() {
            Err(BlockConservationError::AssetImbalanced { asset: a, imbalance }) => {
                assert_eq!(a, asset);
                assert_eq!(imbalance, 989);
            }
            other => panic!("forged-mint block must be REJECTED, got {:?}", other),
        }
    }

    /// A DISCLOSED mint restores conservation: the forged-looking `A −10, B +999` block, WITH a
    /// declared `−989` supply burn row (the issuer's disclosed Annihilative row that funds the
    /// minted credit), balances to 0 and is ACCEPTED. Non-conservation is only legal when DISCLOSED.
    #[test]
    fn declared_supply_change_restores_conservation() {
        let asset = BabyBear::new(7);
        let debit_pi = real_per_cell_transfer_pi(100, 10, 1); // −10
        let credit_pi = real_per_cell_transfer_pi(0, 999, 0); // +999

        let mut block = BlockConservation::new();
        block
            .add_contribution(PerCellContribution::from_proof_pi(asset, &debit_pi).unwrap())
            .add_contribution(PerCellContribution::from_proof_pi(asset, &credit_pi).unwrap())
            .add_supply_change(DeclaredSupplyChange {
                asset,
                magnitude: 989,
                mint: false, // a declared −989 burn/supply row that funds the +999 credit
            });

        assert_eq!(block.per_asset_balances().get(&7), Some(&0));
        block.check().expect("disclosed supply row conserves");
    }

    /// THE PER-ASSET PARTITION TOOTH. A block where asset 7 is short `−10` and asset 8 is long `+10`
    /// nets to zero ACROSS assets, but each asset is independently unbalanced — so the collector
    /// REJECTS it (cross-asset borrowing is impossible). The first imbalanced asset is reported.
    #[test]
    fn cross_asset_borrowing_rejected() {
        let asset7 = BabyBear::new(7);
        let asset8 = BabyBear::new(8);
        let debit_pi = real_per_cell_transfer_pi(100, 10, 1); // asset 7: −10
        let credit_pi = real_per_cell_transfer_pi(0, 10, 0); // asset 8: +10

        let mut block = BlockConservation::new();
        block
            .add_contribution(PerCellContribution::from_proof_pi(asset7, &debit_pi).unwrap())
            .add_contribution(PerCellContribution::from_proof_pi(asset8, &credit_pi).unwrap());

        let balances = block.per_asset_balances();
        assert_eq!(balances.get(&7), Some(&-10));
        assert_eq!(balances.get(&8), Some(&10));
        assert!(
            block.check().is_err(),
            "cross-asset borrowing must be REJECTED (each asset checked independently)"
        );
    }

    /// THE FULL END-TO-END COLLECTOR (law #1, real proofs through the proven AIR). The honest
    /// two-cell transfer block PROVES + VERIFIES per asset through the committed Lean descriptor; the
    /// forged-mint block is REJECTED (the per-asset `balance[last]==0` boundary is unsatisfiable). NO
    /// trust beyond the per-cell proofs + the proven AIR.
    #[test]
    fn block_collector_proves_honest_rejects_forged() {
        let asset = BabyBear::new(7);

        // Honest: two REAL per-cell proofs, A −10 + B +10 → the per-asset AIR proves + verifies.
        let mut honest = BlockConservation::new();
        honest
            .add_contribution(
                PerCellContribution::from_proof_pi(asset, &real_per_cell_transfer_pi(100, 10, 1))
                    .unwrap(),
            )
            .add_contribution(
                PerCellContribution::from_proof_pi(asset, &real_per_cell_transfer_pi(0, 10, 0))
                    .unwrap(),
            );
        honest
            .prove_and_verify()
            .expect("honest block must prove + verify per asset through the committed AIR");

        // Forged: A −10 + B +999, no declared mint → REJECTED (per-asset Σδ ≠ 0).
        let mut forged = BlockConservation::new();
        forged
            .add_contribution(
                PerCellContribution::from_proof_pi(asset, &real_per_cell_transfer_pi(100, 10, 1))
                    .unwrap(),
            )
            .add_contribution(
                PerCellContribution::from_proof_pi(asset, &real_per_cell_transfer_pi(0, 999, 0))
                    .unwrap(),
            );
        let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            forged.prove_and_verify()
        }));
        match rejected {
            // The pre-flight gate / Err path: the forged block is rejected before/at proving.
            Ok(Err(BlockConservationError::AssetImbalanced { imbalance, .. })) => {
                assert_eq!(imbalance, 989);
            }
            Ok(Err(BlockConservationError::AssetProofRejected { .. })) => { /* AIR rejected */ }
            // Or the debug batch prover panicked on the unsatisfiable trace — also a rejection.
            Err(_) => {}
            Ok(Ok(())) => panic!("forged-mint block must NOT be accepted by the collector"),
        }
    }

    /// MULTI-ASSET: a block touching asset 7 (A −10 / B +10) AND asset 8 (C −5 / D +5), each
    /// balanced, PROVES + VERIFIES — one per-asset AIR run per asset (the
    /// `multi_domain_independent` conjunction). NO declared supply rows needed.
    #[test]
    fn multi_asset_balanced_block_conserves() {
        let asset7 = BabyBear::new(7);
        let asset8 = BabyBear::new(8);
        let mut block = BlockConservation::new();
        block
            .add_contribution(
                PerCellContribution::from_proof_pi(asset7, &real_per_cell_transfer_pi(100, 10, 1))
                    .unwrap(),
            )
            .add_contribution(
                PerCellContribution::from_proof_pi(asset7, &real_per_cell_transfer_pi(0, 10, 0))
                    .unwrap(),
            )
            .add_contribution(
                PerCellContribution::from_proof_pi(asset8, &real_per_cell_transfer_pi(50, 5, 1))
                    .unwrap(),
            )
            .add_contribution(
                PerCellContribution::from_proof_pi(asset8, &real_per_cell_transfer_pi(0, 5, 0))
                    .unwrap(),
            );
        block
            .prove_and_verify()
            .expect("multi-asset balanced block conserves (one proof per asset)");
    }

    /// An empty block (no per-cell proofs) trivially conserves.
    #[test]
    fn empty_block_conserves() {
        BlockConservation::new()
            .check()
            .expect("empty block trivially conserves");
    }
}
