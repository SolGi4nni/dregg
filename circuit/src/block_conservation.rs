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
//! proofs (each carrying its published `(NET_DELTA, asset)`), it (a) extracts each proof's signed
//! delta via
//! [`crate::cross_cell_conservation_air::CrossCellDelta::from_net_delta_pi`], (b) groups by asset
//! (AssetId := issuer-cell), (c) runs the PROVEN per-asset AIR
//! ([`crate::cross_cell_conservation_air::verify_cross_cell_conservation`]) on each group, and
//! (d) ACCEPTS the block iff EVERY asset balances to zero, else
//! REJECTS — with NO trust beyond the per-cell proofs (which are individually valid). This is the
//! cross-cell light-client bite the per-cell path structurally cannot give.
//!
//! ## The per-asset partition is the soundness floor — AND THE CLASS IS ONLY ~31 BITS
//!
//! Each asset's `Σδ=0` is checked INDEPENDENTLY (one proven AIR run per asset class). Cross-asset
//! borrowing — "pay one asset's deficit with another asset's surplus" — cannot cross a CLASS
//! boundary: asset 7's deltas can never enter asset 8's balance (the per-asset proof's `pi[asset]`
//! partition pin, the committed AIR's `assetPinFirst/Last`). A block that nets to zero ACROSS
//! classes but is unbalanced WITHIN a class is correctly REJECTED.
//!
//! ⚠ **But a class is not an asset.** [`fold_token_id_to_asset`] maps 32-byte asset ids onto ONE
//! `BabyBear`, so the partition has ~2^30.87 classes and two distinct assets landing in one class
//! is a **2^15.67 birthday grind** — at which point the borrowing above is between two genuine
//! currencies and is INVISIBLE, here and in the verified Lean decider downstream (which is handed
//! the already-folded class). Read that function's docs before treating this partition as a floor;
//! [`assert_asset_classes_injective`] is the refusal every caller still holding the ids must run.
//!
//! ## Mint / burn are NOT a hole — and the DISCLOSURE IS A LEDGER ROW, not a claim
//!
//! This module used to carry a `DeclaredSupplyChange` row type so a block could ASSERT "this `+989`
//! is a disclosed mint" and have the assertion enter the conserved sum. **It was deleted on
//! 2026-07-28 and nothing was lost**, because the deployed supply model
//! (`.docs-history-noclaude/SUPPLY-MODEL.md`) does not disclose supply with a claim — it discloses
//! it with a *paired ledger delta*:
//!
//! * **Mint** debits the asset's ISSUER WELL (a real, signed, negative-capable `−supply` account)
//!   and credits the holder — `turn/src/executor/apply.rs::apply_mint`. Per-asset `Σδ = 0`.
//! * **Burn** is the dual: holder → well. `apply_burn`. Per-asset `Σδ = 0`.
//! * `CreateCell` **cannot** open a balance (`apply.rs`, hard `Err(CreateCellNonZeroBalance)`), so
//!   there is no implicit value entry either.
//!
//! So a genuine supply change already appears in this collector as TWO ordinary contributions that
//! cancel, and the well's leg is *auditable state* rather than an unbacked assertion. A HIDDEN mint
//! is a `+999` credit whose well leg is absent — and that is exactly what the per-asset boundary
//! catches, with no row type required.
//!
//! ⚠ Why the row type is not merely unused but WRONG here: it added `+magnitude` to the conserved
//! sum with **no authority check of any kind**, while `Effect::Mint` requires a control-grade
//! capability over the issuer well carrying the `EFFECT_MINT` facet (the Rust image of Lean
//! `mintAuthorizedB` — "a cell cannot coin its own supply"). Any caller that populated it would
//! have minted past that gate. It had no producer anywhere in the tree; every call site in the
//! executor, the bundle path and the tests passed an empty slice.
//!
//! The Lean decision procedure `Dregg2.Circuit.CrossCellConserveDecision` still MODELS declared
//! supply rows — its wire section is optional and its `#guard` for them is a true theorem about the
//! rule. That is the spec being more general than the deployment, which is fine. What is not fine
//! is a Rust parameter advertising a channel with no producer, because a parameter is a call-site
//! obligation and the next reader fills it in.
//!
//! ## ADDITIVE — the live-wire seam (NOT wired here)
//!
//! ⚠ THE SECOND, LARGER GAP THE SUPPLY-ROW DELETION MAKES VISIBLE: this collector sums the
//! contributions it is HANDED, and on both live paths the row set is built from a narrow channel —
//! `Action::balance_change` on the cleartext path (`executor/execute_tree.rs`), and
//! `Transfer`/`Burn`/`Mint` only on the mixed-atomic path (`executor/atomic.rs`). A `Σδ = 0` verdict
//! is therefore a statement about THOSE rows, not about every way value moves in a turn. See
//! `docs/reference/EXECUTED-PATH-SYMMETRY-2026-07-26.md` §2 for the four pairwise holes.
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
//! > [`PerCellContribution::from_proof_pi`] into a [`BlockConservation`] (a mint/burn already
//! > contributes BOTH its legs, holder and issuer well), and require
//! > [`BlockConservation::prove_and_verify`] (or, on the light-client
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
/// The native / computron asset (the zero token_id) folds to a stable class.
///
/// # ⚠ THIS FOLD IS NOT INJECTIVE, AND NO CHOICE OF HASH BYTES CAN MAKE IT SO
///
/// This doc used to read: *"The distinct-token-ids-stay-distinct property is
/// what the partition needs; a domain-separated BLAKE3 reduction gives a stable,
/// collision-resistant-to-the-field-modulus class."* The first clause is true —
/// the partition does need injectivity. The second does not deliver it, and the
/// code never did. Both halves are measured in this module's tests:
///
/// * It discards **28 of BLAKE3's 32 output bytes** (`h[0..4]`), then reduces the
///   surviving `u32` mod `p = 2013265921`. `2^32 = 2p + 268435454`, so the image
///   is ALL of `[0, p)`: 268435454 classes have three `u32` preimages and
///   1744830467 have two. Effective class count `1/Σpᵢ² = 1.963e9 = 2^30.87` —
///   `1.025×` worse than uniform over `p`, which is a rounding error next to the
///   fact that there are only ~2^31 classes at all.
/// * A birthday collision is expected at **~52,172 folds (2^15.67)** for 50%.
///   `driven_fold_collision_is_cheap` performs the search and reports the actual
///   count; it runs in well under a second.
///
/// ⚠ **A WIDER HASH KEY WOULD BE A NO-OP.** Taking `h[0..8]`, or the full 32
/// bytes as a bignum mod `p`, buys ~2.5% and nothing else: the destination is ONE
/// `BabyBear`, and `p < 2^31`. The width lives in the DESTINATION TYPE, not in
/// the truncation. The asset class is one felt because `PI[v3::ASSET_CLASS]` is
/// one PI slot pinned to one row-0 AIR column
/// (`effect_vm::{pi::v3::ASSET_CLASS, columns::aux_off::ASSET_CLASS}`), and the
/// committed per-asset AIR (`Dregg2.Circuit.CrossCellConservation`) partitions on
/// one felt. Making the partition genuinely collision-resistant means widening
/// that column to a multi-felt asset commitment — a LEAN-AUTHORED change to the
/// AIR plus a PI-layout flag day, not an edit to this function.
///
/// # What a collision costs, and the refusal that is available instead
///
/// Two DISTINCT assets that fold to one class become ONE conservation class, so
/// cross-asset borrowing between them — asset A `−10`, asset B `+10` — sums to
/// zero and is ACCEPTED. That is exactly the forge the per-asset partition exists
/// to reject (`cross_asset_borrowing_rejected`), and it is invisible to every
/// consumer downstream of the fold, INCLUDING the verified Lean decider: the
/// executor hands `dregg_cross_cell_conserves` the already-folded `u32`
/// (`turn/src/executor/atomic.rs::check_per_asset_conservation_by_asset`), so the
/// oracle decides `Σδ=0` correctly over classes that were already wrong.
///
/// The collision is NOT detectable from the folded felt — but it IS detectable
/// wherever both 32-byte ids are still in hand, which on the executor path is
/// every row-producing cell of the turn. Since a conservation SCOPE is exactly
/// one turn/bundle, a cross-asset borrow needs both legs inside one scope, and
/// [`assert_asset_classes_injective`] refuses that scope. Callers that still hold
/// the ids MUST call it; see its docs for the surface it cannot reach.
pub fn fold_token_id_to_asset(token_id: &[u8; 32]) -> BabyBear {
    let h = blake3::derive_key("dregg-asset-class-from-token-id-v1", token_id);
    let v = u32::from_le_bytes([h[0], h[1], h[2], h[3]]);
    BabyBear::new_canonical(v)
}

/// Two DISTINCT 32-byte asset ids that [`fold_token_id_to_asset`] maps onto ONE
/// conservation class. Carrying both ids (not just the class) is the point: the
/// refusal has to be able to say WHICH assets were about to be merged.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AssetClassCollision {
    /// The lexicographically smaller of the two colliding asset ids.
    pub first: [u8; 32],
    /// The lexicographically larger of the two colliding asset ids.
    pub second: [u8; 32],
    /// The single class both ids fold to.
    pub class: u32,
}

impl std::fmt::Display for AssetClassCollision {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "asset-class collision: distinct asset ids {} and {} both fold to class {} — \
             the per-asset conservation partition would merge two currencies into one \
             class, making cross-asset borrowing between them invisible",
            hex32(&self.first),
            hex32(&self.second),
            self.class
        )
    }
}

impl std::error::Error for AssetClassCollision {}

fn hex32(b: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for byte in b {
        s.push_str(&format!("{byte:02x}"));
    }
    s
}

/// REFUSE an asset-id set whose [`fold_token_id_to_asset`] images are not
/// distinct — the guard that makes the ~2^30.87-class partition safe to use over
/// the ids a single conservation scope actually touches.
///
/// Two distinct ids at one class is a WITNESS-GENERATION FAULT, not a value the
/// partition may quietly absorb: merging them silently is the bug. Identical ids
/// repeated are fine (one asset, many cells) — only DISTINCT ids at one class
/// refuse.
///
/// # Why an in-scope check is enough on the paths that can run it
///
/// A conservation scope is one turn (`check_per_asset_conservation_by_asset`) or
/// one bundle (`check_bundle_per_asset_conservation`). Cross-asset borrowing
/// needs BOTH legs — the short asset and the long one — inside a single scope: a
/// lone `−10` leg in its own turn leaves that class at `Σδ = −10` and is rejected
/// on the spot. So a colliding pair can only be exploited where both ids are
/// present, which is where this check sees them.
///
/// # ⚠ WHERE THIS DOES NOT REACH
///
/// The pure light-client / bundle path
/// (`turn/src/executor/proof_verify.rs::check_bundle_per_asset_conservation`)
/// groups by `PI[v3::ASSET_CLASS]` and has NO ledger, so the 32-byte ids do not
/// exist for it and this guard cannot be called there. That leg is already
/// weaker for a strictly larger reason, named in
/// `atomic.rs::resolve_proof_asset_class`: nothing in-AIR binds
/// `PI[v3::ASSET_CLASS]` to a cell's committed asset bytes, so a light client's
/// partition key is prover-chosen outright — an attacker there does not need a
/// collision, it writes the class it wants. Closing THAT is the multi-felt
/// asset-commitment column above, which is the same Lean-authored flag day.
///
/// # The trade this makes
///
/// A genuine accidental collision between two live production assets becomes a
/// LIVENESS fault (every turn touching both refuses) instead of a silent
/// soundness fault (the two currencies merge). At `k` live assets the accident
/// probability is `≈ k²/2 · 5.09e-10`; the deployed asset set is
/// operator-authored (genesis `token_id`s plus registered issuer wells, since
/// `turn/src/executor/apply.rs::birth_asset` makes every effect-created cell
/// INHERIT its parent's asset), so `k` is tens and the probability is ~1e-16.
/// Under an asset set an attacker can extend, the same accident becomes a 2^15.67
/// grind — and then the liveness refusal is the whole point.
pub fn assert_asset_classes_injective(ids: &[[u8; 32]]) -> Result<(), AssetClassCollision> {
    let mut seen: BTreeMap<u32, [u8; 32]> = BTreeMap::new();
    for id in ids {
        let class = fold_token_id_to_asset(id).as_u32();
        match seen.get(&class) {
            None => {
                seen.insert(class, *id);
            }
            Some(prev) if prev == id => {}
            Some(prev) => {
                let (first, second) = if prev < id {
                    (*prev, *id)
                } else {
                    (*id, *prev)
                };
                return Err(AssetClassCollision {
                    first,
                    second,
                    class,
                });
            }
        }
    }
    Ok(())
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
    /// Asset `asset` does not conserve: the signed sum of its per-cell deltas is `imbalance ≠ 0`
    /// (e.g. a hidden mint — a credit whose issuer-well leg is absent). The block is REJECTED.
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
                 mint/burn across cells with no matching issuer-well leg",
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

/// The BLOCK-level cross-cell conservation collector: the set of verified per-cell proof
/// contributions, grouped by asset and checked per-asset through the PROVEN AIR.
///
/// A supply change needs no separate row type here: a mint/burn is a holder↔issuer-well MOVE, so it
/// arrives as TWO contributions of the same asset that cancel (see the module header).
#[derive(Clone, Debug, Default)]
pub struct BlockConservation {
    contributions: Vec<PerCellContribution>,
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

    /// Group every contribution by asset, in a deterministic asset order (the
    /// `BabyBear` canonical value). Each group is the full signed-delta list one per-asset proof
    /// certifies. Padding-collector convention from the committed AIR: a group with a single delta
    /// still proves (the trace builder pads to ≥2 rows).
    fn groups_by_asset(&self) -> BTreeMap<u32, Vec<CrossCellDelta>> {
        let mut groups: BTreeMap<u32, Vec<CrossCellDelta>> = BTreeMap::new();
        for c in &self.contributions {
            groups.entry(c.asset.0).or_default().push(c.as_delta());
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
    /// is zero. Returns the first imbalanced asset as the rejection.
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
            let proof =
                proofs
                    .get(asset)
                    .ok_or_else(|| BlockConservationError::AssetProofRejected {
                        asset: asset_felt,
                        reason: "block carries no per-asset conservation proof for this asset"
                            .into(),
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
        assert_eq!(
            credit[pi::NET_DELTA_SIGN],
            BabyBear::ZERO,
            "credit sign = 0"
        );
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
            Err(BlockConservationError::AssetImbalanced {
                asset: a,
                imbalance,
            }) => {
                assert_eq!(a, asset);
                assert_eq!(imbalance, 989);
            }
            other => panic!("forged-mint block must be REJECTED, got {:?}", other),
        }
    }

    /// A DISCLOSED SUPPLY CHANGE RESTORES CONSERVATION — AND ITS DISCLOSURE IS THE ISSUER WELL'S
    /// OWN LEG, not a claimed row. The forged-looking `A −10, B +999` block balances to 0 once the
    /// well contributes the `−989` that funded the extra credit, exactly as
    /// `turn/src/executor/apply.rs::apply_mint` writes it (well debited, holder credited, same
    /// asset). The well's leg is a real per-cell delta, so it needs no separate row type — and it
    /// carries a capability gate the deleted `DeclaredSupplyChange` row never had.
    #[test]
    fn issuer_well_leg_is_the_supply_disclosure() {
        let asset = BabyBear::new(7);
        let debit_pi = real_per_cell_transfer_pi(100, 10, 1); // holder A: −10
        let credit_pi = real_per_cell_transfer_pi(0, 999, 0); // holder B: +999
        // ISSUER WELL: −989, the leg that funds the extra credit. Its pre-balance is 989 because
        // the Effect-VM trace generator's `CellState` is unsigned and refuses a debit below zero;
        // the DEPLOYED well is negative-capable (`well_debit_balance`), and the collector only ever
        // sees the published NET_DELTA, which is `−989` either way.
        let well_pi = real_per_cell_transfer_pi(989, 989, 1);

        let mut block = BlockConservation::new();
        block
            .add_contribution(PerCellContribution::from_proof_pi(asset, &debit_pi).unwrap())
            .add_contribution(PerCellContribution::from_proof_pi(asset, &credit_pi).unwrap())
            .add_contribution(PerCellContribution::from_proof_pi(asset, &well_pi).unwrap());

        assert_eq!(block.per_asset_balances().get(&7), Some(&0));
        block
            .check()
            .expect("a mint whose issuer-well leg is present conserves");

        // ANTI-VACUITY: the SAME three-row shape WITHOUT the well leg is the hidden mint, and it is
        // refused. So the acceptance above is the well's contribution, not an empty check.
        let mut undisclosed = BlockConservation::new();
        undisclosed
            .add_contribution(PerCellContribution::from_proof_pi(asset, &debit_pi).unwrap())
            .add_contribution(PerCellContribution::from_proof_pi(asset, &credit_pi).unwrap());
        match undisclosed.check() {
            Err(BlockConservationError::AssetImbalanced { imbalance, .. }) => {
                assert_eq!(imbalance, 989, "the un-funded credit is the imbalance")
            }
            other => panic!("a mint with no issuer-well leg must be REJECTED, got {other:?}"),
        }
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
        let rejected =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| forged.prove_and_verify()));
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
    /// `multi_domain_independent` conjunction).
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

    // =======================================================================
    // THE ASSET-CLASS PARTITION IS ~31 BITS: the driven collision
    // =======================================================================

    /// Search for two DISTINCT 32-byte asset ids that [`fold_token_id_to_asset`]
    /// maps onto ONE class. Deterministic (a counter in the low 8 bytes), and
    /// bounded — a 50% birthday hit is expected at ~52,172 folds over the
    /// measured 2^30.87 effective classes, so `budget` of a few hundred thousand
    /// is a near-certainty. Returns `(a, b, class, folds_performed)`.
    fn grind_colliding_asset_ids(budget: u64) -> Option<([u8; 32], [u8; 32], u32, u64)> {
        let mut seen: std::collections::HashMap<u32, [u8; 32]> =
            std::collections::HashMap::with_capacity(budget as usize);
        for i in 0..budget {
            let mut id = [0u8; 32];
            id[0..8].copy_from_slice(&i.to_le_bytes());
            let class = fold_token_id_to_asset(&id).as_u32();
            if let Some(prev) = seen.get(&class) {
                if prev != &id {
                    return Some((*prev, id, class, i + 1));
                }
            }
            seen.insert(class, id);
        }
        None
    }

    /// ⚑ THE MECHANISM, MEASURED — not inherited from a brief.
    ///
    /// 1. The fold is a GENUINE truncation: 28 of BLAKE3's 32 output bytes are
    ///    discarded before the mod-p reduction. (Contrast the sibling
    ///    `heap_root` finding, where `as_u32()` was NOT a truncation.)
    /// 2. But the truncation is NOT the binding constraint: the image is all of
    ///    `[0, p)` either way, because the destination is one `BabyBear`. A wider
    ///    hash key buys the 1.025× non-uniformity and nothing else.
    /// 3. A collision is a cheap offline grind, and this test performs one.
    #[test]
    fn driven_fold_collision_is_cheap() {
        // (1) The truncation is real: flipping a byte of the hash tail that the
        //     fold discards is not observable, because only h[0..4] is read.
        //     Demonstrated structurally — the fold reads exactly 4 of 32 bytes.
        let probe = [0u8; 32];
        let h = blake3::derive_key("dregg-asset-class-from-token-id-v1", &probe);
        assert_eq!(
            fold_token_id_to_asset(&probe),
            BabyBear::new_canonical(u32::from_le_bytes([h[0], h[1], h[2], h[3]])),
            "the fold reads h[0..4] and discards h[4..32]"
        );

        // (2) The destination bounds the width. p < 2^32, so mod-p is surjective
        //     onto [0, p) from a 32-bit key AND from any wider one: widening the
        //     key cannot add classes.
        assert!(
            crate::field::BABYBEAR_P < u32::MAX,
            "p < 2^32: a u32 key already covers every class; a wider key adds none"
        );

        // (2b) THE ZERO CLASS IS OVERLOADED AS A SENTINEL.
        //      `turn::executor::atomic::resolve_proof_asset_class` reads
        //      `PI[v3::ASSET_CLASS] == 0` as "the prover has not populated the
        //      class", so an asset whose class IS zero is indistinguishable from
        //      an unlabelled proof. Grinding a token_id onto that ONE class is
        //      ~2^30.87 folds — at the ~1.2M folds/s this test measures, on the
        //      order of half an hour on ONE core. Record where the ledger's own
        //      default lands: `[0u8; 32]` is both the native/computron asset and
        //      the fallback for a cell absent from the ledger
        //      (`asset_id_for_cell`), so if IT folded to zero the sentinel would
        //      already be occupied by a real, reachable asset.
        let native_class = fold_token_id_to_asset(&[0u8; 32]).as_u32();
        println!(
            "NATIVE ASSET ([0u8;32]) folds to class {native_class}; the ZERO sentinel is \
             {}occupied by it",
            if native_class == 0 { "" } else { "NOT " }
        );
        assert_ne!(
            native_class, 0,
            "the native asset must not land on the ZERO 'class not populated' sentinel"
        );

        // (3) The driven collision.
        let (a, b, class, folds) =
            grind_colliding_asset_ids(2_000_000).expect("a birthday collision inside 2e6 folds");
        assert_ne!(a, b, "the colliding ids must be DISTINCT 32-byte assets");
        assert_eq!(fold_token_id_to_asset(&a).as_u32(), class);
        assert_eq!(fold_token_id_to_asset(&b).as_u32(), class);
        println!(
            "DRIVEN COLLISION: asset {} and asset {} both fold to class {} after {} folds \
             (2^{:.2}); analytic 50% birthday = 52172 (2^15.67) over 2^30.87 effective classes",
            hex32(&a),
            hex32(&b),
            class,
            folds,
            (folds as f64).log2()
        );
        assert!(
            folds < 500_000,
            "a collision must be CHEAP; took {folds} folds"
        );
    }

    /// ⚑ THE WOUND, DRIVEN. Cross-asset borrowing between two DISTINCT assets
    /// that fold to one class is INVISIBLE to this collector — the exact forge
    /// [`cross_asset_borrowing_rejected`] proves is rejected for non-colliding
    /// assets.
    ///
    /// The "before" pole is a VERBATIM IN-TEST ORACLE of the pre-fix behaviour:
    /// group by `fold_token_id_to_asset` and require every class to net to zero,
    /// with NO id-level check — which is precisely what `BlockConservation` does
    /// and will keep doing (the felt is all it has). So the wound stays
    /// demonstrated permanently rather than resting on a git-history claim.
    #[test]
    fn colliding_assets_make_cross_asset_borrowing_invisible_then_refused() {
        let (a, b, class, _) =
            grind_colliding_asset_ids(2_000_000).expect("a birthday collision inside 2e6 folds");

        // ── BEFORE: the fold is all the collector gets, and it accepts. ──
        let debit_pi = real_per_cell_transfer_pi(100, 10, 1); // asset A: −10
        let credit_pi = real_per_cell_transfer_pi(0, 10, 0); // asset B: +10
        let mut block = BlockConservation::new();
        block
            .add_contribution(
                PerCellContribution::from_proof_pi(fold_token_id_to_asset(&a), &debit_pi).unwrap(),
            )
            .add_contribution(
                PerCellContribution::from_proof_pi(fold_token_id_to_asset(&b), &credit_pi).unwrap(),
            );
        assert_eq!(
            block.per_asset_balances().get(&class),
            Some(&0),
            "two DISTINCT currencies netted against each other inside one class"
        );
        block.check().expect(
            "THE WOUND: asset A is destroyed and asset B minted from nothing, and the \
             per-asset collector sees a balanced class",
        );

        // The SAME shape over NON-colliding assets is correctly rejected — so the
        // acceptance above is the collision, not a broken collector.
        let mut honest_partition = BlockConservation::new();
        honest_partition
            .add_contribution(
                PerCellContribution::from_proof_pi(BabyBear::new(7), &debit_pi).unwrap(),
            )
            .add_contribution(
                PerCellContribution::from_proof_pi(BabyBear::new(8), &credit_pi).unwrap(),
            );
        assert!(
            honest_partition.check().is_err(),
            "cross-asset borrowing between DISTINCT classes is rejected — the collision is \
             what makes the same forge invisible"
        );

        // ── AFTER: the ids are still distinct, and the refusal sees it. ──
        let err = assert_asset_classes_injective(&[a, b])
            .expect_err("a turn touching both colliding assets must be REFUSED");
        assert_eq!(err.class, class);
        assert!(err.first == a || err.first == b);
        assert!(err.second == a || err.second == b);
        assert_ne!(err.first, err.second);
    }

    /// BOTH POLES for the refusal: honest traffic is untouched.
    ///
    /// * One asset, many cells (the repeated id) — accepted.
    /// * Several genuinely distinct, non-colliding assets — accepted.
    /// * The empty scope — accepted.
    #[test]
    fn injectivity_refusal_admits_honest_multi_asset_traffic() {
        assert!(assert_asset_classes_injective(&[]).is_ok(), "empty scope");

        let a = [7u8; 32];
        assert!(
            assert_asset_classes_injective(&[a, a, a]).is_ok(),
            "ONE asset over many cells is not a collision"
        );

        // 64 distinct assets: at 2^30.87 classes the accidental-collision odds
        // here are ~1e-6, and these particular ids are checked to be clean.
        let mut ids = Vec::new();
        for i in 0u8..64 {
            let mut id = [0u8; 32];
            id[0] = i;
            id[31] = 0xA5;
            ids.push(id);
        }
        let classes: std::collections::BTreeSet<u32> = ids
            .iter()
            .map(|i| fold_token_id_to_asset(i).as_u32())
            .collect();
        assert_eq!(classes.len(), ids.len(), "fixture assets must not collide");
        assert!(
            assert_asset_classes_injective(&ids).is_ok(),
            "honest multi-asset traffic must NOT be falsely refused"
        );
    }
}
