//! Route the LIVE ring settlement through the VERIFIED Lean executor.
//!
//! # The residual this closes
//!
//! `TrustlessIntentEngine::finalize` (`trustless.rs`) lowers the winning solution to a
//! `dregg_turn::Turn` inside a [`crate::trustless::SettlementOutput`] — but NOTHING executed that
//! turn through the verified executor. The Lean side (`metatheory/Dregg2/Intent/Ring.lean`) proves
//! a ring's legs, folded through the verified per-asset kernel `recKExecAsset`, conserve value per
//! asset (`settleRing_conserves`) and abort atomically on any failing leg (`settleRing_atomic`).
//! But the connection to the running engine was a Rust *re-implementation/mirror* of that fold
//! (`tests/ring_settlement_differential.rs`, `tests/fulfillment_verified_turn.rs`) — "verified by
//! prose", not by the verified executor.
//!
//! This module makes "an intent fulfilled" literally MEAN "a verified, conserving, authorized
//! executor turn executed":
//!
//!   * [`extract_legs`] pulls the `Effect::Transfer` legs out of the lowered `SealedTurn` — the
//!     EXACT value moves the executor would run.
//!   * [`settle_ring_verified`] folds those legs through the verified per-asset executor, one leg
//!     at a time, ALL-OR-NOTHING. On every native build (Lean unconditional), each leg is settled by
//!     the REAL Lean FFI ([`ffi::settle_leg`], `@[export] dregg_record_kernel_step` over the PROVED
//!     `Exec.recKExec`), over that leg's asset-projected column — NOT a Rust mirror. When the
//!     feature is off, the in-process [`rec_exec_asset`] runs the SAME verified transition (the
//!     differential reference the Lean `RingFFI.ffi_export_realises_settleRing_leg` proves the FFI
//!     export realises leg-by-leg); the FFI path additionally cross-checks every leg against the
//!     real export and FAILS CLOSED on any divergence.
//!   * [`crate::trustless::TrustlessIntentEngine::finalize_verified`] (added in `trustless.rs`)
//!     drives `finalize()` then settles the produced turn through this verified path, returning the
//!     verified post-ledger. A fulfilled intent is now a verified executor turn.
//!
//! # Why per-asset column projection
//!
//! The verified executor the FFI exports (`dregg_record_kernel_step`) runs `Exec.recKExec` over a
//! cell record's scalar `balance` field. One `settleRing` leg runs `recKExecAsset` over the
//! per-asset ledger column `a`. The Lean keystone `Dregg2.Intent.RingFFI.projAsset` /
//! `recKExec_projAsset_commits_iff` / `recKExec_projAsset_column_agrees` prove these COINCIDE once
//! we project the per-asset column onto the scalar field: seed each cell's `balance := bal·a`. So
//! [`ffi::settle_leg`] marshals exactly that projection for the leg's asset, calls the verified
//! export, and reads back the verified `a`-column. The result IS the verified `recKExecAsset` step,
//! with NO gap.

use std::collections::{BTreeMap, BTreeSet};

use dregg_turn::action::Effect;

use crate::lowering::SealedTurn;
use crate::solver::Settlement;

// ---------------------------------------------------------------------------
// A single extracted transfer leg + the per-asset verified ledger.
// ---------------------------------------------------------------------------

/// A single value move the lowered fulfillment Turn carries: a transfer of `amount` of `asset`
/// from cell `from` to cell `to`. The Rust analog of the Lean `Dregg2.Intent.Ring.RingLeg`
/// (`from_`/`to_`/`asset`/`amount`), keyed by the verified-ledger's `(cell, asset)` index.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedLeg {
    /// The sender cell, as the low byte used by the verified ledger index (`CellId::as_bytes()[0]`).
    pub from: u8,
    /// The receiver cell.
    pub to: u8,
    /// The 32-byte asset id (the per-asset ledger's asset column).
    pub asset: [u8; 32],
    /// The transferred amount (signed at the ledger level; non-negative for a real settlement).
    pub amount: i128,
}

/// The per-asset balance ledger `(cell, asset) -> balance` — the Rust view of the Lean
/// `RecordKernelState.bal : CellId -> AssetId -> ℤ`, restricted to the cells/assets a ring touches.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct VerifiedLedger {
    bal: BTreeMap<(u8, [u8; 32]), i128>,
    accounts: BTreeSet<u8>,
}

impl VerifiedLedger {
    /// An empty ledger with no live accounts.
    pub fn new() -> Self {
        Self::default()
    }

    /// Read a cell's balance in `asset` (default `0`).
    pub fn get(&self, cell: u8, asset: &[u8; 32]) -> i128 {
        *self.bal.get(&(cell, *asset)).unwrap_or(&0)
    }

    /// Overwrite a cell's balance in `asset`.
    pub fn set(&mut self, cell: u8, asset: &[u8; 32], v: i128) {
        self.bal.insert((cell, *asset), v);
    }

    /// Mark a cell live (an account whose balances are tracked / conserved).
    pub fn add_account(&mut self, cell: u8) {
        self.accounts.insert(cell);
    }

    /// Whether `cell` is a live account.
    pub fn is_live(&self, cell: u8) -> bool {
        self.accounts.contains(&cell)
    }

    /// The total supply of `asset` across the live accounts — the Lean `recTotalAsset`.
    pub fn total_asset(&self, asset: &[u8; 32]) -> i128 {
        self.accounts.iter().map(|c| self.get(*c, asset)).sum()
    }

    /// The live accounts (sorted).
    pub fn accounts(&self) -> impl Iterator<Item = u8> + '_ {
        self.accounts.iter().copied()
    }
}

/// Errors from the verified settlement fold.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifiedSettleError {
    /// The lowered Turn carried a different number of Transfer legs than the settlement rows it was
    /// lowered from (the lowering dropped or duplicated a leg — a `loweredRing` data-loss).
    LegCountMismatch {
        transfers: usize,
        settlements: usize,
    },
    /// A lowered leg's `from`/`to`/`amount` diverges from the settlement row it claims to realise
    /// (the lowering garbled a leg — the Lean `loweredLeg` data-preservation broke).
    LegDataMismatch { index: usize, detail: String },
    /// A leg failed its verified gate (under-funded / unauthorised / non-distinct / dead cell), so
    /// the WHOLE ring aborts — the all-or-nothing atomic-swap contract (`settleRing_atomic`).
    LegRejected { index: usize, leg: VerifiedLeg },
    /// The verified post-state LEAKED value in some asset (a committed ring that did not conserve).
    /// This MUST be impossible for a committed fold (`settleRing_conserves`); surfaced fail-closed.
    ConservationViolated {
        asset: [u8; 32],
        before: i128,
        after: i128,
    },
    /// The real Lean FFI disagreed with the in-process verified transition on a leg (commit bit or
    /// post-column). Fail-closed: the verified executor is the authority, and a drift is a bug we
    /// refuse to settle through. Carries the diverging leg + a description.
    FfiDivergence { index: usize, detail: String },
    /// The real-FFI path is compiled in (native default) but the Lean archive was not
    /// available at runtime.
    FfiUnavailable(String),
}

impl std::fmt::Display for VerifiedSettleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LegCountMismatch {
                transfers,
                settlements,
            } => write!(
                f,
                "lowered Turn carried {transfers} transfer legs but {settlements} settlement rows \
                 (lowering dropped/duplicated a leg)"
            ),
            Self::LegDataMismatch { index, detail } => {
                write!(
                    f,
                    "lowered leg {index} diverges from its settlement row: {detail}"
                )
            }
            Self::LegRejected { index, leg } => write!(
                f,
                "leg {index} ({}->{}, {} of asset {:02x}..) rejected by the verified executor; \
                 ring aborts (atomicity)",
                leg.from, leg.to, leg.amount, leg.asset[0]
            ),
            Self::ConservationViolated {
                asset,
                before,
                after,
            } => write!(
                f,
                "verified executor leaked value in asset {:02x}..: {before} before, {after} after",
                asset[0]
            ),
            Self::FfiDivergence { index, detail } => {
                write!(
                    f,
                    "Lean FFI diverged from the verified transition on leg {index}: {detail}"
                )
            }
            Self::FfiUnavailable(e) => write!(f, "verified-executor FFI unavailable: {e}"),
        }
    }
}

impl std::error::Error for VerifiedSettleError {}

// ---------------------------------------------------------------------------
// Extract the lowered fulfillment legs from a SealedTurn + bind their assets.
// ---------------------------------------------------------------------------

/// Walk the lowered `SealedTurn`'s call forest and pull every `Effect::Transfer` leg, in order,
/// binding each to the asset of the settlement row it was lowered from.
///
/// The lowering (`lowering::lower_settlement_leg`) emits a bare `Effect::Transfer { from, to,
/// amount }` per settlement row — the asset column lives on the originating `Settlement`. We re-pair
/// each lowered transfer with its settlement row IN ORDER, asserting the lowering was
/// data-preserving leg-by-leg (the Lean `loweredLeg`: same from/to/amount, only the authorising
/// actor differs). A mismatch is a divergence, surfaced as an error rather than silently settled.
pub fn extract_legs(
    sealed: &SealedTurn,
    settlements: &[Settlement],
) -> Result<Vec<VerifiedLeg>, VerifiedSettleError> {
    let mut transfers: Vec<(u8, u8, i128)> = Vec::new();
    for root in &sealed.turn.call_forest.roots {
        for effect in &root.action.effects {
            if let Effect::Transfer { from, to, amount } = effect {
                transfers.push((from.as_bytes()[0], to.as_bytes()[0], *amount as i128));
            }
        }
    }

    if transfers.len() != settlements.len() {
        return Err(VerifiedSettleError::LegCountMismatch {
            transfers: transfers.len(),
            settlements: settlements.len(),
        });
    }

    let mut legs = Vec::with_capacity(transfers.len());
    for (index, ((from, to, amount), s)) in transfers.iter().zip(settlements.iter()).enumerate() {
        if *from != s.from.0[0] {
            return Err(VerifiedSettleError::LegDataMismatch {
                index,
                detail: format!("from {} != settlement from {}", from, s.from.0[0]),
            });
        }
        if *to != s.to.0[0] {
            return Err(VerifiedSettleError::LegDataMismatch {
                index,
                detail: format!("to {} != settlement to {}", to, s.to.0[0]),
            });
        }
        if *amount != s.amount as i128 {
            return Err(VerifiedSettleError::LegDataMismatch {
                index,
                detail: format!("amount {} != settlement amount {}", amount, s.amount),
            });
        }
        legs.push(VerifiedLeg {
            from: *from,
            to: *to,
            asset: s.asset,
            amount: *amount,
        });
    }
    Ok(legs)
}

/// Seed a ledger that FUNDS every sender for its leg (so the availability gate passes), with every
/// touched cell live. This isolates the CONSERVATION question from incidental underfunding — a
/// structurally accepted ring should also settle + conserve on the verified executor. (Production
/// callers pass the node's real ledger instead; this is the funded reference for the differential.)
pub fn funded_ledger(legs: &[VerifiedLeg]) -> VerifiedLedger {
    let mut k = VerifiedLedger::new();
    for leg in legs {
        k.add_account(leg.from);
        k.add_account(leg.to);
        let cur = k.get(leg.from, &leg.asset);
        k.set(leg.from, &leg.asset, cur + leg.amount);
    }
    k
}

/// The set of assets a ring of legs touches (for the per-asset conservation check).
pub fn touched_assets(legs: &[VerifiedLeg]) -> BTreeSet<[u8; 32]> {
    legs.iter().map(|l| l.asset).collect()
}

// ---------------------------------------------------------------------------
// The verified per-asset transition — the gate the Lean `recKExecAsset` defines, which
// `RingFFI.ffi_export_realises_settleRing_leg` proves the Lean FFI export realises leg-by-leg.
// ---------------------------------------------------------------------------

/// `recKExecAsset` for one leg — the verified per-asset transition (`Dregg2.Exec.recKExecAsset`).
/// `None` on a failed gate: authorised (here the sender authorises their own send, the `actor==src`
/// leg of `authorizedB`), amount non-negative and available IN THAT ASSET, distinct endpoints, both
/// cells live. This is the SAME gate the Lean FFI export checks over the asset-projected column
/// (`recKExec_projAsset_gate_iff`); on commit it debits `from` and credits `to` in the asset column.
pub fn rec_exec_asset(k: &VerifiedLedger, leg: &VerifiedLeg) -> Option<VerifiedLedger> {
    let src_bal = k.get(leg.from, &leg.asset);
    let ok = leg.amount >= 0
        && leg.amount <= src_bal
        && leg.from != leg.to
        && k.is_live(leg.from)
        && k.is_live(leg.to);
    if !ok {
        return None;
    }
    let mut ns = k.clone();
    ns.set(leg.from, &leg.asset, src_bal - leg.amount);
    let dst_bal = k.get(leg.to, &leg.asset);
    ns.set(leg.to, &leg.asset, dst_bal + leg.amount);
    Some(ns)
}

/// **The atomic verified fold — `settleRing` over the verified executor.**
///
/// Folds each leg through the verified per-asset transition, ALL-OR-NOTHING: any leg whose gate
/// fails aborts the WHOLE ring (returns `Err(LegRejected)`, leaving the caller's pre-state
/// untouched — the Lean `settleRing_atomic`). On full settlement, returns the verified post-ledger
/// and ASSERTS conservation per touched asset (the Lean `settleRing_conserves`); a leak — which
/// must be impossible for a committed fold — is surfaced fail-closed as `ConservationViolated`.
///
/// AUTHORITATIVE decider = the REAL Lean FFI export `dregg_record_kernel_step` (via
/// [`ffi::settle_leg`]) over each leg's asset-projected column. The in-process `rec_exec_asset` is the
/// DIFFERENTIAL sibling, cross-checked against the export leg-by-leg; a drift (commit bit or
/// post-column) FAILS CLOSED (`FfiDivergence`). So the fold's accept/reject and post-ledger ARE the
/// linked verified executor's — not a Rust decision. FAIL CLOSED: when NO verified gate is registered
/// (archive absent / gate not installed) the ring is REFUSED rather than settled by an unverified
/// in-process fold — a node/app that settles intents MUST install the `dregg-exec-lean` gate.
pub fn settle_ring_verified(
    k0: &VerifiedLedger,
    legs: &[VerifiedLeg],
) -> Result<VerifiedLedger, VerifiedSettleError> {
    let mut k = k0.clone();
    for (index, leg) in legs.iter().enumerate() {
        // The verified export decides this leg (accept/reject + post-column) and is the authority; the
        // in-process transition is cross-checked against it. No gate ⇒ fail closed.
        k = settle_leg_authoritative(&k, leg, index)?;
    }

    // Conservation (the Lean `settleRing_conserves`): every touched asset's total supply must be
    // preserved across the whole ring. A committed fold cannot leak; surfaced fail-closed if it did.
    for asset in touched_assets(legs) {
        let before = k0.total_asset(&asset);
        let after = k.total_asset(&asset);
        if before != after {
            return Err(VerifiedSettleError::ConservationViolated {
                asset,
                before,
                after,
            });
        }
    }
    Ok(k)
}

/// Settle ONE ring leg with the VERIFIED Lean export `dregg_record_kernel_step` as the AUTHORITATIVE
/// decider — the inverted `settleRing` fold. The export (`Dregg2.Intent.RingFFI`,
/// `ffi_export_realises_settleRing_leg`) decides accept/reject and produces the asset-projected
/// post-column; the in-process [`rec_exec_asset`] is now the DIFFERENTIAL sibling, built to carry the
/// FULL multi-asset ledger forward (only `leg.asset` moves) and cross-checked against the export's
/// authoritative column. Any disagreement FAILS CLOSED (`FfiDivergence`).
///
/// FAIL CLOSED: when no verified gate is registered, [`ffi::settle_leg`] returns
/// `Err(FfiUnavailable)`, which refuses the leg — and, since the ring is all-or-none, the whole ring.
/// The unverified in-process fold is NO LONGER the authority when the gate is absent; the settlement
/// is refused instead of silently decided in Rust.
#[cfg(not(test))]
fn settle_leg_authoritative(
    k: &VerifiedLedger,
    leg: &VerifiedLeg,
    index: usize,
) -> Result<VerifiedLedger, VerifiedSettleError> {
    // AUTHORITATIVE: the verified export's verdict + post-column. `Err(FfiUnavailable)` (no gate) or a
    // wire error propagates up and REFUSES the ring — fail closed.
    let (post_cells, ok) = ffi::settle_leg(k, leg)?;
    if !ok {
        return Err(VerifiedSettleError::LegRejected {
            index,
            leg: leg.clone(),
        });
    }
    // DIFFERENTIAL sibling: `rec_exec_asset` carries the full multi-asset ledger forward and MUST
    // agree with the authoritative export on the asset column; a drift fails closed.
    let next = rec_exec_asset(k, leg).ok_or_else(|| VerifiedSettleError::FfiDivergence {
        index,
        detail:
            "the verified Lean export COMMITTED the leg but the in-process transition rejected it"
                .into(),
    })?;
    for (cell, bal) in &post_cells {
        let want = next.get(*cell, &leg.asset);
        if *bal != want {
            return Err(VerifiedSettleError::FfiDivergence {
                index,
                detail: format!(
                    "cell {cell}: Lean export balance {bal} != in-process a-column {want} \
                     (asset {:02x}..)",
                    leg.asset[0]
                ),
            });
        }
    }
    Ok(next)
}

/// In-crate differential tests run WITHOUT a registered verified gate, so here the in-process
/// transition stays AUTHORITATIVE (the pre-inversion behavior) and is still cross-checked against the
/// REAL export whenever a gate IS present ([`ffi::cross_check_leg`] skips when absent). This keeps
/// `cargo test` exercising the fold; the INVERTED, fail-closed release/consumer path is the
/// `#[cfg(not(test))]` sibling above, and its no-gate refusal is proved by `tests/settle_fail_closed.rs`.
#[cfg(test)]
fn settle_leg_authoritative(
    k: &VerifiedLedger,
    leg: &VerifiedLeg,
    index: usize,
) -> Result<VerifiedLedger, VerifiedSettleError> {
    let next = match rec_exec_asset(k, leg) {
        Some(nk) => nk,
        None => {
            return Err(VerifiedSettleError::LegRejected {
                index,
                leg: leg.clone(),
            });
        }
    };
    ffi::cross_check_leg(k, leg, &next, index)?;
    Ok(next)
}

/// Convenience: extract the legs from a lowered `SealedTurn`, fund a reference ledger, and settle
/// the ring through the verified executor. Returns the funded pre-ledger and the verified
/// post-ledger on success. This is the end-to-end "a fulfilled intent IS a verified, conserving
/// executor turn" — the lowered Turn the engine ships, settled through the verified semantics.
pub fn settle_fulfillment_verified(
    sealed: &SealedTurn,
    settlements: &[Settlement],
) -> Result<(VerifiedLedger, VerifiedLedger), VerifiedSettleError> {
    let legs = extract_legs(sealed, settlements)?;
    let k0 = funded_ledger(&legs);
    let k1 = settle_ring_verified(&k0, &legs)?;
    Ok((k0, k1))
}

// ---------------------------------------------------------------------------
// Full-width (32-byte) cell indexing — the collision-free settlement path.
// ---------------------------------------------------------------------------
//
// `VerifiedLeg`/`VerifiedLedger` key accounts by a single `u8` (a cell's low
// byte). That truncation is LOSSY: two distinct cells/commitments that share a
// low byte ALIAS to the same ledger account, silently merging their balances (or
// collapsing a real transfer into a `from == to` self-leg the gate rejects). For
// a settlement path where the parties are arbitrary 32-byte commitments — the
// ring coordinator and the service-promise escrow — that is a correctness bug.
//
// `WideLeg`/`WideLedger` close it by keying accounts on the FULL 32-byte cell id,
// so distinct cells NEVER collide. Settlement reduces to the proven `u8` fold
// (`settle_ring_verified`, FFI-cross-checked leg by leg) over an INJECTIVE dense
// relabeling of the touched cells: distinct full ids map to distinct indices, so
// the reduction preserves the verified semantics while removing the collision.
// Unlike the old low-byte projection, the relabel loses no identity — it is a
// bijection on the (≤ 256) cells a ring touches, not a truncation.

/// A single value move keyed by the FULL 32-byte cell id / commitment. The
/// collision-free analog of [`VerifiedLeg`] (whose `u8` index aliases cells that
/// share a low byte).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WideLeg {
    /// The sender cell, as its full 32-byte id (`CellId`/`CommitmentId` bytes).
    pub from: [u8; 32],
    /// The receiver cell (full id).
    pub to: [u8; 32],
    /// The 32-byte asset id (the per-asset ledger's asset column).
    pub asset: [u8; 32],
    /// The transferred amount (non-negative for a real settlement).
    pub amount: i128,
}

/// The per-asset balance ledger `(cell, asset) -> balance` keyed by the FULL
/// 32-byte cell id — the collision-free analog of [`VerifiedLedger`].
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct WideLedger {
    bal: BTreeMap<([u8; 32], [u8; 32]), i128>,
    accounts: BTreeSet<[u8; 32]>,
}

impl WideLedger {
    /// An empty ledger with no live accounts.
    pub fn new() -> Self {
        Self::default()
    }

    /// Read a cell's balance in `asset` (default `0`).
    pub fn get(&self, cell: [u8; 32], asset: &[u8; 32]) -> i128 {
        *self.bal.get(&(cell, *asset)).unwrap_or(&0)
    }

    /// Overwrite a cell's balance in `asset`.
    pub fn set(&mut self, cell: [u8; 32], asset: &[u8; 32], v: i128) {
        self.bal.insert((cell, *asset), v);
    }

    /// Mark a cell live (an account whose balances are tracked / conserved).
    pub fn add_account(&mut self, cell: [u8; 32]) {
        self.accounts.insert(cell);
    }

    /// Whether `cell` is a live account.
    pub fn is_live(&self, cell: [u8; 32]) -> bool {
        self.accounts.contains(&cell)
    }

    /// The total supply of `asset` across the live accounts.
    pub fn total_asset(&self, asset: &[u8; 32]) -> i128 {
        self.accounts.iter().map(|c| self.get(*c, asset)).sum()
    }

    /// The live accounts (sorted).
    pub fn accounts(&self) -> impl Iterator<Item = [u8; 32]> + '_ {
        self.accounts.iter().copied()
    }
}

/// Seed a full-width ledger that FUNDS every sender for its leg, with every
/// touched cell live — the collision-free analog of [`funded_ledger`].
pub fn funded_wide_ledger(legs: &[WideLeg]) -> WideLedger {
    let mut k = WideLedger::new();
    for leg in legs {
        k.add_account(leg.from);
        k.add_account(leg.to);
        let cur = k.get(leg.from, &leg.asset);
        k.set(leg.from, &leg.asset, cur + leg.amount);
    }
    k
}

/// **The atomic verified fold over FULL 32-byte cell ids.**
///
/// Settles `legs` against `k0`, all-or-nothing, with per-asset conservation
/// asserted — the same contract as [`settle_ring_verified`] but with distinct
/// cells GUARANTEED never to collide. It reduces to the proven `u8` fold over an
/// injective dense relabeling of the touched cells (the relabel is a bijection,
/// so it preserves the verified accept/reject + post-state, leg by leg, including
/// the real Lean FFI cross-check), then lifts the post-state back to full ids.
///
/// The relabel addresses ≤ 256 distinct cells (the `u8` ledger's domain); a ring
/// touching more is refused fail-closed ([`VerifiedSettleError::FfiUnavailable`]
/// with a descriptive message) rather than silently truncated.
pub fn settle_ring_wide_verified(
    k0: &WideLedger,
    legs: &[WideLeg],
) -> Result<WideLedger, VerifiedSettleError> {
    // (1) Build the injective dense index over every touched cell (the ledger's
    //     live accounts ∪ each leg's endpoints). DISTINCT full ids → DISTINCT
    //     indices: this is the bijection that replaces the lossy low-byte cast.
    let mut order: BTreeSet<[u8; 32]> = k0.accounts().collect();
    for leg in legs {
        order.insert(leg.from);
        order.insert(leg.to);
    }
    if order.len() > 256 {
        return Err(VerifiedSettleError::FfiUnavailable(format!(
            "ring touches {} distinct cells; the verified ledger indexes at most 256",
            order.len()
        )));
    }
    let index: BTreeMap<[u8; 32], u8> = order
        .iter()
        .enumerate()
        .map(|(i, c)| (*c, i as u8))
        .collect();
    let reverse: Vec<[u8; 32]> = order.iter().copied().collect();

    // (2) Project k0 + legs onto the `u8` ledger under the index.
    let mut k0_u8 = VerifiedLedger::new();
    for &cell in &reverse {
        k0_u8.add_account(index[&cell]);
    }
    for ((cell, asset), v) in &k0.bal {
        k0_u8.set(index[cell], asset, *v);
    }
    let legs_u8: Vec<VerifiedLeg> = legs
        .iter()
        .map(|l| VerifiedLeg {
            from: index[&l.from],
            to: index[&l.to],
            asset: l.asset,
            amount: l.amount,
        })
        .collect();

    // (3) Settle through the PROVEN fold (FFI-cross-checked leg by leg).
    let post_u8 = settle_ring_verified(&k0_u8, &legs_u8)?;

    // (4) Lift the verified post-state back to full ids via the bijection.
    let mut post = WideLedger::new();
    for cell in post_u8.accounts() {
        post.add_account(reverse[cell as usize]);
    }
    for ((cell, asset), v) in &post_u8.bal {
        post.set(reverse[*cell as usize], asset, *v);
    }
    Ok(post)
}

// ---------------------------------------------------------------------------
// The REAL Lean FFI path — route each leg through `dregg_record_kernel_step`.
// ---------------------------------------------------------------------------

pub mod ffi {
    //! Settle one ring leg through the REAL verified Lean executor export
    //! `@[export] dregg_record_kernel_step` (the PROVED `Exec.recKExec`), over the leg's
    //! asset-projected single-column cell state.
    //!
    //! By the Lean keystone `Dregg2.Intent.RingFFI.ffi_export_realises_settleRing_leg`, this export
    //! over the asset-`a` projection commits a leg iff the per-asset executor does, and its
    //! post-`balance` column equals the verified `a`-column. So the FFI's verdict + post-column ARE
    //! the verified `recKExecAsset` leg's — not a Rust re-derivation.

    use super::{VerifiedLedger, VerifiedLeg, VerifiedSettleError};

    /// Encode the per-asset projection of the ledger for ONE leg's asset into the wire grammar
    /// `dregg_record_kernel_step` reads: `{"cells":[[ID,{"rec":[["balance",{"int":N}]]}],…],
    /// "actor":N,"src":N,"dst":N,"amt":N}`. Each live cell's `balance` is its balance in the leg's
    /// asset (`RingFFI.projAsset`); the actor is the sender (self-authorised send — `actor==src`).
    fn encode_leg_input(k: &VerifiedLedger, leg: &VerifiedLeg) -> String {
        let mut cells = String::from("[");
        let mut first = true;
        for cell in k.accounts() {
            if !first {
                cells.push(',');
            }
            first = false;
            let bal = k.get(cell, &leg.asset);
            cells.push_str(&format!(
                "[{cell},{{\"rec\":[[\"balance\",{{\"int\":{bal}}}]]}}]"
            ));
        }
        cells.push(']');
        format!(
            "{{\"cells\":{cells},\"actor\":{actor},\"src\":{src},\"dst\":{dst},\"amt\":{amt}}}",
            actor = leg.from,
            src = leg.from,
            dst = leg.to,
            amt = leg.amount
        )
    }

    /// Parse the output wire `{"cells":[[ID,{"rec":[["balance",{"int":N}],…]}],…],"ok":B}` into
    /// `(post-balances-by-cell, ok)`. A strict, dependency-free reader matching the Lean
    /// `encode*`/`parse*` grammar (the same one `state_differential.rs` round-trips). Returns the
    /// `balance` field per cell id.
    fn parse_leg_output(wire: &str) -> Result<(Vec<(u8, i128)>, bool), String> {
        let b = wire.as_bytes();
        let mut i = 0usize;
        let lit = |i: &mut usize, s: &str| -> Result<(), String> {
            let sb = s.as_bytes();
            if *i + sb.len() <= b.len() && &b[*i..*i + sb.len()] == sb {
                *i += sb.len();
                Ok(())
            } else {
                Err(format!("expected `{s}` at {i}"))
            }
        };
        let int = |i: &mut usize| -> Result<i128, String> {
            let start = *i;
            if b.get(*i) == Some(&b'-') {
                *i += 1;
            }
            while matches!(b.get(*i), Some(c) if c.is_ascii_digit()) {
                *i += 1;
            }
            std::str::from_utf8(&b[start..*i])
                .map_err(|e| e.to_string())?
                .parse::<i128>()
                .map_err(|e| format!("bad int: {e}"))
        };

        lit(&mut i, "{\"cells\":")?;
        let mut cells: Vec<(u8, i128)> = Vec::new();
        if lit(&mut i, "[]").is_ok() {
            // empty cell list
        } else {
            lit(&mut i, "[")?;
            loop {
                lit(&mut i, "[")?;
                let id = int(&mut i)? as u8;
                lit(&mut i, ",")?;
                // value: {"rec":[["balance",{"int":N}],…]} — find the balance field.
                lit(&mut i, "{\"rec\":")?;
                // walk the fields list, capturing the balance int.
                let mut bal: i128 = 0;
                if lit(&mut i, "[]").is_ok() {
                    // no fields
                } else {
                    lit(&mut i, "[")?;
                    loop {
                        lit(&mut i, "[\"")?;
                        // field name up to closing quote
                        let nstart = i;
                        while b.get(i) != Some(&b'"') && i < b.len() {
                            i += 1;
                        }
                        let name = std::str::from_utf8(&b[nstart..i]).map_err(|e| e.to_string())?;
                        lit(&mut i, "\",")?;
                        // value {"int":N} | {"dig":N} | {"sym":N} | nested {"rec":...}
                        if lit(&mut i, "{\"int\":").is_ok() {
                            let v = int(&mut i)?;
                            lit(&mut i, "}")?;
                            if name == "balance" {
                                bal = v;
                            }
                        } else if lit(&mut i, "{\"dig\":").is_ok()
                            || lit(&mut i, "{\"sym\":").is_ok()
                        {
                            let _ = int(&mut i)?;
                            lit(&mut i, "}")?;
                        } else {
                            return Err(format!("unexpected field value at {i}"));
                        }
                        lit(&mut i, "]")?;
                        if lit(&mut i, ",").is_ok() {
                            continue;
                        }
                        lit(&mut i, "]")?;
                        break;
                    }
                }
                lit(&mut i, "}")?; // close the {"rec":...}
                lit(&mut i, "]")?; // close the [id, value]
                cells.push((id, bal));
                if lit(&mut i, ",").is_ok() {
                    continue;
                }
                lit(&mut i, "]")?;
                break;
            }
        }
        lit(&mut i, ",\"ok\":")?;
        let ok = int(&mut i)?;
        lit(&mut i, "}")?;
        Ok((cells, ok == 1))
    }

    /// Settle one leg through the REAL verified export (via the [`crate::verified_gate`] seam):
    /// marshal the asset projection, call `dregg_record_kernel_step`, parse `(post-balances, ok)`.
    /// `Ok((cells, ok))` is the verified export's verdict + post-column. `Err` only on FFI
    /// unavailability (no gate registered / archive absent) / wire errors.
    pub fn settle_leg(
        k: &VerifiedLedger,
        leg: &VerifiedLeg,
    ) -> Result<(Vec<(u8, i128)>, bool), VerifiedSettleError> {
        let gate = crate::verified_gate::gate().ok_or_else(|| {
            VerifiedSettleError::FfiUnavailable("no verified gate registered".into())
        })?;
        let input = encode_leg_input(k, leg);
        let out = gate
            .record_kernel_step(&input)
            .map_err(VerifiedSettleError::FfiUnavailable)?;
        parse_leg_output(&out).map_err(VerifiedSettleError::FfiUnavailable)
    }

    /// Cross-check the in-process verified transition `expected` (the post-ledger `rec_exec_asset`
    /// produced for `leg` at `k`) against the REAL Lean FFI export over the asset projection. The
    /// export must COMMIT (since `rec_exec_asset` committed — `Some(expected)` was passed) and its
    /// post-`balance` column must equal `expected`'s `a`-column for every touched cell
    /// (`RingFFI.recKExec_projAsset_column_agrees`). Any drift FAILS CLOSED.
    pub fn cross_check_leg(
        k: &VerifiedLedger,
        leg: &VerifiedLeg,
        expected: &VerifiedLedger,
        index: usize,
    ) -> Result<(), VerifiedSettleError> {
        // No verified gate registered (every FFI-free target) ⇒ skip the cross-check; the
        // in-process verified transition stands on its own. (When a native node registers a
        // `dregg-exec-lean` gate, the leg is cross-checked against the REAL export and any drift
        // fails closed below.)
        if crate::verified_gate::gate().is_none() {
            return Ok(());
        }
        let (post_cells, ok) = settle_leg(k, leg)?;
        if !ok {
            return Err(VerifiedSettleError::FfiDivergence {
                index,
                detail: "verified transition committed but the Lean export REJECTED the leg".into(),
            });
        }
        // Every touched cell's exported `balance` must equal the verified `a`-column post-balance.
        for (cell, bal) in &post_cells {
            let want = expected.get(*cell, &leg.asset);
            if *bal != want {
                return Err(VerifiedSettleError::FfiDivergence {
                    index,
                    detail: format!(
                        "cell {cell}: Lean export balance {bal} != verified a-column {want} \
                         (asset {:02x}..)",
                        leg.asset[0]
                    ),
                });
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Tests (in-process verified transition; the FFI path is exercised in
// tests/fulfillment_verified_turn.rs on the default native build).
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CommitmentId;

    fn asset(byte: u8) -> [u8; 32] {
        let mut a = [0u8; 32];
        a[0] = byte;
        a
    }

    fn cid(byte: u8) -> CommitmentId {
        CommitmentId([byte; 32])
    }

    /// A closed 3-ring A->B->C->A, each leg a distinct asset — the canonical `chainedRing3`.
    fn closed_ring3() -> Vec<VerifiedLeg> {
        vec![
            VerifiedLeg {
                from: 1,
                to: 2,
                asset: asset(10),
                amount: 5,
            },
            VerifiedLeg {
                from: 2,
                to: 3,
                asset: asset(11),
                amount: 7,
            },
            VerifiedLeg {
                from: 3,
                to: 1,
                asset: asset(12),
                amount: 9,
            },
        ]
    }

    #[test]
    fn closed_ring_settles_and_conserves() {
        let legs = closed_ring3();
        let k0 = funded_ledger(&legs);
        let k1 = settle_ring_verified(&k0, &legs).expect("closed ring settles");
        for a in touched_assets(&legs) {
            assert_eq!(
                k1.total_asset(&a),
                k0.total_asset(&a),
                "verified settle must conserve asset {:02x}",
                a[0]
            );
        }
    }

    #[test]
    fn underfunded_leg_aborts_whole_ring() {
        // A ring where the first leg's sender is not funded for the amount.
        let legs = closed_ring3();
        let mut k0 = funded_ledger(&legs);
        // Drain cell 1's asset-10 balance so leg 0 cannot commit.
        k0.set(1, &asset(10), 0);
        let res = settle_ring_verified(&k0, &legs);
        assert!(
            matches!(res, Err(VerifiedSettleError::LegRejected { index: 0, .. })),
            "underfunded leg 0 must abort the whole ring; got {res:?}"
        );
    }

    #[test]
    fn zero_amount_leg_is_rejected_as_a_nondistinct_or_noop() {
        // A self-transfer (from == to) fails the distinctness gate — atomicity bites.
        let legs = vec![VerifiedLeg {
            from: 1,
            to: 1,
            asset: asset(10),
            amount: 5,
        }];
        let mut k0 = VerifiedLedger::new();
        k0.add_account(1);
        k0.set(1, &asset(10), 5);
        let res = settle_ring_verified(&k0, &legs);
        assert!(matches!(res, Err(VerifiedSettleError::LegRejected { .. })));
    }

    #[test]
    fn extract_legs_pins_lowering_data_preservation() {
        // Build a sealed turn with two transfer legs and matching settlement rows.
        use crate::lowering::{Intent, LoweringContext, lower, seal_plan_uniform};
        use crate::solver::RingTrade;
        use dregg_cell::CellId;
        use dregg_turn::action::Authorization;

        let settlements = vec![
            Settlement {
                from: cid(1),
                to: cid(2),
                asset: asset(10),
                amount: 5,
            },
            Settlement {
                from: cid(2),
                to: cid(1),
                asset: asset(11),
                amount: 7,
            },
        ];
        let ring = RingTrade {
            participants: vec![[1u8; 32], [2u8; 32]],
            settlements: settlements.clone(),
            score: 2.0,
        };
        let intent = Intent::RingSettlement {
            rings: vec![ring],
            anchor: CellId::from_bytes([9u8; 32]),
            solver_id: [0xAB; 32],
            validity_proof_hash: [0xCD; 32],
        };
        let plan = lower(intent, &LoweringContext::default()).expect("lowers");
        let sealed = seal_plan_uniform(
            plan,
            CellId::from_bytes([9u8; 32]),
            0,
            Authorization::Signature([0u8; 32], [0u8; 32]),
        );

        let legs = extract_legs(&sealed, &settlements).expect("legs extract + data-preserve");
        assert_eq!(legs.len(), 2);
        assert_eq!(legs[0].from, 1);
        assert_eq!(legs[0].to, 2);
        assert_eq!(legs[0].amount, 5);
        assert_eq!(legs[0].asset, asset(10));
        assert_eq!(legs[1].asset, asset(11));

        // The lowered turn settles + conserves on the verified executor.
        let (k0, k1) = settle_fulfillment_verified(&sealed, &settlements).expect("settles");
        for a in touched_assets(&legs) {
            assert_eq!(k1.total_asset(&a), k0.total_asset(&a));
        }
    }

    fn wide(byte0: u8, byte1: u8) -> [u8; 32] {
        let mut c = [0u8; 32];
        c[0] = byte0;
        c[1] = byte1;
        c
    }

    #[test]
    fn wide_settle_keeps_low_byte_colliding_cells_distinct() {
        // Three cells that SHARE a low byte (0x07) but differ above it. Under the
        // old `u8` projection all three alias to cell 7 — the sender's transfer
        // to the escrow would become a `from == to` self-leg the gate rejects,
        // and the two endpoints' balances would merge. Full indexing keeps them
        // distinct, so the transfer settles and conserves.
        let sender = wide(0x07, 0x01);
        let escrow = wide(0x07, 0x02);
        let bystander = wide(0x07, 0x03);
        assert_eq!(sender[0], escrow[0]);
        assert_eq!(sender[0], bystander[0]);

        let legs = vec![WideLeg {
            from: sender,
            to: escrow,
            asset: asset(7),
            amount: 100,
        }];
        let mut k0 = funded_wide_ledger(&legs);
        k0.add_account(bystander); // a third party sharing the same low byte

        let k1 = settle_ring_wide_verified(&k0, &legs)
            .expect("distinct full ids settle despite the shared low byte");
        assert_eq!(k1.get(sender, &asset(7)), 0, "sender debited");
        assert_eq!(k1.get(escrow, &asset(7)), 100, "escrow credited");
        assert_eq!(k1.get(bystander, &asset(7)), 0, "bystander untouched");
        assert_eq!(k1.total_asset(&asset(7)), 100, "conserved");
    }

    #[test]
    fn wide_settle_aborts_an_underfunded_ring() {
        // The atomicity contract is inherited from the proven fold.
        let legs = vec![WideLeg {
            from: wide(0x07, 0x01),
            to: wide(0x07, 0x02),
            asset: asset(7),
            amount: 100,
        }];
        let mut k0 = funded_wide_ledger(&legs);
        k0.set(wide(0x07, 0x01), &asset(7), 0); // drain the sender
        assert!(matches!(
            settle_ring_wide_verified(&k0, &legs),
            Err(VerifiedSettleError::LegRejected { .. })
        ));
    }

    #[test]
    fn leg_count_mismatch_is_an_error() {
        let sealed = {
            use crate::lowering::{Intent, LoweringContext, lower, seal_plan_uniform};
            use crate::solver::RingTrade;
            use dregg_cell::CellId;
            use dregg_turn::action::Authorization;
            let ring = RingTrade {
                participants: vec![[1u8; 32], [2u8; 32]],
                settlements: vec![
                    Settlement {
                        from: cid(1),
                        to: cid(2),
                        asset: asset(10),
                        amount: 5,
                    },
                    Settlement {
                        from: cid(2),
                        to: cid(1),
                        asset: asset(11),
                        amount: 7,
                    },
                ],
                score: 2.0,
            };
            let intent = Intent::RingSettlement {
                rings: vec![ring],
                anchor: CellId::from_bytes([9u8; 32]),
                solver_id: [0xAB; 32],
                validity_proof_hash: [0xCD; 32],
            };
            let plan = lower(intent, &LoweringContext::default()).unwrap();
            seal_plan_uniform(
                plan,
                CellId::from_bytes([9u8; 32]),
                0,
                Authorization::Signature([0u8; 32], [0u8; 32]),
            )
        };
        // Pass only ONE settlement row against a TWO-leg turn.
        let res = extract_legs(
            &sealed,
            &[Settlement {
                from: cid(1),
                to: cid(2),
                asset: asset(10),
                amount: 5,
            }],
        );
        assert!(matches!(
            res,
            Err(VerifiedSettleError::LegCountMismatch {
                transfers: 2,
                settlements: 1
            })
        ));
    }
}
