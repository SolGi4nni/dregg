//! Economic slash loop — from a proven custody fault to a seized bond.
//!
//! This module WELDS three parts that already exist independently:
//!
//!   1. the referee — [`dregg_captp::custody::adjudicate_from_inbox`], the
//!      crypto-sound, reorg-robust verdict (`slash` iff a well-formed receipt +
//!      the inbox cell shows the box was never delivered and never refunded);
//!   2. the executor-enforced slash transition —
//!      [`dregg_storage_templates::relay_operator::build_slash_action`], which
//!      decrements `BOND_AMOUNT_SLOT` while advancing `DISPUTE_COUNT_SLOT` by
//!      exactly one (`BoundedBy{bond,dispute}` + `FieldDelta{dispute,+1}`); and
//!   3. the relay service HTTP surface (`relay_service.rs`), which had no
//!      dispute/slash route.
//!
//! The loop is **bilateral**: an owner-anchored fraud proof (the relay's OWN
//! signed [`dregg_captp::custody::CustodyReceipt`] against the inbox cell's
//! authenticated state), NOT a global-consensus vote.
//!
//! # What is REAL here
//!
//!   * [`referee_then_plan`] runs the real referee and, on a slash verdict,
//!     computes a [`SlashPlan`] whose seizure is capped by the bond floor
//!     (`bond_min`) — the same floor the relay-operator slash transition
//!     enforces.
//!   * [`build_slash_turn`] drives the real [`build_slash_action`] and appends
//!     the effects that dispose of the seized bond FROM the relay cell: a
//!     bounded RESTITUTION [`Effect::Transfer`] to the wronged inbox owner
//!     (their proven loss + a small bounty), and the REMAINDER as a conserving
//!     [`Effect::Transfer`] to the configured remainder destination
//!     ([`default_slash_treasury`] by default). The bond leaves the operator in
//!     full (`restitution + remainder == seized`); nothing is destroyed.
//!     `build_slash_action` deliberately omits these (its doc: "the accompanying
//!     `Effect::Transfer` … is the cclerk-side composition"); this is that
//!     composition. Restitution makes the wronged party whole; the remainder is a
//!     public fault-beacon + funding flywheel at a deployment-chosen cell (an OSS
//!     fund, a lottery among grain-owners, or a burn address) — never a windfall
//!     to the disputer, never a protocol-governed entity.
//!   * [`handle_dispute`] is the `POST /relay/dispute` intake: it gates on the
//!     referee's own `well_formed`, reads the inbox cell (the content-addressed
//!     delivered set is the service's `delivery_proofs` cache), runs the referee,
//!     and on a slash applies the transition to the in-process template mirror
//!     (bond down, dispute +1 — the same slot moves the ledger action encodes).
//!
//! # What still needs promotion (honest gaps)
//!
//!   * **Emitting the signed ledger turn from the route.** [`build_slash_turn`]
//!     produces the real [`Action`] (bond/dispute `SetField`s + the conserving
//!     restitution `Transfer` + the conserving remainder `Transfer`), and it is
//!     unit-tested with a test
//!     cipherclerk. The legacy in-process [`crate::relay_service::RelayState`]
//!     holds no [`AppCipherclerk`], no governance slash capability, and no minted
//!     relay-operator `CellId`, so the route mutates the MIRROR and reports the
//!     plan rather than submitting a signed turn. Promotion = give `RelayState`
//!     the operator's clerk + the real relay `CellId`, then call
//!     [`build_slash_turn`] and submit through the operator's turn pipeline.
//!   * **Cell-program intake now exists; this route is mirror-only.** The
//!     dispute intake on the cell-program path is
//!     [`crate::relay_slash_intake::intake_dispute`]: on a conviction it
//!     produces a signed Turn invoking the relay-operator CELL's `slash`
//!     method (the [`dregg_storage_templates::relay_operator`]
//!     executor-enforced transition) with the conserving payout composed in,
//!     and it is tested end-to-end against an executor with the cell program
//!     installed. The legacy `POST /relay/dispute` below remains the
//!     deprecated in-process view (it mutates the MIRROR only); wiring the
//!     intake turn into the node's live turn-submission pipeline is the
//!     remaining seam.
//!   * **The refund witness.** The in-process service has no per-message refund
//!     record queryable by `content_hash`, so [`handle_dispute`] passes
//!     `refund_recorded = false` to
//!     [`dregg_captp::custody::InboxState::from_dequeue`]. A box that was
//!     refunded (not delivered) would therefore read as `Dropped`. Production
//!     must source the refund bit from the operator's refund ledger / the cell's
//!     `refund_recorded` state. Until then a slash verdict is only sound for
//!     boxes that were genuinely neither delivered nor refunded.
//!   * The referee returns a **`bool`** (`true` = slash), NOT a magnitude: the
//!     custody model adjudicates GUILT, not a penalty. The seizure amount is a
//!     policy input ([`DEFAULT_SLASH_PENALTY`] / the disputant's request), capped
//!     by the bond floor.

use axum::Json;
use axum::extract::State;
use axum::http::StatusCode;
use serde::{Deserialize, Serialize};

use dregg_app_framework::{Action, AppCipherclerk, AssetId, CellId, Effect};
use dregg_captp::custody::{EvidenceOfDrop, InboxState, adjudicate_from_inbox};
use dregg_storage_templates::relay_operator::{
    BOND_AMOUNT_SLOT, BOND_MIN_SLOT, DISPUTE_COUNT_SLOT, build_slash_action,
};

use crate::relay_service::SharedRelayState;

/// Default TOTAL seizure requested on a proven drop (computrons), used when the
/// disputant does not name one. Always capped by the bond floor. The seizure is
/// split into a bounded restitution to the wronged party + a remainder Transferred
/// to the remainder destination (conserving, not destroyed).
pub const DEFAULT_SLASH_PENALTY: u64 = 1_000;

/// Default bounty added to the wronged party's proven fee when bounding
/// restitution (computrons). Small — it compensates the cost of raising a
/// well-formed dispute without turning restitution into a windfall; everything
/// beyond `proven_fee + this` goes to the remainder destination (the treasury).
pub const DEFAULT_RESTITUTION_BOUNTY: u64 = 100;

/// The default remainder destination — a derived treasury / OSS-fund cell. A slash
/// remainder Transferred here is a public fault-beacon (a windfall appeared => a slash
/// fired somewhere) and a funding flywheel. Deployments override `SlashPlan::remainder_dest`
/// (a lottery among grain-owners, an OSS fund, or a burn address). NOT a protocol-governed
/// entity — just the cell a deployment points slashes at.
pub fn default_slash_treasury() -> CellId {
    CellId::from_bytes(*blake3::hash(b"dregg-slash-treasury-v1").as_bytes())
}

// =============================================================================
// The payout split: restitution to the wronged party, remainder to the treasury
// =============================================================================

/// How a seizure is disposed. A conviction does NOT hand the whole bond to the
/// disputer, nor does it accrue to any global-owned entity: the wronged party is
/// made whole up to their proven loss (plus a small bounty), and everything
/// beyond that is Transferred to the configured remainder destination (a treasury
/// by default). Both legs are CONSERVING Transfers out of the relay cell; nothing
/// is destroyed. By
/// construction `restitution + remainder == seized`: the operator loses the full
/// seizure, the wronged party gains `restitution`, and the `remainder` is
/// Transferred to the remainder destination (conserving — supply is unchanged).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SlashPayout {
    /// Computrons restituted to the wronged inbox owner (their proven loss,
    /// bounded by the seizure).
    pub restitution: u64,
    /// Computrons routed to the configured remainder destination (a treasury /
    /// OSS-fund cell by default) — the remainder of the seizure after restitution.
    pub remainder: u64,
}

impl SlashPayout {
    /// Split a `seized` seizure into a bounded restitution + a remainder.
    ///
    /// Restitution is `min(seized, proven_fee + bounty)`: the wronged party never
    /// receives more than their proven loss (fee) plus a small bounty, and never
    /// more than was actually seized. The remainder is Transferred to the remainder
    /// destination (conserving, not destroyed). The seizure is fully accounted:
    /// `restitution + remainder == seized`.
    pub fn split(seized: u64, proven_fee: u64, bounty: u64) -> SlashPayout {
        let restitution = seized.min(proven_fee.saturating_add(bounty));
        SlashPayout {
            restitution,
            remainder: seized - restitution,
        }
    }

    /// The total disposed — always equal to the seizure
    /// (`restitution + remainder`).
    pub fn total(&self) -> u64 {
        self.restitution + self.remainder
    }
}

// =============================================================================
// The junior tranche: a $DREGG first-loss holding, forfeited PRICE-FREE
// =============================================================================

/// The $DREGG **junior** first-loss tranche of a two-tranche bond.
///
/// A separate Payable holding — its own cell, its own asset: $DREGG is not the
/// relay cell's computron balance, so it lives in a distinct bond cell (a cell
/// holds value in exactly one asset). On a slash it forfeits PROPORTIONALLY with
/// pure integer arithmetic and **no price input** (obligation 4 — the slash path
/// is oracle-free), and it NEVER counts toward the deterrence floor: the senior
/// (quote) tranche alone bears the penalty. See [`junior_forfeit`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JuniorTranche {
    /// The $DREGG bond cell — the `from` of the conserving junior forfeit
    /// [`Effect::Transfer`].
    pub junior_cell: CellId,
    /// The junior asset ($DREGG). Carried so the forfeit leg is asset-explicit
    /// even though a kernel `Transfer` is per-cell (the cell holds one asset).
    pub junior_asset: AssetId,
    /// The junior bond before this slash.
    pub junior_amount: u64,
    /// $DREGG forfeited: `min(junior_amount, ⌊junior_amount · seized_senior /
    /// slashable_senior_headroom⌋)` — the SAME fraction of slashable collateral
    /// the senior seized, in integer arithmetic, with no price term.
    pub seized_junior: u64,
    /// The junior bond after this slash (`junior_amount − seized_junior`, ≥ 0).
    pub new_junior_amount: u64,
}

/// The proportional junior forfeit — the **price-free kernel** of the two-tranche
/// rule (obligation 4's Rust shadow).
///
/// `seized_junior = min(junior_amount, ⌊junior_amount · seized_senior /
/// slashable_senior_headroom⌋)`: the junior loses the same *fraction* of its bond
/// that the senior lost of its slashable collateral. The intermediate product is
/// computed in `u128` (no overflow), the result never exceeds `junior_amount`
/// (since `seized_senior ≤ slashable_senior_headroom`, the `min` is a proven
/// belt-and-suspenders bound), and a zero `slashable_senior_headroom` — the bond
/// already at its floor — forfeits nothing (no division by zero).
///
/// Its signature admits **no price / mark argument**; the slash path can never
/// consult an oracle. That is not a comment — it is the type. The following must
/// not compile (a mark threaded into the forfeit):
/// ```compile_fail
/// # use dregg_node::relay_dispute::junior_forfeit;
/// // There is no price term in the slash path — a fourth mark argument is a
/// // type error, so a crashed-mark regression is type-visible, not silent.
/// let _ = junior_forfeit(2_000, 900, 9_000, /* price_mark = */ 3u64);
/// ```
pub fn junior_forfeit(
    junior_amount: u64,
    seized_senior: u64,
    slashable_senior_headroom: u64,
) -> u64 {
    if slashable_senior_headroom == 0 {
        // No slashable senior collateral (bond at its floor) ⇒ no junior forfeit.
        return 0;
    }
    let proportional =
        (junior_amount as u128 * seized_senior as u128) / slashable_senior_headroom as u128;
    // proportional ≤ junior_amount whenever seized_senior ≤ headroom (always true
    // here); the min is the enforced upper bound "seized_junior ≤ junior_amount".
    junior_amount.min(proportional as u64)
}

// =============================================================================
// The slash plan: the adjudicated seizure, floor-capped
// =============================================================================

/// The concrete consequence of a `slash` verdict: how much of the relay's bond
/// is seized, the resulting slot values, and how the seized bond is disposed
/// (restituted to the wronged party, remainder Transferred to the treasury —
/// conserving, nothing destroyed). Produced by [`plan_slash`] (senior-only) or
/// [`plan_two_tranche_slash`] (senior + a $DREGG junior) and realized as an
/// on-ledger [`Action`] by [`build_slash_turn`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SlashPlan {
    /// The bonded relay-operator cell being slashed (the `from` of both the
    /// restitution and remainder Transfers, and the target of the slash
    /// transition).
    pub relay_cell: CellId,
    /// The wronged inbox owner (`receipt.inbox_owner`) — the `to` of the
    /// conserving restitution Transfer.
    pub wronged_party: CellId,
    /// How the seizure is split between restitution and the remainder.
    /// `payout.restitution + payout.remainder == seized_amount`.
    pub payout: SlashPayout,
    /// Where the remainder (seizure minus restitution) is Transferred — a treasury /
    /// OSS-fund cell by default (a public fault-beacon + funding flywheel); a deployment
    /// may point it at a verifiable-random lottery among grain-owners, or a burn address.
    /// A CONSERVING Transfer, not destruction.
    pub remainder_dest: CellId,
    /// Computrons seized from the bond = `min(requested_penalty, bond - bond_min)`.
    /// May be `0` if the bond is already at its floor (the dispute is still
    /// recorded, but nothing is seizable).
    pub seized_amount: u64,
    /// The post-slash bond value (`bond - seized_amount`), never below `bond_min`.
    pub new_bond_amount: u64,
    /// The post-slash dispute counter (`dispute_count + 1`).
    pub new_dispute_count: u64,
    /// On-ledger slash provenance: the `content_hash` of the dropped box, so the
    /// slash names the exact fault that caused it.
    pub reason: [u8; 32],
    /// The $DREGG **junior** first-loss tranche, when this is a two-tranche plan
    /// ([`plan_two_tranche_slash`]). `None` for a senior-only plan ([`plan_slash`],
    /// the legacy intake path). The senior fields above are always the QUOTE
    /// (computron) tranche that bears the deterrence floor; the junior never
    /// counts toward it and is forfeited PRICE-FREE ([`junior_forfeit`]).
    pub junior: Option<JuniorTranche>,
}

/// Turn a referee verdict into a floor-capped, senior-only [`SlashPlan`] with a
/// split payout.
///
/// Returns `None` when the verdict is `acquit`. On `slash` it always returns a
/// plan (recording the dispute), with `seized_amount` capped by the bond floor:
/// the seizure can never push the bond below `bond_min`, mirroring the
/// relay-operator slash transition's floor. The seizure is then SPLIT: a bounded
/// restitution (`min(seized, proven_fee + restitution_bounty)`) to the wronged
/// party and the remainder Transferred to the remainder destination (a treasury
/// by default) — the operator loses the full seizure, `restitution` is credited
/// to the wronged party, and the rest is a CONSERVING Transfer, nothing destroyed.
/// The plan carries no junior tranche (`junior: None`); [`plan_two_tranche_slash`]
/// adds the $DREGG junior.
#[allow(clippy::too_many_arguments)]
pub fn plan_slash(
    slash: bool,
    bond_amount: u64,
    bond_min: u64,
    dispute_count: u64,
    requested_penalty: u64,
    proven_fee: u64,
    restitution_bounty: u64,
    relay_cell: CellId,
    wronged_party: CellId,
    reason: [u8; 32],
) -> Option<SlashPlan> {
    if !slash {
        return None;
    }
    // Seizable headroom above the floor; the seizure is capped so the bond never
    // drops below bond_min (the relay-operator slash floor).
    let headroom = bond_amount.saturating_sub(bond_min);
    let seized = requested_penalty.min(headroom);
    // Split the seizure: restitution makes the wronged party whole (their proven
    // loss + a small bounty, never more than was seized); the remainder is a
    // conserving Transfer to the remainder destination (the treasury by default)
    // rather than a windfall to the disputer — nothing is destroyed.
    let payout = SlashPayout::split(seized, proven_fee, restitution_bounty);
    Some(SlashPlan {
        relay_cell,
        wronged_party,
        payout,
        remainder_dest: default_slash_treasury(),
        seized_amount: seized,
        new_bond_amount: bond_amount - seized,
        new_dispute_count: dispute_count.saturating_add(1),
        reason,
        junior: None,
    })
}

/// Turn a referee verdict into a floor-capped **two-tranche** [`SlashPlan`]: the
/// QUOTE senior tranche (computrons) pays the penalty in full via the existing
/// split, and a $DREGG **junior** first-loss tranche forfeits PROPORTIONALLY.
///
/// The senior computation is exactly [`plan_slash`] (same floor cap, same split,
/// same quote-only restitution). The junior forfeit is [`junior_forfeit`] over
/// the senior's own seizure fraction — **no price argument appears anywhere in
/// this signature**, so the slash path stays oracle-free (obligation 4). The
/// junior never counts toward the deterrence floor: it is pure first-loss forfeit,
/// routed (in [`build_slash_turn`]) as a third conserving Transfer to the same
/// remainder cell — never to the wronged party (their make-whole is quote-only),
/// never burned.
///
/// Returns `None` on `acquit` (neither tranche is touched).
#[allow(clippy::too_many_arguments)]
pub fn plan_two_tranche_slash(
    slash: bool,
    // Senior (QUOTE / computron) tranche — the deterrence floor.
    bond_amount: u64,
    bond_min: u64,
    dispute_count: u64,
    requested_penalty: u64,
    proven_fee: u64,
    restitution_bounty: u64,
    relay_cell: CellId,
    wronged_party: CellId,
    reason: [u8; 32],
    // Junior ($DREGG) first-loss tranche — NO price/mark argument, by design.
    junior_cell: CellId,
    junior_asset: AssetId,
    junior_amount: u64,
) -> Option<SlashPlan> {
    let mut plan = plan_slash(
        slash,
        bond_amount,
        bond_min,
        dispute_count,
        requested_penalty,
        proven_fee,
        restitution_bounty,
        relay_cell,
        wronged_party,
        reason,
    )?;
    // The junior forfeits the SAME fraction of collateral the senior did, computed
    // with pure integers over the senior's slashable headroom — no price.
    let slashable_senior_headroom = bond_amount.saturating_sub(bond_min);
    let seized_junior =
        junior_forfeit(junior_amount, plan.seized_amount, slashable_senior_headroom);
    plan.junior = Some(JuniorTranche {
        junior_cell,
        junior_asset,
        junior_amount,
        seized_junior,
        new_junior_amount: junior_amount - seized_junior,
    });
    Some(plan)
}

/// Run the referee ([`adjudicate_from_inbox`]) against the inbox cell and, on a
/// slash, compute the floor-capped, split [`SlashPlan`]. Returns
/// `(slash_verdict, plan)`.
///
/// The wronged party is `receipt.inbox_owner` interpreted as a cell, and the
/// slash reason is the dropped box's `content_hash`. `proven_fee` is the wronged
/// party's proven loss (bounding restitution); the remainder of any seizure is
/// Transferred to the remainder destination (conserving).
#[allow(clippy::too_many_arguments)]
pub fn referee_then_plan(
    evidence: &EvidenceOfDrop,
    inbox: &InboxState,
    bond_amount: u64,
    bond_min: u64,
    dispute_count: u64,
    requested_penalty: u64,
    proven_fee: u64,
    restitution_bounty: u64,
    relay_cell: CellId,
) -> (bool, Option<SlashPlan>) {
    let slash = adjudicate_from_inbox(evidence, inbox);
    let wronged_party = CellId::from_bytes(evidence.receipt.inbox_owner.0);
    let reason = evidence.receipt.content_hash;
    let plan = plan_slash(
        slash,
        bond_amount,
        bond_min,
        dispute_count,
        requested_penalty,
        proven_fee,
        restitution_bounty,
        relay_cell,
        wronged_party,
        reason,
    );
    (slash, plan)
}

/// Drive the relay-operator slash transition for `plan` and append the payout
/// effects (restitution Transfer + remainder Transfer + — for a two-tranche plan
/// — the junior $DREGG forfeit Transfer).
///
/// [`build_slash_action`] emits the state-transition effects only (`SetField`
/// bond, `SetField` dispute_count, `EmitEvent`); this appends the effects that
/// dispose of the seized bond: the bounded senior RESTITUTION [`Effect::Transfer`]
/// to the wronged party and the senior REMAINDER as a conserving
/// [`Effect::Transfer`] to the remainder destination (both FROM the relay cell,
/// summing to the senior seizure — nothing destroyed), and, when
/// [`SlashPlan::junior`] is set, the junior $DREGG forfeit as a third conserving
/// Transfer FROM the junior bond cell to the SAME remainder destination. Every
/// leg is a conserving Transfer (no [`Effect::Burn`]): the senior seizure leaves
/// the relay cell in full, the junior forfeit leaves the junior cell in full. A
/// zero-amount leg is omitted (a zero seizure carries no senior legs; a zero or
/// absent junior forfeit carries no junior leg).
pub fn build_slash_turn(cclerk: &AppCipherclerk, plan: &SlashPlan) -> Action {
    let mut action = build_slash_action(
        cclerk,
        plan.relay_cell,
        u64_to_field(plan.new_bond_amount),
        u64_to_field(plan.new_dispute_count),
        plan.reason,
    );
    // Restitution leg: the wronged party's bounded make-whole (a conserving
    // Transfer out of the relay cell). QUOTE-only — the make-whole never arrives
    // in the correlated junior asset.
    if plan.payout.restitution > 0 {
        action.effects.push(Effect::Transfer {
            from: plan.relay_cell,
            to: plan.wronged_party,
            amount: plan.payout.restitution,
        });
    }
    // Senior remainder leg: the rest of the seizure is Transferred to the
    // remainder destination (the treasury by default) — a conserving Transfer,
    // debited from the relay cell and credited to the destination. Nothing is
    // destroyed; no global-owned entity receives it beyond the deployment-chosen
    // remainder cell.
    if plan.payout.remainder > 0 {
        action.effects.push(Effect::Transfer {
            from: plan.relay_cell,
            to: plan.remainder_dest,
            amount: plan.payout.remainder,
        });
    }
    // Junior forfeit leg ($DREGG): the proportional first-loss forfeit, a single
    // conserving Transfer FROM the junior bond cell TO the same remainder
    // destination. Never to the wronged party (restitution is quote-only), never
    // burned. Omitted when there is no junior tranche or the forfeit is zero.
    if let Some(junior) = &plan.junior {
        if junior.seized_junior > 0 {
            action.effects.push(Effect::Transfer {
                from: junior.junior_cell,
                to: plan.remainder_dest,
                amount: junior.seized_junior,
            });
        }
    }
    action
}

// =============================================================================
// POST /relay/dispute — the intake route
// =============================================================================

/// `POST /relay/dispute` request: the owner-anchored fraud proof.
///
/// The body is the referee's own [`EvidenceOfDrop`] (the relay's signed receipt
/// + the dispute height), which deserializes directly from JSON. `requested_penalty`
/// is the TOTAL seizure the disputant asks for (capped by the bond floor); the
/// seizure is then split into restitution + a remainder Transferred to the
/// remainder destination, so a large request is not a windfall to the disputer.
#[derive(Debug, Deserialize)]
pub struct DisputeRequest {
    /// The relay's own signed receipt + claimed outcome + dispute height.
    pub evidence: EvidenceOfDrop,
    /// Requested TOTAL seizure in computrons; defaults to [`DEFAULT_SLASH_PENALTY`].
    /// The wronged party's restitution is bounded by their proven loss regardless
    /// of this; the remainder is Transferred to the remainder destination.
    #[serde(default)]
    pub requested_penalty: Option<u64>,
}

/// `POST /relay/dispute` response: the verdict and (on a slash) the realized
/// seizure applied to the in-process template mirror.
#[derive(Debug, Serialize)]
pub struct DisputeResponse {
    /// `"slash"` or `"acquit"`.
    pub verdict: &'static str,
    /// True iff the relay was slashed.
    pub slashed: bool,
    /// Bond seized (computrons); `0` on acquit or when the bond is at its floor.
    pub seized_amount: u64,
    /// Of the seizure, computrons restituted to the wronged party (their bounded
    /// proven loss). `0` on acquit.
    pub restitution_amount: u64,
    /// Of the seizure, the remainder Transferred to the remainder destination
    /// (the treasury by default) — conserving, NOT destroyed. `0` on acquit. (The
    /// field name is retained for wire compatibility; the value is the remainder
    /// leg, not a burn — see [`SlashPayout`].)
    pub burned_amount: u64,
    /// The bond before this dispute.
    pub prior_bond_amount: u64,
    /// The bond after this dispute (== prior on acquit).
    pub new_bond_amount: u64,
    /// The dispute counter after this dispute (advanced by one on a slash).
    pub dispute_count: u64,
    /// The wronged inbox owner (hex) — the restitution recipient.
    pub wronged_party: String,
    /// The bonded relay-operator cell (hex).
    pub relay_cell: String,
    /// The dropped box's `content_hash` (hex) — the slash provenance.
    pub reason: String,
    /// Number of payout effects the paired ledger turn would carry: one per
    /// non-zero leg (the restitution Transfer and/or the remainder Transfer), so
    /// `0`, `1`, or `2`.
    pub payout_effects: usize,
}

/// `POST /relay/dispute` error body.
#[derive(Debug, Serialize)]
pub struct DisputeError {
    pub error: String,
}

/// The dispute intake handler: run the referee, then the slash.
///
/// Gates on the referee's own `well_formed` (a forged receipt or a dispute
/// raised before `accept_by` is a 400 — no cell read, no slash), reads the inbox
/// cell's authenticated state from the running service, runs
/// [`referee_then_plan`], and on a slash applies the transition to the template
/// mirror. See the module docs for the ledger-turn emission gap.
pub async fn handle_dispute(
    State(state): State<SharedRelayState>,
    Json(req): Json<DisputeRequest>,
) -> Result<Json<DisputeResponse>, (StatusCode, Json<DisputeError>)> {
    let evidence = req.evidence;

    // Admissibility (the referee's own gate): a forged receipt (signature does
    // not verify against `receipt.relay`) or a premature dispute (`at_height <
    // accept_by`) convicts nobody. Reject before any cell read.
    if !evidence.well_formed() {
        return Err((
            StatusCode::BAD_REQUEST,
            Json(DisputeError {
                error: "evidence not well-formed: bad receipt signature or dispute raised before accept_by".into(),
            }),
        ));
    }

    let mut s = state.write().await;

    // Node-authoritative dispute window (audit #10 — the upper deadline that makes
    // bounded eviction of `delivery_proofs` slash-safe). `well_formed` above already
    // checked the disputer's OWN `at_height >= accept_by` — a crypto lower bound the
    // disputer asserts and can craft. Here the NODE re-decides admissibility against
    // its own finalized `current_height`, which a disputer cannot forge, so neither
    // bound is bypassable by a chosen `at_height`:
    //
    //   * current_height < accept_by            → the custody deadline has NOT passed
    //     at the node's real height; the relay may still deliver or refund. Reject —
    //     no PREMATURE slash of a relay that has not defaulted.
    //   * current_height > accept_by + window   → the dispute (challenge) window has
    //     CLOSED; the delivery is FINAL. Reject. Past this point every dispute over
    //     the box is inadmissible, which is EXACTLY what lets the relay service evict
    //     that box's cached delivery proof (`evict_expired_delivery_proofs`) without
    //     ever flipping an acquit into a slash: no admissible dispute can read the
    //     evicted (now content-hash-absent) delivered set. The eviction threshold and
    //     this gate coincide by construction (see `DeliveryProofRecord`).
    let current_height = s.current_height;
    let accept_by = evidence.receipt.accept_by;
    let dispute_deadline = accept_by.saturating_add(s.config.dispute_window_blocks);
    if current_height < accept_by {
        return Err((
            StatusCode::BAD_REQUEST,
            Json(DisputeError {
                error: format!(
                    "dispute premature: finalized height {current_height} < accept_by {accept_by} (the relay has not defaulted)"
                ),
            }),
        ));
    }
    if current_height > dispute_deadline {
        return Err((
            StatusCode::BAD_REQUEST,
            Json(DisputeError {
                error: format!(
                    "dispute window closed: finalized height {current_height} > accept_by {accept_by} + window {} (delivery is final)",
                    s.config.dispute_window_blocks
                ),
            }),
        ));
    }

    let owner = evidence.receipt.inbox_owner.0;
    // The inbox's authenticated head root at the dispute height (0 if the inbox
    // has been unsubscribed / never existed). The verdict reads the delivery
    // witness, not this root; it is carried for diagnostics.
    let root = s
        .template
        .hosted_inboxes
        .get(&owner)
        .map(|inbox| inbox.queue_root)
        .unwrap_or([0u8; 32]);
    // The content-address-honest DELIVERED set: every box this relay dequeued
    // toward a recipient is cached in `delivery_proofs`, keyed by content_hash.
    // Membership of `receipt.content_hash` is the sticky delivery witness.
    let delivered: Vec<[u8; 32]> = s.delivery_proofs.keys().copied().collect();
    // refund_recorded = false: the legacy in-process service keeps no per-message
    // refund witness (see module docs — promotion gap). A slash verdict is sound
    // only for boxes that were genuinely neither delivered nor refunded.
    let inbox = InboxState::from_dequeue(&evidence.receipt, &delivered, root, false);

    let prior_bond = u64_from_field(s.template.slots[BOND_AMOUNT_SLOT as usize]);
    let bond_min = u64_from_field(s.template.slots[BOND_MIN_SLOT as usize]);
    let dispute_count = u64_from_field(s.template.slots[DISPUTE_COUNT_SLOT as usize]);
    let penalty = req.requested_penalty.unwrap_or(DEFAULT_SLASH_PENALTY);
    // The wronged party's PROVEN per-message loss: the fee-policy floor a sender
    // must post per message (the minimum they paid for the box the relay
    // dropped). Restitution is bounded by this + a small bounty; the remainder of
    // any seizure is Transferred to the remainder destination (conserving).
    // Promotion sources the exact paid fee from the dropped box's queue-entry
    // `deposit` (see module docs).
    let proven_fee = s.config.fee_policy.min_deposit_computrons;
    // The relay-operator cell identity. The legacy service does not track the
    // minted relay CellId; the operator identity is its closest in-process
    // proxy (promotion binds the real minted cell — see module docs).
    let relay_cell = CellId::from_bytes(s.config.operator_key);

    // `plan.is_some()` IS the adjudication verdict: `plan_slash` returns `None`
    // whenever the referee declined, and `Some` in every case where it did not.
    // So the `if let Some(plan)` below IS the adjudication gate, and the separate
    // bool would be a second copy of the same decision — dropped deliberately.
    let (_slash, plan) = referee_then_plan(
        &evidence,
        &inbox,
        prior_bond,
        bond_min,
        dispute_count,
        penalty,
        proven_fee,
        DEFAULT_RESTITUTION_BOUNTY,
        relay_cell,
    );

    if let Some(plan) = plan {
        // Apply the slash transition to the in-process template mirror: bond
        // down by the seized amount, dispute_count +1 — the same slot moves the
        // ledger `build_slash_action` encodes. The paired restitution Transfer
        // and remainder Transfer ride the on-ledger turn (see `build_slash_turn`);
        // the mirror carries no per-cell balance ledger.
        s.template.slots[BOND_AMOUNT_SLOT as usize] = u64_to_field(plan.new_bond_amount);
        s.template.slots[DISPUTE_COUNT_SLOT as usize] = u64_to_field(plan.new_dispute_count);
        // One payout effect per non-zero leg of the split (restitution Transfer,
        // remainder Transfer).
        let payout_effects =
            usize::from(plan.payout.restitution > 0) + usize::from(plan.payout.remainder > 0);
        return Ok(Json(DisputeResponse {
            verdict: "slash",
            slashed: true,
            seized_amount: plan.seized_amount,
            restitution_amount: plan.payout.restitution,
            burned_amount: plan.payout.remainder,
            prior_bond_amount: prior_bond,
            new_bond_amount: plan.new_bond_amount,
            dispute_count: plan.new_dispute_count,
            wronged_party: hex32(&plan.wronged_party.0),
            relay_cell: hex32(&plan.relay_cell.0),
            reason: hex32(&plan.reason),
            payout_effects,
        }));
    }

    // Acquit: the cell witnesses delivery (or a refund) — no slash, no mutation.
    Ok(Json(DisputeResponse {
        verdict: "acquit",
        slashed: false,
        seized_amount: 0,
        restitution_amount: 0,
        burned_amount: 0,
        prior_bond_amount: prior_bond,
        new_bond_amount: prior_bond,
        dispute_count,
        wronged_party: hex32(&owner),
        relay_cell: hex32(&relay_cell.0),
        reason: hex32(&evidence.receipt.content_hash),
        payout_effects: 0,
    }))
}

// =============================================================================
// Field codec (big-endian trailing-8, matching relay_service + the templates)
// =============================================================================

pub(crate) fn u64_to_field(value: u64) -> [u8; 32] {
    let mut f = [0u8; 32];
    f[24..32].copy_from_slice(&value.to_be_bytes());
    f
}

pub(crate) fn u64_from_field(field: [u8; 32]) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&field[24..32]);
    u64::from_be_bytes(b)
}

fn hex32(bytes: &[u8; 32]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

// =============================================================================
// Tests — the WELD, both polarities
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;
    use dregg_captp::FederationId;
    use dregg_captp::custody::CustodyReceipt;
    use dregg_types::{SigningKey, generate_keypair};

    fn test_cclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32])
    }

    fn relay_identity() -> (FederationId, SigningKey) {
        let (sk, pk) = generate_keypair();
        (FederationId(pk.0), sk)
    }

    fn demo_receipt() -> CustodyReceipt {
        let (relay, sk) = relay_identity();
        CustodyReceipt::sign(
            relay,
            &sk,
            [0xAB; 32],               // content_hash
            FederationId([0x03; 32]), // inbox_owner (the wronged party)
            [0x64; 32],               // old_root
            [0x8E; 32],               // new_root (promised)
            500,                      // accept_by
        )
    }

    #[test]
    fn proven_drop_restitutes_wronged_and_routes_remainder_to_treasury() {
        // A well-formed receipt + a dropped inbox (no delivered hash, no refund)
        // convicts. The seizure SPLITS: a bounded restitution to the wronged
        // owner + the remainder Transferred to the treasury. The bond leaves the
        // operator in full; both legs are conserving, nothing destroyed.
        let evidence = EvidenceOfDrop::from_receipt(demo_receipt());
        let inbox = InboxState::from_dequeue(&evidence.receipt, &[], [0x64; 32], false);
        let relay_cell = CellId::from_bytes([0x11; 32]);

        // Seize 500; proven loss 120 + bounty 30 => restitution 150, remainder 350.
        let (slash, plan) = referee_then_plan(
            &evidence, &inbox, 10_000, 1_000, 0, 500, 120, 30, relay_cell,
        );
        assert!(slash, "a genuine drop must slash");
        let plan = plan.expect("a slash verdict must yield a plan");
        assert_eq!(plan.seized_amount, 500);
        assert_eq!(plan.payout.restitution, 150, "proven loss + bounty");
        assert_eq!(
            plan.payout.remainder, 350,
            "the remainder is Transferred to the treasury (conserving)"
        );
        assert_eq!(
            plan.payout.total(),
            plan.seized_amount,
            "the split accounts for the whole seizure"
        );
        assert_eq!(plan.new_bond_amount, 9_500);
        assert_eq!(plan.new_dispute_count, 1);
        assert_eq!(plan.wronged_party.0, [0x03; 32]);
        assert_eq!(plan.reason, [0xAB; 32], "slash names the dropped box");

        let action = build_slash_turn(&test_cclerk(), &plan);
        // build_slash_action = SetField(bond) + SetField(dispute) + EmitEvent (3);
        // the weld appends the restitution Transfer + the remainder Transfer.
        assert_eq!(action.effects.len(), 5);

        // Exactly one restitution Transfer, seized FROM the relay cell TO the
        // wronged owner.
        let transfers: Vec<(CellId, CellId, u64)> = action
            .effects
            .iter()
            .filter_map(|e| match e {
                Effect::Transfer { from, to, amount } => Some((*from, *to, *amount)),
                _ => None,
            })
            .collect();
        // Two conserving Transfers: restitution to the wronged owner + the remainder
        // to the treasury (default_slash_treasury). No burn — nothing destroyed.
        assert_eq!(transfers.len(), 2, "restitution + remainder legs");
        assert_eq!(
            transfers[0].0, relay_cell,
            "restitution seized FROM the relay"
        );
        assert_eq!(
            transfers[0].1, plan.wronged_party,
            "restitution TO the wronged owner"
        );
        assert_eq!(transfers[0].2, 150);
        assert_eq!(
            transfers[1].0, relay_cell,
            "remainder seized FROM the relay"
        );
        assert_eq!(
            transfers[1].1,
            default_slash_treasury(),
            "remainder TO the treasury"
        );
        assert_eq!(transfers[1].2, 350, "remainder = seized - restitution");
        assert!(
            !action
                .effects
                .iter()
                .any(|e| matches!(e, Effect::Burn { .. })),
            "no burn — the remainder is Transferred, conserving"
        );
        assert_eq!(
            transfers[0].2 + transfers[1].2,
            plan.seized_amount,
            "the whole seizure leaves the operator (restitution + remainder), conserving"
        );
    }

    #[test]
    fn whole_seizure_to_treasury_when_no_proven_loss() {
        // No proven fee and no bounty => the wronged party is owed nothing extra,
        // so the ENTIRE seizure is Transferred to the treasury (a single conserving
        // Transfer). Nothing is destroyed.
        let evidence = EvidenceOfDrop::from_receipt(demo_receipt());
        let inbox = InboxState::from_dequeue(&evidence.receipt, &[], [0x64; 32], false);
        let relay_cell = CellId::from_bytes([0x11; 32]);

        let (slash, plan) =
            referee_then_plan(&evidence, &inbox, 10_000, 1_000, 0, 500, 0, 0, relay_cell);
        assert!(slash);
        let plan = plan.unwrap();
        assert_eq!(plan.payout.restitution, 0, "nothing proven to restitute");
        assert_eq!(
            plan.payout.remainder, 500,
            "the whole seizure goes to the treasury"
        );
        assert_eq!(plan.payout.total(), plan.seized_amount);

        let action = build_slash_turn(&test_cclerk(), &plan);
        // Restitution 0 (omitted); the whole seizure is a single conserving Transfer of
        // the remainder to the treasury — no burn.
        let transfers: Vec<(CellId, CellId, u64)> = action
            .effects
            .iter()
            .filter_map(|e| match e {
                Effect::Transfer { from, to, amount } => Some((*from, *to, *amount)),
                _ => None,
            })
            .collect();
        assert_eq!(
            transfers.len(),
            1,
            "one Transfer: the remainder to the treasury"
        );
        assert_eq!(transfers[0].0, relay_cell, "seized FROM the relay");
        assert_eq!(transfers[0].1, default_slash_treasury(), "TO the treasury");
        assert_eq!(transfers[0].2, 500, "the whole seizure");
        assert!(
            !action
                .effects
                .iter()
                .any(|e| matches!(e, Effect::Burn { .. })),
            "no burn"
        );
    }

    #[test]
    fn restitution_capped_at_seized_no_remainder() {
        // The proven loss dwarfs the seizure (bond at its floor): restitution is
        // capped at the whole seizure and there is no remainder.
        let evidence = EvidenceOfDrop::from_receipt(demo_receipt());
        let inbox = InboxState::from_dequeue(&evidence.receipt, &[], [0x64; 32], false);
        let relay_cell = CellId::from_bytes([0x11; 32]);

        // Headroom only 200; proven loss 10_000 + bounty 100 dwarfs it.
        let (slash, plan) = referee_then_plan(
            &evidence, &inbox, 1_200, 1_000, 3, 5_000, 10_000, 100, relay_cell,
        );
        assert!(slash);
        let plan = plan.unwrap();
        assert_eq!(plan.seized_amount, 200, "capped at the bond floor");
        assert_eq!(
            plan.payout.restitution, 200,
            "restitution never exceeds the seizure"
        );
        assert_eq!(plan.payout.remainder, 0, "no remainder left");
        assert_eq!(plan.payout.total(), plan.seized_amount);

        let action = build_slash_turn(&test_cclerk(), &plan);
        let transfers = action
            .effects
            .iter()
            .filter(|e| matches!(e, Effect::Transfer { .. }))
            .count();
        assert_eq!(transfers, 1, "the restitution leg");
        let burns = action
            .effects
            .iter()
            .filter(|e| matches!(e, Effect::Burn { .. }))
            .count();
        assert_eq!(
            burns, 0,
            "never a burn — every leg is a conserving Transfer"
        );
    }

    #[test]
    fn payout_split_conserves() {
        // The pure split accounts for the whole seizure for every
        // proven_fee/bounty: restitution + remainder == seized.
        for (seized, fee, bounty) in [
            (0u64, 0u64, 0u64),
            (500, 0, 0),
            (500, 120, 30),
            (500, 500, 500),
            (500, 1_000, 1_000),
            (1, u64::MAX, u64::MAX),
        ] {
            let p = SlashPayout::split(seized, fee, bounty);
            assert_eq!(
                p.restitution + p.remainder,
                seized,
                "restitution + remainder == seized"
            );
            assert_eq!(p.total(), seized);
            assert!(
                p.restitution <= seized,
                "restitution never exceeds the seizure"
            );
            assert!(
                p.restitution <= fee.saturating_add(bounty),
                "restitution bounded by proven loss + bounty"
            );
        }
    }

    #[test]
    fn honest_delivery_yields_no_slash() {
        // The box's content_hash is among the delivered set (witness set) ⇒ the
        // referee acquits ⇒ no plan, no payout, regardless of the drop-claim.
        let evidence = EvidenceOfDrop::from_receipt(demo_receipt());
        let inbox = InboxState::from_dequeue(&evidence.receipt, &[[0xAB; 32]], [0x8E; 32], false);
        let relay_cell = CellId::from_bytes([0x11; 32]);

        let (slash, plan) = referee_then_plan(
            &evidence, &inbox, 10_000, 1_000, 0, 500, 120, 30, relay_cell,
        );
        assert!(!slash, "a delivered box must acquit");
        assert!(plan.is_none(), "acquit ⇒ no slash plan");
    }

    #[test]
    fn bond_floor_caps_the_seizure() {
        // penalty 5_000 but only 200 above the floor ⇒ seize 200, land exactly on
        // bond_min. The dispute is still recorded, and the 200 splits per the
        // payout model (here proven loss 500 => all 200 restituted, no remainder).
        let evidence = EvidenceOfDrop::from_receipt(demo_receipt());
        let inbox = InboxState::from_dequeue(&evidence.receipt, &[], [0x64; 32], false);
        let relay_cell = CellId::from_bytes([0x11; 32]);

        let (slash, plan) = referee_then_plan(
            &evidence, &inbox, 1_200, 1_000, 3, 5_000, 500, 0, relay_cell,
        );
        assert!(slash);
        let plan = plan.unwrap();
        assert_eq!(plan.seized_amount, 200, "capped at the bond floor");
        assert_eq!(plan.new_bond_amount, 1_000, "never below bond_min");
        assert_eq!(plan.new_dispute_count, 4);
        assert_eq!(plan.payout.restitution, 200);
        assert_eq!(plan.payout.remainder, 0);
        assert_eq!(plan.payout.total(), plan.seized_amount);
    }

    #[test]
    fn overshoot_delivery_still_acquits_through_the_weld() {
        // The overshoot/reorg tooth composes through the weld: a delivered box
        // whose live root grew PAST the promise still acquits (the witness bit is
        // sticky), so no bond is seized.
        let evidence = EvidenceOfDrop::from_receipt(demo_receipt());
        // Delivered (content_hash in the set) but root overshot the promise.
        let inbox = InboxState::from_dequeue(&evidence.receipt, &[[0xAB; 32]], [0x99; 32], false);
        let relay_cell = CellId::from_bytes([0x11; 32]);

        let (slash, plan) = referee_then_plan(
            &evidence, &inbox, 10_000, 1_000, 0, 500, 120, 30, relay_cell,
        );
        assert!(!slash, "overshoot must not convict a delivered relay");
        assert!(plan.is_none());
    }

    #[test]
    fn field_codec_roundtrips() {
        for v in [0u64, 1, 500, 10_000, u64::MAX] {
            assert_eq!(u64_from_field(u64_to_field(v)), v);
        }
    }

    // ── Two-tranche bond (Track C rung 1): a QUOTE senior + a $DREGG junior ──────
    //
    // The senior tranche (computrons) is the deterrence floor and pays the penalty
    // IN FULL through the existing split. The $DREGG junior is a first-loss tranche
    // that forfeits PROPORTIONALLY with integer arithmetic and NO price input, and
    // NEVER counts toward the floor. The whole path stays oracle-free and conserving
    // (no burn; the junior forfeit is a Transfer to the remainder cell, restitution
    // stays quote-only).

    #[test]
    fn two_tranche_junior_forfeits_proportionally_senior_pays_in_full_conserving() {
        // seized_senior / slashable_headroom = 900 / 9_000 = 1/10, so the $DREGG
        // junior (2_000) forfeits the SAME fraction: 200 — computed with no price.
        let relay_cell = CellId::from_bytes([0x11; 32]);
        let junior_cell = CellId::from_bytes([0x22; 32]);
        let dregg_asset: AssetId = *blake3::hash(b"dregg").as_bytes();
        let wronged = CellId::from_bytes([0x03; 32]);

        let plan = plan_two_tranche_slash(
            true,
            10_000,
            1_000,
            0,
            900,
            120,
            30,
            relay_cell,
            wronged,
            [0xAB; 32],
            junior_cell,
            dregg_asset,
            2_000,
        )
        .expect("a slash verdict yields a two-tranche plan");

        // Senior pays the QUOTE penalty in full: 900 seized, split 150 / 750.
        assert_eq!(
            plan.seized_amount, 900,
            "senior pays the quote penalty in full"
        );
        assert_eq!(plan.payout.restitution, 150);
        assert_eq!(plan.payout.remainder, 750);
        assert_eq!(
            plan.payout.total(),
            plan.seized_amount,
            "senior (quote) split conserves"
        );

        let junior = plan
            .junior
            .expect("two-tranche plan carries a junior tranche");
        assert_eq!(
            junior.seized_junior, 200,
            "junior forfeits the same 1/10 fraction (price-free)"
        );
        assert_eq!(junior.new_junior_amount, 1_800);
        assert_eq!(junior.junior_amount, 2_000);
        assert_eq!(
            junior.junior_asset, dregg_asset,
            "the junior tranche is $DREGG, not computrons"
        );

        // Emit: senior restitution + senior remainder + junior forfeit = 3
        // conserving Transfers atop build_slash_action's state effects. No burn.
        let action = build_slash_turn(&test_cclerk(), &plan);
        assert!(
            !action
                .effects
                .iter()
                .any(|e| matches!(e, Effect::Burn { .. })),
            "no burn — every leg is a conserving Transfer"
        );
        let transfers: Vec<(CellId, CellId, u64)> = action
            .effects
            .iter()
            .filter_map(|e| match e {
                Effect::Transfer { from, to, amount } => Some((*from, *to, *amount)),
                _ => None,
            })
            .collect();
        assert_eq!(
            transfers.len(),
            3,
            "senior restitution + senior remainder + junior forfeit"
        );
        // Senior legs come FROM the relay cell (computrons).
        assert_eq!(
            transfers[0],
            (relay_cell, wronged, 150),
            "senior restitution"
        );
        assert_eq!(
            transfers[1],
            (relay_cell, default_slash_treasury(), 750),
            "senior remainder to the treasury"
        );
        // Junior leg comes FROM the $DREGG bond cell to the SAME remainder cell —
        // never to the wronged party (their make-whole is quote-only), never burned.
        assert_eq!(
            transfers[2],
            (junior_cell, default_slash_treasury(), 200),
            "junior $DREGG forfeit to the treasury"
        );

        // Per-asset conservation of the split (obligation 1):
        //   quote: restitution + remainder == seized_senior
        assert_eq!(
            plan.payout.restitution + plan.payout.remainder,
            plan.seized_amount
        );
        //   dregg: the whole junior seizure leaves the junior cell (restitution_dregg = 0)
        assert_eq!(junior.seized_junior, transfers[2].2);
    }

    #[test]
    fn two_tranche_no_seizure_beyond_each_tranches_bond() {
        let relay_cell = CellId::from_bytes([0x11; 32]);
        let junior_cell = CellId::from_bytes([0x22; 32]);
        let dregg: AssetId = [0x07; 32];
        let wronged = CellId::from_bytes([0x03; 32]);

        // (a) The WHOLE slashable senior is taken (penalty ≫ headroom): senior
        // lands EXACTLY on bond_min; junior forfeits its WHOLE bond (fraction 1),
        // never a token more, landing on zero.
        let plan = plan_two_tranche_slash(
            true,
            5_000,
            1_000,
            0,
            999_999,
            0,
            0,
            relay_cell,
            wronged,
            [1u8; 32],
            junior_cell,
            dregg,
            3_000,
        )
        .unwrap();
        assert_eq!(
            plan.seized_amount, 4_000,
            "senior capped at headroom (5000-1000)"
        );
        assert_eq!(plan.new_bond_amount, 1_000, "senior never below bond_min");
        let j = plan.junior.unwrap();
        assert_eq!(
            j.seized_junior, 3_000,
            "junior forfeits its whole bond at fraction 1"
        );
        assert_eq!(j.new_junior_amount, 0, "junior never below zero");
        assert!(
            j.seized_junior <= j.junior_amount,
            "seized_junior never exceeds the junior bond"
        );

        // (b) Bond already at its floor (headroom 0): senior seizes nothing and
        // the junior forfeits NOTHING — no division by zero, no seizure at all.
        let plan0 = plan_two_tranche_slash(
            true,
            1_000,
            1_000,
            2,
            5_000,
            0,
            0,
            relay_cell,
            wronged,
            [2u8; 32],
            junior_cell,
            dregg,
            3_000,
        )
        .unwrap();
        assert_eq!(plan0.seized_amount, 0, "no slashable senior headroom");
        let j0 = plan0.junior.unwrap();
        assert_eq!(
            j0.seized_junior, 0,
            "no senior seizure => no junior forfeit (no div-by-zero)"
        );
        assert_eq!(j0.new_junior_amount, 3_000, "junior untouched");

        // The price-free kernel of the rule, asserted directly at its bounds.
        assert_eq!(
            junior_forfeit(3_000, 4_000, 4_000),
            3_000,
            "fraction 1 => whole junior, capped at the bond"
        );
        assert_eq!(
            junior_forfeit(3_000, 0, 4_000),
            0,
            "no senior seizure => zero"
        );
        assert_eq!(
            junior_forfeit(3_000, 5, 0),
            0,
            "zero headroom => zero (no div-by-zero)"
        );
        // No overflow: the intermediate product is computed in u128.
        assert_eq!(junior_forfeit(u64::MAX, u64::MAX, u64::MAX), u64::MAX);
    }

    #[test]
    fn two_tranche_acquit_seizes_neither_tranche() {
        // Acquit ⇒ no plan at all — neither the senior nor the junior is touched.
        let plan = plan_two_tranche_slash(
            false,
            10_000,
            1_000,
            0,
            900,
            120,
            30,
            CellId::from_bytes([0x11; 32]),
            CellId::from_bytes([0x03; 32]),
            [0u8; 32],
            CellId::from_bytes([0x22; 32]),
            [0x07; 32],
            2_000,
        );
        assert!(plan.is_none(), "acquit => no plan, neither tranche seized");
    }

    #[test]
    fn plan_slash_carries_no_junior_tranche() {
        // The legacy senior-only planner produces a plan with no junior tranche,
        // so the existing intake path and its emitted turn are unchanged.
        let plan = plan_slash(
            true,
            10_000,
            1_000,
            0,
            500,
            120,
            30,
            CellId::from_bytes([0x11; 32]),
            CellId::from_bytes([0x03; 32]),
            [0xAB; 32],
        )
        .unwrap();
        assert!(
            plan.junior.is_none(),
            "senior-only plan has no junior tranche"
        );
        let action = build_slash_turn(&test_cclerk(), &plan);
        let transfers = action
            .effects
            .iter()
            .filter(|e| matches!(e, Effect::Transfer { .. }))
            .count();
        assert_eq!(
            transfers, 2,
            "senior-only: restitution + remainder, no junior leg"
        );
    }

    // ── audit #10: the dispute window makes bounded delivery_proofs slash-safe ──────
    //
    // `handle_dispute` reads `delivery_proofs`' KEYS as the delivery witness. Left
    // unbounded the map leaks; but blind eviction could drop a still-disputable
    // delivered box and WRONGLY SLASH an honest relay (or, past the deadline, wrongly
    // fail to slash). The node-authoritative dispute window
    // (`accept_by ..= accept_by + dispute_window_blocks`, decided against the
    // finalized `current_height`, which a disputer cannot forge) makes a delivery
    // FINAL past the window, and the height-keyed eviction's deadline coincides with
    // it. These are the both-directions falsifiers over the REAL handler + eviction:
    //   (a) within the window a dropped box still slashes and a delivered box acquits;
    //   (c) past the deadline the proof IS evicted AND the late dispute is rejected,
    //       so the honest relay is never wrongly slashed by the eviction;
    //       the two thresholds coincide exactly (no gap where the proof is gone but a
    //       dispute would still slash); a premature dispute is rejected too.

    use crate::relay_service::{DeliveryProofRecord, RelayConfig, RelayState, RelayTemplateState};
    use dregg_storage::queue::{DequeueProof, QueueEntry};
    use std::sync::Arc;
    use tokio::sync::RwLock;

    #[allow(deprecated)]
    fn dispute_state(current_height: u64, dispute_window_blocks: u64) -> SharedRelayState {
        use dregg_storage::operator::RelayOperator;
        let config = RelayConfig {
            operator_key: [0xAA; 32],
            bond_amount: 10_000,
            dispute_window_blocks,
            ..RelayConfig::default()
        };
        let mut template = RelayTemplateState::new(&config);
        // Genesis sets bond_min == bond_amount (zero headroom); lower it so a slash
        // actually seizes, exercising the real seizure path within the headroom.
        template.slots[BOND_MIN_SLOT as usize] = u64_to_field(1_000);
        let operator = RelayOperator::new(
            config.operator_key,
            config.bond_amount,
            config.max_delivery_latency_blocks,
        );
        Arc::new(RwLock::new(RelayState {
            operator,
            template,
            config,
            current_height,
            delivery_proofs: std::collections::HashMap::new(),
            messages_delivered: 0,
            messages_received: 0,
        }))
    }

    fn dummy_proof() -> DequeueProof {
        DequeueProof {
            entry: QueueEntry {
                content_hash: [0xAB; 32],
                sender: [0u8; 32],
                deposit: 0,
                enqueued_at: 0,
                size: 0,
            },
            old_root: [0u8; 32],
            new_root: [0u8; 32],
            position: 0,
            remaining_leaves: Vec::new(),
        }
    }

    fn dispute_req() -> DisputeRequest {
        DisputeRequest {
            evidence: EvidenceOfDrop::from_receipt(demo_receipt()), // content_hash 0xAB, accept_by 500
            requested_penalty: Some(500),
        }
    }

    /// (a) A dropped box (never delivered) disputed WITHIN its window slashes: the
    /// window gate admits it, the empty witness set reads Dropped.
    #[tokio::test]
    async fn audit10_within_window_dropped_box_still_slashes() {
        let state = dispute_state(500, 1_000); // accept_by 500; window [500, 1500]
        let resp = handle_dispute(State(state.clone()), Json(dispute_req()))
            .await
            .expect("within-window dispute is admissible")
            .0;
        assert_eq!(resp.verdict, "slash");
        assert!(resp.slashed);
        assert_eq!(resp.dispute_count, 1, "the dispute is recorded");
        assert_eq!(
            resp.seized_amount, 500,
            "a real seizure within the bond headroom"
        );
        assert_eq!(
            u64_from_field(state.read().await.template.slots[BOND_AMOUNT_SLOT as usize]),
            9_500
        );
    }

    /// (a) A delivered box (its content_hash in the witness set) disputed within the
    /// window ACQUITS — the proof is present, not evicted.
    #[tokio::test]
    async fn audit10_within_window_delivered_box_acquits() {
        let state = dispute_state(500, 1_000);
        state.write().await.delivery_proofs.insert(
            [0xAB; 32],
            DeliveryProofRecord {
                proof: dummy_proof(),
                dispute_deadline: 1_500,
            },
        );
        let resp = handle_dispute(State(state.clone()), Json(dispute_req()))
            .await
            .expect("admissible")
            .0;
        assert_eq!(resp.verdict, "acquit");
        assert!(!resp.slashed);
        assert_eq!(resp.dispute_count, 0);
        assert_eq!(
            u64_from_field(state.read().await.template.slots[BOND_AMOUNT_SLOT as usize]),
            10_000,
            "an acquit seizes nothing"
        );
    }

    /// (c) THE CRUX. A delivered box PAST its dispute deadline: the proof IS evicted
    /// (map bounded) AND a late dispute over it is REJECTED by the window gate, so the
    /// honest relay is NEVER wrongly slashed by the eviction.
    #[tokio::test]
    async fn audit10_evicted_delivered_proof_never_wrongly_slashes() {
        let state = dispute_state(0, 1_000);
        {
            let mut s = state.write().await;
            s.delivery_proofs.insert(
                [0xAB; 32],
                DeliveryProofRecord {
                    proof: dummy_proof(),
                    dispute_deadline: 1_500, // accept_by 500 + window 1000
                },
            );
            s.current_height = 1_501; // finalized frontier one past the deadline
            assert_eq!(
                s.evict_expired_delivery_proofs(1_501),
                1,
                "proof past deadline evicted"
            );
            assert!(
                s.delivery_proofs.is_empty(),
                "map bounded — the leak is closed"
            );
        }
        // The witness is gone, but the honest relay is safe: the late dispute is
        // inadmissible (window closed), so it can never flip into a slash.
        let err = handle_dispute(State(state.clone()), Json(dispute_req()))
            .await
            .expect_err("a dispute past the window is rejected");
        assert_eq!(err.0, StatusCode::BAD_REQUEST);
        assert!(
            err.1.0.error.contains("window closed"),
            "rejected as final: {}",
            err.1.0.error
        );
        let s = state.read().await;
        assert_eq!(
            u64_from_field(s.template.slots[DISPUTE_COUNT_SLOT as usize]),
            0,
            "no mutation on a rejected dispute"
        );
        assert_eq!(
            u64_from_field(s.template.slots[BOND_AMOUNT_SLOT as usize]),
            10_000
        );
    }

    /// (c, precise) The eviction threshold and the window gate COINCIDE: at the last
    /// in-window height the proof is retained AND the dispute acquits; at the first
    /// height past it the proof is evictable AND the dispute is rejected. There is no
    /// height where the proof is gone but a dispute would still slash.
    #[tokio::test]
    async fn audit10_eviction_and_gate_thresholds_coincide() {
        // Last admissible height (== deadline 1500): retained + acquit.
        let state = dispute_state(1_500, 1_000);
        state.write().await.delivery_proofs.insert(
            [0xAB; 32],
            DeliveryProofRecord {
                proof: dummy_proof(),
                dispute_deadline: 1_500,
            },
        );
        assert_eq!(
            state.write().await.evict_expired_delivery_proofs(1_500),
            0,
            "retained at the deadline"
        );
        let resp = handle_dispute(State(state.clone()), Json(dispute_req()))
            .await
            .expect("admissible at the deadline")
            .0;
        assert_eq!(resp.verdict, "acquit");

        // First height past (1501): evictable + rejected.
        let state = dispute_state(1_501, 1_000);
        state.write().await.delivery_proofs.insert(
            [0xAB; 32],
            DeliveryProofRecord {
                proof: dummy_proof(),
                dispute_deadline: 1_500,
            },
        );
        assert_eq!(
            state.write().await.evict_expired_delivery_proofs(1_501),
            1,
            "evictable past the deadline"
        );
        let err = handle_dispute(State(state.clone()), Json(dispute_req()))
            .await
            .expect_err("rejected past the deadline");
        assert_eq!(err.0, StatusCode::BAD_REQUEST);
    }

    /// A dispute raised before the deadline is reached at the node's real height is
    /// rejected — no PREMATURE slash of a relay that has not defaulted (even against an
    /// empty/dropped witness set, and even though the disputer forged `at_height`).
    #[tokio::test]
    async fn audit10_premature_dispute_rejected() {
        let state = dispute_state(499, 1_000); // accept_by 500 > current 499
        let err = handle_dispute(State(state.clone()), Json(dispute_req()))
            .await
            .expect_err("premature dispute is rejected");
        assert_eq!(err.0, StatusCode::BAD_REQUEST);
        assert!(
            err.1.0.error.contains("premature"),
            "rejected as premature: {}",
            err.1.0.error
        );
        assert_eq!(
            u64_from_field(state.read().await.template.slots[DISPUTE_COUNT_SLOT as usize]),
            0
        );
    }
}
