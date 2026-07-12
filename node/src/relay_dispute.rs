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
//!     the **conserving [`Effect::Transfer`]s** that distribute the seized bond
//!     FROM the relay cell: a bounded RESTITUTION to the wronged inbox owner
//!     (their proven loss + a small bounty) and the REMAINDER to the protocol
//!     treasury cell (per-asset Σδ = 0; the two legs sum to the seizure).
//!     `build_slash_action` deliberately omits the Transfer (its doc: "the
//!     accompanying `Effect::Transfer` … is the cclerk-side composition"); this
//!     is that composition. Restitution makes the wronged party whole; the
//!     remainder funds the protocol rather than becoming a windfall to the
//!     disputer.
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
//!     `Transfer`), and it is unit-tested with a test cipherclerk. The legacy
//!     in-process [`crate::relay_service::RelayState`] holds no
//!     [`AppCipherclerk`], no governance slash capability, and no minted
//!     relay-operator `CellId`, so the route mutates the MIRROR and reports the
//!     plan rather than submitting a signed turn. Promotion = give `RelayState`
//!     the operator's clerk + the real relay `CellId`, then call
//!     [`build_slash_turn`] and submit through the operator's turn pipeline.
//!   * **Intake still on the deprecated relay-service route.** The live
//!     `POST /relay/dispute` handler hangs off [`crate::relay_service`], the
//!     legacy in-process HTTP surface. The custody-sound intake belongs on the
//!     cell-program relay (the
//!     [`dregg_storage_templates::relay_operator`] executor-enforced slash
//!     transition), NOT this deprecated route; promotion moves the intake there
//!     so the slash rides the executor's turn pipeline, not a mirror mutation.
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

use dregg_app_framework::{Action, AppCipherclerk, CellId, Effect};
use dregg_captp::custody::{EvidenceOfDrop, InboxState, adjudicate_from_inbox};
use dregg_storage_templates::relay_operator::{
    BOND_AMOUNT_SLOT, BOND_MIN_SLOT, DISPUTE_COUNT_SLOT, build_slash_action,
};

use crate::relay_service::SharedRelayState;

/// Default TOTAL seizure requested on a proven drop (computrons), used when the
/// disputant does not name one. Always capped by the bond floor. The seizure is
/// split into a bounded restitution to the wronged party + a treasury remainder.
pub const DEFAULT_SLASH_PENALTY: u64 = 1_000;

/// Default bounty added to the wronged party's proven fee when bounding
/// restitution (computrons). Small — it compensates the cost of raising a
/// well-formed dispute without turning restitution into a windfall; everything
/// beyond `proven_fee + this` flows to the treasury.
pub const DEFAULT_RESTITUTION_BOUNTY: u64 = 100;

/// The protocol treasury cell — destination of the seizure REMAINDER (the part
/// beyond the wronged party's bounded restitution). A well-known, system-owned
/// cell id; the seizure that exceeds restitution funds the protocol rather than
/// becoming a windfall to the disputer.
pub const PROTOCOL_TREASURY_CELL: [u8; 32] = *b"dregg-protocol-treasury-cell-v1\0";

// =============================================================================
// The payout split: restitution to the wronged party, remainder to the treasury
// =============================================================================

/// How a seizure is distributed. A conviction does NOT hand the whole bond to
/// the disputer: the wronged party is made whole up to their proven loss (plus a
/// small bounty), and everything beyond that funds the protocol treasury. Both
/// legs are conserving Transfers out of the relay cell; by construction
/// `restitution + treasury == seized`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SlashPayout {
    /// Computrons restituted to the wronged inbox owner (their proven loss,
    /// bounded by the seizure).
    pub restitution: u64,
    /// Computrons routed to the protocol treasury (the remainder of the seizure).
    pub treasury: u64,
}

impl SlashPayout {
    /// Split a `seized` seizure into a bounded restitution + treasury remainder.
    ///
    /// Restitution is `min(seized, proven_fee + bounty)`: the wronged party never
    /// receives more than their proven loss (fee) plus a small bounty, and never
    /// more than was actually seized. The remainder funds the treasury. Total is
    /// conserved: `restitution + treasury == seized`.
    pub fn split(seized: u64, proven_fee: u64, bounty: u64) -> SlashPayout {
        let restitution = seized.min(proven_fee.saturating_add(bounty));
        SlashPayout {
            restitution,
            treasury: seized - restitution,
        }
    }

    /// The total distributed — always equal to the seizure.
    pub fn total(&self) -> u64 {
        self.restitution + self.treasury
    }
}

// =============================================================================
// The slash plan: the adjudicated seizure, floor-capped
// =============================================================================

/// The concrete, conserving consequence of a `slash` verdict: how much of the
/// relay's bond is seized, the resulting slot values, and where the seized bond
/// flows. Produced by [`plan_slash`] / [`referee_then_plan`] and realized as an
/// on-ledger [`Action`] by [`build_slash_turn`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SlashPlan {
    /// The bonded relay-operator cell being slashed (the `from` of the Transfer,
    /// the target of the slash transition).
    pub relay_cell: CellId,
    /// The wronged inbox owner (`receipt.inbox_owner`) — the `to` of the
    /// conserving restitution Transfer.
    pub wronged_party: CellId,
    /// The protocol treasury cell — the `to` of the conserving REMAINDER
    /// Transfer (the seizure beyond the wronged party's bounded restitution).
    pub treasury_cell: CellId,
    /// How the seizure is split between the wronged party and the treasury.
    /// `payout.restitution + payout.treasury == seized_amount`.
    pub payout: SlashPayout,
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
}

/// Turn a referee verdict into a floor-capped [`SlashPlan`] with a split payout.
///
/// Returns `None` when the verdict is `acquit`. On `slash` it always returns a
/// plan (recording the dispute), with `seized_amount` capped by the bond floor:
/// the seizure can never push the bond below `bond_min`, mirroring the
/// relay-operator slash transition's floor. The seizure is then SPLIT: a bounded
/// restitution (`min(seized, proven_fee + restitution_bounty)`) to the wronged
/// party and the remainder to the treasury — conserving by construction.
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
    treasury_cell: CellId,
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
    // loss + a small bounty, never more than was seized); the remainder funds the
    // protocol treasury rather than becoming a windfall to the disputer.
    let payout = SlashPayout::split(seized, proven_fee, restitution_bounty);
    Some(SlashPlan {
        relay_cell,
        wronged_party,
        treasury_cell,
        payout,
        seized_amount: seized,
        new_bond_amount: bond_amount - seized,
        new_dispute_count: dispute_count.saturating_add(1),
        reason,
    })
}

/// Run the referee ([`adjudicate_from_inbox`]) against the inbox cell and, on a
/// slash, compute the floor-capped, split [`SlashPlan`]. Returns
/// `(slash_verdict, plan)`.
///
/// The wronged party is `receipt.inbox_owner` interpreted as a cell, and the
/// slash reason is the dropped box's `content_hash`. `proven_fee` is the wronged
/// party's proven loss (bounding restitution); `treasury_cell` receives the
/// remainder.
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
    treasury_cell: CellId,
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
        treasury_cell,
        reason,
    );
    (slash, plan)
}

/// Drive the relay-operator slash transition for `plan` and append the conserving
/// payout Transfers.
///
/// [`build_slash_action`] emits the state-transition effects only (`SetField`
/// bond, `SetField` dispute_count, `EmitEvent`); this appends up to TWO
/// [`Effect::Transfer`]s that distribute the seized bond FROM the relay cell: the
/// bounded RESTITUTION to the wronged party and the REMAINDER to the treasury
/// cell. Their amounts sum to the seizure, so computron conservation holds across
/// the three cells (Σδ = 0). A zero-amount leg is omitted (a fully-restituted or
/// fully-treasuried seizure carries a single Transfer; a zero seizure carries
/// none).
pub fn build_slash_turn(cclerk: &AppCipherclerk, plan: &SlashPlan) -> Action {
    let mut action = build_slash_action(
        cclerk,
        plan.relay_cell,
        u64_to_field(plan.new_bond_amount),
        u64_to_field(plan.new_dispute_count),
        plan.reason,
    );
    // Restitution leg: the wronged party's bounded make-whole.
    if plan.payout.restitution > 0 {
        action.effects.push(Effect::Transfer {
            from: plan.relay_cell,
            to: plan.wronged_party,
            amount: plan.payout.restitution,
        });
    }
    // Treasury leg: the remainder of the seizure funds the protocol.
    if plan.payout.treasury > 0 {
        action.effects.push(Effect::Transfer {
            from: plan.relay_cell,
            to: plan.treasury_cell,
            amount: plan.payout.treasury,
        });
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
/// seizure is then split into restitution + treasury remainder, so a large
/// request is not a windfall to the disputer.
#[derive(Debug, Deserialize)]
pub struct DisputeRequest {
    /// The relay's own signed receipt + claimed outcome + dispute height.
    pub evidence: EvidenceOfDrop,
    /// Requested TOTAL seizure in computrons; defaults to [`DEFAULT_SLASH_PENALTY`].
    /// The wronged party's restitution is bounded by their proven loss regardless
    /// of this; the remainder flows to the treasury.
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
    /// Of the seizure, computrons routed to the protocol treasury (the
    /// remainder). `0` on acquit.
    pub treasury_amount: u64,
    /// The bond before this dispute.
    pub prior_bond_amount: u64,
    /// The bond after this dispute (== prior on acquit).
    pub new_bond_amount: u64,
    /// The dispute counter after this dispute (advanced by one on a slash).
    pub dispute_count: u64,
    /// The wronged inbox owner (hex) — the restitution recipient.
    pub wronged_party: String,
    /// The protocol treasury cell (hex) — the remainder recipient.
    pub treasury_cell: String,
    /// The bonded relay-operator cell (hex).
    pub relay_cell: String,
    /// The dropped box's `content_hash` (hex) — the slash provenance.
    pub reason: String,
    /// Number of conserving Transfer effects the paired ledger turn would carry:
    /// one per non-zero payout leg (restitution and/or treasury), so `0`, `1`,
    /// or `2`.
    pub transfer_effects: usize,
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
    // any seizure funds the treasury. Promotion sources the exact paid fee from
    // the dropped box's queue-entry `deposit` (see module docs).
    let proven_fee = s.config.fee_policy.min_deposit_computrons;
    // The relay-operator cell identity. The legacy service does not track the
    // minted relay CellId; the operator identity is its closest in-process
    // proxy (promotion binds the real minted cell — see module docs).
    let relay_cell = CellId::from_bytes(s.config.operator_key);
    // The protocol treasury cell — receives the seizure REMAINDER beyond the
    // wronged party's bounded restitution (not a windfall to the disputer).
    let treasury_cell = CellId::from_bytes(PROTOCOL_TREASURY_CELL);

    let (slash, plan) = referee_then_plan(
        &evidence,
        &inbox,
        prior_bond,
        bond_min,
        dispute_count,
        penalty,
        proven_fee,
        DEFAULT_RESTITUTION_BOUNTY,
        relay_cell,
        treasury_cell,
    );

    if let Some(plan) = plan {
        // Apply the slash transition to the in-process template mirror: bond
        // down by the seized amount, dispute_count +1 — the same slot moves the
        // ledger `build_slash_action` encodes. The paired conserving Transfer
        // rides the on-ledger turn (see `build_slash_turn`); the mirror carries
        // no per-cell balance ledger.
        s.template.slots[BOND_AMOUNT_SLOT as usize] = u64_to_field(plan.new_bond_amount);
        s.template.slots[DISPUTE_COUNT_SLOT as usize] = u64_to_field(plan.new_dispute_count);
        // One conserving Transfer per non-zero leg of the payout split.
        let transfer_effects =
            usize::from(plan.payout.restitution > 0) + usize::from(plan.payout.treasury > 0);
        return Ok(Json(DisputeResponse {
            verdict: "slash",
            slashed: true,
            seized_amount: plan.seized_amount,
            restitution_amount: plan.payout.restitution,
            treasury_amount: plan.payout.treasury,
            prior_bond_amount: prior_bond,
            new_bond_amount: plan.new_bond_amount,
            dispute_count: plan.new_dispute_count,
            wronged_party: hex32(&plan.wronged_party.0),
            treasury_cell: hex32(&plan.treasury_cell.0),
            relay_cell: hex32(&plan.relay_cell.0),
            reason: hex32(&plan.reason),
            transfer_effects,
        }));
    }

    // Acquit: the cell witnesses delivery (or a refund) — no slash, no mutation.
    Ok(Json(DisputeResponse {
        verdict: "acquit",
        slashed: false,
        seized_amount: 0,
        restitution_amount: 0,
        treasury_amount: 0,
        prior_bond_amount: prior_bond,
        new_bond_amount: prior_bond,
        dispute_count,
        wronged_party: hex32(&owner),
        treasury_cell: hex32(&treasury_cell.0),
        relay_cell: hex32(&relay_cell.0),
        reason: hex32(&evidence.receipt.content_hash),
        transfer_effects: 0,
    }))
}

// =============================================================================
// Field codec (big-endian trailing-8, matching relay_service + the templates)
// =============================================================================

fn u64_to_field(value: u64) -> [u8; 32] {
    let mut f = [0u8; 32];
    f[24..32].copy_from_slice(&value.to_be_bytes());
    f
}

fn u64_from_field(field: [u8; 32]) -> u64 {
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
    fn proven_drop_splits_restitution_and_treasury_conserving() {
        // A well-formed receipt + a dropped inbox (no delivered hash, no refund)
        // convicts. The seizure SPLITS: a bounded restitution to the wronged
        // owner + the remainder to the treasury. The two Transfers conserve.
        let evidence = EvidenceOfDrop::from_receipt(demo_receipt());
        let inbox = InboxState::from_dequeue(&evidence.receipt, &[], [0x64; 32], false);
        let relay_cell = CellId::from_bytes([0x11; 32]);
        let treasury_cell = CellId::from_bytes([0x77; 32]);

        // Seize 500; proven loss 120 + bounty 30 => restitution 150, treasury 350.
        let (slash, plan) = referee_then_plan(
            &evidence,
            &inbox,
            10_000,
            1_000,
            0,
            500,
            120,
            30,
            relay_cell,
            treasury_cell,
        );
        assert!(slash, "a genuine drop must slash");
        let plan = plan.expect("a slash verdict must yield a plan");
        assert_eq!(plan.seized_amount, 500);
        assert_eq!(plan.payout.restitution, 150, "proven loss + bounty");
        assert_eq!(
            plan.payout.treasury, 350,
            "the remainder funds the protocol"
        );
        assert_eq!(
            plan.payout.total(),
            plan.seized_amount,
            "the split conserves the seizure"
        );
        assert_eq!(plan.new_bond_amount, 9_500);
        assert_eq!(plan.new_dispute_count, 1);
        assert_eq!(plan.wronged_party.0, [0x03; 32]);
        assert_eq!(plan.treasury_cell.0, [0x77; 32]);
        assert_eq!(plan.reason, [0xAB; 32], "slash names the dropped box");

        let action = build_slash_turn(&test_cclerk(), &plan);
        // build_slash_action = SetField(bond) + SetField(dispute) + EmitEvent (3);
        // the weld appends TWO conserving Transfers (restitution + treasury).
        assert_eq!(action.effects.len(), 5);
        let transfers: Vec<(CellId, CellId, u64)> = action
            .effects
            .iter()
            .filter_map(|e| match e {
                Effect::Transfer { from, to, amount } => Some((*from, *to, *amount)),
                _ => None,
            })
            .collect();
        assert_eq!(transfers.len(), 2, "restitution + treasury legs");
        assert!(
            transfers.iter().all(|(from, _, _)| *from == relay_cell),
            "every leg is seized FROM the relay cell"
        );
        let restitution = transfers
            .iter()
            .find(|(_, to, _)| *to == plan.wronged_party)
            .expect("a restitution leg to the wronged owner");
        let treasury = transfers
            .iter()
            .find(|(_, to, _)| *to == treasury_cell)
            .expect("a treasury leg for the remainder");
        assert_eq!(restitution.2, 150);
        assert_eq!(treasury.2, 350);
        assert_eq!(
            restitution.2 + treasury.2,
            plan.seized_amount,
            "Σδ = 0 across the seizure"
        );
    }

    #[test]
    fn treasury_gets_the_rest_when_no_proven_loss() {
        // No proven fee and no bounty => the wronged party is owed nothing extra,
        // so the ENTIRE seizure funds the treasury (a single treasury Transfer).
        let evidence = EvidenceOfDrop::from_receipt(demo_receipt());
        let inbox = InboxState::from_dequeue(&evidence.receipt, &[], [0x64; 32], false);
        let relay_cell = CellId::from_bytes([0x11; 32]);
        let treasury_cell = CellId::from_bytes([0x77; 32]);

        let (slash, plan) = referee_then_plan(
            &evidence,
            &inbox,
            10_000,
            1_000,
            0,
            500,
            0,
            0,
            relay_cell,
            treasury_cell,
        );
        assert!(slash);
        let plan = plan.unwrap();
        assert_eq!(plan.payout.restitution, 0, "nothing proven to restitute");
        assert_eq!(
            plan.payout.treasury, 500,
            "the whole seizure funds the treasury"
        );
        assert_eq!(plan.payout.total(), plan.seized_amount);

        let action = build_slash_turn(&test_cclerk(), &plan);
        let transfers: Vec<(CellId, u64)> = action
            .effects
            .iter()
            .filter_map(|e| match e {
                Effect::Transfer { to, amount, .. } => Some((*to, *amount)),
                _ => None,
            })
            .collect();
        assert_eq!(transfers.len(), 1, "a zero restitution leg is omitted");
        assert_eq!(transfers[0], (treasury_cell, 500));
    }

    #[test]
    fn restitution_capped_at_seized() {
        // The proven loss dwarfs the seizure (bond at its floor): restitution is
        // capped at the whole seizure and the treasury gets nothing.
        let evidence = EvidenceOfDrop::from_receipt(demo_receipt());
        let inbox = InboxState::from_dequeue(&evidence.receipt, &[], [0x64; 32], false);
        let relay_cell = CellId::from_bytes([0x11; 32]);
        let treasury_cell = CellId::from_bytes([0x77; 32]);

        // Headroom only 200; proven loss 10_000 + bounty 100 dwarfs it.
        let (slash, plan) = referee_then_plan(
            &evidence,
            &inbox,
            1_200,
            1_000,
            3,
            5_000,
            10_000,
            100,
            relay_cell,
            treasury_cell,
        );
        assert!(slash);
        let plan = plan.unwrap();
        assert_eq!(plan.seized_amount, 200, "capped at the bond floor");
        assert_eq!(
            plan.payout.restitution, 200,
            "restitution never exceeds the seizure"
        );
        assert_eq!(plan.payout.treasury, 0, "nothing left for the treasury");
        assert_eq!(plan.payout.total(), plan.seized_amount);

        let action = build_slash_turn(&test_cclerk(), &plan);
        let transfers = action
            .effects
            .iter()
            .filter(|e| matches!(e, Effect::Transfer { .. }))
            .count();
        assert_eq!(transfers, 1, "a zero-treasury leg is omitted");
    }

    #[test]
    fn payout_split_conserves() {
        // The pure split is conserving for every proven_fee/bounty relative to
        // the seizure.
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
                p.restitution + p.treasury,
                seized,
                "restitution + treasury == seized"
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
        // referee acquits ⇒ no plan, no Transfer, regardless of the drop-claim.
        let evidence = EvidenceOfDrop::from_receipt(demo_receipt());
        let inbox = InboxState::from_dequeue(&evidence.receipt, &[[0xAB; 32]], [0x8E; 32], false);
        let relay_cell = CellId::from_bytes([0x11; 32]);
        let treasury_cell = CellId::from_bytes([0x77; 32]);

        let (slash, plan) = referee_then_plan(
            &evidence,
            &inbox,
            10_000,
            1_000,
            0,
            500,
            120,
            30,
            relay_cell,
            treasury_cell,
        );
        assert!(!slash, "a delivered box must acquit");
        assert!(plan.is_none(), "acquit ⇒ no slash plan");
    }

    #[test]
    fn bond_floor_caps_the_seizure() {
        // penalty 5_000 but only 200 above the floor ⇒ seize 200, land exactly on
        // bond_min. The dispute is still recorded, and the 200 splits per the
        // payout model (here proven loss 500 => all 200 restituted).
        let evidence = EvidenceOfDrop::from_receipt(demo_receipt());
        let inbox = InboxState::from_dequeue(&evidence.receipt, &[], [0x64; 32], false);
        let relay_cell = CellId::from_bytes([0x11; 32]);
        let treasury_cell = CellId::from_bytes([0x77; 32]);

        let (slash, plan) = referee_then_plan(
            &evidence,
            &inbox,
            1_200,
            1_000,
            3,
            5_000,
            500,
            0,
            relay_cell,
            treasury_cell,
        );
        assert!(slash);
        let plan = plan.unwrap();
        assert_eq!(plan.seized_amount, 200, "capped at the bond floor");
        assert_eq!(plan.new_bond_amount, 1_000, "never below bond_min");
        assert_eq!(plan.new_dispute_count, 4);
        assert_eq!(plan.payout.restitution, 200);
        assert_eq!(plan.payout.treasury, 0);
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
        let treasury_cell = CellId::from_bytes([0x77; 32]);

        let (slash, plan) = referee_then_plan(
            &evidence,
            &inbox,
            10_000,
            1_000,
            0,
            500,
            120,
            30,
            relay_cell,
            treasury_cell,
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
}
