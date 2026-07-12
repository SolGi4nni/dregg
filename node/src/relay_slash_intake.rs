//! Cell-program slash intake — the dispute path on the relay-operator CELL.
//!
//! Replaces the deprecated in-process [`crate::relay_service`] dispute route as
//! the intake for custody disputes. Where the legacy `POST /relay/dispute`
//! handler ([`crate::relay_dispute::handle_dispute`]) applies the slash to an
//! in-process template MIRROR, [`intake_dispute`] produces the real thing: on a
//! conviction, a signed [`Turn`] invoking the relay-operator cell's `slash`
//! method — the executor-enforced transition of
//! [`dregg_storage_templates::relay_operator::relay_operator_program`]
//! (`BoundedBy { bond, dispute }` + `FieldDelta { dispute, +1 }`) — carrying the
//! adjudicated [`SlashPlan`]'s conserving payout.
//!
//! The loop stays **bilateral and owner-anchored**: the conviction is the
//! relay's OWN signed receipt against the inbox cell's authenticated state
//! (`dregg_captp::custody::adjudicate_from_inbox`), not a global-consensus
//! vote. No global-owned entity appears anywhere: the remainder destination is
//! `SlashPlan::remainder_dest`, a deployment-chosen cell.
//!
//! # What is REAL vs the submit-seam (honest scope)
//!
//! REAL:
//!   * the referee — [`referee_then_plan`] runs the crypto-sound, reorg-robust
//!     verdict and computes the floor-capped, split [`SlashPlan`];
//!   * the [`dregg_app_framework::Action`] — [`build_slash_turn`] drives the
//!     template's `build_slash_action` (SetField bond + SetField dispute_count
//!     + EmitEvent, method = `slash_method_symbol()`) and appends the
//!     conserving restitution + remainder `Effect::Transfer`s
//!     (`restitution + remainder == seized`, so Σδ = 0 across the relay cell,
//!     the wronged party, and the remainder destination — nothing minted,
//!     nothing destroyed), signed for real by `AppCipherclerk::make_action`;
//!   * the [`Turn`] — `AppCipherclerk::make_turn` wraps the action in the
//!     canonical single-action call forest;
//!   * the enforcement — the tests below install the relay-operator
//!     `CellProgram` on a relay cell in a real
//!     [`dregg_app_framework::EmbeddedExecutor`] and submit the produced turn:
//!     the slash case ADMITS it, and a bond decrement without the dispute-count
//!     advance (or an unknown drain method) is REJECTED by the program and
//!     rolled back. The "no-drain-without-dispute" invariant is enforced by the
//!     executor's program evaluation, not re-implemented here.
//!
//! THE SEAM (submission + inputs):
//!   * **Submission.** This module does not submit. The returned turn's nonce
//!     is 0; the caller's turn pipeline sets the real nonce and ships it —
//!     `EmbeddedExecutor::submit_turn` in-process, or the node's
//!     `POST /turns/submit` ingress for a remote relay-operator cell. Both
//!     Transfer destinations (the wronged party, the remainder destination)
//!     must be live cells on the executing ledger, or the executor fails
//!     closed with `TransferDestNotFound` — a payout can never silently vanish.
//!   * **Authorization.** The turn is signed by the intake cipherclerk; which
//!     authorization the DEPLOYED relay cell demands for `slash` (the factory's
//!     governance `CapTemplate` / its `Permissions`) is deployment
//!     configuration that the executor enforces at submission. Nothing here
//!     weakens that check — an unauthorized intake turn is simply rejected.
//!   * **Slot readings.** [`RelaySlots`] comes from the caller, read off the
//!     LIVE relay-operator cell state ([`RelaySlots::from_cell_state`]) — not
//!     the legacy mirror. A stale reading cannot smuggle a wrong transition:
//!     the program's `FieldDelta { dispute, +1 }` compares against the live
//!     cell at execution and rejects a mismatched turn.
//!   * **Refund witness / proven fee.** Unchanged from
//!     [`crate::relay_dispute`]'s module docs: the caller owns supplying an
//!     [`InboxState`] whose `refund_recorded` bit is real, and a
//!     [`SlashPolicy::proven_fee`] sourced from the dropped box's actual
//!     deposit. The default policy is fail-conservative: `proven_fee = 0`
//!     restitutes nothing it cannot prove (the whole seizure goes to the
//!     remainder destination).
//!
//! A conviction with the bond already at its floor still produces a turn: the
//! bond `SetField` carries the unchanged value (so `BoundedBy` sees no bond
//! move), the dispute counter still advances by one, and there are no payout
//! legs — the dispute is RECORDED on the cell even when nothing is seizable.

use dregg_app_framework::{AppCipherclerk, CellId, Turn};
use dregg_captp::custody::{EvidenceOfDrop, InboxState};
use dregg_storage_templates::relay_operator::{
    BOND_AMOUNT_SLOT, BOND_MIN_SLOT, DISPUTE_COUNT_SLOT,
};

use crate::relay_dispute::{
    DEFAULT_RESTITUTION_BOUNTY, DEFAULT_SLASH_PENALTY, SlashPlan, build_slash_turn,
    referee_then_plan, u64_from_field,
};

/// Live slot readings off the relay-operator CELL (not the legacy in-process
/// mirror): the three slots the slash transition consults.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelaySlots {
    /// Current `bond_amount` (slot 0).
    pub bond_amount: u64,
    /// Immutable `bond_min` floor (slot 1).
    pub bond_min: u64,
    /// Current `dispute_count` (slot 7).
    pub dispute_count: u64,
}

impl RelaySlots {
    /// Read the slash-relevant slots off a live relay-operator cell state
    /// (e.g. `EmbeddedExecutor::cell_state(relay_cell)`, or the node's ledger
    /// view of a remote cell).
    pub fn from_cell_state(state: &dregg_cell::CellState) -> Self {
        Self {
            bond_amount: u64_from_field(state.fields[BOND_AMOUNT_SLOT as usize]),
            bond_min: u64_from_field(state.fields[BOND_MIN_SLOT as usize]),
            dispute_count: u64_from_field(state.fields[DISPUTE_COUNT_SLOT as usize]),
        }
    }
}

/// Seizure policy inputs: how much total seizure the disputant asks for and
/// how the wronged party's restitution is bounded. See
/// [`crate::relay_dispute::SlashPayout::split`] for the conserving split.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SlashPolicy {
    /// Requested TOTAL seizure (computrons); always capped by the bond floor.
    pub requested_penalty: u64,
    /// The wronged party's PROVEN loss (the dropped box's actual deposit).
    /// Bounds restitution; `0` (the default) restitutes nothing unproven.
    pub proven_fee: u64,
    /// Small bounty added to the proven fee when bounding restitution.
    pub restitution_bounty: u64,
}

impl Default for SlashPolicy {
    fn default() -> Self {
        Self {
            requested_penalty: DEFAULT_SLASH_PENALTY,
            proven_fee: 0,
            restitution_bounty: DEFAULT_RESTITUTION_BOUNTY,
        }
    }
}

/// The outcome of a dispute intake on the cell-program path.
#[derive(Debug)]
pub enum DisputeIntake {
    /// The evidence failed the referee's own admissibility gate (forged
    /// receipt signature, or a dispute raised before `accept_by`). No cell
    /// read, no referee run, no turn.
    Rejected {
        /// Why the evidence was inadmissible.
        reason: &'static str,
    },
    /// The referee acquitted — the inbox cell witnesses delivery (or a
    /// refund). No turn; nothing to submit.
    Acquitted,
    /// Conviction: the adjudicated, floor-capped [`SlashPlan`] and the SIGNED
    /// [`Turn`] invoking the relay-operator cell's `slash` method with the
    /// conserving payout composed in. Submitting it through the node's turn
    /// pipeline is the caller's seam (see module docs).
    Convicted {
        /// The adjudicated seizure and its conserving disposition.
        plan: SlashPlan,
        /// The signed, unsubmitted turn (nonce is set by the submission path).
        turn: Box<Turn>,
    },
}

/// The cell-program dispute intake: admissibility gate → referee → on a
/// conviction, the signed slash turn for the relay-operator CELL.
///
/// Mirrors the verdict logic of the legacy route exactly (same
/// [`referee_then_plan`], same floor cap, same conserving split) but realizes
/// the consequence as the executor-enforced cell transition instead of a
/// mirror mutation. See the module docs for what is real vs the submit-seam.
pub fn intake_dispute(
    cclerk: &AppCipherclerk,
    evidence: &EvidenceOfDrop,
    inbox: &InboxState,
    relay_cell: CellId,
    slots: RelaySlots,
    policy: SlashPolicy,
) -> DisputeIntake {
    // Admissibility (the referee's own gate): a forged receipt or a premature
    // dispute convicts nobody — reject before any adjudication.
    if !evidence.well_formed() {
        return DisputeIntake::Rejected {
            reason: "evidence not well-formed: bad receipt signature or dispute raised before accept_by",
        };
    }

    let (_slash, plan) = referee_then_plan(
        evidence,
        inbox,
        slots.bond_amount,
        slots.bond_min,
        slots.dispute_count,
        policy.requested_penalty,
        policy.proven_fee,
        policy.restitution_bounty,
        relay_cell,
    );

    match plan {
        None => DisputeIntake::Acquitted,
        Some(plan) => {
            // The REAL action: build_slash_action's SetFields (bond,
            // dispute_count) + EmitEvent under the `slash` method symbol, plus
            // the conserving restitution/remainder Transfers — signed by the
            // intake cipherclerk and wrapped in the canonical single-action
            // call forest.
            let action = build_slash_turn(cclerk, &plan);
            let turn = cclerk.make_turn(action);
            DisputeIntake::Convicted {
                plan,
                turn: Box::new(turn),
            }
        }
    }
}

// =============================================================================
// Tests — the produced Action, and the cell program actually biting
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, Effect, EmbeddedExecutor};
    use dregg_captp::FederationId;
    use dregg_captp::custody::CustodyReceipt;
    use dregg_cell::{AuthRequired, Cell, Permissions};
    use dregg_storage_templates::relay_operator::{
        OPERATOR_PK_HASH_SLOT, QUOTA_BYTES_PER_EPOCH_SLOT, ROUTE_TABLE_ROOT_SLOT,
        relay_operator_program, slash_method_symbol,
    };
    use dregg_types::{SigningKey, generate_keypair};

    use crate::relay_dispute::{default_slash_treasury, u64_to_field};

    fn test_cclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [0x42u8; 32])
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

    fn dropped_inbox(evidence: &EvidenceOfDrop) -> InboxState {
        InboxState::from_dequeue(&evidence.receipt, &[], [0x64; 32], false)
    }

    const SLOTS: RelaySlots = RelaySlots {
        bond_amount: 10_000,
        bond_min: 1_000,
        dispute_count: 0,
    };

    const POLICY: SlashPolicy = SlashPolicy {
        requested_penalty: 500,
        proven_fee: 120,
        restitution_bounty: 30,
    };

    #[test]
    fn conviction_turn_invokes_slash_method_on_the_relay_cell_and_conserves() {
        let cclerk = test_cclerk();
        let relay_cell = CellId::from_bytes([0x11; 32]);
        let evidence = EvidenceOfDrop::from_receipt(demo_receipt());
        let inbox = dropped_inbox(&evidence);

        let DisputeIntake::Convicted { plan, turn } =
            intake_dispute(&cclerk, &evidence, &inbox, relay_cell, SLOTS, POLICY)
        else {
            panic!("a genuine drop must convict");
        };

        // Seize 500; proven loss 120 + bounty 30 => restitution 150, remainder 350.
        assert_eq!(plan.seized_amount, 500);
        assert_eq!(plan.payout.restitution, 150);
        assert_eq!(plan.payout.remainder, 350);

        // One action, agent = the intake cclerk, target = the relay-operator
        // cell, method = the CELL PROGRAM's slash symbol.
        assert_eq!(turn.agent, cclerk.cell_id());
        assert_eq!(turn.call_forest.roots.len(), 1, "single-action call forest");
        let action = &turn.call_forest.roots[0].action;
        assert_eq!(action.target, relay_cell, "turn targets the relay cell");
        assert_eq!(
            action.method,
            slash_method_symbol(),
            "turn invokes the relay_operator cell program's slash method"
        );

        // The transition legs land on the RIGHT SLOTS of the RIGHT CELL with
        // the plan's exact values (bond 10_000 -> 9_500, dispute 0 -> 1).
        assert!(action.effects.iter().any(|e| matches!(e,
            Effect::SetField { cell, index, value }
            if *cell == relay_cell
                && *index == BOND_AMOUNT_SLOT as usize
                && *value == u64_to_field(9_500)
        )));
        assert!(action.effects.iter().any(|e| matches!(e,
            Effect::SetField { cell, index, value }
            if *cell == relay_cell
                && *index == DISPUTE_COUNT_SLOT as usize
                && *value == u64_to_field(1)
        )));

        // Conserving payout: both legs FROM the relay cell, restitution TO the
        // wronged inbox owner, remainder TO the treasury; Σ legs == seizure.
        let transfers: Vec<(CellId, CellId, u64)> = action
            .effects
            .iter()
            .filter_map(|e| match e {
                Effect::Transfer { from, to, amount } => Some((*from, *to, *amount)),
                _ => None,
            })
            .collect();
        assert_eq!(transfers.len(), 2, "restitution + remainder legs");
        assert_eq!(
            transfers[0],
            (relay_cell, CellId::from_bytes([0x03; 32]), 150)
        );
        assert_eq!(transfers[1], (relay_cell, default_slash_treasury(), 350));
        assert_eq!(
            transfers[0].2 + transfers[1].2,
            plan.seized_amount,
            "the whole seizure leaves the operator, conserving (Sigma delta 0)"
        );
    }

    #[test]
    fn acquit_and_inadmissible_evidence_produce_no_turn() {
        let cclerk = test_cclerk();
        let relay_cell = CellId::from_bytes([0x11; 32]);

        // Delivered box (witness bit set) => the referee acquits => no turn.
        let evidence = EvidenceOfDrop::from_receipt(demo_receipt());
        let delivered =
            InboxState::from_dequeue(&evidence.receipt, &[[0xAB; 32]], [0x8E; 32], false);
        assert!(matches!(
            intake_dispute(&cclerk, &evidence, &delivered, relay_cell, SLOTS, POLICY),
            DisputeIntake::Acquitted
        ));

        // Forged receipt (content_hash mutated after signing) => rejected at
        // the admissibility gate, before any referee run.
        let mut forged = demo_receipt();
        forged.content_hash = [0xEE; 32];
        let forged_evidence = EvidenceOfDrop::from_receipt(forged);
        let inbox = dropped_inbox(&forged_evidence);
        assert!(matches!(
            intake_dispute(&cclerk, &forged_evidence, &inbox, relay_cell, SLOTS, POLICY),
            DisputeIntake::Rejected { .. }
        ));

        // Premature dispute (at_height < accept_by) => rejected.
        let mut premature = EvidenceOfDrop::from_receipt(demo_receipt());
        premature.at_height = premature.receipt.accept_by - 1;
        let inbox = dropped_inbox(&premature);
        assert!(matches!(
            intake_dispute(&cclerk, &premature, &inbox, relay_cell, SLOTS, POLICY),
            DisputeIntake::Rejected { .. }
        ));
    }

    // ── The executor-enforced weld ───────────────────────────────────────────

    fn open_permissions() -> Permissions {
        Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        }
    }

    /// Boot an operator + embedded executor with a REAL relay-operator cell:
    /// the template [`dregg_cell::CellProgram`] installed, the §3.5 slot
    /// layout seeded (bond 10_000 / floor 1_000 / dispute_count 0), a 100_000
    /// balance, and LIVE Transfer destinations for the payout legs. The relay
    /// cell is open-permissioned so the test isolates the PROGRAM's
    /// enforcement (the deployed cell's authorization is a separate,
    /// still-enforced deployment choice — see module docs).
    fn executor_with_relay_cell() -> (AppCipherclerk, EmbeddedExecutor, CellId) {
        let operator = AppCipherclerk::new(AgentCipherclerk::new(), [0x42u8; 32]);
        let exec = EmbeddedExecutor::new(&operator, "default");
        let operator_cell = operator.cell_id();

        // A dedicated relay cell (NOT the operator's agent cell, so turn fees
        // never touch the bond accounting this test asserts on).
        let token_id = *blake3::hash(b"default").as_bytes();
        let mut relay = Cell::with_balance([0x51u8; 32], token_id, 100_000);
        relay.permissions = open_permissions();
        let relay_id = relay.id();
        exec.ensure_cell(relay).expect("relay cell co-placed");
        exec.install_program(relay_id, relay_operator_program());

        exec.with_ledger_mut(|ledger| {
            let cell = ledger.get_mut(&relay_id).expect("relay cell exists");
            cell.state
                .set_field(BOND_AMOUNT_SLOT as usize, u64_to_field(10_000));
            cell.state
                .set_field(BOND_MIN_SLOT as usize, u64_to_field(1_000));
            cell.state
                .set_field(QUOTA_BYTES_PER_EPOCH_SLOT as usize, u64_to_field(1_000_000));
            cell.state.set_field(
                OPERATOR_PK_HASH_SLOT as usize,
                *blake3::hash(b"operator-pk").as_bytes(),
            );
            cell.state.set_field(
                ROUTE_TABLE_ROOT_SLOT as usize,
                *blake3::hash(b"route-table").as_bytes(),
            );
            let op = ledger
                .get_mut(&operator_cell)
                .expect("operator agent cell exists");
            op.capabilities
                .grant(relay_id, AuthRequired::None)
                .expect("grant relay access");
        });

        // Transfer destinations must be LIVE cells on the executing ledger
        // (the executor fails closed with TransferDestNotFound otherwise).
        let wronged = CellId::from_bytes([0x03u8; 32]); // demo receipt inbox_owner
        exec.ensure_cell(Cell::remote_stub_with_id(wronged))
            .expect("wronged party cell");
        exec.ensure_cell(Cell::remote_stub_with_id(default_slash_treasury()))
            .expect("treasury cell");

        (operator, exec, relay_id)
    }

    fn balance_of(exec: &EmbeddedExecutor, cell: CellId) -> i64 {
        exec.cell_state(cell).map(|s| s.balance()).unwrap_or(0)
    }

    #[test]
    fn executor_admits_the_intake_turn_through_the_installed_cell_program() {
        let (operator, exec, relay_id) = executor_with_relay_cell();
        let wronged = CellId::from_bytes([0x03u8; 32]);

        // Slot readings come off the LIVE cell, not a mirror.
        let slots = RelaySlots::from_cell_state(&exec.cell_state(relay_id).expect("relay state"));
        assert_eq!(slots, SLOTS, "live-cell readback matches the seeded layout");

        let evidence = EvidenceOfDrop::from_receipt(demo_receipt());
        let inbox = dropped_inbox(&evidence);
        let DisputeIntake::Convicted { plan, turn } =
            intake_dispute(&operator, &evidence, &inbox, relay_id, slots, POLICY)
        else {
            panic!("a genuine drop must convict");
        };

        // THE WELD: the produced turn commits through the EXECUTOR-ENFORCED
        // relay_operator cell program (BoundedBy + FieldDelta both satisfied).
        let receipt = exec
            .submit_turn(&turn)
            .expect("the slash turn must commit through the installed cell program");
        assert_eq!(receipt.action_count, 1);

        // Slots moved exactly as the plan encoded.
        let state = exec.cell_state(relay_id).expect("relay state after slash");
        assert_eq!(
            state.fields[BOND_AMOUNT_SLOT as usize],
            u64_to_field(9_500),
            "bond decremented by the seizure"
        );
        assert_eq!(
            state.fields[DISPUTE_COUNT_SLOT as usize],
            u64_to_field(1),
            "dispute counter advanced by exactly one"
        );

        // Conserving payout landed: relay -500, wronged +150, treasury +350.
        assert_eq!(plan.seized_amount, 500);
        assert_eq!(balance_of(&exec, relay_id), 100_000 - 500);
        assert_eq!(balance_of(&exec, wronged), 150);
        assert_eq!(balance_of(&exec, default_slash_treasury()), 350);
    }

    #[test]
    fn cell_program_rejects_bond_drain_without_dispute_advance() {
        let (operator, exec, relay_id) = executor_with_relay_cell();
        let attacker = CellId::from_bytes([0x66u8; 32]);
        exec.ensure_cell(Cell::remote_stub_with_id(attacker))
            .expect("attacker cell");

        // Adversarial slash: decrement the bond and take the money WITHOUT
        // advancing the dispute counter. BoundedBy (bond changed, witness
        // zero) and FieldDelta (dispute not +1) must both refuse it.
        let drain = operator.make_action(
            relay_id,
            "slash",
            vec![
                Effect::SetField {
                    cell: relay_id,
                    index: BOND_AMOUNT_SLOT as usize,
                    value: u64_to_field(9_500),
                },
                Effect::Transfer {
                    from: relay_id,
                    to: attacker,
                    amount: 500,
                },
            ],
        );
        assert!(
            exec.submit_turn(&operator.make_turn(drain)).is_err(),
            "a bond drain without the dispute advance must be rejected by the cell program"
        );

        // Unknown method: default-deny (Cav-Codex Block 4) — the program's
        // operation discrimination protects the bond even off the slash case.
        let skim = operator.make_action(
            relay_id,
            "withdraw_bond",
            vec![Effect::Transfer {
                from: relay_id,
                to: attacker,
                amount: 500,
            }],
        );
        assert!(
            exec.submit_turn(&operator.make_turn(skim)).is_err(),
            "an unknown method must be default-denied by the cell program"
        );

        // Both rejections rolled back: bond intact, attacker got nothing.
        let state = exec.cell_state(relay_id).expect("relay state");
        assert_eq!(
            state.fields[BOND_AMOUNT_SLOT as usize],
            u64_to_field(10_000)
        );
        assert_eq!(balance_of(&exec, relay_id), 100_000);
        assert_eq!(balance_of(&exec, attacker), 0);
    }
}
