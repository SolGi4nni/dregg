//! The **cap∧state council board**, end-to-end on the composed deos app — the
//! `GatedAffordance` (the Rust twin of the Lean rung `Dregg2.Deos.GatedAffordance`)
//! driven through the framework's `DeosCell` + `EmbeddedExecutor`. This is the CI gate
//! for the `deos_council_board` example: the demo's narrated claims, as assertions.
//!
//! `docs/deos/DEOS.md` §"htmx on crack". A button on a deos surface lights IFF the
//! viewer holds the cap AND the cell's LIVE state admits the fire — and the surface
//! REACTS to the cell (a button dark in one state lights in another). The four corners
//! of the conjunction + the htmx transition, each carried through the REAL executor.
//!
//! The load-bearing honesty mirrors the Lean keystones:
//!   - `fireGated_both_pass` — caps ∧ state ⇒ a real verified turn (the executor's own
//!     receipt);
//!   - `fireGated_cap_fail_refuses` — wrong caps ⇒ refused in-band, nothing submitted;
//!   - `fireGated_state_fail_refuses` — wrong state ⇒ refused in-band EVEN for a
//!     fully-authorized actor, nothing submitted (the half a cap-only gate can't express);
//!   - `fireGated_reactive` — the SAME viewer's verdict changes as the cell transitions.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellAffordance, DeosApp, DeosCell, Effect,
    EmbeddedExecutor, Event, FireError, FireExecuteError, GatedAffordance,
};
use dregg_cell::state::FieldElement;
use dregg_cell::{CellProgram, StateConstraint};

const STATUS_SLOT: usize = 0;
const PENDING: u64 = 1;
const RESOLVED: u64 = 2;

fn fe(n: u64) -> FieldElement {
    let mut b = [0u8; 32];
    b[24..32].copy_from_slice(&n.to_be_bytes());
    b
}

/// The affordance precondition: fire only while the proposal is PENDING.
fn pending_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: STATUS_SLOT as u8,
        value: fe(PENDING),
    }])
}

/// The cell's lifetime invariant: status is monotonic (may resolve, never un-resolve).
fn proposal_invariant() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::Monotonic {
        index: STATUS_SLOT as u8,
    }])
}

fn set_status(executor: &EmbeddedExecutor, proposal: dregg_app_framework::CellId, status: u64) {
    executor.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&proposal) {
            cell.state.set_field(STATUS_SLOT, fe(status));
        }
    });
}

/// Build the council board on the agent's own cell (so the embedded ledger holds it and
/// gated fires execute through the real executor), seeded PENDING with the monotonic
/// invariant installed.
fn board() -> (AppCipherclerk, EmbeddedExecutor, DeosCell) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0xC0; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let proposal = cclerk.cell_id();
    executor.install_program(proposal, proposal_invariant());
    set_status(&executor, proposal, PENDING);

    let approve = GatedAffordance::new(
        CellAffordance::new(
            "approve",
            AuthRequired::Either,
            Effect::SetField {
                cell: proposal,
                index: STATUS_SLOT,
                value: fe(RESOLVED),
            },
        ),
        pending_precondition(),
    );
    let comment = CellAffordance::new(
        "comment",
        AuthRequired::Signature,
        Effect::EmitEvent {
            cell: proposal,
            event: Event {
                topic: [0xC0; 32],
                data: vec![],
            },
        },
    );
    let cell = DeosCell::new(proposal, "proposal")
        .affordance(comment)
        .gated(approve);
    let app = DeosApp::builder("council-board", cclerk.clone(), executor.clone())
        .cell(cell)
        .build();
    let cell = app.cells()[0].clone();
    (cclerk, executor, cell)
}

#[test]
fn the_per_viewer_per_state_projection_diverges_by_caps_and_state() {
    let (_cclerk, executor, board) = board();
    let approver = AuthRequired::Either;
    let member = AuthRequired::Signature;

    // PENDING: the approver projects `approve` (cap ∧ state both pass); the member does
    // not (cap tooth darkens it). The framework reads the live state from the executor.
    let approver_lit = board.gated_fireable_names(&approver, &executor);
    let member_lit = board.gated_fireable_names(&member, &executor);
    assert_eq!(
        approver_lit,
        vec!["approve".to_string()],
        "approver: approve lit in PENDING"
    );
    assert!(
        member_lit.is_empty(),
        "member: approve dark (wrong caps) — got {member_lit:?}"
    );

    // Transition to RESOLVED: the SAME approver's projected set loses `approve` (the
    // htmx tooth — the surface reacted to the cell, not to who is looking).
    set_status(&executor, board.cell(), RESOLVED);
    let approver_after = board.gated_fireable_names(&approver, &executor);
    assert!(
        approver_after.is_empty(),
        "htmx tooth: approve darkened in RESOLVED for the SAME approver — got {approver_after:?}"
    );
}

#[test]
fn both_pass_fires_a_real_verified_turn_through_the_executor() {
    let (cclerk, executor, board) = board();
    // caps (Either) ∧ state (PENDING) both pass ⇒ a real verified turn; the receipt is
    // the executor's OWN, and the proposal actually transitions to RESOLVED.
    let receipt = board
        .fire_gated_through_executor("approve", &AuthRequired::Either, &cclerk, &executor)
        .expect("caps ∧ state both pass ⇒ a real verified turn");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real turn hash");
    assert_eq!(
        receipt.agent,
        board.cell(),
        "the receipt's agent is the proposal cell"
    );
    // The verified turn moved the cell: status is now RESOLVED.
    let st = executor.cell_state(board.cell()).expect("cell present");
    assert_eq!(
        st.get_field(STATUS_SLOT),
        Some(&fe(RESOLVED)),
        "approve resolved the proposal"
    );
}

#[test]
fn the_cap_tooth_refuses_a_member_in_band_nothing_submitted() {
    let (cclerk, executor, board) = board();
    // PENDING (right state), Signature (wrong caps) ⇒ refused by the CAP tooth in-band.
    match board.fire_gated_through_executor("approve", &AuthRequired::Signature, &cclerk, &executor)
    {
        Err(FireExecuteError::Gate(FireError::Unauthorized { affordance, .. })) => {
            assert_eq!(affordance, "approve");
        }
        other => panic!("expected an in-band Unauthorized refusal, got {other:?}"),
    }
    // Anti-ghost: nothing was submitted — the proposal is still PENDING.
    let st = executor.cell_state(board.cell()).expect("cell present");
    assert_eq!(
        st.get_field(STATUS_SLOT),
        Some(&fe(PENDING)),
        "no turn ran (still PENDING)"
    );
}

#[test]
fn the_state_tooth_refuses_a_stale_fire_even_for_an_authorized_actor() {
    let (cclerk, executor, board) = board();
    // Resolve the proposal first (a legitimate approve), then the approver fires AGAIN.
    board
        .fire_gated_through_executor("approve", &AuthRequired::Either, &cclerk, &executor)
        .expect("the first approve resolves it");
    // RESOLVED (wrong state), Either (right caps) ⇒ refused by the STATE tooth in-band —
    // the half a cap-only gate could never express.
    match board.fire_gated_through_executor("approve", &AuthRequired::Either, &cclerk, &executor) {
        Err(FireExecuteError::Gate(FireError::StateConditionUnmet { affordance, .. })) => {
            assert_eq!(affordance, "approve");
        }
        other => panic!("expected an in-band StateConditionUnmet refusal, got {other:?}"),
    }
    // Anti-ghost for the state tooth: the second fire submitted nothing; status is the
    // RESOLVED the FIRST (legitimate) turn left, not a second mutation.
    let st = executor.cell_state(board.cell()).expect("cell present");
    assert_eq!(
        st.get_field(STATUS_SLOT),
        Some(&fe(RESOLVED)),
        "the stale fire ran no turn"
    );
}

#[test]
fn a_missing_gated_affordance_is_refused_and_an_unknown_cell_fails_closed() {
    let (cclerk, executor, board) = board();
    // A name not on the surface ⇒ NoSuchAffordance (in-band).
    match board.fire_gated_through_executor("nope", &AuthRequired::Either, &cclerk, &executor) {
        Err(FireExecuteError::Gate(FireError::NoSuchAffordance)) => {}
        other => panic!("expected NoSuchAffordance, got {other:?}"),
    }
}
