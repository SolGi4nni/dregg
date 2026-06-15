//! Pre-submission assurance for the orchestration plan — "lint your plan before you spend gas."
//!
//! Before the coordinator drives the orchestration, the delegation/step forest is run through the
//! userspace `dregg_userspace_verify::analyze()` toolkit — conservation (the value moves net to zero
//! per asset), non-amplification (no in-forest grant exceeds a delegated cap), and well-formedness —
//! so a stranger can pre-flight the orchestration's plan and SEE it pass before submitting any turn.
//! The userspace twin of the verified executor's gates.

use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, CellId};
use dregg_turn::forest::{CallForest, CallTree};
use dregg_userspace_verify::analyze;
use starbridge_agent_orchestration::{
    Tool, WorkerSlot, build_open_board_action, build_worker_step_action,
};

fn cclerk() -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [0x5au8; 32])
}
fn board_cell() -> CellId {
    CellId::from_bytes([7u8; 32])
}

fn forest(actions: Vec<dregg_turn::action::Action>) -> CallForest {
    CallForest {
        roots: actions.into_iter().map(CallTree::new).collect(),
        forest_hash: [0u8; 32],
    }
}

/// THE ORCHESTRATION PLAN PASSES THE PRE-FLIGHT. The honest open-board + worker-step forest is
/// conserving (the steps are `SetField` meters + `EmitEvent` records — no value moves),
/// non-amplifying (no grants), and well-formed (real signatures, non-empty actions). `analyze()`
/// returns a clean verdict — the stranger sees GREEN before spending gas.
#[test]
fn the_honest_orchestration_plan_passes_userspace_verify() {
    let c = cclerk();
    let board = board_cell();
    let plan = forest(vec![
        build_open_board_action(&c, board, "lead-pk", 1000),
        build_worker_step_action(&c, board, WorkerSlot::A, Tool::Search, 0, 250, 2, "search"),
        build_worker_step_action(&c, board, WorkerSlot::A, Tool::Summarize, 250, 200, 3, "summarize"),
        build_worker_step_action(&c, board, WorkerSlot::B, Tool::Read, 0, 150, 4, "fact-check"),
    ]);

    let assurance = analyze(&plan, false);
    assert!(
        assurance.pass(),
        "the honest orchestration plan must pass every static check; findings: {:?}",
        assurance.all_findings()
    );
    assert!(assurance.conservation.is_pass(), "no value moves ⇒ conserves");
    assert!(
        assurance.no_amplification.is_pass(),
        "no grants ⇒ no amplification"
    );
    assert!(
        assurance.wellformed.is_pass(),
        "real signatures, non-empty actions"
    );
}
