//! The **interactive-tempo bridge**, end-to-end on the composed deos app — the
//! #169 optimistic-local + verified-at-boundary dial, wired onto affordance fires.
//!
//! `docs/deos/DEOS-APPS.md` (§"the interactive/real-time tempo gap"): dregg's tempo
//! is "commit a verified turn"; live collaboration / games need a faster tempo
//! (frames, optimistic updates). The bridge is **optimistic local interaction +
//! verified turns at trust boundaries.** This test exercises the FULL loop on a
//! composed [`DeosApp`]:
//!
//!   1. **predict** (the interactive tempo) — the cap gate runs NOW, the UI updates
//!      this frame from the predicted effect, NO verified turn yet;
//!   2. **settle** (the trust boundary) — the SAME gated effect runs as a real
//!      verified turn through the embedded executor;
//!   3. **reconcile** — the optimistic frame is `Confirmed` (the verified turn was
//!      accepted; the prediction matched) or `Rolledback` (the boundary rejected it;
//!      the provisional apply is reverted).
//!
//! The load-bearing honesty: **optimistic ≠ unchecked.** The gate is the genuine
//! [`dregg_cell::is_attenuation`] at BOTH predict and settle; an unauthorized fire is
//! refused at predict and never even applies locally. The optimism is only about
//! *when the verified turn is demanded*, never *whether the gate holds*.

use dregg_app_framework::{
    AffordanceSpec, AgentCipherclerk, AppCipherclerk, AppSpec, AuthRequired, CellAffordance,
    CellId, CellSpec, DeosApp, DeosCell, Effect, EmbeddedExecutor, Event, FireError, Settlement,
};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x69; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

/// A live-collaboration whiteboard: `stroke` (anyone authenticated can draw) is the
/// high-tempo move; `clear` (only the owner) is the boundary move. Backed by the
/// agent's own cell so settlement turns execute.
fn whiteboard(cclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    AppSpec::new("whiteboard")
        .cell(
            CellSpec::new("board")
                .affordance(AffordanceSpec::emit("stroke", "either", "stroke"))
                .affordance(AffordanceSpec::emit("clear", "none", "cleared")),
        )
        .into_app(cclerk.clone(), executor.clone())
        .expect("whiteboard spec is valid")
}

#[test]
fn predict_then_settle_confirms_at_the_boundary() {
    let (cclerk, executor) = agent();
    let app = whiteboard(&cclerk, &executor);
    let board = &app.cells()[0];
    let actor = cclerk.cell_id();

    // 1) PREDICT (interactive tempo): a publisher (Either) strokes. The gate passes;
    //    the UI would render the stroke NOW from the predicted effect; no turn yet.
    let fire = board
        .predict_fire("stroke", actor, &AuthRequired::Either)
        .expect("authorized predict");
    assert_eq!(fire.affordance(), "stroke");
    assert_eq!(
        *fire.predicted_effect(),
        dregg_app_framework::EffectSummary::EmitEvent { cell: actor }
    );

    // 2+3) SETTLE at the boundary + RECONCILE: the verified turn executes; the
    //      optimistic frame is Confirmed with the executor's OWN receipt.
    let settlement = fire.settle(board.surface(), &cclerk, &executor);
    assert!(settlement.is_confirmed(), "the verified turn was accepted");
    let receipt = settlement.receipt().expect("confirmed carries a receipt");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real settled turn");
    assert_eq!(receipt.agent, actor);
}

#[test]
fn optimism_is_not_unchecked_an_unauthorized_fire_is_refused_at_predict() {
    let (cclerk, executor) = agent();
    let app = whiteboard(&cclerk, &executor);
    let board = &app.cells()[0];
    let actor = cclerk.cell_id();

    // A publisher (Either) tries to PREDICT `clear` (req None/root): Either ⊄ None →
    // REFUSED at predict by the real gate. The local apply is anti-ghost too — the
    // stroke never even renders, let alone settles. (The type makes settling a refused
    // predict impossible: you cannot settle what you could not predict.)
    let refused = board.predict_fire("clear", actor, &AuthRequired::Either);
    assert!(matches!(refused, Err(FireError::Unauthorized { .. })));

    // The OWNER (root) CAN predict + settle `clear`.
    let owner_fire = board
        .predict_fire("clear", actor, &AuthRequired::None)
        .expect("owner predicts clear");
    assert!(
        owner_fire
            .settle(board.surface(), &cclerk, &executor)
            .is_confirmed()
    );
}

#[test]
fn settle_rolls_back_when_the_boundary_rejects() {
    // The optimistic frame is fast but HONEST: if the verified boundary rejects the
    // turn, the provisional apply must be reverted. Build a board over a cell the
    // embedded ledger does NOT have ⇒ the gate passes (root) but the executor declines
    // the unknown surface cell at settlement.
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x42; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ghost = CellId::from_bytes([0xEE; 32]); // not in the ledger
    let board = DeosCell::new(ghost, "ghost-board").affordance(CellAffordance::new(
        "stroke",
        AuthRequired::None,
        Effect::EmitEvent {
            cell: ghost,
            event: Event {
                topic: [1u8; 32],
                data: vec![],
            },
        },
    ));

    let fire = board
        .predict_fire("stroke", cclerk.cell_id(), &AuthRequired::None)
        .expect("predict passes the gate");
    let settlement = fire.settle(board.surface(), &cclerk, &executor);

    // Not confirmed — the boundary rejected it; the optimistic apply rolls back. The
    // witness-graph recorded nothing.
    assert!(!settlement.is_confirmed());
    assert!(settlement.receipt().is_none());
    match settlement {
        Settlement::Rolledback { reason } => assert!(reason.contains("executor rejected")),
        other => panic!("expected a rollback, got {other:?}"),
    }
}

#[test]
fn many_optimistic_strokes_then_settle_chain_on_the_executors_chain() {
    // The interactive tempo in action: many strokes predicted + settled in sequence;
    // the SETTLED turns chain on the executor's OWN receipt chain (the optimistic
    // frames were correct, the verified truth is the chain).
    let (cclerk, executor) = agent();
    let app = whiteboard(&cclerk, &executor);
    let board = &app.cells()[0];
    let actor = cclerk.cell_id();

    let mut last_hash: Option<[u8; 32]> = None;
    for _ in 0..3 {
        let fire = board
            .predict_fire("stroke", actor, &AuthRequired::Either)
            .expect("predict");
        let settlement = fire.settle(board.surface(), &cclerk, &executor);
        let receipt = settlement.receipt().expect("each stroke settles").clone();
        if let Some(prev) = last_hash {
            assert_ne!(receipt.turn_hash, prev, "each settled turn is distinct");
        }
        last_hash = Some(receipt.turn_hash);
    }
    assert!(last_hash.is_some(), "three strokes settled");
}
