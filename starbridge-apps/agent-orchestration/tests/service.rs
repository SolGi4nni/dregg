//! **The CELLS-AS-SERVICE-OBJECTS proof for agent-orchestration, end-to-end.**
//!
//! The durable+auditable coordinator board lifecycle, driven through the `invoke()` front
//! door against the real [`EmbeddedExecutor`]. The same guarantees the
//! `bounty-board`/`swarm-orchestration` service exemplars pin, on the orchestration's
//! `AffineLe(spent_a + spent_b <= budget)` + `StrictMonotonic(EPOCH)` +
//! `Monotonic(SPENT_*)` policy program:
//!
//! 1. **The board publishes a typed interface** (open_board/worker_step/delegate_mandate/
//!    view with their auth + replayable-vs-serviced semantics), resolvable as a
//!    Service-Explorer would resolve it (via an [`InterfaceRegistry`]).
//! 2. **An authorized `worker_step` commits a real verified turn** — the desugared
//!    `SetField`s land on the ledger and a worker meter + the epoch advance.
//! 3. **The cap-gate bites at the front door** — an unauthorized `worker_step`
//!    (`InvokeAuthority::None` vs the method's `Signature`) is refused before any turn is
//!    built; nothing is submitted (anti-ghost).
//! 4. **The verified invariant bites at the executor** — an over-budget `worker_step` is
//!    refused on the commit path by `AffineLe(spent_a + spent_b <= budget)`, not by a
//!    userspace check.
//! 5. **A serviced method is the named seam** — `view` refuses to desugar (its answer
//!    rides the OFE cross-cell-read), and an unknown method does not route.
//!
//! Run `--release` (the embedded executor is slow in debug).

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, field_from_u64,
};
use dregg_cell::interface::{Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use starbridge_agent_orchestration::service::{
    BoardService, BoardServiceError, METHOD_VIEW, METHOD_WORKER_STEP, interface_descriptor,
    register_interface,
};
use starbridge_agent_orchestration::{
    EPOCH_SLOT, SPENT_A_SLOT, Tool, WorkerSlot, coordinator_program, seed_board,
};

/// A cipherclerk + an embedded executor whose agent cell IS the board cell, with the
/// canonical coordinator program installed and an OPEN/epoch-1 genesis state.
fn deploy_board(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, BoardService) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let board = cclerk.cell_id();
    // Installs `coordinator_program()` (AffineLe budget + WriteOnce lead/budget + Monotonic
    // meters + StrictMonotonic epoch) and opens the board at epoch 1 — the same program the
    // factory bakes, so the invoke()-desugared turns are re-enforced identically.
    seed_board(&executor, 1000, "lead");
    let service = BoardService::new(board);
    (cclerk, executor, service)
}

#[test]
fn the_board_publishes_a_resolvable_typed_interface() {
    let (_cclerk, _executor, service) = deploy_board(0x01);

    // The Service Explorer resolves a cell's interface from an InterfaceRegistry an app
    // populated — the richer-than-derived descriptor with real auth/seam.
    let mut registry = InterfaceRegistry::new();
    register_interface(&mut registry, service.cell);
    let resolved = registry
        .get(&service.cell)
        .expect("the interface is registered");

    assert_eq!(resolved.methods.len(), 4);
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_WORKER_STEP))
            .unwrap()
            .auth_required,
        AuthRequired::Signature,
    );
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_VIEW))
            .unwrap()
            .semantics,
        Semantics::Serviced,
    );

    // The published descriptor carries richer semantics than derive-from-program would
    // (all-Replayable / all-None): the ids differ.
    let derived =
        dregg_cell::interface::InterfaceDescriptor::derive_replayable(&coordinator_program());
    assert_ne!(
        derived.interface_id, resolved.interface_id,
        "the registered interface carries Signature/Serviced the derived one cannot"
    );
}

#[test]
fn an_authorized_worker_step_commits_a_real_turn_and_advances_the_swarm() {
    let (cclerk, executor, service) = deploy_board(0x02);

    // a 300-cost step to worker A: meter 0 -> 300, epoch 1 -> 2.
    let turn = service
        .worker_step(
            &cclerk,
            WorkerSlot::A,
            Tool::Search,
            300,
            300,
            2,
            "index",
            InvokeAuthority::Signature,
        )
        .expect("a Signature holder may build a worker_step invocation");
    let receipt = executor
        .submit_turn(&turn)
        .expect("the desugared worker_step turn commits through the verified executor");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real receipt");

    // THE LOOP CLOSES: the desugared SetFields landed — worker A's meter advanced and the
    // epoch advanced.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[SPENT_A_SLOT as usize],
        field_from_u64(300),
        "worker A's meter advanced to 300"
    );
    assert_eq!(
        state.fields[EPOCH_SLOT as usize],
        field_from_u64(2),
        "the step strictly advanced the epoch"
    );
}

#[test]
fn an_unauthorized_worker_step_is_refused_at_the_front_door() {
    let (cclerk, executor, service) = deploy_board(0x03);

    // The caller holds NO authority; `worker_step` requires Signature. Refused before any
    // turn is built (fail-closed at the userspace front door).
    let refused = service
        .worker_step(
            &cclerk,
            WorkerSlot::A,
            Tool::Search,
            300,
            300,
            2,
            "index",
            InvokeAuthority::None,
        )
        .expect_err("an unauthorized worker_step must be refused");
    assert!(matches!(
        refused,
        BoardServiceError::Refused(InvokeRefused::Unauthorized {
            required: AuthRequired::Signature,
            ..
        })
    ));

    // Nothing was submitted — the board is untouched (anti-ghost): meter still 0.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(state.fields[SPENT_A_SLOT as usize], field_from_u64(0));
}

#[test]
fn an_over_budget_worker_step_is_refused_by_the_executor_not_userspace() {
    let (cclerk, executor, service) = deploy_board(0x04);

    // A Signature-authorized but over-budget step: the front door passes (auth + routing
    // OK), but the EXECUTOR refuses on the verified
    // AffineLe(spent_a + spent_b <= budget) gate — the protocol layer, not a userspace
    // check. cost 1001 > budget 1000.
    let runaway = service
        .worker_step(
            &cclerk,
            WorkerSlot::A,
            Tool::Spend,
            1001,
            1001,
            2,
            "runaway",
            InvokeAuthority::Signature,
        )
        .expect("the over-budget worker_step invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&runaway);
    assert!(
        rejected.is_err(),
        "the executor must refuse an over-budget worker_step"
    );

    // Anti-ghost: the meter is untouched; the runaway committed nothing.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[SPENT_A_SLOT as usize],
        field_from_u64(0),
        "the over-budget worker_step committed nothing"
    );
}

#[test]
fn the_two_meter_lifecycle_runs_through_invoke() {
    let (cclerk, executor, service) = deploy_board(0x05);

    // step 600 to A (epoch 1 -> 2), then 300 to B (epoch 2 -> 3): 900 <= 1000 fits.
    executor
        .submit_turn(
            &service
                .worker_step(
                    &cclerk,
                    WorkerSlot::A,
                    Tool::Search,
                    600,
                    600,
                    2,
                    "task-a",
                    InvokeAuthority::Signature,
                )
                .unwrap(),
        )
        .expect("A step commits");
    executor
        .submit_turn(
            &service
                .worker_step(
                    &cclerk,
                    WorkerSlot::B,
                    Tool::Read,
                    300,
                    300,
                    3,
                    "task-b",
                    InvokeAuthority::Signature,
                )
                .unwrap(),
        )
        .expect("B step commits (900 <= 1000)");

    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(state.fields[EPOCH_SLOT as usize], field_from_u64(3));

    // A third step that breaches the budget (A 600 + B 300 + 200 = 1100 > 1000) is an
    // executor refusal on the AffineLe gate.
    let breach = executor.submit_turn(
        &service
            .worker_step(
                &cclerk,
                WorkerSlot::A,
                Tool::Summarize,
                800,
                200,
                4,
                "task-a2",
                InvokeAuthority::Signature,
            )
            .unwrap(),
    );
    assert!(breach.is_err(), "a budget-breaching worker_step is refused");
}

#[test]
fn view_is_a_serviced_seam_and_an_unknown_method_does_not_route() {
    let (cclerk, _executor, service) = deploy_board(0x06);

    // `view` is Serviced — its answer rides the OFE cross-cell-read, never a replay.
    assert!(matches!(
        service.view(&cclerk),
        Err(BoardServiceError::Refused(
            InvokeRefused::ServicedSeam { .. }
        ))
    ));

    // An unknown method does not route against the published interface (fail-closed).
    let iface = interface_descriptor();
    assert!(
        iface.method(&method_symbol("frobnicate")).is_none(),
        "an unknown method is not a member of the interface"
    );
}
