//! **The CELLS-AS-SERVICE-OBJECTS proof for compartment-workflow-mandate,
//! end-to-end.**
//!
//! The canonical 3-step charter DAG (review → redact → sign), driven through the
//! `invoke()` front door against the real [`EmbeddedExecutor`]. The same guarantees
//! the `bounty-board`/`kvstore` service exemplars pin, on the mandate's
//! `MonotonicSequence(STEP_CURSOR)` + root-bound `ClearanceDominates` program:
//!
//! 1. **The mandate publishes a typed interface** (`advance_step` Signature-gated +
//!    `view` Serviced), resolvable as a Service-Explorer would resolve it (via an
//!    [`InterfaceRegistry`]).
//! 2. **An authorized officer `advance_step` commits a real verified turn** — the
//!    desugared `SetField`s land on the ledger and the charter cursor advances 0 → 1.
//! 3. **The verified clearance tooth bites at the executor** — a clerk advancing
//!    past `review` (to `redact`) is refused on the commit path by the root-bound
//!    `ClearanceDominates`, not by a userspace check (the clerk does not dominate
//!    `redact`).
//! 4. **The cap-gate bites at the front door** — an unauthorized `advance_step`
//!    (`InvokeAuthority::None` vs the method's `Signature`) is refused before any
//!    turn is built; nothing is submitted (anti-ghost).
//! 5. **A serviced method is the named seam** — `view` refuses to desugar (its
//!    answer rides the OFE cross-cell-read), and an unknown method does not route.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, field_from_u64,
};
use dregg_cell::interface::{Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use starbridge_compartment_workflow_mandate::service::{
    METHOD_ADVANCE_STEP, METHOD_VIEW, WorkflowService, WorkflowServiceError, interface_descriptor,
    register_interface,
};
use starbridge_compartment_workflow_mandate::{
    DEFAULT_CHARTER_STEPS, DEFAULT_COMMITMENT_ANCHOR, DEFAULT_STEP_SPEND_POLICY, STEP_CURSOR_SLOT,
    WorkflowPhase, charter_clearance_root, clerk_label, officer_label, seed_workflow,
};

/// A cipherclerk + an embedded executor whose agent cell IS the mandate cell, with
/// the canonical workflow program installed at cursor 0 (charter terminal 3, the
/// REAL clearance-graph root).
fn deploy(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, WorkflowService) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let cell = cclerk.cell_id();
    seed_workflow(
        &executor,
        DEFAULT_COMMITMENT_ANCHOR,
        DEFAULT_CHARTER_STEPS,
        charter_clearance_root(),
        DEFAULT_STEP_SPEND_POLICY,
    );
    let service = WorkflowService::new(cell);
    (cclerk, executor, service)
}

#[test]
fn the_mandate_publishes_a_resolvable_typed_interface() {
    let (_cclerk, _executor, service) = deploy(0x01);

    // The Service Explorer resolves a cell's interface from an InterfaceRegistry an
    // app populated — the richer-than-derived descriptor with real auth/seam.
    let mut registry = InterfaceRegistry::new();
    register_interface(&mut registry, service.cell);
    let resolved = registry
        .get(&service.cell)
        .expect("the interface is registered");

    assert_eq!(resolved.methods.len(), 2);
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_ADVANCE_STEP))
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
}

#[test]
fn an_authorized_officer_advance_commits_a_real_turn_and_advances_the_cursor() {
    let (cclerk, executor, service) = deploy(0x02);

    // An officer advances step 0 (review): cursor 0 -> 1, presenting officer
    // clearance so the executor's root-bound ClearanceDominates admits.
    let turn = service
        .advance_step(
            &cclerk,
            0,
            officer_label(),
            WorkflowPhase::Review,
            InvokeAuthority::Signature,
        )
        .expect("a Signature holder may build an advance invocation");
    let receipt = executor
        .submit_turn(&turn)
        .expect("the desugared advance turn commits through the verified executor");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real receipt");

    // THE LOOP CLOSES: the desugared SetFields landed — the charter cursor advanced.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[STEP_CURSOR_SLOT as usize],
        field_from_u64(1),
        "the charter cursor advanced 0 -> 1"
    );
}

#[test]
fn a_clerk_advancing_past_review_is_refused_by_the_executor_not_userspace() {
    let (cclerk, executor, service) = deploy(0x03);

    // First step: an officer advances review (0 -> 1).
    let t1 = service
        .advance_step(
            &cclerk,
            0,
            officer_label(),
            WorkflowPhase::Review,
            InvokeAuthority::Signature,
        )
        .unwrap();
    executor
        .submit_turn(&t1)
        .expect("the review advance commits");

    // A Signature-authorized clerk advancing to `redact` (1 -> 2): the front door
    // passes (auth + routing OK), but the EXECUTOR refuses on the root-bound
    // ClearanceDominates — a clerk does not dominate `redact` in the charter graph.
    // The protocol layer, not a userspace check.
    let steal = service
        .advance_step(
            &cclerk,
            1,
            clerk_label(),
            WorkflowPhase::Redact,
            InvokeAuthority::Signature,
        )
        .expect("the clerk advance invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&steal);
    assert!(
        rejected.is_err(),
        "the executor must refuse a clerk advancing past review"
    );
    let msg = format!("{:?}", rejected.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("dominate") || msg.contains("clearance") || msg.contains("program"),
        "refused on the root-bound ClearanceDominates tooth, got: {msg}"
    );

    // Anti-ghost: the cursor still holds 1 (the refused clerk-redact committed nothing).
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[STEP_CURSOR_SLOT as usize],
        field_from_u64(1),
        "the cursor still holds 1"
    );

    // ...whereas an OFFICER advancing the SAME step (1 -> 2) IS admitted: the same
    // live cursor, the same step, but a dominating clearance. Both polarities.
    let officer_step = service
        .advance_step(
            &cclerk,
            1,
            officer_label(),
            WorkflowPhase::Redact,
            InvokeAuthority::Signature,
        )
        .unwrap();
    executor
        .submit_turn(&officer_step)
        .expect("an officer clears redact: admitted");
    assert_eq!(
        executor.cell_state(service.cell).unwrap().fields[STEP_CURSOR_SLOT as usize],
        field_from_u64(2),
        "the officer's redact advance committed (1 -> 2)"
    );
}

#[test]
fn an_unauthorized_advance_is_refused_at_the_front_door() {
    let (cclerk, executor, service) = deploy(0x04);

    // The caller holds NO authority; `advance_step` requires Signature. Refused
    // before any turn is built (fail-closed at the userspace front door).
    let refused = service
        .advance_step(
            &cclerk,
            0,
            officer_label(),
            WorkflowPhase::Review,
            InvokeAuthority::None,
        )
        .expect_err("an unauthorized advance must be refused");
    assert!(matches!(
        refused,
        WorkflowServiceError::Refused(InvokeRefused::Unauthorized {
            required: AuthRequired::Signature,
            ..
        })
    ));

    // Nothing was submitted — the charter is untouched (anti-ghost).
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(state.fields[STEP_CURSOR_SLOT as usize], field_from_u64(0));
}

#[test]
fn view_is_a_serviced_seam_and_an_unknown_method_does_not_route() {
    let (cclerk, _executor, service) = deploy(0x05);

    // `view` is Serviced — its answer rides the OFE cross-cell-read, never a replay.
    assert!(matches!(
        service.view(&cclerk),
        Err(WorkflowServiceError::Refused(
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
