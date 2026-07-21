//! **The CELLS-AS-SERVICE-OBJECTS proof for tool-access-delegation, end-to-end.**
//!
//! The delegation lifecycle (grant / exercise / delegate / revoke / view) driven through the
//! `invoke()` front door against the real [`EmbeddedExecutor`]. The same guarantees the
//! `bounty-board` / `escrow-market` service exemplars pin, on the mandate's `WriteOnce`
//! scope/rate/deadline + `Monotonic` / `FieldLteField` rate-ceiling program:
//!
//! 1. **The mandate publishes a typed interface** (grant/exercise/delegate/revoke/view with
//!    their auth + replayable-vs-serviced semantics), resolvable as a Service-Explorer would
//!    resolve it (via an [`InterfaceRegistry`]).
//! 2. **An authorized `exercise` commits a real verified turn** — the desugared `SetField`
//!    lands and the meter advances.
//! 3. **The cap-gate bites at the front door** — an unauthorized `exercise` is refused before
//!    any turn is built; nothing is submitted (anti-ghost).
//! 4. **The attenuation CANNOT be amplified** — a delegated N-call mandate gets exactly N
//!    calls: the (N+1)th `exercise` is refused on the commit path by
//!    `FieldLteField(calls_made <= rate_limit)`, and any attempt to RAISE the granted ceiling
//!    is refused by `WriteOnce(rate_limit)` — both EXECUTOR refusals, not userspace checks.
//! 5. **`grant` mints the mandate through the front door**, and `delegate` (the cap-graph
//!    attenuation handoff) builds as a real `GrantCapability`.
//! 6. **A serviced method is the named seam** — `view` refuses to desugar, and an unknown
//!    method does not route.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, Effect, EmbeddedExecutor,
    InterfaceRegistry, InvokeAuthority, InvokeRefused, field_from_u64,
};
use dregg_cell::interface::{Semantics, method_symbol};
use starbridge_tool_access_delegation::service::{
    METHOD_EXERCISE, METHOD_VIEW, MandateService, MandateServiceError, interface_descriptor,
    register_interface, seed_empty_mandate, seed_granted_mandate,
};
use starbridge_tool_access_delegation::{
    CALLS_MADE_SLOT, DEADLINE_SLOT, RATE_LIMIT_SLOT, TOOL_ID_SLOT, tool_id_field,
};

/// A cipherclerk + an embedded executor whose agent cell IS the mandate cell, with the
/// canonical mandate program installed and a granted baseline (tool `search-mcp`, the given
/// `rate`, no expiry at the embedded height).
fn deploy(seed: u8, rate: u64) -> (AppCipherclerk, EmbeddedExecutor, MandateService) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let mandate = cclerk.cell_id();
    seed_granted_mandate(&executor, "search-mcp", rate, 0);
    let service = MandateService::new(mandate);
    (cclerk, executor, service)
}

#[test]
fn the_mandate_publishes_a_resolvable_typed_interface() {
    let (_cclerk, _executor, service) = deploy(0x01, 4);

    let mut registry = InterfaceRegistry::new();
    register_interface(&mut registry, service.cell);
    let resolved = registry
        .get(&service.cell)
        .expect("the interface is registered");

    assert_eq!(resolved.methods.len(), 5);
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_EXERCISE))
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
    let derived = dregg_cell::interface::InterfaceDescriptor::derive_replayable(
        &starbridge_tool_access_delegation::tad_born_cell_program(),
    );
    assert_ne!(
        derived.interface_id, resolved.interface_id,
        "the registered interface carries Signature/Serviced the derived one cannot"
    );
}

#[test]
fn an_authorized_exercise_commits_a_real_turn_and_advances_the_meter() {
    let (cclerk, executor, service) = deploy(0x02, 4);

    let turn = service
        .exercise(
            &cclerk,
            0,
            field_from_u64(0xabc),
            InvokeAuthority::Signature,
        )
        .expect("a Signature holder may build an exercise invocation");
    let receipt = executor
        .submit_turn(&turn)
        .expect("the desugared exercise turn commits through the verified executor");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real receipt");

    // THE LOOP CLOSES: the desugared SetField landed — the meter advanced 0 → 1.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[CALLS_MADE_SLOT as usize],
        field_from_u64(1),
        "the meter advanced to 1"
    );
}

#[test]
fn an_unauthorized_exercise_is_refused_at_the_front_door() {
    let (cclerk, executor, service) = deploy(0x03, 4);

    // The caller holds NO authority; `exercise` requires Signature. Refused before any turn.
    let refused = service
        .exercise(&cclerk, 0, field_from_u64(1), InvokeAuthority::None)
        .expect_err("an unauthorized exercise must be refused");
    assert!(matches!(
        refused,
        MandateServiceError::Refused(InvokeRefused::Unauthorized {
            required: AuthRequired::Signature,
            ..
        })
    ));

    // Nothing was submitted — the meter is untouched (anti-ghost).
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(state.fields[CALLS_MADE_SLOT as usize], field_from_u64(0));
}

#[test]
fn the_delegated_cap_cannot_be_amplified() {
    // ATTENUATION: a mandate granted N=3 calls gets EXACTLY 3 — it cannot exceed its rate
    // (the executor's FieldLteField ceiling) nor raise it (WriteOnce). This is the
    // consumption-budget attenuation: a delegated cap cannot be amplified downstream.
    let (cclerk, executor, service) = deploy(0x04, 3);

    // The three granted exercises commit (meter 0→1→2→3).
    for prev in 0u64..3 {
        let turn = service
            .exercise(
                &cclerk,
                prev,
                field_from_u64(0xabc + prev),
                InvokeAuthority::Signature,
            )
            .expect("the invocation builds");
        executor
            .submit_turn(&turn)
            .unwrap_or_else(|e| panic!("exercise {} must commit: {e:?}", prev + 1));
    }
    assert_eq!(
        executor.cell_state(service.cell).unwrap().fields[CALLS_MADE_SLOT as usize],
        field_from_u64(3),
        "the full granted budget is spent"
    );

    // The fourth exercise overruns the granted rate (4 > 3) — refused on the COMMIT path by
    // FieldLteField(calls_made <= rate_limit), not a userspace check.
    let overrun = service
        .exercise(
            &cclerk,
            3,
            field_from_u64(0xdead),
            InvokeAuthority::Signature,
        )
        .expect("the over-budget exercise invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&overrun);
    assert!(
        rejected.is_err(),
        "the executor must refuse the over-budget exercise"
    );
    let msg = format!("{:?}", rejected.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("lte") || msg.contains("field") || msg.contains("program"),
        "refused on the calls <= rate ceiling, got: {msg}"
    );

    // Nor can the holder RAISE the granted ceiling to forge head-room — WriteOnce(rate_limit)
    // refuses it (the granted authority is frozen, never widened).
    let raise = cclerk.make_action(
        service.cell,
        "exercise",
        vec![Effect::SetField {
            cell: service.cell,
            index: RATE_LIMIT_SLOT as u64,
            value: field_from_u64(100),
        }],
    );
    let raised = executor.submit_action(&cclerk, raise);
    assert!(
        raised.is_err(),
        "raising the granted ceiling must be refused"
    );
    let msg = format!("{:?}", raised.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("writeonce") || msg.contains("write-once") || msg.contains("program"),
        "refused on WriteOnce(rate_limit), got: {msg}"
    );

    // Anti-ghost: the meter still reads 3 — the refused overrun committed nothing.
    assert_eq!(
        executor.cell_state(service.cell).unwrap().fields[CALLS_MADE_SLOT as usize],
        field_from_u64(3),
        "the meter survives the refused overrun"
    );
}

#[test]
fn grant_mints_the_mandate_through_the_front_door() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x05; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    // Born-empty: just the program installed, no grant terms bound yet.
    seed_empty_mandate(&executor);
    let service = MandateService::new(cclerk.cell_id());

    let turn = service
        .grant(&cclerk, "search-mcp", 5, 0, InvokeAuthority::Signature)
        .expect("a Signature holder may grant");
    executor
        .submit_turn(&turn)
        .expect("the grant turn binds scope/rate/deadline from zero (WriteOnce admit)");

    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[TOOL_ID_SLOT as usize],
        tool_id_field("search-mcp")
    );
    assert_eq!(state.fields[RATE_LIMIT_SLOT as usize], field_from_u64(5));
    assert_eq!(state.fields[DEADLINE_SLOT as usize], field_from_u64(0));
    assert_eq!(state.fields[CALLS_MADE_SLOT as usize], field_from_u64(0));
}

#[test]
fn delegate_builds_the_cap_graph_attenuation_handoff() {
    let (cclerk, _executor, service) = deploy(0x06, 4);
    let worker = CellId::from_bytes([0xAA; 32]);

    // `delegate` (the attenuation) builds through the front door — a Signature holder may hand
    // the invoke cap forward. A `None` holder cannot (cap-gated, fail-closed).
    service
        .delegate(&cclerk, worker, InvokeAuthority::Signature)
        .expect("a Signature holder may delegate the invoke cap forward");
    assert!(matches!(
        service.delegate(&cclerk, worker, InvokeAuthority::None),
        Err(MandateServiceError::Refused(
            InvokeRefused::Unauthorized { .. }
        ))
    ));

    // The desugared effect is a GrantCapability to the worker NARROWED at the Signature
    // ceiling — never widened (the `derive_no_amplify` cap-graph shape of attenuation).
    let effect = starbridge_tool_access_delegation::grant_invoke_effect(service.cell, worker);
    match effect {
        Effect::GrantCapability { to, cap, .. } => {
            assert_eq!(to, worker, "the cap is handed to the worker");
            assert_eq!(
                cap.permissions,
                AuthRequired::Signature,
                "the forwarded invoke cap is narrowed at the Signature ceiling, never widened"
            );
        }
        other => panic!("delegate must desugar to GrantCapability, got {other:?}"),
    }
}

#[test]
fn view_is_a_serviced_seam_and_an_unknown_method_does_not_route() {
    let (cclerk, _executor, service) = deploy(0x07, 4);

    // `view` is Serviced — its answer rides the OFE cross-cell-read, never a replay.
    assert!(matches!(
        service.view(&cclerk),
        Err(MandateServiceError::Refused(
            InvokeRefused::ServicedSeam { .. }
        ))
    ));

    // An unknown method does not route against the published interface (fail-closed).
    let iface = interface_descriptor();
    assert!(
        iface.method(&method_symbol("exfiltrate")).is_none(),
        "an unknown method is not a member of the interface"
    );
}
