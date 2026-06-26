//! **The CELLS-AS-SERVICE-OBJECTS proof for governed-namespace, end-to-end.**
//!
//! The propose → vote → commit governance lifecycle, driven through the `invoke()`
//! front door against the real [`EmbeddedExecutor`]. The same guarantees the
//! `bounty-board` / `subscription` service exemplars pin, on the namespace's
//! constitutional invariants (the descriptor's own `WriteOnce`
//! committee-root/threshold + `Monotonic` version/dispute-window):
//!
//! 1. **The namespace publishes a typed interface** (propose/vote/commit/register/
//!    view with their auth + replayable-vs-serviced semantics), resolvable as a
//!    Service-Explorer would resolve it (via an [`InterfaceRegistry`]).
//! 2. **The whole lifecycle commits through invoke()** — propose → vote → commit,
//!    each an invoke()-desugared verified turn the executor re-enforces the
//!    constitutional invariants on; the route table swaps and the version advances.
//! 3. **The cap-gate bites at the front door** — an unauthorized `commit`
//!    (`InvokeAuthority::None` vs the method's `Signature`) is refused before any
//!    turn is built; nothing is submitted (anti-ghost).
//! 4. **The verified invariant bites at the executor** — a `commit` that rewinds the
//!    version is refused on the commit path by `Monotonic(VERSION)`, not by a
//!    userspace check.
//! 5. **A serviced method is the named seam** — `view` refuses to desugar (its
//!    answer rides the OFE cross-cell-read), and an unknown method does not route.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, field_from_bytes, field_from_u64,
};
use dregg_cell::interface::{Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use starbridge_governed_namespace::service::{
    GovernanceService, GovernanceServiceError, METHOD_COMMIT, METHOD_VIEW, interface_descriptor,
    register_interface, seed_namespace,
};
use starbridge_governed_namespace::{ROUTE_TABLE_ROOT_SLOT, VERSION_SLOT};

/// A cipherclerk + an embedded executor whose agent cell IS the namespace cell, with
/// the service program (the descriptor's flat invariants) installed and a quiescent
/// genesis at version 1.
fn deploy_namespace(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, GovernanceService) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    seed_namespace(
        &executor,
        3,
        1,
        field_from_bytes(b"genesis-route-table-root"),
    );
    let service = GovernanceService::new(cclerk.cell_id());
    (cclerk, executor, service)
}

#[test]
fn the_namespace_publishes_a_resolvable_typed_interface() {
    let (_cclerk, _executor, service) = deploy_namespace(0x01);

    // The Service Explorer resolves a cell's interface from an InterfaceRegistry an
    // app populated — the richer-than-derived descriptor with real auth/seam.
    let mut registry = InterfaceRegistry::new();
    register_interface(&mut registry, service.cell);
    let resolved = registry
        .get(&service.cell)
        .expect("the interface is registered");

    assert_eq!(resolved.methods.len(), 5);
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_COMMIT))
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

    // The published descriptor carries richer semantics than derive-from-program
    // would (all-Replayable / all-None): the ids differ.
    let derived = dregg_cell::interface::InterfaceDescriptor::derive_replayable(
        &starbridge_governed_namespace::governance_program(),
    );
    assert_ne!(
        derived.interface_id, resolved.interface_id,
        "the registered interface carries Signature/Serviced the derived one cannot"
    );
}

#[test]
fn the_full_lifecycle_runs_through_invoke() {
    let (cclerk, executor, service) = deploy_namespace(0x02);
    let proposed_root = field_from_bytes(b"proposed-route-table-v2");

    // propose → vote → commit, each an invoke()-desugared verified turn the executor
    // re-enforces the constitutional invariants on.
    executor
        .submit_turn(
            &service
                .propose(&cclerk, proposed_root, 10_000, InvokeAuthority::Signature)
                .unwrap(),
        )
        .expect("propose commits");
    executor
        .submit_turn(
            &service
                .vote(&cclerk, 3, proposed_root, 2, InvokeAuthority::Signature)
                .unwrap(),
        )
        .expect("vote commits");
    executor
        .submit_turn(
            &service
                .commit(&cclerk, proposed_root, 2, InvokeAuthority::Signature)
                .unwrap(),
        )
        .expect("commit commits");

    // THE LOOP CLOSES: the desugared SetFields landed — the route table swapped and
    // the version advanced 1 → 2.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[ROUTE_TABLE_ROOT_SLOT as usize], proposed_root,
        "the route table swapped to the proposed root"
    );
    assert_eq!(
        state.fields[VERSION_SLOT as usize],
        field_from_u64(2),
        "the route-table generation advanced to 2"
    );
}

#[test]
fn an_unauthorized_commit_is_refused_at_the_front_door() {
    let (cclerk, executor, service) = deploy_namespace(0x03);

    // The caller holds NO authority; `commit` requires Signature. Refused before any
    // turn is built (fail-closed at the userspace front door).
    let refused = service
        .commit(
            &cclerk,
            field_from_bytes(b"sneaky-table"),
            2,
            InvokeAuthority::None,
        )
        .expect_err("an unauthorized commit must be refused");
    assert!(matches!(
        refused,
        GovernanceServiceError::Refused(InvokeRefused::Unauthorized {
            required: AuthRequired::Signature,
            ..
        })
    ));

    // Nothing was submitted — the route table is untouched (anti-ghost).
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(
        state.fields[ROUTE_TABLE_ROOT_SLOT as usize],
        field_from_bytes(b"genesis-route-table-root")
    );
}

#[test]
fn a_version_rewind_commit_is_refused_by_the_executor_not_userspace() {
    let (cclerk, executor, service) = deploy_namespace(0x04);

    // First commit: advance version 1 → 2.
    executor
        .submit_turn(
            &service
                .commit(
                    &cclerk,
                    field_from_bytes(b"table-v2"),
                    2,
                    InvokeAuthority::Signature,
                )
                .unwrap(),
        )
        .expect("the first commit advances the version");

    // A Signature-authorized commit that REWINDS the version to 1: the front door
    // passes (auth + routing OK), but the EXECUTOR refuses on the verified
    // `Monotonic(VERSION)` invariant — the protocol layer, not a userspace check.
    let rewind = service
        .commit(
            &cclerk,
            field_from_bytes(b"table-rollback"),
            1,
            InvokeAuthority::Signature,
        )
        .expect("the rewind commit invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&rewind);
    assert!(
        rejected.is_err(),
        "the executor must refuse a version-rewinding commit"
    );
    let msg = format!("{:?}", rejected.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program"),
        "refused on the Monotonic(VERSION) invariant, got: {msg}"
    );

    // Anti-ghost: the version is still 2; the rewind committed nothing.
    let state = executor.cell_state(service.cell).unwrap();
    assert_eq!(state.fields[VERSION_SLOT as usize], field_from_u64(2));
}

#[test]
fn view_is_a_serviced_seam_and_an_unknown_method_does_not_route() {
    let (cclerk, _executor, service) = deploy_namespace(0x05);

    // `view` is Serviced — its answer rides the OFE cross-cell-read, never a replay.
    assert!(matches!(
        service.view(&cclerk),
        Err(GovernanceServiceError::Refused(
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
