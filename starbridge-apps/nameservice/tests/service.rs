//! **The CELLS-AS-SERVICE-OBJECTS proof for the nameservice, end-to-end.**
//!
//! Declares the name-registry service cell, drives its methods through the
//! `invoke()` front door, and submits the desugared turns through the real
//! [`EmbeddedExecutor`]. The properties pinned here (the second worked citizen of
//! the pattern, after `starbridge-kvstore`):
//!
//! 1. **The registry publishes a typed interface** (register/release/resolve with
//!    their auth + replayable-vs-serviced semantics), resolvable as a
//!    Service-Explorer would resolve it (via an [`InterfaceRegistry`]).
//! 2. **An authorized `register` commits a real verified turn** — the desugared
//!    `SetField`s land on the per-cell heap: the `name → cell` binding appears at
//!    `name_slot(name)` and the registry version bumps.
//! 3. **The cap-gate bites at the front door** — an unauthorized `register`
//!    (`InvokeAuthority::None` vs the method's `Signature`) is refused before any
//!    turn is built; nothing is submitted (anti-ghost).
//! 4. **`resolve` is the named seam** — it refuses to desugar (its answer rides
//!    the OFE cross-cell-read = the committed binding), and an unknown method does
//!    not route (fail-closed).
//! 5. **`release` clears the binding** and bumps the version.
//! 6. **The interface is witnessably inspectable** — a route-membership witness
//!    proves `register` is a member of the committed interface.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, field_from_u64, resolve_against,
};
use dregg_cell::interface::{Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_types::CellId;
use starbridge_nameservice::service::{
    METHOD_REGISTER, METHOD_RELEASE, METHOD_RESOLVE, NameError, NameService, VERSION_SLOT,
    interface_descriptor, name_slot, register_interface, registry_program, target_felt,
};

/// A cipherclerk + an embedded executor whose agent cell IS the registry cell,
/// with the registry program installed.
fn deploy_registry(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, NameService) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let registry_cell = cclerk.cell_id();
    executor.install_program(registry_cell, registry_program());
    let svc = NameService::new(registry_cell);
    (cclerk, executor, svc)
}

/// A distinct, deterministic target cell-id to bind a name to.
fn a_target_cell(seed: u8) -> CellId {
    CellId([seed; 32])
}

#[test]
fn the_registry_publishes_a_resolvable_typed_interface() {
    let (_cclerk, _executor, svc) = deploy_registry(0x01);

    // The Service Explorer resolves a cell's interface from an InterfaceRegistry
    // an app populated — the richer-than-derived descriptor with real auth/seam.
    let mut registry = InterfaceRegistry::new();
    register_interface(&mut registry, svc.cell);
    let resolved = registry
        .get(&svc.cell)
        .expect("the interface is registered");

    assert_eq!(resolved.methods.len(), 3);
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_REGISTER))
            .unwrap()
            .auth_required,
        AuthRequired::Signature,
    );
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_RESOLVE))
            .unwrap()
            .semantics,
        Semantics::Serviced,
    );
    // The published descriptor carries richer semantics than derive-from-program
    // would (which is all-Replayable / all-None): the ids differ.
    let derived =
        dregg_cell::interface::InterfaceDescriptor::derive_replayable(&registry_program());
    assert_ne!(
        derived.interface_id, resolved.interface_id,
        "the registered interface carries Signature/Serviced the derived one cannot"
    );
}

#[test]
fn an_authorized_register_commits_a_real_turn_and_binds_the_name() {
    let (cclerk, executor, svc) = deploy_registry(0x02);

    let target = a_target_cell(0x99);
    let turn = svc
        .register(&cclerk, "alice", target, 1, InvokeAuthority::Signature)
        .expect("a Signature holder may build a register invocation");
    let receipt = executor
        .submit_turn(&turn)
        .expect("the desugared register turn commits through the verified executor");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real receipt");

    // THE LOOP CLOSES: the desugared SetFields landed on the per-cell heap — the
    // name → cell binding appears at name_slot("alice") and the version bumped.
    let state = executor.cell_state(svc.cell).unwrap();
    assert_eq!(
        state.fields[name_slot("alice")],
        target_felt(target),
        "the heap holds the name → cell binding"
    );
    assert_eq!(
        state.fields[VERSION_SLOT],
        field_from_u64(1),
        "the registry version bumped to 1"
    );

    // A second name → cell, version 2 — Monotonic permits the forward bump.
    let target2 = a_target_cell(0x42);
    let turn2 = svc
        .register(&cclerk, "bob", target2, 2, InvokeAuthority::Signature)
        .unwrap();
    executor
        .submit_turn(&turn2)
        .expect("forward version bump commits");
    let state = executor.cell_state(svc.cell).unwrap();
    assert_eq!(state.fields[name_slot("bob")], target_felt(target2));
    assert_eq!(state.fields[VERSION_SLOT], field_from_u64(2));
}

#[test]
fn an_unauthorized_register_is_refused_at_the_front_door() {
    let (cclerk, executor, svc) = deploy_registry(0x03);

    // The caller holds NO authority; `register` requires Signature. Refused before
    // any turn is built (fail-closed at the userspace front door).
    let refused = svc
        .register(
            &cclerk,
            "carol",
            a_target_cell(0x07),
            1,
            InvokeAuthority::None,
        )
        .expect_err("an unauthorized register must be refused");
    assert!(matches!(
        refused,
        NameError::Refused(InvokeRefused::Unauthorized {
            required: AuthRequired::Signature,
            ..
        })
    ));

    // Nothing was submitted — the heap is untouched (anti-ghost).
    let state = executor.cell_state(svc.cell).unwrap();
    assert_eq!(state.fields[name_slot("carol")], [0u8; 32]);
    assert_eq!(state.fields[VERSION_SLOT], [0u8; 32]);
}

#[test]
fn a_version_rollback_is_refused_by_the_executor_not_userspace() {
    let (cclerk, executor, svc) = deploy_registry(0x04);

    // Establish version 2.
    let t1 = svc
        .register(
            &cclerk,
            "alice",
            a_target_cell(0x01),
            2,
            InvokeAuthority::Signature,
        )
        .unwrap();
    executor.submit_turn(&t1).expect("version -> 2 commits");

    // A Signature-authorized register that would roll the version BACK to 1: the
    // front door passes (auth + routing OK), but the EXECUTOR refuses on the
    // verified Monotonic(VERSION) invariant — the protocol layer, not a userspace
    // check.
    let rollback = svc
        .register(
            &cclerk,
            "bob",
            a_target_cell(0x02),
            1,
            InvokeAuthority::Signature,
        )
        .expect("the rollback invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&rollback);
    assert!(
        rejected.is_err(),
        "the executor must refuse a version rollback"
    );
    let msg = format!("{:?}", rejected.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program") || msg.contains("field[0]"),
        "refused on the Monotonic(VERSION) caveat, got: {msg}"
    );

    // Anti-ghost: the rejected turn committed nothing.
    let state = executor.cell_state(svc.cell).unwrap();
    assert_eq!(
        state.fields[name_slot("bob")],
        [0u8; 32],
        "the rollback wrote nothing"
    );
    assert_eq!(
        state.fields[VERSION_SLOT],
        field_from_u64(2),
        "version held at 2"
    );
}

#[test]
fn release_clears_the_binding_and_bumps_the_version() {
    let (cclerk, executor, svc) = deploy_registry(0x05);

    let target = a_target_cell(0x33);
    let t1 = svc
        .register(&cclerk, "alice", target, 1, InvokeAuthority::Signature)
        .unwrap();
    executor.submit_turn(&t1).expect("register commits");
    let state = executor.cell_state(svc.cell).unwrap();
    assert_eq!(state.fields[name_slot("alice")], target_felt(target));

    let rel = svc
        .release(&cclerk, "alice", 2, InvokeAuthority::Signature)
        .expect("a Signature holder may release");
    executor.submit_turn(&rel).expect("release commits");

    let state = executor.cell_state(svc.cell).unwrap();
    assert_eq!(
        state.fields[name_slot("alice")],
        [0u8; 32],
        "the binding was cleared"
    );
    assert_eq!(
        state.fields[VERSION_SLOT],
        field_from_u64(2),
        "version bumped"
    );
}

#[test]
fn resolve_is_the_named_serviced_seam_and_unknown_methods_fail_closed() {
    let (cclerk, _executor, svc) = deploy_registry(0x06);

    // `resolve` is Serviced — its answer rides the OFE cross-cell-read (the
    // committed binding), not a replay. invoke() refuses to desugar it (the seam).
    let seam = svc
        .resolve(&cclerk, "alice")
        .expect_err("resolve is a serviced seam");
    assert!(matches!(
        seam,
        NameError::Refused(InvokeRefused::ServicedSeam { .. })
    ));

    // An unknown method does not route through the verified DFA — fail-closed.
    let unknown = resolve_against(
        svc.cell,
        &interface_descriptor(),
        "frobnicate",
        vec![],
        vec![],
        InvokeAuthority::Signature,
    )
    .expect_err("an unknown method does not route");
    assert!(matches!(unknown, InvokeRefused::UnknownMethod { .. }));
}

#[test]
fn the_interface_is_witnessably_inspectable() {
    let svc = NameService::new(AppCipherclerk::new(AgentCipherclerk::new(), [0x07; 32]).cell_id());
    let iface = &svc.descriptor;

    // Every published method routes through the verified DFA router (the same path
    // the Service Explorer uses to discover invokable methods).
    for m in [METHOD_REGISTER, METHOD_RELEASE, METHOD_RESOLVE] {
        assert!(
            iface.route_method(&method_symbol(m)).is_some(),
            "{m} routes"
        );
    }

    // A route-membership witness PROVES `register` is a member of the committed
    // interface (via the existing dfa AIR) — and does not verify for a method it
    // was not minted for.
    let reg = method_symbol(METHOD_REGISTER);
    let (proof, root) = iface
        .route_membership_witness(&reg)
        .expect("a declared method has a membership witness");
    assert_eq!(root, iface.to_route_table().commitment);
    assert!(iface.verify_route_membership(&reg, &proof));
    assert!(!iface.verify_route_membership(&method_symbol(METHOD_RESOLVE), &proof));
}
