//! **The CELLS-AS-SERVICE-OBJECTS proof, end-to-end.**
//!
//! Declares the key-value store service cell, drives its methods through the
//! `invoke()` front door, and submits the desugared turns through the real
//! [`EmbeddedExecutor`]. The properties pinned here:
//!
//! 1. **The store publishes a typed interface** (put/delete/get with their
//!    auth + replayable-vs-serviced semantics), resolvable as a Service-Explorer
//!    would resolve it (via an [`InterfaceRegistry`]).
//! 2. **An authorized `put`/`delete` commits a real verified turn** — the
//!    desugared `SetField`s land on the ledger and the store version bumps.
//! 3. **The cap-gate bites at the front door** — an unauthorized `put`
//!    (`InvokeAuthority::None` vs the method's `Signature`) is refused before any
//!    turn is built; nothing is submitted.
//! 4. **The verified invariant bites at the executor** — a `put` that would roll
//!    the store version BACK is refused on the commit path by
//!    `StateConstraint::Monotonic`, not by a userspace check (anti-ghost: it
//!    commits nothing).
//! 5. **A serviced method is the named seam** — `get` refuses to desugar (its
//!    answer rides the OFE cross-cell-read), and an unknown method does not
//!    route (fail-closed).
//! 6. **The interface is witnessably inspectable** — a route-membership witness
//!    proves `put` is a member of the committed interface (the same DFA AIR the
//!    Service Explorer's route check uses).

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, field_from_u64, resolve_against,
};
use dregg_cell::interface::{Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use starbridge_kvstore::{
    KvError, KvStore, LAST_KEY_SLOT, LAST_VALUE_SLOT, METHOD_DELETE, METHOD_GET, METHOD_PUT,
    REG_MIN, VERSION_SLOT, interface_descriptor, register_interface, store_program,
};

/// A cipherclerk + an embedded executor whose agent cell IS the store cell,
/// with the store program installed.
fn deploy_store(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, KvStore) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let store_cell = cclerk.cell_id();
    executor.install_program(store_cell, store_program());
    let store = KvStore::new(store_cell);
    (cclerk, executor, store)
}

#[test]
fn the_store_publishes_a_resolvable_typed_interface() {
    let (_cclerk, _executor, store) = deploy_store(0x01);

    // The Service Explorer resolves a cell's interface from an InterfaceRegistry
    // an app populated — the richer-than-derived descriptor with real auth/seam.
    let mut registry = InterfaceRegistry::new();
    register_interface(&mut registry, store.cell);
    let resolved = registry
        .get(&store.cell)
        .expect("the interface is registered");

    assert_eq!(resolved.methods.len(), 3);
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_PUT))
            .unwrap()
            .auth_required,
        AuthRequired::Signature,
    );
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_GET))
            .unwrap()
            .semantics,
        Semantics::Serviced,
    );
    // The published descriptor carries richer semantics than derive-from-program
    // would (which is all-Replayable / all-None): the ids differ.
    let derived = dregg_cell::interface::InterfaceDescriptor::derive_replayable(&store_program());
    assert_ne!(
        derived.interface_id, resolved.interface_id,
        "the registered interface carries Signature/Serviced the derived one cannot"
    );
}

#[test]
fn an_authorized_put_commits_a_real_turn_and_bumps_the_version() {
    let (cclerk, executor, store) = deploy_store(0x02);

    let value = [9u8; 32];
    let turn = store
        .put(&cclerk, REG_MIN, value, 1, InvokeAuthority::Signature)
        .expect("a Signature holder may build a put invocation");
    let receipt = executor
        .submit_turn(&turn)
        .expect("the desugared put turn commits through the verified executor");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real receipt");

    // THE LOOP CLOSES: the desugared SetFields landed — the register holds the
    // value and the store version bumped to 1.
    let state = executor.cell_state(store.cell).unwrap();
    assert_eq!(
        state.fields[REG_MIN], value,
        "the register holds the put value"
    );
    assert_eq!(
        state.fields[VERSION_SLOT],
        field_from_u64(1),
        "the store version bumped to 1"
    );
    // The header signals: the front-door put records the last key + value it wrote.
    assert_eq!(
        state.fields[LAST_KEY_SLOT],
        field_from_u64(REG_MIN as u64),
        "the last-key header names the register written"
    );
    assert_eq!(
        state.fields[LAST_VALUE_SLOT], value,
        "the last-value header holds the put value"
    );

    // A second put to a different register, version 2 — Monotonic permits the
    // forward bump.
    let turn2 = store
        .put(
            &cclerk,
            REG_MIN + 1,
            [7u8; 32],
            2,
            InvokeAuthority::Signature,
        )
        .unwrap();
    executor
        .submit_turn(&turn2)
        .expect("forward version bump commits");
    let state = executor.cell_state(store.cell).unwrap();
    assert_eq!(state.fields[REG_MIN + 1], [7u8; 32]);
    assert_eq!(state.fields[VERSION_SLOT], field_from_u64(2));
}

#[test]
fn an_unauthorized_put_is_refused_at_the_front_door() {
    let (cclerk, executor, store) = deploy_store(0x03);

    // The caller holds NO authority; `put` requires Signature. Refused before any
    // turn is built (fail-closed at the userspace front door).
    let refused = store
        .put(&cclerk, REG_MIN, [5u8; 32], 1, InvokeAuthority::None)
        .expect_err("an unauthorized put must be refused");
    assert!(matches!(
        refused,
        KvError::Refused(InvokeRefused::Unauthorized {
            required: AuthRequired::Signature,
            ..
        })
    ));

    // Nothing was submitted — the register is untouched (anti-ghost).
    let state = executor.cell_state(store.cell).unwrap();
    assert_eq!(state.fields[REG_MIN], [0u8; 32]);
    assert_eq!(state.fields[VERSION_SLOT], [0u8; 32]);
}

#[test]
fn a_version_rollback_is_refused_by_the_executor_not_userspace() {
    let (cclerk, executor, store) = deploy_store(0x04);

    // Establish version 2.
    let t1 = store
        .put(&cclerk, REG_MIN, [1u8; 32], 2, InvokeAuthority::Signature)
        .unwrap();
    executor.submit_turn(&t1).expect("version -> 2 commits");

    // A Signature-authorized put that would roll the version BACK to 1: the front
    // door passes (auth + routing OK), but the EXECUTOR refuses on the verified
    // Monotonic(VERSION) invariant — the protocol layer, not a userspace check.
    let rollback = store
        .put(
            &cclerk,
            REG_MIN + 1,
            [2u8; 32],
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
    let state = executor.cell_state(store.cell).unwrap();
    assert_eq!(
        state.fields[REG_MIN + 1],
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
fn delete_clears_the_register_and_bumps_the_version() {
    let (cclerk, executor, store) = deploy_store(0x05);

    let t1 = store
        .put(&cclerk, REG_MIN, [3u8; 32], 1, InvokeAuthority::Signature)
        .unwrap();
    executor.submit_turn(&t1).expect("put commits");

    let del = store
        .delete(&cclerk, REG_MIN, 2, InvokeAuthority::Signature)
        .expect("a Signature holder may delete");
    executor.submit_turn(&del).expect("delete commits");

    let state = executor.cell_state(store.cell).unwrap();
    assert_eq!(state.fields[REG_MIN], [0u8; 32], "the register was cleared");
    assert_eq!(
        state.fields[VERSION_SLOT],
        field_from_u64(2),
        "version bumped"
    );
}

#[test]
fn get_is_the_named_serviced_seam_and_unknown_methods_fail_closed() {
    let (cclerk, _executor, store) = deploy_store(0x06);

    // `get` is Serviced — its answer rides the OFE cross-cell-read, not a replay.
    // invoke() refuses to desugar it (the named seam).
    let seam = store
        .get(&cclerk, REG_MIN)
        .expect_err("get is a serviced seam");
    assert!(matches!(
        seam,
        KvError::Refused(InvokeRefused::ServicedSeam { .. })
    ));

    // An unknown method does not route through the verified DFA — fail-closed.
    let unknown = resolve_against(
        store.cell,
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
    let store = KvStore::new(AppCipherclerk::new(AgentCipherclerk::new(), [0x07; 32]).cell_id());
    let iface = &store.descriptor;

    // Every published method routes through the verified DFA router (the same
    // path the Service Explorer uses to discover invokable methods).
    for m in [METHOD_PUT, METHOD_GET, METHOD_DELETE] {
        assert!(
            iface.route_method(&method_symbol(m)).is_some(),
            "{m} routes"
        );
    }

    // A route-membership witness PROVES `put` is a member of the committed
    // interface (via the existing dfa AIR) — and does not verify for a method it
    // was not minted for.
    let put = method_symbol(METHOD_PUT);
    let (proof, root) = iface
        .route_membership_witness(&put)
        .expect("a declared method has a membership witness");
    assert_eq!(root, iface.to_route_table().commitment);
    assert!(iface.verify_route_membership(&put, &proof));
    assert!(!iface.verify_route_membership(&method_symbol(METHOD_GET), &proof));
}
