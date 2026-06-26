//! **The CELLS-AS-SERVICE-OBJECTS proof for the escrow-market, end-to-end.**
//!
//! Declares the escrow service cell, drives its lifecycle through the `invoke()`
//! front door, and submits the desugared turns through the real
//! [`EmbeddedExecutor`]. The properties pinned here (the third worked citizen of
//! the pattern, after `starbridge-kvstore` and `starbridge-nameservice`, and the
//! first NON-TRIVIAL four-organ app):
//!
//! 1. **The escrow publishes a typed interface** (list/fund/ship/settle + view
//!    with their auth + replayable-vs-serviced semantics), resolvable as a
//!    Service-Explorer would resolve it (via an [`InterfaceRegistry`]).
//! 2. **The whole lifecycle commits as real verified turns** — each invoke()-
//!    desugared `SetField`s land on the per-cell heap, advancing the order
//!    LISTED → FUNDED → SHIPPED → SETTLED.
//! 3. **The cap-gate bites at the front door** — an unauthorized `fund`
//!    (`InvokeAuthority::None` vs the method's `Signature`) is refused before any
//!    turn is built; nothing is submitted (anti-ghost).
//! 4. **The four organ caveats re-enforce on invoke()-desugared turns** — an
//!    over-ceiling `fund` (TRUSTLINE `FieldLteField`) and a replayed `settle`
//!    (LIFECYCLE `StrictMonotonic`) are EXECUTOR refusals, not userspace checks.
//! 5. **`view` is the named seam** — it refuses to desugar (its answer rides the
//!    OFE cross-cell-read = the committed state), and an unknown method does not
//!    route (fail-closed).
//! 6. **The interface is witnessably inspectable** — a route-membership witness
//!    proves `settle` is a member of the committed interface.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, field_from_u64, resolve_against,
};
use dregg_cell::interface::{Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use starbridge_escrow_market::service::{
    EscrowError, EscrowService, METHOD_FUND, METHOD_LIST, METHOD_SETTLE, METHOD_SHIP, METHOD_VIEW,
    escrow_service_program, field_value_u64, interface_descriptor, register_interface,
};
use starbridge_escrow_market::{
    CEILING_SLOT, DELIVERY_HASH_SLOT, ESCROWED_SLOT, RELEASED_SLOT, STATE_FUNDED, STATE_LISTED,
    STATE_SETTLED, STATE_SHIPPED, STATE_SLOT, sealed_delivery_digest, state_field,
};

/// A cipherclerk + an embedded executor whose agent cell IS the escrow cell,
/// with the canonical escrow program installed.
fn deploy_escrow(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, EscrowService) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let escrow_cell = cclerk.cell_id();
    executor.install_program(escrow_cell, escrow_service_program());
    let svc = EscrowService::new(escrow_cell);
    (cclerk, executor, svc)
}

#[test]
fn the_escrow_publishes_a_resolvable_typed_interface() {
    let (_cclerk, _executor, svc) = deploy_escrow(0x01);

    // The Service Explorer resolves a cell's interface from an InterfaceRegistry
    // an app populated — the richer-than-derived descriptor with real auth/seam.
    let mut registry = InterfaceRegistry::new();
    register_interface(&mut registry, svc.cell);
    let resolved = registry
        .get(&svc.cell)
        .expect("the interface is registered");

    assert_eq!(resolved.methods.len(), 5);
    for m in [METHOD_LIST, METHOD_FUND, METHOD_SHIP, METHOD_SETTLE] {
        assert_eq!(
            resolved.method(&method_symbol(m)).unwrap().auth_required,
            AuthRequired::Signature,
            "{m} is Signature-gated",
        );
    }
    assert_eq!(
        resolved
            .method(&method_symbol(METHOD_VIEW))
            .unwrap()
            .semantics,
        Semantics::Serviced,
    );

    // The published descriptor carries richer semantics than derive-from-program
    // would (which is all-Replayable / all-None): the ids differ.
    let derived =
        dregg_cell::interface::InterfaceDescriptor::derive_replayable(&escrow_service_program());
    assert_ne!(
        derived.interface_id, resolved.interface_id,
        "the registered interface carries Signature/Serviced the derived one cannot"
    );
}

#[test]
fn the_whole_lifecycle_commits_as_verified_turns() {
    let (cclerk, executor, svc) = deploy_escrow(0x02);

    // list(ceiling = 1000)
    let t = svc
        .list(&cclerk, "acme-corp", 1000, InvokeAuthority::Signature)
        .expect("a Signature holder may build a list invocation");
    let receipt = executor
        .submit_turn(&t)
        .expect("the desugared list turn commits through the verified executor");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real receipt");
    let state = executor.cell_state(svc.cell).unwrap();
    assert_eq!(field_value_u64(&state.fields[CEILING_SLOT]), 1000);
    assert_eq!(state.fields[STATE_SLOT], state_field(STATE_LISTED));

    // fund(amount = 800 ≤ 1000)
    let t = svc
        .fund(&cclerk, "buyer-bob", 800, InvokeAuthority::Signature)
        .unwrap();
    executor.submit_turn(&t).expect("fund commits");
    let state = executor.cell_state(svc.cell).unwrap();
    assert_eq!(field_value_u64(&state.fields[ESCROWED_SLOT]), 800);
    assert_eq!(state.fields[STATE_SLOT], state_field(STATE_FUNDED));

    // ship(delivery)
    let delivery = sealed_delivery_digest(b"the-goods");
    let t = svc
        .ship(&cclerk, delivery, InvokeAuthority::Signature)
        .unwrap();
    executor.submit_turn(&t).expect("ship commits");
    let state = executor.cell_state(svc.cell).unwrap();
    assert_eq!(state.fields[DELIVERY_HASH_SLOT], delivery);
    assert_eq!(state.fields[STATE_SLOT], state_field(STATE_SHIPPED));

    // settle(released = 800, refunded = 0) — conserves the escrow.
    let t = svc
        .settle(&cclerk, 800, 0, InvokeAuthority::Signature)
        .unwrap();
    executor.submit_turn(&t).expect("conserving settle commits");
    let state = executor.cell_state(svc.cell).unwrap();
    assert_eq!(field_value_u64(&state.fields[RELEASED_SLOT]), 800);
    assert_eq!(state.fields[STATE_SLOT], state_field(STATE_SETTLED));
}

#[test]
fn an_unauthorized_fund_is_refused_at_the_front_door() {
    let (cclerk, executor, svc) = deploy_escrow(0x03);
    svc.list(&cclerk, "acme-corp", 1000, InvokeAuthority::Signature)
        .and_then(|t| {
            executor
                .submit_turn(&t)
                .map_err(|_| EscrowError::EmptyParty)
                .map(|_| t)
        })
        .expect("list commits");

    // The caller holds NO authority; `fund` requires Signature. Refused before any
    // turn is built (fail-closed at the userspace front door).
    let refused = svc
        .fund(&cclerk, "buyer-bob", 800, InvokeAuthority::None)
        .expect_err("an unauthorized fund must be refused");
    assert!(matches!(
        refused,
        EscrowError::Refused(InvokeRefused::Unauthorized {
            required: AuthRequired::Signature,
            ..
        })
    ));

    // Nothing was submitted — the order is still LISTED, escrow untouched (anti-ghost).
    let state = executor.cell_state(svc.cell).unwrap();
    assert_eq!(state.fields[STATE_SLOT], state_field(STATE_LISTED));
    assert_eq!(state.fields[ESCROWED_SLOT], [0u8; 32]);
}

#[test]
fn an_over_ceiling_fund_is_refused_by_the_executor_trustline() {
    let (cclerk, executor, svc) = deploy_escrow(0x04);
    let t = svc
        .list(&cclerk, "acme-corp", 1000, InvokeAuthority::Signature)
        .unwrap();
    executor.submit_turn(&t).expect("list commits");

    // A Signature-authorized fund of 1500 against a 1000 ceiling: the front door
    // passes (auth + routing OK), but the EXECUTOR refuses on the verified TRUSTLINE
    // FieldLteField(ESCROWED ≤ CEILING) — the protocol layer, not a userspace check.
    let over = svc
        .fund(&cclerk, "buyer-bob", 1500, InvokeAuthority::Signature)
        .expect("the over-ceiling invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&over);
    assert!(
        rejected.is_err(),
        "the executor must refuse an over-ceiling fund"
    );

    // Anti-ghost: the rejected turn committed nothing — still LISTED, escrow zero.
    let state = executor.cell_state(svc.cell).unwrap();
    assert_eq!(state.fields[STATE_SLOT], state_field(STATE_LISTED));
    assert_eq!(state.fields[ESCROWED_SLOT], [0u8; 32]);
}

#[test]
fn a_replayed_settle_is_refused_by_the_executor_lifecycle() {
    let (cclerk, executor, svc) = deploy_escrow(0x05);

    // Build-then-submit each step in order: each turn binds the prior committed
    // receipt, so the lifecycle must be driven sequentially (not built up front).
    let t = svc
        .list(&cclerk, "acme-corp", 1000, InvokeAuthority::Signature)
        .unwrap();
    executor.submit_turn(&t).expect("list commits");
    let t = svc
        .fund(&cclerk, "buyer-bob", 800, InvokeAuthority::Signature)
        .unwrap();
    executor.submit_turn(&t).expect("fund commits");
    let t = svc
        .ship(
            &cclerk,
            sealed_delivery_digest(b"the-goods"),
            InvokeAuthority::Signature,
        )
        .unwrap();
    executor.submit_turn(&t).expect("ship commits");
    let t = svc
        .settle(&cclerk, 800, 0, InvokeAuthority::Signature)
        .unwrap();
    executor.submit_turn(&t).expect("conserving settle commits");

    let state = executor.cell_state(svc.cell).unwrap();
    assert_eq!(state.fields[STATE_SLOT], state_field(STATE_SETTLED));

    // A Signature-authorized settle REPLAYED on an already-SETTLED order: the front
    // door passes, but STATE 4 → 4 is not a strict advance — the EXECUTOR refuses on
    // the verified LIFECYCLE StrictMonotonic(STATE). No double-settle.
    let replay = svc
        .settle(&cclerk, 800, 0, InvokeAuthority::Signature)
        .expect("the replay invocation BUILDS (front door passes)");
    let rejected = executor.submit_turn(&replay);
    assert!(
        rejected.is_err(),
        "the executor must refuse a settle replay"
    );
    let msg = format!("{:?}", rejected.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic")
            || msg.contains("strict")
            || msg.contains("program")
            || msg.contains("writeonce")
            || msg.contains("field"),
        "refused on the StrictMonotonic(STATE) caveat, got: {msg}"
    );

    // Anti-ghost: STATE still SETTLED, never advanced past it.
    let state = executor.cell_state(svc.cell).unwrap();
    assert_eq!(state.fields[STATE_SLOT], state_field(STATE_SETTLED));
}

#[test]
fn view_is_the_named_serviced_seam_and_unknown_methods_fail_closed() {
    let (cclerk, _executor, svc) = deploy_escrow(0x06);

    // `view` is Serviced — its answer rides the OFE cross-cell-read (the committed
    // lifecycle state), not a replay. invoke() refuses to desugar it (the seam).
    let seam = svc.view(&cclerk).expect_err("view is a serviced seam");
    assert!(matches!(
        seam,
        EscrowError::Refused(InvokeRefused::ServicedSeam { .. })
    ));

    // An unknown method does not route through the verified DFA — fail-closed.
    let unknown = resolve_against(
        svc.cell,
        &interface_descriptor(),
        "drain_funds",
        vec![],
        vec![],
        InvokeAuthority::Signature,
    )
    .expect_err("an unknown method does not route");
    assert!(matches!(unknown, InvokeRefused::UnknownMethod { .. }));
}

#[test]
fn the_interface_is_witnessably_inspectable() {
    let svc =
        EscrowService::new(AppCipherclerk::new(AgentCipherclerk::new(), [0x07; 32]).cell_id());
    let iface = &svc.descriptor;

    // Every published method routes through the verified DFA router (the same path
    // the Service Explorer uses to discover invokable methods).
    for m in [
        METHOD_LIST,
        METHOD_FUND,
        METHOD_SHIP,
        METHOD_SETTLE,
        METHOD_VIEW,
    ] {
        assert!(
            iface.route_method(&method_symbol(m)).is_some(),
            "{m} routes"
        );
    }

    // A route-membership witness PROVES `settle` is a member of the committed
    // interface (via the existing dfa AIR) — and does not verify for a method it
    // was not minted for.
    let settle = method_symbol(METHOD_SETTLE);
    let (proof, root) = iface
        .route_membership_witness(&settle)
        .expect("a declared method has a membership witness");
    assert_eq!(root, iface.to_route_table().commitment);
    assert!(iface.verify_route_membership(&settle, &proof));
    assert!(!iface.verify_route_membership(&method_symbol(METHOD_LIST), &proof));
}

/// `field_from_u64` is re-exported through the framework and used above for the
/// amount encodings; assert the round-trip the service relies on holds.
#[test]
fn amount_encoding_roundtrips() {
    assert_eq!(field_value_u64(&field_from_u64(800)), 800);
}
