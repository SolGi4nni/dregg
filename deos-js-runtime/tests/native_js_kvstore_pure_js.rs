//! THE PURE-JS KVSTORE, PROVEN BY RUNNING: the `starbridge-kvstore` service cell rebuilt as
//! pure JavaScript-on-cells, driven through the native runtime (pure-Rust `boa`, NO servo,
//! NO SpiderMonkey/mozjs). The JS names **typed methods** on the store's PUBLISHED
//! [`InterfaceDescriptor`] — resolved through the verified DFA `route_method`, the SAME
//! dispatch `dregg_app_framework::invoke()` speaks — and writes the JS-supplied value to a
//! JS-supplied register through the literal-write `ApplyOp`. Every mutation is a REAL
//! cap-gated verified turn.
//!
//! This is the two named power-ups landed end-to-end:
//!   1. **literal / register-addressed writes** ([`ApplyOp::SetRegisterFromArgs`]): `put(reg,
//!      value)` writes `value` to register `reg` EXACTLY (overwrite semantics), instead of
//!      riding `AddToSlot` over a zeroed slot — so a JS affordance reaches an arbitrary
//!      register with an arbitrary value;
//!   2. **the route_method bridge** (`CellWorld::publish_interface`): `tCell("store","put",..)`
//!      resolves `put` against the store's published typed interface — an undeclared method
//!      is fail-closed, a `Serviced` method (`get`) is refused as a non-turn read, and the
//!      cap requirement is the published `MethodSig`'s, exactly as the real kvstore.
//!
//! The behavior is checked against the Rust `starbridge-kvstore` shape: `put` is a
//! `Signature`-gated `Replayable` write of `value` into register `reg`; `get` is a
//! `Serviced` read (the named OFE seam invoke() refuses to desugar); the register holds the
//! written value; an over-reach (a method the interface does not route, or a cap the app
//! does not hold) commits nothing.

use deos_js_runtime::applet::{Affordance, ApplyOp};
use deos_js_runtime::{CellWorld, FireError, NativeRuntime};
use dregg_cell::interface::{method_symbol, ArgsSchema, InterfaceDescriptor, MethodSig, Semantics};
use dregg_cell::AuthRequired;
use dregg_cell::{Credential, Requirement};

/// The lowest writable register index — slot 0 is the store version, per the Rust kvstore's
/// `VERSION_SLOT`/`REG_MIN`.
const REG_MIN: usize = 1;

/// Build the store's **published typed interface** — the SAME three-method shape the Rust
/// `starbridge_kvstore::interface_descriptor()` publishes: `put`(Signature, Replayable),
/// `delete`(Signature, Replayable), `get`(None, Serviced — the OFE seam).
fn kvstore_interface() -> InterfaceDescriptor {
    InterfaceDescriptor::new(vec![
        MethodSig {
            args_schema: ArgsSchema::Fixed(2),
            auth_required: AuthRequired::Signature,
            ..MethodSig::replayable(method_symbol("put"))
        },
        MethodSig {
            args_schema: ArgsSchema::Fixed(1),
            auth_required: AuthRequired::Signature,
            ..MethodSig::replayable(method_symbol("delete"))
        },
        MethodSig {
            args_schema: ArgsSchema::Fixed(1),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol("get"))
        },
    ])
}

/// A world holding the kvstore `store` cell (capped under `Signature`, the cap the app
/// holds) with its published typed interface, plus an UNCAPPED `vault` the app cannot name.
fn kvstore_world() -> (CellWorld, dregg_types::CellId) {
    let mut w = CellWorld::new();

    let mut store_pk = [0u8; 32];
    store_pk[0] = 0x57;
    w.add_cell(
        "store",
        store_pk,
        [0u8; 32],
        1_000_000,
        &[],
        vec![
            // put(reg, value): the register-addressed literal write — writes args[1] to the
            // register named by args[0]. This is the keystone power-up.
            Affordance {
                name: "put".into(),
                required: Requirement::AtLeast(Credential::Signature),
                op: ApplyOp::SetRegisterFromArgs,
            },
            // delete(reg): clear the register named by args[0] (write 0).
            Affordance {
                name: "delete".into(),
                required: Requirement::AtLeast(Credential::Signature),
                op: ApplyOp::SetSlot { slot: 0, value: 0 },
            },
            // get(reg): a Serviced read — never fired as a turn (the interface refuses it).
            // Body present only so the method name has an entry; the bridge stops it first.
            Affordance {
                name: "get".into(),
                required: Requirement::Root,
                op: ApplyOp::SetSlotFromArg { slot: 0 },
            },
        ],
        AuthRequired::Signature,
    );
    w.set_home("store");
    w.publish_interface("store", kvstore_interface());

    let mut vault_pk = [0u8; 32];
    vault_pk[0] = 0x99;
    let vault_id = w.add_uncapped_cell(vault_pk, [0u8; 32], 7_000, &[(0usize, 123u64)]);

    (w, vault_id)
}

/// THE PROTOTYPE: a pure-JS program drives the kvstore through its PUBLISHED typed methods,
/// writing the JS-supplied value to a JS-supplied register, then reading it back.
#[test]
fn pure_js_kvstore_put_and_get_via_typed_methods() {
    let (world, _vault) = kvstore_world();

    // The whole kvstore app as pure JS-on-cells. `put` names a TYPED METHOD routed through
    // the store's published interface; the register + value are both JS-supplied.
    let app = format!(
        r#"
        // put(reg=3, value=42) — a Signature-gated typed-method write of 42 into register 3.
        tCell("store", "put", {reg}, 42);
        // overwrite the SAME register with a literal write — lands 7 exactly (not 42+7),
        // the gap AddToSlot could not express.
        tCell("store", "put", {reg}, 7);
        // read the register back (a witnessed cross-cell read = the result).
        get("store", {reg});
    "#,
        reg = REG_MIN + 2
    );

    let mut rt = NativeRuntime::new();
    let outcome = rt
        .run_world(world, &app)
        .expect("the pure-JS kvstore app runs natively");
    let w = &outcome.world;

    // The register-addressed literal write committed and OVERWROTE: register 3 holds 7
    // (the second put), not 49 — proving literal-write semantics the Rust kvstore's
    // SetField(reg, value) has.
    assert_eq!(
        w.get_slot("store", REG_MIN + 2).unwrap(),
        7,
        "put(reg, value) wrote the JS value to the JS register, overwriting (literal write)"
    );
    assert_eq!(outcome.result, Some(7), "get(store, reg) returned 7");

    // Two verified turns committed — the two puts. `get` is a read, no turn.
    assert_eq!(
        w.receipts().len(),
        2,
        "two typed-method writes, two receipts"
    );
    assert!(
        outcome.last_fire_error.is_none(),
        "every typed-method write committed cleanly: {:?}",
        outcome.last_fire_error
    );
}

/// A method the published interface does NOT route is fail-closed — `MethodNotRouted`,
/// nothing committed. The JS cannot invent a method the typed interface never declared.
#[test]
fn undeclared_method_does_not_route() {
    let (world, _vault) = kvstore_world();
    let app = r#" try { tCell("store", "frobnicate", 1, 2); } catch (e) {} "#;
    let mut rt = NativeRuntime::new();
    let outcome = rt
        .run_world(world, app)
        .expect("the try/catch swallows the throw");

    assert!(
        matches!(outcome.last_fire_error, Some(FireError::MethodNotRouted(_))),
        "an undeclared method is refused at the route_method bridge, got {:?}",
        outcome.last_fire_error
    );
    assert_eq!(
        outcome.world.receipts().len(),
        0,
        "the unrouted method committed no turn"
    );
}

/// A `Serviced` method (`get`) named through `tCell` is refused as a non-turn read — the
/// `ServicedSeam`, mirroring the Rust kvstore's `invoke()` refusal to desugar a serviced
/// read into a fake write. The seam is named honestly.
#[test]
fn serviced_method_is_refused_as_a_non_turn() {
    let (world, _vault) = kvstore_world();
    let app = r#" try { tCell("store", "get", 3); } catch (e) {} "#;
    let mut rt = NativeRuntime::new();
    let outcome = rt
        .run_world(world, app)
        .expect("the try/catch swallows the throw");

    assert!(
        matches!(outcome.last_fire_error, Some(FireError::ServicedSeam(_))),
        "a Serviced method fired as a turn is refused as a seam, got {:?}",
        outcome.last_fire_error
    );
    assert_eq!(
        outcome.world.receipts().len(),
        0,
        "the serviced read committed no turn"
    );
}

/// The cap requirement comes from the PUBLISHED `MethodSig`, not the local affordance. The
/// app holds `Proof` toward the store; the local `put` affordance says `required: Proof`
/// (which `Proof` SATISFIES), but the PUBLISHED `put` requires `Signature` (which `Proof`
/// does NOT satisfy — they are incomparable). The refusal therefore proves the bridge gated
/// on the published interface, via the SAME `is_attenuation` tooth.
#[test]
fn typed_method_cap_gate_comes_from_the_published_interface() {
    let mut w = CellWorld::new();
    let mut pk = [0u8; 32];
    pk[0] = 0x57;
    // Capped under `Proof`. The local affordance's `Proof` would PASS the gate; only the
    // published `Signature` requirement refuses — so a refusal proves the published
    // interface drives the cap tooth.
    w.add_cell(
        "store",
        pk,
        [0u8; 32],
        1_000_000,
        &[],
        vec![Affordance {
            name: "put".into(),
            required: Requirement::AtLeast(Credential::Proof),
            op: ApplyOp::SetRegisterFromArgs,
        }],
        AuthRequired::Proof,
    );
    w.publish_interface("store", kvstore_interface());

    let app = r#" try { tCell("store", "put", 3, 42); } catch (e) {} "#;
    let mut rt = NativeRuntime::new();
    let outcome = rt
        .run_world(w, app)
        .expect("the try/catch swallows the throw");

    assert!(
        matches!(outcome.last_fire_error, Some(FireError::Unauthorized(_))),
        "the published Signature requirement gates the typed-method write, got {:?}",
        outcome.last_fire_error
    );
    assert_eq!(
        outcome.world.get_slot("store", REG_MIN + 2).unwrap(),
        0,
        "the unauthorized write committed nothing"
    );
    assert_eq!(
        outcome.world.receipts().len(),
        0,
        "no verified turn committed"
    );
}
