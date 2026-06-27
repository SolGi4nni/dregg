//! THE PURE-JS STARBRIDGE-APP, PROVEN BY RUNNING: a single JavaScript program — run in
//! the NATIVE runtime (pure-Rust `boa`, NO servo, NO SpiderMonkey/mozjs) — **coordinates
//! several cells**: it writes state into a store cell, moves value between a wallet and the
//! store, self-edits its own view-tree, and reads the results back. Every effect is a REAL
//! cap-gated verified turn through the embedded executor, and an over-reach (touching a
//! cell the app holds no cap to) is refused in-band, committing nothing.
//!
//! This is the userspace-apps-as-pure-JS vision: a starbridge-app shaped entirely as
//! JS-on-cells, orchestrating OTHER cells through a cap-bounded host API, with no ambient
//! authority — the app references cells only by the handles the host installed, and each
//! handle IS the capability.

use deos_js_runtime::applet::{Affordance, ApplyOp};
use deos_js_runtime::world::{read_view_blob, VIEW_VERSION_SLOT};
use deos_js_runtime::{CellWorld, FireError, NativeRuntime};
use dregg_cell::AuthRequired;

/// Each verified turn the world stamps pays this fee (see `CellWorld::commit`).
const FEE: i64 = 10_000;

/// A starbridge-app world the JS coordinates:
/// - `store` — a KV-register cell; affordance `put` adds the JS arg to register slot 0 (a
///   fresh `0` slot, so a single `put(v)` lands `v`). Requires `Signature`, which the app
///   holds.
/// - `wallet` — the app's value-bearing HOME cell, balance 1_000_000.
/// - `vault` — a cell on the SAME ledger the app holds NO cap to (no handle names it). It
///   exists, carries a balance + a field, and must stay untouched.
///
/// Cells are funded well above [`FEE`] so each can pay for its own turns.
fn app_world() -> (CellWorld, dregg_types::CellId) {
    let mut w = CellWorld::new();

    let mut store_pk = [0u8; 32];
    store_pk[0] = 0x57;
    w.add_cell(
        "store",
        store_pk,
        [0u8; 32],
        1_000_000,
        &[(0usize, 0u64)],
        vec![Affordance {
            name: "put".into(),
            required: AuthRequired::Signature,
            op: ApplyOp::AddToSlot { slot: 0 },
        }],
        AuthRequired::Signature,
    );

    let mut wallet_pk = [0u8; 32];
    wallet_pk[0] = 0x11;
    w.add_cell(
        "wallet",
        wallet_pk,
        [0u8; 32],
        1_000_000,
        &[(0usize, 0u64)],
        Vec::new(),
        AuthRequired::Signature,
    );
    w.set_home("wallet");

    // The vault exists on the ledger but the app holds NO cap to it (no handle).
    let mut vault_pk = [0u8; 32];
    vault_pk[0] = 0x99;
    let vault_id = w.add_uncapped_cell(vault_pk, [0u8; 32], 7_000, &[(0usize, 123u64)]);

    (w, vault_id)
}

/// THE PROTOTYPE: one pure-JS program coordinates the store + wallet cells — set state,
/// move value, self-edit the view, read back — all verified turns, cap-confined.
#[test]
fn pure_js_app_coordinates_two_cells() {
    let (world, _vault) = app_world();

    // A whole starbridge-app as PURE JS-on-cells. It coordinates two cells through the
    // cap-bounded host API: `tCell` fires another cell's affordance, `transfer` moves
    // value, `viewPatch` self-edits the home surface, `get` reads results back.
    let app = r#"
        // 1. write a value into the store cell (a verified SetField turn on `store`).
        tCell("store", "put", 42);

        // 2. move value from the wallet into the store (a verified Transfer turn).
        transfer("wallet", "store", 100);

        // 3. self-edit the home (wallet) view-tree — a receipted heap edit.
        viewPatch('{"kind":"text","props":{"text":"sent 100 to store"},"children":[]}');

        // 4. read the store register back (a witnessed cross-cell read = the result).
        get("store", 0);
    "#;

    let mut rt = NativeRuntime::new();
    let outcome = rt
        .run_world(world, app)
        .expect("the pure-JS app runs natively");
    let w = &outcome.world;

    // The cross-cell write committed: the store register holds 42.
    assert_eq!(
        w.get_slot("store", 0).unwrap(),
        42,
        "tCell put a real verified value into the store"
    );
    // The JS read it back as the script's completion value.
    assert_eq!(outcome.result, Some(42), "get(\"store\", 0) returned 42");

    // Value moved, conservation-respecting:
    //   store: 1_000_000 - FEE (its own put turn) + 100 (received).
    //   wallet: 1_000_000 - FEE (transfer turn) - 100 (sent) - FEE (viewPatch turn).
    assert_eq!(
        w.balance("store").unwrap(),
        1_000_000 - FEE + 100,
        "store paid its put-turn fee and received 100"
    );
    assert_eq!(
        w.balance("wallet").unwrap(),
        1_000_000 - FEE - 100 - FEE,
        "wallet paid the transfer + viewPatch turn fees and sent 100"
    );

    // The self-edit landed: the view version advanced through a real turn.
    assert_eq!(
        w.get_home_slot(VIEW_VERSION_SLOT).unwrap(),
        1,
        "viewPatch bumped the home view version via a verified turn"
    );
    assert!(
        outcome.last_fire_error.is_none(),
        "every coordinated effect committed cleanly"
    );

    // Three verified turns committed: the store `put`, the wallet->store `transfer`, the
    // home `viewPatch`. (`get` is a read, no turn.)
    assert_eq!(
        w.receipts().len(),
        3,
        "three coordinated verified turns left three receipts"
    );
}

/// THE CONFINEMENT PROOF: a pure-JS app can only touch cells it holds caps to. Firing on a
/// cell with NO installed handle (`vault`) is refused in-band — nothing commits and the
/// vault cell is never touched.
#[test]
fn pure_js_app_cannot_touch_an_uncapped_cell() {
    let (world, vault_id) = app_world();
    assert_eq!(
        world.balance("store").unwrap(),
        1_000_000,
        "store reachable"
    );

    // The app tries to reach a cell it holds no cap to. There is no `vault` handle in the
    // cap table, so the name resolves to NoCapability — the ocap stance: you cannot even
    // name what you do not hold.
    let app = r#"
        try {
            tCell("vault", "put", 999);
        } catch (e) {
            // swallowed — the over-reach threw and committed nothing.
        }
        // a legitimate effect still works after the refused one.
        tCell("store", "put", 7);
    "#;

    let mut rt = NativeRuntime::new();
    let outcome = rt
        .run_world(world, app)
        .expect("the try/catch swallows the over-reach throw");
    let w = &outcome.world;

    // The over-reach was recorded as a missing capability — the ocap gate bit.
    assert!(
        matches!(outcome.last_fire_error, Some(FireError::NoCapability(_))),
        "the uncapped-cell fire recorded a NoCapability refusal, got {:?}",
        outcome.last_fire_error
    );

    // The vault on the ledger is untouched: same balance, same field.
    let vault = w.cell_on_ledger(vault_id).expect("vault on the ledger");
    assert_eq!(
        vault.state.balance(),
        7_000,
        "uncapped vault balance untouched"
    );
    assert_eq!(
        vault.state.get_field(0).copied().map(|fe| fe[0]),
        Some(123),
        "uncapped vault field untouched"
    );

    // Exactly ONE turn committed — the legitimate `store.put(7)` after the refusal.
    assert_eq!(
        w.get_slot("store", 0).unwrap(),
        7,
        "the legitimate fire still committed"
    );
    assert_eq!(
        w.receipts().len(),
        1,
        "only the authorized fire committed a turn; the over-reach committed nothing"
    );
}

/// THE INSUFFICIENT-CAP PROOF: a handle present in the cap table but whose held authority
/// does not satisfy an affordance's `required` is an Unauthorized refusal — the SAME cap
/// tooth `deos-js` runs, now across a multi-cell app.
#[test]
fn pure_js_app_overreach_on_a_held_cell_is_refused() {
    let mut w = CellWorld::new();
    let mut pk = [0u8; 32];
    pk[0] = 0x57;
    // The app holds only `Signature` toward the store, but `wipe` requires `Proof`
    // (incomparable to `Signature`), so the cap tooth refuses it.
    w.add_cell(
        "store",
        pk,
        [0u8; 32],
        1_000_000,
        &[(0usize, 5u64)],
        vec![
            Affordance {
                name: "put".into(),
                required: AuthRequired::Signature,
                op: ApplyOp::AddToSlot { slot: 0 },
            },
            Affordance {
                name: "wipe".into(),
                required: AuthRequired::Proof,
                op: ApplyOp::SetSlot { slot: 0, value: 0 },
            },
        ],
        AuthRequired::Signature,
    );
    w.set_home("store");

    let app = r#" try { tCell("store", "wipe", 0); } catch (e) {} "#;
    let mut rt = NativeRuntime::new();
    let outcome = rt
        .run_world(w, app)
        .expect("the try/catch swallows the throw");

    assert!(
        matches!(outcome.last_fire_error, Some(FireError::Unauthorized(_))),
        "the insufficient-cap fire recorded an Unauthorized refusal, got {:?}",
        outcome.last_fire_error
    );
    assert_eq!(
        outcome.world.get_slot("store", 0).unwrap(),
        5,
        "the unauthorized wipe committed nothing"
    );
    assert_eq!(
        outcome.world.receipts().len(),
        0,
        "no verified turn committed"
    );
}

/// The view-tree self-edit is genuinely committed to the home cell's heap (the blob a
/// renderer reads), not just held in memory.
#[test]
fn view_patch_commits_a_readable_heap_blob() {
    let (world, _vault) = app_world();
    let app = r#" viewPatch('{"kind":"text","props":{"text":"hello cells"},"children":[]}'); "#;
    let mut rt = NativeRuntime::new();
    let outcome = rt.run_world(world, app).expect("the viewPatch app runs");

    let blob = outcome
        .world
        .home_view_blob()
        .expect("the home cell carries a committed view-tree blob");
    let text = String::from_utf8(blob).expect("utf8 view-tree json");
    assert!(
        text.contains("hello cells"),
        "the committed heap blob carries the patched view-tree: {text}"
    );
    let _ = read_view_blob; // re-exported helper the cockpit renderer reads with.
}
