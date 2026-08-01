//! THE PROOF-OF-CONCEPT, PROVEN BY RUNNING: a tiny cell-JS handler, run in the NATIVE
//! runtime (pure-Rust `boa`, NO servo, NO SpiderMonkey/mozjs), fires a REAL cap-gated
//! verified turn through the executor and the model advances.
//!
//! This closes the gap the work targets: cell-attached JS that runs in the cockpit
//! (gpui native), not just the web shell. The host fn `t(turn, arg)` the JS calls is
//! the SAME cap-gated verified-turn path a static `{turn,arg}` button runs.

use deos_js_runtime::applet::{Affordance, ApplyOp, CellApplet};
use deos_js_runtime::NativeRuntime;
use dregg_cell::AuthRequired;
use dregg_cell::Credential;
use dregg_cell::Requirement;

/// A "counter" cell surface: slot 0 is the count; `inc`/`dec` mutate it (require
/// `Signature`, which the driver holds); `reset` requires `Proof` (incomparable to
/// `Signature`, so the cap tooth refuses it). Mirrors the proven `deos-js` counter.
fn counter_applet() -> CellApplet {
    let mut pk = [0u8; 32];
    pk[0] = 0xA7;
    let token = [0u8; 32];
    CellApplet::mint(
        pk,
        token,
        &[(0usize, 0u64)],
        vec![
            Affordance {
                name: "inc".into(),
                required: Requirement::AtLeast(Credential::Signature),
                op: ApplyOp::AddToSlot { slot: 0 },
            },
            Affordance {
                name: "dec".into(),
                required: Requirement::AtLeast(Credential::Signature),
                op: ApplyOp::SubFromSlot { slot: 0 },
            },
            Affordance {
                name: "reset".into(),
                required: Requirement::AtLeast(Credential::Proof),
                op: ApplyOp::SetSlot { slot: 0, value: 0 },
            },
        ],
        AuthRequired::Signature,
    )
}

/// Native JS → the cap-bounded host fn `t(...)` → a REAL verified turn. The handler
/// fires `inc` three times; each fire commits a verified turn leaving a `TurnReceipt`,
/// and the cell's committed model advances. No servo, no mozjs — pure-Rust `boa`.
#[test]
fn native_js_handler_fires_a_verified_turn() {
    let applet = counter_applet();
    assert_eq!(applet.get_u64(0), 0, "the model starts at 0");

    // A tiny cell-JS handler: the behavior a cell's surface attaches. It calls the
    // cap-bounded host fn `t("inc", n)` — each call is a cap-gated verified turn.
    let handler = r#"
        t("inc", 5);
        t("inc", 2);
        t("inc", 1);
    "#;

    let mut rt = NativeRuntime::new();
    let outcome = rt.run(applet, handler).expect("the handler runs");

    // The model advanced through REAL verified turns (5 + 2 + 1 = 8).
    assert_eq!(
        outcome.applet.get_u64(0),
        8,
        "three native-JS fires advanced the committed model to 8"
    );
    // Each fire left a real receipt on the audit tape.
    assert_eq!(
        outcome.applet.receipts().len(),
        3,
        "three verified turns committed, three receipts"
    );
    assert!(
        outcome.last_fire_error.is_none(),
        "every authorized fire committed cleanly"
    );
}

/// The CAP TOOTH bites from native JS too: firing `reset` (requires `Proof`) under a
/// `Signature`-held surface is an over-reach — it commits NOTHING and the JS sees a
/// thrown error. Ocap holds across the engine boundary.
#[test]
fn native_js_overreach_is_refused_in_band() {
    let applet = counter_applet();

    // The handler bumps once (authorized), then tries to `reset` (unauthorized). The
    // thrown refusal aborts the script AFTER the authorized bump committed.
    let handler = r#"
        t("inc", 3);
        t("reset");
    "#;

    let mut rt = NativeRuntime::new();
    let result = rt.run(applet, handler);

    // The script threw on the over-reach (the cap tooth refused in-band).
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("the unauthorized reset should have thrown"),
    };
    assert!(
        err.contains("reset") || err.contains("refused") || err.contains("unauthorized"),
        "the JS error names the refused fire: {err}"
    );
}

/// The same `reset` over-reach, inspected through the host's `last_fire_error` rather
/// than the thrown JS error: nothing about an unauthorized fire reaches the executor.
#[test]
fn native_js_overreach_records_a_cap_refusal() {
    let applet = counter_applet();
    let handler = r#" try { t("reset"); } catch (e) { } "#;

    let mut rt = NativeRuntime::new();
    let outcome = rt
        .run(applet, handler)
        .expect("the try/catch swallows the throw");

    // The model never moved; the cap tooth recorded the refusal.
    assert_eq!(
        outcome.applet.get_u64(0),
        0,
        "the over-reach committed nothing"
    );
    assert_eq!(
        outcome.applet.receipts().len(),
        0,
        "no verified turn committed"
    );
    assert!(
        matches!(
            outcome.last_fire_error,
            Some(deos_js_runtime::FireError::Unauthorized(_))
        ),
        "the cap tooth recorded an Unauthorized refusal"
    );
}
