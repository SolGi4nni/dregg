//! RED-TEAM — the model's CONFINED `run_js` cannot reach the `deos.server.*` GM surface.
//!
//! Closes the coverage GAP the DEOS capability audit named (F1, HIGH / CRITICAL on an
//! open cockpit): the `deos.server.*` GM natives — `spawnCell`/`fork` (mint OPEN funded
//! cells), `setField` (write any OPEN cell), `grant` (hand out caps) — take NO `held`
//! argument and run NO cap tooth, yet were `JS_DefineFunction`'d into the SAME global a
//! model-authored `run_js` script evaluates in. A model emitting `deos.server.spawnCell/
//! setField/grant(...)` inside its script bypassed the `held` cap membrane entirely.
//!
//! The fix gives [`JsRuntime`] a TRUSTED-vs-CONFINED install mode: [`JsRuntime::eval`]
//! (the model's hands — what `run_js`/`run_attached`/`run_authoring`/`run_compose` route
//! through) installs NEITHER the `__deos_server_*` natives NOR the `deos.server` prelude
//! object; [`JsRuntime::eval_trusted`] (the operator's `deos-host` authoring runtime)
//! installs the full surface. This test asserts:
//!
//!   * F1 — from the CONFINED surface, `deos.server` is `undefined`, the raw
//!     `__deos_server_*` natives are absent, and CALLING a GM method throws;
//!   * the legit CONFINED surface (`deos.applet`/`app.fire`, `deos.compose`,
//!     `deos.editor.*`, the crawl) is untouched;
//!   * the TRUSTED operator surface still exposes the `deos.server.*` GM superpowers;
//!   * F5 — even on the trusted surface, a grant of the UNIVERSAL "none"/"open"
//!     authority is refused (a grant must name an explicit non-universal authority).
//!
//! SpiderMonkey's engine init is process-global + one-shot, so ALL assertions share ONE
//! runtime in a single test (each `eval` runs on a fresh global, so reuse is sound).

use deos_js::JsRuntime;

#[test]
fn a_model_confined_run_js_cannot_reach_the_gm_server_surface_the_operator_still_can() {
    let mut rt = JsRuntime::new().expect("boot SpiderMonkey once");

    // ── F1: the CONFINED surface hides the GM path ENTIRELY ────────────────────────
    // `typeof` on an undefined property / undeclared global yields "undefined" without
    // throwing, so this probe reads the surface without tripping. Every bit stays 0.
    let probe = r#"
        var reachable = 0;
        if (typeof deos.server !== "undefined") reachable |= 1;
        if (typeof __deos_server_spawn_cell !== "undefined") reachable |= 2;
        if (typeof __deos_server_grant !== "undefined") reachable |= 4;
        if (typeof __deos_server_set_field !== "undefined") reachable |= 8;
        if (typeof __deos_server_fork !== "undefined") reachable |= 16;
        if (typeof __deos_server_define_affordance !== "undefined") reachable |= 32;
        reachable;
    "#;
    assert_eq!(
        rt.eval(probe).expect("the confined probe evaluates"),
        Some(0),
        "F1 HOLE — the model's confined surface exposes deos.server / a __deos_server_* native"
    );

    // The legit CONFINED surface (the bounded model hands) stays intact — confinement
    // removed ONLY the GM path, not the crawl/fire/compose/editor surface.
    let legit = r#"
        ((typeof deos.applet === "function") &&
         (typeof deos.compose === "function") &&
         (typeof deos.editor === "object") &&
         (typeof deos.world === "object") &&
         (typeof deos.cell === "function")) ? 1 : 0;
    "#;
    assert_eq!(
        rt.eval(legit)
            .expect("the confined legit-surface probe evaluates"),
        Some(1),
        "confinement must NOT break the legit bounded surface (applet/compose/editor/world/cell)"
    );

    // ACTUALLY CALLING a GM method from the confined surface THROWS (deos.server is
    // undefined) — the eval faults, nothing is reached. This is the exploit the audit
    // named, now dead in the model's hands.
    for exploit in [
        r#"deos.server.spawnCell("00", "open"); 1;"#,
        r#"deos.server.grant("00", "00", "signature"); 1;"#,
        r#"deos.server.setField("00", 0, 1); 1;"#,
    ] {
        assert!(
            rt.eval(exploit).is_err(),
            "F1 HOLE — a confined script reached a GM method without throwing: {exploit}"
        );
    }

    // ── the TRUSTED operator authoring runtime DOES have the GM superpowers ─────────
    let operator = r#"
        ((typeof deos.server === "object") &&
         (typeof deos.server.spawnCell === "function") &&
         (typeof deos.server.fork === "function") &&
         (typeof deos.server.grant === "function") &&
         (typeof deos.server.setField === "function") &&
         (typeof deos.server.getField === "function") &&
         (typeof deos.server.defineAffordance === "function")) ? 1 : 0;
    "#;
    assert_eq!(
        rt.eval_trusted(operator)
            .expect("the trusted operator surface evaluates"),
        Some(1),
        "the operator authoring runtime must RETAIN the deos.server.* GM surface"
    );
    // …and the trusted surface ALSO keeps the legit bounded surface (a superset).
    assert_eq!(
        rt.eval_trusted(legit)
            .expect("the trusted legit-surface probe evaluates"),
        Some(1),
        "the trusted surface is a superset — the bounded surface is still present"
    );

    // ── F5: even on the trusted surface, a grant of the UNIVERSAL "none"/"open"
    //    authority is REFUSED (the native records the refusal → eval returns Err). ──
    let a = "11".repeat(32);
    let b = "22".repeat(32);
    let universal = format!(r#"deos.server.grant("{a}", "{b}", "none");"#);
    let err = rt
        .eval_trusted(&universal)
        .expect_err("F5 HOLE — a grant of the universal 'none' authority was accepted");
    assert!(
        err.contains("universal") || err.contains("none"),
        "the universal-label grant must be refused naming the reason, got: {err}"
    );
    // "open" is likewise refused — it is an UNKNOWN label (never parses to an authority),
    // so the grant returns -1 IN-BAND (no cap minted), never a universal cap.
    let open = format!(r#"deos.server.grant("{a}", "{b}", "open");"#);
    assert_eq!(
        rt.eval_trusted(&open)
            .expect("the 'open' grant evaluates (refused in-band)"),
        Some(-1),
        "F5 HOLE — a grant labelled 'open' was not refused (must return -1, no cap minted)"
    );

    // The trusted grant surface still WORKS for an EXPLICIT non-universal authority: an
    // "either" grant does NOT hit the F5 universal-label refusal (with no live World
    // attached it simply returns -1; the point is it is not refused on the LABEL).
    let explicit = format!(r#"deos.server.grant("{a}", "{b}", "either");"#);
    match rt.eval_trusted(&explicit) {
        Ok(_) => {}
        Err(e) => assert!(
            !e.contains("universal"),
            "an EXPLICIT 'either' grant must NOT hit the F5 universal-label refusal: {e}"
        ),
    }
}
