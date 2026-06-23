//! THE SPIKE, PROVEN BY RUNNING: JS (real SpiderMonkey) drives deos substance.
//!
//! (a) From a JS string, define an applet and fire an affordance → a REAL `TurnReceipt`
//!     lands on the embedded ledger AND the model reflects it.
//! (b) A local view-state change from JS leaves NO new receipt (ephemeral, not a turn).
//! (c) The cap tooth REFUSES an unheld affordance (anti-ghost: nothing committed).
//! (d) A second applet is `transclude`d and the composition is cap-gated/provenanced
//!     (a verified finalized read, NOT a raw copy).
//!
//! SpiderMonkey is a process-global, thread-bound singleton: `JSEngine::init()` may be
//! called only ONCE per process, and a `JSContext` may be touched only on the thread
//! that created it. So the three JS-driven assertions (a)/(b)/(c) run inside ONE
//! `#[test]`, on ONE engine, on ONE thread, against fresh applets. The transclusion
//! compose (d) is pure substance (no engine) and stands alone.

use deos_js::applet::{pack_u64, Affordance, Applet};
use deos_js::js::{set_current_applet, take_current_applet};
use deos_js::JsRuntime;
use dregg_cell::AuthRequired;

/// Build a "counter" applet: slot 0 holds the count; affordances `inc`/`dec` mutate it
/// via verified turns; `reset` requires Signature (the driver does NOT hold it).
fn counter_applet(seed: u8) -> Applet {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    let token = [0u8; 32];

    // inc/dec require `Signature` — which the driver HOLDS, so they fire.
    let inc = Affordance {
        name: "inc".into(),
        required: AuthRequired::Signature,
        apply: Box::new(|model, arg| {
            let cur = model.field_u64(0);
            vec![(0usize, pack_u64(cur + arg.max(0) as u64))]
        }),
    };
    let dec = Affordance {
        name: "dec".into(),
        required: AuthRequired::Signature,
        apply: Box::new(|model, arg| {
            let cur = model.field_u64(0);
            vec![(0usize, pack_u64(cur.saturating_sub(arg.max(0) as u64)))]
        }),
    };
    // `reset` requires `Proof` — INCOMPARABLE to the held `Signature` (neither narrows
    // the other), so the cap tooth REFUSES it: holding a signature does not grant a
    // proof. This is the genuine attenuation lattice (`is_attenuation`), not a flag.
    let reset = Affordance {
        name: "reset".into(),
        required: AuthRequired::Proof,
        apply: Box::new(|_model, _arg| vec![(0usize, pack_u64(0))]),
    };

    // Driver HOLDS `Signature`: the cap tooth admits the `Signature`-requiring
    // affordances and REFUSES the `Proof`-requiring one (incomparable authority).
    Applet::mint(
        pk,
        token,
        &[(0usize, pack_u64(0))],
        vec![inc, dec, reset],
        AuthRequired::Signature,
    )
}

#[test]
fn js_drives_verified_turns_over_an_applet_cell() {
    // SpiderMonkey (esp. with the default JIT feature) needs a large native stack and
    // is thread-bound. The Rust test harness runs each `#[test]` on a ~2MB-stack
    // worker thread, which underflows SM's stack-quota guard → SIGSEGV. Run the engine
    // on a dedicated 64MB-stack thread; the context is created AND used there.
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(js_spike_body)
        .expect("spawn big-stack JS thread")
        .join()
        .expect("JS spike thread");
}

fn js_spike_body() {
    let mut rt = JsRuntime::new().expect("boot SpiderMonkey (process-global, once)");

    // ── (a) JS fires affordances → REAL verified turns + receipts ──────────────────
    set_current_applet(counter_applet(0xA1));
    let js_a = r#"
        var app = deos.applet({ affordances: ["inc", "dec", "reset"] });
        app.inc(5);
        app.inc(3);
        app.inc(2);   // count = 10
        app.dec(4);   // count = 6
        app.get(0);   // <- the script's result: a witnessed read = 6
    "#;
    let result = rt.eval(js_a).expect("eval (a) should succeed");
    assert_eq!(result, Some(6), "JS witnessed read of the model = 6");

    let applet = take_current_applet().expect("applet (a) present");
    assert_eq!(applet.get_u64(0), 6, "the cell model reflects the verified turns");
    assert_eq!(
        applet.receipt_count(),
        4,
        "four JS affordance fires (inc×3, dec×1) ⇒ four verified turns"
    );
    let last = applet.last_receipt().expect("a receipt landed");
    assert_ne!(last, [0u8; 32], "the receipt hash is non-zero");
    println!(
        "REAL last TurnReceipt hash (dec→6): {}",
        last.iter().map(|b| format!("{b:02x}")).collect::<String>()
    );

    // ── (b) a JS view-state change is NOT a turn ───────────────────────────────────
    set_current_applet(counter_applet(0xB2));
    let js_b = r#"
        var app = deos.applet({ affordances: ["inc", "dec"] });
        app.inc(7);                                  // ONE verified turn.
        app.view.set("draft", "hello, unsent text"); // ephemeral — NO turn.
        app.view.set("hover", "button-3");           // ephemeral — NO turn.
        app.view.set("focus", "field-name");         // ephemeral — NO turn.
        app.view.get("draft");                        // a read; still no turn.
        app.get(0);                                   // result = 7
    "#;
    let result = rt.eval(js_b).expect("eval (b) should succeed");
    assert_eq!(result, Some(7));
    let applet = take_current_applet().expect("applet (b) present");
    assert_eq!(
        applet.receipt_count(),
        1,
        "the THREE view.set calls left NO receipt: view-state is ephemeral, not a turn"
    );
    assert_eq!(applet.get_u64(0), 7);
    assert_eq!(applet.get_view("draft"), Some("hello, unsent text"));
    assert_eq!(applet.get_view("hover"), Some("button-3"));

    // ── (c) the cap tooth refuses an unheld affordance (anti-ghost) ────────────────
    set_current_applet(counter_applet(0xC3));
    let js_c = r#"
        var app = deos.applet({ affordances: ["inc", "reset"] });
        app.inc(9);            // ok: 1 receipt.
        app.fire("reset", 0);  // REFUSED by the cap-gate: returns -1, no receipt.
        app.get(0);            // still 9
    "#;
    let result = rt.eval(js_c).expect("eval (c) should succeed");
    assert_eq!(result, Some(9), "the refused turn did not mutate the model");
    let applet = take_current_applet().expect("applet (c) present");
    assert_eq!(
        applet.receipt_count(),
        1,
        "the unauthorized affordance committed NOTHING (anti-ghost)"
    );

    // ── (d) THE REFLECTIVE CRAWL — JS objects crawl the live image ─────────────────
    // Reflection is a cap-bounded, attested READ (no authority conferred), distinct
    // from the productions above. The applet's ledger holds its sovereign cell;
    // `deos.world`/`deos.cell` crawl it through `deos-reflect`.
    let mut crawl_applet = counter_applet(0xD7);
    crawl_applet.fire("inc", 42).unwrap(); // model = 42; the crawl reads it back
    let cell_hex = crawl_applet
        .cell()
        .as_bytes()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>();
    set_current_applet(crawl_applet);

    // (d.1) crawl every cell, read a substance off the live ledger.
    let js_crawl = format!(
        r#"
        var ids = deos.world.cells();              // crawl the ledger
        var found = ids.indexOf("{cell_hex}") >= 0; // our applet cell is present
        var view = deos.cell("{cell_hex}").reflect(); // the four substances
        // balance field is a real witnessed read off the ledger:
        var bal = -1;
        for (var i = 0; i < view.fields.length; i++)
            if (view.fields[i].key === "balance") bal = view.fields[i].value;
        // pack: 1 if found AND it's a Cell AND the title mentions "Cell"
        (found && view.kind === "Cell" && view.title.indexOf("Cell") === 0) ? 1 : 0;
    "#
    );
    let crawl_ok = rt.eval(&js_crawl).expect("eval (d.1) should succeed");
    assert_eq!(crawl_ok, Some(1), "JS crawled the live image and read a cell's substances");

    // (d.2) the frustum is cap-bounded: the cell observes ITSELF (it is on its own
    // ledger); an all-zero stranger id is NOT observable (absence, not forgery).
    let js_frustum = format!(
        r#"
        var c = deos.cell("{cell_hex}");
        var self_view = c.as("{cell_hex}");
        var sees_self = self_view.canObserve("{cell_hex}") ? 1 : 0;
        var stranger = "{stranger}";
        var sees_stranger = self_view.canObserve(stranger) ? 1 : 0;
        var stranger_reflect = self_view.reflect(stranger); // null — unobservable
        (sees_self === 1 && sees_stranger === 0 && stranger_reflect === null) ? 1 : 0;
    "#,
        stranger = "00".repeat(32),
    );
    let frustum_ok = rt.eval(&js_frustum).expect("eval (d.2) should succeed");
    assert_eq!(
        frustum_ok,
        Some(1),
        "the frustum is cap-bounded: self observable, a stranger absent (not forged)"
    );

    // The crawl is a READ — it committed NO turns (only the one inc did).
    let crawled = take_current_applet().expect("crawl applet present");
    assert_eq!(
        crawled.receipt_count(),
        1,
        "reflection is a READ: the crawl committed NO turns"
    );

    // ── (e) THE REFLECTION FAN-OUT — faces · affordances · snapshot/rewind · spotter ─
    let mut fanout = counter_applet(0xE8);
    fanout.fire("inc", 5).unwrap(); // model = 5, 1 receipt
    let fan_hex = fanout
        .cell()
        .as_bytes()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>();
    set_current_applet(fanout);

    // (e.1) present() → the moldable faces; every face is a distinct obs-projection.
    let js_present = format!(
        r#"
        var faces = deos.cell("{fan_hex}").present();
        var kinds = faces.map(function(f) {{ return f.kind; }});
        var has_raw = kinds.indexOf("raw-fields") >= 0;
        var has_graph = kinds.indexOf("graph") >= 0;
        var has_dv = kinds.indexOf("domain-visual") >= 0;
        var has_prov = kinds.indexOf("provenance") >= 0;
        // the DomainVisual face is the lifecycle SM, current = Live
        var dv = faces.filter(function(f){{return f.kind==="domain-visual";}})[0];
        var live = dv.body.current === "Live";
        // the Provenance face has 1 event (the one inc turn)
        var prov = faces.filter(function(f){{return f.kind==="provenance";}})[0];
        var one_event = prov.body.events.length === 1;
        (has_raw && has_graph && has_dv && has_prov && live && one_event) ? 1 : 0;
    "#
    );
    assert_eq!(
        rt.eval(&js_present).expect("eval (e.1)"),
        Some(1),
        "present() emits the four faces; DomainVisual=Live; Provenance has the inc turn"
    );

    // (e.2) affordances(viewer) → cap-gated message list. inc/dec require Signature;
    // reset requires Proof. A "signature" viewer sees inc+dec but NOT reset
    // (Proof incomparable to Signature); a "proof" viewer sees reset.
    let js_aff = r#"
        var c = deos.cell("CELL");
        var sig = c.affordances("signature").map(function(a){ return a.name; });
        var proof = c.affordances("proof").map(function(a){ return a.name; });
        var sig_ok = sig.indexOf("inc") >= 0 && sig.indexOf("dec") >= 0 && sig.indexOf("reset") < 0;
        var proof_ok = proof.indexOf("reset") >= 0;
        (sig_ok && proof_ok) ? 1 : 0;
    "#
    .replace("CELL", &fan_hex);
    assert_eq!(
        rt.eval(&js_aff).expect("eval (e.2)"),
        Some(1),
        "affordances(viewer) is cap-gated: a Signature viewer cannot see the Proof affordance"
    );

    // (e.3) snapshot / rewind — time-travel. Snapshot at model=5, advance to 15,
    // rewind, model is back to 5; the audit tape truncates (no phantom receipts).
    let js_tt = format!(
        r#"
        var app2 = deos.applet({{ affordances: ["inc"] }}); // re-bind the driver
        var snap = deos.world.snapshot();   // save model=5 (1 receipt)
        app2.inc(10);                        // model=15 (2 receipts)
        var mid = deos.cell("{fan_hex}").field("balance");
        deos.world.rewind(snap);             // restore model=5
        var after = deos.cell("{fan_hex}").field("balance");
        // mid had the inc's state-field at slot 0 = 15; after rewind slot0 = 5
        (mid !== null && after !== null) ? 1 : 0;
    "#
    );
    assert_eq!(rt.eval(&js_tt).expect("eval (e.3)"), Some(1), "snapshot/rewind round-trip");

    let fanout = take_current_applet().expect("fanout applet");
    // After the rewind the audit tape is back to the snapshot's receipt count (1).
    assert_eq!(
        fanout.receipt_count(),
        1,
        "rewind truncates the audit tape — time-travel leaves no phantom receipts"
    );
    assert_eq!(fanout.get_u64(0), 5, "the model rewound to the snapshot (5)");

    // (e.4) spotter — fuzzy search over every cell's faces finds the applet cell.
    set_current_applet(counter_applet(0xE9));
    let js_search = r#"
        var hits = deos.search("Cell");   // every cell's title is "Cell …"
        (hits.length >= 1 && hits[0].cell.length === 64) ? 1 : 0;
    "#;
    assert_eq!(
        rt.eval(js_search).expect("eval (e.4)"),
        Some(1),
        "the spotter finds cells by their reflective text"
    );
    let searched = take_current_applet().expect("search applet");
    assert_eq!(searched.receipt_count(), 0, "search is a READ: no turns committed");

    // ── (f) THE DRIVE PATH RUNS SYMBOLIC BY DEFAULT — defers the WITNESS, never a GATE ─
    let sym = counter_applet(0xF1);
    assert!(sym.is_symbolic(), "the applet drive path is Symbolic by default");
    set_current_applet(sym);
    let js_sym = r#"
        var app = deos.applet({ affordances: ["inc", "reset"] });
        app.inc(8);            // a Symbolic turn — witness deferred, state applies
        app.fire("reset", 0);  // reset requires Proof; held=Signature → REFUSED (gate runs)
        app.get(0);            // model = 8 (the Symbolic inc applied; reset refused)
    "#;
    assert_eq!(
        rt.eval(js_sym).expect("eval (f)"),
        Some(8),
        "Symbolic applies state (inc=8) AND still refuses the over-reach (reset)"
    );
    let sym = take_current_applet().expect("symbolic applet");
    assert!(
        sym.last_receipt_deferred(),
        "the committed turn DEFERRED its witness (DEFERRED_STATE_HASH) — Symbolic"
    );
    assert_eq!(sym.get_u64(0), 8, "the model is correct under Symbolic (witness deferred only)");
    assert_eq!(
        sym.receipt_count(),
        1,
        "exactly one turn committed (inc); the Proof-gated reset was refused — the GATE still ran"
    );

    // ── (g) THE VIEW LANGUAGE (slice 3) — a serializable element-tree (data, not gpui) ─
    set_current_applet(counter_applet(0xF2));
    let js_view = r#"
        var app = deos.applet({ affordances: ["inc"] });
        // a counter view: a column of [the count, a +1 button].
        var tree = deos.ui.vstack(
            deos.ui.text("Counter"),
            deos.ui.bind(function() { return app.get(0); }),  // signal binding → the model
            deos.ui.button("+1", "inc", 1)                     // onClick = a real turn
        );
        // assert the tree SHAPE
        var shape_ok = tree.kind === "vstack"
            && tree.children.length === 3
            && tree.children[0].kind === "text"
            && tree.children[1].kind === "bind"
            && tree.children[2].kind === "button"
            && tree.children[2].props.onClick.turn === "inc";
        // the bound value re-reads the model: 0 before, then fire the button's turn,
        // then 1 after (a real verified turn, then the binding re-reads).
        var before = tree.children[1].read();           // 0
        var handler = tree.children[2].props.onClick;
        app.fire(handler.turn, handler.arg);            // a REAL turn (model 0 -> 1)
        var after = tree.children[1].read();            // 1
        (shape_ok && before === 0 && after === 1) ? 1 : 0;
    "#;
    assert_eq!(
        rt.eval(js_view).expect("eval (g)"),
        Some(1),
        "the view-tree has the right shape; firing a bound handler commits a real turn; \
         the bound value re-reads correctly"
    );
    let viewed = take_current_applet().expect("view applet");
    assert_eq!(
        viewed.receipt_count(),
        1,
        "building the view-tree committed NOTHING; only firing the button's handler did (1 turn)"
    );
    assert_eq!(viewed.get_u64(0), 1, "the bound model reflects the fired turn");
}

#[test]
fn transclude_composes_two_applets_cap_gated_and_provenanced() {
    // Pure substance (no JS engine): the transclude path is on the applet handle.
    let mut host = counter_applet(0xD4);
    let mut guest = counter_applet(0xE5);

    // Advance each to a distinct model so the transclusion pins a real, dated surface.
    host.fire("inc", 11).unwrap();
    guest.fire("inc", 22).unwrap();
    guest.fire("inc", 1).unwrap(); // guest model = 23

    // (d) THE CAP-GATED, PROVENANCED COMPOSE — a verified finalized read, not a copy.
    let embed = host
        .transclude(&guest)
        .expect("transclusion of a finalized surface must succeed");

    assert!(embed.finalized(), "the embed is quorum-finalized");
    assert_eq!(embed.host, host.cell());
    assert_eq!(embed.source, guest.cell());
    assert_ne!(
        embed.content_hash(),
        [0u8; 32],
        "the embed pins a real content commitment (the anti-forge tooth)"
    );
    // The embed records WHICH applets it composes (host ⟵ guest): a provenanced
    // citation, not a detached copy.
    println!("transclusion badge: {}", embed.badge());

    // THE LOAD-BEARING ANTI-FORGE PROPERTY: the cited content_hash == blake3 of the
    // GUEST's committed surface (content → commitment → receipt → quorum verified by
    // the include). The transclusion pins the source's content; a tampered surface
    // would fail the include's verify. This is NOT a raw copy that can silently
    // diverge.
    let recomputed = blake3::hash(&embed.quoted);
    assert_eq!(
        *recomputed.as_bytes(),
        embed.content_hash(),
        "content-bound provenance: content_hash == blake3(quoted source surface)"
    );
    // And the quoted surface IS the guest's live model: count = 23 (packed little-
    // endian at slot 0) appears in the surface bytes — the embed reflects the source's
    // real, dated state, not an empty or stale copy.
    assert!(
        embed.quoted.windows(8).any(|w| w == 23u64.to_le_bytes()),
        "the embed quotes the guest's ACTUAL committed model (count=23)"
    );
}
