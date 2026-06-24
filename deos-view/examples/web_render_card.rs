//! THE WEB PROJECTION, BY BAKING: the SAME deos-js card view-tree that the native
//! `renders_applet_view_to_pixels` test paints to gpui pixels renders — gpui-FREE — to a
//! browser-loadable `.html`. Same DATA, two renderers ⇒ the card is renderer-INDEPENDENT.
//!
//! This mirrors the native render proof, but through the WEB renderer:
//!
//!   1. Take the EXACT JSON the SpiderMonkey engine produces for the counter card
//!      (`deos.ui.vstack(text, bind, button)`, the same shape the bridge extracts) and
//!      parse it with the SAME `parse_view_tree` the native path uses → one `ViewNode`.
//!   2. Render that tree to HTML at the bound value 0 (count: 0) → write `counter-0.html`.
//!   3. Render the IDENTICAL tree at the bound value 1 (the value a fired `inc` turn would
//!      leave) → write `counter-1.html`. The two documents DIFFER in exactly the bound
//!      span — the web `bind` re-painted, just as the native `bind` re-reads the ledger.
//!   4. Also bake the inspector-shaped card (a table of cell fields + an affordance row)
//!      → `inspector.html`, exercising every node kind through the web vocabulary.
//!
//! No gpui, no SpiderMonkey: this whole bake compiles + runs in the tiny `web` graph.
//! Open any written `.html` in a browser — the SAME card paints.

use std::path::PathBuf;

use deos_view::{parse_view_tree, render_card_document, render_card_live_document, render_html};

/// The EXACT `JSON.stringify(tree)` shape the SpiderMonkey engine produces for the
/// counter card the native test drives:
///
/// ```js
/// var b = deos.ui.bind(function(){ return app.get(0); });
/// b.props.slot = 0; b.props.label = "count: ";
/// deos.ui.vstack(deos.ui.text("Counter applet"), b, deos.ui.button("+1","inc",1))
/// ```
///
/// `deos.ui.button` emits `props.onClick = { turn, arg }`; `text` emits `props.text`; the
/// tagged `bind` emits `props.slot` + `props.label`. This is byte-for-byte the engine
/// output the bridge hands the parser — we render the SAME serialized tree on the web.
const COUNTER_CARD_JSON: &str = r#"{
  "kind": "vstack",
  "props": {},
  "children": [
    { "kind": "text", "props": { "text": "Counter applet" } },
    { "kind": "bind", "props": { "slot": 0, "label": "count: " } },
    { "kind": "button", "props": { "label": "+1", "onClick": { "turn": "inc", "arg": 1 } } }
  ]
}"#;

/// An inspector-shaped card (the moldable `present()` faces the inspector_card surfaces):
/// a labelled field table + an affordance button row. Exercises text/bind/row/table/list.
const INSPECTOR_CARD_JSON: &str = r#"{
  "kind": "vstack",
  "props": {},
  "children": [
    { "kind": "text", "props": { "text": "Cell 0xF2 — inspector" } },
    { "kind": "table", "props": {}, "children": [
        { "kind": "row", "props": {}, "children": [
            { "kind": "text", "props": { "text": "count" } },
            { "kind": "bind", "props": { "slot": 0, "label": "" } }
        ] },
        { "kind": "row", "props": {}, "children": [
            { "kind": "text", "props": { "text": "authority" } },
            { "kind": "text", "props": { "text": "Signature" } }
        ] }
    ] },
    { "kind": "row", "props": {}, "children": [
        { "kind": "button", "props": { "label": "+1", "onClick": { "turn": "inc", "arg": 1 } } }
    ] }
  ]
}"#;

fn out_dir() -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/web-out");
    std::fs::create_dir_all(&dir).expect("create web-out dir");
    dir
}

fn main() {
    let out = out_dir();

    // ── 1. Parse the EXACT engine JSON with the SAME parser the native renderer uses ──
    let counter = parse_view_tree(COUNTER_CARD_JSON).expect("parse the counter card view-tree");
    let inspector =
        parse_view_tree(INSPECTOR_CARD_JSON).expect("parse the inspector card view-tree");

    // ── 2. Render the counter at the bound value 0 (the un-driven start) ─────────────
    let html0 = render_card_document("deos counter card", &counter, &[0]);
    let p0 = out.join("counter-0.html");
    std::fs::write(&p0, &html0).expect("write counter-0.html");

    // ── 3. Render the IDENTICAL tree at the bound value 1 (post-`inc`) ───────────────
    // This is the web `bind` re-paint: same view-tree, advanced model snapshot.
    let html1 = render_card_document("deos counter card", &counter, &[1]);
    let p1 = out.join("counter-1.html");
    std::fs::write(&p1, &html1).expect("write counter-1.html");

    // ── 4. Bake the inspector card (count = 7, to show the bound field) ──────────────
    let html_insp = render_card_document("deos inspector card", &inspector, &[7]);
    let pi = out.join("inspector.html");
    std::fs::write(&pi, &html_insp).expect("write inspector.html");

    // ── PROVE the projection, not merely write it ────────────────────────────────────
    // The bound value PAINTS (count: 0 vs count: 1) and the affordance payload SURVIVED
    // the web projection (the button carries the engine's `{turn:"inc", arg:1}`).
    let frag0 = render_html(&counter, &[0]);
    let frag1 = render_html(&counter, &[1]);
    assert!(
        frag0.contains("count: 0"),
        "frame 0 paints the bound value 0"
    );
    assert!(
        frag1.contains("count: 1"),
        "frame 1 paints the bound value 1"
    );
    assert_ne!(
        frag0, frag1,
        "the two frames DIFFER — the bound value re-painted"
    );
    assert!(
        frag0.contains("data-turn=\"inc\"") && frag0.contains("data-arg=\"1\""),
        "the button carries the REAL affordance payload {{turn:inc, arg:1}} into the DOM"
    );
    assert!(
        frag0.contains("data-slot=\"0\""),
        "the bind carries its model slot (the signal source a browser re-read refreshes)"
    );

    // ── 5. Bake the LIVE counter page — the served, browser-native deos ──────────────
    // This page loads the playground wasm bundle (`./pkg/dregg_wasm.js`), mints an in-tab
    // `CardWorld` (the wasm analog of the native `Applet`), binds it to `window.__deosCard`,
    // and every `+1` click fires a REAL cap-gated verified turn over that embedded executor
    // — the bound value updating from the COMMITTED ledger, with a live receipt count. It
    // is baked into a `dist/` dir; the `pkg/` (wasm bundle) is copied in beside it so the
    // page is self-contained when served (`python3 -m http.server` from `dist/`).
    let dist = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/web-out/dist");
    std::fs::create_dir_all(&dist).expect("create dist dir");
    let live = render_card_live_document(
        "deos counter card — live",
        &counter,
        /*slot*/ 0,
        /*initial*/ 0,
        "./pkg/dregg_wasm.js",
    );
    let plive = dist.join("index.html");
    std::fs::write(&plive, &live).expect("write the live index.html");

    // ── PROVE the live page is wired (not merely written) ────────────────────────────
    assert!(
        live.contains("./pkg/dregg_wasm.js") && live.contains("import init, { CardWorld }"),
        "the live page imports the wasm bundle's `init` + `CardWorld`"
    );
    assert!(
        live.contains("new CardWorld(0, 0n)") && live.contains("window.__deosCard = card"),
        "the live page mints the in-tab verified executor and binds it for the affordance wire"
    );
    assert!(
        live.contains("card.fire(turn, arg)"),
        "the affordance wire fires the click as a real verified turn into the in-tab executor"
    );
    assert!(
        live.contains("data-turn=\"inc\"") && live.contains("data-slot=\"0\""),
        "the SAME card markup carries the affordance + bind contract the wire drives"
    );

    eprintln!("deos-view web projection baked (gpui-free):");
    eprintln!("  counter @ count=0 : {}", p0.display());
    eprintln!("  counter @ count=1 : {}", p1.display());
    eprintln!("  inspector card    : {}", pi.display());
    eprintln!("  LIVE counter page : {}", plive.display());
    eprintln!();
    eprintln!("To serve the LIVE deos (a card firing real cap-gated verified turns in a TAB):");
    eprintln!("  1. wasm-pack build wasm --target web --out-dir pkg --release");
    eprintln!("  2. cp -R ../wasm/pkg {}/pkg", dist.display());
    eprintln!(
        "  3. (cd {} && python3 -m http.server 8000)  # then open http://localhost:8000",
        dist.display()
    );
    eprintln!("Open the static .html files directly; the LIVE page must be SERVED (module + .wasm fetch).");
}
