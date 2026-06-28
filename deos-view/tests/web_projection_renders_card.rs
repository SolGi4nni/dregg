//! THE WEB PROJECTION, IN THE TEST SUITE: the SAME deos-js card view-tree the native
//! render proof paints to gpui pixels renders — gpui-FREE — to a browser-loadable HTML
//! string. Same DATA, two renderers ⇒ the card is renderer-INDEPENDENT.
//!
//! This test is gpui-FREE and deos-js-FREE: it runs under
//! `cargo test -p deos-view --no-default-features --features web` in the tiny graph
//! (serde only). It is the web mirror of `renders_applet_view_to_pixels` (which bakes the
//! native gpui PNGs): there, `ViewNode → gpui pixels`; here, `ViewNode → HTML`.
//!
//! It is `#![cfg(feature = "web")]` so the default (native) `cargo test` — which does NOT
//! enable `web` — skips it cleanly rather than failing to find the gpui-free renderer.
#![cfg(feature = "web")]

use deos_view::{parse_view_tree, render_card_document, render_html};

/// The EXACT `JSON.stringify(tree)` the SpiderMonkey engine produces for the counter card
/// the native test drives (`deos.ui.vstack(text, bind, button)`; `button` emits
/// `onClick:{turn,arg}`; the tagged `bind` emits `slot`+`label`). Byte-for-byte the engine
/// output the bridge hands the parser — the web renderer consumes the SAME serialized tree.
const COUNTER_CARD_JSON: &str = r#"{
  "kind": "vstack",
  "props": {},
  "children": [
    { "kind": "text", "props": { "text": "Counter applet" } },
    { "kind": "bind", "props": { "slot": 0, "label": "count: " } },
    { "kind": "button", "props": { "label": "+1", "onClick": { "turn": "inc", "arg": 1 } } }
  ]
}"#;

#[test]
fn counter_card_view_tree_renders_to_browser_loadable_html_with_a_live_bind() {
    // ── Parse the engine JSON with the SAME parser the native renderer uses ──────────
    let tree = parse_view_tree(COUNTER_CARD_JSON).expect("parse the engine counter card view-tree");

    // ── Frame 0: the un-driven start (count = 0) ─────────────────────────────────────
    let frag0 = render_html(&tree, &[0]);
    assert!(
        frag0.contains(r#"<span class="deos-text">Counter applet</span>"#),
        "the text node painted as a deos-text span"
    );
    assert!(
        frag0.contains(r#"<span class="deos-bind" data-slot="0""#)
            && frag0.contains(">count: 0</span>"),
        "the bind painted its live value 0 AND carries its model slot (the signal source): {frag0}"
    );
    // THE AFFORDANCE SURVIVED THE WEB PROJECTION — the button carries the engine's
    // `{turn:"inc", arg:1}` payload (the exact thing the native Button fires via
    // `Applet::fire`). Without the `onClick` parse fix this would have been turn="" arg=0.
    assert!(
        frag0.contains(r#"<button class="deos-button" data-turn="inc" data-arg="1">+1</button>"#),
        "the button carries the REAL affordance payload into the DOM"
    );

    // ── Frame 1: the IDENTICAL tree at the post-`inc` value (count = 1) ──────────────
    // This is the web `bind` re-paint: same view-tree, advanced model snapshot — the
    // SolidJS-shaped signal re-render, mirroring the native `bind` re-reading the ledger.
    let frag1 = render_html(&tree, &[1]);
    assert!(
        frag1.contains("count: 1"),
        "frame 1 paints the advanced bound value 1"
    );
    assert_ne!(
        frag0, frag1,
        "the two frames DIFFER — the bound value visibly re-painted"
    );

    // ── The full document is a real, browser-loadable file ───────────────────────────
    let doc = render_card_document("deos counter card", &tree, &[0]);
    assert!(
        doc.starts_with("<!doctype html>"),
        "a complete HTML document"
    );
    assert!(doc.contains("<title>deos counter card</title>"));
    assert!(
        doc.contains(".deos-button{"),
        "the cockpit-dark card styling is inlined"
    );
    assert!(
        doc.contains("deos-affordance"),
        "the affordance wire (the click → CustomEvent seam) is present"
    );
}

#[test]
fn web_renderer_maps_every_node_kind() {
    // The inspector-shaped card exercises text/bind/row/table/button — every container +
    // leaf the web vocabulary handles, mirroring the native renderer's node match arms.
    let json = r#"{
      "kind": "vstack", "props": {}, "children": [
        { "kind": "text", "props": { "text": "Cell — inspector" } },
        { "kind": "table", "props": {}, "children": [
            { "kind": "row", "props": {}, "children": [
                { "kind": "text", "props": { "text": "count" } },
                { "kind": "bind", "props": { "slot": 0, "label": "" } }
            ] }
        ] },
        { "kind": "list", "props": {}, "children": [
            { "kind": "input", "props": { "bindView": "draft" } }
        ] },
        { "kind": "button", "props": { "label": "+1", "onClick": { "turn": "inc", "arg": 1 } } }
      ]
    }"#;
    let tree = parse_view_tree(json).expect("parse the inspector card view-tree");
    let html = render_html(&tree, &[42]);

    for needle in [
        "deos-vstack",
        "deos-table",
        "deos-row",
        "deos-list",
        r#"class="deos-bind" data-slot="0""#,
        ">42<",
        r#"class="deos-input" data-bind-view="draft""#,
        r#"data-turn="inc""#,
    ] {
        assert!(html.contains(needle), "the web renderer emitted `{needle}`");
    }
}
