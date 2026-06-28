//! THE CONSUMER-DELIGHT layer, IN THE WEB PROJECTION: the short-hash / avatar `bind` format,
//! the LIVE value→word `pill`, and progressive disclosure all render — gpui-FREE — into the
//! browser HTML, the SAME `crate::fmt` mapping the native/discord renderers use. This is the
//! proof that the rendering-layer delight is renderer-INDEPENDENT: a card sets a prop and every
//! projection inherits it.
//!
//! `#![cfg(feature = "web")]` so the default (native) test run skips it; run it with
//! `cargo test -p deos-view --features web`.
#![cfg(feature = "web")]

use deos_view::{disclose, parse_view_tree, render_card_document, render_html, Disclosure};

/// The dev-y 20-digit seller key from the screenshot — a `bind` tagged `fmt:"hash"` paints it
/// SHORT (`0x…`) instead of `seller key · 10083942588892332568`.
#[test]
fn an_opaque_key_bind_renders_short_not_a_wall_of_digits() {
    let json = r#"{ "kind":"bind", "props":{ "slot":3, "label":"seller key · ", "fmt":"hash" } }"#;
    let tree = parse_view_tree(json).expect("parse the hash bind");
    let html = render_html(&tree, &[10083942588892332568]);

    assert!(
        !html.contains("10083942588892332568"),
        "the raw 20-digit decimal is GONE: {html}"
    );
    assert!(
        html.contains("0x"),
        "a friendly truncated hex took its place: {html}"
    );
    // The span carries data-fmt + data-label so the in-tab re-read re-formats identically.
    assert!(
        html.contains(r#"data-fmt="hex""#),
        "carries the fmt for the live re-read"
    );
    assert!(
        html.contains(r#"data-label="seller key · ""#),
        "carries the label for the live re-read"
    );

    // The avatar variant: a deterministic emoji handle, no raw digits.
    let id = parse_view_tree(r#"{ "kind":"bind", "props":{ "slot":0, "fmt":"id" } }"#).unwrap();
    let id_html = render_html(&id, &[10083942588892332568]);
    assert!(
        id_html.contains('-'),
        "the avatar handle is adjective-noun: {id_html}"
    );
}

/// A LIVE pill carries its bound slot + cases JSON and first-paints the value-0 word — the
/// static phase-word cure.
#[test]
fn a_live_pill_renders_its_bound_cases() {
    let json = r#"{ "kind":"pill", "props":{ "text":"…", "tag":"muted", "slot":7, "cases":[
        { "value":0, "label":"COMMIT", "tag":"warn" },
        { "value":1, "label":"REVEAL", "tag":"accent" },
        { "value":2, "label":"RESOLVED", "tag":"good" } ] } }"#;
    let tree = parse_view_tree(json).expect("parse the live pill");
    let html = render_html(&tree, &[]);

    assert!(html.contains(r#"data-slot="7""#), "the pill binds its slot");
    assert!(
        html.contains("data-cases="),
        "the pill carries its value→word cases for the live re-read"
    );
    assert!(
        html.contains(">COMMIT<"),
        "first paint shows the value-0 word, not the placeholder"
    );
    assert!(
        html.contains(r#"data-tag="warn""#),
        "first paint carries the value-0 color"
    );

    // The document wires the live pill repaint + the shared fmt mirror.
    let doc = render_card_document("delight", &tree, &[]);
    assert!(
        doc.contains("function deosRepaintPills"),
        "the live-pill repaint wire is present"
    );
    assert!(
        doc.contains("function deosFmt"),
        "the shared fmt JS mirror is inlined"
    );
}

/// Progressive disclosure over the web projection: at `simple` the adept-only raw detail is
/// absent from the HTML; at `adept` it appears. One card, two projections.
#[test]
fn disclosure_filters_the_web_projection() {
    let json = r#"{ "kind":"vstack", "props":{}, "children":[
        { "kind":"text", "props":{ "text":"Friendly summary" } },
        { "kind":"text", "props":{ "text":"INTERNAL slot dump", "adept":true } } ] }"#;
    let card = parse_view_tree(json).expect("parse the disclosable card");

    let simple = render_html(&disclose(&card, Disclosure::Simple), &[]);
    assert!(simple.contains("Friendly summary"));
    assert!(
        !simple.contains("INTERNAL slot dump"),
        "simple hides the adept detail: {simple}"
    );

    let adept = render_html(&disclose(&card, Disclosure::Adept), &[]);
    assert!(adept.contains("Friendly summary"));
    assert!(
        adept.contains("INTERNAL slot dump"),
        "adept reveals the bones"
    );
}
