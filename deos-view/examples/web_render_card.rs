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

use deos_view::{
    GalleryCard, parse_view_tree, render_card_document, render_card_live_document,
    render_gallery_document, render_html, render_inspector_live_document,
    render_tally_live_document,
};

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

/// THE REFLECTIVE-INSPECTOR CARD's view-tree — byte-for-byte the shape
/// `wasm/src/bindings_card.rs`'s `InspectorWorld::view_tree_json` generates from a focused
/// cell's REAL moldable faces (`deos_reflect::ReflectedCell::raw_fields` + `AffordanceSurface`),
/// for the default-seeded cell (`state[0]=7`, `state[1]=42`, `state[2]=100`). It is the
/// substance-agnostic core of the native `deos_js::inspector_card::inspector_view_for`, so this
/// is the SAME view-tree the cockpit inspector paints — fed to the WEB renderer to prove the
/// reflective surface is renderer-independent. A titled column with:
///   - a "Cell State" section: a live `Bind` row per revealed scalar slot (`state[0..2]`,
///     re-read off the ledger so a fired affordance updates the row) + a labeled `Text` per
///     structural substance (balance, nonce, id, caps, lifecycle, …);
///   - an "Affordances" section: a cap-gated `Button` per fireable affordance
///     (`tick`→state[0], `add`→state[1], `score`→state[2]).
/// (The structural-row VALUES below — balance/nonce/id — are the live in-tab cell's, re-read
/// from the wasm `InspectorWorld` after boot; the static bake here is the first paint.)
const INSPECTOR_CARD_JSON: &str = r#"{
  "kind": "vstack",
  "props": {},
  "children": [
    { "kind": "text", "props": { "text": "Inspector" } },
    { "kind": "vstack", "props": {}, "children": [
        { "kind": "text", "props": { "text": "Cell State" } },
        { "kind": "text", "props": { "text": "balance: 1000000" } },
        { "kind": "text", "props": { "text": "nonce: 3" } },
        { "kind": "text", "props": { "text": "capabilities: 0" } },
        { "kind": "text", "props": { "text": "has_delegate: false" } },
        { "kind": "text", "props": { "text": "has_program: false" } },
        { "kind": "text", "props": { "text": "lifecycle: live" } },
        { "kind": "bind", "props": { "slot": 0, "label": "state[0]: " } },
        { "kind": "bind", "props": { "slot": 1, "label": "state[1]: " } },
        { "kind": "bind", "props": { "slot": 2, "label": "state[2]: " } }
    ] },
    { "kind": "vstack", "props": {}, "children": [
        { "kind": "text", "props": { "text": "Affordances" } },
        { "kind": "button", "props": { "label": "tick", "on_click": { "turn": "tick", "arg": 1 } } },
        { "kind": "button", "props": { "label": "add", "on_click": { "turn": "add", "arg": 1 } } },
        { "kind": "button", "props": { "label": "score", "on_click": { "turn": "score", "arg": 1 } } }
    ] }
  ]
}"#;

/// THE TALLY-BOARD CARD's view-tree — byte-for-byte the shape `wasm/src/bindings_card.rs`'s
/// `TallyWorld::view_tree_json` generates: a titled column over a `table` of `row`s, one per
/// named tally (apples/oranges/pears = slots 0/1/2). Each `row` carries a `text` label, a live
/// `bind` of its slot, and `+1`/`−1` affordance `button`s (`{turn:inc|dec, arg:slot}`). It
/// exercises the view-tree's LAYOUT nodes (`Row`/`Table`) and a multi-affordance row — surfaces
/// neither the counter nor the inspector touched — proving the FULL ViewNode vocabulary is
/// renderer-independent (the SAME tree the cockpit walks into gpui widgets, fed to the WEB
/// renderer). The static seeds below (3/1/4) are the first paint; the in-tab `TallyWorld`
/// re-reads the live values after boot.
const TALLY_CARD_JSON: &str = r#"{
  "kind": "vstack",
  "props": {},
  "children": [
    { "kind": "text", "props": { "text": "Tally board" } },
    { "kind": "table", "props": {}, "children": [
        { "kind": "row", "props": {}, "children": [
            { "kind": "text", "props": { "text": "apples: " } },
            { "kind": "bind", "props": { "slot": 0, "label": "" } },
            { "kind": "button", "props": { "label": "+1", "on_click": { "turn": "inc", "arg": 0 } } },
            { "kind": "button", "props": { "label": "−1", "on_click": { "turn": "dec", "arg": 0 } } }
        ] },
        { "kind": "row", "props": {}, "children": [
            { "kind": "text", "props": { "text": "oranges: " } },
            { "kind": "bind", "props": { "slot": 1, "label": "" } },
            { "kind": "button", "props": { "label": "+1", "on_click": { "turn": "inc", "arg": 1 } } },
            { "kind": "button", "props": { "label": "−1", "on_click": { "turn": "dec", "arg": 1 } } }
        ] },
        { "kind": "row", "props": {}, "children": [
            { "kind": "text", "props": { "text": "pears: " } },
            { "kind": "bind", "props": { "slot": 2, "label": "" } },
            { "kind": "button", "props": { "label": "+1", "on_click": { "turn": "inc", "arg": 2 } } },
            { "kind": "button", "props": { "label": "−1", "on_click": { "turn": "dec", "arg": 2 } } }
        ] }
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

    // ── 4. Bake the reflective inspector card (the three bound slots: 7, 42, 100) ─────
    // bind_values are in tree-walk order: the three `state[i]` Bind rows → [7, 42, 100].
    let html_insp = render_card_document("deos inspector card", &inspector, &[7, 42, 100]);
    let pi = out.join("inspector.html");
    std::fs::write(&pi, &html_insp).expect("write inspector.html");

    // ── PROVE the reflective projection: the inspector's faces SURVIVED the web render ─
    // The RawFields face's structural rows + the live `Bind` rows + the cap-gated affordance
    // `Button`s all paint, carrying their real `{slot}` / `{turn, arg}` contracts.
    let frag_insp = render_html(&inspector, &[7, 42, 100]);
    assert!(
        frag_insp.contains("Inspector")
            && frag_insp.contains("Cell State")
            && frag_insp.contains("Affordances"),
        "the inspector's section titles paint (RawFields + Affordances faces)"
    );
    assert!(
        frag_insp.contains("state[0]: 7")
            && frag_insp.contains("state[1]: 42")
            && frag_insp.contains("state[2]: 100"),
        "the three live Bind rows paint their seeded slot values"
    );
    assert!(
        frag_insp.contains("data-slot=\"0\"")
            && frag_insp.contains("data-slot=\"1\"")
            && frag_insp.contains("data-slot=\"2\""),
        "each Bind row carries its own model slot (the multi-field signal sources)"
    );
    assert!(
        frag_insp.contains("balance: 1000000") && frag_insp.contains("lifecycle: live"),
        "the structural substances (balance, lifecycle) render as static rows"
    );
    assert!(
        frag_insp.contains("data-turn=\"tick\"")
            && frag_insp.contains("data-turn=\"add\"")
            && frag_insp.contains("data-turn=\"score\""),
        "each cap-gated affordance becomes a Button carrying its `{{turn}}` payload"
    );

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
    let plive = dist.join("counter.html");
    std::fs::write(&plive, &live).expect("write the live counter.html");

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

    // ── 6. Bake the LIVE REFLECTIVE-INSPECTOR page — a cockpit surface, browser-native ──
    // The SAME gpui-free web renderer paints the inspector card's view-tree (Cell State binds
    // + structural rows + Affordance buttons), the bootstrap mints an in-tab `InspectorWorld`
    // (the wasm analog of the native inspector over a live World) seeded to [7, 42, 100], binds
    // `window.__deosCard`, and re-paints each bound row from the committed ledger. Clicking an
    // affordance (`tick`/`add`/`score`) fires a REAL cap-gated verified turn over that executor
    // and the bound field re-paints — a reflective cockpit surface running in a TAB.
    let live_insp = render_inspector_live_document(
        "deos reflective-inspector card — live",
        &inspector,
        /*bind_values (tree-walk order)*/ &[7, 42, 100],
        /*seeds*/ &[7, 42, 100],
        "./pkg/dregg_wasm.js",
    );
    let plive_insp = dist.join("inspector.html");
    std::fs::write(&plive_insp, &live_insp).expect("write the live inspector.html");

    // ── PROVE the live inspector page is wired (not merely written) ───────────────────
    assert!(
        live_insp.contains("./pkg/dregg_wasm.js")
            && live_insp.contains("import init, { InspectorWorld }"),
        "the live inspector page imports the wasm bundle's `init` + `InspectorWorld`"
    );
    assert!(
        live_insp.contains("new InspectorWorld([7n, 42n, 100n])")
            && live_insp.contains("window.__deosCard = card"),
        "the live inspector page mints the in-tab reflective executor seeded to the bound slots"
    );
    assert!(
        live_insp.contains("card.read(slot)"),
        "the live inspector re-paints each bound row from ITS slot off the committed ledger"
    );
    assert!(
        live_insp.contains("card.fire(turn, arg)"),
        "the affordance wire fires a click as a real verified turn into the in-tab executor"
    );
    assert!(
        live_insp.contains("data-slot=\"0\"")
            && live_insp.contains("data-slot=\"1\"")
            && live_insp.contains("data-slot=\"2\"")
            && live_insp.contains("data-turn=\"tick\""),
        "the SAME inspector markup carries the multi-slot bind + affordance contract the wire drives"
    );

    // ── 6b. Bake the LIVE TALLY-BOARD page — the FULL ViewNode vocabulary, browser-native ──
    // The SAME gpui-free web renderer paints the board's view-tree (a `Table` of `Row`s, each a
    // named tally with its live `Bind` value + `+1`/`−1` `Button`s — the LAYOUT nodes the
    // counter/inspector never exercised). The bootstrap mints an in-tab `TallyWorld` seeded to
    // [3, 1, 4], binds `window.__deosCard`, and re-paints each bound row from the committed
    // ledger. Clicking a `+1`/`−1` fires a REAL cap-gated verified turn over that executor (its
    // `data-arg` is the tally's SLOT, `data-turn` the direction) and that one row re-paints.
    let tally = parse_view_tree(TALLY_CARD_JSON).expect("parse the tally card view-tree");
    let live_tally = render_tally_live_document(
        "deos tally-board card — live",
        &tally,
        /*bind_values (tree-walk order)*/ &[3, 1, 4],
        /*seeds*/ &[3, 1, 4],
        "./pkg/dregg_wasm.js",
    );
    let plive_tally = dist.join("tally.html");
    std::fs::write(&plive_tally, &live_tally).expect("write the live tally.html");

    // ── PROVE the tally board exercises the LAYOUT vocabulary + is wired (not merely written) ─
    let frag_tally = render_html(&tally, &[3, 1, 4]);
    assert!(
        frag_tally.contains("deos-table") && frag_tally.matches("deos-row").count() == 3,
        "the board renders a Table of three Rows (the layout vocabulary)"
    );
    assert!(
        frag_tally.contains("apples: ")
            && frag_tally.contains("oranges: ")
            && frag_tally.contains("pears: "),
        "each Row paints its named tally's label"
    );
    assert!(
        frag_tally.contains("data-slot=\"0\">3</span>")
            && frag_tally.contains("data-slot=\"1\">1</span>")
            && frag_tally.contains("data-slot=\"2\">4</span>"),
        "each Row's Bind paints its slot's seeded value (3 / 1 / 4)"
    );
    assert!(
        frag_tally.matches("data-turn=\"inc\"").count() == 3
            && frag_tally.matches("data-turn=\"dec\"").count() == 3,
        "each Row carries BOTH affordances (+1 inc / −1 dec) — a multi-affordance row"
    );
    assert!(
        frag_tally.contains("data-arg=\"0\"")
            && frag_tally.contains("data-arg=\"1\"")
            && frag_tally.contains("data-arg=\"2\""),
        "each affordance carries its tally's SLOT index as `data-arg`"
    );
    assert!(
        live_tally.contains("import init, { TallyWorld }")
            && live_tally.contains("new TallyWorld([3n, 1n, 4n])")
            && live_tally.contains("card.read(slot)"),
        "the live tally page imports + mints the in-tab executor and re-paints each row off its slot"
    );

    // ── 7. Bake the GALLERY / card-picker as the served home page (`/` = index.html) ──
    // Without a front door a visitor lands on one card and never finds the others. This is
    // a plain-HTML (no-wasm) landing of clickable tiles, one per live card — the
    // "click around, no comprehension needed" entry that opens each real card page.
    let gallery = render_gallery_document(
        "deos — live cards in a browser",
        &[
            GalleryCard {
                href: "counter.html",
                name: "Counter",
                blurb: "A deos-js counter card. Click +1 and the bound count advances — each \
                        click is a SetField + IncrementNonce verified turn over an in-tab \
                        executor, leaving a receipt.",
            },
            GalleryCard {
                href: "inspector.html",
                name: "Reflective Inspector",
                blurb: "A cockpit surface, in a tab. A focused cell's real moldable faces \
                        (state rows + affordances) render live; clicking tick/add/score fires a \
                        cap-gated verified turn and the bound field re-paints.",
            },
            GalleryCard {
                href: "tally.html",
                name: "Tally Board",
                blurb: "A table of named tallies, each a row with a live count and +1/−1 \
                        buttons. The full ViewNode layout vocabulary (Row + Table + a \
                        multi-affordance row); every click is a verified turn moving one tally.",
            },
        ],
    );
    let pgallery = dist.join("index.html");
    std::fs::write(&pgallery, &gallery).expect("write the gallery index.html");

    // ── PROVE the gallery is wired (not merely written) ───────────────────────────────
    assert!(
        gallery.contains("href=\"counter.html\"")
            && gallery.contains("href=\"inspector.html\"")
            && gallery.contains("href=\"tally.html\""),
        "the gallery links to ALL THREE live card pages (the card-picker)"
    );
    assert!(
        gallery.contains("Counter")
            && gallery.contains("Reflective Inspector")
            && gallery.contains("Tally Board"),
        "the gallery names all three cards"
    );

    eprintln!("deos-view web projection baked (gpui-free):");
    eprintln!("  counter @ count=0    : {}", p0.display());
    eprintln!("  counter @ count=1    : {}", p1.display());
    eprintln!("  inspector card       : {}", pi.display());
    eprintln!("  LIVE gallery (home)  : {}", pgallery.display());
    eprintln!("  LIVE counter page    : {}", plive.display());
    eprintln!("  LIVE inspector page  : {}", plive_insp.display());
    eprintln!("  LIVE tally page      : {}", plive_tally.display());
    eprintln!();
    eprintln!("To serve the LIVE deos (a card firing real cap-gated verified turns in a TAB):");
    eprintln!("  1. wasm-pack build wasm --target web --out-dir pkg --release");
    eprintln!("  2. cp -R ../wasm/pkg {}/pkg", dist.display());
    eprintln!(
        "  3. (cd {} && python3 -m http.server 8000)  # open http://localhost:8000 (the gallery)",
        dist.display()
    );
    eprintln!("     The gallery links to /counter.html and /inspector.html (the LIVE cards).");
    eprintln!(
        "Open the static .html files directly; the LIVE pages must be SERVED (module + .wasm fetch)."
    );
}
