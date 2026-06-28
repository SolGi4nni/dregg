//! The **web renderer** — walk the SAME deos-js view-tree into an HTML/DOM string.
//!
//! This is the *web projection* of the reflective cockpit. The native renderer
//! ([`crate::render`], gpui-gated) turns a [`ViewNode`] into gpui-component widgets;
//! THIS renderer turns the IDENTICAL [`ViewNode`] into HTML. Same data, two renderers
//! — the card is renderer-INDEPENDENT. It paints in a browser, not just the native
//! cockpit.
//!
//! It is gpui-FREE and deos-js-FREE: it depends on nothing but [`crate::tree`] (which
//! is `serde` only). So `cargo build -p deos-view --no-default-features --features web`
//! compiles a tiny graph — no GPU, no SpiderMonkey — and the `web_render_card` example
//! bakes a browser-loadable `.html`.
//!
//! ## The vocabulary mirrors the gpui renderer one-for-one
//!
//! | view-tree node      | gpui ([`crate::render`])    | web (here)                              |
//! |---------------------|------------------------------|-----------------------------------------|
//! | `vstack(...kids)`   | `v_flex().gap_2().p_3()`     | `<div class="deos-vstack">`             |
//! | `row(...kids)`      | `h_flex().gap_2()`           | `<div class="deos-row">`                |
//! | `text(s)`           | `Label`                      | `<span class="deos-text">`              |
//! | `bind{slot,label}`  | bold `Label`, live re-read   | `<span class="deos-bind" data-slot>`    |
//! | `button{label,...}` | `Button`, onClick fires turn | `<button data-turn data-arg>`           |
//! | `input{bindView}`   | bordered draft field         | `<span class="deos-input">`             |
//! | `list` / `table`    | `v_flex` of children         | `<div class="deos-list/table">`         |
//!
//! ## What is real vs. the seam
//!
//! - **Real here:** the SAME serializable [`ViewNode`] the SpiderMonkey engine produced
//!   (parsed by [`crate::parse_view_tree`]) walks into HTML; a `bind` carries its live
//!   value (read off the applet ledger and passed in) AND the `data-slot` it re-reads; a
//!   `button` carries its affordance `{turn, arg}` as `data-turn`/`data-arg` — the exact
//!   payload a click must fire. The produced document is a real, browser-loadable file.
//! - **The live turn (seam CLOSED):** a browser button-click fires its `{turn, arg}` as
//!   a REAL cap-gated verified turn over an in-tab executor. The executor is the wasm
//!   `CardWorld` (`wasm/src/bindings_card.rs`) — the wasm analog of the native
//!   `Applet::fire` (the SAME `SetField + IncrementNonce` over the embedded `DreggEngine`,
//!   leaving a receipt). A page binds a `CardWorld` to `window.__deosCard`; the [`JS`]
//!   wire calls `__deosCard.fire(turn, arg)` on click and re-paints every `data-slot`
//!   bind from the committed model (`CardWorld.read()` — the witnessed re-read). With NO
//!   `__deosCard` bound (a static bake) the click still emits the `deos-affordance`
//!   event so the payload is observable; loading the playground wasm + binding a
//!   `CardWorld` upgrades that to a live turn. The loop is proven in
//!   `wasm/tests/card_fires_a_verified_turn.rs`.

use crate::tree::ViewNode;

/// The browser-side script for a card document: the shared [`fmt`](crate::fmt) JS mirror (so the
/// in-tab re-read formats a bound value identically to the server bake) followed by the
/// affordance wire ([`JS`]). Built fresh per document; the mirror is derived from the shared
/// wordlists so it can never drift from the Rust formatter.
fn js() -> String {
    format!("{}{}", crate::fmt::fmt_js(), JS)
}

/// The live values of the `bind` nodes, in tree-walk (pre-order) appearance — the SAME
/// order the native renderer's `bind_plan` mints `BindingId`s in. Element `n` is the value the
/// `n`th `bind` node shows. A caller that has a live applet reads these off the ledger
/// (`applet.get_u64(slot)`, the witnessed read); a static bake passes the snapshot it
/// wants to paint. `None`/short → the renderer falls back to `0` (an un-driven bind).
pub type BindValues = [u64];

/// Render a view-tree to an HTML fragment string (no `<html>`/`<head>` — just the card's
/// markup). `bind_values[n]` is the live value of the `n`th `bind` node (tree-walk order);
/// a missing index paints `0`. Use [`render_card_document`] for a full browser-loadable page.
pub fn render_html(tree: &ViewNode, bind_values: &BindValues) -> String {
    let mut out = String::new();
    let mut bind_cursor = 0usize;
    node(tree, bind_values, &mut bind_cursor, &mut out);
    out
}

/// The recursive walker — mirrors [`crate::render::AppletView::node`] node-for-node.
fn node(n: &ViewNode, binds: &BindValues, cursor: &mut usize, out: &mut String) {
    match n {
        ViewNode::VStack(children) => {
            out.push_str("<div class=\"deos-vstack\">");
            for c in children {
                node(c, binds, cursor, out);
            }
            out.push_str("</div>");
        }
        ViewNode::Row(children) => {
            out.push_str("<div class=\"deos-row\">");
            for c in children {
                node(c, binds, cursor, out);
            }
            out.push_str("</div>");
        }
        ViewNode::Text(s) => {
            out.push_str("<span class=\"deos-text\">");
            out.push_str(&escape(s));
            out.push_str("</span>");
        }
        ViewNode::Bind { slot, label, fmt } => {
            // THE SIGNAL BINDING — paint the live value (the same witnessed read the JS
            // closure / gpui `bind` made), and carry `data-slot` so a browser re-read
            // after a turn knows which slot to refresh (the fine-grained signal source).
            // CONSUMER-DELIGHT: `fmt` paints an opaque key/hash SHORT + friendly; `data-fmt` +
            // `data-label` let the in-tab re-read re-format identically (the JS mirror) instead
            // of clobbering the friendly text with a raw number.
            let idx = *cursor;
            let value = binds.get(*cursor).copied().unwrap_or(0);
            *cursor += 1;
            let shown = crate::fmt::format_value(value, *fmt);
            let text = if label.is_empty() {
                shown
            } else {
                format!("{label}{shown}")
            };
            // `data-bind-index` is the stable tree-walk position of this bind. The
            // trustless portal carries per-bind heap openings as a JSON island keyed by
            // this index, so the in-tab verify can flip THIS field's span once its opening
            // checks against the committed heap root (the served-plain closure).
            out.push_str(&format!(
                "<span class=\"deos-bind\" data-slot=\"{slot}\" data-bind-index=\"{idx}\" data-fmt=\"{}\" data-label=\"{}\">{}</span>",
                fmt.as_str(),
                escape(label),
                escape(&text)
            ));
        }
        ViewNode::Button { label, turn, arg } => {
            // THE AFFORDANCE — carry `{turn, arg}` as data-attributes: the exact payload
            // a click must fire as a REAL cap-gated verified turn through the executor
            // (the wasm/node bridge — the named seam). The button is rendered + wired with
            // its payload; the live turn is the documented follow-on (see module docs).
            out.push_str(&format!(
                "<button class=\"deos-button\" data-turn=\"{}\" data-arg=\"{}\">{}</button>",
                escape(turn),
                arg,
                escape(label)
            ));
        }
        ViewNode::Input {
            bind_view,
            fire_turn,
            submit_label,
        } => {
            // A real `<input>` carrying its bind-view; when `fire_turn` is set it also carries a
            // submit button whose click fires `{turn, arg=the field value}` (input → verified
            // turn). The in-tab wire reads the field value as the arg.
            out.push_str(&format!(
                "<span class=\"deos-inputgroup\" data-bind-view=\"{}\">",
                escape(bind_view)
            ));
            out.push_str(&format!(
                "<input class=\"deos-input\" data-bind-view=\"{}\" placeholder=\"{}\">",
                escape(bind_view),
                escape(bind_view)
            ));
            if !fire_turn.is_empty() {
                let label = if submit_label.is_empty() {
                    "submit"
                } else {
                    submit_label.as_str()
                };
                out.push_str(&format!(
                    "<button class=\"deos-input-submit\" data-turn=\"{}\" data-arg-from=\"{}\">{}</button>",
                    escape(fire_turn),
                    escape(bind_view),
                    escape(label)
                ));
            }
            out.push_str("</span>");
        }
        ViewNode::List(items) => {
            out.push_str("<div class=\"deos-list\">");
            for it in items {
                node(it, binds, cursor, out);
            }
            out.push_str("</div>");
        }
        ViewNode::Table(rows) => {
            out.push_str("<div class=\"deos-table\">");
            for r in rows {
                node(r, binds, cursor, out);
            }
            out.push_str("</div>");
        }

        // ── The RICHNESS EXPANSION (batch 1) — the IDENTICAL ViewNode → HTML, mirroring the
        //    gpui renderer node-for-node so the card stays renderer-independent. ───────────
        ViewNode::Section {
            title,
            tag,
            children,
        } => {
            out.push_str(&format!(
                "<section class=\"deos-section\" data-tag=\"{}\">",
                escape(tag)
            ));
            if !title.is_empty() {
                out.push_str(&format!(
                    "<div class=\"deos-section-title\">{}</div>",
                    escape(title)
                ));
            }
            for c in children {
                node(c, binds, cursor, out);
            }
            out.push_str("</section>");
        }
        ViewNode::Tabs {
            tabs,
            selected_slot,
            select_turn,
            panels,
        } => {
            // The tab strip carries each tab's `{selectTurn, index}` as data-attributes (the
            // exact payload a click fires); the active panel is `selectedSlot`'s live value, a
            // JS layer toggling `deos-tabpanel` visibility. ALL panels are emitted (same order
            // the native renderer + bind cursor walk them) so the cursor never desyncs.
            out.push_str(&format!(
                "<div class=\"deos-tabs\" data-selected-slot=\"{selected_slot}\">"
            ));
            out.push_str("<div class=\"deos-tabstrip\">");
            for (i, label) in tabs.iter().enumerate() {
                out.push_str(&format!(
                    "<button class=\"deos-tab\" data-turn=\"{}\" data-arg=\"{}\" data-index=\"{}\">{}</button>",
                    escape(select_turn),
                    i,
                    i,
                    escape(label)
                ));
            }
            out.push_str("</div>");
            for (i, panel) in panels.iter().enumerate() {
                out.push_str(&format!("<div class=\"deos-tabpanel\" data-index=\"{i}\">"));
                node(panel, binds, cursor, out);
                out.push_str("</div>");
            }
            out.push_str("</div>");
        }
        ViewNode::Gauge { slot, max, label } => {
            // The bar carries `data-slot`/`data-max` so the in-tab executor drives the fill
            // live (the witnessed re-read); a static bake shows an empty track + the label.
            out.push_str(&format!(
                "<div class=\"deos-gauge\" data-slot=\"{slot}\" data-max=\"{max}\">"
            ));
            if !label.is_empty() {
                out.push_str(&format!(
                    "<span class=\"deos-gauge-label\">{}</span>",
                    escape(label)
                ));
            }
            out.push_str(
                "<div class=\"deos-gauge-track\"><div class=\"deos-gauge-fill\"></div></div>",
            );
            out.push_str("</div>");
        }
        ViewNode::Divider => {
            out.push_str("<hr class=\"deos-divider\">");
        }

        // ── The RICHNESS EXPANSION batch 2 — the IDENTICAL ViewNode → HTML, node-for-node. ────
        ViewNode::Grid { cols, children } => {
            out.push_str(&format!(
                "<div class=\"deos-grid\" data-cols=\"{cols}\" style=\"{}\">",
                if *cols > 0 {
                    format!("grid-template-columns:repeat({cols},1fr);")
                } else {
                    String::new()
                }
            ));
            for c in children {
                node(c, binds, cursor, out);
            }
            out.push_str("</div>");
        }
        ViewNode::Breadcrumb { items } => {
            out.push_str("<nav class=\"deos-breadcrumb\">");
            for (i, crumb) in items.iter().enumerate() {
                if i > 0 {
                    out.push_str("<span class=\"deos-crumb-sep\">&rsaquo;</span>");
                }
                if crumb.turn.is_empty() {
                    out.push_str(&format!(
                        "<span class=\"deos-crumb\">{}</span>",
                        escape(&crumb.label)
                    ));
                } else {
                    out.push_str(&format!(
                        "<button class=\"deos-crumb deos-button\" data-turn=\"{}\" data-arg=\"{}\">{}</button>",
                        escape(&crumb.turn),
                        crumb.arg,
                        escape(&crumb.label)
                    ));
                }
            }
            out.push_str("</nav>");
        }
        ViewNode::Progress { value, max, label } => {
            // A static progress bar — the in-tab executor never drives it (literal value), so the
            // fill width is baked from `value/max` right here.
            let pct = if *max == 0 {
                0.0
            } else {
                (*value as f64 / *max as f64).clamp(0.0, 1.0) * 100.0
            };
            out.push_str("<div class=\"deos-progress\">");
            if !label.is_empty() {
                out.push_str(&format!(
                    "<span class=\"deos-progress-label\">{}</span>",
                    escape(label)
                ));
            }
            out.push_str(&format!(
                "<div class=\"deos-progress-track\"><div class=\"deos-progress-fill\" style=\"width:{pct:.1}%\"></div></div>"
            ));
            out.push_str("</div>");
        }
        ViewNode::Pill {
            text,
            tag,
            slot,
            cases,
        } => {
            // A static pill OR a LIVE one: a bound pill carries its `data-slot` + cases JSON so
            // the in-tab re-read maps the live value to the matching word + color (the static
            // phase-word cure). First paint shows the case matching value 0 (or the fallback).
            if let (Some(s), false) = (slot, cases.is_empty()) {
                let (l0, t0) = crate::tree::pill_display(text, tag, cases, 0);
                let cases_json = pill_cases_json(cases);
                out.push_str(&format!(
                    "<span class=\"deos-pill\" data-tag=\"{}\" data-slot=\"{s}\" data-cases=\"{}\">{}</span>",
                    escape(t0),
                    escape(&cases_json),
                    escape(l0)
                ));
            } else {
                out.push_str(&format!(
                    "<span class=\"deos-pill\" data-tag=\"{}\">{}</span>",
                    escape(tag),
                    escape(text)
                ));
            }
        }
        ViewNode::Icon { glyph, tag } => {
            out.push_str(&format!(
                "<span class=\"deos-icon\" data-tag=\"{}\">{}</span>",
                escape(tag),
                escape(glyph)
            ));
        }
        ViewNode::Menu { items } => {
            out.push_str("<menu class=\"deos-menu\">");
            for item in items {
                if item.enabled {
                    out.push_str(&format!(
                        "<button class=\"deos-menuitem deos-button\" data-turn=\"{}\" data-arg=\"{}\">{}</button>",
                        escape(&item.turn),
                        item.arg,
                        escape(&item.label)
                    ));
                } else {
                    out.push_str(&format!(
                        "<span class=\"deos-menuitem deos-disabled\">{}</span>",
                        escape(&item.label)
                    ));
                }
            }
            out.push_str("</menu>");
        }
        ViewNode::Halo {
            target_slot,
            handles,
        } => {
            out.push_str(&format!(
                "<div class=\"deos-halo\" data-target-slot=\"{target_slot}\">"
            ));
            for h in handles {
                if h.enabled {
                    out.push_str(&format!(
                        "<button class=\"deos-handle deos-button\" data-turn=\"{}\" data-arg=\"{}\" title=\"{}\">{}</button>",
                        escape(&h.turn),
                        h.arg,
                        escape(&h.turn),
                        escape(&h.glyph)
                    ));
                } else {
                    out.push_str(&format!(
                        "<span class=\"deos-handle deos-disabled\">{}</span>",
                        escape(&h.glyph)
                    ));
                }
            }
            out.push_str("</div>");
        }
        ViewNode::Slider {
            slot,
            min,
            max,
            turn,
        } => {
            // A bound scrubber: an `<input type=range>` carrying its slot + seek turn; the in-tab
            // wire reads the slot live for the thumb and fires `turn` with `arg=the value` on input.
            out.push_str(&format!(
                "<input type=\"range\" class=\"deos-slider\" data-slot=\"{slot}\" data-turn=\"{}\" min=\"{min}\" max=\"{max}\">",
                escape(turn)
            ));
        }
        ViewNode::Toggle {
            slot,
            on_turn,
            off_turn,
            glyph_on,
            glyph_off,
            label,
        } => {
            // An affordance checkbox carrying both turns + glyphs; the in-tab wire reads the slot
            // live to pick the glyph and fires on/off by current state.
            out.push_str(&format!(
                "<button class=\"deos-toggle deos-button\" data-slot=\"{slot}\" data-on-turn=\"{}\" data-off-turn=\"{}\" data-glyph-on=\"{}\" data-glyph-off=\"{}\">{} {}</button>",
                escape(on_turn),
                escape(off_turn),
                escape(glyph_on),
                escape(glyph_off),
                escape(glyph_off),
                escape(label)
            ));
        }
        ViewNode::Tile { handle, w, h } => {
            // The host-resolved region: an `<iframe>`/`<canvas>` placeholder sized `w×h`,
            // carrying its `data-handle` for the host to resolve. An unresolved handle shows a
            // labelled placeholder.
            out.push_str(&format!(
                "<div class=\"deos-tile\" data-handle=\"{}\" style=\"width:{}px;height:{}px;\">",
                escape(handle),
                if *w == 0 { 320 } else { *w },
                if *h == 0 { 200 } else { *h }
            ));
            out.push_str(&format!(
                "<span class=\"deos-tile-label\">&#9638; tile {}: host-painted region {}&times;{}</span>",
                escape(handle),
                w,
                h
            ));
            out.push_str("</div>");
        }

        // The adept-only wrapper renders its inner node transparently (the disclosure filter
        // removes the marker before render; an un-filtered tree still paints the inner node).
        ViewNode::Adept(inner) => node(inner, binds, cursor, out),

        // ── The COMPOSITION KEYSTONE — the IDENTICAL host node → HTML: a framed region with a
        //    `⌂ <cell>` header carrying the mounted cell's whole hosted subtree (or the honest
        //    unresolved placeholder). `data-cell` carries the mount reference for the in-tab
        //    resolver to re-read the cell's heap. ──────────────────────────────────────────
        ViewNode::Host { cell, view } => {
            out.push_str(&format!(
                "<section class=\"deos-host\" data-cell=\"{}\">",
                escape(cell)
            ));
            out.push_str(&format!(
                "<div class=\"deos-host-head\">&#8962; {}</div>",
                escape(cell)
            ));
            match view {
                Some(v) => node(v, binds, cursor, out),
                None => out.push_str(&format!(
                    "<div class=\"deos-host-unresolved\">&lsaquo;mount cell {}: unresolved&rsaquo;</div>",
                    escape(cell)
                )),
            }
            out.push_str("</section>");
        }
    }
}

/// A full, standalone, browser-loadable HTML document for a card. `title` heads the page;
/// `bind_values` are the live `bind` values to paint (tree-walk order). Styling mirrors
/// the cockpit's dark theme (the same dark-mode the gpui `headless` bake forces) so the
/// browser projection LOOKS like the native one. Open the written file in any browser.
pub fn render_card_document(title: &str, tree: &ViewNode, bind_values: &BindValues) -> String {
    let body = render_html(tree, bind_values);
    format!(
        "<!doctype html>\n\
<html lang=\"en\">\n\
<head>\n\
<meta charset=\"utf-8\">\n\
<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
<title>{title}</title>\n\
<style>{CSS}</style>\n\
</head>\n\
<body>\n\
<main class=\"deos-card\">{body}</main>\n\
<script>{JS}</script>\n\
</body>\n\
</html>\n",
        title = escape(title),
        CSS = CSS,
        JS = js(),
    )
}

/// A full, browser-loadable HTML document for a card that is **LIVE** — it loads the
/// playground wasm bundle, mints an in-tab [`crate`]-less `CardWorld` (the wasm analog of
/// the native `Applet`, `wasm/src/bindings_card.rs`), binds it to `window.__deosCard`, and
/// the affordance wire ([`JS`]) fires each `+1` click as a REAL cap-gated verified turn
/// over that embedded executor and re-paints the bound slot. This is the served,
/// browser-native deos: a deos-js card rendered via THIS renderer, firing real turns in a
/// browser TAB, the bound value updating on click.
///
/// `pkg_url` is the ES-module URL of the wasm bundle's JS shim (e.g. `./pkg/dregg_wasm.js`,
/// the `wasm-pack build --target web` output); `slot` is the model field the card's `bind`
/// reads (the counter card binds slot 0); `initial` seeds the genesis value. It must be
/// served over HTTP (a module-import + a `.wasm` fetch — `file://` is blocked by browser
/// CORS), e.g. `python3 -m http.server` from the dist dir.
pub fn render_card_live_document(
    title: &str,
    tree: &ViewNode,
    slot: usize,
    initial: u64,
    pkg_url: &str,
) -> String {
    // First paint at the seeded value so the page is meaningful before wasm finishes
    // loading; the module bootstrap then re-binds it to the live ledger and re-paints.
    let body = render_html(tree, &[initial]);
    let bootstrap = format!(
        "import init, {{ CardWorld }} from '{pkg}';\n\
async function boot() {{\n\
  const status = document.getElementById('deos-status');\n\
  try {{\n\
    await init();                       // instantiate the wasm module\n\
    const card = new CardWorld({slot}, {initial}n);  // mint the in-tab verified executor\n\
    window.__deosCard = card;           // the affordance wire fires real turns into this\n\
    // Re-paint every bound slot from the committed ledger (the witnessed read).\n\
    document.querySelectorAll('.deos-bind[data-slot]').forEach(function(span) {{\n\
      const label = span.textContent.replace(/[0-9]+$/, '');\n\
      span.textContent = label + card.read();\n\
    }});\n\
    if (status) status.textContent = 'live — cell ' + card.cellId().slice(0, 10) + '… · receipts: ' + card.receiptCount();\n\
    // Keep the receipt count fresh after every committed turn.\n\
    document.addEventListener('deos-affordance', function() {{\n\
      requestAnimationFrame(function() {{\n\
        if (status && window.__deosCard) status.textContent = 'live — cell ' + window.__deosCard.cellId().slice(0, 10) + '… · receipts: ' + window.__deosCard.receiptCount();\n\
      }});\n\
    }});\n\
  }} catch (e) {{\n\
    if (status) status.textContent = 'wasm load failed: ' + e;\n\
    console.error('deos: wasm executor failed to load', e);\n\
  }}\n\
}}\n\
boot();\n",
        pkg = pkg_url,
        slot = slot,
        initial = initial,
    );
    format!(
        "<!doctype html>\n\
<html lang=\"en\">\n\
<head>\n\
<meta charset=\"utf-8\">\n\
<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
<title>{title}</title>\n\
<style>{CSS}{LIVE_CSS}</style>\n\
</head>\n\
<body>\n\
<a class=\"deos-back\" href=\"./\">&lsaquo; all cards</a>\n\
<main class=\"deos-card\">{body}<div class=\"deos-status\" id=\"deos-status\">loading the in-tab verified executor…</div></main>\n\
<script>{JS}</script>\n\
<script type=\"module\">{bootstrap}</script>\n\
</body>\n\
</html>\n",
        title = escape(title),
        CSS = CSS,
        LIVE_CSS = LIVE_CSS,
        body = body,
        JS = js(),
        bootstrap = bootstrap,
    )
}

/// A full, browser-loadable HTML document for the **REFLECTIVE-INSPECTOR card** that is
/// **LIVE**. The IDENTICAL gpui-free web renderer paints the inspector card's view-tree (a
/// "Cell State" section of live `Bind` rows + structural `Text` rows, an "Affordances" section
/// of `Button`s — generated from a focused cell's real moldable faces by
/// `wasm/src/bindings_card.rs`'s `InspectorWorld::view_tree_json`); the bootstrap loads the
/// playground wasm, mints an in-tab [`crate`]-less `InspectorWorld` (the wasm analog of the
/// native inspector card over a live World), binds it to `window.__deosCard`, and re-paints
/// EVERY bound row from the committed ledger. An affordance `Button`'s click fires a REAL
/// cap-gated verified turn over that embedded executor (the shared [`JS`] wire) and the bound
/// field re-paints — a fully-reflective cockpit surface running in a browser, not just the
/// native cockpit.
///
/// Unlike [`render_card_live_document`] (the single-slot counter), this carries SEVERAL bound
/// slots: each `deos-bind` span repaints from its own `data-slot` via `InspectorWorld.read(slot)`
/// (the [`JS`] wire dispatches on `read` arity, so it drives both cards). `tree` is the inspector
/// view-tree (parsed from `InspectorWorld::view_tree_json` — serve the SAME tree the in-tab
/// executor reports); `bind_values` is the first-paint snapshot (one per `bind` in tree-walk
/// order) shown before wasm finishes loading; `seeds` seeds the in-tab cell's scalar slots
/// (matching the snapshot). `pkg_url` is the wasm bundle's JS shim URL. Must be served over
/// HTTP (`file://` is CORS-blocked for the module import + `.wasm` fetch).
pub fn render_inspector_live_document(
    title: &str,
    tree: &ViewNode,
    bind_values: &BindValues,
    seeds: &[u64],
    pkg_url: &str,
) -> String {
    let body = render_html(tree, bind_values);
    // `seeds` → a JS array literal for the `InspectorWorld` constructor (it takes a Vec<u64>,
    // which wasm-bindgen maps to a `BigUint64Array`/array of BigInt — pass `Nn` literals).
    let seeds_js = seeds
        .iter()
        .map(|s| format!("{s}n"))
        .collect::<Vec<_>>()
        .join(", ");
    let bootstrap = format!(
        "import init, {{ InspectorWorld }} from '{pkg}';\n\
async function boot() {{\n\
  const status = document.getElementById('deos-status');\n\
  try {{\n\
    await init();                                  // instantiate the wasm module\n\
    const card = new InspectorWorld([{seeds}]);    // mint the in-tab reflective executor\n\
    window.__deosCard = card;                      // the affordance wire fires real turns into this\n\
    // Re-paint every bound slot from the committed ledger (the witnessed read), each row\n\
    // off its OWN data-slot — the reflective inspector binds several fields.\n\
    document.querySelectorAll('.deos-bind[data-slot]').forEach(function(span) {{\n\
      const slot = parseInt(span.getAttribute('data-slot') || '0', 10);\n\
      const label = span.textContent.replace(/[0-9]+$/, '');\n\
      span.textContent = label + card.read(slot);\n\
    }});\n\
    function refreshStatus() {{\n\
      if (status && window.__deosCard) {{\n\
        const c = window.__deosCard;\n\
        status.textContent = 'live — cell ' + c.cellId().slice(0, 10) + '… · balance ' + c.balance() + ' · nonce ' + c.nonce() + ' · receipts ' + c.receiptCount();\n\
      }}\n\
    }}\n\
    refreshStatus();\n\
    // Keep the structural readout fresh after every committed turn.\n\
    document.addEventListener('deos-affordance', function() {{ requestAnimationFrame(refreshStatus); }});\n\
  }} catch (e) {{\n\
    if (status) status.textContent = 'wasm load failed: ' + e;\n\
    console.error('deos: inspector wasm executor failed to load', e);\n\
  }}\n\
}}\n\
boot();\n",
        pkg = pkg_url,
        seeds = seeds_js,
    );
    format!(
        "<!doctype html>\n\
<html lang=\"en\">\n\
<head>\n\
<meta charset=\"utf-8\">\n\
<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
<title>{title}</title>\n\
<style>{CSS}{LIVE_CSS}</style>\n\
</head>\n\
<body>\n\
<a class=\"deos-back\" href=\"./\">&lsaquo; all cards</a>\n\
<main class=\"deos-card\">{body}<div class=\"deos-status\" id=\"deos-status\">loading the in-tab verified executor…</div></main>\n\
<script>{JS}</script>\n\
<script type=\"module\">{bootstrap}</script>\n\
</body>\n\
</html>\n",
        title = escape(title),
        CSS = CSS,
        LIVE_CSS = LIVE_CSS,
        body = body,
        JS = js(),
        bootstrap = bootstrap,
    )
}

/// A full, browser-loadable HTML document for the **TALLY-BOARD card** that is **LIVE**. The
/// IDENTICAL gpui-free web renderer paints the board's view-tree — a `Table` of `Row`s, each a
/// named tally with its live `Bind` value and `+1`/`−1` affordance `Button`s (generated by
/// `wasm/src/bindings_card.rs`'s `TallyWorld::view_tree_json`). This is the proof that the
/// view-tree's LAYOUT nodes (`Row`/`Table`) and multi-affordance rows render AND drive in a
/// browser through the SAME ViewNode IR: the bootstrap loads the playground wasm, mints an
/// in-tab `TallyWorld` seeded to `seeds`, binds `window.__deosCard`, and re-paints every bound
/// row from the committed ledger. Each `+1`/`−1` click fires a REAL cap-gated verified turn (the
/// shared [`JS`] wire — `data-arg` is the tally's SLOT, `data-turn` the direction) and that one
/// row re-paints.
///
/// `tree` is the board view-tree (parse `TallyWorld::view_tree_json` — serve the SAME tree the
/// in-tab executor reports); `bind_values` is the first-paint snapshot (one per `bind` in
/// tree-walk order); `seeds` seeds the in-tab tallies (matching the snapshot). `pkg_url` is the
/// wasm bundle's JS-shim URL. Must be served over HTTP (`file://` is CORS-blocked).
pub fn render_tally_live_document(
    title: &str,
    tree: &ViewNode,
    bind_values: &BindValues,
    seeds: &[u64],
    pkg_url: &str,
) -> String {
    let body = render_html(tree, bind_values);
    let seeds_js = seeds
        .iter()
        .map(|s| format!("{s}n"))
        .collect::<Vec<_>>()
        .join(", ");
    let bootstrap = format!(
        "import init, {{ TallyWorld }} from '{pkg}';\n\
async function boot() {{\n\
  const status = document.getElementById('deos-status');\n\
  try {{\n\
    await init();                                  // instantiate the wasm module\n\
    const card = new TallyWorld([{seeds}]);        // mint the in-tab tally executor\n\
    window.__deosCard = card;                      // the affordance wire fires real turns into this\n\
    // Re-paint every bound row from the committed ledger (the witnessed read), each off its\n\
    // OWN data-slot — the board binds one slot per tally row.\n\
    document.querySelectorAll('.deos-bind[data-slot]').forEach(function(span) {{\n\
      const slot = parseInt(span.getAttribute('data-slot') || '0', 10);\n\
      const label = span.textContent.replace(/[0-9]+$/, '');\n\
      span.textContent = label + card.read(slot);\n\
    }});\n\
    function refreshStatus() {{\n\
      if (status && window.__deosCard) {{\n\
        const c = window.__deosCard;\n\
        status.textContent = 'live — cell ' + c.cellId().slice(0, 10) + '… · receipts ' + c.receiptCount();\n\
      }}\n\
    }}\n\
    refreshStatus();\n\
    document.addEventListener('deos-affordance', function() {{ requestAnimationFrame(refreshStatus); }});\n\
  }} catch (e) {{\n\
    if (status) status.textContent = 'wasm load failed: ' + e;\n\
    console.error('deos: tally wasm executor failed to load', e);\n\
  }}\n\
}}\n\
boot();\n",
        pkg = pkg_url,
        seeds = seeds_js,
    );
    format!(
        "<!doctype html>\n\
<html lang=\"en\">\n\
<head>\n\
<meta charset=\"utf-8\">\n\
<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
<title>{title}</title>\n\
<style>{CSS}{LIVE_CSS}</style>\n\
</head>\n\
<body>\n\
<a class=\"deos-back\" href=\"./\">&lsaquo; all cards</a>\n\
<main class=\"deos-card\">{body}<div class=\"deos-status\" id=\"deos-status\">loading the in-tab verified executor…</div></main>\n\
<script>{JS}</script>\n\
<script type=\"module\">{bootstrap}</script>\n\
</body>\n\
</html>\n",
        title = escape(title),
        CSS = CSS,
        LIVE_CSS = LIVE_CSS,
        body = body,
        JS = js(),
        bootstrap = bootstrap,
    )
}

/// A full, browser-loadable HTML document for the **KV-STORE SERVICE-CELL card** that is
/// **LIVE**. The IDENTICAL gpui-free web renderer paints the store's view-tree — a version row
/// and a `Table` of register rows, each with a live `Bind` value and `put`/`del` affordance
/// `Button`s (generated by `wasm/src/bindings_card.rs`'s `KvStoreWorld::view_tree_json`). This
/// is the proof that a SERVICE CELL — a cell publishing a typed `InterfaceDescriptor` whose
/// methods route through the verified DFA before they desugar to ordinary `SetField` effects —
/// renders AND drives in a browser tab: the bootstrap loads the playground wasm, mints an
/// in-tab `KvStoreWorld` seeded to `seeds`, binds `window.__deosCard`, and each `put`/`del`
/// click fires a REAL cap-gated verified turn ROUTED through the published interface against
/// the store cell, the monotone version bumping and the touched register re-painting.
///
/// The status strip additionally proves the verified guarantee BITES in the tab: it calls
/// `card.tryRollback(reg)` (a `put` lowering the store version, which the program's `Monotonic`
/// constraint REFUSES) and `card.tryGet(reg)` (the `Serviced` read the router refuses to
/// desugar — the named OFE seam), reporting both.
///
/// `tree` is the store view-tree (parse `KvStoreWorld::view_tree_json`); `bind_values` is the
/// first-paint snapshot (one per `bind` in tree-walk order: the version, then each register);
/// `seeds` seeds the in-tab registers. `pkg_url` is the wasm bundle's JS-shim URL. Must be
/// served over HTTP (`file://` is CORS-blocked).
pub fn render_kvstore_live_document(
    title: &str,
    tree: &ViewNode,
    bind_values: &BindValues,
    seeds: &[u64],
    pkg_url: &str,
) -> String {
    let body = render_html(tree, bind_values);
    let seeds_js = seeds
        .iter()
        .map(|s| format!("{s}n"))
        .collect::<Vec<_>>()
        .join(", ");
    let bootstrap = format!(
        "import init, {{ KvStoreWorld }} from '{pkg}';\n\
async function boot() {{\n\
  const status = document.getElementById('deos-status');\n\
  try {{\n\
    await init();                                  // instantiate the wasm module\n\
    const card = new KvStoreWorld([{seeds}]);      // mint the in-tab service cell + verified executor\n\
    window.__deosCard = card;                      // the affordance wire routes real turns into this\n\
    // Re-paint every bound slot from the committed ledger (the witnessed read), each off its\n\
    // OWN data-slot — slot 0 is the store version, the rest are registers.\n\
    document.querySelectorAll('.deos-bind[data-slot]').forEach(function(span) {{\n\
      const slot = parseInt(span.getAttribute('data-slot') || '0', 10);\n\
      const label = span.textContent.replace(/[0-9]+$/, '');\n\
      span.textContent = label + card.read(slot);\n\
    }});\n\
    function refreshStatus() {{\n\
      if (status && window.__deosCard) {{\n\
        const c = window.__deosCard;\n\
        status.textContent = 'live — store ' + c.cellId().slice(0, 10) + '… · version ' + c.version() + ' · receipts ' + c.receiptCount();\n\
      }}\n\
    }}\n\
    refreshStatus();\n\
    document.addEventListener('deos-affordance', function() {{ requestAnimationFrame(refreshStatus); }});\n\
  }} catch (e) {{\n\
    if (status) status.textContent = 'wasm load failed: ' + e;\n\
    console.error('deos: kvstore wasm executor failed to load', e);\n\
  }}\n\
}}\n\
boot();\n",
        pkg = pkg_url,
        seeds = seeds_js,
    );
    format!(
        "<!doctype html>\n\
<html lang=\"en\">\n\
<head>\n\
<meta charset=\"utf-8\">\n\
<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
<title>{title}</title>\n\
<style>{CSS}{LIVE_CSS}</style>\n\
</head>\n\
<body>\n\
<a class=\"deos-back\" href=\"./\">&lsaquo; all cards</a>\n\
<main class=\"deos-card\">{body}<div class=\"deos-status\" id=\"deos-status\">loading the in-tab verified executor…</div></main>\n\
<script>{JS}</script>\n\
<script type=\"module\">{bootstrap}</script>\n\
</body>\n\
</html>\n",
        title = escape(title),
        CSS = CSS,
        LIVE_CSS = LIVE_CSS,
        body = body,
        JS = js(),
        bootstrap = bootstrap,
    )
}

/// A full, browser-loadable HTML document for the **DOCUMENT-COLLABORATION surface** that is
/// **LIVE** — the Pijul/conflicts-as-objects flow (fork → diverge → stitch → a first-class
/// conflict → resolve → publish), node-less, in a browser tab.
///
/// Unlike the other live cards (whose tree SHAPE is static — a click only re-paints a `data-slot`
/// bind), this surface's tree CHANGES on a resolve: a `stitch` surfaces a ConflictView (the two
/// alternatives attributed side-by-side + a resolution `Button` per choice), and a `resolve`
/// collapses it to the clean published document. So the bootstrap re-renders WHOLESALE after every
/// affordance: the in-tab `DocCollabWorld` (`wasm/src/bindings_doc.rs`) renders its OWN view-tree
/// to HTML through THIS gpui-free renderer (`card.viewHtml()`), and the page sets it as the doc
/// container's `innerHTML`. A delegated click handler on the container fires each `.deos-button`'s
/// `{turn, arg}` as a REAL cap-gated verified turn over the embedded executor; a `resolve`
/// publishes the merged document to the doc-cell's umem-heap (the boundary `heap_root` moves) and
/// the status strip re-reads the live umem boundary + receipt count.
///
/// `pkg_url` is the wasm bundle's JS-shim URL. Must be served over HTTP (`file://` is CORS-blocked
/// for the module import + `.wasm` fetch).
pub fn render_doccollab_live_document(title: &str, pkg_url: &str) -> String {
    let bootstrap = format!(
        "import init, {{ DocCollabWorld }} from '{pkg}';\n\
async function boot() {{\n\
  const status = document.getElementById('deos-status');\n\
  const root = document.getElementById('deos-doc-root');\n\
  try {{\n\
    await init();                          // instantiate the wasm module\n\
    const card = new DocCollabWorld();     // mint the in-tab doc-cell + verified executor (fork + publish base)\n\
    window.__deosDoc = card;               // the affordance wire fires real turns into this\n\
    function refreshStatus() {{\n\
      if (!status || !window.__deosDoc) return;\n\
      const c = window.__deosDoc;\n\
      const state = c.hasConflict() ? 'conflict HELD off-heap' : 'published ✓';\n\
      status.textContent = 'doc-cell ' + c.cellId().slice(0, 10) + '… · umem boundary ' + c.commitmentHex().slice(0, 12) + '… · receipts ' + c.receiptCount() + ' · ' + state;\n\
    }}\n\
    function rerender() {{\n\
      // The in-tab DocCollabWorld renders its OWN view-tree to HTML via the SAME gpui-free web\n\
      // renderer; the tree SHAPE changes (ConflictView ⇄ published doc) so we re-render wholesale.\n\
      root.innerHTML = window.__deosDoc.viewHtml();\n\
      refreshStatus();\n\
    }}\n\
    // Delegated affordance wire: dynamically-added resolution buttons work after a re-render.\n\
    root.addEventListener('click', function(e) {{\n\
      const b = e.target.closest('.deos-button');\n\
      if (!b) return;\n\
      const turn = b.getAttribute('data-turn');\n\
      const arg = parseInt(b.getAttribute('data-arg') || '0', 10);\n\
      document.dispatchEvent(new CustomEvent('deos-affordance', {{ detail: {{ turn: turn, arg: arg }} }}));\n\
      try {{\n\
        window.__deosDoc.fire(turn, arg);  // stitch (the pushout) OR resolve+publish (a verified turn)\n\
        rerender();                        // the tree re-renders: ConflictView ⇄ published document\n\
      }} catch (err) {{\n\
        console.error('deos doc affordance refused (no turn committed):', turn, arg, err);\n\
      }}\n\
    }});\n\
    rerender();\n\
  }} catch (e) {{\n\
    if (status) status.textContent = 'wasm load failed: ' + e;\n\
    console.error('deos: doc-collab wasm executor failed to load', e);\n\
  }}\n\
}}\n\
boot();\n",
        pkg = pkg_url,
    );
    format!(
        "<!doctype html>\n\
<html lang=\"en\">\n\
<head>\n\
<meta charset=\"utf-8\">\n\
<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
<title>{title}</title>\n\
<style>{CSS}{LIVE_CSS}{DOC_CSS}</style>\n\
</head>\n\
<body>\n\
<a class=\"deos-back\" href=\"./\">&lsaquo; all cards</a>\n\
<main class=\"deos-card\"><div id=\"deos-doc-root\"></div><div class=\"deos-status\" id=\"deos-status\">loading the in-tab verified executor…</div></main>\n\
<script>{JS}</script>\n\
<script type=\"module\">{bootstrap}</script>\n\
</body>\n\
</html>\n",
        title = escape(title),
        CSS = CSS,
        LIVE_CSS = LIVE_CSS,
        DOC_CSS = DOC_CSS,
        JS = js(),
        bootstrap = bootstrap,
    )
}

/// Extra styling for the document-collaboration surface: the side-by-side ConflictView columns
/// (one per attributed alternative) + readable prose runs. Shares the cockpit dark palette.
const DOC_CSS: &str = "
.deos-card .deos-text{white-space:pre-wrap;line-height:1.5;}
#deos-doc-root > .deos-vstack > .deos-row{align-items:stretch;gap:1rem;}
#deos-doc-root > .deos-vstack > .deos-row > .deos-vstack{flex:1;background:#15171d;border:1px solid var(--border);border-left:3px solid var(--accent);border-radius:6px;padding:.5rem .75rem;}
#deos-doc-root > .deos-vstack > .deos-row > .deos-vstack > .deos-text:first-child{color:var(--accent);font-weight:700;}
#deos-doc-root .deos-button{margin:.15rem 0;text-align:left;}
";

/// One card in the gallery: the page to open, its name, and a one-line blurb of what
/// clicking it does. (`href` is a same-dir page in the served `dist/`, e.g.
/// `"counter.html"`; `name`/`blurb` are the tile's title + subtitle.)
pub struct GalleryCard<'a> {
    /// The served page this tile opens (a sibling `.html` in the `dist/`).
    pub href: &'a str,
    /// The tile's title (the card's name).
    pub name: &'a str,
    /// A one-line description of the live card behind the tile.
    pub blurb: &'a str,
}

/// **THE CARD-PICKER / HOME PAGE** — a discoverable landing for the served browser-native
/// deos. Without it a visitor lands on one card and never finds the others; this page is a
/// gallery of clickable tiles, one per live card, each opening a real card page where a click
/// fires a cap-gated verified turn in the tab. It is plain HTML (no wasm) — the lightweight
/// front door to the live cards (the "click around, absorb, no comprehension needed" entry).
///
/// `cards` are the tiles in display order (each a [`GalleryCard`] → an `<a>` to its served
/// page). Styling matches the cockpit dark theme so the front door looks like the cards behind
/// it. Bake it to the served `dist/`'s `index.html` so `/` is the picker.
pub fn render_gallery_document(title: &str, cards: &[GalleryCard]) -> String {
    let mut tiles = String::new();
    for c in cards {
        tiles.push_str(&format!(
            "<a class=\"deos-tile\" href=\"{href}\">\
<span class=\"deos-tile-name\">{name}</span>\
<span class=\"deos-tile-blurb\">{blurb}</span>\
<span class=\"deos-tile-go\">open the card &rsaquo;</span>\
</a>",
            href = escape(c.href),
            name = escape(c.name),
            blurb = escape(c.blurb),
        ));
    }
    format!(
        "<!doctype html>\n\
<html lang=\"en\">\n\
<head>\n\
<meta charset=\"utf-8\">\n\
<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
<title>{title}</title>\n\
<style>{CSS}{GALLERY_CSS}</style>\n\
</head>\n\
<body>\n\
<main class=\"deos-gallery\">\n\
<header class=\"deos-gallery-head\">\n\
<h1>{title}</h1>\n\
<p>Each tile is a live deos card. Open one and click an affordance — every click fires a \
real cap-gated <em>verified turn</em> over an executor running right here in the tab, and \
the bound field re-paints from the committed ledger.</p>\n\
</header>\n\
<div class=\"deos-tiles\">{tiles}</div>\n\
</main>\n\
</body>\n\
</html>\n",
        title = escape(title),
        CSS = CSS,
        GALLERY_CSS = GALLERY_CSS,
        tiles = tiles,
    )
}

/// Styling for the gallery / card-picker home page — the hero header + the tile grid. Shares
/// the cockpit dark palette (`CSS`'s `:root` vars) so the front door matches the cards.
const GALLERY_CSS: &str = "
body{align-items:flex-start;}
.deos-gallery{max-width:760px;width:100%;margin:0 auto;}
.deos-gallery-head h1{margin:.25rem 0 .5rem;font-size:1.6rem;font-weight:700;}
.deos-gallery-head p{margin:0 0 1.5rem;color:var(--muted);line-height:1.5;}
.deos-gallery-head em{color:var(--fg);font-style:normal;font-weight:600;}
.deos-tiles{display:grid;grid-template-columns:repeat(auto-fill,minmax(240px,1fr));gap:1rem;}
.deos-tile{display:flex;flex-direction:column;gap:.4rem;text-decoration:none;background:#181a20;border:1px solid var(--border);border-radius:10px;padding:1.1rem;transition:border-color .12s,transform .12s;}
.deos-tile:hover{border-color:var(--accent);transform:translateY(-2px);}
.deos-tile-name{color:var(--fg);font-size:1.15rem;font-weight:700;}
.deos-tile-blurb{color:var(--muted);font-size:.85rem;line-height:1.45;}
.deos-tile-go{color:var(--accent);font-size:.8rem;font-weight:600;margin-top:.35rem;}
";

// ─────────────────────────────────────────────────────────────────────────────
// THE TRUSTLESS WEB PORTAL  (the @DreggNet "IPFS-gateway-like portal that
// trustlessly serves dregg content")
// ─────────────────────────────────────────────────────────────────────────────
// The live cards above run a verified EXECUTOR in the tab — a click fires a real
// turn. THIS document answers a different, orthogonal question: *can the browser
// trust that the served page reflects a REAL verified cell, not a server's
// claim?* It bakes the cell's card (the served content) PLUS a light-client
// attestation, and a browser-side check (the wasm `dregg-lightclient` over the
// recursive STARK aggregate) decides — IN THE TAB, re-witnessing nothing —
// whether the cell's committed history is genuine. Until that check passes the
// content is marked "the server's unverified claim"; on success the page asserts
// it reflects a light-client-verified cell.

/// How a [`render_trustless_cell_document`] page obtains the attestation its
/// browser-side light client checks.
///
/// Both arms run the REAL `dregg-lightclient` recursion verify in the tab (the
/// wasm `verify_devnet_history`). They differ only in WHERE the proof + the trust
/// anchor come from — which is the whole substance of "trustless":
pub enum TrustlessAttestation<'a> {
    /// **The production / gateway shape.** A node/relayer produced the recursive
    /// aggregate over the cell's finalized history and serialized it into an
    /// `ExternalHistoryEnvelope` JSON (`wasm::bindings_lightclient`); the page also
    /// carries the client's CONFIG VK anchor (a 64-hex fingerprint distributed at
    /// genesis/checkpoint, held SEPARATELY from the artifact). The tab decodes the
    /// envelope's proof bytes and runs `verify_devnet_history(envelope, anchor)` —
    /// the anchor is config, NEVER read off the served envelope, so a tampered
    /// proof or a foreign-circuit aggregate is REFUSED, never laundered into trust.
    ServerSupplied {
        /// The `ExternalHistoryEnvelope` JSON the server hands over (carries the
        /// base64 proof bytes + the carried public commitments). Embedded verbatim.
        envelope_json: &'a str,
        /// The client's configured root-circuit VK fingerprint (64 hex chars). The
        /// trust anchor — supplied by config, compared against the envelope's claim,
        /// and re-pinned from the proof bytes during the real verify.
        config_anchor_hex: &'a str,
    },
    /// **The self-contained demonstration.** The tab itself folds a real `k`-turn
    /// chain (`produce_external_history_envelope`), mints the matching shape anchor
    /// (`genesis_vk_anchor`), and verifies — so the whole produce→serialize→verify
    /// round-trip is tactile with no external node. Honest about being SELF-ANCHORED
    /// (the setup party proving its own fold): the config-not-artifact discipline is
    /// what the [`TrustlessAttestation::ServerSupplied`] path exercises.
    InTabDemo {
        /// Turns to fold (clamped to `[2, 4]` in-tab — recursive proving is heavy).
        k: usize,
        /// Per-turn transfer step (any non-zero amount).
        step: u64,
    },
}

/// A per-field **heap opening** the trustless portal carries so the tab can bind a
/// rendered `bind` VALUE to the cell's committed umem heap — the served-plain closure.
///
/// One per `bind` the portal wants field-verified (keyed by the bind's tree-walk index,
/// matching the `data-bind-index` the renderer emits). It is the sparse-Merkle opening of
/// the slot `(coll, key)` → `value` against the cell's committed heap `root`, the exact
/// fold `dregg_circuit::heap_root` commits with. The tab runs the wasm
/// `verify_slot_opening(root, coll, key, value, siblings, directions)` over it; a genuine
/// opening flips the field span to verified, a tampered one is refused.
///
/// All values are decimal `BabyBear` felts (`< 2^31`). `siblings`/`directions` are the
/// depth-`HEAP_TREE_DEPTH` (16) path (bottom-up): `directions[i]` is `0` if the running
/// node is the left child at level `i`, `1` if right. The baker mints these from a real
/// `CanonicalHeapTree` (the portal renderer is circuit-free, so the opening is produced by
/// a circuit-aware caller and handed in); it MUST carry the same `value` the card paints
/// for that bind, so "the shown value" and "the opened value" are one and the same.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct HeapSlotOpening {
    /// The cell's committed umem heap root (decimal `BabyBear` felt).
    pub root: u32,
    /// The slot's collection id.
    pub coll: u32,
    /// The slot's key within the collection.
    pub key: u32,
    /// The committed value at the slot (decimal felt) — equals the painted bind value.
    pub value: u32,
    /// The sparse-Merkle siblings along the path, bottom-up (decimal felts), length 16.
    pub siblings: Vec<u32>,
    /// The path direction bits, bottom-up (`0` = left child, `1` = right), length 16.
    pub directions: Vec<u8>,
}

/// Serialize the per-bind openings to a compact JSON array for the `#deos-openings`
/// island: `null` for a bind with no opening, else `{i, root, coll, key, value, sibs, dirs}`
/// (the `data-bind-index` `i` ties it to its span). Numbers only — no string escaping
/// needed — so this is a plain hand-built emit (kept gpui/serde_json-free in spirit, and
/// the `<` neutralisation is handled by [`embed_json`] at the island).
fn openings_json(openings: &[Option<HeapSlotOpening>]) -> String {
    let mut out = String::from("[");
    for (i, op) in openings.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        match op {
            None => out.push_str("null"),
            Some(o) => {
                let sibs = o
                    .siblings
                    .iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>()
                    .join(",");
                let dirs = o
                    .directions
                    .iter()
                    .map(|d| d.to_string())
                    .collect::<Vec<_>>()
                    .join(",");
                out.push_str(&format!(
                    "{{\"i\":{i},\"root\":{},\"coll\":{},\"key\":{},\"value\":{},\"sibs\":\"{sibs}\",\"dirs\":\"{dirs}\"}}",
                    o.root, o.coll, o.key, o.value
                ));
            }
        }
    }
    out.push(']');
    out
}

/// **THE TRUSTLESS PORTAL PAGE** — serve a dregg cell's card to a browser such that
/// the page PROVES (in the tab, re-witnessing nothing) it reflects a genuine verified
/// cell, not a server's bare claim.
///
/// The served content is the cell's deos-view card rendered to HTML by the SAME
/// gpui-free renderer ([`render_html`]) — `bind_values` is the committed snapshot to
/// paint (tree-walk order). Above it sits a TRUST BANNER and an attestation readout;
/// a `type=module` bootstrap loads the playground wasm and runs the REAL
/// `dregg-lightclient` recursion verify (`wasm::bindings_lightclient::verify_devnet_history`)
/// per `attestation`. The card body starts marked `deos-unverified` ("the server's
/// claim"); when the light client attests, the banner flips to verified and reveals the
/// proven commitments (`num_turns`, the 8-felt `final_root`, the ordered-history digest).
///
/// ## What is trustless here, precisely (the honest claim)
///
/// - **VERIFIED, in the browser, re-witnessing nothing:** that the cell's state
///   COMMITMENT (`final_root`) is the genuine recursive fold of a real, in-order,
///   per-turn-correct finalized history of `num_turns` turns — under the one named
///   floor `recursive_sound` (FRI/STARK engine soundness, surfaced not hidden). A
///   tampered proof, a relabeled public, or a foreign circuit is REFUSED. This is
///   exactly `light_client_verifies_whole_history`, run in wasm32.
/// - **SERVED-PLAIN, now closed per-field (when `openings` are carried):** each painted
///   `bind` VALUE is bound to the committed cell state by a per-slot sparse-Merkle
///   OPENING against the cell's umem heap `root` ([`HeapSlotOpening`]), verified tab-side
///   by the wasm `verify_slot_opening` — the executable counterpart of Lean's
///   `Heap.root_binds_get` (equal roots ⇒ equal value at every slot). A field whose
///   opening checks flips from `deos-field-unverified` to verified; a tampered value
///   moves the recomputed root and is REFUSED, never laundered. So the trustless claim
///   now covers the field VALUES, not only the commitment.
/// - **THE RESIDUAL (named, not hidden):** an opening binds a value to the cell's HEAP
///   ROOT. The heap root is one limb of the cell-state commitment that the faithful
///   8-felt `final_root` folds, so it BINDS to the verified anchor — but re-deriving
///   `final_root` from the heap root in-tab (recomputing the whole cell-state commitment
///   from its limbs) is a further rung, not done here. What is proven: each shown field
///   value equals the value committed at its slot in the cell heap whose `root` the
///   opening pins. A bind carrying NO opening stays the server's plain rendering.
///
/// `openings[i]` is the heap opening for the `i`-th `bind` in tree-walk order (`None` =
/// no opening carried, that field stays plain). `pkg_url` is the ES-module URL of the
/// wasm bundle's JS shim (e.g. `./pkg/dregg_wasm.js`). Must be served over HTTP (module
/// import + `.wasm` fetch are CORS-blocked on `file://`).
pub fn render_trustless_cell_document(
    title: &str,
    tree: &ViewNode,
    bind_values: &BindValues,
    openings: &[Option<HeapSlotOpening>],
    attestation: &TrustlessAttestation,
    pkg_url: &str,
) -> String {
    let body = render_html(tree, bind_values);

    // The per-mode verify call: both end at `verify_devnet_history(env, anchor)` with
    // its `{attested, num_turns, final_root, chain_digest, named_floor}` verdict — the
    // anchor a SEPARATE input, never read off the envelope under verification.
    let (attest_block, obtain_js, mode_note) = match attestation {
        TrustlessAttestation::ServerSupplied {
            envelope_json,
            config_anchor_hex,
        } => {
            // Embed the envelope as an inert JSON island (read via textContent) so its
            // quotes/braces never collide with the surrounding script; `<` → < keeps
            // it valid JSON while making `</script>` unrepresentable.
            let safe_env = embed_json(envelope_json);
            let block = format!(
                "<script type=\"application/json\" id=\"deos-attestation\">{safe_env}</script>"
            );
            let obtain = format!(
                "const env = document.getElementById('deos-attestation').textContent;\n\
    const anchor = '{anchor}';\n\
    const verdict = verify_devnet_history(env, anchor);  // REAL recursion verify, config anchor",
                anchor = escape(config_anchor_hex),
            );
            (
                block,
                obtain,
                "verified against a CONFIG-supplied anchor (held separately from the served proof)",
            )
        }
        TrustlessAttestation::InTabDemo { k, step } => {
            let block = String::new();
            let obtain = format!(
                "const env = produce_external_history_envelope({k}, {step}n);   // fold a real {k}-turn history\n\
    const anchor = genesis_vk_anchor({k}, {step}n);                 // the matching-shape VK anchor\n\
    const verdict = verify_devnet_history(env, anchor);  // REAL recursion verify, re-witnessing nothing",
                k = k,
                step = step,
            );
            (
                block,
                obtain,
                "self-anchored demonstration: this tab folded AND verified a real history end-to-end",
            )
        }
    };

    let bootstrap = format!(
        "import init, {{ verify_devnet_history, produce_external_history_envelope, genesis_vk_anchor, verify_slot_opening }} from '{pkg}';\n\
// THE PER-FIELD CLOSURE: once the history attests, bind each painted field VALUE to the\n\
// committed cell heap by verifying its per-slot opening (verify_slot_opening) tab-side.\n\
// Each genuine opening flips its field span to verified; a tampered value is REFUSED.\n\
function deosMarkPendingFields() {{\n\
  // Before the verify runs, mark every field that CARRIES an opening as unverified so it\n\
  // reads as the server's claim until its opening checks (the per-field flip target).\n\
  const island = document.getElementById('deos-openings');\n\
  if (!island) return;\n\
  let openings;\n\
  try {{ openings = JSON.parse(island.textContent); }} catch (e) {{ return; }}\n\
  (openings || []).forEach(function(o) {{\n\
    if (!o) return;\n\
    const span = document.querySelector('.deos-bind[data-bind-index=\\\"' + o.i + '\\\"]');\n\
    if (span) span.classList.add('deos-field-unverified');\n\
  }});\n\
}}\n\
function deosVerifyFields() {{\n\
  const island = document.getElementById('deos-openings');\n\
  if (!island) return;\n\
  let openings;\n\
  try {{ openings = JSON.parse(island.textContent); }} catch (e) {{ return; }}\n\
  let ok = 0, total = 0;\n\
  (openings || []).forEach(function(o) {{\n\
    if (!o) return;\n\
    const span = document.querySelector('.deos-bind[data-bind-index=\\\"' + o.i + '\\\"]');\n\
    if (!span) return;\n\
    total++;\n\
    let good = false;\n\
    try {{ good = verify_slot_opening(o.root, o.coll, o.key, o.value, o.sibs, o.dirs); }} catch (e) {{ good = false; }}\n\
    span.classList.remove('deos-field-unverified');\n\
    span.classList.add(good ? 'deos-field-verified' : 'deos-field-refused');\n\
    span.title = good ? 'field value verified: a per-slot opening checks against the committed heap root' : 'field value REFUSED: opening did not check';\n\
    if (good) ok++;\n\
  }});\n\
  return {{ ok: ok, total: total }};\n\
}}\n\
async function boot() {{\n\
  const banner = document.getElementById('deos-trust');\n\
  const detail = document.getElementById('deos-trust-detail');\n\
  const content = document.getElementById('deos-content');\n\
  deosMarkPendingFields();                         // fields with openings read as unverified until checked\n\
  try {{\n\
    await init();                                  // instantiate the wasm light client\n\
    {obtain}\n\
    if (verdict && verdict.attested) {{\n\
      const fr = (verdict.final_root || []).join(', ');\n\
      banner.className = 'deos-trust verified';\n\
      banner.textContent = '\\u2713 light-client verified \\u2014 ' + verdict.num_turns + ' finalized turns, checked in YOUR browser';\n\
      content.className = content.className.replace('deos-unverified', 'deos-verified');\n\
      const fields = deosVerifyFields();   // bind each painted field value to the committed heap\n\
      let fieldNote = '';\n\
      if (fields && fields.total > 0) {{\n\
        fieldNote = '<br>field values: ' + fields.ok + '/' + fields.total + ' verified by per-slot heap openings (the shown values provably equal the committed cell state under <code>heap_root</code>; binding <code>heap_root</code> into <code>final_root</code> is the named residual)';\n\
      }}\n\
      detail.innerHTML = 'This page reflects a genuine verified cell. The recursive STARK aggregate over its whole finalized history verified in this tab, re-witnessing nothing \\u2014 ' +\n\
        '{mode_note}.<br>commitment <code>final_root</code> = [' + fr + ']<br>engine: ' + verdict.engine + fieldNote + '<br><span class=\\\"deos-floor\\\">' + verdict.named_floor + '</span>';\n\
    }} else {{\n\
      banner.className = 'deos-trust refused';\n\
      banner.textContent = '\\u2717 UNVERIFIED \\u2014 the light client REFUSED this attestation';\n\
      detail.innerHTML = 'Treat the content below as the server\\u2019s unproven claim. ' + ((verdict && verdict.named_floor) || 'no verdict returned');\n\
    }}\n\
  }} catch (e) {{\n\
    banner.className = 'deos-trust refused';\n\
    banner.textContent = '\\u2717 attestation check failed to run';\n\
    if (detail) detail.textContent = 'the served content is unverified: ' + e;\n\
    console.error('deos trustless portal: light-client verify failed to run', e);\n\
  }}\n\
}}\n\
boot();\n",
        pkg = pkg_url,
        obtain = obtain_js,
        mode_note = mode_note,
    );

    // The per-field heap openings as an inert JSON island (read via textContent; `<`
    // neutralised so a value can never break out of the island). The bootstrap's
    // `deosVerifyFields` reads it after the history attests and verifies each opening.
    let openings_block = if openings.iter().any(|o| o.is_some()) {
        format!(
            "<script type=\"application/json\" id=\"deos-openings\">{}</script>",
            embed_json(&openings_json(openings))
        )
    } else {
        String::new()
    };

    format!(
        "<!doctype html>\n\
<html lang=\"en\">\n\
<head>\n\
<meta charset=\"utf-8\">\n\
<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
<title>{title}</title>\n\
<style>{CSS}{TRUSTLESS_CSS}</style>\n\
</head>\n\
<body>\n\
<div class=\"deos-portal\">\n\
<div class=\"deos-trust pending\" id=\"deos-trust\">&#9203; verifying the cell&rsquo;s attestation in your browser&hellip;</div>\n\
<div class=\"deos-trust-detail\" id=\"deos-trust-detail\">A light client is checking the recursive proof of this cell&rsquo;s whole finalized history &mdash; locally, trusting no server.</div>\n\
<main class=\"deos-card deos-unverified\" id=\"deos-content\">{body}</main>\n\
</div>\n\
{attest_block}\n\
{openings_block}\n\
<script>{JS}</script>\n\
<script type=\"module\">{bootstrap}</script>\n\
</body>\n\
</html>\n",
        title = escape(title),
        CSS = CSS,
        TRUSTLESS_CSS = TRUSTLESS_CSS,
        body = body,
        attest_block = attest_block,
        openings_block = openings_block,
        JS = js(),
        bootstrap = bootstrap,
    )
}

/// The portal's full stylesheet — the cockpit card palette ([`CSS`]) + the trustless trust-banner
/// states ([`TRUSTLESS_CSS`]) + the live-status strip ([`LIVE_CSS`]) + the gallery/tile grid
/// ([`GALLERY_CSS`]), concatenated. Exposed so a `portal/` generator reuses the EXACT styling the
/// baked card shell carries (no hand-copied drift): the `portal.dregg.studio` static site links
/// this verbatim, so its network view and trustless cards look like the native cockpit.
pub fn portal_css() -> String {
    format!("{CSS}{TRUSTLESS_CSS}{LIVE_CSS}{GALLERY_CSS}")
}

/// Embed a JSON string inside a `<script type="application/json">` island safely:
/// escape every `<` as the `<` JSON escape. In well-formed JSON `<` only occurs
/// inside string values, so this stays valid JSON while making the `</script>` close
/// sequence unrepresentable (the one XSS/breakout hazard of inline JSON).
fn embed_json(json: &str) -> String {
    json.replace('<', "\\u003c")
}

/// Styling for the trustless portal: the trust banner (pending / verified / refused)
/// + the attestation detail readout + the de-emphasised "unverified" card state.
/// Shares the cockpit dark palette (`CSS`'s `:root`).
const TRUSTLESS_CSS: &str = "
.deos-portal{max-width:560px;width:100%;margin:0 auto;display:flex;flex-direction:column;gap:.6rem;}
.deos-trust{padding:.55rem .8rem;border-radius:8px;font-weight:600;font-size:.92rem;border:1px solid var(--border);}
.deos-trust.pending{color:var(--muted);background:rgba(110,160,255,.06);border-color:#34384a;}
.deos-trust.verified{color:#0c1410;background:#3fb950;border-color:#3fb950;}
.deos-trust.refused{color:#fff;background:#f85149;border-color:#f85149;}
.deos-trust-detail{font-size:.78rem;color:var(--muted);line-height:1.45;padding:0 .2rem;}
.deos-trust-detail code{font-family:ui-monospace,Menlo,monospace;font-size:.72rem;color:var(--fg);word-break:break-all;}
.deos-trust-detail .deos-floor{display:block;margin-top:.35rem;font-style:italic;opacity:.85;}
.deos-card.deos-unverified{opacity:.62;filter:grayscale(.4);border-style:dashed;transition:opacity .25s,filter .25s,border-color .25s;}
.deos-card.deos-verified{opacity:1;filter:none;border-color:#3fb950;border-style:solid;transition:opacity .25s,filter .25s,border-color .25s;}
.deos-bind.deos-field-unverified{border-bottom:1px dashed var(--muted);opacity:.8;}
.deos-bind.deos-field-verified{border-bottom:1px solid #3fb950;color:#3fb950;}
.deos-bind.deos-field-verified::after{content:'\\2713';font-size:.7em;margin-left:.2em;vertical-align:super;opacity:.8;}
.deos-bind.deos-field-refused{border-bottom:1px solid #f85149;color:#f85149;}
.deos-bind.deos-field-refused::after{content:'\\2717';font-size:.7em;margin-left:.2em;vertical-align:super;}
";

/// Extra styling for the live page's status strip (the receipt-count audit readout) + the
/// unobtrusive back-link to the gallery (the card-picker home).
const LIVE_CSS: &str = "
.deos-status{margin-top:.5rem;padding:.4rem .75rem;font-size:.8rem;color:var(--muted);border-top:1px solid var(--border);}
.deos-back{position:fixed;top:1rem;left:1rem;color:var(--muted);text-decoration:none;font-size:.85rem;}
.deos-back:hover{color:var(--accent);}
";

/// Serialize a live pill's cases to a compact JSON array for the `data-cases` attribute — the
/// payload the in-tab re-read (`deosRepaintPills`) maps the live slot value against. Quotes are
/// HTML-escaped by the caller's `escape`; here we emit minimal JSON (labels/tags are short
/// status words, so a plain `\`-escape of `"`/`\` is sufficient).
fn pill_cases_json(cases: &[crate::tree::PillCase]) -> String {
    let esc = |s: &str| s.replace('\\', "\\\\").replace('"', "\\\"");
    let mut out = String::from("[");
    for (i, c) in cases.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(&format!(
            "{{\"value\":{},\"label\":\"{}\",\"tag\":\"{}\"}}",
            c.value,
            esc(&c.label),
            esc(&c.tag)
        ));
    }
    out.push(']');
    out
}

/// HTML-escape text content / attribute values (the view-tree carries author/cell data).
fn escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            _ => out.push(c),
        }
    }
    out
}

/// The card styling — mirrors the cockpit dark theme so the browser projection matches
/// the gpui `headless` dark-mode bake. `deos-vstack`/`deos-row` are flex; the button is
/// the cockpit's primary accent.
const CSS: &str = "
:root{--bg:#15161c;--fg:#ece9e3;--muted:#9a958c;--accent:#6ea0ff;--border:#2c2e36;--panel:#22242c;--card:#1b1d24;}
*{box-sizing:border-box;}
body{margin:0;background:var(--bg);color:var(--fg);font-family:'IBM Plex Sans',system-ui,sans-serif;display:flex;justify-content:center;padding:2rem;line-height:1.5;-webkit-font-smoothing:antialiased;text-rendering:optimizeLegibility;}
.deos-card{background:var(--card);border:1px solid var(--border);border-radius:12px;padding:.6rem;min-width:248px;box-shadow:0 1px 3px rgba(0,0,0,.25);}
.deos-vstack{display:flex;flex-direction:column;gap:.55rem;padding:.8rem;}
.deos-row{display:flex;flex-direction:row;gap:.5rem;align-items:center;}
.deos-text{color:var(--fg);}
.deos-bind{font-weight:600;color:var(--fg);font-variant-numeric:tabular-nums;}
.deos-input{padding:.3rem .55rem;border:1px solid var(--border);border-radius:6px;color:var(--muted);background:var(--bg);}
.deos-button{background:var(--accent);color:#101216;font-weight:600;border:none;border-radius:7px;padding:.42rem .85rem;font-family:inherit;font-size:.9rem;cursor:pointer;transition:filter .12s,transform .06s;}
.deos-button:hover{filter:brightness(1.08);}
.deos-button:active{transform:translateY(1px);}
.deos-list,.deos-table{display:flex;flex-direction:column;gap:.25rem;}
.deos-table{border:1px solid var(--border);border-radius:6px;padding:.25rem;}
.deos-section{display:flex;flex-direction:column;gap:.5rem;border:1px solid var(--border);border-radius:9px;padding:.7rem .8rem;background:rgba(255,255,255,.012);}
.deos-section[data-tag=genuine]{border-color:#3a4d6b;}
.deos-section-title{font-weight:600;font-size:.74rem;letter-spacing:.06em;text-transform:uppercase;color:var(--muted);}
.deos-tabs{display:flex;flex-direction:column;gap:.5rem;}
.deos-tabstrip{display:flex;flex-direction:row;gap:.4rem;}
.deos-tab{background:var(--panel,#22242c);color:var(--fg);border:1px solid var(--border);border-radius:6px;padding:.3rem .7rem;font:inherit;cursor:pointer;}
.deos-tab[data-index='0']{background:var(--accent);color:#fff;border-color:var(--accent);}
.deos-tabpanel{display:block;}
.deos-tabpanel:not([data-index='0']){display:none;}
.deos-gauge{display:flex;flex-direction:column;gap:.25rem;}
.deos-gauge-label{color:var(--fg);font-weight:700;}
.deos-gauge-track{width:140px;height:8px;background:var(--border);border-radius:4px;overflow:hidden;}
.deos-gauge-fill{height:8px;background:var(--fg);border-radius:4px;width:0;}
.deos-divider{border:none;border-top:1px solid var(--border);width:100%;margin:.25rem 0;}
.deos-host{display:flex;flex-direction:column;gap:.4rem;border:1px solid var(--border);border-radius:8px;padding:.5rem .6rem;}
.deos-host-head{color:var(--muted);font-size:.8rem;font-weight:600;}
.deos-host-unresolved{color:var(--muted);font-style:italic;}
.deos-inputgroup{display:inline-flex;gap:.4rem;align-items:center;}
.deos-input-submit{background:var(--accent);color:#fff;border:none;border-radius:6px;padding:.35rem .7rem;font:inherit;cursor:pointer;}
.deos-grid{display:flex;flex-wrap:wrap;gap:.5rem;}
.deos-grid[style*=grid-template]{display:grid;}
.deos-breadcrumb{display:flex;flex-direction:row;align-items:center;gap:.35rem;flex-wrap:wrap;}
.deos-crumb{color:var(--fg);}
.deos-crumb-sep{color:var(--muted);}
button.deos-crumb{background:none;border:none;color:var(--accent);cursor:pointer;font:inherit;padding:0;}
.deos-progress{display:flex;flex-direction:column;gap:.25rem;}
.deos-progress-label{color:var(--fg);font-weight:700;}
.deos-progress-track{width:140px;height:8px;background:var(--border);border-radius:4px;overflow:hidden;}
.deos-progress-fill{height:8px;background:var(--fg);border-radius:4px;}
.deos-pill{display:inline-block;padding:.15rem .55rem;border-radius:999px;font-size:.7rem;font-weight:700;letter-spacing:.05em;text-transform:uppercase;color:#fff;background:var(--accent);transition:background .15s;}
.deos-pill[data-tag=good],.deos-pill[data-tag=genuine],.deos-pill[data-tag=live]{background:#3fb950;}
.deos-pill[data-tag=warn],.deos-pill[data-tag=pending]{background:#d29922;}
.deos-pill[data-tag=bad],.deos-pill[data-tag=refusal],.deos-pill[data-tag=revoked]{background:#f85149;}
.deos-pill[data-tag=muted]{background:#9aa0aa;}
.deos-icon{font-weight:700;color:var(--accent);}
.deos-icon[data-tag=good],.deos-icon[data-tag=live]{color:#3fb950;}
.deos-icon[data-tag=warn]{color:#d29922;}
.deos-icon[data-tag=bad],.deos-icon[data-tag=refusal]{color:#f85149;}
.deos-icon[data-tag=muted]{color:#9aa0aa;}
.deos-menu{display:flex;flex-direction:column;gap:.2rem;margin:0;padding:.25rem;border:1px solid var(--border);border-radius:6px;list-style:none;}
.deos-menuitem{text-align:left;}
button.deos-menuitem{background:none;border:none;color:var(--fg);cursor:pointer;font:inherit;padding:.25rem .5rem;border-radius:4px;}
button.deos-menuitem:hover{background:var(--border);}
.deos-disabled{opacity:.4;cursor:default;padding:.25rem .5rem;}
.deos-halo{display:flex;flex-wrap:wrap;gap:.3rem;align-items:center;}
.deos-handle{width:28px;height:28px;border-radius:999px;display:inline-flex;align-items:center;justify-content:center;background:var(--panel,#22242c);border:1px solid var(--border);color:var(--fg);cursor:pointer;font:inherit;}
button.deos-handle:hover{border-color:var(--accent);}
.deos-slider{width:200px;accent-color:var(--accent);}
.deos-toggle{background:var(--panel,#22242c);color:var(--fg);border:1px solid var(--border);border-radius:6px;padding:.3rem .6rem;cursor:pointer;font:inherit;}
.deos-tile{display:flex;align-items:center;justify-content:center;border:1px solid var(--border);border-radius:6px;background:#101216;color:var(--muted);font-size:.8rem;}
";

/// The browser-side affordance wire — a button click reads its `data-turn`/`data-arg`,
/// dispatches a `deos-affordance` CustomEvent carrying that payload, AND (when an
/// in-tab dregg executor is present) fires it as a REAL cap-gated verified turn and
/// re-paints the bound slot.
///
/// The seam is closed by `wasm/src/bindings_card.rs`'s `CardWorld` — the wasm analog of
/// the native `Applet::fire`. A page that wants live turns loads the playground wasm and
/// hands the document a `window.__deosCard` with `{ fire(turn, arg) -> u64, read() -> u64 }`
/// (a `CardWorld` instance). On click this wire calls `__deosCard.fire(turn, arg)` — a
/// real `SetField + IncrementNonce` verified turn over the embedded executor, leaving a
/// receipt — then writes the returned value into the matching `data-slot` `deos-bind`
/// span (the SolidJS-shaped signal re-render, mirroring the native `bind` re-read).
///
/// With NO `__deosCard` bound (a static bake), the click still dispatches the
/// `deos-affordance` event so the affordance payload is observable; the live turn is the
/// embedding's to wire (load the wasm + bind a `CardWorld`). Either way the click carries
/// exactly the `{turn, arg}` the native `Button` fires through `Applet::fire`.
const JS: &str = "
function deosReadSlot(card, slot){
  // The witnessed read off the live ledger for ONE bound slot (`Applet::get_u64`). The
  // counter's `CardWorld.read()` takes no arg (single slot 0); the inspector's
  // `InspectorWorld.read(slot)` takes the slot (it binds several). Dispatch on arity so the
  // SAME wire drives both cards.
  return card.read.length > 0 ? card.read(slot) : card.read();
}
function deosRepaintBinds(card){
  // Re-read the live ledger for every bound slot and repaint it — the witnessed read the
  // native `bind` makes, here `card.read(slot)`. Each `deos-bind` span carries its own
  // `data-slot`, so a multi-field card (the inspector) repaints each row from ITS slot.
  // CONSUMER-DELIGHT: a span carrying `data-label`+`data-fmt` re-formats through the shared
  // `deosFmt` mirror (so a friendly handle/hex stays friendly on re-read); a legacy span (no
  // data-label) falls back to the trailing-digit replace.
  document.querySelectorAll('.deos-bind[data-slot]').forEach(function(span){
    var slot = parseInt(span.getAttribute('data-slot') || '0', 10);
    var raw = deosReadSlot(card, slot);
    var label = span.getAttribute('data-label');
    if (label !== null && typeof deosFmt === 'function') {
      span.textContent = label + deosFmt(raw, span.getAttribute('data-fmt') || 'raw');
    } else {
      span.textContent = span.textContent.replace(/[0-9]+$/, '') + raw;
    }
  });
  deosRepaintPills(card);
}
function deosRepaintPills(card){
  // A LIVE pill re-reads its bound slot and maps the value to the matching case's word + color
  // (the static phase-word cure) — the witnessed read the native pill makes.
  document.querySelectorAll('.deos-pill[data-slot][data-cases]').forEach(function(p){
    var slot = parseInt(p.getAttribute('data-slot') || '0', 10);
    var v = deosReadSlot(card, slot);
    try {
      var cases = JSON.parse(p.getAttribute('data-cases') || '[]');
      for (var i=0;i<cases.length;i++){
        if (String(cases[i].value) === String(v)) {
          p.textContent = cases[i].label;
          p.setAttribute('data-tag', cases[i].tag);
          break;
        }
      }
    } catch(e) { /* a malformed cases blob leaves the static first paint — honest, never a crash */ }
  });
}
document.querySelectorAll('.deos-button').forEach(function(b){
  b.addEventListener('click', function(){
    var turn = b.getAttribute('data-turn');
    var arg = parseInt(b.getAttribute('data-arg') || '0', 10);
    // Always surface the affordance payload (observable, never papered).
    document.dispatchEvent(new CustomEvent('deos-affordance', {detail:{turn:turn, arg:arg}}));
    // THE LIVE TURN: if an in-tab executor (a `CardWorld`) is bound, fire the affordance
    // as a REAL cap-gated verified turn and re-paint the bound slots from the new model.
    var card = window.__deosCard;
    if (card && typeof card.fire === 'function') {
      try {
        card.fire(turn, arg);   // real SetField + IncrementNonce verified turn → receipt
        deosRepaintBinds(card); // the bind re-reads the committed ledger
      } catch (e) {
        console.error('deos affordance refused (no turn committed):', turn, arg, e);
      }
    } else {
      console.log('deos affordance (no in-tab executor bound):', turn, arg);
    }
  });
});
// THE EXTENDED INPUT — a submit button fires `{turn, arg=the paired field value}` (input →
// verified turn). `data-arg-from` names the `<input>` whose value becomes the arg.
document.querySelectorAll('.deos-input-submit[data-arg-from]').forEach(function(b){
  b.addEventListener('click', function(){
    var turn = b.getAttribute('data-turn');
    var key = b.getAttribute('data-arg-from');
    var field = document.querySelector('.deos-input[data-bind-view=\"' + key + '\"]');
    var arg = parseInt((field && field.value) || '0', 10) || 0;
    document.dispatchEvent(new CustomEvent('deos-affordance', {detail:{turn:turn, arg:arg}}));
    var card = window.__deosCard;
    if (card && typeof card.fire === 'function') {
      try { card.fire(turn, arg); deosRepaintBinds(card); }
      catch (e) { console.error('deos input submit refused:', turn, arg, e); }
    }
  });
});
// THE SLIDER / SCRUBBER — a range input fires `{turn, arg=the value}` on change (seek).
document.querySelectorAll('.deos-slider[data-turn]').forEach(function(s){
  s.addEventListener('change', function(){
    var turn = s.getAttribute('data-turn');
    var arg = parseInt(s.value || '0', 10) || 0;
    document.dispatchEvent(new CustomEvent('deos-affordance', {detail:{turn:turn, arg:arg}}));
    var card = window.__deosCard;
    if (card && typeof card.fire === 'function') {
      try { card.fire(turn, arg); deosRepaintBinds(card); }
      catch (e) { console.error('deos slider seek refused:', turn, arg, e); }
    }
  });
});
// THE TOGGLE — a click fires the off-turn when currently on, else the on-turn (the live slot
// picks the direction + the glyph). Reads the slot off the in-tab executor.
document.querySelectorAll('.deos-toggle[data-slot]').forEach(function(t){
  t.addEventListener('click', function(){
    var slot = parseInt(t.getAttribute('data-slot') || '0', 10);
    var card = window.__deosCard;
    var on = false;
    if (card && typeof card.read === 'function') { on = deosReadSlot(card, slot) != 0; }
    var turn = on ? t.getAttribute('data-off-turn') : t.getAttribute('data-on-turn');
    document.dispatchEvent(new CustomEvent('deos-affordance', {detail:{turn:turn, arg:0}}));
    if (card && typeof card.fire === 'function' && turn) {
      try {
        card.fire(turn, 0);
        deosRepaintBinds(card);
        var nowOn = deosReadSlot(card, slot) != 0;
        t.textContent = (nowOn ? t.getAttribute('data-glyph-on') : t.getAttribute('data-glyph-off')) + t.textContent.slice(1);
      } catch (e) { console.error('deos toggle refused:', turn, e); }
    }
  });
});
";

#[cfg(test)]
mod trustless_tests {
    use super::*;
    use crate::tree::ViewNode;

    /// The minimal served card: a titled counter binding slot 0.
    fn counter() -> ViewNode {
        ViewNode::VStack(vec![
            ViewNode::Text("Counter".into()),
            ViewNode::Bind {
                slot: 0,
                label: "count: ".into(),
                fmt: crate::fmt::BindFmt::Raw,
            },
            ViewNode::Button {
                label: "+1".into(),
                turn: "inc".into(),
                arg: 1,
            },
        ])
    }

    /// THE TRUSTLESS PORTAL CONTRACT (in-tab demo). The served content is the card
    /// rendered to HTML; the page carries the trust banner + the unverified-by-default
    /// card + a module bootstrap that runs the REAL wasm light-client verify, gating the
    /// "verified" flip on `verdict.attested`.
    #[test]
    fn trustless_portal_serves_card_and_gates_on_light_client() {
        let doc = render_trustless_cell_document(
            "trustless counter",
            &counter(),
            &[0],
            &[],
            &TrustlessAttestation::InTabDemo { k: 3, step: 7 },
            "./pkg/dregg_wasm.js",
        );
        // The served content IS the cell's card.
        assert!(doc.contains("count: 0") && doc.contains("data-turn=\"inc\""));
        // The light-client verify is the trust gate (not a server claim).
        assert!(doc.contains("import init, { verify_devnet_history"));
        assert!(doc.contains("produce_external_history_envelope(3, 7n)"));
        assert!(doc.contains("verify_devnet_history(env, anchor)"));
        // The card starts unverified; the flip is gated on a real attestation.
        assert!(doc.contains("deos-unverified") && doc.contains("verdict.attested"));
        assert!(doc.contains("id=\"deos-trust\""));
        // With no openings carried, no field-opening island is emitted.
        assert!(!doc.contains("id=\"deos-openings\""));
    }

    /// THE SERVED-PLAIN CLOSURE WIRING. When per-field heap openings are carried, the page
    /// imports `verify_slot_opening`, embeds the openings as an inert JSON island, tags the
    /// bind span with its `data-bind-index`, and the bootstrap binds each field VALUE to the
    /// committed heap (the field flips to verified on a checking opening). The cryptographic
    /// correctness of the opening verify is covered in `wasm::bindings_lightclient`.
    #[test]
    fn trustless_portal_carries_and_wires_per_field_heap_openings() {
        let opening = HeapSlotOpening {
            root: 12345,
            coll: 0,
            key: 0,
            value: 0,
            siblings: vec![0; 16],
            directions: vec![0; 16],
        };
        let doc = render_trustless_cell_document(
            "trustless counter",
            &counter(),
            &[0],
            &[Some(opening)],
            &TrustlessAttestation::InTabDemo { k: 2, step: 1 },
            "./pkg/dregg_wasm.js",
        );
        // The bind span carries its stable tree-walk index (the opening key).
        assert!(doc.contains("data-bind-index=\"0\""));
        // The per-slot opening verify is imported and called.
        assert!(doc.contains("verify_slot_opening"));
        // The openings ride as an inert JSON island, keyed by bind index.
        assert!(doc.contains("id=\"deos-openings\""));
        assert!(doc.contains("\"i\":0") && doc.contains("\"root\":12345"));
        // The field flips from unverified to verified/refused on its opening.
        assert!(doc.contains("deos-field-unverified") && doc.contains("deos-field-verified"));
        assert!(doc.contains("deosVerifyFields"));
    }

    /// THE CONFIG-NOT-ARTIFACT SHAPE (server-supplied). The envelope is embedded as an
    /// inert JSON island; the config anchor is a SEPARATE input the verify runs against;
    /// a `</script>` in the envelope cannot break out of the island.
    #[test]
    fn trustless_portal_server_supplied_embeds_envelope_and_config_anchor() {
        let anchor = "ab".repeat(32);
        let doc = render_trustless_cell_document(
            "gateway counter",
            &counter(),
            &[0],
            &[],
            &TrustlessAttestation::ServerSupplied {
                envelope_json: r#"{"version":1,"note":"</script><b>x</b>","num_turns":2}"#,
                config_anchor_hex: &anchor,
            },
            "./pkg/dregg_wasm.js",
        );
        assert!(doc.contains("application/json\" id=\"deos-attestation\""));
        assert!(doc.contains(&format!("const anchor = '{anchor}'")));
        assert!(doc.contains("verify_devnet_history(env, anchor)"));
        // The breakout `</script>` is neutralised (escaped `<`), never raw in the island.
        assert!(!doc.contains("</script><b>x</b>"));
        assert!(doc.contains("\\u003c/script>\\u003cb>x\\u003c/b>"));
    }
}
