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
        ViewNode::Bind { slot, label } => {
            // THE SIGNAL BINDING — paint the live value (the same witnessed read the JS
            // closure / gpui `bind` made), and carry `data-slot` so a browser re-read
            // after a turn knows which slot to refresh (the fine-grained signal source).
            let value = binds.get(*cursor).copied().unwrap_or(0);
            *cursor += 1;
            let text = if label.is_empty() {
                value.to_string()
            } else {
                format!("{label}{value}")
            };
            out.push_str(&format!(
                "<span class=\"deos-bind\" data-slot=\"{slot}\">{}</span>",
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
        ViewNode::Pill { text, tag } => {
            out.push_str(&format!(
                "<span class=\"deos-pill\" data-tag=\"{}\">{}</span>",
                escape(tag),
                escape(text)
            ));
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
        JS = JS,
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
        JS = JS,
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
        JS = JS,
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
        JS = JS,
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
        JS = JS,
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
        JS = JS,
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

/// Extra styling for the live page's status strip (the receipt-count audit readout) + the
/// unobtrusive back-link to the gallery (the card-picker home).
const LIVE_CSS: &str = "
.deos-status{margin-top:.5rem;padding:.4rem .75rem;font-size:.8rem;color:var(--muted);border-top:1px solid var(--border);}
.deos-back{position:fixed;top:1rem;left:1rem;color:var(--muted);text-decoration:none;font-size:.85rem;}
.deos-back:hover{color:var(--accent);}
";

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
:root{--bg:#121317;--fg:#e6e7eb;--muted:#9aa0aa;--accent:#5b8cff;--border:#2a2c33;}
*{box-sizing:border-box;}
body{margin:0;background:var(--bg);color:var(--fg);font-family:'IBM Plex Sans',system-ui,sans-serif;display:flex;justify-content:center;padding:2rem;}
.deos-card{background:#181a20;border:1px solid var(--border);border-radius:10px;padding:.5rem;min-width:240px;}
.deos-vstack{display:flex;flex-direction:column;gap:.5rem;padding:.75rem;}
.deos-row{display:flex;flex-direction:row;gap:.5rem;align-items:center;}
.deos-text{color:var(--fg);}
.deos-bind{font-weight:700;color:var(--fg);}
.deos-input{padding:.25rem .5rem;border:1px solid var(--border);border-radius:4px;color:var(--muted);}
.deos-button{background:var(--accent);color:#fff;border:none;border-radius:6px;padding:.4rem .8rem;font:inherit;cursor:pointer;}
.deos-button:hover{filter:brightness(1.1);}
.deos-list,.deos-table{display:flex;flex-direction:column;gap:.25rem;}
.deos-table{border:1px solid var(--border);border-radius:6px;padding:.25rem;}
.deos-section{display:flex;flex-direction:column;gap:.4rem;border:1px solid var(--border);border-radius:6px;padding:.5rem .6rem;}
.deos-section[data-tag=genuine]{border-color:var(--fg);}
.deos-section-title{font-weight:700;color:var(--fg);}
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
.deos-pill{display:inline-block;padding:.1rem .5rem;border-radius:999px;font-size:.78rem;font-weight:600;color:#fff;background:var(--accent);}
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
  document.querySelectorAll('.deos-bind[data-slot]').forEach(function(span){
    var slot = parseInt(span.getAttribute('data-slot') || '0', 10);
    var label = span.textContent.replace(/[0-9]+$/, '');
    span.textContent = label + deosReadSlot(card, slot);
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
