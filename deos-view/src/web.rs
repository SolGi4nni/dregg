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
        ViewNode::Input { bind_view } => {
            out.push_str(&format!(
                "<span class=\"deos-input\" data-bind-view=\"{}\">&lsaquo;{}&rsaquo;</span>",
                escape(bind_view),
                escape(bind_view)
            ));
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
";
