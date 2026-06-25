# deos-view — rendering a deos-js view-tree (native gpui, web HTML)

`deos-view` is the renderer-extraction crate: `deos-js` stays GPUI-free and produces a
*serializable* `deos.ui.*` element-tree; `deos-view` holds the two renderers that turn
that DATA into a surface. One view-tree, two renderers — the card is
renderer-independent (`src/lib.rs:1`–`24`).

Crate layout: a renderer-independent view-tree MODEL, plus a `native` renderer (gpui-
component pixels) and a `web` renderer (HTML string), each behind a feature
(`src/lib.rs:26`–`58`). `native` is the default; `web` is `[]` (`Cargo.toml:107`–`121`).
The crate is its own `[workspace]` root because it path-deps both the mozjs SpiderMonkey
elephant (via deos-js) and the gpui native stack (`Cargo.toml:22`–`29`).

## The view-tree model (`src/tree.rs`) — always compiled

`ViewNode` is the typed Rust mirror of the JS `deos.ui.*` shape, an enum of variants
`VStack`, `Row`, `Text`, `Bind { slot, label }`, `Button { label, turn, arg }`,
`Input { bind_view }`, `List`, `Table` (`src/tree.rs:22`–`48`). It is gpui-free
serializable data, compiled under both renderers (`src/lib.rs:26`–`29`).

The wire format is `RawNode { kind, props, children }` with an all-optional
`RawProps` bag (`src/tree.rs:53`–`83`). `RawNode::lift` maps each `kind` string to a
typed variant; an unknown kind becomes `Text("‹unmapped node: {other}›")` — the renderer
shows what it could not map (`src/tree.rs:96`–`124`). `parse_view_tree` is `serde_json`
then `lift` (`src/tree.rs:128`–`131`).

Two serialization facts the model encodes:
- A `bind` carries only `kind:"bind"` after `JSON.stringify` (the closure
  `node.read` is dropped), so the author tags the node with `props.slot` (the model slot
  to re-read); absent ⇒ slot 0 (`src/tree.rs:78`–`83`, `src/tree.rs:102`–`105`).
- The JS prelude emits camelCase `onClick`; `RawProps::on_click` is
  `#[serde(rename = "onClick", alias = "on_click")]` so the `{turn, arg}` affordance
  survives the parse into both renderers (`src/tree.rs:69`–`75`).

## The bridge (`src/bridge.rs`, native) — drive JS, extract the tree

`build_live_view` runs an applet's JS in real SpiderMonkey and extracts its view-tree
(`src/bridge.rs:53`–`72`):
1. `set_current_applet(applet)` installs the applet on the thread-local the JS natives
   drive;
2. `rt.eval(applet_js)` runs JS that builds the tree with `deos.ui.*`, tags each `bind`'s
   slot, and stashes `JSON.stringify(tree)` into ephemeral view-state under
   `"__deos_view_tree"` (`src/bridge.rs:26`, `src/bridge.rs:39`–`51`);
3. `take_current_applet` reclaims the applet and `get_view(VIEWTREE_KEY)` reads the string
   back; `parse_view_tree` lifts it.

The result is a `LiveView { applet: Applet, tree: ViewNode }` — the `Applet` is the live
substance (its `fire` is a real cap-gated verified turn, `get_u64` a witnessed read), and
the `ViewNode` is the element-tree the engine actually produced (`src/bridge.rs:31`–`37`,
`src/bridge.rs:1`–`17`). Building the tree commits nothing; only firing a button does
(`src/bridge.rs:52`).

## The native renderer (`src/render.rs`) — `ViewNode` → gpui-component widgets

`AppletView` is a gpui `Render` entity that walks the tree into gpui-component widgets:
`vstack→v_flex`, `row→h_flex`, `text→Label`, `button→Button`, `input→`bordered field,
`list`/`table`→`v_flex` of children (`src/render.rs:207`–`302`). The vocabulary is the
gpui-component fork (`Button`, `Label`, `v_flex`/`h_flex`; `src/render.rs:45`–`53`).

Two nodes carry behavior:
- **`Button`** — `on_click` calls `applet.borrow_mut().fire(&turn, arg)`, a REAL
  cap-gated verified turn; a refusal/reject is printed to stderr and the model simply
  does not advance (`src/render.rs:245`–`264`). The button id is salted by an FNV-1a hash
  of its label so two buttons differ (`src/render.rs:327`–`335`).
- **`Bind`** — a bold `Label` re-read off the live ledger via the fine-grained signal
  path below (`src/render.rs:227`–`244`).

`SharedApplet = Rc<RefCell<Applet>>` is the one shared handle every widget reads/fires
through — the single sovereign cell behind the whole view (`src/render.rs:55`–`59`).

### Fine-grained re-render (the signal hook)

`AppletView` welds in deos-js's `BindingRegistry` (the reverse index
`(cell, slot) → bindings`, from `deos-js/src/signals.rs:83`) so a committed turn re-reads
ONLY the affected binds — the SolidJS-shaped re-render (`src/render.rs:16`–`36`):

- At construction `bind_plan` walks the tree once in pre-order, collecting each `bind`'s
  slot; the Nth bind becomes `BindingId(n)` and is `register`ed on `(applet.cell(), slot)`
  (the cell is constant — the applet's sovereign cell) (`src/render.rs:65`–`76`,
  `src/render.rs:117`–`137`).
- A per-binding value `cache: BTreeMap<BindingId, u64>` holds each bind's last-read value;
  a `bind` paints out of the cache, filling it lazily off the live ledger on first paint
  (`next_bind_value`, `src/render.rs:195`–`203`). `render` resets `render_cursor` to 0 so
  the Nth painted bind maps to `BindingId(n)`, the same order `bind_plan` registered
  (`src/render.rs:305`–`309`).
- `on_committed_turn(touched_slots)` is the hook: it builds `SourceEvent`s, calls
  `registry.invalidate_all` to get exactly the dirty bindings, and re-reads ONLY those
  into the cache via `registry.reread(.., |_, slot| app.get_u64(slot))`; clean bindings
  keep their cached value untouched (`src/render.rs:152`–`173`). `last_dirty` exposes the
  dirty set from the last turn (the test bar; `src/render.rs:108`–`111`,
  `src/render.rs:175`–`179`).

First paint is still immediate-mode (an un-driven view is always correct); the
fine-grained path is the incremental update a committed turn drives
(`src/render.rs:33`–`36`).

## The faces view (`src/faces.rs`, native) — `present()` through the same vocabulary

`FacesView` renders a cell's moldable `present()` faces (RawFields · Graph · DomainVisual
· Provenance) through the SAME `Label`/`v_flex`/`h_flex` widgets the applet view uses —
the §7 unification: inspector and custom view share widgets (`src/faces.rs:1`–`13`). It
reads the faces off the live ledger via deos-js's gpui-free
`reflect_binding::cell_present_json` (`src/faces.rs:59`–`61`), deserializes them
(`Face { kind, label, body }`; only the RawFields body is rendered structurally, other
bodies render as a one-line tag — `src/faces.rs:22`–`55`, `src/faces.rs:83`–`102`), and
paints a titled `v_flex` of `key: value` rows. Display strings are formatted ONCE at
construction (`RenderedFace::from_face`) since the parsed faces are immutable
(`src/faces.rs:64`–`102`, `src/faces.rs:127`–`176`).

## Headless capture (`src/headless.rs`, native) — bake a view to PNG

`HeadlessRender` is a reusable harness over the SAME offscreen path starbridge-v2's
`render_cockpit_headless` uses: `HeadlessAppContext::with_platform` +
`gpui_platform::current_headless_renderer` (offscreen wgpu) + `CosmicTextSystem`, baking
any `Render` view to an `RgbaImage` (`src/headless.rs:1`–`11`, `src/headless.rs:29`–`51`).
`boot` registers fonts (no system fonts ⇒ deterministic), inits gpui-component, and forces
the dark theme — exactly as the cockpit bake does (`src/headless.rs:34`–`51`). It keeps the
app live across captures so a test can render, fire a turn, drive
`AppletView::on_committed_turn` via `update_root`, and capture an advanced frame
(`src/headless.rs:11`–`12`, `src/headless.rs:80`–`98`). The headless window reports a 2.0
scale factor, so captures are 2w×2h device pixels (`src/headless.rs:69`–`74`).

## The web renderer (`src/web.rs`, web) — the IDENTICAL view-tree → HTML

The `web` renderer is gpui-FREE and deos-js-FREE (only serde): it depends on nothing but
`tree`, so `--no-default-features --features web` compiles a tiny graph with no GPU and no
SpiderMonkey (`src/web.rs:9`–`13`, `Cargo.toml:120`–`121`). Its walker mirrors the native
`AppletView::node` node-for-node (`src/web.rs:64`–`136`):

| node | native (`render.rs`) | web (`web.rs`) |
|---|---|---|
| `vstack`/`row` | `v_flex`/`h_flex` | `<div class="deos-vstack/row">` |
| `text` | `Label` | `<span class="deos-text">` |
| `bind{slot,label}` | bold `Label`, live re-read | `<span class="deos-bind" data-slot=…>` |
| `button{turn,arg}` | `Button`, onClick fires turn | `<button data-turn data-arg>` |
| `input`/`list`/`table` | field / `v_flex` | `deos-input`/`deos-list`/`deos-table` |

(table at `src/web.rs:14`–`24`.) `render_html(tree, bind_values)` produces the fragment;
`bind_values[n]` is the live value of the Nth bind in the same tree-walk order the native
`bind_plan` mints `BindingId`s in, missing index ⇒ 0 (`src/web.rs:47`–`62`). A `bind`
emits its value AND `data-slot` (so a browser re-read knows which slot to refresh); a
`button` emits `data-turn`/`data-arg` — the exact payload a click must fire
(`src/web.rs:86`–`113`). All text/attribute content is HTML-escaped (`src/web.rs:423`–`436`).

### Documents and the live turn

- `render_card_document` wraps a fragment in a standalone page with the cockpit dark CSS
  and the affordance-wire `JS` (`src/web.rs:142`–`162`).
- `render_card_live_document` and `render_inspector_live_document` additionally emit an ES-
  module bootstrap that `import`s the playground wasm, mints an in-tab `CardWorld` /
  `InspectorWorld` (the wasm analog of the native `Applet`, `wasm/src/bindings_card.rs`),
  binds it to `window.__deosCard`, and re-paints each `data-slot` bind from the committed
  ledger (`src/web.rs:177`–`240`, `src/web.rs:262`–`333`). The inspector carries several
  bound slots and repaints each from its own `data-slot` via `read(slot)`
  (`src/web.rs:254`–`291`).
- `render_gallery_document` is a plain-HTML card-picker home page of clickable tiles
  (`GalleryCard { href, name, blurb }`), no wasm (`src/web.rs:338`–`396`).

The browser-side `JS` wire: a `.deos-button` click reads `data-turn`/`data-arg`, always
dispatches a `deos-affordance` CustomEvent (so the payload is observable even on a static
bake), and — when `window.__deosCard` is bound — calls `card.fire(turn, arg)` (a real
`SetField + IncrementNonce` verified turn over the embedded executor, per the module docs)
then re-paints every bound slot from `card.read(slot)` (`src/web.rs:457`–`513`). It
dispatches on `card.read` arity so the same wire drives both the single-slot counter
(`read()`) and the multi-slot inspector (`read(slot)`) (`src/web.rs:475`–`491`).

The card's CSS mirrors the cockpit dark theme so the browser projection matches the gpui
headless dark-mode bake (`src/web.rs:438`–`455`). The wasm executor that closes the live-
turn seam (`CardWorld::fire`/`read`, `InspectorWorld`) lives in `wasm/src/bindings_card.rs`
(`wasm/src/bindings_card.rs:61`, `:102`, `:124`, `:209`, `:299`, `:317`).

## Tests / examples

`tests/` exercises both renderers: `fine_grained_rerender.rs` (a two-bind scene asserts a
turn on slot A dirties binding A but not B, constructing `AppletView` gpui-free —
`tests/fine_grained_rerender.rs:1`–`13`), the `renders_*_to_pixels.rs` headless-bake
tests, and `web_projection_renders_card.rs`. `examples/web_render_card.rs` bakes the same
counter card the native test paints to a browser-loadable `.html`, gpui-free
(`examples/web_render_card.rs:1`–`17`); it is `required-features = ["web"]`
(`Cargo.toml:126`–`128`).
