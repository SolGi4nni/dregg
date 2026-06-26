# deos from the web

← [guide index](README.md) · [build with dregg](BUILD-WITH-DREGG.md)

deos runs in a browser tab. The real `dregg-cell` / `dregg-turn` ledger and the
verified `TurnExecutor` compile to `wasm32` and run *in-tab* — not a mock, not a
recorded crawl, and **no node**. A button click commits a real cap-gated verified
turn over the embedded executor and re-paints from the committed ledger.

## What deos is in a browser

Three pieces fit together:

1. **A renderer-independent view-tree.** A deos card produces a serializable
   `ViewNode` tree — an enum of `VStack`, `Row`, `Text`, `Bind { slot }`,
   `Button { turn, arg }`, `Input`, `List`, `Table` (`deos-view/src/tree.rs`).
   The card is GPUI-free data; the renderer is separate.

2. **Two renderers, one tree.** `deos-view` holds a `native` renderer (gpui
   pixels) and a `web` renderer (an HTML string), each walking the *same* tree
   node-for-node (`deos-view/src/web.rs`). The browser projection matches the
   native bake.

3. **An in-tab executor closing the live-turn seam.** `wasm/src/bindings_card.rs`
   is the wasm analog of the native applet: `CardWorld` / `InspectorWorld` own one
   `DreggRuntime` with a card-cell; `fire(turn, arg)` issues `Effect::SetField` +
   `Effect::IncrementNonce` through the same `execute_turn_for_agent` path native
   callers use, and `read(slot)` is a witnessed ledger read.

Because the executor is real, the guarantees are real in the tab. The
KV-store card refuses a version rollback (its program's `Monotonic` constraint
bites on the verified commit path); the inspector card's `SurfaceIdentity` badge
is read from the live ledger, so a label that lies about its owner is impossible.

The whole-history light client folds in the tab too:
`wasm/src/bindings_lightclient.rs` wraps `dregg-lightclient::verify_history` —
fold a finalized history into one succinct recursive aggregate and verify it
re-witnessing nothing, anchored to a VK fingerprint (a tampered anchor is refused
with `VkFingerprintMismatch`). See [`docs/reference/wasm-web.md`](../reference/wasm-web.md)
and [`docs/reference/deos-view.md`](../reference/deos-view.md).

## Run the live cards

One script builds the wasm bundle, bakes the card pages, and serves them (each
page is a module-import plus a `.wasm` fetch, so it must be served over HTTP —
`file://` is CORS-blocked):

```sh
scripts/serve-deos-card.sh            # build + bake + serve on http://localhost:8000
```

The served pages:

| page | card | what a click does |
|---|---|---|
| `/` | gallery | a card-picker of clickable tiles (plain HTML, no wasm) |
| `/counter.html` | `CardWorld` | `+1` commits a `SetField + IncrementNonce` turn; the bound count re-paints |
| `/tally.html` | `TallyWorld` | the full layout vocabulary (Row + Table); each `+1`/`−1` moves one tally |
| `/kvstore.html` | `KvStoreWorld` | `put`/`del` route through the cell's `InterfaceDescriptor` (the verified DFA) before desugaring; a rollback is refused; `get` is a named seam |
| `/inspector.html` | `InspectorWorld` | a reflective cockpit surface — click an affordance, a real turn fires, the bound field re-paints |
| `/doccollab.html` | `DocCollabWorld` | Pijul in a tab: `stitch` two authors (the pushout) → a first-class conflict → click a resolution → the merged doc publishes as a verified turn |

Headless end-to-end drivers exercise each page over the Chrome DevTools Protocol
(they assert the rendered DOM, click affordances, read the live ledger, and check
that the guarantee bites):

```sh
node scripts/drive-deos-kvstore.mjs   http://localhost:8000/kvstore.html
node scripts/drive-deos-tally.mjs     http://localhost:8000/tally.html
node scripts/drive-deos-inspector.mjs http://localhost:8000/inspector.html
node scripts/drive-deos-doccollab.mjs http://localhost:8000/doccollab.html
```

(Node ≥ 22 — built-in `fetch` + `WebSocket`, no npm deps. Chrome via `$CHROME`.)

## How to build a web-deos card-app

A card is the `ViewNode` pattern: author a tree, tag each `Bind` with the model
slot it re-reads, and tag each `Button` with the `{turn, arg}` affordance it
fires. The browser-side wire reads `data-turn`/`data-arg` on a click, calls
`card.fire(turn, arg)` (a real verified turn over the in-tab executor), then
re-paints every bound slot from `card.read(slot)`.

The minimal path:

1. **Render the tree.** `deos-view/src/web.rs` turns a `ViewNode` into HTML:
   `render_html(tree, bind_values)` for a fragment, or `render_card_live_document`
   to wrap it in a standalone page that imports the playground wasm and binds an
   in-tab `CardWorld` to `window.__deosCard`. The smallest baked example is
   `deos-view/examples/web_render_card.rs` (gpui-free):

   ```sh
   # deos-view is its own workspace root, so run from inside it:
   cd deos-view && cargo run --no-default-features --features web --example web_render_card
   ```

2. **Close the turn seam.** Back the page with a `CardWorld` (a single card-cell,
   one model slot) or extend the pattern with your own `#[wasm_bindgen]` world in
   `wasm/src/` that owns a `DreggRuntime` and exposes `fire` / `read`. The
   `KvStoreWorld` and `DocCollabWorld` on the served pages show richer worlds — a
   published service interface and a document with conflict objects.

3. **Serve it.** Add your baked page to the dist that `scripts/serve-deos-card.sh`
   assembles, or serve the directory yourself (`python3 -m http.server`).

Because the tree is renderer-independent, the same card you build for the browser
also renders to native gpui pixels through `deos-view`'s `native` renderer with
fine-grained, signal-driven re-render (`deos-view/src/render.rs`).

## The cockpit in the browser

Beyond single cards, the whole cockpit model runs in the tab. `starbridge-v2/web/`
(`starbridge-web`) exposes `WebImage` — a JSON skin over the real
`starbridge_v2::World` whose `survey` / `inspect` / `affordances` / `act` / `ocap`
methods each drive the embedded verified executor (`act` fires a real cap-gated
turn and returns the receipt). A `gpui-web` feature additionally runs the gpui
cockpit on WebGPU. See [`docs/reference/wasm-web.md`](../reference/wasm-web.md) §
`starbridge-web`.

## Where to go next

- The model and SDK these cards run on: [Build with dregg](BUILD-WITH-DREGG.md).
- More buildable shapes: [What you can build](WHAT-YOU-CAN-BUILD.md).
- The web vision in full: `docs/deos/WEB-DEOS.md`, `docs/deos/WEB-CELLS.md`.
