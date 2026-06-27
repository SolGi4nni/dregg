# deos-view richness expansion — growing the card vocabulary to native-cockpit parity

The framing, stated once and held throughout: **we are not shrinking the cockpit surfaces
to fit deos-view; we are growing deos-view until liberating a native surface into a portable
card costs none of the native awesomeness.** The hand-built gpui element trees in
`starbridge-v2/src/cockpit/panels_*.rs` are THE BAR. Every primitive they use — tab-strips,
the Pharo Halo handle-ring, scrubbers, gauges, the spatial wonder-grid, styled sections,
right-click actuation menus, the Servo tile, input bound to a turn arg — becomes a
first-class `deos.ui.*` node. A migrated surface then renders IDENTICAL to its native tree,
and additionally gains what the native tree never had: it is renderer-independent (gpui,
web, discord paint the same data), agent-rewritable (a receipted `ViewPatch`), and
progressively disclosable (one card, two projections).

This document is the design. It is comprehensive on the target node set; §6 names the first
batch implemented in `deos-view/src/tree.rs` + the renderers in this same change.

---

## 0. What exists (the substrate the expansion extends)

`deos-view/src/tree.rs` is the renderer-independent `ViewNode` IR (gpui-free serializable
DATA, always compiled). Four renderers walk it:

- `render.rs` — `AppletView`, `ViewNode` → real gpui-component widgets (the native cockpit).
- `web.rs` — `ViewNode` → an HTML/DOM string (the browser projection).
- `discord.rs` — `ViewNode` → a serenity `CreateEmbed` + button grid (the chat projection).
- `faces.rs` — the moldable `present()` faces through the same widget vocabulary.

The wire format is `{kind, props, children}`; `RawNode::lift` maps a kind string to a typed
`ViewNode`; **an unknown kind renders as a visible `‹unmapped node: …›` placeholder** (the
honest fallback — so a card authored against a newer vocabulary degrades, never crashes).

Two load-bearing serialization facts the expansion preserves:

1. A `bind`'s closure is dropped by `JSON.stringify`; the author tags the node with
   `props.slot`, and the renderer re-reads `(cell, slot)` off the live ledger. Every
   new node that shows live state names its slot the same way.
2. A button's affordance survives as `props.onClick = {turn, arg}` (camelCase, snake alias).
   Every new actuating node (tab, menu item, halo handle, slider, toggle) carries its
   affordance in exactly this `{turn, arg}` shape, so the cap-gated-verified-turn routing
   (`Applet::fire` → `is_attenuation` gate → executor → receipt) is reused unchanged.

The fine-grained re-render (`render.rs`'s `BindingRegistry` + per-binding value cache)
re-reads ONLY the binds a committed turn dirtied. The expansion keeps the **tree-walk
(pre-order) bind cursor** invariant: `bind_plan` (registration) and every renderer's walk
visit `Bind` nodes in the SAME order, so the Nth `Bind` is always `BindingId(n)`. New
container nodes (`section`, `tabs`, `grid`, `menu`) recurse their children in declaration
order; new bound-but-not-`Bind` nodes (`gauge`, `slider`, `toggle`) read their slot
immediate-mode and do NOT consume the bind cursor (they may later opt into the registry).

---

## 1. The full rich node vocabulary (toward gpui-component parity + cockpit richness)

Each node below gives: its `deos.ui.*` wire shape (the serde_json `props`), the native
surface it unlocks, and the gpui-paint contract. The existing 8 (`vstack row text bind
button input list table`) are unchanged.

### Containers & structure

**`section`** — a titled, bordered container (the uniform "styled section").
- shape: `{ kind:"section", props:{ title, tag? }, children:[…] }`
- unlocks: `Organs` (sectioned read-only), the `Trust` guardian/device blocks, `Devtools`
  drill-down groups, every panel's `section_title` + bordered box idiom.
- paint: a `v_flex().gap_1().p_2().border_1()`; `title` a bold `Label`; `tag` selects the
  border accent (the existing `props.tag` styling convention — `genuine`/`refusal`/…). Web:
  `<section class=deos-section data-tag>`; the title a `<div class=deos-section-title>`.

**`tabs`** — a tab-strip whose visible panel is bound to a model slot.
- shape: `{ kind:"tabs", props:{ tabs:[labels], selectedSlot, selectTurn }, children:[panel…] }`
- unlocks: `Lanes` (4-lane strip), `Devtools` (3 sub-tabs), `Moldable` (one sub-tab per
  Presentation), `Workspace`/`Simulate` effect-palette cycles.
- paint: an `h_flex` of `Button`s (one per label; the active one `.primary()`), each firing
  `selectTurn` with `arg = its index` (a real verified turn that writes `selectedSlot`); the
  body is the panel at `get_u64(selectedSlot)`. The renderer walks ALL panels to keep the
  bind cursor aligned, displays only the selected one. Web mirrors (strip + all panels as
  `deos-tabpanel`, a JS layer toggles visibility); discord recurses all panels.

**`grid`** — a wrapping / spatial cell field.
- shape: `{ kind:"grid", props:{ cols? }, children:[…] }` (freeform placement variant:
  per-child `props.x`, `props.y` for the `canvas` flavor + persisted positions).
- unlocks: `Wonder`'s glowing-cell grid, the desktop icon field, the Powerbox app tiles.
- paint: a `flex` with `flex_wrap` + `gap_2` (cols → `max_w` per child); the `canvas` flavor
  uses `absolute` + `left(px(x))`/`top(px(y))`. Web: CSS grid / absolute.

**`divider`** — a horizontal rule (visual separation / groove).
- shape: `{ kind:"divider", props:{} }`
- unlocks: NT `face_section` groove rules, every `border_t_1` separator.
- paint: a `div().h(px(1)).w_full().bg(border)`. Web: `<hr class=deos-divider>`.

**`breadcrumb`** — a navigation path with separators.
- shape: `{ kind:"breadcrumb", props:{ items:[{label, turn?, arg?}] }`
- unlocks: `Time`'s metastack breadcrumb (BASE → crumb → crumb), `Docs` transclusion path.
- paint: an `h_flex` of `Label`s joined by `→`; a crumb with a `turn` is clickable.

### Status & live-value indicators

**`gauge`** — a bound progress / balance bar.
- shape: `{ kind:"gauge", props:{ slot, max, label?, tag? } }`
- unlocks: NT `face_gauge` (balance ratio), `Time` liveness, any "glow = activity" bar.
- paint: a label + a track `div` (`bg=border`) with an inner fill `div` whose width is
  `track_w * (get_u64(slot)/max).clamp(0,1)`. Reads the slot immediate-mode (no cursor).
  Web: `<div class=deos-gauge data-slot data-max>` with a JS-driven fill.

**`progress`** — a static (literal-valued) progress bar (the non-bound gauge).
- shape: `{ kind:"progress", props:{ value, max, label? } }` — same paint as `gauge` with a
  literal `value` instead of a slot. Unlocks a swarm-member completion bar, a download tile.

**`pill`** — a colored status badge (leaf).
- shape: `{ kind:"pill", props:{ text, tag } }`
- unlocks: the cockpit's ubiquitous `pill(text, color)` — authority badges, height/lens
  chips, LIVE/REVOKED status, `kind_badge`/`lifecycle_badge`.
- paint: a `div().px_2().py_0p5().rounded_md()` tinted by `tag` (the semantic palette:
  `good`/`warn`/`bad`/`accent`/`muted`). Web: `<span class=deos-pill data-tag>`.

**`icon`** — a glyph indicator (leaf).
- shape: `{ kind:"icon", props:{ glyph, tag? } }`
- unlocks: the Wonder ✦/○ glow glyphs, the scrubber ▸/⊘/•/· markers, the toggle ✓/○.
- paint: a `Label` of the glyph tinted by `tag`. Web: `<span class=deos-icon>`.

### Actuation (the cross-surface direct-manipulation primitives)

**`menu`** — a right-click / context actuation menu.
- shape: `{ kind:"menu", props:{ items:[{label, turn, arg, enabled?}] } }`
- unlocks: the `deos_desktop` right-click menu — the cross-surface actuation list. `enabled`
  is the cap tooth (`is_attenuation(held, required)`): a dim item is refused in-band.
- paint: a `v_flex` of rows; an enabled row is a `Button` firing `{turn, arg}`; a disabled
  row is a dimmed `Label` (`.opacity(0.4)`). Web: a `<menu>` of `<button data-turn>`.

**`halo`** — the Pharo direct-manipulation handle-ring (overlay).
- shape: `{ kind:"halo", props:{ targetSlot?, handles:[{glyph, turn, arg, enabled?}] } }`
- unlocks: `deos_desktop/halo.rs` — 6–16 handles floating on a selected object, each firing
  the same actuation the menu would. The single richest node; tractable because each handle
  IS just an affordance with a compass anchor.
- paint: an absolutely-positioned ring of `rounded_full` handle `div`s around the target
  bounds (8 compass anchors NW…W, `HANDLE_D≈24px`), each `on_mouse_down` firing `{turn,arg}`;
  a `!enabled` handle is `.opacity(0.4)` (cap-gated). The anchor geometry is renderer-side
  layout, not card data — the card supplies the glyph+affordance set, the renderer rings them.
  Web: absolutely-positioned `<button>`s; discord flattens to a button row.

**`slider`** / **scrubber** — a draggable value → seek turn.
- shape: `{ kind:"slider", props:{ slot, min, max, turn } }`
- unlocks: `Time`'s rewind scrubber, `Replay`. A drag fires `turn` with `arg = the value`
  (re-derive at a past height); the thumb sits at `get_u64(slot)`.
- paint: a track `div` with a draggable thumb `div`; `on_mouse_down`/drag maps x → value →
  fires `turn`. (The scrubber-tick variant: a `list` of clickable `icon`+`label`+`pill` rows,
  each firing `seek` with the step index — expressible TODAY by composition.)

**`toggle`** — an affordance checkbox (✓/○).
- shape: `{ kind:"toggle", props:{ slot, onTurn, offTurn, glyphOn?, glyphOff? } }`
- unlocks: `Share`'s frustum-cull lens/affordance toggles, any boolean affordance.
- paint: a clickable `row` of an `icon` (✓ if `get_u64(slot)!=0` else ○) + a label; the click
  fires `onTurn`/`offTurn` by current state.

### Input bound to a turn argument

**`input` (extended)** — a text field whose value can feed a turn arg.
- shape today: `{ kind:"input", props:{ bindView } }` (ephemeral draft, no turn).
- extension: `{ kind:"input", props:{ bindView, argSlot?, fireTurn?, submitLabel? } }` — the
  field's draft is parsed into the `arg` of `fireTurn` on submit (Enter / a paired button).
- unlocks: `ServiceExplorer` arg rows, `WebShell` URL bar, the predicate composer. The
  `WebShell` URL bar is `input` + `fireTurn:"navigate"`; `ServiceExplorer` invoke is
  `input(argSlot) → button(turn=invoke, arg←draft)`.
- paint: the existing bordered field gains an `on_key_down` Enter handler (or a sibling
  button reads the draft as its arg). Renderer-independent: web is `<input>` + a submit wire.

### The opaque native tile (the genuine ceiling)

**`tile`** / **servo-tile** — a card-referenced native paint region.
- shape: `{ kind:"tile", props:{ handle, w, h } }` (`handle` names a host-side render source).
- unlocks: `WebShell`'s Servo render tile, any embedded native surface (a video, a map, a
  game). The card does NOT carry the pixels; it references an opaque region the host paints
  and routes input events back into (`on_mouse_down`/`on_scroll`/`on_key_down` → the handle).
- paint: native resolves `handle` → an `img()`/render tile sized `w×h` with an event-capture
  overlay; web resolves it to an `<iframe>`/`<canvas>`; an unresolvable handle paints a
  labelled placeholder. This is the one node whose substance is host-resolved, not card data —
  parked last, but designed so the card boundary is honest about it.

### Summary table (target vocabulary)

| node | category | bound? | actuates? | unlocks (native) |
|---|---|---|---|---|
| `section` | container | no | no | Organs, Trust, Devtools groups |
| `tabs` | container | selectedSlot | selectTurn | Lanes, Devtools, Moldable |
| `grid` | container | no | no | Wonder, icon field, app tiles |
| `divider` | structure | no | no | groove rules, separators |
| `breadcrumb` | structure | no | optional | Time metastack, Docs path |
| `gauge` | indicator | slot | no | face_gauge, liveness bars |
| `progress` | indicator | literal | no | swarm/completion bars |
| `pill` | indicator | no | no | every status badge |
| `icon` | indicator | no | no | glow/marker glyphs |
| `menu` | actuation | no | items[].turn | right-click menu |
| `halo` | actuation | targetSlot | handles[].turn | Pharo halo ring |
| `slider` | actuation | slot | turn | Time/Replay scrubber |
| `toggle` | actuation | slot | on/offTurn | Share cull toggles |
| `input` (ext) | input | bindView | fireTurn | ServiceExplorer, WebShell URL |
| `tile` | host-region | no | event handle | WebShell Servo tile |

---

## 2. The rendering contract (fidelity + renderer-independence)

Each new node gets a walker arm in EACH renderer, exactly as the 8 existing nodes do, so the
card stays renderer-independent by construction:

- **native (`render.rs`)** — the bar. A migrated surface must look/behave identical to its
  hand-built gpui tree: the same `v_flex/h_flex/Button/Label` widgets, the same dark-theme
  colors (`cx.theme().{foreground,background,border,…}`), the same spacing idioms
  (`gap_*`/`p_*`/`rounded_*`). Where the native panel used a helper (`pill`, `cycle_chip`,
  `time_button`, `face_gauge`) the corresponding node paints the SAME shape.
- **web (`web.rs`)** — the identical `ViewNode` → HTML, node-for-node. The `CSS` block
  mirrors the cockpit dark palette so the browser projection LOOKS like the native bake; a
  bound/actuating node carries its `data-slot`/`data-turn`/`data-arg` so the in-tab executor
  (`wasm/src/bindings_card.rs`) drives it live.
- **discord (`discord.rs`)** — a graceful flattening: containers recurse, indicators become
  description lines, actuators become the button grid. New nodes never break the embed.

**The invariant that guarantees no fidelity loss across renderers:** the tree-walk bind
cursor. `bind_plan` (native registration), `render.rs`'s `next_bind_value`, `web.rs`'s
cursor, and `discord.rs`'s cursor all visit `Bind` nodes in identical pre-order. Container
nodes recurse children in declaration order; `tabs` walks ALL panels (display-selects one but
consumes every panel's binds) so the cursor never desyncs on a tab switch. Immediate-read
nodes (`gauge`/`slider`/`toggle`) read their slot directly and consume NO cursor position in
any renderer — so they cannot desync it either.

---

## 3. The actuation contract (rich interactions stay live + edit-from-within)

Every interactive node routes to a REAL verified turn through the SAME path the existing
`button` uses — there is no second actuation mechanism:

1. The node carries its affordance as `{turn, arg}` (the `onClick`/`handles[]`/`items[]`/
   `selectTurn` shapes all reduce to this pair).
2. The native handler clones the `SharedApplet` and on click/drag/select calls
   `applet.borrow_mut().fire(turn, arg)` — the in-band `is_attenuation(held, required)` cap
   tooth runs BEFORE the executor; a refusal is surfaced to stderr and the model simply does
   not advance (the screenshot stays honest). A committed turn returns a `TurnReceipt` and
   the touched slots feed `on_committed_turn` → the fine-grained re-read.
3. `enabled`/`authorized` on a `menu` item or `halo` handle is precisely the cap tooth
   evaluated up front: a dim handle is the same refusal, shown rather than hidden.
4. **Edit-from-within is unchanged.** A card's view IS a `ProgramSource` document
   (`deos-js/src/card_editor.rs`); `ModeCardSurface::edit_view` (`dock/card_surface.rs`)
   applies a `ViewPatch` as a receipted patch with blame and `set_tree`s the live
   `AppletView`. The new nodes are new `ViewPatch` targets (e.g. `AddTab`, `AddSection`,
   `AddHandle`) — the same accountable-rewrite loop, a richer vocabulary to rewrite into.

The selection state of `tabs` (and any future stateful container) lives in a MODEL SLOT, not
renderer-local state, so a tab switch is a verified turn — reflective, replayable, and the
selection survives an agent rewrite of the surrounding tree.

---

## 4. Progressive disclosure as a first-class card concept

Delight (a 1999-AOL 4-year-old clicks around with wonder) and moldability (an adept sees the
bones) are TWO PROJECTIONS OF ONE CARD, never two cards:

- **`props.adept: true`** tags a node as adept-only. A card-level `disclosure: "simple" |
  "adept"` setting tells the renderer which projection to paint. At `simple` the renderer
  FILTERS OUT adept-tagged nodes — raw hex cell ids, `ViewNode` kinds, slot/field indices,
  receipt hashes — and shows the friendly label + the live value + the buttons. At `adept`
  it paints everything (the Pharo "see the bones" mode).
- This is a renderer FILTER over one tree, so: it is renderer-independent (web and gpui filter
  the SAME data identically); it survives agent rewrite (a patch adds an `adept` sibling, both
  levels stay coherent); and the card remains the single source of truth.
- It reuses the existing `props.tag` channel (already wired for `genuine`/`refusal` styling)
  rather than inventing a parallel one — `adept` is a reserved tag/flag the filter honors.
- Convention: a `bind`/`text` carries a friendly `label`; its hex/slot is an `adept`-tagged
  sibling. Disclosure is then "show the adept siblings," not a different card. `section`'s
  `tag` and `pill`'s `tag` participate (an adept-only section collapses at the simple level).

Implementation note: the filter is a pre-walk that drops `adept` nodes when
`disclosure=="simple"`, applied before the renderer walk; because it runs before the bind
cursor walk in EVERY renderer, the simple and adept projections each have a self-consistent
cursor (a dropped adept `bind` is dropped in all renderers identically).

---

## 5. The lossless-migration ladder (every surface, full fidelity)

Each rich cockpit surface maps to the nodes it needs. The point: NO surface is "too hard to
migrate" — each is a finite set of the nodes above. (The clean-five — Objects, Graph, Proofs,
Organs, Home — need nothing new and migrate today.)

| surface | nodes it needs (beyond the base 8) |
|---|---|
| `Organs` | `section`, `divider` |
| `Home` | `section`, `pill`, `gauge` |
| `Swarm` | `section`, `pill`, `progress` |
| `Trust` | `section`, `pill`, `gauge` |
| `Cipherclerk` | `section`, `pill` |
| `Simulate` | `tabs`, `input`(ext), `pill` |
| `Workspace` | `tabs`, `input`(ext), `pill` |
| `ServiceExplorer` | `section`, `input`(ext), `pill`, `menu` |
| `Lanes` | `tabs`, `section`, `pill` |
| `Devtools` | `tabs`, `section`, `divider` |
| `Moldable` | `tabs`, `section`, `menu`, `halo` |
| `Time` | `slider`, `breadcrumb`, `gauge`, `icon`, `pill` |
| `Replay` | `slider`, `icon` |
| `Wonder` | `grid`, `icon`, `halo` (hover/select → focus turn) |
| `Share` | `toggle`, `section`, `slider` (attenuation dial), `pill` |
| `Docs` | `section`, `menu` (resolve choices), `breadcrumb` (transclusion) |
| `WebShell` | `tile` (Servo), `input`(ext, URL bar), `menu`, `pill` |
| desktop chrome | `halo`, `menu`, `breadcrumb`, `icon` (the Spotter row = `list`+`pill`) |

The actuation primitives (`menu`, `halo`) are the highest-leverage because they are the
cross-surface direct-manipulation idiom: once expressed as nodes, every carded surface gets
uniform right-click + handle-ring actuation for free. The `tile` node is the genuine ceiling
(an opaque host-painted region) and is migrated last — but its DESIGN keeps the card boundary
honest (the card references the region; it does not pretend to own the pixels).

---

## 6. The first batch implemented (this change)

Highest-leverage 3–4, chosen to exercise all FOUR node shapes (container / actuation+selection
/ bound-visual / leaf) so the expansion path is proven end-to-end:

1. **`section`** (container + the disclosure/tag carrier) — `{title, tag} + children`. A
   titled bordered `v_flex`; `tag=="genuine"` accents the border (the existing convention).
2. **`tabs`** (actuation + selection state) — `{tabs, selectedSlot, selectTurn} + panels`. An
   `h_flex` of `Button`s firing `selectTurn` with `arg=index` (a REAL verified turn writing
   `selectedSlot`); body = panel at `get_u64(selectedSlot)`. Walks all panels (cursor-aligned),
   displays the selected one. This proves the rich-interaction routing: a tab switch is a turn.
3. **`gauge`** (bound visual) — `{slot, max, label}`. A label + a track div with an inner fill
   sized by `get_u64(slot)/max`. Reads its slot immediate-mode (no cursor entanglement).
4. **`divider`** (leaf) — a `h(1px)` full-width rule. Proves the trivial-leaf addition.

All four are added to `ViewNode` + `RawNode::lift` (with `RawProps` gaining `title`, `tag`,
`max`, `tabs`, `selectedSlot`, `selectTurn`), and walked by ALL FOUR renderers (`render.rs`,
`web.rs`, `discord.rs`) plus `bind_plan`'s registration walk — so the bind cursor invariant
holds and the card stays renderer-independent. A new render test
(`renders_rich_nodes_to_pixels.rs`) bakes a card using all four new nodes to real
gpui-component pixels and round-trips the JSON, proving the expansion path.

The remaining vocabulary (§1) lands as the ladder (§5) reaches the surfaces that need it —
`menu`/`halo` next (the actuation crown), then `slider`, `grid`, the extended `input`, and
`tile` last.

## 7. Batch 2 — the actuation crown + the rest of the vocabulary (VOCABULARY COMPLETE)

The remaining §1 nodes are now implemented in lockstep across all four renderers + the deos-js
authoring layer + the cockpit's `card_pane.rs` consumer, completing the target vocabulary:

- **`grid`** (`{cols} + children`) — a wrapping spatial cell field; native `flex_wrap` (cols → a
  per-cell `max_w`), web CSS grid/flex-wrap, discord recurses. Recurses children → the bind cursor
  stays aligned (it is the one new node with `ViewNode` children, so `resolve_mounts`/`bind_plan`
  recurse it).
- **`breadcrumb`** (`{items:[{label, turn?, arg?}]}`) — a `→`-joined path; a crumb with a `turn`
  is a clickable verified turn. Leaf (no bind cursor).
- **`progress`** (`{value, max, label}`) — the STATIC (literal) gauge; same paint, baked fill.
- **`pill`** (`{text, tag}`) / **`icon`** (`{glyph, tag}`) — the semantic-tag palette
  (`good`/`warn`/`bad`/`accent`/`muted`) expressed as data (the cockpit's `pill(text, color)`).
- **`menu`** (`{items:[{label, turn, arg, enabled}]}`) — the right-click actuation list; an
  `enabled:false` row is the cap tooth SHOWN (dimmed `Label`), never hidden.
- **`halo`** (`{targetSlot?, handles:[{glyph, turn, arg, enabled}]}`) — the Pharo handle-ring; each
  handle is the same `{turn, arg}` affordance, ringed by renderer-side layout (the card carries the
  glyph+affordance set, not the geometry). A `!enabled` handle is dimmed (cap-refused).
- **`slider`** (`{slot, min, max, turn}`) — the bound scrubber; the thumb reads the slot
  immediate-mode, and the native paint is discrete clickable ticks (the SAME `on_mouse_down`
  actuation the native Time scrubber uses), each seeking `arg = its value`. Web is `<input
  type=range>`; discord a single `seek` affordance.
- **`toggle`** (`{slot, onTurn, offTurn, glyphOn?, glyphOff?, label?}`) — the affordance checkbox;
  the glyph reflects the live slot, the click fires on/off by current state.
- **`input` (extended)** (`{bindView, fireTurn?, submitLabel?}`) — the draft feeds a turn arg: a
  paired submit button parses the draft into `fireTurn`'s `arg` (input → verified turn).
- **`tile`** (`{handle, w, h}`) — the host-resolved region (the genuine ceiling): native paints a
  sized framed placeholder, web an `<iframe>`/`<canvas>` slot, both carrying `handle` for the host
  to resolve; the card never carries the pixels.

The actuation contract (§3) holds unchanged: every interactive batch-2 node routes its
`{turn, arg}` through the same `Applet::fire` → cap tooth → executor → receipt path the base
`button` uses; `enabled`/cap-dim is the in-band refusal shown. The bind-cursor invariant (§2)
holds: only `Bind` consumes the cursor; the bound batch-2 nodes (`slider`/`toggle`/`gauge`) read
their slot immediate-mode and consume no cursor in any renderer, and `grid` recurses children in
declaration order. The deos-js `deos.ui.*` prelude gained an authoring helper for every node
(plus the batch-1 `section`/`tabs`/`gauge`/`divider` helpers), so a card author (or an agent via
`run_js`) emits the rich nodes the renderers paint. Round-trip + render-to-pixels proofs:
`deos-view/src/tree.rs` (`batch2_lift_tests`) + `deos-view/tests/renders_rich_nodes_to_pixels.rs`
(`the_batch2_nodes_round_trip_and_render_to_pixels`).
