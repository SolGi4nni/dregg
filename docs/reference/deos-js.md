# deos-js & the reflective layer

`deos-js` (`deos-js/`) is a JavaScript scripting surface over deos substance: real
SpiderMonkey (`mozjs`) drives sovereign cells via cap-gated verified turns. JS does not
mutate a DOM — it crawls and drives an embedded (or attached) verified executor, every
mutation leaving a real `TurnReceipt`. The crate is its own Cargo workspace (so the
multi-GB SpiderMonkey C++ build does not feature-unify onto the repo;
`deos-js/Cargo.toml:14-17`), depending on `mozjs = "0.15.7"` (`deos-js/Cargo.toml:30`).

## The factoring

The crate's organizing claim (`deos-js/src/lib.rs:1-26`): a **cell** is a
sovereignty/distribution boundary — one whole interactive "applet", a polynomial-functor
interface whose *positions* are the views it presents and whose *directions* are the
affordances (named turns) it accepts. The applet's **model** is the cell's state; the only
mutators are its affordances = cap-gated verified turns. **Ephemeral view-state** (draft
text, hover) is NOT cell state and is never a turn. Applets compose via **transclusion**.

Two slices (`deos-js/src/lib.rs:19-26`):
- **drive** (`applet`) — `deos.applet`/`app.fire`: an affordance is a real cap-gated turn.
- **crawl** (`reflect_binding`) — `deos.world`/`deos.cell`: a cap-bounded, attested READ
  over the live image (via the gpui-free `deos-reflect`). Reflection confers no authority.

## `Applet` — the embedded drive target (`src/applet.rs`)

`Applet` owns its own embedded verified executor — a `DreggEngine`
(`src/applet.rs:164-187`). `Applet::mint` seeds a cell with a balance and open
permissions, writes genesis model fields, and registers affordances; the drive path is set
to **Symbolic** witness mode by default (`src/applet.rs:202-213`) — the state transition
fully applies and every gate (authority/conservation/freshness) runs, but the
`pre/post_state_hash` Merkle commitment is deferred to the `DEFERRED_STATE_HASH` sentinel;
`set_full_witness()` reaches the publishable mode (`src/applet.rs:316-320`).

An `Affordance` (`src/applet.rs:57-63`) is a name + a `required: AuthRequired` + a pure
`apply: Fn(&CellModel, i64) -> Vec<(Slot, FieldElement)>` closure. `Applet::fire`
(`src/applet.rs:397-452`) is the load-bearing path: (1) resolve the affordance; (2) the
**cap tooth** — `dregg_cell::is_attenuation(&held, &required)`, in-band, an unheld fire
commits nothing (`src/applet.rs:404-408`); (3) compute writes from the live model; (4)
build a turn (the affordance name as the action method, the chain head threaded as
`previous_receipt_hash`, a fee of 10_000) and execute it, appending `receipt_hash()` to the
audit tape (`src/applet.rs:419-451`).

The model (`CellModel`, `src/applet.rs:67-128`) is a witnessed read off the ledger; a
`u64` is packed little-endian into the low 8 bytes of a `FieldElement` (`pack_u64`,
`src/applet.rs:40-44`). Ephemeral view-state is a plain in-memory `BTreeMap`
(`ViewState`, `src/applet.rs:133-136`; `set_view`/`get_view` touch no ledger,
`src/applet.rs:485-495`). `snapshot`/`restore` give cheap fork-based time-travel, the
restore integrity-hashed and the receipt tape truncated to match (`src/applet.rs:353-371`).

`Applet::transclude` (`src/applet.rs:509-537`) composes two applets through the REAL
transclusion primitive: it publishes the other applet's content-addressed surface into a
`WebOfCells` and calls `TranscludedField::include` (the verified `dregg://` finalized read
— content → commitment → receipt → receipt-stream-root → quorum); a forged/non-finalized
surface refuses, and on success the embed carries `Provenance`, not a raw copy.

## `js` — the SpiderMonkey runtime (`src/js.rs`)

`JsRuntime` (`src/js.rs:618-622`) wraps a genuine `JSEngine`/`Runtime`. `eval`
(`src/js.rs:639-742`) creates a fresh global, enters its realm (`AutoRealm`), installs the
native bridge functions with `JS_DefineFunction`, runs a JS **prelude** that builds the
ergonomic `deos.*` object surface atop the natives, then runs the user source. The natives
are thin `unsafe extern "C"` functions over `CallArgs`; reflective natives return JSON
strings the prelude `JSON.parse`s.

The drive target is a thread-local `JsTarget` (`src/js.rs:44-49,192-197`) — either
`Embedded(Applet)` or `Attached(AttachedApplet)` — so one set of natives serves both the
private embedded world and a live World. The prelude (`src/js.rs:389-615`) exposes:

- `deos.applet(spec)` → `app.fire`/`app.get`/`app.view` (`__deos_fire` is one cap-gated
  turn; `__deos_get` a witnessed read; `app.view.set/get` ephemeral, never a turn).
- `deos.world.cells()`/`.ocap()`/`.snapshot()`/`.rewind(token)` — the crawl + fork-based
  rewind (`src/js.rs:412-422`).
- `deos.cell(id)` → `.reflect()`/`.field(key)`/`.present()`/`.affordances(viewer)`/
  `.as(viewer)` (the four substances, the moldable faces, the cap-gated message list, and
  the cap-bounded frustum view) (`src/js.rs:452-497`).
- `deos.search(q)` — a fuzzy spotter over every cell's faces.
- `deos.ui.*` — a serializable **view language**: `vstack`/`row`/`text`/`bind`/`button`/
  `input`/`list`/`table` produce `{kind, props, children}` DATA (deos-js stays gpui-free; a
  separate renderer draws it); a button's `onClick` is `{turn, arg}` (`src/js.rs:430-450`).
- `deos.editor.*` — the card editor (`card`/`editView`/`setField`/`addAffordance`).
- `deos.server.*` — the private-server / GM surface.
- `deos.compose([...])` — the bounded multi-cell story.

`__deos_fire` distinguishes three faces (`FireOutcome`, `src/js.rs:936-970`): **Committed**
(a verified turn), **Refused** (the cap gate said no — an expected, JS-observable `-1`, no
receipt), and **Fatal** (a genuine fault, e.g. the executor rejecting an authorized turn,
which poisons the eval). A cap refusal is never a fatal error.

Run entry points beyond `eval`: `run_attached` (`src/js.rs:753-774`) binds a live World and
hands back the committed-receipt tape; `run_authoring` (`src/js.rs:787-800`) installs a
`CardEditor`; `run_compose` (`src/js.rs:814-832`) installs an `AttachedComposer`. The
editor, composer, and crawl/drive targets are independent thread-locals, so authoring or
composing composes with either an embedded or an attached crawl target.

### Authority labels

JS names authority by string: `parse_auth_label` (`src/js.rs:1320-1329`) maps
`"signature"`/`"proof"`/`"either"`/`"impossible"` to `AuthRequired` variants; anything else
(including `"none"`) → `AuthRequired::None` (the broadest).

## `reflect_binding` — the crawl JSON (`src/reflect_binding.rs`)

The reflective natives project the live ledger through `deos-reflect` into hand-built JSON
(no serde dep, to keep the binding lean — `src/reflect_binding.rs:14`):

- `world_cells_json` — every cell id, id-sorted (`:57-62`).
- `world_ocap_json` — the capability web: nodes (cell, short, balance, lifecycle,
  out/in-degree) + edges (holder/target/slot/rights/faceted/delegated), via
  `OcapGraph::build` (`:66-103`).
- `cell_json` — one cell's four substances; a `Committed` slot surfaces its commitment,
  never the value (`:108-112,188-195`).
- `frustum_json`/`frustum_reflect_json` — the cap-bounded view via `Frustum::project`: an
  unobservable cell is an **absence** (`null`), never a forged read (`:117-141`).
- `cell_present_json` — the moldable faces (Fields/Graph/StateMachine/Timeline), each a
  distinct projection of the same cell; `receipts` feeds the Provenance/Timeline face
  (`:204-314`).
- `cell_affordances_json` — the cap-gated message list, built from registered specs and
  projected by `AffordanceSurface::project_for(held)` (`required ⊆ held`); a weaker viewer
  receives a strictly smaller set (`:322-349`).
- `spotter_json` — fuzzy search (contiguous-substring scores highest, else in-order
  subsequence) over each cell's id/title/subtitle/field-keys, best-first (`:368-430`).

## `attach` — driving a provided live World (`src/attach.rs`)

The embedded `Applet` only ever crawls/drives its own private image. The attach path binds
the runtime to a **provided** World through a thin `WorldSink` trait (`src/attach.rs:46-93`):
`with_ledger` (the witnessed read surface), `fire_effects` (commit one verified turn on an
agent carrying effects), and `mint_open_cell` (the GM superpower — mint an open, funded
cell, default-erroring; the attach host implements it). deos-js does not depend on
starbridge-v2; the host supplies the `impl WorldSink` (`src/attach.rs:25-27`).

`AttachedApplet` (`src/attach.rs:141-164`) carries the agent cell, its `held` authority
(the red-team invariant — the runtime is mounted under the **attenuated** cap, never the
World's root), and a named affordance surface. `AttachedApplet::fire`
(`src/attach.rs:287-334`) runs the SAME `is_attenuation` cap tooth in-band before anything
reaches the executor (`src/attach.rs:297-301`); on admission it commits the affordance's
explicit `effects`, or falls back to a counter-bump on the agent's own cell. A fire's
**actor is always the agent's own cell** — it cannot cross to another vessel.
`fire_raw_effects`/`fire_raw_effects_as` (`src/attach.rs:345-369`) are the GM-superpower
path with no affordance-level cap tooth (the caller IS the agent driving its own world; the
executor's authority gate is the binding check).

### `AttachedComposer` — the bounded multi-cell story (`src/attach.rs`)

`ComposeStep` (`src/attach.rs:410-451`) has three legs: `MintCard` (stand up a fresh OPEN
funded cell, joining scope), `SetField` (write a held cell), `GrantCap` (grant a cap over a
held `from` to any peer `to`). `AttachedComposer::compose` (`src/attach.rs:619-683`) is
all-or-nothing: an **atomic pre-screen** checks every leg's `required ⊑ held` (authority
tooth), its touched cells against the agent's scope (scope tooth — a `MintCard` grows the
*projected* scope so a story may mint-then-write its own new cell), and a grant's `granted ⊑
held`; **any over-reach aborts the whole story in-band with nothing committed**
(`ComposeError::OverReach`). Only when every leg clears does it commit each as its own
verified turn (`ComposeError::Executor` reports a residual executor refusal, with prior legs
already landed). `mint_id_of(seed)` derives the deterministic minted id (`blake3(seed)`
against the default token domain) so the pre-screen can project it (`src/attach.rs:755-759`).

## `card_editor` — authoring a card from within (`src/card_editor.rs`)

Turns inspection into authoring: every authoring gesture is a turn / a receipted patch
(`src/card_editor.rs:1-29`). A `CardEditor` (`src/card_editor.rs:299-315`) is mounted under
a `held` authority and an `edit_authority` (the card's authoring cap); `authorized()` is
`is_attenuation(&held, &edit_authority)` (`:372-374`).

- `edit_view` (`:407-437`) — the keystone. A `ViewPatch` (`AddButton`/`AddText`/`Relabel`,
  `:209-221`) is applied to the card's `ViewTree`, the result appended as a **patch** to the
  card's `view_source` (a `ProgramSource` = a `dregg_doc::Doc` patch-history), re-sealed into
  the manifest, and a provenance receipt is left via a real `SetField` turn bumping
  `AUTHORSHIP_SLOT` (= 15, `:52`). The result carries the re-folded tree, the `blame` (each
  view line attributed to its author/patch), and the receipt. Refused in-band if
  unauthorized or a no-op.
- `set_field` (`:443-459`) — a real `SetField` verified turn on the card's state (registers
  a one-shot affordance gated on `edit_authority`, then fires it).
- `add_affordance` (`:466-481`) — weld a new named effect-template into the manifest AND
  register it live on the card (so it fires immediately), leaving a provenance receipt.

`ViewTree` (`:59-85`) is the gpui-free mirror of the renderer's `{kind, props, children}`
shape (`VStack`/`Row`/`Text`/`Bind`/`Button`; a button serializes `on_click` to match
`deos-view`'s `parse_view_tree`). `remint`/`reseal` (`:487-496`) re-mint the authored card
as a fresh portable cell-blob. The JS-side natives `__deos_editor_*`
(`src/js.rs:1331-1546`) add a SECOND bound: `cardId` must equal the editor's own card
(`editor_card_matches`, `:1341-1343`) — authoring the wrong card is refused in-band.

## `signals` — the fine-grained binding registry (`src/signals.rs`)

The dirty-set model for the view language: a `bind(() => s.x)` node records which
`(cell, slot)` it reads, so a committed turn re-evaluates only the bindings that depend on
the exact written source — not the whole tree. `BindingRegistry` (`src/signals.rs:83-89`)
is a reverse index `(CellId, Slot) → Vec<BindingId>`. `register`/`unregister` keep one
source per binding (`:100-127`); `invalidate(SourceEvent)` is a single map lookup returning
the deduped, id-sorted dirty set (`:132-137`); `invalidate_all` unions several touched
slots; `invalidate_cell` is the conservative "whole cell changed" tooth (`:142-164`);
`reread` hands the binding's source back to a caller-supplied witnessed read closure
(`:174-177`). It is pure data — gpui-free and starbridge-free, naming the changed source
with its own minimal `SourceEvent` a cockpit adapter maps real `WorldEvent`s into
(`:20-34,50-68`). The module has an exhaustive test suite (`:195-328`).

> The module doc-comment references `crate::tree::ViewNode` and a `deos-view` renderer
> integration; there is no `tree` module in deos-js — those are cross-crate/aspirational
> references in the prose, not a type defined here.

## `mailtown` — a verified pen-pal mail town (`src/mailtown.rs`)

A worked example of deos substance: an embedded executor whose ledger holds address-cells, a
privileged **postmaster** (`MailTown`, `src/mailtown.rs:207-226`). A place is a cell, a
letter is a cap-gated verified delivery turn, the receipt chain IS the unforgeable
mail-ledger. The postmaster's authority is a distinct `Custom { vk_hash }` floor
(`postmaster_floor`, `:112-116`) **incomparable** under `is_attenuation` to a resident's
plain `Signature` (`resident_floor`, `:120-122`), so a resident can never open an address or
grant a route. `write_letter` (`:373-410`) runs three in-band teeth: authority (resident
floor), **route** (the sender must hold a cap edge to the recipient via
`Frustum::project(...).can_observe`), then a receipted, attributed delivery turn writing the
recipient's inbox witnesses + the committed body digest. `try_amplify_via_letter`
(`:427-447`) demonstrates **non-amplification structurally**: a letter's author carries at
most the resident floor, incomparable to the postmaster floor, so the cap-lattice refuses
turning a delivery cap into office authority — content, never command.

## The reflective cards (`src/*_card.rs`)

Each card reproduces a hardcoded-Rust cockpit surface as a deos-js card: a cell whose view
is a `ViewTree` generated from live reflective state, editable from within (each `edit_view`
a receipted patch with blame on the card's own chain). From their module docs:

- `inspector_card` — a focused cell's moldable faces (RawFields → live `Bind` rows;
  Affordances → cap-gated `Button`s) (`src/inspector_card.rs:1-29`;
  `INSPECTOR_AUTHORSHIP_SLOT = 14`, `:63`).
- `objects_card` — the live cell roster (id-sorted, balance, an `inspect` button).
- `graph_card` — the ocap web (edges `holder ──▶ target @rights` + node degrees) via
  `OcapGraph`.
- `links_card` — what-links-here: verified backlinks (`← observer transcludes focus ·
  receipt · commitment`), viewer-tier projected.
- `dynamics_card` — the live turn/receipt feed; a `Bind` on `FEED_LEN_SLOT` advances the
  count as turns land; `observe` appends a `FeedEntry`.
- `layout_card` — the cockpit's own mode→surface arrangement, lifted out of compiled Rust
  (`CockpitMode::surfaces()`) into editable cell DATA (`src/layout_card.rs:1-21`).
- `agent_card` — an agent cell's held mandate (its c-list) + its cap-gated turns/receipts;
  a `Bind` on `AGENT_NONCE_SLOT` shows the loop step count.
- `composer_card` — the document composer (composed children + four composition gestures
  over `dregg_doc` / `LayoutGraph`).
- `coauthored_card` — two principals each fork one shared card, each edit in their own view,
  then **stitch**; merge is by `dregg_doc` pushout where a conflict is a first-class
  `ConflictRegion`, never a silent overwrite (`src/coauthored_card.rs:1-25`).

## Portability welds (`src/portable.rs`, `src/program_doc.rs`)

- `portable` — an applet's program (its affordances + view source) serialized into an
  `AppletManifest` and persisted into the cell's committed **heap** (collection
  `PROGRAM_COLL = 0xC0DE`, 31 payload bytes per leaf), so it travels with `to_cell_bytes()`
  and reconstitutes via `PortableApplet::from_cell` (`src/portable.rs:1-30,36`). `ApplyOp`
  (`AddToSlot`/`SubFromSlot`/`SetSlot`) `into_closure()`s into an affordance's `apply`
  (`:48-60`).
- `program_doc` — a gadget's `view_source` is a `dregg_doc::Doc` patch-history:
  `ProgramSource::edit` (patch + content-addressed `blame`), `transclude_fragment` (a
  provenanced live quote carrying the source's blame), and merge of concurrent edits
  (`src/program_doc.rs:1-25`).
