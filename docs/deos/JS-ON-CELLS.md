# JS-on-Cells + a native deos-js runtime

A cell can host JavaScript — event handlers and reactive logic for its surface,
beyond a static view-tree. That JS runs in the **cockpit** (the gpui native
desktop) through a lightweight, embeddable, pure-Rust engine, AND in the web
shell — one runtime everywhere, not servo-only.

This is the companion to the cell-hosted *view-tree* (`CELL-HOSTED-VIEWTREE.md`):
the view-tree is what a cell *shows*; the attached JS is how a cell *behaves*. Both
live in the cell's committed heap, so both travel with the cell and are witnessed
by `heap_root`.

## 1. The model: a cell hosts a JS program

A cell is a sovereignty boundary — a polynomial-functor interface whose
*positions* are the views it presents and whose *directions* are the affordances
(named cap-gated verified turns) it accepts. Today a deos-js applet's *program*
(its affordances + its view source) is a serializable blob stored in the cell heap
under `PROGRAM_COLL` (`deos-js::portable`), and its view-tree is a blob under
`VIEWTREE_COLL` (`deos-view::mount`). JS-on-cells adds a third committed blob: an
**attached JS program** — the behavior source for the cell's surface.

```
cell.state.heap_map
  (PROGRAM_COLL  = 0xC0DE) -> the applet manifest (affordances + view source)
  (VIEWTREE_COLL = 0x1E4F) -> the hosted view-tree {kind,props,children} JSON
  (SCRIPT_COLL   = 0x15CA) -> the attached JS program (event handlers / reactive logic)
```

The same proven chunked heap-blob codec applies (31 payload bytes per `FieldElement`
leaf, key 0 = the length header). Storing the script in the heap means it is part of
the cell's committed state: it travels with `to_cell_bytes()`, it is committed by
`heap_root`, and a receipted edit to it (a `ViewPatch`-style write back to
`SCRIPT_COLL`) moves the root — a light client witnesses the behavior evolving, the
same way it witnesses the view-tree evolving.

The attached JS is **cap-confined**. It runs in a sandbox with a capability-bounded
host API and *no ambient authority*. A JS handler that fires an affordance goes
through the SAME path as a static `{turn, arg}` button: the `is_attenuation` cap
tooth, then the executor's authority/conservation/freshness gates, leaving a real
`TurnReceipt`. The script cannot reach the filesystem, the network, the clock, or
any cell its host cap does not authorize. The only authority it has is the authority
the cell's surface was mounted under — exactly the authority a button on that
surface already had.

This is the ocap tie: **JS-on-a-cell is an attenuation of the cell's own
authority, never an amplification.** The host (cockpit or web shell) installs the
runtime under a *held* authority (the caller's attenuated cap, never the world
root, per the red-team invariant in `deos-js::attach`). Every host function the
script can call is bounded by that `held`.

## 2. The native runtime: boa (pure-Rust)

Today deos-js runs on real SpiderMonkey (`mozjs`) — the multi-GB C++ engine that is
the servo/web elephant. The cockpit (gpui) cannot embed that without dragging the
whole servo build in. We need a second engine for the native path.

### Candidates

| engine | language | size / link cost | sandboxable | runs in gpui native | runs in wasm/web |
|---|---|---|---|---|---|
| `mozjs` (SpiderMonkey) | C++ | multi-GB build, the servo elephant | yes | no (servo-coupled) | no |
| `deno_core` / `v8` | C++ | very heavy, snapshot infra | yes | awkward | no |
| `rquickjs` (QuickJS) | C | small + fast | yes | yes | needs emscripten/C-on-wasm |
| **`boa`** | **pure Rust** | **compile cost only, no C, no link elephant** | **yes (no ambient host)** | **yes** | **yes (native wasm target)** |

### Recommendation: `boa_engine`

`boa` is the right engine for cell-JS in a gpui-native cockpit:

- **Pure Rust, no C, no servo.** It adds compile time, never a native-link
  elephant. A bare `cargo build` produces it; it cross-compiles to `wasm32` with no
  emscripten/C toolchain. This is the decisive property: **one runtime that runs the
  *same* cell-JS in the cockpit (gpui) AND the web shell** — the goal of this work.
- **Sandboxed by construction.** A fresh `boa_engine::Context` has *no* host
  bindings — no `fetch`, no `fs`, no `process`, no clock beyond ECMAScript `Date`.
  The host installs exactly the cap-bounded functions it chooses and nothing else.
  The sandbox boundary is the absence of ambient host functions, which is precisely
  the ocap stance.
- **Embeddable host state.** Host functions are plain Rust closures/fn-pointers
  (`fn(&JsValue, &[JsValue], &mut Context) -> JsResult<JsValue>`). They bridge into
  the *same* substance binding deos-js already factored out (the engine-independent
  `Applet`/`AttachedApplet` over `DreggEngine`) so the verified-turn path is shared
  with the SpiderMonkey runtime.

The cost is honest: `boa` is not as fast as SpiderMonkey/V8, and it carries a
sizeable pure-Rust dependency tree (the `icu` Intl crates). For cell-attached event
handlers — small scripts that fire affordances and read bound state — throughput is
a non-issue, and the *runs-everywhere, links-nothing* property dominates. The two
engines coexist by design (see the no-reflexive-features architecture): they are
**separate crates over a shared substance**, not a feature flag on one crate.

```
                        ┌─────────────────────────────────────┐
                        │   the substance (engine-independent) │
                        │   DreggEngine · is_attenuation ·     │
                        │   verified turn → TurnReceipt        │
                        └───────────────▲─────────▲────────────┘
                                        │         │
                  ┌─────────────────────┘         └────────────────────┐
       deos-js (SpiderMonkey/mozjs)                       deos-js-runtime (boa, pure Rust)
       the servo/web shell path                           the cockpit (gpui) path + wasm/web
```

### Architectural note (the long-term shape)

The substance binding (`Applet`/`AttachedApplet`/`WorldSink`/`portable`/the cap
tooth) is already factored *engine-independent* inside `deos-js`, but `deos-js`'s
crate manifest hard-depends on `mozjs`. The clean end state is to lift that
engine-free substance into a shared crate (`deos-js-core`) that BOTH `deos-js`
(SpiderMonkey) and `deos-js-runtime` (boa) depend on, so neither engine duplicates
the turn path and the cockpit crate never sees mozjs. This first slice does **not**
perform that refactor (it would heavily touch the shared `deos-js` manifest); the
new crate instead binds the substrate crates (`dregg-sdk`/`cell`/`turn`/`types`)
directly — the same crates `deos-js::applet` binds — proving the substance binding
is genuinely engine-independent. Lifting `deos-js-core` is the named follow-up.

## 3. The cap-bounded host API

The surface the cell-JS can call. Everything else (fs/net/clock/ambient) is *absent*,
which is the sandbox.

| host fn | meaning | verified? |
|---|---|---|
| `t(turn, arg)` | **fire an affordance on the HOME cell** — commit ONE cap-gated verified turn | yes — `is_attenuation` + executor + `TurnReceipt` |
| `tCell(cell, turn, arg)` | **fire an affordance on ANOTHER cell** the JS holds a cap to — the multi-cell coordination keystone | yes — same `is_attenuation` tooth, against the cap held for THAT cell |
| `transfer(from, to, amount)` | **move value** between two cells the JS holds caps to | yes — `Effect::Transfer`, conservation enforced by the executor |
| `get(slot)` / `get(cell, slot)` | witnessed read of a home / named-cell model slot off the live ledger | read, confers no authority |
| `viewPatch(node)` | append a `{kind,props,children}` node to the home cell's view-tree, seal the blob into its committed heap, and bump the view version via a turn | yes — a receipted heap write moving `heap_root` + a `SetField` provenance turn |

### The single-cell vs multi-cell substance

`t(turn,arg)` against ONE cell is the [`CellApplet`] substance (slice 1). A starbridge-app
is not one cell behaving but a program *coordinating* several cells, so the upgraded
substance is [`CellWorld`] (`deos-js-runtime::world`): ONE embedded `DreggEngine` holding
several cells, plus a **cap table** mapping each *string handle* the JS may use to
`(cell id, held authority, affordance surface)`. `NativeRuntime::run_world` installs the
full host surface (`t`/`tCell`/`transfer`/`get`/`viewPatch`) over it.

**The confinement keystone (ocap).** The JS references cells ONLY by the handles the cap
table installed — there are no ambient cell ids in the sandbox, exactly as there are no
ambient host functions. A name absent from the table resolves to `NoCapability`: the cell
it would have pointed at is never touched (you cannot even *name* what you do not hold). A
name present whose held cap does not satisfy an affordance's `required` resolves to
`Unauthorized` (the same `is_attenuation` tooth). A JS app can therefore touch only the
cells it holds caps to, and only at the authority it holds — proven in
`tests/native_js_app_coordinates_cells.rs` (the uncapped `vault` cell stays byte-untouched
while a refused over-reach commits nothing).

Each acting cell chains its OWN authority head (`previous_receipt_hash`), because the
executor advances that head only for the submitting agent — a multi-cell app is several
independent per-cell turn chains woven by one script, not a single chain.

`t(turn, arg)` is the keystone and the subject of the first slice. It maps exactly
onto the proven fire path (`deos-js::applet::Applet::fire` /
`AttachedApplet::fire`):

1. resolve the affordance by name (unknown ⇒ no turn);
2. **cap tooth, in-band**: `held` must satisfy the affordance's `required`
   (`dregg_cell::is_attenuation`) — an over-reach commits *nothing* and never reaches
   the executor;
3. compute the writes as a pure function of the live model;
4. build the verified turn (the affordance name as the action method, the chain head
   threaded, the fee stamped) and `execute_turn` it on the embedded executor;
5. a real `TurnReceipt` returns; its hash joins the audit tape.

The host functions are installed on a fresh `boa` global per run; the script sees
only them plus the ECMAScript builtins. There is no `globalThis.fetch`, no `require`,
no `import` of host modules.

## 4. Integration: how the cockpit runs a cell's attached JS

The cockpit's card renderer (`card_surface` / `card_pane`) today wires a surface
button to a static `{turn, arg}` and fires it through the World on click. JS-on-cells
generalizes the click handler:

- when a cell hosts an attached JS program (a `SCRIPT_COLL` blob), the renderer
  resolves a **handler** for a surface event (e.g. `on:click="bump"`) and, on the
  event, runs that handler in the native `deos-js-runtime` `Context` bound to the
  cell's `AttachedApplet` (the same live World + `held` the static path uses);
- the handler calls the cap-bounded host API — typically `t("inc", 1)` — which
  commits a verified turn exactly as the static button did. A handler may do more
  than one fire, read bound state between them, and decide what to fire — that is the
  added expressivity over a static `{turn, arg}`;
- a cell with **no** attached JS keeps the static `{turn, arg}` fast path unchanged.
  Attached JS is additive.

**Renderer-independence.** The handler runs against the engine-independent substance
(`AttachedApplet` over a `WorldSink`), and the host API (`t`/`get`/`viewPatch`) is
identical in the cockpit and in the web shell. The *same* cell-JS therefore runs in
gpui-native and in web — the cockpit binds the boa `Context` to its live `World`; the
web shell binds the (SpiderMonkey today, boa-on-wasm tomorrow) `Context` to its
`World`. Neither the script nor the host API knows which renderer it is under.

## Status / slices

- **Slice 1 (this pass) — DONE:** the `deos-js-runtime` crate (pure-Rust boa over the
  substrate) with the cap-bounded host fn `t(turn, arg)`, plus a proof-of-concept
  test: a tiny cell-JS handler, run in the native runtime with *no* servo/mozjs,
  fires a real verified turn through the executor and the model advances. The cap
  tooth is exercised too (an over-reach `t("reset", 0)` against a `Signature`-held
  surface commits nothing).
- **Slice 2 (this pass) — DONE: userspace apps as pure JS-on-cells.** The host API is
  upgraded toward full-app power over a multi-cell [`CellWorld`]: `get`/`getCell`
  (witnessed read), `viewPatch` (receipted heap self-edit moving `heap_root`), `tCell`
  (cap-gated turn on ANOTHER cell — the multi-cell-coordination keystone), and `transfer`
  (conservation-respecting value movement). A pure-JS starbridge-app prototype
  (`tests/native_js_app_coordinates_cells.rs`) runs in the native runtime with NO servo and
  coordinates two cells — `tCell("store","put",42)` + `transfer("wallet","store",100)` +
  `viewPatch(...)` + `get("store",0)` — committing THREE real verified turns, and an
  over-reach to a cell it holds no cap to is refused in-band (the uncapped cell stays
  byte-untouched).
- **Next rung — cockpit wiring:** resolve a cell's `SCRIPT_COLL` handler on a
  surface event in `card_surface`/`card_pane` and run it in the native runtime bound
  to the live `World` (additive to the static `{turn,arg}` path).
- **Next power-up — a literal-write `ApplyOp` + a published-interface bridge:** today an
  affordance's effect is one of `AddToSlot`/`SubFromSlot`/`SetSlot{fixed}`; `put(reg,v)`
  rides `AddToSlot` over a zeroed slot (post-state = `v`). A `SetSlotFromArg`/multi-write
  `ApplyOp`, and a bridge that reads a cell's published `InterfaceDescriptor`
  (`route_method`) so `tCell` names a *typed method* rather than a local affordance, close
  the gap to expressing an arbitrary starbridge-app `CellProgram` in pure JS.
- **Follow-up — `deos-js-core`:** lift the engine-free substance out of `deos-js` so
  both engines share one turn path and the cockpit crate never links mozjs.
- **Follow-up — boa-on-wasm in the web shell:** retire the servo-only constraint by
  running the *same* `deos-js-runtime` compiled to `wasm32` in the web shell.
