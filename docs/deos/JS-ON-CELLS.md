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
| `t(turn, ...args)` | **fire an affordance/typed method on the HOME cell** — commit ONE cap-gated verified turn | yes — `is_attenuation` + executor + `TurnReceipt` |
| `tCell(cell, method, ...args)` | **fire a typed method on ANOTHER cell** the JS holds a cap to — resolved through THAT cell's published `InterfaceDescriptor::route_method` (the verified DFA dispatch `invoke()` speaks) when one is published, else a bare affordance name | yes — same `is_attenuation` tooth, against the cap held for THAT cell + the published `MethodSig`'s requirement |
| `transfer(from, to, amount)` | **move value** between two cells the JS holds caps to | yes — `Effect::Transfer`, conservation enforced by the executor |
| `get(slot)` / `get(cell, slot)` | witnessed read of a home / named-cell model slot off the live ledger | read, confers no authority |
| `viewPatch(node)` | append a `{kind,props,children}` node to the home cell's view-tree, seal the blob into its committed heap, and bump the view version via a turn | yes — a receipted heap write moving `heap_root` + a `SetField` provenance turn |
| `seal(bidder, value, nonce)` | compute the **sealed commitment** `BLAKE3(bidder‖value‖nonce)` (the same construction the real `Bid::seal` uses), returned as hex — a bidder publishes ONLY this digest at commit time | read / pure — confers no authority, commits no turn |
| `commitSeal(cell, {slot, seal, guard?})` | **freeze a sealed bid** at `slot` as ONE cap-gated verified turn; WRITE-ONCE (a committed bid cannot be overwritten) + an optional phase guard | yes — `is_attenuation` (the published `commit` method's req) + write-once + executor + `TurnReceipt` |
| `revealBid(cell, {sealSlot, revealSlot, bidder, value, nonce, guard?})` | **open a sealed bid** — the runtime RE-HASHES the opening and refuses one that does not bind to the frozen seal (the binding tooth), then writes the value as a turn | yes — `is_attenuation` (published `reveal` req) + in-band binding check + optional phase precondition + `TurnReceipt` |

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
`deos-js-runtime/tests/native_js_app_coordinates_cells.rs` (the uncapped `vault` cell stays byte-untouched
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
  (`deos-js-runtime/tests/native_js_app_coordinates_cells.rs`) runs in the native runtime with NO servo and
  coordinates two cells — `tCell("store","put",42)` + `transfer("wallet","store",100)` +
  `viewPatch(...)` + `get("store",0)` — committing THREE real verified turns, and an
  over-reach to a cell it holds no cap to is refused in-band (the uncapped cell stays
  byte-untouched).
- **Next rung — cockpit wiring:** resolve a cell's `SCRIPT_COLL` handler on a
  surface event in `card_surface`/`card_pane` and run it in the native runtime bound
  to the live `World` (additive to the static `{turn,arg}` path).
- **Power-up — a literal-write `ApplyOp` + a published-interface bridge — DONE:** the two
  named gaps to expressing an arbitrary starbridge-app `CellProgram` in pure JS are closed.
  1. **Literal / register-addressed writes.** `ApplyOp` gains `SetSlotFromArg { slot }`
     (`slot := arg` — write the JS value DIRECTLY, overwriting, so a `put(v)` lands `v`
     exactly even over a non-zero slot) and `SetRegisterFromArgs` (`args[0] := args[1]` —
     write the JS-supplied VALUE to the JS-supplied REGISTER, the kvstore `put(reg, value)`
     shape). Both lower to the SAME ordinary `Effect::SetField` the executor already
     enforces and a light client already witnesses — the op is a runtime-layer *write-shape*,
     **NOT a kernel/effect-vocabulary or circuit change, so there is no VK seam** (the
     `ApplyOp` enum is a `deos-js-runtime`/`deos-js` local, not a `cell/` effect). `t`/`tCell`
     now take variadic numeric args to feed it.
  2. **The `route_method` bridge.** A cell may `CellWorld::publish_interface` its first-class
     typed `InterfaceDescriptor` (the same content-addressed descriptor the real
     kvstore/escrow cells publish). When present, `tCell(cell, "method", ..)` resolves the
     method through the verified DFA `InterfaceDescriptor::route_method` — the SAME dispatch
     `dregg_app_framework::invoke()` speaks: an undeclared method is fail-closed
     (`MethodNotRouted`), a `Semantics::Serviced` method is refused as a non-turn read
     (`ServicedSeam`, mirroring `invoke()`'s seam), and the cap requirement is the published
     `MethodSig`'s — so the JS names a TYPED METHOD, not a bare affordance index.

  Proven by running: `deos-js-runtime/tests/native_js_kvstore_pure_js.rs` rebuilds the `starbridge-kvstore`
  service cell as pure JS-on-cells — `tCell("store", "put", reg, value)` writes the JS value
  to the JS register through the published `put` method (typed, `Signature`-gated,
  DFA-routed), overwrites it with a second literal write, refuses `get` as a serviced seam,
  refuses an undeclared method, and gates on the published interface's cap — all real
  verified turns, with NO servo.
- **Second app — a multi-cell, value-COORDINATING app (2-party escrow) as pure JS — DONE:**
  the kvstore is a single cell behaving; an escrow is a JS program *coordinating several cells
  and moving value through an intermediary*, which is the harder shape the multi-cell
  `CellWorld` exists for. `deos-js-runtime/tests/native_js_escrow_pure_js.rs` drives a whole 2-party escrow
  across THREE cells — a buyer (`alice`), a seller (`bob`), and the `escrow` coordinator —
  entirely in pure JS:
  1. **arm** — `tCell("escrow", "arm", price)` records the agreed price through the escrow's
     published typed interface (DFA-routed, `Signature`-gated, `SetSlotFromArg`);
  2. **fund** — `transfer("alice", "escrow", price)` moves the buyer's value into the escrow,
     conservation enforced by the executor;
  3. **settle** — `tCell("escrow", "settle")` flips the escrow state machine to SETTLED (a
     second typed turn);
  4. **pay out** — the payout amount is READ BACK off committed escrow state
     (`get("escrow", AMOUNT_SLOT)`) and `transfer("escrow", "bob", owed)` releases it to the
     seller.

  Four properties are proven by running: (a) the happy path settles and the three-cell
  balance sum is CONSERVED (initial sum minus exactly one burned fee per committed turn —
  value genuinely moves alice → escrow → bob, none created/destroyed); (b) a `reclaim`
  instead of a settle REFUNDS the depositor and the seller never receives it; (c) an
  unauthorized release leg (the published `settle` requires `Proof`, the app holds only
  `Signature`) is refused IN-BAND (`Unauthorized`) — the funds stay LOCKED in the escrow,
  nothing reaches the seller; (d) a drain to an UNHELD party (`transfer("escrow", "mallory",
  ..)`) is `NoCapability` — the escrow funds untouched, the uncapped cell byte-identical, and
  a legitimate payout still commits afterward. All real verified turns, NO servo.

  **The compound/conditional-turn power-up (LANDED).** The escrow's release is now ONE
  atomic, state-guarded turn. The `batch(actor, specJson)` host fn fires a COMPOUND turn from
  pure JS: `specJson` is a `JSON.stringify`'d `{ guard?, ops }` object — an optional `guard`
  (`{slot, value}`) and an ordered list of legs (`transfer`/`setSlot`). It maps to ONE
  verified turn (`CellWorld::guarded_batch`) built from two kernel primitives the executor
  already enforces and a light client already witnesses:

    - **the guard is a real `require_field_equals` precondition** on the actor's state. The
      executor checks it AHEAD of every effect (`check_preconditions`, before any effect
      runs), and it folds into `Action::hash` (the anti-downgrade commitment) — so the
      "only-if-SETTLED" link between the state cell and the value move is part of what the
      turn PROVES, witnessed by a light client, not an off-chain ordering the JS chose;
    - **the legs commit atomically** — multiple effects in one action are all-or-none ("if
      any action fails, ALL effects are rolled back via journal replay"). A guard that does
      not hold, an over-drawn transfer, or a transfer to an unheld cell refuses the WHOLE
      turn: no partial release.

  So the escrow's "release = check SETTLED ∧ transfer to seller, atomically" is a single
  witnessed turn the kernel commits whole or refuses whole. Proven by running (tests
  (e)..(g2) in `native_js_escrow_pure_js.rs`): (e) a guarded release commits IFF the escrow
  is SETTLED — one receipt; (f) a guarded release attempted while still OPEN is refused
  atomically (`PreconditionFailed`) — no transfer, no partial, no receipt; (g) a compound
  `settle ∧ pay` commits as ONE receipt; (g2) all-or-none — a compound whose transfer leg
  over-draws rolls back the state flip too. (Honest note: the guard refusal is enforced
  INSIDE the executor, so a refused guarded turn burns the submitter's fee — unlike the
  pre-flight cap-tooth / `NoCapability` refusals, which never reach the executor and are
  free.)

  **The kernel primitive, and the one remaining seam.** This is `Preconditions` +
  per-action atomicity — STRONGER than a bolt-on `Effect::ConditionalBatch` would be, because
  both are already kernel-enforced AND already in the action commitment (no new effect
  variant, no VK change). The one narrow limit: the guard reads the ACTOR's OWN state (the
  precondition evaluates against `action.target`). A cross-cell guard — commit on cell B's
  state while acting on cell A — would need a `witnessed`-clause precondition or a
  multi-party atomic turn. For the escrow the guard cell and the value-source are the same
  cell (the escrow), so the release is fully covered. With `batch`, an arbitrary multi-cell
  app — not just its value movement and dispatch but its *guarded coordination* — is
  expressible as pure JS-on-cells.
- **Third app — a multi-party COMMIT-REVEAL sealed-bid auction as pure JS — DONE:** the
  kvstore is one cell behaving and the escrow coordinates two parties through an intermediary;
  a sealed-bid auction is the harder shape — SEVERAL parties COMPETE for one award by sealing
  HIDDEN bids, then opening them under a runtime-enforced binding. `deos-js-runtime/tests/native_js_sealed_auction_pure_js.rs`
  drives a whole auction across FIVE cells (three bidders `alice`/`bob`/`carol`, the `seller`,
  the `auction` coordinator) entirely in pure JS, mirroring `starbridge-apps/sealed-auction`
  (the executable surface of `Dregg2/Intent/SealedAuction.lean`).

  **The power-up this app needed — a commit-reveal helper (LANDED).** No existing primitive
  could enforce that a reveal BINDS to its sealed commitment, and a binding the JS computed
  AND the JS checked would enforce nothing (a malicious script would just write whatever). So
  the RUNTIME owns the seal:
    - `seal(bidder, value, nonce)` — a pure host fn returning the BLAKE3 sealed commitment
      (the same `Bid::seal` construction). A bidder publishes ONLY the digest at commit time;
      the secret value/nonce stay in JS variables until reveal.
    - `commitSeal(auction, {slot, seal, guard?})` — freeze a sealed bid as ONE cap-gated
      verified turn, with WRITE-ONCE (`CommitmentMismatch` refuses overwriting a committed bid
      — the anti-front-running tooth) and an optional phase guard.
    - `revealBid(auction, {sealSlot, revealSlot, bidder, value, nonce, guard?})` — the runtime
      RE-HASHES `(bidder, value, nonce)` and refuses an opening that does not bind to the
      frozen seal (the keystone binding tooth), optionally phase-guarded; the revealed value
      is then written as a verified turn. The full 256-bit BLAKE3 digest lives in ONE
      cell-state field (no truncation), so the binding is the hash's full second-preimage
      resistance, not a folded u64.

  The same guarantees the Lean development proves are exercised AS PURE JS, by running: (a) the
  happy path — three sealed commits hide the bids, three bound reveals open them, the highest
  (bob) wins, the first-price payment reaches the seller, value CONSERVED (only per-turn fees
  burned), and the winner's value is provably bound to its commitment (`winner_was_committed`);
  (b) `reveal_binds_committed` — a reveal with a SWITCHED value is refused in-band
  (`CommitmentMismatch`), no peeking-then-switching; (c) `uncommitted_cannot_open` — a party
  that never sealed cannot reveal; (d) anti-front-running — a committed bid cannot be
  overwritten (write-once); (e) `reveal_requires_reveal_phase` — a reveal before the commit
  phase closes is refused ATOMICALLY by the kernel phase precondition (light-client-witnessed);
  (f) settlement confinement — the payout cannot drain to an unheld party (`NoCapability`), the
  legitimate payout still commits; (g) the reveal cap gate comes from the PUBLISHED interface
  (`reveal` requiring `Proof` refuses the `Signature`-holding app). All real verified turns, NO
  servo.

  **How close to "an arbitrary app in pure JS".** The host surface now spans dispatch (typed
  `route_method`), state writes (the `ApplyOp` write-shapes), value movement (`transfer`,
  conserved), guarded atomic multi-step coordination (`batch`), and a commitment protocol
  (`seal`/`commitSeal`/`revealBid`). The three exemplars cover the single-cell service, the
  intermediary-coordination, and the multi-party-competition shapes. The remaining gap toward
  a fully arbitrary app is the CROSS-CELL guard (a precondition reading cell B's state while
  acting on cell A — the named `batch` seam, needing a `witnessed`-clause precondition or a
  multi-party atomic turn), richer value/heap reads, and lifting `deos-js-core`.
- **Follow-up — `deos-js-core`:** lift the engine-free substance out of `deos-js` so
  both engines share one turn path and the cockpit crate never links mozjs.
- **Follow-up — boa-on-wasm in the web shell:** retire the servo-only constraint by
  running the *same* `deos-js-runtime` compiled to `wasm32` in the web shell.
