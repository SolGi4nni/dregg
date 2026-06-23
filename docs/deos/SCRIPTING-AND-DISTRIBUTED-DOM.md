# A deos-native scripting environment + the distributed DOM

*Design state, grounded in the metatheory and the gpui-free reflective substrate. Present-tense
("what it is"); the proven-vs-open ledger is explicit. Companion to `DREGG-CALCULUS.md` and
`../../metatheory/CONSTRUCTIVE-KNOWLEDGE.md`.*

> **The JS objects crawl and drive the live image.** A reflective scripting surface where you
> write script (JS first, because we already embed mozjs via servo) and the objects you touch
> ARE live handles into the running deos image — cells, caps, the ledger, affordances, surfaces.
> Reflection is cap-bounded and attested (you observe only what you can produce a witness for);
> interaction is production-under-non-forgeability (every fired affordance is a verified turn).
> Pharo-liveness fused with deos's substance — *cap-gated Pharo, not omniscient Pharo.*

It is **language-agnostic at the binding.** The real artifact is the binding layer (cells-as-
objects, turns-as-productions, the reflective object graph, the gpui render of a view). mozjs/JS
is the first host because the engine is already in-tree and it is the lowest barrier for
education / outreach / uplift; the same binding could later host a Scheme or a Smalltalk-ish.

---

## 1. What a cell IS (the structure, read off the Lean)

A cell is **not** a polynomial functor. It is **codata**: `νC. µI. StepProof I × (Turn ⇒ C)`
(`CONSTRUCTIVE-KNOWLEDGE.md §3`) — a greatest-fixpoint whose *every transition carries a
`StepProof` of its full invariant*, with "stays correct forever" being a **▶-guarded bisimulation
to a golden-oracle reference** ("the knowledge never drifts from the truth it claims"). Transitions
aren't state-changes; they are **proof-carrying turns**.

Its observable shadow is a **Moore coalgebra** for the behaviour functor `F X = Obs × (Adm → X)`
(`Metatheory.Categorical §3`, the real cell is `Dregg2.Boundary.TurnCoalg`):
- `Obs` — what you can observe of the state (the **render**);
- `Adm` — the admissible actions (the **affordances** / turns);
- `str : V → Obs × (Adm → V) = (obs, next)`.

The final coalgebra `νF` exists (carrier `List Adm → Obs` — "what I'd observe after each finite
word of turns"; `FinalCoalgebra.lean`, `#assert_axioms`-clean), and **`Boundary.no_drift_into_nuF`**
proves any two observers who unfold the same cell into `νF` compute the *same* Moore behaviour —
the coinductive guarantee that distributed views cannot disagree.

*(The behaviour functor `X ↦ Obs · X^Adm` is itself a monomial polynomial `Obs y^Adm` — so a cell
is a coalgebra FOR a polynomial functor. The cell is the coalgebra; the tools are coinduction /
bisimulation / `νF`, not poly-substitution.)*

So a **reactive UI component IS a cell**, coalgebraically: `obs` = render, `next` = the affordances.
This is exactly `Deos/Affordance.lean` (`fire_authorized_iff`) and `Deos/Reactive.lean`
(`fireReactive_iff`: a reactive affordance is a turn gated by transition-shape AND clock).

## 2. Authority is PRODUCTION, not spend (the load-bearing reframe)

`CONSTRUCTIVE-KNOWLEDGE.md §0`, stated with its negation first because the wrong reading is
seductive: **authority is *not* affine descent / a resource that drains as you spend it.** It is
**production under non-forgeability** — you *hold* a cap iff you can *produce a witness the kernel
accepts*, every time, at the point of use. The four facets (`gateOK`, `FullForestAuth.lean:490`):
non-forgeability (WHO) · `granted ⊆ held` (WHAT) · caveats discharged (HOW) · not-revoked.

For the scripting model this is decisive: **`affordances` are not capabilities you spend — they
are witnesses you can produce.** A button you may press is *a proposition you can prove*. `next`
on an admissible action is a production discharged through `gateOK`, fail-closed, leaving a receipt
(the evidence substance grows; §5 — anti-ghost: you cannot witness knowledge you did not construct).

## 3. The reflective object graph (gpui-free, already proven via dregg-mcp)

The entire reflective + drive surface is gpui-free and exercised live by the **dregg-mcp** server
(`starbridge-v2/src/bin/dregg_mcp.rs`) — the scripting env is its in-process twin. The JS objects
bind to:

```js
deos.world                      // the embedded verified World (executor + ledger) — world.rs
  .cells()                      // ledger().iter()                      — crawl every cell
  .ocap()                       // OcapGraph::build — graph.rs           — the capability web
  .snapshot()/restore()/rewind()// World::fork + replay                 — cheap time-travel
  .receipts()                   // append-only provenance log
deos.cell(id)                   // ledger().get(id) → dregg_cell::Cell  — the four substances:
  .balance                      //   state.balance() : i64              (value)
  .caps                         //   capabilities.iter() → CapabilityRef (authority / c-list)
  .fields / .program / .heap    //   state.fields[..]/fields_map/heap_map + program (state)
  .evidence                     //   committed_height/delegation_epoch/lifecycle (evidence)
  .present(viewer)              //   Registry::present → the 7 moldable faces (§3.1)
  .affordances(viewer)          //   AffordanceSurface::project_for → cap-badged messages
  .fire(msg, actAs)             //   → a REAL verified turn → TurnReceipt (FireOutcome)
  .as(viewer)                   //   → the cap-bounded FRUSTUM (§3.2)
deos.search(q)                  // Spotter — fuzzy over every object's every face
deos.world.dfsGameTree({…})     // the atlas crawl (DFS via snapshot/restore) in JS
```

Every binding is gpui-free, reads live machinery (no parallel model), and is file-cited in the
orientation sweep. The cell-substance accessors are in `cell/src/{cell,state,capability,
permissions}.rs`; the reflective layer in `starbridge-v2/src/{reflect,presentable,inspect_act,
affordance,graph}.rs`.

### 3.1 Reflection is MOLDABLE, not flat — the 7 faces

Every object exports `present()` → up to seven faces (the `Presentable` framework, `presentable.rs`;
38 live impls, all gpui-free): **`RawFields · Graph(ocap) · DomainVisual(state-machine/gauge) ·
Affordances · Provenance(receipt-chain) · Invariant(conservation) · Source(program/Datalog)`**. In
coalgebra terms these are seven `Obs`-projections of the same cell — `cell.present()` is the
moldable multiplicity of observations. (The deep L2–L10 lenses — predicate composer, turn builder,
cap-attenuation dial, circuit verifiers, settlement builders — are designed + gpui-free + callable
from JS now; only the *cockpit's* gpui render Registry for them is unwired.)

### 3.2 Reflection is CAP-BOUNDED + ATTESTED (the frustum) — "cap-gated Pharo"

`.as(viewer)` is a real per-viewer frustum, not a filter, computed gpui-free from REAL authority:
- **which cells** you crawl — reachability BFS through the viewer's c-list (the ocap closure);
- **which fields** you read — `FieldVisibility` bounds it (`Committed`/`SelectivelyDisclosable`
  show the *commitment*, never the value);
- **which affordances** you may fire — `AffordanceSurface::project_for` filters by `is_attenuation`
  (`affordance.rs`); a weaker viewer sees fewer, an admin sees more; lacking authority → refused;
- **embeds darken** on incomparable authority — `WholeCellTransclusion::project_for` →
  `Membrane::project` returns the lattice meet or `Err(Amplification)` → the embed darkens
  (provenance survives, surface withheld). Same machinery the membrane proves non-amplifying.

So crawling can never observe past your authority, and reads are attested + non-omittable (§8 of
the knowledge doc: `server_cannot_omit_position`; `transclusion_grants_no_unheld_authority` —
*certificate is not capability*: observing a child's render confers no power over it).

## 4. The distributed DOM

### 4.1 The local↔fully-distributed spectrum is `Φ × WitnessMode`

`CONSTRUCTIVE-KNOWLEDGE.md §6`: inside a trust root authority is **positional** (caps-as-caps —
holding the edge *is* the proof; cheap, local), and across a boundary it becomes **epistemic**
(keys-as-keys — you must *present* a verifiable witness) via a named-lossy functor **Φ** under which
"permission survives, authority does not" (a forwarded cap becomes revocable by construction).
Layer **WitnessMode** (`§3a`): local turns run **symbolic** (≈ zero hashing), collapsing to a
publishable witness only when crossing the boundary.

This *is* the cell-granularity spectrum:
- **coarse** = one cell whose `obs` renders a whole interactive subgraph (positional + symbolic;
  cheap, local). One coalgebra, free intra-cell interactivity.
- **fine / per-node** = many tiny coalgebras wired into a composite (keys-as-keys + collapse at
  every node-boundary; **maximally inefficient — the valid limit of a fully-distributed DOM**).

You factor cells to keep an interactive subgraph inside one trust root and **cut only where you
genuinely want the epistemic crossing** (a different principal, a handoff, a shareable subrealm).
The per-node limit isn't wrong — it's the expensive end, and it's a real point on the dial.

### 4.2 Composition + multiplayer soundness (mostly deployed proof)

- **render = an attested, non-omittable, per-viewer read that confers no authority** (§3.2). The
  view half is sound *and* powerless by construction.
- **interaction = production** gated by `gateOK`; across a boundary you present a witness
  (keys-as-keys), within a trust root you hold the edge (caps-as-caps).
- **composition**: a parent's `obs` reads its children's `obs` (= transclusion, built) and its
  `next` routes to a child's affordance (= firing a sub-cell turn). The bialgebra/distributive-law
  shape.
- **no two observers drift** — `Boundary.no_drift_into_nuF` (§1).
- **multiplayer co-drivers, incl. adversarial, are bounded by deployed proof** — `polis_safety`
  ("verify the cage, not the animal") bounds *every* opaque controller (human · agent ·
  leaked-key adversary: `key_leak_contained`, `leak_blast_no_amplify`) to the shared floor,
  controller-blind. A subgraph driven by several principals at once is sound *now*.
- **"what each observer knows"** is the epistemic guard modality `Knows/EveryoneKnows/
  DistributedKnows/CommonAt`; the shared *settled* view is `CommonAt(tip)`.
- **merge of diverged distributed subgraphs** = branch-and-stitch pushout (`stitch_is_pushout`),
  conflicts first-class, lossy-drops explicit; authority re-evaluated at the settlement tip.

## 5. The proven-vs-open ledger (honest)

**Deployed proof (the bulk):** the cell coalgebra + `no_drift_into_nuF`; authority = production
(`gateOK`, the four facets, `production_step_fpu`); attested non-omittable reads
(`server_cannot_omit_position`); transclusion confers no authority; per-viewer membrane projection
+ darkening (non-amplifying); `polis_safety` multiplayer/adversary floor; stitch pushout-correctness;
the entire gpui-free reflective API (proven live via dregg-mcp).

**Named open frontiers (from `CONSTRUCTIVE-KNOWLEDGE.md §12`):**
- **the macaroon↔cap arrow** — the four credential aspects (biscuit·macaroon·cap·zk) are today
  joined by `&&`, not by one proven arrow `chainGateG → capAuthorityG`. Genuine fail-closed
  defense-in-depth, just not *one* production. Not on the scripting env's critical path.
- **Settlement `BindsLiveAuthority`** — settlement soundness is proved but the settlement predicate
  the deployed commitment uses is a *typed hypothesis*. **The distributed-DOM *merge* (stitch) leans
  on exactly this** (authority live at the tip). If we lean hard on distributed settlement-time
  merge, this is the floor we stand on; local/single-trust-root composition does not need it.

## 6. The build plan

- **Slice 1 — drive (LANDED, green by running):** `deos-js` embeds mozjs standalone; `deos.applet({
  affordances })` mints one cell (an interactive subgraph), an affordance call = a real cap-gated
  verified turn (a receipt), view-state stays ephemeral, `transclude` composes through the real
  `WebOfCells`/`TranscludedField`. The JS↔substance *production* spine, proven on real SpiderMonkey.
- **Slice 1.5 — `deos-reflect` (LANDED):** the gpui-free reflective substrate extracted as its own
  crate (the clean shared shape; de-bloats the eventual cockpit too). Pure functions of a
  `dregg_cell::Ledger` + receipts: `substance` (the four substances + `Inspectable`, reading fields
  PUBLICLY so `Committed` redacts), `graph` (`OcapGraph`: nodes/edges/reachability/layers), `frustum`
  (the cap-bounded per-viewer crawl — unreachable = absent, never forged), `affordances` (cap-gated
  message projection by `is_attenuation`, decoupled from the window cap onto bare `AuthRequired`),
  `present` (the substrate-pure faces: RawFields · Graph · DomainVisual · Provenance). 5/5 tests.
- **Slice 2 — crawl (LANDED, green by running):** `deos.world.cells()` / `deos.world.ocap()` /
  `deos.cell(id).reflect()` (the 4 substances) / `.field(k)` / `.as(viewer)` (the frustum:
  `.canObserve` / `.reflect`) bound to mozjs over `deos-reflect` (JSON via string-returning natives).
  Proven by running: from JS, crawl the ledger, read a cell's `balance` substance, and confirm the
  frustum is cap-bounded (self observable; a stranger absent + `reflect()===null`) — and the crawl
  commits NO turns (reflection is a READ). *Still to fan out:* the moldable `present()` faces as JS
  objects (the Rust side is done in `deos-reflect::present`), `snapshot`/`rewind` time-travel, and a
  `spotter` fuzzy search.
- **Slice 3 — view (the QML toolkit, next):** render an applet's `obs` as a gpui element tree from JS
  (declarative view + affordance handlers = turns), the moldable faces as inspectable surfaces. The
  per-node↔coarse dial (§4.1) is a property of how you factor applets into cells.
- **Throughout:** language-agnostic binding (JS-first; the binding is the artifact). Reflection
  stays cap-bounded + attested; interaction stays production-under-non-forgeability.
