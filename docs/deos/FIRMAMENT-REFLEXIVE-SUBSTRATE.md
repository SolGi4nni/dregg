# THE FIRMAMENT REFLEXIVE SUBSTRATE

> **BUILT — two of the three design tasks have landed; one seam is still genuinely open.**
> This began as a design doc; the body below is preserved as the design rationale. State at HEAD:
> **Task B (Suspend) is DONE** — `World{ suspended, pending }`, the `commit_turn` pre-check,
> `CommitOutcome::Queued`, the `TurnQueued` event, `pub enum ResumeMode { Drain, Modified(..) }`,
> and `suspend()`/`resume()`/`resume_drain()` all live in `starbridge-v2/src/world.rs`.
> **Task C (the cap-stratified tower) is DONE** — `FocusTarget` carries the
> `DebugFrame(MetaLevelId)`/`World`/`Cockpit` arms (`starbridge-v2/src/presentable.rs`), and
> `MetaLevelId`/`MetaDebugView`/`MetaStack` are implemented (`starbridge-v2/src/meta_debug.rs`).
> **Task A (the mirror-cap: `Target::Mirror{over,depth}` + `MirrorDepth`) is the single open seam** —
> `dregg_firmament::Target` still has only `Local`/`Distributed`/`Surface`/`HostPd`; no `Mirror` arm exists yet.
> The deferred dataflow self-cycle (Seam 1) also remains open by design. See §6 for the per-task status.

## Cap-secure self-hosting: mirror-caps, the cap-stratified reflective tower, and Suspend

starbridge is a self-hosting reflexive image: the inspector, the debugger, and
the time-travel scrubber are themselves dregg objects, focusable like any cell.
This document designs the AUTHORITY-STRUCTURE mechanism that makes that
self-hosting *cap-secure* — three pieces and how they compose:

1. **mirror-caps** — reflection = holding a firmament `Capability` whose
   authority is *reflect/inspect over a target subgraph*;
2. **the cap-stratified tower** — a meta-level holds a mirror-cap OVER the level
   below; the base holds none up; authority flows strictly downward,
   unforgeably, and witnessed;
3. **Suspend** — halt-the-live-loop: a turn-application gate + a pending-turn
   queue + the continuation reified as a *partial turn*.

This is the "firmament is substantial" core. It is the authority structure, not
the dataflow self-cycle. **One piece is deliberately deferred to the
stratified-fixpoint dataflow explorer:** *how the self-projection cycle resolves*
(unit-delay vs. exact) when a projector projects cells that include its own view
state (`REFLEXIVE-MIGRATION.md` §2.3.5, §5.2). Everything here is mechanism that
sits *underneath* that resolution and does not presuppose it; §5 is explicit
about the seam between the two.

The substrate this rides already exists. A window IS a real
`dregg_firmament::Capability` over `Target::Surface(cell)`
(`sel4/dregg-firmament/src/lib.rs:198-211`), authenticated by the genuine
`granted ⊆ held` (`is_attenuation`) gate (`:285-305`), with the `n`-parametrized
`Bounds{revocation_immediate, commit_synchronous, n}` distance model
(`:307-348`). Every reflective act designed below is *the same handle, the same
gate, the same bounds* — pointed at a new kind of target.

---

## 1. MIRROR-CAPS AS FIRMAMENT CAPS

### 1.1 The Bracha–Ungar mirror principles, each as a cap property

Bracha & Ungar's *"Mirrors: Design Principles for Meta-level Facilities"*
(OOPSLA 2004) name three principles for a reflection API:

- **Encapsulation** — reflective access goes *only* through a mirror object; you
  cannot reach a target's internals except by holding a mirror over it. There is
  no ambient reflective authority.
- **Stratification** — the meta-level (the mirror) is cleanly separated from the
  base level (the target); base computation runs with no reflective capability,
  and the meta-level is *layered on top*, removable.
- **Ontological correspondence** — the mirror's structure mirrors the structure
  of what it reflects (a mirror over a cell exposes cell-shaped reflection).

dregg already runs an ocap discipline that makes each of these a *cap property*,
not an API convention you can violate:

| Bracha–Ungar principle | dregg cap realization |
|---|---|
| **Encapsulation** (access only via a mirror) | A mirror-cap is a `Capability`. With no ambient authority (the compositor/shell discipline, `surface.rs:5-9`), the *only* way to reflect over a target is to *hold* a mirror-cap over it. "No mirror, no reflection" = "no cap, no authority" — the system's existing rule. |
| **Stratification** (meta separated from base, layered on, removable) | A cap is *granted*, never *ambient*. The base level is handed no mirror-cap UP (§2); only a constructed meta-level receives one DOWN. Removable = the cap is *revocable* (`Bounds.revocation_immediate`, `lib.rs:315`): drop the mirror-cap and the meta-level loses reflective authority instantly at `n=1`. |
| **Ontological correspondence** | The mirror's `Target` *is* the reflected thing's id: `Target::Cell(cell)`/`DebugFrame(meta)` (§2.3). The presentation a mirror yields is the existing `Registry::present(target, viewer)` — a cell-shaped projection of a cell, a frame-shaped projection of a frame (`presentable.rs:881`). |

The novel content is the third column: Bracha–Ungar argue for these as *design
discipline a library author should follow*; here they are *unforgeable
consequences of the cap fabric* — a mirror you do not hold cannot be faked into
existence (`is_attenuation` refuses a widen, `lib.rs:297`), and dropping it
removes the meta-level by construction.

### 1.2 The mirror-cap shape

A mirror-cap is a firmament `Capability` whose target is a *reflective view* of a
subgraph and whose `rights` are *reflect rights* on the genuine `AuthRequired`
lattice. It introduces no new authority primitive — it reuses the
`(target, rights)` handle and the `granted ⊆ held` gate verbatim.

```
// New Target arm (the ONE structural addition — §6 task A):
Target::Mirror {
    over: FocusTarget,   // the subgraph this mirror reflects (Cell / DebugFrame / World / Cockpit)
    depth: MirrorDepth,  // Structure | ReadState | Live  — the reflective attenuation axis
}
```

A `MirrorCap = Capability{ target: Target::Mirror{over, depth}, rights }`. Three
observations make this *not* a parallel model:

1. **It attenuates through the existing `Capability::attenuate`** (`lib.rs:293`).
   A mirror narrows on TWO axes that both reduce to `is_attenuation`:
   - the `rights` axis (the `AuthRequired` lattice — e.g. `Either → Signature`),
     exactly as `surface.rs:321-328` already attenuates a *writable* surface cap
     into a *read-only* one (the test there literally calls the read-only result
     a "mirror");
   - the `depth` axis (`MirrorDepth`): `Live ⊒ ReadState ⊒ Structure`. A
     `ReadState` mirror reads cell state but cannot follow into the live
     dynamics stream; a `Structure` mirror sees only shape (cell ids, cap edges,
     lifecycle) with state redacted. Narrowing `depth` is a `granted ⊆ held`
     check on the `MirrorDepth` lattice — the *same* monotone order, a second
     coordinate of the rights lattice (`AuthRequired × MirrorDepth`), so no new
     gate is written.

2. **A read-only mirror = a `Signature`-narrowed cap over the subgraph.** The
   inspector's cell-access today is "read the live ledger fresh"
   (`presentable.rs:863-888`); a mirror-cap *gates* that read. `ReflectedCell` /
   `Registry::present` become "present the subgraph the mirror authorizes, at the
   mirror's depth, for the mirror's viewer." The viewer parameter already
   threaded through `PresentCtx::for_viewer` (`presentable.rs:882`) *is* the
   mirror-holder's identity — cap-confined reflection falls out of the existing
   viewer-parametrized projection.

3. **It relates to `SurfaceCapability` as a sibling, not a subtype.** A
   `SurfaceCapability` (`surface.rs:84-90`) authorizes *driving a window*
   (`target = Surface(cell)`, write the glass). A mirror-cap authorizes
   *inspecting a subgraph* (`target = Mirror{over}`, read the structure/state).
   Both are `Capability`s over the same fabric; a surface can be *both* driven
   (you hold its `SurfaceCapability`) and reflected (someone holds a mirror-cap
   over it) — two distinct authorities over one object, which is exactly the
   meta/base separation §2 needs.

### 1.3 Attenuation gives the three mirror flavors for free

Because attenuation is the genuine lattice meet, the useful mirrors are points on
the `(rights, depth)` lattice, each obtained by narrowing a held mirror:

- **a read-only mirror** — `rights = Signature` (or whatever the read-floor is),
  `depth = ReadState`: see the live state, cannot mutate, cannot reach into the
  dynamics tail. The debugger's default lens.
- **a structure-only mirror** — `depth = Structure`: see the cap graph / cell
  shape / lifecycle with state values redacted. The "show me the wiring without
  the secrets" mirror — handed to a less-trusted meta-level (a remote operator,
  §4).
- **a live mirror** — `depth = Live`: follow the dynamics `since(cursor)` stream
  (`dynamics.rs`) as the base evolves. The *only* depth that observes
  liveness; the most authority, granted sparingly.

A widen is refused identically at every depth (`is_attenuation` returns `None`,
`lib.rs:297`), so a `Structure` mirror cannot promote itself to `ReadState` — the
no-amplification rule, on the reflection axis.

---

## 2. THE CAP-STRATIFIED TOWER

### 2.1 The authority-downward mechanism

The reflective tower is firmament-stratified: **a meta-level holds a mirror-cap
OVER the level below; the base level holds NO cap UP.** Authority flows strictly
downward, and because it flows as *caps*, the flow is unforgeable and
attenuating:

```
level 2  (meta-meta)  ── holds MirrorCap over ──▶  level 1
level 1  (meta)       ── holds MirrorCap over ──▶  level 0
level 0  (base)       ── holds NOTHING upward; runs reflection-free
```

The invariant is the firmament's own `granted ⊆ held`: a level-`k+1` mirror over
level-`k` is *minted by attenuating* level-`k`'s own authority (you cannot reflect
over more than the target holds), so the tower never amplifies as it climbs. The
base holding no upward cap is *Bracha–Ungar stratification made structural*: base
computation literally has no handle that names the meta-level, so it cannot reach
up — not by convention, by absence-of-cap.

Every reflective act leaves a **receipt**. Reflection that *only reads* (a
`ReadState`/`Structure` mirror) reads the live ledger and produces a projection;
reflection that *acts* on the base (resume with a modified continuation, §3) is a
real turn through `commit_turn` (`world.rs:571`) and lands a receipt in the
provenance log. The witnessed-ness is not added on; it is the commit path the
whole system already runs through.

### 2.2 The `MetaStack` as the lazily-materialized tower (3-Lisp)

*(BUILT — `MetaLevelId`, `MetaDebugView` (with `capture()`), and `MetaStack` live in
`starbridge-v2/src/meta_debug.rs`; the `FocusTarget::{DebugFrame, World, Cockpit}` arms live in
`starbridge-v2/src/presentable.rs`. The sketch below matches the shipped shape.)*

A 3-Lisp reflective tower is conceptually infinite but **lazily materialized**:
levels exist only when reflection demands them, and the implementation grounds in
a finite non-reflective processor. dregg's tower is the same shape:

```
struct MetaStack {
    levels: Vec<MetaLevel>,   // levels[0] = the base; push to climb, pop to descend
}
struct MetaLevel {
    mirror: MirrorCap,          // the cap this level holds over level-1 (level 0 has none)
    view: MetaDebugView,        // the projection state (focus, scrub_cursor, sub-cockpit state)
}
```

- **Lazy materialization.** A `MetaLevel` is constructed only when the operator
  presses "suspend & inspect" (§3.4) — a `push`. No level is paid for until it
  exists. This replaces the cockpit's flat `Tab` sibling-panels with a push/pop
  stack (`REFLEXIVE-MIGRATION.md` §4.2): the tower is exactly as tall as you
  climbed.

- **Grounding at the native gpui loop.** The tower bottoms out at the
  non-reflective floor: the **native gpui render loop**, which holds no
  firmament cap at all — it is the host processor, outside the cell fabric
  (`REFLEXIVE-MIGRATION.md` §3.1 marks `world`, `FocusHandle`, the live sockets
  as engine-local, never cells). This is the 3-Lisp ground: the bottom turtle is
  not another mirror, it is the bare metal that runs the image. The recursion
  terminates *because the floor is not a cap-holder*.

### 2.3 "Debug the debugger" = the one-arm `FocusTarget` extension

The keystone, already scoped in `REFLEXIVE-MIGRATION.md` §4.2: make a meta-level
*itself a `FocusTarget`*. Today `FocusTarget` has exactly one arm
(`presentable.rs:849-852`) with the doc noting "new object kinds add one arm." Add:

```
pub enum FocusTarget {
    Cell(CellId),               // unchanged
    DebugFrame(MetaLevelId),    // a meta-level's MetaDebugView   ← new
    World,                      // the whole live World as an object ← new
    Cockpit,                    // the running cockpit as an object  ← new
}
```

plus `MetaDebugView impl Presentable`, dispatched in the one `match` in
`Registry::present` (`presentable.rs:883-887`). Then **"debug the debugger" is
literally focusing the inspector on its own `MetaDebugView`** — recursion through
the *same* `present()` dispatch, no new mechanism. Holding a mirror-cap over a
`DebugFrame(k)` is reflecting over meta-level `k`; the projection it yields is
meta-level `k`'s view, presented for the mirror-holder.

This is mechanism only. The *dataflow* question — when the cockpit's own state is
cells (`REFLEXIVE-MIGRATION.md` §3) and the projector projects cells including
its own view state, how the self-invalidation cycle resolves — is the deferred
fixpoint piece (§5 here; §2.3.5/§5.2 there). The cap-stratified tower is
well-defined *regardless* of that resolution: the authority structure (who holds
a mirror over whom, who lands receipts) is independent of how the projection
*recomputes*.

---

## 3. THE SUSPEND PRIMITIVE

*(BUILT — the gate, queue, `CommitOutcome::Queued`, `ResumeMode`, and `suspend`/`resume`/`resume_drain`
live in `starbridge-v2/src/world.rs`. The design below is the rationale; the code blocks show the shape
that shipped, `Modified(Vec<Turn>)` in place of the sketch's `ConditionalBatch`.)*

### 3.1 Suspend ≠ Snapshot

`REFLEXIVE-MIGRATION.md` §4 designs **Snapshot**: capture a `WitnessCursor` at
the head and present the *frozen past* via root-verified `History::replay_to`
(`replay.rs`). Snapshot *freezes a cursor*; **the live loop keeps running.** That
is the right primitive for "inspect a past world honestly," and it already has a
home.

**Suspend is the missing sibling §4.5.3 / §7-Q1 flagged as an ember-decision:
halt the live loop.** The live `World` *stops accepting turns* while inspected,
and resumes where it left off. This is what 3-Lisp/Pharo *can* do (you can stop
the image) and what Snapshot deliberately does *not* do. The two are
complementary axes:

| | freezes | the live loop | resume |
|---|---|---|---|
| **Snapshot** | a *cursor* (a past height) | keeps running | (nothing to resume — it never stopped) |
| **Suspend** | the *head* (turn-application) | **halted** | drain the queue, or apply a modified continuation |

### 3.2 The turn-application gate + the pending-turn queue

Suspend interposes on the single commit seam. `World::commit_turn`
(`world.rs:571`) is *the* place every real state transition passes through. The
gate is a flag the seam consults *before* it runs the executor:

```
struct World {
    // ... existing fields ...
    suspended: bool,
    pending: VecDeque<Turn>,   // turns staged while halted, in arrival order
}

fn commit_turn(&mut self, turn: Turn) -> CommitOutcome {
    if self.suspended {
        self.pending.push_back(turn);
        self.dynamics.emit(WorldEvent::TurnQueued { agent: turn.agent });
        return CommitOutcome::Queued;   // a new, honest outcome arm
    }
    // ... the existing path (executor, receipt, height++, dynamics) unchanged ...
}
```

Suspending is `self.suspended = true`; the executor is untouched, the ledger is
untouched, and every turn that *would* have committed instead lands in `pending`
in arrival order. The head is frozen at the exact height suspension hit — not a
replayed past (that is Snapshot), but *the live head, paused*. Inspection during
suspension uses the ordinary mirror machinery (§1) over the frozen-but-live
World: a `ReadState` mirror over `FocusTarget::World` shows the operator exactly
the state the loop is paused at.

### 3.3 The continuation reified as a partial turn

What is "the continuation" of a suspended live loop? It is *the pending work*:
the queued turns plus their dependency structure. This is exactly a **partial
turn** in dregg's existing, proven sense
(`metatheory/Dregg2/Exec/ConditionalTurn.lean`,
`project-partial-turn-promises.md`):

- A `ConditionalBatch{ nodes, edges }` (`ConditionalTurn.lean:82`) is a set of
  turns (`nodes`) plus `EventualRef` dependency edges (`edges`), executed in
  Kahn-topological order, all-or-nothing (`execConditionalTurn`,
  `ConditionalTurn.lean:190`).
- `abbrev Slots := Nat → Bool` (`:101`) is the output-slot environment:
  `Slots p = true` iff node `p` has committed, so an open `EventualRef` to slot
  `p` is *a hole* — a promise awaiting resolution.

The reification is direct:

```
SuspendedContinuation = ConditionalBatch {
    nodes: pending.into_turns(),     // the queued turns
    edges: <inferred EventualRef deps among them>,
}
```

A suspended live loop's continuation **is a `ConditionalBatch` whose `Slots` are
not yet filled** — the open `EventualRef` edges are the holes/promises; resolution
= a slot-fill = a node committing (`runOrder_fills`, `ConditionalTurn.lean:435`).
This grounds the continuation in code that already exists and is proven (the run
order respects every dependency edge; the all-or-nothing topo execution is the
`Option`-bind chain).

The honest scope (per `project-partial-turn-promises.md`'s
SYSTEM-READ VERDICT): **determination is eager, witness is lazy.** A queued
turn's *shape* (its actions, its δ, its authority demand) is fixed the moment it
enters `pending`; only its *commit* is deferred until resume. The continuation is
a lazy witness over an eager shape — precisely the safe case. We do NOT introduce
a δ-open hole (a contribution whose conservation/authority shape is filled later);
that is the inexpressible/dangerous case the verdict isolates, and Suspend does
not need it. A modified continuation (§3.4) edits the *batch* before resume, but
each turn in it is still a fully-shaped turn re-imposed through `commit_turn`'s
own invariant at fill time — the `holeFill_binds_in_circuit` guardrail, here as
"every drained turn binds its δ + authority through the normal executor gate."

### 3.4 Inspect-frozen-head → resume(drain | modified-continuation)

The flow:

1. **Suspend.** `world.suspended = true`; the head freezes; new turns queue.
2. **Inspect.** Push a `MetaLevel` holding a `ReadState` mirror over
   `FocusTarget::World` (the frozen-but-live head) and over each
   `pending` turn (the continuation as inspectable partial turn). The operator
   walks the queued continuation, sees the state it is paused at, runs the
   existing per-turn debugger / refusal-explanation machinery (`debug.rs`) over
   the *next* queued turn without committing it.
3. **Resume**, two modes:
   - **`resume(drain)`** — `world.suspended = false`; drain `pending` through
     `commit_turn` in Kahn-topological order (the `execConditionalTurn` order),
     all-or-nothing per the batch semantics. The live loop continues as if it had
     never paused, with the queued turns applied in their honest dependency
     order.
   - **`resume(modified_continuation)`** — replace the `SuspendedContinuation`'s
     batch with an edited one (drop a queued turn, insert a fix-up turn, reorder
     within dependency constraints) and *then* drain. Each turn in the modified
     batch still passes through the full `commit_turn` gate, so a modified
     continuation cannot smuggle in unauthorized or non-conserving work — the
     edit is to *which* turns run, never to the per-turn invariant.

This is the Pharo "halt → inspect the stack → proceed / proceed-with-a-changed-
value" loop, but the "stack" is a *witnessed partial turn* and "proceed" is a
*cap-gated, conservation-checked drain*.

### 3.5 The fractal recursion + the gpui-loop base case

Suspend is itself reflective and nests via §2. The "suspend the suspender" button
inside a `MetaDebugView` suspends *that meta-level's* own turn-application (its
sub-cockpit edits are themselves turns once UI-as-cells lands,
`REFLEXIVE-MIGRATION.md` §3.5) and pushes another `MetaLevel`. Termination is the
same 3-Lisp ground as §2.2: the recursion bottoms out at the **native gpui loop**,
which is not a `World`, has no `commit_turn`, and therefore cannot be suspended —
it is the floor that keeps the whole tower drawable while every cell-level loop
above it is halted. You can freeze every reflective level; you cannot freeze the
turtle the image runs on.

---

## 4. REMOTE-DEBUG-ACROSS-`n`

### 4.1 A meta-level on a different node

The firmament's distance parameter `n` (`lib.rs:307-348`) makes the tower
**distributable**: a meta-level need not sit on the same machine as the base it
reflects. A mirror-cap is a `Capability`; the router resolves it local
(`n=1`, kernel/executor path) or distributed (`n>1`, the executor→net path) with
the *same verbs* (`lib.rs:26-43`). So:

> A meta-level on a different node = a **mirror-cap dialed over the netlayer**.

Reflecting over a remote sovereign image is holding a `Target::Mirror{ over }`
whose `over` resolves to a `Target::Distributed{cell}` on another federation
member. The remote operator inspects the remote image through the genuine
`granted ⊆ held` gate — they see exactly the depth their mirror-cap authorizes
(`Structure` for an audit, `ReadState` for a debug session, `Live` to watch it
run), and *nothing more*. The redaction is not a remote-API policy; it is the
mirror's attenuation, enforced at the cap fabric.

### 4.2 Suspend / continuation as a firmament cap across distance

Suspend over distance is the same handle. The authority to halt a remote image's
loop is a *cap* (a write-class mirror, or a dedicated suspend-right on the
`World`'s control cell); resuming with a modified continuation is a **turn over
the net** — the `SuspendedContinuation` (`ConditionalBatch`) is content-addressed
data (`project-partial-turn-promises.md`: it "already lives" in
`RecChainedState`), so a remote operator can be *handed the partial turn*, edit
it, and submit the drain as a delegated, attenuated turn. The continuation is
itself a portable firmament object.

### 4.3 What `Bounds` relax

The `Bounds` carried on every resolution (`lib.rs:307-322`) state honestly what
held:

| at `n=1` (one box) | at `n>1` (over the netlayer) |
|---|---|
| `revocation_immediate = true` — drop the mirror-cap and the remote meta-level loses reflective authority *the instant the syscall returns* | `revocation_immediate = false` — the epoch lift must propagate; the remote mirror dies *eventually* |
| `commit_synchronous = true` — a `resume(modified_continuation)` drain is final the moment it returns | `commit_synchronous = false` — the drain is quorum-gated; the remote image's continuation commits when the federation agrees |
| Suspend halts a *local* loop; the frozen head is *consistent* | Suspend halts a remote loop; the freeze is the remote `World`'s head, observed across a (relaxing) consistency bound |

Crucially the **verbs do not change** — `n=1` and `n=5` differ only in these
relaxed bounds, never in "hold a mirror, inspect, suspend, resume" (`lib.rs:42-43`,
the `n_equals_one_collapse` test `:423-436`). Remote reflection is the same act,
honestly weaker.

### 4.4 What 3-Lisp / Pharo could not do

3-Lisp gave you the reflective tower; Pharo gave you the live, suspendable,
self-hosting image. **Neither gave you reflection that is unforgeable, witnessed,
AND distributable.** In a Smalltalk image, anything in the image can reach the
meta-level (no cap confines reflective authority); a debugger leaves no
tamper-evident receipt; and "debug a remote image" means opening a privileged
remote-eval channel, not dialing an *attenuated* mirror over a distance with the
redaction enforced cryptographically. The `n`-distributable mirror-cap is the new
thing.

---

## 5. THE NOVEL CLAIM — STATED CAREFULLY

**Cap-secure self-hosting:** a reflective tower that is

- **unforgeable** — there is no cap to fake your way up the tower. Reflective
  authority is a `Capability` over a `Target::Mirror`; with no ambient authority
  and the `granted ⊆ held` gate refusing every widen (`lib.rs:297`), a level
  cannot reflect over more than it was granted, and the base — holding no upward
  cap — cannot reach the meta-level at all. Stratification is *structural*
  (absence-of-cap), not conventional.
- **witnessed** — every reflective *act* leaves a receipt. Read-reflection
  produces a projection over the live ledger; act-reflection (resume with a
  modified continuation) is a real turn through `commit_turn` and lands in the
  provenance log. The debugger cannot tamper silently.
- **distributable** — the firmament `n` makes a meta-level a remote node's
  attenuated mirror over the base, with `Bounds` relaxing honestly and the verbs
  unchanged.

### Why this is more than a Smalltalk port

A Pharo image is self-hosting and live, but its reflection is *ambient,
unwitnessed, and local*: any object can mutate any other through the meta-level,
nothing records that it happened, and the image is one machine. dregg's tower
takes the *same* liveness and self-hosting and subjects reflection to the ocap
fabric it already enforces on value and on glass (`compositor.rs` T1/T2/T3, the
no-amplification teeth) — so reflection becomes *another resource governed by
caps*, with the same unforgeability, the same receipts, and the same
`n`-distance. The mirror you cannot forge, the receipt you cannot suppress, and
the distance you can dial are the three things the port does not have.

### Honest: mechanism (here) vs. deferred dataflow-fixpoint (the explorer)

Everything above is the **authority-structure mechanism**: the cap kind, the
stratified tower's downward flow, the Suspend gate, the partial-turn
continuation, the `n`-dialing. It is well-defined independent of *how the
projection recomputes*.

The **one deferred piece** is the dataflow self-cycle resolution: once the
cockpit's own view state is cells (`REFLEXIVE-MIGRATION.md` §3), the projector
projects cells that *include its own view state*, and the self-invalidation cycle
needs a stratification — **unit-delay** (the projection sees the previous frame's
own state, breaking the cycle by a tick) **vs. exact** (a true fixpoint of
"project including self"). That choice is the stratified-fixpoint dataflow
explorer's, not this document's. The cap-stratified tower does NOT presuppose its
answer: who-holds-a-mirror-over-whom and who-lands-receipts is fixed regardless of
whether the projection settles by unit-delay or by exact fixpoint. The seam
between the two is named in §6.

---

## 6. THE SEAMS + THE ORDERED DESIGN TASKS

### Seams

1. **The dataflow self-cycle (deferred, owned by the fixpoint explorer).** When a
   mirror reflects a `Cockpit`/`World` whose state includes the mirror's own view
   cells, the projection's self-reference must be stratified (unit-delay vs.
   exact). This document's mechanism is correct under *either*; the seam is the
   handoff, not a defect here. (`REFLEXIVE-MIGRATION.md` §2.3.5, §5.2.)
2. **`MirrorDepth` as a second rights coordinate.** The rights lattice becomes
   `AuthRequired × MirrorDepth`. The `is_attenuation` check must be the product
   order (narrow on *either* coordinate is a narrowing). This is a real extension
   to the rights type, but it reuses the meet — not a new gate.
3. **Suspend's `Queued` outcome must be honest in the dynamics stream.** Cache /
   liveness soundness depends on every queued turn emitting a `WorldEvent`
   (`TurnQueued`) and every drain emitting the normal commit events
   (`REFLEXIVE-MIGRATION.md` §2.3.2: "cache soundness = dynamics completeness").
   A silently-queued turn is a stale-projection bug.
4. **Suspend liveness honesty.** A meta-view over a *suspended* head must stamp
   its `Liveness` as paused-live, distinct from Snapshot's
   `ReplayedDeterministic` (`ui_snapshot.rs` trichotomy) — the operator must
   always know whether they look at a *paused live* head or a *frozen past*.
5. **Continuation editing stays shape-eager.** `resume(modified_continuation)`
   may edit *which* turns drain, never weaken a turn's δ/authority shape; each
   drained turn re-passes the full `commit_turn` gate (the
   `holeFill_binds_in_circuit` discipline, §3.3).
6. **Remote suspend authority is an ember-decision on the cap kind.** Whether
   "halt a remote loop" is a write-class mirror right or a dedicated control-cell
   cap (§4.2) is a policy choice; both ride the same fabric.

### Ordered design tasks

- **Task A — the new cap kind (mirror-cap). [OPEN — the single genuine seam.]** Add `Target::Mirror{ over, depth }`
  and `MirrorDepth{Structure ⊑ ReadState ⊑ Live}` to `dregg-firmament`; extend
  the rights lattice to `AuthRequired × MirrorDepth` so `Capability::attenuate`
  narrows on both axes through the *existing* `is_attenuation` meet. *Verify:* a
  `Live` mirror attenuates to `ReadState`/`Structure`; a `Structure` mirror
  refuses to widen — the `surface.rs:321-328` read-only-mirror test generalized.
- **Task B — the Suspend gate. [DONE — `starbridge-v2/src/world.rs`.]** `World{ suspended, pending }`, the
  `commit_turn` pre-check, the `CommitOutcome::Queued` arm, the `TurnQueued`
  event, and `suspend()` / `resume(ResumeMode)` with `ResumeMode::{Drain,
  Modified(..)}` draining the pending queue in arrival order — all landed
  (`suspend`, `resume`, `resume_drain`, `is_suspended`). *Verified:* turns staged while suspended queue and do not commit; `resume(drain)`
  applies them in order; `resume(modified)` edits the batch but each
  turn still passes the executor gate.
- **Task C — the `FocusTarget` arm + `MetaDebugView`. [DONE — `presentable.rs` + `meta_debug.rs`.]**
  `FocusTarget::{DebugFrame(MetaLevelId), World, Cockpit}` (`starbridge-v2/src/presentable.rs`),
  `MetaLevelId`/`MetaDebugView` (with `capture()`) and the `MetaStack` push/pop
  (`starbridge-v2/src/meta_debug.rs`) are all built. *Verified:* "debug the debugger" focuses the inspector on its own
  `MetaDebugView` recursively; the tower grounds at the native gpui loop (no
  infinite materialization). The one thing Task C still awaits is Task A: each level's
  reflective authority becomes a real *mirror-cap* only once `Target::Mirror` exists — today the
  tower's authority rides the existing surface/read caps.

Sequencing (as-built): B landed on the `World` commit seam; C landed on the `FocusTarget`/`present()`
dispatch and reuses B's suspend to drive its button. **A (mirror-cap) is the remaining substrate work** —
until it lands, the tower is stratified by construction but not yet cap-*confined* on the reflection axis.
The deferred dataflow-fixpoint (Seam 1) sequences *after* A, in the fixpoint explorer.

---

*( ◕‿◕ ) a closing couplet, since the mirror is just a cap turned inward:*
*the tower climbs on caps it cannot forge —*
*each level a mirror, witnessed, dialable across the gorge.*
