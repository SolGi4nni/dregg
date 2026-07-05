# THE REAL STRATIFIED FIXPOINT
## How a reflexive projector that projects its own view-state has a well-defined answer — and whether the firmament hands us the strata for free

*A teacher's explainer for the self-hosting starbridge image. Intuition first, formalism second, our problem third.*

---

## 0. WHY THIS DOCUMENT EXISTS

`REFLEXIVE-MIGRATION.md` §2.3.5, §4.5.2, §7.3 (now archived to
`.docs-history-noclaude/deos/REFLEXIVE-MIGRATION.md`; its live successors are
`docs/deos/FIRMAMENT-REFLEXIVE-SUBSTRATE.md` and
`docs/deos/REFLEXIVE-DISTRIBUTED-IMAGE.md`) names the deepest open
question of the self-hosting desktop: *when the projector projects cells that
include its own UI view-state, how do we break the self-invalidation cycle?* We
have tentatively picked a **unit-delay** (read the previous frame's self-view;
break the cycle with one frame of latency). This document is about the
**alternative** — the *real stratified fixpoint* — so we can choose the unit
delay (or not) **deliberately**, understanding exactly what we are trading away.

The thesis we will build to, and then test rigorously, is a beautiful one:

> dregg's **capability stratification** (authority flows strictly downward; a
> meta-level holds a mirror-cap *over* the level below; the base holds no cap
> *up*; `granted ⊆ held`) may be *exactly* the dataflow condition that makes the
> reflexive projector's fixpoint **well-founded by its own authority structure**.
> Cap-secure self-hosting → a reflective tower that is fixpoint-stratified for free.

We will find this is *almost* true, and the place it isn't is precisely the
place that decides the verdict.

---

## 1. THE PROBLEM, PRECISELY AND INTUITIVELY

### 1.1 The projector is a pure dataflow node

Strip away gpui and the cockpit's fifty fields. The semantic core
(`presentable.rs`, `Registry::present`) is one **pure function**
(all `presentable.rs:NNN` line numbers below are indicative — the file has been
re-edited since; the *symbols* are the durable anchors):

```
present : (state, focus, viewer) → Vec<Presentation>
```

It reads the live `World` and yields renderable data. It is pure: same inputs,
same output, no hidden mutation (the doc is emphatic — "reads the live world
fresh every call, never a cache"). In dataflow terms it is a single **combinational
node**: outputs are a function of inputs, no internal clock.

A whole UI is a graph of such nodes. The domain ledger flows in; presentations
flow out; the renderer paints them. As long as the arrows only ever point
*forward* — ledger → projection → pixels — the graph is a **DAG** and there is
nothing to discuss. You topologically sort it, evaluate once, done. Every UI
framework you have ever used lives here. This is the **acyclic** regime.

### 1.2 Self-hosting bends an arrow backward

The REFLEXIVE-MIGRATION plan (§3) promotes UI view-state *into dregg cells*:
`WorkspaceCell`, `ViewCell`, `PanelCell`. The focus, the active tab, the open
inspector, the lens index — all become **cells in the same ledger the projector
reads**. And the projector projects *all* cells, including these.

That is the bent arrow. Concretely:

- A `ViewCell` holds `{focus, present_idx, viewer_rights}` (§3.3). It *is* a cell.
- `present` projects cells. So `present` projects the `ViewCell`.
- But the *output* of `present` — which presentation is shown, what is focused —
  is *determined by* the `ViewCell`. The projector reads the very cell whose
  value its own output defines.

The output feeds back as input. The combinational node now has a wire from its
own output to its own input. **The DAG has a cycle.**

This is not a contrived edge case; it is the *point* of the self-hosting
desktop. The inspector inspects the inspector. The meta-debugger (§4) is a
`FocusTarget::DebugFrame` whose `present` shows the live loop — *including the
meta-debugger's own state*. The reflective tower is built from this one bent
arrow, applied recursively.

### 1.3 The concrete cycle — a `ViewCell` that presents `ViewCell`s

Make it painfully concrete. Suppose `present` gains a presentation kind,
"Open Views", which lists every `ViewCell` in the image — what is currently
focused, in each pane. (This is exactly the "Spotter over every live object's
every presentation," `presentable.rs:923`, turned on the UI's own cells.)

Now focus the inspector on a `ViewCell` `V` and open its "Open Views"
presentation. To compute `present(state, focus=V)`:

1. We need the "Open Views" list — every `ViewCell` and its current focus.
2. `V` is itself a `ViewCell`, and *its* current focus is... `V` (we are
   inspecting `V` while focused on `V`).
3. So computing `V`'s presentation requires knowing `V`'s presentation, which
   requires knowing `V`'s presentation, which...

```
        ┌──────────────────────────────────────────┐
        │                                           │
        ▼                                           │
   ViewCell V  ──present──►  "Open Views" body  ────┘
   {focus: V}               (lists V's own focus,
                             which IS this body)
```

### 1.4 The naive failure: infinite regress / invalidation storm

Implemented naively against the §2 incremental delta-fold, this is a
**self-invalidation storm**:

1. `V` changes → emit a `WorldEvent` naming `V` → invalidate `V`'s cached
   projection.
2. Recompute `V`'s projection. Because it *displays* `V`'s state, computing it
   writes/touches `V`'s presented value → emits a `WorldEvent` naming `V` →
   invalidate `V`'s cached projection.
3. Go to 2. Forever.

The frame never settles. Equivalently, in the pure view: `present` has no fixed
input to evaluate at, because its input is defined by its output, which is
defined by its input. There is no "the answer" to compute — *unless we can show
the feedback loop has a unique, reachable resting state*. That resting state, if
it exists, is a **fixpoint**: a value `x` with `present(x) = x` (modulo the
projection). The rest of this document is about *when such a fixpoint exists, is
unique, and is computable*, and how to get there.

---

## 2. FIXPOINT THEORY FROM THE GROUND UP

The mathematics that turns "the cycle has no answer" into "the cycle has *exactly
one* answer, and here is how to compute it" is the theory of **least fixpoints of
monotone operators on complete lattices** — Knaster–Tarski (existence) and
Kleene (computation). Built from intuition:

### 2.1 A lattice is "ordered by how much is known"

Forget the order-theory textbook picture. The order we care about is the
**information order**: `a ⊑ b` means "`b` knows everything `a` knows, and maybe
more." The bottom element `⊥` is "nothing is known yet" (the empty answer). The
join `a ⊔ b` is "everything `a` or `b` knows" (combine two partial answers).

For the projector, an element of the lattice is a **candidate frame**: an
assignment of a (partial) presentation to each cell. `⊥` = "no presentation
computed for anything yet." A bigger element = "more presentations filled in,
none retracted." A **complete lattice** just means every set of candidate frames
has a least upper bound — you can always combine partial answers into one
combined partial answer. (Sets of facts ordered by `⊆` are the canonical
example, and that is *literally* what a Datalog model is — see §3. dregg's
biscuit/Pred heritage is a real predicate algebra; we are squarely in-family.)

### 2.2 Monotone = "more input never retracts output"

An operator `F : L → L` is **monotone** iff `a ⊑ b ⟹ F(a) ⊑ F(b)`. In words:
*if you give the projector more information, it produces more presentations,
never fewer.* It never *un-says* something it said with less input.

This is the single most important property in the whole document. Hold onto the
intuition: **monotone = no retraction = no negation.** A rule like "show the
balance" is monotone — give it more cells, it shows more balances. A rule like
"show the cells that are NOT present" is *anti*-monotone — give it more cells and
the "not present" set *shrinks*. That asymmetry is the entire plot of §3.

### 2.3 Knaster–Tarski: a monotone operator always has a least fixpoint

**Theorem (Knaster 1928 / Tarski 1955).** Every monotone operator `F` on a
complete lattice has a least fixpoint, and it equals the meet of all its
*pre-fixpoints*:

```
   lfp(F) = ⊓ { x : F(x) ⊑ x }
```

Why believe it without the proof? Because monotonicity makes the operator
**unable to overshoot**. Start below a pre-fixpoint and apply `F`: you stay below
it (monotonicity carries the order through). So the set of points `F` can't
escape downward-past has a greatest lower bound, and that bound is forced to be
a fixpoint. The cycle, *if monotone*, has a well-defined answer — the smallest
self-consistent frame — **with no delay, no clock, no z⁻¹**. The feedback resolves
itself into a unique least solution. This is the prize the unit-delay is giving up.

### 2.4 Kleene: and you compute it by iterating from ⊥

Existence is nice; we need to *run* it. **Kleene's fixpoint theorem** says: if
`F` is not just monotone but **(Scott-)continuous** (it commutes with the joins
of increasing chains — true for everything finitary, which a finite ledger
certainly is), then

```
   lfp(F) = ⊔ₙ Fⁿ(⊥)  =  ⊥ ⊑ F(⊥) ⊑ F(F(⊥)) ⊑ …
```

You **iterate the frame to its stable state.** Start with `⊥` (no presentations).
Apply `F` (project once: now domain cells have presentations, but anything that
read a not-yet-computed presentation read `⊥`). Apply `F` again (now those
second-order presentations fill in). Keep going. Because each step only *adds*
(monotonicity) and the lattice is finite (a finite ledger), the chain **rises and
must halt** — at the least fixpoint. Concretely:

```
   frame₀ = ⊥                       (nothing projected)
   frame₁ = present(frame₀)         (domain cells projected; UI cells see ⊥-ish)
   frame₂ = present(frame₁)         (UI cells now see frame₁'s projections)
   …
   frameₖ = present(frameₖ₋₁) = frameₖ₋₁   ← FIXPOINT. stop. paint frameₖ.
```

This is the whole answer to §1.4's storm, **for the monotone case**: the storm
is real, but it is a *terminating, convergent* iteration, not an infinite regress.
You iterate the frame within a single tick until it stops changing, then paint.
The "infinite re-invalidation" was an artifact of treating each pass as a new
external event instead of as one step of an internal fixpoint iteration.

**This is the crux of "no delay needed."** A monotone dataflow cycle does not
need a unit delay. It needs an *iterate-to-convergence* inside the frame. The
unit-delay (z⁻¹) is what you reach for when you *can't* prove convergence — you
break the cycle by fiat with one frame of staleness. The fixpoint is what you
reach for when you *can* prove it — you pay per-frame iteration and get an exact,
non-stale answer.

---

## 3. WHEN MONOTONICITY BREAKS → WHY YOU NEED STRATIFICATION

Everything in §2 rests on one word: **monotone**. The moment the projector can
say "NOT", the clean least fixpoint can evaporate.

### 3.1 The non-monotone faces of `present`

Look hard at what a real inspector shows. Several presentations are *negations*
or *differences*:

- **Affordances** (`presentable.rs:667`) shows, per message, *"you may send"* vs
  *"refused: insufficient authority"* (`messages_as_inspectable`,
  `presentable.rs:746`). "The affordances I do **NOT** hold" is a negation over
  the cap graph.
- A **refusal explanation** (`debug.rs`, the `RefusalExplanation` of §4.1) is
  inherently "this turn would **fail** because precondition P is **absent**."
- A **diff** view (the replay diff, §2 / §4) shows "what is in frame B and **NOT**
  in frame A."
- A "**missing**/dangling focus" readout (`Registry::present → None`,
  `presentable.rs:1166` "surfaces a dangling focus honestly") is "this cell is
  **not** in the ledger."

Each of these reads *the absence of a fact*. Absence is anti-monotone: add a
cell, an "absent" set shrinks; grant a cap, a "you may NOT" badge flips off. Such
a rule is **not** monotone, and Knaster–Tarski no longer applies as stated.

### 3.2 What negation breaks: the unique-least-model fails

The classic one-line demonstration (the reason Datalog forbids unstratified
negation). Consider the rule

```
   p  :−  not p.
```

"`p` holds if `p` does not hold." There is **no** model: if `p` is true the body
is false so `p` shouldn't be derived; if `p` is false the body is true so `p`
should be derived. No fixpoint exists, least or otherwise. That is `p :− not p`
— and it is *exactly* §1.3's `ViewCell` that displays "the views NOT focused on
me" while being focused on itself. **The bent arrow plus negation = no answer at
all**, not merely a slow one.

A subtler case — `p :− not q. q :− not p.` — has *two* minimal models (`{p}` and
`{q}`) and no way to prefer one. The "least fixpoint" is undefined because there
is no least model. So with negation we lose both *existence* (the `p:−not p`
storm) and *uniqueness* (the `p/q` ambiguity). We need a principled way to say
which model is *the* answer.

### 3.3 The fix: stratification (Apt–Blair–Walker 1988)

The insight is structural, not computational. The pathology in §3.2 needs a
**negative cycle**: `p` depends, transitively, *negatively* on itself. Forbid
that one thing and the trouble vanishes.

**Stratified negation.** Build the dependency graph of relations, label each edge
*positive* (depends on the presence of) or *negative* (depends on the absence
of). A program is **stratified** iff no relation depends *negatively* on itself —
i.e., **no cycle in the dependency graph contains a negative edge.** Equivalently:
you can partition the relations into ordered **strata** `S₀ ⊏ S₁ ⊏ … ⊏ Sₖ` such
that

- a *positive* dependency may stay within a stratum or reach down (`Sᵢ` reads `Sⱼ`, `j ≤ i`),
- a *negative* dependency must reach **strictly down** (`Sᵢ` negates only `Sⱼ`, `j < i`).

Then you compute **stratum by stratum, bottom up.** Within each stratum there is
no negation that touches that stratum (all its negations point at *lower,
already-finished* strata), so the stratum is **monotone over the fixed values of
the strata below** — and §2's least fixpoint applies *locally*. You compute `S₀`
to its monotone fixpoint; freeze it; now every negation in `S₁` reads a *constant*
(the frozen `S₀`), so `S₁` is monotone too; compute it; freeze; and so on. The
global "model" is well-defined and computable because **each layer's negation
only ever looks at a layer that is already done.**

This is the cleanest possible deal: negation is fine *as long as it points
downward in a tower*. Hold that sentence — it is §6's whole hypothesis.

### 3.4 When you can't even stratify: well-founded & stable models

Stratification is a *syntactic* sufficient condition. Some programs have a
sensible answer but *aren't* syntactically stratifiable (the negative dependency
is there but never actually "fires" for the data at hand). Two stronger semantics
cover those:

- **Well-founded semantics** (Van Gelder–Ross–Schlipf 1991). Assigns *every*
  program — even unstratifiable ones — a unique **three-valued** model: each fact
  is *true*, *false*, or **undefined**. `p :− not p` resolves to `p = undefined`
  (the honest verdict: "this self-reference has no determinate truth"). It is
  computed by an alternating fixpoint (least fixpoint of `F²`, the operator
  applied twice). The three-valued discipline is *exactly* dregg's fail-closed
  register: an undetermined affordance should render as **"unknown / refused"**,
  never as a guessed `true`. (Notably starbridge already has a *trichotomy* in
  hand — `Liveness::{Live, ReplayedDeterministic, ReconstructedApproximate}`,
  `ui_snapshot.rs:116`; "undefined" is the same shape of honesty.)
- **Stable models** (Gelfond–Lifschitz 1988). The answer-set semantics: a program
  may have *zero, one, or many* stable models (`p:−not q. q:−not p.` has the two
  `{p},{q}`). Powerful, but multiplicity is the wrong shape for a *deterministic
  UI frame* — we want exactly one answer per frame. So well-founded (unique,
  three-valued) is the better fit if we ever leave the stratified regime; stable
  models are the theory to *know* but not what we'd ship.

**The ladder of strength:** stratified ⊂ well-founded ⊂ stable. Stratified is the
sweet spot — it's *decidable from the program text*, it gives a unique two-valued
answer, and (the punchline) it is what an authority tower hands you. We aim to
*stay stratified* and keep well-founded in our pocket as the fail-closed fallback.

### 3.5 A tiny worked dregg example

Two strata, drawn from real `present` faces.

```
   Stratum 0  (monotone, no negation):
     focused(V, C)   :− viewcell_focus(V, C).          -- V's focus is cell C
     present_cell(C) :− ledger_has(C).                 -- C is a live cell

   Stratum 1  (negates ONLY stratum 0):
     dangling(V)     :− focused(V, C),  not present_cell(C).
                        -- V points at a cell NOT in the ledger  (the §1166 honesty)
     unfocused(V, C) :− present_cell(C), not focused(V, C).
                        -- C is live but V is not focused on it
```

`dangling` and `unfocused` both negate, but *only* relations in stratum 0. So:
compute `focused` and `present_cell` to their (trivial, monotone) fixpoint first;
**freeze** them; then `dangling`/`unfocused` are plain monotone reads against
those constants. No storm. The frame settles in two passes. The `p :− not p`
disaster is structurally *impossible* here because the negation never reaches back
up into stratum 1 — and that is the whole game.

---

## 4. HOW REAL SYSTEMS COMPUTE IT INCREMENTALLY

The theory says "iterate to a fixpoint." Production systems do this *and* keep it
cheap under change. Three concrete mechanisms, all directly applicable to §2's
delta-fold:

### 4.1 Differential Dataflow — `iterate` as a first-class loop

Differential dataflow (McSherry et al.; the timely-dataflow lineage) makes the
fixpoint loop a primitive operator, `iterate`. You write the *cyclic* rule
(transitive closure, graph reachability — exactly the §1 feedback) and the
runtime runs the Kleene iteration §2.4 for you, *incrementally*: when an input
changes, it doesn't recompute the fixpoint from `⊥`; it computes the **delta to
the fixpoint** and folds it through the loop, propagating only the changed tuples
to convergence. This is precisely §2's `dynamics().since(cursor)` dream extended
*through* a cycle: a cell changes → only the affected presentations re-iterate →
the loop re-converges on the delta, not the whole frame. The "iterate the frame
to its stable state" of §2.4 becomes "iterate the *delta* to *its* stable state."

### 4.2 Salsa / Adapton — demand-driven memo with explicit cycle handling

Incremental-computation frameworks (salsa, used in rust-analyzer; Adapton) build
a **dependency-tracked memo graph** — exactly the `(FocusTarget, viewer,
WitnessCursor) → Vec<Presentation>` memo §2.2(C) describes. The relevant detail
here: a *self-referential* query is a **cycle in the memo graph**, and these
frameworks have an explicit policy for it. Salsa, by default, **panics on an
unexpected cycle** and offers an opt-in **fixpoint-recovery** mode where you
supply an initial value (a `⊥`) and it iterates the cyclic query to a fixpoint —
the *engineering* embodiment of §2.4. The lesson for us: a memoizing projector
*will* hit the reflexive cycle, and the framework forces an explicit decision —
*panic (forbid the cycle), unit-delay (break it), or iterate (resolve it)*. There
is no "it just works"; the cycle is a design decision the tooling makes you name.

### 4.3 The hand-rolled version for a frame

For starbridge we don't need a dataflow engine; the ledger is small and the loop
is shallow. The honest hand-rolled shape, per frame, is:

```
   frame ← previous_frame            // warm start (NOT a unit-delay output —
                                     // just a good initial guess to converge fast)
   loop:
       next ← present_all(state, frame)   // one Kleene step over all foci
       if next == frame: break            // fixpoint reached this tick
       frame ← next
   paint(frame)
```

With stratification (§3.3) the loop is replaced by a *fixed* number of passes —
one per stratum — each itself a (usually one-shot) monotone evaluation. The
**termination argument** is the height of the lattice (finite ledger) for the
monotone case, and the **number of strata** (a small constant) for the stratified
case. Either way it is bounded; the only question is the constant, which §7 prices.

---

## 5. CONCRETELY FOR DREGG — IS `present` MONOTONE, OR DOES IT NEGATE?

Now the diagnosis our own code demands. **Is `Registry::present` monotone (clean
least fixpoint, §2, no strata needed) or does it carry negation (needs
stratification, §3)?** Read the five presentations `ReflectedCell::present`
actually emits (`presentable.rs:655–728`):

| Presentation | Body source | Monotone? |
|---|---|---|
| **RawFields** (`:658`) | `reflect_cell` — the cell's own fields | **Monotone.** Pure positive projection of one cell's state. More state → more fields. |
| **Provenance** (`:689`) | receipts authored by this cell | **Monotone.** A filter+map over an append-only log; receipts only accumulate. |
| **Graph** (`:705`) | ocap edges touching the cell | **Monotone.** Positive reads of the cap graph; edges add nodes/edges. |
| **DomainVisual** (`:719`) | the lifecycle state machine | **Monotone** in structure; `current` is a *read* of one field (a selection, not a negation). |
| **Affordances** (`:667`) | `InspectAct` — per message, *authorized?* | **NOT monotone.** Emits `"refused: insufficient authority"` (`:747`) — an explicit **NOT-authorized** verdict over the viewer's held caps. |

**Verdict on the projector itself.** Four of the five faces are **monotone** —
for a pure cell projection, the bent-arrow cycle would have a clean least
fixpoint with *no* stratification. The non-monotonicity is **localized to
Affordances** (and, in the meta-debugger, to refusal-explanations and diffs,
§3.1). So the precise statement is:

> The reflexive projector is monotone **except** where it shows *negative
> authority facts* (what you may NOT do, what is absent, what differs). Those —
> and *only* those — need stratification.

This is a *good* outcome, because (a) the non-monotone part is small and
identifiable, and (b) — the §6 hypothesis — the non-monotone part is *exactly the
authority projection*, and authority is *exactly* the thing the firmament already
stratifies. The negation in `present` is **authority negation**, and authority
has a tower. Hold that thought; §6 cashes it.

### 5.1 Stratified-fixpoint frame vs. unit-delay frame, side by side

What actually happens at frame `N`, the two ways:

- **Unit-delay (z⁻¹), the tentative pick.** UI cells' self-view reads frame
  `N−1`'s projection. The cycle is cut by construction: `present` at frame `N`
  treats the `ViewCell`-derived inputs as *last frame's values* — constants, not
  unknowns. Always terminates (it's a DAG once the back-edge is a delay).
  **Cost:** one `present` pass. **Price:** the inspector-of-the-inspector shows
  the state as of one frame ago; a self-referential readout lags reality by one
  tick. For most desktop interaction this is *invisible* (a frame is ~16ms and
  nothing reads its own meta-view at sub-frame latency).

- **Stratified fixpoint, the alternative.** Stratify the relations (§5.2);
  compute each stratum to convergence within frame `N`; the self-view reads the
  *current* frame's lower strata. **Cost:** one pass per stratum (a small
  constant — see §6/§7). **Price:** none in staleness — the frame is exactly
  self-consistent — but you owe a *termination/cost argument* and a *defined
  stratification*, and you must keep `present` stratified as it grows (a new
  non-monotone face must be slotted into the tower, not bolted on).

### 5.2 What the strata actually are in the reflexive projector

Concretely, the tower of `present` over a self-hosting image:

```
   S₀  domain cells           ── RawFields/Provenance/Graph/DomainVisual of
                                 ledger value cells. Pure positive. (monotone)
   S₁  authority facts         ── the ocap graph: who holds what cap.
                                 Positive reads of cap edges. (monotone)
   S₂  affordance negation     ── "viewer may NOT send msg M" : negates S₁
                                 (the absence of a sufficient cap). (stratified ↓ S₁)
   S₃  UI/view cells           ── ViewCell/WorkspaceCell/PanelCell projections;
                                 read S₀–S₂ to render the inspector. (monotone over below)
   S₄  meta-view               ── the meta-debugger's present of S₀–S₃, incl.
                                 refusal/diff faces : negates lower strata. (stratified ↓)
   S₅  meta-meta …             ── debug-the-debugger: present of S₄. (↓ again)
```

The reflective tower of §4 (the `MetaStack`) is *literally* a stack of strata:
each meta-level negates (refuses/diffs) only levels **below** it, and reads —
never writes — its inferiors. *If* that "below-only" discipline holds, the whole
tower is stratified and the fixpoint is well-founded. Whether it holds is not a
hope; it is a property of the *authority* structure, which is §6.

---

## 6. THE KEY HYPOTHESIS — DOES THE FIRMAMENT GIVE US THE STRATA FOR FREE?

### 6.1 Stating it precisely

The firmament's discipline (`surface.rs`, `dregg-firmament/src/lib.rs:285`):

- A capability is `(target, rights)` with `rights : AuthRequired` (`lib.rs:174`).
- **Attenuation only narrows:** `attenuate(narrower)` succeeds iff
  `is_attenuation(held, narrower)` = `granted ⊆ held` (`lib.rs:293–304`). You
  cannot widen. A derived cap is `⊑` its parent on the rights lattice.
- A meta-level's view *of* a sub-level is a **mirror cap** — an *attenuated*
  (read-only / narrowed) capability *over* the level below (`surface.rs:321`, the
  "writable window → read-only mirror" narrowing is the canonical example).
- The base level holds **no cap upward**: a surface's backing cell holds no
  capability over the inspector that mirrors it. Authority is minted by *grant*
  from above and *narrows* on the way down (`surface.rs:78`, "obtained only by
  being granted").

The hypothesis:

> **(H)** "Authority flows strictly downward, and there are no cap-cycles" is
> *exactly* the condition "no relation depends negatively on itself." Therefore
> the cap-tower's strata **are** the dataflow strata, and the reflexive
> projector's fixpoint is well-founded **by the firmament**, for free.

### 6.2 Why the two conditions are the same condition

The argument, carefully. The non-monotone (negating) faces of `present` are the
**authority faces** (§5): "you may NOT" = *the held caps do not include a
sufficient one*. So a *negative* dataflow dependency in `present` is, concretely,
**a cap check**: presentation `X` negatively depends on presentation `Y` iff
computing `X` asks "does the viewer **lack** authority `Y`?"

Now overlay the firmament. A cap check at level `L` reads the *grant structure
beneath it* — `is_attenuation` compares the held cap against a *narrower*
requirement, and the held cap was *granted from above and narrowed downward*. The
meta-level holds a **mirror cap over** its inferior; the inferior holds **no cap
over** the meta-level. So:

```
   negative dependency (a cap check)  ⟹  reads authority of a STRICTLY LOWER level
   (because "may I?" resolves against caps minted above & narrowed downward,
    and the level being checked holds no authority upward)
```

That is **precisely** the stratification condition of §3.3: *a negative edge must
point strictly down the tower.* The firmament's "authority flows downward, no
cycles" makes every authority-negation in `present` point down the cap-tower —
which is the syntactic stratification Apt–Blair–Walker require. **The cap-tower
strata = the dataflow strata.** Under (H), the §5.2 tower's "negates only below"
discipline is not assumed — it is *enforced by the attenuation gate*. The
fixpoint is well-founded *because* the system is cap-secure. That is the beautiful
unification: **a reflective tower that is cap-secure is fixpoint-stratified by its
own authority structure.**

This is the same shape as Smith's 3-Lisp reflective tower (Brian Cantwell Smith,
1982) made *honest by capabilities*: where 3-Lisp's tower is an infinite stack of
interpreters held up by a clever limit, dregg's tower is held up by a *finite
attenuation chain* — each level a strictly-narrower cap over the last, so the
tower has a **floor** (the un-attenuatable base) and a height bounded by the
attenuation depth. Wand & Friedman's "The Mystery of the Tower Revealed" (1986)
showed 3-Lisp's tower collapses to a finite, computable thing once you identify
what each level *actually needs* from the one below; the firmament gives the same
collapse *structurally* — a level needs only a (narrowed) cap downward, never an
upward one, so the tower is finite by construction. Bracha & Ungar's **mirrors**
(2004) is the same idea named: reflection should go through *capability-secured
mirror objects*, not ambient `this.getClass()` — and a mirror is exactly an
attenuated downward cap. dregg's reflexive inspector *is* a Bracha–Ungar mirror
system whose mirrors are firmament caps.

### 6.3 Where (H) holds — and where it might NOT

Rigour means finding the crack. (H) holds **whenever the cap-tower is a strict
partial order** — a DAG of strictly-narrowing grants. It can fail in exactly the
cases where that order degenerates:

**(a) Same-stratum mutual projection — the real crack.** Suppose two cells `A`
and `B` at the *same* level mutually project each other *with negation*: `A`'s
presentation shows "B may NOT …" and `B`'s shows "A may NOT …". If `A` and `B`
hold *symmetric* caps over each other (neither strictly below the other), the
negative dependency is a **cycle within one stratum** — exactly the
`p:−not q. q:−not p.` of §3.2, with *two* minimal models and no least one. The
firmament does **not** automatically forbid this: two cells *can* hold caps over
each other (peer surfaces, two inspectors each focused on the other). Attenuation
forbids *widening*, but it does **not** forbid two *incomparable* caps from
existing at the same level. **So (H) is not free in full generality — it is free
exactly when the cap-tower is a strict order, and peer-symmetric caps are the
exception.**

**(b) A meta-level that negates *upward*.** If a meta-debugger could refuse based
on the *absence* of a cap it would need from a level *above* it, that's an upward
negative edge — unstratified. The firmament makes this hard (you hold no cap up),
but a *poorly designed* meta-view that reads ambient/global state instead of its
downward mirror cap could reintroduce it. (This is precisely the Bracha–Ungar
warning: reflection that reaches for ambient authority breaks the mirror
discipline.) Staying within mirror caps keeps (H); reaching for ambient state
breaks it.

**(c) Cap *grants* as part of the projected state.** If projecting a frame can
*itself grant a cap* (it shouldn't — `present` is pure, `presentable.rs` is read-only),
the dependency graph would gain edges *at evaluation time*, and stratification —
a *static* property of the program — couldn't be checked ahead of time. The
purity of `present` (no mutation, §2.1) is what keeps the dependency graph static
and (H) checkable. **Purity of the projector is a load-bearing precondition of (H).**

### 6.4 The verdict on (H)

(H) is **true for the tower, with one named carve-out.** The firmament *does* give
us the dataflow strata for free **along the meta-level axis** — the recursive
`MetaStack` of §4 is stratified by attenuation, because each meta-level's
negations (refusals, diffs) point at its *downward mirror cap*, never up. That is
the deep, beautiful part and it holds. The carve-out is **peer-symmetric caps at
one level** (§6.3a): two cells that hold incomparable caps over each other and
negate each other create an intra-stratum negative cycle the attenuation gate does
*not* rule out. The fix is cheap and local: **forbid same-stratum mutual negation**
— either by a tie-break (impose a total order on cells within a stratum, e.g. by
`CellId`, so one is canonically "below"; this is a *local stratification* and
recovers a unique model) or by falling to **well-founded semantics** (§3.4) for
that pair (the mutual readout renders as *undefined / "refused"* — the fail-closed
verdict, which is the *right* answer for "two peers each forbidding the other").

So: **the firmament hands us the strata for free for the reflective tower (the
hard, recursive part), and leaves exactly one easy, local obligation (same-level
mutual negation) that a `CellId` tie-break or a well-founded fallback closes.**

---

## 7. THE VERDICT — UNIT-DELAY vs. STRATIFIED FIXPOINT

### 7.1 The honest comparison

| | **Unit-delay (z⁻¹)** | **Stratified fixpoint** |
|---|---|---|
| Cycle handling | break by fiat (read frame `N−1`) | resolve (iterate strata in frame `N`) |
| Staleness | one frame, on self-referential readouts | none — frame is self-consistent |
| Termination | trivial (it's a DAG) | needs an argument: #strata bounded (✓ via firmament, §6) |
| Cost / frame | one `present` pass | one pass *per stratum* (small constant) |
| Strata needed | no | yes — must be *defined* and *maintained* |
| Failure mode | a lagged meta-view (benign) | a missed stratum boundary = storm returns |
| Fits dregg's grain | matches the existing `since(cursor)` pull-model | matches dregg's Datalog/Pred heritage & cap-tower |

### 7.2 When each is right

- **Unit-delay is right** when the cycle is *cosmetic* — a meta-view that can lag
  one frame without anyone caring (window positions, an inspector's own scroll
  state, a self-referential count). It is cheap, it always terminates, it needs no
  theory. For the **vast majority** of starbridge's reflexive surface — the
  inspector showing its own focus, the meta-debugger's own scrubber — one frame of
  self-lag is *imperceptible and harmless*. The §2 delta-fold already pulls on a
  cursor; a z⁻¹ self-edge is a natural fit for that pull-model.

- **Stratified fixpoint is right** when the cycle is *semantic* — when a
  within-frame self-consistent answer is *load-bearing*, not cosmetic. The sharp
  case in dregg: an **affordance/refusal readout that itself gates an action in
  the same frame.** If the meta-debugger refuses a turn *based on a projected
  authority fact that is itself being computed this frame*, a one-frame-stale
  authority view could **authorize on last frame's caps** — a (brief, but real)
  authority-staleness window. That is the §6 fail-closed concern, and it is the
  one place staleness is not benign. There, you want the exact fixpoint so the
  refusal reflects *this frame's* caps.

### 7.3 The recommendation for dregg

**Ship the unit-delay as the default, with the stratified fixpoint reserved for
the authority-bearing strata — and note that the firmament makes that reservation
nearly free.** Concretely:

1. **Default z⁻¹ for the UI/view strata (S₃ and up in §5.2).** `ViewCell`,
   `WorkspaceCell`, `PanelCell` self-views read the previous frame. One pass,
   always terminates, imperceptible lag. This covers ~all of the self-hosting
   inspector and is the right first move (it unblocks M3/M5 of REFLEXIVE-MIGRATION
   *today*, without owing a termination proof).

2. **Stratified (within-frame) evaluation for the authority strata (S₁→S₂, and any
   meta-level refusal/diff that gates a same-frame action).** Here staleness is not
   cosmetic. And here the strata are **already defined for you by the cap-tower
   (§6)** — `S₀ domain ⊏ S₁ authority ⊏ S₂ affordance-negation` is the attenuation
   order itself. So the "must define the strata" cost of the stratified approach is
   *paid by the firmament*, not by us. The termination argument is "#strata =
   attenuation depth, finite by the strict-narrowing of `is_attenuation`."

3. **Close the §6.3(a) carve-out once, globally:** forbid same-stratum mutual
   negation by a `CellId` tie-break (canonical intra-stratum order) with a
   well-founded *undefined → "refused"* fallback. One rule, fail-closed, done.

### 7.4 Does the cap-stratification result make the choice free?

**Partly — and in the direction that matters most.** The expensive part of the
stratified approach is normally *defining and maintaining the stratification* (you
have to prove, and re-prove as the program grows, that no negation cycles). §6's
result says: **for the reflective tower, the firmament defines and maintains the
stratification automatically** — every meta-level's negation points down its
mirror cap by construction, so the tower is stratified *as long as it is
cap-secure*, which it must be anyway. That is the part that would otherwise be a
recurring proof burden, and the firmament retires it.

What is **not** free: (i) the per-frame *iterate-to-convergence* cost (a small
constant — #strata passes — but nonzero vs. the unit-delay's single pass); (ii)
the §6.3(a) peer-symmetric carve-out (cheap, local, one-time); (iii) the
**precondition that `present` stays pure** (§6.3c) — the moment a projection can
grant a cap, the static stratification check is lost. So the honest summary:

> The firmament gives us the *strata* for free (the hard, recurring part). It does
> **not** give us the *per-frame iteration* for free, nor does it absolve us of
> keeping the projector pure and tie-breaking same-level peers. The choice between
> z⁻¹ and fixpoint therefore reduces to a *cost* question (one pass vs. a few),
> not a *correctness/definability* question — and *that* is the real gift: the
> firmament turns "is the reflexive fixpoint even well-defined?" (the §7.3 open
> question of REFLEXIVE-MIGRATION) into a settled **yes, by attenuation**, leaving
> only an engineering trade-off we can make per-stratum with eyes open.

---

## 8. WHAT I'D VERIFY VS. ASSERT FROM MEMORY (honesty ledger)

**Solid from our code (read at HEAD for this doc):** `present` is pure and
read-only (`presentable.rs:341,881`); Affordances emits an explicit
authorized/refused verdict (`:667,746`) — *this is the load-bearing
non-monotonicity*; `is_attenuation` = `granted ⊆ held` and `attenuate` only
narrows (`dregg-firmament/src/lib.rs:174,293–304`); a mirror is an attenuated
downward cap (`surface.rs:321`); the base holds no upward cap (`surface.rs:78`);
the `since(cursor)` delta + `WitnessCursor`/`Liveness` trichotomy
(`dynamics.rs:164`, `ui_snapshot.rs:116`); the open question is real and
unaddressed (REFLEXIVE-MIGRATION §2.3.5/§7.3).

**Canonical prior art — cited from memory; recommend a quick confirm of dates/
attributions before this goes outward:** Knaster–Tarski lattice fixpoint
(Tarski, *Pacific J. Math.* **1955**; Knaster's 1928 special case); Kleene
fixpoint / Scott-continuity; **Apt–Blair–Walker**, "Towards a Theory of
Declarative Knowledge," in *Foundations of Deductive Databases* (**1988**) —
stratified negation; **Van Gelder–Ross–Schlipf**, "The Well-Founded Semantics for
General Logic Programs" (*JACM* **1991**); **Gelfond–Lifschitz**, stable-model
semantics (**1988**); **B. C. Smith**, 3-Lisp / reflective tower (**1982**, PhD
thesis + POPL '84); **Wand & Friedman**, "The Mystery of the Tower Revealed"
(*Lisp & Symbolic Computation*, **1986**); **Bracha & Ungar**, "Mirrors: Design
Principles for Meta-level Facilities" (*OOPSLA* **2004**); McSherry et al.,
**differential dataflow** (CIDR 2013 / timely-dataflow lineage). I'm confident in
the *substance* of each (what the result says and why it applies here); the exact
years/venues above are the thing to spot-check, not the claims.

**The one genuinely open *technical* question** (not a citation): whether
starbridge will, in practice, ever produce a **same-stratum mutual negation**
(§6.3a) — two peer cells holding incomparable caps and negating each other. If it
never arises, (H) is unconditionally true for us and the choice is purely cost. If
it can arise, the `CellId` tie-break / well-founded fallback (§7.3.3) is the
closure, and it should be implemented *with* the first authority-stratum
fixpoint, not deferred (the caveat-with-its-closure-lane discipline).

---

*( ˘▾˘ ) a closing couplet, since the tower turned out to stand on its own
authority:*
*the mirror may not widen what the glass below it gave —*
*so every "no" points downward, and the fixpoint knows its floor.*
