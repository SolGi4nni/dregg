/-
# Dregg2.Deos.Reactive — affordances that react to a state TRANSITION, a deadline WINDOW, and a per-viewer MEMBRANE.

`docs/REFINEMENT-DESIGN.md` Decision 3 ("cells are law, agents are will, receipts are the nervous
system" — the reactivity model) + `docs/deos/DEOS.md` §"htmx on crack". This is the TEMPORAL/REACTIVE
rung above `Dregg2.Deos.GatedAffordance`.

THE GAP THIS CLOSES. `GatedAffordance.fireGated` gates a SINGLE state snapshot: its state gate is
`RecordProgram.admitsCtx ctx method old new`, and `fireGated_reactive` only proves the SAME viewer's
button reacts as the cell sits in `(o₁,n₁)` vs `(o₂,n₂)` — it does NOT gate on the *shape of the
transition* old→new. But real reactivity is "this button fires only on the PENDING→PENDING transition
that ADDS your ballot" (a relational pre→post link, not a property of `new` alone) and "this resolve
fires only inside the [open, close] voting WINDOW" (a deadline, not a static `fieldGteHeight`). And the
per-viewer surface (`projectGatedFor`) divides by CAPS only — the frustum membrane also projects by a
witness-graph permission, so two viewers see DISTINCT surfaces even at equal authority. Those three —
the TRANSITION gate, the WINDOW gate, the MEMBRANE predicate — had no home. This module is the home.

This is NOT new cryptography and NOT a new state machine. The cap-gate is the EXISTING
`Affordance.fireGate` (`required ⊆ held`, the proven `is_attenuation` lattice); the commit shape is the
EXISTING `Affordance.fire` (so the leg-4 attested-root binding is the SAME). What is NEW is the GATE
SHAPE: a `TransitionPred` (a decidable `Value → Value → Bool` over the OLD and NEW records together —
the relational pre→post link the single-state `admitsCtx` cannot express by construction), an explicit
height `[open, close]` window (the executor's `EvalContext::height`, two-sided where `fieldGteHeight` is
one-sided), and a `Membrane` predicate conjoining viewer authority with a witness-graph projection bit.

## What is proven

  * §1 `TransitionPred` — a decidable relation on `(old, new)`; `TransitionGate` packages a `pre`
    (old must satisfy), a `post` (new must satisfy), and a `link` (the relational pre→new bridge —
    e.g. `new.count = old.count + 1`). `transitionOK` is their conjunction. KEY: the `link` reads BOTH
    records, so a property of `new` ALONE can never witness it — the reactivity beyond a single-state gate.
  * §2 `ReactiveAffordance` — a `CellAffordance` (cap-gated effect-template) PLUS a `TransitionGate`
    PLUS a `[open, close]` height window. `fireReactive ga held height old new s post` commits IFF
    caps pass AND the transition qualifies AND `open ≤ height ≤ close`.
  * **§3 `fireReactive_iff` (THE KEYSTONE).** `fireReactive` commits ↔ `(required ⊆ held) ∧
    transitionOK(old,new) ∧ open ≤ height ≤ close`. The three-way conjunction as an `↔`.
  * §4 THE SIX CROSS-POLARITY TEETH — each of the three gates is genuinely load-bearing:
      - `fireReactive_all_pass` (caps ∧ transition ∧ window ⇒ fires, carrying the REAL effect);
      - `fireReactive_cap_fail_refuses` / `fireReactive_transition_fail_refuses` /
        `fireReactive_window_fail_refuses` (drop ANY one gate ⇒ refused);
      - `fireReactive_wrong_old_refuses` (THE TRANSITION TOOTH) — the SAME `new` reached from a
        DIFFERENT `old` that breaks the `link` REFUSES, even with caps + a window + a `new` that
        satisfies `post`. A property of `new` alone is NOT enough — the transition shape is checked.
      - `fireReactive_after_deadline_refuses` (THE DEADLINE TOOTH) — past `close`, a fully-authorized,
        perfectly-qualifying transition is auto-refused (the window closed).
  * §5 `fireReactive_carries_real_effect` / `fireReactive_binds_attested_root` — the leg-4 properties
    survive all three gates (they ride the SAME `Affordance.fire`; the gates only ADD refusal).
  * §6 `fireReactive_window_reactive` (the htmx-temporal tooth) — the SAME viewer, SAME qualifying
    transition, fires INSIDE the window and is dark OUTSIDE it: the surface reacts to the CLOCK.
  * §7 `Membrane` — the per-viewer frustum projection as a PREDICATE: `membraneShows viewer aff`
    conjoins `fireGate aff.required viewer.held` (authority) with `viewer.permits aff.name` (the
    witness-graph projection bit). `projectMembrane` filters a surface by it. KEYSTONE
    `membrane_two_viewers_distinct`: two viewers at EQUAL authority but DIFFERENT witness-graph
    projections see DISTINCT surfaces (the membrane divides beyond caps). And
    `membrane_authority_monotone` (more caps ⇒ superset at a fixed projection).

  * §8 The vote/resolve worked example (`#guard`): a council where "vote" fires ONLY on the
    PENDING→PENDING transition that increments the tally inside the window, "resolve" fires ONLY on the
    quorum-reached transition — and every off-corner (wrong old, after deadline, missing cap, equal-
    authority-different-membrane) REFUSES.

Discipline: axiom-clean (`#assert_all_clean` at the close), no `sorry`, no `native_decide`. `lake build
Dregg2.Deos.Reactive` green (LOCAL). NO core edit — the cap-gate is the REAL `Affordance.fireGate`, the
commit the REAL `Affordance.fire`; the transition/window/membrane gates are decidable Bool conjunctions
layered ON TOP, never a new lattice.

## Rust-mirror sites (LAW #1: Lean-authoritative — the convergence wires Rust; do NOT edit Rust here).

See §"Rust-mirror" at the close for the exact `starbridge-web-surface` file:line targets.
-/
import Dregg2.Deos.Affordance
import Dregg2.Exec.Program
import Dregg2.Tactics

namespace Dregg2.Deos.Reactive

open Dregg2.Authority (Auth)
open Dregg2.Deos.Affordance (CellAffordance FiredSurface AffordanceIntent fireGate fireGate_iff_subset
  fireGate_trans)
open Dregg2.Exec (Value)

set_option linter.dupNamespace false

variable {φ : Type}

/-! ## §1 — `TransitionPred` / `TransitionGate`: a gate on the SHAPE of old→new (not a single state).

The reactivity gap: `RecordProgram.admitsCtx ctx method old new` decides whether `new` is an admissible
post-state — but a real "vote" button fires only on the transition that ADDS a ballot (`new.count =
old.count + 1`), a relation between BOTH records that a property of `new` alone cannot express. A
`TransitionGate` makes that first-class: `pre` (the old record must satisfy), `post` (the new record
must satisfy), and `link` (the relational bridge reading BOTH — the part that is genuinely about the
TRANSITION, not either endpoint). -/

/-- A decidable predicate on a transition `(old, new)` — reads BOTH records. The atom of reactivity:
unlike a single-state predicate, a `TransitionPred` can require `new[count] = old[count] + 1`. -/
abbrev TransitionPred := Value → Value → Bool

/-- **`TransitionGate`** — a transition gate as three decidable predicates: `pre old` (the cell must
START in a qualifying state), `post new` (it must LAND in a qualifying state), and `link old new` (the
relational bridge — the part that reads both, e.g. "the tally went up by exactly one"). The
`link` is what makes this a TRANSITION gate and not two single-state gates: it cannot be witnessed by
either endpoint alone. -/
structure TransitionGate where
  /-- The old record must satisfy this (the cell starts in a qualifying state — e.g. status = PENDING). -/
  pre  : Value → Bool
  /-- The new record must satisfy this (the cell lands in a qualifying state — e.g. status = PENDING). -/
  post : Value → Bool
  /-- The relational pre→new bridge — reads BOTH records (e.g. `new[count] = old[count] + 1`). The
  reactivity core: a property of `new` alone can never witness it. -/
  link : TransitionPred

/-- **`transitionOK tg old new`** — the transition gate fires: `pre old ∧ post new ∧ link old new`.
THE predicate that says "this old→new transition is the one this button reacts to". -/
def transitionOK (tg : TransitionGate) (old new : Value) : Bool :=
  tg.pre old && tg.post new && tg.link old new

/-- The transition gate decomposes into its three conjuncts (the shape every tooth below reads). -/
theorem transitionOK_iff (tg : TransitionGate) (old new : Value) :
    transitionOK tg old new = true ↔
      (tg.pre old = true ∧ tg.post new = true ∧ tg.link old new = true) := by
  unfold transitionOK
  rw [Bool.and_eq_true, Bool.and_eq_true]
  tauto

/-! ## §2 — `ReactiveAffordance`: cap-gate + transition-gate + a `[open, close]` height window.

A `ReactiveAffordance` is the deos element that reacts in THREE dimensions: WHO (the cap-gate, in the
carried `CellAffordance`), WHAT TRANSITION (the `TransitionGate`), and WHEN (a two-sided height window
`[openHeight, closeHeight]` over the executor's `EvalContext::height`). The window is two-sided where
`Exec.Program`'s `fieldGteHeight`/`fieldLteHeight` are one-sided — a genuine `[open, close]` voting
window with an auto-closing deadline. -/

/-- **`ReactiveAffordance φ`** — a `CellAffordance φ` (cap-gated effect-template) plus a `gate`
(the transition gate the old→new must satisfy) plus an inclusive height window `[openHeight,
closeHeight]` (the executor turn-height window the fire must fall in). The "vote" button is
`{ aff := voteAff (requires ballot cap), gate := pending→pending ∧ tally+1, openHeight, closeHeight }`. -/
structure ReactiveAffordance (φ : Type) where
  /-- The cap-gated effect-template (the REAL effect + its `required` rights). -/
  aff         : CellAffordance φ
  /-- The transition gate (`pre`/`post`/`link`) the `(old, new)` must satisfy. -/
  gate        : TransitionGate
  /-- The inclusive window OPEN height — the fire is refused before this turn height. -/
  openHeight  : Nat
  /-- The inclusive window CLOSE height (the deadline) — the fire is refused after this turn height. -/
  closeHeight : Nat

/-- **`inWindow ra height`** — the turn height lies in the inclusive window `[openHeight, closeHeight]`.
The temporal gate: `open ≤ height ≤ close`. Before `open` the button has not yet opened; after `close`
it has auto-closed (the deadline passed). -/
def inWindow (ra : ReactiveAffordance φ) (height : Nat) : Bool :=
  decide (ra.openHeight ≤ height) && decide (height ≤ ra.closeHeight)

/-- The window decomposes into its two bounds. -/
theorem inWindow_iff (ra : ReactiveAffordance φ) (height : Nat) :
    inWindow ra height = true ↔ (ra.openHeight ≤ height ∧ height ≤ ra.closeHeight) := by
  unfold inWindow
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]

/-- **`reactiveOK ra held height old new`** — the THREE-WAY gate as one `Bool`: the cap-gate AND the
transition-gate AND the window-gate. THE predicate that says "this button may fire RIGHT NOW, for this
viewer, on THIS transition, at THIS height". -/
def reactiveOK (ra : ReactiveAffordance φ) (held : List Auth) (height : Nat) (old new : Value) : Bool :=
  fireGate ra.aff.required held && transitionOK ra.gate old new && inWindow ra height

/-- **`fireReactive ra held height old new s post`** — fire the reactive affordance for an agent
holding `held`, at turn `height`, against the transition `(old, new)`, with pre/post commitments
`s`/`post`. Commits (via the SAME `Affordance.fire`, so the leg-4 root-binding is identical) IFF
`reactiveOK` (caps AND transition AND window all pass); else `none` (refused in-band). -/
def fireReactive (ra : ReactiveAffordance φ) (held : List Auth) (height : Nat) (old new : Value)
    (s post : Nat) : Option (AffordanceIntent φ) :=
  if reactiveOK ra held height old new then
    Dregg2.Deos.Affordance.fire ra.aff held s post
  else
    none

/-! ## §3 — THE KEYSTONE: firing happens exactly when ALL THREE gates pass. -/

/-- Under `reactiveOK`, the cap-gate holds, so the inner `Affordance.fire` commits. -/
private theorem fire_isSome_of_capOK (ra : ReactiveAffordance φ) (held : List Auth) (s post : Nat)
    (hcap : fireGate ra.aff.required held = true) :
    (Dregg2.Deos.Affordance.fire ra.aff held s post).isSome = true :=
  (Dregg2.Deos.Affordance.fire_authorized_iff ra.aff held s post).mpr hcap

/-- A small bridge: `reactiveOK = true ↔` the three conjuncts each hold. -/
theorem reactiveOK_iff (ra : ReactiveAffordance φ) (held : List Auth) (height : Nat) (old new : Value) :
    reactiveOK ra held height old new = true ↔
      (fireGate ra.aff.required held = true ∧
       transitionOK ra.gate old new = true ∧
       inWindow ra height = true) := by
  unfold reactiveOK
  rw [Bool.and_eq_true, Bool.and_eq_true]
  tauto

/-- **THE KEYSTONE — `fireReactive_iff`.** A reactive fire COMMITS (`isSome`) if and only if ALL THREE
gates pass: the cap-gate (`required ⊆ held`), the transition-gate (`pre old ∧ post new ∧ link old new`),
AND the window-gate (`open ≤ height ≤ close`). The three-way conjunction the language could not express,
as an `↔`. Drop ANY gate and the fire is refused. -/
theorem fireReactive_iff (ra : ReactiveAffordance φ) (held : List Auth) (height : Nat) (old new : Value)
    (s post : Nat) :
    (fireReactive ra held height old new s post).isSome = true ↔
      (fireGate ra.aff.required held = true ∧
       transitionOK ra.gate old new = true ∧
       inWindow ra height = true) := by
  unfold fireReactive
  by_cases hok : reactiveOK ra held height old new = true
  · rw [if_pos hok]
    rw [reactiveOK_iff] at hok
    obtain ⟨hcap, _, _⟩ := hok
    exact ⟨fun _ => (reactiveOK_iff ra held height old new).mp (by unfold reactiveOK; rw [hcap]; simp_all),
           fun _ => fire_isSome_of_capOK ra held s post hcap⟩
  · have hokf : reactiveOK ra held height old new = false := by
      cases hb : reactiveOK ra held height old new with
      | true => exact absurd hb hok | false => rfl
    rw [if_neg hok]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
    intro hcap htr
    have := (reactiveOK_iff ra held height old new)
    intro hwin
    exact absurd ((reactiveOK_iff ra held height old new).mpr ⟨hcap, htr, hwin⟩) hok

/-! ## §4 — THE SIX CROSS-POLARITY TEETH: each of the three gates is load-bearing. -/

/-- **ALL THREE PASS ⇒ FIRES** (the positive corner). -/
theorem fireReactive_all_pass (ra : ReactiveAffordance φ) (held : List Auth) (height : Nat)
    (old new : Value) (s post : Nat)
    (hcap : fireGate ra.aff.required held = true)
    (htr  : transitionOK ra.gate old new = true)
    (hwin : inWindow ra height = true) :
    (fireReactive ra held height old new s post).isSome = true :=
  (fireReactive_iff ra held height old new s post).mpr ⟨hcap, htr, hwin⟩

/-- **CAP-GATE FAILS ⇒ REFUSED** (the cap tooth), whatever the transition / window. -/
theorem fireReactive_cap_fail_refuses (ra : ReactiveAffordance φ) (held : List Auth) (height : Nat)
    (old new : Value) (s post : Nat) (hcap : fireGate ra.aff.required held = false) :
    fireReactive ra held height old new s post = none := by
  unfold fireReactive reactiveOK
  rw [if_neg (by rw [hcap, Bool.false_and, Bool.false_and]; decide)]

/-- **TRANSITION-GATE FAILS ⇒ REFUSED** (the transition tooth), whatever the caps / window. A
fully-authorized agent inside the window cannot fire if the old→new transition is not the one this
button reacts to. -/
theorem fireReactive_transition_fail_refuses (ra : ReactiveAffordance φ) (held : List Auth)
    (height : Nat) (old new : Value) (s post : Nat) (htr : transitionOK ra.gate old new = false) :
    fireReactive ra held height old new s post = none := by
  unfold fireReactive reactiveOK
  rw [if_neg (by rw [htr]; simp)]

/-- **WINDOW-GATE FAILS ⇒ REFUSED** (the window tooth), whatever the caps / transition. Outside
`[open, close]` the button is dark even for a fully-authorized, perfectly-qualifying transition. -/
theorem fireReactive_window_fail_refuses (ra : ReactiveAffordance φ) (held : List Auth) (height : Nat)
    (old new : Value) (s post : Nat) (hwin : inWindow ra height = false) :
    fireReactive ra held height old new s post = none := by
  unfold fireReactive reactiveOK
  rw [if_neg (by rw [hwin, Bool.and_false]; decide)]

-- `hpost`/`hcap`/`hwin` are load-bearing for the STATEMENT — they pin that the OTHER two gates pass and
-- `new` satisfies `post`, so the refusal is attributable SOLELY to the broken transition `link` (without
-- them this tooth would be content-free) — but the proof only consumes `hlink`; silence the lint locally.
set_option linter.unusedVariables false in
/-- **THE TRANSITION TOOTH — the SAME `new` from a WRONG `old` REFUSES.** Given a transition `(old₂,
new)` whose `link` FAILS (the `new` is identical to a qualifying transition's new state, but it was
reached from a DIFFERENT `old₂` that breaks the relational link — e.g. the tally did NOT actually go up
by one from `old₂`), the fire is refused — EVEN WITH full caps, an open window, and a `new` satisfying
`post`. This is the half a single-state gate (`admitsCtx … old new` used as "is `new` ok") can be
fooled by: the SHAPE of the transition is checked, not just the destination. The anti-"a good-looking
new state is enough" pin. -/
theorem fireReactive_wrong_old_refuses (ra : ReactiveAffordance φ) (held : List Auth) (height : Nat)
    (old₂ new : Value) (s post : Nat)
    -- the destination `new` satisfies `post`, caps pass, the window is open …
    (hpost : ra.gate.post new = true)
    (hcap  : fireGate ra.aff.required held = true)
    (hwin  : inWindow ra height = true)
    -- … but the transition FROM `old₂` breaks the relational link ⇒ REFUSED.
    (hlink : ra.gate.link old₂ new = false) :
    fireReactive ra held height old₂ new s post = none := by
  apply fireReactive_transition_fail_refuses
  unfold transitionOK
  rw [hlink, Bool.and_false]

/-- **THE DEADLINE TOOTH — past `close`, a perfect transition auto-refuses.** When `height >
closeHeight` (the deadline passed), a fully-authorized, perfectly-qualifying transition is refused: the
window auto-closed. The temporal gate is genuinely load-bearing — holding the cap and making the right
move is not enough once the clock runs out. (The dual of `fireReactive_window_reactive`'s "lit inside
the window".) -/
theorem fireReactive_after_deadline_refuses (ra : ReactiveAffordance φ) (held : List Auth)
    (height : Nat) (old new : Value) (s post : Nat) (hlate : ra.closeHeight < height) :
    fireReactive ra held height old new s post = none := by
  apply fireReactive_window_fail_refuses
  unfold inWindow
  have : decide (height ≤ ra.closeHeight) = false := by
    rw [decide_eq_false_iff_not]; exact Nat.not_le.mpr hlate
  rw [this, Bool.and_false]

/-! ## §5 — THE LEG-4 PROPERTIES SURVIVE ALL THREE GATES (the gates only add refusal). -/

/-- **A COMMITTED REACTIVE FIRE CARRIES THE REAL EFFECT** — when `fireReactive` commits, the resulting
intent fires the affordance's REAL effect verbatim (it commits via the SAME `Affordance.fire`). The
three gates are purely refusal conditions; they never forge a surface. -/
theorem fireReactive_carries_real_effect (ra : ReactiveAffordance φ) (held : List Auth) (height : Nat)
    (old new : Value) (s post : Nat) (intent : AffordanceIntent φ)
    (h : fireReactive ra held height old new s post = some intent) :
    intent.surface.firedEffect = ra.aff.effect := by
  unfold fireReactive at h
  by_cases hok : reactiveOK ra held height old new = true
  · rw [if_pos hok] at h
    exact Dregg2.Deos.Affordance.fire_carries_real_effect ra.aff held s post intent h
  · rw [if_neg hok] at h; exact absurd h (by simp)

/-- **A COMMITTED REACTIVE FIRE BINDS THE ATTESTED ROOT** — leg-4's second clause survives: the
surface's `boundRoot` is the verified turn's `newCommit` (`= post`). The three gates add preconditions;
the attested-root binding rides the SAME `Affordance.fire`. -/
theorem fireReactive_binds_attested_root (ra : ReactiveAffordance φ) (held : List Auth) (height : Nat)
    (old new : Value) (s post : Nat) (intent : AffordanceIntent φ)
    (h : fireReactive ra held height old new s post = some intent) :
    intent.surface.boundRoot = post := by
  unfold fireReactive at h
  by_cases hok : reactiveOK ra held height old new = true
  · rw [if_pos hok] at h
    have hcap : fireGate ra.aff.required held = true := by
      rw [reactiveOK_iff] at hok; exact hok.1
    unfold Dregg2.Deos.Affordance.fire at h
    rw [if_pos hcap] at h
    simp only [Option.some.injEq] at h
    subst h; rfl
  · rw [if_neg hok] at h; exact absurd h (by simp)

/-! ## §6 — THE HTMX-TEMPORAL TOOTH: the SAME viewer's SAME move reacts to the CLOCK. -/

/-- **`fireReactive_window_reactive` (THE TEMPORAL HTMX TOOTH).** For a FIXED viewer making a FIXED
qualifying transition (caps pass, transition qualifies), the verdict is decided by the CLOCK: it
commits at a height INSIDE the window and refuses at a height OUTSIDE it. So the SAME viewer's SAME move
reacts to TIME — lit during the voting window, dark after the deadline. The surface is live against the
clock, not just against the state. -/
theorem fireReactive_window_reactive (ra : ReactiveAffordance φ) (held : List Auth)
    (h₁ h₂ : Nat) (old new : Value) (s post : Nat)
    (hcap : fireGate ra.aff.required held = true)
    (htr  : transitionOK ra.gate old new = true)
    (hin  : inWindow ra h₁ = true)      -- inside the window  ⇒ lit
    (hout : inWindow ra h₂ = false) :   -- outside the window ⇒ dark
    (fireReactive ra held h₁ old new s post).isSome = true ∧
    (fireReactive ra held h₂ old new s post).isSome = false := by
  constructor
  · exact fireReactive_all_pass ra held h₁ old new s post hcap htr hin
  · rw [fireReactive_window_fail_refuses ra held h₂ old new s post hout]; rfl

/-! ## §7 — THE MEMBRANE AS A PREDICATE: per-viewer frustum projection (authority ∧ witness-graph).

`Affordance.projectFor` / `GatedAffordance.projectGatedFor` divide a surface by CAPS. But the
rehydration frustum membrane also projects by a WITNESS-GRAPH permission: which fragments of the cell a
viewer's witness graph authorizes them to SEE (a clearance/disclosure bit independent of the fire-cap).
So two viewers can hold the SAME caps yet see DIFFERENT surfaces. `membraneShows` makes the membrane a
PREDICATE: viewer authority (the REAL `fireGate`) AND the viewer's witness-graph projection bit. -/

/-- **`Viewer`** — a membrane viewer: the rights `held` (the cap dimension) PLUS a `permits` predicate
(the witness-graph projection — which affordance names this viewer's frustum authorizes them to see,
e.g. a disclosure/clearance bit decided OUTSIDE the fire-cap). Two viewers can share `held` but differ
in `permits` — the membrane divides them. -/
structure Viewer where
  /-- The rights this viewer holds (the cap dimension — the REAL `is_attenuation` gate input). -/
  held    : List Auth
  /-- The witness-graph projection: which affordance NAMES this viewer's frustum authorizes them to
  see (the disclosure dimension, independent of the fire-cap). -/
  permits : Nat → Bool

/-- **`membraneShows v aff`** — the membrane projects affordance `aff` to viewer `v` IFF the viewer's
caps authorize the fire (`fireGate aff.required v.held`, the REAL `is_attenuation`) AND the viewer's
witness-graph permits the affordance's name (`v.permits aff.name`). The per-viewer frustum surface as a
conjunction of AUTHORITY and PROJECTION — the two dimensions the membrane negotiates. -/
def membraneShows (v : Viewer) (aff : CellAffordance φ) : Bool :=
  fireGate aff.required v.held && v.permits aff.name

/-- **`projectMembrane v affs`** — the affordances the membrane projects to viewer `v`: those
`membraneShows` admits (caps AND witness-graph projection both pass). The per-viewer frustum, divided
by BOTH dimensions. -/
def projectMembrane (v : Viewer) (affs : List (CellAffordance φ)) : List (CellAffordance φ) :=
  affs.filter (fun aff => membraneShows v aff)

/-- A membership bridge: an affordance is in the membrane projection IFF it is in the surface AND the
membrane shows it. -/
theorem mem_projectMembrane (v : Viewer) (affs : List (CellAffordance φ)) (aff : CellAffordance φ) :
    aff ∈ projectMembrane v affs ↔ (aff ∈ affs ∧ membraneShows v aff = true) := by
  unfold projectMembrane; rw [List.mem_filter]

-- `hheld : v₁.held = v₂.held` is the load-bearing EQUAL-AUTHORITY pin — it is what makes this "two
-- viewers at EQUAL authority diverge" rather than "two arbitrary viewers" (so the membrane is shown to
-- divide BEYOND caps); the proof reads the cap-gate on `v₁.held` directly, so the lint flags it — silence
-- it locally.
set_option linter.unusedVariables false in
/-- **THE MEMBRANE KEYSTONE — TWO VIEWERS AT EQUAL AUTHORITY SEE DISTINCT SURFACES.** Given two viewers
with the SAME caps (`v₁.held = v₂.held`) and an affordance both could fire (its cap-gate passes for the
shared held set) that ONE viewer's witness-graph permits and the OTHER's does NOT, the membrane projects
it to the first viewer and NOT the second. So the frustum divides BEYOND caps: two viewers at equal
authority diverge by their witness-graph projection — distinct surfaces by construction, the membrane's
per-viewer reason for being. -/
theorem membrane_two_viewers_distinct (v₁ v₂ : Viewer) (affs : List (CellAffordance φ))
    (aff : CellAffordance φ) (hmem : aff ∈ affs)
    (hheld : v₁.held = v₂.held)
    (hcap  : fireGate aff.required v₁.held = true)
    (hp1   : v₁.permits aff.name = true)
    (hp2   : v₂.permits aff.name = false) :
    aff ∈ projectMembrane v₁ affs ∧ aff ∉ projectMembrane v₂ affs := by
  constructor
  · rw [mem_projectMembrane]
    refine ⟨hmem, ?_⟩
    unfold membraneShows; rw [hcap, hp1]; rfl
  · rw [mem_projectMembrane]
    intro hcontra
    have hshows : membraneShows v₂ aff = true := hcontra.2
    unfold membraneShows at hshows
    rw [hp2, Bool.and_false] at hshows
    exact absurd hshows (by simp)

/-- **THE MEMBRANE IS MONOTONE IN AUTHORITY AT A FIXED PROJECTION.** Two viewers sharing the SAME
witness-graph projection (`v₁.permits = v₂.permits`) but with `v₁.held ⊆ v₂.held`: the weaker viewer's
membrane surface ⊆ the stronger's. Widening caps (at a fixed disclosure) can only ADD buttons —
progressive attenuation survives the membrane's second dimension. The witness-graph projection is the
SAME for both, so the membership difference is exactly the cap-gate (`fireGate_trans`). -/
theorem membrane_authority_monotone (v₁ v₂ : Viewer)
    (hperm : ∀ n, v₁.permits n = v₂.permits n) (h12 : v₁.held ⊆ v₂.held)
    (affs : List (CellAffordance φ)) :
    projectMembrane v₁ affs ⊆ projectMembrane v₂ affs := by
  intro aff ha
  rw [mem_projectMembrane] at ha ⊢
  refine ⟨ha.1, ?_⟩
  have hshows : membraneShows v₁ aff = true := ha.2
  unfold membraneShows at hshows ⊢
  rw [Bool.and_eq_true] at hshows
  rw [fireGate_trans h12 hshows.1, ← hperm aff.name, hshows.2]; rfl

/-! ## §8 — THE VOTE/RESOLVE WORKED EXAMPLE (`#guard`): the reactive gates BITE in every corner. -/

section Witnesses

/-- A concrete effect type for the witnesses: vote / resolve, each carrying a Nat payload. -/
inductive DemoEffect where | vote (id : Nat) | resolve (id : Nat) | view (id : Nat)
deriving DecidableEq, Repr

/-- The PENDING status code (1) and RESOLVED status code (2) for the council cell. -/
def PENDING : Int := 1
def RESOLVED : Int := 2
/-- The quorum threshold — `resolve` fires only on the transition that REACHES it. -/
def QUORUM : Int := 3

/-- `new[status] = s`. -/
private def statusIs (s : Int) (v : Value) : Bool := v.scalar "status" == some s
/-- `new[tally] = old[tally] + 1` (the ballot-added relational link — reads BOTH records). -/
private def tallyPlusOne (old new : Value) : Bool :=
  match old.scalar "tally", new.scalar "tally" with
  | some a, some b => b == a + 1
  | _,      _      => false
/-- `new[tally] ≥ QUORUM ∧ old[tally] < QUORUM` (the quorum-REACHED link — the crossing, not the level). -/
private def quorumReached (old new : Value) : Bool :=
  match old.scalar "tally", new.scalar "tally" with
  | some a, some b => decide (a < QUORUM) && decide (QUORUM ≤ b)
  | _,      _      => false

/-- The VOTE gate: PENDING→PENDING AND the tally went up by exactly one (a ballot was added). -/
def voteGate : TransitionGate :=
  { pre := statusIs PENDING, post := statusIs PENDING, link := tallyPlusOne }

/-- The RESOLVE gate: PENDING→RESOLVED AND the tally CROSSED quorum on this transition. -/
def resolveGate : TransitionGate :=
  { pre := statusIs PENDING, post := statusIs RESOLVED, link := quorumReached }

/-- The "vote" affordance: requires the `write` right (a council member's ballot cap). -/
def voteAff : CellAffordance DemoEffect := { required := [Auth.write], effect := .vote 1, name := 1 }
/-- The "resolve" affordance: requires the `grant` right (the chair's resolve cap). -/
def resolveAff : CellAffordance DemoEffect :=
  { required := [Auth.grant], effect := .resolve 1, name := 2 }

/-- The "vote" reactive button: ballot cap AND the add-a-ballot transition AND inside `[10, 20]`. -/
def voteBtn : ReactiveAffordance DemoEffect :=
  { aff := voteAff, gate := voteGate, openHeight := 10, closeHeight := 20 }
/-- The "resolve" reactive button: chair cap AND the quorum-crossing transition AND inside `[10, 30]`. -/
def resolveBtn : ReactiveAffordance DemoEffect :=
  { aff := resolveAff, gate := resolveGate, openHeight := 10, closeHeight := 30 }

/-- A council member (holds `write` — the ballot cap). -/
def memberHeld : List Auth := [Auth.read, Auth.write]
/-- The chair (holds `grant` — the resolve cap). -/
def chairHeld : List Auth := [Auth.read, Auth.grant]
/-- A plain observer (holds only `read`). -/
def observerHeld : List Auth := [Auth.read]

/-- PENDING with tally 0 (before any ballot). -/
def pend0 : Value := .record [("status", .int 1), ("tally", .int 0)]
/-- PENDING with tally 1 (after one ballot). -/
def pend1 : Value := .record [("status", .int 1), ("tally", .int 1)]
/-- PENDING with tally 2 (the quorum-1 state). -/
def pend2 : Value := .record [("status", .int 1), ("tally", .int 2)]
/-- RESOLVED with tally 3 (quorum reached). -/
def resolved3 : Value := .record [("status", .int 2), ("tally", .int 3)]

-- ════════════ THE TRANSITION TOOTH (vote fires ONLY on the add-a-ballot transition) ════════════

-- (✓) member, ballot-added (tally 0→1), inside window ⇒ FIRES (the only vote-firing corner):
#guard (fireReactive voteBtn memberHeld 15 pend0 pend1 100 110).isSome
-- (✗) member, NO ballot added (tally 1→1, the `link` fails) ⇒ REFUSED — the SAME `new` shape (PENDING,
--     a valid tally) but the WRONG transition (it did not increment). A single-state gate would pass:
#guard (fireReactive voteBtn memberHeld 15 pend1 pend1 100 110).isNone
-- (✗) member, ballot added but from the WRONG old (tally 0→2, jumps by two — not a single ballot):
#guard (fireReactive voteBtn memberHeld 15 pend0 pend2 100 110).isNone

-- ════════════ THE DEADLINE TOOTH (vote auto-closes after height 20) ════════════

-- (✗) member, perfect add-a-ballot transition, but height 25 > close 20 ⇒ REFUSED (deadline passed):
#guard (fireReactive voteBtn memberHeld 25 pend0 pend1 100 110).isNone
-- (✗) member, perfect transition, but height 5 < open 10 ⇒ REFUSED (window not yet open):
#guard (fireReactive voteBtn memberHeld 5 pend0 pend1 100 110).isNone
-- THE TEMPORAL HTMX TOOTH: the SAME member's SAME ballot is LIT at 15 (inside) and DARK at 25 (after):
#guard (fireReactive voteBtn memberHeld 15 pend0 pend1 100 110).isSome
       && (fireReactive voteBtn memberHeld 25 pend0 pend1 100 110).isNone

-- ════════════ THE CAP TOOTH (only the ballot-holder may vote) ════════════

-- (✗) observer (no write cap), perfect transition, inside window ⇒ REFUSED (cap tooth):
#guard (fireReactive voteBtn observerHeld 15 pend0 pend1 100 110).isNone

-- ════════════ RESOLVE fires ONLY on the quorum-REACHED transition ════════════

-- (✓) chair, quorum crossed (tally 2→3, PENDING→RESOLVED), inside window ⇒ FIRES:
#guard (fireReactive resolveBtn chairHeld 22 pend2 resolved3 100 110).isSome
-- (✗) chair, but tally 0→3 from old with tally 0 — wait, that DID cross (0<3≤3). Use a non-crossing:
--     chair, status PENDING→RESOLVED but the quorum link fails (old already ≥ quorum: tally stays 3):
#guard (fireReactive resolveBtn chairHeld 22 resolved3 resolved3 100 110).isNone
-- (✗) member (no grant cap) cannot resolve even on the quorum transition ⇒ REFUSED (cap tooth):
#guard (fireReactive resolveBtn memberHeld 22 pend2 resolved3 100 110).isNone

-- a committed vote carries the REAL effect (vote 1) and binds the new root (110):
#guard match fireReactive voteBtn memberHeld 15 pend0 pend1 100 110 with
       | some i => (i.surface.firedEffect == DemoEffect.vote 1) && (i.surface.boundRoot == 110)
       | none   => false

-- ════════════ THE MEMBRANE: two viewers at EQUAL authority, DIFFERENT witness-graph ════════════

/-- A secret-ballot "view tally" affordance anyone with `read` may fire — IF their frustum permits. -/
def tallyView : CellAffordance DemoEffect := { required := [Auth.read], effect := .view 9, name := 3 }

/-- Viewer A: holds `read`, and the witness-graph PERMITS seeing the tally (a trustee). -/
def trustee : Viewer := { held := [Auth.read], permits := fun n => n == 3 }
/-- Viewer B: holds the SAME `read`, but the witness-graph does NOT permit the tally (a guest). -/
def guest   : Viewer := { held := [Auth.read], permits := fun _ => false }

-- SAME caps (both `[read]`, both pass the cap-gate for `tallyView`) — yet the membrane DIVIDES them:
#guard fireGate tallyView.required trustee.held    -- trustee's caps authorize the fire …
#guard fireGate tallyView.required guest.held      -- … and so do the guest's (EQUAL authority) …
-- … but the trustee's frustum SHOWS the tally and the guest's does NOT (distinct surfaces):
#guard (membraneShows trustee tallyView : Bool)
#guard !(membraneShows guest tallyView : Bool)
-- the projection bears it out: the trustee sees the tally button, the guest sees nothing:
#guard (projectMembrane trustee [tallyView]).length == 1
#guard (projectMembrane guest   [tallyView]).length == 0

end Witnesses

/-! ## §9 — Axiom hygiene. -/

#assert_all_clean [
  transitionOK_iff,
  inWindow_iff,
  reactiveOK_iff,
  fireReactive_iff,
  fireReactive_all_pass,
  fireReactive_cap_fail_refuses,
  fireReactive_transition_fail_refuses,
  fireReactive_window_fail_refuses,
  fireReactive_wrong_old_refuses,
  fireReactive_after_deadline_refuses,
  fireReactive_carries_real_effect,
  fireReactive_binds_attested_root,
  fireReactive_window_reactive,
  mem_projectMembrane,
  membrane_two_viewers_distinct,
  membrane_authority_monotone
]

/-! ## Rust-mirror sites (LAW #1 — the convergence wires these; do NOT edit the Rust here)

For the concurrent Rust-cutover lane, the twins of this module are:

  * `starbridge-web-surface/src/affordance.rs` — ADD a `ReactiveAffordance` struct beside
    `GatedAffordance` (the `GatedAffordance.lean` Rust-mirror target at `affordance.rs:90`):
    `{ affordance: CellAffordance, gate: TransitionGate, open_height: u64, close_height: u64 }`, where
    `TransitionGate { pre: RecordPredicate, post: RecordPredicate, link: TransitionPredicate }` and a
    `TransitionPredicate` is a `Fn(&CellState /*old*/, &CellState /*new*/) -> bool` (the relational
    pre→new bridge — the part that reads BOTH records, which the existing single-state `state_cond`
    cannot). Its `fire` runs the EXISTING cap-gate `CellAffordance::authorized_for` (`affordance.rs:131`)
    AND THEN `gate.pre(old) && gate.post(new) && gate.link(old, new)` AND THEN the inclusive height
    window `open_height <= ctx.height && ctx.height <= close_height` (reading `EvalContext::height`,
    already in scope) — refusing unless ALL THREE pass.

  * `starbridge-web-surface/src/affordance.rs:239` (`enum FireError`) — ADD two variants beside the
    `GatedAffordance.lean` mirror's `StateConditionUnmet`: `FireError::TransitionUnmet { affordance:
    String }` (the transition-tooth refusal, the twin of `fireReactive_transition_fail_refuses` /
    `fireReactive_wrong_old_refuses`) and `FireError::OutsideWindow { affordance: String, open: u64,
    close: u64, height: u64 }` (the deadline-tooth refusal, the twin of
    `fireReactive_window_fail_refuses` / `fireReactive_after_deadline_refuses`).

  * `starbridge-web-surface/src/affordance.rs:291` (`AffordanceSurface::project_for`) — ADD a
    `project_membrane(&self, viewer: &Viewer)` filtering on BOTH `authorized_for` (the cap dimension)
    AND `viewer.permits(affordance.name)` (the witness-graph projection bit), where `Viewer { held:
    Vec<Auth>, permits: Box<dyn Fn(u32) -> bool> }` carries the frustum's per-name disclosure
    predicate. The twin of `projectMembrane` + `membrane_two_viewers_distinct`: two viewers at EQUAL
    `held` but DIFFERENT `permits` get DISTINCT surfaces (the frustum divides beyond caps — the
    rehydration membrane's per-viewer projection, now state-and-disclosure aware).

  * NO `cell/src/program.rs` change: the transition `link` is a closure over the touched cell's
    `(old, new)` records the surface layer evaluates; it authors NO new `StateConstraint` evaluator
    semantics (LAW #1). (A `TransitionGate` whose `pre`/`post`/`link` are expressible as
    `RecordProgram`s MAY delegate to the existing `evaluate_constraint_full`, but the reactive layer
    owns the relational composition.)
-/

end Dregg2.Deos.Reactive
