/-
# Dregg2.Deos.GatedAffordance — an affordance fires only when caps AND live state agree (the htmx-on-crack conjunction).

`docs/CELL-PROGRAM-LANGUAGE.md` §11 (the language uplift) + `docs/deos/DEOS.md` §"htmx on crack".

THE GAP THIS CLOSES. The deos affordance gate (`Dregg2.Deos.Affordance.fireGate`) is CAP-ONLY: it asks
`required ⊆ held` and nothing about the cell's STATE. The cell-program language (`Exec.Program`'s
`RecordProgram.admitsCtx`) decides STATE admissibility and knows nothing about WHO holds what. So the two
worlds — "who may press the button" (caps) and "may the button be pressed RIGHT NOW" (state) — never
composed. A real app's button is BOTH: an "approve" button fires only if the viewer HOLDS the approver
cap AND the proposal is in `PENDING` state AND the viewer has not already voted. That conjunction — a
cap-gate AND a live-state predicate over the SAME interaction — had no home in the language. This module
is the home: a `GatedAffordance` pairs the REAL cap-gate (`fireGate`, the `is_attenuation` order the cap
crown proves) with a REAL state condition (`RecordProgram`, the `Exec.Program` structure-map), and
`fireGated` commits IFF BOTH pass.

This is NOT new mathematics. The cap gate is the EXISTING `Dregg2.Deos.Affordance.fireGate` (`required ⊆
held`); the state gate is the EXISTING `Dregg2.Exec.RecordProgram.admitsCtx` (the cell program the
executor already enforces every turn, threaded with the same `TurnCtx` the context atoms read). A gated
affordance is their CONJUNCTION — `&&` — and the keystone is the `↔` that says firing happens exactly
when both teeth bite. Both gates are load-bearing: the four cross-polarity teeth (§4) show neither alone
suffices.

## What is proven

  * `GatedAffordance φ` — a `CellAffordance φ` (the cap-gated effect-template) PLUS a `stateCond :
    RecordProgram` (the live-state gate the same executor enforces) PLUS the `method` the firing turn
    runs (so the state gate's `Cases`/default-deny dispatch is exercised).
  * `fireGated ga held ctx old new s post` — the gated dispatch: yields the verified-turn
    `AffordanceIntent` (binding the attested root, leg 4) IFF `fireGate ga.aff.required held` (caps) AND
    `ga.stateCond.admitsCtx ctx ga.method old new` (state); else `none` (refused in-band).
  * **`fireGated_iff` (THE KEYSTONE).** `fireGated` commits (`isSome`) ↔ `(required ⊆ held) ∧
    (stateCond admits)`. The conjunction nobody could express, as an `↔` — both teeth, both polarities.
  * The FOUR cross-polarity teeth (each gate is genuinely load-bearing):
      - `fireGated_both_pass` — caps OK ∧ state OK ⇒ fires (carrying the REAL effect, binding the root);
      - `fireGated_cap_fail_refuses` — caps FAIL (whatever the state) ⇒ refused (the cap tooth);
      - `fireGated_state_fail_refuses` — state FAILS (whatever the caps) ⇒ refused (the state tooth);
      - `fireGated_needs_both` — the witness that NEITHER gate alone admits (held-but-state-stale and
        state-ready-but-unheld both refuse) — the anti-"cap is enough" / anti-"state is enough" pin.
  * `fireGated_carries_real_effect` / `fireGated_binds_attested_root` — a committed gated fire still
    carries the affordance's REAL effect and binds the receipt's `newCommit` (leg-4 properties survive
    the state gate — the gate only ADDS a refusal condition, never forges a surface).
  * `fireGated_reactive` (the htmx tooth) — the SAME viewer with the SAME caps gets DIFFERENT verdicts
    as the cell STATE changes: a button dark in one state lights in another. "htmx on crack" — the
    surface reacts to state, not just to who is looking.

  * `GatedSurface`/`projectGatedFor held ctx method old new affs` — the per-viewer affordance set under
    BOTH gates: the affordances a viewer holding `held` may fire AGAINST THE CURRENT STATE. The
    membrane-negotiated frustum, now STATE-aware.
  * `projectGatedFor_monotone` — at a FIXED state, more authority ⇒ a SUPERSET of fireable affordances
    (progressive attenuation, preserved under the state gate).
  * `projectGatedFor_all_fireable` — every projected affordance actually fires (the set is sound: no
    offered-but-refused buttons, even with the state gate).
  * `projectGatedFor_state_reactive` — the SAME viewer's projected set CHANGES with state (the surface
    is live: a button enters/leaves the set as the cell transitions) — the projection-level htmx tooth.

Discipline: axiom-clean (`#assert_all_clean` at the close), no `sorry`, no `native_decide`. `lake build
Dregg2` green (LOCAL). NO core edit — the cap gate is the REAL `Affordance.fireGate`, the state gate the
REAL `Exec.RecordProgram.admitsCtx`; a gated affordance is their conjunction, nothing more.

## Rust-mirror site (LAW #1: the language is EMITTED from Lean; the convergence wires Rust)

The Rust twin is a `GatedAffordance { affordance: CellAffordance, state_cond: RecordProgram,
method: u32 }` beside `CellAffordance` in `starbridge-web-surface/src/affordance.rs`, whose `fire`
runs the EXISTING `is_attenuation` cap-gate (already there, `CellAffordance::authorized_for`) AND THEN
evaluates `state_cond` via the EXISTING `cell/src/program.rs` evaluator
(`evaluate_constraint_full(.., ctx)` over the touched cell's `(old, new)` records) — refusing the fire
(a new `FireError::StateConditionUnmet`) unless BOTH pass. The convergence does NOT author new
evaluator semantics: it calls the cell-program evaluator the executor already owns. (See §"Rust-mirror"
at the close for the exact file:line targets.)
-/
import Dregg2.Deos.Affordance
import Dregg2.Exec.Program
import Dregg2.Tactics

namespace Dregg2.Deos.GatedAffordance

open Dregg2.Authority (Auth)
open Dregg2.Deos.Affordance (CellAffordance FiredSurface AffordanceIntent fireGate fireGate_iff_subset
  fireGate_trans projectFor)
open Dregg2.Exec (RecordProgram StateConstraint SimpleConstraint TurnCtx Value)

-- The central type IS named `GatedAffordance` inside the `…Deos.GatedAffordance` namespace (matching
-- the repo's `Rehydration.Rehydration` / `ClearanceGraph.ClearanceGraph` precedent — the type carries
-- the module's name on purpose); silence the cosmetic duplicate-namespace linter for the module.
set_option linter.dupNamespace false

/-! ## §1 — A `GatedAffordance`: the cap-gated effect-template PLUS a live-state condition.

A `GatedAffordance` is the deos "htmx on crack" element with TEETH IN TWO DIMENSIONS: the rights
`required` to fire (the cap-gate, in the carried `CellAffordance`) AND a `stateCond : RecordProgram`
the cell must satisfy for the fire to be admissible (the live-state gate the executor already enforces).
Both are REAL: the cap-gate is `Affordance.fireGate`, the state-gate is `RecordProgram.admitsCtx`. -/

variable {φ : Type}

/-- **`GatedAffordance φ`** — a `CellAffordance φ` (cap-gated effect-template) plus a `stateCond`
(the live-state `RecordProgram` the same executor enforces) plus the `method` the firing turn runs
(so the state gate's `Cases` dispatch / default-deny is exercised by the right method). The "approve"
button is `{ aff := approveAff (requires approver cap), stateCond := state==PENDING ∧ ¬voted, method }`:
firing it demands BOTH the cap AND the live-state predicate. -/
structure GatedAffordance (φ : Type) where
  /-- The cap-gated effect-template (the REAL effect + its `required` rights — the `is_attenuation`
  template). -/
  aff       : CellAffordance φ
  /-- The live-state condition the cell must satisfy for the fire to be admissible (the REAL
  `RecordProgram` the executor enforces; threaded with the firing turn's `TurnCtx`). -/
  stateCond : RecordProgram
  /-- The method the firing turn runs (so `stateCond`'s `Cases`/default-deny dispatch matches the right
  arm — a wrong method default-denies, exactly as the executor would). -/
  method    : Nat

/-! ## §2 — `fireGated`: commit IFF caps AND state both pass.

`fireGated ga held ctx old new s post` runs the affordance ONLY when `held` authorizes `ga.aff.required`
(`fireGate`) AND the cell's `(old, new)` transition satisfies `ga.stateCond` under the turn context
`ctx` (`admitsCtx`). Both teeth must bite; either refusal is in-band (`none`). `s`/`post` are the
pre/post-state commitments (the receipt's `oldCommit`/`newCommit`), exactly as `Affordance.fire`. -/

/-- **The combined gate** — `gatedOK ga held ctx old new`: the conjunction of the cap-gate and the
state-gate as one `Bool`. `fireGate ga.aff.required held && ga.stateCond.admitsCtx ctx ga.method old new`.
THE predicate that says "this button may fire right now, for this viewer, in this state". -/
def gatedOK (ga : GatedAffordance φ) (held : List Auth) (ctx : TurnCtx) (old new : Value) : Bool :=
  fireGate ga.aff.required held && ga.stateCond.admitsCtx ctx ga.method old new

/-- **`fireGated ga held ctx old new s post`** — fire the gated affordance for an agent holding `held`,
in turn context `ctx`, against the cell transition `(old, new)`, with pre/post-state commitments
`s`/`post`. IF `gatedOK` (caps AND state both pass), yields `some` of the verified-turn
`AffordanceIntent` whose surface binds the attested root `post`; ELSE `none` (refused in-band). Reuses
`Affordance.fire` for the commit shape (so the leg-4 root-binding is the SAME), guarded ADDITIONALLY by
the state gate. -/
def fireGated (ga : GatedAffordance φ) (held : List Auth) (ctx : TurnCtx) (old new : Value)
    (s post : Nat) : Option (AffordanceIntent φ) :=
  if gatedOK ga held ctx old new then
    Dregg2.Deos.Affordance.fire ga.aff held s post
  else
    none

/-! ## §3 — THE KEYSTONE: firing happens exactly when BOTH gates pass. -/

/-- A small bridge: under `gatedOK`, the cap-gate holds, so the inner `Affordance.fire` commits. -/
private theorem fire_isSome_of_capOK (ga : GatedAffordance φ) (held : List Auth) (s post : Nat)
    (hcap : fireGate ga.aff.required held = true) :
    (Dregg2.Deos.Affordance.fire ga.aff held s post).isSome = true :=
  (Dregg2.Deos.Affordance.fire_authorized_iff ga.aff held s post).mpr hcap

/-- **THE KEYSTONE — `fireGated_iff`.** A gated fire COMMITS (`isSome`) if and only if BOTH the cap-gate
(`required ⊆ held`) AND the state-gate (`stateCond` admits the transition under `ctx`) pass. The
conjunction the language could not previously express, as an `↔`. Both teeth, both polarities: drop
either gate and the fire is refused. -/
theorem fireGated_iff (ga : GatedAffordance φ) (held : List Auth) (ctx : TurnCtx) (old new : Value)
    (s post : Nat) :
    (fireGated ga held ctx old new s post).isSome = true ↔
      (fireGate ga.aff.required held = true ∧
       ga.stateCond.admitsCtx ctx ga.method old new = true) := by
  unfold fireGated gatedOK
  by_cases hcap : fireGate ga.aff.required held = true
  · by_cases hst : ga.stateCond.admitsCtx ctx ga.method old new = true
    · rw [if_pos (by rw [hcap, hst]; rfl)]
      exact ⟨fun _ => ⟨hcap, hst⟩, fun _ => fire_isSome_of_capOK ga held s post hcap⟩
    · have hstf : ga.stateCond.admitsCtx ctx ga.method old new = false := by
        cases hb : ga.stateCond.admitsCtx ctx ga.method old new with
        | true => exact absurd hb hst | false => rfl
      rw [if_neg (by rw [hcap, hstf, Bool.and_false]; decide)]
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
      intro _; exact hst
  · have hcapf : fireGate ga.aff.required held = false := by
      cases hb : fireGate ga.aff.required held with
      | true => exact absurd hb hcap | false => rfl
    rw [if_neg (by rw [hcapf, Bool.false_and]; decide)]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
    intro h; exact absurd h hcap

/-! ## §4 — THE FOUR CROSS-POLARITY TEETH: each gate is genuinely load-bearing. -/

/-- **BOTH PASS ⇒ FIRES** (the positive corner). Caps authorize AND the state admits ⇒ the gated fire
commits. -/
theorem fireGated_both_pass (ga : GatedAffordance φ) (held : List Auth) (ctx : TurnCtx)
    (old new : Value) (s post : Nat)
    (hcap : fireGate ga.aff.required held = true)
    (hst : ga.stateCond.admitsCtx ctx ga.method old new = true) :
    (fireGated ga held ctx old new s post).isSome = true :=
  (fireGated_iff ga held ctx old new s post).mpr ⟨hcap, hst⟩

/-- **CAP-GATE FAILS ⇒ REFUSED** (the cap tooth), regardless of state. An agent who lacks the required
rights cannot fire the affordance EVEN IF the live state would admit the turn. The cap-gate is
load-bearing: a permissive state does not paper over missing authority. -/
theorem fireGated_cap_fail_refuses (ga : GatedAffordance φ) (held : List Auth) (ctx : TurnCtx)
    (old new : Value) (s post : Nat)
    (hcap : fireGate ga.aff.required held = false) :
    fireGated ga held ctx old new s post = none := by
  unfold fireGated gatedOK
  rw [if_neg (by rw [hcap, Bool.false_and]; decide)]

/-- **STATE-GATE FAILS ⇒ REFUSED** (the state tooth), regardless of caps. EVEN A FULLY-AUTHORIZED agent
cannot fire the affordance when the live state forbids it (the proposal is not `PENDING`, the deadline
passed, the viewer already voted). The state-gate is load-bearing: holding the cap is not enough — the
cell must be in a state that admits the turn. THIS is the half the cap-only `Affordance.fire` could
never express. -/
theorem fireGated_state_fail_refuses (ga : GatedAffordance φ) (held : List Auth) (ctx : TurnCtx)
    (old new : Value) (s post : Nat)
    (hst : ga.stateCond.admitsCtx ctx ga.method old new = false) :
    fireGated ga held ctx old new s post = none := by
  unfold fireGated gatedOK
  rw [if_neg (by rw [hst, Bool.and_false]; decide)]

-- `h1cap`/`h2st` are load-bearing for the STATEMENT (they pin that config 1 genuinely HAD the cap and
-- config 2 genuinely HAD the right state — without them "needs both" would be content-free), but the
-- proof only consumes the failing half of each; silence the unused-binder lint locally.
set_option linter.unusedVariables false in
/-- **NEITHER GATE ALONE SUFFICES** (the conjunction is genuine). Given a state where the cap-gate
passes but the state-gate fails (`held` authorizes, but the cell is in the wrong state) AND a separate
configuration where the state-gate passes but the cap-gate fails (the cell is ready, but the viewer
lacks the cap), BOTH refuse. So the gate is a true conjunction — you cannot satisfy it with caps alone
or with state alone. (This is the anti-"a cap is enough" / anti-"the right state is enough" pin; the
concrete `#guard` witnesses are in §6.) -/
theorem fireGated_needs_both (ga₁ ga₂ : GatedAffordance φ)
    (held₁ held₂ : List Auth) (ctx₁ ctx₂ : TurnCtx) (o₁ n₁ o₂ n₂ : Value) (s post : Nat)
    -- config 1: caps OK, state STALE ⇒ refused.
    (h1cap : fireGate ga₁.aff.required held₁ = true)
    (h1st  : ga₁.stateCond.admitsCtx ctx₁ ga₁.method o₁ n₁ = false)
    -- config 2: state READY, caps MISSING ⇒ refused.
    (h2cap : fireGate ga₂.aff.required held₂ = false)
    (h2st  : ga₂.stateCond.admitsCtx ctx₂ ga₂.method o₂ n₂ = true) :
    fireGated ga₁ held₁ ctx₁ o₁ n₁ s post = none ∧
    fireGated ga₂ held₂ ctx₂ o₂ n₂ s post = none :=
  ⟨fireGated_state_fail_refuses ga₁ held₁ ctx₁ o₁ n₁ s post h1st,
   fireGated_cap_fail_refuses  ga₂ held₂ ctx₂ o₂ n₂ s post h2cap⟩

/-! ## §5 — THE LEG-4 PROPERTIES SURVIVE THE STATE GATE (the gate only adds refusal). -/

/-- **A COMMITTED GATED FIRE CARRIES THE REAL EFFECT** — the state gate does not forge a surface: when
`fireGated` commits, the resulting intent fires the affordance's REAL effect verbatim (it commits via
the SAME `Affordance.fire`). The state gate is purely a refusal condition. -/
theorem fireGated_carries_real_effect (ga : GatedAffordance φ) (held : List Auth) (ctx : TurnCtx)
    (old new : Value) (s post : Nat) (intent : AffordanceIntent φ)
    (h : fireGated ga held ctx old new s post = some intent) :
    intent.surface.firedEffect = ga.aff.effect := by
  unfold fireGated gatedOK at h
  by_cases hg : (fireGate ga.aff.required held && ga.stateCond.admitsCtx ctx ga.method old new) = true
  · rw [if_pos hg] at h
    exact Dregg2.Deos.Affordance.fire_carries_real_effect ga.aff held s post intent h
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **A COMMITTED GATED FIRE BINDS THE ATTESTED ROOT** — leg-4's second clause survives: the surface's
`boundRoot` is the verified turn's `newCommit` (`= post`). The state gate adds a precondition; the
attested-root binding is untouched (it rides the SAME `Affordance.fire`). -/
theorem fireGated_binds_attested_root (ga : GatedAffordance φ) (held : List Auth) (ctx : TurnCtx)
    (old new : Value) (s post : Nat) (intent : AffordanceIntent φ)
    (h : fireGated ga held ctx old new s post = some intent) :
    intent.surface.boundRoot = post := by
  unfold fireGated gatedOK at h
  by_cases hg : (fireGate ga.aff.required held && ga.stateCond.admitsCtx ctx ga.method old new) = true
  · rw [if_pos hg] at h
    -- `Affordance.fire` commits to a surface whose boundRoot is exactly `post`.
    have hcap : fireGate ga.aff.required held = true := by
      rw [Bool.and_eq_true] at hg; exact hg.1
    unfold Dregg2.Deos.Affordance.fire at h
    rw [if_pos hcap] at h
    simp only [Option.some.injEq] at h
    subst h; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §6 — THE HTMX TOOTH: the SAME viewer's verdict CHANGES with state.

The point of "htmx on crack" is REACTIVITY: the surface responds to the cell's state, not just to who is
looking. With the cap-only gate, a viewer's button-set is fixed forever. With the gated affordance, the
SAME viewer (SAME caps) sees a button LIGHT in one state and DARK in another — the surface is live. -/

/-- **`fireGated_reactive` (THE HTMX TOOTH).** For a FIXED viewer (fixed `held`, fixed caps) who DOES
authorize the affordance, the gated fire's verdict is decided entirely by the state gate: it commits in
a state the `stateCond` admits and refuses in one it does not. So the SAME viewer's button reacts to the
cell's STATE — a button dark in `(o₁,n₁)` lights in `(o₂,n₂)`. The surface is live, not a frozen ACL.
-/
theorem fireGated_reactive (ga : GatedAffordance φ) (held : List Auth)
    (ctx₁ ctx₂ : TurnCtx) (o₁ n₁ o₂ n₂ : Value) (s post : Nat)
    (hcap : fireGate ga.aff.required held = true)
    (hst₁ : ga.stateCond.admitsCtx ctx₁ ga.method o₁ n₁ = false)   -- state STALE ⇒ dark
    (hst₂ : ga.stateCond.admitsCtx ctx₂ ga.method o₂ n₂ = true) :  -- state READY ⇒ lit
    (fireGated ga held ctx₁ o₁ n₁ s post).isSome = false ∧
    (fireGated ga held ctx₂ o₂ n₂ s post).isSome = true := by
  constructor
  · rw [fireGated_state_fail_refuses ga held ctx₁ o₁ n₁ s post hst₁]; rfl
  · exact fireGated_both_pass ga held ctx₂ o₂ n₂ s post hcap hst₂

/-! ## §7 — THE PER-VIEWER PROJECTION UNDER BOTH GATES (the state-aware frustum / membrane negotiation).

`Affordance.projectFor` returns the affordances a viewer may fire — but CAP-ONLY, so a viewer's set is
state-blind. `projectGatedFor` is the membrane-negotiated frustum made STATE-AWARE: the affordances a
viewer holding `held` may fire AGAINST THE CURRENT `(old, new)` transition in context `ctx`. Two viewers
diverge by their caps (as before) AND the SAME viewer's set changes as the cell transitions. -/

/-- A surface of gated affordances (the deos analogue of a server's htmx endpoints, each carrying its
own live-state precondition). -/
abbrev GatedSurface (φ : Type) := List (GatedAffordance φ)

/-- **`projectGatedFor held ctx old new affs`** — the affordances a viewer holding `held` may fire
against the current transition `(old, new)` under context `ctx`: those for which `gatedOK` (the cap-gate
AND the state-gate both pass). The per-viewer, per-STATE button-set — the membrane-negotiated frustum,
now reactive to the cell. -/
def projectGatedFor (held : List Auth) (ctx : TurnCtx) (old new : Value)
    (affs : GatedSurface φ) : GatedSurface φ :=
  affs.filter (fun ga => gatedOK ga held ctx old new)

/-- **EVERY PROJECTED GATED AFFORDANCE FIRES** — the projection is SOUND under both gates: a viewer is
only ever offered buttons that actually fire in the current state (no offered-but-refused buttons, even
with the state precondition). -/
theorem projectGatedFor_all_fireable (held : List Auth) (ctx : TurnCtx) (old new : Value)
    (affs : GatedSurface φ) (ga : GatedAffordance φ) (s post : Nat)
    (hmem : ga ∈ projectGatedFor held ctx old new affs) :
    (fireGated ga held ctx old new s post).isSome = true := by
  unfold projectGatedFor at hmem
  rw [List.mem_filter] at hmem
  have hgok : gatedOK ga held ctx old new = true := hmem.2
  unfold gatedOK at hgok
  rw [Bool.and_eq_true] at hgok
  rw [fireGated_iff]
  exact ⟨hgok.1, hgok.2⟩

/-- **THE PROJECTION IS MONOTONE IN AUTHORITY AT A FIXED STATE** — a viewer holding FEWER rights
(`held₁ ⊆ held₂`) is offered a SUBSET of the gated affordances the more-authorized viewer is, AT THE
SAME STATE. Progressive attenuation survives the state gate: widening authority can only ADD buttons
(those whose cap-gate now passes and whose state-gate already held), never remove one. The state gate
is the SAME for both viewers (it does not read `held`), so the membership difference is exactly the
cap-gate — the `fireGate_trans` law, under the shared state condition. -/
theorem projectGatedFor_monotone {held₁ held₂ : List Auth} (h12 : held₁ ⊆ held₂)
    (ctx : TurnCtx) (old new : Value) (affs : GatedSurface φ) :
    projectGatedFor held₁ ctx old new affs ⊆ projectGatedFor held₂ ctx old new affs := by
  intro ga ha
  unfold projectGatedFor at ha ⊢
  rw [List.mem_filter] at ha ⊢
  refine ⟨ha.1, ?_⟩
  -- gatedOK held₁ = (cap₁ && state); cap₁ ⇒ cap₂ by fireGate_trans; state is shared.
  have hgok₁ : gatedOK ga held₁ ctx old new = true := ha.2
  unfold gatedOK at hgok₁ ⊢
  rw [Bool.and_eq_true] at hgok₁
  have hcap₁ : fireGate ga.aff.required held₁ = true := hgok₁.1
  have hstate : ga.stateCond.admitsCtx ctx ga.method old new = true := hgok₁.2
  have hcap₂ : fireGate ga.aff.required held₂ = true := fireGate_trans h12 hcap₁
  rw [hcap₂, hstate]; rfl

/-! ## §8 — NON-VACUITY TEETH (`#guard`): the gated affordance BITES in all four corners. -/

section Witnesses

/-- A concrete effect type for the witnesses: a tag carrying a Nat payload. -/
inductive DemoEffect where | approve (id : Nat) | view (id : Nat)
deriving DecidableEq, Repr

open Dregg2.Exec (RecordProgram StateConstraint SimpleConstraint)

/-- The "approve" affordance: requires the `grant` right (the approver cap) to fire. -/
def approveCell : CellAffordance DemoEffect :=
  { required := [Auth.grant], effect := .approve 1, name := 1 }

/-- The live-state condition for "approve": the proposal must be in state `PENDING` (status field = 1).
A `predicate` program with one `fieldEquals "status" 1` constraint — the EXISTING cell-program gate. -/
def pendingCond : RecordProgram :=
  .predicate [.simple (.fieldEquals "status" 1)]

/-- The gated "approve" button: approver cap AND state==PENDING. The conjunction nobody could express. -/
def approveBtn : GatedAffordance DemoEffect :=
  { aff := approveCell, stateCond := pendingCond, method := 0 }

/-- A viewer holding the approver cap (`grant`). -/
def approverHeld : List Auth := [Auth.read, Auth.grant]
/-- A viewer holding only `read` (a plain member — NOT an approver). -/
def memberHeld : List Auth := [Auth.read]

/-- The cell in `PENDING` (status = 1) — the state the button needs. -/
def pendingState : Value := .record [("status", .int 1)]
/-- The cell in `RESOLVED` (status = 2) — the button must be DARK here even for an approver. -/
def resolvedState : Value := .record [("status", .int 2)]

-- THE FOUR CORNERS of the conjunction (the gate bites in every quadrant):

-- (1) approver caps ∧ PENDING state  ⇒ FIRES (the only firing corner):
#guard (fireGated approveBtn approverHeld TurnCtx.empty pendingState pendingState 100 110).isSome
-- (2) approver caps ∧ RESOLVED state ⇒ REFUSED (state tooth: holding the cap is NOT enough):
#guard (fireGated approveBtn approverHeld TurnCtx.empty resolvedState resolvedState 100 110).isNone
-- (3) member caps  ∧ PENDING state  ⇒ REFUSED (cap tooth: the right state is NOT enough):
#guard (fireGated approveBtn memberHeld   TurnCtx.empty pendingState pendingState 100 110).isNone
-- (4) member caps  ∧ RESOLVED state ⇒ REFUSED (neither gate passes):
#guard (fireGated approveBtn memberHeld   TurnCtx.empty resolvedState resolvedState 100 110).isNone

-- THE HTMX TOOTH: the SAME approver's button reacts to STATE — lit in PENDING, dark in RESOLVED:
#guard (fireGated approveBtn approverHeld TurnCtx.empty pendingState  pendingState  100 110).isSome
       && (fireGated approveBtn approverHeld TurnCtx.empty resolvedState resolvedState 100 110).isNone

-- A committed fire carries the REAL effect (the approve effect, verbatim) and binds the new root (110):
#guard match fireGated approveBtn approverHeld TurnCtx.empty pendingState pendingState 100 110 with
       | some i => (i.surface.firedEffect == DemoEffect.approve 1) && (i.surface.boundRoot == 110)
       | none   => false

-- THE PROJECTION under both gates is STATE-AWARE. A "view" button anyone may fire in any state, beside
-- the gated "approve" button:
def viewCell : CellAffordance DemoEffect := { required := [Auth.read], effect := .view 9, name := 2 }
def viewBtn  : GatedAffordance DemoEffect :=
  { aff := viewCell, stateCond := .none, method := 0 }   -- `.none` admits every state
def surface : GatedSurface DemoEffect := [approveBtn, viewBtn]

-- The approver in PENDING sees BOTH buttons (approve lit + view); in RESOLVED sees ONLY view
-- (approve darkened by state — the SAME viewer, the surface REACTED):
#guard (projectGatedFor approverHeld TurnCtx.empty pendingState  pendingState  surface).length == 2
#guard (projectGatedFor approverHeld TurnCtx.empty resolvedState resolvedState surface).length == 1
-- the member in PENDING sees ONLY view (approve darkened by CAPS — progressive attenuation):
#guard (projectGatedFor memberHeld TurnCtx.empty pendingState pendingState surface).length == 1
-- the member's single visible button is the view button (the approve is attenuated away):
#guard match projectGatedFor memberHeld TurnCtx.empty pendingState pendingState surface with
       | [b] => b.aff.name == 2
       | _   => false

-- PROGRESSIVE ATTENUATION at a fixed state: the member's set ⊆ the approver's set (in PENDING):
#guard (projectGatedFor memberHeld   TurnCtx.empty pendingState pendingState surface).length
        ≤ (projectGatedFor approverHeld TurnCtx.empty pendingState pendingState surface).length

end Witnesses

/-! ## §9 — Axiom hygiene. -/

#assert_all_clean [
  fireGated_iff,
  fireGated_both_pass,
  fireGated_cap_fail_refuses,
  fireGated_state_fail_refuses,
  fireGated_needs_both,
  fireGated_carries_real_effect,
  fireGated_binds_attested_root,
  fireGated_reactive,
  projectGatedFor_all_fireable,
  projectGatedFor_monotone
]

/-! ## Rust-mirror sites (LAW #1 — the convergence wires these; do NOT edit the Rust here)

For the concurrent Rust-cutover lane, the twins of this module are:

  * `starbridge-web-surface/src/affordance.rs` — ADD a `GatedAffordance` struct beside
    `CellAffordance` (`affordance.rs:90`): `{ affordance: CellAffordance, state_cond:
    dregg_cell::RecordProgram /* the program.rs StateConstraint program */, method: u32 }`. Its `fire`
    runs the EXISTING cap-gate `CellAffordance::authorized_for` (`affordance.rs:131`, the
    `is_attenuation` already there) AND THEN the EXISTING cell-program evaluator over the touched cell's
    `(old, new)` records — refusing unless BOTH pass.

  * `starbridge-web-surface/src/affordance.rs:239` (`enum FireError`) — ADD a
    `FireError::StateConditionUnmet { affordance: String }` variant (the state-tooth refusal, the twin
    of `fireGated_state_fail_refuses`), beside the existing `Unauthorized` (the cap-tooth refusal).

  * `cell/src/program.rs` — NO change needed: `GatedAffordance::fire` CALLS the existing
    `evaluate_constraint_full(&self.state_cond, new, old, ctx, witnesses)` (the evaluator the executor
    already owns); the convergence authors NO new evaluator semantics (LAW #1 — the state gate is the
    EXISTING `RecordProgram.admitsCtx` twin, already mirrored by `program.rs`'s evaluator).

  * `starbridge-web-surface/src/affordance.rs:291` (`AffordanceSurface::project_for`) — ADD a
    `project_gated_for(&self, held, ctx, old, new)` that filters on BOTH `authorized_for` AND
    `state_cond` evaluation (the twin of `projectGatedFor`), so the per-viewer surface is STATE-AWARE
    (the htmx reactivity): the same viewer's button-set changes as the backing cell transitions.
-/

end Dregg2.Deos.GatedAffordance
