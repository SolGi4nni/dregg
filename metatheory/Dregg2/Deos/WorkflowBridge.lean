/-
# Dregg2.Deos.WorkflowBridge — the deos affordance surface IS the rendering of the workflow stack.

`docs/deos/DEOS.md` §"htmx on crack" + `Dregg2.Protocol.Workflow` (the multi-step authenticated
workflow) + `Dregg2.Deos.{GatedAffordance,Reactive}` (the cap∧state gate + the transition gate).

THE GAP THIS CLOSES. Two surfaces of the same kernel grew up apart. `Protocol.Workflow.exec` is the
EXECUTABLE multi-party choreography step: it commits a step ONLY when (1) the actor is the step's
`authorizedParty` (the role/cap check), (2) the workflow is in the step's `precond` phase (the
choreography order), and (3) an attestation `verify`s — advancing `precond → postPhase` and appending an
attested receipt. `Deos.GatedAffordance.fireGated` is the "htmx on crack" deos button: it fires ONLY
when (1) the viewer's caps authorize (`fireGate required held`, the `is_attenuation` order) AND (2) the
live cell STATE admits (`RecordProgram.admitsCtx`, the same executor's state gate). And
`Deos.Reactive.fireReactive` adds the TRANSITION gate: a fire keyed to the SHAPE of `old → new`, not a
property of `new` alone. Nobody had SHOWN these are the same object — that a workflow step is LITERALLY a
sequenced gated/reactive affordance fire, the deos surface RENDERING the choreography, not a fork of it.
This module is that proof.

THE BRIDGE (what is proven). A workflow `StepKind` projects to a `GatedAffordance` (`stepGated`) whose:
  * **cap-gate IS the authorization** — `fireGate (stepRights s) (heldFor actor s)` passes IFF
    `actor = authorizedParty s`. The actor "holds" the step's right exactly when it is the authorized
    party (`heldFor actor s := if actor = authorizedParty s then stepRights s else []`); the gate is the
    GENUINE `Affordance.fireGate`, biting precisely on the workflow's authorization predicate.
  * **state-gate IS the phase precondition** — `stateCond s := phase == precond s` (a `fieldEquals`
    `RecordProgram`, the SAME `admitsCtx` the executor runs); it admits the cell `phaseCell p` IFF
    `p = precond s`. The choreography order, as the deos live-state gate.
And the phase transition `precond → postPhase` projects to a `ReactiveAffordance` (`stepReactive`) whose
`TransitionGate` fires exactly on the `precond s → postPhase s` move (`pre = phase==precond`,
`post = phase==postPhase`, `link` ties them) — the workflow's phase advance IS the reactive transition
gate.

This is NOT new mathematics and NOT a second executor. The cap-gate is the REAL `Affordance.fireGate`;
the state/transition gates are the REAL `RecordProgram.admitsCtx` / `Reactive.TransitionGate`; the commit
shape is the REAL `Affordance.fire`. A workflow step is their conjunction — the deos surface is the
choreography stack RENDERED, with zero new trust. The order/skip teeth of `Workflow` (`exec_in_order`,
`merge_requires_approved`) are carried THROUGH the bridge: the gated/reactive fire refuses out-of-phase
exactly as `exec` does.

## What is proven

  * §2 `workflowStep_is_gatedAffordance` (KEYSTONE) — for any `(actor, s, p)`, the gated fire of
    `stepGated s` (for an actor holding `heldFor actor s`, against `phaseCell p`) COMMITS ↔ the two
    workflow teeth `actor = authorizedParty s ∧ p = precond s`. The step IS a cap∧state affordance.
  * §3 `workflow_fires_iff_affordance_fires` (KEYSTONE) — the `Workflow.exec` commit and the gated
    affordance fire AGREE up to the attestation leg: `exec` commits ↔ (the gated fire commits ∧ the
    attestation verifies). The executor step and the deos button are the same gate, modulo the §8
    crypto leg `exec` additionally carries.
  * §4 the order/skip teeth carried THROUGH (both polarities):
      - `gated_cap_fail_is_unauthorized` — an UNAUTHORIZED actor's gated fire refuses (the cap tooth =
        `exec_authorized`'s contrapositive, rendered);
      - `gated_state_fail_is_out_of_order` — an OUT-OF-PHASE gated fire refuses (the state tooth =
        `exec_in_order`'s contrapositive — the skip tooth);
      - `gated_merge_requires_approved` — the headline `merge_requires_approved`, rendered: the `merge`
        button is DARK except from the `approved` phase.
  * §5 `phaseTransition_is_reactiveAffordance` (KEYSTONE) — the reactive fire of `stepReactive s`
    COMMITS (in-window) ↔ `actor = authorizedParty s ∧ the move is precond s → postPhase s`. The phase
    advance IS the reactive transition gate. With `reactive_wrong_phase_refuses` (the transition tooth:
    the SAME `postPhase` reached from a WRONG `old` phase refuses — a property of `new` alone cannot
    witness the choreography edge).
  * §6 biting `#guard` teeth in BOTH polarities for the worked 3-party review/CI workflow (author
    submits → reviewer approves → CI merges), every corner: authorized∧in-phase FIRES, unauthorized
    REFUSES (cap tooth), out-of-phase REFUSES (skip tooth), and the reactive transition tooth.

Discipline: axiom-clean (`#assert_all_clean` at the close), no `sorry`, no `native_decide`. `lake build
Dregg2.Deos.WorkflowBridge` green (LOCAL). NO core edit, NO sibling edit — the cap-gate is the REAL
`Affordance.fireGate`, the state gate the REAL `RecordProgram.admitsCtx`, the transition gate the REAL
`Reactive.TransitionGate`; the bridge is a faithful PROJECTION of `Workflow` onto them, nothing more.

## Umbrella import line (for the maintainer of `Dregg2/Deos.lean` — NOT edited by this lane)

    import Dregg2.Deos.WorkflowBridge -- the WORKFLOW⟷affordance bridge: a Protocol.Workflow.exec step
      -- IS a sequenced GatedAffordance/ReactiveAffordance fire (the deos surface RENDERS the
      -- choreography stack, not a fork). KEYSTONES workflowStep_is_gatedAffordance (cap-gate=authorized
      -- ∧ state-gate=phase==precond), workflow_fires_iff_affordance_fires (exec ⟺ gated-fire ∧ attest),
      -- phaseTransition_is_reactiveAffordance (precond→postPhase IS the transition gate); the order/skip
      -- teeth carried through (gated_state_fail_is_out_of_order, gated_merge_requires_approved). #assert_all_clean.
-/
import Dregg2.Deos.GatedAffordance
import Dregg2.Deos.Reactive
import Dregg2.Protocol.Workflow
import Dregg2.Tactics

namespace Dregg2.Deos.WorkflowBridge

open Dregg2.Authority (Auth)
open Dregg2.Deos.Affordance (CellAffordance AffordanceIntent fireGate fireGate_iff_subset)
open Dregg2.Deos.GatedAffordance (GatedAffordance gatedOK fireGated fireGated_iff
  fireGated_cap_fail_refuses fireGated_state_fail_refuses fireGated_both_pass)
open Dregg2.Deos.Reactive (TransitionGate ReactiveAffordance transitionOK inWindow
  fireReactive fireReactive_iff fireReactive_transition_fail_refuses)
open Dregg2.Exec (RecordProgram StateConstraint SimpleConstraint TurnCtx Value)
open Dregg2.Protocol.Workflow (Phase StepKind Party authorizedParty precond postPhase
  WState Receipt exec exec_authorized exec_in_order)

set_option linter.dupNamespace false

/-! ## §1 — THE PROJECTION: a workflow `StepKind` ↦ a deos `GatedAffordance` (cap∧state).

The bridge renders each workflow step as a deos button. The step's TWO non-crypto teeth become the
button's two gates, faithfully:

  * the AUTHORIZATION `actor = authorizedParty s` becomes the cap-gate — the actor holds the step's
    `stepRights` exactly when it is the authorized party, so `fireGate` bites on authorization;
  * the PHASE precondition `phase = precond s` becomes the state-gate — `stateCond s` is the
    `RecordProgram` `phase == precond s`, which `admitsCtx` admits exactly in that phase.

(The attestation leg `verify` is the §8 crypto portal; it rides `exec`'s third conjunct and is carried
explicitly in §3 — the deos cap∧state gate is the NON-crypto half, the half the surface renders.) -/

/-- **`phaseCode p`** — a phase as a status `Int` (the cell field the state-gate reads). Distinct codes
for distinct phases (the four-way split is injective: `phaseCode_inj`), so "the cell is in phase `p`"
becomes the decidable `fieldEquals "phase" (phaseCode p)`. -/
def phaseCode : Phase → Int
  | .init      => 0
  | .submitted => 1
  | .approved  => 2
  | .merged    => 3

/-- The phase-code is INJECTIVE — distinct phases get distinct codes, so the `fieldEquals` state-gate
distinguishes every pair of phases (no two phases collapse onto one cell value). -/
theorem phaseCode_inj {p q : Phase} (h : phaseCode p = phaseCode q) : p = q := by
  cases p <;> cases q <;> simp_all [phaseCode]

/-- **`phaseCell p`** — the cell record in phase `p`: a one-field record `{ phase := phaseCode p }`.
The live cell the deos button reads its state-gate against (the workflow `WState.phase`, rendered as a
cell field). -/
def phaseCell (p : Phase) : Value := .record [("phase", .int (phaseCode p))]

/-- **`stepRights s`** — the authorization token a step requires to fire. Each step carries a real
right (the cap an authorized actor wields); the token is NON-empty so the cap-gate is genuinely
load-bearing (an actor with `[]` is refused). We reuse the kernel `Auth` constructors as the
per-step tokens (the gate is the GENUINE `is_attenuation` — `required ⊆ held` — over real `Auth`s). -/
def stepRights : StepKind → List Auth
  | .submit  => [Auth.write]    -- the author's submit cap
  | .approve => [Auth.grant]    -- the reviewer's approve cap
  | .merge   => [Auth.control]  -- the CI bot's merge cap

/-- **`heldFor actor s`** — the rights actor `actor` wields for step `s`: the step's `stepRights`
exactly when `actor` is the step's authorized party, else `[]` (no token). This is the faithful
rendering of the workflow authorization `actor = authorizedParty s` as held capabilities: an actor
holds the step's right IFF it is the one authorized to take the step. -/
def heldFor (actor : Party) (s : StepKind) : List Auth :=
  if actor = authorizedParty s then stepRights s else []

/-- A concrete effect the rendered button fires: the step it takes (so the affordance carries the REAL
workflow step as its effect — the deos surface fires the choreography action). -/
abbrev StepEffect := StepKind

/-- **`stepCell s`** — the cap-gated effect-template of step `s`: requires `stepRights s`, carries the
step as its effect. The `CellAffordance` half of the rendered button. -/
def stepCell (s : StepKind) : CellAffordance StepEffect :=
  { required := stepRights s, effect := s, name := 0 }

/-- **`stateCond s`** — the live-state gate of step `s`: the `RecordProgram` `phase == precond s` (a
`fieldEquals` predicate over the cell's `phase` field). The REAL `admitsCtx` gate the executor runs —
it admits the cell `phaseCell p` exactly when `p = precond s` (`stateCond_admits_iff`). The
choreography order, rendered as the deos state-gate. -/
def stateCond (s : StepKind) : RecordProgram :=
  .predicate [.simple (.fieldEquals "phase" (phaseCode (precond s)))]

/-- **`stepGated s`** — THE RENDERING: a workflow step as a deos `GatedAffordance`. Its cap-gate is the
step's authorization (`stepRights`), its state-gate is the step's phase precondition (`stateCond`). The
"submit" button is `{ aff := requires the author cap, stateCond := phase==init }`; firing it demands the
author's cap AND the `init` phase — exactly the workflow's `submit` preconditions. -/
def stepGated (s : StepKind) : GatedAffordance StepEffect :=
  { aff := stepCell s, stateCond := stateCond s, method := 0 }

/-! ## §1a — The two gates reduce to the two workflow teeth (the load-bearing equivalences). -/

/-- **THE CAP-GATE IS THE AUTHORIZATION** — `fireGate (stepRights s) (heldFor actor s) = true ↔
actor = authorizedParty s`. The deos cap-gate bites EXACTLY on the workflow's authorization predicate:
an actor's caps authorize the step's button iff it is the step's authorized party. (`stepRights s` is
non-empty, so an unauthorized actor — who holds `[]` — genuinely fails the gate.) -/
theorem capGate_iff_authorized (actor : Party) (s : StepKind) :
    fireGate (stepRights s) (heldFor actor s) = true ↔ actor = authorizedParty s := by
  unfold heldFor
  by_cases h : actor = authorizedParty s
  · rw [if_pos h]; simp only [h, iff_true]
    -- fireGate r r = true (reflexive)
    exact Dregg2.Deos.Affordance.fireGate_refl (stepRights s)
  · rw [if_neg h]; simp only [h, iff_false]
    -- fireGate (stepRights s) [] = false, since stepRights s is non-empty.
    intro hg
    rw [fireGate_iff_subset] at hg
    -- a non-empty required ⊆ [] is impossible: the head token would be in `[]`, contradiction.
    cases s <;> simp [stepRights] at hg

/-- The cell `phaseCell p` reads its `phase` field as exactly `phaseCode p` (the cell-record
reduction the state-gate consults). -/
theorem phaseCell_scalar (p : Phase) : (phaseCell p).scalar "phase" = some (phaseCode p) := by
  cases p <;> rfl

/-- **THE STATE-GATE IS THE PHASE PRECONDITION** — `(stateCond s).admitsCtx ctx 0 (phaseCell p)
(phaseCell p) = true ↔ p = precond s`. The deos live-state gate (the GENUINE `admitsCtx`) admits the
cell exactly when its phase is the step's precondition: the choreography order, rendered. The gate reads
the `fieldEquals "phase"` constraint — a context-FREE atom, so the equivalence holds for ANY `ctx` (the
phase-gate does not consult the turn context, exactly as a static choreography order should not). -/
theorem stateGate_iff_phase (s : StepKind) (p : Phase) (ctx : TurnCtx) :
    (stateCond s).admitsCtx ctx 0 (phaseCell p) (phaseCell p) = true ↔ p = precond s := by
  unfold stateCond
  -- `admitsCtx` of a single-constraint `predicate` is that constraint's `evalConstraintCtx`.
  show ([StateConstraint.simple (.fieldEquals "phase" (phaseCode (precond s)))].all
          (fun c => Dregg2.Exec.evalConstraintCtx ctx c (phaseCell p) (phaseCell p)) = true) ↔ _
  -- `fieldEquals` is context-free: `evalConstraintCtx ctx (.simple (.fieldEquals ..)) = evalSimple ..`.
  simp only [List.all_cons, List.all_nil, Bool.and_true,
    Dregg2.Exec.evalConstraintCtx, Dregg2.Exec.evalSimpleCtx, Dregg2.Exec.evalSimple]
  rw [phaseCell_scalar]
  -- now: (some (phaseCode p) == some (phaseCode (precond s))) = true ↔ p = precond s
  rw [beq_iff_eq, Option.some.injEq]
  constructor
  · intro h; exact phaseCode_inj h
  · intro h; subst h; rfl

/-! ## §2 — THE KEYSTONE: a workflow step IS a cap∧state `GatedAffordance`.

The gated fire of `stepGated s` — for an actor holding `heldFor actor s`, against the cell `phaseCell p`
in phase `p` — commits if and only if the two NON-crypto workflow teeth hold: the actor is the step's
`authorizedParty` (the cap-gate, via `capGate_iff_authorized`) AND the cell is in the step's `precond`
phase (the state-gate, via `stateGate_iff_phase`). A workflow step's `(authorizedParty, precond)` pair IS
a deos cap∧state button — `fireGated_iff` factored through the two gate-reductions. -/

/-- **`workflowStep_is_gatedAffordance` — THE KEYSTONE.** The deos gated fire of a workflow step commits
exactly when the step's two non-crypto preconditions hold: `actor` is the authorized party AND the cell
is in the step's `precond` phase. The step `(authorizedParty s, precond s)` IS the cap∧state gate — the
deos surface RENDERS the choreography step, not a fork. (The third workflow conjunct — the attestation
`verify` — is the §8 crypto leg, carried separately in §3.) -/
theorem workflowStep_is_gatedAffordance (actor : Party) (s : StepKind) (p : Phase) (ctx : TurnCtx)
    (sc post : Nat) :
    (fireGated (stepGated s) (heldFor actor s) ctx (phaseCell p) (phaseCell p) sc post).isSome = true ↔
      (actor = authorizedParty s ∧ p = precond s) := by
  rw [fireGated_iff]
  -- `stepGated s` has `.aff.required = stepRights s`, `.stateCond = stateCond s`, `.method = 0`.
  show (fireGate (stepRights s) (heldFor actor s) = true ∧
        (stateCond s).admitsCtx ctx 0 (phaseCell p) (phaseCell p) = true) ↔ _
  rw [capGate_iff_authorized, stateGate_iff_phase]

/-! ## §3 — `workflow_fires_iff_affordance_fires`: the EXECUTOR step and the deos button AGREE.

`Workflow.exec` carries THREE conjuncts: authorization, phase-order, and the §8 attestation `verify`.
The gated affordance is the NON-crypto half (authorization ∧ phase-order). So `exec` commits exactly when
the gated fire commits AND the attestation verifies — the executor step and the deos surface are the SAME
gate, modulo the crypto leg `exec` additionally carries. (`p := k.phase` ties the workflow state's phase
to the cell the button reads.) -/

open Dregg2.Crypto (CryptoKernel)

/-- **`workflow_fires_iff_affordance_fires` — THE KEYSTONE (executor ⟷ deos).** A `Workflow.exec` step
commits if and only if the rendered gated affordance fires AND the attestation verifies. The executor's
step is the deos button's cap∧state gate CONJOINED with the §8 attestation leg: the two surfaces of the
kernel agree exactly, the crypto leg being the only thing `exec` carries beyond the cap∧state button. -/
theorem workflow_fires_iff_affordance_fires {Digest Proof : Type} [AddCommGroup Digest]
    [CryptoKernel Digest Proof] (stmt : Digest)
    (k : WState Proof) (s : StepKind) (actor : Party) (att : Proof) (ctx : TurnCtx) (sc post : Nat) :
    (exec stmt k s actor att).isSome = true ↔
      ((fireGated (stepGated s) (heldFor actor s) ctx (phaseCell k.phase) (phaseCell k.phase) sc post).isSome = true
        ∧ CryptoKernel.verify stmt att = true) := by
  rw [workflowStep_is_gatedAffordance]
  -- LHS: `exec` is `some _` iff its guard `actor = authorizedParty s ∧ k.phase = precond s ∧ verify`.
  unfold exec
  by_cases hg : actor = authorizedParty s ∧ k.phase = precond s
      ∧ CryptoKernel.verify stmt att = true
  · rw [if_pos hg]
    simp only [Option.isSome_some, true_iff]
    exact ⟨⟨hg.1, hg.2.1⟩, hg.2.2⟩
  · rw [if_neg hg]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    -- the RHS conjunction would reconstruct `hg`; contradiction.
    rintro ⟨⟨hauth, hphase⟩, hver⟩
    exact hg ⟨hauth, hphase, hver⟩

/-! ## §4 — THE ORDER/SKIP TEETH, CARRIED THROUGH (both polarities).

`Workflow.exec_authorized` / `exec_in_order` / `merge_requires_approved` are the workflow's refusal
teeth. The bridge carries them THROUGH to the deos button: an unauthorized actor's button is DARK (the
cap tooth = `exec_authorized`'s contrapositive, rendered), an out-of-phase button is DARK (the state
tooth = `exec_in_order`'s contrapositive — the SKIP tooth), and the `merge` button is dark except from
`approved` (the headline `merge_requires_approved`, rendered). Each is the EXISTING affordance refusal
(`fireGated_cap_fail_refuses` / `fireGated_state_fail_refuses`) specialized to the workflow gate. -/

/-- **THE CAP TOOTH (rendered `exec_authorized`).** An UNAUTHORIZED actor's gated step refuses — the
button is dark for anyone who is not the step's authorized party. (`exec_authorized` says a committed
`exec` step's actor IS authorized; here the contrapositive is rendered as the cap-gate refusal.) -/
theorem gated_cap_fail_is_unauthorized (actor : Party) (s : StepKind) (p : Phase) (ctx : TurnCtx)
    (sc post : Nat) (hunauth : actor ≠ authorizedParty s) :
    fireGated (stepGated s) (heldFor actor s) ctx (phaseCell p) (phaseCell p) sc post = none := by
  apply fireGated_cap_fail_refuses
  -- the cap-gate fails because `actor ≠ authorizedParty s` (heldFor gives `[]`, a non-empty req fails).
  show fireGate (stepRights s) (heldFor actor s) = false
  cases hc : fireGate (stepRights s) (heldFor actor s) with
  | false => rfl
  | true  => exact absurd ((capGate_iff_authorized actor s).mp hc) hunauth

/-- **THE SKIP TOOTH (rendered `exec_in_order`).** An OUT-OF-PHASE gated step refuses — the button is
dark unless the cell is in the step's `precond` phase. The choreography order is enforced by the deos
state-gate exactly as `exec_in_order` enforces it: you cannot fire a step's button from the wrong phase
(no merge before approval, rendered). -/
theorem gated_state_fail_is_out_of_order (actor : Party) (s : StepKind) (p : Phase) (ctx : TurnCtx)
    (sc post : Nat) (hskip : p ≠ precond s) :
    fireGated (stepGated s) (heldFor actor s) ctx (phaseCell p) (phaseCell p) sc post = none := by
  apply fireGated_state_fail_refuses
  -- the state-gate fails because `p ≠ precond s`.
  show (stateCond s).admitsCtx ctx 0 (phaseCell p) (phaseCell p) = false
  cases hc : (stateCond s).admitsCtx ctx 0 (phaseCell p) (phaseCell p) with
  | false => rfl
  | true  => exact absurd ((stateGate_iff_phase s p ctx).mp hc) hskip

/-- **THE HEADLINE, RENDERED (`merge_requires_approved`).** The `merge` button is DARK in every phase
except `approved`: the CI bot cannot fire merge before the reviewer's approval lands. This is
`Workflow.merge_requires_approved` rendered onto the deos surface — the skip tooth specialized to the
merge step, the "no merge without prior approval" guarantee as a dark button. -/
theorem gated_merge_requires_approved (actor : Party) (p : Phase) (ctx : TurnCtx) (sc post : Nat)
    (hp : p ≠ .approved) :
    fireGated (stepGated .merge) (heldFor actor .merge) ctx (phaseCell p) (phaseCell p) sc post = none := by
  apply gated_state_fail_is_out_of_order
  -- `precond .merge = .approved`, so `p ≠ .approved` IS `p ≠ precond .merge`.
  show p ≠ precond .merge
  exact hp

/-! ## §5 — THE PHASE TRANSITION IS A `ReactiveAffordance` (`precond → postPhase` IS the transition gate).

The workflow's phase ADVANCE — `precond s → postPhase s` — is the deos reactive button's `TransitionGate`.
`stepReactive s` packages the step's cap-gate with a transition gate whose `pre` requires the OLD cell in
`precond s`, whose `post` requires the NEW cell in `postPhase s`, and whose `link` ties BOTH together
(the relational pre→post edge a property of `new` alone cannot witness — the move is exactly this
choreography edge). The window is `[0, ∞)` (`closeHeight` large): a workflow advance is not deadline-gated
(that is the reactive layer's ADDITIONAL expressive power, not the workflow's), so the window never
refuses and the reactive fire's verdict is decided by the cap-gate and the transition gate alone. -/

/-- **`phaseTransitionGate s`** — the transition gate of step `s`: the old cell must be in `precond s`
(`pre`), the new cell in `postPhase s` (`post`), and the `link` ties BOTH (the relational
`precond s → postPhase s` edge, reading both records). The phase advance, as a reactive transition. -/
def phaseTransitionGate (s : StepKind) : TransitionGate where
  pre  := fun old => old.scalar "phase" == some (phaseCode (precond s))
  post := fun new => new.scalar "phase" == some (phaseCode (postPhase s))
  link := fun old new =>
    (old.scalar "phase" == some (phaseCode (precond s))) &&
    (new.scalar "phase" == some (phaseCode (postPhase s)))

/-- **`stepReactive s`** — THE RENDERING as a reactive button: the step's cap-gate (`stepCell s`) plus the
phase-transition gate (`phaseTransitionGate s`) plus a non-restrictive window `[0, 2^63]` (a workflow
advance is not deadline-gated). The "approve" reactive button fires the author/reviewer/CI cap AND the
`submitted → approved` move — the workflow's phase advance as a deos transition. -/
def stepReactive (s : StepKind) : ReactiveAffordance StepEffect :=
  { aff := stepCell s, gate := phaseTransitionGate s, openHeight := 0, closeHeight := 9223372036854775807 }

/-- The non-restrictive window admits every realistic turn height (`height ≤ 2^63 − 1`); we instantiate
it at any `height` within bound. The window is present for the reactive SHAPE but never refuses a workflow
advance — the verdict rides the cap and transition gates. -/
theorem stepReactive_inWindow (s : StepKind) {height : Nat} (h : height ≤ 9223372036854775807) :
    inWindow (stepReactive s) height = true := by
  rw [Dregg2.Deos.Reactive.inWindow_iff]
  exact ⟨Nat.zero_le _, h⟩

/-- The transition gate fires EXACTLY on the `precond s → postPhase s` move between phase cells:
`transitionOK (phaseTransitionGate s) (phaseCell pold) (phaseCell pnew) = true ↔ pold = precond s ∧
pnew = postPhase s`. The relational edge, decided by both endpoints' phases. -/
theorem phaseTransitionGate_iff (s : StepKind) (pold pnew : Phase) :
    transitionOK (phaseTransitionGate s) (phaseCell pold) (phaseCell pnew) = true ↔
      (pold = precond s ∧ pnew = postPhase s) := by
  rw [Dregg2.Deos.Reactive.transitionOK_iff]
  unfold phaseTransitionGate
  simp only [phaseCell_scalar, beq_iff_eq, Option.some.injEq, Bool.and_eq_true]
  constructor
  · rintro ⟨hpre, hpost, _⟩
    exact ⟨phaseCode_inj hpre, phaseCode_inj hpost⟩
  · rintro ⟨hpre, hpost⟩
    subst hpre; subst hpost
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- **`phaseTransition_is_reactiveAffordance` — THE KEYSTONE (the phase advance IS the transition gate).**
The reactive fire of `stepReactive s` (at any in-window height) commits if and only if the actor is the
step's authorized party AND the cell move is exactly `precond s → postPhase s`. The workflow's phase
transition IS the deos reactive transition gate — the choreography edge, rendered, with the cap-gate
biting on authorization. -/
theorem phaseTransition_is_reactiveAffordance (actor : Party) (s : StepKind) (pold pnew : Phase)
    {height : Nat} (hh : height ≤ 9223372036854775807) (sc post : Nat) :
    (fireReactive (stepReactive s) (heldFor actor s) height (phaseCell pold) (phaseCell pnew) sc post).isSome = true ↔
      (actor = authorizedParty s ∧ pold = precond s ∧ pnew = postPhase s) := by
  rw [fireReactive_iff]
  -- `stepReactive s` has `.aff.required = stepRights s`, `.gate = phaseTransitionGate s`.
  show (fireGate (stepRights s) (heldFor actor s) = true ∧
        transitionOK (phaseTransitionGate s) (phaseCell pold) (phaseCell pnew) = true ∧
        inWindow (stepReactive s) height = true) ↔ _
  rw [capGate_iff_authorized, phaseTransitionGate_iff]
  rw [show inWindow (stepReactive s) height = true from stepReactive_inWindow s hh]
  simp only [and_true]

/-- **THE TRANSITION TOOTH (a property of `new` alone cannot witness the edge).** The SAME destination
phase `pnew = postPhase s`, reached from a WRONG old phase `pold ≠ precond s`, REFUSES — even with the
cap and the window. The deos reactive gate checks the SHAPE of the move (`precond s → postPhase s`), not
just that the cell LANDED in `postPhase s`: you cannot reach `approved` by a non-`submitted→approved`
move. This is the reactive analogue of the skip tooth — the relational edge `Workflow` enforces by
`exec_in_order`, now as the transition `link`. -/
theorem reactive_wrong_phase_refuses (actor : Party) (s : StepKind) (pold pnew : Phase) (height : Nat)
    (sc post : Nat) (hwrong : pold ≠ precond s) :
    fireReactive (stepReactive s) (heldFor actor s) height (phaseCell pold) (phaseCell pnew) sc post = none := by
  apply fireReactive_transition_fail_refuses
  -- the transition gate fails: `pre (phaseCell pold)` is false since `pold ≠ precond s`.
  show transitionOK (phaseTransitionGate s) (phaseCell pold) (phaseCell pnew) = false
  cases hc : transitionOK (phaseTransitionGate s) (phaseCell pold) (phaseCell pnew) with
  | false => rfl
  | true  => exact absurd ((phaseTransitionGate_iff s pold pnew).mp hc).1 hwrong

/-! ## §6 — BITING `#guard` TEETH (both polarities), the worked 3-party review/CI workflow.

The demo: author (party 0) submits → reviewer (party 1) approves → CI bot (party 2) merges. The deos
surface RENDERS each step as a gated/reactive button; the witnesses below show every corner bites: the
authorized actor in the right phase FIRES, an unauthorized actor REFUSES (cap tooth), an out-of-phase
fire REFUSES (skip tooth), and the reactive transition tooth refuses the right destination reached from a
wrong old phase. -/

section Witnesses

-- Pre/post-state commitments and a turn height for the witnesses (concrete, immaterial values).
private def sc0 : Nat := 100
private def post0 : Nat := 110
private def h0 : Nat := 15

-- ══════════ THE GATED BUTTON: authorized ∧ in-phase ⇒ FIRES (the only firing corner per step) ══════════

-- author (0) submits from `init` ⇒ FIRES:
#guard (fireGated (stepGated .submit) (heldFor 0 .submit) TurnCtx.empty
          (phaseCell .init) (phaseCell .init) sc0 post0).isSome
-- reviewer (1) approves from `submitted` ⇒ FIRES:
#guard (fireGated (stepGated .approve) (heldFor 1 .approve) TurnCtx.empty
          (phaseCell .submitted) (phaseCell .submitted) sc0 post0).isSome
-- CI (2) merges from `approved` ⇒ FIRES:
#guard (fireGated (stepGated .merge) (heldFor 2 .merge) TurnCtx.empty
          (phaseCell .approved) (phaseCell .approved) sc0 post0).isSome

-- ══════════ THE CAP TOOTH: the WRONG actor's button is DARK (even in the right phase) ══════════

-- reviewer (1) cannot submit (only the author may) — DARK even from `init`:
#guard (fireGated (stepGated .submit) (heldFor 1 .submit) TurnCtx.empty
          (phaseCell .init) (phaseCell .init) sc0 post0).isNone
-- author (0) cannot approve (only the reviewer may) — DARK even from `submitted`:
#guard (fireGated (stepGated .approve) (heldFor 0 .approve) TurnCtx.empty
          (phaseCell .submitted) (phaseCell .submitted) sc0 post0).isNone
-- the author (0) cannot merge (only the CI bot may) — DARK even from `approved`:
#guard (fireGated (stepGated .merge) (heldFor 0 .merge) TurnCtx.empty
          (phaseCell .approved) (phaseCell .approved) sc0 post0).isNone

-- ══════════ THE SKIP TOOTH: the right actor's button is DARK in the WRONG phase ══════════

-- the CI bot (2) cannot merge from `init` (no merge before approval) — DARK (the headline):
#guard (fireGated (stepGated .merge) (heldFor 2 .merge) TurnCtx.empty
          (phaseCell .init) (phaseCell .init) sc0 post0).isNone
-- the CI bot (2) cannot merge from `submitted` either — DARK until `approved`:
#guard (fireGated (stepGated .merge) (heldFor 2 .merge) TurnCtx.empty
          (phaseCell .submitted) (phaseCell .submitted) sc0 post0).isNone
-- the reviewer (1) cannot approve from `init` (must wait for submit) — DARK:
#guard (fireGated (stepGated .approve) (heldFor 1 .approve) TurnCtx.empty
          (phaseCell .init) (phaseCell .init) sc0 post0).isNone

-- a committed gated fire carries the REAL step as its effect and binds the new root (110):
#guard match fireGated (stepGated .submit) (heldFor 0 .submit) TurnCtx.empty
                (phaseCell .init) (phaseCell .init) sc0 post0 with
       | some i => (i.surface.firedEffect == StepKind.submit) && (i.surface.boundRoot == post0)
       | none   => false

-- ══════════ THE REACTIVE BUTTON: the phase ADVANCE fires on exactly the choreography edge ══════════

-- author (0): the `init → submitted` move at height 15 ⇒ FIRES:
#guard (fireReactive (stepReactive .submit) (heldFor 0 .submit) h0
          (phaseCell .init) (phaseCell .submitted) sc0 post0).isSome
-- reviewer (1): the `submitted → approved` move ⇒ FIRES:
#guard (fireReactive (stepReactive .approve) (heldFor 1 .approve) h0
          (phaseCell .submitted) (phaseCell .approved) sc0 post0).isSome
-- CI (2): the `approved → merged` move ⇒ FIRES:
#guard (fireReactive (stepReactive .merge) (heldFor 2 .merge) h0
          (phaseCell .approved) (phaseCell .merged) sc0 post0).isSome

-- THE TRANSITION TOOTH: the SAME destination `approved` from the WRONG old phase `init` (not the
-- `submitted → approved` edge) REFUSES — a property of `new` alone (it IS `approved`) cannot witness it:
#guard (fireReactive (stepReactive .approve) (heldFor 1 .approve) h0
          (phaseCell .init) (phaseCell .approved) sc0 post0).isNone
-- and merging to `merged` from `submitted` (skipping `approved`) REFUSES (the choreography edge is checked):
#guard (fireReactive (stepReactive .merge) (heldFor 2 .merge) h0
          (phaseCell .submitted) (phaseCell .merged) sc0 post0).isNone

-- THE REACTIVE CAP TOOTH: the wrong actor cannot fire the advance even on the right edge:
#guard (fireReactive (stepReactive .approve) (heldFor 0 .approve) h0
          (phaseCell .submitted) (phaseCell .approved) sc0 post0).isNone

end Witnesses

/-! ## §7 — Axiom hygiene. -/

#assert_all_clean [
  capGate_iff_authorized,
  stateGate_iff_phase,
  workflowStep_is_gatedAffordance,
  workflow_fires_iff_affordance_fires,
  gated_cap_fail_is_unauthorized,
  gated_state_fail_is_out_of_order,
  gated_merge_requires_approved,
  phaseTransitionGate_iff,
  phaseTransition_is_reactiveAffordance,
  reactive_wrong_phase_refuses
]

/- The umbrella import line for `Dregg2/Deos.lean` (NOT edited by this lane) is recorded in this
module's header docstring (§"Umbrella import line"). -/

end Dregg2.Deos.WorkflowBridge
