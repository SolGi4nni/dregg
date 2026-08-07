/-
# Dregg2.Deos.FireProgramAgreement — the fire→CellProgram seam: the surface state-gate and the
EXECUTOR's installed-program gate provably DECIDE THE SAME TRANSITIONS, so a darkened affordance
cannot be bypassed by firing the turn straight at the executor.

`Dregg2.Deos.{GatedAffordance, WorkflowBridge}` (the deos surface) + `Dregg2.Circuit.Argus.Policy`
(the executor's installed-policy enforcement).

THE GAP THIS CLOSES. Two gates over the SAME installed `RecordProgram` grew up apart, each proven on
its own side:

  * THE SURFACE GATE — `GatedAffordance.fireGated ga held ctx old new`. Its state leg is
    `ga.stateCond.admitsCtx ctx ga.method old new` (`RecordProgram.admitsCtx`, i.e. `evalConstraintCtx`).
    `fireGated_iff` is the surface keystone: the deos button lights IFF caps AND state both pass; the
    darkening teeth are `fireGated_state_fail_refuses` (the surface) and `gated_state_fail_is_out_of_order`
    (the workflow rendering).
  * THE EXECUTOR GATE — `Argus.Policy.policyGuarded view prog w s`. It runs the cell's INSTALLED program
    `prog : List StateConstraint` over the same `(old, new)` slot view via `programToGuard`
    (→ `constraintToGuard` → `evalConstraint`), and `policyGuarded_reject` is fail-closed: no effect
    commits unless every installed constraint admits.

What nobody had SHOWN is that these two gates, fed the SAME installed program, decide the SAME
transitions. Without that, "a gated affordance cannot be bypassed" is only TESTED: the surface
darkening and the executor refusal happen to coincide on the worked examples, but a malicious client
who skips the surface and fires the turn STRAIGHT at the executor has no PROVEN wall. This module is
that wall — the surface state-gate and the executor program-gate are the SAME predicate, both reducing
to `cs.all (evalConstraint · old new)` over the installed program, so the executor RE-ENFORCES exactly
what the surface would have refused.

THE BRIDGE (what is proven). For an installed program `cs : List StateConstraint` whose constraints
are all `locallyDecidable` (the first-party arms — every catalog atom except the cross-cell `boundDelta`,
which the single-cell evaluator routes to the §8 verify seam rather than the live gate), and any slot
`view` presenting the cell's `(old, new)` records:

  * §2 `installedProgram_gate_eq_surface_stateGate` (KEYSTONE) — the EXECUTOR program-gate verdict
    `(programToGuard view cs).admits k w` EQUALS the SURFACE state-gate verdict
    `(RecordProgram.predicate cs).admitsCtx TurnCtx.empty method (view k).1 (view k).2`. Same installed
    program ⇒ same verdict; both are `cs.all (evalConstraint · (view k).1 (view k).2)`. The two gates
    are not merely tested-equal — they ARE the same Boolean.
  * §3 `bypass_refused_by_executor` (THE BYPASS-IMPOSSIBILITY THEOREM) — if the SURFACE darkens a fire
    on STATE grounds (the installed program rejects the slot transition), then the EXECUTOR's
    installed-program-gated effect ALSO refuses (`policyGuarded … = none`), REGARDLESS of the effect
    body. A turn the surface would not light cannot be slipped past the executor: the kernel re-enforces
    the installed program on the fired turn. (`surface_dark_iff_executor_refuses` packages the iff.)
  * §4 the WORKFLOW specialization — `workflow_out_of_phase_bypass_refused`: a workflow step fired from
    the WRONG phase (the surface's `gated_state_fail_is_out_of_order` darkening) is refused by the
    executor running the step's installed phase-precondition program `[stateCond-as-constraint]`. The
    "no merge before approval" dark button is ALSO a "no merge before approval" executor refusal.
  * §5 BITING `#guard`/theorem teeth: a concrete installed `memberOf` program where the surface lights
    (role ∈ allowlist) and the executor admits, and darkens (role ∉ allowlist) and the executor
    refuses — the SAME verdict on both sides, both polarities.

This is NOT new mathematics and NOT a third gate. The surface state-gate is the REAL
`RecordProgram.admitsCtx`; the executor gate is the REAL `Argus.Policy.policyGuarded`; the agreement is
the EXISTING `constraintToGuard_firstParty_eval` (executor per-constraint = `evalConstraint`) conjoined
list-wise and met against the EXISTING `admitsCtx_empty` (`admitsCtx TurnCtx.empty = admits` reduces a
`predicate` program to the same `cs.all evalConstraint`). The weld, not a build.

THE CTX SCOPE (honest). The executor's installed-program path (`constraintToGuard`) routes through the
ctx-LESS `evalConstraint` — exactly what `turn/`'s program-check runs for the first-party catalog. The
agreement is therefore stated at the surface's `TurnCtx.empty` specialization (`admitsCtx_empty`), the
faithful match: the context atoms (`senderIs`/`balance…`) are the ctx-aware EXTENSION both sides fail
closed on under the empty context, and a turn-context-bearing executor gate is the lift the convergence
carries forward — not weakened here, scoped honestly.

Discipline: `#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); NON-VACUOUS (§5 exhibits both verdicts). `lake build
Dregg2.Deos.FireProgramAgreement` green (LOCAL). NO core edit, NO sibling edit — imports are READ-ONLY.
-/
import Dregg2.Deos.WorkflowBridge
import Dregg2.Circuit.Argus.Policy

namespace Dregg2.Deos.FireProgramAgreement

open Dregg2.Exec (RecordProgram StateConstraint SimpleConstraint TurnCtx Value evalConstraint
  RecordKernelState)
open Dregg2.Spec (Guard)
open Dregg2.Laws (Verifiable)
open Dregg2.Circuit.Argus (constraintToGuard programToGuard policyGuarded locallyDecidable
  constraintToGuard_firstParty_eval policyGuarded_reject)
open Dregg2.Deos.Affordance (FireCtx)
open Dregg2.Deos.GatedAffordance (GatedAffordance fireGated fireGated_iff fireGated_state_fail_refuses)

set_option linter.dupNamespace false

/-! ## §1 — THE TWO GATES REDUCE TO THE SAME `evalConstraint` CONJUNCTION.

The surface state-gate `(RecordProgram.predicate cs).admitsCtx TurnCtx.empty m old new` is
`cs.all (evalConstraintCtx TurnCtx.empty · old new)` (the `predicate` arm), which is
`cs.all (evalConstraint · old new)` by `evalConstraintCtx_empty`. The executor program-gate
`(programToGuard view cs).admits k w` is the `Guard.all` meet of each `constraintToGuard view c`,
which (for `locallyDecidable` constraints) is `evalConstraint c (view k).1 (view k).2`. We prove the
executor gate equals that same conjunction by list induction, then meet the two against the surface
side. -/

/-- **`executorGate_eq_all_eval`** — the EXECUTOR's routed program-gate over an all-locally-decidable
installed program is exactly the `evalConstraint` conjunction on the slot view: `(programToGuard view
cs).admits k w = cs.all (fun c => evalConstraint c (view k).1 (view k).2)`. The meet of the routed
first-party guards IS the conjunction of the live-leg checks (each `constraintToGuard view c` reduces
by `constraintToGuard_firstParty_eval`). -/
theorem executorGate_eq_all_eval [Verifiable Dregg2.Circuit.Argus.ObligationStmt Witness]
    (view : RecordKernelState → Value × Value) (cs : List StateConstraint)
    (hloc : ∀ c ∈ cs, locallyDecidable c = true)
    (k : RecordKernelState) (w : Dregg2.Circuit.Argus.ObligationStmt → Witness) :
    (programToGuard view cs).admits k w
      = cs.all (fun c => evalConstraint c (view k).1 (view k).2) := by
  unfold programToGuard
  rw [Guard.admits_all_eq]
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.map_cons, Guard.admitsAll_cons, List.all_cons]
    have hc : (constraintToGuard view c).admits k w
        = evalConstraint c (view k).1 (view k).2 :=
      constraintToGuard_firstParty_eval view c (hloc c (by simp)) k w
    rw [hc, ih (fun c hcm => hloc c (by simp [hcm]))]

/-- **`surfaceStateGate_eq_all_eval`** — the SURFACE state-gate over the SAME installed program (a
`predicate` `RecordProgram`) under the empty context is the SAME `evalConstraint` conjunction:
`(RecordProgram.predicate cs).admitsCtx TurnCtx.empty m old new = cs.all (evalConstraint · old new)`.
The `predicate` arm of `admitsCtx` ANDs `evalConstraintCtx`, and `evalConstraintCtx_empty` collapses
each to `evalConstraint`. -/
theorem surfaceStateGate_eq_all_eval (cs : List StateConstraint) (m : Nat) (old new : Value) :
    (RecordProgram.predicate cs).admitsCtx TurnCtx.empty m old new
      = cs.all (fun c => evalConstraint c old new) := by
  -- `admitsCtx` on a `predicate` is `cs.all (evalConstraintCtx empty · old new)`; collapse each atom.
  show (cs.all (fun c => Dregg2.Exec.evalConstraintCtx TurnCtx.empty c old new))
      = cs.all (fun c => evalConstraint c old new)
  exact congrArg cs.all (funext fun c => Dregg2.Exec.evalConstraintCtx_empty c old new)

/-! ## §2 — THE KEYSTONE: the executor's installed-program gate IS the surface state-gate. -/

/-- **`installedProgram_gate_eq_surface_stateGate` — THE KEYSTONE.** For one installed program `cs`
(all-locally-decidable) and the slot `view` presenting `(old, new) = (view k).1, (view k).2`, the
EXECUTOR program-gate verdict EQUALS the SURFACE state-gate verdict:

    (programToGuard view cs).admits k w
      = (RecordProgram.predicate cs).admitsCtx TurnCtx.empty method (view k).1 (view k).2

The two gates are the SAME Boolean — both `cs.all (evalConstraint · (view k))`. So the surface gate and
the kernel gate are PROVEN-equal, not merely tested-equal: whatever the deos button decides on state
grounds, the executor decides identically on the fired turn. -/
theorem installedProgram_gate_eq_surface_stateGate
    [Verifiable Dregg2.Circuit.Argus.ObligationStmt Witness]
    (view : RecordKernelState → Value × Value) (cs : List StateConstraint)
    (hloc : ∀ c ∈ cs, locallyDecidable c = true) (method : Nat)
    (k : RecordKernelState) (w : Dregg2.Circuit.Argus.ObligationStmt → Witness) :
    (programToGuard view cs).admits k w
      = (RecordProgram.predicate cs).admitsCtx TurnCtx.empty method (view k).1 (view k).2 := by
  rw [executorGate_eq_all_eval view cs hloc k w,
      surfaceStateGate_eq_all_eval cs method (view k).1 (view k).2]

/-! ## §3 — BYPASS-IMPOSSIBILITY: a fire the SURFACE darkens on state grounds is REFUSED by the EXECUTOR.

The threat is a malicious client who skips the deos surface and fires the turn STRAIGHT at the executor.
The defense is that the executor RE-ENFORCES the installed program. We prove it: if the SURFACE state-gate
fails (the installed `cs` rejects the slot transition the button reads), then the EXECUTOR's
installed-program-gated effect `policyGuarded view cs w s` REFUSES (`= none`), for ANY effect body `s`.
The surface darkening and the executor refusal are the SAME decision (the §2 keystone), so a darkened
affordance has a PROVEN wall, not a tested coincidence. -/

/-- **`bypass_refused_by_executor` — THE BYPASS-IMPOSSIBILITY THEOREM.** Suppose the SURFACE state-gate
over the installed program `cs` darkens the fire at this slot — the program REJECTS the `(view k)`
transition the button reads (`(RecordProgram.predicate cs).admitsCtx TurnCtx.empty method (view k).1
(view k).2 = false`). Then the EXECUTOR's installed-program-gated effect REFUSES for ANY effect body
`s`: `interp (policyGuarded view cs w s) k = none`. The fired turn cannot bypass the surface gate by
going straight to the executor — the kernel re-enforces the SAME installed program and fails closed. -/
theorem bypass_refused_by_executor [Verifiable Dregg2.Circuit.Argus.ObligationStmt Witness]
    (view : RecordKernelState → Value × Value) (cs : List StateConstraint)
    (hloc : ∀ c ∈ cs, locallyDecidable c = true) (method : Nat)
    (k : RecordKernelState) (w : Dregg2.Circuit.Argus.ObligationStmt → Witness)
    (s : Dregg2.Circuit.Argus.RecStmt)
    (hdark : (RecordProgram.predicate cs).admitsCtx TurnCtx.empty method (view k).1 (view k).2 = false) :
    Dregg2.Circuit.Argus.interp (policyGuarded view cs w s) k = none := by
  apply policyGuarded_reject
  -- the executor gate equals the (failing) surface gate by the §2 keystone.
  rw [installedProgram_gate_eq_surface_stateGate view cs hloc method k w]
  exact hdark

/-- **`surface_dark_iff_executor_refuses` (the iff, both polarities).** The SURFACE state-gate darkens
the fire IFF the EXECUTOR's installed-program-gated effect refuses on state grounds — equivalently, the
EXECUTOR ADMITS the installed program IFF the SURFACE state-gate lights. The two gates agree in BOTH
directions: no state the surface lights is refused by the executor's program-gate, and no state the
surface darkens is admitted. (Stated on the program-gate verdict; the §3 commit-side direction rides
`policyGuarded_commit_iff`.) -/
theorem surface_dark_iff_executor_refuses
    [Verifiable Dregg2.Circuit.Argus.ObligationStmt Witness]
    (view : RecordKernelState → Value × Value) (cs : List StateConstraint)
    (hloc : ∀ c ∈ cs, locallyDecidable c = true) (method : Nat)
    (k : RecordKernelState) (w : Dregg2.Circuit.Argus.ObligationStmt → Witness) :
    (programToGuard view cs).admits k w = false
      ↔ (RecordProgram.predicate cs).admitsCtx TurnCtx.empty method (view k).1 (view k).2 = false := by
  rw [installedProgram_gate_eq_surface_stateGate view cs hloc method k w]

/-! ## §3a — THE SURFACE SIDE, MADE EXPLICIT: the darkened button and the refusing executor SHARE
the installed program.

`fireGated_state_fail_refuses` (the surface tooth) darkens the button when its `stateCond` state-gate
fails. When that `stateCond` IS the installed `RecordProgram.predicate cs` and `ctx = TurnCtx.empty`,
the SAME failing-state hypothesis darkens the button AND (via §3) refuses the executor — one predicate,
two gates, both dark. -/

/-- **`gated_surface_and_executor_both_dark` (the surface button AND the executor, one program).**
Take a `GatedAffordance` whose state-gate IS the installed program (`ga.stateCond = .predicate cs`,
`ga.method = method`), fired against the slot `(view k)` the executor reads. If the installed program
REJECTS that transition, BOTH gates are dark: the deos button refuses (`fireGated … = none`) AND the
executor refuses (`policyGuarded … = none`). The bypass route (skip the button, fire at the executor)
hits the SAME wall — the installed program is enforced on both sides. -/
theorem gated_surface_and_executor_both_dark
    [Verifiable Dregg2.Circuit.Argus.ObligationStmt Witness] {φ : Type}
    (view : RecordKernelState → Value × Value) (cs : List StateConstraint)
    (hloc : ∀ c ∈ cs, locallyDecidable c = true) (method : Nat)
    (k : RecordKernelState) (w : Dregg2.Circuit.Argus.ObligationStmt → Witness)
    (s : Dregg2.Circuit.Argus.RecStmt)
    (ga : GatedAffordance φ) (held : List Dregg2.Authority.Auth) (fc : FireCtx φ)
    (hcond : ga.stateCond = .predicate cs) (hmeth : ga.method = method)
    (hdark : (RecordProgram.predicate cs).admitsCtx TurnCtx.empty method (view k).1 (view k).2 = false) :
    fireGated ga held TurnCtx.empty (view k).1 (view k).2 fc = none
      ∧ Dregg2.Circuit.Argus.interp (policyGuarded view cs w s) k = none := by
  refine ⟨?_, bypass_refused_by_executor view cs hloc method k w s hdark⟩
  -- the surface button: its state-gate IS the installed program at this slot, which fails.
  apply fireGated_state_fail_refuses
  rw [hcond, hmeth]; exact hdark

/-! ## §4 — THE WORKFLOW SPECIALIZATION: an out-of-phase step the surface darkens is REFUSED by the
executor running the step's installed phase-precondition program.

`WorkflowBridge.stateCond s` is the step's installed phase-gate `phase == precond s` (a one-constraint
`RecordProgram.predicate [phaseConstraint s]`). The surface darkens an out-of-phase step
(`gated_state_fail_is_out_of_order`); here we show the EXECUTOR, running that SAME one-constraint
installed program over the phase-cell slot, ALSO refuses. The "no merge before approval" dark button is
a "no merge before approval" executor refusal — the choreography order enforced on BOTH sides. -/

open Dregg2.Protocol.Workflow (Phase StepKind precond)
open Dregg2.Deos.WorkflowBridge (phaseCode phaseCell stateGate_iff_phase)

/-- The step `s`'s installed phase-precondition program as a `List StateConstraint`: the single
`fieldEquals "phase" (phaseCode (precond s))` the `WorkflowBridge.stateCond s` packages. The executor
installs exactly this to gate the step on its choreography precondition. -/
def stepConstraints (s : StepKind) : List StateConstraint :=
  [.simple (.fieldEquals "phase" (phaseCode (precond s)))]

/-- A single `fieldEquals` is locally decidable (it is not the cross-cell `boundDelta`), so the step's
installed program routes entirely to the first-party live-leg gate — the §2 keystone applies. -/
theorem stepConstraints_locallyDecidable (s : StepKind) :
    ∀ c ∈ stepConstraints s, locallyDecidable c = true := by
  intro c hc
  simp only [stepConstraints, List.mem_singleton] at hc
  subst hc; rfl

/-- The step's installed phase-program, as a `predicate` `RecordProgram`, IS `WorkflowBridge.stateCond
s`. So "the executor installs `stepConstraints s`" and "the surface's state-gate is `stateCond s`" are
the SAME program — the precondition for the §2 keystone to weld the two gates on the workflow. -/
theorem stepConstraints_eq_stateCond (s : StepKind) :
    (RecordProgram.predicate (stepConstraints s)) = Dregg2.Deos.WorkflowBridge.stateCond s := rfl

/-- **`workflow_out_of_phase_bypass_refused` (THE CHOREOGRAPHY WALL, executor side).** A workflow step
`s` fired from the WRONG phase `p ≠ precond s` — the surface's `gated_state_fail_is_out_of_order`
darkening — is REFUSED by the EXECUTOR running the step's installed phase-precondition program
`stepConstraints s` over the phase-cell slot `(phaseCell p, phaseCell p)`, for ANY effect body. The
out-of-phase button is dark AND the out-of-phase turn fired straight at the executor fails closed: the
choreography order is re-enforced by the kernel, not just rendered. -/
theorem workflow_out_of_phase_bypass_refused
    [Verifiable Dregg2.Circuit.Argus.ObligationStmt Witness]
    (s : StepKind) (p : Phase) (method : Nat)
    (k : RecordKernelState) (w : Dregg2.Circuit.Argus.ObligationStmt → Witness)
    (eff : Dregg2.Circuit.Argus.RecStmt)
    (hwrong : p ≠ precond s) :
    Dregg2.Circuit.Argus.interp
        (policyGuarded (fun _ => (phaseCell p, phaseCell p)) (stepConstraints s) w eff) k = none := by
  apply bypass_refused_by_executor (fun _ => (phaseCell p, phaseCell p)) (stepConstraints s)
    (stepConstraints_locallyDecidable s) method k w eff
  -- the constant view's `(·).1`/`(·).2` reduce to `(phaseCell p, phaseCell p)`; the installed
  -- phase-program IS `stateCond s`, which `stateGate_iff_phase` admits iff `p = precond s` — false here.
  show (RecordProgram.predicate (stepConstraints s)).admitsCtx TurnCtx.empty method
      (phaseCell p) (phaseCell p) = false
  rw [stepConstraints_eq_stateCond]
  cases hc : (Dregg2.Deos.WorkflowBridge.stateCond s).admitsCtx TurnCtx.empty method
      (phaseCell p) (phaseCell p) with
  | false => rfl
  | true  => exact absurd ((stateGate_iff_phase s p TurnCtx.empty).mp hc) hwrong

/-! ## §5 — NON-VACUITY: the SAME installed program, the SAME verdict on BOTH gates, both polarities.

A concrete installed `memberOf "role" [1,2,3]` program. On a satisfier slot (`role = 2`) the SURFACE
state-gate LIGHTS and the EXECUTOR program-gate ADMITS; on a violator slot (`role = 9`) the surface
DARKENS and the executor REFUSES. Same verdict, both sides, both polarities — the agreement is two-valued
and the wall bites. -/

section Witnesses

open Dregg2.Exec (RecordKernelState)

/-- The installed program: `role ∈ {1,2,3}` (a single `memberOf` mandate, locally decidable). -/
def roleProg : List StateConstraint := [.simple (.memberOf "role" [1, 2, 3])]

theorem roleProg_loc : ∀ c ∈ roleProg, locallyDecidable c = true := by
  intro c hc; simp only [roleProg, List.mem_singleton] at hc; subst hc; rfl

/-- A slot whose `role = 2` (in the allowlist) — the SATISFIER. -/
def roleOkCell : Value := .record [("role", .int 2)]
/-- A slot whose `role = 9` (not in the allowlist) — the VIOLATOR. -/
def roleBadCell : Value := .record [("role", .int 9)]

/-- A kernel whose cell `0` carries `role = 2`. -/
def kOk : RecordKernelState :=
  { accounts := {0}, cell := fun _ => roleOkCell, caps := fun _ => [] }
/-- A kernel whose cell `0` carries `role = 9`. -/
def kBad : RecordKernelState :=
  { accounts := {0}, cell := fun _ => roleBadCell, caps := fun _ => [] }

/-- The slot view reading cell `0` as both `old` and `new` (absolute `memberOf`). -/
def cell0AbsView (k : RecordKernelState) : Value × Value := (k.cell 0, k.cell 0)

-- THE SURFACE state-gate (admitsCtx) and the EXECUTOR program-gate (programToGuard.admits) agree:
-- SATISFIER ⇒ BOTH admit (the button lights, the executor admits).
#guard ((RecordProgram.predicate roleProg).admitsCtx TurnCtx.empty 0 roleOkCell roleOkCell)
#guard ((programToGuard cell0AbsView roleProg).admits kOk (fun _ => ()))
-- VIOLATOR ⇒ BOTH refuse (the button darkens, the executor refuses).
#guard ((RecordProgram.predicate roleProg).admitsCtx TurnCtx.empty 0 roleBadCell roleBadCell) == false
#guard ((programToGuard cell0AbsView roleProg).admits kBad (fun _ => ())) == false

/-- **`agreement_nonvacuous` (the SAME verdict on both gates, both polarities).** On the SATISFIER both
the surface state-gate and the executor program-gate ADMIT; on the VIOLATOR both REFUSE. The two gates
decide identically AND the decision is two-valued — the agreement keystone is non-vacuous (the gates are
not both-always-true). -/
theorem agreement_nonvacuous :
    -- satisfier: surface lights ∧ executor admits
    ((RecordProgram.predicate roleProg).admitsCtx TurnCtx.empty 0 roleOkCell roleOkCell = true
      ∧ (programToGuard cell0AbsView roleProg).admits kOk (fun _ => ()) = true)
    -- violator: surface darkens ∧ executor refuses
    ∧ ((RecordProgram.predicate roleProg).admitsCtx TurnCtx.empty 0 roleBadCell roleBadCell = false
      ∧ (programToGuard cell0AbsView roleProg).admits kBad (fun _ => ()) = false) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · decide
  · rw [executorGate_eq_all_eval cell0AbsView roleProg roleProg_loc kOk (fun _ => ())]; decide
  · decide
  · rw [executorGate_eq_all_eval cell0AbsView roleProg roleProg_loc kBad (fun _ => ())]; decide

/-- **`gates_agree_pointwise` (the keystone, witnessed concretely).** At the satisfier kernel `kOk`,
the executor program-gate verdict EQUALS the surface state-gate verdict on the same slot — the §2
keystone, instantiated end-to-end on a real installed `memberOf` program. -/
theorem gates_agree_pointwise :
    (programToGuard cell0AbsView roleProg).admits kOk (fun _ => ())
      = (RecordProgram.predicate roleProg).admitsCtx TurnCtx.empty 0
          (cell0AbsView kOk).1 (cell0AbsView kOk).2 :=
  installedProgram_gate_eq_surface_stateGate cell0AbsView roleProg roleProg_loc 0 kOk (fun _ => ())

end Witnesses

/-! ## §6 — Axiom hygiene. -/

#assert_all_clean [
  executorGate_eq_all_eval,
  surfaceStateGate_eq_all_eval,
  installedProgram_gate_eq_surface_stateGate,
  bypass_refused_by_executor,
  surface_dark_iff_executor_refuses,
  gated_surface_and_executor_both_dark,
  stepConstraints_locallyDecidable,
  workflow_out_of_phase_bypass_refused,
  agreement_nonvacuous,
  gates_agree_pointwise
]

end Dregg2.Deos.FireProgramAgreement
