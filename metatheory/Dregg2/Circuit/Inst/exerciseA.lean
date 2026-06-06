/-
# Dregg2.Circuit.Inst.exerciseA — the v1 (`EffectCommit`) instance for the composite `exerciseA`
hold-gate (kernel frozen, authority receipt prepended).

`exerciseA` is a COMPOSITE meta-action: the outer `exerciseStepA` hold-gate checks `exerciseGuard`
(actor holds SOME cap conferring an edge to `target`), prepends `authReceipt actor`, and LITERALLY
freezes the entire kernel. The inner `List FullActionA` fold runs from `exerciseHoldState` and is
NOT arithmetized here — it is composed via a parameterized inner-turn hypothesis.

SPECIAL (outer hold layer only — identical shape to `pipelinedSendA`, but fail-closed guard):
  * `touched = ∅` (empty `Finset`);
  * `expectedLeaf = fun s _ c => s.kernel.cell c` (identity; unused when `T` empty);
  * `logUpdate = some (fun s a => authReceipt a.actor :: s.log)`;
  * `guardProp := exerciseGuard` (hold-gate ONLY — R4 facet-mask deferred).

THE VALIDATION: `exerciseA_full_sound ⇒ ExerciseHoldSpec` THROUGH the v1 framework. The composite
refinement theorems `exercise_circuit_refines_spec` / `exercise_circuit_refines_exec` compose the
hold-layer circuit with an inner `innerTurnH` hypothesis and `execFullA_exerciseA_iff_spec`.

ADDITIVE: imports `EffectCommit` + `ActionDispatch` + `Spec.exercise`; edits none of them.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit
import Dregg2.Circuit.ActionDispatch
import Dregg2.Circuit.Spec.exercise

namespace Dregg2.Circuit.Inst.ExerciseA

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.ActionDispatch
open Dregg2.Circuit.Spec.Exercise
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`propBit` at wire `0`).

The hold-gate exposes its guard as a `Prop` (`exerciseGuard`), not a per-gate circuit, so we commit
it as ONE `propBit` column at wire `0` (guardWidth = 1) and decode via `propBit = 1 ↔ p`. -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `exerciseE` instance (touched set = `∅`, log-only hold-gate). -/

/-- The exercise hold-gate arguments: the acting principal and the cap-edge target. -/
structure ExerciseHoldArgs where
  actor  : CellId
  target : CellId

/-- The full composite arguments (hold + inner turn), for refinement-layer naming. -/
structure ExerciseFullArgs where
  actor  : CellId
  target : CellId
  inner  : List FullActionA

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The exercise hold-gate guard as a `Prop` (the dispatcher's `exerciseGuard`). -/
def exerciseGuardProp (s : RecChainedState) (args : ExerciseHoldArgs) : Prop :=
  exerciseGuard s args.actor args.target

instance (s : RecChainedState) (args : ExerciseHoldArgs) : Decidable (exerciseGuardProp s args) := by
  unfold exerciseGuardProp exerciseGuard; exact inferInstanceAs (Decidable (_ = _))

/-- The guard's witness generator: lay the single `propBit` column at wire `0`. -/
def exerciseGuardEncode (s : RecChainedState) (args : ExerciseHoldArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (exerciseGuardProp s args) else 0

/-- The exercise hold-gate guard sub-system: the single `propBit` gate. -/
def exerciseGuardGates : ConstraintSystem := [cBitGuard]

/-- **`exerciseGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem exerciseGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied exerciseGuardGates a ↔ satisfied exerciseGuardGates b := by
  unfold satisfied exerciseGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- **`exerciseE`** — the `EffectSpec` for the `exerciseA` hold-gate, supplied to the v1 framework. -/
def exerciseE : EffectSpec RecChainedState ExerciseHoldArgs where
  view         := chainView
  touched      := fun _ _ => ∅
  expectedLeaf := fun s _ c => s.kernel.cell c
  logUpdate    := some (fun s a => authReceipt a.actor :: s.log)
  guardGates   := exerciseGuardGates
  guardProp    := exerciseGuardProp
  guardWidth   := 1
  guardEncode  := exerciseGuardEncode
  guardLocal   := exerciseGuardLocal
  guardWidth_le := by decide

/-- The CIRCUIT step for the outer hold-gate layer. -/
def exerciseHoldCircuitStep (S : CommitSurface) (pre : RecChainedState) (args : ExerciseHoldArgs)
    (post : RecChainedState) : Prop :=
  satisfiedE S exerciseE (encodeE S exerciseE pre args post)

/-! ### §1a — the per-effect guard obligations. -/

/-- **`GuardDecodes exerciseE`** — the single bit gate decodes to `exerciseGuard`. -/
theorem exerciseGuardDecodes : GuardDecodes exerciseE := by
  intro s args s' hsat
  change satisfied exerciseGuardGates (exerciseGuardEncode s args s') at hsat
  show exerciseGuardProp s args
  have hg := hsat cBitGuard (by simp [exerciseGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, exerciseGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes exerciseE`** — `exerciseGuard` encodes to the satisfied bit gate. -/
theorem exerciseGuardEncodes : GuardEncodes exerciseE := by
  intro s args s' hg
  show satisfied exerciseGuardGates (exerciseGuardEncode s args s')
  intro c hc
  simp only [exerciseGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, exerciseGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-! ### §1b — the apex ↔ `ExerciseHoldSpec` bridge. -/

/-- With `T = ∅`, the framework's `touchedCellMap` is the identity on `cell`. -/
theorem exercise_touchedCellMap_eq (k : RecordKernelState) :
    touchedCellMap k.cell ∅ (fun c => k.cell c) = k.cell := by
  funext c
  unfold touchedCellMap
  rw [if_neg (Finset.notMem_empty c)]

/-- **`AccountsWF` survives the hold post-state** (kernel frozen). -/
theorem exerciseHoldState_accountsWF (st : RecChainedState) (actor : CellId)
    (hwf : AccountsWF st.kernel) : AccountsWF (exerciseHoldState st actor).kernel := by
  simpa [exerciseHoldState_kernel] using hwf

/-- Kernel extensionality on all 17 fields (the `cell` clause is separate in the v1 apex). -/
theorem recordKernel_eq_of_fields {k k' : RecordKernelState}
    (haccounts : k.accounts = k'.accounts) (hcell : k.cell = k'.cell) (hcaps : k.caps = k'.caps)
    (hescrows : k.escrows = k'.escrows) (hnullifiers : k.nullifiers = k'.nullifiers)
    (hrevoked : k.revoked = k'.revoked) (hcommitments : k.commitments = k'.commitments)
    (hbal : k.bal = k'.bal) (hqueues : k.queues = k'.queues) (hswiss : k.swiss = k'.swiss)
    (hslotCaveats : k.slotCaveats = k'.slotCaveats) (hfactories : k.factories = k'.factories)
    (hlifecycle : k.lifecycle = k'.lifecycle) (hdeathCert : k.deathCert = k'.deathCert)
    (hdelegate : k.delegate = k'.delegate) (hdelegations : k.delegations = k'.delegations)
    (hsealedBoxes : k.sealedBoxes = k'.sealedBoxes) : k = k' := by
  cases k; cases k'; simp_all

/-- Chained-state extensionality from kernel + log agreement. -/
theorem recChainedState_eq_of_fields {s s' : RecChainedState}
    (hker : s.kernel = s'.kernel) (hlog : s.log = s'.log) : s = s' := by
  cases s; cases s'; simp_all

/-- **`apex_iff_exerciseHoldSpec`** — the framework's derived `apex` for `exerciseE` is EXACTLY
`ExerciseHoldSpec`. The guard conjunct is `exerciseGuard`; with `T = ∅` the post-cell clause pins
`s'.kernel.cell = s.kernel.cell`; the log clause is the `authReceipt`-prepended chain; the
16-field `kernelFrame` + `cell` equality reconstruct `st' = exerciseHoldState st actor`. -/
theorem apex_iff_exerciseHoldSpec (s : RecChainedState) (args : ExerciseHoldArgs)
    (s' : RecChainedState) :
    exerciseE.apex s args s' ↔ ExerciseHoldSpec s args.actor args.target s' := by
  show (exerciseGuardProp s args
        ∧ s'.kernel.cell
            = touchedCellMap s.kernel.cell ∅ (fun c => s.kernel.cell c)
        ∧ s'.log = authReceipt args.actor :: s.log
        ∧ kernelFrame s.kernel s'.kernel) ↔
      ExerciseHoldSpec s args.actor args.target s'
  rw [exercise_touchedCellMap_eq]
  unfold ExerciseHoldSpec exerciseGuardProp exerciseGuard exerciseHoldState kernelFrame
  constructor
  · rintro ⟨hguard, hcell, hlog, hAcc, hCaps, hBal, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    have hker : s'.kernel = s.kernel :=
      recordKernel_eq_of_fields hAcc hcell hCaps hEsc hNul hRev hCom hBal hQ hSw hSC hFac hLif hDC hDel
        hDgs hSB
    refine ⟨hguard, ?_⟩
    exact recChainedState_eq_of_fields hker hlog
  · rintro ⟨hguard, hhold⟩
    subst hhold
    refine ⟨hguard, rfl, exerciseHoldState_log s args.actor, ?_⟩
    simp [exerciseHoldState_kernel]

/-! ### §1c — THE VALIDATION: `exerciseA_full_sound` through the framework (hold layer). -/

/-- **`exerciseA_full_sound` — the VALIDATION (exercise hold-gate through the v1 framework).** A
satisfying generic full-state witness for `exerciseE` proves the complete declarative
`ExerciseHoldSpec`. -/
theorem exerciseA_full_sound
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ExerciseHoldArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S exerciseE (encodeE S exerciseE s args s')) :
    ExerciseHoldSpec s args.actor args.target s' := by
  have hapex : exerciseE.apex s args s' :=
    effect_circuit_full_sound S exerciseE hN hL hRest hLog exerciseGuardDecodes s args s'
      hwf hwf' h
  exact (apex_iff_exerciseHoldSpec s args s').mp hapex

/-! ## §2 — composite refinement (hold circuit + parameterized inner turn). -/

/-- The hold-gate EXEC step: `exerciseStepA` commits the outer frame. -/
def exerciseHoldExecStep (pre post : RecChainedState) (args : ExerciseHoldArgs) : Prop :=
  exerciseStepA pre args.actor args.target = some post

/-- The full composite SPEC step: hold-gate + inner `turnSpec` from the hold post-state. -/
def exerciseSpecStep (pre post : RecChainedState) (args : ExerciseFullArgs) : Prop :=
  ExerciseSpec pre args.actor args.target args.inner post

/-- The full composite EXEC step: `execFullA` on `.exerciseA`. -/
def exerciseExecStep (pre post : RecChainedState) (args : ExerciseFullArgs) : Prop :=
  execFullA pre (.exerciseA args.actor args.target args.inner) = some post

/-- **`exerciseHold_exec_equiv_spec`** — hold-gate executor ⟺ `ExerciseHoldSpec`. -/
theorem exerciseHold_exec_equiv_spec (st st' : RecChainedState) (args : ExerciseHoldArgs) :
    exerciseHoldExecStep st st' args ↔ ExerciseHoldSpec st args.actor args.target st' := by
  unfold exerciseHoldExecStep ExerciseHoldSpec
  exact exerciseStepA_iff_holdSpec st st' args.actor args.target

/-- **`exercise_circuit_refines_hold_spec`** — SOUNDNESS: hold-layer circuit ⊑ `ExerciseHoldSpec`. -/
theorem exercise_circuit_refines_hold_spec
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (pre holdPost : RecChainedState) (args : ExerciseHoldArgs)
    (hwf : AccountsWF pre.kernel) (hwf' : AccountsWF holdPost.kernel)
    (h : exerciseHoldCircuitStep S pre args holdPost) :
    ExerciseHoldSpec pre args.actor args.target holdPost :=
  exerciseA_full_sound S hN hL hRest hLog pre args holdPost hwf hwf' h

/-- **`exercise_circuit_refines_spec`** — COMPOSITE SOUNDNESS: hold circuit + inner-turn hypothesis
⊑ `ExerciseSpec`. The inner fold is carried as `innerTurnH`, bridged to
`turnSpec (exerciseHoldState pre actor) inner post`. -/
theorem exercise_circuit_refines_spec
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (pre post : RecChainedState) (args : ExerciseFullArgs)
    (innerTurnH : Prop)
    (hinner : innerTurnH)
    (hinnerBridge : innerTurnH ↔ turnSpec (exerciseHoldState pre args.actor) args.inner post)
    (hwf : AccountsWF pre.kernel)
    (hhold : exerciseHoldCircuitStep S pre ⟨args.actor, args.target⟩
        (exerciseHoldState pre args.actor)) :
    ExerciseSpec pre args.actor args.target args.inner post := by
  have hholdSpec :=
    exercise_circuit_refines_hold_spec S hN hL hRest hLog pre (exerciseHoldState pre args.actor)
      ⟨args.actor, args.target⟩ hwf
      (exerciseHoldState_accountsWF pre args.actor hwf) hhold
  rcases hholdSpec with ⟨hguard, _⟩
  exact ⟨hguard, hinnerBridge.mp hinner⟩

/-- **`exercise_circuit_refines_exec`** — COMPOSITE SOUNDNESS: hold circuit + inner-turn hypothesis
⊑ `execFullA` on `.exerciseA`, via `execFullA_exerciseA_iff_spec`. -/
theorem exercise_circuit_refines_exec
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (pre post : RecChainedState) (args : ExerciseFullArgs)
    (innerTurnH : Prop)
    (hinner : innerTurnH)
    (hinnerBridge : innerTurnH ↔ turnSpec (exerciseHoldState pre args.actor) args.inner post)
    (hwf : AccountsWF pre.kernel)
    (hhold : exerciseHoldCircuitStep S pre ⟨args.actor, args.target⟩
        (exerciseHoldState pre args.actor)) :
    execFullA pre (.exerciseA args.actor args.target args.inner) = some post :=
  (execFullA_exerciseA_iff_spec pre post args.actor args.target args.inner).mpr
    (exercise_circuit_refines_spec S hN hL hRest hLog pre post args innerTurnH hinner hinnerBridge
      hwf hhold)

/-! ## §3 — axiom-hygiene tripwires. -/

#assert_axioms exerciseGuardLocal
#assert_axioms exerciseGuardDecodes
#assert_axioms exerciseGuardEncodes
#assert_axioms apex_iff_exerciseHoldSpec
#assert_axioms exerciseA_full_sound
#assert_axioms exerciseHold_exec_equiv_spec
#assert_axioms exercise_circuit_refines_hold_spec
#assert_axioms exercise_circuit_refines_spec
#assert_axioms exercise_circuit_refines_exec

end Dregg2.Circuit.Inst.ExerciseA