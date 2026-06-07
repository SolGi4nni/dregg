/-
# Dregg2.Circuit.Inst.ExerciseInnerTurn — inner-turn emitted witness (Wave 7 exercise portal).

The outer `exerciseA` hold-gate is arithmetized in `exerciseA.lean`; the INNER `List FullActionA`
fold from `exerciseHoldState` is NOT yet composed into the emitted-turn layer. This module names the
parameterized witness bundle and tracks the remaining refinement fronts as explicit `sorry` portals.

POLICY: no silent gaps — every unfinished inner-turn / R4 facet front is named here.
-/
import Dregg2.Circuit.Inst.exerciseA
import Dregg2.Circuit.TurnEmit
import Dregg2.Circuit.TurnWitness
import Dregg2.Circuit.ActionDispatch
import Dregg2.Exec.CircuitEmit
import Dregg2.Exec.HandlerExecutor

namespace Dregg2.Circuit.Inst.ExerciseInnerTurn

open Dregg2.Circuit
open Dregg2.Circuit.Inst.ExerciseA
open Dregg2.Circuit.TurnEmit (TurnEmittedChain stepEmittedSat DescriptorLookup)
open Dregg2.Circuit.TurnWitness (StepWitness TurnWitness)
open Dregg2.Circuit.ActionDispatch (turnSpec fullActionStep)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.HandlerExecutor (execHandlerOne)


/-! ## §0 — inner-turn witness bundle (hold post-state → inner fold → final post). -/

/-- **`exerciseInnerTurnWitness`** — emitted witness for the inner `List FullActionA` fold that runs
from the exercise hold post-state (`exerciseHoldState pre actor`). Bundles a `TurnEmittedChain` over
the inner forest plus the hold/final boundary states (the circuit-layer `innerTurnH` pattern). -/
structure exerciseInnerTurnWitness (lookup : DescriptorLookup) (compress : ℤ → ℤ → ℤ)
    (stepRoot : StepWitness → ℤ) (holdPost post : RecChainedState) (inner : List FullActionA) where
  /-- Per-step turn witness for the inner forest. -/
  turnWit       : TurnWitness
  /-- Emitted satisfaction chain: `holdPost` → … → `post` along `inner`. -/
  emittedChain  : TurnEmittedChain lookup compress stepRoot holdPost inner post turnWit

/-! ## §1 — inner emitted ⊑ `turnSpec` (CLOSED: the inner emitted chain refines `turnSpec`). -/

/-- **`exercise_inner_emitted_refines_turnSpec`** — when the inner emitted chain is satisfied from the
hold post-state, the inner forest refines `turnSpec`. CLOSED: the witness bundles a `TurnEmittedChain`
over the inner forest, so the generic `TurnEmit.turn_emitted_refines_turnSpec` discharges it from the
per-step refinement `hstep` (which `TurnEmit.step_emitted_refines_fullActionStep`, now sorry-free,
supplies). No `sorry`. -/
theorem exercise_inner_emitted_refines_turnSpec
    (lookup : DescriptorLookup)
    (compress : ℤ → ℤ → ℤ)
    (stepRoot : StepWitness → ℤ)
    (hstep :
      ∀ (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA),
        stepEmittedSat lookup sw st st' fa → fullActionStep st fa st')
    (holdPost post : RecChainedState) (inner : List FullActionA)
    (w : exerciseInnerTurnWitness lookup compress stepRoot holdPost post inner) :
    turnSpec holdPost inner post :=
  TurnEmit.turn_emitted_refines_turnSpec lookup hstep holdPost post inner w.turnWit compress stepRoot
    w.emittedChain

/-! ## §2 — R4 facet-mask alignment (handler `facetedOf` vs bare `FullActionA`). -/

/-- **`exercise_r4_facet_mask` — CLOSED (the facet-bridge lemma, no `sorry`).** The R4 front that was a
`sorry` is discharged: `execFullA`'s `exerciseA` now ENFORCES the facet mask (`innerFacetsAdmittedA`) and
the handler bridge tags each inner with its REAL `requiredFacetA fa` (not a blanket `Auth.control`), so
the two facet gates are the SAME `heldCapTo`-cap / `requiredFacetA`-key / `capFacetMask` check —
`HandlerExecutor.handler_refines_execFullA_exercise` carries that bridge. The remaining INNER-FOLD
agreement (`execInnerA (exerciseHoldState …) inner` reaches the handler's kernel) is the ORTHOGONAL W7
inner-turn-emission front, carried here as the explicit `hinner` hypothesis (NOT a hidden `sorry`): once
the inner-turn witness supplies it, the whole exercise refines `execFullA` on the same kernel. The FACET
mask itself is now fully sound on `execFullA` (the canonical semantics). -/
theorem exercise_r4_facet_mask (s s' : RecChainedState) (actor target : CellId)
    (inner : List FullActionA)
    (hinner : ∃ s₁, execInnerA (HandlerExecutor.exerciseHoldState s actor) inner = some s₁ ∧
        s₁.kernel = s'.kernel)
    (h : execHandlerOne (.exerciseA actor target inner) s = some s') :
    ∃ s'', execFullA s (.exerciseA actor target inner) = some s'' ∧ s''.kernel = s'.kernel :=
  HandlerExecutor.handler_refines_execFullA_exercise s s' actor target inner hinner h

end Dregg2.Circuit.Inst.ExerciseInnerTurn