/-
# Dregg2.Circuit.Spec.exercise — re-exports `ActionDispatch` in the `Spec.Exercise` namespace.

The Wave-1 dispatcher (`fullActionStep`, `turnSpec`, `fullActionStep_exec_iff`) lives in
`Circuit/ActionDispatch.lean`. This module re-exports those symbols for downstream callers that
imported `Spec.exercise` historically.

No `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Dregg2.Circuit.ActionDispatch

namespace Dregg2.Circuit.Spec.Exercise

open Dregg2.Circuit.ActionDispatch
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

export ActionDispatch (fullActionStep turnSpec actionTag actionDispatchCoverage
  ExerciseSpec exerciseGuard exerciseHoldState ExerciseHoldSpec
  fullActionStep_exec_iff execInnerA_eq_execFullTurnA execInnerA_iff_turnSpec
  execFullTurnA_iff_turnSpec execFullA_exerciseA_iff_spec
  exerciseStepA_iff_holdSpec turnSpec_ledger_per_asset exerciseSpec_ledger_per_asset)

/-- Historical alias (same statement, flipped sides). -/
theorem fullActionStep_iff_execFullA (st st' : RecChainedState) (fa : FullActionA) :
    fullActionStep st fa st' ↔ execFullA st fa = some st' :=
  Iff.symm (fullActionStep_exec_iff st st' fa)

#assert_axioms fullActionStep_iff_execFullA

end Dregg2.Circuit.Spec.Exercise