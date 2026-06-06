/-
# Dregg2.Circuit.TurnCircuitCompose — Wave 5 whole-turn circuit composition scaffold.

Folds a list of per-step `EmittedDescriptor`s into a composed `ConstraintSystem`
(`turnCircuitOfEmitted`), then composes per-step emitted→spec refinement with whole-turn
execution soundness (`turn_emitted_refines_exec_direct`) **without** the `fullAction_circuit_refines_spec`
fallback arm.

Explicit `sorry` portals (no silent fallbacks):
  * macaroon caveat-chain columns
  * root-compress binding (`preRoot`/`postRoot` ↔ `foldStepRoots`)
  * multi-step wire-alignment glue

Incomplete theorems use `sorry` only — never `exact h` pretending circuit = spec.
-/
import Dregg2.Circuit.TurnEmit
import Dregg2.Circuit.TurnWitness
import Dregg2.Circuit.ActionDispatch
import Dregg2.Circuit.TurnRefinement
import Dregg2.Exec.CircuitEmit

set_option maxHeartbeats 800000

namespace Dregg2.Circuit.TurnCircuitCompose

open Dregg2.Circuit
open Dregg2.Circuit.EffectEmitRegistry (actionAirName)
open Dregg2.Circuit.TurnEmit
  (DescriptorLookup stepEmittedSat TurnEmittedChain turnEmittedSat
   step_emitted_refines_fullActionStep turn_emitted_refines_exec
   defaultDescriptorLookup)
open Dregg2.Circuit.TurnWitness
  (StepWitness TurnWitness turnWitnessSatisfies foldStepRoots stepWitnessDigest)
open Dregg2.Circuit.ActionDispatch
  (fullActionStep actionTag turnSpec execFullTurnA_iff_turnSpec)
open Dregg2.Exec.CircuitEmit (EmittedDescriptor decodeE satisfiedEmitted)
open Dregg2.Exec.TurnExecutorFull (FullActionA execFullTurnA)
open Dregg2.Exec

/-! ## §1 — fold per-step emitted AIRs into one constraint system (scaffold). -/

/-- Append one emitted step's decoded constraints to an accumulator (wire indices unchanged). -/
def appendEmittedStep (acc : ConstraintSystem) (d : EmittedDescriptor) : ConstraintSystem :=
  acc ++ decodeE d

/-- **`turnCircuitOfEmitted`** — fold a left-to-right list of per-step emitted descriptors into a
single composed `ConstraintSystem` (scaffold: constraint-list append; wire remapping deferred). -/
def turnCircuitOfEmitted (steps : List EmittedDescriptor) : ConstraintSystem :=
  steps.foldl appendEmittedStep []

/-- The composed circuit length is the sum of per-step constraint counts (scaffold identity). -/
theorem turnCircuitOfEmitted_length (steps : List EmittedDescriptor) :
    (turnCircuitOfEmitted steps).length =
      (steps.map (fun d => (decodeE d).length)).sum := by
  suffices h : ∀ (acc : ConstraintSystem),
      (steps.foldl appendEmittedStep acc).length =
        acc.length + (steps.map (fun d => (decodeE d).length)).sum by
    simpa [turnCircuitOfEmitted] using h []
  induction steps with
  | nil => intro acc; simp
  | cons d ds ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, appendEmittedStep]
      rw [ih (acc ++ decodeE d), List.length_append]
      omega

/-! ## §2 — explicit sorry portals (Wave 5 composition gaps). -/

/-- HOLE W5: macaroon caveat-chain + hidden caveat columns arithmetized in the turn circuit. -/
def hole_turn_macaroon_chain
    (w : TurnWitness) (authChain : ℤ) : Prop :=
  sorry

/-- HOLE W5: abstract `compress` portal binds `preRoot`/`postRoot` to the step-root fold. -/
def hole_turn_root_compress_binding
    (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ) (w : TurnWitness) : Prop :=
  sorry

/-- HOLE W5: multi-step emitted AIR glue (per-step trace widths aligned across the fold). -/
def hole_turn_multi_step_glue
    (steps : List EmittedDescriptor) (w : TurnWitness) : Prop :=
  sorry

/-! ## §4 — whole-turn emitted ⊑ `execFullTurnA` (direct path, no fallback). -/

/-- **`turn_emitted_refines_exec_direct`** — compose a per-step emitted ⊑ `fullActionStep` lemma
(supplied as the `hstep` hypothesis, e.g. `step_emitted_refines_fullActionStep`) with
`turn_emitted_refines_exec`. Macaroon chain, root-compress binding, and multi-step glue are
explicit sorry obligations (not hidden in a circuit fallback). -/
theorem turn_emitted_refines_exec_direct
    (lookup : DescriptorLookup)
    (hstep :
      ∀ (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA),
        stepEmittedSat lookup sw st st' fa → fullActionStep st fa st')
    (s s' : RecChainedState) (acts : List FullActionA) (w : TurnWitness)
    (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (h : TurnEmittedChain lookup compress stepRoot s acts s' w)
    (_hmac : hole_turn_macaroon_chain w w.authChain)
    (_hroot : hole_turn_root_compress_binding compress stepRoot w)
    (_hglue : hole_turn_multi_step_glue [] w) :
    execFullTurnA s acts = some s' := by
  exact turn_emitted_refines_exec lookup hstep s s' acts w compress stepRoot h

end Dregg2.Circuit.TurnCircuitCompose