/-
# Dregg2.Circuit.TurnCircuitCompose — Wave 5 whole-turn circuit composition scaffold.

Folds a list of per-step `EmittedDescriptor`s into a composed `ConstraintSystem`
(`turnCircuitOfEmitted`), then composes per-step emitted→spec refinement with whole-turn
execution soundness (`turn_emitted_refines_exec_direct`) **without** the `fullAction_circuit_refines_spec`
fallback arm.

Explicit `sorry` portals (no silent fallbacks):
  * macaroon caveat-chain columns
  * multi-step wire-alignment glue

DISCHARGED: the root-compress binding (`preRoot`/`postRoot` ↔ `foldStepRoots`) is no longer a `sorry`
portal — `hole_turn_root_compress_binding` is now the genuine `TurnWitness.authenticTurnRoots`
predicate (boundary roots = `StateCommit.recStateCommit` of the boundary kernels), and
`turn_root_binds_post_commitment` makes `turnWitnessSatisfies` load-bearing (the prover-folded
post-root equals the real post-state commitment; a tampered post-root is rejected).

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
  (StepWitness TurnWitness turnWitnessSatisfies foldStepRoots stepWitnessDigest
   authenticTurnRoots turnWitnessSatisfies_binds_postRoot tampered_postRoot_rejects)
open Dregg2.Circuit.StateCommit (recStateCommit)
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

/-- **`hole_turn_root_compress_binding` — DISCHARGED (was a `sorry` portal).**

The abstract `compress` portal now binds `preRoot`/`postRoot` to a GENUINE full-state commitment:
the witness's boundary roots ARE `StateCommit.recStateCommit` of the boundary kernels (over a chosen
commitment surface `CH`/`RH`/`cmb`/`compress`/`compressN` + turn `t`). No `sorry`: this is the real
`TurnWitness.authenticTurnRoots` predicate. Consumed by `turn_root_binds_post_commitment` below,
which makes `turnWitnessSatisfies` load-bearing (the prover-folded post-root = the real post-state
commitment), so a tampered `postRoot` is rejected (`tampered_postRoot_rejects`). -/
def hole_turn_root_compress_binding
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress compressN' : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (s s' : RecChainedState) (t : Turn) (w : TurnWitness) : Prop :=
  authenticTurnRoots CH RH cmb compress compressN s s' t w

/-- **`turn_root_binds_post_commitment` — `turnWitnessSatisfies` is load-bearing.**

Consume a `TurnEmittedChain` (whose `root_chain` field IS `turnWitnessSatisfies`) and the now-genuine
root-binding portal: the step-root fold reaching `postRoot` is forced to equal the GENUINE
`recStateCommit` of `s'.kernel`. The root chain is no longer decorative — it equates the prover's
folded post-root with the real post-state commitment. -/
theorem turn_root_binds_post_commitment
    (lookup : DescriptorLookup)
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compressN' : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (s s' : RecChainedState) (acts : List FullActionA) (w : TurnWitness)
    (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ) (t : Turn)
    (h : TurnEmittedChain lookup compress stepRoot s acts s' w)
    (hroot : hole_turn_root_compress_binding CH RH cmb compress compressN' compressN s s' t w) :
    foldStepRoots compress stepRoot w.preRoot w.steps
      = recStateCommit CH RH cmb compress compressN s'.kernel t :=
  turnWitnessSatisfies_binds_postRoot CH RH cmb compress compressN stepRoot compress
    s s' t w hroot h.root_chain

/-- HOLE W5: multi-step emitted AIR glue (per-step trace widths aligned across the fold). -/
def hole_turn_multi_step_glue
    (steps : List EmittedDescriptor) (w : TurnWitness) : Prop :=
  sorry

/-! ## §4 — whole-turn emitted ⊑ `execFullTurnA` (direct path, no fallback). -/

/-- **`turn_emitted_refines_exec_direct`** — compose a per-step emitted ⊑ `fullActionStep` lemma
(supplied as the `hstep` hypothesis, e.g. `step_emitted_refines_fullActionStep`) with
`turn_emitted_refines_exec`. The root-compress binding is now DISCHARGED (genuine `authenticTurnRoots`,
no `sorry`) and load-bearing: alongside the executor refinement we EXPORT that the prover-folded
post-root equals the genuine `recStateCommit s'.kernel` (so a tampered post-root is impossible). The
macaroon chain and multi-step glue remain explicit sorry obligations (not hidden in a fallback). -/
theorem turn_emitted_refines_exec_direct
    (lookup : DescriptorLookup)
    (hstep :
      ∀ (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA),
        stepEmittedSat lookup sw st st' fa → fullActionStep st fa st')
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compressN' : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) (t : Turn)
    (s s' : RecChainedState) (acts : List FullActionA) (w : TurnWitness)
    (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (h : TurnEmittedChain lookup compress stepRoot s acts s' w)
    (_hmac : hole_turn_macaroon_chain w w.authChain)
    (hroot : hole_turn_root_compress_binding CH RH cmb compress compressN' compressN s s' t w)
    (_hglue : hole_turn_multi_step_glue [] w) :
    execFullTurnA s acts = some s' ∧
      foldStepRoots compress stepRoot w.preRoot w.steps
        = recStateCommit CH RH cmb compress compressN s'.kernel t :=
  ⟨turn_emitted_refines_exec lookup hstep s s' acts w compress stepRoot h,
   turn_root_binds_post_commitment lookup CH RH cmb compressN' compressN s s' acts w
     compress stepRoot t h hroot⟩

#assert_axioms turn_root_binds_post_commitment

end Dregg2.Circuit.TurnCircuitCompose