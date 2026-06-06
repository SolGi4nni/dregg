/-
# Dregg2.Circuit.TurnWitness — circuit-level turn witness scaffolding.

Abstract turn witnesses for the Wave-1 gadget/witness layer: per-action `StepWitness` records
(action tag + encoded assignment), bundled into a `TurnWitness` with pre/post roots and an auth-chain
digest. `turnWitnessSatisfies` folds step witnesses through an abstract `compress` portal (state-root
chaining); `turn_witness_refines_turnCircuit` lifts per-step declarative satisfaction to `turnSpec`.

Links to `execFullTurnA` via `ActionDispatch.execFullTurnA_iff_turnSpec` and `fullActionStep_exec_iff`.

No `sorry`/`admit`/`native_decide`/`axiom`.
-/
import Dregg2.Circuit.Refinement
import Dregg2.Circuit.ActionDispatch
import Dregg2.Circuit.TurnRefinement

namespace Dregg2.Circuit.TurnWitness

open Dregg2.Circuit.Refinement (Refines StepRel)
open Dregg2.Circuit.ActionDispatch
  (fullActionStep fullActionStep_exec_iff actionTag turnSpec execFullTurnA_iff_turnSpec)
open Dregg2.Circuit.TurnRefinement (TurnStateChain turnSpec_of_turnStateChain)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — Witness carriers. -/

/-- **`StepWitness`** — one action's circuit witness: the constructor tag (wire metadata) plus the
encoded assignment bytes as an abstract `List ℤ` (the trace columns the prover fills). -/
structure StepWitness where
  /-- The `FullActionA` constructor tag (abstract index for the wire decoder). -/
  tag        : Nat
  /-- The encoded assignment bytes (abstract field elements over the trace). -/
  assignment : List ℤ
  deriving Repr, DecidableEq

/-- **`TurnWitness`** — a whole-turn witness bundle: boundary roots, per-step witnesses, and the
auth-chain digest (the §8 credential/delegation chain the turn's auth receipts commit to). -/
structure TurnWitness where
  /-- Pre-turn state root (abstract `compress` portal). -/
  preRoot    : ℤ
  /-- Post-turn state root. -/
  postRoot   : ℤ
  /-- Per-action step witnesses, left-to-right. -/
  steps      : List StepWitness
  /-- Auth-chain digest (abstract commitment to the turn's authority receipts). -/
  authChain  : ℤ
  deriving Repr, DecidableEq

/-! ## §2 — Step-root chaining (abstract `compress` portal). -/

/-- Digest of a single step witness under abstract `stepRoot` (the per-action commitment portal). -/
def stepWitnessDigest (stepRoot : StepWitness → ℤ) (sw : StepWitness) : ℤ :=
  stepRoot sw

/-- Fold step witnesses into a root chain: `foldl (compress acc (stepRoot sw)) preRoot steps`. -/
def foldStepRoots (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (preRoot : ℤ) (steps : List StepWitness) : ℤ :=
  steps.foldl (fun acc sw => compress acc (stepWitnessDigest stepRoot sw)) preRoot

/-- **`turnWitnessSatisfies`** — the turn witness is satisfied when the step fold reaches `postRoot`
under the abstract `compress` portal (realized by Poseidon `compress` at the Rust layer). -/
def turnWitnessSatisfies (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (w : TurnWitness) : Prop :=
  foldStepRoots compress stepRoot w.preRoot w.steps = w.postRoot

/-! ## §3 — Per-step satisfaction and turn-circuit refinement. -/

/-- Per-step witness satisfaction: tag matches the action and the declarative step holds. -/
def stepWitnessSatisfies (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA) : Prop :=
  sw.tag = actionTag fa ∧ fullActionStep st fa st'

/-- **`turn_witness_refines_turnCircuit`** — if each step witness satisfies its declarative step
along a matching state chain, the full turn refines to `turnSpec`. -/
theorem turn_witness_refines_turnCircuit
    (s s' : RecChainedState) (acts : List FullActionA) (w : TurnWitness)
    (hlen : acts.length = w.steps.length)
    (states : List RecChainedState)
    (hchain_len : states.length = acts.length + 1)
    (hchain_head : states[0]'(by rw [hchain_len]; omega) = s)
    (hchain_last : states[acts.length]'(by rw [hchain_len]; omega) = s')
    (hsteps :
      ∀ (i : Fin acts.length),
        stepWitnessSatisfies w.steps[i] (states[i.val]'(by rw [hchain_len]; omega))
          (states[i.val + 1]'(by rw [hchain_len]; omega)) acts[i]) :
    turnSpec s acts s' := by
  refine turnSpec_of_turnStateChain fullActionStep s acts s' ?_
  refine {
    chain := states
    chain_len := hchain_len
    chain_head := hchain_head
    chain_last := hchain_last
    step_witness := fun i => (hsteps i).2 }

/-! ## §4 — Link to `execFullTurnA` (via `ActionDispatch` bridge). -/

/-- **`turn_witness_refines_exec`** — a `turnSpec fullActionStep` commitment refines to a genuine
`execFullTurnA` execution. -/
theorem turn_witness_refines_exec (s s' : RecChainedState) (acts : List FullActionA)
    (h : turnSpec fullActionStep s acts s') :
    execFullTurnA s acts = some s' :=
  (execFullTurnA_iff_turnSpec s s' acts).mpr h

/-- **`turnWitness_exec_link`** — alias: declarative turn spec ⟹ executor commit. -/
theorem turnWitness_exec_link (s s' : RecChainedState) (acts : List FullActionA)
    (h : turnSpec fullActionStep s acts s') :
    execFullTurnA s acts = some s' :=
  turn_witness_refines_exec s s' acts h

#assert_axioms turn_witness_refines_turnCircuit
#assert_axioms turn_witness_refines_exec
#assert_axioms turnWitness_exec_link

end Dregg2.Circuit.TurnWitness