/-
# Dregg2.Circuit.TurnRefinement — the turn-level refinement tower (circuit ⊑ turnSpec ⊑ executor).

Extends `Refinement.lean`'s relational framework and `EffectRefinement.lean`'s per-action diamond
patterns to WHOLE TURNS: a list of `FullActionA` folded all-or-nothing. The generic layer proves
that per-action circuit refinement descends to turn-level refinement over `turnSpec`, and composes
with `execFullTurnA_iff_turnSpec` for the executor corner. Conservation per asset descends when the
turn's net ledger delta is zero.

Links to `TurnWitness.lean` for circuit-level witness scaffolding and `ActionDispatch.fullActionStep`.

No `sorry`/`admit`/`native_decide`/`axiom`.
-/
import Dregg2.Circuit.Refinement
import Dregg2.Circuit.ActionDispatch
import Dregg2.Circuit.Spec.Turn

namespace Dregg2.Circuit.TurnRefinement

open Dregg2.Circuit.Refinement (Refines StepRel)
open Dregg2.Circuit.ActionDispatch (fullActionStep fullActionStep_exec_iff)
open Dregg2.Circuit.Spec.Turn (ActionStep turnSpec_nil execFullTurnA_iff_turnSpec)
open Dregg2.Circuit.ActionDispatch (execFullTurnA_iff_turnSpec)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — Turn-level step relations (parameterized by per-action step). -/

/-- The per-action CIRCUIT step, lifted to a whole turn via `turnSpec`. -/
def turnCircuitStep (circuitStep : StepRel RecChainedState FullActionA RecChainedState) :
    StepRel RecChainedState (List FullActionA) RecChainedState :=
  fun s acts s' => Spec.Turn.turnSpec circuitStep s acts s'

/-- The per-action SPEC step, lifted to a whole turn via `turnSpec`. -/
def turnSpecStep (specStep : StepRel RecChainedState FullActionA RecChainedState) :
    StepRel RecChainedState (List FullActionA) RecChainedState :=
  fun s acts s' => Spec.Turn.turnSpec specStep s acts s'

/-- The EXECUTABLE whole-turn step: `execFullTurnA` commits the action list. -/
def turnExecStep : StepRel RecChainedState (List FullActionA) RecChainedState :=
  fun s acts s' => execFullTurnA s acts = some s'

/-! ## §2 — Generic turn refinement (any per-action step family). -/

section GenericTurn
variable (circuitStep specStep : StepRel RecChainedState FullActionA RecChainedState)

/-- **`turn_circuit_refines_spec_of_steps`** — SOUNDNESS descent: if each action circuit ⊑ spec,
the turn circuit ⊑ `turnSpec spec`. Proved by induction on the action list. -/
theorem turn_circuit_refines_spec_of_steps
    (hrefine : Refines circuitStep specStep) :
    Refines (turnCircuitStep circuitStep) (turnSpecStep specStep) := by
  intro s acts s' hc
  induction acts generalizing s s' with
  | nil =>
      simp only [turnCircuitStep, turnSpecStep, Spec.Turn.turnSpec] at hc ⊢
      exact hc
  | cons a rest ih =>
      simp only [turnCircuitStep, turnSpecStep, Spec.Turn.turnSpec] at hc ⊢
      obtain ⟨s1, hcirc, htail⟩ := hc
      refine ⟨s1, hrefine s a s1 hcirc, ?_⟩
      exact ih s1 s' htail

variable (execStep : StepRel RecChainedState FullActionA RecChainedState)

/-- **`turn_circuit_refines_exec_of_steps`** — compose circuit ⊑ spec with executor⟺spec at the
turn level via `execFullTurnA_iff_turnSpec`. -/
theorem turn_circuit_refines_exec_of_steps
    (hrefine : Refines circuitStep execStep)
    (hstep : ∀ s a s', execFullA s a = some s' ↔ execStep s a s') :
    Refines (turnCircuitStep circuitStep) turnExecStep := by
  intro s acts s' hc
  exact (execFullTurnA_iff_turnSpec execStep hstep s acts s').mpr
    (turn_circuit_refines_spec_of_steps circuitStep execStep hrefine s acts s' hc)

/-- **`turn_conservation_descends`** — per-asset conservation transfers to a committed turn when
the net ledger delta is zero. Uses `execFullTurnA_iff_turnSpec` + `execFullTurnA_conserves_per_asset`. -/
theorem turn_conservation_descends (step : ActionStep)
    (hstep : ∀ s a s', execFullA s a = some s' ↔ step s a s')
    (s s' : RecChainedState) (acts : List FullActionA) (b : AssetId)
    (h : Spec.Turn.turnSpec step s acts s') (hzero : turnLedgerDeltaAsset acts b = 0) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  have hexec : execFullTurnA s acts = some s' :=
    (execFullTurnA_iff_turnSpec step hstep s acts s').mpr h
  exact execFullTurnA_conserves_per_asset s s' acts b hexec hzero

/-! ## §3 — Prop-level state-chain witness (scaffolding; circuit witnesses in `TurnWitness`). -/

/-- A **`TurnStateChain`** threads per-action declarative steps through intermediate states
(Prop-level scaffolding; the circuit-level `TurnWitness` carries roots + assignment bytes). -/
structure TurnStateChain (step : ActionStep) (s : RecChainedState) (acts : List FullActionA)
    (s' : RecChainedState) where
  /-- Intermediate states: `chain[0] = s`, `chain[n] = s'`, length `acts.length + 1`. -/
  chain : List RecChainedState
  chain_len : chain.length = acts.length + 1
  chain_head : chain[0]'(by rw [chain_len]; omega) = s
  chain_last : chain[acts.length]'(by rw [chain_len]; omega) = s'
  step_witness :
    ∀ (i : Fin acts.length),
      step (chain[i.val]'(by rw [chain_len]; omega)) acts[i]
        (chain[i.val + 1]'(by rw [chain_len]; omega))

/-- Every `TurnStateChain` yields `turnSpec` (converse of `turnStateChain_of_turnSpec`). -/
theorem turnSpec_of_turnStateChain (step : ActionStep) :
    ∀ (s s' : RecChainedState) (acts : List FullActionA) (w : TurnStateChain step s acts s'),
      Spec.Turn.turnSpec step s acts s'
  | s, s', [], w => by
      simp only [Spec.Turn.turnSpec]
      have hl := w.chain_last
      simp [w.chain_len] at hl
      exact w.chain_head.symm.trans hl
  | s, s', a :: rest, w => by
      simp only [Spec.Turn.turnSpec]
      cases hchain : w.chain with
      | nil =>
          have hz : (0 : Nat) = rest.length + 2 := by simpa [hchain] using w.chain_len
          omega
      | cons s0 tail =>
          cases tail with
          | nil =>
              have hz : (1 : Nat) = rest.length + 2 := by simpa [hchain] using w.chain_len
              omega
          | cons s1 ws =>
              have hstep := w.step_witness ⟨0, Nat.succ_pos rest.length⟩
              have hstep' : step s0 a s1 := by simpa [hchain] using hstep
              refine ⟨s1, ?_, ?_⟩
              · exact (by simpa [hchain] using w.chain_head) ▸ hstep'
              · exact turnSpec_of_turnStateChain step s1 s' rest {
                  chain := s1 :: ws
                  chain_len := by
                    have hlen := w.chain_len
                    simp [hchain, List.length] at hlen ⊢
                    omega
                  chain_head := by simp
                  chain_last := by
                    have hlast := w.chain_last
                    simp [hchain, List.get_cons_succ] at hlast
                    exact hlast
                  step_witness := fun i => by
                    have hwit := w.step_witness ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
                    simpa [hchain, List.get_cons_succ] using hwit }
termination_by _ _ acts _ => acts.length

/-- Every `turnSpec` commitment yields a `TurnStateChain` (existence, by structural recursion).
Uses classical choice on the cons-case existential (constructing data, not proving a `Prop`). -/
noncomputable def turnStateChain_of_turnSpec (step : ActionStep) :
    ∀ (s : RecChainedState) (acts : List FullActionA) (s' : RecChainedState),
      Spec.Turn.turnSpec step s acts s' → TurnStateChain step s acts s'
  | s, [], s', h => by
      simp only [Spec.Turn.turnSpec] at h
      subst h
      exact { chain := [s]
            , chain_len := by simp
            , chain_head := by simp
            , chain_last := by simp
            , step_witness := fun i => absurd i.2 (Nat.not_lt_zero _) }
  | s, a :: rest, s', h => by
      classical
      simp only [Spec.Turn.turnSpec] at h
      let s1 := Classical.choose h
      have hpair := Classical.choose_spec h
      have hhead : step s a s1 := hpair.1
      have htail : Spec.Turn.turnSpec step s1 rest s' := hpair.2
      let w := turnStateChain_of_turnSpec step s1 rest s' htail
      refine ⟨s :: w.chain, ?_, ?_, ?_, ?_⟩
      · simp [w.chain_len]
      · simp
      · simp [w.chain_len, w.chain_last]
      · intro i
        match i with
        | ⟨0, _⟩ => simpa [List.get_cons_zero, w.chain_head] using hhead
        | ⟨j + 1, hj⟩ =>
            have hj' : j < rest.length := Nat.lt_of_succ_lt_succ hj
            simpa [List.get_cons_succ] using w.step_witness ⟨j, hj'⟩

/-- **`fullAction_turn_refines_exec`** — the Wave-1 apex dispatcher composes with `execFullTurnA`. -/
theorem fullAction_turn_refines_exec (s s' : RecChainedState) (acts : List FullActionA)
    (h : ActionDispatch.turnSpec s acts s') :
    execFullTurnA s acts = some s' :=
  (ActionDispatch.execFullTurnA_iff_turnSpec s s' acts).mpr h

#assert_axioms turn_circuit_refines_spec_of_steps
#assert_axioms turn_circuit_refines_exec_of_steps
#assert_axioms turn_conservation_descends
#assert_axioms turnSpec_of_turnStateChain
#assert_axioms fullAction_turn_refines_exec

end GenericTurn

end Dregg2.Circuit.TurnRefinement