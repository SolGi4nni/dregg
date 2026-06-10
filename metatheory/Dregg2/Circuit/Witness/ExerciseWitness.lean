/-
# Dregg2.Circuit.Witness.ExerciseWitness — execute→prove→verify→anti-ghost for the `exerciseA`
hold-gate.

Amplifies the `Transfer` beachhead to the composite `exerciseA` HOLD-GATE layer (kernel frozen,
authority receipt prepended) through the v1 framework (`EffectCommit`). REUSED (not re-proved):

  * `Exec.exerciseStepA` — the real hold-gate executor (kernel frozen + `authReceipt actor` prepended
    when the actor holds a cap conferring an edge to `target`).
  * `Circuit.ActionDispatch.exerciseStepA_iff_holdSpec` — hold step ⟺ `ExerciseHoldSpec`.
  * `Inst.ExerciseA.{exerciseE, apex_iff_exerciseHoldSpec, exerciseA_full_sound}`.
  * `EffectCommit.{encodeE, satisfiedE, effect_circuit_full_complete}`.

This is the OUTER hold layer (the inner `List FullActionA` fold is composed via a separate inner-turn
hypothesis in `Inst/exerciseA.lean`, not arithmetized here). The witness generator runs the hold step;
the soundness reuses `exerciseA_full_sound ⇒ ExerciseHoldSpec`.

SUPPLIED (the `TransferWitness` pattern): `exerciseWitnessVec`; `execute_produces_satisfying_witness` /
`satisfying_witness_proves_full_state`; the concrete `#guard`s; the JSON the Rust
`lean_executor_derived_exercise` prover proves+verifies / rejects. Forgeries (log-only effect): a
tampered receipt row (log-bind gate 72/73) and a minted bystander cell (frame-reuse gate 68/69).
-/
import Dregg2.Circuit.Witness.Common
import Dregg2.Circuit.Inst.exerciseA

namespace Dregg2.Circuit.Witness.ExerciseWitness

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Witness.Common
open Dregg2.Circuit.Inst.ExerciseA
open Dregg2.Circuit.ActionDispatch
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Cap)

set_option linter.dupNamespace false

/-! ## §1 — THE WITNESS GENERATOR. -/

/-- **`exerciseWitnessVec s args`** — runs `exerciseStepA s actor target`; on commit lays out the
hold-layer full-state witness for the executor's post-state; else falls back to the pre-state. -/
def exerciseWitnessVec (s : RecChainedState) (args : ExerciseHoldArgs) : List Int :=
  match exerciseStepA s args.actor args.target with
  | some s' => layoutE exerciseE s args s'
  | none    => layoutE exerciseE s args s

theorem exerciseWitnessVec_commit {s s' : RecChainedState} {args : ExerciseHoldArgs}
    (h : exerciseStepA s args.actor args.target = some s') :
    exerciseWitnessVec s args = layoutE exerciseE s args s' := by
  unfold exerciseWitnessVec; rw [h]

/-! ## §2 — THE EXECUTE → PROVE / PROVE → ACCEPT theorems. -/

/-- **`execute_produces_satisfying_witness` — execute→prove.** A committed `exerciseStepA` hold step
makes the full-state witness SATISFY the circuit. Reuses `effect_circuit_full_complete` via
`apex_iff_exerciseHoldSpec` ∘ `exerciseStepA_iff_holdSpec`. -/
theorem execute_produces_satisfying_witness
    (S : CommitSurface) (hRest : RestHashIffFrame S.RH)
    {s s' : RecChainedState} {args : ExerciseHoldArgs}
    (h : exerciseStepA s args.actor args.target = some s') :
    satisfiedE S exerciseE (encodeE S exerciseE s args s') := by
  have hspec : ExerciseHoldSpec s args.actor args.target s' :=
    (exerciseStepA_iff_holdSpec s s' args.actor args.target).mp h
  have hapex : exerciseE.apex s args s' := (apex_iff_exerciseHoldSpec s args s').mpr hspec
  exact effect_circuit_full_complete S exerciseE hRest exerciseGuardEncodes s args s' hapex

/-- **`satisfying_witness_proves_full_state` — prove→accept.** Reuses `exerciseA_full_sound`. -/
theorem satisfying_witness_proves_full_state
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ExerciseHoldArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S exerciseE (encodeE S exerciseE s args s')) :
    ExerciseHoldSpec s args.actor args.target s' :=
  exerciseA_full_sound S hN hL hRest hLog s args s' hwf hwf' h

/-! ## §3 — THE EXECUTOR-DERIVED CONCRETE WITNESS.

A concrete 3-cell pre-state {0,1,2} (balances 100/5/50); actor 0 holds a `Cap.node 1` (an edge to
target 1), empty log. We RUN the hold step and materialize the witness. Forgeries: a tampered receipt
row (log-bind 72/73) and a minted bystander cell 2 (frame-reuse 68/69). -/

def kCells : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun c => if c = 0 then .record [("balance", .int 100)]
                     else if c = 1 then .record [("balance", .int 5)]
                     else if c = 2 then .record [("balance", .int 50)]
                     else default
    caps := fun a => if a = 0 then [Cap.node 1] else [] }

def s0 : RecChainedState := { kernel := kCells, log := [] }
def goodArgs : ExerciseHoldArgs := { actor := 0, target := 1 }
def goodPost : RecChainedState := (exerciseStepA s0 goodArgs.actor goodArgs.target).getD s0

/-- THE LOG FORGERY: a forged authority receipt row (actor 9). Log-bind gate (72/73) rejects. -/
def forgedLog : RecChainedState :=
  { kernel := goodPost.kernel, log := { actor := 9, src := 9, dst := 9, amt := 0 } :: s0.log }

/-- THE THIRD-CELL FORGERY: a MINTED bystander cell 2 (50 → 999). Frame-reuse gate (68/69) rejects. -/
def forgedCell : RecChainedState :=
  { kernel := { goodPost.kernel with
      cell := fun c => if c = 2 then .record [("balance", .int 999)] else goodPost.kernel.cell c }
    log := goodPost.log }

def honestWitness : List Int := exerciseWitnessVec s0 goodArgs
def forgedLogWitness : List Int := layoutE exerciseE s0 goodArgs forgedLog
def forgedCellWitness : List Int := layoutE exerciseE s0 goodArgs forgedCell

#guard honestWitness.length == 74
#guard forgedLogWitness.length == 74
#guard forgedCellWitness.length == 74

#guard decide (satisfied (effectCircuit exerciseE) (fun v => honestWitness.getD v 0))
#guard decide (satisfied (effectCircuit exerciseE) (fun v => forgedLogWitness.getD v 0)) == false
#guard decide (satisfied (effectCircuit exerciseE) (fun v => forgedCellWitness.getD v 0)) == false
#guard honestWitness.getD 72 0 == honestWitness.getD 73 0
#guard !(forgedLogWitness.getD 72 0 == forgedLogWitness.getD 73 0)   -- log forgery: log gate
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard !(forgedCellWitness.getD 68 0 == forgedCellWitness.getD 69 0) -- bystander: frame gate

/-! ## §4 — JSON export. -/

def honestWitnessJson : String := witnessJson honestWitness
def forgedLogWitnessJson : String := witnessJson forgedLogWitness
def forgedCellWitnessJson : String := witnessJson forgedCellWitness

-- (no JSON byte pin: Common.lhConcrete is the CR-grounded turnLogDigest)
#guard !(honestWitnessJson == forgedLogWitnessJson)
#guard !(honestWitnessJson == forgedCellWitnessJson)

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms exerciseWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.ExerciseWitness
