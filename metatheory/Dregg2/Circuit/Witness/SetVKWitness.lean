/-
# Dregg2.Circuit.Witness.SetVKWitness — execute→prove→verify→anti-ghost for `setVKA`.

Amplifies the `Transfer`/`refusalA` verifiable-execution beachhead to `setVKA` (writes the verifying-key
slot of a cell), through the GENERIC v1 framework (`EffectCommit`, width 74, 5 gates). Reused (not
re-proved): `Exec.execFullA`, `Spec.CellStateVK.execFullA_setVK_iff_spec`,
`Inst.SetVKA.{setVKE, apex_iff_setVKSpec, setVKA_full_sound}`, `EffectCommit.*`, and the shared concrete
surface `Witness.Common.{SConc, layoutE}`.

§1 the executor-driven `setVKWitnessVec`; §2 abstract execute→prove + verify→accept; §3 the concrete
`#guard`s (honest SATISFIES, REAL forged third-cell-mint UNSAT on the frame-reuse gate 68/69); §4 the
JSON the Rust `lean_executor_derived_set_vk` prover proves+verifies / rejects.
-/
import Dregg2.Circuit.Witness.Common
import Dregg2.Circuit.Inst.setVKA
import Dregg2.Circuit.Spec.cellstatevk

namespace Dregg2.Circuit.Witness.SetVKWitness

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Witness.Common
open Dregg2.Circuit.Inst.SetVKA
open Dregg2.Circuit.Spec.CellStateVK
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §1 — THE WITNESS GENERATOR. -/

def setVKWitnessVec (s : RecChainedState) (args : SetVKArgs) : List Int :=
  match execFullA s (.setVKA args.actor args.cell args.vk) with
  | some s' => layoutE setVKE s args s'
  | none    => layoutE setVKE s args s

theorem setVKWitnessVec_commit {s s' : RecChainedState} {args : SetVKArgs}
    (h : execFullA s (.setVKA args.actor args.cell args.vk) = some s') :
    setVKWitnessVec s args = layoutE setVKE s args s' := by
  unfold setVKWitnessVec; rw [h]

/-! ## §2 — THE EXECUTE → PROVE / PROVE → STATE theorems. -/

theorem execute_produces_satisfying_witness
    (S : CommitSurface) (hRest : RestHashIffFrame S.RH)
    {s s' : RecChainedState} {args : SetVKArgs}
    (h : execFullA s (.setVKA args.actor args.cell args.vk) = some s') :
    satisfiedE S setVKE (encodeE S setVKE s args s') := by
  have hspec : SetVKSpec s args.actor args.cell args.vk s' :=
    (execFullA_setVK_iff_spec s args.actor args.cell args.vk s').mp h
  have hapex : setVKE.apex s args s' := (apex_iff_setVKSpec s args s').mpr hspec
  exact effect_circuit_full_complete S setVKE hRest setVKGuardEncodes s args s' hapex

theorem satisfying_witness_proves_full_state
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SetVKArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S setVKE (encodeE S setVKE s args s')) :
    SetVKSpec s args.actor args.cell args.vk s' :=
  setVKA_full_sound S hN hL hRest hLog s args s' hwf hwf' h

/-! ## §3 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

def kCells : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun c => if c = 0 then .record [("balance", .int 100)]
                     else if c = 1 then .record [("balance", .int 5)]
                     else if c = 2 then .record [("balance", .int 50)]
                     else default
    caps := fun _ => [] }

def s0 : RecChainedState := { kernel := kCells, log := [] }

/-- The good args: actor 0 = cell 0 (self-owned ⇒ authorized, Live), set its verifying-key slot to 7. -/
def goodArgs : SetVKArgs := { actor := 0, cell := 0, vk := 7 }

def goodPost : RecChainedState := (execFullA s0 (.setVKA 0 0 7)).getD s0

/-- THE THIRD-CELL FORGERY: the honest vk write but a MINTED bystander cell 2 (50 → 999). -/
def forgedCell : RecChainedState :=
  { kernel := { goodPost.kernel with
      cell := fun c => if c = 2 then .record [("balance", .int 999)] else goodPost.kernel.cell c }
    log := goodPost.log }

def honestWitness : List Int := setVKWitnessVec s0 goodArgs
def forgedCellWitness : List Int := layoutE setVKE s0 goodArgs forgedCell

#guard honestWitness.length == 74
#guard forgedCellWitness.length == 74
#guard decide (satisfied (effectCircuit setVKE) (fun v => honestWitness.getD v 0))
#guard decide (satisfied (effectCircuit setVKE) (fun v => forgedCellWitness.getD v 0)) == false
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard !(forgedCellWitness.getD 68 0 == forgedCellWitness.getD 69 0)
#guard honestWitness.getD 0 0 == 1

/-! ## §4 — JSON export. -/

def honestWitnessJson : String := witnessJson honestWitness
def forgedCellWitnessJson : String := witnessJson forgedCellWitness

-- (no JSON byte pin: Common.lhConcrete is the CR-grounded turnLogDigest)
#guard !(honestWitnessJson == forgedCellWitnessJson)

#assert_axioms setVKWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.SetVKWitness
