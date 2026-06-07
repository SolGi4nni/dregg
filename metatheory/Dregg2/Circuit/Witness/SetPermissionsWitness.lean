/-
# Dregg2.Circuit.Witness.SetPermissionsWitness — execute→prove→verify→anti-ghost for `setPermissionsA`.

Amplifies the `Transfer`/`refusalA` verifiable-execution beachhead to `setPermissionsA` (writes the
`permissions` slot of a cell), through the GENERIC v1 framework (`EffectCommit`, width 74, 5 gates).
Reused (not re-proved): `Exec.execFullA`, `Spec.CellStatePermissions.execFullA_setPermissions_iff_spec`,
`Inst.SetPermissionsA.{setPermissionsE, apex_iff_setPermissionsSpec, setPermissionsA_full_sound}`,
`EffectCommit.{encodeE, satisfiedE, effect_circuit_full_complete}`, and the shared concrete surface
`Witness.Common.{SConc, layoutE}`.

§1 the executor-driven `setPermissionsWitnessVec`; §2 abstract execute→prove + verify→accept; §3 the
concrete `#guard`s (honest SATISFIES, REAL forged third-cell-mint UNSAT on the frame-reuse gate 68/69);
§4 the JSON the Rust `lean_executor_derived_set_permissions` prover proves+verifies / rejects.

No `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Dregg2.Circuit.Witness.Common
import Dregg2.Circuit.Inst.setPermissionsA
import Dregg2.Circuit.Spec.cellstatepermissions

namespace Dregg2.Circuit.Witness.SetPermissionsWitness

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Witness.Common
open Dregg2.Circuit.Inst.SetPermissionsA
open Dregg2.Circuit.Spec.CellStatePermissions
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §1 — THE WITNESS GENERATOR: `execute → satisfying assignment`. -/

/-- **`setPermissionsWitnessVec s args`** — the executor-driven witness generator. Runs
`execFullA s (.setPermissionsA …)`; on commit lays out the full-state witness for the executor's
post-state via `layoutE`. -/
def setPermissionsWitnessVec (s : RecChainedState) (args : SetPermissionsArgs) : List Int :=
  match execFullA s (.setPermissionsA args.actor args.cell args.p) with
  | some s' => layoutE setPermissionsE s args s'
  | none    => layoutE setPermissionsE s args s

theorem setPermissionsWitnessVec_commit {s s' : RecChainedState} {args : SetPermissionsArgs}
    (h : execFullA s (.setPermissionsA args.actor args.cell args.p) = some s') :
    setPermissionsWitnessVec s args = layoutE setPermissionsE s args s' := by
  unfold setPermissionsWitnessVec; rw [h]

/-! ## §2 — THE EXECUTE → PROVE / PROVE → STATE theorems (abstract surface, CR portals carried). -/

theorem execute_produces_satisfying_witness
    (S : CommitSurface) (hRest : RestHashIffFrame S.RH)
    {s s' : RecChainedState} {args : SetPermissionsArgs}
    (h : execFullA s (.setPermissionsA args.actor args.cell args.p) = some s') :
    satisfiedE S setPermissionsE (encodeE S setPermissionsE s args s') := by
  have hspec : SetPermissionsSpec s args.actor args.cell args.p s' :=
    (execFullA_setPermissions_iff_spec s args.actor args.cell args.p s').mp h
  have hapex : setPermissionsE.apex s args s' := (apex_iff_setPermissionsSpec s args s').mpr hspec
  exact effect_circuit_full_complete S setPermissionsE hRest setPermissionsGuardEncodes s args s' hapex

theorem satisfying_witness_proves_full_state
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SetPermissionsArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S setPermissionsE (encodeE S setPermissionsE s args s')) :
    SetPermissionsSpec s args.actor args.cell args.p s' :=
  setPermissionsA_full_sound S hN hL hRest hLog s args s' hwf hwf' h

/-! ## §3 — THE EXECUTOR-DERIVED CONCRETE WITNESS (the bytes the Rust prover proves). -/

/-- Concrete 3-cell kernel (balances 100/5/50). -/
def kCells : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun c => if c = 0 then .record [("balance", .int 100)]
                     else if c = 1 then .record [("balance", .int 5)]
                     else if c = 2 then .record [("balance", .int 50)]
                     else default
    caps := fun _ => [] }

def s0 : RecChainedState := { kernel := kCells, log := [] }

/-- The good args: actor 0 = cell 0 (self-owned ⇒ authorized, Live), set its permissions slot to 7. -/
def goodArgs : SetPermissionsArgs := { actor := 0, cell := 0, p := 7 }

def goodPost : RecChainedState := (execFullA s0 (.setPermissionsA 0 0 7)).getD s0

/-- THE THIRD-CELL FORGERY: the honest permissions write but a MINTED bystander cell 2 (50 → 999). The
frame-reuse gate (wires 68/69) must reject it. -/
def forgedCell : RecChainedState :=
  { kernel := { goodPost.kernel with
      cell := fun c => if c = 2 then .record [("balance", .int 999)] else goodPost.kernel.cell c }
    log := goodPost.log }

def honestWitness : List Int := setPermissionsWitnessVec s0 goodArgs
def forgedCellWitness : List Int := layoutE setPermissionsE s0 goodArgs forgedCell

#guard honestWitness.length == 74
#guard forgedCellWitness.length == 74
#guard decide (satisfied (effectCircuit setPermissionsE) (fun v => honestWitness.getD v 0))
#guard decide (satisfied (effectCircuit setPermissionsE) (fun v => forgedCellWitness.getD v 0)) == false
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard !(forgedCellWitness.getD 68 0 == forgedCellWitness.getD 69 0)
#guard honestWitness.getD 0 0 == 1

/-! ## §4 — JSON export. -/

def honestWitnessJson : String := witnessJson honestWitness
def forgedCellWitnessJson : String := witnessJson forgedCellWitness

#guard honestWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,3,2000005000050,2000005000050,1000100,1000100,1000000,1000000]"
#guard forgedCellWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,3,2000005000050,2000005000999,1000100,1000100,1000000,1000000]"

#assert_axioms setPermissionsWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.SetPermissionsWitness
