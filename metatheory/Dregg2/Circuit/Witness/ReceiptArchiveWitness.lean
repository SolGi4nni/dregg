/-
# Dregg2.Circuit.Witness.ReceiptArchiveWitness — execute→prove→verify→anti-ghost for `receiptArchiveA`.

Amplifies the `Transfer` verifiable-execution beachhead to the cell-state-audit effect `receiptArchiveA`
(writes the `"lifecycle"` RECORD slot to `1`), through the GENERIC v1 framework (`EffectCommit`). The
SAME shape as `RefusalWitness` (a single touched cell + a growing receipt log), differing only in which
audit slot is written. The pieces reused (not re-proved):

  * `Exec.execFullA` — `execFullA s (.receiptArchiveA actor cell) = some s'` IS the executor's post-state.
  * `Spec.CellStateAudit.execFullA_receiptArchiveA_iff_spec` — executor ⟺ `ReceiptArchiveSpec`.
  * `Inst.ReceiptArchiveA.{receiptArchiveE, apex_iff_ReceiptArchiveSpec, receiptArchiveA_full_sound}`.
  * `EffectCommit.{encodeE, satisfiedE, effect_circuit_full_complete}` + `Witness.Common.{SConc,layoutE}`.
-/
import Dregg2.Circuit.Witness.Common
import Dregg2.Circuit.Inst.receiptArchiveA
import Dregg2.Circuit.Spec.cellstateaudit

namespace Dregg2.Circuit.Witness.ReceiptArchiveWitness

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Witness.Common
open Dregg2.Circuit.Inst.ReceiptArchiveA
open Dregg2.Circuit.Spec.CellStateAudit
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §1 — THE WITNESS GENERATOR: `execute → satisfying assignment`. -/

/-- **`receiptArchiveWitnessVec s args`** — runs `execFullA s (.receiptArchiveA …)`; on commit lays out
the full-state witness for the executor's post-state, digest columns from the concrete surface. -/
def receiptArchiveWitnessVec (s : RecChainedState) (args : ReceiptArchiveArgs) : List Int :=
  match execFullA s (.receiptArchiveA args.actor args.cell) with
  | some s' => layoutE receiptArchiveE s args s'
  | none    => layoutE receiptArchiveE s args s

theorem receiptArchiveWitnessVec_commit {s s' : RecChainedState} {args : ReceiptArchiveArgs}
    (h : execFullA s (.receiptArchiveA args.actor args.cell) = some s') :
    receiptArchiveWitnessVec s args = layoutE receiptArchiveE s args s' := by
  unfold receiptArchiveWitnessVec; rw [h]

/-! ## §2 — THE EXECUTE → PROVE / PROVE → STATE THEOREMS (abstract surface, CR portals carried). -/

theorem execute_produces_satisfying_witness
    (S : CommitSurface) (hRest : RestHashIffFrame S.RH)
    {s s' : RecChainedState} {args : ReceiptArchiveArgs}
    (h : execFullA s (.receiptArchiveA args.actor args.cell) = some s') :
    satisfiedE S receiptArchiveE (encodeE S receiptArchiveE s args s') := by
  have hspec : ReceiptArchiveSpec s args.actor args.cell s' :=
    (execFullA_receiptArchiveA_iff_spec s args.actor args.cell s').mp h
  have hapex : receiptArchiveE.apex s args s' := (apex_iff_ReceiptArchiveSpec s args s').mpr hspec
  exact effect_circuit_full_complete S receiptArchiveE hRest receiptArchiveGuardEncodes s args s' hapex

theorem satisfying_witness_proves_full_state
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ReceiptArchiveArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S receiptArchiveE (encodeE S receiptArchiveE s args s')) :
    ReceiptArchiveSpec s args.actor args.cell s' :=
  receiptArchiveA_full_sound S hN hL hRest hLog s args s' hwf hwf' h

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

/-- Actor 0 = cell 0 (self-owned ⇒ authorized), archive a receipt for cell 0 (Live). -/
def goodArgs : ReceiptArchiveArgs := { actor := 0, cell := 0 }

def goodPost : RecChainedState := (execFullA s0 (.receiptArchiveA 0 0)).getD s0

/-- THE THIRD-CELL FORGERY: the honest lifecycle write but a MINTED bystander cell 2 (50 → 999). The
frame-reuse gate (wires 68/69) must reject it. -/
def forgedCell : RecChainedState :=
  { kernel := { goodPost.kernel with
      cell := fun c => if c = 2 then .record [("balance", .int 999)] else goodPost.kernel.cell c }
    log := goodPost.log }

def honestWitness : List Int := receiptArchiveWitnessVec s0 goodArgs
def forgedCellWitness : List Int := layoutE receiptArchiveE s0 goodArgs forgedCell

#guard honestWitness.length == 74
#guard forgedCellWitness.length == 74

-- THE EXECUTE→PROVE GUARANTEE: the executor-derived witness SATISFIES the full-state circuit.
#guard decide (satisfied (effectCircuit receiptArchiveE) (fun v => honestWitness.getD v 0))

-- THE ANTI-GHOST TOOTH (real UNSAT): the forged post-state FAILS on the frame-reuse gate (68 ≠ 69).
#guard decide (satisfied (effectCircuit receiptArchiveE) (fun v => forgedCellWitness.getD v 0)) == false
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard !(forgedCellWitness.getD 68 0 == forgedCellWitness.getD 69 0)
#guard honestWitness.getD 0 0 == 1

/-! ## §4 — JSON export (the bytes the Rust prover consumes). -/

def honestWitnessJson : String := witnessJson honestWitness
def forgedCellWitnessJson : String := witnessJson forgedCellWitness

-- The exact bytes the Rust `lean_executor_derived_receipt_archive` test pastes.
-- (no JSON byte pin: Common.lhConcrete is the CR-grounded turnLogDigest)
#guard !(honestWitnessJson == forgedCellWitnessJson)

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms receiptArchiveWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.ReceiptArchiveWitness
