/-
# Dregg2.Circuit.Witness.MakeSovereignWitness — execute→prove→verify→anti-ghost for `makeSovereignA`.

Amplifies the `Transfer` beachhead to the commitment-rebind effect `makeSovereignA` through the v1
framework (`EffectCommit`). REUSED (not re-proved):

  * `Exec.execFullA` — the real chained executor (`.makeSovereignA actor cell` arm = `makeSovereignStep`).
  * `Spec.SovereignCommitment.execFullA_makeSovereignA_iff_spec` — executor ⟺ `MakeSovereignSpec`.
  * `Inst.MakeSovereignA.{makeSovereignE, apex_iff_makeSovereignSpec, makeSovereignA_full_sound}`.
  * `EffectCommit.{encodeE, satisfiedE, effect_circuit_full_complete}`.

SUPPLIED (the `TransferWitness` pattern): `makeSovereignWitnessVec` (runs `execFullA`, lays out via
`Witness.Common.layoutE`); `execute_produces_satisfying_witness` / `satisfying_witness_proves_full_
state`; the concrete `#guard`s; the JSON the Rust `lean_executor_derived_make_sovereign` prover
proves+verifies / rejects.

The rebind DROPS the readable record at the target and installs a commitment-only one, so its balance
field MOVES — the touched-bind gate (70/71) is MEANINGFUL here: a wrong-touched forgery (installing the
wrong rebound value) is a visible UNSAT, alongside the bystander-mint (frame gate 68/69).
-/
import Dregg2.Circuit.Witness.Common
import Dregg2.Circuit.Inst.makeSovereignA
import Dregg2.Circuit.Spec.sovereigncommitment

namespace Dregg2.Circuit.Witness.MakeSovereignWitness

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Witness.Common
open Dregg2.Circuit.Inst.MakeSovereignA
open Dregg2.Circuit.Spec.SovereignCommitment
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §1 — THE WITNESS GENERATOR. -/

/-- **`makeSovereignWitnessVec s args`** — runs `execFullA s (.makeSovereignA …)`; on commit lays out
the full-state witness for the executor's post-state; else falls back to the pre-state. -/
def makeSovereignWitnessVec (s : RecChainedState) (args : MakeSovereignArgs) : List Int :=
  match execFullA s (.makeSovereignA args.actor args.cell) with
  | some s' => layoutE makeSovereignE s args s'
  | none    => layoutE makeSovereignE s args s

theorem makeSovereignWitnessVec_commit {s s' : RecChainedState} {args : MakeSovereignArgs}
    (h : execFullA s (.makeSovereignA args.actor args.cell) = some s') :
    makeSovereignWitnessVec s args = layoutE makeSovereignE s args s' := by
  unfold makeSovereignWitnessVec; rw [h]

/-! ## §2 — THE EXECUTE → PROVE / PROVE → ACCEPT theorems. -/

/-- **`execute_produces_satisfying_witness` — execute→prove.** Reuses `effect_circuit_full_complete`
via `apex_iff_makeSovereignSpec` ∘ `execFullA_makeSovereignA_iff_spec`. -/
theorem execute_produces_satisfying_witness
    (S : CommitSurface) (hRest : RestHashIffFrame S.RH)
    {s s' : RecChainedState} {args : MakeSovereignArgs}
    (h : execFullA s (.makeSovereignA args.actor args.cell) = some s') :
    satisfiedE S makeSovereignE (encodeE S makeSovereignE s args s') := by
  have hspec : MakeSovereignSpec s args.actor args.cell s' :=
    (execFullA_makeSovereignA_iff_spec s args.actor args.cell s').mp h
  have hapex : makeSovereignE.apex s args s' := (apex_iff_makeSovereignSpec s args s').mpr hspec
  exact effect_circuit_full_complete S makeSovereignE hRest makeSovereignGuardEncodes s args s' hapex

/-- **`satisfying_witness_proves_full_state` — prove→accept.** Reuses `makeSovereignA_full_sound`. -/
theorem satisfying_witness_proves_full_state
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MakeSovereignArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S makeSovereignE (encodeE S makeSovereignE s args s')) :
    MakeSovereignSpec s args.actor args.cell s' :=
  makeSovereignA_full_sound S hN hL hRest hLog s args s' hwf hwf' h

/-! ## §3 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

def kCells : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun c => if c = 0 then .record [("balance", .int 100)]
                     else if c = 1 then .record [("balance", .int 5)]
                     else if c = 2 then .record [("balance", .int 50)]
                     else default
    caps := fun _ => [] }

def s0 : RecChainedState := { kernel := kCells, log := [] }
def goodArgs : MakeSovereignArgs := { actor := 0, cell := 0 }
def goodPost : RecChainedState := (execFullA s0 (.makeSovereignA goodArgs.actor goodArgs.cell)).getD s0

/-- THE WRONG-TOUCHED FORGERY: the rebound cell 0 installed with a WRONG value (balance 777). The
touched-bind gate (70/71) rejects. -/
def forgedTouched : RecChainedState :=
  { kernel := { goodPost.kernel with
      cell := fun c => if c = 0 then .record [("balance", .int 777)] else goodPost.kernel.cell c }
    log := goodPost.log }

/-- THE THIRD-CELL FORGERY: a MINTED bystander cell 2 (50 → 999). The frame-reuse gate (68/69) rejects. -/
def forgedCell : RecChainedState :=
  { kernel := { goodPost.kernel with
      cell := fun c => if c = 2 then .record [("balance", .int 999)] else goodPost.kernel.cell c }
    log := goodPost.log }

def honestWitness : List Int := makeSovereignWitnessVec s0 goodArgs
def forgedTouchedWitness : List Int := layoutE makeSovereignE s0 goodArgs forgedTouched
def forgedCellWitness : List Int := layoutE makeSovereignE s0 goodArgs forgedCell

#guard honestWitness.length == 74
#guard forgedTouchedWitness.length == 74
#guard forgedCellWitness.length == 74

#guard decide (satisfied (effectCircuit makeSovereignE) (fun v => honestWitness.getD v 0))
#guard decide (satisfied (effectCircuit makeSovereignE) (fun v => forgedTouchedWitness.getD v 0)) == false
#guard decide (satisfied (effectCircuit makeSovereignE) (fun v => forgedCellWitness.getD v 0)) == false
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0
#guard !(forgedTouchedWitness.getD 70 0 == forgedTouchedWitness.getD 71 0)  -- wrong-touched: touched gate
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard !(forgedCellWitness.getD 68 0 == forgedCellWitness.getD 69 0)        -- bystander: frame gate

/-! ## §4 — JSON export. -/

def honestWitnessJson : String := witnessJson honestWitness
def forgedTouchedWitnessJson : String := witnessJson forgedTouchedWitness
def forgedCellWitnessJson : String := witnessJson forgedCellWitness

-- (no JSON byte pin: Common.lhConcrete is the CR-grounded turnLogDigest)
#guard !(honestWitnessJson == forgedTouchedWitnessJson)
#guard !(honestWitnessJson == forgedCellWitnessJson)

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms makeSovereignWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.MakeSovereignWitness
