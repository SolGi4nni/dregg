/-
# Dregg2.Circuit.Witness.RefusalWitness — execute→prove→verify→anti-ghost for `refusalA`.

This amplifies the `Transfer` verifiable-execution beachhead (`Dregg2.Circuit.TransferWitness`) to the
cell-state-audit effect `refusalA` (writes the `"refusal"` audit slot to `1`), through the GENERIC v1
framework (`EffectCommit`). The pieces already proved and REUSED (not re-proved):

  * `Exec.execFullA` — the REAL chained executor. `execFullA s (.refusalA actor cell) = some s'` IS the
    executor computing the post-state (definitionally `stateStep s refusalField actor cell (.int 1)`).
  * `Spec.CellStateAudit.execFullA_refusalA_iff_spec` — executor ⟺ `RefusalSpec` (both directions).
  * `Inst.RefusalA.{refusalE, apex_iff_refusalSpec, refusalA_full_sound}` — the v1 instance + the
    crown-jewel `satisfying witness ⇒ RefusalSpec`.
  * `EffectCommit.{encodeE, satisfiedE, effect_circuit_full_complete}` — the generic full-state circuit.

THE PIECES THIS MODULE SUPPLIES (the `TransferWitness`/`EmitEventWitness` pattern, per effect):

  (1) `refusalWitnessVec : RecChainedState → RefusalArgs → List Int` — the executor-driven witness
      generator: RUNS `execFullA` and lays out the full-state witness (digest columns from the concrete
      surface `Witness.Common.SConc`) via `layoutE`.
  (2) `execute_produces_satisfying_witness` — a committed `execFullA` step ⇒ the witness SATISFIES.
  (3) `satisfying_witness_proves_full_state` — any satisfying witness proves the full `RefusalSpec`.
  (4) the concrete `#guard`s: the EXECUTOR-DERIVED honest witness SATISFIES; a REAL forged post-state
      (a minted bystander cell 2) yields a vector the circuit REJECTS — a real UNSAT (the frame-reuse
      gate, the anti-ghost tooth end-to-end).
  (5) the JSON the Rust `lean_executor_derived_refusal` prover proves+verifies (honest) / rejects.

No `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Dregg2.Circuit.Witness.Common
import Dregg2.Circuit.Inst.refusalA
import Dregg2.Circuit.Spec.cellstateaudit

namespace Dregg2.Circuit.Witness.RefusalWitness

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Witness.Common
open Dregg2.Circuit.Inst.RefusalA
open Dregg2.Circuit.Spec.CellStateAudit
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §1 — THE WITNESS GENERATOR: `execute → satisfying assignment`. -/

/-- **`refusalWitnessVec s args`** — the executor-driven witness generator. Runs
`execFullA s (.refusalA …)`; on commit lays out the full-state witness for the executor's post-state,
every digest column filled by the concrete commitment surface; on a fail-closed turn falls back to the
pre-state (a guard-failing vector). -/
def refusalWitnessVec (s : RecChainedState) (args : RefusalArgs) : List Int :=
  match execFullA s (.refusalA args.actor args.cell) with
  | some s' => layoutE refusalE s args s'
  | none    => layoutE refusalE s args s

/-- **`refusalWitnessVec` IS `layoutE` of the EXECUTOR's post-state** (the some-branch unfold). -/
theorem refusalWitnessVec_commit {s s' : RecChainedState} {args : RefusalArgs}
    (h : execFullA s (.refusalA args.actor args.cell) = some s') :
    refusalWitnessVec s args = layoutE refusalE s args s' := by
  unfold refusalWitnessVec; rw [h]

/-! ## §2 — THE EXECUTE → PROVE THEOREM (abstract surface, CR portals carried). -/

/-- **`execute_produces_satisfying_witness` — the execute→prove direction.** A committed `execFullA`
refusal step makes the full-state witness `encodeE … s args s'` SATISFY the full-state circuit. Reuses
`effect_circuit_full_complete` via `apex_iff_refusalSpec` ∘ `execFullA_refusalA_iff_spec`. -/
theorem execute_produces_satisfying_witness
    (S : CommitSurface) (hRest : RestHashIffFrame S.RH)
    {s s' : RecChainedState} {args : RefusalArgs}
    (h : execFullA s (.refusalA args.actor args.cell) = some s') :
    satisfiedE S refusalE (encodeE S refusalE s args s') := by
  have hspec : RefusalSpec s args.actor args.cell s' :=
    (execFullA_refusalA_iff_spec s args.actor args.cell s').mp h
  have hapex : refusalE.apex s args s' := (apex_iff_refusalSpec s args s').mpr hspec
  exact effect_circuit_full_complete S refusalE hRest refusalGuardEncodes s args s' hapex

/-- **`satisfying_witness_proves_full_state` — the verify→accept direction (soundness).** ANY witness
satisfying the full-state circuit proves the complete declarative `RefusalSpec`. Reuses
`refusalA_full_sound`; carries the standard Poseidon-CR portals + `AccountsWF` on both states. -/
theorem satisfying_witness_proves_full_state
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RefusalArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S refusalE (encodeE S refusalE s args s')) :
    RefusalSpec s args.actor args.cell s' :=
  refusalA_full_sound S hN hL hRest hLog s args s' hwf hwf' h

/-! ## §3 — THE EXECUTOR-DERIVED CONCRETE WITNESS (the bytes the Rust prover proves).

A concrete THREE-cell pre-state {0,1,2} (balances 100/5/50), empty log; actor 0 (= cell 0, self-owned ⇒
authorized) refuses cell 0 (Live). We RUN the executor and materialize the witness. The forgery is a
REAL post-state minting a bystander cell 2 (50 → 999) — the frame-reuse gate (68/69) rejects. -/

/-- Concrete 3-cell kernel (balances 100/5/50). -/
def kCells : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun c => if c = 0 then .record [("balance", .int 100)]
                     else if c = 1 then .record [("balance", .int 5)]
                     else if c = 2 then .record [("balance", .int 50)]
                     else default
    caps := fun _ => [] }

/-- Concrete pre-state: the 3-cell kernel with an empty log. -/
def s0 : RecChainedState := { kernel := kCells, log := [] }

/-- The good args: actor 0 = cell 0 (self-owned ⇒ authorized), refuse cell 0 (Live). -/
def goodArgs : RefusalArgs := { actor := 0, cell := 0 }

/-- The honest executor post-state (= the refusal-slot write). -/
def goodPost : RecChainedState := (execFullA s0 (.refusalA 0 0)).getD s0

/-- THE THIRD-CELL FORGERY: the honest refusal write but a MINTED bystander cell 2 (50 → 999). The
frame-reuse gate (`frameDigPre = frameDigPost`, wires 68/69) must reject it. -/
def forgedCell : RecChainedState :=
  { kernel := { goodPost.kernel with
      cell := fun c => if c = 2 then .record [("balance", .int 999)] else goodPost.kernel.cell c }
    log := goodPost.log }

/-- The honest executor-derived witness vector. -/
def honestWitness : List Int := refusalWitnessVec s0 goodArgs
/-- The third-cell-forged witness vector. -/
def forgedCellWitness : List Int := layoutE refusalE s0 goodArgs forgedCell

-- (1) the witnesses have the framework trace width.
#guard honestWitness.length == 74
#guard forgedCellWitness.length == 74

-- (2) THE EXECUTE→PROVE GUARANTEE: the executor-derived witness SATISFIES the full-state circuit.
#guard decide (satisfied (effectCircuit refusalE) (fun v => honestWitness.getD v 0))

-- (3) THE ANTI-GHOST TOOTH (real UNSAT): the forged post-state FAILS the circuit, SPECIFICALLY on the
--     frame-reuse gate (68 ≠ 69) — the minted bystander shows up.
#guard decide (satisfied (effectCircuit refusalE) (fun v => forgedCellWitness.getD v 0)) == false
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0            -- frame: pre = post
#guard !(forgedCellWitness.getD 68 0 == forgedCellWitness.getD 69 0) -- cell forgery: REJECTED here
#guard honestWitness.getD 0 0 == 1                                    -- guard propBit = 1

/-! ## §4 — JSON export (the bytes the Rust prover consumes). -/

/-- The honest executor-derived witness, as the JSON array the Rust prover proves+verifies. -/
def honestWitnessJson : String := witnessJson honestWitness
/-- The third-cell-forged witness, as the JSON array the Rust prover REJECTS (frame-reuse UNSAT). -/
def forgedCellWitnessJson : String := witnessJson forgedCellWitness

-- The exact bytes the Rust `lean_executor_derived_refusal` test pastes (goldens pin them so an
-- executor/surface drift is caught here first).
#guard honestWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,3,2000005000050,2000005000050,1000100,1000100,1000000,1000000]"
#guard forgedCellWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,3,2000005000050,2000005000999,1000100,1000100,1000000,1000000]"

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms refusalWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.RefusalWitness
