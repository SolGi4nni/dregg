/-
# Dregg2.Circuit.Witness.IncrementNonceWitness — execute→prove→verify→anti-ghost for `incrementNonceA`.

Amplifies the `Transfer` beachhead to the cell-touching monotone effect `incrementNonceA` through the
v1 framework (`EffectCommit`). REUSED (not re-proved):

  * `Exec.execFullA` — the real chained executor (`.incrementNonceA actor cell n` arm = `stateStep …
    nonceField …`). `execFullA s (.incrementNonceA …) = some s'` IS the executor computing the post.
  * `Spec.CellStateMonotone.execFullA_incrementNonce_iff_spec` — executor ⟺ `IncrementNonceSpec`.
  * `Inst.IncrementNonceA.{incrementNonceE, apex_iff_incrementNonceSpec, incrementNonceA_full_sound}`.
  * `EffectCommit.{encodeE, satisfiedE, effect_circuit_full_complete}`.

SUPPLIED (the `TransferWitness` pattern): `incrementNonceWitnessVec` (runs `execFullA`, lays out the
full-state witness via `Witness.Common.layoutE`); `execute_produces_satisfying_witness` /
`satisfying_witness_proves_full_state` (the two halves, reusing the above); the concrete `#guard`s; the
JSON the Rust `lean_executor_derived_increment_nonce` prover proves+verifies / rejects.

ANTI-GHOST NOTE: the CONCRETE leaf hash `Witness.Common.SConc.CH = chConcrete = balOf` is BALANCE-ONLY
(a toy leaf the `#guard`s can `decide`). The nonce write is a DISTINCT slot, invisible to a
balance-only leaf, so a wrong-NONCE forgery is not catchable by THIS toy surface — the visible
concrete forgeries are a BALANCE-affecting bystander mint (frame-reuse gate) and a tampered receipt
row (log-bind gate). The wrong-nonce soundness is carried by the ABSTRACT `satisfying_witness_proves_
full_state` via the `cellLeafInjective CH` portal (a REAL Poseidon leaf binds the WHOLE `Value`,
nonce included); the concrete toy only needs to exhibit a genuine UNSAT, which the two visible
forgeries do.
-/
import Dregg2.Circuit.Witness.Common
import Dregg2.Circuit.Inst.incrementNonceA
import Dregg2.Circuit.Spec.cellstatemonotone

namespace Dregg2.Circuit.Witness.IncrementNonceWitness

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Witness.Common
open Dregg2.Circuit.Inst.IncrementNonceA
open Dregg2.Circuit.Spec.CellStateMonotone
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §1 — THE WITNESS GENERATOR: `execute → satisfying assignment`. -/

/-- **`incrementNonceWitnessVec s args`** — the executor-driven witness generator. Runs
`execFullA s (.incrementNonceA …)`; on commit lays out the full-state witness for the executor's
post-state via the concrete surface; on a fail-closed turn falls back to the pre-state. -/
def incrementNonceWitnessVec (s : RecChainedState) (args : IncrementNonceArgs) : List Int :=
  match execFullA s (.incrementNonceA args.actor args.cell args.n) with
  | some s' => layoutE incrementNonceE s args s'
  | none    => layoutE incrementNonceE s args s

/-- **`incrementNonceWitnessVec` IS `layoutE` of the EXECUTOR's post-state.** -/
theorem incrementNonceWitnessVec_commit {s s' : RecChainedState} {args : IncrementNonceArgs}
    (h : execFullA s (.incrementNonceA args.actor args.cell args.n) = some s') :
    incrementNonceWitnessVec s args = layoutE incrementNonceE s args s' := by
  unfold incrementNonceWitnessVec; rw [h]

/-! ## §2 — THE EXECUTE → PROVE / PROVE → ACCEPT theorems (reusing existing machinery). -/

/-- **`execute_produces_satisfying_witness` — execute→prove.** A committed `execFullA` nonce bump
makes the full-state witness SATISFY the circuit. Reuses `effect_circuit_full_complete` via
`apex_iff_incrementNonceSpec` ∘ `execFullA_incrementNonce_iff_spec`. -/
theorem execute_produces_satisfying_witness
    (S : CommitSurface) (hRest : RestHashIffFrame S.RH)
    {s s' : RecChainedState} {args : IncrementNonceArgs}
    (h : execFullA s (.incrementNonceA args.actor args.cell args.n) = some s') :
    satisfiedE S incrementNonceE (encodeE S incrementNonceE s args s') := by
  have hspec : IncrementNonceSpec s args.actor args.cell args.n s' :=
    (execFullA_incrementNonce_iff_spec s args.actor args.cell args.n s').mp h
  have hapex : incrementNonceE.apex s args s' := (apex_iff_incrementNonceSpec s args s').mpr hspec
  exact effect_circuit_full_complete S incrementNonceE hRest incrementNonceGuardEncodes s args s' hapex

/-- **`satisfying_witness_proves_full_state` — prove→accept (soundness).** ANY satisfying witness
proves the complete declarative `IncrementNonceSpec`. Reuses `incrementNonceA_full_sound`. -/
theorem satisfying_witness_proves_full_state
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : IncrementNonceArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S incrementNonceE (encodeE S incrementNonceE s args s')) :
    IncrementNonceSpec s args.actor args.cell args.n s' :=
  incrementNonceA_full_sound S hN hL hRest hLog s args s' hwf hwf' h

/-! ## §3 — THE EXECUTOR-DERIVED CONCRETE WITNESS.

A concrete 3-cell pre-state {0,1,2} (balances 100/5/50, empty log); actor 0 (owner) bumps cell 0's
nonce to 7. We RUN the executor and materialize the witness. Visible forgeries: a minted bystander
cell 2 (50 → 999, frame-reuse gate 68/69), and a tampered receipt row (log-bind gate 72/73). -/

def kCells : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun c => if c = 0 then .record [("balance", .int 100)]
                     else if c = 1 then .record [("balance", .int 5)]
                     else if c = 2 then .record [("balance", .int 50)]
                     else default
    caps := fun _ => [] }

def s0 : RecChainedState := { kernel := kCells, log := [] }
def goodArgs : IncrementNonceArgs := { actor := 0, cell := 0, n := 7 }
def goodPost : RecChainedState :=
  (execFullA s0 (.incrementNonceA goodArgs.actor goodArgs.cell goodArgs.n)).getD s0

/-- THE THIRD-CELL FORGERY: honest nonce bump but a MINTED bystander cell 2 (50 → 999). Frame-reuse
gate (68/69) rejects. -/
def forgedCell : RecChainedState :=
  { kernel := { goodPost.kernel with
      cell := fun c => if c = 2 then .record [("balance", .int 999)] else goodPost.kernel.cell c }
    log := goodPost.log }

/-- THE LOG FORGERY: honest kernel but a forged receipt row (actor 9). Log-bind gate (72/73) rejects. -/
def forgedLog : RecChainedState :=
  { kernel := goodPost.kernel, log := { actor := 9, src := 0, dst := 0, amt := 0 } :: s0.log }

def honestWitness : List Int := incrementNonceWitnessVec s0 goodArgs
def forgedCellWitness : List Int := layoutE incrementNonceE s0 goodArgs forgedCell
def forgedLogWitness : List Int := layoutE incrementNonceE s0 goodArgs forgedLog

#guard honestWitness.length == 74
#guard forgedCellWitness.length == 74
#guard forgedLogWitness.length == 74

-- THE EXECUTE→PROVE GUARANTEE: the executor-derived witness SATISFIES the circuit.
#guard decide (satisfied (effectCircuit incrementNonceE) (fun v => honestWitness.getD v 0))
-- THE ANTI-GHOST TEETH (real UNSAT): both forged post-states FAIL the circuit.
#guard decide (satisfied (effectCircuit incrementNonceE) (fun v => forgedCellWitness.getD v 0)) == false
#guard decide (satisfied (effectCircuit incrementNonceE) (fun v => forgedLogWitness.getD v 0)) == false
-- ...and SPECIFICALLY at the named gates.
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard !(forgedCellWitness.getD 68 0 == forgedCellWitness.getD 69 0)  -- cell forgery: frame gate
#guard honestWitness.getD 72 0 == honestWitness.getD 73 0
#guard !(forgedLogWitness.getD 72 0 == forgedLogWitness.getD 73 0)    -- log forgery: log gate

/-! ## §4 — JSON export (the bytes the Rust prover consumes). -/

def honestWitnessJson : String := witnessJson honestWitness
def forgedCellWitnessJson : String := witnessJson forgedCellWitness
def forgedLogWitnessJson : String := witnessJson forgedLogWitness

-- (no JSON byte pin: Common.lhConcrete is the CR-grounded turnLogDigest)
#guard !(honestWitnessJson == forgedCellWitnessJson)
#guard !(honestWitnessJson == forgedLogWitnessJson)

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms incrementNonceWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.IncrementNonceWitness
