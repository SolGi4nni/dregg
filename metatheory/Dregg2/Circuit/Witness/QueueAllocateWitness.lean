/-
# Dregg2.Circuit.Witness.QueueAllocateWitness — the WITNESS GENERATOR for `queueAllocateA` (v2).

Mirrors the mint/noteCreate/noteSpend witness generators, for `queueAllocateA` — the FIFO-queue
allocate (touched component = the `queues` LIST of `QueueRecord`; guard = state-authority ∧
id-freshness; the log GROWS by the allocate receipt). The concrete digest reads each `QueueRecord`'s
`id`/`owner`/`capacity`/`buffer`-length positionally, so a forged queue-list (a tampered bystander
queue record) is visible to the BIND gate.

Reuses (not re-proved): `Inst.QueueAllocateA.queueAllocateA_full_sound`,
`effect2_circuit_full_complete`, `encodeE2`. No `sorry`/`admit`/`axiom`/`native_decide`.
`#assert_axioms` whitelists exactly `{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Circuit.Inst.queueAllocateA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.QueueAllocateWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.QueueAllocateA
open Dregg2.Circuit.Spec.QueueFifoCore
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — decidability re-exports. -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

instance {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args) (a : Assignment) :
    Decidable (satisfiedE2 S E a) := by unfold satisfiedE2; infer_instance

/-! ## §1 — the REAL (Poseidon2 CR-grounded) commitment surface.

The queue-list digest is now `Poseidon2Surface.refP2` (the CR-grounded reference sponge realizing the
REAL `babyBearD4W16` Poseidon2) over the FIELD-BINDING `encQueueRec` (which binds the WHOLE buffer, not
just `buffer.length % 1000`, and `capacity` in full). The log hash binds `src`/`dst` (the old
`lhConcrete` dropped them). -/

open Dregg2.Circuit.Poseidon2Surface (recListDigest encQueueRec turnLogDigest)

def qDigConcrete : List QueueRecord → ℤ := recListDigest encQueueRec

/-- Concrete rest hash: a field-count of the non-`queues` components. -/
def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7
            + (k.commitments.length : ℤ) * 11 + (k.escrows.length : ℤ) * 13

/-- Concrete log hash: the REAL `refP2` sponge over the FULL `encTurnRec` (binds `src`/`dst`). -/
def lhConcrete : List Turn → ℤ := turnLogDigest

def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

/-- The concrete `ActiveComponent` for queueAllocate: digest equality on the queue list. -/
def qActiveConcrete : ActiveComponent RecChainedState AllocateArgs where
  digest    := fun k => qDigConcrete k.queues
  expected  := fun s args =>
    qDigConcrete (freshQueue args.id args.actor args.cap :: s.kernel.queues)
  postClause := fun s args post =>
    qDigConcrete post.queues = qDigConcrete (freshQueue args.id args.actor args.cap :: s.kernel.queues)
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def queueAllocateEConcrete : EffectSpec2 RecChainedState AllocateArgs where
  view         := chainView
  active       := qActiveConcrete
  logUpdate    := some (fun s args => allocateReceipt args.actor args.cell :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := allocateGuardGates
  guardProp    := allocateGuardProp
  guardWidth   := 1
  guardEncode  := allocateGuardEncode
  guardLocal   := allocateGuardLocal
  guardWidth_le := by decide

/-! ## §2 — THE WITNESS GENERATOR. -/

def witnessOf (s : RecChainedState) (args : AllocateArgs) (s' : RecChainedState) : List Int :=
  (List.range queueAllocateEConcrete.traceWidth).map
    (fun w => encodeE2 SC queueAllocateEConcrete s args s' w)

def queueAllocateWitnessVec (s : RecChainedState) (args : AllocateArgs) : List Int :=
  match execFullA s (.queueAllocateA args.id args.actor args.cell args.cap) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem queueAllocateWitnessVec_commit {s s' : RecChainedState} {args : AllocateArgs}
    (h : execFullA s (.queueAllocateA args.id args.actor args.cell args.cap) = some s') :
    queueAllocateWitnessVec s args = witnessOf s args s' := by
  unfold queueAllocateWitnessVec; rw [h]

theorem witnessOf_get (s : RecChainedState) (args : AllocateArgs) (s' : RecChainedState)
    (w : Nat) (hw : w < queueAllocateEConcrete.traceWidth) :
    (witnessOf s args s')[w]'(by simpa [witnessOf] using hw)
      = encodeE2 SC queueAllocateEConcrete s args s' w := by
  unfold witnessOf; rw [List.getElem_map, List.getElem_range]

/-! ## §3 — the EXECUTE → PROVE / PROVE → SPEC theorems (abstract surface). -/

variable (S : Surface2) (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
  (hN : compressNInjective cN) (hLE : ListCommit.listLeafInjective LE)

theorem execute_produces_satisfying_witness
    (hRest : RestIffNoQueues S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : AllocateArgs) (s' : RecChainedState)
    (hspec : QueueAllocateSpec s args.id args.actor args.cell args.cap s') :
    satisfiedE2 S (queueAllocateE LE cN hN hLE) (encodeE2 S (queueAllocateE LE cN hN hLE) s args s') := by
  refine effect2_circuit_full_complete S (queueAllocateE LE cN hN hLE)
    (fun k k' h => (hRest k k').mpr h) (allocateGuardEncodes LE cN hN hLE) s args s' ?_
  exact (apex_iff_queueAllocateSpec LE cN hN hLE s args s').mpr hspec

theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoQueues S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : AllocateArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (queueAllocateE LE cN hN hLE) (encodeE2 S (queueAllocateE LE cN hN hLE) s args s')) :
    QueueAllocateSpec s args.id args.actor args.cell args.cap s' :=
  queueAllocateA_full_sound S LE cN hN hLE hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

/-- The concrete pre-kernel: cells {0,1}, an existing bystander queue (id 5, owner 1, cap 4); the
allocated id 9 is FRESH (so the id-freshness guard passes). Actor 0 = cell 0 (self-auth). -/
def kQ0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => default
    caps := fun _ => []
    queues := [{ id := 5, owner := 1, capacity := 4, buffer := [] }] }

def sQ0 : RecChainedState := { kernel := kQ0, log := [] }

/-- The good allocate args: actor 0 allocates fresh queue id 9 over cell 0 with capacity 8. -/
def goodQAArgs : AllocateArgs := { id := 9, actor := 0, cell := 0, cap := 8 }

def goodQAPost : RecChainedState :=
  (execFullA sQ0 (.queueAllocateA goodQAArgs.id goodQAArgs.actor goodQAArgs.cell goodQAArgs.cap)).getD sQ0

/-- **THE FORGERY:** the fresh queue is honest, but the BYSTANDER queue record (id 5) has its capacity
rewritten (4 → 999) — a tampered queue side-table. The BIND digest gate catches the forged list. -/
def forgedThirdQueue : RecChainedState :=
  { goodQAPost with kernel := { goodQAPost.kernel with
      queues := [freshQueue 9 0 8, { id := 5, owner := 1, capacity := 999, buffer := [] }] } }

def honestWitness : List Int := queueAllocateWitnessVec sQ0 goodQAArgs
def forgedWitness : List Int := witnessOf sQ0 goodQAArgs forgedThirdQueue

#guard honestWitness.length == 72
#guard forgedWitness.length == 72

#guard decide (satisfiedE2 SC queueAllocateEConcrete (encodeE2 SC queueAllocateEConcrete sQ0 goodQAArgs goodQAPost))
#guard honestWitness.getD 0 0 == 1
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0

#guard decide (satisfiedE2 SC queueAllocateEConcrete (encodeE2 SC queueAllocateEConcrete sQ0 goodQAArgs forgedThirdQueue)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- compDigPost ≠ compDigExpected
#guard forgedWitness.getD 0 0 == 1
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0

/-! ## §5 — JSON export. -/

def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

def queueAllocateDescriptorJson : String := emitDescriptorJson queueAllocateAEmitted

#guard (queueAllocateDescriptorJson == r#"{"name":"dregg-queueAllocateA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#)

/-! ## §6 — axiom-hygiene tripwires. -/

#assert_axioms queueAllocateWitnessVec_commit
#assert_axioms witnessOf_get
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.QueueAllocateWitness
