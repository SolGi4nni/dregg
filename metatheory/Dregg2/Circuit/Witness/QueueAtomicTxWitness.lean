/-
# Dregg2.Circuit.Witness.QueueAtomicTxWitness — the WITNESS GENERATOR for `queueAtomicTxA` (v3 / triple).

`queueAtomicTxA` is the ALL-OR-NOTHING atomic queue-op batch: it folds a `List QueueTxOpA` through the
chained queue steps, touching THREE non-`cell` components (`queues` + `bal` + `escrows`). This module
supplies the executor-derived witness generator (76-wide, three bind gates), mirroring the other v3
witness modules. A forged ANY-of-the-three post-component is visible to its bind gate.

Reuses (not re-proved): `Inst.QueueAtomicTxA.queueAtomicTxA_full_sound`,
`effect2triple_circuit_full_complete`, `encodeE2Triple`. No `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Dregg2.Circuit.Inst.queueAtomicTxA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.QueueAtomicTxWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit3
open Dregg2.Circuit.Inst.QueueAtomicTxA
open Dregg2.Circuit.Spec.QueueAtomicTx
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — decidability re-exports. -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

instance {St Args : Type} (S : Surface2) (E : EffectSpec2Triple St Args) (a : Assignment) :
    Decidable (satisfiedE2Triple S E a) := by unfold satisfiedE2Triple; infer_instance

/-! ## §1 — the REAL (Poseidon2 CR-grounded) commitment surface.

Every component digest is now `Poseidon2Surface.refP2` (the CR-grounded reference sponge realizing the
REAL `babyBearD4W16` Poseidon2) over FIELD-BINDING encoders. The OLD toy folds dropped fields
(`capacity % 1000`, `amount % 1000`, `src`/`dst` in the log); these bind every field. -/

open Dregg2.Circuit.Poseidon2Surface (refP2 recListDigest encQueueRec encEscrowRec turnLogDigest)

def qDigConcrete : List QueueRecord → ℤ := recListDigest encQueueRec
def eDigConcrete : List EscrowRecord → ℤ := recListDigest encEscrowRec

def balDigConcrete : (CellId → AssetId → ℤ) → ℤ :=
  fun bal => refP2 [bal 0 0, bal 1 0, bal 0 1]

def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7 + (k.commitments.length : ℤ) * 11

def lhConcrete : List Turn → ℤ := turnLogDigest

def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

def eqComponent {β : Type} (read : RecordKernelState → β) (Dg : β → ℤ)
    (expectedVal : RecChainedState → AtomicTxArgs → β) : ActiveComponent RecChainedState AtomicTxArgs where
  digest    := fun k => Dg (read k)
  expected  := fun s args => Dg (expectedVal s args)
  postClause := fun s args post => Dg (read post) = Dg (expectedVal s args)
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def queueAtomicTxEConcrete : EffectSpec2Triple RecChainedState AtomicTxArgs where
  view         := chainView
  active1      := eqComponent (·.queues)  qDigConcrete   (fun s args => atomicTxPostQueues s args)
  active2      := eqComponent (·.bal)     balDigConcrete (fun s args => atomicTxPostBal s args)
  active3      := eqComponent (·.escrows) eDigConcrete   (fun s args => atomicTxPostEscrows s args)
  logUpdate    := some (fun s args =>
    match queueAtomicTxChainA s args.ops with
    | some s1 => escrowReceiptA args.actor :: s1.log
    | none    => s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.swiss = k.swiss ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories
      ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate
      ∧ k'.delegations = k.delegations ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := atomicTxGuardGates
  guardProp    := atomicTxGuardProp
  guardWidth   := 1
  guardEncode  := atomicTxGuardEncode
  guardLocal   := atomicTxGuardLocal
  guardWidth_le := by decide

/-! ## §2 — THE WITNESS GENERATOR. -/

def witnessOf (s : RecChainedState) (args : AtomicTxArgs) (s' : RecChainedState) : List Int :=
  (List.range queueAtomicTxEConcrete.traceWidth).map
    (fun w => encodeE2Triple SC queueAtomicTxEConcrete s args s' w)

def queueAtomicTxWitnessVec (s : RecChainedState) (args : AtomicTxArgs) : List Int :=
  match execFullA s (.queueAtomicTxA args.actor args.ops) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem queueAtomicTxWitnessVec_commit {s s' : RecChainedState} {args : AtomicTxArgs}
    (h : execFullA s (.queueAtomicTxA args.actor args.ops) = some s') :
    queueAtomicTxWitnessVec s args = witnessOf s args s' := by
  unfold queueAtomicTxWitnessVec; rw [h]

theorem witnessOf_get (s : RecChainedState) (args : AtomicTxArgs) (s' : RecChainedState)
    (w : Nat) (hw : w < queueAtomicTxEConcrete.traceWidth) :
    (witnessOf s args s')[w]'(by simpa [witnessOf] using hw)
      = encodeE2Triple SC queueAtomicTxEConcrete s args s' w := by
  unfold witnessOf; rw [List.getElem_map, List.getElem_range]

/-! ## §3 — the EXECUTE → PROVE / PROVE → SPEC theorems (abstract surface). -/

variable (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
  (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
  (hLQ : ListCommit.listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
  (hNE : compressNInjective cNE) (hLE : ListCommit.listLeafInjective LE)

theorem execute_produces_satisfying_witness
    (hRest : RestIffNoQueuesBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : AtomicTxArgs) (s' : RecChainedState)
    (hspec : QueueAtomicTxSpec s args.actor args.ops s') :
    satisfiedE2Triple S (queueAtomicTxE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
      (encodeE2Triple S (queueAtomicTxE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) s args s') := by
  refine effect2triple_circuit_full_complete S (queueAtomicTxE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
    (fun k k' h => (hRest k k').mpr h) (atomicTxGuardEncodes D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
    s args s' ?_
  exact (apex_iff_queueAtomicTxSpec D hD LQ cNQ hNQ hLQ LE cNE hNE hLE s args s').mpr hspec

theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoQueuesBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : AtomicTxArgs) (s' : RecChainedState)
    (h : satisfiedE2Triple S (queueAtomicTxE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
        (encodeE2Triple S (queueAtomicTxE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) s args s')) :
    QueueAtomicTxSpec s args.actor args.ops s' :=
  queueAtomicTxA_full_sound S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS.

The batch is a single `enqueue` op (an all-or-nothing fold of length one): queue 5 (owner 0, room),
ledger holds 100 of asset 0 at cell 0, escrow id 7 fresh. Actor 0 = cell 0 (self-auth). -/

def kA0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => default
    caps := fun _ => []
    queues := [{ id := 5, owner := 0, capacity := 4, buffer := [9] }]
    bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }

def sA0 : RecChainedState := { kernel := kA0, log := [] }

/-- The good atomic batch: actor 0 runs one enqueue op (message 8 onto queue 5, deposit 30, escrow 7). -/
def goodATArgs : AtomicTxArgs :=
  { actor := 0, ops := [QueueTxOpA.enqueue 5 8 0 0 7 0 30] }

def goodATPost : RecChainedState :=
  (execFullA sA0 (.queueAtomicTxA goodATArgs.actor goodATArgs.ops)).getD sA0

/-- **THE FORGERY:** the batch is honest, but a BYSTANDER queue (none here — so we forge the queues
post-list by rewriting the enqueued buffer). The queues BIND gate (68 ≠ 69) catches the tampered FIFO. -/
def forgedQueueBuffer : RecChainedState :=
  { goodATPost with kernel := { goodATPost.kernel with
      queues := goodATPost.kernel.queues.map (fun q => { q with buffer := q.buffer ++ [777] }) } }

def honestWitness : List Int := queueAtomicTxWitnessVec sA0 goodATArgs
def forgedWitness : List Int := witnessOf sA0 goodATArgs forgedQueueBuffer

#guard honestWitness.length == 76
#guard forgedWitness.length == 76

#guard decide (satisfiedE2Triple SC queueAtomicTxEConcrete (encodeE2Triple SC queueAtomicTxEConcrete sA0 goodATArgs goodATPost))
#guard honestWitness.getD 0 0 == 1
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0
#guard honestWitness.getD 72 0 == honestWitness.getD 73 0
#guard honestWitness.getD 74 0 == honestWitness.getD 75 0

#guard decide (satisfiedE2Triple SC queueAtomicTxEConcrete (encodeE2Triple SC queueAtomicTxEConcrete sA0 goodATArgs forgedQueueBuffer)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- queues compDigPost ≠ expected
#guard forgedWitness.getD 0 0 == 1
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0      -- bal honest
#guard forgedWitness.getD 72 0 == forgedWitness.getD 73 0      -- escrows honest

/-! ## §5 — JSON export. -/

def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

def queueAtomicTxDescriptorJson : String := emitDescriptorJson queueAtomicTxAEmitted

#guard (queueAtomicTxDescriptorJson == r#"{"name":"dregg-queueAtomicTxA-v2","trace_width":76,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}},{"lhs":{"t":"var","v":72},"rhs":{"t":"var","v":73}},{"lhs":{"t":"var","v":74},"rhs":{"t":"var","v":75}}]}"#)

/-! ## §6 — axiom-hygiene tripwires. -/

#assert_axioms queueAtomicTxWitnessVec_commit
#assert_axioms witnessOf_get
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.QueueAtomicTxWitness
