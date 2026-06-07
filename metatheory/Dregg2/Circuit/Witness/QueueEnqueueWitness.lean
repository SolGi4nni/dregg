/-
# Dregg2.Circuit.Witness.QueueEnqueueWitness — the WITNESS GENERATOR for `queueEnqueueA` (v3 / triple).

`queueEnqueueA` touches THREE non-`cell` components (`queues` + `bal` + `escrows`) over the
`EffectCommit3` (`EffectSpec2Triple`) framework: enqueue a message + debit a deposit + park an escrow.
This module supplies the executor-derived witness generator (76-wide, three bind gates 68/69, 70/71,
72/73), mirroring the v2 witness modules. Each component's concrete digest reads the post-state, so a
forged ANY-of-the-three component (a tampered bystander queue / a wrong ledger entry / a dropped escrow)
is visible to its bind gate.

Reuses (not re-proved): `Inst.QueueEnqueueA.queueEnqueueA_full_sound`,
`effect2triple_circuit_full_complete`, `encodeE2Triple`. No `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Dregg2.Circuit.Inst.queueEnqueueA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.QueueEnqueueWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit3
open Dregg2.Circuit.Inst.QueueEnqueueA
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

instance {St Args : Type} (S : Surface2) (E : EffectSpec2Triple St Args) (a : Assignment) :
    Decidable (satisfiedE2Triple S E a) := by unfold satisfiedE2Triple; infer_instance

/-! ## §1 — the REAL (Poseidon2 CR-grounded) commitment surface.

Every component digest is now `Poseidon2Surface.refP2` (the CR-grounded reference sponge, realizing the
REAL `babyBearD4W16` Poseidon2 — see `Poseidon2Surface.realRealizedSponge`) over FIELD-BINDING encoders
(`recListDigest encQueueRec`/`encEscrowRec`, `turnLogDigest`). The OLD toy folds dropped fields
(`capacity % 1000`, `src`/`dst` in the log); these bind every field. The `balDigConcrete` ledger digest
is the `refP2` sponge of the demo's `(cell,asset)` entries (positional, injective on the demo domain).
`rhConcrete` is the rest-frame count (unchanged — the rest-frame gate is not the one that bites here). -/

open Dregg2.Circuit.Poseidon2Surface (refP2 recListDigest encQueueRec encEscrowRec turnLogDigest)

/-- The queue-list digest: the REAL `refP2` sponge over the field-binding `encQueueRec` (NO `% 1000`). -/
def qDigConcrete : List QueueRecord → ℤ := recListDigest encQueueRec

/-- The escrow-list digest: the REAL `refP2` sponge over the field-binding `encEscrowRec` (all 9 fields). -/
def eDigConcrete : List EscrowRecord → ℤ := recListDigest encEscrowRec

/-- The per-asset-ledger digest: the REAL `refP2` sponge over the demo's `(cell,asset)` ledger entries
(positional, binding each entry — NO lossy collapse). -/
def balDigConcrete : (CellId → AssetId → ℤ) → ℤ :=
  fun bal => refP2 [bal 0 0, bal 1 0, bal 0 1]

def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7 + (k.commitments.length : ℤ) * 11

/-- The receipt-chain log hash: the REAL `refP2` sponge over the FULL `encTurnRec` (binds `src`/`dst`,
which the old `lhConcrete` DROPPED). -/
def lhConcrete : List Turn → ℤ := turnLogDigest

def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

/-- A digest-equality `ActiveComponent` over a `read`/`expectedVal` pair (binds/encodes = id). -/
def eqComponent {β : Type} (read : RecordKernelState → β) (Dg : β → ℤ)
    (expectedVal : RecChainedState → EnqueueArgs → β) : ActiveComponent RecChainedState EnqueueArgs where
  digest    := fun k => Dg (read k)
  expected  := fun s args => Dg (expectedVal s args)
  postClause := fun s args post => Dg (read post) = Dg (expectedVal s args)
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def queueEnqueueEConcrete : EffectSpec2Triple RecChainedState EnqueueArgs where
  view         := chainView
  active1      := eqComponent (·.queues)  qDigConcrete   (fun s args => enqueuePostQueues s args)
  active2      := eqComponent (·.bal)     balDigConcrete (fun s args => enqueuePostBal s args)
  active3      := eqComponent (·.escrows) eDigConcrete   (fun s args => enqueuePostEscrows s args)
  logUpdate    := some (fun s args => enqueueReceipt args.actor args.cell args.deposit :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.swiss = k.swiss ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories
      ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate
      ∧ k'.delegations = k.delegations ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := enqueueGuardGates
  guardProp    := enqueueGuardProp
  guardWidth   := 1
  guardEncode  := enqueueGuardEncode
  guardLocal   := enqueueGuardLocal
  guardWidth_le := by decide

/-! ## §2 — THE WITNESS GENERATOR. -/

def witnessOf (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState) : List Int :=
  (List.range queueEnqueueEConcrete.traceWidth).map
    (fun w => encodeE2Triple SC queueEnqueueEConcrete s args s' w)

def queueEnqueueWitnessVec (s : RecChainedState) (args : EnqueueArgs) : List Int :=
  match execFullA s (.queueEnqueueA args.id args.m args.actor args.cell args.depId args.dAsset args.deposit) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem queueEnqueueWitnessVec_commit {s s' : RecChainedState} {args : EnqueueArgs}
    (h : execFullA s (.queueEnqueueA args.id args.m args.actor args.cell args.depId args.dAsset args.deposit)
      = some s') :
    queueEnqueueWitnessVec s args = witnessOf s args s' := by
  unfold queueEnqueueWitnessVec; rw [h]

theorem witnessOf_get (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState)
    (w : Nat) (hw : w < queueEnqueueEConcrete.traceWidth) :
    (witnessOf s args s')[w]'(by simpa [witnessOf] using hw)
      = encodeE2Triple SC queueEnqueueEConcrete s args s' w := by
  unfold witnessOf; rw [List.getElem_map, List.getElem_range]

/-! ## §3 — the EXECUTE → PROVE / PROVE → SPEC theorems (abstract surface, full triple-CR portals). -/

variable (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
  (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
  (hLQ : ListCommit.listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
  (hNE : compressNInjective cNE) (hLE : ListCommit.listLeafInjective LE)

theorem execute_produces_satisfying_witness
    (hRest : RestIffNoQueuesBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState)
    (hspec : QueueEnqueueSpec s args.id args.m args.actor args.cell args.depId args.dAsset args.deposit s') :
    satisfiedE2Triple S (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
      (encodeE2Triple S (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) s args s') := by
  refine effect2triple_circuit_full_complete S (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
    (fun k k' h => (hRest k k').mpr h) (enqueueGuardEncodes D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
    s args s' ?_
  exact (apex_iff_queueEnqueueSpec D hD LQ cNQ hNQ hLQ LE cNE hNE hLE s args s').mpr hspec

theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoQueuesBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState)
    (h : satisfiedE2Triple S (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
        (encodeE2Triple S (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) s args s')) :
    QueueEnqueueSpec s args.id args.m args.actor args.cell args.depId args.dAsset args.deposit s' :=
  queueEnqueueA_full_sound S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

/-- The concrete pre-kernel: cells {0,1}; one queue (id 5, owner 0, cap 4, buffer [9]) on cell 0; the
ledger holds 100 of asset 0 at cell 0 (the deposit source). Actor 0 = cell 0 (self-auth), lifecycle
default Live, depId 7 fresh in `escrows`. -/
def kE0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => default
    caps := fun _ => []
    queues := [{ id := 5, owner := 0, capacity := 4, buffer := [9] }]
    bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }

def sE0 : RecChainedState := { kernel := kE0, log := [] }

/-- The good enqueue args: actor 0 enqueues message 8 onto queue 5 over cell 0, deposit 30 of asset 0,
escrow id 7. -/
def goodEQArgs : EnqueueArgs :=
  { id := 5, m := 8, actor := 0, cell := 0, depId := 7, dAsset := 0, deposit := 30 }

def goodEQPost : RecChainedState :=
  (execFullA sE0 (.queueEnqueueA goodEQArgs.id goodEQArgs.m goodEQArgs.actor goodEQArgs.cell
    goodEQArgs.depId goodEQArgs.dAsset goodEQArgs.deposit)).getD sE0

/-- **THE FORGERY:** the enqueue is honest, but the parked escrow's `amount` is forged (the deposit was
30, the post escrow claims 999) — a tampered escrow side-table. The escrow BIND gate (72 ≠ 73) catches it. -/
def forgedEscrowAmount : RecChainedState :=
  { goodEQPost with kernel := { goodEQPost.kernel with
      escrows := goodEQPost.kernel.escrows.map (fun r => { r with amount := 999 }) } }

def honestWitness : List Int := queueEnqueueWitnessVec sE0 goodEQArgs
def forgedWitness : List Int := witnessOf sE0 goodEQArgs forgedEscrowAmount

#guard honestWitness.length == 76
#guard forgedWitness.length == 76

#guard decide (satisfiedE2Triple SC queueEnqueueEConcrete (encodeE2Triple SC queueEnqueueEConcrete sE0 goodEQArgs goodEQPost))
#guard honestWitness.getD 0 0 == 1
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0   -- rest
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0   -- queues bind
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0   -- bal bind
#guard honestWitness.getD 72 0 == honestWitness.getD 73 0   -- escrows bind
#guard honestWitness.getD 74 0 == honestWitness.getD 75 0   -- log

#guard decide (satisfiedE2Triple SC queueEnqueueEConcrete (encodeE2Triple SC queueEnqueueEConcrete sE0 goodEQArgs forgedEscrowAmount)) == false
#guard !(forgedWitness.getD 72 0 == forgedWitness.getD 73 0)   -- escrows compDigPost ≠ expected
#guard forgedWitness.getD 0 0 == 1
#guard forgedWitness.getD 68 0 == forgedWitness.getD 69 0      -- queues still honest
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0      -- bal still honest

/-! ## §5 — JSON export. -/

def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

def queueEnqueueDescriptorJson : String := emitDescriptorJson queueEnqueueAEmitted

#guard (queueEnqueueDescriptorJson == r#"{"name":"dregg-queueEnqueueA-v2","trace_width":76,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}},{"lhs":{"t":"var","v":72},"rhs":{"t":"var","v":73}},{"lhs":{"t":"var","v":74},"rhs":{"t":"var","v":75}}]}"#)

/-! ## §6 — axiom-hygiene tripwires. -/

#assert_axioms queueEnqueueWitnessVec_commit
#assert_axioms witnessOf_get
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.QueueEnqueueWitness
