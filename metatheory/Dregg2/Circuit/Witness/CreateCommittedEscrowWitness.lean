/-
# Dregg2.Circuit.Witness.CreateCommittedEscrowWitness — v2-DUAL WITNESS GENERATOR for `createCommittedEscrowA`.

The `execute → prove → verify → anti-ghost` beachhead for `createCommittedEscrowA` (the committed/hidden
escrow create: DEBIT `bal` AND PREPEND an unresolved `EscrowRecord`, gated additionally on a hiding
proof), over the v2-dual framework (`EffectCommit2Dual`). Width 74, five gates. Mirrors
`CreateEscrowWitness` (same dual bal+escrows shape); the only difference is the guard carries
`hidingProof = true`.

Reused: `execFullA … (.createCommittedEscrowA …)`,
`Inst.CreateCommittedEscrowA.createCommittedEscrowA_full_sound`, `effect2dual_circuit_full_complete`.
No `sorry`/`axiom`/`native_decide`; CR portals carried.
-/
import Dregg2.Circuit.Inst.createCommittedEscrowA

namespace Dregg2.Circuit.Witness.CreateCommittedEscrowWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Inst.CreateCommittedEscrowA
open Dregg2.Circuit.Spec.EscrowCommitted
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))
instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §3 — ABSTRACT execute→prove / prove→state (CR portals carried). -/

variable (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
  (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ) (hN : compressNInjective cN) (hLE : listLeafInjective LE)

theorem execute_produces_satisfying_witness
    (hRest : RestIffNoBalEscrows S.RH)
    (s : RecChainedState) (args : CreateCommittedEscrowArgs) (s' : RecChainedState)
    (hspec : CommittedEscrowCreateSpec s args.id args.actor args.creator args.recipient args.asset
        args.amount args.hidingProof s') :
    satisfiedE2Dual S (createCommittedEscrowE D hD LE cN hN hLE)
      (encodeE2Dual S (createCommittedEscrowE D hD LE cN hN hLE) s args s') :=
  effect2dual_circuit_full_complete S (createCommittedEscrowE D hD LE cN hN hLE)
    (fun k k' h => (hRest k k').mpr h) (createCommittedEscrowGuardEncodes D hD LE cN hN hLE) s args s'
    ((apex_iff_committedEscrowCreateSpec D hD LE cN hN hLE s args s').mpr hspec)

theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateCommittedEscrowArgs) (s' : RecChainedState)
    (h : satisfiedE2Dual S (createCommittedEscrowE D hD LE cN hN hLE)
        (encodeE2Dual S (createCommittedEscrowE D hD LE cN hN hLE) s args s')) :
    CommittedEscrowCreateSpec s args.id args.actor args.creator args.recipient args.asset args.amount
      args.hidingProof s' :=
  createCommittedEscrowA_full_sound S D hD LE cN hN hLE hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

def balDigConcrete : (CellId → AssetId → ℤ) → ℤ :=
  fun bal => [0, 1, 2].foldl (fun acc c => acc * 1000000 + bal c 0) 0
def escDigConcrete : List EscrowRecord → ℤ :=
  fun es => es.foldl (fun acc r => acc * 1000000 + ((r.id : ℤ) * 1000 + r.amount)) (es.length : ℤ)
def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ)
def lhConcrete : List Turn → ℤ :=
  fun log => log.foldl (fun acc t => acc * 1000000 + ((t.actor : ℤ) * 1000 + t.src)) (log.length : ℤ)
def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

def balCompC : ActiveComponent RecChainedState CreateCommittedEscrowArgs :=
  { digest    := fun k => balDigConcrete k.bal
  , expected  := fun s args =>
      balDigConcrete (recBalCreditCell s.kernel.bal args.creator args.asset (-args.amount))
  , postClause := fun s args post =>
      balDigConcrete post.bal
        = balDigConcrete (recBalCreditCell s.kernel.bal args.creator args.asset (-args.amount))
  , binds := fun _ _ _ h => h, encodes := fun _ _ _ h => h }

def escCompC : ActiveComponent RecChainedState CreateCommittedEscrowArgs :=
  { digest    := fun k => escDigConcrete k.escrows
  , expected  := fun s args =>
      escDigConcrete (parkedRecord args.id args.creator args.recipient args.asset args.amount
        :: s.kernel.escrows)
  , postClause := fun s args post =>
      escDigConcrete post.escrows
        = escDigConcrete (parkedRecord args.id args.creator args.recipient args.asset args.amount
          :: s.kernel.escrows)
  , binds := fun _ _ _ h => h, encodes := fun _ _ _ h => h }

def createCommittedEscrowEC : EffectSpec2Dual RecChainedState CreateCommittedEscrowArgs :=
  { view         := chainView
  , active1      := balCompC
  , active2      := escCompC
  , logUpdate    := some (fun s args => escrowReceiptA args.actor :: s.log)
  , restFrame    := fun _ _ => True
  , guardGates   := createCommittedEscrowGuardGates
  , guardProp    := createCommittedEscrowGuardProp
  , guardWidth   := 1
  , guardEncode  := createCommittedEscrowGuardEncode
  , guardLocal   := createCommittedEscrowGuardLocal
  , guardWidth_le := by decide }

/-- Pre-state: actor=creator 0 (self-authority), bal[0][0]=100, accounts {0,1,2}, no escrows. -/
def kPre : RecordKernelState :=
  { accounts := {0, 1, 2}, cell := fun _ => default, caps := fun _ => []
  , bal := fun c _ => if c = 0 then 100 else 0 }
def sPre : RecChainedState := { kernel := kPre, log := [] }
/-- Args: id 1, actor/creator 0, recipient 1, asset 0, amount 30, hidingProof TRUE (the extra gate). -/
def argsRef : CreateCommittedEscrowArgs :=
  { id := 1, actor := 0, creator := 0, recipient := 1, asset := 0, amount := 30, hidingProof := true }
def sPost : RecChainedState := (execFullA sPre (.createCommittedEscrowA 1 0 0 1 0 30 true)).getD sPre

/-- THE FORGERY: honest debit + park, but a THIRD cell (2) is ALSO minted bal 0 → 999 (comp1 68≠69). -/
def sForged : RecChainedState :=
  { kernel := { kPre with
      bal := fun c _ => if c = 0 then 70 else if c = 2 then 999 else 0
      escrows := parkedRecord 1 0 1 0 30 :: kPre.escrows }
  , log := escrowReceiptA 0 :: sPre.log }

def witnessOf (s : RecChainedState) (args : CreateCommittedEscrowArgs) (s' : RecChainedState) :
    List Int :=
  (List.range createCommittedEscrowEC.traceWidth).map
    (fun w => encodeE2Dual SC createCommittedEscrowEC s args s' w)

def createCommittedEscrowWitnessVec (s : RecChainedState) (args : CreateCommittedEscrowArgs) :
    List Int :=
  match execFullA s (.createCommittedEscrowA args.id args.actor args.creator args.recipient args.asset
      args.amount args.hidingProof) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

def honestWitness : List Int := createCommittedEscrowWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

#guard honestWitness.length == 74
#guard decide (satisfied (effectCircuit2Dual createCommittedEscrowEC)
  (encodeE2Dual SC createCommittedEscrowEC sPre argsRef sPost))
#guard decide (satisfied (effectCircuit2Dual createCommittedEscrowEC)
  (encodeE2Dual SC createCommittedEscrowEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0
#guard honestWitness.getD 0 0 == 1

/-! ## §5 — JSON export. -/

def emittedCCE : EmittedDescriptor :=
  emittedEffect2Dual "dregg-createCommittedEscrowA-v2" createCommittedEscrowEC
def descriptorJson : String := emitDescriptorJson emittedCCE
def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedCCE.constraints.length == 5
#guard emittedCCE.traceWidth == 74

-- Golden pins (the bytes the Rust `lean_executor_derived_create_committed_escrow` test pastes).
#guard honestWitness.getD 68 0 == 70000000000000 ∧ honestWitness.getD 70 0 == 1001030
#guard forgedWitness.getD 68 0 == 70000000000999 ∧ forgedWitness.getD 70 0 == 1001030

#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.CreateCommittedEscrowWitness
