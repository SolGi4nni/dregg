/-
# Dregg2.Circuit.Witness.CreateEscrowWitness — the v2-DUAL WITNESS GENERATOR for `createEscrowA`.

The `execute → prove → verify → anti-ghost` beachhead for `createEscrowA` (the canonical dual-component
effect: DEBIT `bal` at `(creator,asset)` AND PREPEND an unresolved `EscrowRecord` onto `escrows`), over
the v2-dual framework (`EffectCommit2Dual`). Width 74, five gates (guard + rest + comp1-bal + comp2-escrows
+ log). Mirrors `DelegateWitness` but with TWO touched components.

Reused (not re-proved): `execFullA … (.createEscrowA …)`, `Inst.CreateEscrowA.createEscrowA_full_sound`,
`effect2dual_circuit_full_complete`. No `sorry`/`axiom`/`native_decide`; CR portals carried.
-/
import Dregg2.Circuit.Inst.createEscrowA

namespace Dregg2.Circuit.Witness.CreateEscrowWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Inst.CreateEscrowA
open Dregg2.Circuit.Spec.EscrowHoldingCreate
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

/-- **`execute_produces_satisfying_witness`** — a `EscrowHoldingCreateSpec`-satisfying step makes the
dual witness SATISFY the dual circuit. -/
theorem execute_produces_satisfying_witness
    (hRest : RestIffNoBalEscrows S.RH)
    (s : RecChainedState) (args : CreateEscrowArgs) (s' : RecChainedState)
    (hspec : EscrowHoldingCreateSpec s args.id args.actor args.creator args.recipient args.asset
        args.amount s') :
    satisfiedE2Dual S (createEscrowE D hD LE cN hN hLE)
      (encodeE2Dual S (createEscrowE D hD LE cN hN hLE) s args s') :=
  effect2dual_circuit_full_complete S (createEscrowE D hD LE cN hN hLE)
    (fun k k' h => (hRest k k').mpr h) (createEscrowGuardEncodes D hD LE cN hN hLE) s args s'
    ((apex_iff_escrowHoldingCreateSpec D hD LE cN hN hLE s args s').mpr hspec)

/-- **`satisfying_witness_proves_full_state`** — a satisfying dual witness proves the complete
`EscrowHoldingCreateSpec`. Reuses `createEscrowA_full_sound`. -/
theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateEscrowArgs) (s' : RecChainedState)
    (h : satisfiedE2Dual S (createEscrowE D hD LE cN hN hLE)
        (encodeE2Dual S (createEscrowE D hD LE cN hN hLE) s args s')) :
    EscrowHoldingCreateSpec s args.id args.actor args.creator args.recipient args.asset args.amount s' :=
  createEscrowA_full_sound S D hD LE cN hN hLE hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

/-- Concrete bal digest over carrier {0,1,2} × asset 0 (Horner fold, fits i64). -/
def balDigConcrete : (CellId → AssetId → ℤ) → ℤ :=
  fun bal => [0, 1, 2].foldl (fun acc c => acc * 1000000 + bal c 0) 0

/-- Concrete escrows-list digest: a Horner fold over each record's (id, amount) (base 1000000). -/
def escDigConcrete : List EscrowRecord → ℤ :=
  fun es => es.foldl (fun acc r => acc * 1000000 + ((r.id : ℤ) * 1000 + r.amount)) (es.length : ℤ)

def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ)
def lhConcrete : List Turn → ℤ :=
  fun log => log.foldl (fun acc t => acc * 1000000 + ((t.actor : ℤ) * 1000 + t.src)) (log.length : ℤ)
def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

/-- The concrete `bal` component. -/
def balCompC : ActiveComponent RecChainedState CreateEscrowArgs :=
  { digest    := fun k => balDigConcrete k.bal
  , expected  := fun s args =>
      balDigConcrete (recBalCreditCell s.kernel.bal args.creator args.asset (-args.amount))
  , postClause := fun s args post =>
      balDigConcrete post.bal
        = balDigConcrete (recBalCreditCell s.kernel.bal args.creator args.asset (-args.amount))
  , binds := fun _ _ _ h => h, encodes := fun _ _ _ h => h }

/-- The concrete `escrows` component. -/
def escCompC : ActiveComponent RecChainedState CreateEscrowArgs :=
  { digest    := fun k => escDigConcrete k.escrows
  , expected  := fun s args =>
      escDigConcrete (parkedRecord args.id args.creator args.recipient args.asset args.amount
        :: s.kernel.escrows)
  , postClause := fun s args post =>
      escDigConcrete post.escrows
        = escDigConcrete (parkedRecord args.id args.creator args.recipient args.asset args.amount
          :: s.kernel.escrows)
  , binds := fun _ _ _ h => h, encodes := fun _ _ _ h => h }

def createEscrowEC : EffectSpec2Dual RecChainedState CreateEscrowArgs :=
  { view         := chainView
  , active1      := balCompC
  , active2      := escCompC
  , logUpdate    := some (fun s args => escrowReceiptA args.actor :: s.log)
  , restFrame    := fun _ _ => True
  , guardGates   := createEscrowGuardGates
  , guardProp    := createEscrowGuardProp
  , guardWidth   := 1
  , guardEncode  := createEscrowGuardEncode
  , guardLocal   := createEscrowGuardLocal
  , guardWidth_le := by decide }

/-- Concrete pre-state: actor=creator 0 (self-authority), bal[0][0]=100, accounts {0,1,2}, no escrows. -/
def kPre : RecordKernelState :=
  { accounts := {0, 1, 2}, cell := fun _ => default, caps := fun _ => []
  , bal := fun c _ => if c = 0 then 100 else 0 }
def sPre : RecChainedState := { kernel := kPre, log := [] }
def argsRef : CreateEscrowArgs :=
  { id := 1, actor := 0, creator := 0, recipient := 1, asset := 0, amount := 30 }
def sPost : RecChainedState := (execFullA sPre (.createEscrowA 1 0 0 1 0 30)).getD sPre

/-- THE FORGERY: honest debit + park, but a THIRD cell (2) is ALSO minted bal 0 → 999. The comp1-bal
gate (68 = 69) must reject it (the escrow + log + rest stay honest). -/
def sForged : RecChainedState :=
  { kernel := { kPre with
      bal := fun c _ => if c = 0 then 70 else if c = 2 then 999 else 0
      escrows := parkedRecord 1 0 1 0 30 :: kPre.escrows }
  , log := escrowReceiptA 0 :: sPre.log }

def witnessOf (s : RecChainedState) (args : CreateEscrowArgs) (s' : RecChainedState) : List Int :=
  (List.range createEscrowEC.traceWidth).map (fun w => encodeE2Dual SC createEscrowEC s args s' w)

/-- **`createEscrowWitnessVec` — the executor-driven witness generator.** -/
def createEscrowWitnessVec (s : RecChainedState) (args : CreateEscrowArgs) : List Int :=
  match execFullA s (.createEscrowA args.id args.actor args.creator args.recipient args.asset args.amount) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

def honestWitness : List Int := createEscrowWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

#guard honestWitness.length == 74
#guard decide (satisfied (effectCircuit2Dual createEscrowEC) (encodeE2Dual SC createEscrowEC sPre argsRef sPost))
#guard decide (satisfied (effectCircuit2Dual createEscrowEC) (encodeE2Dual SC createEscrowEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- comp1 bal gate broken (3rd-cell mint)
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0      -- honest bal binds
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0      -- honest escrows bind
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0      -- forgery preserves the escrow component
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0      -- rest frame
#guard honestWitness.getD 0 0 == 1                              -- guard

/-! ## §5 — JSON export. -/

def emittedCE : EmittedDescriptor := emittedEffect2Dual "dregg-createEscrowA-v2" createEscrowEC
def descriptorJson : String := emitDescriptorJson emittedCE
def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedCE.constraints.length == 5
#guard emittedCE.traceWidth == 74

-- Golden pins (the bytes the Rust `lean_executor_derived_create_escrow` test pastes).
#guard honestWitness.getD 68 0 == 70000000000000 ∧ honestWitness.getD 70 0 == 1001030
#guard forgedWitness.getD 68 0 == 70000000000999 ∧ forgedWitness.getD 70 0 == 1001030

#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.CreateEscrowWitness
