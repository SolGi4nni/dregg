/-
# Dregg2.Circuit.Witness.CreateCellWitness — the v2-TRIPLE WITNESS GENERATOR for `createCellA`.

The `execute → prove → verify → anti-ghost` beachhead for `createCellA` (grow `accounts`, reset every
per-cell indexed slot at `newCell` to born-empty, prepend the creation receipt), over the v2-triple
framework (`EffectCommit3`). Width 76, six gates (guard + rest + 3 component gates + log): comp1 =
`accounts`, comp2 = `bal`, comp3 = the born-empty side tables. Mirrors `DelegateWitness` but with THREE
touched components.

Reused (not re-proved): `execFullA … (.createCellA …)`,
`Inst.CreateCellA.createCellA_full_sound`, `effect2triple_circuit_full_complete`.
CR portals carried.
-/
import Dregg2.Circuit.Inst.createCellA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.CreateCellWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit3
open Dregg2.Circuit.AccountsCommit
open Dregg2.Circuit.BornEmptyCommit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Inst.CreateCellA
open Dregg2.Circuit.Spec.AccountGrowth
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Poseidon2Surface (refP2 turnLogDigest)
open Dregg2.Authority (Cap)

set_option linter.dupNamespace false

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))
instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §3 — ABSTRACT execute→prove / prove→state (CR portals carried). -/

variable (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
  (hN : compressNInjective cN) (hLE : listLeafInjective LE)
  (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
  (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)

theorem execute_produces_satisfying_witness
    (hRest : RestIffNoAccountsBalBorn S.RH)
    (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState)
    (hspec : CreateCellSpec s args.actor args.newCell s') :
    satisfiedE2Triple S (createCellE LE cN hN hLE DBal hDBal DSide hDSide)
      (encodeE2Triple S (createCellE LE cN hN hLE DBal hDBal DSide hDSide) s args s') :=
  effect2triple_circuit_full_complete S (createCellE LE cN hN hLE DBal hDBal DSide hDSide)
    (createCellRestFrameEncodes S LE cN hN hLE DBal hDBal DSide hDSide hRest)
    (createCellGuardEncodes LE cN hN hLE DBal hDBal DSide hDSide) s args s'
    ((apex_iff_createCellSpec LE cN hN hLE DBal hDBal DSide hDSide s args s').mpr hspec)

theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoAccountsBalBorn S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState)
    (h : satisfiedE2Triple S (createCellE LE cN hN hLE DBal hDBal DSide hDSide)
        (encodeE2Triple S (createCellE LE cN hN hLE DBal hDBal DSide hDSide) s args s')) :
    CreateCellSpec s args.actor args.newCell s' :=
  createCellA_full_sound S LE cN hN hLE DBal hDBal DSide hDSide hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

/-- Concrete accounts digest: the REAL `refP2` sponge over the sorted Finset elements length-prefixed (the
OLD `% 1000` Horner truncated cell ids ≥ 1000). -/
def accDigConcrete : Finset CellId → ℤ :=
  fun s => refP2 ((s.card : ℤ) :: (s.sort (· ≤ ·)).map (fun c => (c : ℤ)))

/-- Concrete bal digest over carrier {0,1,2,3} × asset 0: the REAL `refP2` sponge (NO `% 10⁵` truncation). -/
def balDigConcrete : (CellId → AssetId → ℤ) → ℤ :=
  fun bal => refP2 [bal 0 0, bal 1 0, bal 2 0, bal 3 0]

/-- Concrete born-empty side digest: the REAL `refP2` sponge over each cell's `[lifecycle, deathCert]`
(binds BOTH fields separately — the OLD `lifecycle + 1000·deathCert` packing aliased when `lifecycle ≥
1000`). -/
def sideDigConcrete : BornEmptySideTables → ℤ :=
  fun st => refP2 ([0, 1, 2, 3].flatMap (fun c => [(st.lifecycle c : ℤ), (st.deathCert c : ℤ)]))

def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.nullifiers.length : ℤ) + (k.commitments.length : ℤ)
/-- The log hash: the REAL `turnLogDigest` (binds `dst`/`amt` the OLD `actor*1000 + src` fold dropped). -/
def lhConcrete : List Turn → ℤ := turnLogDigest
def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

def accCompC : ActiveComponent RecChainedState CreateCellArgs :=
  { digest    := fun k => accDigConcrete k.accounts
  , expected  := fun s args => accDigConcrete (insert args.newCell s.kernel.accounts)
  , postClause := fun s args post =>
      accDigConcrete post.accounts = accDigConcrete (insert args.newCell s.kernel.accounts)
  , binds := fun _ _ _ h => h, encodes := fun _ _ _ h => h }

def balCompC : ActiveComponent RecChainedState CreateCellArgs :=
  { digest    := fun k => balDigConcrete k.bal
  , expected  := fun s args => balDigConcrete (fun c a => if c = args.newCell then 0 else s.kernel.bal c a)
  , postClause := fun s args post =>
      balDigConcrete post.bal = balDigConcrete (fun c a => if c = args.newCell then 0 else s.kernel.bal c a)
  , binds := fun _ _ _ h => h, encodes := fun _ _ _ h => h }

def sideCompC : ActiveComponent RecChainedState CreateCellArgs :=
  { digest    := fun k => sideDigConcrete (readBornEmptySide k)
  , expected  := fun s args => sideDigConcrete (expectedBornEmptySide s.kernel args.newCell)
  , postClause := fun s args post =>
      sideDigConcrete (readBornEmptySide post)
        = sideDigConcrete (expectedBornEmptySide s.kernel args.newCell)
  , binds := fun _ _ _ h => h, encodes := fun _ _ _ h => h }

def createCellEC : EffectSpec2Triple RecChainedState CreateCellArgs :=
  { view         := chainView
  , active1      := accCompC
  , active2      := balCompC
  , active3      := sideCompC
  , logUpdate    := some (fun s args => createReceipt args.actor args.newCell :: s.log)
  , restFrame    := fun _ _ => True
  , guardGates   := createCellGuardGates
  , guardProp    := createCellGuardProp
  , guardWidth   := 1
  , guardEncode  := createCellGuardEncode
  , guardLocal   := createCellGuardLocal
  , guardWidth_le := by decide }

/-- Concrete pre-state: actor 0 holds `node 3` (mint-authority over the fresh cell 3); bal[0][0]=50;
accounts {0,1,2}; newCell 3 ∉ accounts. -/
def kPre : RecordKernelState :=
  { accounts := {0, 1, 2}, cell := fun _ => default
  , caps := fun c => if c = 0 then [Cap.node 3] else []
  , bal := fun c _ => if c = 0 then 50 else 0 }
def sPre : RecChainedState := { kernel := kPre, log := [] }
def argsRef : CreateCellArgs := { actor := 0, newCell := 3 }
def sPost : RecChainedState := (execFullA sPre (.createCellA 0 3)).getD sPre

/-- THE FORGERY: cell 3 honestly born-empty, accounts grown, but a THIRD cell (2)'s bal is ALSO minted
0 → 999. The comp2-bal gate (70 = 71) must reject it (accounts comp1 + born-empty comp3 stay honest). -/
def sForged : RecChainedState :=
  { kernel := { (bornEmptyCellSlots kPre 3) with
      accounts := insert 3 kPre.accounts
      bal := fun c a => if c = 3 then 0 else if c = 2 then 999 else kPre.bal c a }
  , log := createReceipt 0 3 :: sPre.log }

def witnessOf (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState) : List Int :=
  (List.range createCellEC.traceWidth).map (fun w => encodeE2Triple SC createCellEC s args s' w)

/-- **`createCellWitnessVec` — the executor-driven witness generator.** -/
def createCellWitnessVec (s : RecChainedState) (args : CreateCellArgs) : List Int :=
  match execFullA s (.createCellA args.actor args.newCell) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

def honestWitness : List Int := createCellWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

#guard honestWitness.length == 76
#guard decide (satisfied (effectCircuit2Triple createCellEC) (encodeE2Triple SC createCellEC sPre argsRef sPost))
#guard decide (satisfied (effectCircuit2Triple createCellEC) (encodeE2Triple SC createCellEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 70 0 == forgedWitness.getD 71 0)   -- comp2-bal gate broken (3rd-cell mint)
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0      -- accounts comp1 binds
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0      -- bal comp2 binds
#guard honestWitness.getD 72 0 == honestWitness.getD 73 0      -- born-empty comp3 binds
#guard forgedWitness.getD 68 0 == forgedWitness.getD 69 0      -- forgery preserves accounts comp1
#guard honestWitness.getD 0 0 == 1                              -- guard

-- HIGH-field anti-ghost tooth: bystander cell 2's bal forged ABOVE 10⁵ (the OLD `% 10⁵` Horner collided
-- here; `refP2` does NOT). The comp2-bal bind gate `70 ≠ 71` still REJECTS.
def sForgedHigh : RecChainedState :=
  { kernel := { (bornEmptyCellSlots kPre 3) with
      accounts := insert 3 kPre.accounts
      bal := fun c a => if c = 3 then 0 else if c = 2 then 100000 else kPre.bal c a }
  , log := createReceipt 0 3 :: sPre.log }
#guard decide (satisfied (effectCircuit2Triple createCellEC) (encodeE2Triple SC createCellEC sPre argsRef sForgedHigh)) == false

/-! ## §5 — JSON export. -/

def emittedCC : EmittedDescriptor := emittedEffect2Triple "dregg-createCellA-v2" createCellEC
def descriptorJson : String := emitDescriptorJson emittedCC
def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedCC.constraints.length == 6
#guard emittedCC.traceWidth == 76

-- Structural component-bind goldens (the field-binding `refP2` digests are arbitrary-precision; non-vacuity
-- is at the bind gates; the Rust paste is regenerated from the JSON accessors).
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0      -- bal comp2 binds (honest)
#guard !(forgedWitness.getD 70 0 == forgedWitness.getD 71 0)   -- forged bal comp2 differs (REJECTED)
#guard !(honestWitnessJson == forgedWitnessJson)               -- honest ≠ forged byte streams

#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.CreateCellWitness
