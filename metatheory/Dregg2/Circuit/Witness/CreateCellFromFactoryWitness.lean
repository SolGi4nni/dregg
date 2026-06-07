/-
# Dregg2.Circuit.Witness.CreateCellFromFactoryWitness — the v2-QUINT WITNESS GENERATOR for
`createCellFromFactoryA`.

The `execute → prove → verify → anti-ghost` beachhead for `createCellFromFactoryA` (grow `accounts`,
reset `bal` at `newCell`, mint `cell` with the factory's initial fields + program-VK, install
`slotCaveats`, reset born-empty authority slots, prepend the creation receipt), over the v2-QUINT
framework (`EffectCommit5`). Width 80, seven gates: comp1 = `accounts`, comp2 = `bal`, comp3 = `cell`,
comp4 = `slotCaveats`, comp5 = born-empty authority tables. Mirrors `DelegateWitness` with FIVE touched
components.

Reused (not re-proved): `execFullA … (.createCellFromFactoryA …)`,
`Inst.CreateCellFromFactoryA.createCellFromFactoryA_full_sound`, `effect2quint_circuit_full_complete`.
The reference pre-state is the executor's own `facS` fixture (vk 42 → `subFactory`).
No `sorry`/`axiom`/`native_decide`; CR portals carried.
-/
import Dregg2.Circuit.Inst.createCellFromFactoryA

namespace Dregg2.Circuit.Witness.CreateCellFromFactoryWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit5
open Dregg2.Circuit.AccountsCommit
open Dregg2.Circuit.BornEmptyCommit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Inst.CreateCellFromFactoryA
open Dregg2.Circuit.Spec.FactoryCreation
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull
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
  (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
  (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
  (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)

/-- **`execute_produces_satisfying_witness`** — a `CreateFromFactoryCircuitSpec`-satisfying step makes
the quint witness SATISFY the quint circuit. -/
theorem execute_produces_satisfying_witness
    (hRest : RestIffNoFactoryTouched S.RH)
    (s : RecChainedState) (args : CreateFromFactoryArgs) (s' : RecChainedState)
    (hspec : CreateFromFactoryCircuitSpec s args.actor args.newCell args.vk s') :
    satisfiedE2Quint S (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
      (encodeE2Quint S (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
        s args s') :=
  effect2quint_circuit_full_complete S
    (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
    (fun k k' h => (hRest k k').mpr h)
    (createFromFactoryGuardEncodes LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
    s args s'
    ((apex_iff_createFromFactoryCircuitSpec LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth
        s args s').mpr hspec)

/-- **`satisfying_witness_proves_full_state`** — a satisfying quint witness proves the full
`CreateFromFactoryCircuitSpec` (factory install + born-empty authority + 8 global frame fields).
Reuses `createCellFromFactoryA_full_sound`. -/
theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoFactoryTouched S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateFromFactoryArgs) (s' : RecChainedState)
    (h : satisfiedE2Quint S (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
        (encodeE2Quint S (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
          s args s')) :
    CreateFromFactoryCircuitSpec s args.actor args.newCell args.vk s' :=
  createCellFromFactoryA_full_sound S LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth
    hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

/-- A fixed carrier for the per-cell folds: {0, 5} (the existing cell + the fresh factory cell). -/
def carrier : List CellId := [0, 5]

def accDigConcrete : Finset CellId → ℤ :=
  fun s => (s.sort (· ≤ ·)).foldl (fun acc c => acc * 1000 + (c : ℤ)) (s.card : ℤ)
def balDigConcrete : (CellId → AssetId → ℤ) → ℤ :=
  fun bal => carrier.foldl (fun acc c => acc * 1000000 + bal c 0) 0
def cellDigConcrete : (CellId → Value) → ℤ :=
  fun cell => carrier.foldl (fun acc c => acc * 1000000 + balOf (cell c)) 0
def scDigConcrete : (CellId → List SlotCaveat) → ℤ :=
  fun sc => carrier.foldl (fun acc c => acc * 1000 + ((sc c).length : ℤ)) 0
def authDigConcrete : BornEmptyAuthorityTables → ℤ :=
  fun tbl => carrier.foldl
    (fun acc c => acc * 1000000 + ((tbl.lifecycle c : ℤ) + 1000 * (tbl.deathCert c : ℤ))) 0

def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.nullifiers.length : ℤ) + (k.commitments.length : ℤ)
def lhConcrete : List Turn → ℤ :=
  fun log => log.foldl (fun acc t => acc * 1000000 + ((t.actor : ℤ) * 1000 + t.src)) (log.length : ℤ)
def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

def accCompC : ActiveComponent RecChainedState CreateFromFactoryArgs :=
  { digest := fun k => accDigConcrete k.accounts
  , expected := fun s args => accDigConcrete (expectedAccounts s args)
  , postClause := fun s args post => accDigConcrete post.accounts = accDigConcrete (expectedAccounts s args)
  , binds := fun _ _ _ h => h, encodes := fun _ _ _ h => h }
def balCompC : ActiveComponent RecChainedState CreateFromFactoryArgs :=
  { digest := fun k => balDigConcrete k.bal
  , expected := fun s args => balDigConcrete (expectedBal s args)
  , postClause := fun s args post => balDigConcrete post.bal = balDigConcrete (expectedBal s args)
  , binds := fun _ _ _ h => h, encodes := fun _ _ _ h => h }
def cellCompC : ActiveComponent RecChainedState CreateFromFactoryArgs :=
  { digest := fun k => cellDigConcrete k.cell
  , expected := fun s args => cellDigConcrete (expectedCell s args)
  , postClause := fun s args post => cellDigConcrete post.cell = cellDigConcrete (expectedCell s args)
  , binds := fun _ _ _ h => h, encodes := fun _ _ _ h => h }
def scCompC : ActiveComponent RecChainedState CreateFromFactoryArgs :=
  { digest := fun k => scDigConcrete k.slotCaveats
  , expected := fun s args => scDigConcrete (expectedSlotCaveats s args)
  , postClause := fun s args post =>
      scDigConcrete post.slotCaveats = scDigConcrete (expectedSlotCaveats s args)
  , binds := fun _ _ _ h => h, encodes := fun _ _ _ h => h }
def authCompC : ActiveComponent RecChainedState CreateFromFactoryArgs :=
  { digest := fun k => authDigConcrete (readBornEmptyAuthority k)
  , expected := fun s args => authDigConcrete (expectedBornEmptyAuthority s.kernel args.newCell)
  , postClause := fun s args post =>
      authDigConcrete (readBornEmptyAuthority post)
        = authDigConcrete (expectedBornEmptyAuthority s.kernel args.newCell)
  , binds := fun _ _ _ h => h, encodes := fun _ _ _ h => h }

def createFromFactoryEC : EffectSpec2Quint RecChainedState CreateFromFactoryArgs :=
  { view := chainView
  , active1 := accCompC, active2 := balCompC, active3 := cellCompC, active4 := scCompC
  , active5 := authCompC
  , logUpdate := some (fun s args => factoryReceipt args.actor args.newCell :: s.log)
  , restFrame := fun _ _ => True
  , guardGates := createFromFactoryGuardGates
  , guardProp := createFromFactoryGuardProp
  , guardWidth := 1
  , guardEncode := createFromFactoryGuardEncode
  , guardLocal := createFromFactoryGuardLocal
  , guardWidth_le := by decide }

/-- The reference pre-state is the executor's own `facS` fixture (vk 42 → `subFactory`; actor 0 holds
the privileged minter cap `node 5` over the fresh cell 5; accounts {0}). -/
def sPre : RecChainedState := facS
def argsRef : CreateFromFactoryArgs := { actor := 0, newCell := 5, vk := 42 }
def sPost : RecChainedState := (execFullA sPre (.createCellFromFactoryA 0 5 42)).getD sPre

/-- THE FORGERY: the honest factory creation, but the EXISTING cell 0's bal is ALSO minted 0 → 999 (a
bystander whose bal must stay frozen). The comp2-bal gate (70 = 71) must reject it. -/
def sForged : RecChainedState :=
  { sPost with kernel := { sPost.kernel with
      bal := fun c a => if c = 0 then 999 else sPost.kernel.bal c a } }

def witnessOf (s : RecChainedState) (args : CreateFromFactoryArgs) (s' : RecChainedState) : List Int :=
  (List.range createFromFactoryEC.traceWidth).map (fun w => encodeE2Quint SC createFromFactoryEC s args s' w)

/-- **`createCellFromFactoryWitnessVec` — the executor-driven witness generator.** -/
def createCellFromFactoryWitnessVec (s : RecChainedState) (args : CreateFromFactoryArgs) : List Int :=
  match execFullA s (.createCellFromFactoryA args.actor args.newCell args.vk) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

def honestWitness : List Int := createCellFromFactoryWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

#guard honestWitness.length == 80
#guard decide (satisfied (effectCircuit2Quint createFromFactoryEC) (encodeE2Quint SC createFromFactoryEC sPre argsRef sPost))
#guard decide (satisfied (effectCircuit2Quint createFromFactoryEC) (encodeE2Quint SC createFromFactoryEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 70 0 == forgedWitness.getD 71 0)   -- comp2-bal gate broken (bystander mint)
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0      -- accounts comp1 binds
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0      -- bal comp2 binds
#guard honestWitness.getD 72 0 == honestWitness.getD 73 0      -- cell comp3 binds
#guard honestWitness.getD 74 0 == honestWitness.getD 75 0      -- slotCaveats comp4 binds
#guard honestWitness.getD 76 0 == honestWitness.getD 77 0      -- born-empty authority comp5 binds
#guard forgedWitness.getD 72 0 == forgedWitness.getD 73 0      -- forgery preserves cell comp3
#guard honestWitness.getD 0 0 == 1                              -- guard

/-! ## §5 — JSON export. -/

def emittedCFF : EmittedDescriptor := emittedEffect2Quint "dregg-createCellFromFactoryA-v2" createFromFactoryEC
def descriptorJson : String := emitDescriptorJson emittedCFF
def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedCFF.constraints.length == 8   -- guard bit + rest + 5 component binds + log
#guard emittedCFF.traceWidth == 80

-- Golden pins (the bytes the Rust `lean_executor_derived_create_cell_from_factory` test pastes).
#guard honestWitness.getD 70 0 == 0 ∧ honestWitness.getD 71 0 == 0
#guard forgedWitness.getD 70 0 == 999000000 ∧ forgedWitness.getD 71 0 == 0

#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.CreateCellFromFactoryWitness
