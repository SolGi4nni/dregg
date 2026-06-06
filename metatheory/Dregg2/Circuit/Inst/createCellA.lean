/-
# Dregg2.Circuit.Inst.createCellA — the v2-triple (`EffectCommit3`) VALIDATION for `createCellA`.

`createCellA` grows `accounts`, resets every per-cell indexed slot at `newCell` (born-empty via
`bornEmptyCellSlots`), prepends the creation receipt, and freezes global side-tables. Guard:
`createCellAdmit` (privileged creation authority ∧ freshness).

ADDITIVE: imports `AccountsCommit`, `BornEmptyCommit`, `EffectCommit3`, `Spec/accountgrowth`.
-/
import Dregg2.Circuit.AccountsCommit
import Dregg2.Circuit.BornEmptyCommit
import Dregg2.Circuit.EffectCommit3
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.ListCommit
import Dregg2.Circuit.Spec.accountgrowth

namespace Dregg2.Circuit.Inst.CreateCellA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.EffectCommit3
open Dregg2.Circuit.AccountsCommit
open Dregg2.Circuit.BornEmptyCommit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.AccountGrowth
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — propBit guard (wire 0, guardWidth = 1). -/

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `RestIffNoAccountsBalBorn` portal (global side-tables only). -/

/-- **`RestIffNoAccountsBalBorn RH`** — rest portal: `accounts` + `bal` + born-empty side tables
are digest-bound; only global side-tables ride the rest hash. -/
def RestIffNoAccountsBalBorn (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.factories = k.factories ∧ k'.sealedBoxes = k.sealedBoxes)

/-! ## §2 — the `createCellE` triple instance (`accounts` + `bal` + born-empty side). -/

structure CreateCellArgs where
  actor   : CellId
  newCell : CellId

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

def createCellGuardProp (s : RecChainedState) (args : CreateCellArgs) : Prop :=
  createCellAdmit s.kernel args.actor args.newCell

instance (s : RecChainedState) (args : CreateCellArgs) : Decidable (createCellGuardProp s args) := by
  unfold createCellGuardProp createCellAdmit; exact inferInstanceAs (Decidable (_ ∧ _))

def createCellGuardEncode (s : RecChainedState) (args : CreateCellArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (createCellGuardProp s args) else 0

def createCellGuardGates : ConstraintSystem := [cBitGuard]

theorem createCellGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied createCellGuardGates a ↔ satisfied createCellGuardGates b := by
  unfold satisfied createCellGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

def expectedAccounts (s : RecChainedState) (args : CreateCellArgs) : Finset CellId :=
  insert args.newCell s.kernel.accounts

def expectedBal (s : RecChainedState) (args : CreateCellArgs) : CellId → AssetId → ℤ :=
  fun c a => if c = args.newCell then 0 else s.kernel.bal c a

def accountsComp (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState CreateCellArgs :=
  accountsComponent LE cN hN hLE expectedAccounts

def balComp (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState CreateCellArgs :=
  funcComponent (β := CellId → AssetId → ℤ) (·.bal) D hD expectedBal

def bornEmptyComp (D : BornEmptySideTables → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState CreateCellArgs :=
  bornEmptySideComponent (toKernel := chainView.toKernel) (fresh := fun _ args => args.newCell) D hD

def createCellE (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide) :
    EffectSpec2Triple RecChainedState CreateCellArgs where
  view         := chainView
  active1      := accountsComp LE cN hN hLE
  active2      := balComp DBal hDBal
  active3      := bornEmptyComp DSide hDSide
  logUpdate    := some (fun s args => createReceipt args.actor args.newCell :: s.log)
  restFrame    := fun k k' =>
    (k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.factories = k.factories ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := createCellGuardGates
  guardProp    := createCellGuardProp
  guardWidth   := 1
  guardEncode  := createCellGuardEncode
  guardLocal   := createCellGuardLocal
  guardWidth_le := by decide

/-! ### §2a — per-effect obligations. -/

theorem createCellGuardDecodes (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide) :
    GuardDecodes2Triple (createCellE LE cN hN hLE DBal hDBal DSide hDSide) := by
  intro s args s' hsat
  change satisfied createCellGuardGates (createCellGuardEncode s args s') at hsat
  show createCellGuardProp s args
  have hg := hsat cBitGuard (by simp [createCellGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, createCellGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem createCellGuardEncodes (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide) :
    GuardEncodes2Triple (createCellE LE cN hN hLE DBal hDBal DSide hDSide) := by
  intro s args s' hg
  dsimp [createCellE]
  intro c hc
  simp only [createCellGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, createCellGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem createCellRestFrameDecodes (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (hRest : RestIffNoAccountsBalBorn S.RH) :
    RestFrameDecodes2Triple S (createCellE LE cN hN hLE DBal hDBal DSide hDSide) := by
  intro k k' h
  dsimp [createCellE]
  exact (hRest k k').mp h

theorem createCellRestFrameEncodes (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (hRest : RestIffNoAccountsBalBorn S.RH) :
    RestFrameEncodes2Triple S (createCellE LE cN hN hLE DBal hDBal DSide hDSide) :=
  fun k k' h => (hRest k k').mpr h

/-! ### §2b — apex ↔ FULL `CreateCellSpec` (executor semantics). -/

theorem apex_iff_createCellSpec (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState) :
    (createCellE LE cN hN hLE DBal hDBal DSide hDSide).apex s args s' ↔
      CreateCellSpec s args.actor args.newCell s' := by
  dsimp only [EffectSpec2Triple.apex, createCellE, accountsComp, balComp, bornEmptyComp,
    accountsComponent, funcComponent, bornEmptySideComponent, chainView, CreateCellSpec,
    createCellGuardProp, createCellAdmit, expectedAccounts, expectedBal, readBornEmptySide,
    expectedBornEmptySide]
  constructor
  · rintro ⟨hg, hacc, hbal, hside, hlog, hEsc, hNul, hRev, hCom, hQ, hSw, hFac, hSB⟩
    refine ⟨hg, hacc, ?_, hlog, hEsc, hNul, hRev, hCom, hQ, hSw, hFac, hSB⟩
    exact (bornEmptyAt_iff_side_and_bal s.kernel args.newCell s'.kernel).mpr ⟨hside, hbal⟩
  · rintro ⟨hg, hacc, hborn, hlog, hEsc, hNul, hRev, hCom, hQ, hSw, hFac, hSB⟩
    obtain ⟨hside, hbal⟩ := (bornEmptyAt_iff_side_and_bal s.kernel args.newCell s'.kernel).mp hborn
    exact ⟨hg, hacc, hbal, hside, hlog, hEsc, hNul, hRev, hCom, hQ, hSw, hFac, hSB⟩

/-! ### §2c — THE VALIDATION: `createCellA_full_sound ⇒ CreateCellSpec`. -/

/-- **`createCellA_full_sound` — the VALIDATION (triple-circuit layer).** A satisfying witness proves
the FULL `CreateCellSpec` (accounts + bal + born-empty side tables + globals). -/
theorem createCellA_full_sound
    (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (hRest : RestIffNoAccountsBalBorn S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState)
    (h : satisfiedE2Triple S (createCellE LE cN hN hLE DBal hDBal DSide hDSide)
        (encodeE2Triple S (createCellE LE cN hN hLE DBal hDBal DSide hDSide) s args s')) :
    CreateCellSpec s args.actor args.newCell s' := by
  have hapex :=
    effect2triple_circuit_full_sound S (createCellE LE cN hN hLE DBal hDBal DSide hDSide)
      (createCellRestFrameDecodes S LE cN hN hLE DBal hDBal DSide hDSide hRest) hLog
      (createCellGuardDecodes LE cN hN hLE DBal hDBal DSide hDSide) s args s' h
  exact (apex_iff_createCellSpec LE cN hN hLE DBal hDBal DSide hDSide s args s').mp hapex



/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def createCellEWire : EffectSpec2Triple RecChainedState CreateCellArgs where
  view         := chainView
  active1      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  active2      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  active3      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := createCellGuardGates
  guardProp    := createCellGuardProp
  guardWidth   := 1
  guardEncode  := createCellGuardEncode
  guardLocal   := createCellGuardLocal
  guardWidth_le := by decide

def createCellAAirName : String := "dregg-createCellA-v2"

def createCellAEmitted : EmittedDescriptor := emittedEffect2Triple createCellAAirName createCellEWire

#guard createCellAEmitted.name == createCellAAirName

#assert_axioms createCellGuardLocal
#assert_axioms createCellGuardDecodes
#assert_axioms createCellGuardEncodes
#assert_axioms apex_iff_createCellSpec
#assert_axioms createCellA_full_sound

end Dregg2.Circuit.Inst.CreateCellA