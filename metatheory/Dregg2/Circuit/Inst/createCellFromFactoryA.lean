/-
# Dregg2.Circuit.Inst.createCellFromFactoryA — the v2-quint (`EffectCommit5`) VALIDATION for
`createCellFromFactoryA`.

`createCellFromFactoryA` grows `accounts`, resets `bal` at `newCell`, mints `cell` with the factory's
initial fields + program-VK, installs `slotCaveats` from the factory entry, resets born-empty authority
slots at `newCell`, prepends the creation receipt, and freezes global side-tables. Guard: ∃ conforming
`FactoryEntry` in the registry.

ADDITIVE: imports `AccountsCommit`, `BornEmptyCommit`, `EffectCommit5`, `Spec/factorycreation`; edits none.
-/
import Dregg2.Circuit.AccountsCommit
import Dregg2.Circuit.BornEmptyCommit
import Dregg2.Circuit.EffectCommit5
import Dregg2.Circuit.ListCommit
import Dregg2.Circuit.Spec.factorycreation

namespace Dregg2.Circuit.Inst.CreateCellFromFactoryA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.EffectCommit5
open Dregg2.Circuit.AccountsCommit
open Dregg2.Circuit.BornEmptyCommit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.FactoryCreation
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — propBit guard (wire 0, guardWidth = 1). -/

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `RestIffNoFactoryTouched` portal. -/

/-- **`RestIffNoFactoryTouched RH`** — rest portal for the quint circuit: global side-tables only. -/
def RestIffNoFactoryTouched (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.factories = k.factories ∧ k'.sealedBoxes = k.sealedBoxes)

/-! ## §2 — the `createFromFactoryE` quint instance. -/

structure CreateFromFactoryArgs where
  actor    : CellId
  newCell  : CellId
  vk       : Int

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- Guard: ∃ conforming registered `FactoryEntry` (existential, as in `CreateFromFactorySpec`). -/
def createFromFactoryGuardProp (s : RecChainedState) (args : CreateFromFactoryArgs) : Prop :=
  ∃ e : FactoryEntry, factoryAdmit s.kernel args.actor args.newCell args.vk e

instance (k : RecordKernelState) (actor newCell : CellId) (vk : Int) (e : FactoryEntry) :
    Decidable (factoryAdmit k actor newCell vk e) := by
  unfold factoryAdmit; exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

theorem guardProp_iff_admit (s : RecChainedState) (args : CreateFromFactoryArgs) {e : FactoryEntry}
    (h : findFactory s.kernel.factories args.vk.toNat = some e) :
    createFromFactoryGuardProp s args ↔ factoryAdmit s.kernel args.actor args.newCell args.vk e := by
  constructor
  · rintro ⟨e', hadmit⟩
    have hfind : findFactory s.kernel.factories args.vk.toNat = some e' := hadmit.2.1
    have heq : e' = e := Option.some.inj (Eq.trans hfind.symm h)
    simpa [heq] using hadmit
  · intro hadmit
    exact ⟨e, hadmit⟩

theorem guardProp_false (s : RecChainedState) (args : CreateFromFactoryArgs)
    (h : findFactory s.kernel.factories args.vk.toNat = none) :
    ¬ createFromFactoryGuardProp s args := by
  rintro ⟨e, hadmit⟩
  simp [factoryAdmit, h] at hadmit

instance (s : RecChainedState) (args : CreateFromFactoryArgs) :
    Decidable (createFromFactoryGuardProp s args) := by
  match h : findFactory s.kernel.factories args.vk.toNat with
  | some e =>
    by_cases hga : factoryAdmit s.kernel args.actor args.newCell args.vk e
    · exact isTrue ((guardProp_iff_admit s args h).mpr hga)
    · exact isFalse fun hex => hga ((guardProp_iff_admit s args h).mp hex)
  | none =>
    exact isFalse (guardProp_false s args h)

def createFromFactoryGuardEncode (s : RecChainedState) (args : CreateFromFactoryArgs)
    (_s' : RecChainedState) : Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (createFromFactoryGuardProp s args) else 0

def createFromFactoryGuardGates : ConstraintSystem := [cBitGuard]

theorem createFromFactoryGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied createFromFactoryGuardGates a ↔ satisfied createFromFactoryGuardGates b := by
  unfold satisfied createFromFactoryGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

def expectedAccounts (s : RecChainedState) (args : CreateFromFactoryArgs) : Finset CellId :=
  insert args.newCell s.kernel.accounts

def expectedBal (s : RecChainedState) (args : CreateFromFactoryArgs) : CellId → AssetId → ℤ :=
  fun c a => if c = args.newCell then 0 else s.kernel.bal c a

def expectedCell (s : RecChainedState) (args : CreateFromFactoryArgs) : CellId → Value :=
  match findFactory s.kernel.factories args.vk.toNat with
  | some e => factoryPostCell (factoryBornCell s.kernel args.newCell) args.newCell e
  | none   => s.kernel.cell

def expectedSlotCaveats (s : RecChainedState) (args : CreateFromFactoryArgs) :
    CellId → List SlotCaveat :=
  match findFactory s.kernel.factories args.vk.toNat with
  | some e => factoryPostCaveats (factoryBornCaveats s.kernel args.newCell) args.newCell e
  | none   => s.kernel.slotCaveats

def accountsComp (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState CreateFromFactoryArgs :=
  accountsComponent LE cN hN hLE expectedAccounts

def balComp (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState CreateFromFactoryArgs :=
  funcComponent (β := CellId → AssetId → ℤ) (·.bal) D hD expectedBal

def cellComp (D : (CellId → Value) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState CreateFromFactoryArgs :=
  funcComponent (β := CellId → Value) (·.cell) D hD expectedCell

def slotCaveatsComp (D : (CellId → List SlotCaveat) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState CreateFromFactoryArgs :=
  funcComponent (β := CellId → List SlotCaveat) (·.slotCaveats) D hD expectedSlotCaveats

def bornEmptyAuthorityComp (D : BornEmptyAuthorityTables → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState CreateFromFactoryArgs :=
  bornEmptyAuthorityComponent (toKernel := chainView.toKernel) (fresh := fun _ args => args.newCell) D hD

def createFromFactoryE (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth) :
    EffectSpec2Quint RecChainedState CreateFromFactoryArgs where
  view         := chainView
  active1      := accountsComp LE cN hN hLE
  active2      := balComp DBal hDBal
  active3      := cellComp DCell hDCell
  active4      := slotCaveatsComp DSC hDSC
  active5      := bornEmptyAuthorityComp DAuth hDAuth
  logUpdate    := some (fun s args => factoryReceipt args.actor args.newCell :: s.log)
  restFrame    := fun k k' =>
    (k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.factories = k.factories ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := createFromFactoryGuardGates
  guardProp    := createFromFactoryGuardProp
  guardWidth   := 1
  guardEncode  := createFromFactoryGuardEncode
  guardLocal   := createFromFactoryGuardLocal
  guardWidth_le := by decide

instance createFromFactoryE_guardDecidable (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (s : RecChainedState) (args : CreateFromFactoryArgs) :
    Decidable ((createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth).guardProp
      s args) := by
  dsimp [createFromFactoryE]; infer_instance

/-! ### §2a — per-effect obligations. -/

theorem createFromFactoryGuardDecodes (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth) :
    GuardDecodes2Quint (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth) := by
  intro s args s' hsat
  change satisfied createFromFactoryGuardGates (createFromFactoryGuardEncode s args s') at hsat
  show createFromFactoryGuardProp s args
  have hg := hsat cBitGuard (by simp [createFromFactoryGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, createFromFactoryGuardEncode,
    if_pos] at hg
  exact propBit_eq_one.mp hg

theorem createFromFactoryGuardEncodes (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth) :
    GuardEncodes2Quint (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth) := by
  intro s args s' hg
  dsimp [createFromFactoryE]
  intro c hc
  simp only [createFromFactoryGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, createFromFactoryGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem createFromFactoryRestFrameDecodes (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (hRest : RestIffNoFactoryTouched S.RH) :
    RestFrameDecodes2Quint S
      (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth) := by
  intro k k' h
  dsimp [createFromFactoryE]
  exact (hRest k k').mp h

/-! ### §2b — apex ↔ the QUINT-CIRCUIT spec. -/

/-- What the v2-quint circuit pins: factory install + born-empty authority slots at `newCell`. -/
def CreateFromFactoryCircuitSpec (st : RecChainedState) (actor newCell : CellId) (vk : Int)
    (st' : RecChainedState) : Prop :=
  ∃ e : FactoryEntry,
    factoryAdmit st.kernel actor newCell vk e
    ∧ st'.kernel.accounts = insert newCell st.kernel.accounts
    ∧ st'.kernel.bal = (fun c a => if c = newCell then 0 else st.kernel.bal c a)
    ∧ st'.kernel.cell = factoryPostCell (factoryBornCell st.kernel newCell) newCell e
    ∧ st'.kernel.slotCaveats = factoryPostCaveats (factoryBornCaveats st.kernel newCell) newCell e
    ∧ readBornEmptyAuthority st'.kernel = expectedBornEmptyAuthority st.kernel newCell
    ∧ st'.log = factoryReceipt actor newCell :: st.log
    ∧ st'.kernel.escrows = st.kernel.escrows
    ∧ st'.kernel.nullifiers = st.kernel.nullifiers
    ∧ st'.kernel.revoked = st.kernel.revoked
    ∧ st'.kernel.commitments = st.kernel.commitments
    ∧ st'.kernel.queues = st.kernel.queues
    ∧ st'.kernel.swiss = st.kernel.swiss
    ∧ st'.kernel.factories = st.kernel.factories
    ∧ st'.kernel.sealedBoxes = st.kernel.sealedBoxes

theorem CreateFromFactorySpec_implies_circuitSpec (st : RecChainedState) (actor newCell : CellId)
    (vk : Int) (st' : RecChainedState) (h : CreateFromFactorySpec st actor newCell vk st') :
    CreateFromFactoryCircuitSpec st actor newCell vk st' := by
  obtain ⟨e, hadmit, hacc, hbal, hcell, hsc, hlog, hcaps, hlif, hdc, hdel, hdgs, hEsc, hNull, hRev,
      hCom, hQ, hSw, hFac, hSB⟩ := h
  refine ⟨e, hadmit, hacc, hbal, hcell, hsc, ?_, hlog, hEsc, hNull, hRev, hCom, hQ, hSw, hFac, hSB⟩
  exact (bornEmptyAuthority_post_iff st.kernel newCell st'.kernel).mpr
    ⟨hcaps, hlif, hdc, hdel, hdgs⟩

theorem apex_iff_createFromFactoryCircuitSpec (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (s : RecChainedState) (args : CreateFromFactoryArgs) (s' : RecChainedState) :
    (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth).apex s args s' ↔
      CreateFromFactoryCircuitSpec s args.actor args.newCell args.vk s' := by
  dsimp only [EffectSpec2Quint.apex, createFromFactoryE, accountsComp, balComp, cellComp,
    slotCaveatsComp, bornEmptyAuthorityComp, accountsComponent, funcComponent,
    bornEmptyAuthorityComponent, chainView, CreateFromFactoryCircuitSpec, createFromFactoryGuardProp,
    factoryAdmit, expectedAccounts, expectedBal, expectedCell, expectedSlotCaveats,
    readBornEmptyAuthority, expectedBornEmptyAuthority]
  constructor
  · rintro ⟨hex, hacc, hbal, hcell, hsc, hauth, hlog, hEsc, hNul, hRev, hCom, hQ, hSw, hFac, hSB⟩
    obtain ⟨e, hadmit⟩ := hex
    refine ⟨e, hadmit, hacc, hbal, ?_, ?_, hauth, hlog, hEsc, hNul, hRev, hCom, hQ, hSw, hFac, hSB⟩
    · simpa [expectedCell, hadmit.2.1] using hcell
    · simpa [expectedSlotCaveats, hadmit.2.1] using hsc
  · rintro ⟨e, hadmit, hacc, hbal, hcell, hsc, hauth, hlog, hEsc, hNul, hRev, hCom, hQ, hSw, hFac,
      hSB⟩
    refine ⟨⟨e, hadmit⟩, hacc, hbal, ?_, ?_, hauth, hlog, hEsc, hNul, hRev, hCom, hQ, hSw, hFac, hSB⟩
    · simpa [expectedCell, hadmit.2.1] using hcell
    · simpa [expectedSlotCaveats, hadmit.2.1] using hsc

/-! ### §2c — THE VALIDATION. -/

theorem createCellFromFactoryA_full_sound
    (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (hRest : RestIffNoFactoryTouched S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateFromFactoryArgs) (s' : RecChainedState)
    (h : satisfiedE2Quint S
        (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
        (encodeE2Quint S
          (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
          s args s')) :
    CreateFromFactoryCircuitSpec s args.actor args.newCell args.vk s' := by
  have hapex :=
    effect2quint_circuit_full_sound S
      (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
      (createFromFactoryRestFrameDecodes S LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth
        hRest) hLog
      (createFromFactoryGuardDecodes LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth) s args
      s' h
  exact (apex_iff_createFromFactoryCircuitSpec LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth
      hDAuth s args s').mp hapex

#assert_axioms createFromFactoryGuardLocal
#assert_axioms createFromFactoryGuardDecodes
#assert_axioms createFromFactoryGuardEncodes
#assert_axioms apex_iff_createFromFactoryCircuitSpec
#assert_axioms createCellFromFactoryA_full_sound

end Dregg2.Circuit.Inst.CreateCellFromFactoryA