/-
# Dregg2.Circuit.Inst.spawnA — the v2-quint (`EffectCommit5`) VALIDATION for `spawnA`.

`spawnA` grows `accounts`, resets `bal` at `child`, copies the held parent cap into `caps` at `child`,
initializes `delegate` and `delegations` at `child`, prepends the creation receipt, and freezes the
other 12 kernel fields.

ADDITIVE: imports `AccountsCommit`, `BornEmptyCommit`, `EffectCommit5`, `Spec/accountgrowth`; edits none.
-/
import Dregg2.Circuit.AccountsCommit
import Dregg2.Circuit.BornEmptyCommit
import Dregg2.Circuit.EffectCommit5
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.ListCommit
import Dregg2.Circuit.Spec.accountgrowth

namespace Dregg2.Circuit.Inst.SpawnA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.EffectCommit5
open Dregg2.Circuit.AccountsCommit
open Dregg2.Circuit.BornEmptyCommit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.AccountGrowth
open Dregg2.Authority
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — propBit guard (wire 0, guardWidth = 1). -/

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `RestIffNoSpawnTouched` portal. -/

/-- **`RestIffNoSpawnTouched RH`** — rest portal for the quint circuit: global side-tables only
(per-cell born-empty slots are executor-pinned in full `SpawnSpec`). -/
def RestIffNoSpawnTouched (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments
      ∧ k'.factories = k.factories
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.heaps = k.heaps
      ∧ k'.nullifierRoot = k.nullifierRoot ∧ k'.revokedRoot = k.revokedRoot)

/-! ## §2 — the `spawnE` quint instance. -/

structure SpawnArgs where
  actor  : CellId
  child  : CellId
  target : CellId

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

def spawnGuardProp (s : RecChainedState) (args : SpawnArgs) : Prop :=
  spawnAdmit s.kernel args.actor args.child args.target

instance (k : RecordKernelState) (actor child target : CellId) :
    Decidable (spawnAdmit k actor child target) := by
  unfold spawnAdmit createCellAdmit; exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (s : RecChainedState) (args : SpawnArgs) : Decidable (spawnGuardProp s args) := by
  unfold spawnGuardProp; infer_instance

def spawnGuardEncode (s : RecChainedState) (args : SpawnArgs) (_s' : RecChainedState) : Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (spawnGuardProp s args) else 0

def spawnGuardGates : ConstraintSystem := [cBitGuard]

theorem spawnGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied spawnGuardGates a ↔ satisfied spawnGuardGates b := by
  unfold satisfied spawnGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

def expectedAccounts (s : RecChainedState) (args : SpawnArgs) : Finset CellId :=
  insert args.child s.kernel.accounts

def accountsComp (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState SpawnArgs :=
  accountsComponent LE cN hN hLE expectedAccounts

def spawnCreateLegComp (D : SpawnCreateLeg → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState SpawnArgs :=
  spawnCreateLegComponent (toKernel := chainView.toKernel) (fresh := fun _ args => args.child) D hD

def capsComp (D : Caps → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState SpawnArgs :=
  funcComponent (β := Caps) (·.caps) D hD
    (fun s args => spawnCapsMap s.kernel args.actor args.child args.target)

def delegateComp (D : (CellId → Option CellId) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState SpawnArgs :=
  funcComponent (β := CellId → Option CellId) (·.delegate) D hD
    (fun s args => spawnDelegateMap s.kernel args.actor args.child)

/-- **`delegationsComp`** — the FAITHFUL spawn handoff component binding BOTH touched maps as ONE injective
product digest: the child's initial `delegations` snapshot AND its birth `delegationEpochAt` stamp. The
expected value reads the spawner-parent's CURRENT epoch out of the SAME before-kernel (`spawnEpochAtMap` =
`k.delegationEpoch actor` at the child), so the digest FORCES `post.delegationEpochAt child = parent_epoch`
— a genuine cross-cell force at the WHOLE-KERNEL descriptor layer (the parent's epoch is a value of the same
abstract kernel the descriptor commits over), NOT a freely-witnessed param. A forge that births the child
but leaves the stamp at the `0` default FAILS the product clause (the stamp leg disagrees). -/
def delegationsComp (D : (CellId → List Cap) × (CellId → Nat) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState SpawnArgs :=
  funcComponent (β := (CellId → List Cap) × (CellId → Nat))
    (fun k => (k.delegations, k.delegationEpochAt)) D hD
    (fun s args => (spawnDelegationsMap s.kernel args.actor args.child,
                    spawnEpochAtMap s.kernel args.actor args.child))

def spawnE (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs) :
    EffectSpec2Quint RecChainedState SpawnArgs where
  view         := chainView
  active1      := accountsComp LE cN hN hLE
  active2      := spawnCreateLegComp DLeg hDLeg
  active3      := capsComp DCaps hDCaps
  active4      := delegateComp DDel hDDel
  active5      := delegationsComp DDgs hDDgs
  logUpdate    := some (fun s args => createReceipt args.actor args.child :: s.log)
  restFrame    := fun k k' =>
    (k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments
      ∧ k'.factories = k.factories
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.heaps = k.heaps
      ∧ k'.nullifierRoot = k.nullifierRoot ∧ k'.revokedRoot = k.revokedRoot)
  guardGates   := spawnGuardGates
  guardProp    := spawnGuardProp
  guardWidth   := 1
  guardEncode  := spawnGuardEncode
  guardLocal   := spawnGuardLocal
  guardWidth_le := by decide

instance spawnE_guardDecidable (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs)
    (s : RecChainedState) (args : SpawnArgs) :
    Decidable ((spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs).guardProp s args) := by
  dsimp [spawnE]; infer_instance

/-! ### §2a — per-effect obligations. -/

theorem spawnGuardDecodes (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs) :
    GuardDecodes2Quint (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) := by
  intro s args s' hsat
  dsimp [spawnE] at hsat
  have hg := hsat cBitGuard (by simp [spawnGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, spawnGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem spawnGuardEncodes (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs) :
    GuardEncodes2Quint (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) := by
  intro s args s' hg
  dsimp [spawnE]
  intro c hc
  simp only [spawnGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, spawnGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem spawnRestFrameDecodes (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRest : RestIffNoSpawnTouched S.RH) :
    RestFrameDecodes2Quint S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) := by
  intro k k' h
  dsimp [spawnE]
  exact (hRest k k').mp h

/-! ### §2b — apex ↔ the QUINT-CIRCUIT spec (accounts + bal + caps + delegate + delegations + globals). -/

/-- What the v2-quint circuit pins: create-leg (`bal` + born-empty cell metadata) + authority handoff. -/
def SpawnCircuitSpec (st : RecChainedState) (actor child target : CellId) (st' : RecChainedState) :
    Prop :=
  spawnAdmit st.kernel actor child target
  ∧ st'.kernel.accounts = insert child st.kernel.accounts
  ∧ readSpawnCreateLeg st'.kernel = expectedSpawnCreateLeg st.kernel child
  ∧ st'.kernel.caps = spawnCapsMap st.kernel actor child target
  ∧ st'.kernel.delegate = spawnDelegateMap st.kernel actor child
  -- THE FAITHFUL HANDOFF PRODUCT (delegations snapshot + birth epoch stamp), forced by `active5`.
  ∧ (st'.kernel.delegations, st'.kernel.delegationEpochAt)
      = (spawnDelegationsMap st.kernel actor child, spawnEpochAtMap st.kernel actor child)
  ∧ st'.log = createReceipt actor child :: st.log
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.delegationEpoch = st.kernel.delegationEpoch
  ∧ st'.kernel.heaps = st.kernel.heaps
  ∧ st'.kernel.nullifierRoot = st.kernel.nullifierRoot ∧ st'.kernel.revokedRoot = st.kernel.revokedRoot

theorem SpawnSpec_implies_circuitSpec (st : RecChainedState) (actor child target : CellId)
    (st' : RecChainedState) (h : SpawnFullSpec st actor child target st') :
    SpawnCircuitSpec st actor child target st' := by
  obtain ⟨hadmit, hacc, hcell, hsc, hlif, hdc, hbal, hcaps, hdel, hdgs, hlog, h1, h2, h3, h4, h5,
      hstamp, h6, hNR, hRR⟩ := h
  refine ⟨hadmit, hacc, ?_, hcaps, hdel, ?_, hlog, h1, h2, h3, h4, h5, h6, hNR, hRR⟩
  · have hmeta := (bornEmptyCellMeta_post_iff st.kernel child st'.kernel).mpr ⟨hcell, hsc, hlif, hdc⟩
    exact (spawnCreateLeg_post_iff st.kernel child st'.kernel).mpr ⟨hbal, hmeta⟩
  · rw [Prod.mk.injEq]; exact ⟨hdgs, hstamp⟩

theorem apex_iff_spawnCircuitSpec (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState) :
    (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs).apex s args s' ↔
      SpawnCircuitSpec s args.actor args.child args.target s' := by
  dsimp only [EffectSpec2Quint.apex, spawnE, accountsComp, spawnCreateLegComp, capsComp, delegateComp,
    delegationsComp, accountsComponent, spawnCreateLegComponent, funcComponent, chainView,
    SpawnCircuitSpec, spawnGuardProp, spawnAdmit, expectedAccounts, readSpawnCreateLeg,
    expectedSpawnCreateLeg, spawnCapsMap, spawnDelegateMap]
  constructor
  · rintro ⟨hg, hacc, hleg, hcaps, hdel, hdgs, hlog, hNul, hRev, hCom, hFac, hDE⟩
    exact ⟨hg, hacc, hleg, hcaps, hdel, hdgs, hlog, hNul, hRev, hCom, hFac, hDE⟩
  · rintro ⟨hg, hacc, hleg, hcaps, hdel, hdgs, hlog, hNul, hRev, hCom, hFac, hDE⟩
    exact ⟨hg, hacc, hleg, hcaps, hdel, hdgs, hlog, hNul, hRev, hCom, hFac, hDE⟩

/-! ### §2c — apex ↔ FULL `SpawnSpec` (executor semantics). -/

/-- **`apex_iff_spawnSpec`** — the deployed spawn apex IS the STRENGTHENED `SpawnFullSpec`. The product
`active5` pins `(delegations, delegationEpochAt) = (spawnDelegationsMap, spawnEpochAtMap)`, so the BIRTH
STAMP is forced (no longer the framed/residual face): the child's epoch tag is bound to the spawner-parent's
current epoch read off the same before-kernel. -/
theorem apex_iff_spawnSpec (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState) :
    (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs).apex s args s' ↔
      SpawnFullSpec s args.actor args.child args.target s' := by
  dsimp only [EffectSpec2Quint.apex, spawnE, accountsComp, spawnCreateLegComp, capsComp, delegateComp,
    delegationsComp, accountsComponent, spawnCreateLegComponent, funcComponent, chainView, SpawnFullSpec,
    spawnGuardProp, spawnAdmit, expectedAccounts, readSpawnCreateLeg, expectedSpawnCreateLeg,
    spawnCapsMap, spawnDelegateMap]
  constructor
  · rintro ⟨hg, hacc, hleg, hcaps, hdel, hprod, hlog, hNul, hRev, hCom, hFac, hDE, hHeaps, hNR, hRR⟩
    obtain ⟨hbal, hmeta⟩ :=
      (spawnCreateLeg_post_iff s.kernel args.child s'.kernel).mp hleg
    obtain ⟨hcell, hsc, hlif, hdc⟩ :=
      (bornEmptyCellMeta_post_iff s.kernel args.child s'.kernel).mp hmeta
    rw [Prod.mk.injEq] at hprod
    exact ⟨hg, hacc, hcell, hsc, hlif, hdc, hbal, hcaps, hdel, hprod.1, hlog, hNul, hRev, hCom,
      hFac, hDE, hprod.2, hHeaps, hNR, hRR⟩
  · rintro ⟨hg, hacc, hcell, hsc, hlif, hdc, hbal, hcaps, hdel, hdgs, hlog, hNul, hRev, hCom,
      hFac, hDE, hstamp, hHeaps, hNR, hRR⟩
    refine ⟨hg, hacc, ?_, hcaps, hdel, ?_, hlog, hNul, hRev, hCom, hFac, hDE, hHeaps, hNR, hRR⟩
    · exact (spawnCreateLeg_post_iff s.kernel args.child s'.kernel).mpr
        ⟨hbal, (bornEmptyCellMeta_post_iff s.kernel args.child s'.kernel).mpr ⟨hcell, hsc, hlif, hdc⟩⟩
    · rw [Prod.mk.injEq]; exact ⟨hdgs, hstamp⟩

/-! ### §2d — THE VALIDATION. -/

theorem spawnA_full_sound
    (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRest : RestIffNoSpawnTouched S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState)
    (h : satisfiedE2Quint S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
        (encodeE2Quint S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
          s args s')) :
    SpawnFullSpec s args.actor args.child args.target s' := by
  have hapex :=
    effect2quint_circuit_full_sound S
      (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
      (spawnRestFrameDecodes S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs hRest) hLog
      (spawnGuardDecodes LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) s args s' h
  exact (apex_iff_spawnSpec LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs s args s').mp hapex



/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def spawnEWire : EffectSpec2Quint RecChainedState SpawnArgs where
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
  active4      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  active5      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := spawnGuardGates
  guardProp    := spawnGuardProp
  guardWidth   := 1
  guardEncode  := spawnGuardEncode
  guardLocal   := spawnGuardLocal
  guardWidth_le := by decide

def spawnAAirName : String := "dregg-spawnA-v2"

def spawnAEmitted : EmittedDescriptor := emittedEffect2Quint spawnAAirName spawnEWire

#guard spawnAEmitted.name == spawnAAirName

#assert_axioms spawnGuardLocal
#assert_axioms spawnGuardDecodes
#assert_axioms spawnGuardEncodes
#assert_axioms apex_iff_spawnCircuitSpec
#assert_axioms apex_iff_spawnSpec
#assert_axioms spawnA_full_sound

end Dregg2.Circuit.Inst.SpawnA