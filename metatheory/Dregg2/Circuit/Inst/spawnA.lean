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
    (k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.factories = k.factories ∧ k'.sealedBoxes = k.sealedBoxes)

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

def delegationsComp (D : (CellId → List Cap) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState SpawnArgs :=
  funcComponent (β := CellId → List Cap) (·.delegations) D hD
    (fun s args => spawnDelegationsMap s.kernel args.actor args.child)

def spawnE (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs) :
    EffectSpec2Quint RecChainedState SpawnArgs where
  view         := chainView
  active1      := accountsComp LE cN hN hLE
  active2      := spawnCreateLegComp DLeg hDLeg
  active3      := capsComp DCaps hDCaps
  active4      := delegateComp DDel hDDel
  active5      := delegationsComp DDgs hDDgs
  logUpdate    := some (fun s args => createReceipt args.actor args.child :: s.log)
  restFrame    := fun k k' =>
    (k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.factories = k.factories ∧ k'.sealedBoxes = k.sealedBoxes)
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
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (s : RecChainedState) (args : SpawnArgs) :
    Decidable ((spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs).guardProp s args) := by
  dsimp [spawnE]; infer_instance

/-! ### §2a — per-effect obligations. -/

theorem spawnGuardDecodes (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs) :
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
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs) :
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
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
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
  ∧ st'.kernel.delegations = spawnDelegationsMap st.kernel actor child
  ∧ st'.log = createReceipt actor child :: st.log
  ∧ st'.kernel.escrows = st.kernel.escrows
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.queues = st.kernel.queues
  ∧ st'.kernel.swiss = st.kernel.swiss
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.sealedBoxes = st.kernel.sealedBoxes

theorem SpawnSpec_implies_circuitSpec (st : RecChainedState) (actor child target : CellId)
    (st' : RecChainedState) (h : SpawnSpec st actor child target st') :
    SpawnCircuitSpec st actor child target st' := by
  obtain ⟨hadmit, hacc, hcell, hsc, hlif, hdc, hbal, hcaps, hdel, hdgs, hlog, h1, h2, h3, h4, h5,
      h6, h7, h8⟩ := h
  refine ⟨hadmit, hacc, ?_, hcaps, hdel, hdgs, hlog, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hmeta := (bornEmptyCellMeta_post_iff st.kernel child st'.kernel).mpr ⟨hcell, hsc, hlif, hdc⟩
  exact (spawnCreateLeg_post_iff st.kernel child st'.kernel).mpr ⟨hbal, hmeta⟩

theorem apex_iff_spawnCircuitSpec (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState) :
    (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs).apex s args s' ↔
      SpawnCircuitSpec s args.actor args.child args.target s' := by
  dsimp only [EffectSpec2Quint.apex, spawnE, accountsComp, spawnCreateLegComp, capsComp, delegateComp,
    delegationsComp, accountsComponent, spawnCreateLegComponent, funcComponent, chainView,
    SpawnCircuitSpec, spawnGuardProp, spawnAdmit, expectedAccounts, readSpawnCreateLeg,
    expectedSpawnCreateLeg, spawnCapsMap, spawnDelegateMap, spawnDelegationsMap]
  constructor
  · rintro ⟨hg, hacc, hleg, hcaps, hdel, hdgs, hlog, hEsc, hNul, hRev, hCom, hQ, hSw, hFac, hSB⟩
    exact ⟨hg, hacc, hleg, hcaps, hdel, hdgs, hlog, hEsc, hNul, hRev, hCom, hQ, hSw, hFac, hSB⟩
  · rintro ⟨hg, hacc, hleg, hcaps, hdel, hdgs, hlog, hEsc, hNul, hRev, hCom, hQ, hSw, hFac, hSB⟩
    exact ⟨hg, hacc, hleg, hcaps, hdel, hdgs, hlog, hEsc, hNul, hRev, hCom, hQ, hSw, hFac, hSB⟩

/-! ### §2c — apex ↔ FULL `SpawnSpec` (executor semantics). -/

theorem apex_iff_spawnSpec (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState) :
    (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs).apex s args s' ↔
      SpawnSpec s args.actor args.child args.target s' := by
  dsimp only [EffectSpec2Quint.apex, spawnE, accountsComp, spawnCreateLegComp, capsComp, delegateComp,
    delegationsComp, accountsComponent, spawnCreateLegComponent, funcComponent, chainView, SpawnSpec,
    spawnGuardProp, spawnAdmit, expectedAccounts, readSpawnCreateLeg, expectedSpawnCreateLeg,
    spawnCapsMap, spawnDelegateMap, spawnDelegationsMap]
  constructor
  · rintro ⟨hg, hacc, hleg, hcaps, hdel, hdgs, hlog, hEsc, hNul, hRev, hCom, hQ, hSw, hFac, hSB⟩
    obtain ⟨hbal, hmeta⟩ :=
      (spawnCreateLeg_post_iff s.kernel args.child s'.kernel).mp hleg
    obtain ⟨hcell, hsc, hlif, hdc⟩ :=
      (bornEmptyCellMeta_post_iff s.kernel args.child s'.kernel).mp hmeta
    exact ⟨hg, hacc, hcell, hsc, hlif, hdc, hbal, hcaps, hdel, hdgs, hlog, hEsc, hNul, hRev, hCom, hQ,
      hSw, hFac, hSB⟩
  · rintro ⟨hg, hacc, hcell, hsc, hlif, hdc, hbal, hcaps, hdel, hdgs, hlog, hEsc, hNul, hRev, hCom, hQ,
      hSw, hFac, hSB⟩
    refine ⟨hg, hacc, ?_, hcaps, hdel, hdgs, hlog, hEsc, hNul, hRev, hCom, hQ, hSw, hFac, hSB⟩
    exact (spawnCreateLeg_post_iff s.kernel args.child s'.kernel).mpr
      ⟨hbal, (bornEmptyCellMeta_post_iff s.kernel args.child s'.kernel).mpr ⟨hcell, hsc, hlif, hdc⟩⟩

/-! ### §2d — THE VALIDATION. -/

theorem spawnA_full_sound
    (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRest : RestIffNoSpawnTouched S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState)
    (h : satisfiedE2Quint S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
        (encodeE2Quint S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
          s args s')) :
    SpawnSpec s args.actor args.child args.target s' := by
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