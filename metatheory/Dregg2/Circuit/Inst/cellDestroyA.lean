/-
# Dregg2.Circuit.Inst.cellDestroyA — the v2-dual (`EffectCommit2Dual`) instance for the cell DESTROY
  effect `cellDestroyA` (non-terminal → Destroyed + `deathCert` bind).

Touches TWO function-fields: `lifecycle` (flip to `lcDestroyed`) and `deathCert` (bind `certHash` at
`cell`). THE VALIDATION: `cellDestroyA_full_sound ⇒ CellDestroySpec` THROUGH the dual framework.

ADDITIVE: imports `EffectCommit2Dual` + `Spec/celllifecycle`; edits neither.
-/
import Dregg2.Circuit.EffectCommit2Dual
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.celllifecycle

namespace Dregg2.Circuit.Inst.CellDestroyA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.Spec.CellLifecycle
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-- **`RestIffNoLifecycleDeathCert RH`** — rest portal omitting `lifecycle` and `deathCert`. -/
def RestIffNoLifecycleDeathCert (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories
      ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt
      ∧ k'.heaps = k.heaps)

structure CellDestroyArgs where
  actor    : CellId
  cell     : CellId
  certHash : Nat

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

def cellDestroyGuardProp (s : RecChainedState) (args : CellDestroyArgs) : Prop :=
  CellDestroyGuard s args.actor args.cell

instance (s : RecChainedState) (args : CellDestroyArgs) : Decidable (cellDestroyGuardProp s args) := by
  unfold cellDestroyGuardProp CellDestroyGuard; exact inferInstanceAs (Decidable (_ ∧ _))

def cellDestroyGuardEncode (s : RecChainedState) (args : CellDestroyArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (cellDestroyGuardProp s args) else 0

def cellDestroyGuardGates : ConstraintSystem := [cBitGuard]

theorem cellDestroyGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied cellDestroyGuardGates a ↔ satisfied cellDestroyGuardGates b := by
  unfold satisfied cellDestroyGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

def lifecycleComponent (D : (CellId → Nat) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState CellDestroyArgs :=
  funcComponent (β := CellId → Nat) (·.lifecycle) D hD
    (fun s args => (destroyKernelMap s.kernel args.cell args.certHash).lifecycle)

def deathCertComponent (D : (CellId → Nat) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState CellDestroyArgs :=
  funcComponent (β := CellId → Nat) (·.deathCert) D hD
    (fun s args => (destroyKernelMap s.kernel args.cell args.certHash).deathCert)

def cellDestroyE (DLif : (CellId → Nat) → ℤ) (hDLif : Function.Injective DLif)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC) :
    EffectSpec2Dual RecChainedState CellDestroyArgs where
  view         := chainView
  active1      := lifecycleComponent DLif hDLif
  active2      := deathCertComponent DDC hDDC
  logUpdate    := some (fun s args => cellLifecycleReceipt args.actor args.cell :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories
      ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt
      ∧ k'.heaps = k.heaps)
  guardGates   := cellDestroyGuardGates
  guardProp    := cellDestroyGuardProp
  guardWidth   := 1
  guardEncode  := cellDestroyGuardEncode
  guardLocal   := cellDestroyGuardLocal
  guardWidth_le := by decide

theorem cellDestroyGuardDecodes (DLif : (CellId → Nat) → ℤ) (hDLif : Function.Injective DLif)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC) :
    GuardDecodes2Dual (cellDestroyE DLif hDLif DDC hDDC) := by
  intro s args s' hsat
  change satisfied cellDestroyGuardGates (cellDestroyGuardEncode s args s') at hsat
  show cellDestroyGuardProp s args
  have hg := hsat cBitGuard (by simp [cellDestroyGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, cellDestroyGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem cellDestroyGuardEncodes (DLif : (CellId → Nat) → ℤ) (hDLif : Function.Injective DLif)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC) :
    GuardEncodes2Dual (cellDestroyE DLif hDLif DDC hDDC) := by
  intro s args s' hg
  show satisfied cellDestroyGuardGates (cellDestroyGuardEncode s args s')
  intro c hc
  simp only [cellDestroyGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, cellDestroyGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem cellDestroyRestFrameDecodes (S : Surface2) (DLif : (CellId → Nat) → ℤ)
    (hDLif : Function.Injective DLif) (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (hRest : RestIffNoLifecycleDeathCert S.RH) :
    RestFrameDecodes2Dual S (cellDestroyE DLif hDLif DDC hDDC) := fun k k' h => (hRest k k').mp h

theorem apex_iff_cellDestroySpec (DLif : (CellId → Nat) → ℤ) (hDLif : Function.Injective DLif)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (s : RecChainedState) (args : CellDestroyArgs) (s' : RecChainedState) :
    (cellDestroyE DLif hDLif DDC hDDC).apex s args s' ↔
      CellDestroySpec s args.actor args.cell args.certHash s' := by
  show (cellDestroyGuardProp s args
        ∧ s'.kernel.lifecycle = (destroyKernelMap s.kernel args.cell args.certHash).lifecycle
        ∧ s'.kernel.deathCert = (destroyKernelMap s.kernel args.cell args.certHash).deathCert
        ∧ s'.log = cellLifecycleReceipt args.actor args.cell :: s.log
        ∧ ((cellDestroyE DLif hDLif DDC hDDC).restFrame s.kernel s'.kernel))
       ↔ CellDestroySpec s args.actor args.cell args.certHash s'
  unfold CellDestroySpec cellDestroyGuardProp cellDestroyE
  constructor
  · rintro ⟨hg, hlif, hdc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
      hDel, hDgs, hSB⟩
    exact ⟨hg, hlif, hdc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
      hDel, hDgs, hSB⟩
  · rintro ⟨hg, hlif, hdc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
      hDel, hDgs, hSB⟩
    exact ⟨hg, hlif, hdc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
      hDel, hDgs, hSB⟩

theorem cellDestroyA_full_sound
    (S : Surface2) (DLif : (CellId → Nat) → ℤ) (hDLif : Function.Injective DLif)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (hRest : RestIffNoLifecycleDeathCert S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CellDestroyArgs) (s' : RecChainedState)
    (h : satisfiedE2Dual S (cellDestroyE DLif hDLif DDC hDDC)
        (encodeE2Dual S (cellDestroyE DLif hDLif DDC hDDC) s args s')) :
    CellDestroySpec s args.actor args.cell args.certHash s' := by
  have hapex : (cellDestroyE DLif hDLif DDC hDDC).apex s args s' :=
    effect2dual_circuit_full_sound S (cellDestroyE DLif hDLif DDC hDDC)
      (cellDestroyRestFrameDecodes S DLif hDLif DDC hDDC hRest) hLog
      (cellDestroyGuardDecodes DLif hDLif DDC hDDC) s args s' h
  exact (apex_iff_cellDestroySpec DLif hDLif DDC hDDC s args s').mp hapex



/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def cellDestroyEWire : EffectSpec2Dual RecChainedState CellDestroyArgs where
  view         := chainView
  active1      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  active2      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := cellDestroyGuardGates
  guardProp    := cellDestroyGuardProp
  guardWidth   := 1
  guardEncode  := cellDestroyGuardEncode
  guardLocal   := cellDestroyGuardLocal
  guardWidth_le := by decide

def cellDestroyAAirName : String := "dregg-cellDestroyA-v2"

def cellDestroyAEmitted : EmittedDescriptor := emittedEffect2Dual cellDestroyAAirName cellDestroyEWire

#guard cellDestroyAEmitted.name == cellDestroyAAirName

#assert_axioms cellDestroyGuardLocal
#assert_axioms cellDestroyGuardDecodes
#assert_axioms cellDestroyGuardEncodes
#assert_axioms apex_iff_cellDestroySpec
#assert_axioms cellDestroyA_full_sound

end Dregg2.Circuit.Inst.CellDestroyA