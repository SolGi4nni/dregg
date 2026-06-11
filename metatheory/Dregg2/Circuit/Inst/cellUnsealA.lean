/-
# Dregg2.Circuit.Inst.cellUnsealA — the v2 (`EffectCommit2`) instance for the cell UNSEAL effect
  `cellUnsealA` (Sealed → Live lifecycle transition).

THE VALIDATION: `cellUnsealA_full_sound ⇒ CellUnsealSpec` THROUGH the framework.

ADDITIVE: imports `EffectCommit2` + `Spec/celllifecycle`; edits neither.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.celllifecycle

namespace Dregg2.Circuit.Inst.CellUnsealA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.Spec.CellLifecycle
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-- **`RestIffNoLifecycle RH`** — rest portal omitting the touched `lifecycle` field. -/
def RestIffNoLifecycle (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.deathCert = k.deathCert
      ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt
      ∧ k'.heaps = k.heaps)

structure CellUnsealArgs where
  actor : CellId
  cell  : CellId

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

def cellUnsealGuardProp (s : RecChainedState) (args : CellUnsealArgs) : Prop :=
  CellUnsealGuard s args.actor args.cell

instance (s : RecChainedState) (args : CellUnsealArgs) : Decidable (cellUnsealGuardProp s args) := by
  unfold cellUnsealGuardProp CellUnsealGuard; exact inferInstanceAs (Decidable (_ ∧ _))

def cellUnsealGuardEncode (s : RecChainedState) (args : CellUnsealArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (cellUnsealGuardProp s args) else 0

def cellUnsealGuardGates : ConstraintSystem := [cBitGuard]

theorem cellUnsealGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied cellUnsealGuardGates a ↔ satisfied cellUnsealGuardGates b := by
  unfold satisfied cellUnsealGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

def lifecycleComponent (D : (CellId → Nat) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState CellUnsealArgs :=
  funcComponent (β := CellId → Nat) (·.lifecycle) D hD
    (fun s args => unsealLifecycleMap s.kernel args.cell)

def cellUnsealE (D : (CellId → Nat) → ℤ) (hD : Function.Injective D) :
    EffectSpec2 RecChainedState CellUnsealArgs where
  view         := chainView
  active       := lifecycleComponent D hD
  logUpdate    := some (fun s args => cellLifecycleReceipt args.actor args.cell :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.deathCert = k.deathCert
      ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt
      ∧ k'.heaps = k.heaps)
  guardGates   := cellUnsealGuardGates
  guardProp    := cellUnsealGuardProp
  guardWidth   := 1
  guardEncode  := cellUnsealGuardEncode
  guardLocal   := cellUnsealGuardLocal
  guardWidth_le := by decide

theorem cellUnsealGuardDecodes (D : (CellId → Nat) → ℤ) (hD : Function.Injective D) :
    GuardDecodes2 (cellUnsealE D hD) := by
  intro s args s' hsat
  change satisfied cellUnsealGuardGates (cellUnsealGuardEncode s args s') at hsat
  show cellUnsealGuardProp s args
  have hg := hsat cBitGuard (by simp [cellUnsealGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, cellUnsealGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem cellUnsealGuardEncodes (D : (CellId → Nat) → ℤ) (hD : Function.Injective D) :
    GuardEncodes2 (cellUnsealE D hD) := by
  intro s args s' hg
  show satisfied cellUnsealGuardGates (cellUnsealGuardEncode s args s')
  intro c hc
  simp only [cellUnsealGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, cellUnsealGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem cellUnsealRestFrameDecodes (S : Surface2) (D : (CellId → Nat) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoLifecycle S.RH) :
    RestFrameDecodes2 S (cellUnsealE D hD) := fun k k' h => (hRest k k').mp h

theorem apex_iff_cellUnsealSpec (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : CellUnsealArgs) (s' : RecChainedState) :
    (cellUnsealE D hD).apex s args s' ↔ CellUnsealSpec s args.actor args.cell s' := by
  show (cellUnsealGuardProp s args
        ∧ s'.kernel.lifecycle = unsealLifecycleMap s.kernel args.cell
        ∧ s'.log = cellLifecycleReceipt args.actor args.cell :: s.log
        ∧ ((cellUnsealE D hD).restFrame s.kernel s'.kernel))
       ↔ CellUnsealSpec s args.actor args.cell s'
  unfold CellUnsealSpec cellUnsealGuardProp cellUnsealE
  constructor
  · rintro ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
      hDC, hDel, hDgs, hSB⟩

theorem cellUnsealA_full_sound
    (S : Surface2) (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoLifecycle S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CellUnsealArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (cellUnsealE D hD) (encodeE2 S (cellUnsealE D hD) s args s')) :
    CellUnsealSpec s args.actor args.cell s' := by
  have hapex : (cellUnsealE D hD).apex s args s' :=
    effect2_circuit_full_sound S (cellUnsealE D hD)
      (cellUnsealRestFrameDecodes S D hD hRest) hLog (cellUnsealGuardDecodes D hD) s args s' h
  exact (apex_iff_cellUnsealSpec D hD s args s').mp hapex



/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def cellUnsealEWire : EffectSpec2 RecChainedState CellUnsealArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := cellUnsealGuardGates
  guardProp    := cellUnsealGuardProp
  guardWidth   := 1
  guardEncode  := cellUnsealGuardEncode
  guardLocal   := cellUnsealGuardLocal
  guardWidth_le := by decide

def cellUnsealAAirName : String := "dregg-cellUnsealA-v2"

def cellUnsealAEmitted : EmittedDescriptor := emittedEffect2 cellUnsealAAirName cellUnsealEWire

#guard cellUnsealAEmitted.name == cellUnsealAAirName

#assert_axioms cellUnsealGuardLocal
#assert_axioms cellUnsealGuardDecodes
#assert_axioms cellUnsealGuardEncodes
#assert_axioms apex_iff_cellUnsealSpec
#assert_axioms cellUnsealA_full_sound

end Dregg2.Circuit.Inst.CellUnsealA