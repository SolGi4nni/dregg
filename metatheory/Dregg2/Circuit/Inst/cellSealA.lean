/-
# Dregg2.Circuit.Inst.cellSealA — the v2 (`EffectCommit2`) instance for the cell SEAL effect
  `cellSealA` (Live → Sealed lifecycle transition).

THE VALIDATION: `cellSealA_full_sound ⇒ CellSealSpec` THROUGH the framework.

ADDITIVE: imports `EffectCommit2` + `Spec/celllifecycle`; edits neither.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.celllifecycle

namespace Dregg2.Circuit.Inst.CellSealA

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

structure CellSealArgs where
  actor : CellId
  cell  : CellId

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

def cellSealGuardProp (s : RecChainedState) (args : CellSealArgs) : Prop :=
  CellSealGuard s args.actor args.cell

instance (s : RecChainedState) (args : CellSealArgs) : Decidable (cellSealGuardProp s args) := by
  unfold cellSealGuardProp CellSealGuard; exact inferInstanceAs (Decidable (_ ∧ _))

def cellSealGuardEncode (s : RecChainedState) (args : CellSealArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (cellSealGuardProp s args) else 0

def cellSealGuardGates : ConstraintSystem := [cBitGuard]

theorem cellSealGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied cellSealGuardGates a ↔ satisfied cellSealGuardGates b := by
  unfold satisfied cellSealGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

def lifecycleComponent (D : (CellId → Nat) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState CellSealArgs :=
  funcComponent (β := CellId → Nat) (·.lifecycle) D hD
    (fun s args => sealLifecycleMap s.kernel args.cell)

def cellSealE (D : (CellId → Nat) → ℤ) (hD : Function.Injective D) :
    EffectSpec2 RecChainedState CellSealArgs where
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
  guardGates   := cellSealGuardGates
  guardProp    := cellSealGuardProp
  guardWidth   := 1
  guardEncode  := cellSealGuardEncode
  guardLocal   := cellSealGuardLocal
  guardWidth_le := by decide

theorem cellSealGuardDecodes (D : (CellId → Nat) → ℤ) (hD : Function.Injective D) :
    GuardDecodes2 (cellSealE D hD) := by
  intro s args s' hsat
  change satisfied cellSealGuardGates (cellSealGuardEncode s args s') at hsat
  show cellSealGuardProp s args
  have hg := hsat cBitGuard (by simp [cellSealGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, cellSealGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem cellSealGuardEncodes (D : (CellId → Nat) → ℤ) (hD : Function.Injective D) :
    GuardEncodes2 (cellSealE D hD) := by
  intro s args s' hg
  show satisfied cellSealGuardGates (cellSealGuardEncode s args s')
  intro c hc
  simp only [cellSealGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, cellSealGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem cellSealRestFrameDecodes (S : Surface2) (D : (CellId → Nat) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoLifecycle S.RH) :
    RestFrameDecodes2 S (cellSealE D hD) := fun k k' h => (hRest k k').mp h

theorem apex_iff_cellSealSpec (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : CellSealArgs) (s' : RecChainedState) :
    (cellSealE D hD).apex s args s' ↔ CellSealSpec s args.actor args.cell s' := by
  show (cellSealGuardProp s args
        ∧ s'.kernel.lifecycle = sealLifecycleMap s.kernel args.cell
        ∧ s'.log = cellLifecycleReceipt args.actor args.cell :: s.log
        ∧ ((cellSealE D hD).restFrame s.kernel s'.kernel))
       ↔ CellSealSpec s args.actor args.cell s'
  unfold CellSealSpec cellSealGuardProp cellSealE
  constructor
  · rintro ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
      hDC, hDel, hDgs, hSB⟩

theorem cellSealA_full_sound
    (S : Surface2) (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoLifecycle S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CellSealArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (cellSealE D hD) (encodeE2 S (cellSealE D hD) s args s')) :
    CellSealSpec s args.actor args.cell s' := by
  have hapex : (cellSealE D hD).apex s args s' :=
    effect2_circuit_full_sound S (cellSealE D hD)
      (cellSealRestFrameDecodes S D hD hRest) hLog (cellSealGuardDecodes D hD) s args s' h
  exact (apex_iff_cellSealSpec D hD s args s').mp hapex



/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def cellSealEWire : EffectSpec2 RecChainedState CellSealArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := cellSealGuardGates
  guardProp    := cellSealGuardProp
  guardWidth   := 1
  guardEncode  := cellSealGuardEncode
  guardLocal   := cellSealGuardLocal
  guardWidth_le := by decide

def cellSealAAirName : String := "dregg-cellSealA-v2"

def cellSealAEmitted : EmittedDescriptor := emittedEffect2 cellSealAAirName cellSealEWire

#guard cellSealAEmitted.name == cellSealAAirName

#assert_axioms cellSealGuardLocal
#assert_axioms cellSealGuardDecodes
#assert_axioms cellSealGuardEncodes
#assert_axioms apex_iff_cellSealSpec
#assert_axioms cellSealA_full_sound

end Dregg2.Circuit.Inst.CellSealA