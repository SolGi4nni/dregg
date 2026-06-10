/-
# Dregg2.Circuit.Inst.refreshDelegationA — the v2 (`EffectCommit2`) instance for the
  `refreshDelegationA` effect (parent c-list snapshot into `delegations`).

THE VALIDATION: `refreshDelegationA_full_sound ⇒ RefreshDelegationSpec` THROUGH the framework.

ADDITIVE: imports `EffectCommit2` + `Spec/refreshdelegation`; edits neither.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.refreshdelegation

namespace Dregg2.Circuit.Inst.RefreshDelegationA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.Spec.RefreshDelegation
open Dregg2.Authority (Caps Cap)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-- **`RestIffNoDelegations RH`** — rest portal omitting the touched `delegations` field. -/
def RestIffNoDelegations (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)

structure RefreshDelegationArgs where
  actor : CellId
  child : CellId

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

def refreshDelegationGuardProp (s : RecChainedState) (args : RefreshDelegationArgs) : Prop :=
  RefreshDelegationGuard s args.actor args.child

instance (s : RecChainedState) (args : RefreshDelegationArgs) :
    Decidable (refreshDelegationGuardProp s args) := by
  unfold refreshDelegationGuardProp RefreshDelegationGuard
  exact inferInstanceAs (Decidable (_ ∧ _))

def refreshDelegationGuardEncode (s : RecChainedState) (args : RefreshDelegationArgs)
    (_s' : RecChainedState) : Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (refreshDelegationGuardProp s args) else 0

def refreshDelegationGuardGates : ConstraintSystem := [cBitGuard]

theorem refreshDelegationGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied refreshDelegationGuardGates a ↔ satisfied refreshDelegationGuardGates b := by
  unfold satisfied refreshDelegationGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

def delegationsComponent (D : (CellId → List Cap) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState RefreshDelegationArgs :=
  funcComponent (β := CellId → List Cap) (·.delegations) D hD
    (fun s args => refreshDelegationsMap s.kernel args.child)

def refreshDelegationE (D : (CellId → List Cap) → ℤ) (hD : Function.Injective D) :
    EffectSpec2 RecChainedState RefreshDelegationArgs where
  view         := chainView
  active       := delegationsComponent D hD
  logUpdate    := some (fun s args => refreshDelegationReceipt args.actor args.child :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)
  guardGates   := refreshDelegationGuardGates
  guardProp    := refreshDelegationGuardProp
  guardWidth   := 1
  guardEncode  := refreshDelegationGuardEncode
  guardLocal   := refreshDelegationGuardLocal
  guardWidth_le := by decide

theorem refreshDelegationGuardDecodes (D : (CellId → List Cap) → ℤ) (hD : Function.Injective D) :
    GuardDecodes2 (refreshDelegationE D hD) := by
  intro s args s' hsat
  change satisfied refreshDelegationGuardGates (refreshDelegationGuardEncode s args s') at hsat
  show refreshDelegationGuardProp s args
  have hg := hsat cBitGuard (by simp [refreshDelegationGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, refreshDelegationGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem refreshDelegationGuardEncodes (D : (CellId → List Cap) → ℤ) (hD : Function.Injective D) :
    GuardEncodes2 (refreshDelegationE D hD) := by
  intro s args s' hg
  show satisfied refreshDelegationGuardGates (refreshDelegationGuardEncode s args s')
  intro c hc
  simp only [refreshDelegationGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, refreshDelegationGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem refreshDelegationRestFrameDecodes (S : Surface2) (D : (CellId → List Cap) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoDelegations S.RH) :
    RestFrameDecodes2 S (refreshDelegationE D hD) := fun k k' h => (hRest k k').mp h

theorem apex_iff_refreshDelegationSpec (D : (CellId → List Cap) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : RefreshDelegationArgs) (s' : RecChainedState) :
    (refreshDelegationE D hD).apex s args s' ↔
      RefreshDelegationSpec s args.actor args.child s' := by
  show (refreshDelegationGuardProp s args
        ∧ s'.kernel.delegations = refreshDelegationsMap s.kernel args.child
        ∧ s'.log = refreshDelegationReceipt args.actor args.child :: s.log
        ∧ ((refreshDelegationE D hD).restFrame s.kernel s'.kernel))
       ↔ RefreshDelegationSpec s args.actor args.child s'
  unfold RefreshDelegationSpec refreshDelegationGuardProp refreshDelegationE
  constructor
  · rintro ⟨hg, hdgs, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac,
      hLif, hDC, hDel, hSB⟩
    exact ⟨hg, hdgs, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac,
      hLif, hDC, hDel, hSB⟩
  · rintro ⟨hg, hdgs, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac,
      hLif, hDC, hDel, hSB⟩
    exact ⟨hg, hdgs, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac,
      hLif, hDC, hDel, hSB⟩

theorem refreshDelegationA_full_sound
    (S : Surface2) (D : (CellId → List Cap) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoDelegations S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RefreshDelegationArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (refreshDelegationE D hD)
        (encodeE2 S (refreshDelegationE D hD) s args s')) :
    RefreshDelegationSpec s args.actor args.child s' := by
  have hapex : (refreshDelegationE D hD).apex s args s' :=
    effect2_circuit_full_sound S (refreshDelegationE D hD)
      (refreshDelegationRestFrameDecodes S D hD hRest) hLog
      (refreshDelegationGuardDecodes D hD) s args s' h
  exact (apex_iff_refreshDelegationSpec D hD s args s').mp hapex



/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def refreshDelegationEWire : EffectSpec2 RecChainedState RefreshDelegationArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := refreshDelegationGuardGates
  guardProp    := refreshDelegationGuardProp
  guardWidth   := 1
  guardEncode  := refreshDelegationGuardEncode
  guardLocal   := refreshDelegationGuardLocal
  guardWidth_le := by decide

def refreshDelegationAAirName : String := "dregg-refreshDelegationA-v2"

def refreshDelegationAEmitted : EmittedDescriptor := emittedEffect2 refreshDelegationAAirName refreshDelegationEWire

#guard refreshDelegationAEmitted.name == refreshDelegationAAirName

#assert_axioms refreshDelegationGuardLocal
#assert_axioms refreshDelegationGuardDecodes
#assert_axioms refreshDelegationGuardEncodes
#assert_axioms apex_iff_refreshDelegationSpec
#assert_axioms refreshDelegationA_full_sound

end Dregg2.Circuit.Inst.RefreshDelegationA