/-
# Dregg2.Circuit.Inst.receiptArchiveLifecycleA — the v2 (`EffectCommit2`) instance for the DEPLOYED
  receipt-archive effect `receiptArchiveA` (Live → Archived LIFECYCLE side-table transition).

The DEPLOYED `apply_receipt_archive` (`c.archive(checkpoint)`) moves the `lifecycle` SIDE-TABLE to
`Archived (4)` — the `cellSeal`/`cellDestroy` shape, NOT a `cell` record slot. This is the v2 Surface2
lifecycle circuit for that move (the analog of `Inst.cellSealA`), validating
`receiptArchiveLifecycleA_full_sound ⇒ ReceiptArchiveLifecycleSpec` THROUGH the framework. The
record-slot `receiptArchiveE` (`Inst.receiptArchiveA`) is the SUPERSEDED pre-V3 model; THIS is the
deployed-semantics v2 circuit the turn-refinement dispatch consumes.

ADDITIVE: imports `EffectCommit2` + `Spec/cellstateaudit`; edits neither.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.cellstateaudit

namespace Dregg2.Circuit.Inst.ReceiptArchiveLifecycleA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.Spec.CellStateAudit
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (cellLive stateAuthB)

set_option linter.dupNamespace false

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-- **`RestIffNoLifecycle RH`** — rest portal omitting the touched `lifecycle` field (every non-lifecycle
component, INCLUDING the `cell` record map, frozen — the deployed archive touches only the side-table). -/
def RestIffNoLifecycle (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.deathCert = k.deathCert
      ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt
      ∧ k'.heaps = k.heaps
      ∧ k'.nullifierRoot = k.nullifierRoot ∧ k'.revokedRoot = k.revokedRoot)

structure ReceiptArchiveArgs where
  actor : CellId
  cell  : CellId

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The deployed receipt-archive guard prop is the three-leg `auditGuard` (authority, membership,
liveness — the SAME gate `receiptArchiveChainA` checks and `ReceiptArchiveLifecycleSpec` exposes). -/
def archiveGuardProp (s : RecChainedState) (args : ReceiptArchiveArgs) : Prop :=
  auditGuard s args.actor args.cell

instance (s : RecChainedState) (args : ReceiptArchiveArgs) : Decidable (archiveGuardProp s args) := by
  unfold archiveGuardProp auditGuard; exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def archiveGuardEncode (s : RecChainedState) (args : ReceiptArchiveArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (archiveGuardProp s args) else 0

def archiveGuardGates : ConstraintSystem := [cBitGuard]

theorem archiveGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied archiveGuardGates a ↔ satisfied archiveGuardGates b := by
  unfold satisfied archiveGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The active lifecycle component: the post `lifecycle` side-table IS `archiveLifecycleMap` (flip `cell`
to `Archived`). -/
def lifecycleComponent (D : (CellId → Nat) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState ReceiptArchiveArgs :=
  funcComponent (β := CellId → Nat) (·.lifecycle) D hD
    (fun s args => archiveLifecycleMap s.kernel args.cell)

def receiptArchiveLifecycleE (D : (CellId → Nat) → ℤ) (hD : Function.Injective D) :
    EffectSpec2 RecChainedState ReceiptArchiveArgs where
  view         := chainView
  active       := lifecycleComponent D hD
  logUpdate    := some (fun s args =>
    { actor := args.actor, src := args.cell, dst := args.cell, amt := 0 } :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.deathCert = k.deathCert
      ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt
      ∧ k'.heaps = k.heaps
      ∧ k'.nullifierRoot = k.nullifierRoot ∧ k'.revokedRoot = k.revokedRoot)
  guardGates   := archiveGuardGates
  guardProp    := archiveGuardProp
  guardWidth   := 1
  guardEncode  := archiveGuardEncode
  guardLocal   := archiveGuardLocal
  guardWidth_le := by decide

theorem archiveGuardDecodes (D : (CellId → Nat) → ℤ) (hD : Function.Injective D) :
    GuardDecodes2 (receiptArchiveLifecycleE D hD) := by
  intro s args s' hsat
  change satisfied archiveGuardGates (archiveGuardEncode s args s') at hsat
  show archiveGuardProp s args
  have hg := hsat cBitGuard (by simp [archiveGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, archiveGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem archiveGuardEncodes (D : (CellId → Nat) → ℤ) (hD : Function.Injective D) :
    GuardEncodes2 (receiptArchiveLifecycleE D hD) := by
  intro s args s' hg
  show satisfied archiveGuardGates (archiveGuardEncode s args s')
  intro c hc
  simp only [archiveGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, archiveGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem archiveRestFrameDecodes (S : Surface2) (D : (CellId → Nat) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoLifecycle S.RH) :
    RestFrameDecodes2 S (receiptArchiveLifecycleE D hD) := fun k k' h => (hRest k k').mp h

theorem apex_iff_ReceiptArchiveLifecycleSpec (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : ReceiptArchiveArgs) (s' : RecChainedState) :
    (receiptArchiveLifecycleE D hD).apex s args s' ↔
      ReceiptArchiveLifecycleSpec s args.actor args.cell s' := by
  show (archiveGuardProp s args
        ∧ s'.kernel.lifecycle = archiveLifecycleMap s.kernel args.cell
        ∧ s'.log = { actor := args.actor, src := args.cell, dst := args.cell, amt := 0 } :: s.log
        ∧ ((receiptArchiveLifecycleE D hD).restFrame s.kernel s'.kernel))
       ↔ ReceiptArchiveLifecycleSpec s args.actor args.cell s'
  unfold ReceiptArchiveLifecycleSpec archiveGuardProp receiptArchiveLifecycleE
  constructor
  · rintro ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hSC, hFac,
      hDC, hDel, hDgs, hDgE, hDgEA, hHeaps, hNR, hRR⟩
    exact ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hSC, hFac,
      hDC, hDel, hDgs, hDgE, hDgEA, hHeaps, hNR, hRR⟩
  · rintro ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hSC, hFac,
      hDC, hDel, hDgs, hDgE, hDgEA, hHeaps, hNR, hRR⟩
    exact ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hSC, hFac,
      hDC, hDel, hDgs, hDgE, hDgEA, hHeaps, hNR, hRR⟩

theorem receiptArchiveLifecycleA_full_sound
    (S : Surface2) (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoLifecycle S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ReceiptArchiveArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (receiptArchiveLifecycleE D hD)
          (encodeE2 S (receiptArchiveLifecycleE D hD) s args s')) :
    ReceiptArchiveLifecycleSpec s args.actor args.cell s' := by
  have hapex : (receiptArchiveLifecycleE D hD).apex s args s' :=
    effect2_circuit_full_sound S (receiptArchiveLifecycleE D hD)
      (archiveRestFrameDecodes S D hD hRest) hLog (archiveGuardDecodes D hD) s args s' h
  exact (apex_iff_ReceiptArchiveLifecycleSpec D hD s args s').mp hapex

/-! ## EMISSION — Lean→Plonky3 wire (the `cellSealA` analog). -/

def receiptArchiveLifecycleEWire : EffectSpec2 RecChainedState ReceiptArchiveArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := archiveGuardGates
  guardProp    := archiveGuardProp
  guardWidth   := 1
  guardEncode  := archiveGuardEncode
  guardLocal   := archiveGuardLocal
  guardWidth_le := by decide

def receiptArchiveLifecycleAAirName : String := "dregg-receiptArchiveLifecycleA-v2"

def receiptArchiveLifecycleAEmitted : EmittedDescriptor :=
  emittedEffect2 receiptArchiveLifecycleAAirName receiptArchiveLifecycleEWire

#guard receiptArchiveLifecycleAEmitted.name == receiptArchiveLifecycleAAirName

#assert_axioms apex_iff_ReceiptArchiveLifecycleSpec
#assert_axioms receiptArchiveLifecycleA_full_sound

end Dregg2.Circuit.Inst.ReceiptArchiveLifecycleA
