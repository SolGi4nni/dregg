/-
# Dregg2.Circuit.Inst.swissHandoffA — the v2 (`EffectCommit2`) instance for the CapTP sturdy-ref
  HANDOFF `swissHandoffA` (the swiss-table HANDOFF arm of `execFullA`).

`swissHandoffA sw certHash introducer exporter` binds a 3-vat introduce CERT to the swiss entry and
BUMPS the entry's `refcount` via `replaceSwiss`. GATED on `HandoffGuard` (AUTHORITY ∧ MEMBERSHIP).

Through the v2 framework (`EffectCommit2`):
  * touched component = `swiss` (`listComponent`, FULL-list digest);
  * the log GROWS by the authority receipt;
  * the guard is the 2-conjunct `HandoffGuard`, committed as ONE `propBit` column;
  * the frame is the 16 non-`swiss` kernel fields (`RestIffNoSwiss`).

`swissHandoffA_full_sound` CONCLUDES the bespoke `Spec.SwissHandoff.HandoffSpec` THROUGH the framework.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.swisshandoff

namespace Dregg2.Circuit.Inst.SwissHandoffA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.SwissHandoff
open Dregg2.Circuit.Spec.SwissFrame
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (stateAuthB)

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system. -/

abbrev vBitGuard : Var := 0

def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `RestIffNoSwiss` portal. -/

def RestIffNoSwiss (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)

/-! ## §2 — the `swissHandoffA` instance (touched component = `swiss`). -/

structure HandoffArgs where
  sw         : Nat
  certHash   : Nat
  introducer : CellId
  exporter   : CellId

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

def handoffGuardProp (s : RecChainedState) (args : HandoffArgs) : Prop :=
  HandoffGuard s args.sw args.introducer args.exporter

instance (s : RecChainedState) (args : HandoffArgs) : Decidable (handoffGuardProp s args) := by
  unfold handoffGuardProp HandoffGuard
  exact inferInstanceAs (Decidable (_ ∧ _))

def handoffGuardEncode (s : RecChainedState) (args : HandoffArgs) (_s' : RecChainedState) : Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (handoffGuardProp s args) else 0

def handoffGuardGates : ConstraintSystem := [cBitGuard]

theorem handoffGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied handoffGuardGates a ↔ satisfied handoffGuardGates b := by
  unfold satisfied handoffGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

def handoffSwissPostClause (s : RecChainedState) (args : HandoffArgs) : List SwissRecord :=
  match handoffSwissUpdate s.kernel.swiss args.sw args.certHash with
  | some ss => ss
  | none    => s.kernel.swiss

def swissComponent (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState HandoffArgs :=
  listComponent (·.swiss) LE cN hN hLE handoffSwissPostClause

def swissHandoffE (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    EffectSpec2 RecChainedState HandoffArgs where
  view         := chainView
  active       := swissComponent LE cN hN hLE
  logUpdate    := some (fun s args => handoffReceipt args.introducer args.exporter :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)
  guardGates   := handoffGuardGates
  guardProp    := handoffGuardProp
  guardWidth   := 1
  guardEncode  := handoffGuardEncode
  guardLocal   := handoffGuardLocal
  guardWidth_le := by decide

/-! ### §2a — per-effect obligations. -/

theorem handoffGuardDecodes (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardDecodes2 (swissHandoffE LE cN hN hLE) := by
  intro s args s' hsat
  change satisfied handoffGuardGates (handoffGuardEncode s args s') at hsat
  show handoffGuardProp s args
  have hg := hsat cBitGuard (by simp [handoffGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, handoffGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem handoffGuardEncodes (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardEncodes2 (swissHandoffE LE cN hN hLE) := by
  intro s args s' hg
  show satisfied handoffGuardGates (handoffGuardEncode s args s')
  intro c hc
  simp only [handoffGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, handoffGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem handoffRestFrameDecodes (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoSwiss S.RH) :
    RestFrameDecodes2 S (swissHandoffE LE cN hN hLE) := fun k k' h => (hRest k k').mp h

/-! ### §2b — apex ↔ `HandoffSpec` bridge. -/

theorem apex_iff_handoffSpec (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : HandoffArgs) (s' : RecChainedState) :
    (swissHandoffE LE cN hN hLE).apex s args s'
      ↔ HandoffSpec s args.sw args.certHash args.introducer args.exporter s' := by
  show (handoffGuardProp s args
        ∧ s'.kernel.swiss = handoffSwissPostClause s args
        ∧ s'.log = handoffReceipt args.introducer args.exporter :: s.log
        ∧ ((swissHandoffE LE cN hN hLE).restFrame s.kernel s'.kernel))
       ↔ HandoffSpec s args.sw args.certHash args.introducer args.exporter s'
  unfold HandoffSpec handoffGuardProp handoffSwissPostClause swissHandoffE
  constructor
  · rintro ⟨hg, hsw, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB, hDE, hDEA⟩
    cases s' with | mk kernel log =>
    cases hf : findSwiss s.kernel.swiss args.sw with
    | none => exact absurd hg.2 (by simp [hf, Option.isSome])
    | some e =>
      have hK : kernel = { s.kernel with swiss := kernel.swiss } :=
        recKernel_ext hAcc hCell hCaps hNul hRev hCom hBal rfl hSC hFac hLif hDC hDel hDgs hSB hDE hDEA
      have hupd := handoffSwissUpdate_some s.kernel.swiss args.sw args.certHash e hf
      have hcl : handoffSwissPostClause s args = handoffSwissPost s.kernel.swiss args.sw e args.certHash := by
        simp [handoffSwissPostClause, hupd]
      have hpost : handoffSwissPost s.kernel.swiss args.sw e args.certHash = kernel.swiss :=
        (hsw.trans hcl).symm
      have hsome : handoffSwissUpdate s.kernel.swiss args.sw args.certHash = some kernel.swiss := by
        rw [hupd, congr_arg some hpost]
      have hk' := (handoffSwissUpdate_eq_k s.kernel args.sw args.certHash kernel.swiss).mp hsome
      have hk : swissHandoffK s.kernel args.sw args.certHash = some kernel :=
        hk'.trans (congr_arg some hK.symm)
      refine ⟨hg, ⟨kernel, ⟨hk, ?_⟩⟩⟩
      simpa using hlog
  · rintro ⟨hg, ⟨k', hk, hs'⟩⟩
    rcases withSwiss_preserves_rest s.kernel k'.swiss with
      ⟨hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hSC, hFac, hLif, hDC, hDel, hDgs, hSB, hDE, hDEA⟩
    cases hf : findSwiss s.kernel.swiss args.sw with
    | none => exact absurd hg.2 (by simp [hf, Option.isSome])
    | some e =>
      have hupd := handoffSwissUpdate_some s.kernel.swiss args.sw args.certHash e hf
      have hk' := swissHandoffK_eq_withSwiss hk
      have hupd' : handoffSwissUpdate s.kernel.swiss args.sw args.certHash = some k'.swiss :=
        (handoffSwissUpdate_eq_k s.kernel args.sw args.certHash k'.swiss).mpr hk'
      have hpost : handoffSwissPost s.kernel.swiss args.sw e args.certHash = k'.swiss :=
        Option.some.inj (hupd.symm.trans hupd')
      have hsw' : k'.swiss =
          match handoffSwissUpdate s.kernel.swiss args.sw args.certHash with
          | some ss => ss
          | none => s.kernel.swiss := by
        simp [handoffSwissPostClause, hupd, hpost]
      have hker : s'.kernel = k' := congr_arg RecChainedState.kernel hs'
      have hlog : s'.log = handoffReceipt args.introducer args.exporter :: s.log :=
        congr_arg RecChainedState.log hs'
      have hK' := swissHandoffK_only_swiss hk
      have hrest : (swissHandoffE LE cN hN hLE).restFrame s.kernel s'.kernel := by
        rw [hker, hK']
        exact restFrame_of_withSwiss rfl
      refine ⟨hg, ?_, hlog, hrest⟩
      rw [hker]
      exact hsw'

/-! ### §2c — THE VALIDATION. -/

theorem swissHandoffA_full_sound
    (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoSwiss S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : HandoffArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (swissHandoffE LE cN hN hLE) (encodeE2 S (swissHandoffE LE cN hN hLE) s args s')) :
    HandoffSpec s args.sw args.certHash args.introducer args.exporter s' := by
  have hapex : (swissHandoffE LE cN hN hLE).apex s args s' :=
    effect2_circuit_full_sound S (swissHandoffE LE cN hN hLE)
      (handoffRestFrameDecodes S LE cN hN hLE hRest) hLog (handoffGuardDecodes LE cN hN hLE)
      s args s' h
  exact (apex_iff_handoffSpec LE cN hN hLE s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def swissHandoffEWire : EffectSpec2 RecChainedState HandoffArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := handoffGuardGates
  guardProp    := handoffGuardProp
  guardWidth   := 1
  guardEncode  := handoffGuardEncode
  guardLocal   := handoffGuardLocal
  guardWidth_le := by decide

def swissHandoffAAirName : String := "dregg-swissHandoffA-v2"

def swissHandoffAEmitted : EmittedDescriptor := emittedEffect2 swissHandoffAAirName swissHandoffEWire

#guard swissHandoffAEmitted.name == swissHandoffAAirName

/-! ## §3 — axiom-hygiene tripwires. -/

#assert_axioms handoffGuardLocal
#assert_axioms handoffGuardDecodes
#assert_axioms handoffGuardEncodes
#assert_axioms apex_iff_handoffSpec
#assert_axioms swissHandoffA_full_sound

end Dregg2.Circuit.Inst.SwissHandoffA