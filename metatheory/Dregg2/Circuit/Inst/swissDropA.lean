/-
# Dregg2.Circuit.Inst.swissDropA — the v2 (`EffectCommit2`) instance for the CapTP sturdy-ref DROP/GC
  `swissDropA` (the swiss-table DROP arm of `execFullA`).

`swissDropA sw actor exporter` DECREMENTS the swiss entry's `refcount`, GC-ing the entry when it hits 0
via `removeSwiss` / `replaceSwiss`. GATED on `DropGuard` (AUTHORITY ∧ MEMBERSHIP ∧ LIVE-REF).

Through the v2 framework (`EffectCommit2`):
  * touched component = `swiss` (`listComponent`, FULL-list digest);
  * the log GROWS by the authority receipt;
  * the guard is the 3-conjunct `DropGuard`, committed as ONE `propBit` column;
  * the frame is the 16 non-`swiss` kernel fields (`RestIffNoSwiss`).

`swissDropA_full_sound` CONCLUDES the bespoke `Spec.SwissDrop.DropSpec` THROUGH the framework.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.swissdrop

namespace Dregg2.Circuit.Inst.SwissDropA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.SwissDrop
open Dregg2.Circuit.Spec.SwissFrame
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

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

/-! ## §2 — the `swissDropA` instance (touched component = `swiss`). -/

structure DropArgs where
  sw       : Nat
  actor    : CellId
  exporter : CellId

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

def dropGuardProp (s : RecChainedState) (args : DropArgs) : Prop :=
  DropGuard s args.sw args.actor args.exporter

instance (s : RecChainedState) (args : DropArgs) : Decidable (dropGuardProp s args) := by
  unfold dropGuardProp DropGuard; exact inferInstanceAs (Decidable (_ ∧ _))

def dropGuardEncode (s : RecChainedState) (args : DropArgs) (_s' : RecChainedState) : Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (dropGuardProp s args) else 0

def dropGuardGates : ConstraintSystem := [cBitGuard]

theorem dropGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied dropGuardGates a ↔ satisfied dropGuardGates b := by
  unfold satisfied dropGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

def dropSwissPostClause (s : RecChainedState) (args : DropArgs) : List SwissRecord :=
  match dropSwissUpdate s.kernel.swiss args.sw with
  | some ss => ss
  | none    => s.kernel.swiss

def swissComponent (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState DropArgs :=
  listComponent (·.swiss) LE cN hN hLE dropSwissPostClause

def swissDropE (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    EffectSpec2 RecChainedState DropArgs where
  view         := chainView
  active       := swissComponent LE cN hN hLE
  logUpdate    := some (fun s args => dropReceipt args.actor args.exporter :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)
  guardGates   := dropGuardGates
  guardProp    := dropGuardProp
  guardWidth   := 1
  guardEncode  := dropGuardEncode
  guardLocal   := dropGuardLocal
  guardWidth_le := by decide

/-! ### §2a — per-effect obligations. -/

theorem dropGuardDecodes (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardDecodes2 (swissDropE LE cN hN hLE) := by
  intro s args s' hsat
  change satisfied dropGuardGates (dropGuardEncode s args s') at hsat
  show dropGuardProp s args
  have hg := hsat cBitGuard (by simp [dropGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, dropGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem dropGuardEncodes (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardEncodes2 (swissDropE LE cN hN hLE) := by
  intro s args s' hg
  show satisfied dropGuardGates (dropGuardEncode s args s')
  intro c hc
  simp only [dropGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, dropGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem dropRestFrameDecodes (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoSwiss S.RH) :
    RestFrameDecodes2 S (swissDropE LE cN hN hLE) := fun k k' h => (hRest k k').mp h

/-! ### §2b — apex ↔ `DropSpec` bridge. -/

theorem apex_iff_dropSpec (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : DropArgs) (s' : RecChainedState) :
    (swissDropE LE cN hN hLE).apex s args s'
      ↔ DropSpec s args.sw args.actor args.exporter s' := by
  show (dropGuardProp s args
        ∧ s'.kernel.swiss = dropSwissPostClause s args
        ∧ s'.log = dropReceipt args.actor args.exporter :: s.log
        ∧ ((swissDropE LE cN hN hLE).restFrame s.kernel s'.kernel))
       ↔ DropSpec s args.sw args.actor args.exporter s'
  unfold DropSpec dropGuardProp dropSwissPostClause swissDropE
  constructor
  · rintro ⟨hg, hsw, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB, hDE, hDEA⟩
    cases s' with | mk kernel log =>
    obtain ⟨e, ⟨hf, hpos⟩⟩ := hg.2
    have hK : kernel = { s.kernel with swiss := kernel.swiss } :=
      recKernel_ext hAcc hCell hCaps hNul hRev hCom hBal rfl hSC hFac hLif hDC hDel hDgs hSB hDE hDEA
    have hupd := dropSwissPost_eq_update s.kernel.swiss args.sw e hf hpos
    have hcl : dropSwissPostClause s args = dropSwissPost s.kernel.swiss args.sw e := by
      simp [dropSwissPostClause, hupd]
    have hpost : dropSwissPost s.kernel.swiss args.sw e = kernel.swiss := (hsw.trans hcl).symm
    have hsome : dropSwissUpdate s.kernel.swiss args.sw = some kernel.swiss := by
      rw [hupd, congr_arg some hpost]
    have hk' := (dropSwissUpdate_eq_k s.kernel args.sw kernel.swiss).mp hsome
    have hk : swissDropK s.kernel args.sw = some kernel :=
      hk'.trans (congr_arg some hK.symm)
    refine ⟨hg, ⟨kernel, ⟨hk, ?_⟩⟩⟩
    simpa using hlog
  · rintro ⟨hg, ⟨k', hk, hs'⟩⟩
    rcases withSwiss_preserves_rest s.kernel k'.swiss with
      ⟨hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hSC, hFac, hLif, hDC, hDel, hDgs, hSB, hDE, hDEA⟩
    obtain ⟨e, ⟨hf, hpos⟩⟩ := hg.2
    have hupd := dropSwissPost_eq_update s.kernel.swiss args.sw e hf hpos
    have hk' := swissDropK_eq_withSwiss hk
    have hupd' : dropSwissUpdate s.kernel.swiss args.sw = some k'.swiss :=
      (dropSwissUpdate_eq_k s.kernel args.sw k'.swiss).mpr hk'
    have hpost : dropSwissPost s.kernel.swiss args.sw e = k'.swiss :=
      Option.some.inj (hupd.symm.trans hupd')
    have hsw' : k'.swiss =
        match dropSwissUpdate s.kernel.swiss args.sw with
        | some ss => ss
        | none => s.kernel.swiss := by
      simp [dropSwissPostClause, hupd, hpost]
    have hker : s'.kernel = k' := congr_arg RecChainedState.kernel hs'
    have hlog : s'.log = dropReceipt args.actor args.exporter :: s.log := congr_arg RecChainedState.log hs'
    have hK' := swissDropK_only_swiss hk
    have hrest : (swissDropE LE cN hN hLE).restFrame s.kernel s'.kernel := by
      rw [hker, hK']
      exact restFrame_of_withSwiss rfl
    refine ⟨hg, ?_, hlog, hrest⟩
    rw [hker]
    exact hsw'

/-! ### §2c — THE VALIDATION. -/

theorem swissDropA_full_sound
    (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoSwiss S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DropArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (swissDropE LE cN hN hLE) (encodeE2 S (swissDropE LE cN hN hLE) s args s')) :
    DropSpec s args.sw args.actor args.exporter s' := by
  have hapex : (swissDropE LE cN hN hLE).apex s args s' :=
    effect2_circuit_full_sound S (swissDropE LE cN hN hLE)
      (dropRestFrameDecodes S LE cN hN hLE hRest) hLog (dropGuardDecodes LE cN hN hLE)
      s args s' h
  exact (apex_iff_dropSpec LE cN hN hLE s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def swissDropEWire : EffectSpec2 RecChainedState DropArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := dropGuardGates
  guardProp    := dropGuardProp
  guardWidth   := 1
  guardEncode  := dropGuardEncode
  guardLocal   := dropGuardLocal
  guardWidth_le := by decide

def swissDropAAirName : String := "dregg-swissDropA-v2"

def swissDropAEmitted : EmittedDescriptor := emittedEffect2 swissDropAAirName swissDropEWire

#guard swissDropAEmitted.name == swissDropAAirName

/-! ## §3 — axiom-hygiene tripwires. -/

#assert_axioms dropGuardLocal
#assert_axioms dropGuardDecodes
#assert_axioms dropGuardEncodes
#assert_axioms apex_iff_dropSpec
#assert_axioms swissDropA_full_sound

end Dregg2.Circuit.Inst.SwissDropA