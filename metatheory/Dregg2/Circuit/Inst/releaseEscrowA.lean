/-
# Dregg2.Circuit.Inst.releaseEscrowA — the v2-dual (`EffectCommit2Dual`) VALIDATION for `releaseEscrowA`.

`releaseEscrowA` is the canonical dual-component settle effect: it CREDITS the per-asset ledger `bal` at
`(recipient, asset)` by the parked `amount` AND MARKS the unresolved `EscrowRecord` resolved in `escrows`,
advances the log by `escrowReceiptA actor ::`, and freezes the other 15 kernel fields. This is Gate 1's
validator: `releaseEscrowA_full_sound ⇒ ReleaseEscrowSpec` THROUGH the generic dual-component framework.

ADDITIVE: imports `EffectCommit2Dual` + `Spec/escrowholdingrelease`; edits neither.
-/
import Dregg2.Circuit.EffectCommit2Dual
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.escrowholdingrelease

namespace Dregg2.Circuit.Inst.ReleaseEscrowA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.EscrowHoldingRelease
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (escrowReceiptA)

set_option linter.dupNamespace false

/-! ## §0 — propBit guard (wire 0, guardWidth = 1). -/

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `releaseEscrowE` dual instance (`bal` + `escrows`). -/

structure ReleaseArgs where
  id    : Nat
  actor : CellId

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

def releaseGuardProp (s : RecChainedState) (args : ReleaseArgs) : Prop :=
  match s.kernel.escrows.find? (matchesId args.id) with
  | none => False
  | some r => releaseGuard s args.id args.actor r

instance (s : RecChainedState) (args : ReleaseArgs) : Decidable (releaseGuardProp s args) := by
  unfold releaseGuardProp
  cases hf : s.kernel.escrows.find? (matchesId args.id) with
  | none => exact inferInstanceAs (Decidable False)
  | some r =>
    unfold releaseGuard
    rw [hf]
    exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def releaseGuardEncode (s : RecChainedState) (args : ReleaseArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (releaseGuardProp s args) else 0

def releaseGuardGates : ConstraintSystem := [cBitGuard]

theorem releaseGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied releaseGuardGates a ↔ satisfied releaseGuardGates b := by
  unfold satisfied releaseGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

def balExpected (s : RecChainedState) (args : ReleaseArgs) : CellId → AssetId → ℤ :=
  match s.kernel.escrows.find? (matchesId args.id) with
  | some r => recBalCreditCell s.kernel.bal r.recipient r.asset r.amount
  | none => s.kernel.bal

def balComponent (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState ReleaseArgs :=
  funcComponent (β := CellId → AssetId → ℤ) (·.bal) D hD balExpected

def escrowsComponent (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState ReleaseArgs :=
  listComponent (·.escrows) LE cN hN hLE
    (fun s args => markResolved s.kernel.escrows args.id)

def releaseEscrowE (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    EffectSpec2Dual RecChainedState ReleaseArgs where
  view         := chainView
  active1      := balComponent D hD
  active2      := escrowsComponent LE cN hN hLE
  logUpdate    := some (fun s args => escrowReceiptA args.actor :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss ∧ k'.slotCaveats = k.slotCaveats
      ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert
      ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := releaseGuardGates
  guardProp    := releaseGuardProp
  guardWidth   := 1
  guardEncode  := releaseGuardEncode
  guardLocal   := releaseGuardLocal
  guardWidth_le := by decide

/-! ### §2a — per-effect obligations. -/

theorem releaseEscrowGuardDecodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardDecodes2Dual (releaseEscrowE D hD LE cN hN hLE) := by
  intro s args s' hsat
  change satisfied releaseGuardGates (releaseGuardEncode s args s') at hsat
  show releaseGuardProp s args
  have hg := hsat cBitGuard (by simp [releaseGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, releaseGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem releaseEscrowGuardEncodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardEncodes2Dual (releaseEscrowE D hD LE cN hN hLE) := by
  intro s args s' hg
  show satisfied releaseGuardGates (releaseGuardEncode s args s')
  intro c hc
  simp only [releaseGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, releaseGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem releaseEscrowRestFrameDecodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoBalEscrows S.RH) :
    RestFrameDecodes2Dual S (releaseEscrowE D hD LE cN hN hLE) := fun k k' h => (hRest k k').mp h

/-! ### §2b — apex ↔ `ReleaseEscrowSpec` (the found-record witness). -/

theorem releaseGuardProp_iff_guard (s : RecChainedState) (args : ReleaseArgs) :
    releaseGuardProp s args ↔ ∃ r, releaseGuard s args.id args.actor r := by
  unfold releaseGuardProp
  cases hf : s.kernel.escrows.find? (matchesId args.id) with
  | none =>
    constructor
    · simp [hf]
    · rintro ⟨r, hfind, _, _⟩
      simp [hf, releaseGuard] at hfind
  | some r =>
    simp only [hf]
    constructor
    · intro hg
      exact ⟨r, hg⟩
    · rintro ⟨r', hg⟩
      rcases hg with ⟨hfind', hrec, hlive, hauth⟩
      have hr' : r' = r := Option.some.inj (hfind'.symm.trans hf)
      subst hr'
      exact ⟨hf, hrec, hlive, hauth⟩

theorem balExpected_eq_credit (s : RecChainedState) (args : ReleaseArgs) (r : EscrowRecord)
    (hfind : s.kernel.escrows.find? (matchesId args.id) = some r) :
    balExpected s args = recBalCreditCell s.kernel.bal r.recipient r.asset r.amount := by
  unfold balExpected
  rw [hfind]

theorem apex_iff_releaseEscrowSpec (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : ReleaseArgs) (s' : RecChainedState) :
    (releaseEscrowE D hD LE cN hN hLE).apex s args s' ↔
      ReleaseEscrowSpec s args.id args.actor s' := by
  show (releaseGuardProp s args
        ∧ s'.kernel.bal = balExpected s args
        ∧ s'.kernel.escrows = markResolved s.kernel.escrows args.id
        ∧ s'.log = escrowReceiptA args.actor :: s.log
        ∧ ((releaseEscrowE D hD LE cN hN hLE).restFrame s.kernel s'.kernel))
       ↔ ReleaseEscrowSpec s args.id args.actor s'
  unfold ReleaseEscrowSpec releaseEscrowE
  constructor
  · rintro ⟨hg, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    rcases (releaseGuardProp_iff_guard s args).mp hg with ⟨r, hfind, hrec, hlive, hauth⟩
    refine ⟨r, ⟨hfind, hrec, hlive, hauth⟩, ?_, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw,
      hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩
    rw [← balExpected_eq_credit s args r hfind]; exact hbal
  · rintro ⟨r, ⟨hfind, hrec, hlive, hauth⟩, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw,
      hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩
    have hg : releaseGuardProp s args :=
      (releaseGuardProp_iff_guard s args).mpr ⟨r, hfind, hrec, hlive, hauth⟩
    refine ⟨hg, ?_, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    rw [balExpected_eq_credit s args r hfind]; exact hbal

/-! ### §2c — THE VALIDATION: `releaseEscrowA_full_sound ⇒ ReleaseEscrowSpec`. -/

/-- **`releaseEscrowA_full_sound` — Gate 1 VALIDATION.** A satisfying dual-component full-state witness
for `releaseEscrowE` proves the complete declarative `ReleaseEscrowSpec`. Portals:
`RestIffNoBalEscrows RH`, `logHashInjective LH`, `Function.Injective D` (bal whole-function digest),
`compressNInjective cN` + `listLeafInjective LE` (escrows list digest). -/
theorem releaseEscrowA_full_sound
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ReleaseArgs) (s' : RecChainedState)
    (h : satisfiedE2Dual S (releaseEscrowE D hD LE cN hN hLE)
        (encodeE2Dual S (releaseEscrowE D hD LE cN hN hLE) s args s')) :
    ReleaseEscrowSpec s args.id args.actor s' := by
  have hapex : (releaseEscrowE D hD LE cN hN hLE).apex s args s' :=
    effect2dual_circuit_full_sound S (releaseEscrowE D hD LE cN hN hLE)
      (releaseEscrowRestFrameDecodes S D hD LE cN hN hLE hRest) hLog
      (releaseEscrowGuardDecodes D hD LE cN hN hLE) s args s' h
  exact (apex_iff_releaseEscrowSpec D hD LE cN hN hLE s args s').mp hapex



/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def releaseEscrowEWire : EffectSpec2Dual RecChainedState ReleaseArgs where
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
  guardGates   := releaseGuardGates
  guardProp    := releaseGuardProp
  guardWidth   := 1
  guardEncode  := releaseGuardEncode
  guardLocal   := releaseGuardLocal
  guardWidth_le := by decide

def releaseEscrowAAirName : String := "dregg-releaseEscrowA-v2"

def releaseEscrowAEmitted : EmittedDescriptor := emittedEffect2Dual releaseEscrowAAirName releaseEscrowEWire

#guard releaseEscrowAEmitted.name == releaseEscrowAAirName

#assert_axioms releaseGuardLocal
#assert_axioms releaseEscrowGuardDecodes
#assert_axioms releaseEscrowGuardEncodes
#assert_axioms apex_iff_releaseEscrowSpec
#assert_axioms releaseEscrowA_full_sound

end Dregg2.Circuit.Inst.ReleaseEscrowA