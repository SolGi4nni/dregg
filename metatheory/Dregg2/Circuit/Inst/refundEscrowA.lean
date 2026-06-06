/-
# Dregg2.Circuit.Inst.refundEscrowA — the v2-dual (`EffectCommit2Dual`) VALIDATION for `refundEscrowA`.

`refundEscrowA` is the canonical dual-component settle effect: it CREDITS the per-asset ledger `bal` at
`(creator, asset)` by the parked `amount` AND MARKS the unresolved `EscrowRecord` resolved in `escrows`,
advances the log by `escrowReceiptA actor ::`, and freezes the other 15 kernel fields. This is Gate 1's
validator: `refundEscrowA_full_sound ⇒ RefundEscrowSpec` THROUGH the generic dual-component framework.

ADDITIVE: imports `EffectCommit2Dual` + `Spec/escrowholdingrefund`; edits neither.
-/
import Dregg2.Circuit.EffectCommit2Dual
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.escrowholdingrefund

namespace Dregg2.Circuit.Inst.RefundEscrowA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.EscrowHoldingRefund
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (escrowReceiptA)

set_option linter.dupNamespace false

/-! ## §0 — propBit guard (wire 0, guardWidth = 1). -/

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `refundEscrowE` dual instance (`bal` + `escrows`). -/

structure RefundEscrowArgs where
  id    : Nat
  actor : CellId

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

def refundEscrowGuardProp (s : RecChainedState) (args : RefundEscrowArgs) : Prop :=
  match s.kernel.escrows.find? (matchPred args.id) with
  | none => False
  | some r => admitRefund s.kernel args.id args.actor r

instance (s : RecChainedState) (args : RefundEscrowArgs) : Decidable (refundEscrowGuardProp s args) := by
  unfold refundEscrowGuardProp
  cases hf : s.kernel.escrows.find? (matchPred args.id) with
  | none => exact inferInstanceAs (Decidable False)
  | some r =>
    unfold admitRefund
    rw [hf]
    exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def refundEscrowGuardEncode (s : RecChainedState) (args : RefundEscrowArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (refundEscrowGuardProp s args) else 0

def refundEscrowGuardGates : ConstraintSystem := [cBitGuard]

theorem refundEscrowGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied refundEscrowGuardGates a ↔ satisfied refundEscrowGuardGates b := by
  unfold satisfied refundEscrowGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

def balExpected (s : RecChainedState) (args : RefundEscrowArgs) : CellId → AssetId → ℤ :=
  match s.kernel.escrows.find? (matchPred args.id) with
  | some r => recBalCreditCell s.kernel.bal r.creator r.asset r.amount
  | none => s.kernel.bal

def balComponent (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState RefundEscrowArgs :=
  funcComponent (β := CellId → AssetId → ℤ) (·.bal) D hD balExpected

def escrowsComponent (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState RefundEscrowArgs :=
  listComponent (·.escrows) LE cN hN hLE
    (fun s args => markResolved s.kernel.escrows args.id)

def refundEscrowE (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    EffectSpec2Dual RecChainedState RefundEscrowArgs where
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
  guardGates   := refundEscrowGuardGates
  guardProp    := refundEscrowGuardProp
  guardWidth   := 1
  guardEncode  := refundEscrowGuardEncode
  guardLocal   := refundEscrowGuardLocal
  guardWidth_le := by decide

/-! ### §2a — per-effect obligations. -/

theorem refundEscrowGuardDecodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardDecodes2Dual (refundEscrowE D hD LE cN hN hLE) := by
  intro s args s' hsat
  change satisfied refundEscrowGuardGates (refundEscrowGuardEncode s args s') at hsat
  show refundEscrowGuardProp s args
  have hg := hsat cBitGuard (by simp [refundEscrowGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, refundEscrowGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem refundEscrowGuardEncodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardEncodes2Dual (refundEscrowE D hD LE cN hN hLE) := by
  intro s args s' hg
  show satisfied refundEscrowGuardGates (refundEscrowGuardEncode s args s')
  intro c hc
  simp only [refundEscrowGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, refundEscrowGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem refundEscrowRestFrameDecodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoBalEscrows S.RH) :
    RestFrameDecodes2Dual S (refundEscrowE D hD LE cN hN hLE) := fun k k' h => (hRest k k').mp h

/-! ### §2b — apex ↔ `RefundEscrowSpec` (the found-record witness). -/

theorem refundEscrowGuardProp_iff_admitRefund (s : RecChainedState) (args : RefundEscrowArgs) :
    refundEscrowGuardProp s args ↔ ∃ r, admitRefund s.kernel args.id args.actor r := by
  unfold refundEscrowGuardProp
  cases hf : s.kernel.escrows.find? (matchPred args.id) with
  | none =>
    simp only [hf, admitRefund, exists_eq_right]
    constructor
    · intro h; exact absurd h id
    · rintro ⟨r, hfind, _⟩; simpa [hf] using hfind
  | some r =>
    simp only [hf]
    constructor
    · intro hg
      exact ⟨r, hg⟩
    · rintro ⟨r', hg⟩
      rcases hg with ⟨hfind', hmem, hlive, hauth⟩
      have hr' : r' = r := Option.some.inj (hfind'.symm.trans hf)
      subst hr'
      exact ⟨hfind', hmem, hlive, hauth⟩

theorem balExpected_eq_credit (s : RecChainedState) (args : RefundEscrowArgs) (r : EscrowRecord)
    (hfind : s.kernel.escrows.find? (matchPred args.id) = some r) :
    balExpected s args = recBalCreditCell s.kernel.bal r.creator r.asset r.amount := by
  unfold balExpected
  rw [hfind]

theorem apex_iff_refundEscrowSpec (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : RefundEscrowArgs) (s' : RecChainedState) :
    (refundEscrowE D hD LE cN hN hLE).apex s args s' ↔
      RefundEscrowSpec s args.id args.actor s' := by
  show (refundEscrowGuardProp s args
        ∧ s'.kernel.bal = balExpected s args
        ∧ s'.kernel.escrows = markResolved s.kernel.escrows args.id
        ∧ s'.log = escrowReceiptA args.actor :: s.log
        ∧ ((refundEscrowE D hD LE cN hN hLE).restFrame s.kernel s'.kernel))
       ↔ RefundEscrowSpec s args.id args.actor s'
  unfold RefundEscrowSpec refundEscrowE
  constructor
  · rintro ⟨hg, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    rcases (refundEscrowGuardProp_iff_admitRefund s args).mp hg with ⟨r, ⟨hfind, hmem, hlive, hauth⟩⟩
    refine ⟨r, ⟨hfind, hmem, hlive, hauth⟩, ?_, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw,
      hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩
    rw [← balExpected_eq_credit s args r hfind]; exact hbal
  · rintro ⟨r, ⟨hfind, hmem, hlive, hauth⟩, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw,
      hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩
    have hg : refundEscrowGuardProp s args :=
      (refundEscrowGuardProp_iff_admitRefund s args).mpr ⟨r, ⟨hfind, hmem, hlive, hauth⟩⟩
    refine ⟨hg, ?_, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    rw [balExpected_eq_credit s args r hfind]; exact hbal

/-! ### §2c — THE VALIDATION: `refundEscrowA_full_sound ⇒ RefundEscrowSpec`. -/

/-- **`refundEscrowA_full_sound` — Gate 1 VALIDATION.** A satisfying dual-component full-state witness
for `refundEscrowE` proves the complete declarative `RefundEscrowSpec`. Portals:
`RestIffNoBalEscrows RH`, `logHashInjective LH`, `Function.Injective D` (bal whole-function digest),
`compressNInjective cN` + `listLeafInjective LE` (escrows list digest). -/
theorem refundEscrowA_full_sound
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RefundEscrowArgs) (s' : RecChainedState)
    (h : satisfiedE2Dual S (refundEscrowE D hD LE cN hN hLE)
        (encodeE2Dual S (refundEscrowE D hD LE cN hN hLE) s args s')) :
    RefundEscrowSpec s args.id args.actor s' := by
  have hapex : (refundEscrowE D hD LE cN hN hLE).apex s args s' :=
    effect2dual_circuit_full_sound S (refundEscrowE D hD LE cN hN hLE)
      (refundEscrowRestFrameDecodes S D hD LE cN hN hLE hRest) hLog
      (refundEscrowGuardDecodes D hD LE cN hN hLE) s args s' h
  exact (apex_iff_refundEscrowSpec D hD LE cN hN hLE s args s').mp hapex



/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def refundEscrowEWire : EffectSpec2Dual RecChainedState RefundEscrowArgs where
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
  guardGates   := refundEscrowGuardGates
  guardProp    := refundEscrowGuardProp
  guardWidth   := 1
  guardEncode  := refundEscrowGuardEncode
  guardLocal   := refundEscrowGuardLocal
  guardWidth_le := by decide

def refundEscrowAAirName : String := "dregg-refundEscrowA-v2"

def refundEscrowAEmitted : EmittedDescriptor := emittedEffect2Dual refundEscrowAAirName refundEscrowEWire

#guard refundEscrowAEmitted.name == refundEscrowAAirName

#assert_axioms refundEscrowGuardLocal
#assert_axioms refundEscrowGuardDecodes
#assert_axioms refundEscrowGuardEncodes
#assert_axioms apex_iff_refundEscrowSpec
#assert_axioms refundEscrowA_full_sound

end Dregg2.Circuit.Inst.RefundEscrowA