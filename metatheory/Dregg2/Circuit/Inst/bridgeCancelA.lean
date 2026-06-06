/-
# Dregg2.Circuit.Inst.bridgeCancelA — the v2-dual (`EffectCommit2Dual`) VALIDATION for `bridgeCancelA`.

`bridgeCancelA` is the canonical dual-component bridge-outbound-cancel effect: it CREDITS the per-asset
ledger `bal` at `(r.creator, r.asset)` by the parked `amount` AND MARKS the unresolved bridge
`EscrowRecord` resolved in `escrows`, advances the log by `escrowReceiptA actor ::`, and freezes the
other 15 kernel fields. This is Gate 1's validator: `bridgeCancelA_full_sound ⇒ BridgeOutboundCancelSpec`
THROUGH the generic dual-component framework.

ADDITIVE: imports `EffectCommit2Dual` + `Spec/bridgeoutboundcancel`; edits neither.
-/
import Dregg2.Circuit.EffectCommit2Dual
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.bridgeoutboundcancel

namespace Dregg2.Circuit.Inst.BridgeCancelA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.BridgeOutboundCancel
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (escrowReceiptA)

set_option linter.dupNamespace false

/-! ## §0 — propBit guard (wire 0, guardWidth = 1). -/

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `bridgeCancelE` dual instance (`bal` + `escrows`). -/

/-- The `find?` predicate shared with `cancelGuard` (unresolved record of `id`). -/
def cancelFind? (k : RecordKernelState) (id : Nat) : Option EscrowRecord :=
  k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false))

structure BridgeCancelArgs where
  id    : Nat
  actor : CellId

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

def bridgeCancelGuardProp (s : RecChainedState) (args : BridgeCancelArgs) : Prop :=
  match cancelFind? s.kernel args.id with
  | none => False
  | some r => cancelGuard s.kernel args.id args.actor r

instance (s : RecChainedState) (args : BridgeCancelArgs) : Decidable (bridgeCancelGuardProp s args) := by
  unfold bridgeCancelGuardProp cancelFind?
  cases hf : s.kernel.escrows.find? (fun r => decide (r.id = args.id ∧ r.resolved = false)) with
  | none => simp [hf]; infer_instance
  | some r => simp [hf, cancelGuard]; infer_instance

def bridgeCancelGuardEncode (s : RecChainedState) (args : BridgeCancelArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (bridgeCancelGuardProp s args) else 0

def bridgeCancelGuardGates : ConstraintSystem := [cBitGuard]

theorem bridgeCancelGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied bridgeCancelGuardGates a ↔ satisfied bridgeCancelGuardGates b := by
  unfold satisfied bridgeCancelGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

def balExpected (s : RecChainedState) (args : BridgeCancelArgs) : CellId → AssetId → ℤ :=
  match cancelFind? s.kernel args.id with
  | some r => recBalCreditCell s.kernel.bal r.creator r.asset r.amount
  | none => s.kernel.bal

def balComponent (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState BridgeCancelArgs :=
  funcComponent (β := CellId → AssetId → ℤ) (·.bal) D hD balExpected

def escrowsComponent (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState BridgeCancelArgs :=
  listComponent (·.escrows) LE cN hN hLE
    (fun s args => markResolved s.kernel.escrows args.id)

def bridgeCancelE (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    EffectSpec2Dual RecChainedState BridgeCancelArgs where
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
  guardGates   := bridgeCancelGuardGates
  guardProp    := bridgeCancelGuardProp
  guardWidth   := 1
  guardEncode  := bridgeCancelGuardEncode
  guardLocal   := bridgeCancelGuardLocal
  guardWidth_le := by decide

/-! ### §2a — per-effect obligations. -/

theorem bridgeCancelGuardDecodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardDecodes2Dual (bridgeCancelE D hD LE cN hN hLE) := by
  intro s args s' hsat
  change satisfied bridgeCancelGuardGates (bridgeCancelGuardEncode s args s') at hsat
  show bridgeCancelGuardProp s args
  have hg := hsat cBitGuard (by simp [bridgeCancelGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, bridgeCancelGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem bridgeCancelGuardEncodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardEncodes2Dual (bridgeCancelE D hD LE cN hN hLE) := by
  intro s args s' hg
  show satisfied bridgeCancelGuardGates (bridgeCancelGuardEncode s args s')
  intro c hc
  simp only [bridgeCancelGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, bridgeCancelGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem bridgeCancelRestFrameDecodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoBalEscrows S.RH) :
    RestFrameDecodes2Dual S (bridgeCancelE D hD LE cN hN hLE) := fun k k' h => (hRest k k').mp h

/-! ### §2b — apex ↔ `BridgeOutboundCancelSpec` (the found-record witness). -/

theorem bridgeCancelGuardProp_iff_cancelGuard (s : RecChainedState) (args : BridgeCancelArgs) :
    bridgeCancelGuardProp s args ↔ ∃ r, cancelGuard s.kernel args.id args.actor r := by
  unfold bridgeCancelGuardProp cancelFind? cancelGuard
  cases hf : s.kernel.escrows.find? (fun r => decide (r.id = args.id ∧ r.resolved = false)) with
  | none =>
    constructor
    · intro h; exact absurd h id
    · rintro ⟨r, hfind, _⟩; simpa [hf] using hfind
  | some r =>
    constructor
    · intro hguard; exact ⟨r, hguard⟩
    · rintro ⟨r', hguard⟩
      obtain rfl : r' = r := Option.some.inj hguard.1.symm
      exact hguard

theorem balExpected_eq_credit (s : RecChainedState) (args : BridgeCancelArgs) (r : EscrowRecord)
    (hfind : cancelFind? s.kernel args.id = some r) :
    balExpected s args = recBalCreditCell s.kernel.bal r.creator r.asset r.amount := by
  unfold balExpected cancelFind? at *
  rw [hfind]

theorem apex_iff_bridgeOutboundCancelSpec (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : BridgeCancelArgs) (s' : RecChainedState) :
    (bridgeCancelE D hD LE cN hN hLE).apex s args s' ↔
      BridgeOutboundCancelSpec s args.id args.actor s' := by
  show (bridgeCancelGuardProp s args
        ∧ s'.kernel.bal = balExpected s args
        ∧ s'.kernel.escrows = markResolved s.kernel.escrows args.id
        ∧ s'.log = escrowReceiptA args.actor :: s.log
        ∧ ((bridgeCancelE D hD LE cN hN hLE).restFrame s.kernel s'.kernel))
       ↔ BridgeOutboundCancelSpec s args.id args.actor s'
  unfold BridgeOutboundCancelSpec bridgeCancelE
  constructor
  · rintro ⟨hg, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    rcases (bridgeCancelGuardProp_iff_cancelGuard s args).mp hg with ⟨r, hfind, hbridge, hcreator, hmem, hlive⟩
    refine ⟨r, ⟨hfind, hbridge, hcreator, hmem, hlive⟩, ?_, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom,
      hQ, hSw, hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩
    rw [← balExpected_eq_credit s args r hfind]; exact hbal
  · rintro ⟨r, ⟨hfind, hbridge, hcreator, hmem, hlive⟩, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom,
      hQ, hSw, hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩
    have hg : bridgeCancelGuardProp s args :=
      (bridgeCancelGuardProp_iff_cancelGuard s args).mpr
        ⟨r, ⟨hfind, hbridge, hcreator, hmem, hlive⟩⟩
    refine ⟨hg, ?_, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    rw [balExpected_eq_credit s args r hfind]; exact hbal

/-! ### §2c — THE VALIDATION: `bridgeCancelA_full_sound ⇒ BridgeOutboundCancelSpec`. -/

/-- **`bridgeCancelA_full_sound` — Gate 1 VALIDATION.** A satisfying dual-component full-state witness
for `bridgeCancelE` proves the complete declarative `BridgeOutboundCancelSpec`. Portals:
`RestIffNoBalEscrows RH`, `logHashInjective LH`, `Function.Injective D` (bal whole-function digest),
`compressNInjective cN` + `listLeafInjective LE` (escrows list digest). -/
theorem bridgeCancelA_full_sound
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BridgeCancelArgs) (s' : RecChainedState)
    (h : satisfiedE2Dual S (bridgeCancelE D hD LE cN hN hLE)
        (encodeE2Dual S (bridgeCancelE D hD LE cN hN hLE) s args s')) :
    BridgeOutboundCancelSpec s args.id args.actor s' := by
  have hapex : (bridgeCancelE D hD LE cN hN hLE).apex s args s' :=
    effect2dual_circuit_full_sound S (bridgeCancelE D hD LE cN hN hLE)
      (bridgeCancelRestFrameDecodes S D hD LE cN hN hLE hRest) hLog
      (bridgeCancelGuardDecodes D hD LE cN hN hLE) s args s' h
  exact (apex_iff_bridgeOutboundCancelSpec D hD LE cN hN hLE s args s').mp hapex



/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def bridgeCancelEWire : EffectSpec2Dual RecChainedState BridgeCancelArgs where
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
  guardGates   := bridgeCancelGuardGates
  guardProp    := bridgeCancelGuardProp
  guardWidth   := 1
  guardEncode  := bridgeCancelGuardEncode
  guardLocal   := bridgeCancelGuardLocal
  guardWidth_le := by decide

def bridgeCancelAAirName : String := "dregg-bridgeCancelA-v2"

def bridgeCancelAEmitted : EmittedDescriptor := emittedEffect2Dual bridgeCancelAAirName bridgeCancelEWire

#guard bridgeCancelAEmitted.name == bridgeCancelAAirName

#assert_axioms bridgeCancelGuardLocal
#assert_axioms bridgeCancelGuardDecodes
#assert_axioms bridgeCancelGuardEncodes
#assert_axioms apex_iff_bridgeOutboundCancelSpec
#assert_axioms bridgeCancelA_full_sound

end Dregg2.Circuit.Inst.BridgeCancelA