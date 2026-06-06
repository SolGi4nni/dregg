/-
# Dregg2.Circuit.Inst.createEscrowA — the v2-dual (`EffectCommit2Dual`) VALIDATION for `createEscrowA`.

`createEscrowA` is the canonical dual-component effect: it DEBITS the per-asset ledger `bal` at
`(creator, asset)` by `amount` AND PREPENDS an unresolved `EscrowRecord` onto `escrows`, advances the
log by `escrowReceiptA actor ::`, and freezes the other 15 kernel fields. This is Gate 1's validator:
`createEscrowA_full_sound ⇒ EscrowHoldingCreateSpec` THROUGH the generic dual-component framework.

ADDITIVE: imports `EffectCommit2Dual` + `Spec/escrowholdingcreate`; edits neither.
-/
import Dregg2.Circuit.EffectCommit2Dual
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.escrowholdingcreate

namespace Dregg2.Circuit.Inst.CreateEscrowA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.EscrowHoldingCreate
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (escrowReceiptA)

set_option linter.dupNamespace false

/-! ## §0 — propBit guard (wire 0, guardWidth = 1). -/

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `createEscrowE` dual instance (`bal` + `escrows`). -/

structure CreateEscrowArgs where
  id        : Nat
  actor     : CellId
  creator   : CellId
  recipient : CellId
  asset     : AssetId
  amount    : ℤ

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

def createEscrowGuardProp (s : RecChainedState) (args : CreateEscrowArgs) : Prop :=
  createGuard s.kernel args.id args.actor args.creator args.recipient args.asset args.amount

instance (s : RecChainedState) (args : CreateEscrowArgs) : Decidable (createEscrowGuardProp s args) := by
  unfold createEscrowGuardProp createGuard; exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def createEscrowGuardEncode (s : RecChainedState) (args : CreateEscrowArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (createEscrowGuardProp s args) else 0

def createEscrowGuardGates : ConstraintSystem := [cBitGuard]

theorem createEscrowGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied createEscrowGuardGates a ↔ satisfied createEscrowGuardGates b := by
  unfold satisfied createEscrowGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

def balComponent (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState CreateEscrowArgs :=
  funcComponent (β := CellId → AssetId → ℤ) (·.bal) D hD
    (fun s args => recBalCreditCell s.kernel.bal args.creator args.asset (-args.amount))

def escrowsComponent (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState CreateEscrowArgs :=
  listComponent (·.escrows) LE cN hN hLE
    (fun s args => parkedRecord args.id args.creator args.recipient args.asset args.amount
      :: s.kernel.escrows)

def createEscrowE (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    EffectSpec2Dual RecChainedState CreateEscrowArgs where
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
  guardGates   := createEscrowGuardGates
  guardProp    := createEscrowGuardProp
  guardWidth   := 1
  guardEncode  := createEscrowGuardEncode
  guardLocal   := createEscrowGuardLocal
  guardWidth_le := by decide

/-! ### §2a — per-effect obligations. -/

theorem createEscrowGuardDecodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardDecodes2Dual (createEscrowE D hD LE cN hN hLE) := by
  intro s args s' hsat
  change satisfied createEscrowGuardGates (createEscrowGuardEncode s args s') at hsat
  show createEscrowGuardProp s args
  have hg := hsat cBitGuard (by simp [createEscrowGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, createEscrowGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem createEscrowGuardEncodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardEncodes2Dual (createEscrowE D hD LE cN hN hLE) := by
  intro s args s' hg
  show satisfied createEscrowGuardGates (createEscrowGuardEncode s args s')
  intro c hc
  simp only [createEscrowGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, createEscrowGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem createEscrowRestFrameDecodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoBalEscrows S.RH) :
    RestFrameDecodes2Dual S (createEscrowE D hD LE cN hN hLE) := fun k k' h => (hRest k k').mp h

/-! ### §2b — apex ↔ `EscrowHoldingCreateSpec` (direct identity). -/

theorem apex_iff_escrowHoldingCreateSpec (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : CreateEscrowArgs) (s' : RecChainedState) :
    (createEscrowE D hD LE cN hN hLE).apex s args s' ↔
      EscrowHoldingCreateSpec s args.id args.actor args.creator args.recipient args.asset
        args.amount s' := by
  show (createEscrowGuardProp s args
        ∧ s'.kernel.bal = recBalCreditCell s.kernel.bal args.creator args.asset (-args.amount)
        ∧ s'.kernel.escrows = parkedRecord args.id args.creator args.recipient args.asset args.amount
            :: s.kernel.escrows
        ∧ s'.log = escrowReceiptA args.actor :: s.log
        ∧ ((createEscrowE D hD LE cN hN hLE).restFrame s.kernel s'.kernel))
       ↔ EscrowHoldingCreateSpec s args.id args.actor args.creator args.recipient args.asset
            args.amount s'
  unfold EscrowHoldingCreateSpec createEscrowGuardProp createEscrowE parkedRecord
  constructor
  · rintro ⟨hg, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §2c — THE VALIDATION: `createEscrowA_full_sound ⇒ EscrowHoldingCreateSpec`. -/

/-- **`createEscrowA_full_sound` — Gate 1 VALIDATION.** A satisfying dual-component full-state witness
for `createEscrowE` proves the complete declarative `EscrowHoldingCreateSpec`. Portals:
`RestIffNoBalEscrows RH`, `logHashInjective LH`, `Function.Injective D` (bal whole-function digest),
`compressNInjective cN` + `listLeafInjective LE` (escrows list digest). -/
theorem createEscrowA_full_sound
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateEscrowArgs) (s' : RecChainedState)
    (h : satisfiedE2Dual S (createEscrowE D hD LE cN hN hLE)
        (encodeE2Dual S (createEscrowE D hD LE cN hN hLE) s args s')) :
    EscrowHoldingCreateSpec s args.id args.actor args.creator args.recipient args.asset args.amount s' := by
  have hapex : (createEscrowE D hD LE cN hN hLE).apex s args s' :=
    effect2dual_circuit_full_sound S (createEscrowE D hD LE cN hN hLE)
      (createEscrowRestFrameDecodes S D hD LE cN hN hLE hRest) hLog
      (createEscrowGuardDecodes D hD LE cN hN hLE) s args s' h
  exact (apex_iff_escrowHoldingCreateSpec D hD LE cN hN hLE s args s').mp hapex



/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def createEscrowEWire : EffectSpec2Dual RecChainedState CreateEscrowArgs where
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
  guardGates   := createEscrowGuardGates
  guardProp    := createEscrowGuardProp
  guardWidth   := 1
  guardEncode  := createEscrowGuardEncode
  guardLocal   := createEscrowGuardLocal
  guardWidth_le := by decide

def createEscrowAAirName : String := "dregg-createEscrowA-v2"

def createEscrowAEmitted : EmittedDescriptor := emittedEffect2Dual createEscrowAAirName createEscrowEWire

#guard createEscrowAEmitted.name == createEscrowAAirName

#assert_axioms createEscrowGuardLocal
#assert_axioms createEscrowGuardDecodes
#assert_axioms createEscrowGuardEncodes
#assert_axioms apex_iff_escrowHoldingCreateSpec
#assert_axioms createEscrowA_full_sound

end Dregg2.Circuit.Inst.CreateEscrowA