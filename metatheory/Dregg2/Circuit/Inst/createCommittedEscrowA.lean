/-
# Dregg2.Circuit.Inst.createCommittedEscrowA — the v2-dual (`EffectCommit2Dual`) VALIDATION for
`createCommittedEscrowA`.

`createCommittedEscrowA` is the §8 hiding-portal-gated dual-component effect: it DEBITS `bal` at
`(creator, asset)` AND PREPENDS an unresolved `EscrowRecord` onto `escrows`, advances the log by
`escrowReceiptA actor ::`, and freezes the other 15 kernel fields. Guard: `hidingProof = true` AND
the per-asset lock `createGuard`.

ADDITIVE: imports `EffectCommit2Dual` + `Spec/escrowcommitted`; edits neither.
-/
import Dregg2.Circuit.EffectCommit2Dual
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.escrowcommitted

namespace Dregg2.Circuit.Inst.CreateCommittedEscrowA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.EscrowCommitted
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (escrowReceiptA)

set_option linter.dupNamespace false

/-! ## §0 — propBit guard (wire 0, guardWidth = 1). -/

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `createCommittedEscrowE` dual instance (`bal` + `escrows`). -/

structure CreateCommittedEscrowArgs where
  id           : Nat
  actor        : CellId
  creator      : CellId
  recipient    : CellId
  asset        : AssetId
  amount       : ℤ
  hidingProof  : Bool

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

def createCommittedEscrowGuardProp (s : RecChainedState) (args : CreateCommittedEscrowArgs) : Prop :=
  createGuard s.kernel args.id args.actor args.creator args.recipient args.asset args.amount
    args.hidingProof

instance (s : RecChainedState) (args : CreateCommittedEscrowArgs) :
    Decidable (createCommittedEscrowGuardProp s args) := by
  unfold createCommittedEscrowGuardProp createGuard
  exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def createCommittedEscrowGuardEncode (s : RecChainedState) (args : CreateCommittedEscrowArgs)
    (_s' : RecChainedState) : Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (createCommittedEscrowGuardProp s args) else 0

def createCommittedEscrowGuardGates : ConstraintSystem := [cBitGuard]

theorem createCommittedEscrowGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied createCommittedEscrowGuardGates a ↔ satisfied createCommittedEscrowGuardGates b := by
  unfold satisfied createCommittedEscrowGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

def balComponent (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState CreateCommittedEscrowArgs :=
  funcComponent (β := CellId → AssetId → ℤ) (·.bal) D hD
    (fun s args => recBalCreditCell s.kernel.bal args.creator args.asset (-args.amount))

def escrowsComponent (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState CreateCommittedEscrowArgs :=
  listComponent (·.escrows) LE cN hN hLE
    (fun s args => parkedRecord args.id args.creator args.recipient args.asset args.amount
      :: s.kernel.escrows)

def createCommittedEscrowE (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    EffectSpec2Dual RecChainedState CreateCommittedEscrowArgs where
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
  guardGates   := createCommittedEscrowGuardGates
  guardProp    := createCommittedEscrowGuardProp
  guardWidth   := 1
  guardEncode  := createCommittedEscrowGuardEncode
  guardLocal   := createCommittedEscrowGuardLocal
  guardWidth_le := by decide

/-! ### §2a — per-effect obligations. -/

theorem createCommittedEscrowGuardDecodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardDecodes2Dual (createCommittedEscrowE D hD LE cN hN hLE) := by
  intro s args s' hsat
  change satisfied createCommittedEscrowGuardGates (createCommittedEscrowGuardEncode s args s') at hsat
  show createCommittedEscrowGuardProp s args
  have hg := hsat cBitGuard (by simp [createCommittedEscrowGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, createCommittedEscrowGuardEncode,
    if_pos] at hg
  exact propBit_eq_one.mp hg

theorem createCommittedEscrowGuardEncodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardEncodes2Dual (createCommittedEscrowE D hD LE cN hN hLE) := by
  intro s args s' hg
  show satisfied createCommittedEscrowGuardGates (createCommittedEscrowGuardEncode s args s')
  intro c hc
  simp only [createCommittedEscrowGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, createCommittedEscrowGuardEncode,
    if_pos]
  exact propBit_eq_one.mpr hg

theorem createCommittedEscrowRestFrameDecodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) :
    RestFrameDecodes2Dual S (createCommittedEscrowE D hD LE cN hN hLE) :=
  fun k k' h => (hRest k k').mp h

/-! ### §2b — apex ↔ `CommittedEscrowCreateSpec` (direct identity). -/

theorem apex_iff_committedEscrowCreateSpec (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : CreateCommittedEscrowArgs) (s' : RecChainedState) :
    (createCommittedEscrowE D hD LE cN hN hLE).apex s args s' ↔
      CommittedEscrowCreateSpec s args.id args.actor args.creator args.recipient args.asset
        args.amount args.hidingProof s' := by
  show (createCommittedEscrowGuardProp s args
        ∧ s'.kernel.bal = recBalCreditCell s.kernel.bal args.creator args.asset (-args.amount)
        ∧ s'.kernel.escrows = parkedRecord args.id args.creator args.recipient args.asset args.amount
            :: s.kernel.escrows
        ∧ s'.log = escrowReceiptA args.actor :: s.log
        ∧ ((createCommittedEscrowE D hD LE cN hN hLE).restFrame s.kernel s'.kernel))
       ↔ CommittedEscrowCreateSpec s args.id args.actor args.creator args.recipient args.asset
            args.amount args.hidingProof s'
  unfold CommittedEscrowCreateSpec createCommittedEscrowGuardProp createCommittedEscrowE parkedRecord
  constructor
  · rintro ⟨hg, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §2c — THE VALIDATION: `createCommittedEscrowA_full_sound ⇒ CommittedEscrowCreateSpec`. -/

/-- **`createCommittedEscrowA_full_sound` — Gate 1 VALIDATION.** A satisfying dual-component full-state
witness for `createCommittedEscrowE` proves the complete declarative `CommittedEscrowCreateSpec`.
Portals: `RestIffNoBalEscrows RH`, `logHashInjective LH`, `Function.Injective D` (bal whole-function
digest), `compressNInjective cN` + `listLeafInjective LE` (escrows list digest). -/
theorem createCommittedEscrowA_full_sound
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateCommittedEscrowArgs) (s' : RecChainedState)
    (h : satisfiedE2Dual S (createCommittedEscrowE D hD LE cN hN hLE)
        (encodeE2Dual S (createCommittedEscrowE D hD LE cN hN hLE) s args s')) :
    CommittedEscrowCreateSpec s args.id args.actor args.creator args.recipient args.asset
      args.amount args.hidingProof s' := by
  have hapex : (createCommittedEscrowE D hD LE cN hN hLE).apex s args s' :=
    effect2dual_circuit_full_sound S (createCommittedEscrowE D hD LE cN hN hLE)
      (createCommittedEscrowRestFrameDecodes S D hD LE cN hN hLE hRest) hLog
      (createCommittedEscrowGuardDecodes D hD LE cN hN hLE) s args s' h
  exact (apex_iff_committedEscrowCreateSpec D hD LE cN hN hLE s args s').mp hapex



/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def createCommittedEscrowEWire : EffectSpec2Dual RecChainedState CreateCommittedEscrowArgs where
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
  guardGates   := createCommittedEscrowGuardGates
  guardProp    := createCommittedEscrowGuardProp
  guardWidth   := 1
  guardEncode  := createCommittedEscrowGuardEncode
  guardLocal   := createCommittedEscrowGuardLocal
  guardWidth_le := by decide

def createCommittedEscrowAAirName : String := "dregg-createCommittedEscrowA-v2"

def createCommittedEscrowAEmitted : EmittedDescriptor := emittedEffect2Dual createCommittedEscrowAAirName createCommittedEscrowEWire

#guard createCommittedEscrowAEmitted.name == createCommittedEscrowAAirName

#assert_axioms createCommittedEscrowGuardLocal
#assert_axioms createCommittedEscrowGuardDecodes
#assert_axioms createCommittedEscrowGuardEncodes
#assert_axioms apex_iff_committedEscrowCreateSpec
#assert_axioms createCommittedEscrowA_full_sound

end Dregg2.Circuit.Inst.CreateCommittedEscrowA