/-
# Dregg2.Circuit.Inst.bridgeFinalizeA — the v2 (`EffectCommit2`) instance for `bridgeFinalizeA`.

`bridgeFinalizeA` is the single-component outbound-bridge finalize: it MARKS the unresolved bridge
`EscrowRecord` resolved in `escrows` (`markResolved`), prepends `escrowReceiptA actor ::` to the log,
and freezes the other 16 kernel fields (INCLUDING `bal` — the no-credit OUTFLOW; value already left
`bal` at lock). Touched component = `escrows` only (`listComponent`).

THE VALIDATION: `bridgeFinalizeA_full_sound ⇒ BridgeFinalizeSpec` THROUGH `effect2_circuit_full_sound`.

ADDITIVE: imports `EffectCommit2` + `Spec/bridgeoutboundfinalize`; edits neither.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.bridgeoutboundfinalize

namespace Dregg2.Circuit.Inst.BridgeFinalizeA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.BridgeOutboundFinalize
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (escrowReceiptA)

set_option linter.dupNamespace false

/-! ## §0 — propBit guard (wire 0, guardWidth = 1). -/

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `RestIffNoEscrows` portal (the v1 `RestHashIffFrame` minus `escrows`).

Clause ORDER is verbatim `BridgeFinalizeSpec`'s frame order (`accounts cell caps bal nullifiers revoked
commitments queues swiss slotCaveats factories lifecycle deathCert delegate delegations sealedBoxes`). -/

/-- **`RestIffNoEscrows RH`** — the rest hash binds the 16 non-`escrows` components (BIDIRECTIONAL),
omitting `escrows` (the touched field of `bridgeFinalizeA`). -/
def RestIffNoEscrows (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.bal = k.bal ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)

/-! ## §2 — the `bridgeFinalizeE` instance (touched component = `escrows`). -/

structure BridgeFinalizeArgs where
  id     : Nat
  actor  : CellId
  asset  : AssetId
  amount : ℤ

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

def bridgeFinalizeGuardProp (s : RecChainedState) (args : BridgeFinalizeArgs) : Prop :=
  match s.kernel.escrows.find? (matchesId args.id) with
  | none   => False
  | some r => finalizeGuard s args.id args.actor args.asset args.amount r

instance (s : RecChainedState) (args : BridgeFinalizeArgs) : Decidable (bridgeFinalizeGuardProp s args) := by
  unfold bridgeFinalizeGuardProp
  cases hf : s.kernel.escrows.find? (matchesId args.id) with
  | none => exact inferInstanceAs (Decidable False)
  | some r =>
    unfold finalizeGuard
    simp only [hf]
    exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def bridgeFinalizeGuardEncode (s : RecChainedState) (args : BridgeFinalizeArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (bridgeFinalizeGuardProp s args) else 0

def bridgeFinalizeGuardGates : ConstraintSystem := [cBitGuard]

theorem bridgeFinalizeGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied bridgeFinalizeGuardGates a ↔ satisfied bridgeFinalizeGuardGates b := by
  unfold satisfied bridgeFinalizeGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

def escrowsComponent (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState BridgeFinalizeArgs :=
  listComponent (·.escrows) LE cN hN hLE
    (fun s args => markResolved s.kernel.escrows args.id)

def bridgeFinalizeE (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    EffectSpec2 RecChainedState BridgeFinalizeArgs where
  view         := chainView
  active       := escrowsComponent LE cN hN hLE
  logUpdate    := some (fun s args => escrowReceiptA args.actor :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.bal = k.bal ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := bridgeFinalizeGuardGates
  guardProp    := bridgeFinalizeGuardProp
  guardWidth   := 1
  guardEncode  := bridgeFinalizeGuardEncode
  guardLocal   := bridgeFinalizeGuardLocal
  guardWidth_le := by decide

/-! ### §2a — per-effect obligations. -/

theorem bridgeFinalizeGuardDecodes (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardDecodes2 (bridgeFinalizeE LE cN hN hLE) := by
  intro s args s' hsat
  change satisfied bridgeFinalizeGuardGates (bridgeFinalizeGuardEncode s args s') at hsat
  show bridgeFinalizeGuardProp s args
  have hg := hsat cBitGuard (by simp [bridgeFinalizeGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, bridgeFinalizeGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem bridgeFinalizeGuardEncodes (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardEncodes2 (bridgeFinalizeE LE cN hN hLE) := by
  intro s args s' hg
  show satisfied bridgeFinalizeGuardGates (bridgeFinalizeGuardEncode s args s')
  intro c hc
  simp only [bridgeFinalizeGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, bridgeFinalizeGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem bridgeFinalizeRestFrameDecodes (S : Surface2) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoEscrows S.RH) :
    RestFrameDecodes2 S (bridgeFinalizeE LE cN hN hLE) := fun k k' h => (hRest k k').mp h

/-! ### §2b — apex ↔ `BridgeFinalizeSpec` (the found-record witness). -/

theorem bridgeFinalizeGuardProp_iff_guard (s : RecChainedState) (args : BridgeFinalizeArgs) :
    bridgeFinalizeGuardProp s args ↔
      ∃ r, finalizeGuard s args.id args.actor args.asset args.amount r := by
  unfold bridgeFinalizeGuardProp
  cases hf : s.kernel.escrows.find? (matchesId args.id) with
  | none =>
    simp only [hf]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨r, hg⟩; unfold finalizeGuard at hg; simp [hf] at hg
  | some r =>
    unfold finalizeGuard
    constructor
    · intro hg
      exact ⟨r, hg⟩
    · rintro ⟨r', ⟨hfind', hbr, hcreator, hasset, hamt⟩⟩
      have hr : r' = r := Option.some.inj (hfind'.symm.trans hf)
      subst hr
      exact ⟨hfind', hbr, hcreator, hasset, hamt⟩

theorem apex_iff_bridgeFinalizeSpec (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : BridgeFinalizeArgs) (s' : RecChainedState) :
    (bridgeFinalizeE LE cN hN hLE).apex s args s' ↔
      BridgeFinalizeSpec s args.id args.actor args.asset args.amount s' := by
  show (bridgeFinalizeGuardProp s args
        ∧ s'.kernel.escrows = markResolved s.kernel.escrows args.id
        ∧ s'.log = escrowReceiptA args.actor :: s.log
        ∧ ((bridgeFinalizeE LE cN hN hLE).restFrame s.kernel s'.kernel))
       ↔ BridgeFinalizeSpec s args.id args.actor args.asset args.amount s'
  unfold BridgeFinalizeSpec bridgeFinalizeE
  constructor
  · rintro ⟨hg, hesc, hlog, hAcc, hCell, hCaps, hBal, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    rcases (bridgeFinalizeGuardProp_iff_guard s args).mp hg with ⟨r, hfind, hbr, hcreator, hasset, hamt⟩
    exact ⟨r, ⟨hfind, hbr, hcreator, hasset, hamt⟩, hesc, hlog, hAcc, hCell, hCaps, hBal, hNul, hRev,
      hCom, hQ, hSw, hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩
  · rintro ⟨r, ⟨hfind, hbr, hcreator, hasset, hamt⟩, hesc, hlog, hAcc, hCell, hCaps, hBal, hNul, hRev,
      hCom, hQ, hSw, hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩
    have hg : bridgeFinalizeGuardProp s args :=
      (bridgeFinalizeGuardProp_iff_guard s args).mpr ⟨r, hfind, hbr, hcreator, hasset, hamt⟩
    exact ⟨hg, hesc, hlog, hAcc, hCell, hCaps, hBal, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §2c — THE VALIDATION: `bridgeFinalizeA_full_sound ⇒ BridgeFinalizeSpec`. -/

/-- **`bridgeFinalizeA_full_sound` — Gate 1 VALIDATION.** A satisfying v2 full-state witness for
`bridgeFinalizeE` proves the complete declarative `BridgeFinalizeSpec`. Portals: `RestIffNoEscrows RH`,
`logHashInjective LH`, `compressNInjective cN` + `listLeafInjective LE` (escrows list digest). -/
theorem bridgeFinalizeA_full_sound
    (S : Surface2) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BridgeFinalizeArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (bridgeFinalizeE LE cN hN hLE)
        (encodeE2 S (bridgeFinalizeE LE cN hN hLE) s args s')) :
    BridgeFinalizeSpec s args.id args.actor args.asset args.amount s' := by
  have hapex : (bridgeFinalizeE LE cN hN hLE).apex s args s' :=
    effect2_circuit_full_sound S (bridgeFinalizeE LE cN hN hLE)
      (bridgeFinalizeRestFrameDecodes S LE cN hN hLE hRest) hLog
      (bridgeFinalizeGuardDecodes LE cN hN hLE) s args s' h
  exact (apex_iff_bridgeFinalizeSpec LE cN hN hLE s args s').mp hapex



/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def bridgeFinalizeEWire : EffectSpec2 RecChainedState BridgeFinalizeArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := bridgeFinalizeGuardGates
  guardProp    := bridgeFinalizeGuardProp
  guardWidth   := 1
  guardEncode  := bridgeFinalizeGuardEncode
  guardLocal   := bridgeFinalizeGuardLocal
  guardWidth_le := by decide

def bridgeFinalizeAAirName : String := "dregg-bridgeFinalizeA-v2"

def bridgeFinalizeAEmitted : EmittedDescriptor := emittedEffect2 bridgeFinalizeAAirName bridgeFinalizeEWire

#guard bridgeFinalizeAEmitted.name == bridgeFinalizeAAirName

#assert_axioms bridgeFinalizeGuardLocal
#assert_axioms bridgeFinalizeGuardDecodes
#assert_axioms bridgeFinalizeGuardEncodes
#assert_axioms apex_iff_bridgeFinalizeSpec
#assert_axioms bridgeFinalizeA_full_sound

end Dregg2.Circuit.Inst.BridgeFinalizeA