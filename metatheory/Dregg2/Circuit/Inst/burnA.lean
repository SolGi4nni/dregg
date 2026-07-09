/-
# Dregg2.Circuit.Inst.burnA — the v2 (`EffectCommit2`) instance for the SUPPLY-BURN effect `burnA`.

`burnA` is the single-component `supply-destruction` constructor of `FullActionA`: a per-asset supply
BURN that DEBITS the per-asset ledger `bal` at one `(cell, asset)` by `amt` (a `recBalCredit … (-amt)`
credit of the NEGATIVE amount), prepends a disclosing receipt to the log, and freezes the 16 non-`bal`
kernel fields. It is NEAR-IDENTICAL to the `mintE` worked template in `EffectInstances2.lean` — the
SAME touched component (`bal`, a `funcComponent` over the whole ledger function), the SAME growing log,
the SAME `RestIffNoBal` frame portal — differing ONLY in (1) the spec-predicted ledger value uses the
NEGATIVE amount (`recBalCredit … (-amt)`, a DEBIT, not the mint's credit `… amt`), (2) the guard is the
4-conjunct `BurnGuard` (privileged-supply authority ∧ non-negativity ∧ per-asset availability ∧
cell-liveness) rather than the mint's 3-conjunct `mintAdmit`, and (3) the receipt + bridge target are
the burn's (`burnReceipt`, `BurnSpec`).

THE VALIDATION: `burnA_full_sound ⇒ BurnSpec` THROUGH the framework. A satisfying v2 full-state witness
for `burnE` proves the complete declarative `BurnSpec` (the apex truth in
`Dregg2/Circuit/Spec/supplydestruction.lean`, whose executor corner is `recCBurnAsset_iff_spec`).

ADDITIVE: imports `EffectCommit2` + the supply-destruction spec; edits NONE of them. Follows the
`mintE` template (`EffectInstances2.lean`) EXACTLY + the recipe in `Dregg2/Circuit/CONTRIBUTING.md`.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.Spec.supplydestruction

namespace Dregg2.Circuit.Inst.BurnA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Spec.SupplyDestruction
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`mkBitGuard`, copied from the `mintE` template).

The burn spec exposes its guard as a `Prop` (`BurnGuard`), not a per-gate circuit, so we commit it as
ONE `propBit` column at wire `0` (guardWidth = 1) and decode via `propBit = 1 ↔ p`. (Identical to
`mintE`/`noteSpendE`; the bit gate is guard-agnostic, so `BurnGuard` fits the same shape as the
3-conjunct `mintAdmit`.) STAGE-3 NOTE: `BurnGuard`'s authority leg is now the disjunction
`(actor = cell ∨ mintAuthorizedB actor a)` — holder self-redeem is permissionless. The COLUMN shape
is unchanged (one `propBit`), but the BIT's MEANING changed, so the burn AIR is VK-affecting (the
prover may now satisfy the guard bit by exhibiting `actor = cell` without an issuer cap). -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `burnE` instance (touched component = `bal`).

`burnA` over `RecChainedState`: the touched component is the per-asset ledger `bal` (a `funcComponent`
whose digest is an injective whole-function hash — the realizable bar of `cellLeafInjective`); the log
GROWS by the burn receipt; the frame is the 16 non-`bal` kernel fields (`RestIffNoBal`). -/

/-- The burn effect arguments: actor, target cell, asset, amount (the SAME shape as `MintArgs`). -/
structure BurnArgs where
  actor : CellId
  cell  : CellId
  a     : AssetId
  amt   : ℤ

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The burn guard as a `Prop` (the spec's `BurnGuard`). -/
def burnGuardProp (s : RecChainedState) (args : BurnArgs) : Prop :=
  BurnGuard s.kernel args.actor args.cell args.a args.amt

instance (s : RecChainedState) (args : BurnArgs) : Decidable (burnGuardProp s args) := by
  unfold burnGuardProp BurnGuard; exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The burn guard's witness generator: lay the single `propBit` column at wire `0`. -/
def burnGuardEncode (s : RecChainedState) (args : BurnArgs) (_s' : RecChainedState) : Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (burnGuardProp s args) else 0

/-- The burn guard sub-system: the single `propBit` gate. -/
def burnGuardGates : ConstraintSystem := [cBitGuard]

/-- **`burnGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem burnGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied burnGuardGates a ↔ satisfied burnGuardGates b := by
  unfold satisfied burnGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The `bal` component digest: an injective whole-function hash (carried `Function.Injective D`).
W1: the spec-predicted value is the RETURN-TO-WELL write `recTransferBal … cell a a amt` — the
holder debited, the issuer's well credited, in ONE pinned ledger function. -/
def balComponent (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState BurnArgs :=
  funcComponent (β := CellId → AssetId → ℤ) (·.bal) D hD
    (fun s args => recTransferBal s.kernel.bal args.cell args.a args.a args.amt)

/-- **`burnE`** — the `EffectSpec2` for `burnA`, supplied to the v2 framework. -/
def burnE (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    EffectSpec2 RecChainedState BurnArgs where
  view         := chainView
  active       := balComponent D hD
  logUpdate    := some (fun s args => burnReceipt args.actor args.cell args.a args.amt :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt
      ∧ k'.heaps = k.heaps
      ∧ k'.nullifierRoot = k.nullifierRoot ∧ k'.revokedRoot = k.revokedRoot)
  guardGates   := burnGuardGates
  guardProp    := burnGuardProp
  guardWidth   := 1
  guardEncode  := burnGuardEncode
  guardLocal   := burnGuardLocal
  guardWidth_le := by decide

/-! ### §1a — the per-effect obligations for `burnE`. -/

/-- **`GuardDecodes2 (burnE …)`** — the single bit gate on the guard witness decodes to `BurnGuard`. -/
theorem burnGuardDecodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    GuardDecodes2 (burnE D hD) := by
  intro s args s' hsat
  change satisfied burnGuardGates (burnGuardEncode s args s') at hsat
  show burnGuardProp s args
  have hg := hsat cBitGuard (by simp [burnGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, burnGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (burnE …)`** — `BurnGuard` encodes to the satisfied bit gate. -/
theorem burnGuardEncodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    GuardEncodes2 (burnE D hD) := by
  intro s args s' hg
  show satisfied burnGuardGates (burnGuardEncode s args s')
  intro c hc
  simp only [burnGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, burnGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `burnE` rest-frame portal (the `→`): `RestIffNoBal RH`'s soundness side (the SAME `bal`-omitting
rest frame the mint uses). -/
theorem burnRestFrameDecodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) :
    RestFrameDecodes2 S (burnE D hD) := fun k k' h => (hRest k k').mp h

/-! ### §1b — the apex ↔ `BurnSpec` bridge. -/

/-- **`apex_iff_burnSpec`** — the framework's derived `apex` for `burnE` is EXACTLY `BurnSpec`. The
guard is `BurnGuard`; the component `postClause` is the FULL `bal`-DEBIT equality (`recBalCredit …
(-amt)`); the log is the burn-receipt-prepended chain; the `restFrame` is the 16 non-`bal` frame
clauses in `BurnSpec`'s order (which is identical to `MintASpec`'s). -/
theorem apex_iff_burnSpec (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState) :
    (burnE D hD).apex s args s' ↔ BurnSpec s args.actor args.cell args.a args.amt s' := by
  -- unfold the apex's four conjuncts to the bare components.
  show (burnGuardProp s args
        ∧ s'.kernel.bal = recTransferBal s.kernel.bal args.cell args.a args.a args.amt
        ∧ s'.log = burnReceipt args.actor args.cell args.a args.amt :: s.log
        ∧ ((burnE D hD).restFrame s.kernel s'.kernel)) ↔ BurnSpec s args.actor args.cell args.a args.amt s'
  unfold BurnSpec burnGuardProp burnE
  constructor
  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB, hNR, hRR⟩
    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB, hNR, hRR⟩
  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB, hNR, hRR⟩
    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB, hNR, hRR⟩

/-! ### §1c — THE VALIDATION: `burnA_full_sound ⇒ BurnSpec` through the framework. -/

/-- **`burnA_full_sound` — the VALIDATION (burn through the v2 framework).** A satisfying v2 full-state
witness for `burnE` proves the complete declarative `BurnSpec`. Portals: `RestIffNoBal RH` (the
`bal`-omitting rest frame, shared with mint), `logHashInjective LH` (the growing log),
`Function.Injective D` (the `bal` component's whole-function digest — the realizable Poseidon-CR bar).
CONCLUDES the bespoke `Spec.SupplyDestruction.BurnSpec` THROUGH the generic
`effect2_circuit_full_sound`. -/
theorem burnA_full_sound
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (burnE D hD) (encodeE2 S (burnE D hD) s args s')) :
    BurnSpec s args.actor args.cell args.a args.amt s' := by
  have hapex : (burnE D hD).apex s args s' :=
    effect2_circuit_full_sound S (burnE D hD)
      (burnRestFrameDecodes S D hD hRest) hLog (burnGuardDecodes D hD) s args s' h
  exact (apex_iff_burnSpec D hD s args s').mp hapex

/-! ## §2 — EMISSION: production burn circuit on the Lean→Plonky3 wire.

`effectCircuit2` depends only on `guardGates` (not on the digest function `D`), so a wire-only
`burnEWire` yields the same bytes as any lawful `burnE D hD`. -/

/-- Wire-emission carrier: same guard sub-system as `burnE`, dummy `active` (not read by `effectCircuit2`). -/
def burnEWire : EffectSpec2 RecChainedState BurnArgs where
  view         := chainView
  active       :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := burnGuardGates
  guardProp    := burnGuardProp
  guardWidth   := 1
  guardEncode  := burnGuardEncode
  guardLocal   := burnGuardLocal
  guardWidth_le := by decide

theorem burnEWire_circuit_eq (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    effectCircuit2 burnEWire = effectCircuit2 (burnE D hD) := rfl

def burnAirName : String := "dregg-burn-v2"

def burnEmitted : EmittedDescriptor := emittedEffect2 burnAirName burnEWire

/-- Canonical burn wire string — copy into Rust `lean_emitted_burn_roundtrip` golden. -/
def burnDescriptorJson : String := emitDescriptorJson burnEmitted

#guard burnEmitted.name == burnAirName
#guard burnEmitted.traceWidth == 72

/-! ## §3 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}`. -/

#assert_axioms burnGuardLocal
#assert_axioms burnGuardDecodes
#assert_axioms burnGuardEncodes
#assert_axioms apex_iff_burnSpec
#assert_axioms burnA_full_sound
#assert_axioms burnEWire_circuit_eq

end Dregg2.Circuit.Inst.BurnA
