/-
# Dregg2.Circuit.Inst.mintA — the v2 (`EffectCommit2`) instance for the SUPPLY-CREATION effect `mintA`.

`mintA` is the single-component `supply-creation` constructor of `FullActionA`: a per-asset privileged
MINT that CREDITS the per-asset ledger `bal` at one `(cell, asset)` by `amt` (a `recBalCredit … amt`
credit of the POSITIVE amount), prepends a disclosing receipt to the log, and freezes the 16 non-`bal`
kernel fields. It is the exact dual of `burnA` (`Inst/burnA.lean`) — the SAME touched component (`bal`,
a `funcComponent` over the whole ledger function), the SAME growing log, the SAME `RestIffNoBal` frame
portal (reused from `EffectCommit2` — present already) — differing ONLY in (1) the spec-predicted ledger
value uses the POSITIVE amount (`recBalCredit … amt`, a CREDIT, not the burn's debit `… (-amt)`), (2) the
guard is the 3-conjunct `mintAdmit` (privileged-supply authority ∧ non-negativity ∧ cell-liveness)
rather than the burn's 4-conjunct `BurnGuard`, and (3) the receipt + bridge target are the mint's
(`mintReceipt`, `MintASpec`).

THE VALIDATION: `mintA_full_sound ⇒ MintASpec` THROUGH the framework. A satisfying v2 full-state witness
for `mintE` proves the complete declarative `MintASpec` (the apex truth in
`Dregg2/Circuit/Spec/supplycreation.lean`, whose executor corner is `execMintA_iff_spec`).

ADDITIVE: imports `EffectCommit2` + the supply-creation spec; edits NEITHER. Follows the
`burnA`/`noteCreateA` templates EXACTLY + the recipe in `Dregg2/Circuit/CONTRIBUTING.md`.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.Spec.supplycreation

namespace Dregg2.Circuit.Inst.MintA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Spec.SupplyCreation
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`mkBitGuard`, copied from the validated template).

The mint spec exposes its guard as a `Prop` (`mintAdmit`), not a per-gate circuit, so we commit it as
ONE `propBit` column at wire `0` (guardWidth = 1) and decode via `propBit = 1 ↔ p`. (Identical to
`burnA`/`noteCreateA`; the bit gate is guard-agnostic, so the 3-conjunct `mintAdmit` fits the same
shape as the burn's 4-conjunct `BurnGuard`.) -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `mintE` instance (touched component = `bal`).

`mintA` over `RecChainedState`: the touched component is the per-asset ledger `bal` (a `funcComponent`
whose digest is an injective whole-function hash — the realizable bar of `cellLeafInjective`); the log
GROWS by the mint receipt; the frame is the 16 non-`bal` kernel fields (`RestIffNoBal`, reused from
`EffectCommit2`). -/

/-- The mint effect arguments: actor, target cell, asset, amount (the SAME shape as `BurnArgs`). -/
structure MintArgs where
  actor : CellId
  cell  : CellId
  a     : AssetId
  amt   : ℤ

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The mint guard as a `Prop` (the spec's `mintAdmit`). -/
def mintGuardProp (s : RecChainedState) (args : MintArgs) : Prop :=
  mintAdmit s.kernel args.actor args.cell args.amt

instance (s : RecChainedState) (args : MintArgs) : Decidable (mintGuardProp s args) := by
  unfold mintGuardProp mintAdmit; exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The mint guard's witness generator: lay the single `propBit` column at wire `0`. -/
def mintGuardEncode (s : RecChainedState) (args : MintArgs) (_s' : RecChainedState) : Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (mintGuardProp s args) else 0

/-- The mint guard sub-system: the single `propBit` gate. -/
def mintGuardGates : ConstraintSystem := [cBitGuard]

/-- **`mintGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem mintGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied mintGuardGates a ↔ satisfied mintGuardGates b := by
  unfold satisfied mintGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The `bal` component digest: an injective whole-function hash (carried `Function.Injective D`). The
spec-predicted value is the CREDIT `recBalCredit … amt` (the SOLE difference from `burnE`, which
predicts the debit `… (-amt)`). -/
def balComponent (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState MintArgs :=
  funcComponent (β := CellId → AssetId → ℤ) (·.bal) D hD
    (fun s args => recBalCredit s.kernel.bal args.cell args.a args.amt)

/-- **`mintE`** — the `EffectSpec2` for `mintA`, supplied to the v2 framework. -/
def mintE (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    EffectSpec2 RecChainedState MintArgs where
  view         := chainView
  active       := balComponent D hD
  logUpdate    := some (fun s args => mintReceipt args.actor args.cell args.amt :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := mintGuardGates
  guardProp    := mintGuardProp
  guardWidth   := 1
  guardEncode  := mintGuardEncode
  guardLocal   := mintGuardLocal
  guardWidth_le := by decide

/-! ### §1a — the per-effect obligations for `mintE`. -/

/-- **`GuardDecodes2 (mintE …)`** — the single bit gate on the guard witness decodes to `mintAdmit`. -/
theorem mintGuardDecodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    GuardDecodes2 (mintE D hD) := by
  intro s args s' hsat
  change satisfied mintGuardGates (mintGuardEncode s args s') at hsat
  show mintGuardProp s args
  have hg := hsat cBitGuard (by simp [mintGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, mintGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (mintE …)`** — `mintAdmit` encodes to the satisfied bit gate. -/
theorem mintGuardEncodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    GuardEncodes2 (mintE D hD) := by
  intro s args s' hg
  show satisfied mintGuardGates (mintGuardEncode s args s')
  intro c hc
  simp only [mintGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, mintGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `mintE` rest-frame portal (the `→`): `RestIffNoBal RH`'s soundness side (the SAME `bal`-omitting
rest frame the burn uses, reused from `EffectCommit2`). -/
theorem mintRestFrameDecodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) :
    RestFrameDecodes2 S (mintE D hD) := fun k k' h => (hRest k k').mp h

/-! ### §1b — the apex ↔ `MintASpec` bridge. -/

/-- **`apex_iff_mintASpec`** — the framework's derived `apex` for `mintE` is EXACTLY `MintASpec`. The
guard is `mintAdmit`; the component `postClause` is the FULL `bal`-CREDIT equality (`recBalCredit …
amt`); the log is the mint-receipt-prepended chain; the `restFrame` is the 16 non-`bal` frame clauses
in `MintASpec`'s order (which is identical to `BurnSpec`'s). -/
theorem apex_iff_mintASpec (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState) :
    (mintE D hD).apex s args s' ↔ MintASpec s args.actor args.cell args.a args.amt s' := by
  -- unfold the apex's four conjuncts to the bare components.
  show (mintGuardProp s args
        ∧ s'.kernel.bal = recBalCredit s.kernel.bal args.cell args.a args.amt
        ∧ s'.log = mintReceipt args.actor args.cell args.amt :: s.log
        ∧ ((mintE D hD).restFrame s.kernel s'.kernel)) ↔ MintASpec s args.actor args.cell args.a args.amt s'
  unfold MintASpec mintGuardProp mintE
  constructor
  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §1c — THE VALIDATION: `mintA_full_sound ⇒ MintASpec` through the framework. -/

/-- **`mintA_full_sound` — the VALIDATION (mint through the v2 framework).** A satisfying v2 full-state
witness for `mintE` proves the complete declarative `MintASpec`. Portals: `RestIffNoBal RH` (the
`bal`-omitting rest frame, shared with burn), `logHashInjective LH` (the growing log),
`Function.Injective D` (the `bal` component's whole-function digest — the realizable Poseidon-CR bar).
CONCLUDES the bespoke `Spec.SupplyCreation.MintASpec` THROUGH the generic
`effect2_circuit_full_sound`. -/
theorem mintA_full_sound
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (mintE D hD) (encodeE2 S (mintE D hD) s args s')) :
    MintASpec s args.actor args.cell args.a args.amt s' := by
  have hapex : (mintE D hD).apex s args s' :=
    effect2_circuit_full_sound S (mintE D hD)
      (mintRestFrameDecodes S D hD hRest) hLog (mintGuardDecodes D hD) s args s' h
  exact (apex_iff_mintASpec D hD s args s').mp hapex

/-! ## §2 — EMISSION: production mint circuit on the Lean→Plonky3 wire.

`effectCircuit2` depends only on `guardGates` (not on the digest function `D`), so a wire-only
`mintEWire` yields the same bytes as any lawful `mintE D hD`. -/

/-- Wire-emission carrier: same guard sub-system as `mintE`, dummy `active` (not read by `effectCircuit2`). -/
def mintEWire : EffectSpec2 RecChainedState MintArgs where
  view         := chainView
  active       :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := mintGuardGates
  guardProp    := mintGuardProp
  guardWidth   := 1
  guardEncode  := mintGuardEncode
  guardLocal   := mintGuardLocal
  guardWidth_le := by decide

theorem mintEWire_circuit_eq (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    effectCircuit2 mintEWire = effectCircuit2 (mintE D hD) := rfl

def mintAirName : String := "dregg-mint-v2"

def mintEmitted : EmittedDescriptor := emittedEffect2 mintAirName mintEWire

/-- Canonical mint wire string — copy into Rust `lean_emitted_mint_roundtrip` golden. -/
def mintDescriptorJson : String := emitDescriptorJson mintEmitted

#eval mintDescriptorJson
#guard mintEmitted.constraints.length == 4
#guard mintEmitted.traceWidth == 72

/-! ## §3 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms mintGuardLocal
#assert_axioms mintGuardDecodes
#assert_axioms mintGuardEncodes
#assert_axioms apex_iff_mintASpec
#assert_axioms mintA_full_sound
#assert_axioms mintEWire_circuit_eq

end Dregg2.Circuit.Inst.MintA
