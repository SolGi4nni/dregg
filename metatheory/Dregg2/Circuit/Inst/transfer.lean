/-
# Dregg2.Circuit.Inst.transfer — the v2 (`EffectCommit2`) instance for the BALANCE-MOVEMENT effect.

`balanceA` is the single-component per-asset VALUE-MOVEMENT constructor of `FullActionA`: the unified
action executor dispatches `.balanceA t a` to `recCexecAsset s t a`, which (on its admissibility guard)
rewrites ONLY the per-asset ledger `bal : CellId → AssetId → ℤ` — debiting `(src,a)` and crediting
`(dst,a)` via `recTransferBal` — prepends the turn `t` to the receipt log, and freezes the 16 non-`bal`
kernel fields. It is the canonical "transfer" effect (`Dregg2/Circuit/StateCommit.lean` proved this
SAME movement bespoke; this is its THIN v2 instance through the generic framework).

Structurally it is NEAR-IDENTICAL to the `burnA` worked template (`Dregg2/Circuit/Inst/burnA.lean`) —
the SAME touched component (`bal`, a `funcComponent` over the whole-ledger function = the realizable
whole-function injective digest), the SAME growing log, the SAME `RestIffNoBal` frame portal (reused
from `EffectCommit2` — no new `RestIffNo*` needed) — differing ONLY in (1) the spec-predicted ledger
value is the debit/credit movement `recTransferBal bal src dst a amt` (not the burn's `recBalCredit …
(-amt)`), (2) the guard is the 6-conjunct `admitGuardA` (authority ∧ non-negativity ∧ per-asset
availability ∧ distinctness ∧ src-liveness ∧ dst-liveness) rather than the burn's 4-conjunct, and
(3) the log GROWS by the bare turn `t ::` (the value-movement receipt IS the turn) and the bridge target
is the bespoke `BalanceMovementSpec` (via `recCexecAsset_iff_spec`).

THE VALIDATION: `transfer_full_sound ⇒ BalanceMovementSpec` THROUGH the framework. A satisfying v2
full-state witness for `balanceE` proves the complete declarative `BalanceMovementSpec` (the apex truth
in `Dregg2/Circuit/Spec/balancemovement.lean`, whose executor corner is `recCexecAsset_iff_spec`).

The bridge `apex_iff_balanceMovementSpec` is a DIRECT identity match (no And-reassoc): the framework's
derived `apex` for `balanceE` lays its 19 conjuncts (guard ∧ post-`bal` ∧ log ∧ 16-field frame) in the
VERBATIM order of `BalanceMovementSpec`. The apex's component clause is the FULL whole-function equality
`bal = recTransferBal …`, which is EXACTLY `BalanceMovementSpec`'s `bal` clause (not a weaker subset),
so no "subset ⇐ full-equality" weakening is needed.

ADDITIVE: imports `EffectCommit2` + the balance-movement spec; edits NEITHER `EffectCommit2`/`StateCommit`
NOR any `Spec/*` file NOR `Dregg2.lean`. Follows the `burnA` template EXACTLY + the recipe in
`Dregg2/Circuit/CONTRIBUTING.md`.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.balancemovement

namespace Dregg2.Circuit.Inst.Transfer

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.Spec.BalanceMovement
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`mkBitGuard`, copied from the `burnA` template).

The balance-movement spec exposes its guard as a `Prop` (`admitGuardA` — the 6-conjunct admissibility
the per-asset executor `recKExecAsset` checks), not a per-gate circuit, so we commit it as ONE `propBit`
column at wire `0` (guardWidth = 1) and decode via `propBit = 1 ↔ p`. (Identical to `burnA`/`mintE`; the
bit gate is guard-agnostic, so the 6-conjunct `admitGuardA` fits the same shape.) -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `balanceA` instance (touched component = `bal`).

`balanceA` over `RecChainedState`: the touched component is the per-asset ledger `bal` (a `funcComponent`
whose digest is an injective whole-function hash — the realizable bar of `cellLeafInjective`); the log
GROWS by the turn `t`; the frame is the 16 non-`bal` kernel fields (`RestIffNoBal`, reused from the
framework — `balanceA` shares the burn/mint touched field). -/

/-- The balance-movement effect arguments: the moving turn `t` and the asset column `a`. (`Turn` carries
`actor`/`src`/`dst`/`amt`; `a : AssetId` selects the ledger column.) -/
structure BalanceArgs where
  t : Turn
  a : AssetId

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The balance-movement guard as a `Prop` (the spec's `admitGuardA`). -/
def balanceGuardProp (s : RecChainedState) (args : BalanceArgs) : Prop :=
  admitGuardA s.kernel args.t args.a

instance (s : RecChainedState) (args : BalanceArgs) : Decidable (balanceGuardProp s args) := by
  unfold balanceGuardProp admitGuardA
  exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The balance-movement guard's witness generator: lay the single `propBit` column at wire `0`. -/
def balanceGuardEncode (s : RecChainedState) (args : BalanceArgs) (_s' : RecChainedState) : Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (balanceGuardProp s args) else 0

/-- The balance-movement guard sub-system: the single `propBit` gate. -/
def balanceGuardGates : ConstraintSystem := [cBitGuard]

/-- **`balanceGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem balanceGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied balanceGuardGates a ↔ satisfied balanceGuardGates b := by
  unfold satisfied balanceGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The `bal` component digest: an injective whole-function hash (carried `Function.Injective D`). The
spec-predicted value is the debit/credit movement `recTransferBal bal src dst a amt` — the SOLE
difference from `burnA`, which predicts the supply debit `recBalCredit … (-amt)`. -/
def balComponent (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState BalanceArgs :=
  funcComponent (β := CellId → AssetId → ℤ) (·.bal) D hD
    (fun s args => recTransferBal s.kernel.bal args.t.src args.t.dst args.a args.t.amt)

/-- **`balanceE`** — the `EffectSpec2` for `balanceA`, supplied to the v2 framework. -/
def balanceE (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    EffectSpec2 RecChainedState BalanceArgs where
  view         := chainView
  active       := balComponent D hD
  logUpdate    := some (fun s args => args.t :: s.log)
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
  guardGates   := balanceGuardGates
  guardProp    := balanceGuardProp
  guardWidth   := 1
  guardEncode  := balanceGuardEncode
  guardLocal   := balanceGuardLocal
  guardWidth_le := by decide

/-! ### §1a — the per-effect obligations for `balanceE`. -/

/-- **`GuardDecodes2 (balanceE …)`** — the single bit gate on the guard witness decodes to
`admitGuardA`. -/
theorem balanceGuardDecodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    GuardDecodes2 (balanceE D hD) := by
  intro s args s' hsat
  change satisfied balanceGuardGates (balanceGuardEncode s args s') at hsat
  show balanceGuardProp s args
  have hg := hsat cBitGuard (by simp [balanceGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, balanceGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (balanceE …)`** — `admitGuardA` encodes to the satisfied bit gate. -/
theorem balanceGuardEncodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    GuardEncodes2 (balanceE D hD) := by
  intro s args s' hg
  show satisfied balanceGuardGates (balanceGuardEncode s args s')
  intro c hc
  simp only [balanceGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, balanceGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `balanceE` rest-frame portal (the `→`): `RestIffNoBal RH`'s soundness side (the SAME `bal`-omitting
rest frame the burn/mint use — reused from `EffectCommit2`). -/
theorem balanceRestFrameDecodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) :
    RestFrameDecodes2 S (balanceE D hD) := fun k k' h => (hRest k k').mp h

/-! ### §1b — the apex ↔ `BalanceMovementSpec` bridge.

A DIRECT identity match (no And-reassoc): the `restFrame` field order is VERBATIM `BalanceMovementSpec`'s
frame order (`accounts cell caps escrows nullifiers revoked commitments queues swiss slotCaveats factories
lifecycle deathCert delegate delegations sealedBoxes`), and the guard / component / log clauses line up
one-to-one. So both directions are a flat re-packaging of the same 19 conjuncts. The apex's component
clause is the FULL whole-function equality `bal = recTransferBal …`, which is EXACTLY (not weaker than)
`BalanceMovementSpec`'s `bal` clause — so no subset-weakening is needed. -/

/-- **`apex_iff_balanceMovementSpec`** — the framework's derived `apex` for `balanceE` is EXACTLY
`BalanceMovementSpec`. The guard is `admitGuardA`; the component `postClause` is the FULL ledger equality
(`bal = recTransferBal …`); the log is the turn-prepended chain (`t :: st.log`); the `restFrame` is the
16 non-`bal` frame clauses in `BalanceMovementSpec`'s order. -/
theorem apex_iff_balanceMovementSpec (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) :
    (balanceE D hD).apex s args s' ↔ BalanceMovementSpec s args.t args.a s' := by
  -- unfold the apex's four conjuncts to the bare components.
  show (balanceGuardProp s args
        ∧ s'.kernel.bal = recTransferBal s.kernel.bal args.t.src args.t.dst args.a args.t.amt
        ∧ s'.log = args.t :: s.log
        ∧ ((balanceE D hD).restFrame s.kernel s'.kernel))
       ↔ BalanceMovementSpec s args.t args.a s'
  unfold BalanceMovementSpec balanceGuardProp balanceE
  constructor
  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB, hNR, hRR⟩
    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB, hNR, hRR⟩
  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB, hNR, hRR⟩
    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB, hNR, hRR⟩

/-! ### §1c — THE VALIDATION: `transfer_full_sound ⇒ BalanceMovementSpec` through the framework. -/

/-- **`transfer_full_sound` — the VALIDATION (balance-movement through the v2 framework).** A satisfying
v2 full-state witness for `balanceE` proves the complete declarative `BalanceMovementSpec`. Portals:
`RestIffNoBal RH` (the `bal`-omitting rest frame, shared with burn/mint), `logHashInjective LH` (the
growing log), `Function.Injective D` (the `bal` component's whole-function digest — the realizable
Poseidon-CR bar). CONCLUDES the bespoke `Spec.BalanceMovement.BalanceMovementSpec` THROUGH the generic
`effect2_circuit_full_sound`, the circuit⟺spec corner of the balance-movement triangle. -/
theorem transfer_full_sound
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (balanceE D hD) (encodeE2 S (balanceE D hD) s args s')) :
    BalanceMovementSpec s args.t args.a s' := by
  have hapex : (balanceE D hD).apex s args s' :=
    effect2_circuit_full_sound S (balanceE D hD)
      (balanceRestFrameDecodes S D hD hRest) hLog (balanceGuardDecodes D hD) s args s' h
  exact (apex_iff_balanceMovementSpec D hD s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def balanceEWire : EffectSpec2 RecChainedState BalanceArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := balanceGuardGates
  guardProp    := balanceGuardProp
  guardWidth   := 1
  guardEncode  := balanceGuardEncode
  guardLocal   := balanceGuardLocal
  guardWidth_le := by decide

def transferAirName : String := "dregg-transfer-v2"

def transferEmitted : EmittedDescriptor := emittedEffect2 transferAirName balanceEWire

#guard transferEmitted.name == transferAirName

/-! ## §2 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}`. -/

#assert_axioms balanceGuardLocal
#assert_axioms balanceGuardDecodes
#assert_axioms balanceGuardEncodes
#assert_axioms apex_iff_balanceMovementSpec
#assert_axioms transfer_full_sound

end Dregg2.Circuit.Inst.Transfer
