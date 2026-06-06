/-
# Dregg2.Circuit.Inst.unsealA — the v2 (`EffectCommit2`) instance for the SEAL-BOX UNSEAL effect
  `unsealA` (the cap-recovering arm of the `seal-box-operations` family).

`unsealA` is the single-component cap-RECOVERY constructor of `FullActionA`: against the box the
holding-store binds for `pid`, GRANT the recovered `box.payload` cap to `recipient` (the cap prepended
to `recipient`'s c-list slot, every other holder verbatim — the executor's `grant`, exhibited
declaratively as `grantedCaps`), prepend the `unsealReceipt` to the log, and FREEZE the 16 non-`caps`
kernel fields (INCLUDING `sealedBoxes` — the box is NOT consumed, a PROVEN frame-gap; the box may be
unsealed REPEATEDLY). Unlike the unconditional `revoke`, `unsealA` is GUARDED (fail-closed): the actor
must HOLD the unsealer cap for `pid` AND the box must EXIST in the store (`unsealAdmitGuard`).

The touched component is the per-holder cap table `caps : CellId → List Cap` (a FUNCTION-field), so —
exactly like `revoke`'s `caps` and `burnA`'s `bal` — this is a `funcComponent` whose digest is an
injective whole-function hash (the realizable Poseidon-CR bar `Function.Injective D`); the
spec-predicted value is the declarative `grantedCaps st.kernel.caps recipient box.payload`. The log
GROWS by `unsealReceipt actor recipient`. The frame is the 16 non-`caps` kernel fields (`RestIffNoCaps`,
ADDED here — the v1 `RestHashIffFrame` with `caps` omitted, the 1-line mirror of `RestIffNoBal`).

The guard is the REAL two-conjunct `unsealAdmitGuard` (held-unsealer-cap ∧ box-exists), modelled
exactly like `burnA`'s `BurnGuard` (a decidable conjunction committed as ONE `propBit` column at wire
`0`, decoded by `propBit p = 1 ↔ p`) — NOT the trivial `True` of `revoke`. Because the box's identity
feeds BOTH the guard (existential `findSealedBox … = some box`) and the post-`caps` (`box.payload`), the
`box` is carried as an effect ARGUMENT (the spec is parametrized by it); the framework's `Args` then
pins it on both faces, so the apex is EXACTLY `UnsealSpec st pid actor recipient box st'`.

THE VALIDATION: `unsealA_full_sound ⇒ UnsealSpec` THROUGH the framework. A satisfying v2 full-state
witness for `unsealE` proves the complete declarative `UnsealSpec` (the apex truth in
`Dregg2/Circuit/Spec/sealboxoperations.lean`, whose executor corner is `execFullA_unseal_iff_spec`
via `unsealChainA_iff_spec`).

The apex ↔ `UnsealSpec` bridge is a DIRECT identity match (no And-reassoc, no weakening): the guard is
`unsealAdmitGuard` (matching `UnsealSpec`'s leading guard conjunct verbatim — the spec is FULL function
equality on `caps`, so the apex full-equality IS the spec, not a weaker subset), the component
`postClause` is the FULL cap-table equality (`grantedCaps …`), the log is the `unsealReceipt`-prepended
chain, and the `restFrame` field order is VERBATIM `UnsealSpec`'s frame order.

ADDITIVE: imports `EffectCommit2` + the seal-box-operations spec; edits NEITHER. Follows the `revoke`
template (funcComponent `caps`-field + added `RestIffNoCaps` portal) + the `burnA` template (real
conjunctive guard) + the recipe in `Dregg2/Circuit/CONTRIBUTING.md`.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.sealboxoperations

namespace Dregg2.Circuit.Inst.UnsealA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.Spec.SealBoxOperations
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap)

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (copied from the `burnA` real-conjunctive-guard template).

`unsealA`'s guard is the REAL two-conjunct `unsealAdmitGuard` (held-unsealer-cap ∧ box-exists), a
decidable `Prop`. We commit it as ONE `propBit` column at wire `0` (guardWidth = 1) and decode via
`propBit = 1 ↔ p`. (Identical mechanism to `burnA`/`noteSpendE`; the bit gate is guard-agnostic, so the
2-conjunct `unsealAdmitGuard` fits the same shape as `burnA`'s 4-conjunct `BurnGuard`.) -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `RestIffNoCaps` portal (the v1 `RestHashIffFrame` minus `caps`).

The realizable injective-rest-hash portal for the effect that touches the `caps` function-field: the
rest hash binds the 16 non-`caps` components (BIDIRECTIONAL), OMITTING `caps` (the touched field of
`unsealA`). This is the 1-line mirror of `EffectCommit2.RestIffNoBal`, swapping the omitted field from
`bal` to `caps`. The 16 named fields are EXACTLY `UnsealSpec`'s frame (accounts cell escrows nullifiers
revoked commitments bal queues swiss slotCaveats factories lifecycle deathCert delegate delegations
sealedBoxes — INCLUDING `sealedBoxes`, the box NOT consumed). Carried Prop hypothesis (realizable — a
Poseidon hash of a canonical serialization of the named fields), never an axiom. -/

/-- **`RestIffNoCaps RH`** — the rest hash binds the 16 non-`caps` components (BIDIRECTIONAL), omitting
`caps` (the touched field of `unsealA`). -/
def RestIffNoCaps (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.escrows = k.escrows
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.bal = k.bal ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)

/-! ## §2 — the `unsealA` instance (touched component = `caps`).

`unsealA` over `RecChainedState`: the touched component is the per-holder cap table `caps` (a
`funcComponent` whose digest is an injective whole-function hash — the realizable bar of
`cellLeafInjective`); the log GROWS by `unsealReceipt actor recipient`; the frame is the 16 non-`caps`
kernel fields (`RestIffNoCaps`). The spec-predicted value is the declarative `grantedCaps`. -/

/-- The unseal effect arguments: the seal-pair id, the unsealing actor, the cap recipient, AND the box
the store binds (`box` feeds BOTH the guard's existential and the post-`caps` `box.payload`, so the spec
is parametrized by it — it is an effect argument). -/
structure UnsealArgs where
  pid       : Nat
  actor     : CellId
  recipient : CellId
  box       : SealedBoxRecord

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The unseal guard as a `Prop` (the spec's two-conjunct `unsealAdmitGuard`). -/
def unsealGuardProp (s : RecChainedState) (args : UnsealArgs) : Prop :=
  unsealAdmitGuard s args.pid args.actor args.box

instance (s : RecChainedState) (args : UnsealArgs) : Decidable (unsealGuardProp s args) := by
  unfold unsealGuardProp unsealAdmitGuard; exact inferInstanceAs (Decidable (_ ∧ _))

/-- The unseal guard's witness generator: lay the single `propBit` column at wire `0`. -/
def unsealGuardEncode (s : RecChainedState) (args : UnsealArgs) (_s' : RecChainedState) : Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (unsealGuardProp s args) else 0

/-- The unseal guard sub-system: the single `propBit` gate. -/
def unsealGuardGates : ConstraintSystem := [cBitGuard]

/-- **`unsealGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem unsealGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied unsealGuardGates a ↔ satisfied unsealGuardGates b := by
  unfold satisfied unsealGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The `caps` component digest: an injective whole-function hash (carried `Function.Injective D`). The
spec-predicted value is the declarative `grantedCaps s.kernel.caps recipient box.payload` — a `grant`
of the recovered cap to `recipient` over the WHOLE cap table (a drop/reorder/tamper of ANY holder's
cap-list is REJECTED, since `funcComponent`'s `postClause` is FULL function equality). -/
def capsComponent (D : Caps → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState UnsealArgs :=
  funcComponent (β := Caps) (·.caps) D hD
    (fun s args => grantedCaps s.kernel.caps args.recipient args.box.payload)

/-- **`unsealE`** — the `EffectSpec2` for `unsealA`, supplied to the v2 framework. -/
def unsealE (D : Caps → ℤ) (hD : Function.Injective D) :
    EffectSpec2 RecChainedState UnsealArgs where
  view         := chainView
  active       := capsComponent D hD
  logUpdate    := some (fun s args => unsealReceipt args.actor args.recipient :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.escrows = k.escrows
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.bal = k.bal ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := unsealGuardGates
  guardProp    := unsealGuardProp
  guardWidth   := 1
  guardEncode  := unsealGuardEncode
  guardLocal   := unsealGuardLocal
  guardWidth_le := by decide

/-! ### §2a — the per-effect obligations for `unsealE`. -/

/-- **`GuardDecodes2 (unsealE …)`** — the single bit gate decodes to `unsealAdmitGuard`. -/
theorem unsealGuardDecodes (D : Caps → ℤ) (hD : Function.Injective D) :
    GuardDecodes2 (unsealE D hD) := by
  intro s args s' hsat
  change satisfied unsealGuardGates (unsealGuardEncode s args s') at hsat
  show unsealGuardProp s args
  have hg := hsat cBitGuard (by simp [unsealGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, unsealGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (unsealE …)`** — `unsealAdmitGuard` encodes to the satisfied bit gate. -/
theorem unsealGuardEncodes (D : Caps → ℤ) (hD : Function.Injective D) :
    GuardEncodes2 (unsealE D hD) := by
  intro s args s' hg
  show satisfied unsealGuardGates (unsealGuardEncode s args s')
  intro c hc
  simp only [unsealGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, unsealGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `unsealE` rest-frame portal (the `→`): `RestIffNoCaps RH`'s soundness side (the `caps`-omitting
rest frame). -/
theorem unsealRestFrameDecodes (S : Surface2) (D : Caps → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoCaps S.RH) :
    RestFrameDecodes2 S (unsealE D hD) := fun k k' h => (hRest k k').mp h

/-! ### §2b — the apex ↔ `UnsealSpec` bridge.

A DIRECT identity match (no And-reassoc, no weakening): the guard is `unsealAdmitGuard` (matching
`UnsealSpec`'s leading guard conjunct verbatim), the component `postClause` is the FULL cap-table
equality (`grantedCaps …` — `UnsealSpec`'s `caps` clause is FULL function equality, so the apex's
full-function equality IS the spec, not a weaker subset), the log is the `unsealReceipt`-prepended
chain, and the `restFrame` field order is VERBATIM `UnsealSpec`'s frame order (accounts cell escrows
nullifiers revoked commitments bal queues swiss slotCaveats factories lifecycle deathCert delegate
delegations sealedBoxes). So both directions are a flat re-packaging of the same 19 conjuncts. -/

/-- **`apex_iff_unsealSpec`** — the framework's derived `apex` for `unsealE` is EXACTLY `UnsealSpec`. The
guard is `unsealAdmitGuard`; the component `postClause` is the FULL cap-table equality (`grantedCaps
s.kernel.caps recipient box.payload`); the log is the `unsealReceipt`-prepended chain; the `restFrame`
is the 16 non-`caps` frame clauses in `UnsealSpec`'s order. -/
theorem apex_iff_unsealSpec (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : UnsealArgs) (s' : RecChainedState) :
    (unsealE D hD).apex s args s' ↔ UnsealSpec s args.pid args.actor args.recipient args.box s' := by
  show (unsealGuardProp s args
        ∧ s'.kernel.caps = grantedCaps s.kernel.caps args.recipient args.box.payload
        ∧ s'.log = unsealReceipt args.actor args.recipient :: s.log
        ∧ ((unsealE D hD).restFrame s.kernel s'.kernel))
       ↔ UnsealSpec s args.pid args.actor args.recipient args.box s'
  unfold UnsealSpec unsealGuardProp unsealE
  constructor
  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §2c — THE VALIDATION: `unsealA_full_sound ⇒ UnsealSpec` through the framework. -/

/-- **`unsealA_full_sound` — the VALIDATION (seal-box unseal through the v2 framework).** A satisfying v2
full-state witness for `unsealE` proves the complete declarative `UnsealSpec`. Portals: `RestIffNoCaps
RH` (the `caps`-omitting rest frame, INCLUDING the `sealedBoxes`-frozen clause — the box is not
consumed), `logHashInjective LH` (the growing log), `Function.Injective D` (the `caps` component's
whole-function digest — the realizable Poseidon-CR bar). CONCLUDES the bespoke
`Spec.SealBoxOperations.UnsealSpec` THROUGH the generic `effect2_circuit_full_sound`, the circuit⟺spec
corner of the unseal triangle (the executor corner is `execFullA_unseal_iff_spec`). -/
theorem unsealA_full_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : UnsealArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (unsealE D hD) (encodeE2 S (unsealE D hD) s args s')) :
    UnsealSpec s args.pid args.actor args.recipient args.box s' := by
  have hapex : (unsealE D hD).apex s args s' :=
    effect2_circuit_full_sound S (unsealE D hD)
      (unsealRestFrameDecodes S D hD hRest) hLog (unsealGuardDecodes D hD) s args s' h
  exact (apex_iff_unsealSpec D hD s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def unsealEWire : EffectSpec2 RecChainedState UnsealArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := unsealGuardGates
  guardProp    := unsealGuardProp
  guardWidth   := 1
  guardEncode  := unsealGuardEncode
  guardLocal   := unsealGuardLocal
  guardWidth_le := by decide

def unsealAAirName : String := "dregg-unsealA-v2"

def unsealAEmitted : EmittedDescriptor := emittedEffect2 unsealAAirName unsealEWire

#guard unsealAEmitted.name == unsealAAirName

/-! ## §3 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms unsealGuardLocal
#assert_axioms unsealGuardDecodes
#assert_axioms unsealGuardEncodes
#assert_axioms apex_iff_unsealSpec
#assert_axioms unsealA_full_sound

end Dregg2.Circuit.Inst.UnsealA
