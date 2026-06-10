/-
# Dregg2.Circuit.Inst.validateHandoffA — the v2 (`EffectCommit2`) instance for the AUTHORITY
  validate-handoff effect `validateHandoffA`.

`validateHandoffA` is one of the THREE authority-unattenuated family constructors (`delegate` ·
`introduceA` · `validateHandoffA`) that the full executor `execFullA` dispatches DEFINITIONALLY to
the SAME chained authority primitive `recCDelegate` (see `Spec/authorityunattenuated.lean`:
`execFullA_validateHandoff_eq` is `rfl`). So its executable content is the Granovetter introduce
skeleton: the unattenuated held-cap copy that

  * GUARDS on the connectivity premise `delegateGuard s del t` (the delegator already holds a
    `t`-conferring cap — `(s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true`);
  * TOUCHES `kernel.caps` ← `recDelegateCaps s.kernel.caps del rec t`
    (= `grant s.kernel.caps rec (heldCapTo s.kernel.caps del t)`, the NON-amplifying held-copy);
  * GROWS `log` by exactly one authority receipt `authReceipt del`;
  * FRAMES the OTHER 16 `RecordKernelState` fields LITERALLY unchanged.

`caps` is the ONE touched kernel field, and it is a FUNCTION-field (`Caps := Label → List Cap`), so the
touched component is a `funcComponent` over the whole `caps` function — IDENTICAL in shape to `burnA`'s
`bal` `funcComponent` (a whole-function injective digest, the realizable `cellLeafInjective`-class bar),
differing only in (1) the predicted post-value (`recDelegateCaps …` not `recBalCredit …`), (2) the
guard (`delegateGuard` not `BurnGuard`), and (3) the receipt + bridge target (`authReceipt del`,
`DelegateSpec`).

THE VALIDATION: `validateHandoffA_full_sound ⇒ DelegateSpec` THROUGH the framework. A satisfying v2
full-state witness for `validateHandoffE` proves the complete declarative bespoke
`Spec.AuthorityUnattenuated.DelegateSpec` (the apex truth whose executor corner is
`recCDelegate_iff_spec` / `execFullA_validateHandoff_iff_spec`).

ADDITIVE: imports `EffectCommit2` + the authority-unattenuated spec; edits NEITHER. Adds a 1-line
`RestIffNoCaps` portal (the v1 `RestHashIffFrame` minus `caps` — no existing `RestIffNo*` omits `caps`).
Follows `burnA.lean`'s `funcComponent` template EXACTLY + the recipe in `Dregg2/Circuit/CONTRIBUTING.md`.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.authorityunattenuated

namespace Dregg2.Circuit.Inst.ValidateHandoffA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.Spec.AuthorityUnattenuated
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth)

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`mkBitGuard`, copied from the `burnE` template).

The authority spec exposes its guard as a `Prop` (`delegateGuard`), not a per-gate circuit, so we
commit it as ONE `propBit` column at wire `0` (guardWidth = 1) and decode via `propBit = 1 ↔ p`. The
bit gate is guard-agnostic, so the single-conjunct `delegateGuard` fits the same shape as `burnE`'s
4-conjunct `BurnGuard`. -/

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
`validateHandoffA`). This is the 1-line mirror of `EffectCommit2.RestIffNoBal`, swapping the omitted
field from `bal` to `caps` (and listing `bal` among the framed fields). Carried Prop hypothesis
(realizable — a Poseidon hash of a canonical serialization of the named fields), never an axiom. -/

/-- **`RestIffNoCaps RH`** — the rest hash binds the 16 non-`caps` components (BIDIRECTIONAL),
omitting `caps` (the touched field of `validateHandoffA`/`delegate`/`introduceA`). -/
def RestIffNoCaps (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)

/-! ## §2 — the `validateHandoffE` instance (touched component = `caps`).

`validateHandoffA` over `RecChainedState`: the touched component is the per-holder cap table `caps`
(a `funcComponent` whose digest is an injective whole-function hash — the realizable bar of
`cellLeafInjective`); the log GROWS by the authority receipt; the frame is the 16 non-`caps` kernel
fields (`RestIffNoCaps`). -/

/-- The validate-handoff effect arguments: the delegator (`intro`), the recipient (`recip`), the
target edge (`tgt`). (`rec`/`t` are avoided as field names: `rec` collides with the auto-generated
recursor `HandoffArgs.rec`, and a bare `t` mis-elaborates.) -/
structure HandoffArgs where
  intro : CellId
  recip : CellId
  tgt   : CellId

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The handoff guard as a `Prop` (the spec's `delegateGuard`: the Granovetter connectivity premise). -/
def handoffGuardProp (s : RecChainedState) (args : HandoffArgs) : Prop :=
  delegateGuard s args.intro args.tgt

instance (s : RecChainedState) (args : HandoffArgs) : Decidable (handoffGuardProp s args) := by
  unfold handoffGuardProp delegateGuard; exact inferInstanceAs (Decidable (_ = _))

/-- The handoff guard's witness generator: lay the single `propBit` column at wire `0`. -/
def handoffGuardEncode (s : RecChainedState) (args : HandoffArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (handoffGuardProp s args) else 0

/-- The handoff guard sub-system: the single `propBit` gate. -/
def handoffGuardGates : ConstraintSystem := [cBitGuard]

/-- **`handoffGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem handoffGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied handoffGuardGates a ↔ satisfied handoffGuardGates b := by
  unfold satisfied handoffGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The `caps` component digest: an injective whole-function hash (carried `Function.Injective D`). The
spec-predicted value is the grant `recDelegateCaps s.kernel.caps intro rec t` (the SOLE arithmetic
difference from `burnE`, which predicts `recBalCredit … (-amt)`). -/
def capsComponent (D : Caps → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState HandoffArgs :=
  funcComponent (β := Caps) (·.caps) D hD
    (fun s args => recDelegateCaps s.kernel.caps args.intro args.recip args.tgt)

/-- **`validateHandoffE`** — the `EffectSpec2` for `validateHandoffA`, supplied to the v2 framework. -/
def validateHandoffE (D : Caps → ℤ) (hD : Function.Injective D) :
    EffectSpec2 RecChainedState HandoffArgs where
  view         := chainView
  active       := capsComponent D hD
  logUpdate    := some (fun s args => authReceipt args.intro :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)
  guardGates   := handoffGuardGates
  guardProp    := handoffGuardProp
  guardWidth   := 1
  guardEncode  := handoffGuardEncode
  guardLocal   := handoffGuardLocal
  guardWidth_le := by decide

/-! ### §2a — the per-effect obligations for `validateHandoffE`. -/

/-- **`GuardDecodes2 (validateHandoffE …)`** — the single bit gate decodes to `delegateGuard`. -/
theorem handoffGuardDecodes (D : Caps → ℤ) (hD : Function.Injective D) :
    GuardDecodes2 (validateHandoffE D hD) := by
  intro s args s' hsat
  change satisfied handoffGuardGates (handoffGuardEncode s args s') at hsat
  show handoffGuardProp s args
  have hg := hsat cBitGuard (by simp [handoffGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, handoffGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (validateHandoffE …)`** — `delegateGuard` encodes to the satisfied bit gate. -/
theorem handoffGuardEncodes (D : Caps → ℤ) (hD : Function.Injective D) :
    GuardEncodes2 (validateHandoffE D hD) := by
  intro s args s' hg
  show satisfied handoffGuardGates (handoffGuardEncode s args s')
  intro c hc
  simp only [handoffGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, handoffGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `validateHandoffE` rest-frame portal (the `→`): `RestIffNoCaps RH`'s soundness side (the
`caps`-omitting rest frame). -/
theorem handoffRestFrameDecodes (S : Surface2) (D : Caps → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoCaps S.RH) :
    RestFrameDecodes2 S (validateHandoffE D hD) := fun k k' h => (hRest k k').mp h

/-! ### §2b — the apex ↔ `DelegateSpec` bridge.

A DIRECT identity match (no And-reassoc): the derived `apex`'s four conjuncts (guard ∧ component
`postClause` ∧ log ∧ `restFrame`) line up one-to-one against `DelegateSpec`'s structure (guard ∧ caps ∧
log ∧ the 16 frame fields), and our `restFrame` field order is VERBATIM `DelegateSpec`'s frame order
(`accounts cell escrows nullifiers revoked commitments bal queues swiss slotCaveats factories lifecycle
deathCert delegate delegations sealedBoxes`). So both directions are a flat re-packaging of the same 19
conjuncts. -/

/-- **`apex_iff_delegateSpec`** — the framework's derived `apex` for `validateHandoffE` is EXACTLY
`DelegateSpec`. The guard is `delegateGuard`; the component `postClause` is the FULL `caps`-function
equality (`recDelegateCaps …`); the log is the authority-receipt-prepended chain; the `restFrame` is the
16 non-`caps` frame clauses in `DelegateSpec`'s order. -/
theorem apex_iff_delegateSpec (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : HandoffArgs) (s' : RecChainedState) :
    (validateHandoffE D hD).apex s args s' ↔ DelegateSpec s args.intro args.recip args.tgt s' := by
  -- unfold the apex's four conjuncts to the bare components.
  show (handoffGuardProp s args
        ∧ s'.kernel.caps = recDelegateCaps s.kernel.caps args.intro args.recip args.tgt
        ∧ s'.log = authReceipt args.intro :: s.log
        ∧ ((validateHandoffE D hD).restFrame s.kernel s'.kernel))
       ↔ DelegateSpec s args.intro args.recip args.tgt s'
  unfold DelegateSpec handoffGuardProp validateHandoffE
  constructor
  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §2c — THE VALIDATION: `validateHandoffA_full_sound ⇒ DelegateSpec` through the framework. -/

/-- **`validateHandoffA_full_sound` — the VALIDATION (validate-handoff through the v2 framework).** A
satisfying v2 full-state witness for `validateHandoffE` proves the complete declarative bespoke
`DelegateSpec`. Portals: `RestIffNoCaps RH` (the `caps`-omitting rest frame), `logHashInjective LH` (the
growing log), `Function.Injective D` (the `caps` component's whole-function digest — the realizable
Poseidon-CR bar). CONCLUDES the bespoke `Spec.AuthorityUnattenuated.DelegateSpec` THROUGH the generic
`effect2_circuit_full_sound` — the circuit⟺spec corner of the authority-unattenuated triangle (whose
executor corner is `execFullA_validateHandoff_iff_spec`, via `execFullA_validateHandoff_eq`). -/
theorem validateHandoffA_full_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : HandoffArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (validateHandoffE D hD) (encodeE2 S (validateHandoffE D hD) s args s')) :
    DelegateSpec s args.intro args.recip args.tgt s' := by
  have hapex : (validateHandoffE D hD).apex s args s' :=
    effect2_circuit_full_sound S (validateHandoffE D hD)
      (handoffRestFrameDecodes S D hD hRest) hLog (handoffGuardDecodes D hD) s args s' h
  exact (apex_iff_delegateSpec D hD s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def validateHandoffEWire : EffectSpec2 RecChainedState HandoffArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := handoffGuardGates
  guardProp    := handoffGuardProp
  guardWidth   := 1
  guardEncode  := handoffGuardEncode
  guardLocal   := handoffGuardLocal
  guardWidth_le := by decide

def validateHandoffAAirName : String := "dregg-validateHandoffA-v2"

def validateHandoffAEmitted : EmittedDescriptor := emittedEffect2 validateHandoffAAirName validateHandoffEWire

#guard validateHandoffAEmitted.name == validateHandoffAAirName

/-! ## §3 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms handoffGuardLocal
#assert_axioms handoffGuardDecodes
#assert_axioms handoffGuardEncodes
#assert_axioms apex_iff_delegateSpec
#assert_axioms validateHandoffA_full_sound

end Dregg2.Circuit.Inst.ValidateHandoffA
