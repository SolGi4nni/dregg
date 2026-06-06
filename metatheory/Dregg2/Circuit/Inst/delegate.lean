/-
# Dregg2.Circuit.Inst.delegate — the v2 (`EffectCommit2`) instance for the AUTHORITY-UNATTENUATED
  DELEGATE effect `delegate` (the Granovetter unattenuated held-cap copy).

`delegate` is the single-`caps`-component constructor of the authority-unattenuated family (shared,
definitionally, with `introduceA`/`validateHandoffA`). A committed `delegate del rec t`:

  * **GUARD** `delegateGuard s del t` — the Granovetter connectivity premise: the delegator already
    holds a `t`-conferring cap (`(s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true`).
  * **TOUCHED `kernel.caps`** ← `recDelegateCaps s.kernel.caps del rec t` (= `grant s.kernel.caps rec
    (heldCapTo s.kernel.caps del t)`): the recipient's slot gains the delegator's held `t`-conferring
    cap, every other holder's slot whole. `caps : Caps = CellId → List Cap` is a FUNCTION-field, so
    this is a `funcComponent` (whole-function injective digest — the SAME shape as `burnA`'s `bal`),
    and the spec'd post-shape is FULL function equality (a tamper of any OTHER holder's slot is
    REJECTED, not just "the recipient grew").
  * **TOUCHED `log`** ← `authReceipt del :: s.log` (one authority-receipt row prepended).
  * **FRAME** the 16 non-`caps` kernel fields (`accounts cell escrows nullifiers revoked commitments
    bal queues swiss slotCaveats factories lifecycle deathCert delegate delegations sealedBoxes`)
    LITERALLY unchanged (`RestIffNoCaps`, ADDED here — the v1 `RestHashIffFrame` with `caps` omitted).

Through the v2 framework (`EffectCommit2`):
  * touched component = `kernel.caps` (a `funcComponent` over `Caps`, whole-function digest);
  * the log GROWS by the authority receipt (`authReceipt del`);
  * the frame is the 16 non-`caps` kernel fields (`RestIffNoCaps`).

`delegate_full_sound` CONCLUDES the bespoke `Spec.AuthorityUnattenuated.DelegateSpec` THROUGH the
framework: `effect2_circuit_full_sound` gives the derived `apex`, and `apex_iff_delegateSpec`
(a DIRECT identity match — the component clause is FULL `caps`-equality, EXACTLY `DelegateSpec`'s
`caps` clause, and the `restFrame` order is verbatim `DelegateSpec`'s 16-field frame order) rewrites
it to the bespoke spec. (`DelegateSpec`'s executor corner is `recCDelegate_iff_spec`.)

ADDITIVE: imports `EffectCommit2` + the bespoke spec `Dregg2.Circuit.Spec.authorityunattenuated`; edits
NEITHER `EffectCommit2`/`EffectInstances2`/`StateCommit` NOR any `Spec/*` file NOR `Dregg2.lean`.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.Spec.authorityunattenuated

namespace Dregg2.Circuit.Inst.Delegate

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Spec.AuthorityUnattenuated
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap)

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`mkBitGuard`), copied from the validated template.

The delegate spec exposes its guard as a `Prop` (`delegateGuard` = the `.any confersEdgeTo` Granovetter
connectivity premise), not a per-gate circuit, so we commit it as ONE `propBit` column at wire `0`
(guardWidth = 1) and decode via `propBit = 1 ↔ p`. (Identical to `burnE`/`noteCreateE`; the bit gate is
guard-agnostic.) -/

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
`delegate`). This is the 1-line mirror of `EffectCommit2.RestIffNoBal`, swapping the omitted field from
`bal` to `caps` (and so RE-including `bal`). The field order is VERBATIM `DelegateSpec`'s 16-field
frame order, so the apex↔spec bridge is a flat identity. Carried Prop hypothesis (realizable — a
Poseidon hash of a canonical serialization of the named fields), never an axiom. -/

/-- **`RestIffNoCaps RH`** — the rest hash binds the 16 non-`caps` components (BIDIRECTIONAL), omitting
`caps` (the touched field of `delegate`). -/
def RestIffNoCaps (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.escrows = k.escrows
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.bal = k.bal ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)

/-! ## §2 — the `delegate` instance (touched component = `caps`). -/

/-- The delegate effect arguments: delegator, recipient, target. (Field `recipient` rather than `rec`:
`rec` is a reserved structure recursor name in Lean 4.) -/
structure DelegateArgs where
  del       : CellId
  recipient : CellId
  target    : CellId

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The delegate guard as a `Prop` (the spec's `delegateGuard`). -/
def delegateGuardProp (s : RecChainedState) (args : DelegateArgs) : Prop :=
  delegateGuard s args.del args.target

instance (s : RecChainedState) (args : DelegateArgs) : Decidable (delegateGuardProp s args) := by
  unfold delegateGuardProp delegateGuard; exact inferInstanceAs (Decidable (_ = _))

/-- The delegate guard's witness generator: lay the single `propBit` column at wire `0`. -/
def delegateGuardEncode (s : RecChainedState) (args : DelegateArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (delegateGuardProp s args) else 0

/-- The delegate guard sub-system: the single `propBit` gate. -/
def delegateGuardGates : ConstraintSystem := [cBitGuard]

/-- **`delegateGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem delegateGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied delegateGuardGates a ↔ satisfied delegateGuardGates b := by
  unfold satisfied delegateGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The `caps` component digest: an injective whole-function hash `D : Caps → ℤ` (carried
`Function.Injective D` — a Poseidon Merkle over `caps`'s canonical serialization, the same CR bar as
`cellLeafInjective`). The spec-predicted value is `recDelegateCaps s.kernel.caps del rec t` (the grant);
the `funcComponent` `postClause` is FULL function equality `s'.kernel.caps = recDelegateCaps …`, so a
tamper of any OTHER holder's cap-slot is REJECTED, not just "the recipient grew". -/
def capsComponent (D : Caps → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState DelegateArgs :=
  funcComponent (β := Caps) (·.caps) D hD
    (fun s args => recDelegateCaps s.kernel.caps args.del args.recipient args.target)

/-- **`delegateE`** — the `EffectSpec2` for `delegate`, supplied to the v2 framework. -/
def delegateE (D : Caps → ℤ) (hD : Function.Injective D) :
    EffectSpec2 RecChainedState DelegateArgs where
  view         := chainView
  active       := capsComponent D hD
  logUpdate    := some (fun s args => authReceipt args.del :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.escrows = k.escrows
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.bal = k.bal ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := delegateGuardGates
  guardProp    := delegateGuardProp
  guardWidth   := 1
  guardEncode  := delegateGuardEncode
  guardLocal   := delegateGuardLocal
  guardWidth_le := by decide

/-! ### §2a — the per-effect obligations for `delegateE`. -/

/-- **`GuardDecodes2 (delegateE …)`** — the single bit gate decodes to `delegateGuard`. -/
theorem delegateGuardDecodes (D : Caps → ℤ) (hD : Function.Injective D) :
    GuardDecodes2 (delegateE D hD) := by
  intro s args s' hsat
  change satisfied delegateGuardGates (delegateGuardEncode s args s') at hsat
  show delegateGuardProp s args
  have hg := hsat cBitGuard (by simp [delegateGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, delegateGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (delegateE …)`** — `delegateGuard` encodes to the satisfied bit gate. -/
theorem delegateGuardEncodes (D : Caps → ℤ) (hD : Function.Injective D) :
    GuardEncodes2 (delegateE D hD) := by
  intro s args s' hg
  show satisfied delegateGuardGates (delegateGuardEncode s args s')
  intro c hc
  simp only [delegateGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, delegateGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `delegateE` rest-frame portal (the `→`): `RestIffNoCaps RH`'s soundness side. -/
theorem delegateRestFrameDecodes (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoCaps S.RH) :
    RestFrameDecodes2 S (delegateE D hD) := fun k k' h => (hRest k k').mp h

/-! ### §2b — the apex ↔ `DelegateSpec` bridge.

A DIRECT identity match (no And-reassoc): the component `postClause` is the FULL `caps`-equality
(`s'.kernel.caps = recDelegateCaps …`), which is EXACTLY `DelegateSpec`'s `caps` clause; the log is the
authority-receipt-prepended chain; and the `restFrame` field order is VERBATIM `DelegateSpec`'s 16-field
frame order (`accounts cell escrows nullifiers revoked commitments bal queues swiss slotCaveats
factories lifecycle deathCert delegate delegations sealedBoxes`). So both directions are a flat
re-packaging of the same 19 conjuncts. -/

/-- **`apex_iff_delegateSpec`** — the framework's derived `apex` for `delegateE` is EXACTLY
`DelegateSpec`. The guard is `delegateGuard`; the component `postClause` is FULL `caps`-equality; the
log is the receipt-prepended chain; the `restFrame` is the 16 non-`caps` frame clauses in
`DelegateSpec`'s order. -/
theorem apex_iff_delegateSpec (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState) :
    (delegateE D hD).apex s args s' ↔ DelegateSpec s args.del args.recipient args.target s' := by
  show (delegateGuardProp s args
        ∧ s'.kernel.caps = recDelegateCaps s.kernel.caps args.del args.recipient args.target
        ∧ s'.log = authReceipt args.del :: s.log
        ∧ ((delegateE D hD).restFrame s.kernel s'.kernel))
       ↔ DelegateSpec s args.del args.recipient args.target s'
  unfold DelegateSpec delegateGuardProp delegateE
  constructor
  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §2c — THE VALIDATION: `delegate_full_sound ⇒ DelegateSpec` through the framework. -/

/-- **`delegate_full_sound` — the VALIDATION (delegate through the v2 framework).** A satisfying v2
full-state witness for `delegateE` proves the complete declarative bespoke `DelegateSpec`. Portals:
`RestIffNoCaps RH` (the `caps`-omitting rest frame), `logHashInjective LH` (the growing log),
`Function.Injective D` (the `caps` component's whole-function digest — the realizable Poseidon-CR bar).
This CONCLUDES the bespoke `Spec.AuthorityUnattenuated.DelegateSpec` THROUGH the generic
`effect2_circuit_full_sound`, the circuit⟺spec corner of the authority-unattenuated triangle (whose
executor corner is `recCDelegate_iff_spec`). -/
theorem delegate_full_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (delegateE D hD) (encodeE2 S (delegateE D hD) s args s')) :
    DelegateSpec s args.del args.recipient args.target s' := by
  have hapex : (delegateE D hD).apex s args s' :=
    effect2_circuit_full_sound S (delegateE D hD)
      (delegateRestFrameDecodes S D hD hRest) hLog (delegateGuardDecodes D hD) s args s' h
  exact (apex_iff_delegateSpec D hD s args s').mp hapex

/-! ## §3 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms delegateGuardLocal
#assert_axioms delegateGuardDecodes
#assert_axioms delegateGuardEncodes
#assert_axioms apex_iff_delegateSpec
#assert_axioms delegate_full_sound

end Dregg2.Circuit.Inst.Delegate
