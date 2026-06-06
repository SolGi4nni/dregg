/-
# Dregg2.Circuit.Inst.delegateAttenA — the v2 (`EffectCommit2`) instance for the gated rights-carrying
  Granovetter delegation `delegateAttenA`.

`delegateAttenA del rec t keep` is the single-component `caps`-mutating arm of `FullActionA`: the GATED
"only connectivity begets connectivity" delegation (`recCDelegateAtten`). On commit (GATED on `del`
already holding a cap conferring a connectivity edge to `t`) it rewrites the WHOLE capability table to
`grant caps rec (attenuate keep (heldCapTo caps del t))` — `rec`'s slot GAINS the delegator's held cap
ATTENUATED to `keep` (genuine non-amplification `confRights granted ≤ confRights held`), every other
holder's slot LITERALLY unchanged — prepends an authority receipt to the log, and FREEZES the 16
non-`caps` kernel fields. Fail-closed (no held edge ⇒ `none`).

The touched component is the CAPABILITY TABLE `caps : Caps = Label → List Cap`, a FUNCTION-field — so it
uses the `funcComponent` smart constructor (a whole-function injective digest, the realizable
Poseidon-CR bar), EXACTLY the `burnA`/`bal` template shape. Its `postClause` is the FULL function
equality `post.caps = grant caps rec (attenuate keep (heldCapTo caps del t))` — so a tamper with ANY
holder's slot (not just `rec`'s, and not just "grew by the granted cap") is REJECTED, not merely the
recipient's. This is precisely `DelegateAttenSpec`'s `caps` clause.

THE VALIDATION: `delegateAttenA_full_sound ⇒ DelegateAttenSpec` THROUGH the framework. A satisfying v2
full-state witness for `delegateAttenE` proves the complete declarative `DelegateAttenSpec` (the apex
truth in `Dregg2/Circuit/Spec/authorityattenuation.lean`, whose executor corner is
`delegateAtten_iff_spec`). The apex full-function equality IS the spec's `caps` clause (no
subset-weakening), and the `restFrame` field order is VERBATIM `DelegateAttenSpec`'s frame order — so
the bridge is a DIRECT identity match (like `noteCreateA`), no And-reassoc.

ADDITIVE: imports `EffectCommit2` + the authority-attenuation spec; edits NEITHER (nor any `Spec/*`
file nor `Dregg2.lean`). Adds the `RestIffNoCaps` portal locally (the 1-line `RestHashIffFrame` mirror
with `caps` omitted — no `caps`-omitting `RestIffNo*` existed in `EffectCommit2`). Follows the `burnA`
template (function-field) + the `noteCreateA` template (local `RestIffNo*`, direct identity bridge) +
the recipe in `Dregg2/Circuit/CONTRIBUTING.md`.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.authorityattenuation

namespace Dregg2.Circuit.Inst.DelegateAttenA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.Spec.AuthorityAttenuation
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth Label)

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`mkBitGuard`, copied from the `burnA` template).

The attenuation spec exposes its guard as a `Prop` (`DelegateAttenGuard` — the delegator holds a cap
conferring an edge to `t`, the Granovetter premise), not a per-gate circuit, so we commit it as ONE
`propBit` column at wire `0` (guardWidth = 1) and decode via `propBit = 1 ↔ p`. (Identical to
`burnA`/`mintE`/`noteSpendE`; the bit gate is guard-agnostic.) -/

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
`delegateAttenA`/`attenuateA`). This is the 1-line mirror of `EffectCommit2.RestIffNoBal`, swapping the
omitted field from `bal` to `caps`. Carried Prop hypothesis (realizable — a Poseidon hash of a
canonical serialization of the named fields), never an axiom. The conjunction order is VERBATIM
`DelegateAttenSpec`'s frame order (accounts cell escrows nullifiers revoked commitments bal queues
swiss slotCaveats factories lifecycle deathCert delegate delegations sealedBoxes) so the apex↔spec
bridge is a direct identity match. -/

/-- **`RestIffNoCaps RH`** — the rest hash binds the 16 non-`caps` components (BIDIRECTIONAL), omitting
`caps` (the touched field of `delegateAttenA`). -/
def RestIffNoCaps (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.escrows = k.escrows
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.bal = k.bal ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)

/-! ## §2 — the `delegateAttenA` instance (touched component = `caps`).

`delegateAttenA` over `RecChainedState`: the touched component is the capability table `caps` (a
`funcComponent` whose digest is an injective whole-function hash — the realizable bar of
`cellLeafInjective`); the log GROWS by the authority receipt; the frame is the 16 non-`caps` kernel
fields (`RestIffNoCaps`). -/

/-- The delegate-attenuation effect arguments: delegator, recipient, target cell, retained auths. -/
structure DelegateAttenArgs where
  del  : CellId
  recv : CellId
  t    : CellId
  keep : List Auth

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The delegate-attenuation guard as a `Prop` (the spec's `DelegateAttenGuard`). -/
def delAttenGuardProp (s : RecChainedState) (args : DelegateAttenArgs) : Prop :=
  DelegateAttenGuard s args.del args.t

instance (s : RecChainedState) (args : DelegateAttenArgs) : Decidable (delAttenGuardProp s args) := by
  unfold delAttenGuardProp DelegateAttenGuard; exact inferInstanceAs (Decidable (_ = true))

/-- The guard's witness generator: lay the single `propBit` column at wire `0`. -/
def delAttenGuardEncode (s : RecChainedState) (args : DelegateAttenArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (delAttenGuardProp s args) else 0

/-- The guard sub-system: the single `propBit` gate. -/
def delAttenGuardGates : ConstraintSystem := [cBitGuard]

/-- **`delAttenGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem delAttenGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied delAttenGuardGates a ↔ satisfied delAttenGuardGates b := by
  unfold satisfied delAttenGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The `caps` component digest: an injective whole-function hash (carried `Function.Injective D`). The
spec-predicted value is the attenuated grant `grant caps rec (attenuate keep (heldCapTo caps del t))`
(the WHOLE post-table, so a tamper with any holder's slot is REJECTED — FULL function equality). -/
def capsComponent (D : Caps → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState DelegateAttenArgs :=
  funcComponent (β := Caps) (·.caps) D hD
    (fun s args =>
      grant s.kernel.caps args.recv (attenuate args.keep (heldCapTo s.kernel.caps args.del args.t)))

/-- **`delegateAttenE`** — the `EffectSpec2` for `delegateAttenA`, supplied to the v2 framework. -/
def delegateAttenE (D : Caps → ℤ) (hD : Function.Injective D) :
    EffectSpec2 RecChainedState DelegateAttenArgs where
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
  guardGates   := delAttenGuardGates
  guardProp    := delAttenGuardProp
  guardWidth   := 1
  guardEncode  := delAttenGuardEncode
  guardLocal   := delAttenGuardLocal
  guardWidth_le := by decide

/-! ### §2a — the per-effect obligations for `delegateAttenE`. -/

/-- **`GuardDecodes2 (delegateAttenE …)`** — the single bit gate on the guard witness decodes to
`DelegateAttenGuard`. -/
theorem delAttenGuardDecodes (D : Caps → ℤ) (hD : Function.Injective D) :
    GuardDecodes2 (delegateAttenE D hD) := by
  intro s args s' hsat
  change satisfied delAttenGuardGates (delAttenGuardEncode s args s') at hsat
  show delAttenGuardProp s args
  have hg := hsat cBitGuard (by simp [delAttenGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, delAttenGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (delegateAttenE …)`** — `DelegateAttenGuard` encodes to the satisfied bit gate. -/
theorem delAttenGuardEncodes (D : Caps → ℤ) (hD : Function.Injective D) :
    GuardEncodes2 (delegateAttenE D hD) := by
  intro s args s' hg
  show satisfied delAttenGuardGates (delAttenGuardEncode s args s')
  intro c hc
  simp only [delAttenGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, delAttenGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `delegateAttenE` rest-frame portal (the `→`): `RestIffNoCaps RH`'s soundness side (the
`caps`-omitting rest frame). -/
theorem delAttenRestFrameDecodes (S : Surface2) (D : Caps → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoCaps S.RH) :
    RestFrameDecodes2 S (delegateAttenE D hD) := fun k k' h => (hRest k k').mp h

/-! ### §2b — the apex ↔ `DelegateAttenSpec` bridge.

A DIRECT identity match (no And-reassoc): the `restFrame` field order is VERBATIM `DelegateAttenSpec`'s
frame order (`accounts cell escrows nullifiers revoked commitments bal queues swiss slotCaveats
factories lifecycle deathCert delegate delegations sealedBoxes`), and the guard / component / log
clauses line up one-to-one. The component `postClause` is the FULL function equality `post.caps = grant
…`, which is EXACTLY `DelegateAttenSpec`'s `caps` clause (no subset weakening — the apex full-equality
IS the spec relation). So both directions are a flat re-packaging of the same 19 conjuncts. -/

/-- **`apex_iff_delegateAttenSpec`** — the framework's derived `apex` for `delegateAttenE` is EXACTLY
`DelegateAttenSpec`. The guard is `DelegateAttenGuard`; the component `postClause` is the FULL
capability-table equality (`grant … (attenuate keep (heldCapTo …))`); the log is the
authority-receipt-prepended chain; the `restFrame` is the 16 non-`caps` frame clauses in
`DelegateAttenSpec`'s order. -/
theorem apex_iff_delegateAttenSpec (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : DelegateAttenArgs) (s' : RecChainedState) :
    (delegateAttenE D hD).apex s args s'
      ↔ DelegateAttenSpec s args.del args.recv args.t args.keep s' := by
  show (delAttenGuardProp s args
        ∧ s'.kernel.caps
            = grant s.kernel.caps args.recv
                (attenuate args.keep (heldCapTo s.kernel.caps args.del args.t))
        ∧ s'.log = authReceipt args.del :: s.log
        ∧ ((delegateAttenE D hD).restFrame s.kernel s'.kernel))
       ↔ DelegateAttenSpec s args.del args.recv args.t args.keep s'
  unfold DelegateAttenSpec delAttenGuardProp delegateAttenE
  constructor
  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §2c — THE VALIDATION: `delegateAttenA_full_sound ⇒ DelegateAttenSpec` through the framework. -/

/-- **`delegateAttenA_full_sound` — the VALIDATION (delegate-attenuation through the v2 framework).** A
satisfying v2 full-state witness for `delegateAttenE` proves the complete declarative
`DelegateAttenSpec`. Portals: `RestIffNoCaps RH` (the `caps`-omitting rest frame), `logHashInjective LH`
(the growing log), `Function.Injective D` (the `caps` component's whole-function digest — the
realizable Poseidon-CR bar). CONCLUDES the bespoke `Spec.AuthorityAttenuation.DelegateAttenSpec`
THROUGH the generic `effect2_circuit_full_sound`, the circuit⟺spec corner of the attenuation
triangle. -/
theorem delegateAttenA_full_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DelegateAttenArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (delegateAttenE D hD) (encodeE2 S (delegateAttenE D hD) s args s')) :
    DelegateAttenSpec s args.del args.recv args.t args.keep s' := by
  have hapex : (delegateAttenE D hD).apex s args s' :=
    effect2_circuit_full_sound S (delegateAttenE D hD)
      (delAttenRestFrameDecodes S D hD hRest) hLog (delAttenGuardDecodes D hD) s args s' h
  exact (apex_iff_delegateAttenSpec D hD s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def delegateAttenEWire : EffectSpec2 RecChainedState DelegateAttenArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := delAttenGuardGates
  guardProp    := delAttenGuardProp
  guardWidth   := 1
  guardEncode  := delAttenGuardEncode
  guardLocal   := delAttenGuardLocal
  guardWidth_le := by decide

def delegateAttenAAirName : String := "dregg-delegateAttenA-v2"

def delegateAttenAEmitted : EmittedDescriptor := emittedEffect2 delegateAttenAAirName delegateAttenEWire

#guard delegateAttenAEmitted.name == delegateAttenAAirName

/-! ## §3 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms delAttenGuardLocal
#assert_axioms delAttenGuardDecodes
#assert_axioms delAttenGuardEncodes
#assert_axioms apex_iff_delegateAttenSpec
#assert_axioms delegateAttenA_full_sound

end Dregg2.Circuit.Inst.DelegateAttenA
