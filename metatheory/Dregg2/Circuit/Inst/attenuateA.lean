/-
# Dregg2.Circuit.Inst.attenuateA — the v2 (`EffectCommit2`) instance for the AUTHORITY-ATTENUATION
  effect `attenuateA` (the TOTAL in-place self-narrowing of a held cap).

`attenuateA actor idx keep` is the single-component `authority-attenuation` arm of `execFullA`: it
rewrites ONLY the `caps` slot of `actor` — replacing the `idx`-th held cap with its `keep`-attenuation
(`attenuateSlotF caps actor idx keep`, narrower-or-equal rights, `apply.rs:4377`) — prepends an
authority receipt to the log, and freezes the 16 non-`caps` kernel fields. It is the `caps`-touching
analog of `burnA` (which touches `bal`): the SAME `funcComponent` shape (a whole-function injective
digest over the cap table `Caps = Label → List Cap`), the SAME growing log. It differs from `burnA` in
(1) the touched function-field is `caps` (post-value `attenuateSlotF …`, not `bal`'s `recBalCredit …`),
(2) the frame omits `caps` (`RestIffNoCaps`, ADDED here — the v1 `RestHashIffFrame` minus `caps`), and
(3) the guard is UNCONDITIONAL — `attenuateA` ALWAYS commits (attenuation cannot fail: `List.modify` is
a no-op out of bounds and `attenuate` only narrows), so the guard `Prop` is the trivial `True` (the
`noteCreateA` shape), and the bespoke `AttenuateSpec` has NO guard clause.

THE VALIDATION: `attenuateA_full_sound ⇒ AttenuateSpec` THROUGH the framework. A satisfying v2
full-state witness for `attenuateE` proves the complete declarative `AttenuateSpec` (the apex truth in
`Dregg2/Circuit/Spec/authorityattenuation.lean`, whose executor corner is `attenuate_iff_spec`).

Because the spec has NO guard conjunct (the arm is total), the apex's leading `True` guard clause is
DROPPED in the bridge (`apex_iff_attenuateSpec` strips it) — the apex full-`caps`-function equality
(`funcComponent`'s `postClause`) is EXACTLY the spec's `caps` clause, so the apex IMPLIES (and equals)
the bespoke spec.

ADDITIVE: imports `EffectCommit2` + the authority-attenuation spec; edits NEITHER them NOR any other
file. Follows the `burnA` template (function-field `funcComponent`) + the `noteCreateA` template
(trivial `True` guard + a fresh `RestIffNo*` portal) + the recipe in `Dregg2/Circuit/CONTRIBUTING.md`.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.authorityattenuation

namespace Dregg2.Circuit.Inst.AttenuateA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.Spec.AuthorityAttenuation
open Dregg2.Authority (Caps Cap Auth Label)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`mkBitGuard`, copied from the validated template).

`attenuateA`'s guard is the TRIVIAL `True` — the in-place self-narrowing is UNCONDITIONAL (it always
commits; at worst the identity, still narrower-or-equal). We still commit it as ONE `propBit` column at
wire `0` (guardWidth = 1) so the instance shape matches the framework's guard sub-system uniformly;
`propBit True = 1` always, so the single gate `propBit (guardProp) = 1` is always satisfiable — the
circuit-level reflection of "always commits". (Identical to `noteCreateA`'s trivial guard.) -/

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
`attenuateA`). This is the 1-line mirror of `EffectCommit2.RestIffNoBal`, swapping the omitted field
from `bal` to `caps`. The frame clause order is VERBATIM `AttenuateSpec`'s frame order (`accounts cell
escrows nullifiers revoked commitments bal queues swiss slotCaveats factories lifecycle deathCert
delegate delegations sealedBoxes`). Carried Prop hypothesis (realizable — a Poseidon hash of a
canonical serialization of the named fields), never an axiom. -/

/-- **`RestIffNoCaps RH`** — the rest hash binds the 16 non-`caps` components (BIDIRECTIONAL), omitting
`caps` (the touched field of `attenuateA`). -/
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

/-! ## §2 — the `attenuateA` instance (touched component = `caps`, a `funcComponent`). -/

/-- The attenuate effect arguments: the acting principal, the slot index, the narrowed authority list. -/
structure AttenuateArgs where
  actor : CellId
  idx   : Nat
  keep  : List Auth

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The attenuate guard as a `Prop` (the TRIVIAL `True` — the arm is total/unconditional). -/
def attenuateGuardProp (_s : RecChainedState) (_args : AttenuateArgs) : Prop := True

instance (s : RecChainedState) (args : AttenuateArgs) : Decidable (attenuateGuardProp s args) := by
  unfold attenuateGuardProp; exact inferInstanceAs (Decidable True)

/-- The attenuate guard's witness generator: the single `propBit` column at wire `0`. -/
def attenuateGuardEncode (s : RecChainedState) (args : AttenuateArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (attenuateGuardProp s args) else 0

/-- The attenuate guard sub-system: the single `propBit` gate. -/
def attenuateGuardGates : ConstraintSystem := [cBitGuard]

/-- **`attenuateGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem attenuateGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied attenuateGuardGates a ↔ satisfied attenuateGuardGates b := by
  unfold satisfied attenuateGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The `caps` function-field component: digest = an injective whole-function hash `D : Caps → ℤ`
(realizable — a Poseidon Merkle over the cap table's canonical serialization, the same CR bar as
`cellLeafInjective`). The spec-predicted value is the in-place slot narrowing `attenuateSlotF caps actor
idx keep` — FULL function equality, so a drop/reorder/tamper of ANY OTHER holder's slot is REJECTED by
`Function.Injective D`, not just "`actor`'s `idx`-th cap narrowed". (Identical shape to `burnA`'s `bal`
component; differs only in the read field + the predicted value.) -/
def capsComponent (D : Caps → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState AttenuateArgs :=
  funcComponent (β := Caps) (·.caps) D hD
    (fun s args => attenuateSlotF s.kernel.caps args.actor args.idx args.keep)

/-- **`attenuateE`** — the `EffectSpec2` for `attenuateA`, supplied to the v2 framework. -/
def attenuateE (D : Caps → ℤ) (hD : Function.Injective D) :
    EffectSpec2 RecChainedState AttenuateArgs where
  view         := chainView
  active       := capsComponent D hD
  logUpdate    := some (fun s args => authReceipt args.actor :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)
  guardGates   := attenuateGuardGates
  guardProp    := attenuateGuardProp
  guardWidth   := 1
  guardEncode  := attenuateGuardEncode
  guardLocal   := attenuateGuardLocal
  guardWidth_le := by decide

/-! ### §2a — the per-effect obligations for `attenuateE`. -/

/-- **`GuardDecodes2 (attenuateE …)`** — the single bit gate decodes to `True`. -/
theorem attenuateGuardDecodes (D : Caps → ℤ) (hD : Function.Injective D) :
    GuardDecodes2 (attenuateE D hD) := by
  intro s args s' hsat
  change satisfied attenuateGuardGates (attenuateGuardEncode s args s') at hsat
  show attenuateGuardProp s args
  have hg := hsat cBitGuard (by simp [attenuateGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, attenuateGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (attenuateE …)`** — `True` encodes to the satisfied bit gate. -/
theorem attenuateGuardEncodes (D : Caps → ℤ) (hD : Function.Injective D) :
    GuardEncodes2 (attenuateE D hD) := by
  intro s args s' hg
  show satisfied attenuateGuardGates (attenuateGuardEncode s args s')
  intro c hc
  simp only [attenuateGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, attenuateGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `attenuateE` rest-frame portal (the `→`): `RestIffNoCaps RH`'s soundness side (the `caps`-omitting
rest frame). -/
theorem attenuateRestFrameDecodes (S : Surface2) (D : Caps → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoCaps S.RH) :
    RestFrameDecodes2 S (attenuateE D hD) := fun k k' h => (hRest k k').mp h

/-! ### §2b — the apex ↔ `AttenuateSpec` bridge.

The framework's derived `apex` is `True ∧ (caps eq) ∧ (log eq) ∧ restFrame`. The bespoke `AttenuateSpec`
is `(caps eq) ∧ (log eq) ∧ (16 frame fields)` — NO guard conjunct (the arm is total). So the bridge
DROPS the leading `True` and re-packages the same 18 load-bearing conjuncts (the `restFrame` field order
is VERBATIM `AttenuateSpec`'s frame order, so it is a flat repackaging once `True` is stripped). The
component `postClause` is the FULL `caps`-function equality `s'.kernel.caps = attenuateSlotF …`, which is
EXACTLY `AttenuateSpec`'s `caps` clause — so the apex full-function equality IMPLIES (and here equals)
the bespoke spec. -/

/-- **`apex_iff_attenuateSpec`** — the framework's derived `apex` for `attenuateE` is EXACTLY
`AttenuateSpec` (modulo the dropped trivial `True` guard). The component `postClause` is the FULL
`caps`-function equality (`attenuateSlotF …`); the log is the authority-receipt-prepended chain; the
`restFrame` is the 16 non-`caps` frame clauses in `AttenuateSpec`'s order. -/
theorem apex_iff_attenuateSpec (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : AttenuateArgs) (s' : RecChainedState) :
    (attenuateE D hD).apex s args s' ↔ AttenuateSpec s args.actor args.idx args.keep s' := by
  -- unfold the apex's four conjuncts (guard = True, component, log, restFrame) to the bare components.
  show (attenuateGuardProp s args
        ∧ s'.kernel.caps = attenuateSlotF s.kernel.caps args.actor args.idx args.keep
        ∧ s'.log = authReceipt args.actor :: s.log
        ∧ ((attenuateE D hD).restFrame s.kernel s'.kernel))
       ↔ AttenuateSpec s args.actor args.idx args.keep s'
  unfold AttenuateSpec attenuateGuardProp attenuateE
  constructor
  · rintro ⟨_, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨trivial, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §2c — THE VALIDATION: `attenuateA_full_sound ⇒ AttenuateSpec` through the framework. -/

/-- **`attenuateA_full_sound` — the VALIDATION (attenuate through the v2 framework).** A satisfying v2
full-state witness for `attenuateE` proves the complete declarative `AttenuateSpec`. Portals:
`RestIffNoCaps RH` (the `caps`-omitting rest frame), `logHashInjective LH` (the growing log),
`Function.Injective D` (the `caps` component's whole-function digest — the realizable Poseidon-CR bar).
CONCLUDES the bespoke `Spec.AuthorityAttenuation.AttenuateSpec` THROUGH the generic
`effect2_circuit_full_sound`, the circuit⟺spec corner of the authority-attenuation triangle (whose
executor corner is `attenuate_iff_spec`). -/
theorem attenuateA_full_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : AttenuateArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (attenuateE D hD) (encodeE2 S (attenuateE D hD) s args s')) :
    AttenuateSpec s args.actor args.idx args.keep s' := by
  have hapex : (attenuateE D hD).apex s args s' :=
    effect2_circuit_full_sound S (attenuateE D hD)
      (attenuateRestFrameDecodes S D hD hRest) hLog (attenuateGuardDecodes D hD) s args s' h
  exact (apex_iff_attenuateSpec D hD s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def attenuateEWire : EffectSpec2 RecChainedState AttenuateArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := attenuateGuardGates
  guardProp    := attenuateGuardProp
  guardWidth   := 1
  guardEncode  := attenuateGuardEncode
  guardLocal   := attenuateGuardLocal
  guardWidth_le := by decide

def attenuateAAirName : String := "dregg-attenuateA-v2"

def attenuateAEmitted : EmittedDescriptor := emittedEffect2 attenuateAAirName attenuateEWire

#guard attenuateAEmitted.name == attenuateAAirName

/-! ## §3 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms attenuateGuardLocal
#assert_axioms attenuateGuardDecodes
#assert_axioms attenuateGuardEncodes
#assert_axioms apex_iff_attenuateSpec
#assert_axioms attenuateA_full_sound

end Dregg2.Circuit.Inst.AttenuateA
