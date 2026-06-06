/-
# Dregg2.Circuit.Inst.revokeDelegationA — the v2 (`EffectCommit2`) instance for the parent-revocation
  effect `revokeDelegationA` (the cap-graph `removeEdge`).

`revokeDelegationA holder t` is the parent-revocation arm of `FullActionA` (`apply_revoke_delegation`,
dregg1). It is ONE of three protocol-distinct entry points (`revoke` · `dropRefA` · `revokeDelegationA`)
that route to the SAME chained kernel mutator `recCRevoke`, a cap-graph `removeEdge`: the targeted
`holder` loses every cap conferring an edge to `t`; every OTHER holder's cap-list is verbatim; a single
`authReceipt holder` row is prepended to the log; and ALL sixteen non-`caps` kernel fields are frozen.

The touched component is `caps` (a FUNCTION-field `Label → List Cap`), so this instance is NEAR-IDENTICAL
to the `burnA` template (`Inst/burnA.lean`), which touches the other function-field `bal`. It uses the
SAME `funcComponent` (whole-function injective digest — the realizable `cellLeafInjective`-class CR bar),
the SAME growing log, and a `RestIffNoCaps` frame portal (the v1 `RestHashIffFrame` minus `caps`, ADDED
here as `noteCreateA` added `RestIffNoCommitments`). The two differences from `burnA`:
  * the spec-predicted function value is the cap-graph `removeEdgeCaps … holder t` (a DECLARATIVE
    `removeEdge`), not `burnA`'s `recBalCredit`;
  * the guard is `True` — revocation is UNCONDITIONAL (the executor arm is a bare `some`, no fail-closed
    `if`). We commit `True` as ONE `propBit` column (the always-satisfiable guard, as in `noteCreateA`).

THE VALIDATION: `revokeDelegationA_full_sound ⇒ RevokeSpec` THROUGH the framework. A satisfying v2
full-state witness for `revokeDelegationE` proves the complete declarative `RevokeSpec` (the apex truth
in `Dregg2/Circuit/Spec/authorityrevocation.lean`, whose executor corner for this arm is
`execFullA_revokeDelegation_iff_spec`).

ADDITIVE: imports `EffectCommit2` + the authority-revocation spec; edits NONE of them. Follows the
`burnA` template (`Inst/burnA.lean`) + the recipe in `Dregg2/Circuit/CONTRIBUTING.md`.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.Spec.authorityrevocation

namespace Dregg2.Circuit.Inst.RevokeDelegationA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Spec.AuthorityRevocation
open Dregg2.Authority (Caps Cap Auth)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`mkBitGuard`, copied from the validated template).

`revokeDelegationA`'s guard is the TRIVIAL `True` — revocation is UNCONDITIONAL (the executor arm is a
bare `some`, no fail-closed `if`). We still commit it as ONE `propBit` column at wire `0`
(guardWidth = 1) so the instance shape matches the framework's guard sub-system uniformly;
`propBit True = 1` always, so the single gate `propBit (guardProp) = 1` is always satisfiable — the
circuit-level reflection of "always commits". (Identical guard shape to `noteCreateA`.) -/

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
`revokeDelegationA`). This is the 1-line mirror of `EffectCommit2.RestIffNoBal`, swapping the omitted
field from `bal` to `caps`. Carried Prop hypothesis (realizable — a Poseidon hash of a canonical
serialization of the named fields), never an axiom. -/

/-- **`RestIffNoCaps RH`** — the rest hash binds the 16 non-`caps` components (BIDIRECTIONAL), omitting
`caps` (the touched field of `revokeDelegationA`). -/
def RestIffNoCaps (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.escrows = k.escrows
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.bal = k.bal ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)

/-! ## §2 — the `revokeDelegationE` instance (touched component = `caps`).

`revokeDelegationA` over `RecChainedState`: the touched component is the cap-graph `caps` (a
`funcComponent` whose digest is an injective whole-function hash — the realizable bar of
`cellLeafInjective`); the log GROWS by the `authReceipt holder` row; the frame is the 16 non-`caps`
kernel fields (`RestIffNoCaps`). -/

/-- The revoke effect arguments: the revoking `holder` and the revoked target `t`. -/
structure RevokeArgs where
  holder : CellId
  t      : CellId

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The revoke guard as a `Prop` (the spec's TRIVIAL `True` — revocation is unconditional). -/
def revokeGuardProp (_s : RecChainedState) (_args : RevokeArgs) : Prop :=
  True

instance (s : RecChainedState) (args : RevokeArgs) : Decidable (revokeGuardProp s args) := by
  unfold revokeGuardProp; exact inferInstanceAs (Decidable True)

/-- The revoke guard's witness generator: lay the single `propBit` column at wire `0`. -/
def revokeGuardEncode (s : RecChainedState) (args : RevokeArgs) (_s' : RecChainedState) : Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (revokeGuardProp s args) else 0

/-- The revoke guard sub-system: the single `propBit` gate. -/
def revokeGuardGates : ConstraintSystem := [cBitGuard]

/-- **`revokeGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem revokeGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied revokeGuardGates a ↔ satisfied revokeGuardGates b := by
  unfold satisfied revokeGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The `caps` component digest: an injective whole-function hash (carried `Function.Injective D`). The
spec-predicted value is the declarative cap-graph `removeEdgeCaps … holder t` (the SOLE arithmetic
difference from `burnA`, which predicts `recBalCredit`). -/
def capsComponent (D : Caps → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState RevokeArgs :=
  funcComponent (β := Caps) (·.caps) D hD
    (fun s args => removeEdgeCaps s.kernel.caps args.holder args.t)

/-- **`revokeDelegationE`** — the `EffectSpec2` for `revokeDelegationA`, supplied to the v2 framework. -/
def revokeDelegationE (D : Caps → ℤ) (hD : Function.Injective D) :
    EffectSpec2 RecChainedState RevokeArgs where
  view         := chainView
  active       := capsComponent D hD
  logUpdate    := some (fun s args => authReceipt args.holder :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.escrows = k.escrows
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.bal = k.bal ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := revokeGuardGates
  guardProp    := revokeGuardProp
  guardWidth   := 1
  guardEncode  := revokeGuardEncode
  guardLocal   := revokeGuardLocal
  guardWidth_le := by decide

/-! ### §2a — the per-effect obligations for `revokeDelegationE`. -/

/-- **`GuardDecodes2 (revokeDelegationE …)`** — the single bit gate on the guard witness decodes to
`True`. -/
theorem revokeGuardDecodes (D : Caps → ℤ) (hD : Function.Injective D) :
    GuardDecodes2 (revokeDelegationE D hD) := by
  intro s args s' hsat
  change satisfied revokeGuardGates (revokeGuardEncode s args s') at hsat
  show revokeGuardProp s args
  have hg := hsat cBitGuard (by simp [revokeGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, revokeGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (revokeDelegationE …)`** — `True` encodes to the satisfied bit gate. -/
theorem revokeGuardEncodes (D : Caps → ℤ) (hD : Function.Injective D) :
    GuardEncodes2 (revokeDelegationE D hD) := by
  intro s args s' hg
  show satisfied revokeGuardGates (revokeGuardEncode s args s')
  intro c hc
  simp only [revokeGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, revokeGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `revokeDelegationE` rest-frame portal (the `→`): `RestIffNoCaps RH`'s soundness side (the
`caps`-omitting rest frame). -/
theorem revokeRestFrameDecodes (S : Surface2) (D : Caps → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoCaps S.RH) :
    RestFrameDecodes2 S (revokeDelegationE D hD) := fun k k' h => (hRest k k').mp h

/-! ### §2b — the apex ↔ `RevokeSpec` bridge.

A DIRECT identity match (no And-reassoc): the apex's four conjuncts (`guardProp = True`, the `caps`
component `postClause = removeEdgeCaps`, the log = `authReceipt holder ::`, the 16-field `restFrame`)
line up ONE-TO-ONE with `RevokeSpec`'s conjuncts in verbatim order (`True ∧ caps ∧ log ∧ accounts ∧
cell ∧ escrows ∧ nullifiers ∧ revoked ∧ commitments ∧ bal ∧ queues ∧ swiss ∧ slotCaveats ∧ factories
∧ lifecycle ∧ deathCert ∧ delegate ∧ delegations ∧ sealedBoxes`). So both directions are a flat
re-packaging of the same 19 conjuncts. -/

/-- **`apex_iff_revokeSpec`** — the framework's derived `apex` for `revokeDelegationE` is EXACTLY
`RevokeSpec`. The guard is `True`; the component `postClause` is the FULL `caps`-function equality
(`removeEdgeCaps … holder t`); the log is the `authReceipt holder`-prepended chain; the `restFrame` is
the 16 non-`caps` frame clauses in `RevokeSpec`'s order. -/
theorem apex_iff_revokeSpec (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState) :
    (revokeDelegationE D hD).apex s args s' ↔ RevokeSpec s args.holder args.t s' := by
  show (revokeGuardProp s args
        ∧ s'.kernel.caps = removeEdgeCaps s.kernel.caps args.holder args.t
        ∧ s'.log = authReceipt args.holder :: s.log
        ∧ ((revokeDelegationE D hD).restFrame s.kernel s'.kernel))
       ↔ RevokeSpec s args.holder args.t s'
  unfold RevokeSpec revokeGuardProp revokeDelegationE
  constructor
  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §2c — THE VALIDATION: `revokeDelegationA_full_sound ⇒ RevokeSpec` through the framework. -/

/-- **`revokeDelegationA_full_sound` — the VALIDATION (parent-revocation through the v2 framework).** A
satisfying v2 full-state witness for `revokeDelegationE` proves the complete declarative `RevokeSpec`.
Portals: `RestIffNoCaps RH` (the `caps`-omitting rest frame), `logHashInjective LH` (the growing log),
`Function.Injective D` (the `caps` component's whole-function digest — the realizable Poseidon-CR bar).
CONCLUDES the bespoke `Spec.AuthorityRevocation.RevokeSpec` THROUGH the generic
`effect2_circuit_full_sound`, the circuit⟺spec corner of the authority-revocation triangle (its executor
corner is `execFullA_revokeDelegation_iff_spec`). -/
theorem revokeDelegationA_full_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (revokeDelegationE D hD) (encodeE2 S (revokeDelegationE D hD) s args s')) :
    RevokeSpec s args.holder args.t s' := by
  have hapex : (revokeDelegationE D hD).apex s args s' :=
    effect2_circuit_full_sound S (revokeDelegationE D hD)
      (revokeRestFrameDecodes S D hD hRest) hLog (revokeGuardDecodes D hD) s args s' h
  exact (apex_iff_revokeSpec D hD s args s').mp hapex

/-! ## §3 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms revokeGuardLocal
#assert_axioms revokeGuardDecodes
#assert_axioms revokeGuardEncodes
#assert_axioms apex_iff_revokeSpec
#assert_axioms revokeDelegationA_full_sound

end Dregg2.Circuit.Inst.RevokeDelegationA
