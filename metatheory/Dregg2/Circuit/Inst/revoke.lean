/-
# Dregg2.Circuit.Inst.revoke — the v2 (`EffectCommit2`) instance for the AUTHORITY-REVOCATION effect
  `revoke` (and its definitionally-equal arms `dropRefA` / `revokeDelegationA`).

`revoke` is the single-component cap-graph `removeEdge` of `FullActionA`: at `holder`, drop every cap
that confers an edge to `t` (keeping every OTHER holder's cap-list verbatim), prepend an `authReceipt`
to the log, and freeze the 16 non-`caps` kernel fields. It is UNCONDITIONAL — the executor arm is a
bare `some (recCRevoke …)`, no fail-closed `if` — so the admissibility guard is `True` (the spec's
guard slot).

The touched component is the per-holder cap table `caps : CellId → List Cap` (a FUNCTION-field), so —
exactly like `burnE`'s `bal` — this is a `funcComponent` whose digest is an injective whole-function
hash (the realizable Poseidon-CR bar `Function.Injective D`); the spec-predicted value is the
declarative `removeEdgeCaps st.kernel.caps holder t`. The log GROWS by `authReceipt holder`. The frame
is the 16 non-`caps` kernel fields (`RestIffNoCaps`, ADDED here — the v1 `RestHashIffFrame` with `caps`
omitted; the swarm adds one `RestIffNo*` per touched field).

THE VALIDATION: `revoke_full_sound ⇒ RevokeSpec` THROUGH the framework. A satisfying v2 full-state
witness for `revokeE` proves the complete declarative `RevokeSpec` (the apex truth in
`Dregg2/Circuit/Spec/authorityrevocation.lean`, whose executor corner is `execFullA_revoke_iff_spec`
via `recCRevoke_iff_spec`).

The guard slot is the trivial `True` (`revokeAdmit`, copied from the `noteCreateA` unconditional-guard
shape): one `propBit` column at wire `0`, always satisfiable (`propBit True = 1`). Because the spec's
guard conjunct is literally `True`, the apex's guard clause matches `RevokeSpec`'s leading `True`
verbatim — the bridge is a flat re-packaging of the 19 conjuncts (no And-reassoc, no weakening).

ADDITIVE: imports `EffectCommit2` + the authority-revocation spec; edits NEITHER. Follows the `burnA`
template (funcComponent function-field) + the `noteCreateA` template (added `RestIffNo*` portal + trivial
guard) + the recipe in `Dregg2/Circuit/CONTRIBUTING.md`.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.Spec.authorityrevocation

namespace Dregg2.Circuit.Inst.Revoke

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Spec.AuthorityRevocation
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap)

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (copied from the `noteCreateA` unconditional template).

`revoke`'s guard is the TRIVIAL `revokeAdmit = True` — revocation is UNCONDITIONAL (a bare `some` in the
executor, no fail-closed `if`). We still commit it as ONE `propBit` column at wire `0` (guardWidth = 1)
so the instance shape matches the framework's guard sub-system uniformly; `propBit True = 1` always, so
the single gate `propBit (guardProp) = 1` is always satisfiable — the circuit-level reflection of
"always commits". -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-- The trivial revoke admissibility predicate — revocation is UNCONDITIONAL (matches `RevokeSpec`'s
leading `True` conjunct). -/
def revokeAdmit : Prop := True

/-! ## §1 — the `RestIffNoCaps` portal (the v1 `RestHashIffFrame` minus `caps`).

The realizable injective-rest-hash portal for the effect that touches the `caps` function-field: the
rest hash binds the 16 non-`caps` components (BIDIRECTIONAL), OMITTING `caps` (the touched field of
`revoke`). This is the 1-line mirror of `EffectCommit2.RestIffNoBal`, swapping the omitted field from
`bal` to `caps`. Carried Prop hypothesis (realizable — a Poseidon hash of a canonical serialization of
the named fields), never an axiom. -/

/-- **`RestIffNoCaps RH`** — the rest hash binds the 16 non-`caps` components (BIDIRECTIONAL), omitting
`caps` (the touched field of `revoke`). The 16 named fields are EXACTLY `RevokeSpec`'s frame (accounts
cell escrows nullifiers revoked commitments bal queues swiss slotCaveats factories lifecycle deathCert
delegate delegations sealedBoxes). -/
def RestIffNoCaps (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.escrows = k.escrows
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.bal = k.bal ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)

/-! ## §2 — the `revoke` instance (touched component = `caps`).

`revoke` over `RecChainedState`: the touched component is the per-holder cap table `caps` (a
`funcComponent` whose digest is an injective whole-function hash — the realizable bar of
`cellLeafInjective`); the log GROWS by `authReceipt holder`; the frame is the 16 non-`caps` kernel
fields (`RestIffNoCaps`). The spec-predicted value is the declarative `removeEdgeCaps`. -/

/-- The revoke effect arguments: the holder whose authority shrinks, and the target whose edge is torn
down (the `(holder, t)` pair of `recCRevoke`). -/
structure RevokeArgs where
  holder : CellId
  t      : CellId

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The revoke guard as a `Prop` (the spec's TRIVIAL `revokeAdmit = True`). -/
def revokeGuardProp (_s : RecChainedState) (_args : RevokeArgs) : Prop :=
  revokeAdmit

instance (s : RecChainedState) (args : RevokeArgs) : Decidable (revokeGuardProp s args) := by
  unfold revokeGuardProp revokeAdmit; exact inferInstanceAs (Decidable True)

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
spec-predicted value is the declarative `removeEdgeCaps s.kernel.caps holder t` — a `removeEdge` of the
WHOLE cap table (a drop/reorder/tamper of ANY holder's cap-list is REJECTED, since `funcComponent`'s
`postClause` is FULL function equality). -/
def capsComponent (D : Caps → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState RevokeArgs :=
  funcComponent (β := Caps) (·.caps) D hD
    (fun s args => removeEdgeCaps s.kernel.caps args.holder args.t)

/-- **`revokeE`** — the `EffectSpec2` for `revoke`, supplied to the v2 framework. -/
def revokeE (D : Caps → ℤ) (hD : Function.Injective D) :
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

/-! ### §2a — the per-effect obligations for `revokeE`. -/

/-- **`GuardDecodes2 (revokeE …)`** — the single bit gate decodes to `revokeAdmit`. -/
theorem revokeGuardDecodes (D : Caps → ℤ) (hD : Function.Injective D) :
    GuardDecodes2 (revokeE D hD) := by
  intro s args s' hsat
  change satisfied revokeGuardGates (revokeGuardEncode s args s') at hsat
  show revokeGuardProp s args
  have hg := hsat cBitGuard (by simp [revokeGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, revokeGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (revokeE …)`** — `revokeAdmit` encodes to the satisfied bit gate. -/
theorem revokeGuardEncodes (D : Caps → ℤ) (hD : Function.Injective D) :
    GuardEncodes2 (revokeE D hD) := by
  intro s args s' hg
  show satisfied revokeGuardGates (revokeGuardEncode s args s')
  intro c hc
  simp only [revokeGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, revokeGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `revokeE` rest-frame portal (the `→`): `RestIffNoCaps RH`'s soundness side (the `caps`-omitting
rest frame). -/
theorem revokeRestFrameDecodes (S : Surface2) (D : Caps → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoCaps S.RH) :
    RestFrameDecodes2 S (revokeE D hD) := fun k k' h => (hRest k k').mp h

/-! ### §2b — the apex ↔ `RevokeSpec` bridge.

A DIRECT identity match (no And-reassoc): the guard is `revokeAdmit = True` (matching `RevokeSpec`'s
leading `True`), the component `postClause` is the FULL cap-table equality (`removeEdgeCaps …`), the log
is the `authReceipt`-prepended chain, and the `restFrame` field order is VERBATIM `RevokeSpec`'s frame
order (`accounts cell escrows nullifiers revoked commitments bal queues swiss slotCaveats factories
lifecycle deathCert delegate delegations sealedBoxes`). So both directions are a flat re-packaging of
the same 19 conjuncts. -/

/-- **`apex_iff_revokeSpec`** — the framework's derived `apex` for `revokeE` is EXACTLY `RevokeSpec`. The
guard is `revokeAdmit = True`; the component `postClause` is the FULL cap-table equality (`removeEdgeCaps
s.kernel.caps holder t`); the log is the `authReceipt`-prepended chain; the `restFrame` is the 16
non-`caps` frame clauses in `RevokeSpec`'s order. -/
theorem apex_iff_revokeSpec (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState) :
    (revokeE D hD).apex s args s' ↔ RevokeSpec s args.holder args.t s' := by
  show (revokeGuardProp s args
        ∧ s'.kernel.caps = removeEdgeCaps s.kernel.caps args.holder args.t
        ∧ s'.log = authReceipt args.holder :: s.log
        ∧ ((revokeE D hD).restFrame s.kernel s'.kernel))
       ↔ RevokeSpec s args.holder args.t s'
  unfold RevokeSpec revokeGuardProp revokeAdmit revokeE
  constructor
  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcaps, hlog, hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §2c — THE VALIDATION: `revoke_full_sound ⇒ RevokeSpec` through the framework. -/

/-- **`revoke_full_sound` — the VALIDATION (authority-revocation through the v2 framework).** A satisfying
v2 full-state witness for `revokeE` proves the complete declarative `RevokeSpec`. Portals: `RestIffNoCaps
RH` (the `caps`-omitting rest frame), `logHashInjective LH` (the growing log), `Function.Injective D` (the
`caps` component's whole-function digest — the realizable Poseidon-CR bar). CONCLUDES the bespoke
`Spec.AuthorityRevocation.RevokeSpec` THROUGH the generic `effect2_circuit_full_sound`, the circuit⟺spec
corner of the authority-revocation triangle (the executor corner is `execFullA_revoke_iff_spec`). One
spec certifies all three arms (`revoke`/`dropRefA`/`revokeDelegationA`) since they are definitionally the
same transition. -/
theorem revoke_full_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (revokeE D hD) (encodeE2 S (revokeE D hD) s args s')) :
    RevokeSpec s args.holder args.t s' := by
  have hapex : (revokeE D hD).apex s args s' :=
    effect2_circuit_full_sound S (revokeE D hD)
      (revokeRestFrameDecodes S D hD hRest) hLog (revokeGuardDecodes D hD) s args s' h
  exact (apex_iff_revokeSpec D hD s args s').mp hapex

/-! ## §3 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms revokeGuardLocal
#assert_axioms revokeGuardDecodes
#assert_axioms revokeGuardEncodes
#assert_axioms apex_iff_revokeSpec
#assert_axioms revoke_full_sound

end Dregg2.Circuit.Inst.Revoke
