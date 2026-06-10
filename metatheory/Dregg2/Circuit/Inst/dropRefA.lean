/-
# Dregg2.Circuit.Inst.dropRefA — the v2 (`EffectCommit2`) instance for the CapTP GC effect `dropRefA`.

`dropRefA` is the CapTP garbage-collect / reference-drop arm of the authority-revocation FAMILY
(`revoke` · `dropRefA` · `revokeDelegationA`). All three arms are DEFINITIONALLY the SAME transition —
they route onto ONE chained kernel mutator `recCRevoke`, a cap-graph `removeEdge`:

    execFullA s (.dropRefA holder t) = some (recCRevoke s holder t)
    recCRevoke s holder t = { kernel := recKRevokeTarget s.kernel holder t
                            , log := authReceipt holder :: s.log }

`recKRevokeTarget` rewrites the `caps` table to the `removeEdge` filter (`holder` loses every cap that
confers an edge to `t`; every OTHER holder's cap-list literally unchanged) and prepends one receipt
row to the log — touching exactly TWO `RecChainedState` components (`caps`, `log`) and FREEZING the
other 16 kernel fields.

So this is a SINGLE-component effect whose touched component is the FUNCTION-field `caps`
(`Caps = Label → List Cap`) — exactly the `funcComponent` shape of the `bal` instances
(`burnA`/`bridgeMintA`/`balanceA`), only over `caps` instead of `bal`. Through the v2 framework
(`EffectCommit2`):
  * touched component = `caps` (a `funcComponent`, FULL-function digest = the realizable injective
    whole-value hash bar — a drop/reorder of any holder's cap-list is REJECTED, not just "filtered at
    `holder`"). The spec-predicted post value is the INDEPENDENT declarative `removeEdgeCaps`
    (`Spec.AuthorityRevocation`), NOT the executor's `recKRevokeTarget`;
  * the log GROWS by the authority receipt (`authReceipt holder :: s.log`);
  * the guard is the TRIVIAL `True` — revocation is UNCONDITIONAL (the executor arm is a bare `some`,
    no fail-closed `if`). Same shape as `noteCreateA`'s `noteCreateAdmit = True`;
  * the frame is the 16 non-`caps` kernel fields (`RestIffNoCaps`, ADDED here — the v1
    `RestHashIffFrame` with `caps` omitted; the swarm adds one `RestIffNo*` per touched field).

`dropRefA_full_sound` CONCLUDES the bespoke `Spec.AuthorityRevocation.RevokeSpec` THROUGH the
framework: `effect2_circuit_full_sound` gives the derived `apex`, and `apex_iff_revokeSpec`
(a DIRECT identity match — the `restFrame` order is verbatim `RevokeSpec`'s 16-field frame order, and
the `True` guard / `caps` component / log clauses line up one-to-one) rewrites it to the bespoke spec.
The bespoke spec's executor corner is `execFullA_dropRef_iff_spec` (`recCRevoke` ⟺ `RevokeSpec`), so
the circuit⟺spec corner here completes the dropRefA triangle.

ADDITIVE: imports `EffectCommit2` + the bespoke spec `Dregg2.Circuit.Spec.authorityrevocation`; edits
NEITHER `EffectCommit2`/`EffectInstances2`/`StateCommit` NOR any `Spec/*` file NOR `Dregg2.lean`.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.authorityrevocation

namespace Dregg2.Circuit.Inst.DropRefA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.Spec.AuthorityRevocation
open Dregg2.Authority (Caps Cap Auth)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`mkBitGuard`), copied from the validated template.

`dropRefA`'s guard is the TRIVIAL `True` — authority-revocation is UNCONDITIONAL (the executor arm is a
bare `some (recCRevoke …)`, no fail-closed `if`). We still commit it as ONE `propBit` column at wire
`0` (guardWidth = 1) so the instance shape matches the framework's guard sub-system uniformly;
`propBit True = 1` always, so the single gate `propBit (guardProp) = 1` is always satisfiable — the
circuit-level reflection of "always commits". (Identical shape to `noteCreateA`.) -/

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
`dropRefA`). This is the 1-line mirror of `EffectCommit2.RestIffNoBal`, swapping the omitted field from
`bal` to `caps`. Carried Prop hypothesis (realizable — a Poseidon hash of a canonical serialization of
the named fields), never an axiom. The omitted/included fields are precisely `RevokeSpec`'s 16-field
frame (`accounts cell escrows nullifiers revoked commitments bal queues swiss slotCaveats factories
lifecycle deathCert delegate delegations sealedBoxes`). -/

/-- **`RestIffNoCaps RH`** — the rest hash binds the 16 non-`caps` components (BIDIRECTIONAL), omitting
`caps` (the touched field of `dropRefA`). -/
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

/-! ## §2 — the `dropRefA` instance (touched component = `caps`). -/

/-- The drop-ref effect arguments: the revoking holder and the target it drops its edge(s) to. -/
structure DropRefArgs where
  holder : CellId
  t      : CellId

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The drop-ref guard as a `Prop` (the spec's TRIVIAL `True`). -/
def dropRefGuardProp (_s : RecChainedState) (_args : DropRefArgs) : Prop :=
  True

instance (s : RecChainedState) (args : DropRefArgs) : Decidable (dropRefGuardProp s args) := by
  unfold dropRefGuardProp; exact inferInstanceAs (Decidable True)

/-- The drop-ref guard's witness generator: the single `propBit` column at wire `0`. -/
def dropRefGuardEncode (s : RecChainedState) (args : DropRefArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (dropRefGuardProp s args) else 0

/-- The drop-ref guard sub-system: the single `propBit` gate. -/
def dropRefGuardGates : ConstraintSystem := [cBitGuard]

/-- **`dropRefGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem dropRefGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied dropRefGuardGates a ↔ satisfied dropRefGuardGates b := by
  unfold satisfied dropRefGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The `caps` component digest: an injective whole-function hash `D : Caps → ℤ` (carried
`Function.Injective D` — the realizable Poseidon-Merkle over `caps`'s canonical serialization, the same
CR bar as `cellLeafInjective`/`listLeafInjective`). The spec-predicted post value is the INDEPENDENT
declarative `removeEdgeCaps` (the cap-graph `removeEdge`, NOT the executor's `recKRevokeTarget`); a
drop/reorder of ANY holder's cap-list is REJECTED by `funcComponent`'s FULL-function equality. -/
def capsComponent (D : Caps → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState DropRefArgs :=
  funcComponent (β := Caps) (·.caps) D hD
    (fun s args => removeEdgeCaps s.kernel.caps args.holder args.t)

/-- **`dropRefE`** — the `EffectSpec2` for `dropRefA`, supplied to the v2 framework. -/
def dropRefE (D : Caps → ℤ) (hD : Function.Injective D) :
    EffectSpec2 RecChainedState DropRefArgs where
  view         := chainView
  active       := capsComponent D hD
  logUpdate    := some (fun s args => authReceipt args.holder :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)
  guardGates   := dropRefGuardGates
  guardProp    := dropRefGuardProp
  guardWidth   := 1
  guardEncode  := dropRefGuardEncode
  guardLocal   := dropRefGuardLocal
  guardWidth_le := by decide

/-! ### §2a — the per-effect obligations for `dropRefE`. -/

/-- **`GuardDecodes2 (dropRefE …)`** — the single bit gate decodes to `True`. -/
theorem dropRefGuardDecodes (D : Caps → ℤ) (hD : Function.Injective D) :
    GuardDecodes2 (dropRefE D hD) := by
  intro s args s' hsat
  change satisfied dropRefGuardGates (dropRefGuardEncode s args s') at hsat
  show dropRefGuardProp s args
  have hg := hsat cBitGuard (by simp [dropRefGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, dropRefGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (dropRefE …)`** — `True` encodes to the satisfied bit gate. -/
theorem dropRefGuardEncodes (D : Caps → ℤ) (hD : Function.Injective D) :
    GuardEncodes2 (dropRefE D hD) := by
  intro s args s' hg
  show satisfied dropRefGuardGates (dropRefGuardEncode s args s')
  intro c hc
  simp only [dropRefGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, dropRefGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `dropRefE` rest-frame portal (the `→`): `RestIffNoCaps RH`'s soundness side. -/
theorem dropRefRestFrameDecodes (S : Surface2) (D : Caps → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoCaps S.RH) :
    RestFrameDecodes2 S (dropRefE D hD) := fun k k' h => (hRest k k').mp h

/-! ### §2b — the apex ↔ `RevokeSpec` bridge.

A DIRECT identity match (no And-reassoc): the framework's `apex` is
`guardProp ∧ postClause(caps) ∧ log ∧ restFrame`, and `RevokeSpec` is
`True ∧ caps ∧ log ∧ [16 frame fields]`. The `dropRefGuardProp = True` matches `RevokeSpec`'s `True`
slot, the `funcComponent` `postClause` is the FULL `caps` equality (`= removeEdgeCaps`), the log is the
`authReceipt`-prepended chain, and the `restFrame` field order is VERBATIM `RevokeSpec`'s 16-field
frame order (`accounts cell escrows nullifiers revoked commitments bal queues swiss slotCaveats
factories lifecycle deathCert delegate delegations sealedBoxes`). So both directions are a flat
re-packaging of the same 19 conjuncts. -/

/-- **`apex_iff_revokeSpec`** — the framework's derived `apex` for `dropRefE` is EXACTLY `RevokeSpec`.
The guard is `True`; the component `postClause` is the FULL `caps`-function equality (`= removeEdgeCaps
… holder t`); the log is the receipt-prepended chain; the `restFrame` is the 16 non-`caps` frame
clauses in `RevokeSpec`'s order. -/
theorem apex_iff_revokeSpec (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : DropRefArgs) (s' : RecChainedState) :
    (dropRefE D hD).apex s args s' ↔ RevokeSpec s args.holder args.t s' := by
  show (dropRefGuardProp s args
        ∧ s'.kernel.caps = removeEdgeCaps s.kernel.caps args.holder args.t
        ∧ s'.log = authReceipt args.holder :: s.log
        ∧ ((dropRefE D hD).restFrame s.kernel s'.kernel))
       ↔ RevokeSpec s args.holder args.t s'
  unfold RevokeSpec dropRefGuardProp dropRefE
  constructor
  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §2c — THE VALIDATION: `dropRefA_full_sound ⇒ RevokeSpec` through the framework. -/

/-- **`dropRefA_full_sound` — the VALIDATION (drop-ref through the v2 framework).** A satisfying v2
full-state witness for `dropRefE` proves the complete declarative bespoke `RevokeSpec` (all 17 kernel
fields + log are pinned). Portals: `RestIffNoCaps RH` (the `caps`-omitting rest frame),
`logHashInjective LH` (the growing log), `Function.Injective D` (the `caps` component's whole-function
digest — the realizable Poseidon-CR bar). This CONCLUDES the bespoke authority-revocation spec
(`Spec.AuthorityRevocation.RevokeSpec`, whose executor corner is `execFullA_dropRef_iff_spec`) THROUGH
the generic `effect2_circuit_full_sound` — the circuit⟺spec corner of the dropRefA triangle. -/
theorem dropRefA_full_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DropRefArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (dropRefE D hD) (encodeE2 S (dropRefE D hD) s args s')) :
    RevokeSpec s args.holder args.t s' := by
  have hapex : (dropRefE D hD).apex s args s' :=
    effect2_circuit_full_sound S (dropRefE D hD)
      (dropRefRestFrameDecodes S D hD hRest) hLog (dropRefGuardDecodes D hD) s args s' h
  exact (apex_iff_revokeSpec D hD s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def dropRefEWire : EffectSpec2 RecChainedState DropRefArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := dropRefGuardGates
  guardProp    := dropRefGuardProp
  guardWidth   := 1
  guardEncode  := dropRefGuardEncode
  guardLocal   := dropRefGuardLocal
  guardWidth_le := by decide

def dropRefAAirName : String := "dregg-dropRefA-v2"

def dropRefAEmitted : EmittedDescriptor := emittedEffect2 dropRefAAirName dropRefEWire

#guard dropRefAEmitted.name == dropRefAAirName

/-! ## §3 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms dropRefGuardLocal
#assert_axioms dropRefGuardDecodes
#assert_axioms dropRefGuardEncodes
#assert_axioms apex_iff_revokeSpec
#assert_axioms dropRefA_full_sound

end Dregg2.Circuit.Inst.DropRefA
