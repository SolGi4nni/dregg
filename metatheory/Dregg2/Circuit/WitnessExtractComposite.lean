/-
# Dregg2.Circuit.WitnessExtractComposite — the adversarial-witness EXTRACTOR for the COMPOSITE `exerciseA`.

`exerciseA` is the one COMPOSITE meta-action: an outer v1 hold-gate (`exerciseE` over `EffectCommit`)
that checks `exerciseGuard` (the actor holds SOME cap conferring an edge to `target`), prepends the
authority receipt and FREEZES the kernel, followed by an inner `List FullActionA` fold run from the hold
post-state. Its full-state spec is `ExerciseSpec = innerFacetsAdmittedA ∧ exerciseGuard ∧ turnSpec …`.

The other 31 effects close hostile-witness extraction with a single framework extractor each
(`WitnessExtract{,Dual,3,5}` + the v1 `WitnessExtractV1`). The composite is the product of TWO already-
closed legs:

  1. **HOLD-GATE LEG (hostile extraction, CLOSED here).** The hold-gate is a v1 `EffectSpec`, so its
     hostile extractor is `WitnessExtractV1.effect_extract` instantiated for `exerciseE`: an ARBITRARY
     PI-bound (`PIBindsDigestsV1`) satisfying witness — NOT the honest `encodeE` — forces
     `ExerciseHoldSpec`, hence `exerciseGuard` (the hold AUTHORITY). This is `exerciseHold_extract` /
     `exerciseHold_extract_authority` below: the genuine hostile closure of the authority leg.

  2. **INNER-FOLD LEG (refinement, already CLOSED upstream).** The inner fold reuses the per-effect
     extractors: `ExerciseInnerTurn.exercise_inner_emitted_refines_turnSpec` reduces the inner emitted
     chain to the per-step `step_emitted_refines_fullActionStep` (which dispatches each inner action to
     the per-effect refinement/extractor already banked). It is carried here as the standard
     `innerTurnH ↔ turnSpec …` bridge — exactly the shape `exercise_circuit_refines_spec` uses.

`exerciseA_extract` composes the two: a PI-bound satisfying HOLD witness (the adversary keeps the root
wires `64/65` and every `w ≥ 74`) + the inner EMITTED circuit witness (`exerciseInnerTurnWitness`, a
`TurnEmittedChain` over the inner forest) discharged per-step by the banked `hstep` extractor + the facet
mask FORCES the COMPLETE `ExerciseSpec`. This is the hostile-witness upgrade of
`Inst.ExerciseA.exercise_circuit_refines_spec` (which consumed the honest `encodeE` hold witness via
`exerciseA_full_sound`); we swap in `WitnessExtractV1.effect_extract` for the hold leg.

NO foundational residual: BOTH legs are forced from circuit evidence — the hold authority from the
satisfying PI-bound hold witness, and the inner fold from the inner emitted chain via
`exercise_inner_emitted_refines_turnSpec` ∘ the per-step `hstep` extractors. The inner conjunct is NOT a
carried `innerTurnH ↔ turnSpec` bridge; `exerciseA_extract` threads the emitted witness directly. The
composite is a WIRE of two closed legs, not a new soundness obligation.

ADDITIVE: imports `WitnessExtractV1` + `Inst/exerciseA` + `Inst/ExerciseInnerTurn`; edits none.
-/
import Dregg2.Circuit.WitnessExtractV1
import Dregg2.Circuit.Inst.exerciseA
import Dregg2.Circuit.Inst.ExerciseInnerTurn

namespace Dregg2.Circuit.WitnessExtractComposite

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit (CommitSurface satisfiedE)
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective cellLeafInjective
  RestHashIffFrame AccountsWF)
open Dregg2.Circuit.ActionDispatch (exerciseGuard exerciseHoldState ExerciseHoldSpec ExerciseSpec
  turnSpec fullActionStep)
open Dregg2.Exec.TurnExecutorFull (innerFacetsAdmittedA)
open Dregg2.Circuit.WitnessExtractV1 (PIBindsDigestsV1 effect_extract effect_extract_rejects_log_forge)
open Dregg2.Circuit.Inst.ExerciseA (exerciseE exerciseGuardDecodes apex_iff_exerciseHoldSpec
  ExerciseHoldArgs ExerciseFullArgs exerciseHoldState_accountsWF)
open Dregg2.Circuit.TurnEmit (DescriptorLookup stepEmittedSat)
open Dregg2.Circuit.TurnWitness (StepWitness TurnWitness)
open Dregg2.Circuit.Inst.ExerciseInnerTurn (exerciseInnerTurnWitness
  exercise_inner_emitted_refines_turnSpec)
open Dregg2.Exec (RecChainedState CellId)
open Dregg2.Exec.TurnExecutorFull (FullActionA)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the HOLD-GATE leg: hostile extraction for `exerciseE` (the v1 hold-gate).

A PI-bound (`PIBindsDigestsV1`) satisfying witness for the hold-gate circuit — an ARBITRARY assignment,
NOT the honest `encodeE` — forces `ExerciseHoldSpec`. The adversary keeps the un-gated root wires
`64/65` and every `w ≥ 74`; the verifier pins only the eight digest wires + the single guard bit. -/

/-- **`exerciseHold_extract`** — the hold-gate hostile extractor: an ARBITRARY PI-bound satisfying
witness for `exerciseE` forces the COMPLETE `ExerciseHoldSpec` (the kernel-frozen, receipt-prepended
hold step under the held authority). -/
theorem exerciseHold_extract
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ExerciseHoldArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (a : Assignment)
    (hsat : satisfiedE S exerciseE a)
    (hPI : PIBindsDigestsV1 S exerciseE s args s' a) :
    ExerciseHoldSpec s args.actor args.target s' :=
  (apex_iff_exerciseHoldSpec s args s').mp
    (effect_extract S exerciseE hN hL hRest hLog exerciseGuardDecodes s args s' hwf hwf' a hsat hPI)

/-- **`exerciseHold_extract_authority`** — the AUTHORITY conjunct of the hold extraction: a satisfying
PI-bound hold witness FORCES `exerciseGuard` (the actor genuinely holds a cap conferring the edge to
`target`). The hold-gate cannot be satisfied without the held authority — fail-closed. -/
theorem exerciseHold_extract_authority
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ExerciseHoldArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (a : Assignment)
    (hsat : satisfiedE S exerciseE a)
    (hPI : PIBindsDigestsV1 S exerciseE s args s' a) :
    exerciseGuard s args.actor args.target :=
  (exerciseHold_extract S hN hL hRest hLog s args s' hwf hwf' a hsat hPI).1

/-! ## §2 — anti-ghost teeth for the hold leg. -/

/-- **`exerciseHold_extract_rejects_log_forge`** — a claimed hold post-log differing from the spec-
predicted `authReceipt actor :: log` has NO satisfying PI-bound hold witness. (`cELog` + injective log
hash.) The hold receipt cannot be forged. -/
theorem exerciseHold_extract_rejects_log_forge
    (S : CommitSurface) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ExerciseHoldArgs) (s' : RecChainedState) (a : Assignment)
    (hPI : PIBindsDigestsV1 S exerciseE s args s' a)
    (htamper : exerciseE.view.getLog s' ≠ exerciseE.postLog s args) :
    ¬ satisfiedE S exerciseE a :=
  effect_extract_rejects_log_forge S exerciseE hLog s args s' a hPI htamper

/-! ## §3 — the COMPOSITE extractor: hostile hold leg ∘ inner-turn refinement ⇒ `ExerciseSpec`.

This is the hostile-witness upgrade of `Inst.ExerciseA.exercise_circuit_refines_spec`. That theorem
consumed the HONEST `encodeE` hold witness (via `exerciseA_full_sound`); here we consume an ARBITRARY
PI-bound satisfying hold witness `a` (via `exerciseHold_extract`). The inner fold is FORCED from the
inner EMITTED circuit witness `innerW : exerciseInnerTurnWitness …` (a `TurnEmittedChain` over the inner
forest), NOT a free bridge: `exerciseA_extract_inner_refines` reduces the emitted chain to `turnSpec`
per-step through the per-effect `hstep` extractor already banked. So BOTH legs are now forced from circuit
evidence — the hold authority from `a`/`hPI`, the inner fold from `innerW`/`hstep`. -/

/-- **`exerciseA_extract`** — THE composite adversarial-witness extractor. An ARBITRARY PI-bound
satisfying HOLD witness `a` (the adversary keeps the roots `64/65` and `w ≥ 74`) + the inner EMITTED
circuit witness `innerW` (a `TurnEmittedChain` over the inner forest from the hold post-state) discharged
per-step by the banked extractor `hstep` + the facet mask `hfacet` FORCES the COMPLETE `ExerciseSpec`
(facet-admitted ∧ held authority ∧ inner fold from the hold post-state). BOTH the hold authority AND the
inner fold are EXTRACTED from circuit evidence, not assumed: the inner conjunct is forced by
`exerciseA_extract_inner_refines` (`exercise_inner_emitted_refines_turnSpec` ∘ the per-step refinement),
not a carried `innerTurnH ↔ turnSpec` bridge. -/
theorem exerciseA_extract
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (pre post : RecChainedState) (args : ExerciseFullArgs)
    -- The inner emitted circuit witness + the banked per-step refinement (the inner leg's circuit evidence):
    (lookup : DescriptorLookup) (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (hstep :
      ∀ (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA),
        stepEmittedSat lookup sw st st' fa → fullActionStep st fa st')
    (innerW : exerciseInnerTurnWitness lookup compress stepRoot
        (exerciseHoldState pre args.actor) post args.inner)
    (hfacet : innerFacetsAdmittedA pre args.actor args.target args.inner = true)
    (hwf : AccountsWF pre.kernel)
    (a : Assignment)
    (hsat : satisfiedE S exerciseE a)
    (hPI : PIBindsDigestsV1 S exerciseE pre ⟨args.actor, args.target⟩
        (exerciseHoldState pre args.actor) a) :
    ExerciseSpec pre args.actor args.target args.inner post := by
  have hguard : exerciseGuard pre args.actor args.target :=
    exerciseHold_extract_authority S hN hL hRest hLog pre ⟨args.actor, args.target⟩
      (exerciseHoldState pre args.actor) hwf
      (exerciseHoldState_accountsWF pre args.actor hwf) a hsat hPI
  -- The inner fold is FORCED from the inner emitted chain (not a free bridge): the banked per-step
  -- refinement `hstep` discharges the `TurnEmittedChain` in `innerW` to `turnSpec` (this is exactly
  -- `exerciseA_extract_inner_refines` / `exercise_inner_emitted_refines_turnSpec`, §4).
  have hinner : turnSpec (exerciseHoldState pre args.actor) args.inner post :=
    exercise_inner_emitted_refines_turnSpec lookup compress stepRoot hstep
      (exerciseHoldState pre args.actor) post args.inner innerW
  exact ⟨hfacet, hguard, hinner⟩

/-! ## §4 — the inner-fold leg, restated standalone (the lemma `exerciseA_extract` threads inline).

`exerciseA_extract` (§3) forces the inner conjunct of `ExerciseSpec` by threading the inner emitted chain
through `exercise_inner_emitted_refines_turnSpec` — so the composite has NO carried inner-turn bridge.
This §4 lemma restates that same inner-fold closure standalone (it is definitionally the body
`exerciseA_extract` invokes): when the inner emitted chain is satisfied, the inner forest refines
`turnSpec`, via the generic `TurnEmit.turn_emitted_refines_turnSpec` discharged per-step by `hstep`. That
per-step hypothesis (`hstep : stepEmittedSat … fa → fullActionStep … fa`) IS the per-effect extractors
composed — every inner `FullActionA` arm routes to a banked `*_extract` / `*_emitted_refines_*`. So the
inner leg's hostile extraction is NOT a new foundational obligation; it is the SAME per-effect closure
applied along the fold, terminating structurally over `inner : List FullActionA`. -/

/-- **`exerciseA_extract_inner_refines`** — the inner-fold leg, restated as the per-step closure: when the
inner emitted chain is satisfied (the upstream `exerciseInnerTurnWitness`), the inner forest refines
`turnSpec`, via the per-effect `hstep` refinement. This is the concrete witness that the inner leg reuses
the banked per-effect extractors (no new obligation). -/
theorem exerciseA_extract_inner_refines
    (lookup : DescriptorLookup)
    (compress : ℤ → ℤ → ℤ)
    (stepRoot : StepWitness → ℤ)
    (hstep :
      ∀ (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA),
        stepEmittedSat lookup sw st st' fa → fullActionStep st fa st')
    (holdPost post : RecChainedState) (inner : List FullActionA)
    (w : exerciseInnerTurnWitness lookup compress stepRoot holdPost post inner) :
    turnSpec holdPost inner post :=
  exercise_inner_emitted_refines_turnSpec lookup compress stepRoot hstep holdPost post inner w

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms exerciseHold_extract
#assert_axioms exerciseHold_extract_authority
#assert_axioms exerciseHold_extract_rejects_log_forge
#assert_axioms exerciseA_extract
#assert_axioms exerciseA_extract_inner_refines

end Dregg2.Circuit.WitnessExtractComposite
