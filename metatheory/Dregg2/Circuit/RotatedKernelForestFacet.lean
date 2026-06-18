/-
# Dregg2.Circuit.RotatedKernelForestFacet — the FAITHFUL WHOLE-TURN (forest) apex.

`RotatedKernelRefinementFacet` lands the FAITHFUL transfer apex on ONE step: a single committed transfer
whose authority leg is the deployed two-axis `authorizedFacetB` (NOT the toy `authorizedB`), discharged
in-circuit by the cap-open. This module LIFTS that single step to a WHOLE TURN — a LIST of effects — so
the light-client unfoolability headline holds for a faithful KERNEL TURN relation.

## The win over the single-step lowering

The single-step lowering `RotatedKernelRefinementFacet.dispatchArmFacet_to_dispatchArm` targets the TOY
`fullActionStep` (whose `.balanceA` arm is `BalanceMovementSpec`, gating on `authorizedB`); so it MUST
carry a toy-authority side-condition `htoy`. This module builds a FAITHFUL step relation
`fullActionStepFacet` whose `.balanceA` arm IS `BalanceMovementSpecFacet` (authority via
`authorizedFacetB`). The lowering `dispatchArmFacet_to_fullActionStepFacet` is then DIRECT — NO toy
side-condition — because the faithful arm's data IS exactly the faithful step's `.balanceA` arm.

## What is built (additive; nothing existing is mutated)

  1. **`fullActionStepFacet fcaps provided`** — the per-action declarative step IDENTICAL to
     `ActionDispatch.fullActionStep` EXCEPT the `.balanceA t a` arm is the FAITHFUL
     `BalanceMovementSpecFacet fcaps provided st t a st'`. Every OTHER arm is the exact `fullActionStep`
     arm (those effects' authority is not yet cut over — honest, additive). Defined as the one-arm swap
     `match fa with | .balanceA t a => BalanceMovementSpecFacet … | _ => fullActionStep st fa st'`;
     `fullActionStepFacet_balanceA` / `fullActionStepFacet_other` pin both branches.

  2. **`dispatchArmFacet_to_fullActionStepFacet`** — the KEY lowering: `dispatchArmFacet fcaps provided
     0 pre post` ⟹ `∃ fa, actionTag fa = 0 ∧ fullActionStepFacet fcaps provided pre fa post`, with NO
     toy side-condition (the witness `fa := .balanceA tr a` lands its faithful arm directly).

  3. **`turnSpecFacet fcaps provided := Spec.Turn.turnSpec (fullActionStepFacet fcaps provided)`** — the
     faithful turn relation (reusing the generic `Spec.Turn.turnSpec`).

  4. **`lightclient_turn_unfoolable_forest_facet`** — the FAITHFUL whole-turn apex. From a verifying
     batch (a `TurnDecodeChain` whose steps are the transfer effect) + the named floors + the carried
     per-effect rung at `dispatchArmFacet`, conclude a genuine DECLARATIVE faithful turn
     `Spec.Turn.turnSpec (fullActionStepFacet fcaps provided) start acts fin` whose endpoints commit to
     the published turn-level `(pre, post)`. The fold is `CircuitSoundness`'s NEW generic
     `turnDecodeChain_refines_turnSpec_gen` instantiated at the faithful arm/step. There is no separate
     faithful executor for the whole turn yet — the faithful executor IS this spec; that's correct and
     honest (the single-step faithful executor⟺spec is `execFaithful_iff_specFacet`).

  5. **`fullActionStepFacet_forest_rejects_unauthorized`** (the TOOTH) — a transfer step whose deployed
     authority is REJECTED (`authorizedFacetB fcaps provided tr = false`) cannot be the faithful
     `.balanceA` step at any position, so a faithful turn genuinely BITES.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the named carriers inherited through the
imported keystones. No `sorry`, no `native_decide`, no `:= True`, no fresh axiom. NEW names only.
-/
import Dregg2.Circuit.RotatedKernelRefinementFacet

namespace Dregg2.Circuit.RotatedKernelForestFacet

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (FullActionA execFullTurnA)
open Dregg2.Exec.FacetAuthority (FacetCaps AuthProvided)
open Dregg2.Circuit.Spec.BalanceMovement (BalanceMovementSpec)
open Dregg2.Circuit.ActionDispatch (fullActionStep actionTag)
open Dregg2.Circuit.DescriptorIR2 (Satisfied2)
open Dregg2.Circuit.CircuitSoundness
open Dregg2.Exec.FacetAuthority (authorizedFacetEffB)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2)
open Dregg2.Circuit.RotatedKernelRefinementFacet
  (BalanceMovementSpecFacet dispatchArmFacet transfer_descriptorRefines_facet_rejects_unauthorized
   EffAuthoritySourceCanon effAuthoritySourceCanon_authorizes)

set_option autoImplicit false

/-! ## §1 — `fullActionStepFacet`: the FAITHFUL per-action step (one-arm swap of `fullActionStep`).

Identical to `ActionDispatch.fullActionStep` EXCEPT the `.balanceA t a` arm is the FAITHFUL
`BalanceMovementSpecFacet fcaps provided st t a st'` (authority via the deployed two-axis
`authorizedFacetB`). Every other constructor falls through to the verbatim `fullActionStep` arm — those
effects' authority is not yet cut over (honest, additive). -/

/-- **`fullActionStepFacet fcaps provided st fa st'`** — the FAITHFUL per-action step: the `.balanceA`
arm is `BalanceMovementSpecFacet` (deployed authority), every other arm is the toy `fullActionStep`
arm verbatim (those leaves are unchanged — additive). -/
def fullActionStepFacet (fcaps : FacetCaps) (provided : AuthProvided)
    (st : RecChainedState) (fa : FullActionA) (st' : RecChainedState) : Prop :=
  match fa with
  | .balanceA t a => BalanceMovementSpecFacet fcaps provided st t a st'
  | _ => fullActionStep st fa st'

/-- The `.balanceA` arm of `fullActionStepFacet` IS the FAITHFUL spec (definitional, named). -/
theorem fullActionStepFacet_balanceA (fcaps : FacetCaps) (provided : AuthProvided)
    (st : RecChainedState) (t : Turn) (a : AssetId) (st' : RecChainedState) :
    fullActionStepFacet fcaps provided st (.balanceA t a) st'
      ↔ BalanceMovementSpecFacet fcaps provided st t a st' := Iff.rfl

/-! ## §2 — `dispatchArmFacet_to_fullActionStepFacet`: the KEY lowering (NO toy side-condition).

The win. The single-step lowering in `RotatedKernelRefinementFacet` targets the TOY `fullActionStep`
(`.balanceA` = `BalanceMovementSpec`, gating on `authorizedB`), so it carries a toy-authority
side-condition. Here the target is the FAITHFUL `fullActionStepFacet`, whose `.balanceA` arm IS
`BalanceMovementSpecFacet` — so the dispatcher's data lands the step DIRECTLY, no side-condition. -/

/-- **`dispatchArmFacet_to_fullActionStepFacet` — the faithful transfer arm IS a faithful step.** A
`dispatchArmFacet fcaps provided 0 pre post` (the faithful transfer arm: `∃ tr a,
BalanceMovementSpecFacet …`) entails `∃ fa, actionTag fa = 0 ∧ fullActionStepFacet fcaps provided pre
fa post` — with the witness `fa := .balanceA tr a`. NO toy-authority side-condition: the faithful
arm's `BalanceMovementSpecFacet` IS the `.balanceA` arm of `fullActionStepFacet`. -/
theorem dispatchArmFacet_to_fullActionStepFacet (fcaps : FacetCaps) (provided : AuthProvided)
    (e : EffectIdx) (pre post : RecChainedState)
    (he : e = 0)
    (h : dispatchArmFacet fcaps provided e pre post) :
    ∃ fa : FullActionA, actionTag fa = e ∧ fullActionStepFacet fcaps provided pre fa post := by
  subst he
  obtain ⟨tr, a, hfacet⟩ := h
  exact ⟨FullActionA.balanceA tr a, rfl, hfacet⟩

/-! ## §3 — the FAITHFUL turn relation (reuse the generic `Spec.Turn.turnSpec`). -/

/-- **`turnSpecFacet fcaps provided`** — the FAITHFUL whole-turn relation: the generic
`Spec.Turn.turnSpec` folded over the FAITHFUL per-action step `fullActionStepFacet`. A turn is an
all-or-nothing chain of faithful steps; the `.balanceA` steps gate on the deployed `authorizedFacetB`.
This IS the faithful turn executor (there is no separate executor — the single-step
`execFaithful_iff_specFacet` is the executor corner). -/
def turnSpecFacet (fcaps : FacetCaps) (provided : AuthProvided)
    (start : RecChainedState) (acts : List FullActionA) (fin : RecChainedState) : Prop :=
  Spec.Turn.turnSpec (fullActionStepFacet fcaps provided) start acts fin

/-! ## §4 — the FAITHFUL whole-turn (forest) apex.

Mirrors `CircuitSoundness.lightclient_turn_unfoolable_forest` exactly, swapping `dispatchArm →
dispatchArmFacet` and `fullActionStep`/`turnSpec → fullActionStepFacet`/`turnSpecFacet`. The fold is
the NEW generic `turnDecodeChain_refines_turnSpec_gen`, instantiated at the faithful arm/step with the
NO-side-condition lowering `dispatchArmFacet_to_fullActionStepFacet`. The conclusion is a DECLARATIVE
faithful turn (the faithful executor IS this spec). -/

/-- **`lightclient_turn_unfoolable_forest_facet` — the FAITHFUL WHOLE-TURN apex.** A verified turn (a
`TurnDecodeChain` whose every step's circuit is `Satisfied2`, decoded, seam-published) whose steps are
the transfer effect (`hidx0 : every step's effect index is the transfer tag 0`) + the turn-level
endpoint pinning (`TurnEndpoints`) + the named floors (`hCR` + the carried per-effect family
`hrefines` AT `dispatchArmFacet`) yields a GENUINE DECLARATIVE faithful turn `turnSpecFacet fcaps
provided start acts fin` whose ENDPOINTS commit to the published turn-level `(pre, post)`. The
authority leg of every transfer step is the deployed two-axis gate, discharged in-circuit by the
cap-open through `hrefines` — NO toy-authority side-condition (contrast the single-step
`dispatchArmFacet_to_dispatchArm`). The light client RAN NOTHING. -/
theorem lightclient_turn_unfoolable_forest_facet
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR hash)
    (fcaps : FacetCaps) (provided : AuthProvided)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (dispatchArmFacet fcaps provided e))
    {start fin : RecChainedState} (c : TurnDecodeChain hash S start fin)
    (hidx0 : ∀ d ∈ c.steps, ∃ e : EffectIdx, d.descr = R e ∧ e = 0)
    (te : TurnEndpoints hash S c) :
    ∃ (acts : List FullActionA) (s s' : RecChainedState),
      turnSpecFacet fcaps provided s acts s' ∧
      te.tp.pubPre = S.commit s.kernel te.tp.turn ∧
      te.tp.pubPost = S.commit s'.kernel te.tp.turn := by
  -- (1) the carried per-effect family discharges the per-step `dispatchArmFacet` over the whole chain.
  --     We reuse `stepsRefine_of_descriptorRefines` shape inline: each step's circuit accepts +
  --     faithful decode force `dispatchArmFacet e d.pre d.post`.
  -- The fold's arm is the transfer-tag-RESTRICTED faithful arm `e = 0 ∧ dispatchArmFacet …`; the
  -- `e = 0` (from `hidx0`) is what lets the lowering pin `actionTag (.balanceA …) = e`.
  have hsteps : ∀ d ∈ c.steps, ∃ e : EffectIdx, d.descr = R e ∧
      (e = 0 ∧ dispatchArmFacet fcaps provided e d.pre d.post) := by
    intro d hd
    obtain ⟨e, hde, he0⟩ := hidx0 d hd
    obtain ⟨minit, mfin, maddrs, t, hsat, _hpub⟩ := c.sat d hd
    refine ⟨e, hde, he0, ?_⟩
    have hsat' : Satisfied2 hash (R e) minit mfin maddrs t := hde ▸ hsat
    exact hrefines e hCR minit mfin maddrs t d.pc d.pre d.post hsat' d.decode
  -- (2) fold the per-step FAITHFUL arm along the threaded chain into the FAITHFUL `turnSpec`,
  --     using the NO-side-condition lowering `dispatchArmFacet_to_fullActionStepFacet` (steps are
  --     the transfer effect `e = 0`, so the lowering's `he` hypothesis is met per step).
  obtain ⟨acts, hturn⟩ :=
    turnDecodeChain_refines_turnSpec_gen hash S R
      (fun e pre post => e = 0 ∧ dispatchArmFacet fcaps provided e pre post)
      (fullActionStepFacet fcaps provided)
      (by
        -- the lowering hypothesis: each transfer-restricted faithful arm step entails its faithful
        -- step. The `e = 0` pins `actionTag (.balanceA …) = e`; the carried `BalanceMovementSpecFacet`
        -- IS the `.balanceA` arm of `fullActionStepFacet`, landed directly (no toy side-condition).
        intro e pre post harm
        obtain ⟨he0, tr, a, hfacet⟩ := harm
        subst he0
        exact ⟨FullActionA.balanceA tr a, by simp [actionTag], hfacet⟩)
      c hsteps
  -- (3) the published turn-level commitments ARE the endpoint commitments (derived; §8.1).
  obtain ⟨hpre, hpost⟩ := turnDecodeChain_endpoints_commit hash S c te
  exact ⟨acts, start, fin, hturn, hpre, hpost⟩

/-! ## §5 — the faithful authority TOOTH (the forest genuinely bites).

A transfer step whose deployed authority is REJECTED cannot be the faithful `.balanceA` step at any
position. Reuses `transfer_descriptorRefines_facet_rejects_unauthorized` (the single-step tooth). -/

/-- **`fullActionStepFacet_forest_rejects_unauthorized` (the TOOTH).** If the deployed two-axis gate
REJECTS the turn (`authorizedFacetB fcaps provided tr = false`), then NO `post` is a faithful
`.balanceA tr a` step at any position — the faithful authority leg genuinely bites inside the turn
fold (an unauthorized transfer cannot appear as a faithful step). -/
theorem fullActionStepFacet_forest_rejects_unauthorized (fcaps : FacetCaps) (provided : AuthProvided)
    (st : RecChainedState) (tr : Turn) (a : AssetId) (st' : RecChainedState)
    (hbad : Dregg2.Exec.FacetAuthority.authorizedFacetB fcaps provided tr = false) :
    ¬ fullActionStepFacet fcaps provided st (.balanceA tr a) st' := by
  rw [fullActionStepFacet_balanceA]
  exact transfer_descriptorRefines_facet_rejects_unauthorized fcaps provided st tr a st' hbad

/-! ## §6 — the PARAMETRIC per-effect authority arm: each fan-out step's authority bit is FORCED.

The transfer arm above discharges `authorizedFacetB` (= `authorizedFacetEffB … (turnEffectBit _) =
EFF_TRANSFER`) from the transfer cap-open. The 6 FAN-OUT cap-effects
(introduce/delegate/grantCap/revoke/refreshDelegation/revokeCapability) ride DIFFERENT effect bits and
do NOT collapse to `authorizedFacetB`; their per-step authority is `authorizedFacetEffB caps provided
(1 <<< n)` at the effect's OWN bit `n`. `stepAuthorityFacetEff` is the parametric authority arm: for ANY
fan-out effect at bit `n`, its step authority is FORCED from that step's SLIM canonical cap-open
`EffAuthoritySourceCanon` (the descriptor `Rfix <tag>` now ranges over — `effAuthoritySourceCanon_authorizes`),
NOT carried, NOT riding the toy gate, and with the deployed faithfulness DISCHARGED from the canonical leaf
construction (no assumed `DeployedFaithfulEff` field). The transfer arm is the `n = EFF_TRANSFER` instance;
this is the whole-turn-level analog, parametric over the fan-out effects. -/

/-- **`stepAuthorityFacetEff` — a fan-out step's two-axis authority is FORCED at its OWN effect bit.**
For any fan-out effect at bit `n`, the deployed `authorizedFacetEffB caps provided (1 <<< n) tr` PASSES,
discharged from that step's SLIM in-circuit cap-open `EffAuthoritySourceCanon … base name n` (the descriptor
the re-keyed `Rfix <tag>` ranges over) — faithfulness CONSTRUCTED via the canonical leaf set, NOT a carried
`hfaith` field. This is the per-effect authority arm of the whole-turn fold: each cap-effect step's authority
bit is forced in-circuit at its genuine effect-kind, no longer riding the toy gate. (The transfer step is the
`base := transferV3, n := EFF_TRANSFER` instance.) -/
theorem stepAuthorityFacetEff (hash : List ℤ → ℤ) (caps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Turn) (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (src0 : EffAuthoritySourceCanon hash caps provided pre tr base name n) :
    authorizedFacetEffB caps provided (1 <<< n) tr = true :=
  effAuthoritySourceCanon_authorizes hash caps provided pre tr base name n src0

/-- **`stepAuthorityFacetEff_rejects_wrong_facet` (the parametric authority TOOTH).** If the deployed
general gate REJECTS the step at its effect bit (`authorizedFacetEffB caps provided (1 <<< n) tr =
false`), then NO `EffAuthoritySource` for that fan-out effect at bit `n` can exist — the per-effect
authority leg genuinely bites at the whole-turn level (a wrong-facet / wrong-tier / missing-cap step
cannot be discharged). The both-polarity counterpart of `stepAuthorityFacetEff`, parametric over the 6
fan-out effects. -/
theorem stepAuthorityFacetEff_rejects_wrong_facet (hash : List ℤ → ℤ) (caps : FacetCaps)
    (provided : AuthProvided) (pre : RecChainedState) (tr : Turn)
    (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hbad : authorizedFacetEffB caps provided (1 <<< n) tr = false)
    (src0 : EffAuthoritySourceCanon hash caps provided pre tr base name n) : False := by
  have hgood : authorizedFacetEffB caps provided (1 <<< n) tr = true :=
    effAuthoritySourceCanon_authorizes hash caps provided pre tr base name n src0
  rw [hbad] at hgood
  exact Bool.noConfusion hgood

/-! ## §7 — Axiom hygiene. -/

#assert_axioms fullActionStepFacet_balanceA
#assert_axioms dispatchArmFacet_to_fullActionStepFacet
#assert_axioms lightclient_turn_unfoolable_forest_facet
#assert_axioms fullActionStepFacet_forest_rejects_unauthorized
#assert_axioms stepAuthorityFacetEff
#assert_axioms stepAuthorityFacetEff_rejects_wrong_facet

end Dregg2.Circuit.RotatedKernelForestFacet
