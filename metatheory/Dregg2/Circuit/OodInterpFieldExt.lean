import Dregg2.Circuit.FieldIntegerLift
import Mathlib.FieldTheory.Finite.GaloisField
import Dregg2.Tactics

/-!
# `Dregg2.Circuit.OodInterpFieldExt` — the QUARTIC-EXTENSION OOD landing, placed where the DEPLOYED
chain can actually consume it.

## Why this module exists (a RELOCATION, stated plainly)

The extension-typed OOD landing was first authored in `ExtChallengeOodSites`, and the deployed
quartic extension `BB4` in `FriDeployedExtCode`.  Both of those modules sit BELOW
`DeployedTraceExtract` in the import DAG (`ExtChallengeOodSites → OodExtChallengeLayout →
FriDecodedDomainRebase → FriDecodedTraceWitness → DeployedTraceExtract`), so the module that DEFINES
the deployed extraction bundle `DeployedTraceExtract.DeployedTraceDecode` can never name its own
correction.  That is the ordering problem the cutover discipline calls out.

The fix is a relocation, not an exception: the three things the deployed chain needs — the
coefficient lift `liftPoly`, the deployed challenge field `BB4`, and the extension-typed OOD bridge
`OodInterpFExt` — are DEFINED here, upstream of everything that consumes them, and re-exported by
their former homes so that no name downstream moves and no statement is duplicated.  There is
exactly ONE `liftPoly`, ONE `BB4`, ONE `OodInterpFExt` in the tree.

## What is retyped, and why it is not conservative to leave it base-typed

The deployed FRI algebra challenges (constraint-RLC `α`, out-of-domain `ζ`, every commit-phase fold
`β`) are QUARTIC-EXTENSION elements — `ExtFieldChallenge.lean:8-15`.  Modelling them as single
BabyBear felts is not a restriction of the deployed equation, it is a DIFFERENT equation:

* base witnesses LIFT (`oodInterpFExt_of_oodInterpF`), so the extension-typed hypothesis is strictly
  WEAKER — nothing the base-typed bridge delivered is lost;
* extension witnesses do NOT descend, and the base-typed equation cannot even EXPRESS the deployed
  right-hand side (`OodExtChallengeLayout.extLayout_value_beyond_base`,
  `ExtChallengeOodSites.extOod_rhs_beyond_base`, both fired at the real deployed descriptor
  `transferV3`);
* the tempting rescue is unavailable: `OodExtChallengeLayout.coordFunctional_not_multiplicative`
  proves NO basis-coordinate functional of a nontrivial extension is multiplicative, fired at the
  deployed quartic basis (`bb4_lane_not_multiplicative`).

So a consumer left on `OodInterpF` is not being conservative; it is standing on a statement that may
be about nothing.  `mainAirAcceptF_of_oodInterpF_via_ext` records the payoff: weaker hypothesis,
IDENTICAL base-field conclusion.

## What this module does NOT touch

The opened VALUES (`TableOpening.constraintEval` / `quotientAtZeta` / `vanishingAtZeta : ℤ`) are
still one felt each — that is the felt-width wound
(`docs/WOUND-felt-width-boundaries-2026-07-19.md`), named and not repaired here.  The FRI soundness
floor is unchanged: retyping challenges moves ε denominators, it discharges no FRI/STARK assumption.

Sorry-free; no `axiom`; every keystone `#assert_all_clean`-checked.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Circuit.OodInterpFieldExt

open Polynomial
open Dregg2.Circuit.BabyBearFriField (BabyBear babyBearP)
open Dregg2.Circuit.DescriptorIR2 (VmTrace EffectVmDescriptor2 VmConstraint2 envAt)
open Dregg2.Circuit.AirChecksSatisfied (MainAirAcceptF isArith arithResidual dArith tHonest)
open Dregg2.Circuit.TraceColumnInterp
  (constraintPoly domainSize rowPt constraintPoly_eval_eq_arithResidual colPoly)
open Dregg2.Circuit.OodQuotientConsistency (exceptionalSet ood_consistency)
open Dregg2.Circuit.FieldIntegerLift
  (OodInterpF vanishingPoly vanishingPoly_eval_rowPt babyBear_cast_eq_zero_iff)

/-! ## §1 — THE COEFFICIENT LIFT.

The committed trace is BASE-field data, so `constraintPoly` and `vanishingPoly` are genuinely
`Polynomial BabyBear`; what the deployed verifier moves into the extension is the POINT they are read
at and the quotient/challenge algebra around it.  So the honest retyping embeds their COEFFICIENTS
and keeps the objects themselves. -/

section Lift

variable {E : Type*} [Field E] [Algebra BabyBear E]

/-- The coefficient lift of a trace-derived polynomial into the challenge extension — the deployed
`Val → Challenge` embedding applied to a committed polynomial. -/
noncomputable def liftPoly (E : Type*) [Field E] [Algebra BabyBear E]
    (p : Polynomial BabyBear) : Polynomial E :=
  p.map (algebraMap BabyBear E)

/-- Reading a lifted polynomial at an EMBEDDED base point is the embedding of the base reading —
the sense in which the lift is faithful on the base points. -/
theorem liftPoly_eval_base (p : Polynomial BabyBear) (x : BabyBear) :
    (liftPoly E p).eval (algebraMap BabyBear E x) = algebraMap BabyBear E (p.eval x) := by
  rw [liftPoly, eval_map, eval₂_at_apply]

@[simp] theorem liftPoly_zero : liftPoly E (0 : Polynomial BabyBear) = 0 := by
  simp [liftPoly]

theorem liftPoly_eq_zero_iff {p : Polynomial BabyBear} : liftPoly E p = 0 ↔ p = 0 := by
  rw [liftPoly, Polynomial.map_eq_zero_iff (algebraMap BabyBear E).injective]

@[simp] theorem liftPoly_sub (p q : Polynomial BabyBear) :
    liftPoly E (p - q) = liftPoly E p - liftPoly E q := by
  simp [liftPoly, Polynomial.map_sub]

@[simp] theorem liftPoly_mul (p q : Polynomial BabyBear) :
    liftPoly E (p * q) = liftPoly E p * liftPoly E q := by
  simp [liftPoly, Polynomial.map_mul]

/-- **Non-exceptionality LIFTS** — the Fiat–Shamir side condition is not lost by the retyping.
(Both poles are handled: the zero polynomial has an EMPTY exceptional set on both sides, and a
nonzero base residual with a nonzero value at `x` lifts to a nonzero extension residual with a
nonzero value at `φ x`.) -/
theorem notMem_exceptionalSet_lift [DecidableEq E] {p : Polynomial BabyBear} {x : BabyBear}
    (h : x ∉ exceptionalSet p) :
    algebraMap BabyBear E x ∉ exceptionalSet (liftPoly E p) := by
  classical
  intro hmem
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [liftPoly_zero, exceptionalSet] at hmem
    simp at hmem
  · have hne : liftPoly E p ≠ 0 := fun h0 => hp0 (liftPoly_eq_zero_iff.mp h0)
    rw [exceptionalSet, Multiset.mem_toFinset, mem_roots hne] at hmem
    have hroot : (liftPoly E p).eval (algebraMap BabyBear E x) = 0 := hmem
    rw [liftPoly_eval_base] at hroot
    have hx : p.eval x = 0 := (algebraMap BabyBear E).injective (by rw [hroot, map_zero])
    exact h (by rw [exceptionalSet, Multiset.mem_toFinset, mem_roots hp0]; exact hx)

end Lift

/-! ## §2 — THE DEPLOYED CHALLENGE FIELD.

The deployed `Challenge` is `BinomialExtensionField<BabyBear, 4>` = `BabyBear[X]/(X^4 − 11)`
(`p3-baby-bear/src/baby_bear.rs:66`, `W = 11`; `ExtFieldChallenge.deployed_extDeg_four`).  The
irreducibility of `X^4 − 11` over BabyBear is a numeric fact this tree does not prove — and does not
need: every degree-4 extension of BabyBear is the SAME field up to a BabyBear-algebra isomorphism
(`deployed_quartic_ext_canonical`), so the deployed quartic extension IS (isomorphic to)
`GaloisField p 4`, which Mathlib supplies as a genuine `Field` with a genuine `Algebra BabyBear`
structure. -/

section Deployed

/-- **The deployed quartic extension**, as a Lean field. -/
abbrev BB4 : Type := GaloisField babyBearP 4

noncomputable instance instDecidableEqBB4 : DecidableEq BB4 := Classical.decEq _
noncomputable instance instFintypeBB4 : Fintype BB4 := Fintype.ofFinite _

/-- `[BB4 : BabyBear] = 4` — the deployed `extDeg`. -/
theorem bb4_finrank : Module.finrank BabyBear BB4 = 4 :=
  GaloisField.finrank babyBearP (by norm_num)

/-- `|BB4| = p^4 ≈ 2^124` — the deployed challenge space. -/
theorem bb4_card : Fintype.card BB4 = babyBearP ^ 4 := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card babyBearP 4 (by norm_num)

/-- **⚑ CANONICITY — this IS the deployed extension.** Any field that is a BabyBear-algebra of
cardinality `p^4` — in particular the deployed `BabyBear[X]/(X^4 − 11)`, whatever presentation is
used — is BabyBear-algebra isomorphic to `BB4`.  So nothing below depends on the binomial
presentation. -/
theorem deployed_quartic_ext_canonical (L : Type) [Field L] [Fintype L] [Algebra BabyBear L]
    (hcard : Fintype.card L = babyBearP ^ 4) : Nonempty (L ≃ₐ[BabyBear] BB4) :=
  ⟨FiniteField.algEquivOfCardEq babyBearP (by rw [hcard, bb4_card])⟩

/-- A basis of the deployed extension over BabyBear — the four `Val` lanes of a `Challenge`. -/
noncomputable def bb4Basis : Module.Basis (Fin 4) BabyBear BB4 :=
  Module.finBasisOfFinrankEq BabyBear BB4 bb4_finrank

/-- If `[E:F] > 1` then `algebraMap` is not surjective: were it, it would be an `F`-linear
equivalence and force `[E:F] = 1`. -/
theorem exists_not_mem_range_algebraMap {F E : Type*} [Field F] [Field E] [Algebra F E]
    (h : 1 < Module.finrank F E) : ∃ x : E, x ∉ Set.range (algebraMap F E) := by
  by_contra hcon
  push_neg at hcon
  have hinj : Function.Injective (Algebra.linearMap F E) := fun a b hab =>
    (algebraMap F E).injective hab
  have hsurj : Function.Surjective (Algebra.linearMap F E) := by
    intro x
    obtain ⟨y, hy⟩ := hcon x
    exact ⟨y, hy⟩
  have hrank : Module.finrank F F = Module.finrank F E :=
    (LinearEquiv.ofBijective (Algebra.linearMap F E) ⟨hinj, hsurj⟩).finrank_eq
  rw [Module.finrank_self] at hrank
  omega

/-- **A genuine `Challenge` outside the base field.** This is the regime the whole retyping is about:
the deployed verifier's `ζ`/`α`/`β` land here, and no base-typed statement can name this value. -/
theorem exists_nonbase_bb4 : ∃ ξ : BB4, ξ ∉ Set.range (algebraMap BabyBear BB4) :=
  exists_not_mem_range_algebraMap (F := BabyBear) (E := BB4) (by rw [bb4_finrank]; norm_num)

end Deployed

/-! ## §3 — ⚑ THE EXTENSION-TYPED OOD BRIDGE.

`FieldIntegerLift.OodInterpF` binds `ζ : BabyBear`, `Zp qp : Polynomial BabyBear`; `verifyAlgo`'s
opened `vanishingAtZeta`/`quotientAtZeta` are, in the deployed verifier, `Challenge` values
(`vendor/plonky3-fri-82cfad73/src/verifier.rs:623-640`).  LOAD-BEARING: this bridge is the OOD
landing every `MainAirAcceptF` chain in the tree bottoms out at.

`OodInterpFExt` is the same bridge with the CHALLENGE and the QUOTIENT/VANISHING polynomials drawn
from the extension.  The committed constraint polynomial stays a `Polynomial BabyBear` embedded
coefficientwise (the trace IS base-field data — that is not the wound). -/

section OodInterpExt

variable {E : Type*} [Field E] [Algebra BabyBear E] [DecidableEq E]

/-- **`OodInterpF` AT THE DEPLOYED CHALLENGE TYPING.** `ζ : E`, and the vanishing/quotient
polynomials are genuinely extension-coefficiented (the deployed `vanishingAtZeta`/`quotientAtZeta`
openings are `Challenge`).  `hZrow` is the domain-geometry axis, now read at the EMBEDDED row points
— the trace rows are base-field points, and they must remain roots of the extension-typed vanisher. -/
structure OodInterpFExt (E : Type*) [Field E] [Algebra BabyBear E] [DecidableEq E]
    (d : EffectVmDescriptor2) (t : VmTrace) where
  hcap : t.rows.length ≤ domainSize
  ζ : E
  Zp : Polynomial E
  qp : VmConstraint2 → Polynomial E
  hZrow : ∀ i < t.rows.length, Zp.eval (algebraMap BabyBear E (rowPt i)) = 0
  hood : ∀ c ∈ d.constraints, isArith c →
    (liftPoly E (constraintPoly d t c)).eval ζ = Zp.eval ζ * (qp c).eval ζ
  hnonexc : ∀ c ∈ d.constraints, isArith c →
    ζ ∉ exceptionalSet (liftPoly E (constraintPoly d t c) - Zp * qp c)

/-- **⚑ THE PAYOFF — the extension-typed OOD bridge still forces the BASE-field AIR conclusion.**
The Schwartz–Zippel step runs over `E`, yielding the polynomial identity `C.map φ = Zp · qp` in
`Polynomial E`; evaluating at the EMBEDDED row points (where `Zp` vanishes by `hZrow`) and using
injectivity of `φ` lands the base-field row vanishing that `MainAirAcceptF` is stated with.
Conclusion IDENTICAL to `ood_forces_mainAirAccept_field`; hypothesis strictly weaker (§3.1). -/
theorem ood_forces_mainAirAccept_field_ext {d : EffectVmDescriptor2} {t : VmTrace}
    (I : OodInterpFExt E d t) : MainAirAcceptF d t := by
  intro i hi c hc
  rw [← babyBear_cast_eq_zero_iff]
  by_cases ha : isArith c
  · have hCq : liftPoly E (constraintPoly d t c) = I.Zp * I.qp c :=
      ood_consistency _ I.Zp (I.qp c) I.ζ (I.hood c hc ha) (I.hnonexc c hc ha)
    have hev := congrArg (Polynomial.eval (algebraMap BabyBear E (rowPt i))) hCq
    rw [liftPoly_eval_base, eval_mul, I.hZrow i hi, zero_mul] at hev
    have hz : (constraintPoly d t c).eval (rowPt i) = 0 :=
      (algebraMap BabyBear E).injective (by rw [hev, map_zero])
    rw [← constraintPoly_eval_eq_arithResidual d t I.hcap i hi c ha]
    exact hz
  · cases c <;> simp_all [isArith, arithResidual]

/-- **The residual form at the extension typing** — the exact analogue of
`FieldIntegerLift.ood_forces_mainAirAccept_field_of_residuals` with the committed domain vanisher
supplied (embedded coefficientwise) and the challenge drawn from `E`. -/
theorem ood_forces_mainAirAccept_field_of_residuals_ext (E : Type*) [Field E] [Algebra BabyBear E]
    [DecidableEq E] (d : EffectVmDescriptor2) (t : VmTrace)
    (hcap : t.rows.length ≤ domainSize) (ζ : E) (qp : VmConstraint2 → Polynomial E)
    (hood : ∀ c ∈ d.constraints, isArith c →
        (liftPoly E (constraintPoly d t c)).eval ζ
          = (liftPoly E (vanishingPoly t)).eval ζ * (qp c).eval ζ)
    (hnonexc : ∀ c ∈ d.constraints, isArith c →
        ζ ∉ exceptionalSet
          (liftPoly E (constraintPoly d t c) - liftPoly E (vanishingPoly t) * qp c)) :
    MainAirAcceptF d t :=
  ood_forces_mainAirAccept_field_ext
    { hcap := hcap, ζ := ζ, Zp := liftPoly E (vanishingPoly t), qp := qp
    , hZrow := fun i hi => by
        rw [liftPoly_eval_base, vanishingPoly_eval_rowPt t i hi, map_zero]
    , hood := hood, hnonexc := hnonexc }

/-! ### §3.1 — THE TRUE RELATION: base witnesses LIFT, so the retyping loses nothing. -/

/-- **The base-typed OOD bridge LIFTS.** Every `OodInterpF` witness embeds into an `OodInterpFExt`
witness along `algebraMap BabyBear E`: the domain axis, the OOD identity, and the non-exceptionality
side condition all transport.  So `OodInterpFExt` is a strictly WEAKER demand — which is the point,
because the deployed verifier supplies extension witnesses and base ones it does not supply at all. -/
noncomputable def oodInterpFExt_of_oodInterpF {d : EffectVmDescriptor2} {t : VmTrace}
    (I : OodInterpF d t) : OodInterpFExt E d t where
  hcap := I.hcap
  ζ := algebraMap BabyBear E I.ζ
  Zp := liftPoly E I.Zp
  qp := fun c => liftPoly E (I.qp c)
  hZrow := fun i hi => by rw [liftPoly_eval_base, I.hZrow i hi, map_zero]
  hood := by
    intro c hc ha
    show (liftPoly E (constraintPoly d t c)).eval (algebraMap BabyBear E I.ζ)
      = (liftPoly E I.Zp).eval (algebraMap BabyBear E I.ζ)
        * (liftPoly E (I.qp c)).eval (algebraMap BabyBear E I.ζ)
    rw [liftPoly_eval_base, liftPoly_eval_base, liftPoly_eval_base, ← map_mul, I.hood c hc ha]
  hnonexc := by
    intro c hc ha
    show algebraMap BabyBear E I.ζ ∉ exceptionalSet
      (liftPoly E (constraintPoly d t c) - liftPoly E I.Zp * liftPoly E (I.qp c))
    have hrw : liftPoly E (constraintPoly d t c) - liftPoly E I.Zp * liftPoly E (I.qp c)
        = liftPoly E (constraintPoly d t c - I.Zp * I.qp c) := by
      rw [liftPoly_sub, liftPoly_mul]
    rw [hrw]
    exact notMem_exceptionalSet_lift (I.hnonexc c hc ha)

/-- **The extension route SUBSUMES the base route.** Every base-typed `OodInterpF` witness yields
`MainAirAcceptF` *through* the extension-typed landing at the DEPLOYED quartic extension `BB4` — so
nothing that the base-typed bridge delivered is lost by moving the deployed chain onto the extension
typing. -/
theorem mainAirAcceptF_of_oodInterpF_via_ext {d : EffectVmDescriptor2} {t : VmTrace}
    (I : OodInterpF d t) : MainAirAcceptF d t :=
  ood_forces_mainAirAccept_field_ext (E := BB4) (oodInterpFExt_of_oodInterpF I)

end OodInterpExt

/-! ## §4 — ⚑ NON-EMPTINESS: the extension-typed bridge is INHABITED at a genuinely NON-BASE
challenge, and every challenge-dependent HYPOTHESIS is carried, not just the conclusion.

The methodological correction this campaign paid for: an inhabitation witness that records only the
CONCLUSION is weaker than it looks — the conclusion may be reachable by other means while the
hypothesis bundle is unsatisfiable.  `fire_oodInterpFExt_nonbase` below is stated in the
`fire_kprime_composeExt_nonbase` shape: the OOD point is exhibited OUTSIDE `image(BabyBear)`, and
BOTH challenge-dependent conjuncts (`hood` and `hnonexc`) are asserted AT that point, alongside the
delivered `MainAirAcceptF`. -/

section Fire

/-- The honest toy trace's column-0 interpolant is the ZERO polynomial (its two rows are zero, and
`Lagrange.interpolate` of the zero value family is `0`). -/
theorem colPoly_tHonest_zero : colPoly tHonest 0 = 0 := by
  show Lagrange.interpolate (Finset.range tHonest.rows.length) rowPt
      (fun i => (((tHonest.rows.getD i Dregg2.Circuit.DescriptorIR2.zeroAsg 0 : ℤ) : BabyBear))) = 0
  rw [Lagrange.interpolate_apply]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hv : (((tHonest.rows.getD i Dregg2.Circuit.DescriptorIR2.zeroAsg 0 : ℤ) : BabyBear)) = 0 := by
    rcases i with _ | _ | i <;>
      simp [tHonest, Dregg2.Circuit.AirChecksSatisfied.zRow,
        Dregg2.Circuit.DescriptorIR2.zeroAsg, List.getD]
  rw [hv, map_zero, zero_mul]

/-- Hence the honest toy descriptor's single arithmetic constraint has the ZERO constraint
polynomial on that trace. -/
theorem constraintPoly_dArith_tHonest_zero :
    constraintPoly dArith tHonest (.base (.gate (.var 0))) = 0 := by
  show (1 - Dregg2.Circuit.TraceColumnInterp.lastSelector tHonest)
      * Dregg2.Circuit.TraceColumnInterp.exprPoly tHonest (.var 0) = 0
  show (1 - Dregg2.Circuit.TraceColumnInterp.lastSelector tHonest) * colPoly tHonest 0 = 0
  rw [colPoly_tHonest_zero, mul_zero]

/-- **⚑ FIRE — the extension-typed OOD bridge is INHABITED at a genuinely NON-BASE challenge, and
DELIVERS.** Every challenge-dependent hypothesis of `ood_forces_mainAirAccept_field_of_residuals_ext`
is recorded at the exhibited point, so this cannot be satisfied by a vacuous witness: the OOD point
is drawn from `BB4 ∖ image(BabyBear)` (so it is NOT a lifted base witness — the regime `no descent`
is about), the per-constraint OOD identity HOLDS there, the Fiat–Shamir non-exceptionality side
condition HOLDS there, and the bridge produces the real base-field per-row AIR acceptance
`MainAirAcceptF dArith tHonest`. -/
theorem fire_oodInterpFExt_nonbase :
    ∃ ζ : BB4,
      ζ ∉ Set.range (algebraMap BabyBear BB4) ∧
      (∀ c ∈ dArith.constraints, isArith c →
          (liftPoly BB4 (constraintPoly dArith tHonest c)).eval ζ
            = (liftPoly BB4 (vanishingPoly tHonest)).eval ζ * (0 : Polynomial BB4).eval ζ) ∧
      (∀ c ∈ dArith.constraints, isArith c →
          ζ ∉ exceptionalSet (liftPoly BB4 (constraintPoly dArith tHonest c)
            - liftPoly BB4 (vanishingPoly tHonest) * 0)) ∧
      MainAirAcceptF dArith tHonest := by
  obtain ⟨ξ, hξ⟩ := exists_nonbase_bb4
  have hood : ∀ c ∈ dArith.constraints, isArith c →
      (liftPoly BB4 (constraintPoly dArith tHonest c)).eval ξ
        = (liftPoly BB4 (vanishingPoly tHonest)).eval ξ * (0 : Polynomial BB4).eval ξ := by
    intro c hc _
    simp only [dArith, List.mem_singleton] at hc
    subst hc
    rw [constraintPoly_dArith_tHonest_zero]
    simp
  have hnonexc : ∀ c ∈ dArith.constraints, isArith c →
      ξ ∉ exceptionalSet (liftPoly BB4 (constraintPoly dArith tHonest c)
        - liftPoly BB4 (vanishingPoly tHonest) * 0) := by
    intro c hc _
    simp only [dArith, List.mem_singleton] at hc
    subst hc
    rw [constraintPoly_dArith_tHonest_zero]
    simp [liftPoly, exceptionalSet]
  refine ⟨ξ, hξ, hood, hnonexc, ?_⟩
  exact ood_forces_mainAirAccept_field_of_residuals_ext BB4 dArith tHonest
    (by simp [tHonest, domainSize]) ξ (fun _ => 0) hood hnonexc

/-- **⚑ THE WITNESS IS NOT A LIFTED BASE WITNESS.** The exhibited OOD point is attained by no
`algebraMap` image whatsoever, so `fire_oodInterpFExt_nonbase` genuinely inhabits the extension
regime rather than re-reading a base-typed witness in extension clothing. -/
theorem fire_oodInterpFExt_nonbase_not_lifted :
    ∃ ζ : BB4, (∀ z : BabyBear, ζ ≠ algebraMap BabyBear BB4 z) ∧ MainAirAcceptF dArith tHonest := by
  obtain ⟨ζ, hζ, -, -, hair⟩ := fire_oodInterpFExt_nonbase
  exact ⟨ζ, fun z hz => hζ ⟨z, hz.symm⟩, hair⟩

end Fire

/-! ## §5 — Axiom hygiene. -/

#assert_all_clean [
  liftPoly_eval_base,
  liftPoly_eq_zero_iff,
  liftPoly_sub,
  liftPoly_mul,
  notMem_exceptionalSet_lift
]

#assert_all_clean [
  bb4_finrank,
  bb4_card,
  deployed_quartic_ext_canonical,
  bb4Basis,
  exists_not_mem_range_algebraMap,
  exists_nonbase_bb4
]

#assert_all_clean [
  ood_forces_mainAirAccept_field_ext,
  ood_forces_mainAirAccept_field_of_residuals_ext,
  oodInterpFExt_of_oodInterpF,
  mainAirAcceptF_of_oodInterpF_via_ext
]

#assert_all_clean [
  colPoly_tHonest_zero,
  constraintPoly_dArith_tHonest_zero,
  fire_oodInterpFExt_nonbase,
  fire_oodInterpFExt_nonbase_not_lifted
]

end Dregg2.Circuit.OodInterpFieldExt
