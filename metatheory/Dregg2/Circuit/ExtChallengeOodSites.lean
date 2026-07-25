/-
# `Dregg2.Circuit.ExtChallengeOodSites` — the QUARTIC-EXTENSION challenge typing at the remaining
OOD/RLC sites, and the EXACT relation to the base-typed forms.

## STATUS OF THIS FILE (read this before trusting any header claim below)

Sites healed here, all ADDITIVELY (no landed definition is edited):

  * §1 `FieldIntegerLift.OodInterpF` (`:70-79`) / `ood_forces_mainAirAccept_field_of_residuals`
        (`:139`) — `ζ : BabyBear`, `Zp qp : Polynomial BabyBear`. LOAD-BEARING (it is the OOD
        landing every `MainAirAcceptF` chain in the tree bottoms out at). Counterpart
        `OodInterpFExt` / `ood_forces_mainAirAccept_field_ext` /
        `ood_forces_mainAirAccept_field_of_residuals_ext`.
  * §2 `KprimeCompose.constraintResidualAtZeta` (`:62-67`) / `kprime_compose` /
        `kprime_compose_of_tableIdentity` — `ζ α : BabyBear`. LOAD-BEARING (the composed K′ chain).
        Counterpart `constraintResidualAtZetaExt` / `kprime_composeExt` /
        `kprime_compose_of_tableIdentityExt`.
  * §3 `OodColumnLayout` (`:96-283`) — the ∀-descriptor modeler at `ζ Λ : BabyBear`. The GENERIC
        half was already repaired by `OodExtChallengeLayout` §2; what was missing is the DEPLOYED
        `transferV3` half (`:249-288`), supplied here.
  * §4 `OodSoundnessGame` `oodNonExc_soundness_error_babybear` (`:107`) /
        `rlc_debatch_error_babybear` (`:223`) — priced at `|BabyBear| = 2013265921`. VERDICT:
        UNFAITHFUL (they are the field-generic game at `F = BabyBear`, so they price a different
        object and do NOT bound the deployed event), but CONSERVATIVE IN THE NUMBER (`deg/p^4 <
        deg/p`, so nothing was reported too small). Both halves proved in §4; restated at
        `|Challenge| = |BB4| = 2013265921^4`.
  * §5 `RlcRomBound.hLam_clause_bounded_babybear` (`:298-317`) — the deployed Λ-clause ε, likewise
        priced at `|BabyBear|`. Restated at `|BB4|`, at the SAME acceptance event.

NOT done here, and named so nobody reads a closure into this file:

  * The deployed `SingleAirOpening.alpha`/`TableOpening.*` RECORD FIELDS are still ONE felt. §5
    types the declared challenge as a `BB4` element, which is the faithful typing of the STATEMENT;
    that the deployed serialized record carries four lanes is the felt-width wound
    (`docs/WOUND-felt-width-boundaries-2026-07-19.md`), untouched.
  * The FRI soundness floor is unchanged. Retyping challenges moves ε denominators; it discharges
    no FRI/STARK assumption.
  * `LogUpColumnLayout.logupChallenge` is handled in the companion file, not here.

Sorry-free; no `axiom`; no carrier; every keystone `#assert_axioms`-checked.

## ⚑ THE TRUE RELATION FOUND (investigated, not assumed)

Identical in shape to `OodExtChallengeLayout`'s finding, now at these five sites:

  * **Base witnesses LIFT, completely** (`oodInterpFExt_of_oodInterpF`,
    `constraintResidualAtZetaExt_lift`): everything transports along `algebraMap BabyBear E`,
    including both non-exceptionality side conditions. So the extension-typed hypothesis is
    strictly WEAKER.
  * **Extension witnesses do NOT descend, and the base equation cannot EXPRESS the deployed value**
    (`extOod_rhs_beyond_base`, `extOod_rhs_not_lifted`, `extResidual_beyond_base`): with a genuinely
    `Challenge`-valued quotient opening — which is exactly what the deployed `quotient : Challenge`
    is — the OOD identity's right-hand side `Z(ζ)·q(ζ)` lands OUTSIDE `Set.range (algebraMap)`,
    while every base-typed right-hand side is confined to it. Fired at the DEPLOYED `transferV3`.
  * **The consumer survives**: the extension-typed hypothesis still forces the BASE-field
    conclusion `MainAirAcceptF d t`, unchanged (`ood_forces_mainAirAccept_field_ext`,
    `kprime_composeExt`). Weaker hypothesis, identical conclusion.
  * **The ε moves in the FAVOURABLE direction and the base number was strictly looser**
    (`ext_pricing_strictly_tighter`): the faithful denominator is `p^4`, not `p`; the base-typed
    ε is a valid upper bound (so nothing was UNSOUND) but is `p^3`-times larger than the truth.

## NON-VACUITY

`fire_kprime_composeExt_nonbase` runs the whole §2 chain with BOTH challenges drawn from
`BB4 ∖ image(BabyBear)` and produces a real `MainAirAcceptF dArith tHonest`.
`fire_extOod_rhs_beyond_base_transferV3` fires §1's separation at the REAL deployed descriptor.
`fire_declaredAlphaExceptional_nonbase` exhibits a CONCRETE `BatchProofData BB4` declaring a
genuinely non-base challenge that IS exceptional, so §5's bounded event is not empty.
-/
import Dregg2.Circuit.OodExtChallengeLayout
import Dregg2.Circuit.KprimeCompose
import Dregg2.Circuit.RlcRomBound

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Circuit.ExtChallengeOodSites

open Polynomial
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.DescriptorIR2 (VmTrace EffectVmDescriptor2 VmConstraint2 envAt)
open Dregg2.Circuit.AirChecksSatisfied
  (MainAirAcceptF isArith arithResidual dArith tHonest)
open Dregg2.Circuit.TraceColumnInterp
  (constraintPoly domainSize rowPt constraintPoly_eval_eq_arithResidual)
open Dregg2.Circuit.FieldIntegerLift
  (vanishingPoly vanishingPoly_eval_rowPt vanishingPoly_ne_zero babyBear_cast_eq_zero_iff
   OodInterpF)
open Dregg2.Circuit.OodQuotientConsistency
  (exceptionalSet ood_consistency rlcResidualPoly rlc_batch_split_of_combined)
open Dregg2.Circuit.OodExtChallengeLayout
  (liftPoly liftPoly_eval_base liftPoly_zero liftPoly_sub liftPoly_mul liftPoly_eq_zero_iff
   notMem_exceptionalSet_lift oodRfamExt oodBatchResidualExt oodColumnLayoutExt_law
   oodBatchResidualExt_exceptionalSet_card_lt constraintPoly_dArith_tHonest_zero)
open Dregg2.Circuit.OodColumnLayout
  (oodArithList mem_oodArithList_iff oodArithList_transferV3_length oodArithList_transferV3_pos)
open Dregg2.Circuit.KprimeCompose (constraintResidualAtZeta)
open Dregg2.Circuit.RotatedKernelRefinement (transferV3)
open Dregg2.Circuit.FriDeployedExtCode
  (BB4 bb4Basis bb4_finrank bb4_card exists_not_mem_range_algebraMap)
open Dregg2.Circuit.OodSoundnessGame
  (oodNonExcAcc oodNonExc_winProb_le batchResidual batchResidual_coeff batchResidual_natDegree_lt)
open Dregg2.Crypto.ProbCrypto (winProb)

/-! ## §0 — the one algebraic fact the whole "no descent" half rides.

`Set.range (algebraMap BabyBear E)` is closed under the base-field operations but NOT under
multiplication by a genuine extension element: scaling a non-base element by a NONZERO base element
keeps it outside the base image. This is what makes an extension-valued quotient opening
`quotient : Challenge` inexpressible in a base-typed OOD identity. -/

section Beyond

variable {E : Type*} [Field E] [Algebra BabyBear E]

/-- A nonzero base scalar times a NON-base element is still non-base. -/
theorem mul_algebraMap_notMem_range {b : BabyBear} (hb : b ≠ 0) {ξ : E}
    (hξ : ξ ∉ Set.range (algebraMap BabyBear E)) :
    algebraMap BabyBear E b * ξ ∉ Set.range (algebraMap BabyBear E) := by
  rintro ⟨s, hs⟩
  have hbne : algebraMap BabyBear E b ≠ 0 :=
    fun h0 => hb ((algebraMap BabyBear E).injective (by rw [h0, map_zero]))
  refine hξ ⟨s / b, ?_⟩
  rw [map_div₀, div_eq_iff hbne, hs]
  ring

end Beyond

/-! ## §1 — SITE `FieldIntegerLift.lean:70-79, :139` — the OOD landing at the deployed challenge
typing.

`OodInterpF` binds `ζ : BabyBear`, `Zp qp : Polynomial BabyBear`; `verifyAlgo`'s opened
`vanishingAtZeta`/`quotientAtZeta` are, in the deployed verifier, `Challenge` values
(`vendor/plonky3-fri-82cfad73/src/verifier.rs:623-640`). LOAD-BEARING: this bridge is what
`OodColumnLayout.mainAirAcceptF_of_oodLayout` and `KprimeCompose.kprime_compose` land through.

`OodInterpFExt` is the same bridge with the CHALLENGE and the QUOTIENT/VANISHING polynomials drawn
from the extension. The committed constraint polynomial stays a `Polynomial BabyBear` embedded
coefficientwise (the trace IS base-field data — that is not the wound). -/

section OodInterpExt

variable {E : Type*} [Field E] [Algebra BabyBear E] [DecidableEq E]

/-- **`OodInterpF` AT THE DEPLOYED CHALLENGE TYPING.** `ζ : E`, and the vanishing/quotient
polynomials are genuinely extension-coefficiented (the deployed `vanishingAtZeta`/`quotientAtZeta`
openings are `Challenge`). `hZrow` is the domain-geometry axis, now read at the EMBEDDED row points
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

/-- **⚑ THE PAYOFF AT SITE 1 — the extension-typed OOD bridge still forces the BASE-field AIR
conclusion.** The Schwartz–Zippel step runs over `E`, yielding the polynomial identity
`C.map φ = Zp · qp` in `Polynomial E`; evaluating at the EMBEDDED row points (where `Zp` vanishes by
`hZrow`) and using injectivity of `φ` lands the base-field row vanishing that `MainAirAcceptF` is
stated with. Conclusion IDENTICAL to `ood_forces_mainAirAccept_field`; hypothesis strictly weaker
(§1.2). -/
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
supplied (embedded coefficientwise) and the challenge drawn from `E`. This is the shape §2 and the
deployed chains consume. -/
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

/-! ### §1.2 — THE TRUE RELATION at site 1: base witnesses LIFT. -/

/-- **The base-typed OOD bridge LIFTS.** Every `OodInterpF` witness embeds into an `OodInterpFExt`
witness along `algebraMap BabyBear E`: the domain axis, the OOD identity, and the
non-exceptionality side condition all transport. So `OodInterpFExt` is a strictly WEAKER demand —
which is the point, because the deployed verifier supplies extension witnesses and base ones it
does not supply at all. -/
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
nothing that the base-typed bridge delivered is lost by moving to the extension typing. -/
theorem mainAirAcceptF_of_oodInterpF_via_ext {d : EffectVmDescriptor2} {t : VmTrace}
    (I : OodInterpF d t) : MainAirAcceptF d t :=
  ood_forces_mainAirAccept_field_ext (E := BB4) (oodInterpFExt_of_oodInterpF I)

/-! ### §1.3 — THE TRUE RELATION at site 1: extension witnesses do NOT descend, and the base
equation cannot even EXPRESS the deployed right-hand side. -/

/-- Every BASE-typed OOD right-hand side, under the embedding, is confined to the base image. -/
theorem base_ood_rhs_mem_range (_t : VmTrace) (ζ : BabyBear) (Zp qp : Polynomial BabyBear) :
    (liftPoly E Zp).eval (algebraMap BabyBear E ζ) * (liftPoly E qp).eval
        (algebraMap BabyBear E ζ)
      ∈ Set.range (algebraMap BabyBear E) := by
  rw [liftPoly_eval_base, liftPoly_eval_base, ← map_mul]
  exact ⟨_, rfl⟩

/-- **⚑ THE DEPLOYED OOD RIGHT-HAND SIDE IS BEYOND THE BASE FIELD.** With a genuinely
`Challenge`-valued quotient opening `ξ` — which is exactly what the deployed `quotient : Challenge`
IS — and a domain vanisher that does not vanish at the OOD point (it cannot: the OOD point is by
definition off the trace domain), the OOD identity's right-hand side `Z(ζ)·q(ζ)` lies OUTSIDE
`Set.range (algebraMap BabyBear E)`. So the base-typed `OodInterpF.hood` equation, whose both sides
are base-field values, is a DIFFERENT equation over a strictly smaller value space — not a
specialization of the deployed one. -/
theorem extOod_rhs_beyond_base {ζ₀ : BabyBear} {ξ : E}
    (hξ : ξ ∉ Set.range (algebraMap BabyBear E)) (t : VmTrace)
    (hZ : (vanishingPoly t).eval ζ₀ ≠ 0) :
    (liftPoly E (vanishingPoly t)).eval (algebraMap BabyBear E ζ₀)
        * (Polynomial.C ξ).eval (algebraMap BabyBear E ζ₀)
      ∉ Set.range (algebraMap BabyBear E) := by
  rw [liftPoly_eval_base, Polynomial.eval_C]
  exact mul_algebraMap_notMem_range hZ hξ

/-- **The same fact as a SEPARATION of witnesses**: that deployed-shape right-hand side is attained
by NO lifted base-typed witness, for any base `ζ'`, `Zp'`, `qp'`. -/
theorem extOod_rhs_not_lifted {ζ₀ : BabyBear} {ξ : E}
    (hξ : ξ ∉ Set.range (algebraMap BabyBear E)) (t : VmTrace)
    (hZ : (vanishingPoly t).eval ζ₀ ≠ 0)
    (ζ' : BabyBear) (Zp' qp' : Polynomial BabyBear) :
    (liftPoly E (vanishingPoly t)).eval (algebraMap BabyBear E ζ₀)
        * (Polynomial.C ξ).eval (algebraMap BabyBear E ζ₀)
      ≠ (liftPoly E Zp').eval (algebraMap BabyBear E ζ')
          * (liftPoly E qp').eval (algebraMap BabyBear E ζ') := by
  intro heq
  exact extOod_rhs_beyond_base hξ t hZ (heq ▸ base_ood_rhs_mem_range t ζ' Zp' qp')

end OodInterpExt

/-! ## §2 — SITE `KprimeCompose.lean:62-67` — the composed K′ chain at the deployed challenge
typing.

`constraintResidualAtZeta` reads `ζ : BabyBear` and `qp : VmConstraint2 → Polynomial BabyBear`;
`kprime_compose` batches with `α : BabyBear`. Both the OOD point and the constraint-RLC challenge
are `Challenge` in the deployed verifier. LOAD-BEARING: `kprime_compose_of_tableIdentity` is the
verifier-facing composition. -/

section KprimeExt

variable {E : Type*} [Field E] [Algebra BabyBear E] [DecidableEq E]

/-- **`constraintResidualAtZeta` AT THE DEPLOYED CHALLENGE TYPING** — `Rᵢ(ζ) = Cᵢ(ζ) − Z(ζ)·qᵢ(ζ)`
with `ζ` an extension element, the committed `Cᵢ`/`Z` embedded coefficientwise, and `qᵢ` a genuinely
extension-coefficiented quotient. -/
noncomputable def constraintResidualAtZetaExt (E : Type*) [Field E] [Algebra BabyBear E]
    (d : EffectVmDescriptor2) (t : VmTrace) (ζ : E) (qp : VmConstraint2 → Polynomial E)
    (i : ℕ) : E :=
  if h : i < d.constraints.length then
    (liftPoly E (constraintPoly d t (d.constraints[i]'h))).eval ζ
      - (liftPoly E (vanishingPoly t)).eval ζ * (qp (d.constraints[i]'h)).eval ζ
  else 0

/-- **⚑ THE PAYOFF AT SITE 2 — K′ COMPOSED at the extension typing.** From the SINGLE combined RLC
identity `∑ᵢ Rᵢ(ζ)·αⁱ = 0` over the EXTENSION, a non-exceptional extension batching challenge `α`,
a non-exceptional extension OOD point `ζ`, and the deployed domain cap, conclude the very same
BASE-field `MainAirAcceptF d t`. The RLC split (`rlc_batch_split_of_combined`) was already
field-generic; §1's landing does the rest. -/
theorem kprime_composeExt (E : Type*) [Field E] [Algebra BabyBear E] [DecidableEq E]
    (d : EffectVmDescriptor2) (t : VmTrace) (hcap : t.rows.length ≤ domainSize)
    (ζ α : E) (qp : VmConstraint2 → Polynomial E)
    (hCombined : ∑ i ∈ Finset.range d.constraints.length,
        constraintResidualAtZetaExt E d t ζ qp i * α ^ i = 0)
    (hαnonexc : α ∉ exceptionalSet
        (rlcResidualPoly d.constraints.length (constraintResidualAtZetaExt E d t ζ qp)))
    (hζnonexc : ∀ c ∈ d.constraints, isArith c →
        ζ ∉ exceptionalSet
          (liftPoly E (constraintPoly d t c) - liftPoly E (vanishingPoly t) * qp c)) :
    MainAirAcceptF d t := by
  have hsplit := rlc_batch_split_of_combined d.constraints.length
    (constraintResidualAtZetaExt E d t ζ qp) α hCombined hαnonexc
  refine ood_forces_mainAirAccept_field_of_residuals_ext E d t hcap ζ qp ?_ hζnonexc
  intro c hc _
  obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hc
  have h0 := hsplit i hi
  unfold constraintResidualAtZetaExt at h0
  rw [dif_pos hi, hci] at h0
  exact sub_eq_zero.mp h0

/-- **K′ COMPOSED (outer, verifier-facing) at the extension typing.** The opened
`constraintEval`/`vanishingAtZeta`/`quotientAtZeta` are extension elements — the deployed
`Challenge` values — and the one honest identification `hCombinedIsRlc` is carried as the same
named Prop hypothesis the base-typed form carries (never an axiom). -/
theorem kprime_compose_of_tableIdentityExt (E : Type*) [Field E] [Algebra BabyBear E]
    [DecidableEq E] (d : EffectVmDescriptor2) (t : VmTrace)
    (hcap : t.rows.length ≤ domainSize)
    (ζ α : E) (qp : VmConstraint2 → Polynomial E)
    (constraintEval vanishingAtZeta quotientAtZeta : E)
    (hTable : constraintEval = vanishingAtZeta * quotientAtZeta)
    (hCombinedIsRlc : constraintEval - vanishingAtZeta * quotientAtZeta
        = ∑ i ∈ Finset.range d.constraints.length,
            constraintResidualAtZetaExt E d t ζ qp i * α ^ i)
    (hαnonexc : α ∉ exceptionalSet
        (rlcResidualPoly d.constraints.length (constraintResidualAtZetaExt E d t ζ qp)))
    (hζnonexc : ∀ c ∈ d.constraints, isArith c →
        ζ ∉ exceptionalSet
          (liftPoly E (constraintPoly d t c) - liftPoly E (vanishingPoly t) * qp c)) :
    MainAirAcceptF d t :=
  kprime_composeExt E d t hcap ζ α qp
    (by rw [← hCombinedIsRlc, hTable, sub_self]) hαnonexc hζnonexc

/-! ### §2.1 — THE TRUE RELATION at site 2. -/

/-- **The residual vector LIFTS.** At embedded base data, the extension-typed per-constraint
residual is the embedding of the base-typed one — so the base layer sits inside the extension layer
as exactly the `algebraMap`-image slice. -/
theorem constraintResidualAtZetaExt_lift (d : EffectVmDescriptor2) (t : VmTrace)
    (ζ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear) (i : ℕ) :
    constraintResidualAtZetaExt E d t (algebraMap BabyBear E ζ)
        (fun c => liftPoly E (qp c)) i
      = algebraMap BabyBear E (constraintResidualAtZeta d t ζ qp i) := by
  unfold constraintResidualAtZetaExt constraintResidualAtZeta
  by_cases h : i < d.constraints.length
  · rw [dif_pos h, dif_pos h]
    simp only [liftPoly_eval_base, map_sub, map_mul]
  · rw [dif_neg h, dif_neg h, map_zero]

/-- **⚑ NO DESCENT at site 2**: with a genuinely `Challenge`-valued quotient (the deployed
`quotient : Challenge`) and a nonvanishing domain vanisher at the OOD point, the extension-typed
residual `R₀` takes a value the base-typed residual CANNOT take — it differs from the embedded base
constraint value by a non-base amount. So `constraintResidualAtZeta`'s value space is strictly
smaller than the deployed one. -/
theorem extResidual_beyond_base {ζ₀ : BabyBear} {ξ : E}
    (hξ : ξ ∉ Set.range (algebraMap BabyBear E))
    (d : EffectVmDescriptor2) (hn : 0 < d.constraints.length) (t : VmTrace)
    (hZ : (vanishingPoly t).eval ζ₀ ≠ 0) :
    constraintResidualAtZetaExt E d t (algebraMap BabyBear E ζ₀) (fun _ => Polynomial.C ξ) 0
      ∉ Set.range (algebraMap BabyBear E) := by
  unfold constraintResidualAtZetaExt
  rw [dif_pos hn]
  simp only [liftPoly_eval_base, Polynomial.eval_C]
  rintro ⟨s, hs⟩
  refine mul_algebraMap_notMem_range (E := E) hZ hξ ⟨
    (constraintPoly d t (d.constraints[0]'hn)).eval ζ₀ - s, ?_⟩
  rw [map_sub, hs]
  ring

end KprimeExt

/-! ## §3 — SITE `OodColumnLayout.lean:96-283` — the DEPLOYED `transferV3` half.

`OodExtChallengeLayout` §2 already supplies the ∀-descriptor extension-typed modeler
(`oodRfamExt`, `oodBatchResidualExt`, `oodColumnLayoutExt_law`, `oodLayoutExt_debatch`,
`mainAirAcceptF_of_oodLayoutExt`). What it does NOT supply — and what `OodColumnLayout` §4/§5 has
at the base typing — is the DEPLOYED `transferV3` half: the membership form of the law, the law
fired at the real 147-column layout, and the RLC bad-set cap at that layout. Supplied here at the
extension typing, so the deployed descriptor's column-layout facts exist at the challenge typing the
deployed verifier actually uses. -/

section TransferV3Ext

variable {E : Type*} [Field E] [Algebra BabyBear E] [DecidableEq E]

/-- **The extension-typed column-layout law in MEMBERSHIP form (∀ d)** — every declared arithmetic
constraint occupies a column of the extension-valued batched residual. (`OodColumnLayout`'s
`oodColumnLayout_law_mem` at the deployed challenge typing.) -/
theorem oodColumnLayoutExt_law_mem (d : EffectVmDescriptor2) (t : VmTrace) (ζ : E)
    (qp : VmConstraint2 → Polynomial E) (c : VmConstraint2)
    (hc : c ∈ d.constraints) (harith : isArith c) :
    ∃ j : Fin (oodArithList d).length,
      (oodArithList d).get j = c ∧
      (oodBatchResidualExt E d t ζ qp).coeff (j : ℕ)
        = (liftPoly E (constraintPoly d t c)).eval ζ
            - (liftPoly E (vanishingPoly t)).eval ζ * (qp c).eval ζ := by
  have hcf : c ∈ oodArithList d := (mem_oodArithList_iff d c).mpr ⟨hc, harith⟩
  obtain ⟨i, hlt, hget⟩ := List.mem_iff_getElem.mp hcf
  refine ⟨⟨i, hlt⟩, ?_, ?_⟩
  · simpa [List.get_eq_getElem] using hget
  · rw [oodColumnLayoutExt_law d t ζ qp ⟨i, hlt⟩]
    simp only [List.get_eq_getElem, hget]

/-- **The law FIRES on the DEPLOYED descriptor at the deployed challenge typing**: coefficient `0`
of `transferV3`'s extension-valued batched residual is the extension-valued residual of the FIRST
column of its actual 147-column layout. -/
theorem oodColumnLayoutExt_law_fires_transferV3 (t : VmTrace) (ζ : E)
    (qp : VmConstraint2 → Polynomial E) :
    (oodBatchResidualExt E transferV3 t ζ qp).coeff 0
      = oodRfamExt E transferV3 t ζ qp ⟨0, oodArithList_transferV3_pos⟩ :=
  batchResidual_coeff (oodRfamExt E transferV3 t ζ qp) ⟨0, oodArithList_transferV3_pos⟩

/-- **The deployed RLC bad-Λ cap at the extension typing**: fewer than 147 bad batching challenges,
now inside a challenge space of size `|E|` rather than `|BabyBear|`. (`OodColumnLayout`'s
`transferV3_rlc_bound` at the deployed challenge typing; §4 prices it.) -/
theorem transferV3_rlc_bound_ext (t : VmTrace) (ζ : E) (qp : VmConstraint2 → Polynomial E) :
    (exceptionalSet (oodBatchResidualExt E transferV3 t ζ qp)).card < 147 := by
  have h := oodBatchResidualExt_exceptionalSet_card_lt (E := E) transferV3
    oodArithList_transferV3_pos t ζ qp
  rwa [oodArithList_transferV3_length] at h

end TransferV3Ext

/-! ## §4 — SITE `OodSoundnessGame.lean:107, :223` — the ε, priced at the REAL challenge space.

⚑ VERDICT — say which, precisely, because "conservative" is easy to launder here:

  * The underlying games are ALREADY field-generic (`{F} [Fintype F] [CommRing F] [IsDomain F]
    [DecidableEq F]`). Nothing in them is wrong. What is base-typed is only the INSTANCE:
    `oodNonExc_soundness_error_babybear` / `rlc_debatch_error_babybear` are the generic theorem at
    `F = BabyBear`.
  * That instance is therefore **UNFAITHFUL** — it prices a BabyBear-valued residual sampled from a
    BabyBear challenge space, and the deployed residual/challenge are `Challenge`-valued. It is NOT
    a bound on the deployed event at all: it is a true statement about a different object. Saying
    "the deployed ε is ≤ deg/p because `oodNonExc_soundness_error_babybear`" would be laundering.
  * It IS **CONSERVATIVE IN THE NUMBER**: for any numerator, `deg/p^4 ≤ deg/p`
    (`babybear_pricing_is_conservative`), and strictly so when the numerator is positive
    (`ext_pricing_strictly_tighter`). So the mis-typing never made a reported number too SMALL —
    the deployed ε is `p^3 ≈ 2^93` times better than the one the tree reports.
  * The repair is therefore purely additive: re-instantiate at `BB4`, the canonical deployed quartic
    extension. Nothing has to be re-proved. -/

section EpsilonBB4

/-- `|Challenge| = |BB4| = 2013265921^4` — the deployed challenge space, as a Nat. -/
theorem bb4_card_deployed : Fintype.card BB4 = 2013265921 ^ 4 := by
  rw [bb4_card]

/-- …as a real number, for the ε denominators. -/
theorem bb4_card_real : (Fintype.card BB4 : ℝ) = (2013265921 : ℝ) ^ 4 := by
  rw [bb4_card_deployed]; norm_num

/-- **REDUCTION 1 @ THE DEPLOYED CHALLENGE SPACE.** The probability a uniform OOD point — a
`Challenge`, i.e. a `BB4` element — escapes into the exceptional set of the residual is at most
`deg R / 2013265921^4`. This is `oodNonExc_soundness_error_babybear` at the object the deployed
verifier actually samples. -/
theorem oodNonExc_soundness_error_bb4 (R : Polynomial BB4) :
    winProb (oodNonExcAcc R) ≤ (R.natDegree : ℝ) / 2013265921 ^ 4 := by
  have h := oodNonExc_winProb_le R
  rwa [bb4_card_real] at h

/-- **REDUCTION 2 @ THE DEPLOYED CHALLENGE SPACE.** ε_RLC `≤ (n−1)/2013265921^4` when the batching
challenge is a `Challenge`. -/
theorem rlc_debatch_error_bb4 {n : ℕ} (hn : 0 < n) (R : Fin n → BB4) :
    winProb (oodNonExcAcc (batchResidual R)) ≤ ((n - 1 : ℕ) : ℝ) / 2013265921 ^ 4 := by
  have hd : (batchResidual R).natDegree ≤ n - 1 := by
    have := batchResidual_natDegree_lt hn R; omega
  refine le_trans (oodNonExc_soundness_error_bb4 (batchResidual R)) ?_
  gcongr

/-- **The DEPLOYED descriptor's RLC ε at the DEPLOYED challenge space**: at `transferV3`'s real
147-column layout, `≤ 146/2013265921^4`. -/
theorem transferV3_rlc_error_bb4 (t : VmTrace) (ζ : BB4) (qp : VmConstraint2 → Polynomial BB4) :
    winProb (oodNonExcAcc (oodBatchResidualExt BB4 transferV3 t ζ qp))
      ≤ (((oodArithList transferV3).length - 1 : ℕ) : ℝ) / 2013265921 ^ 4 :=
  rlc_debatch_error_bb4 oodArithList_transferV3_pos (oodRfamExt BB4 transferV3 t ζ qp)

/-- **THE VERDICT, half one — the base-typed NUMBER is conservative.** For any numerator, the
faithful denominator gives the smaller bound, so the mis-typing never reported an ε that was too
SMALL. (This is a statement about the NUMBERS only; the base-typed theorem still does not bound the
deployed event, which is about `Challenge`-valued residuals — that is what `*_bb4` supplies.) -/
theorem babybear_pricing_is_conservative (x : ℝ) (hx : 0 ≤ x) :
    x / (2013265921 : ℝ) ^ 4 ≤ x / 2013265921 := by
  have h1 : (0 : ℝ) < 2013265921 := by norm_num
  have h2 : (2013265921 : ℝ) ≤ 2013265921 ^ 4 := by norm_num
  gcongr

/-- **THE VERDICT, half two — and it was UNFAITHFUL.** Whenever the numerator is positive the two
numbers are DIFFERENT, the faithful one strictly smaller. So the base-typed ε is not the deployed
ε; it is a strictly looser statement about a strictly smaller object. -/
theorem ext_pricing_strictly_tighter (x : ℝ) (hx : 0 < x) :
    x / (2013265921 : ℝ) ^ 4 < x / 2013265921 := by
  have h1 : (0 : ℝ) < 2013265921 := by norm_num
  have h2 : (2013265921 : ℝ) < 2013265921 ^ 4 := by norm_num
  exact div_lt_div_of_pos_left hx h1 h2

/-- The separation, fired at the DEPLOYED `transferV3` RLC numerator (146 bad challenges): the
faithful ε is strictly below the reported one. -/
theorem transferV3_pricing_separation :
    (146 : ℝ) / 2013265921 ^ 4 < (146 : ℝ) / 2013265921 :=
  ext_pricing_strictly_tighter 146 (by norm_num)

end EpsilonBB4

/-! ## §5 — SITE `RlcRomBound.lean:298-317` — the deployed Λ-clause ε, at the real challenge space.

`rlc_lambda_nonexceptionality_is_bounded` is field-generic; only its `*_babybear` instances price
at `|BabyBear|`. Re-instantiated at `BB4`: the SAME acceptance event, the SAME adaptive prover, the
SAME forcing lemma — a `p^3`-times tighter and faithful bound.

⚠ SCOPE, at its real resolution: `declaredAlphaExceptional` reads `SingleAirOpening.alpha : F`. At
`F = BB4` that is the faithful TYPING of the declared challenge. The deployed serialized record
still stores ONE felt per challenge — that is the felt-width wound, adjacent to this one and NOT
repaired here. -/

section RlcBB4

open Dregg2.Circuit.FriVerifier
  (BatchProofData WrapPublics FriParams RecursionVk FriCore FieldArith)
open Dregg2.Circuit.BatchTablesSingleAir (SingleAirOpening)
open Dregg2.Circuit.FriChallengerUnified (verifyAlgoUnifiedFaithful)
open Dregg2.Circuit.RlcRomBound
  (RomUniformAlpha declaredAlphaExceptional rlc_lambda_nonexceptionality_is_bounded)

/-- `BB4` has an inhabitant (`0`) — required by the transcript machinery's `headD default`. -/
noncomputable instance instInhabitedBB4 : Inhabited BB4 := ⟨0⟩

/-- **The Λ error at the DEPLOYED CHALLENGE SPACE.** For a per-constraint residual family
`Rf : Fin n → BB4`, the probability the deployed faithful verifier accepts with a declared RLC
`Challenge` in the batching polynomial's bad set is at most `(n − 1)/2013265921^4`. -/
theorem rlc_lambda_bounded_bb4 {Ω : Type} [Fintype Ω]
    (perm : List BB4 → List BB4) (RATE : Nat) (toNat : BB4 → Nat)
    (params : FriParams) (vk : RecursionVk BB4) (core : FriCore BB4) (A : FieldArith BB4)
    (initState : List BB4) (logN : Nat)
    (pub : WrapPublics BB4) (proofOf : Ω → BatchProofData BB4)
    (hrom : RomUniformAlpha perm RATE toNat params initState logN proofOf pub)
    {n : ℕ} (hn : 0 < n) (Rf : Fin n → BB4) :
    winProb (fun ω =>
        verifyAlgoUnifiedFaithful perm RATE toNat params vk core A initState logN (proofOf ω) pub
          && declaredAlphaExceptional (batchResidual Rf) (proofOf ω))
      ≤ ((n - 1 : ℕ) : ℝ) / 2013265921 ^ 4 := by
  have hbase := rlc_lambda_nonexceptionality_is_bounded perm RATE toNat params vk core A
    initState logN pub proofOf hrom (batchResidual Rf)
  rw [bb4_card_real] at hbase
  refine le_trans hbase ?_
  have hd : (batchResidual Rf).natDegree ≤ n - 1 := by
    have := batchResidual_natDegree_lt hn Rf; omega
  gcongr

/-- **⚑ THE `FriLdtExtractV3` Λ-CLAUSE AT THE DEPLOYED CHALLENGE SPACE.** At the exact object the
deployed bundle carries — now typed as the extension-valued batched residual of `transferV3`'s real
147-column layout — the probability that the deployed faithful verifier accepts while the prover's
declared RLC `Challenge` violates the clause is at most `146/2013265921^4`. -/
theorem hLam_clause_bounded_bb4 {Ω : Type} [Fintype Ω]
    (perm : List BB4 → List BB4) (RATE : Nat) (toNat : BB4 → Nat)
    (params : FriParams) (vk : RecursionVk BB4) (core : FriCore BB4) (A : FieldArith BB4)
    (initState : List BB4) (logN : Nat)
    (pub : WrapPublics BB4) (proofOf : Ω → BatchProofData BB4)
    (hrom : RomUniformAlpha perm RATE toNat params initState logN proofOf pub)
    (t : VmTrace) (ζ : BB4) (qp : VmConstraint2 → Polynomial BB4) :
    winProb (fun ω =>
        verifyAlgoUnifiedFaithful perm RATE toNat params vk core A initState logN (proofOf ω) pub
          && declaredAlphaExceptional (oodBatchResidualExt BB4 transferV3 t ζ qp) (proofOf ω))
      ≤ (((oodArithList transferV3).length - 1 : ℕ) : ℝ) / 2013265921 ^ 4 :=
  rlc_lambda_bounded_bb4 perm RATE toNat params vk core A initState logN pub proofOf hrom
    oodArithList_transferV3_pos (oodRfamExt BB4 transferV3 t ζ qp)

/-! ### §5.1 — the bounded event is INHABITED at a genuinely non-base declared challenge. -/

/-- A minimal single-AIR opening declaring the challenge `a`. -/
noncomputable def openingDeclaring (a : BB4) : SingleAirOpening BB4 :=
  { zeta := 0, degreeBits := 0, expectedDegreeBits := 0, alpha := a,
    constraintEvals := [0], zps := [], quotientChunks := [],
    vanishing := 0, invVanishing := 0, logupCumSum := 0 }

/-- A minimal well-formed proof carrying exactly that opening. -/
noncomputable def proofDeclaring (a : BB4) : BatchProofData BB4 :=
  { degreeBitsPreamble := [0], baseDegreeBitsPreamble := [0], preprocessedWidthPreamble := [0],
    traceCommit := [0], friCommitments := [], finalPoly := [0], queries := [],
    exposedSegment := [], oodPoint := [0], powWitness := [0], friLogArities := [],
    singleAirOpenings := [openingDeclaring a] }

/-- **⚑ FIRE — §5's escape event is NON-EMPTY at a challenge OUTSIDE the base field.** There is a
`Challenge` value that is not the image of any `Val`, and a concrete submitted proof declaring it,
for which `declaredAlphaExceptional` is `true` against the residual `X − C ξ` (whose unique root is
`ξ`). So the bounded event of §5 is genuinely reachable in the regime the retyping is about, not
true by emptiness. -/
theorem fire_declaredAlphaExceptional_nonbase :
    ∃ ξ : BB4, ξ ∉ Set.range (algebraMap BabyBear BB4) ∧
      declaredAlphaExceptional (X - C ξ) (proofDeclaring ξ) = true := by
  obtain ⟨ξ, hξ⟩ := exists_not_mem_range_algebraMap (F := BabyBear) (E := BB4)
    (by rw [bb4_finrank]; norm_num)
  refine ⟨ξ, hξ, ?_⟩
  unfold declaredAlphaExceptional
  rw [List.any_eq_true]
  refine ⟨openingDeclaring ξ, by simp [proofDeclaring], ?_⟩
  refine decide_eq_true ?_
  show ξ ∈ exceptionalSet (X - C ξ)
  unfold exceptionalSet
  rw [roots_X_sub_C]
  simp

end RlcBB4

/-! ## §6 — NON-VACUITY: the §1/§2 hypothesis bundles are INHABITED at genuinely NON-BASE
challenges, on the committed toy instance, and the §1 separation FIRES at the REAL deployed
descriptor. -/

section Fire

open Dregg2.Circuit.FriDecodedTraceWitness (defaultTrace)

/-- The modeled per-constraint residual vector of `dArith`/`tHonest` at ANY extension OOD point,
with the honest zero quotient, is the zero function (the honest all-zero column interpolates to the
zero polynomial). -/
theorem constraintResidualAtZetaExt_dArith_tHonest (ζ : BB4) :
    constraintResidualAtZetaExt BB4 dArith tHonest ζ (fun _ => 0) = fun _ => 0 := by
  funext i
  unfold constraintResidualAtZetaExt
  split
  · next h =>
      have hi0 : i = 0 := by
        have h1 : i < 1 := by simpa [dArith] using h
        omega
      subst hi0
      rw [show dArith.constraints[0]'h = VmConstraint2.base (.gate (.var 0)) from rfl,
        constraintPoly_dArith_tHonest_zero]
      simp
  · rfl

/-- **⚑ FIRE — the §2 hypothesis bundle is INHABITED at genuinely non-base challenges, and the
composition DELIVERS.** The statement records EVERY challenge-dependent hypothesis of
`kprime_composeExt`, not just its conclusion, so this cannot be satisfied by a vacuous witness: both
the OOD point and the constraint-RLC challenge are drawn from `BB4 ∖ image(BabyBear)` (so the
witness is NOT a lifted base witness — §2.1's regime), the combined RLC identity HOLDS there, both
non-exceptionality side conditions HOLD there, and the composition produces the real base-field
per-row AIR acceptance `MainAirAcceptF dArith tHonest`. -/
theorem fire_kprime_composeExt_nonbase :
    ∃ ζ α : BB4,
      ζ ∉ Set.range (algebraMap BabyBear BB4) ∧
      α ∉ Set.range (algebraMap BabyBear BB4) ∧
      (∑ i ∈ Finset.range dArith.constraints.length,
          constraintResidualAtZetaExt BB4 dArith tHonest ζ (fun _ => 0) i * α ^ i = 0) ∧
      α ∉ exceptionalSet (rlcResidualPoly dArith.constraints.length
          (constraintResidualAtZetaExt BB4 dArith tHonest ζ (fun _ => 0))) ∧
      (∀ c ∈ dArith.constraints, isArith c →
          ζ ∉ exceptionalSet (liftPoly BB4 (constraintPoly dArith tHonest c)
            - liftPoly BB4 (vanishingPoly tHonest) * 0)) ∧
      MainAirAcceptF dArith tHonest := by
  obtain ⟨ξ, hξ⟩ := exists_not_mem_range_algebraMap (F := BabyBear) (E := BB4)
    (by rw [bb4_finrank]; norm_num)
  have hcomb : ∑ i ∈ Finset.range dArith.constraints.length,
      constraintResidualAtZetaExt BB4 dArith tHonest ξ (fun _ => 0) i * ξ ^ i = 0 := by
    rw [constraintResidualAtZetaExt_dArith_tHonest]; simp
  have hα : ξ ∉ exceptionalSet (rlcResidualPoly dArith.constraints.length
      (constraintResidualAtZetaExt BB4 dArith tHonest ξ (fun _ => 0))) := by
    rw [constraintResidualAtZetaExt_dArith_tHonest]
    simp [exceptionalSet, rlcResidualPoly]
  have hζ : ∀ c ∈ dArith.constraints, isArith c →
      ξ ∉ exceptionalSet (liftPoly BB4 (constraintPoly dArith tHonest c)
        - liftPoly BB4 (vanishingPoly tHonest) * 0) := by
    intro c hc _
    simp only [dArith, List.mem_singleton] at hc
    subst hc
    rw [constraintPoly_dArith_tHonest_zero]
    simp [liftPoly, exceptionalSet]
  refine ⟨ξ, ξ, hξ, hξ, hcomb, hα, hζ, ?_⟩
  exact kprime_composeExt BB4 dArith tHonest (by simp [tHonest, domainSize]) ξ ξ (fun _ => 0)
    hcomb hα hζ

/-- **⚑ FIRE — the §1 separation, at the REAL deployed descriptor.** With the quotient opening a
genuine `Challenge` outside the base field (exactly as the deployed `quotient : Challenge` is), the
OOD identity's right-hand side on the deployed trace shape is beyond the base field — so the
base-typed `OodInterpF.hood` equation cannot express it. -/
theorem fire_extOod_rhs_beyond_base_transferV3 :
    ∃ ξ : BB4, ξ ∉ Set.range (algebraMap BabyBear BB4) ∧
      (liftPoly BB4 (vanishingPoly defaultTrace)).eval (algebraMap BabyBear BB4 0)
          * (Polynomial.C ξ).eval (algebraMap BabyBear BB4 0)
        ∉ Set.range (algebraMap BabyBear BB4) := by
  obtain ⟨ξ, hξ⟩ := exists_not_mem_range_algebraMap (F := BabyBear) (E := BB4)
    (by rw [bb4_finrank]; norm_num)
  refine ⟨ξ, hξ, extOod_rhs_beyond_base hξ defaultTrace ?_⟩
  simp [vanishingPoly, defaultTrace]

/-- **⚑ FIRE — the §2 no-descent separation at the deployed descriptor `transferV3`.** -/
theorem fire_extResidual_beyond_base_transferV3 :
    ∃ ξ : BB4, ξ ∉ Set.range (algebraMap BabyBear BB4) ∧
      constraintResidualAtZetaExt BB4 transferV3 defaultTrace
          (algebraMap BabyBear BB4 0) (fun _ => Polynomial.C ξ) 0
        ∉ Set.range (algebraMap BabyBear BB4) := by
  obtain ⟨ξ, hξ⟩ := exists_not_mem_range_algebraMap (F := BabyBear) (E := BB4)
    (by rw [bb4_finrank]; norm_num)
  refine ⟨ξ, hξ, extResidual_beyond_base hξ transferV3 ?_ defaultTrace ?_⟩
  · have hle : (oodArithList transferV3).length ≤ transferV3.constraints.length :=
      List.length_filter_le _ _
    rw [oodArithList_transferV3_length] at hle
    omega
  · simp [vanishingPoly, defaultTrace]

end Fire

/-! ## §7 — Axiom hygiene. Every keystone kernel-clean (Lean's own three axioms only). -/

#assert_all_clean [
  mul_algebraMap_notMem_range,
  ood_forces_mainAirAccept_field_ext,
  ood_forces_mainAirAccept_field_of_residuals_ext,
  base_ood_rhs_mem_range,
  extOod_rhs_beyond_base,
  extOod_rhs_not_lifted,
  mainAirAcceptF_of_oodInterpF_via_ext
]

#assert_all_clean [
  kprime_composeExt,
  kprime_compose_of_tableIdentityExt,
  constraintResidualAtZetaExt_lift,
  extResidual_beyond_base
]

#assert_all_clean [
  oodColumnLayoutExt_law_mem,
  oodColumnLayoutExt_law_fires_transferV3,
  transferV3_rlc_bound_ext
]

#assert_all_clean [
  bb4_card_deployed,
  oodNonExc_soundness_error_bb4,
  rlc_debatch_error_bb4,
  transferV3_rlc_error_bb4,
  babybear_pricing_is_conservative,
  ext_pricing_strictly_tighter,
  transferV3_pricing_separation
]

#assert_all_clean [
  rlc_lambda_bounded_bb4,
  hLam_clause_bounded_bb4,
  fire_declaredAlphaExceptional_nonbase
]

#assert_all_clean [
  constraintResidualAtZetaExt_dArith_tHonest,
  fire_kprime_composeExt_nonbase,
  fire_extOod_rhs_beyond_base_transferV3,
  fire_extResidual_beyond_base_transferV3
]

end Dregg2.Circuit.ExtChallengeOodSites
