/-
# `Dregg2.Circuit.KprimeCompose` — the K′ chain COMPOSED end-to-end.

Tonight's three K′ pieces exist separately in the tree:

  (a) K′(a) — `FieldIntegerLift.ood_forces_mainAirAccept_field_of_residuals`: the OOD landing on the
      REAL `VmTrace`, with the domain axis (`vanishingPoly t`, `hZrow`) and the interpolation axis
      (`TraceColumnInterp.constraintPoly_eval_eq_arithResidual`) already discharged;
  (b) K′(b) — `TraceColumnInterp.constraintPoly`: the committed trace-column interpolation of every
      arithmetic constraint (baked into (a) via `OodInterpF.hCrow`);
  (c) K′(c) — `OodQuotientConsistency.rlc_batch_split_of_combined`: the RLC constraint-batching
      split, from the ONE combined identity `verifyAlgo` delivers to the per-constraint residuals.

This file COMPOSES them into one theorem over the DEPLOYED BabyBear field (`ZMod 2013265921`):
from (i) the single RLC-COMBINED OOD identity `∑ᵢ Rᵢ(ζ)·αⁱ = 0` (the shape `verifyAlgo` checks),
(ii) `α`/`ζ` non-exceptional (Fiat–Shamir), and (iii) the domain cap `t.rows.length ≤ 2^27`,
conclude `MainAirAcceptF d t`. Inside the composition NO interpolation, domain, or RLC residual
remains open: the per-constraint residuals `Rᵢ` are the MODELED ones (`constraintPoly` minus
`vanishingPoly · qp`, both committed objects), the split is the REAL `rlc_batch_split_of_combined`,
and the landing is the REAL `ood_forces_mainAirAccept_field_of_residuals`.

## The ONE remaining honest identification (`hCombinedIsRlc`)

`verifyAlgo`'s `TableOpening.constraintEval` is an OPAQUE field element; the tree does not (yet)
prove that it equals the RLC `∑ᵢ (Cᵢ(ζ) − Z_H(ζ)·qᵢ(ζ))·αⁱ` of the MODELED per-constraint
residuals — that is the commitment-opening link. The outer theorem
`kprime_compose_of_tableIdentity` therefore carries it as ONE clearly-named Prop HYPOTHESIS,
`hCombinedIsRlc` (never an axiom): given the table identity `constraintEval = vanishingAtZeta ·
quotientAtZeta` that `verifyAlgo_accept_forces_table_identity` extracts from acceptance, plus
`hCombinedIsRlc`, the whole chain closes to `MainAirAcceptF d t`.

## FIRE

`kprime_compose_fires` runs the full composition on the committed toy descriptor
`AirChecksSatisfied.dArith` (one REAL arithmetic gate `col 0 = 0`) and the committed honest trace
`tHonest`, with every hypothesis — including `hCombinedIsRlc` — actually DISCHARGED (the honest
all-zero column interpolates to the zero polynomial, so the modeled residuals vanish and both
non-exceptionality sets are empty). The hypothesis package is satisfiable; the composition is not
vacuous.
-/
import Dregg2.Circuit.FieldIntegerLift
import Dregg2.Circuit.OodQuotientConsistency
import Dregg2.Circuit.OodInterpFieldExt

namespace Dregg2.Circuit.KprimeCompose

open Polynomial
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.AirChecksSatisfied
open Dregg2.Circuit.BabyBearFriField
open Dregg2.Circuit.TraceColumnInterp
open Dregg2.Circuit.OodQuotientConsistency
open Dregg2.Circuit.FieldIntegerLift
open Dregg2.Circuit.OodInterpFieldExt
  (BB4 liftPoly liftPoly_eval_base liftPoly_sub liftPoly_mul notMem_exceptionalSet_lift
   exists_nonbase_bb4 ood_forces_mainAirAccept_field_of_residuals_ext)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

/-! **⚑ RELOCATED, NOT DUPLICATED.** `colPoly_tHonest_zero` / `constraintPoly_dArith_tHonest_zero`
were proved in THREE places (here, `OodExtChallengeLayout`, and now the single source
`OodInterpFieldExt`). One survives; the other two are exports. -/
export Dregg2.Circuit.OodInterpFieldExt
  (colPoly_tHonest_zero constraintPoly_dArith_tHonest_zero)

/-! ## §1 — The modeled per-constraint OOD residual vector. -/

/-- **The `i`-th MODELED per-constraint OOD residual at ζ** — `Rᵢ(ζ) = Cᵢ(ζ) − Z_H(ζ)·qᵢ(ζ)`, with
`Cᵢ` the COMMITTED trace-column interpolation `constraintPoly d t (d.constraints[i])` (K′(b)) and
`Z_H` the COMMITTED domain vanisher `vanishingPoly t` (K′(a)'s discharged axis). These are exactly
the coefficients of the RLC batching polynomial the split (K′(c)) runs on; out-of-range indices
contribute `0` (they never arise under `Finset.range d.constraints.length`). -/
noncomputable def constraintResidualAtZeta (d : EffectVmDescriptor2) (t : VmTrace)
    (ζ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear) (i : ℕ) : BabyBear :=
  if h : i < d.constraints.length then
    (constraintPoly d t (d.constraints[i]'h)).eval ζ
      - (vanishingPoly t).eval ζ * (qp (d.constraints[i]'h)).eval ζ
  else 0

/-! ## §1.5 — ⚑ THE SAME RESIDUAL AT THE DEPLOYED CHALLENGE TYPING.

Both the OOD point `ζ` and the constraint-RLC challenge `α` are QUARTIC-EXTENSION elements in the
deployed verifier (`ExtFieldChallenge.lean:8-15`), and the opened `quotient` is a `Challenge`.  So
`constraintResidualAtZeta` above is not the deployed residual restricted — it is a residual over a
strictly smaller value space: `extResidual_beyond_base` (fired at the real deployed descriptor by
`ExtChallengeOodSites.fire_extResidual_beyond_base_transferV3`) exhibits an extension-typed `R₀`
outside `Set.range (algebraMap BabyBear BB4)`, which every base-typed residual is confined to.

`constraintResidualAtZetaExt` is the deployed typing.  §2 is stated at it, and the base-typed §2 is
then derived FROM it by the lift — one chain, no twin. -/

section Ext

variable {E : Type*} [Field E] [Algebra BabyBear E] [DecidableEq E]

/-- **`constraintResidualAtZeta` AT THE DEPLOYED CHALLENGE TYPING** — `Rᵢ(ζ) = Cᵢ(ζ) − Z(ζ)·qᵢ(ζ)`
with `ζ` an extension element, the committed `Cᵢ`/`Z` embedded coefficientwise, and `qᵢ` a genuinely
extension-coefficiented quotient (the deployed `quotient : Challenge` opening). -/
noncomputable def constraintResidualAtZetaExt (E : Type*) [Field E] [Algebra BabyBear E]
    (d : EffectVmDescriptor2) (t : VmTrace) (ζ : E) (qp : VmConstraint2 → Polynomial E)
    (i : ℕ) : E :=
  if h : i < d.constraints.length then
    (liftPoly E (constraintPoly d t (d.constraints[i]'h))).eval ζ
      - (liftPoly E (vanishingPoly t)).eval ζ * (qp (d.constraints[i]'h)).eval ζ
  else 0

/-- **The residual vector LIFTS.** At embedded base data the extension-typed residual is the
embedding of the base-typed one — the base layer is exactly the `algebraMap`-image slice. -/
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

/-- The RLC batching polynomial commutes with the coefficient lift. -/
theorem rlcResidualPoly_lift (n : ℕ) (r : ℕ → BabyBear) :
    rlcResidualPoly n (fun i => algebraMap BabyBear E (r i)) = liftPoly E (rlcResidualPoly n r) := by
  simp only [rlcResidualPoly, liftPoly, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]

end Ext

/-! ## §2 — The composition: combined RLC identity ⟹ `MainAirAcceptF`. -/

/-- **K′ COMPOSED (inner form).** From the SINGLE combined OOD identity
`∑ᵢ Rᵢ(ζ)·αⁱ = 0` over the modeled per-constraint residuals (the RLC-batched shape `verifyAlgo`
checks), a non-exceptional batching challenge `α`, a non-exceptional OOD point `ζ`, and the
deployed domain cap, conclude the canonical field AIR acceptance `MainAirAcceptF d t`.

The chain, with NO open interpolation/domain/RLC residual inside:
`rlc_batch_split_of_combined` (K′(c), Schwartz–Zippel in α) splits the combined identity into the
per-constraint `hood`; `vanishingPoly t` supplies the domain axis; and
`ood_forces_mainAirAccept_field_of_residuals` (K′(a), Schwartz–Zippel in ζ, with K′(b)'s
interpolation baked in) lands `MainAirAcceptF`. -/
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

/-- **K′ COMPOSED (inner form), BASE-TYPED — now a COROLLARY of the deployed-typed composition.**
Every base-typed `{hCombined, hαnonexc, hζnonexc}` package transports along `algebraMap BabyBear BB4`
(`constraintResidualAtZetaExt_lift`, `rlcResidualPoly_lift`, `notMem_exceptionalSet_lift`) and lands
the identical conclusion.  The base statement is retained because it is a real (stronger) hypothesis
someone may hold; it no longer carries its own derivation, so the deployed-typed composition is the
single source and the two cannot drift. -/
theorem kprime_compose (d : EffectVmDescriptor2) (t : VmTrace)
    (hcap : t.rows.length ≤ domainSize)
    (ζ α : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
    (hCombined : ∑ i ∈ Finset.range d.constraints.length,
        constraintResidualAtZeta d t ζ qp i * α ^ i = 0)
    (hαnonexc : α ∉ exceptionalSet
        (rlcResidualPoly d.constraints.length (constraintResidualAtZeta d t ζ qp)))
    (hζnonexc : ∀ c ∈ d.constraints, isArith c →
        ζ ∉ exceptionalSet (constraintPoly d t c - vanishingPoly t * qp c)) :
    MainAirAcceptF d t := by
  have hfam : constraintResidualAtZetaExt BB4 d t (algebraMap BabyBear BB4 ζ)
      (fun c => liftPoly BB4 (qp c))
      = fun i => algebraMap BabyBear BB4 (constraintResidualAtZeta d t ζ qp i) :=
    funext (fun i => constraintResidualAtZetaExt_lift d t ζ qp i)
  refine kprime_composeExt BB4 d t hcap (algebraMap BabyBear BB4 ζ) (algebraMap BabyBear BB4 α)
    (fun c => liftPoly BB4 (qp c)) ?_ ?_ ?_
  · rw [hfam]
    rw [show ∑ i ∈ Finset.range d.constraints.length,
        algebraMap BabyBear BB4 (constraintResidualAtZeta d t ζ qp i)
          * algebraMap BabyBear BB4 α ^ i
        = algebraMap BabyBear BB4 (∑ i ∈ Finset.range d.constraints.length,
            constraintResidualAtZeta d t ζ qp i * α ^ i) by
      rw [map_sum]; exact Finset.sum_congr rfl (fun i _ => by rw [map_mul, map_pow])]
    rw [hCombined, map_zero]
  · rw [hfam, rlcResidualPoly_lift]
    exact notMem_exceptionalSet_lift hαnonexc
  · intro c hc ha
    have hrw : liftPoly BB4 (constraintPoly d t c)
        - liftPoly BB4 (vanishingPoly t) * liftPoly BB4 (qp c)
        = liftPoly BB4 (constraintPoly d t c - vanishingPoly t * qp c) := by
      rw [liftPoly_sub, liftPoly_mul]
    rw [hrw]
    exact notMem_exceptionalSet_lift (hζnonexc c hc ha)

/-- **K′ COMPOSED (outer, verifier-facing form).** `verifyAlgo` acceptance delivers, per opened
table, the identity `constraintEval = vanishingAtZeta · quotientAtZeta` on OPAQUE field elements
(`verifyAlgo_accept_forces_table_identity`). The ONE honest identification the tree does not yet
prove is that the combined table residual `constraintEval − vanishingAtZeta·quotientAtZeta` IS the
RLC of the MODELED per-constraint residuals — carried here as the single named Prop hypothesis
`hCombinedIsRlc` (the commitment-opening link; NOT an axiom). Everything else is closed:
table identity + `hCombinedIsRlc` ⟹ combined RLC identity ⟹ (by `kprime_compose`)
`MainAirAcceptF d t`. -/
theorem kprime_compose_of_tableIdentity (d : EffectVmDescriptor2) (t : VmTrace)
    (hcap : t.rows.length ≤ domainSize)
    (ζ α : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
    (constraintEval vanishingAtZeta quotientAtZeta : BabyBear)
    (hTable : constraintEval = vanishingAtZeta * quotientAtZeta)
    (hCombinedIsRlc : constraintEval - vanishingAtZeta * quotientAtZeta
        = ∑ i ∈ Finset.range d.constraints.length,
            constraintResidualAtZeta d t ζ qp i * α ^ i)
    (hαnonexc : α ∉ exceptionalSet
        (rlcResidualPoly d.constraints.length (constraintResidualAtZeta d t ζ qp)))
    (hζnonexc : ∀ c ∈ d.constraints, isArith c →
        ζ ∉ exceptionalSet (constraintPoly d t c - vanishingPoly t * qp c)) :
    MainAirAcceptF d t :=
  kprime_compose d t hcap ζ α qp
    (by rw [← hCombinedIsRlc, hTable, sub_self]) hαnonexc hζnonexc

/-- **K′ COMPOSED (outer, verifier-facing) AT THE DEPLOYED CHALLENGE TYPING.** The opened
`constraintEval`/`vanishingAtZeta`/`quotientAtZeta` are extension elements — the deployed `Challenge`
values — and the one honest identification `hCombinedIsRlc` is carried as the same named Prop
hypothesis the base-typed form carries (never an axiom). -/
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

/-! ## §3 — FIRE: the whole composition runs on the committed `dArith`/`tHonest`, every hypothesis
discharged (including `hCombinedIsRlc`). -/

/-- With the honest quotient choice `qp = 0`, EVERY modeled per-constraint residual of
`dArith`/`tHonest` at ζ = 5 vanishes — the residual vector is literally the zero function. -/
theorem constraintResidualAtZeta_dArith_tHonest_zero :
    constraintResidualAtZeta dArith tHonest 5 (fun _ => 0) = (fun _ => 0) := by
  funext i
  unfold constraintResidualAtZeta
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

/-- **FIRE — the composed K′ chain actually runs.** On the committed toy descriptor `dArith` (one
REAL arithmetic gate `col 0 = 0`) and the committed honest trace `tHonest`, EVERY hypothesis of
`kprime_compose_of_tableIdentity` is discharged — the table identity (`0 = 0·0`), the
`hCombinedIsRlc` identification (both sides compute to `0`), and both non-exceptionality sets
(empty, since the modeled residual polynomials are `0`) — and the composition produces the same
`MainAirAcceptF dArith tHonest` the committed `honest_mainAirAcceptF` exhibits. The hypothesis
package is SATISFIABLE; the composition is not vacuous. -/
theorem kprime_compose_fires : MainAirAcceptF dArith tHonest :=
  kprime_compose_of_tableIdentity dArith tHonest
    (by norm_num [tHonest, domainSize])
    5 7 (fun _ => 0) 0 0 0
    (by ring)
    (by rw [constraintResidualAtZeta_dArith_tHonest_zero]; simp)
    (by rw [constraintResidualAtZeta_dArith_tHonest_zero]
        simp [exceptionalSet, rlcResidualPoly])
    (by intro c hc _
        simp only [dArith, List.mem_singleton] at hc
        subst hc
        rw [constraintPoly_dArith_tHonest_zero]
        simp [exceptionalSet])

#assert_axioms kprime_composeExt
#assert_axioms kprime_compose_of_tableIdentityExt
#assert_axioms kprime_compose
#assert_axioms kprime_compose_of_tableIdentity
#assert_axioms constraintResidualAtZetaExt_lift
#assert_axioms rlcResidualPoly_lift
#assert_axioms colPoly_tHonest_zero
#assert_axioms constraintPoly_dArith_tHonest_zero
#assert_axioms constraintResidualAtZeta_dArith_tHonest_zero
#assert_axioms kprime_compose_fires

end Dregg2.Circuit.KprimeCompose
