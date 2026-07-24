import Mathlib.Tactic
import Dregg2.Circuit.FriCorrelatedAgreementSharp
import Dregg2.Circuit.FriLdtJohnson

/-!
# `FriIncidenceDesign` — a correlated-agreement counterexample is an INCIDENCE DESIGN

This file formalizes the syndrome-incidence lens for Reed–Solomon correlated agreement, in the
tower's own Hamming vocabulary (`disagree`/`closeN`/`farN`), with NO parity-check / syndrome object
introduced (the tree has none, and adding one would mirror content `disagree`/`Submodule` already
carry).

## The picture

Viewing the FRI fold `Fold α f = E f + α · O f` as the affine LINE `{u + α·v}` (`u = E f`, `v = O f`)
of functions on the folded domain, a *good challenge* `α` is one whose fold lands within `dIn` of the
folded code `C'`, i.e. its fold-error is supported on some `T` with `|T| ≤ dIn`. That support may
CHANGE with `α`. Correlated agreement is the stronger event: a SINGLE support works for the whole
line.

`FriCorrelatedAgreementSharp.correlatedAgreementLine_twoPoint` already reconstructs off the UNION
`T₁ ∪ T₂` of two per-challenge supports, giving the weak floor `|κ| − 2·dIn`. The new content here:

* **`commonSupport_pointwise` / `commonSupport_line`** — if two good challenges share a COMMON support
  `T`, the reconstruction agrees off `T` *pointwise*, and the WHOLE line `Fold α f = ge + α·go` off
  `T` for every `α`. This is the Hamming analogue of "an affine line meeting one span in two points
  lies in that span".
* **`sharedSupport_sharpAgree`** — a common support of size `≤ dIn` collapses the union, yielding the
  SHARP δ-preserving floor `|κ| − dIn` (strictly beyond the two-point `|κ| − 2·dIn`).
* **`sharpAgree_or_incidenceDesign`** — the dichotomy: for any far word and any set of good
  challenges, EITHER two share a support (⇒ sharp correlated agreement) OR the good set is an
  `IncidenceDesign` (each caught by its own DISTINCT support). Contrapositive: a correlated-agreement
  counterexample is necessarily an incidence design.

⚠ **No list bound is claimed.** At the deployed radius the incidence-design branch is realizable —
`FriProximityGapWitness §5` constructs a pencil of ~100 good challenges with pairwise-distinct
supports (that is why `WrapCorrelatedAgreementSharp 292` cannot be improved to a small `L` at
`dIn = 56`). The payoff of this file is the STRUCTURAL dichotomy, not an improved bound.
-/

namespace Dregg2.Circuit.FriIncidenceDesign

open Dregg2.Circuit.FriSoundness
open Dregg2.Circuit.FriLdtJohnson
open Dregg2.Circuit.FriCorrelatedAgreementSharp

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Common-support reconstruction (pointwise).** If two distinct good challenges `α₁ ≠ α₂` have
their fold-errors on a COMMON support `T` (`disagree (Fold αᵢ f) gᵢ ⊆ T`), the Vandermonde solve pins
folded codewords `ge, go ∈ C'` that agree with `(E f, O f)` at every fibre OUTSIDE `T`. -/
theorem commonSupport_pointwise (S : FriSetup F ι κ) {f : ι → F} {α₁ α₂ : F} (hα : α₁ ≠ α₂)
    {T : Finset κ} {g₁ g₂ : κ → F} (hg₁ : g₁ ∈ S.C') (hg₂ : g₂ ∈ S.C')
    (h1 : disagree (Fold S.geom α₁ f) g₁ ⊆ T) (h2 : disagree (Fold S.geom α₂ f) g₂ ⊆ T) :
    ∃ ge ∈ S.C', ∃ go ∈ S.C', ∀ y ∉ T, E S.geom f y = ge y ∧ O S.geom f y = go y := by
  classical
  set G := S.geom with hG
  have hne : α₁ - α₂ ≠ 0 := sub_ne_zero.mpr hα
  set inv : F := (α₁ - α₂)⁻¹ with hinv
  set Go : κ → F := inv • (g₁ - g₂) with hGo
  set Ge : κ → F := inv • (α₁ • g₂ - α₂ • g₁) with hGe
  have hGoC : Go ∈ S.C' := S.C'.smul_mem _ (S.C'.sub_mem hg₁ hg₂)
  have hGeC : Ge ∈ S.C' :=
    S.C'.smul_mem _ (S.C'.sub_mem (S.C'.smul_mem _ hg₂) (S.C'.smul_mem _ hg₁))
  refine ⟨Ge, hGeC, Go, hGoC, ?_⟩
  intro y hy
  have hy1 : Fold G α₁ f y = g₁ y := by
    by_contra hcon; exact hy (h1 (mem_disagree.mpr hcon))
  have hy2 : Fold G α₂ f y = g₂ y := by
    by_contra hcon; exact hy (h2 (mem_disagree.mpr hcon))
  have e1 : E G f y + α₁ * O G f y = g₁ y := by simpa [Fold] using hy1
  have e2 : E G f y + α₂ * O G f y = g₂ y := by simpa [Fold] using hy2
  have hGoy : Go y = inv * (g₁ y - g₂ y) := by
    simp only [hGo, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hGey : Ge y = inv * (α₁ * g₂ y - α₂ * g₁ y) := by
    simp only [hGe, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  refine ⟨?_, ?_⟩
  · rw [hGey, hinv, inv_mul_eq_div, eq_div_iff hne]
    linear_combination α₁ * e2 - α₂ * e1
  · rw [hGoy, hinv, inv_mul_eq_div, eq_div_iff hne]
    linear_combination e1 - e2

/-- **The whole affine line is reconstructed off `T`.** From a common support, `Fold α f = ge + α·go`
at every fibre outside `T`, for EVERY challenge `α` — the line lies inside the common support-span. -/
theorem commonSupport_line (S : FriSetup F ι κ) {f : ι → F} {α₁ α₂ : F} (hα : α₁ ≠ α₂)
    {T : Finset κ} {g₁ g₂ : κ → F} (hg₁ : g₁ ∈ S.C') (hg₂ : g₂ ∈ S.C')
    (h1 : disagree (Fold S.geom α₁ f) g₁ ⊆ T) (h2 : disagree (Fold S.geom α₂ f) g₂ ⊆ T) :
    ∃ ge ∈ S.C', ∃ go ∈ S.C', ∀ α : F, ∀ y ∉ T, Fold S.geom α f y = ge y + α * go y := by
  obtain ⟨ge, hge, go, hgo, hoff⟩ := commonSupport_pointwise S hα hg₁ hg₂ h1 h2
  refine ⟨ge, hge, go, hgo, fun α y hy => ?_⟩
  obtain ⟨hE, hO⟩ := hoff y hy
  simp only [Fold, hE, hO]

/-- **Agreement-count form:** the reconstruction agrees with `(E f, O f)` on at least `|κ| − |T|`
fibres. -/
theorem commonSupport_agree_card (S : FriSetup F ι κ) {f : ι → F} {α₁ α₂ : F} (hα : α₁ ≠ α₂)
    {T : Finset κ} {g₁ g₂ : κ → F} (hg₁ : g₁ ∈ S.C') (hg₂ : g₂ ∈ S.C')
    (h1 : disagree (Fold S.geom α₁ f) g₁ ⊆ T) (h2 : disagree (Fold S.geom α₂ f) g₂ ⊆ T) :
    ∃ ge ∈ S.C', ∃ go ∈ S.C',
      Fintype.card κ - T.card ≤
        (Finset.univ.filter (fun y : κ => E S.geom f y = ge y ∧ O S.geom f y = go y)).card := by
  obtain ⟨ge, hge, go, hgo, hoff⟩ := commonSupport_pointwise S hα hg₁ hg₂ h1 h2
  refine ⟨ge, hge, go, hgo, ?_⟩
  have hsub : Tᶜ ⊆ Finset.univ.filter (fun y : κ => E S.geom f y = ge y ∧ O S.geom f y = go y) := by
    intro y hy
    rw [Finset.mem_compl] at hy
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hoff y hy⟩
  have hcompl : Fintype.card κ - T.card = Tᶜ.card := by rw [Finset.card_compl]
  rw [hcompl]
  exact Finset.card_le_card hsub

/-- **Shared support ⇒ SHARP (δ-preserving) correlated agreement.** A common support `T` of size
`≤ dIn` gives agreement on `≥ |κ| − dIn` fibres — the sharp floor, strictly beyond the two-point
`|κ| − 2·dIn` of `correlatedAgreementLine_twoPoint`, because a common (not unioned) support does not
double. -/
theorem sharedSupport_sharpAgree (S : FriSetup F ι κ) {dIn : ℕ} {f : ι → F} {α₁ α₂ : F} (hα : α₁ ≠ α₂)
    {T : Finset κ} (hT : T.card ≤ dIn) {g₁ g₂ : κ → F} (hg₁ : g₁ ∈ S.C') (hg₂ : g₂ ∈ S.C')
    (h1 : disagree (Fold S.geom α₁ f) g₁ ⊆ T) (h2 : disagree (Fold S.geom α₂ f) g₂ ⊆ T) :
    ∃ ge ∈ S.C', ∃ go ∈ S.C',
      Fintype.card κ - dIn ≤
        (Finset.univ.filter (fun y : κ => E S.geom f y = ge y ∧ O S.geom f y = go y)).card := by
  obtain ⟨ge, hge, go, hgo, hcard⟩ := commonSupport_agree_card S hα hg₁ hg₂ h1 h2
  refine ⟨ge, hge, go, hgo, le_trans ?_ hcard⟩
  omega

/-- **`IncidenceDesign S dIn f Good`** — the structure a correlated-agreement counterexample MUST
have: every good challenge `α ∈ Good` is caught by its OWN support `Tof α` of size `≤ dIn` (the
fold-error of some folded codeword), and the supports are pairwise DISTINCT (`Set.InjOn`). This is
"many good challenges scattered across many different support-spans, no common one", in the tower's
Hamming vocabulary. -/
def IncidenceDesign (S : FriSetup F ι κ) (dIn : ℕ) (f : ι → F) (Good : Finset F) : Prop :=
  ∃ Tof : F → Finset κ,
    (∀ α ∈ Good, (Tof α).card ≤ dIn ∧ ∃ g ∈ S.C', disagree (Fold S.geom α f) g = Tof α) ∧
    Set.InjOn Tof (↑Good : Set F)

/-- **The dichotomy.** For any word `f` and any set `Good` of folding challenges each folding `f`
within `dIn` of the folded code, EITHER two of them share a support — forcing SHARP correlated
agreement (`≥ |κ| − dIn` common fibres) — OR the good set is an `IncidenceDesign`. Contrapositive: a
correlated-agreement counterexample (no common `(ge, go)` reaching the sharp floor) is necessarily an
incidence design of pairwise-distinct supports. -/
theorem sharpAgree_or_incidenceDesign (S : FriSetup F ι κ) {dIn : ℕ} {f : ι → F}
    (Good : Finset F) (hGood : ∀ α ∈ Good, closeN S.C' dIn (Fold S.geom α f)) :
    (∃ ge ∈ S.C', ∃ go ∈ S.C',
        Fintype.card κ - dIn ≤
          (Finset.univ.filter (fun y : κ => E S.geom f y = ge y ∧ O S.geom f y = go y)).card)
    ∨ IncidenceDesign S dIn f Good := by
  classical
  -- for each good challenge, choose a nearby folded codeword `gof α` (support `≤ dIn`)
  choose! gof hgof_mem hgof_card using hGood
  set Tof : F → Finset κ := fun α => disagree (Fold S.geom α f) (gof α) with hTof
  by_cases hinj : Set.InjOn Tof (↑Good : Set F)
  · -- distinct supports: an incidence design
    right
    refine ⟨Tof, fun α hα => ⟨hgof_card α hα, gof α, hgof_mem α hα, rfl⟩, hinj⟩
  · -- a collision: two good challenges share a support ⇒ sharp correlated agreement
    left
    rw [Set.InjOn] at hinj
    push_neg at hinj
    obtain ⟨α₁, hα₁, α₂, hα₂, hTeq, hne⟩ := hinj
    have hmem1 : α₁ ∈ Good := Finset.mem_coe.mp hα₁
    have hmem2 : α₂ ∈ Good := Finset.mem_coe.mp hα₂
    refine sharedSupport_sharpAgree S hne (T := Tof α₁) (hgof_card α₁ hmem1)
      (hgof_mem α₁ hmem1) (hgof_mem α₂ hmem2) (Finset.Subset.refl _) ?_
    -- `disagree (Fold α₂ f) (gof α₂) = Tof α₂ = Tof α₁`
    rw [hTeq]

/-! ## Teeth -/

/-- **FIRE (non-vacuity).** An honest word `f ∈ C` folds to a codeword at every challenge, so any two
challenges share the EMPTY support and the reconstruction agrees EVERYWHERE (`|κ| − 0` fibres). The
`sharedSupport_sharpAgree` conclusion is inhabited on concrete data. -/
theorem sharedSupport_sharpAgree_fires (S : FriSetup F ι κ) {f : ι → F} (hf : f ∈ S.C)
    {α₁ α₂ : F} (hα : α₁ ≠ α₂) :
    ∃ ge ∈ S.C', ∃ go ∈ S.C',
      Fintype.card κ - 0 ≤
        (Finset.univ.filter (fun y : κ => E S.geom f y = ge y ∧ O S.geom f y = go y)).card := by
  have hfold : ∀ α : F, Fold S.geom α f ∈ S.C' := by
    intro α
    have hE := S.foldE_mem f hf
    have hO := S.foldO_mem f hf
    have hEq : Fold S.geom α f = E S.geom f + α • O S.geom f := by
      funext y; simp [Fold, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hEq]; exact S.C'.add_mem hE (S.C'.smul_mem α hO)
  have hself : ∀ α : F, disagree (Fold S.geom α f) (Fold S.geom α f) ⊆ (∅ : Finset κ) := by
    intro α; rw [disagree_eq_empty_iff.mpr rfl]
  exact sharedSupport_sharpAgree S hα (T := (∅ : Finset κ)) (by simp)
    (hfold α₁) (hfold α₂) (hself α₁) (hself α₂)

/-- **Arithmetic gap (why a common support is worth having).** A modest fact, honestly a truism:
the sharp floor `|κ| − dIn` this file reaches from a COMMON support is strictly above the union floor
`|κ| − 2·dIn` that `correlatedAgreementLine_twoPoint` gets from two per-challenge supports, whenever
`dIn > 0` and `2·dIn ≤ |κ|`. This only compares the two bounds; it is NOT a canary and does not by
itself show the common-support hypothesis is indispensable (that would need a concrete `f` with
disjoint supports meeting the union bound but failing the sharp one). -/
theorem sharp_floor_above_union_floor {dIn n : ℕ} (hd : 0 < dIn) (hn : 2 * dIn ≤ n) :
    n - 2 * dIn < n - dIn := by
  omega

#assert_axioms commonSupport_pointwise
#assert_axioms commonSupport_line
#assert_axioms commonSupport_agree_card
#assert_axioms sharedSupport_sharpAgree
#assert_axioms sharpAgree_or_incidenceDesign
#assert_axioms sharedSupport_sharpAgree_fires

end Dregg2.Circuit.FriIncidenceDesign
