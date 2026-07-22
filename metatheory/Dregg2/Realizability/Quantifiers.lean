/-
# Dregg2.Realizability.Quantifiers — exact adjoints on the fragment where they exist directly.

For the indexed predicates `I → Set A` with ONE uniform tracker, existential quantification along
an arbitrary map is the ordinary union over its fibers.  It is a left adjoint to reindexing with
the very same tracker in both directions.

The direct universal construction is intersection over a fiber.  Its right-adjoint law is proved
for SURJECTIVE maps.  Surjectivity matters: it supplies a point in every fiber at which the common
tracker is known to be defined; functionality of PCA application then identifies the outputs at
all other points in that fiber.  We do not claim this construction is a right adjoint for arbitrary
maps with mixed empty/nonempty fibers.  Arbitrary-map universals need a richer coding/realizer
construction and remain outside this module.

Both quantifiers satisfy exact Beck–Chevalley equalities for weak pullback squares.  A pullback of
a surjection is again surjective, so the proven universal adjunction is stable under base change.
-/
import Dregg2.Realizability.IndexedPredicates

namespace Dregg2.Realizability

universe u v w x y

/-- Existential image along `f`: union of the realizer sets over the fiber of `i`. -/
def existsAlong (P : PCA.{u}) {J : Type v} {I : Type w} (f : J → I)
    (φ : Pred P J) : Pred P I := fun i a =>
  ∃ j, f j = i ∧ a ∈ φ j

/-- Uniform intersection over the fiber of `f`.  The right-adjoint theorem below requires `f`
surjective. -/
def forallAlong (P : PCA.{u}) {J : Type v} {I : Type w} (f : J → I)
    (φ : Pred P J) : Pred P I := fun i a =>
  ∀ j, f j = i → a ∈ φ j

/-! ## Adjunctions -/

/-- Existential image is a left adjoint to reindexing along every set map. -/
theorem existsAlong_adjunction (P : PCA.{u}) {J : Type v} {I : Type w}
    (f : J → I) (φ : Pred P J) (ψ : Pred P I) :
    Entails P (existsAlong P f φ) ψ ↔ Entails P φ (reindex P f ψ) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    intro j a ha
    exact he (f j) a ⟨j, rfl, ha⟩
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    intro i a ha
    rcases ha with ⟨j, hfj, haj⟩
    rcases he j a haj with ⟨b, hab, hb⟩
    exact ⟨b, hab, by simpa [reindex, hfj] using hb⟩

/-- Uniform fiber intersection is a right adjoint to reindexing along a surjection. -/
theorem forallAlong_adjunction_of_surjective (P : PCA.{u})
    {J : Type v} {I : Type w} (f : J → I) (hf : Function.Surjective f)
    (φ : Pred P J) (ψ : Pred P I) :
    Entails P (reindex P f ψ) φ ↔ Entails P ψ (forallAlong P f φ) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    intro i a ha
    rcases hf i with ⟨j₀, hj₀⟩
    have ha₀ : a ∈ (reindex P f ψ) j₀ := by
      simpa [reindex, hj₀] using ha
    rcases he j₀ a ha₀ with ⟨b, hab, hb₀⟩
    refine ⟨b, hab, ?_⟩
    intro j hj
    have haj : a ∈ (reindex P f ψ) j := by
      simpa [reindex, hj] using ha
    rcases he j a haj with ⟨b', hab', hb'⟩
    have hbb' : b' = b := P.app_functional hab' hab
    simpa [hbb'] using hb'
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    intro j a ha
    rcases he (f j) a ha with ⟨b, hab, hb⟩
    exact ⟨b, hab, hb j rfl⟩

/-- Product projection is the most common finite/bounded universal.  A supplied point of the
quantified type makes the projection surjective; no unspoken code for arbitrary indices is used. -/
theorem forall_fst_adjunction (P : PCA.{u}) {I : Type v} {K : Type w} (k₀ : K)
    (φ : Pred P (I × K)) (ψ : Pred P I) :
    Entails P (reindex P Prod.fst ψ) φ ↔
      Entails P ψ (forallAlong P Prod.fst φ) := by
  apply forallAlong_adjunction_of_surjective P Prod.fst
  intro i
  exact ⟨(i, k₀), rfl⟩

/-! ## Identity and composition laws -/

@[simp] theorem existsAlong_id (P : PCA.{u}) {I : Type v} (φ : Pred P I) :
    existsAlong P id φ = φ := by
  ext i a
  constructor
  · rintro ⟨j, hj, ha⟩
    change j = i at hj
    subst j
    exact ha
  · intro ha
    exact ⟨i, rfl, ha⟩

@[simp] theorem forallAlong_id (P : PCA.{u}) {I : Type v} (φ : Pred P I) :
    forallAlong P id φ = φ := by
  ext i a
  constructor
  · intro hall
    exact hall i rfl
  · intro ha j hj
    change j = i at hj
    subst j
    exact ha

theorem existsAlong_comp (P : PCA.{u}) {K : Type v} {J : Type w} {I : Type x}
    (g : K → J) (f : J → I) (φ : Pred P K) :
    existsAlong P (f ∘ g) φ = existsAlong P f (existsAlong P g φ) := by
  ext i a
  constructor
  · rintro ⟨k, hk, ha⟩
    exact ⟨g k, hk, k, rfl, ha⟩
  · rintro ⟨j, hfj, k, hgk, ha⟩
    exact ⟨k, by simp only [Function.comp_apply, hgk, hfj], ha⟩

theorem forallAlong_comp (P : PCA.{u}) {K : Type v} {J : Type w} {I : Type x}
    (g : K → J) (f : J → I) (φ : Pred P K) :
    forallAlong P (f ∘ g) φ = forallAlong P f (forallAlong P g φ) := by
  ext i a
  constructor
  · intro h j hfj k hgk
    exact h k (by simp only [Function.comp_apply, hgk, hfj])
  · intro h k hk
    exact h (g k) hk k rfl

/-! ## Beck–Chevalley for weak pullback squares -/

/-- A commuting square with existence (not uniqueness) of lifts.  Weak pullback is exactly what
the predicate equalities below need; requiring uniqueness would add an unused hypothesis.

```
K --g--> J
|         |
q         f
|         |
v         v
L --h--> I
```
-/
structure IsWeakPullback {K : Type v} {J : Type w} {L : Type x} {I : Type y}
    (g : K → J) (q : K → L) (f : J → I) (h : L → I) : Prop where
  commutes : ∀ k, f (g k) = h (q k)
  lift : ∀ l j, f j = h l → ∃ k, q k = l ∧ g k = j

/-- Existential Beck–Chevalley: pullback then existential image equals existential image then
pullback, as literal predicate families (stronger than mutual entailment). -/
theorem existsAlong_beckChevalley (P : PCA.{u})
    {K : Type v} {J : Type w} {L : Type x} {I : Type y}
    {g : K → J} {q : K → L} {f : J → I} {h : L → I}
    (W : IsWeakPullback g q f h) (φ : Pred P J) :
    reindex P h (existsAlong P f φ) =
      existsAlong P q (reindex P g φ) := by
  ext l a
  constructor
  · rintro ⟨j, hfj, ha⟩
    rcases W.lift l j hfj with ⟨k, hqk, hgk⟩
    exact ⟨k, hqk, by simpa [reindex, hgk] using ha⟩
  · rintro ⟨k, hqk, ha⟩
    refine ⟨g k, ?_, ha⟩
    simpa [hqk] using W.commutes k

/-- Universal Beck–Chevalley for uniform fiber intersections, again as literal equality. -/
theorem forallAlong_beckChevalley (P : PCA.{u})
    {K : Type v} {J : Type w} {L : Type x} {I : Type y}
    {g : K → J} {q : K → L} {f : J → I} {h : L → I}
    (W : IsWeakPullback g q f h) (φ : Pred P J) :
    reindex P h (forallAlong P f φ) =
      forallAlong P q (reindex P g φ) := by
  ext l a
  constructor
  · intro hall k hqk
    exact hall (g k) (by simpa [hqk] using W.commutes k)
  · intro hall j hfj
    rcases W.lift l j hfj with ⟨k, hqk, hgk⟩
    have hk := hall k hqk
    simpa [reindex, hgk] using hk

/-- Base change preserves the surjectivity condition used by the universal adjunction. -/
theorem weakPullback_q_surjective
    {K : Type v} {J : Type w} {L : Type x} {I : Type y}
    {g : K → J} {q : K → L} {f : J → I} {h : L → I}
    (W : IsWeakPullback g q f h) (hf : Function.Surjective f) :
    Function.Surjective q := by
  intro l
  rcases hf (h l) with ⟨j, hfj⟩
  rcases W.lift l j hfj with ⟨k, hqk, hgk⟩
  exact ⟨k, hqk⟩

#assert_all_clean [existsAlong_adjunction, forallAlong_adjunction_of_surjective,
  forall_fst_adjunction, existsAlong_id, forallAlong_id, existsAlong_comp,
  forallAlong_comp, existsAlong_beckChevalley, forallAlong_beckChevalley,
  weakPullback_q_surjective]

end Dregg2.Realizability
