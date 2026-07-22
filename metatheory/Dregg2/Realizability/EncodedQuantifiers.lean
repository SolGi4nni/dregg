/-
# Dregg2.Realizability.EncodedQuantifiers — arbitrary-map adjoints by explicit thunks.

The ordinary union over a fiber gives existential quantification.  Raw intersection over a fiber
does *not* give an arbitrary-map right adjoint for uniformly tracked entailment: over an empty
fiber it asks a tracker to manufacture definedness that the premise never supplied.

The realizability universal below fixes exactly that obstruction.  A universal realizer is a
chosen pair `(e, x)` whose computation `e x` is delayed.  It must produce a realizer of every
actual fiber obligation, but no application is demanded when the fiber is empty.  Introduction
pairs the common tracker with its argument; elimination evaluates the pair.  Thus the chosen
pairing code is the only additional PCA coding assumption, and the right adjunction holds along
every set map.

Both adjoints satisfy literal Beck--Chevalley equality for weak pullback squares.  No choice,
surjectivity, finiteness, or encoding of base indices is hidden in the proofs.
-/
import Dregg2.Realizability.LogicalStructure

namespace Dregg2.Realizability

universe u v w x y

/-- Realizability existential image: union of the realizer sets over a map fiber. -/
def existsReal (P : PCA.{u}) {J : Type v} {I : Type w} (f : J → I)
    (φ : Pred P J) : Pred P I := fun i a =>
  ∃ j, f j = i ∧ a ∈ φ j

/-- Realizability universal image.  Its elements are explicit suspended applications `(e, x)`;
the application is required exactly when an element of the map fiber supplies an obligation. -/
def forallReal (P : PCA.{u}) (C : ChosenPairing P)
    {J : Type v} {I : Type w} (f : J → I) (φ : Pred P J) : Pred P I := fun i r =>
  ∃ e x, r = C.pairVal e x ∧
    ∀ j, f j = i → ∃ b, P.App e x b ∧ b ∈ φ j

/-! ## Arbitrary-map adjunctions -/

/-- Existential image is left adjoint to reindexing along every set map. -/
theorem existsReal_adjunction (P : PCA.{u}) {J : Type v} {I : Type w}
    (f : J → I) (φ : Pred P J) (ψ : Pred P I) :
    Entails P (existsReal P f φ) ψ ↔ Entails P φ (reindex P f ψ) := by
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
    exact ⟨b, hab, by simpa only [reindex, hfj] using hb⟩

/-- The thunked universal image is right adjoint to reindexing along every set map. -/
theorem forallReal_adjunction (P : PCA.{u}) (C : ChosenPairing P)
    {J : Type v} {I : Type w} (f : J → I) (φ : Pred P J) (ψ : Pred P I) :
    Entails P (reindex P f ψ) φ ↔ Entails P ψ (forallReal P C f φ) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨C.pairArg e, ?_⟩
    intro i a ha
    refine ⟨C.pairVal e a, C.app_pairArg e a, e, a, rfl, ?_⟩
    intro j hfj
    have haj : a ∈ (reindex P f ψ) j := by
      simpa only [reindex, hfj] using ha
    exact he j a haj
  · rintro ⟨d, hd⟩
    refine ⟨P.compose C.eval d, ?_⟩
    intro j a ha
    rcases hd (f j) a ha with ⟨r, hdar, hr⟩
    rcases hr with ⟨e, x, rfl, hall⟩
    rcases hall j rfl with ⟨b, hexb, hb⟩
    exact ⟨b, P.app_compose hdar (C.app_eval hexb), hb⟩

/-- Existential quantification over an arbitrary product projection. -/
theorem existsReal_fst_adjunction (P : PCA.{u}) {I : Type v} {K : Type w}
    (φ : Pred P (I × K)) (ψ : Pred P I) :
    Entails P (existsReal P Prod.fst φ) ψ ↔
      Entails P φ (reindex P Prod.fst ψ) :=
  existsReal_adjunction P Prod.fst φ ψ

/-- Universal quantification over an arbitrary product projection, including an empty or finite
quantified type.  No chosen point of `K` is required. -/
theorem forallReal_fst_adjunction (P : PCA.{u}) (C : ChosenPairing P)
    {I : Type v} {K : Type w} (φ : Pred P (I × K)) (ψ : Pred P I) :
    Entails P (reindex P Prod.fst ψ) φ ↔
      Entails P ψ (forallReal P C Prod.fst φ) :=
  forallReal_adjunction P C Prod.fst φ ψ

/-! ## Identity laws at the preorder level -/

@[simp] theorem existsReal_id (P : PCA.{u}) {I : Type v} (φ : Pred P I) :
    existsReal P id φ = φ := by
  apply funext
  intro i
  apply Set.ext
  intro a
  constructor
  · rintro ⟨j, hj, ha⟩
    change j = i at hj
    subst j
    exact ha
  · intro ha
    exact ⟨i, rfl, ha⟩

/-- The thunked universal along identity is equivalent, rather than definitionally equal, to the
original predicate.  This is the correct equality notion in the indexed preorder. -/
theorem forallReal_id_equiprovable (P : PCA.{u}) (C : ChosenPairing P)
    {I : Type v} (φ : Pred P I) : Equiprovable P (forallReal P C id φ) φ := by
  constructor
  · exact (forallReal_adjunction P C id φ (forallReal P C id φ)).mpr
      (entails_refl P (forallReal P C id φ))
  · exact (forallReal_adjunction P C id φ φ).mp
      (entails_refl P φ)

/-! ## Beck--Chevalley -/

/-- A commuting square with existence, but not necessarily uniqueness, of lifts.

```
K --g--> J
|         |
q         f
|         |
v         v
L --h--> I
```

Existence is precisely what the two predicate equalities below use. -/
structure WeakPullbackSquare {K : Type v} {J : Type w} {L : Type x} {I : Type y}
    (g : K → J) (q : K → L) (f : J → I) (h : L → I) : Prop where
  commutes : ∀ k, f (g k) = h (q k)
  lift : ∀ l j, f j = h l → ∃ k, q k = l ∧ g k = j

/-- Existential Beck--Chevalley as literal equality of predicate families. -/
theorem existsReal_beckChevalley (P : PCA.{u})
    {K : Type v} {J : Type w} {L : Type x} {I : Type y}
    {g : K → J} {q : K → L} {f : J → I} {h : L → I}
    (W : WeakPullbackSquare g q f h) (φ : Pred P J) :
    reindex P h (existsReal P f φ) =
      existsReal P q (reindex P g φ) := by
  apply funext
  intro l
  apply Set.ext
  intro a
  constructor
  · rintro ⟨j, hfj, ha⟩
    rcases W.lift l j hfj with ⟨k, hqk, hgk⟩
    exact ⟨k, hqk, by simpa only [reindex, hgk] using ha⟩
  · rintro ⟨k, hqk, ha⟩
    refine ⟨g k, ?_, ha⟩
    rw [W.commutes k, hqk]

/-- Thunked-universal Beck--Chevalley as literal equality of predicate families. -/
theorem forallReal_beckChevalley (P : PCA.{u}) (C : ChosenPairing P)
    {K : Type v} {J : Type w} {L : Type x} {I : Type y}
    {g : K → J} {q : K → L} {f : J → I} {h : L → I}
    (W : WeakPullbackSquare g q f h) (φ : Pred P J) :
    reindex P h (forallReal P C f φ) =
      forallReal P C q (reindex P g φ) := by
  apply funext
  intro l
  apply Set.ext
  intro r
  constructor
  · rintro ⟨e, a, rfl, hall⟩
    refine ⟨e, a, rfl, ?_⟩
    intro k hqk
    rcases hall (g k) (by rw [W.commutes k, hqk]) with ⟨b, heab, hb⟩
    exact ⟨b, heab, hb⟩
  · rintro ⟨e, a, rfl, hall⟩
    refine ⟨e, a, rfl, ?_⟩
    intro j hfj
    rcases W.lift l j hfj with ⟨k, hqk, hgk⟩
    rcases hall k hqk with ⟨b, heab, hb⟩
    exact ⟨b, heab, by simpa only [reindex, hgk] using hb⟩

/-! ## Empty-fiber sanity check -/

/-- Universal quantification over the globally empty map is equivalent to truth.  The forward
tracker merely forgets the thunk; the reverse tracker builds `(I, a)` without evaluating it. -/
theorem forallReal_empty_equiprovable_truth (P : PCA.{u}) (C : ChosenPairing P)
    {I : Type v} (φ : Pred P (I × Fin 0)) :
    Equiprovable P (forallReal P C Prod.fst φ) (truth P) := by
  constructor
  · exact entails_truth P (forallReal P C Prod.fst φ)
  · refine ⟨C.pairArg P.ident, ?_⟩
    intro i a ha
    refine ⟨C.pairVal P.ident a, C.app_pairArg P.ident a, P.ident, a, rfl, ?_⟩
    intro j hj
    exact Fin.elim0 j.2

#assert_all_clean [existsReal_adjunction, forallReal_adjunction,
  existsReal_fst_adjunction, forallReal_fst_adjunction, existsReal_id,
  forallReal_id_equiprovable, existsReal_beckChevalley,
  forallReal_beckChevalley, forallReal_empty_equiprovable_truth]

end Dregg2.Realizability
