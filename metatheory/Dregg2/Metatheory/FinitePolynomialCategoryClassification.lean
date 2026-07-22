/-
# Classification of indexed finite-polynomial category presentations

This module separates two claims which must not be conflated.

* A **single** finite field-power model has finite hom-sets, so a faithful
  functor into it can only represent a locally finite source category.
* A **family-indexed** presentation may choose a finite coordinate type for
  each source hom-set.  Such a presentation exists exactly when the source
  category is locally finite.  Its identity codes are constants and its
  composition operation has an explicit degree-two polynomial realization.

The second statement is a positive arithmetization theorem for category
structure.  It is not a full and faithful strong-CCC embedding into one fixed
finite semantic category: exponential preservation is additional structure,
and an infinite locally finite category may require infinitely many members of
the coordinate family.
-/
import Dregg2.Metatheory.FinitePolynomialFunctionLimits
import Mathlib.CategoryTheory.Category.Basic

namespace Dregg2.Metatheory.FinitePolynomialCategoryClassification

open CategoryTheory
open Dregg2.Metatheory.FinitePolynomialFunctions

open scoped BigOperators

noncomputable section

universe u v w

variable {C : Type u} [Category.{v} C]
variable {F : Type w} [Field F] [Fintype F]

/-! ## The exact boundary: local finiteness -/

/-- A category is locally finite when each of its hom-types is finite.

This is the exact cardinal condition for the family-indexed presentation below.
It is only a necessary condition for a faithful functor into one *fixed*
finite polynomial-function CCC, whose object assignment and exponential
comparison impose further uniformity requirements. -/
class LocallyFiniteHom (C : Type u) [Category.{v} C] : Prop where
  homFinite : ∀ A B : C, Finite (A ⟶ B)

instance homFiniteInstance [LocallyFiniteHom C] (A B : C) : Finite (A ⟶ B) :=
  LocallyFiniteHom.homFinite A B

/-- A faithful family of finite-field coordinate codes, one coordinate type
for each source hom-type.  The coordinates are finite, but need not have one
uniform shape across all object pairs. -/
structure IndexedHomPresentation (C : Type u) [Category.{v} C] (F : Type w) where
  Coord : C → C → Type v
  coordFinite : ∀ A B, Finite (Coord A B)
  encode : ∀ {A B}, (A ⟶ B) → (Coord A B → F)
  encode_injective : ∀ A B, Function.Injective (@encode A B)

namespace IndexedHomPresentation

/-- Every hom-type of a faithfully indexed finite presentation is finite. -/
theorem locallyFinite (P : IndexedHomPresentation C F) : LocallyFiniteHom C where
  homFinite A B := by
    letI : Finite (P.Coord A B) := P.coordFinite A B
    exact Finite.of_injective P.encode (P.encode_injective A B)

/-- Equality of coordinate tables reflects equality of source morphisms. -/
theorem encode_eq_iff (P : IndexedHomPresentation C F) {A B : C} (f g : A ⟶ B) :
    P.encode f = P.encode g ↔ f = g :=
  (P.encode_injective A B).eq_iff

end IndexedHomPresentation

/-! ## The canonical one-hot construction -/

/-- One-hot encoding over an arbitrary index type. -/
def oneHot {H : Type v} (h : H) : H → F := by
  classical
  exact fun k => if k = h then 1 else 0

@[simp] theorem oneHot_self {H : Type v} (h : H) : oneHot (F := F) h h = 1 := by
  simp [oneHot]

theorem oneHot_of_ne {H : Type v} {h k : H} (hk : k ≠ h) :
    oneHot (F := F) h k = 0 := by
  simp [oneHot, hk]

/-- One-hot coding is faithful over every nontrivial field. -/
theorem oneHot_injective {H : Type v} :
    Function.Injective (oneHot (F := F) : H → (H → F)) := by
  intro h k heq
  by_contra hne
  have hcoord := congrFun heq h
  have hhk : h ≠ k := hne
  have : (1 : F) = 0 := by
    simpa [oneHot, hhk] using hcoord
  exact one_ne_zero this

/-- Every locally finite category has a faithful family-indexed presentation
over the one fixed field `F`: use the source hom-type itself as coordinates and
encode each arrow by its one-hot vector. -/
def oneHotPresentation [LocallyFiniteHom C] : IndexedHomPresentation C F where
  Coord A B := A ⟶ B
  coordFinite A B := inferInstance
  encode := oneHot
  encode_injective A B := oneHot_injective

/-- Exact classification: a faithful family-indexed finite-field presentation
exists if and only if the category is locally finite. -/
theorem indexedPresentation_nonempty_iff_locallyFinite :
    Nonempty (IndexedHomPresentation C F) ↔ LocallyFiniteHom C := by
  constructor
  · rintro ⟨P⟩
    exact IndexedHomPresentation.locallyFinite P
  · intro h
    letI : LocallyFiniteHom C := h
    exact ⟨oneHotPresentation (C := C) (F := F)⟩

/-! ## Polynomial realization of the category operations -/

/-- A morphism code is already a vector of constant polynomials on the
zero-coordinate terminal field power. -/
def morphismCodePolynomial {A B : C} (f : A ⟶ B) (h : A ⟶ B) :
    MvPolynomial Empty F :=
  MvPolynomial.C (oneHot (F := F) f h)

/-- Evaluating the constant code polynomial gives the one-hot morphism code. -/
@[simp] theorem eval_morphismCodePolynomial {A B : C} (f h : A ⟶ B)
    (x : Empty → F) :
    MvPolynomial.eval x (morphismCodePolynomial (F := F) f h) =
      oneHot (F := F) f h := by
  simp [morphismCodePolynomial]

/-- A finite enumeration hidden behind the proposition-valued `Finite`
interface, so the public construction does not require a chosen enumeration. -/
def allElements (H : Type v) [Finite H] : Finset H := by
  letI := Fintype.ofFinite H
  exact Finset.univ

@[simp] theorem mem_allElements {H : Type v} [Finite H] (h : H) :
    h ∈ allElements H := by
  classical
  simp [allElements]

/-- The output coordinate of categorical composition as a degree-two
polynomial in the one-hot codes of the two input morphisms.

The coordinate `h : A ⟶ D` receives the sum of `x_f * y_g` over all pairs
whose categorical composite is `h`. -/
def compositionPolynomial [LocallyFiniteHom C]
    {A B D : C} (h : A ⟶ D) :
    MvPolynomial ((A ⟶ B) ⊕ (B ⟶ D)) F :=
  ∑ f ∈ allElements (A ⟶ B), ∑ g ∈ allElements (B ⟶ D),
    MvPolynomial.C (oneHot (F := F) (f ≫ g) h) *
      MvPolynomial.X (Sum.inl f) * MvPolynomial.X (Sum.inr g)

/-- The composition polynomial is exact on valid one-hot morphism codes. -/
@[simp] theorem eval_compositionPolynomial [LocallyFiniteHom C]
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D) :
    MvPolynomial.eval
        (pack (oneHot (F := F) f) (oneHot (F := F) g))
        (compositionPolynomial (F := F) h) =
      oneHot (F := F) (f ≫ g) h := by
  classical
  simp only [compositionPolynomial, MvPolynomial.eval_sum,
    MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    pack, Sum.elim_inl, Sum.elim_inr]
  rw [Finset.sum_eq_single f]
  · rw [Finset.sum_eq_single g]
    · simp
    · intro b _ hbg
      simp [oneHot, hbg]
    · intro hg
      exact False.elim (hg (mem_allElements g))
  · intro a _ haf
    simp [oneHot, haf]
  · intro hf
    exact False.elim (hf (mem_allElements f))

/-- Identity is represented by the ordinary morphism code of `𝟙 A`. -/
def identityPolynomial (A : C) (h : A ⟶ A) : MvPolynomial Empty F :=
  morphismCodePolynomial (F := F) (𝟙 A) h

@[simp] theorem eval_identityPolynomial (A : C) (h : A ⟶ A) (x : Empty → F) :
    MvPolynomial.eval x (identityPolynomial (F := F) A h) =
      oneHot (F := F) (𝟙 A) h := by
  simp [identityPolynomial]

/-! ## The sharp distinction from a single finite semantic model -/

/-- A faithful encoding of even one source hom-type into one fixed finite
field-power function space forces that hom-type to be finite.  Applied to every
object pair, this is the local-finiteness obstruction for a single fixed-shape
model. -/
theorem fixedShape_forces_finite {A B : C} {σ τ : Type*}
    [Fintype σ] [Fintype τ]
    (encode : (A ⟶ B) → ((σ → F) → (τ → F)))
    (hinj : Function.Injective encode) :
    Finite (A ⟶ B) :=
  Finite.of_injective encode hinj

#assert_all_clean [IndexedHomPresentation.locallyFinite,
  IndexedHomPresentation.encode_eq_iff, oneHot_self, oneHot_of_ne,
  oneHot_injective, indexedPresentation_nonempty_iff_locallyFinite,
  eval_morphismCodePolynomial, eval_compositionPolynomial,
  eval_identityPolynomial, fixedShape_forces_finite]

end

end Dregg2.Metatheory.FinitePolynomialCategoryClassification
