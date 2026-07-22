/-
# The family-polynomial Yoneda frontier

There are three materially different meanings of "arithmetize a cartesian
closed category".

1. A source category may be encoded faithfully, hom-set by hom-set.
2. Its chosen cartesian closed structure may be preserved by a semantic
   embedding.
3. The resulting family may admit one finite, computable and cryptographically
   bound verifier.

The first two statements have a sharp positive synthesis.  If a small category
is locally finite, every representable `C(X,A)` is finite.  Yoneda therefore
becomes a family of finite sets, and postcomposition by `f : A ⟶ B` is a
degree-one polynomial on one-hot coordinates.  If `C` is cartesian closed,
ordinary Yoneda is fully faithful and strongly preserves the chosen products
and exponentials.

The third statement does *not* follow.  A uniform coordinate budget forces a
uniform cardinal bound on all hom-sets.  The cartesian closed category of finite
sets is locally finite but has hom-sets of unbounded size, so no such budget can
encode it faithfully over a fixed finite field.  Moreover, `Finite` supplies no
algorithmic enumeration, and a cryptographic commitment requires a separate
binding assumption.

Thus arbitrary small locally-finite CCCs do have an exact family-polynomial
Yoneda presentation.  What fails in general is its compression into one fixed
finite/succinct cryptographic instance.
-/
import Dregg2.Metatheory.FinitePolynomialCategoryClassification
import Dregg2.Metatheory.SmallCCCYonedaPresheaf
import Mathlib.CategoryTheory.FintypeCat

namespace Dregg2.Metatheory.FamilyPolynomialYonedaFrontier

open CategoryTheory
open Dregg2.Metatheory.FinitePolynomialFunctions
open Dregg2.Metatheory.FinitePolynomialCategoryClassification

open scoped BigOperators

noncomputable section

universe u v w

variable {C : Type u} [Category.{v} C]
variable {F : Type w} [Field F] [Fintype F]

/-! ## 1. Representables as a family of finite field powers -/

/-- The component at the probe `X` of the representable object `y A`.

Under local finiteness this is a finite coordinate type, even when the set of
all probes is infinite. -/
abbrev YonedaCoord (X A : C) := X ⟶ A

/-- The one-hot field vector representing `a : y A (X)`. -/
def yonedaCode {X A : C} (a : X ⟶ A) : YonedaCoord X A → F :=
  oneHot a

/-- The ordinary covariant action of a representable on a source arrow. -/
def yonedaAction {A B : C} (f : A ⟶ B) (X : C) :
    YonedaCoord X A → YonedaCoord X B :=
  fun a ↦ a ≫ f

@[simp] theorem yonedaAction_id {X A : C} (a : YonedaCoord X A) :
    yonedaAction (𝟙 A) X a = a := by
  simp [yonedaAction]

@[simp] theorem yonedaAction_comp {X A B D : C} (f : A ⟶ B) (g : B ⟶ D)
    (a : YonedaCoord X A) :
    yonedaAction (f ≫ g) X a = yonedaAction g X (yonedaAction f X a) := by
  simp [yonedaAction]

/-- The Yoneda action at the *single probe `A`* already reflects a morphism
`f : A ⟶ B`: evaluate it at `𝟙 A`.  No infinite search through probes is
needed to distinguish two parallel source arrows. -/
theorem yonedaAction_atSource_injective {A B : C} :
    Function.Injective (fun f : A ⟶ B ↦ yonedaAction f A) := by
  intro f g h
  have hid := congrFun h (𝟙 A)
  simpa [yonedaAction] using hid

/-- Equality of parallel arrows is exactly one semantic Yoneda query. -/
theorem eq_iff_identityProbe {A B : C} (f g : A ⟶ B) :
    f = g ↔ yonedaAction f A (𝟙 A) = yonedaAction g A (𝟙 A) := by
  simp [yonedaAction]

/-! ## 2. The linear polynomial action -/

/-- Coordinate `b` of postcomposition by `f`, as a polynomial in the one-hot
coordinates of `a : X ⟶ A`.

This is a matrix-vector product: the coefficient of `X_a` is one precisely
when `a ≫ f = b`.  In particular, this construction is linear, unlike the
degree-two polynomial needed when *both* composands are variable. -/
def actionPolynomial [LocallyFiniteHom C]
    {A B : C} (f : A ⟶ B) (X : C) (b : X ⟶ B) :
    MvPolynomial (X ⟶ A) F :=
  ∑ a ∈ allElements (X ⟶ A),
    MvPolynomial.C (oneHot (F := F) (a ≫ f) b) * MvPolynomial.X a

omit [Fintype F] in
/-- The representable action really is degree at most one as formal
polynomial syntax, not merely extensionally on the one-hot locus. -/
theorem actionPolynomial_totalDegree_le_one [LocallyFiniteHom C]
    {A B : C} (f : A ⟶ B) (X : C) (b : X ⟶ B) :
    (actionPolynomial (F := F) f X b).totalDegree ≤ 1 := by
  classical
  rw [actionPolynomial]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a _
  calc
    (MvPolynomial.C (oneHot (F := F) (a ≫ f) b) *
        MvPolynomial.X a).totalDegree ≤
        (MvPolynomial.C (oneHot (F := F) (a ≫ f) b)).totalDegree +
          (MvPolynomial.X a).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ = 1 := by simp

/-- The linear polynomial computes representable postcomposition exactly on
every valid one-hot code. -/
@[simp] theorem eval_actionPolynomial [LocallyFiniteHom C]
    {A B X : C} (f : A ⟶ B) (a : X ⟶ A) (b : X ⟶ B) :
    MvPolynomial.eval (yonedaCode (F := F) a) (actionPolynomial (F := F) f X b) =
      yonedaCode (F := F) (a ≫ f) b := by
  classical
  simp only [actionPolynomial, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [Finset.sum_eq_single a]
  · simp [yonedaCode]
  · intro a' _ hne
    simp [yonedaCode, oneHot, hne]
  · intro ha
    exact False.elim (ha (mem_allElements a))

/-- A faithful hom-family together with polynomial representable action of
every source arrow on every representable probe.

Unlike a bare `IndexedHomPresentation`, this record knows that categorical
postcomposition is realized by the polynomial family. -/
structure FamilyPolynomialCategoryPresentation
    (C : Type u) [Category.{v} C] (F : Type w) [Field F] [Fintype F]
    extends IndexedHomPresentation C F where
  action : ∀ {A B : C}, (A ⟶ B) → (X : C) →
    Coord X B → MvPolynomial (Coord X A) F
  action_exact : ∀ {A B X : C} (f : A ⟶ B) (a : X ⟶ A) (b : Coord X B),
    MvPolynomial.eval (encode a) (action f X b) = encode (a ≫ f) b

/-- The canonical polynomial Yoneda family of a locally finite category. -/
def familyPolynomialYonedaPresentation [LocallyFiniteHom C] :
    FamilyPolynomialCategoryPresentation C F where
  Coord X A := X ⟶ A
  coordFinite X A := inferInstanceAs (Finite (X ⟶ A))
  encode := oneHot
  encode_injective X A :=
    show Function.Injective (oneHot (F := F) : (X ⟶ A) → ((X ⟶ A) → F)) from
      oneHot_injective
  action := actionPolynomial
  action_exact := eval_actionPolynomial

namespace FamilyPolynomialCategoryPresentation

/-- The polynomial action structure still forces local finiteness, since its
underlying hom encodings are finite and faithful. -/
theorem locallyFinite (P : FamilyPolynomialCategoryPresentation C F) :
    LocallyFiniteHom C :=
  P.toIndexedHomPresentation.locallyFinite

end FamilyPolynomialCategoryPresentation

/-- **Exact classification of family-polynomial category arithmetization.**

A small category admits faithful finite-field coordinates with exact
polynomial representable action if and only if every hom-set is finite. -/
theorem familyPolynomialPresentation_nonempty_iff_locallyFinite :
    Nonempty (FamilyPolynomialCategoryPresentation C F) ↔ LocallyFiniteHom C := by
  constructor
  · rintro ⟨P⟩
    exact P.locallyFinite
  · intro h
    letI : LocallyFiniteHom C := h
    exact ⟨familyPolynomialYonedaPresentation (C := C) (F := F)⟩

/-- The whole output vector of the polynomial action. -/
def polynomialAction [LocallyFiniteHom C]
    {A B : C} (f : A ⟶ B) (X : C) (x : (X ⟶ A) → F) : (X ⟶ B) → F :=
  fun b ↦ MvPolynomial.eval x (actionPolynomial (F := F) f X b)

@[simp] theorem polynomialAction_oneHot [LocallyFiniteHom C]
    {A B X : C} (f : A ⟶ B) (a : X ⟶ A) :
    polynomialAction (F := F) f X (yonedaCode (F := F) a) =
      yonedaCode (F := F) (a ≫ f) := by
  funext b
  exact eval_actionPolynomial f a b

/-- Polynomial representable actions obey identity on valid codes. -/
@[simp] theorem polynomialAction_id_onCode [LocallyFiniteHom C]
    {X A : C} (a : X ⟶ A) :
    polynomialAction (F := F) (𝟙 A) X (yonedaCode (F := F) a) =
      yonedaCode (F := F) a := by
  simp

/-- Polynomial representable actions obey composition on valid codes. -/
@[simp] theorem polynomialAction_comp_onCode [LocallyFiniteHom C]
    {X A B D : C} (f : A ⟶ B) (g : B ⟶ D) (a : X ⟶ A) :
    polynomialAction (F := F) (f ≫ g) X (yonedaCode (F := F) a) =
      polynomialAction (F := F) g X
        (polynomialAction (F := F) f X (yonedaCode (F := F) a)) := by
  simp

/-- Equality of source arrows is reflected by equality of their polynomial
output at the one finite identity probe. -/
theorem polynomial_identityProbe_iff [LocallyFiniteHom C]
    {A B : C} (f g : A ⟶ B) :
    polynomialAction (F := F) f A (yonedaCode (F := F) (𝟙 A)) =
        polynomialAction (F := F) g A (yonedaCode (F := F) (𝟙 A)) ↔
      f = g := by
  rw [polynomialAction_oneHot, polynomialAction_oneHot]
  simp only [Category.id_comp]
  change oneHot (F := F) f = oneHot (F := F) g ↔ f = g
  exact (oneHot_injective (F := F)).eq_iff

/-! ## 3. Strong CCC preservation is semantic, not a size claim -/

open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed

/-- The semantic embedding paired with the polynomial family is fully
faithful, not merely faithful on individual encoded hom-sets. -/
def familyYonedaFullyFaithful {D : Type u} [Category.{u} D] :
    (yoneda (C := D)).FullyFaithful :=
  SmallCCCYonedaPresheaf.yonedaFullyFaithful

/-- The family-polynomial action above and the fully faithful Yoneda embedding
describe the same source postcomposition operation. -/
theorem polynomialAction_is_yoneda [LocallyFiniteHom C]
    {A B X : C} (f : A ⟶ B) (a : X ⟶ A) :
    polynomialAction (F := F) f X (yonedaCode (F := F) a) =
      yonedaCode (F := F) (yonedaAction f X a) := by
  simp [yonedaAction]

/-- For a small CCC, Yoneda's exponential comparison is an isomorphism.

Together with `polynomialAction_is_yoneda`, this is the positive
generalization: arbitrary *locally finite* small CCCs have a faithful family of
finite-field polynomial actions and their chosen exponentials are preserved
strongly in presheaves.  The codomain presheaf topos, and usually the family of
probes, are not finite. -/
def familyYonedaExponentialIso
    {D : Type u} [Category.{u} D]
    [CartesianMonoidalCategory D] [MonoidalClosed D] (A B : D) :
    yoneda.obj ((ihom A).obj B) ≅
      (ihom (yoneda.obj A)).obj (yoneda.obj B) :=
  SmallCCCYonedaPresheaf.smallCCCYonedaExponentialIso A B

/-! ## 4. Computability is extra structure -/

/-- Effective local finiteness chooses enumerations and equality procedures.

`LocallyFiniteHom` alone is proposition-valued and its canonical polynomial
construction uses classical `Fintype.ofFinite`.  This stronger record is the
minimum data needed to enumerate the action matrix as an executable artifact.
-/
class EffectiveLocallyFiniteHom (C : Type u) [Category.{v} C] where
  homFintype : ∀ A B : C, Fintype (A ⟶ B)
  homDecidableEq : ∀ A B : C, DecidableEq (A ⟶ B)

namespace EffectiveLocallyFiniteHom

instance [EffectiveLocallyFiniteHom C] (A B : C) : Fintype (A ⟶ B) :=
  EffectiveLocallyFiniteHom.homFintype A B

instance [EffectiveLocallyFiniteHom C] (A B : C) : DecidableEq (A ⟶ B) :=
  EffectiveLocallyFiniteHom.homDecidableEq A B

theorem locallyFinite [EffectiveLocallyFiniteHom C] : LocallyFiniteHom C where
  homFinite A B := inferInstanceAs (Finite (A ⟶ B))

end EffectiveLocallyFiniteHom

/-- Executable enumeration of the same linear action matrix, when explicit
finite hom data is supplied. -/
def effectiveActionPolynomial [EffectiveLocallyFiniteHom C]
    {A B : C} (f : A ⟶ B) (X : C) (b : X ⟶ B) :
    MvPolynomial (X ⟶ A) F :=
  ∑ a : X ⟶ A,
    MvPolynomial.C (if a ≫ f = b then 1 else 0) * MvPolynomial.X a

omit [Fintype F] in
@[simp] theorem eval_effectiveActionPolynomial [EffectiveLocallyFiniteHom C]
    {A B X : C} (f : A ⟶ B) (a : X ⟶ A) (b : X ⟶ B) :
    MvPolynomial.eval (yonedaCode (F := F) a)
        (effectiveActionPolynomial (F := F) f X b) =
      yonedaCode (F := F) (a ≫ f) b := by
  classical
  simp only [effectiveActionPolynomial, MvPolynomial.eval_sum,
    MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [Finset.sum_eq_single a]
  · simp [yonedaCode, oneHot, eq_comm]
  · intro a' _ hne
    simp [yonedaCode, oneHot, hne]
  · simp

/-! ## 5. Uniform succinctness has a stronger obstruction -/

/-- A family-indexed presentation with one global coordinate budget.

This is strictly stronger than `IndexedHomPresentation`: its coordinate types
may vary with `(A,B)`, but their cardinalities are all bounded by `budget`. -/
structure UniformIndexedHomPresentation
    (C : Type u) [Category.{v} C] (F : Type w) [Field F] [Fintype F]
    (budget : ℕ) extends IndexedHomPresentation C F where
  coord_card_le : ∀ A B, Nat.card (Coord A B) ≤ budget

namespace UniformIndexedHomPresentation

/-- A uniform coordinate budget imposes a uniform exponential bound on every
source hom-set. -/
theorem hom_card_le (P : UniformIndexedHomPresentation C F budget) (A B : C) :
    Nat.card (A ⟶ B) ≤ Nat.card F ^ budget := by
  letI : Finite (P.Coord A B) := P.coordFinite A B
  calc
    Nat.card (A ⟶ B) ≤ Nat.card (P.Coord A B → F) :=
      Nat.card_le_card_of_injective P.encode (P.encode_injective A B)
    _ = Nat.card F ^ Nat.card (P.Coord A B) := Nat.card_fun
    _ ≤ Nat.card F ^ budget := by
      exact Nat.pow_le_pow_right (Nat.card_pos) (P.coord_card_le A B)

end UniformIndexedHomPresentation

/-! ## 6. The finite-set CCC is the sharp counterexample to uniformity -/

namespace FiniteSetCCC

/-- Chosen terminal finite set. -/
abbrev terminal : FintypeCat.{0} := FintypeCat.of PUnit

/-- Chosen binary product of finite sets. -/
abbrev product (A B : FintypeCat.{0}) : FintypeCat.{0} := FintypeCat.of (A × B)

/-- Chosen exponential of finite sets. -/
abbrev exponential (A B : FintypeCat.{0}) : FintypeCat.{0} := FintypeCat.of (A → B)

def terminate (A : FintypeCat.{0}) : A ⟶ terminal :=
  FintypeCat.homMk fun _ ↦ PUnit.unit

def fst (A B : FintypeCat.{0}) : product A B ⟶ A :=
  FintypeCat.homMk Prod.fst

def snd (A B : FintypeCat.{0}) : product A B ⟶ B :=
  FintypeCat.homMk Prod.snd

def pair {X A B : FintypeCat.{0}} (f : X ⟶ A) (g : X ⟶ B) :
    X ⟶ product A B :=
  FintypeCat.homMk fun x ↦ (f x, g x)

def evaluation (A B : FintypeCat.{0}) : product (exponential A B) A ⟶ B :=
  FintypeCat.homMk fun z ↦ z.1 z.2

def curry {X A B : FintypeCat.{0}} (f : product X A ⟶ B) :
    X ⟶ exponential A B :=
  FintypeCat.homMk fun x a ↦ f (x, a)

def uncurry {X A B : FintypeCat.{0}} (g : X ⟶ exponential A B) :
    product X A ⟶ B :=
  FintypeCat.homMk fun xa ↦ g xa.1 xa.2

theorem terminal_unique {A : FintypeCat.{0}} (f : A ⟶ terminal) :
    f = terminate A := by
  apply FintypeCat.hom_ext
  intro a
  exact Subsingleton.elim _ _

@[simp] theorem fst_pair {X A B : FintypeCat.{0}} (f : X ⟶ A) (g : X ⟶ B) :
    pair f g ≫ fst A B = f := by
  apply FintypeCat.hom_ext
  intro x
  rfl

@[simp] theorem snd_pair {X A B : FintypeCat.{0}} (f : X ⟶ A) (g : X ⟶ B) :
    pair f g ≫ snd A B = g := by
  apply FintypeCat.hom_ext
  intro x
  rfl

@[simp] theorem pair_fst_snd {X A B : FintypeCat.{0}} (h : X ⟶ product A B) :
    pair (h ≫ fst A B) (h ≫ snd A B) = h := by
  apply FintypeCat.hom_ext
  intro x
  apply Prod.ext <;> rfl

@[simp] theorem uncurry_curry {X A B : FintypeCat.{0}} (f : product X A ⟶ B) :
    uncurry (curry f) = f := by
  apply FintypeCat.hom_ext
  intro xa
  rfl

@[simp] theorem curry_uncurry {X A B : FintypeCat.{0}} (g : X ⟶ exponential A B) :
    curry (uncurry g) = g := by
  apply FintypeCat.hom_ext
  intro x
  funext a
  rfl

/-- A compact, explicit witness that finite sets are cartesian closed. -/
structure Laws : Prop where
  terminality : ∀ {A : FintypeCat.{0}} (f : A ⟶ terminal), f = terminate A
  productBetaFst : ∀ {X A B : FintypeCat.{0}} (f : X ⟶ A) (g : X ⟶ B),
    pair f g ≫ fst A B = f
  productBetaSnd : ∀ {X A B : FintypeCat.{0}} (f : X ⟶ A) (g : X ⟶ B),
    pair f g ≫ snd A B = g
  productEta : ∀ {X A B : FintypeCat.{0}} (h : X ⟶ product A B),
    pair (h ≫ fst A B) (h ≫ snd A B) = h
  exponentialBeta : ∀ {X A B : FintypeCat.{0}} (f : product X A ⟶ B),
    uncurry (curry f) = f
  exponentialEta : ∀ {X A B : FintypeCat.{0}} (g : X ⟶ exponential A B),
    curry (uncurry g) = g

theorem laws : Laws where
  terminality := terminal_unique
  productBetaFst := fst_pair
  productBetaSnd := snd_pair
  productEta := pair_fst_snd
  exponentialBeta := uncurry_curry
  exponentialEta := curry_uncurry

end FiniteSetCCC

/-- Finite sets are locally finite. -/
instance fintypeCatLocallyFiniteHom : LocallyFiniteHom FintypeCat.{0} where
  homFinite A B := inferInstanceAs (Finite (A ⟶ B))

abbrev singletonObject : FintypeCat.{0} := FintypeCat.of PUnit

abbrev finObject (n : ℕ) : FintypeCat.{0} := FintypeCat.of (Fin n)

/-- The maps from a singleton to an `n`-element finite set form an `n`-element
hom-set. -/
theorem card_singleton_hom_fin (n : ℕ) :
    Nat.card (singletonObject ⟶ finObject n) = n := by
  let e : (singletonObject ⟶ finObject n) ≃ Fin n :=
    { toFun := fun f ↦ f PUnit.unit
      invFun := fun i ↦ FintypeCat.homMk (fun _ ↦ i)
      left_inv := by
        intro f
        apply FintypeCat.hom_ext
        intro x
        rw [show x = PUnit.unit from Subsingleton.elim _ _]
        rfl
      right_inv := by intro i; rfl }
  rw [Nat.card_congr e]
  simp

/-- **Uniform-budget no-go.**  For every fixed finite field and every fixed
coordinate budget, the cartesian closed category of finite sets has no
faithful family presentation obeying that budget.

This is strictly stronger than the local-finiteness obstruction: every
individual hom-set here is finite, and the unbounded family is the problem. -/
theorem no_uniform_presentation_of_finite_sets (budget : ℕ) :
    ¬ Nonempty (UniformIndexedHomPresentation FintypeCat.{0} F budget) := by
  rintro ⟨P⟩
  let n := Nat.card F ^ budget + 1
  have hbound := P.hom_card_le singletonObject (finObject n)
  rw [card_singleton_hom_fin] at hbound
  omega

/-- The sharp separation in one statement: finite sets do admit the exact
family-polynomial Yoneda presentation, but no member of that construction can
be replaced by a globally bounded coordinate family while retaining
faithfulness. -/
theorem finite_sets_family_yes_uniform_no (budget : ℕ) :
    Nonempty (FamilyPolynomialCategoryPresentation FintypeCat.{0} F) ∧
      ¬ Nonempty (UniformIndexedHomPresentation FintypeCat.{0} F budget) := by
  constructor
  · exact familyPolynomialPresentation_nonempty_iff_locallyFinite.mpr inferInstance
  · exact no_uniform_presentation_of_finite_sets (F := F) budget

/-! ## 7. Cryptographic binding is a separate assumption -/

/-- An abstract binding commitment.  Real proof systems normally replace the
information-theoretic injectivity field by a computational binding game; either
way, this layer is data not supplied by Yoneda or polynomial interpolation. -/
structure BindingCommitment (Message : Type*) where
  Commitment : Type*
  commit : Message → Commitment
  binding : Function.Injective commit

/-- Once a binding commitment is supplied, a commitment to the polynomial
identity-probe output reflects equality of source morphisms. -/
theorem committed_identityProbe_sound [LocallyFiniteHom C]
    {A B : C} (K : BindingCommitment ((A ⟶ B) → F)) (f g : A ⟶ B)
    (hcommit :
      K.commit (polynomialAction (F := F) f A (yonedaCode (F := F) (𝟙 A))) =
      K.commit (polynomialAction (F := F) g A (yonedaCode (F := F) (𝟙 A)))) :
    f = g := by
  apply (polynomial_identityProbe_iff (F := F) f g).mp
  exact K.binding hcommit

#assert_all_clean [yonedaAction_id, yonedaAction_comp,
  yonedaAction_atSource_injective, eq_iff_identityProbe,
  actionPolynomial_totalDegree_le_one, eval_actionPolynomial, polynomialAction_oneHot,
  FamilyPolynomialCategoryPresentation.locallyFinite,
  familyPolynomialPresentation_nonempty_iff_locallyFinite,
  polynomialAction_id_onCode, polynomialAction_comp_onCode,
  polynomial_identityProbe_iff, polynomialAction_is_yoneda,
  familyYonedaFullyFaithful, familyYonedaExponentialIso,
  EffectiveLocallyFiniteHom.locallyFinite,
  eval_effectiveActionPolynomial, UniformIndexedHomPresentation.hom_card_le,
  FiniteSetCCC.terminal_unique, FiniteSetCCC.fst_pair,
  FiniteSetCCC.snd_pair, FiniteSetCCC.pair_fst_snd,
  FiniteSetCCC.uncurry_curry, FiniteSetCCC.curry_uncurry,
  FiniteSetCCC.laws, card_singleton_hom_fin,
  no_uniform_presentation_of_finite_sets,
  finite_sets_family_yes_uniform_no, committed_identityProbe_sound]

end

end Dregg2.Metatheory.FamilyPolynomialYonedaFrontier
