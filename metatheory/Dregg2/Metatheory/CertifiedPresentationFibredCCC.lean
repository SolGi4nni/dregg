/-
# The categorical boundary of certified presentations

The category in `CertifiedPresentationChange` is intentionally broad: an
object carries its own source predicate, and an arrow requires those predicates
to be equivalent.  That category is not cartesian closed.  In fact it has no
weak terminal object, because true and false source predicates cannot both map
to one presentation.

This file proves the obstruction and then constructs the correct positive
replacement.  Over one *fixed* source meaning, zero-resource evidence families
form a genuine cartesian closed category, pointwise in the statement:

* terminal evidence is `Unit`;
* product evidence is a pair;
* exponential evidence is an evidence transformer; and
* beta/eta and product universal laws hold as arrow equalities.

These products combine representations of the same predicate.  They are not
logical conjunction of unrelated predicates.  A separate theorem shows why
the obvious conjunction presentation generally cannot have categorical
projections: either projection would force a logical implication between the
two meanings.

Finally, the function-space discussion is tied to the existing intensional
CCC construction: a family of represented shared-net arrows carries an actual
closed-net representative for every element.  We do not replace those
intensional programs with finite function tables.

Standalone construction: no integration root is modified.  Pure; no axioms.
-/

import Dregg2.Calculus.IntensionalCCCTrace
import Dregg2.Metatheory.CertifiedPresentationChange

namespace Dregg2.Metatheory.CertifiedPresentationFibredCCC

open CategoryTheory
open Dregg2.Metatheory.ArithmetizationCost
open Dregg2.Metatheory.CertifiedPresentationChange

set_option autoImplicit false

/-! ## 1. The global presentation category has no terminal object -/

def truthPresentation : Presentation Unit where
  meaning := fun _ => True
  Evidence := fun _ => Unit
  accepts := fun _ _ => True
  resources := fun _ _ => BackendCost.zero

def falsityPresentation : Presentation Unit where
  meaning := fun _ => False
  Evidence := fun _ => Unit
  accepts := fun _ _ => False
  resources := fun _ _ => BackendCost.zero

/-- The existence part of terminality; uniqueness is not needed for the
obstruction. -/
def WeakTerminal (terminal : Presentation Unit) : Prop :=
  ∀ source : Presentation Unit, Nonempty (Change source terminal)

theorem no_weakTerminal : ¬ ∃ terminal : Presentation Unit, WeakTerminal terminal := by
  rintro ⟨terminal, hterminal⟩
  rcases hterminal truthPresentation with ⟨fromTrue⟩
  rcases hterminal falsityPresentation with ⟨fromFalse⟩
  have htrue : terminal.meaning () :=
    (fromTrue.meaning_iff ()).mpr trivial
  have hfalse : False :=
    (fromFalse.meaning_iff ()).mp htrue
  exact hfalse.elim

/-- Consequently the global category cannot be cartesian closed. -/
theorem no_global_cartesian_structure :
    ¬ ∃ terminal : Presentation Unit,
      ∀ source : Presentation Unit, Nonempty (source ⟶ terminal) :=
  no_weakTerminal

/-! ## 2. Logical conjunction is not the categorical product -/

variable {Statement : Type}

/-- The semantically natural conjunction of two proof presentations. -/
def logicalConjunction (P Q : Presentation Statement) : Presentation Statement where
  meaning := fun statement => P.meaning statement ∧ Q.meaning statement
  Evidence := fun statement => P.Evidence statement × Q.Evidence statement
  accepts := fun statement evidence =>
    P.accepts statement evidence.1 ∧ Q.accepts statement evidence.2
  resources := fun statement evidence =>
    BackendCost.combine (P.resources statement evidence.1)
      (Q.resources statement evidence.2)

/-- A would-be first projection can exist only if the left meaning implies the
right meaning.  This is much stronger than the product law wanted for logical
conjunction. -/
theorem firstProjection_forces_right {P Q : Presentation Statement}
    (projection : Change (logicalConjunction P Q) P)
    (statement : Statement) (hleft : P.meaning statement) :
    Q.meaning statement :=
  (projection.meaning_iff statement).mp hleft |>.2

/-- Symmetrically, a second projection forces right-to-left implication. -/
theorem secondProjection_forces_left {P Q : Presentation Statement}
    (projection : Change (logicalConjunction P Q) Q)
    (statement : Statement) (hright : Q.meaning statement) :
    P.meaning statement :=
  (projection.meaning_iff statement).mp hright |>.1

theorem truth_and_falsity_has_no_firstProjection :
    ¬ Nonempty (Change (logicalConjunction truthPresentation falsityPresentation)
      truthPresentation) := by
  rintro ⟨projection⟩
  exact firstProjection_forces_right projection () trivial

/-! ## 3. The fixed-meaning zero-resource fibre -/

/-- An evidence family over a fixed statement language.  Source meaning is an
ambient fibre parameter below, not object-varying data. -/
structure EvidenceFamily (Statement : Type) where
  Evidence : Statement → Type

namespace EvidenceFamily

variable {X Y Z W : EvidenceFamily Statement}

/-- Fibre arrows are pointwise evidence transformers. -/
structure Hom (X Y : EvidenceFamily Statement) where
  toFun : ∀ statement, X.Evidence statement → Y.Evidence statement

instance (X Y : EvidenceFamily Statement) : CoeFun (Hom X Y)
    (fun _ => ∀ statement, X.Evidence statement → Y.Evidence statement) :=
  ⟨Hom.toFun⟩

@[ext]
theorem Hom.ext {f g : Hom X Y} (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  cases h
  rfl

def idHom (X : EvidenceFamily Statement) : Hom X X where
  toFun := fun _ evidence => evidence

def compHom (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  toFun := fun statement evidence =>
    g.toFun statement (f.toFun statement evidence)

instance categoryEvidenceFamily : Category (EvidenceFamily Statement) where
  Hom := Hom
  id := idHom
  comp := compHom
  id_comp := by intros; apply Hom.ext; rfl
  comp_id := by intros; apply Hom.ext; rfl
  assoc := by intros; apply Hom.ext; rfl

@[simp]
theorem id_apply (X : EvidenceFamily Statement) (statement : Statement)
    (evidence : X.Evidence statement) :
    (𝟙 X : X ⟶ X).toFun statement evidence = evidence := rfl

@[simp]
theorem comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (statement : Statement)
    (evidence : X.Evidence statement) :
    (f ≫ g).toFun statement evidence =
      g.toFun statement (f.toFun statement evidence) := rfl

/-- Embed a family into the global presentation category over one fixed
meaning.  Acceptance is exactly that meaning, and the bookkeeping cost is
zero. -/
def asPresentation (Meaning : Statement → Prop) (X : EvidenceFamily Statement) :
    Presentation Statement where
  meaning := Meaning
  Evidence := X.Evidence
  accepts := fun statement _ => Meaning statement
  resources := fun _ _ => BackendCost.zero

/-- Every fibre arrow gives an exact global presentation change. -/
def Hom.toChange (Meaning : Statement → Prop) (f : Hom X Y) :
    Change (asPresentation Meaning X) (asPresentation Meaning Y) where
  mapEvidence := f.toFun
  meaning_iff := fun _ => Iff.rfl
  acceptance_iff := fun _ _ => Iff.rfl
  resourceBound := ⟨fun _ => BackendCost.zero, fun _ _ =>
    CostLE.combine_zero BackendCost.zero⟩

theorem Hom.toChange_injective (Meaning : Statement → Prop) :
    Function.Injective (Hom.toChange (X := X) (Y := Y) Meaning) := by
  intro f g h
  apply Hom.ext
  exact congrArg Change.mapEvidence h

/-! ### Chosen terminal object and products -/

def terminal : EvidenceFamily Statement :=
  ⟨fun _ => Unit⟩

def product (X Y : EvidenceFamily Statement) : EvidenceFamily Statement :=
  ⟨fun statement => X.Evidence statement × Y.Evidence statement⟩

def toTerminal (X : EvidenceFamily Statement) : X ⟶ terminal where
  toFun := fun _ _ => ()

def fst (X Y : EvidenceFamily Statement) : product X Y ⟶ X where
  toFun := fun _ evidence => evidence.1

def snd (X Y : EvidenceFamily Statement) : product X Y ⟶ Y where
  toFun := fun _ evidence => evidence.2

def pair (f : Z ⟶ X) (g : Z ⟶ Y) : Z ⟶ product X Y where
  toFun := fun statement evidence =>
    (f.toFun statement evidence, g.toFun statement evidence)

theorem toTerminal_unique (f : X ⟶ terminal) : f = toTerminal X := by
  apply Hom.ext
  funext statement evidence
  exact Unit.ext _ _

@[simp]
theorem fst_pair (f : Z ⟶ X) (g : Z ⟶ Y) :
    pair f g ≫ fst X Y = f := by
  apply Hom.ext
  funext statement evidence
  rfl

@[simp]
theorem snd_pair (f : Z ⟶ X) (g : Z ⟶ Y) :
    pair f g ≫ snd X Y = g := by
  apply Hom.ext
  funext statement evidence
  rfl

@[simp]
theorem pair_fst_snd (h : Z ⟶ product X Y) :
    pair (h ≫ fst X Y) (h ≫ snd X Y) = h := by
  apply Hom.ext
  funext statement evidence
  rfl

theorem pair_unique (h : Z ⟶ product X Y) (f : Z ⟶ X) (g : Z ⟶ Y)
    (hfst : h ≫ fst X Y = f) (hsnd : h ≫ snd X Y = g) :
    h = pair f g := by
  rw [← hfst, ← hsnd, pair_fst_snd]

/-! ### Pointwise function-space evidence -/

def exponential (X Y : EvidenceFamily Statement) : EvidenceFamily Statement :=
  ⟨fun statement => X.Evidence statement → Y.Evidence statement⟩

def evaluation (X Y : EvidenceFamily Statement) :
    product (exponential X Y) X ⟶ Y where
  toFun := fun _ evidence => evidence.1 evidence.2

def curry (f : product Z X ⟶ Y) : Z ⟶ exponential X Y where
  toFun := fun statement z x => f.toFun statement (z, x)

def uncurry (g : Z ⟶ exponential X Y) : product Z X ⟶ Y where
  toFun := fun statement evidence =>
    g.toFun statement evidence.1 evidence.2

@[simp]
theorem uncurry_curry (f : product Z X ⟶ Y) : uncurry (curry f) = f := by
  apply Hom.ext
  funext statement evidence
  rfl

@[simp]
theorem curry_uncurry (g : Z ⟶ exponential X Y) : curry (uncurry g) = g := by
  apply Hom.ext
  funext statement evidence input
  rfl

theorem uncurry_eq_evaluation (g : Z ⟶ exponential X Y) :
    uncurry g = pair (fst Z X ≫ g) (snd Z X) ≫ evaluation X Y := by
  apply Hom.ext
  funext statement evidence
  rfl

theorem evaluation_beta (f : product Z X ⟶ Y) :
    pair (fst Z X ≫ curry f) (snd Z X) ≫ evaluation X Y = f := by
  rw [← uncurry_eq_evaluation, uncurry_curry]

theorem curry_unique (f : product Z X ⟶ Y) (g : Z ⟶ exponential X Y)
    (heval : pair (fst Z X ≫ g) (snd Z X) ≫ evaluation X Y = f) :
    g = curry f := by
  rw [← uncurry_eq_evaluation] at heval
  rw [← heval, curry_uncurry]

/-- Complete chosen CCC law bundle for the fixed-meaning evidence fibre. -/
structure Laws (Statement : Type) : Prop where
  terminality : ∀ {X : EvidenceFamily Statement} (f : X ⟶ terminal),
    f = toTerminal X
  productBetaFst : ∀ {Z X Y : EvidenceFamily Statement}
    (f : Z ⟶ X) (g : Z ⟶ Y),
    pair f g ≫ fst X Y = f
  productBetaSnd : ∀ {Z X Y : EvidenceFamily Statement}
    (f : Z ⟶ X) (g : Z ⟶ Y),
    pair f g ≫ snd X Y = g
  productEta : ∀ {Z X Y : EvidenceFamily Statement}
    (h : Z ⟶ product X Y),
    pair (h ≫ fst X Y) (h ≫ snd X Y) = h
  exponentialBeta : ∀ {Z X Y : EvidenceFamily Statement}
    (f : product Z X ⟶ Y),
    uncurry (curry f) = f
  exponentialEta : ∀ {Z X Y : EvidenceFamily Statement}
    (g : Z ⟶ exponential X Y),
    curry (uncurry g) = g

theorem laws : Laws Statement where
  terminality := toTerminal_unique
  productBetaFst := fst_pair
  productBetaSnd := snd_pair
  productEta := pair_fst_snd
  exponentialBeta := uncurry_curry
  exponentialEta := curry_uncurry

/-! ## 4. Intensional, represented function evidence -/

namespace Intensional

open Dregg2.Calculus.IntensionalCCCTrace

/-- A constant family of shared-net-represented functions.  This is the
intensional alternative to an extensional function table. -/
def representedArrow (domain codomain : Ty) : EvidenceFamily Statement :=
  ⟨fun _ => Net [] (.arr domain codomain)⟩

/-- Every element is definitionally a concrete closed shared net, not a dense
function table. -/
theorem is_closedNet (domain codomain : Ty) (statement : Statement)
    (evidence : (representedArrow (Statement := Statement) domain codomain).Evidence statement) :
    ∃ net : Net [] (.arr domain codomain), net = evidence :=
  ⟨evidence, rfl⟩

/-- The existing local-interaction theorem supplies exact denotational
equality between alternative intensional presentations. -/
theorem localStep_same_denotation {domain codomain : Ty}
    {before after : Net [] (.arr domain codomain)}
    (step : LocalStep before after) :
    after.denote PUnit.unit = before.denote PUnit.unit :=
  localStep_denote step PUnit.unit

end Intensional

#assert_all_clean [
  Hom.ext,
  Hom.toChange_injective,
  toTerminal_unique,
  fst_pair,
  snd_pair,
  pair_fst_snd,
  pair_unique,
  uncurry_curry,
  curry_uncurry,
  uncurry_eq_evaluation,
  evaluation_beta,
  curry_unique,
  laws,
  Intensional.is_closedNet,
  Intensional.localStep_same_denotation]

end EvidenceFamily

#assert_all_clean [
  no_weakTerminal,
  no_global_cartesian_structure,
  firstProjection_forces_right,
  secondProjection_forces_left,
  truth_and_falsity_has_no_firstProjection]

end Dregg2.Metatheory.CertifiedPresentationFibredCCC
