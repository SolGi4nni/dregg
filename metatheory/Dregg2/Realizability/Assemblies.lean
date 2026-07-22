/-
# Dregg2.Realizability.Assemblies — the assembly category above a relational PCA.

This file takes one honest step beyond the Set-indexed tripos-law package.  An assembly has an
underlying type and a nonempty family of PCA realizers for every element.  Its arrows are actual
functions carrying a *uniform* PCA tracking program.  Identity and composition are inherited from
the derived PCA combinators, and proof irrelevance makes arrows equal exactly when their underlying
functions are equal.  Thus the construction below is a genuine `CategoryTheory.Category`, not just
an analogy with one.

Chosen PCA pairing supplies explicit terminal and binary-product cones, with their universal maps
proved at the level of assembly arrows.  A reindexed assembly and its canonical display map make
the change-of-base operation explicit.  Modest assemblies induce partial equivalence relations on
realizers, and every tracked map respects those PERs.  Finally, partitioned assemblies state the
precise interface at which a polynomial evaluator (or any other compiled program) enters: a code
and an exact PCA application theorem produce an assembly morphism; no code is manufactured merely
from an extensional function.

This is not yet the tripos-to-topos theorem.  In particular, this file does not construct the exact
completion of assemblies/PERs, prove the elementary-topos axioms for that completion, or identify it
with the topos associated to `UFamTriposLaws`.
-/
import Dregg2.Realizability.UFamTripos
import Mathlib.CategoryTheory.Category.Basic

namespace Dregg2.Realizability

open CategoryTheory

universe u v w

/-! ## Assemblies and uniformly tracked maps -/

/-- An assembly over `P`: every semantic element has at least one concrete PCA realizer. -/
structure Assembly (P : PCA.{u}) where
  Carrier : Type v
  Realizes : P.Carrier → Carrier → Prop
  realized : ∀ x, ∃ r, Realizes r x

namespace Assembly

variable {P : PCA.{u}}

/-- A PCA element uniformly tracks a semantic function between two assemblies. -/
def Tracks (X Y : Assembly.{u, v} P) (e : P.Carrier)
    (f : X.Carrier → Y.Carrier) : Prop :=
  ∀ x r, X.Realizes r x → ∃ s, P.App e r s ∧ Y.Realizes s (f x)

/-- Morphisms remember the semantic function and the proposition that one uniform program tracks
it.  The particular program is evidence for existence, not part of arrow equality. -/
structure Hom (X Y : Assembly.{u, v} P) where
  toFun : X.Carrier → Y.Carrier
  tracked : ∃ e, Tracks X Y e toFun

instance (X Y : Assembly.{u, v} P) : CoeFun (Hom X Y) (fun _ => X.Carrier → Y.Carrier) :=
  ⟨Hom.toFun⟩

@[ext]
theorem Hom.ext {X Y : Assembly.{u, v} P} {f g : Hom X Y}
    (h : f.toFun = g.toFun) : f = g := by
  cases f with
  | mk ff hf =>
    cases g with
    | mk gg hg =>
      cases h
      rfl

theorem Hom.eq_iff {X Y : Assembly.{u, v} P} {f g : Hom X Y} :
    f = g ↔ f.toFun = g.toFun := by
  constructor
  · exact congrArg Hom.toFun
  · exact Hom.ext

/-- Identity is tracked by the derived `I` combinator. -/
def idHom (X : Assembly.{u, v} P) : Hom X X where
  toFun := id
  tracked := by
    refine ⟨P.ident, ?_⟩
    intro x r hr
    exact ⟨r, P.app_ident r, hr⟩

/-- Composition uses the exact derived PCA composition program. -/
def compHom {X Y Z : Assembly.{u, v} P} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  toFun := g.toFun ∘ f.toFun
  tracked := by
    rcases f.tracked with ⟨e, he⟩
    rcases g.tracked with ⟨d, hd⟩
    refine ⟨P.compose d e, ?_⟩
    intro x r hr
    rcases he x r hr with ⟨s, hers, hs⟩
    rcases hd (f x) s hs with ⟨t, hdst, ht⟩
    exact ⟨t, P.app_compose hers hdst, ht⟩

/-- Assemblies and uniformly tracked functions form a genuine category. -/
instance categoryAssembly : Category (Assembly.{u, v} P) where
  Hom := Hom
  id := idHom
  comp := compHom
  id_comp := by
    intro X Y f
    apply Hom.ext
    rfl
  comp_id := by
    intro X Y f
    apply Hom.ext
    rfl
  assoc := by
    intro W X Y Z f g h
    apply Hom.ext
    rfl

@[simp]
theorem idHom_apply (X : Assembly.{u, v} P) (x : X.Carrier) :
    (𝟙 X : X ⟶ X).toFun x = x := rfl

@[simp]
theorem compHom_apply {X Y Z : Assembly.{u, v} P} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X.Carrier) : (f ≫ g).toFun x = g.toFun (f.toFun x) := rfl

/-- Equality of assembly arrows is reflected by their semantic functions. -/
theorem hom_eq_of_pointwise {X Y : Assembly.{u, v} P} {f g : X ⟶ Y}
    (h : ∀ x, f.toFun x = g.toFun x) : f = g :=
  Hom.ext (funext h)

/-! ## Reindexing an assembly along a semantic map -/

/-- Pull the realizability family of `X` back along an arbitrary function. -/
def reindex (X : Assembly.{u, v} P) {A : Type w} (f : A → X.Carrier) :
    Assembly.{u, w} P where
  Carrier := A
  Realizes := fun r a => X.Realizes r (f a)
  realized := fun a => X.realized (f a)

/-- The display map from a reindexed assembly is tracked by identity. -/
def reindexMap (X : Assembly.{u, v} P) {A : Type v} (f : A → X.Carrier) :
    reindex X f ⟶ X where
  toFun := f
  tracked := by
    refine ⟨P.ident, ?_⟩
    intro a r hr
    exact ⟨r, P.app_ident r, hr⟩

@[simp]
theorem reindexMap_apply (X : Assembly.{u, v} P) {A : Type v}
    (f : A → X.Carrier) (a : A) : (reindexMap X f).toFun a = f a := rfl

/-- Iterated semantic reindexing has literally the expected realizability relation. -/
theorem reindex_comp_realizes (X : Assembly.{u, v} P) {A B : Type w}
    (f : A → X.Carrier) (g : B → A) (r : P.Carrier) (b : B) :
    (reindex (reindex X f) g).Realizes r b ↔ (reindex X (f ∘ g)).Realizes r b :=
  Iff.rfl

/-! ## Chosen finite-product structure -/

/-- The terminal assembly: its unique semantic point is realized by every PCA element. -/
def terminal (P : PCA.{u}) : Assembly.{u, v} P where
  Carrier := ULift.{v} Unit
  Realizes := fun _ _ => True
  realized := fun _ => ⟨P.k, trivial⟩

/-- Every assembly has the canonical arrow to the terminal assembly. -/
def toTerminal (X : Assembly.{u, v} P) : X ⟶ terminal P where
  toFun := fun _ => ULift.up ()
  tracked := by
    refine ⟨P.ident, ?_⟩
    intro x r hr
    exact ⟨r, P.app_ident r, trivial⟩

/-- The terminal arrow is unique as an assembly morphism. -/
theorem toTerminal_unique (X : Assembly.{u, v} P) (f : X ⟶ terminal P) :
    f = toTerminal X := by
  apply hom_eq_of_pointwise
  intro x
  change f.toFun x = ULift.up ()
  obtain ⟨u⟩ := f.toFun x
  obtain ⟨⟩ := u
  rfl

/-- Product assembly realized by the chosen concrete pairing operation. -/
def product (C : ChosenPairing P) (X Y : Assembly.{u, v} P) : Assembly.{u, v} P where
  Carrier := X.Carrier × Y.Carrier
  Realizes := fun r xy =>
    ∃ a, X.Realizes a xy.1 ∧ ∃ b, Y.Realizes b xy.2 ∧ r = C.pairVal a b
  realized := by
    intro xy
    rcases X.realized xy.1 with ⟨a, ha⟩
    rcases Y.realized xy.2 with ⟨b, hb⟩
    exact ⟨C.pairVal a b, a, ha, b, hb, rfl⟩

/-- First product projection, tracked by the chosen PCA projection. -/
def fst (C : ChosenPairing P) (X Y : Assembly.{u, v} P) : product C X Y ⟶ X where
  toFun := Prod.fst
  tracked := by
    refine ⟨C.fst, ?_⟩
    rintro ⟨x, y⟩ r ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, C.app_fst a b, ha⟩

/-- Second product projection, tracked by the chosen PCA projection. -/
def snd (C : ChosenPairing P) (X Y : Assembly.{u, v} P) : product C X Y ⟶ Y where
  toFun := Prod.snd
  tracked := by
    refine ⟨C.snd, ?_⟩
    rintro ⟨x, y⟩ r ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, C.app_snd a b, hb⟩

/-- Pairing of assembly arrows is tracked by the chosen PCA fork operation. -/
def pair (C : ChosenPairing P) {Z X Y : Assembly.{u, v} P}
    (f : Z ⟶ X) (g : Z ⟶ Y) : Z ⟶ product C X Y where
  toFun := fun z => (f.toFun z, g.toFun z)
  tracked := by
    rcases f.tracked with ⟨e, he⟩
    rcases g.tracked with ⟨d, hd⟩
    refine ⟨C.fork e d, ?_⟩
    intro z r hr
    rcases he z r hr with ⟨a, hea, ha⟩
    rcases hd z r hr with ⟨b, hdb, hb⟩
    exact ⟨C.pairVal a b, C.app_fork hea hdb, a, ha, b, hb, rfl⟩

@[simp]
theorem pair_fst (C : ChosenPairing P) {Z X Y : Assembly.{u, v} P}
    (f : Z ⟶ X) (g : Z ⟶ Y) : pair C f g ≫ fst C X Y = f := by
  apply hom_eq_of_pointwise
  intro z
  rfl

@[simp]
theorem pair_snd (C : ChosenPairing P) {Z X Y : Assembly.{u, v} P}
    (f : Z ⟶ X) (g : Z ⟶ Y) : pair C f g ≫ snd C X Y = g := by
  apply hom_eq_of_pointwise
  intro z
  rfl

/-- Exact binary-product universal property in the assembly category. -/
theorem pair_unique (C : ChosenPairing P) {Z X Y : Assembly.{u, v} P}
    (f : Z ⟶ X) (g : Z ⟶ Y) (h : Z ⟶ product C X Y)
    (hfst : h ≫ fst C X Y = f) (hsnd : h ≫ snd C X Y = g) :
    h = pair C f g := by
  apply hom_eq_of_pointwise
  intro z
  apply Prod.ext
  · exact congrArg (fun k : Z ⟶ X => k.toFun z) hfst
  · exact congrArg (fun k : Z ⟶ Y => k.toFun z) hsnd

/-! ## Equalizers -/

/-- The equalizer assembly inherits exactly the realizers of its underlying source element. -/
def equalizer {X Y : Assembly.{u, v} P} (f g : X ⟶ Y) : Assembly.{u, v} P where
  Carrier := {x : X.Carrier // f.toFun x = g.toFun x}
  Realizes := fun r x => X.Realizes r x.1
  realized := fun x => X.realized x.1

/-- Equalizer inclusion, tracked by identity. -/
def equalizerι {X Y : Assembly.{u, v} P} (f g : X ⟶ Y) : equalizer f g ⟶ X where
  toFun := Subtype.val
  tracked := by
    refine ⟨P.ident, ?_⟩
    intro x r hr
    exact ⟨r, P.app_ident r, hr⟩

@[simp]
theorem equalizer_condition {X Y : Assembly.{u, v} P} (f g : X ⟶ Y) :
    equalizerι f g ≫ f = equalizerι f g ≫ g := by
  apply hom_eq_of_pointwise
  intro x
  exact x.2

/-- Any tracked map satisfying the equalizer equation lifts without changing its tracker. -/
def equalizerLift {Z X Y : Assembly.{u, v} P} (f g : X ⟶ Y) (h : Z ⟶ X)
    (heq : h ≫ f = h ≫ g) : Z ⟶ equalizer f g where
  toFun := fun z => ⟨h.toFun z, congrArg (fun k : Z ⟶ Y => k.toFun z) heq⟩
  tracked := by
    rcases h.tracked with ⟨e, he⟩
    exact ⟨e, he⟩

@[simp]
theorem equalizerLift_ι {Z X Y : Assembly.{u, v} P} (f g : X ⟶ Y) (h : Z ⟶ X)
    (heq : h ≫ f = h ≫ g) : equalizerLift f g h heq ≫ equalizerι f g = h := by
  apply hom_eq_of_pointwise
  intro z
  rfl

/-- Exact equalizer universal property in the assembly category. -/
theorem equalizerLift_unique {Z X Y : Assembly.{u, v} P} (f g : X ⟶ Y)
    (h : Z ⟶ X) (heq : h ≫ f = h ≫ g) (k : Z ⟶ equalizer f g)
    (hk : k ≫ equalizerι f g = h) : k = equalizerLift f g h heq := by
  apply hom_eq_of_pointwise
  intro z
  apply Subtype.ext
  exact congrArg (fun q : Z ⟶ X => q.toFun z) hk

/-! ## Modest assemblies and their realizer PERs -/

/-- A partial equivalence relation, presented by symmetry and transitivity. -/
structure PER (α : Type u) where
  Rel : α → α → Prop
  symmetric : ∀ {a b}, Rel a b → Rel b a
  transitive : ∀ {a b c}, Rel a b → Rel b c → Rel a c

namespace PER

/-- The support of a PER consists of elements related to themselves. -/
def Support (R : PER α) (a : α) : Prop := R.Rel a a

theorem support_of_rel (R : PER α) {a b : α} (h : R.Rel a b) :
    R.Support a ∧ R.Support b := by
  exact ⟨R.transitive h (R.symmetric h), R.transitive (R.symmetric h) h⟩

theorem rel_refl_on_support (R : PER α) {a : α} (h : R.Support a) : R.Rel a a := h

end PER

/-- An assembly is modest when one realizer cannot realize two distinct semantic elements. -/
def Modest (X : Assembly.{u, v} P) : Prop :=
  ∀ r x y, X.Realizes r x → X.Realizes r y → x = y

/-- A modest assembly induces a PER on PCA realizers: two codes are related when they realize the
same semantic element. -/
def realizerPER (X : Assembly.{u, v} P) (hX : Modest X) : PER P.Carrier where
  Rel := fun a b => ∃ x, X.Realizes a x ∧ X.Realizes b x
  symmetric := by
    rintro a b ⟨x, ha, hb⟩
    exact ⟨x, hb, ha⟩
  transitive := by
    rintro a b c ⟨x, ha, hb⟩ ⟨y, hb', hc⟩
    have hxy : x = y := hX b x y hb hb'
    subst y
    exact ⟨x, ha, hc⟩

theorem realizerPER_support_iff (X : Assembly.{u, v} P) (hX : Modest X)
    (r : P.Carrier) :
    (realizerPER X hX).Support r ↔ ∃ x, X.Realizes r x := by
  constructor
  · rintro ⟨x, hr, hr'⟩
    exact ⟨x, hr⟩
  · rintro ⟨x, hr⟩
    exact ⟨x, hr, hr⟩

/-- A tracker for a map between modest assemblies respects the induced PERs.  This theorem is
evidence-relevant: it returns the output realizers and the exact PCA applications. -/
theorem tracker_respects_realizerPER {X Y : Assembly.{u, v} P}
    (hX : Modest X) (hY : Modest Y) {e : P.Carrier}
    {f : X.Carrier → Y.Carrier} (he : Tracks X Y e f)
    {a b : P.Carrier} (hab : (realizerPER X hX).Rel a b) :
    ∃ s t, P.App e a s ∧ P.App e b t ∧ (realizerPER Y hY).Rel s t := by
  rcases hab with ⟨x, ha, hb⟩
  rcases he x a ha with ⟨s, has, hs⟩
  rcases he x b hb with ⟨t, hbt, ht⟩
  exact ⟨s, t, has, hbt, f x, hs, ht⟩

/-- Every assembly morphism between modest assemblies has a PER-respecting tracker. -/
theorem Hom.exists_PER_tracker {X Y : Assembly.{u, v} P}
    (hX : Modest X) (hY : Modest Y) (f : X ⟶ Y) :
    ∃ e, ∀ {a b}, (realizerPER X hX).Rel a b →
      ∃ s t, P.App e a s ∧ P.App e b t ∧ (realizerPER Y hY).Rel s t := by
  rcases f.tracked with ⟨e, he⟩
  exact ⟨e, fun hab => tracker_respects_realizerPER hX hY he hab⟩

/-! ## Partitioned assemblies: the exact compiled-program boundary -/

/-- An explicit representation of semantic values by PCA codes. -/
structure Representation (P : PCA.{u}) (A : Type v) where
  encode : A → P.Carrier

/-- A representation is faithful when distinct semantic values receive distinct codes. -/
def Representation.Faithful (A : Representation P α) : Prop :=
  Function.Injective A.encode

/-- The partitioned assembly generated by an explicit representation. -/
def Representation.assembly (A : Representation P α) : Assembly P where
  Carrier := α
  Realizes := fun r x => r = A.encode x
  realized := fun x => ⟨A.encode x, rfl⟩

theorem Representation.assembly_modest (A : Representation P α) (hA : A.Faithful) :
    Modest A.assembly := by
  intro r x y hx hy
  exact hA (hx.symm.trans hy)

/-- A compiled program certificate is exactly an application theorem on encoded inputs. -/
structure ProgramCertificate (A : Representation P α) (B : Representation P β)
    (f : α → β) where
  code : P.Carrier
  runs : ∀ x, P.App code (A.encode x) (B.encode (f x))

/-- A certified program induces a tracked morphism between its partitioned assemblies. -/
def ProgramCertificate.hom {A : Representation P α} {B : Representation P β}
    {f : α → β} (C : ProgramCertificate A B f) : A.assembly ⟶ B.assembly where
  toFun := f
  tracked := by
    refine ⟨C.code, ?_⟩
    intro x r hr
    subst r
    exact ⟨B.encode (f x), C.runs x, rfl⟩

@[simp]
theorem ProgramCertificate.hom_apply {A : Representation P α}
    {B : Representation P β} {f : α → β} (C : ProgramCertificate A B f) (x : α) :
    C.hom.toFun x = f x := rfl

/-- Certified programs compose using the exact PCA composition program. -/
def ProgramCertificate.comp {A : Representation P α} {B : Representation P β}
    {C : Representation P γ} {f : α → β} {g : β → γ}
    (F : ProgramCertificate A B f) (G : ProgramCertificate B C g) :
    ProgramCertificate A C (g ∘ f) where
  code := P.compose G.code F.code
  runs := fun x => P.app_compose (F.runs x) (G.runs (f x))

@[simp]
theorem ProgramCertificate.comp_hom {A : Representation P α}
    {B : Representation P β} {C : Representation P γ}
    {f : α → β} {g : β → γ}
    (F : ProgramCertificate A B f) (G : ProgramCertificate B C g) :
    (F.comp G).hom = F.hom ≫ G.hom := by
  apply hom_eq_of_pointwise
  intro x
  rfl

#assert_all_clean [Hom.ext, Hom.eq_iff, idHom_apply, compHom_apply,
  hom_eq_of_pointwise, reindexMap_apply, reindex_comp_realizes,
  toTerminal_unique, pair_fst, pair_snd, pair_unique,
  equalizer_condition, equalizerLift_ι, equalizerLift_unique,
  PER.support_of_rel, PER.rel_refl_on_support, realizerPER_support_iff,
  tracker_respects_realizerPER, Hom.exists_PER_tracker,
  Representation.assembly_modest, ProgramCertificate.hom_apply,
  ProgramCertificate.comp_hom]

end Assembly

end Dregg2.Realizability
