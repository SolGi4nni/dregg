/-
# Dregg2.Realizability.IndexedPredicates — uniformly tracked indexed predicates.

For a relational PCA `P`, a predicate over an index type `I` is a family `I → Set P.Carrier`.
Entailment is *uniformly tracked*: one PCA element must transform every realizer at every index.
The derived identity and composition combinators prove the preorder laws.  Substitution is plain
precomposition and preserves tracked entailment, with identity/composition laws on the nose.

The fiberwise implication below is the standard realizability clause and the final theorem gives
an exact generic-predicate classifier at the indexed-family level.  These facts are deliberately
not advertised as a full tripos: no conjunction/disjunction, quantifier adjoints, or tripos-to-
topos construction is claimed in this first slice.
-/
import Dregg2.Realizability.PCA
import Mathlib.Data.Set.Basic

namespace Dregg2.Realizability

universe u v w z

/-- A realizability predicate indexed by `I`. -/
abbrev Pred (P : PCA.{u}) (I : Type v) := I → Set P.Carrier

/-- `e` uniformly tracks the implication `φ ⊢ ψ` at every index. -/
def Tracks (P : PCA.{u}) {I : Type v} (e : P.Carrier) (φ ψ : Pred P I) : Prop :=
  ∀ i a, a ∈ φ i → ∃ b, P.App e a b ∧ b ∈ ψ i

/-- Uniformly tracked entailment.  The existential tracker is outside the index quantifier. -/
def Entails (P : PCA.{u}) {I : Type v} (φ ψ : Pred P I) : Prop :=
  ∃ e, Tracks P e φ ψ

/-- Reindexing/substitution of a predicate family. -/
def reindex (P : PCA.{u}) {I : Type v} {J : Type w} (f : J → I) (φ : Pred P I) :
    Pred P J := fun j => φ (f j)

/-! ## Uniform tracking is a preorder -/

/-- The derived `I` combinator uniformly tracks reflexivity. -/
theorem tracks_ident (P : PCA.{u}) {I : Type v} (φ : Pred P I) :
    Tracks P P.ident φ φ := by
  intro i a ha
  exact ⟨a, P.app_ident a, ha⟩

theorem entails_refl (P : PCA.{u}) {I : Type v} (φ : Pred P I) :
    Entails P φ φ := ⟨P.ident, tracks_ident P φ⟩

/-- Composition of uniform trackers remains uniform. -/
theorem tracks_compose (P : PCA.{u}) {I : Type v} {d e : P.Carrier}
    {φ ψ χ : Pred P I} (he : Tracks P e φ ψ) (hd : Tracks P d ψ χ) :
    Tracks P (P.compose d e) φ χ := by
  intro i a ha
  rcases he i a ha with ⟨b, hab, hb⟩
  rcases hd i b hb with ⟨c, hbc, hc⟩
  exact ⟨c, P.app_compose hab hbc, hc⟩

theorem entails_trans (P : PCA.{u}) {I : Type v} {φ ψ χ : Pred P I}
    (hφψ : Entails P φ ψ) (hψχ : Entails P ψ χ) : Entails P φ χ := by
  rcases hφψ with ⟨e, he⟩
  rcases hψχ with ⟨d, hd⟩
  exact ⟨P.compose d e, tracks_compose P he hd⟩

/-! ## Reindexing is functorial and monotone -/

@[simp] theorem reindex_id (P : PCA.{u}) {I : Type v} (φ : Pred P I) :
    reindex P id φ = φ := rfl

@[simp] theorem reindex_comp (P : PCA.{u}) {I : Type v} {J : Type w} {K : Type z}
    (f : J → I) (g : K → J) (φ : Pred P I) :
    reindex P g (reindex P f φ) = reindex P (f ∘ g) φ := rfl

theorem tracks_reindex (P : PCA.{u}) {I : Type v} {J : Type w} (f : J → I)
    {e : P.Carrier} {φ ψ : Pred P I} (h : Tracks P e φ ψ) :
    Tracks P e (reindex P f φ) (reindex P f ψ) := by
  intro j a ha
  exact h (f j) a ha

theorem entails_reindex (P : PCA.{u}) {I : Type v} {J : Type w} (f : J → I)
    {φ ψ : Pred P I} (h : Entails P φ ψ) :
    Entails P (reindex P f φ) (reindex P f ψ) := by
  rcases h with ⟨e, he⟩
  exact ⟨e, tracks_reindex P f he⟩

/-! ## Mutual tracked entailment -/

/-- The equivalence relation induced by the tracked-entailment preorder. -/
def Equiprovable (P : PCA.{u}) {I : Type v} (φ ψ : Pred P I) : Prop :=
  Entails P φ ψ ∧ Entails P ψ φ

theorem equiprovable_refl (P : PCA.{u}) {I : Type v} (φ : Pred P I) :
    Equiprovable P φ φ := ⟨entails_refl P φ, entails_refl P φ⟩

theorem equiprovable_symm (P : PCA.{u}) {I : Type v} {φ ψ : Pred P I}
    (h : Equiprovable P φ ψ) : Equiprovable P ψ φ := ⟨h.2, h.1⟩

theorem equiprovable_trans (P : PCA.{u}) {I : Type v} {φ ψ χ : Pred P I}
    (hφψ : Equiprovable P φ ψ) (hψχ : Equiprovable P ψ χ) :
    Equiprovable P φ χ :=
  ⟨entails_trans P hφψ.1 hψχ.1, entails_trans P hψχ.2 hφψ.2⟩

theorem equiprovable_reindex (P : PCA.{u}) {I : Type v} {J : Type w} (f : J → I)
    {φ ψ : Pred P I} (h : Equiprovable P φ ψ) :
    Equiprovable P (reindex P f φ) (reindex P f ψ) :=
  ⟨entails_reindex P f h.1, entails_reindex P f h.2⟩

/-! ## Implication and the exact uniform-tracker reading -/

/-- Fiberwise realizability implication.  An element belongs when applying it to any realizer
of `φ i` produces a realizer of `ψ i`. -/
def imp (P : PCA.{u}) {I : Type v} (φ ψ : Pred P I) : Pred P I := fun i e =>
  ∀ a, a ∈ φ i → ∃ b, P.App e a b ∧ b ∈ ψ i

theorem tracks_iff_uniform_imp_realizer (P : PCA.{u}) {I : Type v}
    (e : P.Carrier) (φ ψ : Pred P I) :
    Tracks P e φ ψ ↔ ∀ i, e ∈ (imp P φ ψ) i := Iff.rfl

theorem entails_iff_uniform_imp_realizer (P : PCA.{u}) {I : Type v}
    (φ ψ : Pred P I) :
    Entails P φ ψ ↔ ∃ e, ∀ i, e ∈ (imp P φ ψ) i := Iff.rfl

@[simp] theorem reindex_imp (P : PCA.{u}) {I : Type v} {J : Type w} (f : J → I)
    (φ ψ : Pred P I) :
    reindex P f (imp P φ ψ) = imp P (reindex P f φ) (reindex P f ψ) := rfl

/-! ## The exact indexed generic predicate -/

/-- Membership as a predicate over the index object `Set P.Carrier`. -/
def generic (P : PCA.{u}) : Pred P (Set P.Carrier) := fun U => U

/-- The classifying map of an indexed predicate is the family itself, regarded as a map to the
power set of realizers. -/
def classify (P : PCA.{u}) {I : Type v} (φ : Pred P I) : I → Set P.Carrier := fun i => φ i

/-- **Generic-predicate theorem (at the indexed-family level).** Every indexed predicate is
exactly a reindexing of membership. -/
theorem reindex_generic (P : PCA.{u}) {I : Type v} (φ : Pred P I) :
    reindex P (classify P φ) (generic P) = φ := rfl

theorem generic_classifies_every_predicate (P : PCA.{u}) {I : Type v} (φ : Pred P I) :
    ∃ χ : I → Set P.Carrier, reindex P χ (generic P) = φ :=
  ⟨classify P φ, reindex_generic P φ⟩

#assert_all_clean [tracks_ident, entails_refl, tracks_compose, entails_trans,
  reindex_id, reindex_comp, tracks_reindex, entails_reindex,
  equiprovable_refl, equiprovable_symm, equiprovable_trans, equiprovable_reindex,
  tracks_iff_uniform_imp_realizer, entails_iff_uniform_imp_realizer, reindex_imp,
  reindex_generic, generic_classifies_every_predicate]

end Dregg2.Realizability
