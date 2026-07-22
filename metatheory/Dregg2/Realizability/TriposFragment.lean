/-
# Dregg2.Realizability.TriposFragment — a packaged, kernel-clean realizability doctrine.

This file packages exactly the laws proved by the preceding modules:

* uniformly tracked entailment is an indexed preorder;
* truth/falsity, binary conjunction/disjunction, and implication have their expected universal
  properties;
* reindexing preserves those operations;
* the ordinary existential and thunked universal are adjoint to reindexing along every set map;
* both adjoints satisfy Beck--Chevalley for weak pullback squares; and
* membership is an exact generic predicate.

The witness is deliberately called `TriposFragmentLaws`, not `Tripos`.  It records the standard
logical and quantifier spine but does not define the tripos-to-topos construction, quotient the
preorders, or claim categorical comprehension.  The last section makes the generic-predicate /
comprehension boundary precise: the evident sigma of pointwise realizers has pointwise witnesses,
but turning those into one uniformly tracked truth entailment is additional data.
-/
import Dregg2.Realizability.EncodedQuantifiers

namespace Dregg2.Realizability

universe u v

/-- The law bundle established for a PCA with chosen pairing, sums, and currying code.

All base objects in the order/quantifier fields live in one arbitrary universe `v`; the generic
predicate may live in the PCA carrier universe and still classifies every such family. -/
structure TriposFragmentLaws (P : PCA.{u}) (C : ChosenPairing P)
    (S : ChosenSums P) (Q : ChosenCurrying P C) : Prop where
  entails_refl_law : ∀ {I : Type v} (φ : Pred P I), Entails P φ φ
  entails_trans_law : ∀ {I : Type v} {φ ψ χ : Pred P I},
    Entails P φ ψ → Entails P ψ χ → Entails P φ χ
  reindex_entails_law : ∀ {I J : Type v} (f : J → I) {φ ψ : Pred P I},
    Entails P φ ψ → Entails P (reindex P f φ) (reindex P f ψ)

  truth_law : ∀ {I : Type v} (φ : Pred P I), Entails P φ (truth P)
  falsity_law : ∀ {I : Type v} (φ : Pred P I), Entails P (falsity P) φ
  conjunction_law : ∀ {I : Type v} {θ φ ψ : Pred P I},
    Entails P θ (conj P C φ ψ) ↔ Entails P θ φ ∧ Entails P θ ψ
  disjunction_law : ∀ {I : Type v} {φ ψ θ : Pred P I},
    Entails P (disj P S φ ψ) θ ↔ Entails P φ θ ∧ Entails P ψ θ
  implication_law : ∀ {I : Type v} {θ φ ψ : Pred P I},
    Entails P (conj P C θ φ) ψ ↔ Entails P θ (imp P φ ψ)

  reindex_truth_law : ∀ {I J : Type v} (f : J → I),
    reindex P f (truth P) = truth P
  reindex_falsity_law : ∀ {I J : Type v} (f : J → I),
    reindex P f (falsity P) = falsity P
  reindex_conjunction_law : ∀ {I J : Type v} (f : J → I) (φ ψ : Pred P I),
    reindex P f (conj P C φ ψ) =
      conj P C (reindex P f φ) (reindex P f ψ)
  reindex_disjunction_law : ∀ {I J : Type v} (f : J → I) (φ ψ : Pred P I),
    reindex P f (disj P S φ ψ) =
      disj P S (reindex P f φ) (reindex P f ψ)
  reindex_implication_law : ∀ {I J : Type v} (f : J → I) (φ ψ : Pred P I),
    reindex P f (imp P φ ψ) =
      imp P (reindex P f φ) (reindex P f ψ)

  existential_adjunction_law : ∀ {J I : Type v} (f : J → I)
      (φ : Pred P J) (ψ : Pred P I),
    Entails P (existsReal P f φ) ψ ↔ Entails P φ (reindex P f ψ)
  universal_adjunction_law : ∀ {J I : Type v} (f : J → I)
      (φ : Pred P J) (ψ : Pred P I),
    Entails P (reindex P f ψ) φ ↔ Entails P ψ (forallReal P C f φ)

  existential_beckChevalley_law : ∀ {K J L I : Type v}
      {g : K → J} {q : K → L} {f : J → I} {h : L → I},
    WeakPullbackSquare g q f h → ∀ φ : Pred P J,
      reindex P h (existsReal P f φ) = existsReal P q (reindex P g φ)
  universal_beckChevalley_law : ∀ {K J L I : Type v}
      {g : K → J} {q : K → L} {f : J → I} {h : L → I},
    WeakPullbackSquare g q f h → ∀ φ : Pred P J,
      reindex P h (forallReal P C f φ) = forallReal P C q (reindex P g φ)

  generic_predicate_law : ∀ {I : Type v} (φ : Pred P I),
    reindex P (classify P φ) (generic P) = φ

/-- The realizability construction supplies the entire advertised law bundle. -/
def realizabilityTriposFragmentLaws (P : PCA.{u}) (C : ChosenPairing P)
    (S : ChosenSums P) (Q : ChosenCurrying P C) :
    TriposFragmentLaws.{u, v} P C S Q where
  entails_refl_law := entails_refl P
  entails_trans_law := fun hφψ hψχ => entails_trans P hφψ hψχ
  reindex_entails_law := fun {_ _} f {_ _} h => entails_reindex P f h
  truth_law := entails_truth P
  falsity_law := falsity_entails P
  conjunction_law := entails_conj_iff P C
  disjunction_law := disj_entails_iff P S
  implication_law := entails_imp_iff P C Q
  reindex_truth_law := reindex_truth P
  reindex_falsity_law := reindex_falsity P
  reindex_conjunction_law := reindex_conj P C
  reindex_disjunction_law := reindex_disj P S
  reindex_implication_law := reindex_imp P
  existential_adjunction_law := existsReal_adjunction P
  universal_adjunction_law := forallReal_adjunction P C
  existential_beckChevalley_law := fun W φ => existsReal_beckChevalley P W φ
  universal_beckChevalley_law := fun W φ => forallReal_beckChevalley P C W φ
  generic_predicate_law := reindex_generic P

/-! ## Generic predicate versus comprehension -/

/-- The set-level object of an index together with one realizer of its predicate fiber.  This is
the evident candidate underlying a comprehension construction. -/
def RealizerComprehension (P : PCA.{u}) {I : Type v} (φ : Pred P I) :=
  { p : I × P.Carrier // p.2 ∈ φ p.1 }

namespace RealizerComprehension

def base {P : PCA.{u}} {I : Type v} {φ : Pred P I}
    (c : RealizerComprehension P φ) : I := c.1.1

def witness {P : PCA.{u}} {I : Type v} {φ : Pred P I}
    (c : RealizerComprehension P φ) : P.Carrier := c.1.2

/-- Every point of the sigma candidate carries a pointwise realizer of the pulled-back predicate. -/
theorem witness_mem {P : PCA.{u}} {I : Type v} {φ : Pred P I}
    (c : RealizerComprehension P φ) :
    witness c ∈ (reindex P (base (P := P) (φ := φ)) φ) c :=
  c.2

end RealizerComprehension

/-- The additional statement needed to promote the sigma candidate to a tracked comprehension:
one tracker must transform every truth realizer at every sigma point. -/
def HasTrackedComprehension (P : PCA.{u}) {I : Type v} (φ : Pred P I) : Prop :=
  Entails P (truth P)
    (reindex P (RealizerComprehension.base (P := P) (φ := φ)) φ)

/-- A globally uniform truth realizer is sufficient for tracked comprehension. -/
theorem hasTrackedComprehension_of_truth_entails (P : PCA.{u})
    {I : Type v} {φ : Pred P I} (h : Entails P (truth P) φ) :
    HasTrackedComprehension P φ :=
  entails_reindex P (RealizerComprehension.base (P := P) (φ := φ)) h

/-- If every fiber is inhabited, tracked comprehension of the sigma candidate is equivalent to
the stronger uniform statement `truth ⊢ φ`.  Pointwise witnesses alone therefore do not erase the
uniform-tracker obligation. -/
theorem hasTrackedComprehension_iff_of_pointwise_inhabited (P : PCA.{u})
    {I : Type v} {φ : Pred P I} (hφ : ∀ i, ∃ r, r ∈ φ i) :
    HasTrackedComprehension P φ ↔ Entails P (truth P) φ := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    intro i a ha
    rcases hφ i with ⟨r, hr⟩
    let c : RealizerComprehension P φ := ⟨(i, r), hr⟩
    exact he c a trivial
  · exact hasTrackedComprehension_of_truth_entails P

#assert_all_clean [realizabilityTriposFragmentLaws,
  RealizerComprehension.witness_mem, hasTrackedComprehension_of_truth_entails,
  hasTrackedComprehension_iff_of_pointwise_inhabited]

end Dregg2.Realizability
