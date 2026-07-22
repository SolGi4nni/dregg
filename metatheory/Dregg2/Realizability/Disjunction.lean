/-
# Dregg2.Realizability.Disjunction — chosen tags/case analysis and realizability join.

This module adds explicit computable left/right constructors and a curried case realizer to the
bare relational PCA.  The case laws are exact on tagged inputs.  From them, disjunction is proved
to satisfy the binary-join universal property for uniformly tracked entailment, and reindexing
preserves it definitionally.

The sum operations are model data, not global axioms.  A degenerate unit model witnesses
consistency; useful PCAs supply nondegenerate Church/number encodings.  We do not silently assume
tag injectivity or disjointness because neither is needed for the stated join theorems.
-/
import Dregg2.Realizability.IndexedPredicates

namespace Dregg2.Realizability

universe u v w

/-- Chosen computable sum constructors and exact case analysis over a PCA. -/
structure ChosenSums (P : PCA.{u}) where
  inl : P.Carrier
  inlVal : P.Carrier → P.Carrier
  app_inl : ∀ a, P.App inl a (inlVal a)

  inr : P.Carrier
  inrVal : P.Carrier → P.Carrier
  app_inr : ∀ b, P.App inr b (inrVal b)

  case : P.Carrier
  caseArg : P.Carrier → P.Carrier
  caseVal : P.Carrier → P.Carrier → P.Carrier
  app_case : ∀ e, P.App case e (caseArg e)
  app_caseArg : ∀ e d, P.App (caseArg e) d (caseVal e d)
  app_case_inl_iff : ∀ {e d a r},
    P.App (caseVal e d) (inlVal a) r ↔ P.App e a r
  app_case_inr_iff : ∀ {e d b r},
    P.App (caseVal e d) (inrVal b) r ↔ P.App d b r

namespace ChosenSums

/-- The one-element PCA carries a degenerate but lawful chosen sum interface. -/
def unitSums : ChosenSums PCA.unitPCA where
  inl := ()
  inlVal := fun _ => ()
  app_inl := by simp [PCA.unitPCA]
  inr := ()
  inrVal := fun _ => ()
  app_inr := by simp [PCA.unitPCA]
  case := ()
  caseArg := fun _ => ()
  caseVal := fun _ _ => ()
  app_case := by simp [PCA.unitPCA]
  app_caseArg := by simp [PCA.unitPCA]
  app_case_inl_iff := by simp [PCA.unitPCA]
  app_case_inr_iff := by simp [PCA.unitPCA]

end ChosenSums

/-- Concrete realizability disjunction: a tagged realizer of either branch. -/
def disj (P : PCA.{u}) (S : ChosenSums P) {I : Type v}
    (φ ψ : Pred P I) : Pred P I := fun i r =>
  (∃ a, a ∈ φ i ∧ r = S.inlVal a) ∨ (∃ b, b ∈ ψ i ∧ r = S.inrVal b)

/-- The left constructor uniformly realizes disjunction introduction. -/
theorem left_entails_disj (P : PCA.{u}) (S : ChosenSums P) {I : Type v}
    (φ ψ : Pred P I) : Entails P φ (disj P S φ ψ) := by
  refine ⟨S.inl, ?_⟩
  intro i a ha
  exact ⟨S.inlVal a, S.app_inl a, Or.inl ⟨a, ha, rfl⟩⟩

/-- The right constructor uniformly realizes disjunction introduction. -/
theorem right_entails_disj (P : PCA.{u}) (S : ChosenSums P) {I : Type v}
    (φ ψ : Pred P I) : Entails P ψ (disj P S φ ψ) := by
  refine ⟨S.inr, ?_⟩
  intro i b hb
  exact ⟨S.inrVal b, S.app_inr b, Or.inr ⟨b, hb, rfl⟩⟩

/-- Exact case analysis combines two uniform branch trackers into a disjunction eliminator. -/
theorem disj_entails (P : PCA.{u}) (S : ChosenSums P) {I : Type v}
    {φ ψ θ : Pred P I} (hφ : Entails P φ θ) (hψ : Entails P ψ θ) :
    Entails P (disj P S φ ψ) θ := by
  rcases hφ with ⟨e, he⟩
  rcases hψ with ⟨d, hd⟩
  refine ⟨S.caseVal e d, ?_⟩
  intro i r hr
  rcases hr with (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
  · rcases he i a ha with ⟨c, heac, hc⟩
    exact ⟨c, S.app_case_inl_iff.mpr heac, hc⟩
  · rcases hd i b hb with ⟨c, hdbc, hc⟩
    exact ⟨c, S.app_case_inr_iff.mpr hdbc, hc⟩

/-- The introduction/elimination laws are exactly the binary-join universal property. -/
theorem disj_entails_iff (P : PCA.{u}) (S : ChosenSums P) {I : Type v}
    {φ ψ θ : Pred P I} :
    Entails P (disj P S φ ψ) θ ↔ Entails P φ θ ∧ Entails P ψ θ := by
  constructor
  · intro h
    exact ⟨entails_trans P (left_entails_disj P S φ ψ) h,
      entails_trans P (right_entails_disj P S φ ψ) h⟩
  · rintro ⟨hφ, hψ⟩
    exact disj_entails P S hφ hψ

/-- Substitution preserves concrete disjunction on the nose. -/
@[simp] theorem reindex_disj (P : PCA.{u}) (S : ChosenSums P)
    {I : Type v} {J : Type w} (f : J → I) (φ ψ : Pred P I) :
    reindex P f (disj P S φ ψ) =
      disj P S (reindex P f φ) (reindex P f ψ) := rfl

/-- Disjunction commutes up to mutual uniformly tracked entailment. -/
theorem disj_comm (P : PCA.{u}) (S : ChosenSums P) {I : Type v}
    (φ ψ : Pred P I) : Equiprovable P (disj P S φ ψ) (disj P S ψ φ) := by
  constructor
  · exact disj_entails P S (right_entails_disj P S ψ φ) (left_entails_disj P S ψ φ)
  · exact disj_entails P S (right_entails_disj P S φ ψ) (left_entails_disj P S φ ψ)

#assert_all_clean [left_entails_disj, right_entails_disj, disj_entails,
  disj_entails_iff, reindex_disj, disj_comm]

end Dregg2.Realizability
