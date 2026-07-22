/-
# Dregg2.Realizability.LogicalStructure — bounded Heyting operations with explicit coding.

Truth and falsity need no extra computational assumptions.  Conjunction uses the chosen pairing
from `Conjunction`, and disjunction uses the chosen tags and exact case operation from
`Disjunction`.

The missing computational ingredient for the implication adjunction is stated explicitly as
`ChosenCurrying`: it turns a tracker on pairs into a tracker-valued function, with an exact
application law.  This is ordinary model data, not a Lean axiom, and the one-element PCA supplies
a concrete witness.  With that data, conjunction and the fiberwise implication from
`IndexedPredicates` satisfy the Heyting adjunction.
-/
import Dregg2.Realizability.Conjunction
import Dregg2.Realizability.Disjunction

namespace Dregg2.Realizability

universe u v w

/-! ## Truth and falsity -/

/-- The greatest realizability predicate. -/
def truth (P : PCA.{u}) {I : Type v} : Pred P I := fun _ _ => True

/-- The least realizability predicate. -/
def falsity (P : PCA.{u}) {I : Type v} : Pred P I := fun _ _ => False

theorem entails_truth (P : PCA.{u}) {I : Type v} (φ : Pred P I) :
    Entails P φ (truth P) := by
  refine ⟨P.ident, ?_⟩
  intro i a ha
  exact ⟨a, P.app_ident a, trivial⟩

theorem falsity_entails (P : PCA.{u}) {I : Type v} (φ : Pred P I) :
    Entails P (falsity P) φ := by
  refine ⟨P.ident, ?_⟩
  intro i a ha
  exact False.elim ha

theorem entails_truth_iff (P : PCA.{u}) {I : Type v} (φ : Pred P I) :
    Entails P φ (truth P) ↔ True := by
  constructor
  · intro h
    trivial
  · intro h
    exact entails_truth P φ

theorem falsity_entails_iff (P : PCA.{u}) {I : Type v} (φ : Pred P I) :
    Entails P (falsity P) φ ↔ True := by
  constructor
  · intro h
    trivial
  · intro h
    exact falsity_entails P φ

@[simp] theorem reindex_truth (P : PCA.{u}) {I : Type v} {J : Type w}
    (f : J → I) : reindex P f (truth P) = truth P := rfl

@[simp] theorem reindex_falsity (P : PCA.{u}) {I : Type v} {J : Type w}
    (f : J → I) : reindex P f (falsity P) = falsity P := rfl

/-! ## Explicit currying code and the implication adjunction -/

/-- A chosen code for currying a tracker whose input is a chosen pair.

`curryVal e t` behaves exactly as `fun a => e (pairVal t a)`.  The first two application laws
make the two curried stages available without choice; the iff law rules out spurious results. -/
structure ChosenCurrying (P : PCA.{u}) (C : ChosenPairing P) where
  curry : P.Carrier
  curryArg : P.Carrier → P.Carrier
  curryVal : P.Carrier → P.Carrier → P.Carrier
  app_curry : ∀ e, P.App curry e (curryArg e)
  app_curryArg : ∀ e t, P.App (curryArg e) t (curryVal e t)
  app_curryVal_iff : ∀ {e t a r},
    P.App (curryVal e t) a r ↔ P.App e (C.pairVal t a) r

namespace ChosenCurrying

/-- The one-element PCA satisfies the explicit currying interface. -/
def unitCurrying : ChosenCurrying PCA.unitPCA ChosenPairing.unitPairing where
  curry := ()
  curryArg := fun _ => ()
  curryVal := fun _ _ => ()
  app_curry := by simp [PCA.unitPCA]
  app_curryArg := by simp [PCA.unitPCA]
  app_curryVal_iff := by simp [PCA.unitPCA]

end ChosenCurrying

namespace ChosenPairing

/-- Evaluation on a chosen pair, derived as `S fst snd`. -/
def eval {P : PCA.{u}} (C : ChosenPairing P) : P.Carrier :=
  P.sArg₂ C.fst C.snd

theorem app_eval {P : PCA.{u}} (C : ChosenPairing P) {q a b : P.Carrier}
    (hqa : P.App q a b) : P.App C.eval (C.pairVal q a) b := by
  exact P.app_s_result (C.app_fst q a) (C.app_snd q a) hqa

end ChosenPairing

/-- Applying an implication realizer to the second component of a pair is uniformly tracked. -/
theorem conj_imp_evaluation (P : PCA.{u}) (C : ChosenPairing P) {I : Type v}
    (φ ψ : Pred P I) : Entails P (conj P C (imp P φ ψ) φ) ψ := by
  refine ⟨C.eval, ?_⟩
  intro i r hr
  rcases hr with ⟨q, hq, a, ha, rfl⟩
  rcases hq a ha with ⟨b, hqab, hb⟩
  exact ⟨b, C.app_eval hqab, hb⟩

/-- Explicit currying turns a tracker on paired inputs into an implication realizer. -/
theorem entails_imp (P : PCA.{u}) (C : ChosenPairing P) (Q : ChosenCurrying P C)
    {I : Type v} {θ φ ψ : Pred P I} (h : Entails P (conj P C θ φ) ψ) :
    Entails P θ (imp P φ ψ) := by
  rcases h with ⟨e, he⟩
  refine ⟨Q.curryArg e, ?_⟩
  intro i t ht
  refine ⟨Q.curryVal e t, Q.app_curryArg e t, ?_⟩
  intro a ha
  rcases he i (C.pairVal t a) ⟨t, ht, a, ha, rfl⟩ with ⟨b, heb, hb⟩
  exact ⟨b, Q.app_curryVal_iff.mpr heb, hb⟩

/-- Evaluation is the reverse direction of implication introduction. -/
theorem imp_elim_entails (P : PCA.{u}) (C : ChosenPairing P)
    {I : Type v} {θ φ ψ : Pred P I} (h : Entails P θ (imp P φ ψ)) :
    Entails P (conj P C θ φ) ψ := by
  have hpair : Entails P (conj P C θ φ) (conj P C (imp P φ ψ) φ) :=
    entails_conj P C
      (entails_trans P (conj_entails_left P C θ φ) h)
      (conj_entails_right P C θ φ)
  exact entails_trans P hpair (conj_imp_evaluation P C φ ψ)

/-- The concrete conjunction and fiberwise implication form a Heyting adjunction when the PCA
has the stated currying code. -/
theorem entails_imp_iff (P : PCA.{u}) (C : ChosenPairing P) (Q : ChosenCurrying P C)
    {I : Type v} {θ φ ψ : Pred P I} :
    Entails P (conj P C θ φ) ψ ↔ Entails P θ (imp P φ ψ) := by
  constructor
  · exact entails_imp P C Q
  · exact imp_elim_entails P C

#assert_all_clean [entails_truth, falsity_entails, entails_truth_iff,
  falsity_entails_iff, reindex_truth, reindex_falsity, ChosenPairing.app_eval,
  conj_imp_evaluation, entails_imp, imp_elim_entails, entails_imp_iff]

end Dregg2.Realizability
