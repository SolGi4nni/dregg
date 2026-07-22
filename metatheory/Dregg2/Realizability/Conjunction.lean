/-
# Dregg2.Realizability.Conjunction — a chosen computable pairing and realizability meet.

The bare PCA layer is enough for uniform entailment and implication membership.  To expose the
usual concrete realizability conjunction without burying a long bracket-abstraction development,
this module asks for explicit *chosen* pair/projection trackers.  This is extra structure carried
as data, not a new axiom: applications and their laws remain ordinary fields/hypotheses of the
model, and `unitPairing` proves the interface inhabited.

From those witnesses we derive the fork combinator using only `S` and `K`, then prove conjunction
introduction and both eliminations.  Hence `conj` is a binary meet for uniformly tracked
entailment.  Reindexing preserves it definitionally.  This still does NOT establish a full tripos:
the implication/conjunction adjunction and quantifier adjoints are not claimed here.
-/
import Dregg2.Realizability.IndexedPredicates

namespace Dregg2.Realizability

universe u v w

/-- Explicit computable pair construction and projections over a PCA. -/
structure ChosenPairing (P : PCA.{u}) where
  pair : P.Carrier
  pairArg : P.Carrier → P.Carrier
  pairVal : P.Carrier → P.Carrier → P.Carrier
  app_pair : ∀ a, P.App pair a (pairArg a)
  app_pairArg : ∀ a b, P.App (pairArg a) b (pairVal a b)
  fst : P.Carrier
  snd : P.Carrier
  app_fst : ∀ a b, P.App fst (pairVal a b) a
  app_snd : ∀ a b, P.App snd (pairVal a b) b

namespace ChosenPairing

/-- `fork e d` computes the pair of `e x` and `d x` when both applications are defined:
`S (S (K pair) e) d`. -/
def fork {P : PCA.{u}} (C : ChosenPairing P) (e d : P.Carrier) : P.Carrier :=
  P.sArg₂ (P.sArg₂ (P.kArg C.pair) e) d

theorem app_fork {P : PCA.{u}} (C : ChosenPairing P) {e d x a b : P.Carrier}
    (he : P.App e x a) (hd : P.App d x b) :
    P.App (C.fork e d) x (C.pairVal a b) := by
  have hpairStage : P.App (P.sArg₂ (P.kArg C.pair) e) x (C.pairArg a) :=
    P.app_s_result (P.app_kArg C.pair x) he (C.app_pair a)
  exact P.app_s_result hpairStage hd (C.app_pairArg a b)

/-- The trivial PCA carries a trivial chosen pairing, providing a concrete model of the extra
interface. -/
def unitPairing : ChosenPairing PCA.unitPCA where
  pair := ()
  pairArg := fun _ => ()
  pairVal := fun _ _ => ()
  app_pair := by simp [PCA.unitPCA]
  app_pairArg := by simp [PCA.unitPCA]
  fst := ()
  snd := ()
  app_fst := by simp [PCA.unitPCA]
  app_snd := by simp [PCA.unitPCA]

end ChosenPairing

/-- Concrete realizability conjunction: a realizer is the chosen computable pair of a realizer
of the left predicate and a realizer of the right predicate. -/
def conj (P : PCA.{u}) (C : ChosenPairing P) {I : Type v}
    (φ ψ : Pred P I) : Pred P I := fun i r =>
  ∃ a, a ∈ φ i ∧ ∃ b, b ∈ ψ i ∧ r = C.pairVal a b

/-- First projection is a uniform conjunction eliminator. -/
theorem conj_entails_left (P : PCA.{u}) (C : ChosenPairing P) {I : Type v}
    (φ ψ : Pred P I) : Entails P (conj P C φ ψ) φ := by
  refine ⟨C.fst, ?_⟩
  intro i r hr
  rcases hr with ⟨a, ha, b, hb, rfl⟩
  exact ⟨a, C.app_fst a b, ha⟩

/-- Second projection is a uniform conjunction eliminator. -/
theorem conj_entails_right (P : PCA.{u}) (C : ChosenPairing P) {I : Type v}
    (φ ψ : Pred P I) : Entails P (conj P C φ ψ) ψ := by
  refine ⟨C.snd, ?_⟩
  intro i r hr
  rcases hr with ⟨a, ha, b, hb, rfl⟩
  exact ⟨b, C.app_snd a b, hb⟩

/-- Pairing two uniform trackers proves conjunction introduction.  The tracker constructed here
is the derived `S (S (K pair) e) d`, not a postulated fork primitive. -/
theorem entails_conj (P : PCA.{u}) (C : ChosenPairing P) {I : Type v}
    {θ φ ψ : Pred P I} (hφ : Entails P θ φ) (hψ : Entails P θ ψ) :
    Entails P θ (conj P C φ ψ) := by
  rcases hφ with ⟨e, he⟩
  rcases hψ with ⟨d, hd⟩
  refine ⟨C.fork e d, ?_⟩
  intro i x hx
  rcases he i x hx with ⟨a, hxa, ha⟩
  rcases hd i x hx with ⟨b, hxb, hb⟩
  exact ⟨C.pairVal a b, C.app_fork hxa hxb, ⟨a, ha, b, hb, rfl⟩⟩

/-- The three laws above are exactly the binary-meet universal property in the tracked preorder. -/
theorem entails_conj_iff (P : PCA.{u}) (C : ChosenPairing P) {I : Type v}
    {θ φ ψ : Pred P I} :
    Entails P θ (conj P C φ ψ) ↔ Entails P θ φ ∧ Entails P θ ψ := by
  constructor
  · intro h
    exact ⟨entails_trans P h (conj_entails_left P C φ ψ),
      entails_trans P h (conj_entails_right P C φ ψ)⟩
  · rintro ⟨hφ, hψ⟩
    exact entails_conj P C hφ hψ

/-- Substitution preserves concrete conjunction on the nose. -/
@[simp] theorem reindex_conj (P : PCA.{u}) (C : ChosenPairing P)
    {I : Type v} {J : Type w} (f : J → I) (φ ψ : Pred P I) :
    reindex P f (conj P C φ ψ) =
      conj P C (reindex P f φ) (reindex P f ψ) := rfl

/-- Conjunction commutes up to mutual uniformly tracked entailment. -/
theorem conj_comm (P : PCA.{u}) (C : ChosenPairing P) {I : Type v}
    (φ ψ : Pred P I) : Equiprovable P (conj P C φ ψ) (conj P C ψ φ) := by
  constructor
  · exact entails_conj P C (conj_entails_right P C φ ψ) (conj_entails_left P C φ ψ)
  · exact entails_conj P C (conj_entails_right P C ψ φ) (conj_entails_left P C ψ φ)

#assert_all_clean [ChosenPairing.app_fork, conj_entails_left, conj_entails_right,
  entails_conj, entails_conj_iff, reindex_conj, conj_comm]

end Dregg2.Realizability
