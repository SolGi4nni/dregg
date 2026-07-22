/-
# Dregg2.Metatheory.RobustProofObjectDescent — sampled robust descent interfaces.

`ProofObjectDescent` proves exact gluing from complete overlap agreement.  Agreement tests,
locally testable/sheaf codes, IOPPs, and folding proximity gaps require a more permissive
quantitative boundary.  In particular, their theorems normally apply only to locally valid
views, sample weighted edges or queries, reject an entire overlap restriction, and use
nonlinear or thresholded soundness moduli.

This module therefore keeps exact zero-disagreement descent, but makes the quantitative layer
abstract in precisely those dimensions:

* `WeightedQueryModel` is an explicit finite query distribution represented by natural weights;
* a query's rejection predicate is arbitrary and can inspect a whole overlap;
* `RejectLowerSoundness` states `rejectWeight >= h(distance)` for an arbitrary monotone `h`;
* `DistanceUpperSoundness` states `distance <= rho(rejectWeight)` for an arbitrary monotone `rho`;
* both soundness interfaces have an explicit `locallyValid` premise;
* `FoldChainSoundness` separates one-round distance preservation and exceptional challenges; and
* `ProximityGap` separately bounds challenges that move a far object close.

These structures are theorem *sockets*.  No external code, expansion, IOPP, or proximity-gap
theorem is postulated here.  Concrete papers may instantiate a socket only after their actual
hypotheses and proof have been formalized.
-/
import Dregg2.Metatheory.ProofObjectDescent
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace Dregg2.Metatheory.RobustProofObjectDescent

open Set
open scoped BigOperators
open Dregg2.Metatheory.ProofObjectDescent

universe u v w q

/-! ## 1. Finite covers. -/

/-- A finite cover retaining the constructive locator needed by exact descent. -/
structure FinCover (X : Type u) (I : Type v) [DecidableEq X] where
  patch : I → Finset X
  locate : ∀ x : X, {i : I // x ∈ patch i}

def FinCover.patchSet {X : Type u} {I : Type v} [DecidableEq X]
    (C : FinCover X I) (i : I) : Set X := ↑(C.patch i)

def FinCover.toDataCover {X : Type u} {I : Type v} [DecidableEq X]
    (C : FinCover X I) : DataCover X I C.patchSet where
  locate x := C.locate x

abbrev SectionFamily {X : Type u} {I : Type v} [DecidableEq X]
    (C : FinCover X I) (A : X → Type w) :=
  ∀ i, LocalSection A (C.patchSet i)

/-! ## 2. Weighted finite query distributions and whole-overlap tests. -/

/-- A denominator-free finite distribution: query `a` has natural mass `weight a`.
The rejection predicate may inspect any local data represented by `Family`. -/
structure WeightedQueryModel (Family : Type*) (Query : Type q) [Fintype Query] where
  weight : Query → Nat
  reject : Family → Query → Prop
  rejectDecidable : ∀ s a, Decidable (reject s a)

/-- Weighted cardinality of a decidable predicate. -/
def weightedCount {Q : Type q} [Fintype Q] (weight : Q → Nat)
    (P : Q → Prop) (hP : ∀ a, Decidable (P a)) : Nat :=
  Finset.univ.sum fun a => @ite Nat (P a) (hP a) (weight a) 0

namespace WeightedQueryModel

variable {Family : Type*} {Query : Type q} [Fintype Query]

def totalWeight (M : WeightedQueryModel Family Query) : Nat :=
  Finset.univ.sum M.weight

def rejectedWeight (M : WeightedQueryModel Family Query) (s : Family) : Nat :=
  weightedCount M.weight (M.reject s) (M.rejectDecidable s)

def rejectionRate (M : WeightedQueryModel Family Query) (s : Family) : ℚ :=
  (M.rejectedWeight s : ℚ) / (M.totalWeight : ℚ)

end WeightedQueryModel

/-- Reject a pair of local views when their *whole overlap restriction* disagrees.
Unlike `overlapBadAt`, one query is the edge `(i,j)`, not an incidence `(i,j,x)`. -/
def wholeOverlapReject {X : Type u} {I : Type v} [DecidableEq X]
    {C : FinCover X I} {A : X → Type w}
    (s : SectionFamily C A) (e : I × I) : Prop :=
  ∃ (x : X) (hi : x ∈ C.patch e.1) (hj : x ∈ C.patch e.2),
    s e.1 x hi ≠ s e.2 x hj

/-- Whole-overlap acceptance on every ordered edge is exactly the matching condition. -/
theorem noWholeOverlapReject_iff_matching
    {X : Type u} {I : Type v} [DecidableEq X]
    {C : FinCover X I} {A : X → Type w} (s : SectionFamily C A) :
    (∀ e : I × I, ¬ wholeOverlapReject s e) ↔ Matching C.patchSet A s := by
  constructor
  · intro h i j x hi hj
    by_contra hne
    exact h (i, j) ⟨x, hi, hj, hne⟩
  · intro h e he
    obtain ⟨x, hi, hj, hne⟩ := he
    exact hne (h e.1 e.2 x hi hj)

/-- Uniform ordered-edge queries are one adapter; weighted graph edges and protocol queries may
instead provide their own `WeightedQueryModel`. -/
noncomputable def wholeOverlapQueryModel
    {X : Type u} {I : Type v} [DecidableEq X] [Fintype X] [Fintype I]
    (C : FinCover X I) (A : X → Type w) [∀ x, DecidableEq (A x)] :
    WeightedQueryModel (SectionFamily C A) (I × I) where
  weight _ := 1
  reject := wholeOverlapReject
  rejectDecidable _ _ := Classical.propDecidable _

section ExactWholeOverlap

variable {X : Type u} {I : Type v} [DecidableEq X]
variable [Fintype I]
variable (C : FinCover X I)
variable {A : X → Type w}

/-- The finite set of ordered patch edges whose whole overlap restriction disagrees. -/
noncomputable def overlapBadEdges (s : SectionFamily C A) : Finset (I × I) :=
  by
    classical
    exact Finset.univ.filter (wholeOverlapReject s)

/-- Exact disagreement count.  Quantitative theorems below are not tied to this uniform count. -/
noncomputable def overlapBadCount (s : SectionFamily C A) : Nat :=
  (overlapBadEdges C s).card

theorem overlapBadCount_eq_zero_iff_matching (s : SectionFamily C A) :
    overlapBadCount C s = 0 ↔ Matching C.patchSet A s := by
  classical
  rw [overlapBadCount, overlapBadEdges, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp only [Finset.mem_univ, true_implies]
  exact noWholeOverlapReject_iff_matching s

/-- Exact zero-disagreement descent, unchanged semantically and delegated to the exact theorem. -/
theorem exact_descent_of_zero_overlap (s : SectionFamily C A)
    (hzero : overlapBadCount C s = 0) :
    ∃! g : ∀ x, A x, RestrictsTo C.patchSet A s g :=
  (matching_iff_existsUnique_amalgamation C.toDataCover s).mp
    ((overlapBadCount_eq_zero_iff_matching C s).mp hzero)

theorem zero_overlap_of_amalgamation (s : SectionFamily C A) (g : ∀ x, A x)
    (hg : RestrictsTo C.patchSet A s g) : overlapBadCount C s = 0 :=
  (overlapBadCount_eq_zero_iff_matching C s).mpr (matching_of_restricts s g hg)

end ExactWholeOverlap

/-! ## 3. Two equivalent styles of robust local-to-global theorem. -/

section RobustInterfaces

variable {X : Type u} {I : Type v} [DecidableEq X]
variable (C : FinCover X I)
variable (A : X → Type w)
variable {Query : Type q} [Fintype Query]

/-- A chosen distance to a global section, with precisely the zero law needed by exact descent.
Different code families may use weighted symbol distance, block distance, or another promised
metric; the robust interfaces do not force uniform local-point incidence. -/
structure DescentDistance where
  distance : SectionFamily C A → (∀ x, A x) → Nat
  zero_iff_restricts : ∀ s g,
    distance s g = 0 ↔ RestrictsTo C.patchSet A s g

/-- Literature form `reject >= h(distance)`.  `h` may be nonlinear, thresholded, or zero below
a promised radius.  Its output is measured in the query model's integer weight units. -/
structure RejectLowerSoundness (M : WeightedQueryModel (SectionFamily C A) Query)
    (D : DescentDistance C A) where
  locallyValid : SectionFamily C A → Prop
  h : Nat → Nat
  h_mono : Monotone h
  sound : ∀ s, locallyValid s →
    ∃ g : ∀ x, A x, h (D.distance s g) ≤ M.rejectedWeight s

/-- Literature form `distance <= rho(reject)`.  No linear-factor or inverse assumption is built
in: cube-root, small-radius, and piecewise moduli all fit this structure. -/
structure DistanceUpperSoundness (M : WeightedQueryModel (SectionFamily C A) Query)
    (D : DescentDistance C A) where
  locallyValid : SectionFamily C A → Prop
  rho : Nat → Nat
  rho_mono : Monotone rho
  sound : ∀ s, locallyValid s →
    ∃ g : ∀ x, A x, D.distance s g ≤ rho (M.rejectedWeight s)

/-- A lower-bound soundness theorem whose modulus reflects zero recovers exact descent when the
weighted tester has zero rejection. -/
theorem RejectLowerSoundness.zero_rejection_exact
    {M : WeightedQueryModel (SectionFamily C A) Query}
    {D : DescentDistance C A} (R : RejectLowerSoundness C A M D)
    (hReflectsZero : ∀ d, R.h d = 0 → d = 0)
    (s : SectionFamily C A) (hvalid : R.locallyValid s)
    (hzero : M.rejectedWeight s = 0) :
    ∃! g : ∀ x, A x, RestrictsTo C.patchSet A s g := by
  obtain ⟨g, hbound⟩ := R.sound s hvalid
  rw [hzero] at hbound
  have hh : R.h (D.distance s g) = 0 := Nat.eq_zero_of_le_zero hbound
  have hdist : D.distance s g = 0 := hReflectsZero _ hh
  have hg := (D.zero_iff_restricts s g).mp hdist
  exact (matching_iff_existsUnique_amalgamation C.toDataCover s).mp
    (matching_of_restricts s g hg)

/-- The inverse-modulus form has the corresponding exact adapter when `rho 0 = 0`. -/
theorem DistanceUpperSoundness.zero_rejection_exact
    {M : WeightedQueryModel (SectionFamily C A) Query}
    {D : DescentDistance C A} (R : DistanceUpperSoundness C A M D)
    (hrho0 : R.rho 0 = 0)
    (s : SectionFamily C A) (hvalid : R.locallyValid s)
    (hzero : M.rejectedWeight s = 0) :
    ∃! g : ∀ x, A x, RestrictsTo C.patchSet A s g := by
  obtain ⟨g, hbound⟩ := R.sound s hvalid
  rw [hzero, hrho0] at hbound
  have hg := (D.zero_iff_restricts s g).mp (Nat.eq_zero_of_le_zero hbound)
  exact (matching_iff_existsUnique_amalgamation C.toDataCover s).mp
    (matching_of_restricts s g hg)

end RobustInterfaces

/-! ## 4. Folding chains and proximity gaps are separate protocol properties. -/

/-- One-step data sufficient to compose fold-round distance preservation.

An exceptional challenge is required to cover every challenge that decreases distance by more
than the advertised slack.  `exceptionalBound` is an explicit weighted-count theorem.  A concrete
protocol may sum these bounds across a transcript, but Fiat--Shamir/adaptive-prover reasoning is
intentionally outside this combinatorial interface. -/
structure FoldChainSoundness (State : Type u) (Challenge : Type v) [Fintype Challenge] where
  rounds : Nat
  challengeWeight : Fin rounds → Challenge → Nat
  locallyValid : Fin rounds → State → Prop
  distance : Nat → State → Nat
  fold : Fin rounds → State → Challenge → State
  slack : Fin rounds → Nat
  exceptional : Fin rounds → State → Challenge → Prop
  exceptionalDecidable : ∀ r s a, Decidable (exceptional r s a)
  exceptionalBudget : Fin rounds → State → Nat
  exceptional_covers_drop : ∀ r s a,
    distance (r.1 + 1) (fold r s a) + slack r < distance r.1 s → exceptional r s a
  exceptional_bound : ∀ r s, locallyValid r s →
    weightedCount (challengeWeight r) (exceptional r s) (exceptionalDecidable r s)
      ≤ exceptionalBudget r s

/-- Outside the declared exceptional set, one fold cannot lose more distance than `slack`. -/
theorem FoldChainSoundness.distance_preserved
    {State : Type u} {Challenge : Type v} [Fintype Challenge]
    (F : FoldChainSoundness State Challenge) (r : Fin F.rounds) (s : State) (a : Challenge)
    (hgood : ¬ F.exceptional r s a) :
    F.distance r.1 s ≤ F.distance (r.1 + 1) (F.fold r s a) + F.slack r := by
  exact Nat.le_of_not_gt (fun hdrop => hgood (F.exceptional_covers_drop r s a hdrop))

/-- A correlated-agreement/proximity-gap socket.  A source beyond `sourceRadius` has at most
`goodBudget` challenge weight whose transformed object lies inside `targetRadius`.

This is deliberately not called a tester: it has no query/prover complexity and makes no claim
that a transformation is locally checkable. -/
structure ProximityGap (Word : Type u) (Challenge : Type v) [Fintype Challenge] where
  challengeWeight : Challenge → Nat
  sourceDistance : Word → Nat
  transformedDistance : Word → Challenge → Nat
  sourceRadius : Nat
  targetRadius : Nat
  goodBudget : Nat
  goodDecidable : ∀ w a, Decidable (transformedDistance w a < targetRadius)
  gap : ∀ w, sourceRadius ≤ sourceDistance w →
    weightedCount challengeWeight
      (fun a => transformedDistance w a < targetRadius) (goodDecidable w) ≤ goodBudget

/-! ## 5. Nontrivial finite witnesses. -/

namespace UnitPair

def patch (_ : Bool) : Finset Unit := Finset.univ

def cover : FinCover Unit Bool where
  patch := patch
  locate _ := ⟨false, by simp [patch]⟩

def pairSection (a b : Bool) : SectionFamily cover (fun _ : Unit => Bool)
  | false => fun _ _ => a
  | true => fun _ _ => b

theorem section_eq_pairSection (s : SectionFamily cover (fun _ : Unit => Bool)) :
    s = pairSection (s false () (by simp [FinCover.patchSet, cover, patch]))
      (s true () (by simp [FinCover.patchSet, cover, patch])) := by
  funext i x hx
  cases i <;> cases x <;> simp [pairSection]

/-- Unit-pair block distance.  It is one iff either submitted site differs from `g ()`. -/
def pairDistance : DescentDistance cover (fun _ : Unit => Bool) where
  distance s g :=
    if s false () (by simp [FinCover.patchSet, cover, patch]) = g () ∧
        s true () (by simp [FinCover.patchSet, cover, patch]) = g () then 0 else 1
  zero_iff_restricts := by
    intro s g
    constructor
    · intro hzero
      have hpairs :
          s false () (by simp [FinCover.patchSet, cover, patch]) = g () ∧
          s true () (by simp [FinCover.patchSet, cover, patch]) = g () := by
        by_contra hbad
        simp [hbad] at hzero
      intro i x hx
      cases i <;> cases x
      · exact hpairs.1.symm
      · exact hpairs.2.symm
    · intro hrestrict
      have hf := (hrestrict false () (by simp [FinCover.patchSet, cover, patch])).symm
      have ht := (hrestrict true () (by simp [FinCover.patchSet, cover, patch])).symm
      simp [hf, ht]

theorem distance_table (a b : Bool) :
    pairDistance.distance (pairSection a b) (fun _ => a) =
      (if a = b then 0 else 1) := by
  cases a <;> cases b <;> simp [pairDistance, pairSection]

/-- One whole-overlap edge of weight two.  Thus the inconsistent pair has rejection weight two,
without introducing diagonal queries or point-incidence normalization. -/
def pairQuery : WeightedQueryModel
    (SectionFamily cover (fun _ : Unit => Bool)) Unit where
  weight _ := 2
  reject s _ :=
    s false () (by simp [FinCover.patchSet, cover, patch]) ≠
      s true () (by simp [FinCover.patchSet, cover, patch])
  rejectDecidable _ _ := inferInstance

theorem rejection_table (a b : Bool) :
    pairQuery.rejectedWeight (pairSection a b) = (if a = b then 0 else 2) := by
  cases a <;> cases b <;>
    simp [WeightedQueryModel.rejectedWeight, weightedCount, pairQuery, pairSection,
      cover, patch]

/-- A locally-valid nonlinear-socket instance with `h(d)=2d`; the disagreeing family attains
equality `rejectWeight = 2`, `distance = 1`. -/
def pairLower : RejectLowerSoundness cover (fun _ : Unit => Bool) pairQuery pairDistance where
  locallyValid _ := True
  h d := 2 * d
  h_mono _ _ h := Nat.mul_le_mul_left 2 h
  sound s _ := by
    let a := s false () (by simp [FinCover.patchSet, cover, patch])
    let b := s true () (by simp [FinCover.patchSet, cover, patch])
    have hs : s = pairSection a b := section_eq_pairSection s
    refine ⟨fun _ => a, ?_⟩
    rw [hs, distance_table, rejection_table]
    by_cases h : a = b <;> simp [h]

/-- The inverse-modulus presentation of the same theorem, `rho(r)=r/2`. -/
def pairUpper : DistanceUpperSoundness cover (fun _ : Unit => Bool) pairQuery pairDistance where
  locallyValid _ := True
  rho r := r / 2
  rho_mono _ _ h := Nat.div_le_div_right h
  sound s _ := by
    let a := s false () (by simp [FinCover.patchSet, cover, patch])
    let b := s true () (by simp [FinCover.patchSet, cover, patch])
    have hs : s = pairSection a b := section_eq_pairSection s
    refine ⟨fun _ => a, ?_⟩
    rw [hs, distance_table, rejection_table]
    by_cases h : a = b <;> simp [h]

def disagreeing : SectionFamily cover (fun _ : Unit => Bool) := pairSection false true

theorem disagreeing_is_quantitative :
    pairQuery.rejectedWeight disagreeing = 2 ∧
      pairDistance.distance disagreeing (fun _ => false) = 1 := by
  exact ⟨by simpa [disagreeing] using rejection_table false true,
    by simpa [disagreeing] using distance_table false true⟩

/-- Zero-rejection exact descent is obtained through the new lower-soundness adapter, not by a
second gluing proof. -/
theorem pairLower_zero_exact (s : SectionFamily cover (fun _ : Unit => Bool))
    (hzero : pairQuery.rejectedWeight s = 0) :
    ∃! g : Unit → Bool, RestrictsTo cover.patchSet (fun _ : Unit => Bool) s g := by
  apply pairLower.zero_rejection_exact
  · intro d hd
    simpa [pairLower] using hd
  · trivial
  · exact hzero

end UnitPair

namespace FoldToy

def boolDistance (_ : Nat) (s : Bool) : Nat := if s then 1 else 0
def boolFold (_ : Fin 1) (s a : Bool) : Bool := if a then false else s

/-- A one-round chain with two challenges.  Exactly challenge `true` is exceptional when the
state is `true`; its weight-one budget is sharp. -/
def chain : FoldChainSoundness Bool Bool where
  rounds := 1
  challengeWeight _ _ := 1
  locallyValid _ _ := True
  distance := boolDistance
  fold := boolFold
  slack _ := 0
  exceptional _ s a := s = true ∧ a = true
  exceptionalDecidable _ _ _ := inferInstance
  exceptionalBudget _ _ := 1
  exceptional_covers_drop := by
    intro r s a
    fin_cases r
    cases s <;> cases a <;> decide
  exceptional_bound := by
    intro r s _
    fin_cases r
    cases s <;> simp [weightedCount]

def round0 : Fin chain.rounds := ⟨0, by simp [chain]⟩

theorem true_true_is_exceptional : chain.exceptional round0 true true := by
  simp [chain, round0]

theorem false_challenge_preserves_true_distance :
    chain.distance round0.1 true ≤
      chain.distance (round0.1 + 1) (chain.fold round0 true false) + chain.slack round0 :=
  chain.distance_preserved round0 true false (by simp [chain, round0])

end FoldToy

namespace GapToy

def sourceDistance (w : Bool) : Nat := if w then 0 else 1
def transformedDistance (w a : Bool) : Nat := if a = w then 0 else 1

/-- The only far word is `false`; exactly one of two unit-weight challenges moves it inside the
target radius.  This witnesses a genuine proximity gap with budget one. -/
def gap : ProximityGap Bool Bool where
  challengeWeight _ := 1
  sourceDistance := sourceDistance
  transformedDistance := transformedDistance
  sourceRadius := 1
  targetRadius := 1
  goodBudget := 1
  goodDecidable _ _ := inferInstance
  gap w hfar := by
    cases w <;> simp [transformedDistance, weightedCount] at hfar ⊢

theorem far_false_has_one_good_challenge :
    weightedCount gap.challengeWeight
      (fun a => gap.transformedDistance false a < gap.targetRadius)
      (gap.goodDecidable false) = 1 := by
  simp [gap, transformedDistance, weightedCount]

end GapToy

/-! ## 6. Axiom-hygiene pins. -/

#assert_all_clean [
  overlapBadCount_eq_zero_iff_matching,
  exact_descent_of_zero_overlap,
  zero_overlap_of_amalgamation,
  noWholeOverlapReject_iff_matching,
  RejectLowerSoundness.zero_rejection_exact,
  DistanceUpperSoundness.zero_rejection_exact,
  FoldChainSoundness.distance_preserved,
  UnitPair.section_eq_pairSection,
  UnitPair.distance_table,
  UnitPair.rejection_table,
  UnitPair.disagreeing_is_quantitative,
  UnitPair.pairLower_zero_exact,
  FoldToy.true_true_is_exceptional,
  FoldToy.false_challenge_preserves_true_distance,
  GapToy.far_false_has_one_good_challenge]

end Dregg2.Metatheory.RobustProofObjectDescent
