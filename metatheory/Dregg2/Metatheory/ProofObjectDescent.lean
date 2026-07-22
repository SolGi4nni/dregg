/-
# Dregg2.Metatheory.ProofObjectDescent — executable local-to-global proof-object gluing.

This module isolates the exact, backend-neutral content of a sheaf condition for the
presheaf of dependent proof objects on a set:

* `DataCover U` is a cover with a computational locator: every point names a patch
  containing it;
* `Matching U s` says local proof objects agree on every pairwise overlap;
* `glue` chooses a local proof object at each point;
* `matching_iff_existsUnique_amalgamation` proves the full existence-and-uniqueness
  sheaf condition; and
* `verifiedEvidence_descends` specializes the result to proof-carrying witnesses
  `{w // Checks x w}`.

The theorem is deliberately independent of polynomials, hashes, commitments, FRI, or
any particular proof backend.  Those mechanisms may establish that a submitted family
is locally valid and overlap-compatible; this module states exactly what then turns the
family into one global proof object.

Honest boundary: this is exact descent under a COMPLETE cover.  A randomly sampled set
of patches is generally not a cover.  Turning sampled local agreement into high-probability
global agreement needs an additional quantitative hypothesis (code distance, expansion,
agreement testing, or another robust local-to-global theorem); ordinary sheaf gluing alone
does not supply IOP/FRI soundness.
-/
import Dregg2.Tactics
import Mathlib.Data.Set.Basic

namespace Dregg2.Metatheory.ProofObjectDescent

universe u v w z

open Set

/-! ## 1. Covers and dependent local sections. -/

/-- A cover equipped with a pointwise patch locator.  Carrying `locate` as data makes
`glue` computational and avoids an appeal to global choice. -/
structure DataCover (X : Type u) (I : Type v) (U : I → Set X) where
  locate : ∀ x : X, {i : I // x ∈ U i}

/-- A section of the dependent family `A` over the subset `V`.  An element may be a
value, a proof, a trace, a strategy certificate, or a verified witness. -/
abbrev LocalSection {X : Type u} (A : X → Type w) (V : Set X) :=
  ∀ (x : X), x ∈ V → A x

/-- Pairwise overlap compatibility for a family of local sections. -/
def Matching {X : Type u} {I : Type v} (U : I → Set X) (A : X → Type w)
    (s : ∀ i, LocalSection A (U i)) : Prop :=
  ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j), s i x hi = s j x hj

/-- A global section restricts to the submitted local family on every patch. -/
def RestrictsTo {X : Type u} {I : Type v} (U : I → Set X) (A : X → Type w)
    (s : ∀ i, LocalSection A (U i)) (g : ∀ x, A x) : Prop :=
  ∀ i x (hx : x ∈ U i), g x = s i x hx

/-! ## 2. The executable gluing map and the sheaf condition. -/

/-- Assemble a global dependent proof object by using the cover's chosen local patch
at each point.  Compatibility is not needed to define the term; it is exactly what
proves that the result is independent of the chosen patch. -/
def glue {X : Type u} {I : Type v} {U : I → Set X} {A : X → Type w}
    (C : DataCover X I U) (s : ∀ i, LocalSection A (U i)) : ∀ x, A x :=
  fun x => s (C.locate x).1 x (C.locate x).2

/-- A matching family glues back to every one of its local sections. -/
theorem glue_restricts {X : Type u} {I : Type v} {U : I → Set X} {A : X → Type w}
    (C : DataCover X I U) (s : ∀ i, LocalSection A (U i))
    (hmatch : Matching U A s) : RestrictsTo U A s (glue C s) := by
  intro i x hx
  exact hmatch (C.locate x).1 i x (C.locate x).2 hx

/-- Any two global amalgamations of the same local family are equal.  Coverage is the
load-bearing hypothesis: inspect both globals on the located patch at each point. -/
theorem amalgamation_unique {X : Type u} {I : Type v} {U : I → Set X} {A : X → Type w}
    (C : DataCover X I U) (s : ∀ i, LocalSection A (U i))
    {g h : ∀ x, A x} (hg : RestrictsTo U A s g) (hh : RestrictsTo U A s h) : g = h := by
  funext x
  exact (hg (C.locate x).1 x (C.locate x).2).trans
    (hh (C.locate x).1 x (C.locate x).2).symm

/-- A global amalgamation forces pairwise agreement on every overlap. -/
theorem matching_of_restricts {X : Type u} {I : Type v} {U : I → Set X} {A : X → Type w}
    (s : ∀ i, LocalSection A (U i)) (g : ∀ x, A x)
    (hg : RestrictsTo U A s g) : Matching U A s := by
  intro i j x hi hj
  exact (hg i x hi).symm.trans (hg j x hj)

/-- **The exact sheaf/descent interface.** A local proof-object family is compatible on
all pairwise overlaps iff it has a unique global amalgamation. -/
theorem matching_iff_existsUnique_amalgamation
    {X : Type u} {I : Type v} {U : I → Set X} {A : X → Type w}
    (C : DataCover X I U) (s : ∀ i, LocalSection A (U i)) :
    Matching U A s ↔ ∃! g : ∀ x, A x, RestrictsTo U A s g := by
  constructor
  · intro hmatch
    refine ⟨glue C s, glue_restricts C s hmatch, ?_⟩
    intro g hg
    exact amalgamation_unique C s hg (glue_restricts C s hmatch)
  · rintro ⟨g, hg, _⟩
    exact matching_of_restricts s g hg

/-- Incompatibility on even one overlap rules out every global amalgamation. -/
theorem incompatible_no_amalgamation
    {X : Type u} {I : Type v} {U : I → Set X} {A : X → Type w}
    (s : ∀ i, LocalSection A (U i)) (hbad : ¬ Matching U A s) :
    ¬ ∃ g : ∀ x, A x, RestrictsTo U A s g := by
  rintro ⟨g, hg⟩
  exact hbad (matching_of_restricts s g hg)

/-! ## 3. Proof-carrying witnesses are a direct instance. -/

/-- The fibre of witnesses that pass `Checks` at point `x`. -/
abbrev VerifiedEvidence {X : Type u} (Witness : X → Type z)
    (Checks : ∀ x, Witness x → Prop) (x : X) :=
  {w : Witness x // Checks x w}

/-- Compatible locally verified witnesses glue to one unique globally verified witness
family.  Verification is retained by construction because every fibre is a subtype. -/
theorem verifiedEvidence_descends
    {X : Type u} {I : Type v} {U : I → Set X}
    (C : DataCover X I U) (Witness : X → Type z)
    (Checks : ∀ x, Witness x → Prop)
    (s : ∀ i, LocalSection (VerifiedEvidence Witness Checks) (U i))
    (hmatch : Matching U (VerifiedEvidence Witness Checks) s) :
    ∃! g : ∀ x, VerifiedEvidence Witness Checks x,
      RestrictsTo U (VerifiedEvidence Witness Checks) s g :=
  (matching_iff_existsUnique_amalgamation C s).mp hmatch

/-! ## 4. Teeth: agreement glues; disagreement on a real overlap cannot. -/

/-- Two patches on `Bool`: patch `false` covers everything and patch `true` covers
the point `true`.  Their overlap is therefore nonempty. -/
def demoPatch : Bool → Set Bool
  | false => Set.univ
  | true => {true}

/-- A constructive cover: patch `false` locates every point. -/
def demoCover : DataCover Bool Bool demoPatch where
  locate x := ⟨false, Set.mem_univ x⟩

/-- Compatible local data: the large patch says `false ↦ 3`, `true ↦ 7`; the small
patch agrees on the overlap point `true`. -/
def demoLocal : ∀ i, LocalSection (fun _ : Bool => Nat) (demoPatch i)
  | false => fun x _ => if x then 7 else 3
  | true => fun _ _ => 7

theorem demoLocal_matching : Matching demoPatch (fun _ : Bool => Nat) demoLocal := by
  intro i j x hi hj
  cases i <;> cases j <;> cases x <;> simp [demoLocal, demoPatch] at hi hj ⊢

theorem demo_glue_false : glue demoCover demoLocal false = 3 := rfl
theorem demo_glue_true : glue demoCover demoLocal true = 7 := rfl

/-- The bad small patch reports `99` at the overlap where the large patch reports `7`. -/
def badLocal : ∀ i, LocalSection (fun _ : Bool => Nat) (demoPatch i)
  | false => fun x _ => if x then 7 else 3
  | true => fun _ _ => 99

theorem badLocal_not_matching : ¬ Matching demoPatch (fun _ : Bool => Nat) badLocal := by
  intro hmatch
  have h := hmatch false true true (Set.mem_univ true) (by simp [demoPatch])
  change (7 : Nat) = 99 at h
  exact (by decide : (7 : Nat) ≠ 99) h

theorem badLocal_has_no_global :
    ¬ ∃ g : Bool → Nat, RestrictsTo demoPatch (fun _ : Bool => Nat) badLocal g :=
  incompatible_no_amalgamation badLocal badLocal_not_matching

#assert_all_clean [glue_restricts, amalgamation_unique, matching_of_restricts,
  matching_iff_existsUnique_amalgamation, incompatible_no_amalgamation,
  verifiedEvidence_descends, demoLocal_matching, demo_glue_false, demo_glue_true,
  badLocal_not_matching, badLocal_has_no_global]

end Dregg2.Metatheory.ProofObjectDescent
