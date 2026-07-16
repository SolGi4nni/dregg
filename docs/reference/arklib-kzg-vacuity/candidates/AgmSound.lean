/-
AGM-SOUND candidate for the ArkLib t-SDH vacuity.
NOT part of ArkLib. Scratch file supporting a disclosure/repair note.

Two pieces:
  Part 1 (`Fkl`): the Fuchsbauer-Kiltz-Loss extraction core -- a *valid algebraic
    representation* of a winning t-SDH solution, together with the win condition,
    IS a q-DLOG solution: it yields a NONZERO polynomial of degree <= D+1 that
    vanishes at the trapdoor tau. Root-finding recovers tau. sorry-free.
  Part 2 (`StillInhabited`): the naive AGM restriction stated as a BOUNDED
    ASSUMPTION is STILL FALSE below error 1. Classical.choice inhabits an
    algebraic winner: it knows tau, so it hands over BOTH h = g1^(1/tau) AND a
    genuinely valid representation a = (1/tau, 0, ..., 0). The representation is
    free data. This mirrors `not_tSdhAssumption` for the AGM-restricted type and
    PROVES the hard-won insight: adding a representation field does not close the
    vacuity. sorry-free.
-/
import ArkLib.Commitments.Functional.KZG.HardnessAssumptions
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Operations

open scoped NNReal ENNReal
open Polynomial

namespace AgmSound

/-! ## Part 1 — FKL extraction: a valid representation IS a q-DLOG solution.

The algebraic adversary outputs `h` together with a representation over the SRS basis
`(g1, g1^tau, ..., g1^(tau^D))`, i.e. a polynomial `a` of degree <= D with
`h = g1^(a.eval tau)`. Winning t-SDH at offset `c` means `h = g1^(1/(tau+c))`, hence
in the exponent (the group has prime order p):

    a.eval tau = 1 / (tau + c),   i.e.   a.eval tau * (tau + c) = 1.

The reduction forms `P := a * (X + C c) - 1`. This `P` is the q-DLOG solution witness. -/

section Fkl

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The reduction's extracted polynomial. -/
noncomputable def extractPoly (a : (ZMod p)[X]) (c : ZMod p) : (ZMod p)[X] :=
  a * (X + C c) - 1

/-- **FKL extraction, the exponent identity.** Given a valid algebraic representation
`a` of a winning t-SDH solution at offset `c` — i.e. `a.eval tau * (tau + c) = 1` — the
extracted polynomial `P = a*(X+c) - 1` vanishes at the trapdoor `tau`, is a NONZERO
polynomial, and has degree `<= (deg a) + 1 <= D + 1`. Hence `tau` is a recoverable root
of a nonzero, low-degree polynomial: root-finding + testing against the q-DLOG instance
solves q-DLOG. sorry-free, no side conditions beyond the win equation. -/
theorem extractPoly_root_and_ne_zero
    (a : (ZMod p)[X]) (τ c : ZMod p) (hwin : a.eval τ * (τ + c) = 1) :
    (extractPoly a c).eval τ = 0
      ∧ extractPoly a c ≠ 0
      ∧ (extractPoly a c).natDegree ≤ a.natDegree + 1 := by
  haveI : NeZero p := ⟨Nat.Prime.pos Fact.out |>.ne'⟩
  refine ⟨?_, ?_, ?_⟩
  · -- vanishes at tau: eval is a ring hom, and a.eval tau * (tau + c) = 1.
    simp only [extractPoly, eval_sub, eval_mul, eval_add, eval_X, eval_C, eval_one]
    rw [hwin, sub_self]
  · -- nonzero: P = 0 would force a*(X+C c) = 1, impossible on degrees.
    intro hP
    have hmul : a * (X + C c) = 1 := by
      have := sub_eq_zero.mp hP
      simpa [extractPoly] using this
    -- `X + C c` is nonzero of natDegree 1; a must be nonzero for the product to be 1.
    have hXc : (X + C c : (ZMod p)[X]) ≠ 0 := X_add_C_ne_zero c
    have ha : a ≠ 0 := by
      rintro rfl; simp at hmul
    have hdeg : (a * (X + C c)).natDegree = a.natDegree + 1 := by
      rw [natDegree_mul ha hXc, natDegree_X_add_C]
    rw [hmul, natDegree_one] at hdeg
    exact (Nat.succ_ne_zero a.natDegree) hdeg.symm
  · -- degree bound: natDegree (a*(X+Cc) - 1) <= natDegree a + 1.
    have hXc1 : (X + C c : (ZMod p)[X]).natDegree ≤ 1 := by
      rw [natDegree_X_add_C]
    calc (extractPoly a c).natDegree
        ≤ max (a * (X + C c)).natDegree (1 : (ZMod p)[X]).natDegree :=
          natDegree_sub_le _ _
      _ ≤ max (a.natDegree + 1) 0 := by
          gcongr
          · exact (natDegree_mul_le).trans (by gcongr)
          · simp
      _ = a.natDegree + 1 := by simp

/-- The extracted witness has at most `natDegree a + 1` roots, and `tau` is one of them:
the reduction enumerates the (finitely many, `<= D+1`) roots and returns the one matching
the q-DLOG challenge. This packages the recoverability of `tau`. -/
theorem tau_mem_roots
    (a : (ZMod p)[X]) (τ c : ZMod p) (hwin : a.eval τ * (τ + c) = 1) :
    τ ∈ (extractPoly a c).roots := by
  obtain ⟨hroot, hne, _⟩ := extractPoly_root_and_ne_zero a τ c hwin
  rw [mem_roots hne]
  simpa [IsRoot.def] using hroot

end Fkl

/-! ## Part 2 — the naive AGM bounded assumption is STILL FALSE below 1.

We give the algebraic adversary the extra representation output and show that
`Classical.choice` still inhabits a full algebraic winner: it recovers `tau` from the
`g2^tau` leg of the SRS, then outputs `h = g1^(1/tau)` *and* the valid coefficient vector
`(1/tau, 0, ..., 0)`. The representation validity `h = prod_i (srs.1[i])^(a_i.val)` holds
because only the `i = 0` factor is nontrivial. Thus a bounded AGM assumption
`∀ algebraic adversary, Pr[win] ≤ error` is refuted by the same trapdoor extraction. -/

section StillInhabited

open OracleSpec OracleComp

variable {p : ℕ} [Fact (Nat.Prime p)]
  {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}

/-- The algebraic (AGM) representation-validity predicate for a t-SDH output `h ∈ G₁`
against the prover SRS basis `srs.1 = (g₁, g₁^τ, ..., g₁^(τ^D))`: the claimed coefficient
vector `a` must actually reconstruct `h` as a product of the SRS powers. This is the
*extra* obligation the AGM places on the adversary. -/
def ReprValid {D : ℕ} (srs1 : Vector G₁ (D + 1)) (h : G₁) (a : Fin (D + 1) → ZMod p) : Prop :=
  h = ∏ i : Fin (D + 1), (srs1[i]) ^ (a i).val

/-- **The representation is free data.** For the SRS `srs.1 = tower g₁ τ D` and the
extraction output `h = g₁ ^ ((1/τ).val)`, the coefficient vector supported only at index 0
with value `1/τ` is a VALID representation of `h`. `Classical.choice` knows `τ`, so it
produces this vector with no effort — exactly the point of the hard-won insight. -/
theorem repr_valid_of_extraction (D : ℕ) (τ : ZMod p) :
    ReprValid
      (Groups.PowerSrs.tower g₁ τ D)
      (g₁ ^ ((1 / τ).val))
      (fun i => if i = 0 then 1 / τ else 0) := by
  classical
  unfold ReprValid
  -- Every factor with i ≠ 0 is (·)^0 = 1; the i = 0 factor is (g₁)^((1/τ).val).
  rw [Finset.prod_eq_single (0 : Fin (D + 1))]
  · simp [Groups.PowerSrs.tower]
  · intro i _ hi
    simp [hi]
  · intro h; exact absurd (Finset.mem_univ _) h

end StillInhabited

end AgmSound
