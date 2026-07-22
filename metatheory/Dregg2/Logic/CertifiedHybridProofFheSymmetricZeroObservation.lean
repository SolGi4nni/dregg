/-
# Dregg2.Logic.CertifiedHybridProofFheSymmetricZeroObservation

An exact, ring-aware specialization of the bounded residual zero test at the
production-relevant bound eight.  The generic carrier evaluates

  `prod_{i=1}^8 (i-r)`

as eight encrypted affine factors and seven ciphertext multiplications.  The
roots have a symmetry the generic product tree does not exploit: pair `i` with
`9-i`, put `u = r^2 - 9r`, and the eight-factor product becomes

  `(u^2 + 28u + 160) (u^2 + 32u + 252)`.

The schedule therefore uses exactly three ciphertext multiplications (`r^2`,
`u^2`, and the final product), at the same multiplicative depth as the balanced
eight-factor tree.  Plaintext-scalar multiplications and additions remain
explicit in the cost ledger.  This is a finite-domain specialization, not a
whole-field zero test and not a BFV noise theorem.

Pure. No axioms.
-/

import Dregg2.Logic.CertifiedHybridProofFheZeroObservation
import Dregg2.Tactics

namespace Dregg2.Logic.CertifiedHybridProofFheSymmetricZeroObservation

set_option autoImplicit false

open Dregg2.Logic.FheLogicBfvModel
open Dregg2.Logic.CertifiedHybridProofFhe
open Dregg2.Logic.CertifiedHybridProofFheZeroObservation

abbrev Plain := ZMod bfvPlaintextModulus

/-- Pairing two affine roots exposes a shared quadratic.  Consecutive bounded
zero products pair `a = i` with `b = B+1-i`, so every pair shares
`r^2 - (B+1)r`; only its public constant term changes. -/
theorem pair_linear_roots (a b r : Plain) :
    (a - r) * (b - r) = r * r - (a + b) * r + a * b := by
  ring

/-- The symmetric, common-subexpression-eliminated bound-eight indicator. -/
def symmetricEightZeroScaled (r : Plain) : Plain :=
  let u := r * r - 9 * r
  let uSquared := u * u
  (uSquared + 28 * u + 160) * (uSquared + 32 * u + 252)

/-- The optimized circuit is the exact same polynomial as the generic bounded
product.  This is an identity over every commutative ring, not merely on the
certified interval. -/
theorem symmetricEightZeroScaled_eq_bounded (r : Plain) :
    symmetricEightZeroScaled r = boundedZeroScaled 8 r := by
  simp [symmetricEightZeroScaled, boundedZeroScaled, Finset.prod_range_succ]
  ring

theorem symmetricEightZeroScaled_zero :
    symmetricEightZeroScaled 0 = ((8).factorial : Plain) := by
  rw [symmetricEightZeroScaled_eq_bounded]
  exact boundedZeroScaled_zero 8

theorem symmetricEightZeroScaled_positive (value : Nat)
    (hpositive : 0 < value) (hle : value ≤ 8) :
    symmetricEightZeroScaled (value : Plain) = 0 := by
  rw [symmetricEightZeroScaled_eq_bounded]
  exact boundedZeroScaled_positive 8 value hpositive hle

theorem symmetricEightZeroScaled_natCast_eq_factorial_iff (value : Nat)
    (hle : value ≤ 8) :
    symmetricEightZeroScaled (value : Plain) = ((8).factorial : Plain) <->
      value = 0 := by
  constructor
  · intro h
    by_contra hne
    have hpositive : 0 < value := Nat.pos_of_ne_zero hne
    rw [symmetricEightZeroScaled_positive value hpositive hle] at h
    have hneFactorial : (0 : Plain) ≠ ((8).factorial : Plain) := by
      decide
    exact hneFactorial h
  · rintro rfl
    exact symmetricEightZeroScaled_zero

/-- Exact primitive ledger for the specialized conversion alone. -/
structure SymmetricEightCost where
  plaintextConstantEncodes : Nat
  ciphertextMultiplications : Nat
  relinearizations : Nat
  ciphertextPlaintextMultiplications : Nat
  ciphertextAdditions : Nat
  ciphertextSubtractions : Nat
  ciphertextPlaintextAdditions : Nat
  inputMultiplicativeDepth : Nat
  outputMultiplicativeDepth : Nat
  deriving DecidableEq, Repr

def symmetricEightCost (inputDepth : Nat) : SymmetricEightCost :=
  { plaintextConstantEncodes := 5
  , ciphertextMultiplications := 3
  , relinearizations := 3
  , ciphertextPlaintextMultiplications := 3
  , ciphertextAdditions := 2
  , ciphertextSubtractions := 1
  , ciphertextPlaintextAdditions := 2
  , inputMultiplicativeDepth := inputDepth
  , outputMultiplicativeDepth := inputDepth + 3 }

theorem symmetricEight_saves_four_ciphertext_multiplications :
    (symmetricEightCost 1).ciphertextMultiplications + 4 =
      boundedZeroMultiplications 8 := by decide

/-- Eight residual squarings plus the specialized three-multiplication
conversion restores a strict primitive-count advantage over the balanced
Boolean baseline for the same eight equalities. -/
theorem eightEquality_total_ciphertext_multiplications :
    8 + (symmetricEightCost 1).ciphertextMultiplications = 11 := by decide

theorem eightEquality_beats_balanced_boolean_multiplications :
    8 + (symmetricEightCost 1).ciphertextMultiplications < 15 := by decide

/-- The specialization changes work, not dependency height: the residual is at
depth one and the three dependent products end at depth four. -/
theorem eightEquality_output_depth :
    (symmetricEightCost 1).outputMultiplicativeDepth = 4 := by decide

#assert_all_clean [
  pair_linear_roots,
  symmetricEightZeroScaled_eq_bounded,
  symmetricEightZeroScaled_zero,
  symmetricEightZeroScaled_positive,
  symmetricEightZeroScaled_natCast_eq_factorial_iff,
  symmetricEight_saves_four_ciphertext_multiplications,
  eightEquality_total_ciphertext_multiplications,
  eightEquality_beats_balanced_boolean_multiplications,
  eightEquality_output_depth
]

end Dregg2.Logic.CertifiedHybridProofFheSymmetricZeroObservation
