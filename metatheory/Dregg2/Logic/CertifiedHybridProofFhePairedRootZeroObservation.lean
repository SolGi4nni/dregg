/-
# Complementary-root bounded zero observation

The generic bounded fhIR zero test evaluates `prod (i-r)` for roots
`1..B`.  At an even bound `B = 2k`, pair root `i+1` with root `2k-i`.
Every pair has the shared encrypted quadratic

  `u = r*r - (2k+1)*r`,

and differs only by a public constant.  Consequently the executable schedule
needs one multiplication for `r*r` and `k-1` multiplications for the balanced
product of `k` pair factors: `k` ciphertext multiplications instead of
`2k-1`.  This module proves that the paired polynomial is exactly the existing
bounded polynomial over the whole BFV plaintext ring, not just at test points.

The Rust carrier also handles odd bounds by appending the unpaired middle
root.  The whole-ring identity below covers every complementary pair; the
arbitrary-bound Rust differential is executable validation, not claimed here
as a Rust-to-Lean refinement theorem.  As elsewhere, algebra and primitive
counts are not a BFV noise theorem.

Pure. No axioms.
-/

import Dregg2.Logic.CertifiedHybridProofFheSymmetricZeroObservation
import Dregg2.Tactics

namespace Dregg2.Logic.CertifiedHybridProofFhePairedRootZeroObservation

set_option autoImplicit false

open Dregg2.Logic.FheLogicBfvModel
open Dregg2.Logic.CertifiedHybridProofFhe
open Dregg2.Logic.CertifiedHybridProofFheZeroObservation

abbrev Plain := ZMod bfvPlaintextModulus

def rootFactor (root : Nat) (r : Plain) : Plain := (root : Plain) - r

/-- Pair `i+1` with the reflected root `2k-i`.  The index is intended to be
in `range k`, which makes both roots members of `1..2k`. -/
def complementaryPairFactor (k i : Nat) (r : Plain) : Plain :=
  rootFactor (i + 1) r * rootFactor (2 * k - i) r

/-- Product of all `k` complementary pairs for the bound `2k`. -/
def pairedEvenZeroScaled (k : Nat) (r : Plain) : Plain :=
  ∏ i ∈ Finset.range k, complementaryPairFactor k i r

/-- Each pair is one affine function of the same encrypted quadratic. -/
theorem complementaryPairFactor_shared_quadratic (k i : Nat) (hi : i < k)
    (r : Plain) :
    complementaryPairFactor k i r =
      r * r - ((2 * k + 1 : Nat) : Plain) * r +
        (((i + 1) * (2 * k - i) : Nat) : Plain) := by
  have hki : i ≤ 2 * k := by omega
  simp only [complementaryPairFactor, rootFactor]
  push_cast [hki]
  ring

/-- The paired schedule is the exact generic bounded polynomial.  The proof
uses reflection only to reorder the upper half of the commutative product. -/
theorem pairedEvenZeroScaled_eq_bounded (k : Nat) (r : Plain) :
    pairedEvenZeroScaled k r = boundedZeroScaled (2 * k) r := by
  let factor : Nat → Plain := fun i => rootFactor (i + 1) r
  have hreflect := Finset.prod_range_reflect (fun j => factor (k + j)) k
  have hpairs :
      pairedEvenZeroScaled k r =
        (∏ i ∈ Finset.range k, factor i) *
          ∏ i ∈ Finset.range k, factor (k + (k - 1 - i)) := by
    simp only [pairedEvenZeroScaled, complementaryPairFactor,
      Finset.prod_mul_distrib, factor, rootFactor]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    congr 2
    omega
  rw [hpairs, hreflect]
  rw [← Finset.prod_range_add]
  simp only [factor, rootFactor, boundedZeroScaled]
  congr 3
  omega

theorem pairedEvenZeroScaled_zero (k : Nat) :
    pairedEvenZeroScaled k 0 = ((2 * k).factorial : Plain) := by
  rw [pairedEvenZeroScaled_eq_bounded]
  exact boundedZeroScaled_zero (2 * k)

theorem pairedEvenZeroScaled_positive (k value : Nat)
    (hpositive : 0 < value) (hle : value ≤ 2 * k) :
    pairedEvenZeroScaled k (value : Plain) = 0 := by
  rw [pairedEvenZeroScaled_eq_bounded]
  exact boundedZeroScaled_positive (2 * k) value hpositive hle

/-- Exact high-cost primitives for the complementary-pair conversion.  The
remaining plaintext operations are carried in the executable manifest. -/
structure PairedEvenCost where
  rootPairs : Nat
  ciphertextMultiplications : Nat
  relinearizations : Nat
  deriving DecidableEq, Repr

def pairedEvenCost (k : Nat) : PairedEvenCost :=
  { rootPairs := k
  , ciphertextMultiplications := if k = 0 then 0 else k
  , relinearizations := if k = 0 then 0 else k }

/-- For every useful even bound, pairing saves exactly `k-1` ciphertext
multiplications against the generic balanced factor product. -/
theorem pairedEven_exact_saving (k : Nat) (hk : 0 < k) :
    (pairedEvenCost k).ciphertextMultiplications + (k - 1) =
      boundedZeroMultiplications (2 * k) := by
  simp [pairedEvenCost, boundedZeroMultiplications, hk.ne']
  omega

theorem boundSixteen_saves_seven_ciphertext_multiplications :
    (pairedEvenCost 8).ciphertextMultiplications + 7 =
      boundedZeroMultiplications 16 := by decide

#assert_all_clean [
  complementaryPairFactor_shared_quadratic,
  pairedEvenZeroScaled_eq_bounded,
  pairedEvenZeroScaled_zero,
  pairedEvenZeroScaled_positive,
  pairedEven_exact_saving,
  boundSixteen_saves_seven_ciphertext_multiplications
]

end Dregg2.Logic.CertifiedHybridProofFhePairedRootZeroObservation
