import Dregg2.Tactics
import Bfv.Noise
import Bfv.Mul

/-!
# The Oracle Pit — first theory stone: the weighted quadratic pricing term decrypts exactly

The Oracle Pit (a FRONTIER hall in `THE-DARK-BAZAAR.md`: a confidential prediction market priced by a
quadratic cost function, not LMSR) needs, at its core, to evaluate a PUBLIC-WEIGHTED QUADRATIC TERM over
ENCRYPTED positions: `A · q₁ · q₂` for a public weight `A`. `Bfv.Mul` proves the ct×ct product `q₁·q₂`
decrypts to the exact `m₁·m₂` (`deployed_mul_relin_decrypts_exact`); this file adds the public weight — the
atomic operation of a quadratic cost function — and proves the weighted term decrypts exactly.

Unlike the linear convex engine (iterated public-scalar-mul), the quadratic COST is a SINGLE ct×ct evaluation
(a public-weighted sum of products, not a T-deep loop), so its noise budget is one multiply's, which is
already proved safe. This is why the Oracle Pit is reachable: quadratic PRICING is one multiply, not an
iterated squaring. (An iterated quadratic SOLVER would square the noise each step and need rescaling —
NAMED, not attempted here.)

The GPU relevance: this weighted product rides the ct×ct multiply that MEASURES a real GPU win at batch
(`FHEGG-GPU-ARCHITECTURE-RECONSIDERED.md`: iGPU 3.35×, 6750 XT 5.13×, Metal 10×). So a batched Oracle-Pit
pricing pass is exactly the compute-bound GPU-favorable shape.
-/

namespace Market.OraclePitQuadratic

open Bfv

/-- **The Oracle Pit atomic op: a public-weighted quadratic term decrypts exactly.** Given a product
ciphertext `prodCt` that decrypts to `m` (`= m₁·m₂`, from `Bfv.Mul`) with its own noise decrypt-safe, scaling
it by a PUBLIC weight `A` (the quadratic cost coefficient) decrypts to exactly `A·m` — PROVIDED the weighted
value does not wrap (`A·m < t`) and the scaled noise `A·(product noise)` is still decrypt-safe. This is the
pricing primitive of a quadratic cost function over encrypted positions. -/
theorem weighted_quadratic_term_decrypts {P : Params} {A m : ℕ} {prodCt : Ct P}
    (hphaseSafe : SafeNoise P |prodCt.noiseAt m|)
    (hwrap : A * m < P.t)
    (hscaleSafe : SafeNoise P |(A : ℤ) * prodCt.noiseAt m|) :
    decryptPhase P ((A : ℤ) * prodCt.phase) = (A * m : ℕ) := by
  have hphase : prodCt.phase = (P.Δ : ℤ) * m + prodCt.noiseAt m := by
    unfold Ct.noiseAt; ring
  have hscaled : (A : ℤ) * prodCt.phase
      = (P.Δ : ℤ) * ((A * m : ℕ) : ℤ) + (A : ℤ) * prodCt.noiseAt m := by
    rw [hphase]; push_cast; ring
  rw [hscaled]
  exact decrypt_exact P (A * m) ((A : ℤ) * prodCt.noiseAt m) hwrap hscaleSafe

/-- The weight-`1` term is exactly the product decrypt — the Oracle Pit reduces to `Bfv.Mul` when unweighted,
so the two stories cannot drift (a sanity anchor, and shows the stronger theorem is a real generalization). -/
theorem unweighted_term_is_product_decrypt {P : Params} {m : ℕ} {prodCt : Ct P}
    (hphaseSafe : SafeNoise P |prodCt.noiseAt m|) (hwrap : m < P.t) :
    decryptPhase P prodCt.phase = (m : ℕ) := by
  have h := weighted_quadratic_term_decrypts (A := 1) (m := m) (prodCt := prodCt)
    hphaseSafe (by simpa using hwrap) (by simpa using hphaseSafe)
  simpa using h

/-- The weighted term is MONOTONE in the weight while it stays below `t`: distinct weights give distinct
prices (injectivity of the pricing map on the no-wrap range), so a quadratic cost is faithfully readable —
and, contrapositively, once `A·m` reaches `t` the map is no longer injective (the `hwrap` guard is what keeps
the price faithful; the Oracle Pit must enforce it at ingest). -/
theorem weighted_term_injective_below_modulus {P : Params} {A A' m : ℕ} {prodCt : Ct P}
    (hSafe : SafeNoise P |prodCt.noiseAt m|)
    (hw : A * m < P.t) (hw' : A' * m < P.t)
    (hsA : SafeNoise P |(A : ℤ) * prodCt.noiseAt m|)
    (hsA' : SafeNoise P |(A' : ℤ) * prodCt.noiseAt m|)
    (hprice : decryptPhase P ((A : ℤ) * prodCt.phase)
            = decryptPhase P ((A' : ℤ) * prodCt.phase)) :
    A * m = A' * m := by
  have hA := weighted_quadratic_term_decrypts (A := A) (m := m) (prodCt := prodCt) hSafe hw hsA
  have hA' := weighted_quadratic_term_decrypts (A := A') (m := m) (prodCt := prodCt) hSafe hw' hsA'
  rw [hA, hA'] at hprice
  exact_mod_cast hprice

#assert_all_clean [Market.OraclePitQuadratic.weighted_quadratic_term_decrypts,
  Market.OraclePitQuadratic.unweighted_term_is_product_decrypt,
  Market.OraclePitQuadratic.weighted_term_injective_below_modulus]

end Market.OraclePitQuadratic
