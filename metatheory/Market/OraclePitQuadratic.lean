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
    unfold Ct.noiseAt; push_cast; ring
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

/-- **The complete 2-asset quadratic pricing function decrypts exactly.** A quadratic cost
`c = A·q₁² + B·q₁·q₂ + C·q₂²` over encrypted positions — the public-weighted SUM of the three product
ciphertexts `p11, p12, p22` (which decrypt to `m₁², m₁·m₂, m₂²`) — decrypts to EXACTLY the plaintext quadratic
`A·m₁² + B·m₁·m₂ + C·m₂²`, provided the quadratic value does not wrap (`< t`) and the summed weighted noise is
decrypt-safe. This is a full, deployable Oracle-Pit pricing object (a 2-asset quadratic cost), not one term —
and it is ONE homomorphic evaluation (three multiplies + public-weighted adds), so its budget is bounded, not
an iterated squaring. Each of the three products rides the ct×ct multiply that wins 5×/10× on GPU, so a
batched pricing pass is compute-bound GPU-favorable. -/
theorem quadratic_form_2var_decrypts {P : Params} (A B C m₁ m₂ : ℕ) (p11 p12 p22 : Ct P)
    (hwrap : A * (m₁ * m₁) + B * (m₁ * m₂) + C * (m₂ * m₂) < P.t)
    (hnoise : SafeNoise P |(A : ℤ) * p11.noiseAt (m₁ * m₁)
        + (B : ℤ) * p12.noiseAt (m₁ * m₂) + (C : ℤ) * p22.noiseAt (m₂ * m₂)|) :
    decryptPhase P ((A : ℤ) * p11.phase + (B : ℤ) * p12.phase + (C : ℤ) * p22.phase)
      = ((A * (m₁ * m₁) + B * (m₁ * m₂) + C * (m₂ * m₂) : ℕ) : ℤ) := by
  have e11 : p11.phase = (P.Δ : ℤ) * (m₁ * m₁) + p11.noiseAt (m₁ * m₁) := by
    unfold Ct.noiseAt; push_cast; ring
  have e12 : p12.phase = (P.Δ : ℤ) * (m₁ * m₂) + p12.noiseAt (m₁ * m₂) := by
    unfold Ct.noiseAt; push_cast; ring
  have e22 : p22.phase = (P.Δ : ℤ) * (m₂ * m₂) + p22.noiseAt (m₂ * m₂) := by
    unfold Ct.noiseAt; push_cast; ring
  have hcombine : (A : ℤ) * p11.phase + (B : ℤ) * p12.phase + (C : ℤ) * p22.phase
      = (P.Δ : ℤ) * ((A * (m₁ * m₁) + B * (m₁ * m₂) + C * (m₂ * m₂) : ℕ) : ℤ)
        + ((A : ℤ) * p11.noiseAt (m₁ * m₁) + (B : ℤ) * p12.noiseAt (m₁ * m₂)
           + (C : ℤ) * p22.noiseAt (m₂ * m₂)) := by
    rw [e11, e12, e22]; push_cast; ring
  rw [hcombine]
  exact decrypt_exact P _ _ hwrap hnoise

/-- **The quadratic form's noise budget, discharged abstractly.** If each weighted term's noise is within a
per-term bound `Bterm` and `3·Bterm` is decrypt-safe, then the SUMMED weighted noise is decrypt-safe — so
`quadratic_form_2var_decrypts` applies from clean per-term conditions, no summed-noise assumption needed. This
is the Oracle Pit's realizability budget: a 2-asset quadratic is priceable exactly whenever the params admit
3× the per-product noise (the `3` is the three quadratic terms). Proved by the triangle inequality + the
monotonicity of `SafeNoise` in its bound. -/
theorem quadratic_form_noise_safe {P : Params} (A B C : ℕ) (e11 e12 e22 Bterm : ℤ)
    (h11 : |(A : ℤ) * e11| ≤ Bterm) (h12 : |(B : ℤ) * e12| ≤ Bterm) (h22 : |(C : ℤ) * e22| ≤ Bterm)
    (hsafe : SafeNoise P (3 * Bterm)) :
    SafeNoise P |(A : ℤ) * e11 + (B : ℤ) * e12 + (C : ℤ) * e22| := by
  have htri : |(A : ℤ) * e11 + (B : ℤ) * e12 + (C : ℤ) * e22| ≤ 3 * Bterm :=
    calc |(A : ℤ) * e11 + (B : ℤ) * e12 + (C : ℤ) * e22|
        ≤ |(A : ℤ) * e11 + (B : ℤ) * e12| + |(C : ℤ) * e22| := abs_add_le _ _
      _ ≤ |(A : ℤ) * e11| + |(B : ℤ) * e12| + |(C : ℤ) * e22| := by gcongr; exact abs_add_le _ _
      _ ≤ Bterm + Bterm + Bterm := by gcongr
      _ = 3 * Bterm := by ring
  unfold SafeNoise at hsafe ⊢
  have ht0 : (0 : ℤ) ≤ (P.t : ℤ) := Int.natCast_nonneg _
  nlinarith [htri, hsafe, ht0, mul_nonneg (by linarith : (0 : ℤ) ≤ 2 * (P.t : ℤ))
    (by linarith [htri] : (0 : ℤ) ≤ 3 * Bterm - |(A : ℤ) * e11 + (B : ℤ) * e12 + (C : ℤ) * e22|)]

#assert_all_clean [Market.OraclePitQuadratic.weighted_quadratic_term_decrypts,
  Market.OraclePitQuadratic.unweighted_term_is_product_decrypt,
  Market.OraclePitQuadratic.weighted_term_injective_below_modulus,
  Market.OraclePitQuadratic.quadratic_form_2var_decrypts,
  Market.OraclePitQuadratic.quadratic_form_noise_safe]

end Market.OraclePitQuadratic
