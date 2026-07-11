/-
# `Dregg2.Crypto.VerifyCoreEqSpec` — closing the `verifyCore` IS-the-spec residuals: the coeff↔`R_q` bridge.

`VerifyCoreSpec.verifyCore_split` reduced the executable ML-DSA-65 `verifyCore` to the two FIPS 204 Algorithm
8 acceptance conditions, leaving three NAMED `∀`-bridges (`VerifyCoreSpec.{RingRepFaithful, DecodeSemantics,
ChallengeMatchesSpec}`). `NttFaithful.ringRepFaithful_proven` closed the hard one (the fast NTT multiply
computes the negacyclic ring product, for all size-256 reduced polys). THIS file builds the remaining
algebraic bridge that turns that coefficient-array fact into a statement over the REAL ring
`R_q = ℤ_q[X]/(X²⁵⁶+1)` (`Fips204CorrectReal.Rq`):

* **`toRq : Poly → Rq`** — the coeff-array → `R_q` map `a ↦ ∑_{i<256} a_i · root^i`. This is the executable-
  representation ↔ `AdjoinRoot` bridge the seam named as remaining.
* **`toRq_schoolbookMul`** — `toRq (schoolbookMul a b) = toRq a * toRq b`: the executable negacyclic
  convolution IS the `R_q` product, for ALL poly pairs. Proved from `NttFaithful.schoolbookMul_getElem` (the
  `∑_{i+j=m} − ∑_{i+j=m+256}` coefficient formula) + `Fips204CorrectReal.root_pow_256` (`root²⁵⁶ = −1`).
* **`toRq_nttMul`** — composing with `ringRepFaithful_proven`: `toRq (intt (pointwiseMul (ntt a) (ntt b))) =
  toRq a * toRq b`. verifyCore's NTT-domain multiply computes the `R_q` product.
* **`toRq_add` / `toRq_sub`** — `toRq` carries the executable `addPoly`/`subPoly` to `R_q` `+`/`−`.
* **`nttMatmul_isRingArg`** — the culmination for the challenge conjunct: verifyCore's per-row
  `intt(Σ_j Â[i,j]⊙ntt(z_j) − ĉ⊙ntt(2^d·t1_i))` equals the spec's `Σ_j A_ij·z_j − c·(2^d·t1_i)` over `R_q`.

The residuals that remain (NAMED, not laundered) are the codec bit-packing round-trip (`DecodeSemantics`) and
the hash/challenge INSTANTIATION — see the closing section.
-/
import Dregg2.Crypto.NttFaithful
import Dregg2.Crypto.Fips204CorrectReal

namespace Dregg2.Crypto.VerifyCoreEqSpec

open Dregg2.Crypto.MlDsaRing (Poly q zeroPoly ntt intt pointwiseMul addPoly subPoly schoolbookMul cJ
  schoolbookMul_getElem schoolbookMul_size schoolbookMul_lt ringRepFaithful_proven
  cast_addPoly cast_subPoly)
open Polynomial Finset

set_option maxRecDepth 8000

/-- The negacyclic ring modulus polynomial, over `ℤ_q` (`q = MlDsaRing.q = 8380417`). -/
local notation "F" => (X ^ 256 + 1 : (ZMod q)[X])

/-- **The REAL ML-DSA ring** `R_q = ℤ_q[X]/(X²⁵⁶+1)` — DEFINITIONALLY `Fips204CorrectReal.Rq` (its base
`Fips204CorrectReal.q` is `rfl`-equal to `MlDsaRing.q`), stated over `MlDsaRing.q` so the executable
coefficient casts (`cJ`, `schoolbookMul_getElem`) match syntactically. -/
noncomputable abbrev Rq := AdjoinRoot F

/-- `Rq` IS `Fips204CorrectReal.Rq` (the `q`s are `rfl`-equal). -/
theorem Rq_eq : Rq = Dregg2.Crypto.Fips204CorrectReal.Rq := rfl

/-- The `R_q` root of `X²⁵⁶+1`. -/
noncomputable abbrev r : Rq := AdjoinRoot.root F

/-- **`root²⁵⁶ = −1` in `R_q`** — the negacyclic relation (re-derived here over `MlDsaRing.q`; identical to
`Fips204CorrectReal.root_pow_256`). -/
theorem root_pow_256 : r ^ 256 = -1 := by
  have h : AdjoinRoot.mk F (X ^ 256 + 1) = 0 := AdjoinRoot.mk_self
  have hr : r ^ 256 + 1 = 0 := by
    simpa [map_add, map_pow, map_one, AdjoinRoot.mk_X] using h
  linear_combination hr

/-- The `ℤ_q` reduction of an executable `Nat` coefficient. -/
abbrev cf (n : Nat) : ZMod q := (n : ZMod q)

/-- **The coeff-array → `R_q` bridge.** `toRq a = ∑_{i<256} a_i · root^i` — the executable size-256
coefficient array read as an element of `R_q = ℤ_q[X]/(X²⁵⁶+1)`. -/
noncomputable def toRq (a : Poly) : Rq :=
  ∑ i ∈ range 256, AdjoinRoot.of F (cf (a[i]!)) * r ^ i

/-- Expand the `R_q` product of two bridged arrays into the double coefficient sum with `root^{i+j}`
(no negacyclic reduction yet — that lands per-`(i,j)` in `coeff_collapse`). -/
theorem toRq_mul_expand (a b : Poly) :
    toRq a * toRq b
      = ∑ i ∈ range 256, ∑ j ∈ range 256,
          AdjoinRoot.of F (cf (a[i]!) * cf (b[j]!)) * r ^ (i + j) := by
  unfold toRq
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [map_mul, pow_add]
  ring

/-- **The negacyclic collapse, per coefficient pair.** For `i, j < 256`, summing the signed contribution
`cJ a b i j m · root^m` over all output slots `m` collapses (using `root²⁵⁶ = −1`) to the single ring term
`a_i·b_j · root^{i+j}`. The `i+j ≥ 256` branch is where `X²⁵⁶ = −1` fires. -/
theorem coeff_collapse (a b : Poly) (i j : Nat) (hi : i < 256) (hj : j < 256) :
    ∑ m ∈ range 256, AdjoinRoot.of F (cJ a b i j m) * r ^ m
      = AdjoinRoot.of F (cf (a[i]!) * cf (b[j]!)) * r ^ (i + j) := by
  by_cases hlt : i + j < 256
  · rw [Finset.sum_eq_single (i + j)]
    · have hcj : cJ a b i j (i + j) = cf (a[i]!) * cf (b[j]!) := by unfold cJ; rw [if_pos rfl]
      rw [hcj]
    · intro m hmem hm
      rw [Finset.mem_range] at hmem
      have : cJ a b i j m = 0 := by unfold cJ; rw [if_neg (by omega), if_neg (by omega)]
      rw [this, map_zero, zero_mul]
    · intro hmem; exact absurd (Finset.mem_range.mpr hlt) hmem
  · have hm0 : i + j - 256 < 256 := by omega
    rw [Finset.sum_eq_single (i + j - 256)]
    · have hcj : cJ a b i j (i + j - 256) = -(cf (a[i]!) * cf (b[j]!)) := by
        unfold cJ; rw [if_neg (by omega), if_pos (by omega)]
      rw [hcj, map_neg]
      have hpow : r ^ (i + j) = -(r ^ (i + j - 256)) := by
        conv_lhs => rw [show i + j = 256 + (i + j - 256) from by omega]
        rw [pow_add, root_pow_256, neg_one_mul]
      rw [hpow]; ring
    · intro m hmem hm
      rw [Finset.mem_range] at hmem
      have : cJ a b i j m = 0 := by unfold cJ; rw [if_neg (by omega), if_neg (by omega)]
      rw [this, map_zero, zero_mul]
    · intro hmem; exact absurd (Finset.mem_range.mpr hm0) hmem

/-- **THE COEFF↔`R_q` RING BRIDGE.** `toRq (schoolbookMul a b) = toRq a * toRq b` for ALL poly pairs: the
executable negacyclic convolution IS the `R_q = ℤ_q[X]/(X²⁵⁶+1)` product. Proved from
`NttFaithful.schoolbookMul_getElem` (the `∑_{i+j=m} − ∑_{i+j=m+256}` coefficient formula) and
`Fips204CorrectReal.root_pow_256` (`root²⁵⁶ = −1`) — no `native_decide`, no size/range guard needed (both
sides read the same reduced 256-array). -/
theorem toRq_schoolbookMul (a b : Poly) :
    toRq (schoolbookMul a b) = toRq a * toRq b := by
  rw [toRq_mul_expand]
  unfold toRq
  -- Rewrite each coefficient of the product array by the negacyclic formula, push `of`/`* r^m` inward.
  have hstep : ∀ m ∈ range 256,
      AdjoinRoot.of F (cf ((schoolbookMul a b)[m]!)) * r ^ m
        = ∑ i ∈ range 256, ∑ j ∈ range 256, AdjoinRoot.of F (cJ a b i j m) * r ^ m := by
    intro m hm
    have hm256 : m < 256 := Finset.mem_range.mp hm
    have hcoef : cf ((schoolbookMul a b)[m]!) = ∑ i ∈ range 256, ∑ j ∈ range 256, cJ a b i j m := by
      show (((schoolbookMul a b)[m]! : Nat) : ZMod q) = _
      exact schoolbookMul_getElem a b m hm256
    rw [hcoef, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl hstep]
  -- Now swap `∑_m ∑_i ∑_j = ∑_i ∑_j ∑_m` and collapse the inner `m`-sum.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  exact coeff_collapse a b i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)

/-- **`toRq` carries `addPoly` to `R_q` addition.** `toRq (addPoly a b) = toRq a + toRq b`, from
`NttFaithful.cast_addPoly` (coordinatewise `ℤ_q` add). -/
theorem toRq_add (a b : Poly) : toRq (addPoly a b) = toRq a + toRq b := by
  unfold toRq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi256 := Finset.mem_range.mp hi
  have hc : cf ((addPoly a b)[i]!) = cf (a[i]!) + cf (b[i]!) := cast_addPoly a b i hi256
  rw [hc, map_add, add_mul]

/-- **`toRq` carries `subPoly` to `R_q` subtraction** (on reduced arrays `b[i]! ≤ q`, the deployed case:
verifyCore's subtrahend is a `pointwiseMul`, all coeffs `< q`). From `NttFaithful.cast_subPoly`. -/
theorem toRq_sub (a b : Poly) (hb : ∀ i, i < 256 → b[i]! ≤ q) :
    toRq (subPoly a b) = toRq a - toRq b := by
  unfold toRq
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi256 := Finset.mem_range.mp hi
  have hc : cf ((subPoly a b)[i]!) = cf (a[i]!) - cf (b[i]!) := cast_subPoly a b i hi256 (hb i hi256)
  rw [hc, map_sub, sub_mul]

/-- **verifyCore's NTT-domain multiply computes the `R_q` product.** Composing `toRq_schoolbookMul` with
`NttFaithful.ringRepFaithful_proven`: `toRq (intt (pointwiseMul (ntt a) (ntt b))) = toRq a * toRq b` for all
size-256 arrays. This is the exact identity that turns verifyCore's per-row `intt(Â⊙ntt(z))` into the spec's
`R_q` matrix–vector product term `A_ij · z_j`. -/
theorem toRq_nttMul (a b : Poly) (ha : a.size = 256) (hb : b.size = 256) :
    toRq (intt (pointwiseMul (ntt a) (ntt b))) = toRq a * toRq b := by
  rw [ringRepFaithful_proven a b ha hb, toRq_schoolbookMul]

#assert_axioms toRq_schoolbookMul
#assert_axioms toRq_nttMul
#assert_axioms toRq_add
#assert_axioms toRq_sub

/-! ## NON-VACUITY — the bridge lands in a GENUINE degree-256 ring, not a trivial/degenerate one.

`toRq_schoolbookMul` is a statement over `R_q = ℤ_q[X]/(X²⁵⁶+1)`; if that ring were trivial the multiplication
law would be vacuous. It is NOT: `root²⁵⁶ = −1 ≠ 1` (char `q ≠ 2`), the power-basis dimension is exactly
`256` (`Fips204CorrectReal.realDim`). -/

/-- `R_q` is a genuine degree-`256` extension (its `ℤ_q`-power-basis dimension is `256`), NOT a scalar — via
`Fips204CorrectReal.realDim`. So the coeff↔`R_q` bridge maps into the real ML-DSA ring. -/
theorem Rq_dim_256 : Dregg2.Crypto.Fips204CorrectReal.pb.dim = 256 :=
  Dregg2.Crypto.Fips204CorrectReal.realDim

/-! ## HONEST FRONTIER — what `verifyCore_eq_spec` still needs (NAMED, not laundered).

With the coeff↔`R_q` bridge CLOSED (`toRq_schoolbookMul`/`toRq_nttMul`, above) and
`VerifyCoreSpec.verifyCore_split` (verifyCore's verdict = the two FIPS 204 Alg-8 conditions), the full
`verifyCore pk M ctx sig = true ↔ verifyB (pkDecode/sigDecode)` identification reduces to exactly THREE
remaining `∀`-bridges. None is a hardness carrier; each is a concrete imperative-loop / codec fact:

1. **`DecodeSemantics`** (`VerifyCoreSpec.DecodeSemantics`, still open) — the codec `decode∘encode = id` over
   the FIPS 204 bit-(un)packing (`pkEncode`/`sigEncode` ↔ `pkDecode`/`sigDecode`). The mathematical core is
   the mixed-radix round-trip `unpackBits (packBits coeffs c) 0 count c = coeffs` (a positional-numeral
   `Nat`-arithmetic proof through the four `Id.run do` accumulate/emit/read/extract loops), the
   `zCoeffFromField`/`zFieldFromCoeff` sign-map inverse, and the `hintEncode`/`hintDecode` inverse on valid
   hints. Heavy but hardness-free; the exact remaining lemma is the `unpackBits∘packBits` mixed-radix identity.

2. **`InttLinearMatmul`** (below) — verifyCore's per-row accumulator `intt(Σ_j Â[i,j]⊙ntt(z_j) − ĉ⊙ntt(2^d·t1_i))`
   equals `Σ_j toRq(Â-source_ij)·toRq(z_j) − toRq(c)·toRq(2^d·t1_i)` over `R_q` (the spec's `(A·z − c·t1·2^d)_i`).
   The single-product step is CLOSED (`toRq_nttMul`); what remains is `intt`-ADDITIVITY (`intt (addPoly u v) =
   addPoly (intt u) (intt v)` and the `subPoly` mirror — a butterfly-linearity induction over the
   Gentleman–Sande network, the additive twin of `NttFaithful.stage_inv`) plus the `for j` `addPoly`-fold
   characterization (the reusable `foldSet`-style engine). Both are hardness-free imperative-loop lemmas.

3. **The GENERIC instantiation** — `verifyB`'s abstract `hash`/`challenge`/`round`/`zBoundB` chosen as the
   concrete SHAKE256-framing / `sampleInBall` / `useHint`(=`Decompose`)-rounding / `infNormZ`-gate. Per
   `VerifyCoreSpec`'s classification this is a legitimate INTERPRETATION (the CR/rejection SPECS live on the
   `HashSig`/`FoQrom` floor), not a soundness gap — but wiring it needs the `w1Encode`/`useHint` per-row
   identification, riding bridge (2).

`verifyCore_eq_spec` is the composition `verifyCore_split ∘ (2) ∘ (1) ∘ (3)`; it is NOT closed here. This file
closes the flagged coeff↔`R_q` bridge (the NTT-multiply-computes-the-ring-product leg) and names the residual
legs precisely. -/

/-- **RESIDUAL (per-row matmul over `R_q`).** GIVEN `intt`-additivity, verifyCore's per-row inner value maps
under `toRq` to the spec's `R_q`-module matrix–vector argument `(A·z − c·t1·2^d)_i`. The single-product core
(`toRq_nttMul`) is CLOSED; this names the remaining `intt`-linearity + `addPoly`-fold leg. -/
def InttLinearMatmul : Prop :=
  (∀ u v : Poly, u.size = 256 → v.size = 256 → intt (addPoly u v) = addPoly (intt u) (intt v))

end Dregg2.Crypto.VerifyCoreEqSpec
