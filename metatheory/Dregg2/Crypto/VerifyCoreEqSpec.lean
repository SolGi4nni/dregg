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
  cast_addPoly cast_subPoly intt_add intt_sub intt_size intt_lt intt_interp addPoly_size addPoly_lt
  subPoly_size subPoly_lt pointwiseMul_size pointwiseMul_lt zeroPoly_lt zeroPoly_cast)
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

/-! ## LEG 1+2 — `intt`-linearity carried to `R_q`, and the per-row matmul-IS-the-`R_q`-matvec.

`NttFaithful.intt_add`/`intt_sub` (leg 1) prove `intt` is ℤ_q-additive on reduced size-256 inputs. Composed
with `toRq_add`/`toRq_sub` they carry to `R_q`; and folded over the `for j` accumulator + closed with
`toRq_nttMul` on each product they give leg 2 — verifyCore's per-row inner value IS the spec's `R_q`-module
matrix–vector argument `(A·z − c·s)_i`. -/

/-- `toRq` of an all-`ℤ_q`-zero-coefficient array is `0`. -/
theorem toRq_eq_zero_of_coeffs (a : Poly) (h : ∀ i : Nat, i < 256 → (a[i]! : ZMod q) = 0) :
    toRq a = 0 := by
  unfold toRq
  refine Finset.sum_eq_zero (fun i hi => ?_)
  rw [show cf (a[i]!) = (0 : ZMod q) from h i (mem_range.mp hi), map_zero, zero_mul]

/-- `intt` of the zero polynomial maps to `0` in `R_q` (the `intt_interp` sum vanishes coefficientwise). -/
theorem toRq_intt_zero : toRq (intt zeroPoly) = 0 := by
  refine toRq_eq_zero_of_coeffs _ (fun i hi => ?_)
  rw [intt_interp zeroPoly (by simp [zeroPoly]) zeroPoly_lt i hi,
      Finset.sum_eq_zero (fun u _ => by rw [zeroPoly_cast, zero_mul]), mul_zero]

/-- **`toRq` carries `intt`-additivity to `R_q`.** `toRq (intt (addPoly u v)) = toRq (intt u) + toRq (intt v)`
on reduced size-256 `u, v` — leg 1 composed with `toRq_add`. -/
theorem toRq_intt_add (u v : Poly) (hu : u.size = 256) (hv : v.size = 256)
    (hult : ∀ (p : Nat), u[p]! < q) (hvlt : ∀ (p : Nat), v[p]! < q) :
    toRq (intt (addPoly u v)) = toRq (intt u) + toRq (intt v) := by
  rw [intt_add u v hu hv hult hvlt, toRq_add]

/-- **`toRq` carries `intt`-subtractivity to `R_q`.** `toRq (intt (subPoly u v)) = toRq (intt u) −
toRq (intt v)` on reduced size-256 `u, v`. -/
theorem toRq_intt_sub (u v : Poly) (hu : u.size = 256) (hv : v.size = 256)
    (hult : ∀ (p : Nat), u[p]! < q) (hvlt : ∀ (p : Nat), v[p]! < q) :
    toRq (intt (subPoly u v)) = toRq (intt u) - toRq (intt v) := by
  rw [intt_sub u v hu hv hult hvlt, toRq_sub _ _ (fun i _ => le_of_lt (intt_lt v hv hvlt i))]

/-- The verifyCore per-row `for j` accumulator (fold of `addPoly az (Â_ij ⊙ ẑ_j)`) keeps size 256. -/
theorem addFold_size (terms : List (Poly × Poly)) :
    ∀ (acc : Poly), acc.size = 256 →
      (List.foldl (fun az t => addPoly az (pointwiseMul (ntt t.1) (ntt t.2))) acc terms).size = 256 := by
  induction terms with
  | nil => intro acc h; simpa using h
  | cons t ts ih => intro acc _; simp only [List.foldl_cons]; exact ih _ (addPoly_size _ _)

/-- The verifyCore per-row accumulator stays reduced (`< q`). -/
theorem addFold_lt (terms : List (Poly × Poly)) :
    ∀ (acc : Poly), (∀ (p : Nat), acc[p]! < q) →
      ∀ (p : Nat),
        (List.foldl (fun az t => addPoly az (pointwiseMul (ntt t.1) (ntt t.2))) acc terms)[p]! < q := by
  induction terms with
  | nil => intro acc h; simpa using h
  | cons t ts ih => intro acc _; simp only [List.foldl_cons]; exact ih _ (addPoly_lt _ _)

/-- **`intt` distributes over the `for j` `addPoly`-fold, in `R_q`.** Folding `addPoly az (Â_ij ⊙ ẑ_j)` and
applying `intt`, then `toRq`, equals `toRq (intt acc)` plus the `R_q`-sum `Σ_j toRq A_ij · toRq z_j` (each
NTT-domain product collapsed by `toRq_nttMul`). The reusable fold-linearity engine for leg 2. -/
theorem toRq_intt_addFold : ∀ (terms : List (Poly × Poly)),
    (∀ t ∈ terms, t.1.size = 256 ∧ t.2.size = 256) →
    ∀ (acc : Poly), acc.size = 256 → (∀ (p : Nat), acc[p]! < q) →
      toRq (intt (List.foldl (fun az t => addPoly az (pointwiseMul (ntt t.1) (ntt t.2))) acc terms))
        = toRq (intt acc) + (terms.map (fun t => toRq t.1 * toRq t.2)).sum := by
  intro terms
  induction terms with
  | nil => intro _ acc _ _; simp
  | cons t ts ih =>
    intro hterm acc hacc hacclt
    have ht := hterm t (by simp)
    have hpwsz : (pointwiseMul (ntt t.1) (ntt t.2)).size = 256 := pointwiseMul_size _ _
    have hpwlt : ∀ (p : Nat), (pointwiseMul (ntt t.1) (ntt t.2))[p]! < q := pointwiseMul_lt _ _
    have hacc'sz : (addPoly acc (pointwiseMul (ntt t.1) (ntt t.2))).size = 256 := addPoly_size _ _
    have hacc'lt : ∀ (p : Nat), (addPoly acc (pointwiseMul (ntt t.1) (ntt t.2)))[p]! < q :=
      addPoly_lt _ _
    have hstep : List.foldl (fun az t => addPoly az (pointwiseMul (ntt t.1) (ntt t.2))) acc (t :: ts)
        = List.foldl (fun az t => addPoly az (pointwiseMul (ntt t.1) (ntt t.2)))
            (addPoly acc (pointwiseMul (ntt t.1) (ntt t.2))) ts := by
      simp only [List.foldl_cons]
    rw [hstep, ih (fun t' ht' => hterm t' (List.mem_cons_of_mem _ ht'))
          (addPoly acc (pointwiseMul (ntt t.1) (ntt t.2))) hacc'sz hacc'lt,
        toRq_intt_add acc (pointwiseMul (ntt t.1) (ntt t.2)) hacc hpwsz hacclt hpwlt,
        toRq_nttMul t.1 t.2 ht.1 ht.2, List.map_cons, List.sum_cons]
    ring

/-- **LEG 2 — the per-row matmul IS the `R_q` matrix–vector argument.** verifyCore's per-row inner value
`w_i = intt(Σ_j Â_ij ⊙ ẑ_j − ĉ ⊙ ŝ_i)` maps under `toRq` to the FIPS 204 spec's `(A·z − c·s)_i` over
`R_q = ℤ_q[X]/(X²⁵⁶+1)`, where `Â_ij = ntt A_ij`, `ẑ_j = ntt z_j`, `ĉ = ntt c`, `ŝ_i = ntt s_i` (`s_i =
2^d·t1_i`). The `for j` accumulator distributes via `toRq_intt_addFold`, the subtracted `ĉ⊙ŝ_i` term via
`toRq_intt_sub`, and each NTT-domain product collapses to the `R_q` product via `toRq_nttMul`. This is the
mathematically-meaningful ALGEBRA path to the spec matmul: verifyCore's fast NTT matmul computes exactly the
`R_q`-module matrix–vector product the FIPS 204 acceptance predicate quantifies over, for all inputs. -/
theorem toRq_intt_matmul_row (terms : List (Poly × Poly)) (c s : Poly)
    (hterm : ∀ t ∈ terms, t.1.size = 256 ∧ t.2.size = 256) (hc : c.size = 256) (hs : s.size = 256) :
    toRq (intt (subPoly
        (List.foldl (fun az t => addPoly az (pointwiseMul (ntt t.1) (ntt t.2))) zeroPoly terms)
        (pointwiseMul (ntt c) (ntt s))))
      = (terms.map (fun t => toRq t.1 * toRq t.2)).sum - toRq c * toRq s := by
  have hazsz : (List.foldl (fun az t => addPoly az (pointwiseMul (ntt t.1) (ntt t.2))) zeroPoly terms).size
      = 256 := addFold_size terms zeroPoly (by simp [zeroPoly])
  have hazlt : ∀ (p : Nat),
      (List.foldl (fun az t => addPoly az (pointwiseMul (ntt t.1) (ntt t.2))) zeroPoly terms)[p]! < q :=
    addFold_lt terms zeroPoly zeroPoly_lt
  have hct1sz : (pointwiseMul (ntt c) (ntt s)).size = 256 := pointwiseMul_size _ _
  have hct1lt : ∀ (p : Nat), (pointwiseMul (ntt c) (ntt s))[p]! < q := pointwiseMul_lt _ _
  rw [toRq_intt_sub _ _ hazsz hct1sz hazlt hct1lt,
      toRq_intt_addFold terms hterm zeroPoly (by simp [zeroPoly]) zeroPoly_lt,
      toRq_intt_zero, zero_add, toRq_nttMul c s hc hs]

#assert_axioms intt_add
#assert_axioms toRq_intt_add
#assert_axioms toRq_intt_sub
#assert_axioms toRq_intt_addFold
#assert_axioms toRq_intt_matmul_row

/-! ## HONEST FRONTIER — what `verifyCore_eq_spec` still needs (NAMED, not laundered).

With the coeff↔`R_q` bridge CLOSED (`toRq_schoolbookMul`/`toRq_nttMul`) AND the `intt`-linearity matmul bridge
CLOSED (leg 1 `NttFaithful.intt_add`/`intt_sub`; leg 2 `toRq_intt_matmul_row` — verifyCore's per-row fast NTT
matmul IS the spec's `R_q` matrix–vector product `(A·z − c·s)_i`, for all inputs) plus
`VerifyCoreSpec.verifyCore_split` (verifyCore's verdict = the two FIPS 204 Alg-8 conditions), the full
`verifyCore pk M ctx sig = true ↔ verifyB (pkDecode/sigDecode)` identification reduces to exactly TWO remaining
`∀`-bridges. Neither is a hardness carrier:

1. **`DecodeSemantics`** (`VerifyCoreSpec.DecodeSemantics`, still open) — the codec `decode∘encode = id` over
   the FIPS 204 bit-(un)packing (`MlDsaCodec.pkEncode`/`sigEncode` ↔ `pkDecode`/`sigDecode`). The exact
   remaining mathematical core is the mixed-radix round-trip
   `MlDsaCodec.unpackBits (MlDsaCodec.packBits coeffs cbits) 0 256 cbits = coeffs`
   (a positional-numeral `Nat`-arithmetic proof through the `Id.run do` accumulate/emit and read/extract
   loops of `packBits`/`unpackBits` — reachable with the same `foldSet`/`Array.set!` engine used for the NTT
   loops), together with the `MlDsaCodec.zCoeffFromField`/`zFieldFromCoeff` sign-map inverse and the
   `hintEncode`/`hintDecode` inverse on valid hints. Heavy codec grind, hardness-free; NOT closed here.

2. **The GENERIC instantiation** — `verifyB`'s abstract `hash`/`challenge`/`round`/`zBoundB` chosen as the
   concrete SHAKE256-framing / `sampleInBall` / `useHint`(=`Decompose`)-rounding / `infNormZ`-gate. Per
   `VerifyCoreSpec`'s classification this is a legitimate INTERPRETATION (the CR/rejection SPECS live on the
   `HashSig`/`FoQrom` floor), not a soundness gap — but wiring it needs the `w1Encode`/`useHint` per-row
   identification, riding the now-closed matmul bridge (leg 2).

`verifyCore_eq_spec` is the composition `verifyCore_split ∘ leg2 ∘ DecodeSemantics ∘ instantiation`; the
ALGEBRA legs (1+2) are CLOSED here, leaving `DecodeSemantics` (the codec round-trip, exact lemma named above)
and the hash/challenge instantiation as the remaining wiring. -/

end Dregg2.Crypto.VerifyCoreEqSpec
