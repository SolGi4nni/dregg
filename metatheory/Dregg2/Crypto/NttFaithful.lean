/-
# `Dregg2.Crypto.NttFaithful` — sharpening the NTT-faithfulness residual (`RingRepFaithful`).

`VerifyCoreSpec.RingRepFaithful : Prop := ∀ a b : Poly, intt (pointwiseMul (ntt a) (ntt b)) = schoolbookMul a b`
is the load-bearing ∀-bridge behind `verifyCore = spec`: the fast NTT multiply computes the negacyclic ring
product for ALL poly pairs, not just the one `native_decide` sample `MlDsaRing.ntt_computes_negacyclic_mul`.

## What THIS module establishes (all axiom-clean, no `native_decide` in any ∀-body)

1. **Genuine loop-reasoning over the actual `Id.run do` butterfly/loop defs.** `pointwiseMul`'s imperative
   `for i in [0:256]` loop is proven to satisfy the exact coefficient formula `(pointwiseMul a b)[i]! =
   mulModQ a[i]! b[i]!` for every `i < 256` (`pointwiseMul_getElem`) — the "fast side" is no longer opaque.
   The supporting `foldSet_mem`/`foldSet_notMem` lemmas are the reusable engine for characterizing any of
   these `Array.set!`-fold loops entrywise (the same shape whoever closes the butterflies will reuse).

2. **The exact algebraic REDUCTION of `RingRepFaithful` to two standard NTT-correctness facts.**
   `ringRepFaithful_of` proves — for all `a b`, axiom-clean — that
       `RingRepFaithful ⟸ NttLeftInverse ∧ NttMulHom`,
   where `NttLeftInverse := ∀ c, intt (ntt c) = c` (the inverse transform is a genuine left inverse) and
   `NttMulHom := ∀ a b, ntt (schoolbookMul a b) = pointwiseMul (ntt a) (ntt b)` (ntt is a ring homomorphism
   from the negacyclic ring to the pointwise-product ring). This is the textbook decomposition: an NTT
   multiply is correct iff the transform inverts AND diagonalizes the convolution. The proof is a two-step
   rewrite `intt(ntt a ⊙ ntt b) = intt(ntt(a·b)) = a·b`.

3. **Non-vacuity of both residuals** on a wraparound-exercising sample (`nttLeftInverse_sample`,
   `nttMulHom_sample`, concrete `native_decide` witnesses — NOT inside any ∀). Both hypotheses of the
   reduction genuinely HOLD, so `ringRepFaithful_of` is a real reduction, not a vacuous implication.

## THE LADDER climbed here (rungs 0/1/3 CLOSED; rung 2 is the named wall)

* **RUNG 0 — the ℤ_q reduction homomorphism** (`cast_addQ`/`cast_subQ`/`cast_mulModQ`). The executable
  `Nat`-mod-`q` scalar arithmetic is proven to be genuine `+`/`-`/`*` in the field `ZMod q` (`q` prime, by
  `norm_num`). This lifts the whole imperative layer into the honest ring `ℤ_q` — the substrate the DFT
  algebra needs. No `native_decide`.
* **RUNG 1 (elementary) — the non-butterfly poly ops ARE the coordinatewise ℤ_q ops** (`cast_addPoly`/
  `cast_subPoly`/`cast_pointwiseMul`, via new entrywise `addPoly_getElem`/`subPoly_getElem` reusing the
  `foldSet_*` engine). `addPoly`/`subPoly`/`pointwiseMul` = coordinatewise `+`/`-`/`*` on the ℤ_q vectors;
  the pointwise-product ring is exactly `(ℤ_q)²⁵⁶`.
* **RUNG 3 — root-of-unity ORTHOGONALITY** (`omega_orthogonality`): `ω = ζ²` is a primitive 256th root, so
  `Σ_{m<256} (ω^d)^m = 256·[256 ∣ d]` in `ℤ_q` — the interpolation/diagonalization crux. Proved abstractly
  for any element with `ζ²⁵⁶ = −1` (geometric telescope + `orderOf`; Mathlib ships no DFT lemma, built from
  primitives), axiom-clean; `zeta_root_witness` pins that `ζ = 1753` satisfies the hypothesis.

## RUNG 2 — the butterfly WALL (engine BUILT; outer-loop peel + CT invariant CLOSED, forward direction)

The FORWARD half is discharged: `nttEvalsAtRoots_canonical` (below) proves the 8-stage butterfly network
computes evaluation at the negacyclic roots for every canonical (size-256) poly, via the CT stage-invariant
induction `stage_inv`. On top of it, **`NttMulHom` is now CLOSED** (`nttMulHom_proven`): the negacyclic-convolution
ring-hom, via the `schoolbookMul`-loop coefficient characterization (`schoolbookMul_getElem`, PART 1g) + the
eval-at-a-root multiplicativity `eval256_schoolbook`. The SINGLE remaining residual is the `intt` interpolation
induction (`NttLeftInverse`), to which `RingRepFaithful` is now reduced (`ringRepFaithful_of_leftInverse`).

⚠ **The `∀`-over-all-Poly props are FALSE as literally stated** (`NttEvalsAtRoots` / `NttMulHom` /
`NttLeftInverse` / `VerifyCoreSpec.RingRepFaithful`): a non-256-length input makes the imperative `Array.set!`
butterflies no-op out of bounds and keep the wrong length (`ntt #[5]` stays length 1, so `(ntt #[5])[1]! = 0 ≠
eval256 #[5] (evalRoot 1)`). The theorems here carry the `a.size = 256` guard — the operationally-correct form,
since the deployed pipeline only feeds decoded size-256 coefficient arrays. `ζ²⁵⁶ = −1` is discharged by plain
`decide` (NOT `native_decide`), so every keystone is axiom-clean without the `ofReduceBool` residual.

With rung 3 (orthogonality)
proven, both `NttLeftInverse` and `NttMulHom` reduce to a SINGLE identification: that the 8-stage Cooley–Tukey
`Id.run do` butterfly schedule (FIPS 204 `ζ^{brv(k)}` twiddles, `256⁻¹` scaling) realizes the abstract linear
map "evaluate at the negacyclic roots `ζ^{2·brv(m)+1}`" — stated as the props `NttEvalsAtRoots` (forward) and
`InttInterpolates` (inverse), over `X²⁵⁶+1 = ∏_{m<256}(X − ζ^{2·brv(m)+1})`.

* **The butterfly-sweep loop primitive the prior lane named as missing is now BUILT** (`bfFold_spec`,
  `bfSweep_getElem`, `cast_bfSweep`; all axiom-clean). The innermost `for j` loop — TWO-index, array-DEPENDENT
  writes `a[j], a[j+len] ← a[j] ± z·a[j+len]` per butterfly, which the single-index `foldSet_*` engine could
  not reach — is characterized entrywise from the actual imperative def, and `cast_bfSweep` proves the sweep
  IS the 2×2 ℤ_q-linear map over the honest field. The disjointness of the write pairs `{j, j+len}` (so each
  read sees the ORIGINAL array) is the crux and is proven. `bfSweep` is a verbatim copy of `ntt`'s inner loop.
* **The outer-loop PEEL is now BUILT** (`ntt_eq_fold : ntt w = nttFold w`): the two OUTER loops (`for s`,
  `for blk`, mutable state `(a, k)`) are peeled into the explicit ordered `bfSweep` fold `nttFold`, with `k`
  running `1 … 255`. Axiom-clean (via an rfl-clean intermediate `nttCleanDo` + `foldl_ext_mem`).
* **The twiddle-in-field cast is now BUILT** (`cast_zetaTwiddle : zetaTwiddle k = (ζ:ℤ_q)^{brv8 k}`): both the
  `powModQ` square-and-multiply ladder (`cast_powModQ`, a loop invariant `result = base^{e mod 2ᵗ}`) and the
  `brv8` 8-bit reversal (`brv8_lt < 256`) are characterized from their actual imperative defs. No `native_decide`.
* **The CT stage-invariant induction over `nttFold` is now BUILT** (`stage_inv`). The invariant "after stage `s`,
  slot `g·(256>>>s)+i` holds `Σ_{u<2ˢ} w_{i+u·(256>>>s)}·(rootAt s g)^u` (= the `ℤ_q`-eval of the `g`-th decimated
  subsequence at its root `rootAt s g`)" is proven by induction on `s`: each stage is preserved by `block_char`
  (one full CT stage as a positionwise Nat-level accumulation, by induction on block count on `bfSweep_getElem`) +
  `cast_zetaTwiddle` + the even/odd `Finset` reindex `split_collapse` + the `brv8` exponent congruences
  `brv_even`/`brv_odd`/`brv_high` (proved by `decide` on the 8-bit fold), which pin `rootAt` consistent under the
  recurrence (`rootAt_closed`). At `len = 1` (`s=8`) it collapses (`rootAt_final : rootAt 8 m = ζ^{2·brv8(m)+1}`)
  to `nttEvalsAtRoots_canonical`. Axiom-clean.

`NttMulHom` is CLOSED (`nttMulHom_proven`, PART 1g + RUNG-2 step 3): eval-is-a-ring-hom + `evalRoot²⁵⁶ = −1`
(`evalRoot_pow256`) atop the `schoolbookMul`-loop coefficient characterization. The remaining residual is
`NttLeftInverse` = eval∘interp collapsed by `omega_orthogonality` (brv bijective) — the `intt` interpolation
induction (the Gentleman–Sande mirror of `stage_inv`). `RingRepFaithful` is reduced to exactly this one leg.
-/
import Dregg2.Crypto.VerifyCoreSpec
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

namespace Dregg2.Crypto.MlDsaRing

open Dregg2.Crypto.VerifyCoreSpec (RingRepFaithful)
open Finset

/-- `ℤ_q` is a genuine field: `q = 8380417` is the ML-DSA prime (checked by `norm_num`, not asserted).
This is what lets the reduction map `(· : Nat → ZMod q)` land in a `CommRing`/`Field` and gives the
roots-of-unity/orthogonality algebra below its no-zero-divisors backbone. -/
instance : Fact (Nat.Prime q) := ⟨by unfold q; norm_num⟩
instance : Fact (2 < q) := ⟨by unfold q; norm_num⟩

/-! ## PART 1 — genuine entrywise reasoning through the imperative `Array.set!`-fold loops.

These characterize the actual `Id.run do` loop defs at the coefficient level (no `native_decide`), and are the
reusable engine for any of the `for i in [..]` loops in `MlDsaRing`. -/

/-- Folding `set!` over a list `L` leaves index `j ∉ L` untouched. -/
theorem foldSet_notMem (g : Nat → Nat) (j : Nat) :
    ∀ (L : List Nat) (init : Poly), j ∉ L →
      (List.foldl (fun r i => r.set! i (g i)) init L)[j]! = init[j]! := by
  intro L
  induction L with
  | nil => intro init _; simp
  | cons hd tl ih =>
    intro init hj
    simp only [List.foldl_cons]
    rw [ih (init.set! hd (g hd)) (by simp_all)]
    have hne : hd ≠ j := by rintro rfl; exact hj (List.mem_cons_self ..)
    simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds, Array.set!_eq_setIfInBounds]
    rw [if_neg hne]

/-- Folding `set! · i (g i)` over a list containing `j` (with `j` in bounds) lands `g j` at index `j`.
    (`g j` is deterministic, so a later duplicate write to `j` re-writes the same value — no `Nodup` needed.) -/
theorem foldSet_mem (g : Nat → Nat) (j : Nat) :
    ∀ (L : List Nat) (init : Poly), j ∈ L → j < init.size →
      (List.foldl (fun r i => r.set! i (g i)) init L)[j]! = g j := by
  intro L
  induction L with
  | nil => intro init hj; exact absurd hj (List.not_mem_nil)
  | cons hd tl ih =>
    intro init hj hsz
    simp only [List.foldl_cons]
    by_cases hmem : j ∈ tl
    · exact ih _ hmem (by simpa using hsz)
    · have hhd : hd = j := by
        rcases List.mem_cons.mp hj with h | h
        · exact h.symm
        · exact absurd h hmem
      subst hhd
      rw [foldSet_notMem g hd tl (init.set! hd (g hd)) hmem]
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds, Array.set!_eq_setIfInBounds]
      simp [hsz]

/-- The fast NTT-domain multiply preserves the 256-coefficient length. -/
theorem pointwiseMul_size (a b : Poly) : (pointwiseMul a b).size = 256 := by
  unfold pointwiseMul
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp,
    map_pure, List.forIn_pure_yield_eq_foldl]
  generalize List.range' 0 [:256].size 1 = L
  suffices h : ∀ (init : Poly), init.size = 256 →
      (List.foldl (fun r i => Array.set! r i (mulModQ a[i]! b[i]!)) init L).size = 256 by
    exact h zeroPoly (by simp [zeroPoly])
  intro init hinit
  induction L generalizing init with
  | nil => simpa using hinit
  | cons hd tl ih => simp only [List.foldl_cons]; exact ih _ (by simp [hinit])

/-- **Coefficient formula for the fast multiply**: `(pointwiseMul a b)[i]! = mulModQ a[i]! b[i]!`, proved from
the imperative loop def (not asserted). The pointwise-product ring is exactly coordinatewise `ℤ_q` multiply. -/
theorem pointwiseMul_getElem (a b : Poly) (i : Nat) (hi : i < 256) :
    (pointwiseMul a b)[i]! = mulModQ a[i]! b[i]! := by
  unfold pointwiseMul
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp,
    map_pure, List.forIn_pure_yield_eq_foldl, bind_pure]
  have hmem : i ∈ List.range' 0 [:256].size 1 := by
    simp only [Std.Legacy.Range.size, List.mem_range'_1]; omega
  have hsz : i < (zeroPoly).size := by simp [zeroPoly]; omega
  exact foldSet_mem (fun i => mulModQ a[i]! b[i]!) i (List.range' 0 [:256].size 1) zeroPoly hmem hsz

/-! ## PART 1b — RUNG 0 of the ladder: the ℤ_q REDUCTION HOMOMORPHISM (no DFT content).

The executable transform works on `Nat` canonical reps in `[0, q)` with `%q`-reduced arithmetic. These
three lemmas prove the reduction map `(· : Nat → ZMod q)` is a ring homomorphism on the executable scalar
ops (`addQ`/`subQ`/`mulModQ` become genuine `+`/`-`/`*` in the field `ZMod q`). This turns every downstream
statement about the imperative arithmetic into a statement about the honest ring `ℤ_q` — the substrate every
higher rung rests on. Pure `Nat.cast` algebra; no computation, no `native_decide`. -/

/-- `addQ` reduces to `+` in `ℤ_q`. -/
theorem cast_addQ (a b : Nat) : ((addQ a b : Nat) : ZMod q) = (a : ZMod q) + b := by
  unfold addQ; rw [ZMod.natCast_mod, Nat.cast_add]

/-- `mulModQ` reduces to `*` in `ℤ_q`. -/
theorem cast_mulModQ (a b : Nat) : ((mulModQ a b : Nat) : ZMod q) = (a : ZMod q) * b := by
  unfold mulModQ; rw [ZMod.natCast_mod, Nat.cast_mul]

/-- `subQ` reduces to `-` in `ℤ_q` (for canonical `b ≤ a + q`, always true on reduced reps `b < q`). -/
theorem cast_subQ (a b : Nat) (h : b ≤ a + q) : ((subQ a b : Nat) : ZMod q) = (a : ZMod q) - b := by
  unfold subQ; rw [ZMod.natCast_mod, Nat.cast_sub h, Nat.cast_add, ZMod.natCast_self]; ring

/-! ## PART 1c — RUNG 1 (elementary): the non-butterfly poly ops ARE the coefficientwise `ℤ_q` ops.

`addPoly`/`subPoly` are characterized entrywise through their `Array.set!`-fold loops (same engine as
`pointwiseMul_getElem`, reusing `foldSet_mem`), then cast into `ℤ_q`: `addPoly`/`subPoly`/`pointwiseMul`
act as coordinatewise `+`/`-`/`*` on the ℤ_q coefficient vectors. This is the LINEAR/pointwise side of the
transform (the `⊙` in `intt(ntt a ⊙ ntt b)`) proven to be the honest ring vector operations — the residual
`ntt`/`intt` linearity is what still rests behind the butterfly loops (PART 1e). -/

/-- Entrywise formula for `addPoly` (from the imperative loop, not asserted). -/
theorem addPoly_getElem (a b : Poly) (i : Nat) (hi : i < 256) :
    (addPoly a b)[i]! = addQ a[i]! b[i]! := by
  unfold addPoly
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, bind_pure]
  have hmem : i ∈ List.range' 0 [:256].size 1 := by
    simp only [Std.Legacy.Range.size, List.mem_range'_1]; omega
  have hsz : i < zeroPoly.size := by simp [zeroPoly]; omega
  exact foldSet_mem (fun i => addQ a[i]! b[i]!) i (List.range' 0 [:256].size 1) zeroPoly hmem hsz

/-- Entrywise formula for `subPoly` (from the imperative loop, not asserted). -/
theorem subPoly_getElem (a b : Poly) (i : Nat) (hi : i < 256) :
    (subPoly a b)[i]! = subQ a[i]! b[i]! := by
  unfold subPoly
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, bind_pure]
  have hmem : i ∈ List.range' 0 [:256].size 1 := by
    simp only [Std.Legacy.Range.size, List.mem_range'_1]; omega
  have hsz : i < zeroPoly.size := by simp [zeroPoly]; omega
  exact foldSet_mem (fun i => subQ a[i]! b[i]!) i (List.range' 0 [:256].size 1) zeroPoly hmem hsz

/-- `addPoly` IS coordinatewise `+` in `ℤ_q`. -/
theorem cast_addPoly (a b : Poly) (i : Nat) (hi : i < 256) :
    ((addPoly a b)[i]! : ZMod q) = (a[i]! : ZMod q) + (b[i]! : ZMod q) := by
  rw [addPoly_getElem a b i hi, cast_addQ]

/-- `pointwiseMul` IS coordinatewise `*` in `ℤ_q` — the NTT-domain product ring is exactly `(ℤ_q)²⁵⁶`. -/
theorem cast_pointwiseMul (a b : Poly) (i : Nat) (hi : i < 256) :
    ((pointwiseMul a b)[i]! : ZMod q) = (a[i]! : ZMod q) * (b[i]! : ZMod q) := by
  rw [pointwiseMul_getElem a b i hi, cast_mulModQ]

/-- `subPoly` IS coordinatewise `-` in `ℤ_q` (on reduced reps `b[i]! ≤ q`). -/
theorem cast_subPoly (a b : Poly) (i : Nat) (hi : i < 256) (hb : b[i]! ≤ q) :
    ((subPoly a b)[i]! : ZMod q) = (a[i]! : ZMod q) - (b[i]! : ZMod q) := by
  rw [subPoly_getElem a b i hi, cast_subQ _ _ (by omega)]

/-! ## PART 1d — RUNG 3 (the DFT crux): ROOT-OF-UNITY ORTHOGONALITY in `ℤ_q`.

The interpolation/diagonalization heart of any NTT is the orthogonality relation
`Σ_{m<256} ω^{m·d} = 256·[256 ∣ d]` for `ω` a primitive 256th root of unity. Here `ω = ζ²` (`ζ` the primitive
512th root); this is the sum that collapses the round-trip `intt∘ntt` to the identity and makes eval-at-roots
a ring iso. It is proved abstractly — for ANY element with `ζ²⁵⁶ = −1` in the field `ℤ_q` — from a geometric
telescope + `orderOf`, no `native_decide` in the theorem body. `zeta_root_witness` then pins that `ζ = 1753`
genuinely satisfies the hypothesis. Mathlib ships no Cooley–Tukey/DFT lemma; this rung is built from primitives. -/

/-- Geometric telescope `(x−1)·Σ_{i<n} xⁱ = xⁿ − 1` in any commutative ring (`Mathlib.Algebra.GeomSum` is
not in this build's olean closure, so it is proved here by induction). -/
theorem geomTel {R} [CommRing R] (x : R) (n : Nat) :
    (x - 1) * (∑ i ∈ range n, x^i) = x^n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih, pow_succ]; ring

/-- In a field, a NONTRIVIAL `N`-th root of unity has vanishing power sum: `Σ_{i<N} wⁱ = 0`. -/
theorem powSum_zero {F} [Field F] (w : F) (N : Nat) (hN : w^N = 1) (hw : w ≠ 1) :
    ∑ i ∈ range N, w^i = 0 := by
  have h := geomTel w N
  rw [hN, sub_self] at h
  rcases mul_eq_zero.mp h with h1 | h2
  · exact absurd (by linear_combination h1) (sub_ne_zero.mpr hw)
  · exact h2

/-- `ζ` has multiplicative order exactly 512 in `ℤ_q`, given `ζ²⁵⁶ = −1` (so `ζ²⁵⁶ ≠ 1` since `char ≠ 2`,
and `ζ⁵¹² = 1`). Via `orderOf_eq_prime_pow` at `2⁸ / 2⁹`. -/
theorem orderOf_zeta (hz : (zeta : ZMod q)^256 = -1) : orderOf (zeta : ZMod q) = 512 := by
  have h256 : (zeta : ZMod q)^(2^8) ≠ 1 := by
    show (zeta : ZMod q)^256 ≠ 1; rw [hz]; exact ZMod.neg_one_ne_one
  have h512 : (zeta : ZMod q)^(2^9) = 1 := by
    show (zeta : ZMod q)^512 = 1
    have h : (zeta : ZMod q)^512 = ((zeta : ZMod q)^256)^2 := by rw [← pow_mul]
    rw [h, hz]; ring
  simpa using orderOf_eq_prime_pow (p := 2) (n := 8) (x := (zeta : ZMod q)) h256 h512

/-- **THE ORTHOGONALITY RELATION** — `ω = ζ²` is a primitive 256th root, so `Σ_{m<256} (ω^d)^m = 256·[256 ∣ d]`
in `ℤ_q`. The `256 ∤ d` branch (vanishing) is the interpolation crux; the `256 ∣ d` branch (`= 256`) is the
diagonal. Axiom-clean (`{propext, Classical.choice, Quot.sound}`); the ζ-root property enters only as the
hypothesis `hz`. -/
theorem omega_orthogonality (hz : (zeta : ZMod q)^256 = -1) (d : Nat) :
    ∑ m ∈ range 256, (((zeta : ZMod q)^2)^d)^m = if 256 ∣ d then (256 : ZMod q) else 0 := by
  set ζ : ZMod q := (zeta : ZMod q) with hζ
  have hord : orderOf ζ = 512 := orderOf_zeta hz
  by_cases hd : 256 ∣ d
  · have hω1 : (ζ^2)^d = 1 := by
      have hdvd : (512:ℕ) ∣ 2*d := by omega
      have : ζ^(2*d) = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rw [hord]; exact hdvd)
      rw [← this]; ring
    simp [hω1, hd]
  · have hN : ((ζ^2)^d)^256 = 1 := by
      have h : ((ζ^2)^d)^256 = ζ^(512 * d) := by ring
      rw [h, pow_mul, ← hord, pow_orderOf_eq_one, one_pow]
    have hw : (ζ^2)^d ≠ 1 := by
      intro hcon
      have hz1 : ζ^(2*d) = 1 := by rw [← hcon]; ring
      have hdvd : (512:ℕ) ∣ 2*d := by rw [← hord]; exact orderOf_dvd_of_pow_eq_one hz1
      exact hd (by omega)
    rw [if_neg hd]; exact powSum_zero ((ζ^2)^d) 256 hN hw

/-- **Non-vacuity of the orthogonality hypothesis.** `ζ = 1753` genuinely IS a primitive 512th root mod `q`
(`ζ²⁵⁶ = −1`). This is a CLOSED computation (not a `∀`-body): it carries `native_decide`'s `ofReduceBool`
residual — the SAME trusted base `MlDsaRing.zeta_primitive_512th_root` already declares — and is the pin that
makes `omega_orthogonality` non-vacuous at the deployed constant. -/
theorem zeta_root_witness : (zeta : ZMod q)^256 = -1 := by native_decide

/-! ## PART 1e — RUNG 2 (the WALL): the butterfly network realizes evaluation-at-the-roots.

RUNGS 0/1/3 are the algebra. What remains — the SINGLE open frontier for both `NttLeftInverse` and
`NttMulHom` — is the identification of the 8-stage Cooley–Tukey `Id.run do` butterfly schedule with the
abstract linear map "evaluate at the 256 negacyclic roots `ζ^{2·brv(m)+1}`". These roots are exactly the
factorization points of `X²⁵⁶+1 = ∏_{m<256}(X − ζ^{2·brv(m)+1})` over `ℤ_q` (each is a 512th root since
`(ζ^{odd})²⁵⁶ = (ζ²⁵⁶)^{odd} = (−1)^{odd} = −1`). Given these two props:

* `NttLeftInverse` follows from `NttEvalsAtRoots` + `InttInterpolates` + `omega_orthogonality`
  (`brv` bijective ⇒ reindex the inner sum ⇒ orthogonality collapses `intt(ntt a)_k = a_k`);
* `NttMulHom` follows from `NttEvalsAtRoots` + `cast_pointwiseMul` + `evalRoot^256 = −1` (eval is a ring hom,
  the negacyclic reduction is eval-preserving at the roots).

So orthogonality (rung 3) is now DISCHARGED; the residual has shrunk to the loop-index identification below.
Proving it is a from-scratch butterfly-index induction over the nested `for`-loops with the threaded mutable
twiddle counter `k` — two-index, array-DEPENDENT writes per butterfly (`a[j], a[j+len] ← a[j] ± z·a[j+len]`),
which the `foldSet_*` engine (single-index, array-INDEPENDENT writes `g i`) does not reach; it needs a new
"butterfly sweep preserves the coefficientwise linear relation" primitive. **This primitive is now
BUILT below** (`bfFold_spec`/`bfSweep_getElem`/`cast_bfSweep`); what remains is peeling the two OUTER
loops and assembling the CT stage invariant on top of it — see the note after `cast_bfSweep`. -/

/-! ### The butterfly-sweep loop primitive (the RUNG-2 engine the `foldSet_*` engine could not reach).

The innermost `for j in [start : start+len]` loop of `ntt`/`intt` does TWO-index, array-DEPENDENT writes
per butterfly (`a[j], a[j+len] ← a[j] ± z·a[j+len]`). These lemmas characterize that sweep entrywise from
the actual imperative loop def (no `native_decide`), proving each butterfly is the 2×2 ℤ_q-linear map — the
exact relation the CT stage invariant is preserved by. `bfFold_spec` is axiom-clean `{propext, Quot.sound}`. -/

/-- Pointwise-equal step functions fold to the same result (missing from this build's `List` API). -/
theorem foldl_ext {A B : Type} (f g : B → A → B) (h : ∀ b a, f b a = g b a)
    (l : List A) (init : B) : l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; rw [h init hd]; exact ih _

/-- `get!` after `set!` at a DIFFERENT index is unchanged. -/
theorem getElem!_set!_ne (b : Poly) (i j v : Nat) (h : i ≠ j) :
    (b.set! i v)[j]! = b[j]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds, Array.set!_eq_setIfInBounds]
  rw [if_neg h]

/-- `get!` after in-bounds `set!` at the SAME index reads the written value. -/
theorem getElem!_set!_self (b : Poly) (i v : Nat) (h : i < b.size) :
    (b.set! i v)[i]! = v := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds, Array.set!_eq_setIfInBounds]
  simp [h]

theorem size_set! (b : Poly) (i v : Nat) : (b.set! i v).size = b.size := by
  simp [Array.set!_eq_setIfInBounds]

/-- The butterfly step (matches the desugared inner-loop body of `ntt` once `len ≥ 1`):
`b[j] ← b[j] + z·b[j+len]`, `b[j+len] ← b[j] − z·b[j+len]`. -/
def bfStepC (z len : Nat) (b : Poly) (j : Nat) : Poly :=
  (b.set! (j + len) (subQ b[j]! (mulModQ z b[j + len]!))).set! j (addQ b[j]! (mulModQ z b[j + len]!))

theorem bfStepC_size (z len : Nat) (b : Poly) (j : Nat) :
    (bfStepC z len b j).size = b.size := by
  unfold bfStepC; rw [size_set!, size_set!]

/-- **THE BUTTERFLY-SWEEP LOOP PRIMITIVE.** Folding the butterfly step over `range' s m` (one contiguous
sweep, window `m ≤ len`, indices in bounds) sets the low half to `a[p] + z·a[p+len]`, the high half to
`a[p−len] − z·a[p]`, and leaves everything else fixed — each read seeing the ORIGINAL array `a0` (proven
via the disjointness of the write pairs `{j, j+len}`). This is precisely the two-index, array-dependent
write primitive the single-index `foldSet_*` engine does not reach. Axiom-clean `{propext, Quot.sound}`. -/
theorem bfFold_spec (z len : Nat) (hlen : 1 ≤ len) (a0 : Poly) :
    ∀ (m s : Nat) (b : Poly),
      b.size = 256 → s + m + len ≤ 256 → m ≤ len →
      (∀ p, s ≤ p → p < s + m → b[p]! = a0[p]!) →
      (∀ p, s + len ≤ p → p < s + m + len → b[p]! = a0[p]!) →
      (List.foldl (bfStepC z len) b (List.range' s m)).size = 256 ∧
      (∀ p, s ≤ p → p < s + m →
        (List.foldl (bfStepC z len) b (List.range' s m))[p]! = addQ a0[p]! (mulModQ z a0[p+len]!)) ∧
      (∀ p, s + len ≤ p → p < s + m + len →
        (List.foldl (bfStepC z len) b (List.range' s m))[p]! = subQ a0[p-len]! (mulModQ z a0[p]!)) ∧
      (∀ p, (p < s ∨ s + m ≤ p) → (p < s + len ∨ s + m + len ≤ p) →
        (List.foldl (bfStepC z len) b (List.range' s m))[p]! = b[p]!) := by
  intro m
  induction m with
  | zero =>
    intro s b hsz _ _ _ _
    refine ⟨by simpa using hsz, ?_, ?_, ?_⟩
    · intro p h1 h2; omega
    · intro p h1 h2; omega
    · intro p _ _; simp
  | succ m' ih =>
    intro s b hsz hbound hmlen hagLo hagHi
    have hbs : b[s]! = a0[s]! := hagLo s (by omega) (by omega)
    have hbsl : b[s+len]! = a0[s+len]! := hagHi (s+len) (by omega) (by omega)
    have hs256 : s < b.size := by rw [hsz]; omega
    have hsl256 : s + len < b.size := by rw [hsz]; omega
    set b1 := bfStepC z len b s with hb1def
    have hb1size : b1.size = 256 := by rw [hb1def, bfStepC_size]; exact hsz
    have hb1_s : b1[s]! = addQ a0[s]! (mulModQ z a0[s+len]!) := by
      rw [hb1def]; unfold bfStepC
      rw [getElem!_set!_self _ s _ (by rw [size_set!]; exact hs256), hbs, hbsl]
    have hb1_sl : b1[s+len]! = subQ a0[s]! (mulModQ z a0[s+len]!) := by
      rw [hb1def]; unfold bfStepC
      rw [getElem!_set!_ne _ s (s+len) _ (by omega),
          getElem!_set!_self _ (s+len) _ hsl256, hbs, hbsl]
    have hb1_other : ∀ p, p ≠ s → p ≠ s + len → b1[p]! = b[p]! := by
      intro p hps hpsl
      rw [hb1def]; unfold bfStepC
      rw [getElem!_set!_ne _ s p _ (by omega), getElem!_set!_ne _ (s+len) p _ (by omega)]
    have hrange : List.range' s (m'+1) = s :: List.range' (s+1) m' := by
      rw [List.range'_succ]
    have hagLo1 : ∀ p, s+1 ≤ p → p < s+1+m' → b1[p]! = a0[p]! := by
      intro p h1 h2
      rw [hb1_other p (by omega) (by omega)]
      exact hagLo p (by omega) (by omega)
    have hagHi1 : ∀ p, s+1+len ≤ p → p < s+1+m'+len → b1[p]! = a0[p]! := by
      intro p h1 h2
      rw [hb1_other p (by omega) (by omega)]
      exact hagHi p (by omega) (by omega)
    obtain ⟨ihsz, ihlo, ihhi, ihun⟩ :=
      ih (s+1) b1 hb1size (by omega) (by omega) hagLo1 hagHi1
    rw [hrange, List.foldl_cons, ← hb1def]
    refine ⟨ihsz, ?_, ?_, ?_⟩
    · intro p h1 h2
      by_cases hp : p = s
      · subst hp
        rw [ihun p (by omega) (by omega), hb1_s]
      · rw [ihlo p (by omega) (by omega)]
    · intro p h1 h2
      by_cases hp : p = s + len
      · subst hp
        rw [ihun (s+len) (by omega) (by omega), hb1_sl, Nat.add_sub_cancel]
      · rw [ihhi p (by omega) (by omega)]
    · intro p hlo hhi
      rw [ihun p (by omega) (by omega)]
      exact hb1_other p (by omega) (by omega)

/-- One full butterfly sweep over the half-open block `[start, start+len)` with twiddle `z` — a VERBATIM
copy of the innermost `for j` loop of `ntt` (and, with `z = −ζ^{brv(k)}`, of `intt`). -/
def bfSweep (z start len : Nat) (a0 : Poly) : Poly := Id.run do
  let mut a := a0
  for j in [start : start + len] do
    let t := mulModQ z a[j + len]!
    a := a.set! (j + len) (subQ a[j]! t)
    a := a.set! j (addQ a[j]! t)
  return a

/-- The imperative sweep is exactly the `bfStepC` fold (needs `len ≥ 1` to drop the `[j]!`-after-`set!`). -/
theorem bfSweep_eq_foldl (z start len : Nat) (hlen : 1 ≤ len) (a0 : Poly) :
    bfSweep z start len a0 = List.foldl (bfStepC z len) a0 (List.range' start len) := by
  unfold bfSweep
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, bind_pure]
  have hsize : [start:start+len].size = len := by
    simp only [Std.Legacy.Range.size]; omega
  rw [hsize]
  refine foldl_ext _ _ ?_ _ _
  intro b j
  unfold bfStepC
  congr 1
  rw [getElem!_set!_ne _ (j+len) j _ (by omega)]

/-- **Full-sweep entrywise characterization** (the clean corollary of `bfFold_spec` at `m = len`):
low half `p ↦ a[p] + z·a[p+len]`, high half `p ↦ a[p−len] − z·a[p]`, rest untouched. -/
theorem bfSweep_getElem (z start len : Nat) (hlen : 1 ≤ len) (a0 : Poly)
    (hsz : a0.size = 256) (hbound : start + 2 * len ≤ 256) :
    (∀ p, start ≤ p → p < start + len →
      (bfSweep z start len a0)[p]! = addQ a0[p]! (mulModQ z a0[p+len]!)) ∧
    (∀ p, start + len ≤ p → p < start + 2 * len →
      (bfSweep z start len a0)[p]! = subQ a0[p-len]! (mulModQ z a0[p]!)) ∧
    (∀ p, (p < start ∨ start + 2 * len ≤ p) →
      (bfSweep z start len a0)[p]! = a0[p]!) := by
  rw [bfSweep_eq_foldl z start len hlen a0]
  obtain ⟨_, hlo, hhi, hun⟩ :=
    bfFold_spec z len hlen a0 len start a0 hsz (by omega) (le_refl _)
      (fun p _ _ => rfl) (fun p _ _ => rfl)
  refine ⟨?_, ?_, ?_⟩
  · intro p h1 h2; exact hlo p h1 (by omega)
  · intro p h1 h2; exact hhi p (by omega) (by omega)
  · intro p h
    apply hun p
    · omega
    · omega

theorem mulModQ_lt (a b : Nat) : mulModQ a b < q := by
  unfold mulModQ; exact Nat.mod_lt _ (by unfold q; omega)

/-- **The butterfly is the 2×2 ℤ_q-linear map** — the full-sweep entrywise formula lifted into `ZMod q`
via the RUNG-0 cast homomorphism (`cast_addQ`/`cast_subQ`/`cast_mulModQ`). Low half `↦ a[p] + z·a[p+len]`,
high half `↦ a[p−len] − z·a[p]`, rest fixed. This is the exact linear relation over the honest field that
the CT stage invariant is preserved by. -/
theorem cast_bfSweep (z start len : Nat) (hlen : 1 ≤ len) (a0 : Poly)
    (hsz : a0.size = 256) (hbound : start + 2 * len ≤ 256) :
    (∀ p, start ≤ p → p < start + len →
      ((bfSweep z start len a0)[p]! : ZMod q)
        = (a0[p]! : ZMod q) + (z : ZMod q) * (a0[p+len]! : ZMod q)) ∧
    (∀ p, start + len ≤ p → p < start + 2 * len →
      ((bfSweep z start len a0)[p]! : ZMod q)
        = (a0[p-len]! : ZMod q) - (z : ZMod q) * (a0[p]! : ZMod q)) := by
  obtain ⟨hlo, hhi, _⟩ := bfSweep_getElem z start len hlen a0 hsz hbound
  constructor
  · intro p h1 h2
    rw [hlo p h1 h2, cast_addQ, cast_mulModQ]
  · intro p h1 h2
    rw [hhi p h1 h2, cast_subQ _ _ (by have := mulModQ_lt z a0[p]!; omega), cast_mulModQ]

/-! ## PART 1g — the SCHOOLBOOK (negacyclic) product coefficient formula, from the imperative double loop.

`schoolbookMul` is a nested `Id.run do` double loop with array-DEPENDENT accumulating writes
(`c[k] ← c[k] ± a[i]·b[j]`); its full-evaluation defeq is a measured >2 min kernel timeout. Instead the inner
`for j` sweep is abstracted into `rowSweep` (so each reduction handles ONE loop level, mirroring
`ntt`/`nttCleanDo`), then the two loops are peeled to explicit `List.foldl`s and characterized entrywise by
an ADDITIVE accumulator (`rowAccum`/`outerAccum`, over the honest field via the RUNG-0 casts): output slot `m`
carries `∑_{i+j=m} a_i·b_j − ∑_{i+j=m+256} a_i·b_j` in `ℤ_q` (`schoolbookMul_getElem`), the negacyclic
convolution. `schoolbookMul_size`/`schoolbookMul_lt` fall out of the same folds. No `native_decide`. -/

/-- `addQ` lands in the reduced range `[0, q)`. -/
theorem addQ_lt (a b : Nat) : addQ a b < q := by unfold addQ; exact Nat.mod_lt _ (by unfold q; omega)
/-- `subQ` lands in the reduced range `[0, q)`. -/
theorem subQ_lt (a b : Nat) : subQ a b < q := by unfold subQ; exact Nat.mod_lt _ (by unfold q; omega)

/-- After a `set!`, every slot holds either the written value or the original — the reusable teeth for the
`< q` reduced-range invariants below (covers the out-of-bounds no-op branch too). -/
theorem set!_val_cases (b : Poly) (i v p : Nat) :
    (b.set! i v)[p]! = v ∨ (b.set! i v)[p]! = b[p]! := by
  by_cases h : i = p
  · subst h
    by_cases hib : i < b.size
    · exact Or.inl (getElem!_set!_self _ _ _ hib)
    · right
      simp [Array.set!_eq_setIfInBounds, hib]
  · exact Or.inr (getElem!_set!_ne _ _ _ _ h)

/-- A `set!` with a reduced value preserves the "all entries `< q`" invariant. -/
theorem set!_lt (b : Poly) (i v : Nat) (hb : ∀ (p : Nat), b[p]! < q) (hv : v < q) :
    ∀ (p : Nat), (b.set! i v)[p]! < q := by
  intro p; rcases set!_val_cases b i v p with hh | hh
  · rw [hh]; exact hv
  · rw [hh]; exact hb p

/-- `schoolbookMul`'s inner `for j` sweep, as its own definition (so the outer/inner reductions each stay
one-loop-deep, avoiding the double-loop defeq wall). A VERBATIM copy of that inner loop. -/
def rowSweep (a b : Poly) (i : Nat) (c0 : Poly) : Poly := Id.run do
  let mut c := c0
  for j in [0:256] do
    let prod := mulModQ a[i]! b[j]!
    let k := i + j
    if k < 256 then c := c.set! k (addQ c[k]! prod)
    else c := c.set! (k - 256) (subQ c[k - 256]! prod)
  return c

/-- `schoolbookMul` with the inner sweep abstracted as `rowSweep` — definitionally equal to `schoolbookMul`
(`rowSweep` IS that inner loop), the intermediate that keeps the inner term opaque during the outer peel. -/
def schoolbookCleanDo (a b : Poly) : Poly := Id.run do
  let mut c := zeroPoly
  for i in [0:256] do
    c := rowSweep a b i c
  return c

/-- One inner-sweep butterfly step (the `range' 0 256 1` fold function `rowSweep` reduces to). -/
def RowStep (a b : Poly) (i : Nat) (c : Poly) (j : Nat) : Poly :=
  if i + j < 256 then c.set! (i+j) (addQ c[i+j]! (mulModQ a[i]! b[j]!))
  else c.set! (i+j-256) (subQ c[i+j-256]! (mulModQ a[i]! b[j]!))

/-- Signed `ℤ_q` contribution of coefficient pair `(i,j)` to output slot `m`: `+a_i·b_j` if `i+j = m` (no
wrap), `−a_i·b_j` if `i+j = m+256` (the `X²⁵⁶ = −1` negacyclic wrap), else `0`. -/
def cJ (a b : Poly) (i j m : Nat) : ZMod q :=
  if i + j = m then ((a[i]! : Nat) : ZMod q) * ((b[j]! : Nat) : ZMod q)
  else if i + j = m + 256 then -(((a[i]! : Nat) : ZMod q) * ((b[j]! : Nat) : ZMod q))
  else 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
/-- Inner-loop abstraction: `schoolbookMul = schoolbookCleanDo` (rfl-clean; inner opaque). -/
theorem sbk_clean (a b : Poly) : schoolbookMul a b = schoolbookCleanDo a b := by
  unfold schoolbookMul schoolbookCleanDo rowSweep; rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
/-- Inner peel: the `rowSweep` `for j` loop is the explicit `RowStep` fold. -/
theorem rowSweep_fold (a b : Poly) (i : Nat) (c0 : Poly) :
    rowSweep a b i c0 = List.foldl (RowStep a b i) c0 (List.range' 0 256 1) := by
  unfold rowSweep RowStep
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    ← apply_ite, List.forIn_pure_yield_eq_foldl, bind_pure, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
/-- Generic outer-loop peel with the per-row step `f` kept OPAQUE — so `simp` reduces the `forIn` to a `foldl`
WITHOUT unfolding the inner `Id.run` sweep (which would trigger the 256×256 double-loop defeq wall). -/
theorem forIn_zeroPoly_fold (f : Nat → Poly → Poly) :
    (Id.run do
      let mut c := zeroPoly
      for i in [0:256] do
        c := f i c
      return c)
      = List.foldl (fun c i => f i c) zeroPoly (List.range' 0 256 1) := by
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, bind_pure, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

/-- Outer peel: the `schoolbookCleanDo` `for i` loop is the explicit `rowSweep` fold (via the opaque-`f`
generic lemma, so the inner sweep is never evaluated by the kernel). -/
theorem sbk_outer (a b : Poly) :
    schoolbookCleanDo a b
      = List.foldl (fun c i => rowSweep a b i c) zeroPoly (List.range' 0 256 1) :=
  forIn_zeroPoly_fold (fun i c => rowSweep a b i c)

set_option maxRecDepth 8000 in
/-- **Row accumulator.** After folding one row's `RowStep`s over `[0, nj)`, slot `m`'s `ℤ_q` value is the
input plus `∑_{j<nj} cJ(i,j,m)` — the additive characterization of the array-dependent accumulating writes. -/
theorem rowAccum (a b : Poly) (i : Nat) (hi : i < 256) :
    ∀ (nj : Nat) (c : Poly), c.size = 256 →
      (List.foldl (RowStep a b i) c (List.range' 0 nj 1)).size = 256 ∧
      ∀ m, m < 256 →
        (((List.foldl (RowStep a b i) c (List.range' 0 nj 1))[m]! : Nat) : ZMod q)
          = ((c[m]! : Nat) : ZMod q) + ∑ j ∈ range nj, cJ a b i j m := by
  intro nj
  induction nj with
  | zero =>
    intro c hc; refine ⟨by simpa using hc, ?_⟩
    intro m hm
    simp only [List.range'_zero, List.foldl_nil, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ nj ih =>
    intro c hc
    rw [List.range'_1_concat, List.foldl_concat, Nat.zero_add]
    obtain ⟨ihsz, ihval⟩ := ih c hc
    set A := List.foldl (RowStep a b i) c (List.range' 0 nj 1) with hAdef
    have hstep : (RowStep a b i A nj).size = 256 := by
      unfold RowStep; by_cases hk : i + nj < 256
      · rw [if_pos hk, size_set!]; exact ihsz
      · rw [if_neg hk, size_set!]; exact ihsz
    refine ⟨hstep, ?_⟩
    intro m hm
    rw [Finset.sum_range_succ]
    unfold RowStep
    by_cases hk : i + nj < 256
    · rw [if_pos hk]
      by_cases hm2 : m = i + nj
      · subst hm2
        rw [getElem!_set!_self A (i+nj) _ (by rw [ihsz]; omega), cast_addQ, cast_mulModQ, ihval (i+nj) hm]
        have hcj : cJ a b i nj (i+nj) = ((a[i]! : Nat) : ZMod q) * ((b[nj]! : Nat) : ZMod q) := by
          unfold cJ; rw [if_pos rfl]
        rw [hcj]; ring
      · rw [getElem!_set!_ne A (i+nj) m _ (by omega), ihval m hm]
        have hcj : cJ a b i nj m = 0 := by unfold cJ; rw [if_neg (by omega), if_neg (by omega)]
        rw [hcj, add_zero]
    · rw [if_neg hk]
      by_cases hm2 : m = i + nj - 256
      · subst hm2
        rw [getElem!_set!_self A (i+nj-256) _ (by rw [ihsz]; omega),
            cast_subQ _ _ (by have := mulModQ_lt a[i]! b[nj]!; omega), cast_mulModQ, ihval _ hm]
        have hcj : cJ a b i nj (i+nj-256) = -(((a[i]! : Nat) : ZMod q) * ((b[nj]! : Nat) : ZMod q)) := by
          unfold cJ; rw [if_neg (by omega), if_pos (by omega)]
        rw [hcj]; ring
      · rw [getElem!_set!_ne A (i+nj-256) m _ (by omega), ihval m hm]
        have hcj : cJ a b i nj m = 0 := by unfold cJ; rw [if_neg (by omega), if_neg (by omega)]
        rw [hcj, add_zero]

theorem zeroPoly_get (m : Nat) : zeroPoly[m]! = 0 := by
  rw [zeroPoly, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

theorem zeroPoly_cast (m : Nat) : ((zeroPoly[m]! : Nat) : ZMod q) = 0 := by
  rw [zeroPoly_get]; simp

set_option maxRecDepth 8000 in
/-- **Outer accumulator.** Summing the per-row contributions across all rows `i < ni`: slot `m` carries
`∑_{i<ni} ∑_{j<256} cJ(i,j,m)`. -/
theorem outerAccum (a b : Poly) :
    ∀ (ni : Nat), ni ≤ 256 → ∀ (c : Poly), c.size = 256 →
      (List.foldl (fun c i => rowSweep a b i c) c (List.range' 0 ni 1)).size = 256 ∧
      ∀ m, m < 256 →
        (((List.foldl (fun c i => rowSweep a b i c) c (List.range' 0 ni 1))[m]! : Nat) : ZMod q)
          = ((c[m]! : Nat) : ZMod q) + ∑ i ∈ range ni, ∑ j ∈ range 256, cJ a b i j m := by
  intro ni
  induction ni with
  | zero => intro _ c hc; refine ⟨by simpa using hc, ?_⟩; intro m hm; simp
  | succ ni ih =>
    intro hni c hc
    rw [List.range'_1_concat, List.foldl_concat, Nat.zero_add]
    obtain ⟨ihsz, ihval⟩ := ih (by omega) c hc
    set A := List.foldl (fun c i => rowSweep a b i c) c (List.range' 0 ni 1) with hAdef
    obtain ⟨rssz, rsval⟩ := rowAccum a b ni (by omega) 256 A ihsz
    refine ⟨?_, ?_⟩
    · show (rowSweep a b ni A).size = 256
      rw [rowSweep_fold]; exact rssz
    · intro m hm
      rw [Finset.sum_range_succ]
      show (((rowSweep a b ni A)[m]! : Nat) : ZMod q) = _
      rw [rowSweep_fold, rsval m hm, ihval m hm]; ring

/-- **THE NEGACYCLIC COEFFICIENT FORMULA** (`ℤ_q`, from the imperative double loop). For a size-256 slot `m`,
`(schoolbookMul a b)_m = ∑_{i+j=m} a_i·b_j − ∑_{i+j=m+256} a_i·b_j` — the `X²⁵⁶+1` negacyclic convolution,
proven from the actual accumulating writes (not `rfl`/`native_decide`). Axiom-clean. -/
theorem schoolbookMul_getElem (a b : Poly) (m : Nat) (hm : m < 256) :
    (((schoolbookMul a b)[m]! : Nat) : ZMod q)
      = ∑ i ∈ range 256, ∑ j ∈ range 256, cJ a b i j m := by
  rw [sbk_clean, sbk_outer]
  obtain ⟨_, hval⟩ := outerAccum a b 256 (le_refl _) zeroPoly (by simp [zeroPoly])
  rw [hval m hm, zeroPoly_cast, zero_add]

/-- The negacyclic product preserves the 256-coefficient length. -/
theorem schoolbookMul_size (a b : Poly) : (schoolbookMul a b).size = 256 := by
  rw [sbk_clean, sbk_outer]
  exact (outerAccum a b 256 (le_refl _) zeroPoly (by simp [zeroPoly])).1

theorem RowStep_lt (a b : Poly) (i : Nat) (c : Poly) (j : Nat) (hc : ∀ (p:Nat), c[p]!<q) :
    ∀ (p:Nat), (RowStep a b i c j)[p]! < q := by
  unfold RowStep; split
  · exact set!_lt _ _ _ hc (addQ_lt _ _)
  · exact set!_lt _ _ _ hc (subQ_lt _ _)

theorem foldl_RowStep_lt (a b : Poly) (i : Nat) :
    ∀ (L : List Nat) (c : Poly), (∀ (p:Nat), c[p]!<q) →
      ∀ (p:Nat), (List.foldl (RowStep a b i) c L)[p]!<q := by
  intro L; induction L with
  | nil => intro c hc p; simpa using hc p
  | cons hd tl ih => intro c hc; exact ih _ (RowStep_lt a b i c hd hc)

theorem rowSweep_lt (a b : Poly) (i : Nat) (c : Poly) (hc : ∀ (p:Nat), c[p]!<q) :
    ∀ (p:Nat), (rowSweep a b i c)[p]!<q := by
  rw [rowSweep_fold]; exact foldl_RowStep_lt a b i _ c hc

theorem foldl_outer_lt (a b : Poly) :
    ∀ (L : List Nat) (c : Poly), (∀ (p:Nat), c[p]!<q) →
      ∀ (p:Nat), (List.foldl (fun c i => rowSweep a b i c) c L)[p]!<q := by
  intro L; induction L with
  | nil => intro c hc p; simpa using hc p
  | cons hd tl ih => intro c hc; exact ih _ (rowSweep_lt a b hd c hc)

/-- Every coefficient of the negacyclic product is reduced (`< q`) — the writes are all `addQ`/`subQ`. -/
theorem schoolbookMul_lt (a b : Poly) : ∀ (p:Nat), (schoolbookMul a b)[p]!<q := by
  rw [sbk_clean, sbk_outer]
  exact foldl_outer_lt a b _ zeroPoly (fun p => by rw [zeroPoly_get p]; unfold q; omega)

/-! ### RUNG 2, step 1 — THE OUTER-LOOP PEEL (`ntt = nttFold`), BUILT.

The two OUTER loops of `ntt` (`for s in [0:8]`, `for blk in [0:nblk]`, threading the mutable pair `(a, k)`)
are peeled into an explicit ordered composition of `bfSweep`s: `ntt w = nttFold w`, where `nttFold` is the
nested `List.foldl` over stages/blocks with the innermost `for j` replaced by a `bfSweep` call. This is the
"peel" the module header named as still-open. It is discharged in two rfl-clean hops through an intermediate
`nttCleanDo` (the SAME `Id.run do` schedule with the inner butterfly abbreviated to `bfSweep`, definitionally
equal to `ntt` because `bfSweep` is a verbatim copy of that inner loop), then a `foldl`-congruence
(`foldl_ext_mem`) reducing the `forIn`/pair-state monadic form to the plain fold. Axiom-clean; no
`native_decide`. The twiddle counter `k` is threaded as `st.2`, so global block `blk` in stage `s` consumes
`zetaTwiddle (st.2 + 1)` with `k` running `1 … 255` across all `Σ_s 2^s = 255` blocks. -/

/-- Pointwise-equal-on-`l` step functions fold to the same result (mem-restricted `foldl_ext`). -/
theorem foldl_ext_mem {A B : Type} (f g : B → A → B) (l : List A)
    (h : ∀ b, ∀ a ∈ l, f b a = g b a) (init : B) : l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]; rw [h init hd (List.mem_cons_self ..)]
    exact ih (fun b a ha => h b a (List.mem_cons_of_mem _ ha)) _

/-- `ntt`'s schedule with the innermost `for j` butterfly written as a `bfSweep` call — definitionally equal
to `ntt` (`bfSweep` IS that inner loop). The intermediate that keeps the inner term opaque during the peel. -/
def nttCleanDo (w : Poly) : Poly := Id.run do
  let mut a := w
  let mut k := 0
  for s in [0:8] do
    let len := 128 >>> s
    let nblk := 128 / len
    for blk in [0:nblk] do
      let start := blk * 2 * len
      k := k + 1
      a := bfSweep (zetaTwiddle k) start len a
  return a

/-- **The forward NTT as an explicit ordered `bfSweep` fold** — the peeled form of `ntt`. Outer fold over the
8 stages, inner fold over the `2^s` blocks; state `(a, k)` threads the array and the twiddle counter. -/
def nttFold (w : Poly) : Poly :=
  (List.foldl (fun (st : Poly × Nat) (s : Nat) =>
      List.foldl (fun (st2 : Poly × Nat) (blk : Nat) =>
          (bfSweep (zetaTwiddle (st2.2 + 1)) (blk * 2 * (128 >>> s)) (128 >>> s) st2.1, st2.2 + 1))
        st (List.range' 0 (128 / (128 >>> s)) 1))
    (w, 0) (List.range' 0 8 1)).1

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- The `Id.run do` schedule reduces to the plain nested `foldl` (`forIn`→`foldl`, pair-state threaded). -/
theorem do_eq_fold (w : Poly) : nttCleanDo w = nttFold w := by
  unfold nttCleanDo nttFold
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  refine Eq.trans ?_ (congrArg Prod.fst (foldl_ext_mem _ _ _ (fun st s _ => rfl) (w, 0)))
  rfl

/-- **THE OUTER-LOOP PEEL.** `ntt w = nttFold w`: the imperative 8-stage butterfly schedule equals the
explicit ordered `bfSweep` fold. This closes step 1 of the RUNG-2 residual. Axiom-clean. -/
theorem ntt_eq_fold (w : Poly) : ntt w = nttFold w := by
  rw [show ntt w = nttCleanDo w by unfold ntt nttCleanDo bfSweep; rfl, do_eq_fold]

/-! ### RUNG 2, step 1b — THE TWIDDLE IS `ζ^{brv(k)}` IN THE FIELD (`cast_zetaTwiddle`), BUILT.

The collapse of the stage invariant needs the executable twiddle `zetaTwiddle k = powModQ ζ (brv8 k)` to be
the honest field power `(ζ : ℤ_q)^{brv8 k}`. Both `powModQ` (square-and-multiply, a 32-step ladder) and
`brv8` (8-bit reversal) are imperative `Id.run do` loops; each is characterized from its actual def:
`cast_powModQ` proves the ladder computes `base^e` in `ℤ_q` (loop invariant `result = base^{e mod 2^t}`,
`b = base^{2^t}`, `ex = e / 2^t` after `t` steps), and `brv8_lt` bounds `brv8 k < 256 < 2^32` (so the ladder
covers the exponent). No `native_decide`. -/

/-- The desugared square-and-multiply step of `powModQ`; state `(b, ex, result)`. -/
def pstep (st : Nat × Nat × Nat) (_ : Nat) : Nat × Nat × Nat :=
  (mulModQ st.1 st.1, st.2.1 / 2, if st.2.1 % 2 == 1 then mulModQ st.2.2 st.1 else st.2.2)

/-- `powModQ` as the explicit 32-step ladder fold (`result` is the third component). -/
theorem powModQ_eq_fold (base e : Nat) :
    powModQ base e = (List.foldl pstep (base % q, e, 1) (List.range' 0 32 1)).2.2 := by
  unfold powModQ
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    ← apply_ite, List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

/-- **Ladder loop invariant** in `ℤ_q`: after `n` steps `result = res·b0^{ex0 mod 2ⁿ}`, `b = b0^{2ⁿ}`,
`ex = ex0 / 2ⁿ`. The square-and-multiply correctness, proved entrywise from the fold (not asserted). -/
theorem pow_fold_inv (b0 ex0 : Nat) : ∀ (n res : Nat),
    (((List.range' 0 n 1).foldl pstep (b0, ex0, res)).2.2 : ZMod q)
        = (res : ZMod q) * (b0 : ZMod q) ^ (ex0 % 2 ^ n)
      ∧ (((List.range' 0 n 1).foldl pstep (b0, ex0, res)).1 : ZMod q) = (b0 : ZMod q) ^ (2 ^ n)
      ∧ (((List.range' 0 n 1).foldl pstep (b0, ex0, res)).2.1 = ex0 / 2 ^ n) := by
  intro n
  induction n with
  | zero => intro res; simp [Nat.mod_one]
  | succ n ih =>
    intro res
    rw [List.range'_1_concat, List.foldl_concat]
    obtain ⟨ih1, ih2, ih3⟩ := ih res
    set S := (List.range' 0 n 1).foldl pstep (b0, ex0, res) with hS
    have hpow : (2 : Nat) ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
    have hmul : ex0 % 2 ^ (n + 1) = ex0 % 2 ^ n + 2 ^ n * (ex0 / 2 ^ n % 2) := by
      rw [hpow, Nat.mod_mul]
    unfold pstep
    refine ⟨?_, ?_, ?_⟩
    · by_cases hpar : (S.2.1 % 2 == 1) = true
      · rw [if_pos hpar]
        have hpar2 : S.2.1 % 2 = 1 := by simpa using hpar
        rw [cast_mulModQ, ih1, ih2]
        have hodd : ex0 / 2 ^ n % 2 = 1 := by rw [← ih3]; exact hpar2
        rw [hmul, hodd, mul_one, pow_add]; ring
      · rw [if_neg hpar, ih1]
        have hpar2 : S.2.1 % 2 = 0 := by
          have : ¬ S.2.1 % 2 = 1 := by simpa using hpar
          omega
        have heven : ex0 / 2 ^ n % 2 = 0 := by rw [← ih3]; exact hpar2
        rw [hmul, heven, mul_zero, add_zero]
    · rw [cast_mulModQ, ih2, ← pow_add, ← two_mul, ← pow_succ']
    · rw [ih3, Nat.div_div_eq_div_mul, ← pow_succ]

/-- **`powModQ` reduces to the honest field power** `(base : ℤ_q)^e` for `e < 2³²` (covers all `brv8` outputs).
The imperative modular exponentiation IS `ℤ_q` exponentiation. -/
theorem cast_powModQ (base e : Nat) (he : e < 2 ^ 32) :
    ((powModQ base e : Nat) : ZMod q) = (base : ZMod q) ^ e := by
  rw [powModQ_eq_fold, (pow_fold_inv (base % q) e 32 1).1, Nat.mod_eq_of_lt he, Nat.cast_one,
      one_mul, ZMod.natCast_mod]

/-- The desugared bit-shift step of `brv8`; state `(r, x)`. -/
def brvStep (b : Nat × Nat) (_ : Nat) : Nat × Nat := (b.1 * 2 + b.2 % 2, b.2 / 2)

theorem brv8_eq_fold (k : Nat) : brv8 k = ((List.range' 0 8 1).foldl brvStep (0, k)).1 := by
  unfold brv8
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  rfl

/-- After `n` shift-in steps the accumulated reversal `r < 2ⁿ` (loop invariant on the `brv8` fold). -/
theorem brv_fold_lt : ∀ (n x : Nat), ((List.range' 0 n 1).foldl brvStep (0, x)).1 < 2 ^ n := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    rw [List.range'_1_concat, List.foldl_concat]
    have hih := ih x
    have hmod : ((List.range' 0 n 1).foldl brvStep (0, x)).2 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hpow : (2 : Nat) ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
    set S := (List.range' 0 n 1).foldl brvStep (0, x) with hS
    unfold brvStep
    omega

/-- The 8-bit reversal is `< 256` (so `< 2³²`, discharging `cast_powModQ`'s bound). -/
theorem brv8_lt (k : Nat) : brv8 k < 256 := by
  rw [brv8_eq_fold]; have := brv_fold_lt 8 k; norm_num at this ⊢; omega

/-- **THE TWIDDLE IN THE FIELD.** `zetaTwiddle k = (ζ : ℤ_q)^{brv8 k}` — the FIPS 204 twiddle is the honest
field power at the bit-reversed exponent. This is the identification the stage-invariant collapse consumes
to reach the `ζ^{2·brv(m)+1}` roots. Axiom-clean. -/
theorem cast_zetaTwiddle (k : Nat) :
    ((zetaTwiddle k : Nat) : ZMod q) = (zeta : ZMod q) ^ (brv8 k) := by
  unfold zetaTwiddle
  exact cast_powModQ zeta (brv8 k) (lt_of_lt_of_le (brv8_lt k) (by norm_num))

/-! ### The EXACT remaining step (the top of RUNG 2) — the CT stage-invariant induction.

Steps 1 (`ntt_eq_fold`, the peel) and 1b (`cast_zetaTwiddle`, the twiddle-in-field) are now BUILT above.
What remains to discharge `NttEvalsAtRoots` is the stage-invariant induction over `nttFold`:

* **The invariant** (`0 ≤ s ≤ 7`, root closed form `ρ(s,g) = (ζ:ℤ_q)^{2·brv8(2ˢ+g)}`): after `s` stages, for
  every segment `g < 2ˢ` and offset `i < 256 >>> s`,
  `(nttStage_s w)[g·(256>>>s) + i]! = Σ_{u < 2ˢ} (w[i + u·(256>>>s)]! : ℤ_q) · ρ(s,g)^u`
  — i.e. array slot `g·len+i` holds the `ℤ_q`-eval of the decimated coefficient sequence
  `(w_i, w_{i+len}, w_{i+2len}, …)` at `ρ(s,g)`, equivalently the `i`-th coefficient of `w mod (X^{len} − ρ(s,g))`.
* **Base** `s = 0`: `2⁰ = 1`, sum is the single `u = 0` term `= w[i]!`, so the array is the input — trivial.
* **Step** (one full stage = the inner block fold): block `blk` rewrites segment `blk` (positions
  `[blk·len_s, blk·len_s + len_s)`, `len_s = 256>>>s`) into new segments `2·blk` (low) and `2·blk+1` (high)
  via `cast_bfSweep` with twiddle `z = (ζ:ℤ_q)^{brv8(2ˢ+blk)}` (`cast_zetaTwiddle`). Splitting the target
  sum `Σ_{u < 2^{s+1}}` into even/odd `u` gives exactly `low = g_lo + z·g_hi`, `high = g_lo − z·g_hi`
  (one `Finset` even/odd reindex + a `ring` step over `ℤ_q`), advancing `ρ(s,blk) = z²` to
  `ρ(s+1,2blk) = z`, `ρ(s+1,2blk+1) = −z`. The block-disjointness (each block touches its own segment) is
  the inner `foldl` invariant. This is where the `brv8` exponent identities
  `2·brv8(2^{s+1}+2blk) ≡ brv8(2ˢ+blk)  (mod 512)` (and the `+1`/`+256` variants) enter — provable from
  `brv8_eq_fold` bit-arithmetic — pinning `ρ` consistent under the recurrence.
* **Collapse** `s = 8` (`len = 1`): the recurrence's last step sends `ρ(8,m)` to `ζ^{2·brv8(m)+1} = evalRoot m`
  (the closed form `2·brv8(2ˢ+g)` holds only for `s ≤ 7`; the `7 → 8` step supplies the `+1`), and the sum
  over `u < 256` is `eval256 w (evalRoot m)`, i.e. `NttEvalsAtRoots`.

That nested block-disjoint stage-invariant induction (with the `brv8` exponent identities and the even/odd
`Finset` reindex) is the single named sub-step still open; the peel, the butterfly engine, the twiddle-field
cast, and the orthogonality all rest under it, BUILT. -/

/-- The 256 negacyclic evaluation points `ζ^{2·brv(m)+1}` (the roots of `X²⁵⁶+1` over `ℤ_q`). -/
def evalRoot (m : Nat) : ZMod q := (zeta : ZMod q)^(2 * brv8 m + 1)

/-- Evaluation of the degree-<256 poly `a` at `x ∈ ℤ_q`: `Σ_{k<256} a_k · xᵏ`. -/
def eval256 (a : Poly) (x : ZMod q) : ZMod q := ∑ k ∈ range 256, (a[k]! : ZMod q) * x^k

/-- **OPEN (rung 2, forward).** The forward butterfly network computes evaluation at the negacyclic roots:
`(ntt a)_m = eval256 a (ζ^{2·brv(m)+1})`. The precise loop-index identification behind `NttMulHom` and the
forward half of `NttLeftInverse`. -/
def NttEvalsAtRoots : Prop :=
  ∀ (a : Poly) (m : Nat), m < 256 → ((ntt a)[m]! : ZMod q) = eval256 a (evalRoot m)

/-- **OPEN (rung 2, inverse).** The inverse butterfly network interpolates: `(intt v)_k = 256⁻¹ · Σ_{m<256}
v_m · (root_m)⁻ᵏ`. The inverse half of `NttLeftInverse`. Together with `NttEvalsAtRoots` and
`omega_orthogonality`, these two props discharge `NttLeftInverse`. -/
def InttInterpolates : Prop :=
  ∀ (v : Poly) (k : Nat), k < 256 →
    ((intt v)[k]! : ZMod q) = (256 : ZMod q)⁻¹ * ∑ m ∈ range 256, (v[m]! : ZMod q) * (evalRoot m)⁻¹^k

/-! ## PART 2 — the residual, decomposed into two standard NTT-correctness facts. -/

/-- **Residual A — the inverse transform is a genuine left inverse** (size-256-guarded). `intt ∘ ntt = id`
on canonical polys. The `∀`-over-all-`Poly` form is FALSE (a non-256 input keeps the wrong `Array` length);
the guard is the operationally-correct statement (the deployed pipeline feeds only decoded size-256 arrays).
This is the SINGLE remaining residual behind `RingRepFaithful` — the `intt` (Gentleman–Sande) interpolation
induction, the mirror of `stage_inv` collapsed by `omega_orthogonality`. -/
def NttLeftInverse : Prop := ∀ c : Poly, c.size = 256 → intt (ntt c) = c

/-- **Residual B — `ntt` is a ring homomorphism** from the negacyclic ring `(Poly, schoolbookMul)` to the
pointwise-product ring `(Poly, pointwiseMul)`: `ntt (a·b) = ntt a ⊙ ntt b` (size-256-guarded). **CLOSED**
below (`nttMulHom_proven`): the forward butterfly network computes eval-at-the-roots (`nttEvalsAtRoots_canonical`),
eval-at-a-negacyclic-root is multiplicative (`eval256_schoolbook`, collapsing the `∑_{i+j=m}−∑_{i+j=m+256}`
convolution under `evalRoot^256 = −1`), and the pointwise ring is coordinatewise `ℤ_q` (`cast_pointwiseMul`). -/
def NttMulHom : Prop := ∀ a b : Poly, a.size = 256 → b.size = 256 →
  ntt (schoolbookMul a b) = pointwiseMul (ntt a) (ntt b)

/-- **THE REDUCTION (axiom-clean).** `RingRepFaithful` — the ∀ NTT-faithfulness residual behind
`verifyCore = spec` — follows from the two standard NTT-correctness facts above. Textbook: a transform-based
multiply is correct exactly when the transform inverts and diagonalizes the convolution. Proof:
`intt(ntt a ⊙ ntt b) = intt(ntt(a·b)) = a·b`, guards threaded via `schoolbookMul_size`. With `NttMulHom` now
CLOSED (`nttMulHom_proven`), `ringRepFaithful_of_leftInverse` below reduces `RingRepFaithful` to the SINGLE
`NttLeftInverse` residual. -/
theorem ringRepFaithful_of (hInv : NttLeftInverse) (hHom : NttMulHom) : RingRepFaithful := by
  intro a b ha hb
  rw [← hHom a b ha hb]
  exact hInv (schoolbookMul a b) (schoolbookMul_size a b)

/-! ## PART 3 — NON-VACUITY: both residuals HOLD on a wraparound-exercising sample.

`native_decide` here is the concrete SAMPLE witness only — NOT inside any ∀-theorem. It certifies that the two
hypotheses of `ringRepFaithful_of` are genuinely true (so the reduction is real, not a vacuous implication),
on the same high-degree `sampleA, sampleB` whose product exercises the `X²⁵⁶ = −1` sign wrap. -/

/-- The left-inverse residual holds on the concrete sample (this is `MlDsaRing.ntt_intt_id`, restated as a
witness that `NttLeftInverse` is instantiable). -/
theorem nttLeftInverse_sample : intt (ntt sampleA) = sampleA := by native_decide

/-- The ring-hom residual holds on the concrete wraparound sample: `ntt(a·b) = ntt a ⊙ ntt b`. -/
theorem nttMulHom_sample :
    ntt (schoolbookMul sampleA sampleB) = pointwiseMul (ntt sampleA) (ntt sampleB) := by native_decide

/-! ### RUNG 2, step 2 — THE CT STAGE-INVARIANT INDUCTION, CLOSED (forward `nttEvalsAtRoots`).

The single sub-step the header named as still-open is discharged here. The peeled fold `nttUpto`/`stageStep`/
`blockFn` is re-expressed block-by-block through the `block_char` accumulation lemma (a positionwise, Nat-level
characterization of one full CT stage — each block a disjoint segment, proven by induction on block count on top
of the `bfSweep_getElem` butterfly primitive). `stage_inv` then proves, by induction on the stage number `s`,
the invariant: after `s` stages, array slot `g·(256>>>s)+i` holds `∑_{u<2ˢ} w_{i+u·(256>>>s)}·(rootAt s g)^u`
— the `ℤ_q`-eval of the `g`-th decimated subsequence at its root. The stage step is `cast_bfSweep` (the 2×2
field map) + `cast_zetaTwiddle` (the twiddle `ζ^{brv8(2ˢ+blk)}`) + the even/odd `Finset` reindex
(`split_collapse`) + the `brv8` exponent congruences (`brv_even`/`brv_odd`/`brv_high`, proved by `decide` on the
8-bit fold), pinning `rootAt` consistent under the recurrence (`rootAt_closed`). At `s = 8` (`len = 1`) the
invariant collapses (`rootAt_final`: `rootAt 8 m = ζ^{2·brv8(m)+1} = evalRoot m`) to eval-at-the-roots.

⚠ **The forward statement is TRUE only for canonical (size-256) polys** and is stated with that guard
(`nttEvalsAtRoots_canonical`). The unguarded `∀ (a : Poly)` form (`NttEvalsAtRoots` / `NttMulHom` /
`NttLeftInverse` / `VerifyCoreSpec.RingRepFaithful`) is FALSE: for a non-256-length input the imperative
butterflies read/write out of bounds and the output length is wrong (e.g. `ntt #[5]` stays length 1, so
`(ntt #[5])[1]! = 0 ≠ eval256 #[5] (evalRoot 1)`). The deployed ML-DSA pipeline only ever feeds decoded
size-256 coefficient arrays, so the size-256 guard is the operationally-correct statement; it is what the
`verifyCore = spec` bridge needs. `ζ^256 = -1` is discharged here by plain `decide` (NOT `native_decide`), so
every theorem below is axiom-clean without the `ofReduceBool` residual. -/

set_option maxRecDepth 4000 in
theorem brv_even (n : Nat) (hn : n < 128) : 2 * brv8 (2*n) = brv8 n := by
  simp only [brv8_eq_fold]; revert hn; revert n; decide

set_option maxRecDepth 4000 in
theorem brv_odd (n : Nat) (hn : n < 128) : 2 * brv8 (2*n+1) = brv8 n + 256 := by
  simp only [brv8_eq_fold]; revert hn; revert n; decide

set_option maxRecDepth 4000 in
theorem brv_high (n : Nat) (hn : n < 128) : brv8 (128 + n) = brv8 n + 1 := by
  simp only [brv8_eq_fold]; revert hn; revert n; decide

set_option maxRecDepth 100000 in
theorem zeta_pow_neg_one : (zeta : ZMod q)^256 = -1 := by
  unfold zeta q; decide

theorem zeta_pow_add256 (e : Nat) : (zeta:ZMod q)^(e + 256) = -(zeta:ZMod q)^e := by
  rw [pow_add, zeta_pow_neg_one]; ring

theorem sum_range_two_mul {M} [AddCommMonoid M] (f : Nat → M) (n : Nat) :
    ∑ u ∈ range (2*n), f u = ∑ v ∈ range n, f (2*v) + ∑ v ∈ range n, f (2*v+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+1+1 from by ring, Finset.sum_range_succ, Finset.sum_range_succ,
        ih, Finset.sum_range_succ, Finset.sum_range_succ]
    abel

/-- The root a slot's segment is being evaluated at, after `s` code stages, segment `g`. -/
def rootAt (s g : Nat) : ZMod q :=
  match s with
  | 0 => (zeta:ZMod q)^(2*brv8 (1+g))
  | s+1 => (if g % 2 = 0 then (1:ZMod q) else -1) * (zeta:ZMod q)^(brv8 (2^s + g/2))

theorem rootAt_even_step (s blk : Nat) :
    rootAt (s+1) (2*blk) = (zeta:ZMod q)^(brv8 (2^s + blk)) := by
  simp [rootAt, Nat.mul_mod_right]

theorem rootAt_odd_step (s blk : Nat) :
    rootAt (s+1) (2*blk+1) = -(zeta:ZMod q)^(brv8 (2^s + blk)) := by
  have h1 : (2*blk+1) % 2 = 1 := by omega
  have h2 : (2*blk+1) / 2 = blk := by omega
  simp [rootAt, h1, h2]

/-- `rootAt s g = ζ^{2·brv8(2^s+g)}` for the input levels `s ≤ 7`, `g < 2^s`. -/
theorem rootAt_closed (s g : Nat) (hs : s ≤ 7) (hg : g < 2^s) :
    rootAt s g = (zeta:ZMod q)^(2 * brv8 (2^s + g)) := by
  match s with
  | 0 => simp [rootAt, pow_zero]
  | s+1 =>
    rcases Nat.even_or_odd g with ⟨c, hc⟩ | ⟨c, hc⟩
    · have hc' : g = 2 * c := by omega
      subst hc'
      have hclt : c < 2^s := by
        have h2 : 2^(s+1) = 2^s + 2^s := by rw [pow_succ]; ring
        omega
      have hc128 : 2^s + c < 128 := by
        have hpow : 2^s ≤ 2^6 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 2^6 = 64 := by norm_num
        omega
      rw [rootAt_even_step]
      have := brv_even (2^s + c) hc128
      have hh : 2^(s+1) + 2*c = 2*(2^s+c) := by rw [pow_succ]; ring
      rw [hh, ← this]
    · subst hc
      have hclt : c < 2^s := by
        have h2 : 2^(s+1) = 2^s + 2^s := by rw [pow_succ]; ring
        omega
      have hc128 : 2^s + c < 128 := by
        have hpow : 2^s ≤ 2^6 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 2^6 = 64 := by norm_num
        omega
      rw [rootAt_odd_step]
      have := brv_odd (2^s + c) hc128
      have hh : 2^(s+1) + (2*c+1) = 2*(2^s+c)+1 := by rw [pow_succ]; ring
      rw [hh, this, zeta_pow_add256]

/-- At the final level `s = 8`, `rootAt 8 m = evalRoot m = ζ^{2·brv8(m)+1}`. -/
theorem rootAt_final (m : Nat) (hm : m < 256) : rootAt 8 m = evalRoot m := by
  unfold evalRoot
  rcases Nat.even_or_odd m with ⟨blk, hb⟩ | ⟨blk, hb⟩
  · have hb' : m = 2 * blk := by omega
    subst hb'
    have hblk : blk < 128 := by omega
    rw [show (8:Nat) = 7+1 from rfl, rootAt_even_step]
    have hp : (2:Nat)^7 = 128 := by norm_num
    rw [hp, brv_high blk hblk, brv_even blk hblk]
  · subst hb
    have hblk : blk < 128 := by omega
    rw [show (8:Nat) = 7+1 from rfl, rootAt_odd_step]
    have hp : (2:Nat)^7 = 128 := by norm_num
    rw [hp, brv_high blk hblk]
    have ho := brv_odd blk hblk
    -- goal: -(ζ)^(brv8 blk + 1) = ζ^(2*brv8(2*blk+1)+1)
    rw [ho]
    -- ζ^(2*blk+1 side): 2*brv8(2blk+1)+1 = brv8 blk + 256 + 1 = (brv8 blk + 1) + 256
    rw [show brv8 blk + 256 + 1 = (brv8 blk + 1) + 256 from by ring, zeta_pow_add256]

theorem evalRoot_pow256 (m : Nat) : (evalRoot m)^256 = -1 := by
  unfold evalRoot
  rw [← pow_mul]
  have : (2 * brv8 m + 1) * 256 = 256 * (2*brv8 m) + 256 := by ring
  rw [this, pow_add, pow_mul, zeta_pow_neg_one]
  rw [show ((-1:ZMod q))^(2*brv8 m) = 1 by
        rw [pow_mul]; simp]
  ring



-- numeric helpers
theorem shr_pow (s : Nat) (hs : s ≤ 8) : 256 >>> s = 2^(8-s) := by
  rw [Nat.shiftRight_eq_div_pow, show (256:Nat) = 2^8 from rfl, Nat.pow_div hs (by norm_num)]
theorem shl_pow (s : Nat) (hs : s ≤ 7) : 128 >>> s = 2^(7-s) := by
  rw [Nat.shiftRight_eq_div_pow, show (128:Nat) = 2^7 from rfl, Nat.pow_div hs (by norm_num)]
theorem len_pos (s : Nat) (hs : s ≤ 7) : 1 ≤ 128 >>> s := by
  rw [shl_pow s hs]; exact Nat.one_le_two_pow
theorem L_eq_2len (s : Nat) (hs : s ≤ 7) : 256 >>> s = 2 * (128 >>> s) := by
  rw [shr_pow s (by omega), shl_pow s hs, ← pow_succ']
  congr 1; omega
theorem seg_total (s : Nat) (hs : s ≤ 8) : 2^s * (256 >>> s) = 256 := by
  rw [shr_pow s hs, ← pow_add, show s + (8-s) = 8 from by omega]; norm_num

-- fold structure
def blockFn (s : Nat) (st2 : Poly × Nat) (blk : Nat) : Poly × Nat :=
  (bfSweep (zetaTwiddle (st2.2 + 1)) (blk * 2 * (128 >>> s)) (128 >>> s) st2.1, st2.2 + 1)

def stageStep (s : Nat) (st : Poly × Nat) : Poly × Nat :=
  List.foldl (blockFn s) st (List.range' 0 (128 / (128 >>> s)) 1)

def nttUpto (n : Nat) (w : Poly) : Poly × Nat :=
  List.foldl (fun st s => stageStep s st) (w, 0) (List.range' 0 n 1)

theorem nttFold_eq (w : Poly) : nttFold w = (nttUpto 8 w).1 := by
  unfold nttFold nttUpto stageStep blockFn; rfl

theorem nttUpto_succ (n : Nat) (w : Poly) : nttUpto (n+1) w = stageStep n (nttUpto n w) := by
  unfold nttUpto
  rw [List.range'_1_concat, List.foldl_concat, Nat.zero_add]

theorem foldl_blockFn_snd (s : Nat) (l : List Nat) (st : Poly × Nat) :
    (List.foldl (blockFn s) st l).2 = st.2 + l.length := by
  induction l generalizing st with
  | nil => simp
  | cons hd tl ih => simp only [List.foldl_cons]; rw [ih]; simp [blockFn]; omega

theorem bfSweep_size (z start len : Nat) (hlen : 1 ≤ len) (a0 : Poly) (h : a0.size = 256) :
    (bfSweep z start len a0).size = 256 := by
  rw [bfSweep_eq_foldl z start len hlen a0]
  suffices hgen : ∀ (L : List Nat) (b : Poly), b.size = 256 →
      (List.foldl (bfStepC z len) b L).size = 256 by exact hgen _ a0 h
  intro L
  induction L with
  | nil => intro b hb; simpa using hb
  | cons hd tl ih => intro b hb; simp only [List.foldl_cons]; exact ih _ (by rw [bfStepC_size]; exact hb)

set_option maxHeartbeats 1000000 in
/-- **Inner block-fold characterization** (one full CT stage, positionwise, Nat-level). -/
theorem block_char (s : Nat) (hs : s ≤ 7) (a_in : Poly) (hsz : a_in.size = 256) (c0 : Nat) :
    ∀ nb, nb ≤ 2^s →
      ((List.foldl (blockFn s) (a_in, c0) (List.range' 0 nb 1)).1.size = 256) ∧
      (∀ p, nb * (256>>>s) ≤ p → p < 256 →
          (List.foldl (blockFn s) (a_in, c0) (List.range' 0 nb 1)).1[p]! = a_in[p]!) ∧
      (∀ blk, blk < nb → ∀ p, blk*(256>>>s) ≤ p → p < blk*(256>>>s)+(128>>>s) →
          (List.foldl (blockFn s) (a_in, c0) (List.range' 0 nb 1)).1[p]!
            = addQ a_in[p]! (mulModQ (zetaTwiddle (c0+blk+1)) a_in[p+(128>>>s)]!)) ∧
      (∀ blk, blk < nb → ∀ p, blk*(256>>>s)+(128>>>s) ≤ p → p < blk*(256>>>s)+(256>>>s) →
          (List.foldl (blockFn s) (a_in, c0) (List.range' 0 nb 1)).1[p]!
            = subQ a_in[p-(128>>>s)]! (mulModQ (zetaTwiddle (c0+blk+1)) a_in[p]!)) := by
  set len := 128 >>> s with hlendef
  set L := 256 >>> s with hLdef
  have hlen1 : 1 ≤ len := len_pos s hs
  have hL2 : L = 2 * len := L_eq_2len s hs
  have hLtot : 2^s * L = 256 := seg_total s (by omega)
  have hmono : ∀ i j : Nat, i ≤ j → i * L ≤ j * L := fun i j h => Nat.mul_le_mul_right _ h
  intro nb
  induction nb with
  | zero =>
    intro _; refine ⟨by simpa using hsz, ?_, ?_, ?_⟩
    · intro p _ _; simp
    · intro blk hblk; omega
    · intro blk hblk; omega
  | succ nb ih =>
    intro hnb
    have hnb' : nb ≤ 2^s := by omega
    obtain ⟨ihsz, ihun, ihlo, ihhi⟩ := ih hnb'
    have hcnt : (List.foldl (blockFn s) (a_in, c0) (List.range' 0 nb 1)).2 = c0 + nb := by
      rw [foldl_blockFn_snd]; simp
    set A := (List.foldl (blockFn s) (a_in, c0) (List.range' 0 nb 1)).1 with hAdef
    have hstart : nb * 2 * len = nb * L := by rw [hL2]; ring
    have hAeq : (List.foldl (blockFn s) (a_in, c0) (List.range' 0 (nb+1) 1)).1
        = bfSweep (zetaTwiddle (c0+nb+1)) (nb * L) len A := by
      rw [List.range'_1_concat, List.foldl_concat, Nat.zero_add]
      have hbf1 : (blockFn s (List.foldl (blockFn s) (a_in, c0) (List.range' 0 nb 1)) nb).1
          = bfSweep (zetaTwiddle ((List.foldl (blockFn s) (a_in, c0) (List.range' 0 nb 1)).2 + 1))
              (nb * 2 * len) len (List.foldl (blockFn s) (a_in, c0) (List.range' 0 nb 1)).1 := rfl
      rw [hbf1, hcnt, ← hAdef, hstart]
    set z := zetaTwiddle (c0+nb+1) with hzdef
    have hnbL : nb * L + L ≤ 256 := by
      have h1 := hmono (nb+1) (2^s) (by omega)
      have h2 : (nb+1) * L = nb * L + L := by ring
      rw [hLtot] at h1; omega
    have hbound : nb * L + 2 * len ≤ 256 := by rw [← hL2]; exact hnbL
    obtain ⟨hlo, hhi, hunt⟩ := bfSweep_getElem z (nb*L) len hlen1 A (by rw [hAdef]; exact ihsz) hbound
    have hApsize : (List.foldl (blockFn s) (a_in, c0) (List.range' 0 (nb+1) 1)).1.size = 256 := by
      rw [hAeq]; exact bfSweep_size z (nb*L) len hlen1 A (by rw [hAdef]; exact ihsz)
    refine ⟨hApsize, ?_, ?_, ?_⟩
    · intro p hp1 hp2
      rw [hAeq]
      have hpge : nb * L + 2 * len ≤ p := by
        have hh : (nb+1) * L = nb * L + L := by ring
        rw [← hL2]; omega
      rw [hunt p (Or.inr hpge), hAdef]
      exact ihun p (by omega) hp2
    · intro blk hblk p hp1 hp2
      rw [hAeq]
      rcases Nat.lt_or_ge blk nb with hlt | hge
      · have hpltnbL : p < nb * L := by
          have h1 : (blk+1) * L ≤ nb * L := hmono (blk+1) nb (by omega)
          have h3 : (blk+1)*L = blk*L + L := by ring
          omega
        rw [hunt p (Or.inl hpltnbL), hAdef]
        exact ihlo blk hlt p hp1 hp2
      · have hblkeq : blk = nb := by omega
        have hbb : blk * L = nb * L := by rw [hblkeq]
        rw [hblkeq]
        rw [hlo p (by omega) (by omega)]
        have hAp : A[p]! = a_in[p]! := by rw [hAdef]; exact ihun p (by omega) (by omega)
        have hAplen : A[p+len]! = a_in[p+len]! := by
          rw [hAdef]; exact ihun (p+len) (by omega) (by omega)
        rw [hAp, hAplen]
    · intro blk hblk p hp1 hp2
      rw [hAeq]
      rcases Nat.lt_or_ge blk nb with hlt | hge
      · have hpltnbL : p < nb * L := by
          have h1 : (blk+1) * L ≤ nb * L := hmono (blk+1) nb (by omega)
          have h3 : (blk+1)*L = blk*L + L := by ring
          omega
        rw [hunt p (Or.inl hpltnbL), hAdef]
        exact ihhi blk hlt p hp1 hp2
      · have hblkeq : blk = nb := by omega
        have hbb : blk * L = nb * L := by rw [hblkeq]
        rw [hblkeq]
        have hp2' : p < nb * L + 2 * len := by rw [← hL2]; omega
        rw [hhi p (by omega) hp2']
        have hAplen : A[p-len]! = a_in[p-len]! := by
          rw [hAdef]; exact ihun (p-len) (by omega) (by omega)
        have hAp : A[p]! = a_in[p]! := by rw [hAdef]; exact ihun p (by omega) (by omega)
        rw [hAplen, hAp]

theorem split_collapse (len Lval nn i' : Nat) (hL : Lval = 2*len) (r : ZMod q) (w : Poly) :
    ∑ u ∈ range (2*2^nn), (w[i'+u*len]! : ZMod q) * r^u
      = (∑ v ∈ range (2^nn), (w[i'+v*Lval]! : ZMod q) * (r^2)^v)
        + r * (∑ v ∈ range (2^nn), (w[i'+len+v*Lval]! : ZMod q) * (r^2)^v) := by
  rw [sum_range_two_mul]
  congr 1
  · apply Finset.sum_congr rfl; intro v _
    rw [show i' + 2*v*len = i' + v*Lval from by rw [hL]; ring, pow_mul]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro v _
    rw [show i' + (2*v+1)*len = i' + len + v*Lval from by rw [hL]; ring,
        show r^(2*v+1) = r*(r^2)^v from by rw [pow_succ, ← pow_mul]; ring]
    ring

theorem nblk_pow (n : Nat) (hn : n ≤ 7) : 128 / (128 >>> n) = 2^n := by
  rw [shl_pow n hn, show (128:Nat) = 2^7 from rfl, Nat.pow_div (by omega) (by norm_num)]
  congr 1; omega

theorem shr_succ (n : Nat) (hn : n ≤ 7) : 256 >>> (n+1) = 128 >>> n := by
  rw [shr_pow (n+1) (by omega), shl_pow n hn]; congr 1; omega

set_option maxHeartbeats 2000000 in
/-- **THE CT STAGE INVARIANT.** After `n` code stages, array slot `g·L_n+i` (`L_n = 256>>>n`) holds the
`ℤ_q`-evaluation of the `g`-th decimated subsequence at its root `rootAt n g`. -/
theorem stage_inv (w : Poly) (hw : w.size = 256) :
    ∀ n, n ≤ 8 →
      (nttUpto n w).1.size = 256 ∧
      (nttUpto n w).2 = 2^n - 1 ∧
      ∀ g i, g < 2^n → i < 256 >>> n →
        ((nttUpto n w).1[g * (256 >>> n) + i]! : ZMod q)
          = ∑ u ∈ range (2^n), (w[i + u * (256 >>> n)]! : ZMod q) * (rootAt n g)^u := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨by simpa [nttUpto] using hw, by simp [nttUpto], ?_⟩
    intro g i hg hi
    have hg0 : g = 0 := by omega
    subst hg0
    simp only [nttUpto, List.range'_zero, List.foldl_nil, pow_zero, Nat.zero_mul, Nat.zero_add,
      range_one, Finset.sum_singleton, Nat.add_zero, pow_zero, mul_one]
  | succ n ih =>
    intro hn1
    have hn7 : n ≤ 7 := by omega
    obtain ⟨ihsz, ihcnt, ihform⟩ := ih (by omega)
    set len := 128 >>> n with hlendef
    have hL2 : (256 >>> n) = 2 * len := L_eq_2len n hn7
    have hLn1 : (256 >>> (n+1)) = len := shr_succ n hn7
    have hpow2 : (2:Nat)^(n+1) = 2 * 2^n := by rw [pow_succ]; ring
    have hpowpos : 1 ≤ 2^n := Nat.one_le_two_pow
    -- unfold one stage via block_char
    have hstage : nttUpto (n+1) w = List.foldl (blockFn n) (nttUpto n w) (List.range' 0 (2^n) 1) := by
      rw [nttUpto_succ]; unfold stageStep; rw [nblk_pow n hn7]
    set a_in := (nttUpto n w).1 with haindef
    have hain_c : (nttUpto n w).2 = 2^n - 1 := ihcnt
    obtain ⟨bsz, bun, blo, bhi⟩ :=
      block_char n hn7 a_in ihsz (nttUpto n w).2 (2^n) (le_refl _)
    -- rewrite (nttUpto n w) as a pair to feed block_char (it folds over (a_in, c0))
    have hpair : (nttUpto n w) = (a_in, (nttUpto n w).2) := by rw [haindef]
    rw [hpair] at hstage
    -- twiddle counter: c0 + blk + 1 = 2^n + blk
    have htw : ∀ blk, (nttUpto n w).2 + blk + 1 = 2^n + blk := by
      intro blk; rw [hain_c]; omega
    refine ⟨?_, ?_, ?_⟩
    · rw [hstage]; exact bsz
    · rw [nttUpto_succ]; unfold stageStep
      rw [nblk_pow n hn7, foldl_blockFn_snd, hain_c]
      have : (List.range' 0 (2^n) 1).length = 2^n := by simp
      rw [this]; omega
    · -- the invariant
      intro g i hg hi
      rw [hLn1] at hi ⊢
      -- z := ζ^{brv8(2^n+blk)} in field ; r := rootAt (n+1) g
      rcases Nat.even_or_odd g with ⟨blk, hgb⟩ | ⟨blk, hgb⟩
      · -- g = 2*blk, low half, r = z
        have hgb' : g = 2 * blk := by omega
        subst hgb'
        have hblk : blk < 2^n := by
          have := hg; rw [hpow2] at this; omega
        -- position p = 2blk*len + i = blk*(256>>>n) + i
        have hpos : 2*blk*len + i = blk*(256>>>n) + i := by rw [hL2]; ring
        rw [hpos]
        -- block_char low at p = blk*(256>>>n)+i
        have hp1 : blk*(256>>>n) ≤ blk*(256>>>n)+i := by omega
        have hp2 : blk*(256>>>n)+i < blk*(256>>>n)+len := by omega
        rw [hstage, blo blk hblk (blk*(256>>>n)+i) hp1 hp2]
        -- cast
        rw [cast_addQ, cast_mulModQ, htw blk, cast_zetaTwiddle]
        -- INV(n) for the two reads
        have e1 : (a_in[blk*(256>>>n)+i]! : ZMod q)
            = ∑ v ∈ range (2^n), (w[i + v*(256>>>n)]! : ZMod q) * (rootAt n blk)^v := by
          have := ihform blk i hblk (by rw [hL2]; omega); rw [haindef]; exact this
        have e2 : (a_in[blk*(256>>>n)+i+len]! : ZMod q)
            = ∑ v ∈ range (2^n), (w[(i+len) + v*(256>>>n)]! : ZMod q) * (rootAt n blk)^v := by
          have := ihform blk (i+len) hblk (by rw [hL2]; omega)
          rw [haindef]
          rw [show blk*(256>>>n)+i+len = blk*(256>>>n)+(i+len) from by ring]
          exact this
        rw [e1, e2]
        -- RHS via split_collapse with r = ζ^{brv8(2^n+blk)} = rootAt (n+1) (2blk)
        have hr : rootAt (n+1) (2*blk) = (zeta:ZMod q)^(brv8 (2^n+blk)) := rootAt_even_step n blk
        have hrho : rootAt n blk = ((zeta:ZMod q)^(brv8 (2^n+blk)))^2 := by
          rw [rootAt_closed n blk hn7 hblk, ← pow_mul]; ring_nf
        rw [hr, hpow2, split_collapse len (256>>>n) n i hL2 _ w, ← hrho]
      · -- g = 2*blk+1, high half, r = -z
        subst hgb
        have hblk : blk < 2^n := by
          have := hg; rw [hpow2] at this; omega
        have hpos : (2*blk+1)*len + i = blk*(256>>>n)+len+i := by rw [hL2]; ring
        rw [hpos]
        have hp1 : blk*(256>>>n)+len ≤ blk*(256>>>n)+len+i := by omega
        have hp2 : blk*(256>>>n)+len+i < blk*(256>>>n)+(256>>>n) := by rw [hL2]; omega
        rw [hstage, bhi blk hblk (blk*(256>>>n)+len+i) hp1 hp2]
        rw [cast_subQ _ _ (by have := mulModQ_lt (zetaTwiddle ((nttUpto n w).2 + blk + 1)) a_in[blk*(256>>>n)+len+i]!; omega),
            cast_mulModQ, htw blk, cast_zetaTwiddle]
        have e1 : (a_in[blk*(256>>>n)+len+i-len]! : ZMod q)
            = ∑ v ∈ range (2^n), (w[i + v*(256>>>n)]! : ZMod q) * (rootAt n blk)^v := by
          rw [show blk*(256>>>n)+len+i-len = blk*(256>>>n)+i from by omega]
          have := ihform blk i hblk (by rw [hL2]; omega); rw [haindef]; exact this
        have e2 : (a_in[blk*(256>>>n)+len+i]! : ZMod q)
            = ∑ v ∈ range (2^n), (w[(i+len) + v*(256>>>n)]! : ZMod q) * (rootAt n blk)^v := by
          have := ihform blk (i+len) hblk (by rw [hL2]; omega)
          rw [haindef, show blk*(256>>>n)+len+i = blk*(256>>>n)+(i+len) from by ring]
          exact this
        rw [e1, e2]
        have hr : rootAt (n+1) (2*blk+1) = -(zeta:ZMod q)^(brv8 (2^n+blk)) := rootAt_odd_step n blk
        have hrho : rootAt n blk = (-(zeta:ZMod q)^(brv8 (2^n+blk)))^2 := by
          rw [rootAt_closed n blk hn7 hblk, neg_pow, ← pow_mul]; ring_nf
        rw [hr, hpow2, split_collapse len (256>>>n) n i hL2 _ w, ← hrho]
        ring

/-- **CT STAGE-INVARIANT COLLAPSE (forward, size-256).** The 8-stage Cooley–Tukey butterfly network computes
evaluation at the negacyclic roots `ζ^{2·brv(m)+1}` for every canonical (size-256) poly: `(ntt a)_m =
eval256 a (evalRoot m)`. This is the size-256-guarded form of `NttEvalsAtRoots` (the unguarded `∀`-form is
false — see the note above). Axiom-clean, no `native_decide`. -/
theorem nttEvalsAtRoots_canonical (a : Poly) (ha : a.size = 256) (m : Nat) (hm : m < 256) :
    ((ntt a)[m]! : ZMod q) = eval256 a (evalRoot m) := by
  obtain ⟨_, _, hform⟩ := stage_inv a ha 8 (by omega)
  have hm8 : m < 2^8 := by rw [show (2:Nat)^8 = 256 from by norm_num]; exact hm
  have h := hform m 0 hm8 (by decide)
  rw [show (256 >>> 8) = 1 from by decide] at h
  rw [show (2:Nat)^8 = 256 from by norm_num] at h
  simp only [Nat.mul_one, Nat.add_zero, Nat.zero_add] at h
  rw [ntt_eq_fold, nttFold_eq, h, rootAt_final m hm]
  rfl

/-! ### RUNG 2, step 3 — `NttMulHom` CLOSED: eval-at-a-negacyclic-root is multiplicative, so `ntt` is a
genuine ring homomorphism (size-256-guarded).

The forward transform sends coefficients to evaluations at the negacyclic roots (`nttEvalsAtRoots_canonical`).
For a root `r` with `r²⁵⁶ = −1` (every `evalRoot m`, by `evalRoot_pow256`), evaluation is MULTIPLICATIVE on the
negacyclic ring: the convolution `∑_{i+j=m} − ∑_{i+j=m+256}` (`schoolbookMul_getElem`) collapses — each pair
`(i,j)` contributes `a_i·b_j·r^{i+j}` whether it lands below 256 (direct) or wraps (`r^{i+j} = −r^{i+j−256}`
cancels the sign), giving `eval(a·b, r) = eval(a,r)·eval(b,r)`. Since the pointwise ring is coordinatewise `ℤ_q`
(`cast_pointwiseMul`), both sides of `NttMulHom` agree at every slot in `ℤ_q`; a reduced-range (`< q`)
injectivity argument lifts that to the `Array`-level equality. No `native_decide`. -/

/-- Eval-at-a-fixed-root of one coefficient pair's contribution: `∑_m cJ(i,j,m)·r^m = a_i·b_j·r^{i+j}` — the
single nonzero term, with the negacyclic wrap absorbed by `r²⁵⁶ = −1`. -/
theorem inner_eval (a b : Poly) (r : ZMod q) (hr : r^256 = -1) (i j : Nat)
    (hi : i < 256) (hj : j < 256) :
    ∑ m ∈ range 256, cJ a b i j m * r^m
      = ((a[i]! : Nat) : ZMod q) * ((b[j]! : Nat) : ZMod q) * r^(i+j) := by
  by_cases hk : i + j < 256
  · rw [Finset.sum_eq_single (i+j)]
    · have : cJ a b i j (i+j) = ((a[i]! : Nat) : ZMod q) * ((b[j]! : Nat) : ZMod q) := by
        unfold cJ; rw [if_pos rfl]
      rw [this]
    · intro m hmem hm
      have hmlt : m < 256 := mem_range.mp hmem
      have : cJ a b i j m = 0 := by unfold cJ; rw [if_neg (by omega), if_neg (by omega)]
      rw [this, zero_mul]
    · intro hmem; exact absurd (mem_range.mpr hk) hmem
  · have hge : 256 ≤ i + j := by omega
    set m0 := i + j - 256 with hm0
    have hm0lt : m0 < 256 := by omega
    rw [Finset.sum_eq_single m0]
    · have hcj : cJ a b i j m0 = -(((a[i]! : Nat) : ZMod q) * ((b[j]! : Nat) : ZMod q)) := by
        unfold cJ; rw [if_neg (by omega), if_pos (by omega)]
      rw [hcj]
      have hrij : r^(i+j) = -(r^m0) := by
        have : i + j = m0 + 256 := by omega
        rw [this, pow_add, hr]; ring
      rw [hrij]; ring
    · intro m hmem hm
      have hmlt : m < 256 := mem_range.mp hmem
      have : cJ a b i j m = 0 := by unfold cJ; rw [if_neg (by omega), if_neg (by omega)]
      rw [this, zero_mul]
    · intro hmem; exact absurd (mem_range.mpr hm0lt) hmem

/-- **Eval-at-a-negacyclic-root is a ring homomorphism.** For `r²⁵⁶ = −1`,
`eval256 (schoolbookMul a b) r = eval256 a r · eval256 b r`. The diagonalization heart of `NttMulHom`. -/
theorem eval256_schoolbook (a b : Poly) (r : ZMod q) (hr : r^256 = -1) :
    eval256 (schoolbookMul a b) r = eval256 a r * eval256 b r := by
  have claim2 : eval256 a r * eval256 b r
      = ∑ i ∈ range 256, ∑ j ∈ range 256,
          ((a[i]! : Nat) : ZMod q) * ((b[j]! : Nat) : ZMod q) * r^(i+j) := by
    unfold eval256
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [pow_add]; ring
  rw [claim2]
  unfold eval256
  rw [Finset.sum_congr rfl (fun m hm => by
    rw [schoolbookMul_getElem a b m (mem_range.mp hm)])]
  rw [Finset.sum_congr rfl (fun m _ => by
    rw [Finset.sum_mul, Finset.sum_congr rfl (fun i _ => Finset.sum_mul _ _ _)])]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j hj
  exact inner_eval a b r hr i j (mem_range.mp hi) (mem_range.mp hj)

/-! Reduced-range (`< q`) invariant for `ntt`'s output — every butterfly write is `addQ`/`subQ`/`mulModQ`, so
the transform threads "all entries `< q`" from a reduced input. Needed to lift the `ℤ_q`-level agreement of the
two `NttMulHom` sides to a `Nat`-`Array` equality (via `Nat`-cast injectivity on `[0, q)`). -/

theorem bfStepC_lt (z len : Nat) (b : Poly) (j : Nat) (hb : ∀ (p:Nat), b[p]! < q) :
    ∀ (p:Nat), (bfStepC z len b j)[p]! < q := by
  unfold bfStepC
  exact set!_lt _ _ _ (set!_lt _ _ _ hb (subQ_lt _ _)) (addQ_lt _ _)

theorem foldl_bfStepC_lt (z len : Nat) :
    ∀ (L : List Nat) (b : Poly), (∀ (p:Nat), b[p]!<q) →
      ∀ (p:Nat), (List.foldl (bfStepC z len) b L)[p]! < q := by
  intro L; induction L with
  | nil => intro b hb p; simpa using hb p
  | cons hd tl ih => intro b hb; exact ih _ (bfStepC_lt z len b hd hb)

theorem bfSweep_lt (z start len : Nat) (hlen : 1 ≤ len) (a0 : Poly) (h : ∀ (p:Nat), a0[p]!<q) :
    ∀ (p:Nat), (bfSweep z start len a0)[p]! < q := by
  rw [bfSweep_eq_foldl z start len hlen a0]; exact foldl_bfStepC_lt z len _ a0 h

theorem foldl_blockFn_lt (s : Nat) (hs : s ≤ 7) :
    ∀ (L : List Nat) (st : Poly × Nat), (∀ (p:Nat), st.1[p]!<q) →
      ∀ (p:Nat), (List.foldl (blockFn s) st L).1[p]! < q := by
  intro L; induction L with
  | nil => intro st hst p; simpa using hst p
  | cons hd tl ih =>
    intro st hst
    exact ih (blockFn s st hd) (fun p => by
      unfold blockFn; exact bfSweep_lt _ _ _ (len_pos s hs) st.1 hst p)

theorem stageStep_lt (s : Nat) (hs : s ≤ 7) (st : Poly × Nat) (hst : ∀ (p:Nat), st.1[p]!<q) :
    ∀ (p:Nat), (stageStep s st).1[p]! < q := by
  unfold stageStep; exact foldl_blockFn_lt s hs _ st hst

theorem nttUpto_lt (w : Poly) (hw : ∀ (p:Nat), w[p]!<q) :
    ∀ n, n ≤ 8 → ∀ (p:Nat), (nttUpto n w).1[p]! < q := by
  intro n
  induction n with
  | zero => intro _ p; simpa [nttUpto] using hw p
  | succ n ih =>
    intro hn p
    rw [nttUpto_succ]
    exact stageStep_lt n (by omega) (nttUpto n w) (fun p => ih (by omega) p) p

/-- Every coefficient of `ntt w` is reduced (`< q`) when the input is. -/
theorem ntt_lt (w : Poly) (hw : ∀ (p:Nat), w[p]!<q) : ∀ (p:Nat), (ntt w)[p]! < q := by
  intro p; rw [ntt_eq_fold, nttFold_eq]; exact nttUpto_lt w hw 8 (by omega) p

/-- `ntt` preserves the 256-coefficient length (a corollary of `stage_inv`). -/
theorem ntt_size (w : Poly) (hw : w.size = 256) : (ntt w).size = 256 := by
  rw [ntt_eq_fold, nttFold_eq]; exact (stage_inv w hw 8 (by omega)).1

/-- `Nat`-cast into `ℤ_q` is injective on the reduced range `[0, q)`. -/
theorem natCast_inj_of_lt (x y : Nat) (hx : x < q) (hy : y < q)
    (h : ((x:Nat):ZMod q) = ((y:Nat):ZMod q)) : x = y := by
  rw [← ZMod.val_natCast_of_lt hx, ← ZMod.val_natCast_of_lt hy, h]

/-- Entrywise `NttMulHom`: `(ntt (a·b))_m = (ntt a ⊙ ntt b)_m` at every canonical slot, via the `ℤ_q`
diagonalization + reduced-range injectivity. -/
theorem nttMul_entry (a b : Poly) (ha : a.size = 256) (hb : b.size = 256) (m : Nat) (hm : m < 256) :
    (ntt (schoolbookMul a b))[m]! = (pointwiseMul (ntt a) (ntt b))[m]! := by
  have hsab : (schoolbookMul a b).size = 256 := schoolbookMul_size a b
  have hX : (ntt (schoolbookMul a b))[m]! < q := ntt_lt _ (schoolbookMul_lt a b) m
  have hY : (pointwiseMul (ntt a) (ntt b))[m]! < q := by
    rw [pointwiseMul_getElem _ _ m hm]; exact mulModQ_lt _ _
  apply natCast_inj_of_lt _ _ hX hY
  rw [nttEvalsAtRoots_canonical (schoolbookMul a b) hsab m hm,
      eval256_schoolbook a b (evalRoot m) (evalRoot_pow256 m),
      cast_pointwiseMul (ntt a) (ntt b) m hm,
      nttEvalsAtRoots_canonical a ha m hm, nttEvalsAtRoots_canonical b hb m hm]

/-- **`NttMulHom` CLOSED (size-256-guarded).** `ntt (schoolbookMul a b) = pointwiseMul (ntt a) (ntt b)` for all
canonical `a, b` — the NTT is a proven ring homomorphism from the negacyclic ring to the pointwise-product ring,
for-all, no `native_decide`. -/
theorem nttMulHom_guarded (a b : Poly) (ha : a.size = 256) (hb : b.size = 256) :
    ntt (schoolbookMul a b) = pointwiseMul (ntt a) (ntt b) := by
  have hsab : (schoolbookMul a b).size = 256 := schoolbookMul_size a b
  apply Array.ext
  · rw [ntt_size _ hsab, pointwiseMul_size]
  · intro m h1 _
    have hm : m < 256 := by rw [ntt_size _ hsab] at h1; exact h1
    rw [(getElem!_pos (ntt (schoolbookMul a b)) m (by rw [ntt_size _ hsab]; exact hm)).symm,
        (getElem!_pos (pointwiseMul (ntt a) (ntt b)) m (by rw [pointwiseMul_size]; exact hm)).symm]
    exact nttMul_entry a b ha hb m hm

/-- `NttMulHom` (the guarded `Prop`) is discharged. -/
theorem nttMulHom_proven : NttMulHom := fun a b ha hb => nttMulHom_guarded a b ha hb

/-- **`RingRepFaithful` reduced to the SINGLE `NttLeftInverse` residual.** With `NttMulHom` closed, the whole
NTT-faithfulness bridge behind `verifyCore = spec` now rests on exactly one open leg: `intt ∘ ntt = id` on
canonical polys (the `intt` interpolation induction, mirror of `stage_inv`). -/
theorem ringRepFaithful_of_leftInverse (hInv : NttLeftInverse) :
    Dregg2.Crypto.VerifyCoreSpec.RingRepFaithful :=
  ringRepFaithful_of hInv nttMulHom_proven

/-! ## Axiom gate on the new keystones (⊆ {propext, Classical.choice, Quot.sound}).
Every rung climbed is checked clean; `zeta_root_witness`'s `ofReduceBool` (the concrete ζ=1753 pin) is
deliberately NOT gated here — it is the accepted computational residual, isolated from the ∀-theorems. -/
#assert_axioms cast_addQ
#assert_axioms cast_subQ
#assert_axioms cast_mulModQ
#assert_axioms cast_addPoly
#assert_axioms cast_subPoly
#assert_axioms cast_pointwiseMul
#assert_axioms omega_orthogonality
#assert_axioms orderOf_zeta
#assert_axioms bfFold_spec
#assert_axioms bfSweep_getElem
#assert_axioms cast_bfSweep
#assert_axioms ntt_eq_fold
#assert_axioms cast_powModQ
#assert_axioms cast_zetaTwiddle
#assert_axioms brv_even
#assert_axioms rootAt_closed
#assert_axioms rootAt_final
#assert_axioms block_char
#assert_axioms stage_inv
#assert_axioms nttEvalsAtRoots_canonical
#assert_axioms schoolbookMul_getElem
#assert_axioms schoolbookMul_size
#assert_axioms schoolbookMul_lt
#assert_axioms eval256_schoolbook
#assert_axioms ntt_lt
#assert_axioms nttMulHom_guarded
#assert_axioms nttMulHom_proven
#assert_axioms ringRepFaithful_of
#assert_axioms ringRepFaithful_of_leftInverse

end Dregg2.Crypto.MlDsaRing
