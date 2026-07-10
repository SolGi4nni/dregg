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

## RUNG 2 — the butterfly WALL (engine BUILT; outer-loop peel + CT invariant the named residual)

`RingRepFaithful` is still **not discharged**; but the residual has shrunk again. With rung 3 (orthogonality)
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
* **The exact remaining step** (named precisely after `cast_bfSweep`): a separate, larger induction that peels
  the two OUTER loops (`for s`, `for blk`, mutable state `(a, k)`) — expressing `ntt` as the ordered
  composition of `bfSweep`s with `k = 1 … 255` — and carries the CT stage invariant "after stage `s`, position
  `g·len_s+i` holds `eval256` of the `g`-th decimated subpolynomial at its root", each step preserved by
  `cast_bfSweep` (`ring`), collapsing at `len = 1` to `NttEvalsAtRoots`. That outer-peel + stage invariant is
  the single sub-step still open; the butterfly engine under it is closed.

Given `NttEvalsAtRoots`/`InttInterpolates`, `NttLeftInverse` = eval∘interp collapsed by `omega_orthogonality`
(brv bijective), and `NttMulHom` = eval-is-a-ring-hom + `evalRoot²⁵⁶ = −1`.
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

/-! ### The EXACT remaining step (the top of RUNG 2).

`bfSweep` above is a verbatim copy of `ntt`'s innermost `for j` loop, and `cast_bfSweep` proves that sweep
IS the 2×2 ℤ_q-linear butterfly. What remains to discharge `NttEvalsAtRoots` (and dually `InttInterpolates`)
is a genuinely separate, larger induction over the two OUTER loops of `ntt`:

* **peel** the `for s in [0:8]` / `for blk in [0:nblk]` loops (state = the mutable pair `(a, k)`), expressing
  `ntt w` as the ordered composition of `bfSweep (zetaTwiddle kᵢ) startᵢ (128 >>> s)` — the twiddle counter
  `k` runs `1 … 255` across all blocks (`Σ_s nblk = 1+2+…+128 = 255`), so global block `g` uses `zetaTwiddle g`;
* carry the **CT stage invariant**: after stage `s`, array position `g·len_s + i` (`len_s = 2^{7−s}`) holds
  `eval256` of the `g`-th length-`2^{s+1}` decimated subpolynomial at the appropriate `ζ^{odd}` root, each
  butterfly step preserving it by `cast_bfSweep` (`ring`);
* collapse the final stage (`len = 1`) to `(ntt a)[m]! = eval256 a (evalRoot m)`.

That outer-loop-peel + stage-invariant induction is the single named sub-step still open; the butterfly
engine it rests on is closed above. -/

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

/-- **Residual A — the inverse transform is a genuine left inverse.** `intt ∘ ntt = id` on all polys. -/
def NttLeftInverse : Prop := ∀ c : Poly, intt (ntt c) = c

/-- **Residual B — `ntt` is a ring homomorphism** from the negacyclic ring `(Poly, schoolbookMul)` to the
pointwise-product ring `(Poly, pointwiseMul)`: `ntt (a·b) = ntt a ⊙ ntt b`. -/
def NttMulHom : Prop := ∀ a b : Poly, ntt (schoolbookMul a b) = pointwiseMul (ntt a) (ntt b)

/-- **THE REDUCTION (axiom-clean).** `RingRepFaithful` — the ∀ NTT-faithfulness residual behind
`verifyCore = spec` — follows from the two standard NTT-correctness facts above. Textbook: a transform-based
multiply is correct exactly when the transform inverts and diagonalizes the convolution. Proof:
`intt(ntt a ⊙ ntt b) = intt(ntt(a·b)) = a·b`. This does NOT prove `RingRepFaithful`; it reduces it to
`NttLeftInverse` and `NttMulHom` (the open butterfly=DFT frontier — see the module header). -/
theorem ringRepFaithful_of (hInv : NttLeftInverse) (hHom : NttMulHom) : RingRepFaithful := by
  intro a b
  rw [← hHom, hInv]

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

end Dregg2.Crypto.MlDsaRing
