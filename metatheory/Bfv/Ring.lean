/-
# Bfv.Ring — the noise model on the ACTUAL ring `R = ℤ[X]/(X^N+1)`.

**The gap this module closes.** `Bfv.Noise` models a ciphertext's phase as a SINGLE integer
(`Bfv.Ct.phase : ℤ`) and says so: "the lift to n = 4096 polynomial coefficients is NOT formalized —
that correspondence is a NAMED model gap". `Bfv.Mul` names the same gap harder: "the ring lift is
MISSING and multiplication makes it load-bearing … the lift itself (`‖a·b‖_∞ ≤ n·‖a‖_∞·‖b‖_∞` over
`R_q = Z_q[X]/(X^n+1)`) is Phase-2." This module IS that lift, for the additive/public-linear path.

## Which noise model is formalized here — say it plainly

**The WORST-CASE COEFFICIENT (ℓ∞) model, and only that.** Every bound below is a statement about
`max_k |coefficient k|` that holds for EVERY input, with no distributional hypothesis.

**The average-case / heuristic model is DELIBERATELY NOT FORMALIZED.** The commonly quoted ring
expansion factor `δ_R ≈ 2√N` is an *experimental* constant — HEIR's own source annotates it as an
"experimental result", and Gao–Zheng (2025/1036) attack exactly that heuristic for BFV's dependent
products. It is not a theorem and nothing here pretends it is one. What is proved here is the
provable constant, `δ_R = N` (`negaMul_normInf_le`) — and `negaMul_expansion_attained` proves that
constant is EXACTLY ATTAINED, so `δ_R = N` is not a lazy over-estimate either: it is tight.

## The carrier

`Rn N = Fin N → ℤ` — an element of `ℤ[X]/(X^N+1)` in its DEPLOYED representation, the `N`
coefficients. Integer coefficients, not `ZMod q`, for the same reason `Bfv.Noise` works in `ℤ`: the
noise analysis is an exact-integer argument and the mod-`q` correspondence is handled separately
(`Bfv.Noise.decryptPhase_add_q`, which now applies coefficientwise — the wrap argument is
per-coefficient and unchanged by this lift).

`negaMul` is NOT postulated to be the ring product; it is PROVED to be one. `negaMul_toPoly_dvd`
and `toPoly_negaMul_quotient` show the coefficient map `toPoly` carries `negaMul` to genuine
multiplication in Mathlib's `Polynomial ℤ ⧸ (X^N+1)`. Without that, `‖negaMul a b‖ ≤ N‖a‖‖b‖`
would be a theorem about an arbitrary bilinear operation wearing a ring's name.

## What is proved

  1. **`negaMul_toPoly_dvd` / `toPoly_negaMul_quotient` (THE ANCHOR)** — `negaMul` is multiplication
     in `ℤ[X]/(X^N+1)`. `toPoly_add` does the same for `+`, discharging the "additions are
     coefficient-wise, so every statement lifts pointwise" claim `Bfv.Noise` left unformalized.
  2. **`negaMul_normInf_le` (THE ONE NEW RING FACT)** — `‖a·b‖_∞ ≤ N·‖a‖_∞·‖b‖_∞`. The provable
     worst-case expansion, `δ_R = N`.
  3. **`negaMul_expansion_attained` (TEETH, general in N)** — with `a = b = 1 + X + ⋯ + X^(N−1)`
     (so `‖a‖_∞ = ‖b‖_∞ = 1`), the `(N−1)`-th coefficient of `a·b` is EXACTLY `N`. The bound is
     attained at every degree, so no constant below `N` is sound;
     `negaMul_expansion_not_below_N` states that as a refutation.
  4. **THE PORT.** `matVecRCt` / `RowBound` / `stepR_noise_le` / `iterR_noise_le` — the
     `Bfv.Noise` public-linear-step theorems on the ring carrier. `RowBound` is not re-stated: this
     module IMPORTS and reuses `Bfv.RowBound` verbatim, because the row-sum hypothesis is about the
     integer matrix `S` and the carrier change does not touch it. **The row-sum bound survives with
     NO ring expansion factor** (`stepR_noise_le` concludes `G·M`, not `N·G·M`) — this is the
     coefficient-encoded / LZ–Bae matmul route's noise statement, and the reason that route is the
     one that closes under a bound we can prove.
  5. **`scalarMul_noise_le` vs `negaMul_normInf_le` (the price of a polynomial multiplier)** — an
     INTEGER scalar multiplier costs `|c|`; a PLAINTEXT-POLYNOMIAL multiplier costs `N·‖p‖_∞`.
     `polyStep_costs_expansion` pins the gap at the deployed `N = 4096`.
  6. **`stepR_rowBound_necessary` (TEETH)** — drop the row bound and the step conclusion is FALSE.
     The hypothesis is a constraint, not decoration.

## What is NOT claimed

  * Nothing here says the deployed Rust enforces any of this; these are the theorems the emitted
    constants would make enforceable, as everywhere in `Bfv/`.
  * `negaMul` is proved to be the ring product; it is NOT proved to be a `CommRing` instance
    (associativity/commutativity are inherited facts about the quotient, not re-proved here).
  * The mod-`q` reduction is still the named `Bfv.Noise` correspondence, now read coefficientwise.
    Ring MULTIPLICATION of two CIPHERTEXTS is `Bfv.Mul`'s scalar model still — this module lifts
    the additive/public-linear path and the plaintext-multiplier expansion factor, not the
    ct×ct tensor step.
  * Lattice security (class B) is not a Lean theorem here or anywhere in `Bfv/`.

Pure. No axioms beyond the kernel triple.
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Bfv.Params
import Bfv.Noise

namespace Bfv

open Finset

/-! ## 1. The carrier: `R = ℤ[X]/(X^N+1)` in coefficients, and its ∞-norm. -/

/-- An element of the negacyclic ring `R = ℤ[X]/(X^N+1)`, in the representation the deployed
library actually stores: its `N` integer coefficients. This is the carrier that replaces
`Bfv.Ct`'s single `phase : ℤ`. -/
abbrev Rn (N : ℕ) : Type := Fin N → ℤ

/-- **The ∞-norm bound on coefficients, as a predicate:** `NormInfLE a B` is `‖a‖_∞ ≤ B`.

Stated as a predicate rather than a `sup`-valued function for the same reason `Bfv.RowBound` is a
predicate: it keeps every ported statement in the shape `bound ≤ bound`, needs no nonemptiness
side-condition, and is decidable at concrete `N`. -/
def NormInfLE {N : ℕ} (a : Rn N) (B : ℤ) : Prop := ∀ k, |a k| ≤ B

/-- **Negacyclic convolution — the product of `ℤ[X]/(X^N+1)` written on coefficients.**

Coefficient `k` collects every pair `(i, j)` with `i + j ≡ k (mod N)`, with the sign that
`X^N = −1` forces: `+` when `i + j = k` (no wrap) and `−` when `i + j = k + N` (one wrap). Writing
`j = k − i` in `Fin N` makes the wrap test exactly `i ≤ k`.

This is a DEFINITION, not a postulate: `negaMul_toPoly_dvd` proves it agrees with genuine
polynomial multiplication modulo `X^N+1`. -/
def negaMul {N : ℕ} (a b : Rn N) : Rn N :=
  fun k => ∑ i : Fin N, (if (i : ℕ) ≤ (k : ℕ) then a i * b (k - i) else -(a i * b (k - i)))

/-! ## 2. THE ANCHOR: `negaMul` really is multiplication in `ℤ[X]/(X^N+1)`. -/

/-- The polynomial with these coefficients, `∑ᵢ aᵢ·Xⁱ` (degree `< N` by construction). -/
noncomputable def toPoly {N : ℕ} (a : Rn N) : Polynomial ℤ :=
  ∑ i : Fin N, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)

/-- **`toPoly` IS FAITHFUL — read the carrier before the conclusion.** It returns exactly the
coefficients it was handed. Without this, the anchor theorems below would be statements about a
possibly-degenerate embedding (the classic identity-carrier vacuity: a "binding" discharged over
a map that throws its argument away). With it, `toPoly` is injective (`toPoly_injective`) and the
anchor genuinely transports `negaMul` into `Polynomial ℤ`. -/
theorem toPoly_coeff {N : ℕ} (a : Rn N) (i : Fin N) : (toPoly a).coeff (i : ℕ) = a i := by
  unfold toPoly
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun h => hj (Fin.val_injective h).symm), mul_zero]
  · simp

/-- The coefficient map is injective — `Rn N` really does sit inside `Polynomial ℤ`. -/
theorem toPoly_injective {N : ℕ} : Function.Injective (toPoly (N := N)) := by
  intro a b hab
  funext i
  rw [← toPoly_coeff a i, ← toPoly_coeff b i, hab]

/-- **Coefficientwise addition IS polynomial addition.** This discharges, for the ring carrier,
the correspondence `Bfv.Noise`'s module doc names and leaves unformalized ("homomorphic addition
is coefficient-wise, so every statement here lifts pointwise. The lift is NOT formalized"). -/
theorem toPoly_add {N : ℕ} (a b : Rn N) : toPoly (a + b) = toPoly a + toPoly b := by
  unfold toPoly
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Pi.add_apply, add_mul]

/-- `X^s` reduced negacyclically: `X^s` when `s < N`, and `−X^(s−N)` when `N ≤ s` (the `X^N = −1`
rewrite). Only used for `s < 2N`, which is all a product of two degree-`<N` elements produces. -/
noncomputable def negaX (N s : ℕ) : Polynomial ℤ :=
  if s < N then Polynomial.X ^ s else -(Polynomial.X ^ (s - N))

/-- The single ring fact `X^N = −1` in divisibility form: reducing `X^s` negacyclically changes it
by a multiple of `X^N + 1`. -/
theorem negaX_dvd (N s : ℕ) :
    (Polynomial.X ^ N + 1 : Polynomial ℤ) ∣ (Polynomial.X ^ s - negaX N s) := by
  unfold negaX
  split
  · simp
  · refine ⟨Polynomial.X ^ (s - N), ?_⟩
    have hs : s - N + N = s := by omega
    rw [sub_neg_eq_add, add_mul, one_mul, ← pow_add, Nat.add_comm N (s - N), hs]

/-- The product of two `toPoly`s, expanded over index PAIRS. -/
theorem toPoly_mul_expand {N : ℕ} (a b : Rn N) :
    toPoly a * toPoly b
      = ∑ i : Fin N, ∑ j : Fin N,
          Polynomial.C (a i * b j) * Polynomial.X ^ ((i : ℕ) + (j : ℕ)) := by
  unfold toPoly
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.C_mul, pow_add]
  ring

/-- `negaMul`, expanded over the SAME index pairs as `toPoly_mul_expand`, with each `X^(i+j)`
replaced by its negacyclic reduction. This is the reindexing step: `k := j + i` in `Fin N`. -/
theorem toPoly_negaMul_expand {N : ℕ} [NeZero N] (a b : Rn N) :
    toPoly (negaMul a b)
      = ∑ i : Fin N, ∑ j : Fin N,
          Polynomial.C (a i * b j) * negaX N ((i : ℕ) + (j : ℕ)) := by
  unfold toPoly negaMul
  -- push `C` through the inner sum, then swap the `k` and `i` sums
  have h1 : ∀ k : Fin N,
      Polynomial.C (∑ i : Fin N, (if (i : ℕ) ≤ (k : ℕ) then a i * b (k - i)
        else -(a i * b (k - i)))) * Polynomial.X ^ (k : ℕ)
        = ∑ i : Fin N, Polynomial.C (if (i : ℕ) ≤ (k : ℕ) then a i * b (k - i)
            else -(a i * b (k - i))) * Polynomial.X ^ (k : ℕ) := by
    intro k
    rw [map_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- reindex `k ↦ j` by `k = j + i`
  rw [← Equiv.sum_comp (Equiv.addRight i) (fun k : Fin N =>
    Polynomial.C (if (i : ℕ) ≤ (k : ℕ) then a i * b (k - i) else -(a i * b (k - i)))
      * Polynomial.X ^ (k : ℕ))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hi : (i : ℕ) < N := i.isLt
  have hj : (j : ℕ) < N := j.isLt
  have hcancel : (j + i : Fin N) - i = j := add_sub_cancel_right j i
  have hval : ((j + i : Fin N) : ℕ) = ((j : ℕ) + (i : ℕ)) % N := Fin.val_add j i
  simp only [Equiv.coe_addRight, hcancel, hval, negaX]
  by_cases hlt : (i : ℕ) + (j : ℕ) < N
  · have hmod : ((j : ℕ) + (i : ℕ)) % N = (i : ℕ) + (j : ℕ) := by
      rw [Nat.add_comm]; exact Nat.mod_eq_of_lt hlt
    rw [hmod, if_pos (by omega), if_pos hlt]
  · have hmod : ((j : ℕ) + (i : ℕ)) % N = (i : ℕ) + (j : ℕ) - N := by
      have : (j : ℕ) + (i : ℕ) - N < N := by omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt this]
      omega
    rw [hmod, if_neg (by omega), if_neg hlt]
    simp

/-- **THE ANCHOR:** the coefficient map carries `negaMul` to genuine polynomial multiplication,
modulo `X^N + 1`. This is what makes `Rn N` the ring `ℤ[X]/(X^N+1)` rather than a vector space
carrying an operation that has been NAMED a product. -/
theorem negaMul_toPoly_dvd {N : ℕ} [NeZero N] (a b : Rn N) :
    (Polynomial.X ^ N + 1 : Polynomial ℤ) ∣ (toPoly a * toPoly b - toPoly (negaMul a b)) := by
  rw [toPoly_mul_expand, toPoly_negaMul_expand, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun j _ => ?_
  rw [← mul_sub]
  exact Dvd.dvd.mul_left (negaX_dvd N _) _

/-- **The anchor, in the quotient ring:** `toPoly` descends to `ℤ[X] ⧸ (X^N+1)` and is
multiplicative there — `negaMul` IS the product of `ℤ[X]/(X^N+1)`. -/
theorem toPoly_negaMul_quotient {N : ℕ} [NeZero N] (a b : Rn N) :
    (Ideal.Quotient.mk (Ideal.span {(Polynomial.X ^ N + 1 : Polynomial ℤ)})) (toPoly (negaMul a b))
      = (Ideal.Quotient.mk (Ideal.span {(Polynomial.X ^ N + 1 : Polynomial ℤ)})) (toPoly a)
        * (Ideal.Quotient.mk (Ideal.span {(Polynomial.X ^ N + 1 : Polynomial ℤ)})) (toPoly b) := by
  rw [← map_mul]
  exact (Ideal.Quotient.eq.mpr
    (Ideal.mem_span_singleton.mpr (negaMul_toPoly_dvd a b))).symm

/-- **The wrap is REAL and it is SIGNED:** at `N = 2`, `X · X = X² = −1`. Both inputs are
nonnegative and the product has a NEGATIVE coefficient — the negacyclic signature (an ordinary
cyclic convolution would give `+1` here). This is why every bound in this module is an
absolute-value bound and none of them may be replaced by a sign-preserving argument. -/
theorem negaMul_wraps_signed :
    negaMul (fun i : Fin 2 => if i = 1 then (1 : ℤ) else 0)
            (fun i : Fin 2 => if i = 1 then (1 : ℤ) else 0) 0 = -1 := by
  decide

/-- **The scalar model is THIS model at `N = 1`.** `ℤ[X]/(X+1) ≅ ℤ`, and `negaMul` there is
ordinary integer multiplication — so `Bfv.Noise`'s `Ct.phase : ℤ` is the `N = 1` slice of `RCt`,
and the expansion factor `δ_R = N` degenerates to `1` exactly where the scalar model has none.
The two files agree; this one strictly refines the other. -/
theorem negaMul_one_eq_mul (a b : Rn 1) (k : Fin 1) : negaMul a b k = a 0 * b 0 := by
  have hk : k = 0 := Subsingleton.elim _ _
  subst hk
  simp [negaMul]

#assert_all_clean [Bfv.toPoly_coeff, Bfv.toPoly_injective, Bfv.toPoly_add,
  Bfv.negaX_dvd, Bfv.toPoly_mul_expand,
  Bfv.toPoly_negaMul_expand, Bfv.negaMul_toPoly_dvd, Bfv.toPoly_negaMul_quotient,
  Bfv.negaMul_wraps_signed, Bfv.negaMul_one_eq_mul]

/-! ## 3. THE ONE NEW RING FACT: the provable worst-case expansion `δ_R = N`. -/

/-- **`‖a·b‖_∞ ≤ N·‖a‖_∞·‖b‖_∞` — the provable ring expansion factor, `δ_R = N`.**

This is the WORST-CASE coefficient bound: it holds for every pair of ring elements, with no
distributional assumption. The heuristic `δ_R ≈ 2√N` that the literature usually quotes is an
experimental average-case constant (HEIR annotates its own source that way; Gao–Zheng 2025/1036
attack it for dependent BFV products) and is deliberately NOT formalized anywhere in this module.

Tightness is not left to the reader: `negaMul_expansion_attained` exhibits, at every `N`, inputs
of ∞-norm `1` whose product has a coefficient equal to `N`. -/
theorem negaMul_normInf_le {N : ℕ} {a b : Rn N} {A B : ℤ}
    (ha : NormInfLE a A) (hb : NormInfLE b B) (hA : 0 ≤ A) :
    NormInfLE (negaMul a b) ((N : ℤ) * A * B) := by
  intro k
  have hterm : ∀ i : Fin N,
      |(if (i : ℕ) ≤ (k : ℕ) then a i * b (k - i) else -(a i * b (k - i)))| ≤ A * B := by
    intro i
    have habs : |(if (i : ℕ) ≤ (k : ℕ) then a i * b (k - i) else -(a i * b (k - i)))|
        = |a i| * |b (k - i)| := by
      split <;> simp [abs_mul]
    rw [habs]
    exact mul_le_mul (ha i) (hb _) (abs_nonneg _) hA
  simp only [negaMul]
  calc |∑ i : Fin N, (if (i : ℕ) ≤ (k : ℕ) then a i * b (k - i) else -(a i * b (k - i)))|
      ≤ ∑ i : Fin N, |(if (i : ℕ) ≤ (k : ℕ) then a i * b (k - i) else -(a i * b (k - i)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, A * B := Finset.sum_le_sum fun i _ => hterm i
    _ = (N : ℤ) * A * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### Teeth: the expansion factor `N` is EXACTLY ATTAINED, at every degree. -/

/-- The all-ones ring element `1 + X + ⋯ + X^(N−1)`, whose ∞-norm is `1`. -/
def onesR (N : ℕ) : Rn N := fun _ => 1

theorem onesR_normInf (N : ℕ) : NormInfLE (onesR N) 1 := fun _ => by simp [onesR]

/-- **THE BOUND IS ATTAINED, for every `N`:** with `a = b = 1 + X + ⋯ + X^(N−1)` (∞-norm `1`
each), the top coefficient of `a·b` is exactly `N` — the full `N·1·1` the bound allows. `δ_R = N`
is therefore not a conservative over-estimate: no smaller constant is sound at ANY degree.

(At `k = N−1` every index `i` satisfies `i ≤ k`, so no term wraps and none is negated: all `N`
products contribute `+1`. This is the `X^(N-1) · 1` diagonal of the convolution.) -/
theorem negaMul_expansion_attained (N : ℕ) (hN : 0 < N) :
    negaMul (onesR N) (onesR N) ⟨N - 1, by omega⟩ = (N : ℤ) := by
  have hall : ∀ i : Fin N, (i : ℕ) ≤ N - 1 := fun i => by have := i.isLt; omega
  have hsum : negaMul (onesR N) (onesR N) ⟨N - 1, by omega⟩ = ∑ _i : Fin N, (1 : ℤ) := by
    simp only [negaMul, onesR]
    exact Finset.sum_congr rfl fun i _ => by rw [if_pos (hall i), mul_one]
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- The refutation side: `N` cannot be lowered. `N − 1` is NOT a sound expansion constant — the
witness of `negaMul_expansion_attained` breaks it. A bound with no failing side would be satisfied
by any over-estimate; this pins the constant from below. -/
theorem negaMul_expansion_not_below_N (N : ℕ) (hN : 0 < N) :
    ¬ NormInfLE (negaMul (onesR N) (onesR N)) ((N : ℤ) * 1 * 1 - 1) := by
  intro h
  have := h ⟨N - 1, by omega⟩
  rw [negaMul_expansion_attained N hN] at this
  rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ (N : ℤ))] at this
  omega

/-- The deployed pin: at the fhe.rs degree-4096 ring, the worst-case expansion is exactly
`δ_R = 4096`, attained. (This is the constant `Bfv.Mul`'s
`deployed_mul_margin_survives_ring_expansion` inflates its scalar bound by — now a theorem about
the ring, not a hedge.) -/
theorem deployed_expansion_attained :
    negaMul (onesR 4096) (onesR 4096) ⟨4095, by omega⟩ = (4096 : ℤ) := by
  simpa using negaMul_expansion_attained 4096 (by omega)

#assert_all_clean [Bfv.negaMul_normInf_le, Bfv.onesR_normInf, Bfv.negaMul_expansion_attained,
  Bfv.negaMul_expansion_not_below_N, Bfv.deployed_expansion_attained]

/-! ## 4. THE PORT: `Bfv.Noise`'s public-linear step, on the ring carrier.

Every statement below is its `Bfv.Noise` counterpart with `Ct` replaced by `RCt` and `|·| ≤ B`
replaced by `NormInfLE · B`. `RowBound` is NOT re-stated — `Bfv.RowBound` is imported and used
verbatim, because the row-sum hypothesis constrains the INTEGER matrix `S`, which the carrier
change does not touch. -/

/-- A model BFV ciphertext on the ring carrier: its exact phase, all `N` coefficients. The
`Bfv.Ct` of `Bfv.Noise` is this at `N = 1`. -/
structure RCt (P : Params) (N : ℕ) where
  /-- The exact phase of the ciphertext, as an element of `R = ℤ[X]/(X^N+1)`. -/
  phase : Rn N

/-- Noise relative to an intended message (itself a ring element): `phase − Δ·m`, coefficientwise.
The exact port of `Bfv.Ct.noiseAtInt`. -/
def RCt.noiseAtInt {P : Params} {N : ℕ} (c : RCt P N) (m : Rn N) : Rn N :=
  fun k => c.phase k - (P.Δ : ℤ) * m k

/-- One homomorphic public-linear step on a ciphertext VECTOR, ring carrier: component `i` of
`S·x` where `S` is a public INTEGER matrix acting coefficientwise. The exact port of
`Bfv.matVecCt`. -/
def matVecRCt {P : Params} {N n : ℕ} (S : Fin n → Fin n → ℤ) (x : Fin n → RCt P N) :
    Fin n → RCt P N :=
  fun i => ⟨fun k => ∑ j, S i j * (x j).phase k⟩

/-- The same linear step on the intended (clear) ring messages. Port of `Bfv.matVecMsg`. -/
def matVecMsgR {N n : ℕ} (S : Fin n → Fin n → ℤ) (m : Fin n → Rn N) : Fin n → Rn N :=
  fun i k => ∑ j, S i j * m j k

/-- The step's noise is the SAME linear map applied to the input noises — exact coefficient
algebra. Port of `Bfv.matVec_noiseAtInt`. -/
theorem matVecR_noiseAtInt {P : Params} {N n : ℕ} (S : Fin n → Fin n → ℤ)
    (x : Fin n → RCt P N) (m : Fin n → Rn N) (i : Fin n) (k : Fin N) :
    (matVecRCt S x i).noiseAtInt (matVecMsgR S m i) k
      = ∑ j, S i j * (x j).noiseAtInt (m j) k := by
  simp only [RCt.noiseAtInt, matVecRCt, matVecMsgR, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **THE ROW-SUM BOUND, ON THE RING, UNCHANGED: one step multiplies the noise bound by ≤ G.**

This is `Bfv.step_noise_le` with the carrier swapped and NOTHING ELSE — same `RowBound`
hypothesis (the imported definition, not a copy), same conclusion `G·M`. **No factor of `N`
appears**, because the step never uses ring multiplication: the multipliers `S i j` are public
integer scalars, which act coefficientwise. That is exactly the property the coefficient-encoded
(Cheetah §4.1 / LZ–Bae PC-MM) matmul route is built to have, and the reason it closes under a
bound that can be PROVED rather than one that is measured. -/
theorem stepR_noise_le {P : Params} {N n : ℕ} {S : Fin n → Fin n → ℤ} {G : ℤ}
    (hS : RowBound S G) {x : Fin n → RCt P N} {m : Fin n → Rn N} (M : ℤ) (hM : 0 ≤ M)
    (h : ∀ j, NormInfLE ((x j).noiseAtInt (m j)) M) (i : Fin n) :
    NormInfLE ((matVecRCt S x i).noiseAtInt (matVecMsgR S m i)) (G * M) := by
  intro k
  rw [matVecR_noiseAtInt]
  calc |∑ j, S i j * (x j).noiseAtInt (m j) k|
      ≤ ∑ j, |S i j * (x j).noiseAtInt (m j) k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |S i j| * |(x j).noiseAtInt (m j) k| := by simp only [abs_mul]
    _ ≤ ∑ j, |S i j| * M :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j k) (abs_nonneg _)
    _ = (∑ j, |S i j|) * M := (Finset.sum_mul _ _ _).symm
    _ ≤ G * M := mul_le_mul_of_nonneg_right (hS i) hM

/-- T iterations of the homomorphic linear step, ring carrier. Port of `Bfv.iterCt`. -/
def iterRCt {P : Params} {N n : ℕ} (S : Fin n → Fin n → ℤ) (T : ℕ) (x : Fin n → RCt P N) :
    Fin n → RCt P N :=
  (matVecRCt S)^[T] x

/-- T iterations on the clear ring messages. Port of `Bfv.iterMsg`. -/
def iterMsgR {N n : ℕ} (S : Fin n → Fin n → ℤ) (T : ℕ) (m : Fin n → Rn N) : Fin n → Rn N :=
  (matVecMsgR S)^[T] m

theorem iterRCt_succ {P : Params} {N n : ℕ} (S : Fin n → Fin n → ℤ) (T : ℕ)
    (x : Fin n → RCt P N) :
    iterRCt S (T + 1) x = matVecRCt S (iterRCt S T x) :=
  Function.iterate_succ_apply' _ _ _

theorem iterMsgR_succ {N n : ℕ} (S : Fin n → Fin n → ℤ) (T : ℕ) (m : Fin n → Rn N) :
    iterMsgR S (T + 1) m = matVecMsgR S (iterMsgR S T m) :=
  Function.iterate_succ_apply' _ _ _

/-- **THE COMPOUNDING LAW, ON THE RING:** T public-linear steps from noise `≤ M` leave every
component's ∞-norm `≤ G^T·M`. Port of `Bfv.iter_noise_le`, with the SAME `G^T` — the depth budget
`Bfv.Noise.iterCeiling` computes is therefore a statement about the actual ring, not about one
scalar coefficient, for the public-linear path. -/
theorem iterR_noise_le {P : Params} {N n : ℕ} {S : Fin n → Fin n → ℤ} {G M : ℤ}
    (hS : RowBound S G) (hG : 0 ≤ G) (hM : 0 ≤ M) {x : Fin n → RCt P N} {m : Fin n → Rn N}
    (h : ∀ j, NormInfLE ((x j).noiseAtInt (m j)) M) (T : ℕ) :
    ∀ i, NormInfLE ((iterRCt S T x i).noiseAtInt (iterMsgR S T m i)) (G ^ T * M) := by
  induction T with
  | zero => simpa [iterRCt, iterMsgR] using h
  | succ T ih =>
    intro i k
    rw [iterRCt_succ, iterMsgR_succ]
    have hstep := stepR_noise_le hS (G ^ T * M) (mul_nonneg (pow_nonneg hG T) hM) ih i k
    calc |(matVecRCt S (iterRCt S T x) i).noiseAtInt (matVecMsgR S (iterMsgR S T m) i) k|
        ≤ G * (G ^ T * M) := hstep
      _ = G ^ (T + 1) * M := by ring

/-! ### Teeth: the row bound is a CONSTRAINT, not decoration. -/

/-- **Drop the row bound and the step conclusion is FALSE.** One component, `S = (2)`, claimed
row bound `G = 1` (which `RowBound` refutes: `|2| > 1`), input noise `≤ 1` — the step's noise is
`2`, outside the `G·M = 1` the conclusion would assert. `stepR_noise_le`'s hypothesis is
load-bearing: a version without it proves something false. -/
theorem stepR_rowBound_necessary :
    ∃ (S : Fin 1 → Fin 1 → ℤ) (x : Fin 1 → RCt fheRs4096 4) (m : Fin 1 → Rn 4),
      ¬ RowBound S 1 ∧ (∀ j, NormInfLE ((x j).noiseAtInt (m j)) 1) ∧
      ¬ (∀ i, NormInfLE ((matVecRCt S x i).noiseAtInt (matVecMsgR S m i)) (1 * 1)) := by
  refine ⟨fun _ _ => 2, fun _ => ⟨fun _ => 1⟩, fun _ _ => 0, ?_, ?_, ?_⟩
  · intro hrow
    have := hrow 0
    simp at this
  · intro j k
    simp [RCt.noiseAtInt]
  · intro hcon
    have := hcon 0 0
    simp [RCt.noiseAtInt, matVecRCt, matVecMsgR] at this

/-- The companion SATISFIABILITY side (house law: a floor must be satisfiable AND refutable, and
not provable). `stepR_rowBound_necessary` shows the hypotheses can FAIL; this shows they can be
MET, with a conclusion that then says something — otherwise `stepR_noise_le` could be vacuously
true over an empty hypothesis set. -/
theorem stepR_hypotheses_satisfiable :
    ∃ (S : Fin 1 → Fin 1 → ℤ) (x : Fin 1 → RCt fheRs4096 4) (m : Fin 1 → Rn 4),
      RowBound S 1 ∧ (∀ j, NormInfLE ((x j).noiseAtInt (m j)) 1) ∧
      (∀ i, NormInfLE ((matVecRCt S x i).noiseAtInt (matVecMsgR S m i)) (1 * 1)) ∧
      ¬ (∀ i, NormInfLE ((matVecRCt S x i).noiseAtInt (matVecMsgR S m i)) 0) := by
  refine ⟨fun _ _ => 1, fun _ => ⟨fun _ => 1⟩, fun _ _ => 0, ?_, ?_, ?_, ?_⟩
  · intro i
    simp
  · intro j k
    simp [RCt.noiseAtInt]
  · exact stepR_noise_le (fun i => by simp) 1 (by norm_num) (fun j k => by simp [RCt.noiseAtInt])
  · intro hcon
    have := hcon 0 0
    simp [RCt.noiseAtInt, matVecRCt, matVecMsgR] at this

/-- **THE DEPLOYED DEPTH CEILING, NOW A RING STATEMENT.** At the deployed degree `N = 4096`, the
deployed growth factor `G = 3` (τ = 1, `‖A‖∞ ≤ 2`) and fresh noise `≤ 2^20`, `T = 42` public-linear
steps leave EVERY COEFFICIENT of every component's noise inside `3^42·2^20` — and that bound
satisfies the decrypt margin. `Bfv.deployed_iterCeiling` proved `T_max = 42` about one scalar
coefficient; for this path the same 42 now holds on the whole ring, with no expansion factor
spent. -/
theorem deployed_ring_depth {n : ℕ} {S : Fin n → Fin n → ℤ} (hS : RowBound S 3)
    {x : Fin n → RCt fheRs4096 4096} {m : Fin n → Rn 4096}
    (hfresh : ∀ j, NormInfLE ((x j).noiseAtInt (m j)) (2 ^ 20)) :
    (∀ i, NormInfLE ((iterRCt S 42 x i).noiseAtInt (iterMsgR S 42 m i))
        ((3 : ℤ) ^ 42 * (2 : ℤ) ^ 20))
      ∧ SafeNoise fheRs4096 ((3 : ℤ) ^ 42 * (2 : ℤ) ^ 20) := by
  have hsafe := noise_after_T fheRs4096 3 (2 ^ 20) 42 (by norm_num) (by norm_num) (by decide)
    (le_of_eq deployed_iterCeiling.symm)
  refine ⟨iterR_noise_le hS (by norm_num) (by positivity) hfresh 42, ?_⟩
  simpa using hsafe

/-! ## 5. The price of a POLYNOMIAL multiplier (what the row-sum route is buying). -/

/-- A public INTEGER scalar multiplier costs exactly `|c|` on the noise bound — no `N`. -/
theorem scalarMul_noise_le {N : ℕ} {e : Rn N} {M : ℤ} (c : ℤ) (hc : 0 ≤ c)
    (h : NormInfLE e M) : NormInfLE (fun k => c * e k) (c * M) := by
  intro k
  rw [abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (h k) hc

/-- **The gap, at the deployed degree.** A plaintext-POLYNOMIAL multiplier of ∞-norm `A` costs
`4096·A` on the noise bound (`negaMul_normInf_le` at `N = 4096`, and
`deployed_expansion_attained` shows that factor is real, not slack), where an integer scalar of
the same magnitude costs `A`. The full `2^12` is the price of leaving the public-integer-scalar
step — which is why the coefficient-encoded route, whose multipliers stay integer scalars in
`stepR_noise_le`, is the one with a provable budget. -/
theorem polyStep_costs_expansion {p e : Rn 4096} {A M : ℤ}
    (hp : NormInfLE p A) (he : NormInfLE e M) (hA : 0 ≤ A) :
    NormInfLE (negaMul p e) (4096 * A * M) := by
  simpa using negaMul_normInf_le hp he hA

#assert_all_clean [Bfv.matVecR_noiseAtInt, Bfv.stepR_noise_le, Bfv.iterRCt_succ,
  Bfv.iterMsgR_succ, Bfv.iterR_noise_le, Bfv.stepR_rowBound_necessary,
  Bfv.stepR_hypotheses_satisfiable, Bfv.deployed_ring_depth,
  Bfv.scalarMul_noise_le, Bfv.polyStep_costs_expansion]

end Bfv
