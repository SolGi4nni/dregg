/-
# `Dregg2.Crypto.InvertibilityNormGen` — challenge-difference invertibility BEYOND the n=4/q=5 point.

`InvertibilityNorm` proved the Lyubashevsky–Seiler bound (IACR 2018/786) at the single point
`n = 4, q = 5`, with the min-norm discharged by `decide` over 625 elements. This file replaces the
per-`q` decision with PARAMETRIC theorems over infinite families of `q`, with the true `q^(d/n)`
threshold shape.

**What is PROVED here (no `sorry`, every keystone `#assert_axioms`-clean, kernel `decide` only):**

1. **n = 2, ALL primes `q ≡ 3 (mod 4)`, no norm needed** (`challenge_diff_isUnit_inert`): `−1` is a
   non-square (Mathlib's `ZMod.exists_sq_eq_neg_one_iff`), so `ℤ_q[X]/(X²+1) = 𝔽_{q²}` via the parent
   file's anisotropic-norm inverse — EVERY nonzero challenge difference inverts. Generalizes
   `HermineInvertibility`'s fixed-`q` field trick to the whole residue class.

2. **THE PARAMETRIC MIN-NORM LEMMA, n = 2, d = 1** (`minNorm_linear_factor`): for ANY `q` (no
   primality!) and any root `r² = −1`, every nonzero multiple of `X − r` in `ℤ_q[X]/(X²+1)` has
   coefficient ∞-norm `> B` whenever `2·B² < q` — min-norm `> √(q/2)`, the Lyubashevsky–Seiler
   `q^(d/n)`-shape with constant `1/√2`. Proof: centered integer lifts (`ZMod.valMinAbs`, bridged to
   the parent's `caval`), the kernel forces the Gaussian norm `â² + b̂²` ≡ 0 mod `q`, the bound pins
   it to 0, and `x² + y² = 0 ⇒ x = y = 0` over ℤ. NOT a `decide` — one proof, all `q`.

3. **THE n = 2 HEADLINE** (`challenge_diff_isUnit_all_odd_primes`): for EVERY odd prime `q`,
   distinct challenges with `2·‖c−c'‖∞² < q` have INVERTIBLE difference. (`q ≡ 3`: inert; `q ≡ 1`:
   split through `crtLin`, a CONSTRUCTED CRT iso `ℤ_q[X]/(X²+1) ≃+* ℤ_q × ℤ_q` for the LINEAR factor
   structure, `r` and `2⁻¹` obtained, not assumed.) SHARP at `q = 13`: `3 + 2X` (norm 3, just past
   the `B ≤ 2` threshold) is a nonzero non-unit — and the decided 169-element min-norm at `q = 13`
   agrees exactly with the parametric route (`minNorm13_decided` vs `minNorm13_parametric`).

4. **n = 4, THE PARAMETRIC `q^(1/4)` BOUND, fully-split family `q ≡ 1 (mod 8)`**
   (`minNorm_quartic_linear`, `low_norm_isUnit_quartic`, `challenge_diff_isUnit_quartic`): for ANY
   `q` and any root `a⁴ = −1`, every nonzero multiple of `X − a` in `ℤ_q[X]/(X⁴+1)` has ∞-norm `> B`
   whenever `18·B⁴ < q`; for prime such `q`, nonzero `f` with `18·‖f‖∞⁴ < q` is a UNIT. The engine:
   `f(a) = 0` forces the `ℤ[ζ₈]`-norm form `N(f) = P² + Q²` (`P = c0²−c2²+2c1c3`,
   `Q = 2c0c2−c1²+c3²` — again a sum of two squares, since `ℚ(ζ₈) ⊃ ℚ(i)`) to vanish mod `q`;
   lifts bound it by `18B⁴ < q`; and the form is INTEGRALLY ANISOTROPIC (`formPQ_anisotropic` — the
   arithmetic content of `[ℚ(ζ₈):ℚ] = 4`, reduced by hand in ℤ[i]-coordinates to `2x² = m²`, killed
   by 2-adic factorization parity). Unit conclusion via CRT injectivity at the four linear factors
   plus finite-ring non-zero-divisor ⇒ unit — no interpolation needed. Non-vacuous at `q = 41`
   (`3⁴ = 81 = −1`): the ternary difference `1 + X − X³` is certified a unit parametrically —
   `Quart 41` has 2.8M elements, beyond any `decide`.

**The remaining gap toward full arbitrary-(n, q) Lyubashevsky–Seiler, honestly:**
- **Higher-degree factors `d ≥ 2` parametrically.** Here every parametric bound is at `d = 1`
  (linear factors; the parent file has `d = 2` only as decided `q = 5`). LS Lemma 2.2 handles general
  `d | n` via the resultant `Res(f, X^n+1) = ∏ f(ζ)` over complex `2n`-th roots with `|f(ζ)| ≤ n‖f‖`
  — a genuinely analytic bound (complex absolute values of cyclotomic evaluations) with no Mathlib
  infrastructure; the sum-of-two-squares shortcut used here is special to `ℤ[i] ⊆ ℤ[ζ_{2n}]`, i.e.
  to `4 | 2n` with the norm form staying binary. For `n = 8` the same route would need
  quaternary-form anisotropy (`ℤ[ζ₁₆]`), and for general splitting type the full cyclotomic
  factorization of `X^n + 1 mod q` by `q mod 2n` — neither is in Mathlib.
- **Constants.** The thresholds `2B² < q` (tight at `q = 13`) and `18B⁴ < q` (not tight; LS get
  `q^(1/4)` with a better constant via `s`-powers of the factor) are the honest cost of the
  elementary lift argument.
- **Intermediate residue classes.** `q ≡ 5 (mod 8)` at `n = 4` (two quadratic factors, the parent's
  decided case) still lacks a parametric min-norm: its ideal norm form is quaternary. The
  `q ≡ 3 (mod 8)` case likewise.
-/
import Dregg2.Crypto.InvertibilityNorm
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Data.Nat.Factorization.Defs

namespace Dregg2.Crypto.InvertibilityNormGen

open Dregg2.Crypto.InvertibilityNorm
open Quart (caval normInf)

/-! ## 0. Infrastructure: the ∞-norm on the pair model, and the centered integer lift -/

/-- The coefficient ∞-norm on `Quad q r` (the pair model of `ℤ_q[X]/(X² − r)`). -/
def normInf2 {q : ℕ} {r : ZMod q} (f : Quad q r) : ℕ := max (caval f.re) (caval f.im)

/-- `caval` (the parent file's centered absolute value) IS the absolute value of Mathlib's
minimal-absolute-value integer lift `ZMod.valMinAbs`. This is the bridge from the decided norm
to the integer geometry that powers the parametric bound. -/
theorem caval_eq_natAbs_valMinAbs {q : ℕ} [NeZero q] (x : ZMod q) :
    caval x = x.valMinAbs.natAbs := by
  have hlt : x.val < q := ZMod.val_lt x
  rw [ZMod.valMinAbs_def_pos]
  simp only [Quart.caval]
  split_ifs with h <;> omega

theorem abs_valMinAbs_le_of_caval_le {q : ℕ} [NeZero q] {x : ZMod q} {B : ℕ}
    (h : caval x ≤ B) : |x.valMinAbs| ≤ (B : ℤ) := by
  rw [Int.abs_eq_natAbs, ← caval_eq_natAbs_valMinAbs]
  exact_mod_cast h

/-- The integer-lift workhorse: an integer that vanishes mod `q` and sits in `[0, q)` is zero. -/
theorem int_eq_zero_of_zmod_zero_of_lt {q : ℕ} {N : ℤ}
    (hcast : (N : ZMod q) = 0) (h0 : 0 ≤ N) (hlt : N < (q : ℤ)) : N = 0 :=
  Int.eq_zero_of_abs_lt_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd N q).mp hcast)
    (by rwa [abs_of_nonneg h0])

/-- `2` is nonzero mod an odd prime. -/
theorem two_ne_zero_zmod {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) : (2 : ZMod q) ≠ 0 := by
  intro h0
  have hdvd : q ∣ 2 := (CharP.cast_eq_zero_iff (ZMod q) q 2).mp (by exact_mod_cast h0)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact (Fact.out : q.Prime).ne_one h
  · exact hq h

/-- Enumeration equivalence for the pair model (only to make small concrete `∀` facts decidable). -/
def quadEquivProd (q : ℕ) (r : ZMod q) : Quad q r ≃ ZMod q × ZMod q where
  toFun f := (f.re, f.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {q : ℕ} [NeZero q] {r : ZMod q} : Fintype (Quad q r) :=
  Fintype.ofEquiv _ (quadEquivProd q r).symm

/-! ## 1. The INERT case, parametric: n = 2, ALL primes q ≡ 3 (mod 4)

`HermineInvertibility` proved this for a single fixed `q`. Here it is for the whole residue
class at once: `X² + 1` is irreducible mod every prime `q ≡ 3 (mod 4)` (because `−1` is a
non-square), so `ℤ_q[X]/(X²+1) = 𝔽_{q²}` and EVERY nonzero challenge difference is a unit —
no norm hypothesis whatsoever. -/

section Inert

variable {q : ℕ} [Fact q.Prime]

/-- For prime `q ≡ 3 (mod 4)`, `−1` is a non-square mod `q`. -/
theorem neg_one_nonsquare (hq : q % 4 = 3) : ∀ x : ZMod q, x * x ≠ -1 := fun x hx =>
  (ZMod.exists_sq_eq_neg_one_iff.mp ⟨x, hx.symm⟩) hq

/-- **n = 2, all primes q ≡ 3 (mod 4)**: every nonzero element of `ℤ_q[X]/(X²+1)` is a unit,
with the inverse EXHIBITED by the parent file's anisotropic-norm construction. -/
theorem isUnit_of_ne_zero_inert (hq : q % 4 = 3) {f : Quad q (-1)} (hf : f ≠ 0) : IsUnit f :=
  Quad.isUnit_of_ne_zero (neg_one_nonsquare hq) hf

/-- The challenge-difference form of the inert case: distinct challenges always invert. -/
theorem challenge_diff_isUnit_inert (hq : q % 4 = 3) {c c' : Quad q (-1)} (hcc : c ≠ c') :
    IsUnit (c - c') :=
  isUnit_of_ne_zero_inert hq (sub_ne_zero.mpr hcc)

end Inert

/-! ### Non-vacuity of the inert case: q = 11 concrete, inverse exhibited; teeth at q = 13 -/

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- First fork challenge over `q = 11` (a fresh prime `≡ 3 mod 4`, beyond Hermine's fixed one). -/
def c11 : Quad 11 (-1) := ⟨1, 1⟩

def c11' : Quad 11 (-1) := ⟨0, 2⟩

theorem c11_distinct : c11 ≠ c11' := by decide

theorem c11_diff_isUnit : IsUnit (c11 - c11') :=
  challenge_diff_isUnit_inert (by norm_num) c11_distinct

/-- The difference is `1 − X` and its inverse is `6 + 6X`: `(1−X)(6+6X) = 6 − 6X² = 12 = 1`. -/
theorem c11_diff_eq : c11 - c11' = (⟨1, 10⟩ : Quad 11 (-1)) := by decide

theorem c11_inv_verifies : (⟨1, 10⟩ : Quad 11 (-1)) * ⟨6, 6⟩ = 1 := by decide

/-- TEETH: the inert hypothesis is load-bearing. At `q = 13 ≡ 1 (mod 4)` the ring is NOT a
field — `(8 + X)(5 + X) = 40 − 1 + 13X = 0`, a genuine zero-divisor pair. -/
theorem quad13_zero_divisor : (⟨8, 1⟩ : Quad 13 (-1)) * ⟨5, 1⟩ = 0 := by decide

theorem quad13_nonzero_nonunit : ¬ IsUnit ((⟨8, 1⟩ : Quad 13 (-1))) := by
  intro h
  have h5 : (⟨5, 1⟩ : Quad 13 (-1)) = 0 :=
    h.mul_left_cancel (by rw [quad13_zero_divisor, mul_zero])
  exact absurd h5 (by decide)

/-! ## 2. The SPLIT case: linear factors `X ∓ r` of `X² + 1` (q ≡ 1 mod 4), and
     THE PARAMETRIC MIN-NORM BOUND — the Lyubashevsky–Seiler threshold shape, all q at once -/

section Split

variable {q : ℕ}

/-- Evaluation at a root `a` of `X² + 1`: the factor map
`ℤ_q[X]/(X²+1) → ℤ_q[X]/(X − a) = ℤ_q` (well-defined when `a² = −1`). -/
def toLin (a : ZMod q) (f : Quad q (-1)) : ZMod q := f.re + a * f.im

@[simp] theorem toLin_def (a : ZMod q) (f : Quad q (-1)) : toLin a f = f.re + a * f.im := rfl

theorem toLin_mul {a : ZMod q} (ha : a * a = -1) (f g : Quad q (-1)) :
    toLin a (f * g) = toLin a f * toLin a g := by
  simp only [toLin, Quad.mul_re, Quad.mul_im]
  linear_combination (-(f.im * g.im)) * ha

/-- The factor map as a ring hom. -/
def toLinHom {a : ZMod q} (ha : a * a = -1) : Quad q (-1) →+* ZMod q where
  toFun := toLin a
  map_one' := by simp [toLin]
  map_mul' := toLin_mul ha
  map_zero' := by simp [toLin]
  map_add' f g := by simp only [toLin, Quad.add_re, Quad.add_im]; ring

@[simp] theorem toLinHom_apply {a : ZMod q} (ha : a * a = -1) (f : Quad q (-1)) :
    toLinHom ha f = toLin a f := rfl

/-- The heart of the d = 1 bound: an element of the kernel of the factor map has
`re² + im² = 0` — the Gaussian-integer norm form vanishes mod `q`. -/
theorem sq_add_sq_eq_zero_of_ker {r : ZMod q} (hr : r * r = -1) {f : Quad q (-1)}
    (hker : toLin r f = 0) : f.re ^ 2 + f.im ^ 2 = 0 := by
  simp only [toLin] at hker
  linear_combination (f.re - r * f.im) * hker + f.im ^ 2 * hr

/-- **THE PARAMETRIC MIN-NORM LEMMA (n = 2, d = 1) — the Lyubashevsky–Seiler bound, all q.**
For ANY modulus `q` and any root `r` of `X² + 1` mod `q`, every nonzero multiple of the linear
factor `X − r` in `ℤ_q[X]/(X²+1)` has coefficient ∞-norm `> B` whenever `2·B² < q` — i.e. the
ideal's min-norm is `> √(q/2)`, the true `q^(d/n)`-shape threshold (LS Corollary 1.2 at
`n = 2, d = 1`, constant `1/√2`). Proof: lift the two coefficients to their centered integer
representatives; the kernel condition forces the Gaussian norm `â² + b̂²` to vanish mod `q`,
but `0 ≤ â² + b̂² ≤ 2B² < q` pins it to zero, and the form is anisotropic over ℤ.
NOT a `decide` — one proof for the whole infinite family, no primality needed. -/
theorem minNorm_linear_factor [NeZero q] {r : ZMod q} (hr : r * r = -1) {B : ℕ}
    (hB : 2 * B ^ 2 < q) :
    ∀ f : Quad q (-1), toLin r f = 0 → f ≠ 0 → B + 1 ≤ normInf2 f := by
  intro f hker hf
  by_contra hlt
  rw [not_le, Nat.lt_succ_iff] at hlt
  have hre : caval f.re ≤ B := le_trans (le_max_left _ _) hlt
  have him : caval f.im ≤ B := le_trans (le_max_right _ _) hlt
  have haB := abs_le.mp (abs_valMinAbs_le_of_caval_le hre)
  have hbB := abs_le.mp (abs_valMinAbs_le_of_caval_le him)
  have hcast : ((f.re.valMinAbs ^ 2 + f.im.valMinAbs ^ 2 : ℤ) : ZMod q) = 0 := by
    push_cast [ZMod.coe_valMinAbs]
    exact sq_add_sq_eq_zero_of_ker hr hker
  have h0 : (0 : ℤ) ≤ f.re.valMinAbs ^ 2 + f.im.valMinAbs ^ 2 := by positivity
  have hlt2 : f.re.valMinAbs ^ 2 + f.im.valMinAbs ^ 2 < (q : ℤ) := by
    have hq : ((2 * B ^ 2 : ℕ) : ℤ) < (q : ℤ) := by exact_mod_cast hB
    have h1 : f.re.valMinAbs ^ 2 ≤ (B : ℤ) ^ 2 := sq_le_sq' haB.1 haB.2
    have h2 : f.im.valMinAbs ^ 2 ≤ (B : ℤ) ^ 2 := sq_le_sq' hbB.1 hbB.2
    push_cast at hq
    linarith
  have hzero : f.re.valMinAbs ^ 2 + f.im.valMinAbs ^ 2 = 0 :=
    int_eq_zero_of_zmod_zero_of_lt hcast h0 hlt2
  have ha0 : f.re.valMinAbs = 0 := by
    have h : f.re.valMinAbs ^ 2 = 0 := by nlinarith [sq_nonneg f.im.valMinAbs]
    exact sq_eq_zero_iff.mp h
  have hb0 : f.im.valMinAbs = 0 := by
    have h : f.im.valMinAbs ^ 2 = 0 := by nlinarith [sq_nonneg f.re.valMinAbs]
    exact sq_eq_zero_iff.mp h
  apply hf
  refine Quad.ext2 ?_ ?_
  · have h := ZMod.coe_valMinAbs f.re
    rw [ha0] at h
    simpa using h.symm
  · have h := ZMod.coe_valMinAbs f.im
    rw [hb0] at h
    simpa using h.symm

/-- The CRT ring isomorphism for the LINEAR splitting `X² + 1 = (X − r)(X + r)`, CONSTRUCTED
for any `q, r` with `r² = −1` and `2` invertible: `ℤ_q[X]/(X²+1) ≃+* ℤ_q × ℤ_q`. This is the
`q ≡ 1 (mod 8 or 4)` factor structure — LINEAR residue fields, complementing the parent file's
quadratic-factor `crtEquiv`. Both directions and both hom laws proved algebraically. -/
def crtLin {r half : ZMod q} (hr : r * r = -1) (h2 : 2 * half = 1) :
    Quad q (-1) ≃+* ZMod q × ZMod q where
  toFun f := (toLin r f, toLin (-r) f)
  invFun p := ⟨(p.1 + p.2) * half, (p.1 - p.2) * half * (-r)⟩
  left_inv f := by
    refine Quad.ext2 ?_ ?_ <;> simp only [toLin]
    · linear_combination f.re * h2
    · linear_combination (-(2 * f.im * half)) * hr + f.im * h2
  right_inv p := by
    refine Prod.ext ?_ ?_ <;> simp only [toLin]
    · linear_combination (-((p.1 - p.2) * half)) * hr + p.1 * h2
    · linear_combination ((p.1 - p.2) * half) * hr + p.2 * h2
  map_mul' f g := Prod.ext (toLin_mul hr f g) (toLin_mul (by linear_combination hr) f g)
  map_add' f g := by
    refine Prod.ext ?_ ?_ <;>
      simp only [toLin, Quad.add_re, Quad.add_im, Prod.fst_add, Prod.snd_add] <;> ring

@[simp] theorem crtLin_apply {r half : ZMod q} (hr : r * r = -1) (h2 : 2 * half = 1)
    (f : Quad q (-1)) : crtLin hr h2 f = (toLin r f, toLin (-r) f) := rfl

/-- **The split-case unit theorem, parametric**: prime `q`, `r² = −1`, `2` invertible — every
nonzero `f` with `2·‖f‖∞² < q` is a unit. Min-norm bound at BOTH linear factors, chained
through the constructed CRT. -/
theorem low_norm_isUnit_split [Fact q.Prime] {r half : ZMod q} (hr : r * r = -1)
    (h2 : 2 * half = 1) {f : Quad q (-1)} (hf : f ≠ 0)
    (hν : 2 * normInf2 f ^ 2 < q) : IsUnit f := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hr' : (-r) * (-r) = -1 := by linear_combination hr
  have h₁ : toLin r f ≠ 0 :=
    factor_nonzero_of_norm_lt (toLin r) normInf2 (normInf2 f + 1)
      (minNorm_linear_factor hr hν) hf (Nat.lt_succ_self _)
  have h₂ : toLin (-r) f ≠ 0 :=
    factor_nonzero_of_norm_lt (toLin (-r)) normInf2 (normInf2 f + 1)
      (minNorm_linear_factor hr' hν) hf (Nat.lt_succ_self _)
  refine isUnit_of_map_isUnit (crtLin hr h2) ?_
  rw [crtLin_apply]
  exact Prod.isUnit_iff.mpr ⟨h₁.isUnit, h₂.isUnit⟩

/-- The split case packaged over the residue class: for every prime `q ≡ 1 (mod 4)`, every
nonzero `f ∈ ℤ_q[X]/(X²+1)` with `2·‖f‖∞² < q` is a unit — the root `r` of `−1` and the
half `2⁻¹` are OBTAINED, not assumed. -/
theorem low_norm_isUnit_mod_four_eq_one [Fact q.Prime] (hq : q % 4 = 1)
    {f : Quad q (-1)} (hf : f ≠ 0) (hν : 2 * normInf2 f ^ 2 < q) : IsUnit f := by
  obtain ⟨r, hr⟩ : IsSquare (-1 : ZMod q) :=
    ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  have hq2 : (2 : ZMod q) ≠ 0 := two_ne_zero_zmod (by omega)
  exact low_norm_isUnit_split hr.symm (mul_inv_cancel₀ hq2) hf hν

end Split

/-! ## 3. THE HEADLINE: n = 2 challenge-difference invertibility for EVERY odd prime q -/

/-- **THE GENERAL n = 2 LYUBASHEVSKY–SEILER THEOREM, ALL ODD PRIMES.** In
`R_q = ℤ_q[X]/(X²+1)` for ANY odd prime `q`: distinct challenges whose difference has
coefficient ∞-norm below the `√(q/2)` threshold (`2·‖c−c'‖∞² < q`) have INVERTIBLE difference.
`q ≡ 3 (mod 4)`: inert, no norm needed; `q ≡ 1 (mod 4)`: split, the parametric min-norm bound
at both linear CRT factors. One theorem, the whole infinite family, the true `q^(d/n)` = `√q`
threshold shape — not a per-`q` decision. -/
theorem challenge_diff_isUnit_all_odd_primes {q : ℕ} [Fact q.Prime] (hodd : q % 2 = 1)
    {c c' : Quad q (-1)} (hcc : c ≠ c') (hν : 2 * normInf2 (c - c') ^ 2 < q) :
    IsUnit (c - c') := by
  have h4 : q % 4 = 1 ∨ q % 4 = 3 := by omega
  rcases h4 with h | h
  · exact low_norm_isUnit_mod_four_eq_one h (sub_ne_zero.mpr hcc) hν
  · exact challenge_diff_isUnit_inert h hcc

/-! ### Non-vacuity + sharpness of the split case, at q = 13 (and scaling demo at q = 101) -/

theorem five_sq_13 : (5 : ZMod 13) * 5 = -1 := by decide

set_option maxRecDepth 40000 in
/-- Cross-validation, decided route: the min-norm of the ideal `(X − 5)` in `ℤ₁₃[X]/(X²+1)` is
≥ 3, checked over all 169 elements. -/
theorem minNorm13_decided : ∀ f : Quad 13 (-1), toLin 5 f = 0 → f ≠ 0 → 3 ≤ normInf2 f := by
  decide

/-- Cross-validation, parametric route: the SAME statement falls out of `minNorm_linear_factor`
at `B = 2` (`2·2² = 8 < 13`) — the general theorem and the finite decision agree. -/
theorem minNorm13_parametric : ∀ f : Quad 13 (-1), toLin 5 f = 0 → f ≠ 0 → 3 ≤ normInf2 f :=
  minNorm_linear_factor five_sq_13 (by norm_num)

/-- Concrete challenge pair at `q = 13` with difference `1 − X` (∞-norm 1, threshold `2 < 13`). -/
def c13 : Quad 13 (-1) := ⟨1, 0⟩

def c13' : Quad 13 (-1) := ⟨0, 1⟩

theorem c13_distinct : c13 ≠ c13' := by decide

/-- The headline theorem fires on a real element at a split prime. -/
theorem c13_diff_isUnit : IsUnit (c13 - c13') :=
  challenge_diff_isUnit_all_odd_primes (by norm_num) c13_distinct (by decide)

/-- Same fact by exhibited inverse: `(1 − X)(7 + 7X) = 7 − 7X² = 14 = 1`. Two routes agree. -/
theorem c13_diff_eq : c13 - c13' = (⟨1, 12⟩ : Quad 13 (-1)) := by decide

theorem c13_inv_verifies : (⟨1, 12⟩ : Quad 13 (-1)) * ⟨7, 7⟩ = 1 := by decide

/-- **SHARPNESS of the parametric threshold at q = 13**: `3 + 2X` is nonzero, has ∞-norm
exactly 3 — just past the `2·B² < 13 ⇒ B ≤ 2` threshold — and is NOT a unit (it is a multiple
of `X − 5`, vanishing in that CRT factor). The `√(q/2)` shape cannot be relaxed. -/
def sharp13 : Quad 13 (-1) := ⟨3, 2⟩

theorem sharp13_ne_zero : sharp13 ≠ 0 := by decide

theorem sharp13_norm : normInf2 sharp13 = 3 := by decide

theorem sharp13_ker : toLin 5 sharp13 = 0 := by decide

theorem sharp13_not_unit : ¬ IsUnit sharp13 := by
  intro h
  have hu := h.map (toLinHom five_sq_13)
  rw [toLinHom_apply, sharp13_ker] at hu
  exact absurd (isUnit_zero_iff.mp hu) (by decide)

theorem norm_threshold_sharp_13 :
    ∃ f : Quad 13 (-1), f ≠ 0 ∧ normInf2 f = 3 ∧ ¬ 2 * normInf2 f ^ 2 < 13 ∧ ¬ IsUnit f :=
  ⟨sharp13, sharp13_ne_zero, sharp13_norm, by decide, sharp13_not_unit⟩

/-- Teeth at the parent file's `q = 5`: `3 + X` is a nonzero NON-unit of norm 2 — and the
parametric threshold correctly does NOT cover it (`2·2² = 8 ≥ 5`). The bound is honest at
small `q` too. -/
theorem q5_nonunit_outside_threshold :
    ¬ (2 * normInf2 ((⟨3, 1⟩ : Quad 5 (-1))) ^ 2 < 5) := by decide

theorem q5_ker : toLin 2 (⟨3, 1⟩ : Quad 5 (-1)) = 0 := by decide

theorem q5_not_unit : ¬ IsUnit ((⟨3, 1⟩ : Quad 5 (-1))) := by
  intro h
  have hu := h.map (toLinHom two_sq)
  rw [toLinHom_apply, q5_ker] at hu
  exact absurd (isUnit_zero_iff.mp hu) (by decide)

/-- Scaling demo at `q = 101` (split, `10² = −1`): a norm-7 element is certified a unit by the
PARAMETRIC theorem (`2·7² = 98 < 101`) — no 101²-element enumeration anywhere in the proof. -/
instance : Fact (Nat.Prime 101) := ⟨by norm_num⟩

theorem w101_isUnit : IsUnit ((⟨7, 6⟩ : Quad 101 (-1))) :=
  low_norm_isUnit_mod_four_eq_one (by norm_num) (by decide) (by decide)

/-! ## 4. n = 4, LINEAR factors (q ≡ 1 mod 8): the parametric `q^(1/4)` bound

`X⁴ + 1` splits into four LINEAR factors `X ∓ a, X ∓ a³` exactly when `−1` is a fourth power
(`q ≡ 1 mod 8`). Same strategy at the next `n`: the kernel of one evaluation forces the
`ℤ[ζ₈]`-norm form — which is again a SUM OF TWO SQUARES, `N(f) = P² + Q²` with
`P = c0² − c2² + 2c1c3`, `Q = 2c0c2 − c1² + c3²` (since `ℚ(ζ₈) ⊃ ℚ(i)`) — to vanish mod `q`;
centered lifts bound it below `q`; integral anisotropy of the form kills `f`. -/

section Quartic

variable {q : ℕ}

/-- Evaluation at a root `a` of `X⁴ + 1` on the parent file's `Quart q` model — the factor map
`ℤ_q[X]/(X⁴+1) → ℤ_q[X]/(X − a) = ℤ_q`. -/
def evalQ (a : ZMod q) (f : Quart q) : ZMod q :=
  f.c0 + a * f.c1 + a * a * f.c2 + a * a * a * f.c3

theorem evalQ_zero (a : ZMod q) : evalQ a (0 : Quart q) = 0 := by simp [evalQ]

theorem evalQ_mul {a : ZMod q} (ha : a * a * (a * a) = -1) (f g : Quart q) :
    evalQ a (f * g) = evalQ a f * evalQ a g := by
  simp only [evalQ, Quart.mul_c0, Quart.mul_c1, Quart.mul_c2, Quart.mul_c3]
  linear_combination
    (-(f.c1 * g.c3 + f.c2 * g.c2 + f.c3 * g.c1 + (f.c2 * g.c3 + f.c3 * g.c2) * a
      + f.c3 * g.c3 * (a * a))) * ha

/-- Fourth-power fact for the conjugate root `−a`. -/
theorem root_neg {a : ZMod q} (ha : a * a * (a * a) = -1) :
    (-a) * (-a) * ((-a) * (-a)) = -1 := by linear_combination ha

/-- Fourth-power fact for the conjugate root `a³`. -/
theorem root_cube {a : ZMod q} (ha : a * a * (a * a) = -1) :
    (a * a * a) * (a * a * a) * ((a * a * a) * (a * a * a)) = -1 := by
  linear_combination (a * a * (a * a) * (a * a * (a * a)) - a * a * (a * a) + 1) * ha

/-- The `P` coordinate of the `ℤ[ζ₈]`-norm (defined over any commutative ring, so the same
polynomial serves `ZMod q` and the integer lifts). -/
def formP {α : Type*} [CommRing α] (c0 c1 c2 c3 : α) : α := c0 * c0 - c2 * c2 + 2 * (c1 * c3)

/-- The `Q` coordinate of the `ℤ[ζ₈]`-norm. -/
def formQ {α : Type*} [CommRing α] (c0 c1 c2 c3 : α) : α := 2 * (c0 * c2) - c1 * c1 + c3 * c3

/-- The two-conjugate product lands in `ℤ[i]`: `f(a)·f(−a) = P + Q·a²` mod `a⁴ + 1`. -/
theorem evalQ_mul_neg {a : ZMod q} (ha : a * a * (a * a) = -1) (f : Quart q) :
    evalQ a f * evalQ (-a) f
      = formP f.c0 f.c1 f.c2 f.c3 + formQ f.c0 f.c1 f.c2 f.c3 * (a * a) := by
  simp only [evalQ, formP, formQ]
  linear_combination (f.c2 * f.c2 - 2 * (f.c1 * f.c3) - f.c3 * f.c3 * (a * a)) * ha

/-- Kernel at ONE root already forces the full norm form to vanish:
`f(a) = 0 ⇒ P² + Q² = 0` in `ZMod q` (the other three conjugate factors come along for free,
`(P + Qa²)(P − Qa²) = P² + Q²` using `a⁴ = −1`). -/
theorem formPQ_eq_zero_of_ker {a : ZMod q} (ha : a * a * (a * a) = -1) {f : Quart q}
    (hker : evalQ a f = 0) :
    formP f.c0 f.c1 f.c2 f.c3 ^ 2 + formQ f.c0 f.c1 f.c2 f.c3 ^ 2 = 0 := by
  have h1 := evalQ_mul_neg ha f
  rw [hker, zero_mul] at h1
  linear_combination
    (formQ f.c0 f.c1 f.c2 f.c3 * (a * a) - formP f.c0 f.c1 f.c2 f.c3) * h1
      + formQ f.c0 f.c1 f.c2 f.c3 ^ 2 * ha

/-- `2x² = m²` has only the trivial solution over ℤ (irrationality of `√2`, by 2-adic
factorization parity). -/
theorem two_mul_sq_eq_sq {x m : ℤ} (h : 2 * (x * x) = m * m) : x = 0 ∧ m = 0 := by
  by_cases hx0 : x = 0
  · refine ⟨hx0, ?_⟩
    rw [hx0, mul_zero, mul_zero] at h
    exact mul_self_eq_zero.mp h.symm
  exfalso
  have hm0 : m ≠ 0 := by
    intro hm
    rw [hm, mul_zero] at h
    exact hx0 (mul_self_eq_zero.mp (by linarith))
  have hnat : 2 * (x.natAbs * x.natAbs) = m.natAbs * m.natAbs := by
    have hcongr := congrArg Int.natAbs h
    simpa [Int.natAbs_mul] using hcongr
  have hxn : x.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hx0
  have hmn : m.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hm0
  have hfact := congrArg (fun n => n.factorization 2) hnat
  simp only [Nat.factorization_mul (by norm_num : (2 : ℕ) ≠ 0) (Nat.mul_ne_zero hxn hxn),
    Nat.factorization_mul hxn hxn, Nat.factorization_mul hmn hmn,
    Nat.Prime.factorization Nat.prime_two, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_eq_same] at hfact
  omega

/-- **Integral anisotropy of the `ℤ[ζ₈]`-norm coordinates**: `P(c) = Q(c) = 0` over ℤ forces
`c = 0` — the arithmetic content of `[ℚ(ζ₈) : ℚ] = 4`. Elementary route, in bare coordinates:
`P + Qi = (c0 + c2 i)² − i(c1 + c3 i)²` in `ℤ[i]`, so `P = Q = 0` would make `i` a square of a
Gaussian rational; multiplying by the conjugate reduces that to `2x² = m²`, which `√2 ∉ ℚ`
forbids. -/
theorem formPQ_anisotropic {c0 c1 c2 c3 : ℤ}
    (hP : formP c0 c1 c2 c3 = 0) (hQ : formQ c0 c1 c2 c3 = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 := by
  simp only [formP, formQ] at hP hQ
  -- w := (c0 + c2·i)·conj(c1 + c3·i) = x + y·i with x, y below; n := c1² + c3² = N(c1 + c3·i).
  -- From P = Q = 0: w² = i·n², i.e. x² = y² and 2xy = n².
  have hsq : (c0 * c1 + c2 * c3) * (c0 * c1 + c2 * c3)
      = (c1 * c2 - c0 * c3) * (c1 * c2 - c0 * c3) := by
    linear_combination (c1 * c1 - c3 * c3) * hP + (2 * (c1 * c3)) * hQ
  have hxy : 2 * ((c0 * c1 + c2 * c3) * (c1 * c2 - c0 * c3))
      = (c1 * c1 + c3 * c3) * (c1 * c1 + c3 * c3) := by
    linear_combination (-(2 * (c1 * c3))) * hP + (c1 * c1 - c3 * c3) * hQ
  have hn : c1 * c1 + c3 * c3 = 0 := by
    have hcase : ((c0 * c1 + c2 * c3) - (c1 * c2 - c0 * c3))
        * ((c0 * c1 + c2 * c3) + (c1 * c2 - c0 * c3)) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hcase with h | h
    · -- y = x: 2x² = n², so n = 0.
      have hyx : c1 * c2 - c0 * c3 = c0 * c1 + c2 * c3 := by linarith
      rw [hyx] at hxy
      exact (two_mul_sq_eq_sq hxy).2
    · -- y = −x: n² = −2x² ≤ 0, so n² = 0.
      have hyx : c1 * c2 - c0 * c3 = -(c0 * c1 + c2 * c3) := by linarith
      rw [hyx] at hxy
      have hnn : (c1 * c1 + c3 * c3) * (c1 * c1 + c3 * c3) = 0 := by
        nlinarith [mul_self_nonneg (c0 * c1 + c2 * c3),
          mul_self_nonneg (c1 * c1 + c3 * c3)]
      exact mul_self_eq_zero.mp hnn
  have hc1 : c1 = 0 := by
    have h : c1 * c1 = 0 := by linarith [mul_self_nonneg c1, mul_self_nonneg c3]
    exact mul_self_eq_zero.mp h
  have hc3 : c3 = 0 := by
    have h : c3 * c3 = 0 := by linarith [mul_self_nonneg c1, mul_self_nonneg c3]
    exact mul_self_eq_zero.mp h
  subst hc1; subst hc3
  have hP' : c0 * c0 = c2 * c2 := by linear_combination hP
  have hQ2 : (2 : ℤ) * (c0 * c2) = 0 := by linear_combination hQ
  have hQ' : c0 * c2 = 0 := (mul_eq_zero.mp hQ2).resolve_left (by norm_num)
  rcases mul_eq_zero.mp hQ' with h0 | h0
  · refine ⟨h0, rfl, ?_, rfl⟩
    rw [h0] at hP'
    exact mul_self_eq_zero.mp (by linear_combination -hP')
  · refine ⟨?_, rfl, h0, rfl⟩
    rw [h0] at hP'
    exact mul_self_eq_zero.mp (by linear_combination hP')

/-- Centered coefficient bounds pin the norm form: `|cᵢ| ≤ B ⇒ P² + Q² ≤ 18·B⁴`. -/
theorem formPQ_bound {c0 c1 c2 c3 B : ℤ} (h0 : |c0| ≤ B) (h1 : |c1| ≤ B) (h2 : |c2| ≤ B)
    (h3 : |c3| ≤ B) : formP c0 c1 c2 c3 ^ 2 + formQ c0 c1 c2 c3 ^ 2 ≤ 18 * B ^ 4 := by
  obtain ⟨h0l, h0r⟩ := abs_le.mp h0
  obtain ⟨h1l, h1r⟩ := abs_le.mp h1
  obtain ⟨h2l, h2r⟩ := abs_le.mp h2
  obtain ⟨h3l, h3r⟩ := abs_le.mp h3
  have hc0B : c0 * c0 ≤ B * B := by
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ B - c0) (by linarith : (0:ℤ) ≤ B + c0)]
  have hc1B : c1 * c1 ≤ B * B := by
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ B - c1) (by linarith : (0:ℤ) ≤ B + c1)]
  have hc2B : c2 * c2 ≤ B * B := by
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ B - c2) (by linarith : (0:ℤ) ≤ B + c2)]
  have hc3B : c3 * c3 ≤ B * B := by
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ B - c3) (by linarith : (0:ℤ) ≤ B + c3)]
  have h13u : c1 * c3 ≤ B * B := by
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ B - c1) (by linarith : (0:ℤ) ≤ B + c3),
      mul_nonneg (by linarith : (0:ℤ) ≤ B + c1) (by linarith : (0:ℤ) ≤ B - c3)]
  have h13l : -(B * B) ≤ c1 * c3 := by
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ B - c1) (by linarith : (0:ℤ) ≤ B - c3),
      mul_nonneg (by linarith : (0:ℤ) ≤ B + c1) (by linarith : (0:ℤ) ≤ B + c3)]
  have h02u : c0 * c2 ≤ B * B := by
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ B - c0) (by linarith : (0:ℤ) ≤ B + c2),
      mul_nonneg (by linarith : (0:ℤ) ≤ B + c0) (by linarith : (0:ℤ) ≤ B - c2)]
  have h02l : -(B * B) ≤ c0 * c2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ B - c0) (by linarith : (0:ℤ) ≤ B - c2),
      mul_nonneg (by linarith : (0:ℤ) ≤ B + c0) (by linarith : (0:ℤ) ≤ B + c2)]
  have hPu : formP c0 c1 c2 c3 ≤ 3 * (B * B) := by
    simp only [formP]
    linarith [mul_self_nonneg c2]
  have hPl : -(3 * (B * B)) ≤ formP c0 c1 c2 c3 := by
    simp only [formP]
    linarith [mul_self_nonneg c0]
  have hQu : formQ c0 c1 c2 c3 ≤ 3 * (B * B) := by
    simp only [formQ]
    linarith [mul_self_nonneg c1]
  have hQl : -(3 * (B * B)) ≤ formQ c0 c1 c2 c3 := by
    simp only [formQ]
    linarith [mul_self_nonneg c3]
  have hP2 : formP c0 c1 c2 c3 ^ 2 ≤ (3 * (B * B)) ^ 2 := sq_le_sq' hPl hPu
  have hQ2 : formQ c0 c1 c2 c3 ^ 2 ≤ (3 * (B * B)) ^ 2 := sq_le_sq' hQl hQu
  nlinarith [hP2, hQ2]

/-- **THE PARAMETRIC MIN-NORM LEMMA (n = 4, d = 1) — the `q^(1/4)` threshold shape, all q.**
For ANY modulus `q` and ANY root `a` of `X⁴ + 1` mod `q`: every nonzero multiple of the linear
factor `X − a` in `ℤ_q[X]/(X⁴+1)` has coefficient ∞-norm `> B` whenever `18·B⁴ < q`.
One proof for the whole family — no primality, no `decide`, no per-`q` case. -/
theorem minNorm_quartic_linear [NeZero q] {a : ZMod q} (ha : a * a * (a * a) = -1) {B : ℕ}
    (hB : 18 * B ^ 4 < q) :
    ∀ f : Quart q, evalQ a f = 0 → f ≠ 0 → B + 1 ≤ normInf f := by
  intro f hker hf
  by_contra hlt
  rw [not_le, Nat.lt_succ_iff] at hlt
  have h0c : caval f.c0 ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hlt
  have h1c : caval f.c1 ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hlt
  have h2c : caval f.c2 ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hlt
  have h3c : caval f.c3 ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hlt
  have hPQ := formPQ_eq_zero_of_ker ha hker
  have hcast : ((formP f.c0.valMinAbs f.c1.valMinAbs f.c2.valMinAbs f.c3.valMinAbs ^ 2
      + formQ f.c0.valMinAbs f.c1.valMinAbs f.c2.valMinAbs f.c3.valMinAbs ^ 2 : ℤ)
      : ZMod q) = 0 := by
    simp only [formP, formQ] at hPQ ⊢
    push_cast [ZMod.coe_valMinAbs]
    linear_combination hPQ
  have hbound := formPQ_bound (abs_valMinAbs_le_of_caval_le h0c)
    (abs_valMinAbs_le_of_caval_le h1c) (abs_valMinAbs_le_of_caval_le h2c)
    (abs_valMinAbs_le_of_caval_le h3c)
  have h0' : (0 : ℤ) ≤ formP f.c0.valMinAbs f.c1.valMinAbs f.c2.valMinAbs f.c3.valMinAbs ^ 2
      + formQ f.c0.valMinAbs f.c1.valMinAbs f.c2.valMinAbs f.c3.valMinAbs ^ 2 := by positivity
  have hlt2 : formP f.c0.valMinAbs f.c1.valMinAbs f.c2.valMinAbs f.c3.valMinAbs ^ 2
      + formQ f.c0.valMinAbs f.c1.valMinAbs f.c2.valMinAbs f.c3.valMinAbs ^ 2 < (q : ℤ) := by
    have hq : ((18 * B ^ 4 : ℕ) : ℤ) < (q : ℤ) := by exact_mod_cast hB
    push_cast at hq
    linarith [hbound]
  have hzero := int_eq_zero_of_zmod_zero_of_lt hcast h0' hlt2
  have hPz : formP f.c0.valMinAbs f.c1.valMinAbs f.c2.valMinAbs f.c3.valMinAbs = 0 := by
    refine sq_eq_zero_iff.mp ?_
    nlinarith [sq_nonneg (formQ f.c0.valMinAbs f.c1.valMinAbs f.c2.valMinAbs f.c3.valMinAbs),
      sq_nonneg (formP f.c0.valMinAbs f.c1.valMinAbs f.c2.valMinAbs f.c3.valMinAbs)]
  have hQz : formQ f.c0.valMinAbs f.c1.valMinAbs f.c2.valMinAbs f.c3.valMinAbs = 0 := by
    refine sq_eq_zero_iff.mp ?_
    nlinarith [sq_nonneg (formQ f.c0.valMinAbs f.c1.valMinAbs f.c2.valMinAbs f.c3.valMinAbs),
      sq_nonneg (formP f.c0.valMinAbs f.c1.valMinAbs f.c2.valMinAbs f.c3.valMinAbs)]
  obtain ⟨e0, e1, e2, e3⟩ := formPQ_anisotropic hPz hQz
  apply hf
  refine Quart.ext4 ?_ ?_ ?_ ?_
  · have h := ZMod.coe_valMinAbs f.c0; rw [e0] at h; simpa using h.symm
  · have h := ZMod.coe_valMinAbs f.c1; rw [e1] at h; simpa using h.symm
  · have h := ZMod.coe_valMinAbs f.c2; rw [e2] at h; simpa using h.symm
  · have h := ZMod.coe_valMinAbs f.c3; rw [e3] at h; simpa using h.symm

/-- CRT injectivity for the four linear factors, parametric: vanishing at ALL of
`a, −a, a³, −a³` kills the element (prime `q`, `2 ≠ 0`). This is the injective half of the
four-factor CRT — exactly what the unit criterion below needs. -/
theorem eq_zero_of_evalQ_four [Fact q.Prime] {a : ZMod q} (ha : a * a * (a * a) = -1)
    (h2 : (2 : ZMod q) ≠ 0) {f : Quart q}
    (e1 : evalQ a f = 0) (e2 : evalQ (-a) f = 0)
    (e3 : evalQ (a * a * a) f = 0) (e4 : evalQ (-(a * a * a)) f = 0) : f = 0 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact one_ne_zero (by linear_combination ha : (1 : ZMod q) = 0)
  simp only [evalQ] at e1 e2 e3 e4
  have he1 : f.c0 + a * a * f.c2 = 0 := by
    have h : (2 : ZMod q) * (f.c0 + a * a * f.c2) = 0 := by linear_combination e1 + e2
    exact (mul_eq_zero.mp h).resolve_left h2
  have he2 : f.c0 - a * a * f.c2 = 0 := by
    have h : (2 : ZMod q) * (f.c0 - a * a * f.c2) = 0 := by
      linear_combination e3 + e4 - 2 * f.c2 * (a * a) * ha
    exact (mul_eq_zero.mp h).resolve_left h2
  have hc0 : f.c0 = 0 := by
    have h : (2 : ZMod q) * f.c0 = 0 := by linear_combination he1 + he2
    exact (mul_eq_zero.mp h).resolve_left h2
  have hc2 : f.c2 = 0 := by
    have h : (2 : ZMod q) * (a * a * f.c2) = 0 := by linear_combination he1 - he2
    have h' := (mul_eq_zero.mp h).resolve_left h2
    exact (mul_eq_zero.mp h').resolve_left (mul_ne_zero ha0 ha0)
  have ho1 : f.c1 + a * a * f.c3 = 0 := by
    have h : (2 : ZMod q) * (a * (f.c1 + a * a * f.c3)) = 0 := by linear_combination e1 - e2
    have h' := (mul_eq_zero.mp h).resolve_left h2
    exact (mul_eq_zero.mp h').resolve_left ha0
  have ho2 : a * a * f.c1 + f.c3 = 0 := by
    have h : (2 : ZMod q) * (a * (a * a * f.c1 + f.c3)) = 0 := by
      linear_combination e3 - e4 - 2 * f.c3 * a * (a * a * (a * a) - 1) * ha
    have h' := (mul_eq_zero.mp h).resolve_left h2
    exact (mul_eq_zero.mp h').resolve_left ha0
  have hc3 : f.c3 = 0 := by
    have h : (2 : ZMod q) * f.c3 = 0 := by
      linear_combination (-(a * a)) * ho1 + ho2 + f.c3 * ha
    exact (mul_eq_zero.mp h).resolve_left h2
  have hc1 : f.c1 = 0 := by
    have h := ho1
    rw [hc3, mul_zero, add_zero] at h
    exact h
  refine Quart.ext4 ?_ ?_ ?_ ?_ <;> simp [hc0, hc1, hc2, hc3]

/-- Finite commutative ring: a non-zero-divisor is a unit (left-multiplication is injective,
hence surjective, hence hits `1`). -/
theorem isUnit_of_mul_cancel {R : Type*} [CommRing R] [Finite R] {f : R}
    (hcancel : ∀ g : R, f * g = 0 → g = 0) : IsUnit f := by
  have hinj : Function.Injective (fun g : R => f * g) := by
    intro g g' h
    have hsub : f * (g - g') = 0 := by
      simp only at h
      rw [mul_sub, h, sub_self]
    exact sub_eq_zero.mp (hcancel _ hsub)
  obtain ⟨g, hg⟩ := Finite.injective_iff_surjective.mp hinj 1
  exact ⟨⟨f, g, hg, by rw [mul_comm]; exact hg⟩, rfl⟩

/-- **THE n = 4 UNIT THEOREM, PARAMETRIC (fully-split family)**: prime `q` with a root
`a⁴ = −1` (⟺ `q ≡ 1 mod 8`) and `2 ≠ 0`. Every nonzero `f ∈ ℤ_q[X]/(X⁴+1)` with
`18·‖f‖∞⁴ < q` is a UNIT. Min-norm at each of the four linear factors ⇒ `f` survives every
evaluation ⇒ `f` is a non-zero-divisor (CRT injectivity) ⇒ unit (finite ring). -/
theorem low_norm_isUnit_quartic [Fact q.Prime] {a : ZMod q} (ha : a * a * (a * a) = -1)
    (h2 : (2 : ZMod q) ≠ 0) {f : Quart q} (hf : f ≠ 0)
    (hν : 18 * normInf f ^ 4 < q) : IsUnit f := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hmin : ∀ b : ZMod q, b * b * (b * b) = -1 → evalQ b f ≠ 0 := fun b hb =>
    factor_nonzero_of_norm_lt (evalQ b) normInf (normInf f + 1)
      (minNorm_quartic_linear hb hν) hf (Nat.lt_succ_self _)
  apply isUnit_of_mul_cancel
  intro g hg
  refine eq_zero_of_evalQ_four ha h2 ?_ ?_ ?_ ?_
  · have h := congrArg (evalQ a) hg
    rw [evalQ_mul ha, evalQ_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (hmin a ha)
  · have h := congrArg (evalQ (-a)) hg
    rw [evalQ_mul (root_neg ha), evalQ_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (hmin _ (root_neg ha))
  · have h := congrArg (evalQ (a * a * a)) hg
    rw [evalQ_mul (root_cube ha), evalQ_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (hmin _ (root_cube ha))
  · have h := congrArg (evalQ (-(a * a * a))) hg
    rw [evalQ_mul (root_neg (root_cube ha)), evalQ_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (hmin _ (root_neg (root_cube ha)))

/-- The challenge-difference form at `n = 4`, parametric over the fully-split family. -/
theorem challenge_diff_isUnit_quartic [Fact q.Prime] {a : ZMod q}
    (ha : a * a * (a * a) = -1) (h2 : (2 : ZMod q) ≠ 0) {c c' : Quart q} (hcc : c ≠ c')
    (hν : 18 * normInf (c - c') ^ 4 < q) : IsUnit (c - c') :=
  low_norm_isUnit_quartic ha h2 (sub_ne_zero.mpr hcc) hν

end Quartic

/-! ### Non-vacuity of the quartic branch: q = 41 (`3⁴ = 81 = −1`), a real ternary-style
challenge difference certified a unit by the PARAMETRIC theorem — `Quart 41` has 2.8M
elements, far beyond any `decide`; the parametric bound does not care. -/

instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩

theorem three_quartic_root_41 : (3 : ZMod 41) * 3 * ((3 : ZMod 41) * 3) = -1 := by decide

theorem two_ne_zero_41 : (2 : ZMod 41) ≠ 0 := by decide

/-- Fork challenges over `R₄₁ = ℤ₄₁[X]/(X⁴+1)`: `c = 1 + X`, `c' = X³` (binary, like a real
challenge set). Difference `1 + X − X³` has ∞-norm 1 and `18·1⁴ = 18 < 41`. -/
def c41 : Quart 41 := ⟨1, 1, 0, 0⟩

def c41' : Quart 41 := ⟨0, 0, 0, 1⟩

theorem c41_distinct : c41 ≠ c41' := by decide

theorem c41_diff_norm : normInf (c41 - c41') = 1 := by decide

theorem c41_diff_isUnit : IsUnit (c41 - c41') :=
  challenge_diff_isUnit_quartic three_quartic_root_41 two_ne_zero_41 c41_distinct (by decide)

#assert_axioms caval_eq_natAbs_valMinAbs
#assert_axioms int_eq_zero_of_zmod_zero_of_lt
#assert_axioms neg_one_nonsquare
#assert_axioms isUnit_of_ne_zero_inert
#assert_axioms challenge_diff_isUnit_inert
#assert_axioms c11_diff_isUnit
#assert_axioms c11_inv_verifies
#assert_axioms quad13_zero_divisor
#assert_axioms quad13_nonzero_nonunit
#assert_axioms toLin_mul
#assert_axioms sq_add_sq_eq_zero_of_ker
#assert_axioms minNorm_linear_factor
#assert_axioms crtLin
#assert_axioms low_norm_isUnit_split
#assert_axioms low_norm_isUnit_mod_four_eq_one
#assert_axioms challenge_diff_isUnit_all_odd_primes
#assert_axioms minNorm13_decided
#assert_axioms minNorm13_parametric
#assert_axioms c13_diff_isUnit
#assert_axioms c13_inv_verifies
#assert_axioms sharp13_not_unit
#assert_axioms norm_threshold_sharp_13
#assert_axioms q5_not_unit
#assert_axioms w101_isUnit
#assert_axioms evalQ_mul
#assert_axioms root_neg
#assert_axioms root_cube
#assert_axioms evalQ_mul_neg
#assert_axioms formPQ_eq_zero_of_ker
#assert_axioms two_mul_sq_eq_sq
#assert_axioms formPQ_anisotropic
#assert_axioms formPQ_bound
#assert_axioms minNorm_quartic_linear
#assert_axioms eq_zero_of_evalQ_four
#assert_axioms isUnit_of_mul_cancel
#assert_axioms low_norm_isUnit_quartic
#assert_axioms challenge_diff_isUnit_quartic
#assert_axioms three_quartic_root_41
#assert_axioms c41_distinct
#assert_axioms c41_diff_norm
#assert_axioms c41_diff_isUnit

end Dregg2.Crypto.InvertibilityNormGen
