/-
# `Dregg2.Crypto.InvertibilityNorm` — the norm side of general-`n` challenge-difference invertibility.

`InvertibilityCRT.challenge_diff_isUnit_general` reduces invertibility in `R_q ≅ ∏ Kᵢ` to `hnz`:
the challenge difference is NONZERO in every CRT factor. This file supplies `hnz` from a NORM bound —
the Lyubashevsky–Seiler step (IACR 2018/786): a nonzero element whose coefficient ∞-norm is below the
minimum ∞-norm of the nonzero elements of the ideal `(gᵢ)` cannot vanish mod `gᵢ`.

**What is PROVED here (no `sorry`, all `#assert_axioms`-clean):**

1. *The framework, norm side* (general `R`): `factor_nonzero_of_norm_lt` — below the ideal's min-norm,
   a nonzero element does not vanish in the factor — and `isUnit_of_norm_lt_ideal_min`, which chains it
   through `InvertibilityCRT.isUnit_of_crt_nonzero` to give: nonzero + ∞-norm below every factor's
   min-norm ⇒ UNIT. The min-norm-of-ideal is the stated interface hypothesis.
2. *The concrete `n = 4` case, done fully*: `R_5 = ℤ_5[X]/(X⁴+1)` (`Quart 5`, the negacyclic 4-tuple
   model; `5 ≡ 5 mod 8`, so `X⁴+1 = (X²−2)(X²+2)` splits into two irreducible quadratics). The CRT ring
   isomorphism `Quart q ≃+* Quad q r × Quad q r'` is CONSTRUCTED for any `q, r` with `r² = −1`,
   `r' = −r`, `2` invertible (`crtEquiv`) — `map_mul` proved algebraically, not decided. The residue
   rings `Quad q r` (`ℤ_q[Y]/(Y²−r)`) have every nonzero element a unit when `r` is a non-square
   (explicit inverse via the anisotropic norm `a² − r·b²`, generalizing `HermineInvertibility`'s `r = −1`).
3. *The min-norm bound discharged* (the number-theoretic heart, at `q = 5, d = 2`): every nonzero
   multiple of `X²∓2` in `R_5` has coefficient ∞-norm ≥ 2 (`minNorm_factor₁/₂`, decided over all 625
   elements — note `2 ≤ √5 = q^(d/n)`, the Lyubashevsky–Seiler threshold shape). Hence
   `low_norm_isUnit`: EVERY nonzero `f : R_5` with `‖f‖∞ < 2` is a unit, and
   `challenge_diff_isUnit_of_low_norm₅`: distinct challenges with low-norm difference invert.
4. *Anti-vacuity, both directions*: the concrete challenge difference `δ = 1 − X²` (`‖δ‖∞ = 1`) is a
   unit with EXHIBITED inverse `3 + 3X²` (`δ·δ⁻¹ = 1` decided), AND the bound is SHARP: `X² + 2` is
   nonzero of ∞-norm exactly 2 and is NOT a unit (it vanishes in the second CRT factor) — the norm
   hypothesis has teeth.

**The remaining gap, honestly:** the GENERAL Lyubashevsky–Seiler bound — for arbitrary prime `q` and
`n = 2^k` with `X^n + 1` splitting into `n/d` irreducible degree-`d` factors, every nonzero multiple of
a factor has ∞-norm ≥ `q^(d/n)/s` (their Lemma 2.2/Corollary 1.2, via the `2n`-th-root structure of the
factor's roots and a resultant/geometry-of-numbers argument). That is research-level Mathlib work
(cyclotomic factorization mod `q` + coefficient bounds); here it enters only as the min-norm interface
hypothesis of (1), discharged by decision at `q = 5, n = 4`. Nothing below fakes it.
-/
import Dregg2.Crypto.InvertibilityCRT
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime

namespace Dregg2.Crypto.InvertibilityNorm

/-! ## 1. The framework, norm side: below the ideal's min-norm ⇒ nonzero in the factor ⇒ unit -/

variable {R : Type*} [CommRing R]

/-- **The norm→nonzero-per-factor step, as a clean structural lemma.** If every nonzero element of the
kernel of the factor map `ρ` (the ideal `(gᵢ)`) has ∞-norm at least `B`, then a nonzero `f` with
`ν f < B` cannot map to zero. This is the exact shape of the Lyubashevsky–Seiler argument; the
min-norm-of-the-ideal bound `hmin` is the number-theoretic interface, discharged concretely below. -/
theorem factor_nonzero_of_norm_lt {K : Type*} [Zero K] (ρ : R → K) (ν : R → ℕ) (B : ℕ)
    (hmin : ∀ x : R, ρ x = 0 → x ≠ 0 → B ≤ ν x)
    {f : R} (hf : f ≠ 0) (hν : ν f < B) : ρ f ≠ 0 :=
  fun h => absurd (hmin f h hf) (not_le.mpr hν)

/-- **The framework theorem: low norm ⇒ unit.** Chains the min-norm bound through the CRT reduction
`InvertibilityCRT.isUnit_of_crt_nonzero`: a nonzero `f` whose ∞-norm is below the min-norm of every
factor ideal is nonzero in every CRT factor, hence a unit. This is the Lyubashevsky–Seiler skeleton
with the per-factor min-norm bounds `B i` as the stated hypothesis. -/
theorem isUnit_of_norm_lt_ideal_min {ι : Type*} {K : ι → Type*} [∀ i, Field (K i)]
    (φ : R ≃+* ∀ i, K i) (ν : R → ℕ) (B : ι → ℕ)
    (hmin : ∀ i, ∀ x : R, φ x i = 0 → x ≠ 0 → B i ≤ ν x)
    {f : R} (hf : f ≠ 0) (hν : ∀ i, ν f < B i) : IsUnit f :=
  Dregg2.Crypto.InvertibilityCRT.isUnit_of_crt_nonzero φ fun i =>
    factor_nonzero_of_norm_lt (fun x => φ x i) ν (B i) (hmin i) hf (hν i)

/-- The challenge-difference form: distinct challenges whose difference has ∞-norm below every
factor's min-norm have INVERTIBLE difference — `hnz` of
`InvertibilityCRT.challenge_diff_isUnit_general` supplied by the norm bound. -/
theorem challenge_diff_isUnit_of_norm_lt {ι : Type*} {K : ι → Type*} [∀ i, Field (K i)]
    (φ : R ≃+* ∀ i, K i) (ν : R → ℕ) (B : ι → ℕ)
    (hmin : ∀ i, ∀ x : R, φ x i = 0 → x ≠ 0 → B i ≤ ν x)
    {c c' : R} (hcc : c ≠ c') (hν : ∀ i, ν (c - c') < B i) : IsUnit (c - c') :=
  isUnit_of_norm_lt_ideal_min φ ν B hmin (sub_ne_zero.mpr hcc) hν

/-! ## 2a. The CRT residue ring `Quad q r = ℤ_q[Y]/(Y² − r)` — nonzero ⇒ unit when `r` is a non-square

Generalizes `HermineInvertibility.GaussMod` (which is `r = −1`): pairs `a + bY` with `Y² = r`. -/

/-- `ℤ_q[Y]/(Y² − r)`, modeled as pairs with `Y² = r`. For `r` a non-square mod prime `q` this is the
field `𝔽_{q²}` — the residue field of an irreducible quadratic factor of `X⁴ + 1`. -/
structure Quad (q : ℕ) (r : ZMod q) where
  re : ZMod q
  im : ZMod q
  deriving DecidableEq

namespace Quad

variable {q : ℕ} {r : ZMod q}

@[ext] theorem ext2 {a b : Quad q r} (hre : a.re = b.re) (him : a.im = b.im) : a = b := by
  cases a; cases b; cases hre; cases him; rfl

instance : Zero (Quad q r) := ⟨⟨0, 0⟩⟩
instance : One (Quad q r) := ⟨⟨1, 0⟩⟩
instance : Add (Quad q r) := ⟨fun a b => ⟨a.re + b.re, a.im + b.im⟩⟩
instance : Neg (Quad q r) := ⟨fun a => ⟨-a.re, -a.im⟩⟩
/-- `(a + bY)(c + dY) = (ac + r·bd) + (ad + bc)Y` since `Y² = r`. -/
instance : Mul (Quad q r) := ⟨fun a b => ⟨a.re * b.re + r * (a.im * b.im), a.re * b.im + a.im * b.re⟩⟩

@[simp] theorem zero_re : (0 : Quad q r).re = 0 := rfl
@[simp] theorem zero_im : (0 : Quad q r).im = 0 := rfl
@[simp] theorem one_re : (1 : Quad q r).re = 1 := rfl
@[simp] theorem one_im : (1 : Quad q r).im = 0 := rfl
@[simp] theorem add_re (a b : Quad q r) : (a + b).re = a.re + b.re := rfl
@[simp] theorem add_im (a b : Quad q r) : (a + b).im = a.im + b.im := rfl
@[simp] theorem neg_re (a : Quad q r) : (-a).re = -a.re := rfl
@[simp] theorem neg_im (a : Quad q r) : (-a).im = -a.im := rfl
@[simp] theorem mul_re (a b : Quad q r) : (a * b).re = a.re * b.re + r * (a.im * b.im) := rfl
@[simp] theorem mul_im (a b : Quad q r) : (a * b).im = a.re * b.im + a.im * b.re := rfl

/-- The `CommRing` axioms, proved componentwise over `ZMod q` by `ring`. -/
instance : CommRing (Quad q r) where
  add := (· + ·)
  zero := 0
  neg := (- ·)
  mul := (· * ·)
  one := 1
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc a b c := by ext <;> simp <;> ring
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp <;> ring
  neg_add_cancel a := by ext <;> simp
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  mul_comm a b := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp

/-- The quadratic norm `N(a + bY) = a² − r·b²` — anisotropic exactly when `r` is a non-square. -/
def qnorm (a : Quad q r) : ZMod q := a.re * a.re - r * (a.im * a.im)

/-- The explicit inverse candidate `(a + bY)⁻¹ = (a − bY)·N⁻¹`. -/
def qinv (a : Quad q r) : Quad q r := ⟨a.re * (qnorm a)⁻¹, -(a.im * (qnorm a)⁻¹)⟩

/-- **Anisotropy.** For prime `q` and `r` a NON-square, `a² − r·b² = 0` forces `a = b = 0` (else
`(a·b⁻¹)² = r`). This is the `r = −1, q ≡ 3 mod 4` argument of `HermineInvertibility`, generalized. -/
theorem qnorm_eq_zero_iff [Fact q.Prime] (hns : ∀ x : ZMod q, x * x ≠ r) (a : Quad q r) :
    qnorm a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h₀ : a.re * a.re - r * (a.im * a.im) = 0 := h
    by_cases him : a.im = 0
    · refine ext2 ?_ him
      have hre : a.re * a.re = 0 := by rw [him] at h₀; simpa using h₀
      simpa using mul_self_eq_zero.mp hre
    · exfalso
      have h2 : a.re * a.re = r * (a.im * a.im) := by linear_combination h₀
      have key : (a.re * a.im⁻¹) * (a.re * a.im⁻¹) = r := by
        calc (a.re * a.im⁻¹) * (a.re * a.im⁻¹)
            = (a.re * a.re) * (a.im⁻¹ * a.im⁻¹) := by ring
          _ = (r * (a.im * a.im)) * (a.im⁻¹ * a.im⁻¹) := by rw [h2]
          _ = r * ((a.im * a.im⁻¹) * (a.im * a.im⁻¹)) := by ring
          _ = r := by rw [mul_inv_cancel₀ him]; ring
      exact hns _ key
  · rintro rfl
    simp [qnorm]

/-- The exhibited inverse WORKS: `a · qinv a = 1` for nonzero `a` (non-square `r`). -/
theorem mul_qinv_cancel [Fact q.Prime] (hns : ∀ x : ZMod q, x * x ≠ r) {a : Quad q r}
    (ha : a ≠ 0) : a * qinv a = 1 := by
  have hN : qnorm a ≠ 0 := fun h => ha ((qnorm_eq_zero_iff hns a).mp h)
  have hNN : (a.re * a.re - r * (a.im * a.im)) * (qnorm a)⁻¹ = 1 := mul_inv_cancel₀ hN
  refine ext2 ?_ ?_
  · show a.re * (a.re * (qnorm a)⁻¹) + r * (a.im * -(a.im * (qnorm a)⁻¹)) = 1
    linear_combination hNN
  · show a.re * -(a.im * (qnorm a)⁻¹) + a.im * (a.re * (qnorm a)⁻¹) = 0
    ring

/-- **Every nonzero element of the residue ring is a unit** — inverse EXHIBITED, not summoned.
(`Y² − r` irreducible for non-square `r`, so the quotient is the field `𝔽_{q²}`.) -/
theorem isUnit_of_ne_zero [Fact q.Prime] (hns : ∀ x : ZMod q, x * x ≠ r) {a : Quad q r}
    (ha : a ≠ 0) : IsUnit a :=
  ⟨⟨a, qinv a, mul_qinv_cancel hns ha, by rw [mul_comm]; exact mul_qinv_cancel hns ha⟩, rfl⟩

end Quad

/-! ## 2b. The ring `Quart q = ℤ_q[X]/(X⁴ + 1)` — the `n = 4` negacyclic model -/

/-- `R_q = ℤ_q[X]/(X⁴ + 1)`: coefficients `c0 + c1·X + c2·X² + c3·X³` with `X⁴ = −1`
(negacyclic convolution). Computable and decidable. -/
structure Quart (q : ℕ) where
  c0 : ZMod q
  c1 : ZMod q
  c2 : ZMod q
  c3 : ZMod q
  deriving DecidableEq

namespace Quart

variable {q : ℕ}

@[ext] theorem ext4 {a b : Quart q} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) (h2 : a.c2 = b.c2)
    (h3 : a.c3 = b.c3) : a = b := by
  cases a; cases b; cases h0; cases h1; cases h2; cases h3; rfl

instance : Zero (Quart q) := ⟨⟨0, 0, 0, 0⟩⟩
instance : One (Quart q) := ⟨⟨1, 0, 0, 0⟩⟩
instance : Add (Quart q) := ⟨fun a b => ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3⟩⟩
instance : Neg (Quart q) := ⟨fun a => ⟨-a.c0, -a.c1, -a.c2, -a.c3⟩⟩
/-- Negacyclic multiplication: `(f·g)_k = Σ_{i+j=k} f_i g_j − Σ_{i+j=k+4} f_i g_j` (`X⁴ = −1`). -/
instance : Mul (Quart q) :=
  ⟨fun a b =>
    ⟨a.c0 * b.c0 - a.c1 * b.c3 - a.c2 * b.c2 - a.c3 * b.c1,
     a.c0 * b.c1 + a.c1 * b.c0 - a.c2 * b.c3 - a.c3 * b.c2,
     a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 - a.c3 * b.c3,
     a.c0 * b.c3 + a.c1 * b.c2 + a.c2 * b.c1 + a.c3 * b.c0⟩⟩

@[simp] theorem zero_c0 : (0 : Quart q).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : Quart q).c1 = 0 := rfl
@[simp] theorem zero_c2 : (0 : Quart q).c2 = 0 := rfl
@[simp] theorem zero_c3 : (0 : Quart q).c3 = 0 := rfl
@[simp] theorem one_c0 : (1 : Quart q).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : Quart q).c1 = 0 := rfl
@[simp] theorem one_c2 : (1 : Quart q).c2 = 0 := rfl
@[simp] theorem one_c3 : (1 : Quart q).c3 = 0 := rfl
@[simp] theorem add_c0 (a b : Quart q) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Quart q) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem add_c2 (a b : Quart q) : (a + b).c2 = a.c2 + b.c2 := rfl
@[simp] theorem add_c3 (a b : Quart q) : (a + b).c3 = a.c3 + b.c3 := rfl
@[simp] theorem neg_c0 (a : Quart q) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : Quart q) : (-a).c1 = -a.c1 := rfl
@[simp] theorem neg_c2 (a : Quart q) : (-a).c2 = -a.c2 := rfl
@[simp] theorem neg_c3 (a : Quart q) : (-a).c3 = -a.c3 := rfl
@[simp] theorem mul_c0 (a b : Quart q) :
    (a * b).c0 = a.c0 * b.c0 - a.c1 * b.c3 - a.c2 * b.c2 - a.c3 * b.c1 := rfl
@[simp] theorem mul_c1 (a b : Quart q) :
    (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 - a.c2 * b.c3 - a.c3 * b.c2 := rfl
@[simp] theorem mul_c2 (a b : Quart q) :
    (a * b).c2 = a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 - a.c3 * b.c3 := rfl
@[simp] theorem mul_c3 (a b : Quart q) :
    (a * b).c3 = a.c0 * b.c3 + a.c1 * b.c2 + a.c2 * b.c1 + a.c3 * b.c0 := rfl

/-- The `CommRing` axioms, proved componentwise by `ring` (each is a polynomial identity). -/
instance : CommRing (Quart q) where
  add := (· + ·)
  zero := 0
  neg := (- ·)
  mul := (· * ·)
  one := 1
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc a b c := by ext <;> simp <;> ring
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp <;> ring
  neg_add_cancel a := by ext <;> simp
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  mul_comm a b := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp

/-- Enumeration equivalence — used only to make `∀ f : Quart q, …` decidable for the min-norm facts. -/
def equivProd (q : ℕ) : Quart q ≃ (ZMod q × ZMod q) × ZMod q × ZMod q where
  toFun f := ((f.c0, f.c1), f.c2, f.c3)
  invFun p := ⟨p.1.1, p.1.2, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [NeZero q] : Fintype (Quart q) := Fintype.ofEquiv _ (equivProd q).symm

/-- The centered absolute value of a coefficient: `|x̂|` for the representative of minimal
absolute value. -/
def caval (x : ZMod q) : ℕ := min x.val (q - x.val)

/-- The coefficient ∞-norm on `R_q`: the max centered absolute value over the four coefficients —
the norm of the Lyubashevsky–Seiler bound. -/
def normInf (f : Quart q) : ℕ :=
  max (max (caval f.c0) (caval f.c1)) (max (caval f.c2) (caval f.c3))

end Quart

/-! ## 2c. The CRT for `X⁴ + 1 = (X² − r)(X² − r')` with `r² = −1`, `r' = −r` — constructed, general -/

section CRT

variable {q : ℕ} {r r' half : ZMod q}

/-- The factor map `X² ↦ r`: reduction of `f mod (X² − r)`, landing in `Quad q r`. -/
def toQuad (r : ZMod q) (f : Quart q) : Quad q r := ⟨f.c0 + r * f.c2, f.c1 + r * f.c3⟩

@[simp] theorem toQuad_re (f : Quart q) : (toQuad r f).re = f.c0 + r * f.c2 := rfl
@[simp] theorem toQuad_im (f : Quart q) : (toQuad r f).im = f.c1 + r * f.c3 := rfl

/-- `toQuad` is multiplicative, given `r² = −1` (so `X⁴ = (X²)² ↦ r² = −1` is respected).
Proved algebraically — each component is a polynomial identity modulo `r² + 1 = 0`. -/
theorem toQuad_mul (hr : r * r = -1) (f g : Quart q) :
    toQuad r (f * g) = toQuad r f * toQuad r g := by
  refine Quad.ext2 ?_ ?_
  · simp only [toQuad_re, toQuad_im, Quad.mul_re, Quart.mul_c0, Quart.mul_c2]
    linear_combination (-(f.c1 * g.c3 + f.c2 * g.c2 + f.c3 * g.c1 + f.c3 * g.c3 * r)) * hr
  · simp only [toQuad_re, toQuad_im, Quad.mul_im, Quart.mul_c1, Quart.mul_c3]
    linear_combination (-(f.c2 * g.c3 + f.c3 * g.c2)) * hr

/-- The factor map as a ring hom `R_q →+* R_q/(X² − r)`. -/
def toQuadHom (hr : r * r = -1) : Quart q →+* Quad q r where
  toFun := toQuad r
  map_one' := by refine Quad.ext2 ?_ ?_ <;> simp
  map_mul' := toQuad_mul hr
  map_zero' := by refine Quad.ext2 ?_ ?_ <;> simp
  map_add' f g := by refine Quad.ext2 ?_ ?_ <;> simp <;> ring

@[simp] theorem toQuadHom_apply (hr : r * r = -1) (f : Quart q) :
    toQuadHom hr f = toQuad r f := rfl

/-- The inverse of the CRT pairing: interpolation from the two residues (`half = 2⁻¹`;
`r⁻¹ = −r` since `r² = −1`). -/
def fromQuads (half : ZMod q) (p : Quad q r × Quad q r') : Quart q :=
  ⟨(p.1.re + p.2.re) * half, (p.1.im + p.2.im) * half,
   (p.1.re - p.2.re) * half * (-r), (p.1.im - p.2.im) * half * (-r)⟩

/-- **The CRT ring isomorphism, CONSTRUCTED**: `ℤ_q[X]/(X⁴+1) ≃+* ℤ_q[Y]/(Y²−r) × ℤ_q[Y]/(Y²+r)`
for any `q, r` with `r² = −1` and `2` invertible. This is the general `q ≡ 5 (mod 8)` splitting —
the two-factor instance of the `φ` that `InvertibilityCRT.challenge_diff_isUnit_general` consumes.
Both directions and both hom laws are proved algebraically (`linear_combination` over `r² = −1`,
`2·half = 1`), not decided. -/
def crtEquiv (hr : r * r = -1) (hopp : r' = -r) (h2 : 2 * half = 1) :
    Quart q ≃+* Quad q r × Quad q r' where
  toFun f := (toQuad r f, toQuad r' f)
  invFun := fromQuads half
  left_inv f := by
    subst hopp
    refine Quart.ext4 ?_ ?_ ?_ ?_ <;>
      simp only [fromQuads, toQuad_re, toQuad_im]
    · linear_combination f.c0 * h2
    · linear_combination f.c1 * h2
    · linear_combination (-(2 * f.c2 * half)) * hr + f.c2 * h2
    · linear_combination (-(2 * f.c3 * half)) * hr + f.c3 * h2
  right_inv p := by
    subst hopp
    refine Prod.ext ?_ ?_ <;> refine Quad.ext2 ?_ ?_ <;>
      simp only [fromQuads, toQuad_re, toQuad_im]
    · linear_combination (-(p.1.re - p.2.re) * half) * hr + p.1.re * h2
    · linear_combination (-(p.1.im - p.2.im) * half) * hr + p.1.im * h2
    · linear_combination ((p.1.re - p.2.re) * half) * hr + p.2.re * h2
    · linear_combination ((p.1.im - p.2.im) * half) * hr + p.2.im * h2
  map_mul' f g := by
    have hr' : r' * r' = -1 := by rw [hopp]; linear_combination hr
    exact Prod.ext (toQuad_mul hr f g) (toQuad_mul hr' f g)
  map_add' f g := by
    refine Prod.ext ?_ ?_ <;> refine Quad.ext2 ?_ ?_ <;> simp <;> ring

@[simp] theorem crtEquiv_apply (hr : r * r = -1) (hopp : r' = -r) (h2 : 2 * half = 1)
    (f : Quart q) : crtEquiv hr hopp h2 f = (toQuad r f, toQuad r' f) := rfl

/-- Units pull back through a ring isomorphism. -/
theorem isUnit_of_map_isUnit {S : Type*} [CommRing S] {R : Type*} [CommRing R] (e : R ≃+* S)
    {x : R} (h : IsUnit (e x)) : IsUnit x := by
  have h2 := h.map e.symm
  rwa [RingEquiv.symm_apply_apply] at h2

end CRT

/-! ## 3. The concrete case, done fully: `q = 5`, `X⁴ + 1 = (X² − 2)(X² + 2)` over `ℤ_5` -/

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- `2² = 4 = −1` in `ℤ_5` — `2` is the square root of `−1` that splits `X⁴ + 1`. -/
theorem two_sq : (2 : ZMod 5) * 2 = -1 := by decide

/-- `3 = −2` in `ℤ_5`: the second factor's root of `−1`. -/
theorem three_eq_neg_two : (3 : ZMod 5) = -(2 : ZMod 5) := by decide

/-- `2 · 3 = 1` in `ℤ_5`: `half = 3`. -/
theorem two_mul_three : (2 : ZMod 5) * 3 = 1 := by decide

theorem three_sq : (3 : ZMod 5) * 3 = -1 := by decide

/-- `2` is a non-square mod 5 (squares are `{0, 1, 4}`) — so `X² − 2` is irreducible. -/
theorem nonsquare_two : ∀ x : ZMod 5, x * x ≠ 2 := by decide

/-- `3 = −2` is a non-square mod 5 — so `X² + 2` is irreducible. -/
theorem nonsquare_three : ∀ x : ZMod 5, x * x ≠ 3 := by decide

/-- The concrete CRT isomorphism `ℤ_5[X]/(X⁴+1) ≃+* 𝔽_25 × 𝔽_25`. -/
def crt5 : Quart 5 ≃+* Quad 5 2 × Quad 5 3 := crtEquiv two_sq three_eq_neg_two two_mul_three

open Quart (normInf)

set_option maxRecDepth 20000 in
/-- **The min-norm-of-ideal bound, DISCHARGED (factor `X² − 2`)**: every nonzero multiple of
`X² − 2` in `R_5` has coefficient ∞-norm ≥ 2 — decided over all 625 elements. `2` is
`⌈√5⌉ = ⌈q^(d/n)⌉`: exactly the Lyubashevsky–Seiler threshold shape at `q = 5, n = 4, d = 2`. -/
theorem minNorm_factor₁ : ∀ f : Quart 5, toQuad 2 f = 0 → f ≠ 0 → 2 ≤ normInf f := by decide

set_option maxRecDepth 20000 in
/-- The same bound for the factor `X² + 2`, decided. -/
theorem minNorm_factor₂ : ∀ f : Quart 5, toQuad 3 f = 0 → f ≠ 0 → 2 ≤ normInf f := by decide

/-- **THE `n = 4` LYUBASHEVSKY–SEILER THEOREM, CONCRETE AND COMPLETE**: in
`R_5 = ℤ_5[X]/(X⁴ + 1)`, every nonzero element of coefficient ∞-norm `< 2` is a UNIT.
Norm below the ideal min-norm ⇒ nonzero in both CRT factors (the framework lemma) ⇒ unit in each
residue field (explicit inverses) ⇒ unit in `R_5` (pulled back through the constructed CRT iso). -/
theorem low_norm_isUnit {f : Quart 5} (hf : f ≠ 0) (hν : normInf f < 2) : IsUnit f := by
  have h₁ : toQuad 2 f ≠ 0 :=
    factor_nonzero_of_norm_lt (toQuad 2) normInf 2 (fun x => minNorm_factor₁ x) hf hν
  have h₂ : toQuad 3 f ≠ 0 :=
    factor_nonzero_of_norm_lt (toQuad 3) normInf 2 (fun x => minNorm_factor₂ x) hf hν
  refine isUnit_of_map_isUnit crt5 ?_
  rw [show crt5 f = (toQuad 2 f, toQuad 3 f) from rfl]
  exact Prod.isUnit_iff.mpr
    ⟨Quad.isUnit_of_ne_zero nonsquare_two h₁, Quad.isUnit_of_ne_zero nonsquare_three h₂⟩

/-- **The challenge-difference form at `n = 4`**: distinct challenges of `R_5` whose difference has
∞-norm `< 2` have INVERTIBLE difference — the `hinv` that `HermineDischarge` consumes, now at
`n = 4` from a norm bound, extending `HermineInvertibility`'s `n = 2` result. -/
theorem challenge_diff_isUnit_of_low_norm₅ {c c' : Quart 5} (hcc : c ≠ c')
    (hν : normInf (c - c') < 2) : IsUnit (c - c') :=
  low_norm_isUnit (sub_ne_zero.mpr hcc) hν

/-! ## 4. Anti-vacuity, both directions -/

/-- First fork challenge: `c = 1 + X` (binary coefficients, like a real challenge set). -/
def cFirst : Quart 5 := ⟨1, 1, 0, 0⟩

/-- Second fork challenge: `c' = X + X²`. -/
def cSecond : Quart 5 := ⟨0, 1, 1, 0⟩

/-- The challenge difference `δ = c − c' = 1 − X²`, computed by the ring's own subtraction. -/
def δ : Quart 5 := ⟨1, 0, 4, 0⟩

/-- The EXHIBITED inverse `δ⁻¹ = 3 + 3X²`: `(1 − X²)(3 + 3X²) = 3 − 3X⁴ = 3 + 3 = 6 = 1`. -/
def δInv : Quart 5 := ⟨3, 0, 3, 0⟩

/-- The difference really is `δ` — decided through the ring's subtraction. -/
theorem challenge_diff_eq : cFirst - cSecond = δ := by decide

/-- The challenges are genuinely distinct. -/
theorem challenges_distinct : cFirst ≠ cSecond := by decide

/-- `δ` is a real nonzero element of ∞-norm exactly 1 (coefficients `1` and `−1`). -/
theorem δ_ne_zero : δ ≠ 0 := by decide

theorem δ_norm : normInf δ = 1 := by decide

/-- Anti-vacuity leg 1: the exhibited inverse VERIFIES on the actual negacyclic arithmetic. -/
theorem δ_mul_δInv : δ * δInv = 1 := by decide

theorem δInv_mul_δ : δInv * δ = 1 := by decide

/-- `IsUnit δ` — built from the exhibited, verified inverse. -/
theorem δ_isUnit : IsUnit δ := ⟨⟨δ, δInv, δ_mul_δInv, δInv_mul_δ⟩, rfl⟩

/-- The concrete challenge-difference invertibility, from the exhibited inverse. -/
theorem concrete_challenge_diff_isUnit : IsUnit (cFirst - cSecond) :=
  challenge_diff_eq ▸ δ_isUnit

/-- Cross-check: the SAME fact falls out of the general `n = 4` norm theorem — distinctness plus
the decided norm bound alone, no inverse supplied. The two routes agree on a real element. -/
theorem concrete_challenge_diff_isUnit' : IsUnit (cFirst - cSecond) :=
  challenge_diff_isUnit_of_low_norm₅ challenges_distinct (by decide)

/-- The bad element `g = 2 + X²` (a unit multiple of the factor `X² + 2`): nonzero, ∞-norm
exactly 2. -/
def gBad : Quart 5 := ⟨2, 0, 1, 0⟩

theorem gBad_ne_zero : gBad ≠ 0 := by decide

theorem gBad_norm : normInf gBad = 2 := by decide

/-- `g` vanishes in the second CRT factor (`2 + 3·1 = 5 = 0`): it IS a multiple of `X² + 2`. -/
theorem gBad_kernel : toQuad 3 gBad = 0 := by decide

/-- **Anti-vacuity leg 2 — the norm bound has TEETH and is SHARP**: `g = 2 + X²` is a nonzero
element of ∞-norm exactly 2 (one more than the theorem's bound allows) and is NOT a unit — a unit
would stay a unit in the residue field, but `g` maps to `0` there. So `normInf f < 2` in
`low_norm_isUnit` cannot be weakened to `≤ 2`: the threshold is exactly the ideal's min-norm. -/
theorem gBad_not_isUnit : ¬ IsUnit gBad := by
  intro h
  have hu : IsUnit ((0 : Quad 5 3)) := by
    have hmap := h.map (toQuadHom three_sq)
    rwa [toQuadHom_apply, gBad_kernel] at hmap
  have h01 : (0 : Quad 5 3) = 1 := isUnit_zero_iff.mp hu
  exact absurd h01 (by decide)

/-- The sharpness statement, packaged: the norm-2 frontier contains a nonzero NON-unit. -/
theorem norm_bound_sharp : ∃ f : Quart 5, f ≠ 0 ∧ normInf f = 2 ∧ ¬ IsUnit f :=
  ⟨gBad, gBad_ne_zero, gBad_norm, gBad_not_isUnit⟩

/-! ## Axiom hygiene — every keystone kernel-clean (`decide` only; no `native_decide`) -/

#assert_axioms factor_nonzero_of_norm_lt
#assert_axioms isUnit_of_norm_lt_ideal_min
#assert_axioms challenge_diff_isUnit_of_norm_lt
#assert_axioms Quad.qnorm_eq_zero_iff
#assert_axioms Quad.mul_qinv_cancel
#assert_axioms Quad.isUnit_of_ne_zero
#assert_axioms toQuad_mul
#assert_axioms toQuadHom
#assert_axioms crtEquiv
#assert_axioms isUnit_of_map_isUnit
#assert_axioms crt5
#assert_axioms minNorm_factor₁
#assert_axioms minNorm_factor₂
#assert_axioms low_norm_isUnit
#assert_axioms challenge_diff_isUnit_of_low_norm₅
#assert_axioms challenge_diff_eq
#assert_axioms challenges_distinct
#assert_axioms δ_ne_zero
#assert_axioms δ_norm
#assert_axioms δ_mul_δInv
#assert_axioms δ_isUnit
#assert_axioms concrete_challenge_diff_isUnit
#assert_axioms concrete_challenge_diff_isUnit'
#assert_axioms gBad_ne_zero
#assert_axioms gBad_norm
#assert_axioms gBad_kernel
#assert_axioms gBad_not_isUnit
#assert_axioms norm_bound_sharp

end Dregg2.Crypto.InvertibilityNorm
