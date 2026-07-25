/-
# Dregg2.Crypto.BN254.TowerField — the extension-tower FIELD discharges.

With the base-field primality closed (`Primality.lean`: `Fact (Nat.Prime pBN254)`, `Field Fq`,
`Field Fp2`), this module discharges the two remaining tower field-obligations and BUILDS the two
tower `Field` instances, so the pairing's target group `Fp12` finally supports INVERSION.

## The two named goals (both reduced to a `Fp2` non-residue certificate).

* **`Fp6FieldGoal`** (`∀ x : Fp2, x³ ≠ ξ`, `ξ = 9 + u`): `ξ` is a NON-CUBE in `Fp2*`.  `Fp2` is a
  finite field of order `p²`, so `Fp2*` is cyclic of order `p²−1` (`3 ∣ p²−1` since `p ≡ 1 mod 3`).
  A cube root `x³ = ξ` (with `x ≠ 0`) forces `ξ^((p²−1)/3) = x^(p²−1) = 1`; but a kernel-checked
  modexp shows `ξ^((p²−1)/3) ≠ 1`.  Certificate `E3 = (p²−1)/3` (506 bits).

* **`Fp12FieldGoal`** (`∀ x : Fp6, x² ≠ v`): `v` is a NON-SQUARE in `Fp6*`.  Via the multiplicative
  cubic norm `N6 : Fp6 → Fp2` (`N6 v = ξ`), a square root `x² = v` forces `ξ = N6(x)²` to be a
  SQUARE in `Fp2` — contradicting a second kernel-checked modexp `ξ^((p²−1)/2) ≠ 1` (`ξ` non-square,
  `E2 = (p²−1)/2`, 507 bits).  This routes the `Fp6`-level obligation back to a cheap `Fp2` modexp,
  avoiding a ~1500-bit `Fp6` exponentiation.

## The field instances (House Law #1: authored in Lean; kernel-checked, no `sorry`/`axiom`/
`native_decide`).  Both mirror the `Fp2` construction (norm to the base + explicit inverse):

* `Field Fp6`: for `a ≠ 0` the cubic norm `N6 a ≠ 0` (adjugate `adj a` with `a · adj a = ofFp2 (N6 a)`;
  `N6 a = 0` forces `ξ` a cube via `adj (adj a) = ofFp2 (N6 a) · a`), so `a⁻¹ = adj a · ofFp2 (N6 a)⁻¹`.
* `Field Fp12`: for `a ≠ 0` the quadratic norm `N12 a = a0² − v·a1² ≠ 0` (else `v` a square in `Fp6`),
  so `a⁻¹ = conj a · ofFp6 (N12 a)⁻¹`.

The modexp is the fuel-structural square-and-multiply of `Primality.lean`, generalized to an
arbitrary monoid (`powMonFuel`): the kernel reduces it in `O(fuel)` steps (each an `Fp2` coordinate
product = a handful of GMP `Nat` mul/mod), NOT `Monoid.npow`'s `O(2^bits)`.
-/
import Dregg2.Crypto.BN254.Fp12
import Dregg2.Crypto.BN254.Primality
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.IntegralDomain

set_option autoImplicit false
-- The `Fp2` modexp folds recurse ~508 levels; the kernel `decide` needs the headroom.
set_option maxRecDepth 100000
-- The fuel bounds `E < 2^508` are checked by `decide`; raise the simp exponentiation gate to match.
set_option exponentiation.threshold 100000

namespace Dregg2.Crypto.BN254

/-! ## §1 Fuel-indexed monoid exponentiation (`Fp2`/`Fp6` reuse the same combinator). -/

/-- Square-and-multiply `x^e` in a monoid, as a FUEL-structural recursion so the kernel reduces it
in `O(fuel)` `*`-steps (vs. `Monoid.npow = npowRec`'s `O(e)`).  Base returns `1`. -/
def powMonFuel {M : Type*} [Monoid M] (x : M) : ℕ → ℕ → M
  | 0, _ => 1
  | fuel+1, e =>
      if e = 0 then 1
      else
        let half := powMonFuel x fuel (e / 2)
        let sq := half * half
        if e % 2 = 1 then sq * x else sq

/-- `powMonFuel` computes `x^e` whenever the fuel covers the exponent (`e < 2^fuel`).  One-time
induction on `fuel`; never evaluates the huge `x^e`. -/
theorem powMonFuel_correct {M : Type*} [Monoid M] (x : M) :
    ∀ (fuel e : ℕ), e < 2 ^ fuel → powMonFuel x fuel e = x ^ e := by
  intro fuel
  induction fuel with
  | zero => intro e he; simp only [pow_zero, Nat.lt_one_iff] at he; subst he; simp [powMonFuel]
  | succ fuel ih =>
      intro e he
      unfold powMonFuel
      by_cases h0 : e = 0
      · subst h0; simp
      · rw [if_neg h0, ih (e / 2) (by
          have : e < 2 ^ fuel * 2 := by rw [← pow_succ]; exact he
          omega)]
        have hsq : x ^ (e / 2) * x ^ (e / 2) = x ^ (2 * (e / 2)) := by
          rw [← pow_add]; congr 1; omega
        by_cases hpar : e % 2 = 1
        · rw [if_pos hpar, hsq, ← pow_succ]; congr 1; omega
        · rw [if_neg hpar, hsq]; congr 1; omega

/-! ## §2 `Fp2` is a finite field of order `p²`. -/

/-- `Fp2 ≃ Fq × Fq` (the coordinate pair), used only to transport `Fintype` and `card`. -/
def Fp2.equivProd : Fp2 ≃ Fq × Fq where
  toFun a := (a.c0, a.c1)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype Fp2 := Fintype.ofEquiv (Fq × Fq) Fp2.equivProd.symm

/-- `#Fp2 = p²`. -/
theorem card_fp2 : Fintype.card Fp2 = pBN254 * pBN254 := by
  rw [Fintype.card_congr Fp2.equivProd, Fintype.card_prod]
  simp [ZMod.card]

/-! ## §3 The two `Fp2` non-residue certificates (kernel-checked modexp). -/

/-- `E3 = (p²−1)/3` — the cube-non-residue exponent (`3 ∣ p²−1`, `506` bits). -/
def E3 : ℕ :=
  159698392005540947480662681738892913599750772177033607478815934084690031228792745815947017273145957323729410771604366753945418544713195649548797674289296

/-- `E2 = (p²−1)/2` — the square-non-residue exponent (`507` bits). -/
def E2 : ℕ :=
  239547588008311421220994022608339370399626158265550411218223901127035046843189118723920525909718935985594116157406550130918127817069793474323196511433944

/-- `3·E3 = p²−1` (so `E3 = (p²−1)/3`, exactly). -/
theorem three_mul_E3 : 3 * E3 = pBN254 * pBN254 - 1 := by norm_num [E3, pBN254]

/-- `2·E2 = p²−1` (so `E2 = (p²−1)/2`, exactly). -/
theorem two_mul_E2 : 2 * E2 = pBN254 * pBN254 - 1 := by norm_num [E2, pBN254]

/-- **`ξ` is a non-cube certificate**: `ξ^((p²−1)/3) ≠ 1` in `Fp2`, kernel-checked via `powMonFuel`
(508 fuel covers the 506-bit `E3`). -/
theorem xi_pow_E3_ne_one : xiFp2 ^ E3 ≠ 1 := by
  have hc := powMonFuel_correct xiFp2 508 E3 (by decide)
  rw [← hc]; decide

/-- **`ξ` is a non-square certificate**: `ξ^((p²−1)/2) ≠ 1` in `Fp2`, kernel-checked via `powMonFuel`
(508 fuel covers the 507-bit `E2`). -/
theorem xi_pow_E2_ne_one : xiFp2 ^ E2 ≠ 1 := by
  have hc := powMonFuel_correct xiFp2 508 E2 (by decide)
  rw [← hc]; decide

theorem xi_ne_zero : xiFp2 ≠ 0 := by
  intro h
  have : (1 : Fq) = 0 := congrArg Fp2.c1 h
  exact one_ne_zero this

/-! ## §4 `Fp6FieldGoal`: `ξ` is a non-cube ⇒ `X³ − ξ` irreducible over `Fp2`. -/

/-- **`Fp6FieldGoal` DISCHARGED.**  `ξ = 9 + u` has no cube root in `Fp2`: a root `x³ = ξ` (with
`x ≠ 0`) forces `ξ^E3 = x^(p²−1) = 1`, contradicting `xi_pow_E3_ne_one`. -/
theorem fp6FieldGoal_holds : Fp6.Fp6FieldGoal := by
  intro x hx3
  have hxne : x ≠ 0 := by
    rintro rfl
    exact xi_ne_zero (by rw [← hx3]; ring)
  apply xi_pow_E3_ne_one
  have hpow : x ^ (Fintype.card Fp2 - 1) = 1 := FiniteField.pow_card_sub_one_eq_one x hxne
  calc xiFp2 ^ E3 = (x ^ 3) ^ E3 := by rw [hx3]
    _ = x ^ (3 * E3) := by rw [← pow_mul]
    _ = x ^ (Fintype.card Fp2 - 1) := by rw [three_mul_E3, card_fp2]
    _ = 1 := hpow

/-! ## §5 `Field Fp6` via the cubic norm `N6 : Fp6 → Fp2` and its adjugate. -/

namespace Fp6

/-- The cubic field norm `N6 : Fp6 → Fp2` (the determinant of multiplication-by-`a`), a
multiplicative map to the base field; `Fp6` is a field exactly when `N6` is nonvanishing off `0`. -/
noncomputable def norm6 (a : Fp6) : Fp2 :=
  a.c0 ^ 3 + xiFp2 * a.c1 ^ 3 + xiFp2 ^ 2 * a.c2 ^ 3 - 3 * xiFp2 * a.c0 * a.c1 * a.c2

/-- The adjugate `adj : Fp6 → Fp6`, satisfying `a · adj a = ofFp2 (N6 a)` and
`adj (adj a) = ofFp2 (N6 a) · a` (the `3×3` `adj∘adj = det · id`). -/
noncomputable def adj (a : Fp6) : Fp6 :=
  ⟨a.c0 ^ 2 - xiFp2 * a.c1 * a.c2,
   xiFp2 * a.c2 ^ 2 - a.c0 * a.c1,
   a.c1 ^ 2 - a.c0 * a.c2⟩

@[simp] theorem adj_c0 (a : Fp6) : (adj a).c0 = a.c0 ^ 2 - xiFp2 * a.c1 * a.c2 := rfl
@[simp] theorem adj_c1 (a : Fp6) : (adj a).c1 = xiFp2 * a.c2 ^ 2 - a.c0 * a.c1 := rfl
@[simp] theorem adj_c2 (a : Fp6) : (adj a).c2 = a.c1 ^ 2 - a.c0 * a.c2 := rfl

/-- The base-`Fp2` embedding is multiplicative (lands the norm inverse back in `Fp6`). -/
theorem ofFp2_mul (x y : Fp2) : ofFp2 x * ofFp2 y = ofFp2 (x * y) := by
  ext <;> simp [ofFp2]

/-- `a · adj a = ofFp2 (N6 a)` — the key adjugate identity (char-free coordinate identity). -/
theorem mul_adj (a : Fp6) : a * adj a = ofFp2 (norm6 a) := by
  ext <;>
    simp only [mul_c0, mul_c1, mul_c2, adj_c0, adj_c1, adj_c2,
      ofFp2_c0, ofFp2_c1, ofFp2_c2, norm6] <;> ring

/-- `adj (adj a) = ofFp2 (N6 a) · a` — the `adj∘adj = det · id` identity (char-free). -/
theorem adj_adj (a : Fp6) : adj (adj a) = ofFp2 (norm6 a) * a := by
  ext <;>
    simp only [mul_c0, mul_c1, mul_c2, adj_c0, adj_c1, adj_c2,
      ofFp2_c0, ofFp2_c1, ofFp2_c2, norm6] <;> ring

/-- If `adj c = 0` and `c ≠ 0`, then `ξ` has a cube root in `Fp2` — impossible by
`fp6FieldGoal_holds`.  (The engine that turns a would-be zero divisor into a cube root.) -/
theorem adj_eq_zero_absurd (c : Fp6) (hc : c ≠ 0) (hadj : adj c = 0) : False := by
  have e0 : c.c0 ^ 2 - xiFp2 * c.c1 * c.c2 = 0 := by
    have := congrArg Fp6.c0 hadj; simpa using this
  have e1 : xiFp2 * c.c2 ^ 2 - c.c0 * c.c1 = 0 := by
    have := congrArg Fp6.c1 hadj; simpa using this
  have e2 : c.c1 ^ 2 - c.c0 * c.c2 = 0 := by
    have := congrArg Fp6.c2 hadj; simpa using this
  by_cases hc2 : c.c2 = 0
  · apply hc
    have hc0 : c.c0 = 0 := by
      have h : c.c0 * c.c0 = 0 := by rw [hc2] at e0; linear_combination e0
      exact mul_self_eq_zero.mp h
    have hc1 : c.c1 = 0 := by
      have h : c.c1 * c.c1 = 0 := by rw [hc0, hc2] at e2; linear_combination e2
      exact mul_self_eq_zero.mp h
    ext <;> simp [hc0, hc1, hc2]
  · refine fp6FieldGoal_holds (c.c1 * (c.c2)⁻¹) ?_
    have h1 : c.c0 * c.c1 = xiFp2 * c.c2 ^ 2 := by rw [sub_eq_zero] at e1; exact e1.symm
    have h2 : c.c1 ^ 2 = c.c0 * c.c2 := by rw [sub_eq_zero] at e2; exact e2
    have hinv : c.c2 * (c.c2)⁻¹ = 1 := mul_inv_cancel₀ hc2
    have hcube : c.c1 ^ 3 = xiFp2 * c.c2 ^ 3 := by
      calc c.c1 ^ 3 = c.c1 * c.c1 ^ 2 := by ring
        _ = c.c1 * (c.c0 * c.c2) := by rw [h2]
        _ = (c.c0 * c.c1) * c.c2 := by ring
        _ = (xiFp2 * c.c2 ^ 2) * c.c2 := by rw [h1]
        _ = xiFp2 * c.c2 ^ 3 := by ring
    calc (c.c1 * (c.c2)⁻¹) ^ 3
        = c.c1 ^ 3 * ((c.c2)⁻¹) ^ 3 := by ring
      _ = (xiFp2 * c.c2 ^ 3) * ((c.c2)⁻¹) ^ 3 := by rw [hcube]
      _ = xiFp2 * (c.c2 * (c.c2)⁻¹) ^ 3 := by ring
      _ = xiFp2 * (1 : Fp2) ^ 3 := by rw [hinv]
      _ = xiFp2 := by ring

/-- **The `Fp6` field obstruction is nonvanishing**: `a ≠ 0 → N6 a ≠ 0`.  If `N6 a = 0` then
`a · adj a = 0`; either `adj a = 0` (⇒ `ξ` a cube) or `adj a ≠ 0` with `adj (adj a) = 0`
(again ⇒ `ξ` a cube) — both impossible. -/
theorem norm6_ne_zero (a : Fp6) (ha : a ≠ 0) : norm6 a ≠ 0 := by
  intro hN
  by_cases hadj : adj a = 0
  · exact adj_eq_zero_absurd a ha hadj
  · have hz : ofFp2 (norm6 a) = 0 := by rw [hN]; rfl
    have hadjadj : adj (adj a) = 0 := by rw [adj_adj, hz, zero_mul]
    exact adj_eq_zero_absurd (adj a) hadj hadjadj

/-- **`Fp6` is a genuine field.**  `a⁻¹ = adj a · ofFp2 (N6 a)⁻¹` (from `a · adj a = ofFp2 (N6 a)`
and `N6 a ≠ 0`); packaged as `IsField Fp6`.  Mirrors the `Fp2` construction. -/
theorem fp6_isField : IsField Fp6 where
  exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (α := Fp2) (by simpa using congrArg Fp6.c0 h)⟩
  mul_comm := mul_comm
  mul_inv_cancel := by
    intro a ha
    have hn : norm6 a ≠ 0 := norm6_ne_zero a ha
    refine ⟨adj a * ofFp2 ((norm6 a)⁻¹), ?_⟩
    rw [← mul_assoc, mul_adj, ofFp2_mul, mul_inv_cancel₀ hn]; rfl

/-- The `Field Fp6` instance — the cubic tower level is now an actual field. -/
noncomputable instance : Field Fp6 := fp6_isField.toField

/-- `N6 v = ξ` (the norm of the cubic generator is the non-residue itself). -/
theorem norm6_v : norm6 v = xiFp2 := by
  simp only [norm6, v]; ring

/-- `N6` is multiplicative (char-free coordinate identity) — routes the `Fp12` non-square check
back to `Fp2`. -/
theorem norm6_mul (a b : Fp6) : norm6 (a * b) = norm6 a * norm6 b := by
  simp only [norm6, mul_c0, mul_c1, mul_c2]; ring

end Fp6

/-! ## §6 `ξ` is a non-square in `Fp2` (the second `Fp2` modexp certificate, packaged). -/

/-- `ξ` is not a square in `Fp2`: a root `ξ = r·r` forces `ξ^E2 = r^(p²−1) = 1`, contradicting
`xi_pow_E2_ne_one`. -/
theorem xi_not_isSquare : ¬ IsSquare (xiFp2 : Fp2) := by
  rintro ⟨r, hr⟩
  have hr0 : r ≠ 0 := fun h => xi_ne_zero (by rw [hr, h, mul_zero])
  apply xi_pow_E2_ne_one
  have hpow : r ^ (Fintype.card Fp2 - 1) = 1 := FiniteField.pow_card_sub_one_eq_one r hr0
  calc xiFp2 ^ E2 = (r * r) ^ E2 := by rw [hr]
    _ = (r ^ 2) ^ E2 := by rw [← pow_two]
    _ = r ^ (2 * E2) := by rw [← pow_mul]
    _ = r ^ (Fintype.card Fp2 - 1) := by rw [two_mul_E2, card_fp2]
    _ = 1 := hpow

/-! ## §7 `Fp12FieldGoal`: `v` is a non-square in `Fp6` (via the `N6`-norm to `Fp2`). -/

/-- **`Fp12FieldGoal` DISCHARGED.**  `v` has no square root in `Fp6`: a root `x² = v` maps under the
multiplicative norm `N6` to `ξ = N6 v = N6(x)²`, making `ξ` a square in `Fp2` — impossible by
`xi_not_isSquare`.  (Routes the `Fp6`-level obligation to a cheap `Fp2` modexp.) -/
theorem fp12FieldGoal_holds : Fp12.Fp12FieldGoal := by
  intro x hx2
  apply xi_not_isSquare
  refine ⟨Fp6.norm6 x, ?_⟩
  calc xiFp2 = Fp6.norm6 Fp6.v := (Fp6.norm6_v).symm
    _ = Fp6.norm6 (x ^ 2) := by rw [hx2]
    _ = Fp6.norm6 (x * x) := by rw [pow_two]
    _ = Fp6.norm6 x * Fp6.norm6 x := Fp6.norm6_mul x x

/-! ## §8 `Field Fp12` via the quadratic norm `N12 : Fp12 → Fp6` (mirrors `Fp2`). -/

namespace Fp12

/-- Conjugation `a₀ + a₁w ↦ a₀ − a₁w` (the nontrivial `Fp6`-automorphism of `Fp12`). -/
def conj (a : Fp12) : Fp12 := ⟨a.c0, -a.c1⟩

@[simp] theorem conj_c0 (a : Fp12) : (conj a).c0 = a.c0 := rfl
@[simp] theorem conj_c1 (a : Fp12) : (conj a).c1 = -a.c1 := rfl

/-- The quadratic field norm `N12 a = a₀² − v·a₁² ∈ Fp6` (`a · conj a = ofFp6 (N12 a)`). -/
noncomputable def norm12 (a : Fp12) : Fp6 := a.c0 ^ 2 - Fp6.v * a.c1 ^ 2

/-- The base-`Fp6` embedding is multiplicative. -/
theorem ofFp6_mul (x y : Fp6) : ofFp6 x * ofFp6 y = ofFp6 (x * y) := by
  ext <;> simp [ofFp6]

/-- `a · conj a = ofFp6 (N12 a)`. -/
theorem mul_conj (a : Fp12) : a * conj a = ofFp6 (norm12 a) := by
  ext <;> simp only [mul_c0, mul_c1, conj_c0, conj_c1, ofFp6_c0, ofFp6_c1, norm12] <;> ring

/-- **The `Fp12` field obstruction is nonvanishing**: `a ≠ 0 → N12 a ≠ 0`.  If `N12 a = 0` and
`a₁ ≠ 0` then `v = (a₀·a₁⁻¹)²` is a square in `Fp6` — impossible by `fp12FieldGoal_holds`; if
`a₁ = 0` then `a₀ = 0` too, so `a = 0`. -/
theorem norm12_ne_zero (a : Fp12) (ha : a ≠ 0) : norm12 a ≠ 0 := by
  intro hnorm
  apply ha
  have h0 : a.c0 ^ 2 - Fp6.v * a.c1 ^ 2 = 0 := hnorm
  have hc1 : a.c1 = 0 := by
    by_contra hne
    apply fp12FieldGoal_holds (a.c0 * (a.c1)⁻¹)
    have hi : a.c1 * (a.c1)⁻¹ = 1 := mul_inv_cancel₀ hne
    have hsq : a.c0 ^ 2 = Fp6.v * a.c1 ^ 2 := by linear_combination h0
    calc (a.c0 * (a.c1)⁻¹) ^ 2
        = a.c0 ^ 2 * ((a.c1)⁻¹) ^ 2 := by ring
      _ = (Fp6.v * a.c1 ^ 2) * ((a.c1)⁻¹) ^ 2 := by rw [hsq]
      _ = Fp6.v * (a.c1 * (a.c1)⁻¹) ^ 2 := by ring
      _ = Fp6.v * (1 : Fp6) ^ 2 := by rw [hi]
      _ = Fp6.v := by ring
  have hc0 : a.c0 = 0 := by
    have h : a.c0 * a.c0 = 0 := by rw [hc1] at h0; rw [← pow_two]; linear_combination h0
    exact mul_self_eq_zero.mp h
  ext <;> simp [hc0, hc1]

/-- **`Fp12` is a genuine field** — the pairing's target group now supports inversion.
`a⁻¹ = conj a · ofFp6 (N12 a)⁻¹`; packaged as `IsField Fp12`.  Mirrors the `Fp2` construction. -/
theorem fp12_isField : IsField Fp12 where
  exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (α := Fp6) (by simpa using congrArg Fp12.c0 h)⟩
  mul_comm := mul_comm
  mul_inv_cancel := by
    intro a ha
    have hn : norm12 a ≠ 0 := norm12_ne_zero a ha
    refine ⟨conj a * ofFp6 ((norm12 a)⁻¹), ?_⟩
    rw [← mul_assoc, mul_conj, ofFp6_mul, mul_inv_cancel₀ hn]; rfl

/-- The `Field Fp12` instance — the top tower level (the pairing target) is now an actual field. -/
noncomputable instance : Field Fp12 := fp12_isField.toField

end Fp12

/-! ## §9 Axiom-cleanliness guards on all four discharged obligations. -/

#assert_axioms fp6FieldGoal_holds
#assert_axioms fp12FieldGoal_holds
#assert_axioms Fp6.fp6_isField
#assert_axioms Fp12.fp12_isField

end Dregg2.Crypto.BN254
