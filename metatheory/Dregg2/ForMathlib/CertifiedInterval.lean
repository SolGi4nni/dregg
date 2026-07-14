/-
# `Dregg2.ForMathlib.CertifiedInterval` — signed rational interval arithmetic with outward rounding.

Mathlib (as of the pinned rev) has `NonemptyInterval`/`Interval` with an ordered-monoid `Mul`
(`⟨s.fst*t.fst, s.snd*t.snd⟩`, gated on `MulLeftMono`/`MulRightMono`). That instance is SOUND only in a
positive cone — it does **not** apply to a linearly ordered field like `ℚ`, where multiplying by a negative
reverses order. There is no *signed* certified interval-arithmetic (four-corner multiplication, outward-rounded
endpoints, containment monotonicity) in Mathlib. This file supplies that reusable, upstreamable core.

An `Interval` is a pair of rational endpoints `⟨lo, hi⟩`; `I.Contains x := lo ≤ x ≤ hi`. Every operation is
proven to be an *enclosure*: whenever the inputs contain exact values, the output contains the exact result of
the corresponding real operation. That is the only property a rigorous numeric certificate needs.

## What is proved (all containment theorems are genuine — the interval really brackets the exact value)

* `pt_contains`, `add_contains`, `neg_contains`, `sub_contains`, `scale_contains` — the linear operations.
* `mul_contains` — the four-corner **signed** interval product `⟨min₄, max₄⟩`, valid for any signs (the piece
  Mathlib's cone-only `Mul` cannot do). Proved via two elementary monotonicity steps, no `nlinarith` blind spot.
* `pow_contains` — the `n`-th power by repeated `mul`, `x ∈ I → xⁿ ∈ Iⁿ`.
* `contains_of_subset` + `round_contains` — **outward dyadic rounding** widens an interval, so replacing exact
  (unboundedly large) endpoints by their outward `k`-bit dyadic rounding preserves every enclosure. This is what
  makes a long interval computation run at *bounded precision*: after each op, `round` back to `k` fractional
  bits and the containment survives. The reusable answer to "known-true but the exact rationals are too big".

Every theorem is kernel-clean (`#assert_axioms ⊆ {propext, Classical.choice, Quot.sound}`); no `sorry`, no
`native_decide`.
-/
import Mathlib

namespace Dregg2.ForMathlib.CertifiedInterval

/-- A closed rational interval `[lo, hi]` (allowed to be empty as a set when `hi < lo`, but every operation
here preserves `lo ≤ hi` when its inputs satisfy it — see `Wf`). -/
structure Interval where
  lo : ℚ
  hi : ℚ
deriving DecidableEq, Repr

namespace Interval

/-- `I.Contains x` : the exact rational `x` lies in the interval. This is the enclosure predicate every
containment theorem below preserves. -/
def Contains (I : Interval) (x : ℚ) : Prop := I.lo ≤ x ∧ x ≤ I.hi

instance (I : Interval) (x : ℚ) : Decidable (I.Contains x) := by
  unfold Contains; infer_instance

/-- Well-formed (nonempty) interval. Preserved by every operation, but not needed for the containment theorems
themselves (containment is about the exact value, not about nonemptiness). -/
def Wf (I : Interval) : Prop := I.lo ≤ I.hi

/-- Real-valued containment: a rational interval also encloses a real number that equals a rational in it.
Bridges the exact ℚ certificate to ℝ comparisons (the δ target compares to `2^(-174) : ℝ`). -/
theorem contains_real (I : Interval) {x : ℚ} (h : I.Contains x) :
    (I.lo : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ (I.hi : ℝ) :=
  ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-! ### Subset / widening — the backbone of outward rounding -/

/-- `I ⊆ J` : `J` encloses everything `I` does. -/
def Subset (I J : Interval) : Prop := J.lo ≤ I.lo ∧ I.hi ≤ J.hi

/-- Widening preserves enclosure — the load-bearing monotonicity for outward rounding. -/
theorem contains_of_subset {I J : Interval} {x : ℚ} (hsub : I.Subset J) (hx : I.Contains x) :
    J.Contains x :=
  ⟨le_trans hsub.1 hx.1, le_trans hx.2 hsub.2⟩

/-! ### Point interval -/

/-- The degenerate interval `[q, q]`. -/
def pt (q : ℚ) : Interval := ⟨q, q⟩

@[simp] theorem pt_lo (q : ℚ) : (pt q).lo = q := rfl
@[simp] theorem pt_hi (q : ℚ) : (pt q).hi = q := rfl

theorem pt_contains (q : ℚ) : (pt q).Contains q := ⟨le_refl _, le_refl _⟩

/-! ### Addition -/

/-- Interval sum `[a,b] + [c,d] = [a+c, b+d]`. -/
def add (I J : Interval) : Interval := ⟨I.lo + J.lo, I.hi + J.hi⟩

theorem add_contains {I J : Interval} {x y : ℚ} (hx : I.Contains x) (hy : J.Contains y) :
    (add I J).Contains (x + y) :=
  ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

/-! ### Negation and subtraction -/

/-- Interval negation `-[a,b] = [-b, -a]`. -/
def neg (I : Interval) : Interval := ⟨-I.hi, -I.lo⟩

theorem neg_contains {I : Interval} {x : ℚ} (hx : I.Contains x) : (neg I).Contains (-x) :=
  ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

/-- Interval subtraction. -/
def sub (I J : Interval) : Interval := add I (neg J)

theorem sub_contains {I J : Interval} {x y : ℚ} (hx : I.Contains x) (hy : J.Contains y) :
    (sub I J).Contains (x - y) := by
  rw [sub_eq_add_neg]; exact add_contains hx (neg_contains hy)

/-! ### Scaling by a rational constant (may be negative) -/

/-- Multiply an interval by an exact rational scalar `c`, flipping endpoints when `c < 0`. -/
def scale (c : ℚ) (I : Interval) : Interval :=
  if 0 ≤ c then ⟨c * I.lo, c * I.hi⟩ else ⟨c * I.hi, c * I.lo⟩

theorem scale_contains (c : ℚ) {I : Interval} {x : ℚ} (hx : I.Contains x) :
    (scale c I).Contains (c * x) := by
  unfold scale
  by_cases hc : 0 ≤ c
  · simp only [hc, if_true]
    exact ⟨mul_le_mul_of_nonneg_left hx.1 hc, mul_le_mul_of_nonneg_left hx.2 hc⟩
  · simp only [hc, if_false]
    have hcle : c ≤ 0 := le_of_lt (not_le.mp hc)
    exact ⟨mul_le_mul_of_nonpos_left hx.2 hcle, mul_le_mul_of_nonpos_left hx.1 hcle⟩

/-! ### Signed multiplication — the four-corner product Mathlib's cone-only `Mul` cannot express -/

/-- Signed interval product `[a,b]·[c,d] = [min₄, max₄]` over the four corner products. Valid for ALL signs. -/
def mul (I J : Interval) : Interval :=
  let p1 := I.lo * J.lo
  let p2 := I.lo * J.hi
  let p3 := I.hi * J.lo
  let p4 := I.hi * J.hi
  ⟨min (min p1 p2) (min p3 p4), max (max p1 p2) (max p3 p4)⟩

/-- Step 1 (upper): for `a ≤ x ≤ b`, `x·y ≤ max (a·y) (b·y)` (whichever endpoint the sign of `y` picks). -/
private theorem mul_le_max_endpoint {a b x y : ℚ} (h1 : a ≤ x) (h2 : x ≤ b) :
    x * y ≤ max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact le_trans (mul_le_mul_of_nonneg_right h2 hy) (le_max_right _ _)
  · exact le_trans (mul_le_mul_of_nonpos_right h1 hy) (le_max_left _ _)

/-- Step 1 (lower): for `a ≤ x ≤ b`, `min (a·y) (b·y) ≤ x·y`. -/
private theorem min_endpoint_le_mul {a b x y : ℚ} (h1 : a ≤ x) (h2 : x ≤ b) :
    min (a * y) (b * y) ≤ x * y := by
  rcases le_total 0 y with hy | hy
  · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right h1 hy)
  · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_right h2 hy)

/-- Step 2 (upper): for `c ≤ y ≤ d`, `a·y ≤ max (a·c) (a·d)`. -/
private theorem mul_const_le_max {a c d y : ℚ} (h1 : c ≤ y) (h2 : y ≤ d) :
    a * y ≤ max (a * c) (a * d) := by
  rcases le_total 0 a with ha | ha
  · exact le_trans (mul_le_mul_of_nonneg_left h2 ha) (le_max_right _ _)
  · exact le_trans (mul_le_mul_of_nonpos_left h1 ha) (le_max_left _ _)

/-- Step 2 (lower): for `c ≤ y ≤ d`, `min (a·c) (a·d) ≤ a·y`. -/
private theorem min_le_mul_const {a c d y : ℚ} (h1 : c ≤ y) (h2 : y ≤ d) :
    min (a * c) (a * d) ≤ a * y := by
  rcases le_total 0 a with ha | ha
  · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left h1 ha)
  · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left h2 ha)

theorem mul_contains {I J : Interval} {x y : ℚ} (hx : I.Contains x) (hy : J.Contains y) :
    (mul I J).Contains (x * y) := by
  obtain ⟨ha, hb⟩ := hx
  obtain ⟨hc, hd⟩ := hy
  refine ⟨?_, ?_⟩
  · -- min₄ ≤ x*y
    refine le_trans ?_ (min_endpoint_le_mul ha hb)
    -- min₄ ≤ min (I.lo*y) (I.hi*y)
    apply le_min
    · exact le_trans (min_le_left _ _) (min_le_mul_const hc hd)
    · exact le_trans (min_le_right _ _) (min_le_mul_const hc hd)
  · -- x*y ≤ max₄
    refine le_trans (mul_le_max_endpoint ha hb) ?_
    apply max_le
    · exact le_trans (mul_const_le_max hc hd) (le_max_left _ _)
    · exact le_trans (mul_const_le_max hc hd) (le_max_right _ _)

/-- A point interval multiplied is the point of the product (all four corners coincide). -/
@[simp] theorem mul_pt (a b : ℚ) : mul (pt a) (pt b) = pt (a * b) := by
  simp only [mul, pt, min_self, max_self]

/-- A point interval added is the point of the sum. -/
@[simp] theorem add_pt (a b : ℚ) : add (pt a) (pt b) = pt (a + b) := rfl

/-! ### Powers by repeated multiplication -/

/-- `n`-fold interval power (`Iⁿ` via repeated `mul`). -/
def pow (I : Interval) : ℕ → Interval
  | 0 => pt 1
  | n + 1 => mul I (pow I n)

theorem pow_contains {I : Interval} {x : ℚ} (hx : I.Contains x) :
    ∀ n, (I.pow n).Contains (x ^ n)
  | 0 => by simpa [pow] using pt_contains (1 : ℚ)
  | n + 1 => by
    rw [pow, pow_succ, mul_comm]
    exact mul_contains hx (pow_contains hx n)

/-! ### Outward dyadic rounding — bounded precision -/

/-- Round `q` DOWN to the dyadic grid `ℤ / 2^k` (so `≤ q`). -/
def floorDyadic (k : ℕ) (q : ℚ) : ℚ := (⌊q * 2 ^ k⌋ : ℤ) / (2 ^ k)

/-- Round `q` UP to the dyadic grid `ℤ / 2^k` (so `≥ q`). -/
def ceilDyadic (k : ℕ) (q : ℚ) : ℚ := (⌈q * 2 ^ k⌉ : ℤ) / (2 ^ k)

theorem floorDyadic_le (k : ℕ) (q : ℚ) : floorDyadic k q ≤ q := by
  unfold floorDyadic
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

theorem le_ceilDyadic (k : ℕ) (q : ℚ) : q ≤ ceilDyadic k q := by
  unfold ceilDyadic
  rw [le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

/-- Outward rounding of an interval to `k` fractional bits: `lo` down, `hi` up. Always a superset. -/
def round (k : ℕ) (I : Interval) : Interval := ⟨floorDyadic k I.lo, ceilDyadic k I.hi⟩

theorem round_subset (k : ℕ) (I : Interval) : I.Subset (round k I) :=
  ⟨floorDyadic_le k I.lo, le_ceilDyadic k I.hi⟩

/-- **Bounded-precision enclosure survives.** Replacing an interval by its outward `k`-bit dyadic rounding never
loses a contained value — so a long computation can `round` after every op and remain a rigorous certificate. -/
theorem round_contains (k : ℕ) {I : Interval} {x : ℚ} (hx : I.Contains x) : (round k I).Contains x :=
  contains_of_subset (round_subset k I) hx

end Interval
end Dregg2.ForMathlib.CertifiedInterval
