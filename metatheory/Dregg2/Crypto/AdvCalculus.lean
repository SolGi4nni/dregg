/-
# `Dregg2.Crypto.AdvCalculus` — the `advOf` advantage-in-bits calculus (LEAF).

`advOf b = 2^(−b)` — an advantage of `b` BITS of security — together with ALL its laws. This is the single
object the whole parameter-level composition is arithmetic in: the union/product law (`advOf_mul`), the
square-root loss (`advOf_sqrt`, only in the CONTRAST terms now), antitonicity (`advOf_antitone`), the
two- and three-term union folds (`advOf_add_le`, `advOf_add3_le`), the power blow-ups (`natpow_mul_advOf`,
`two_mul_advOf`), and the bridge to negligibility (`negl_advOf`).

It is a **leaf** on purpose: it imports only Mathlib + `Dregg2.Crypto.ConcreteSecurity` (+ `Dregg2.Tactics`),
so the TIGHT reduction files (`LossyIdentification`, `DoubleSidedO2H`) and the system-bound file
(`ParameterSecurity`) can all depend on this calculus WITHOUT a cyclic import — the tight files no longer
have to import `ParameterSecurity` just to get `advOf`. The declarations keep the namespace
`Dregg2.Crypto.ParameterSecurity` so every existing call site (`advOf`, `advOf_add3_le`, …) resolves
unchanged.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Dregg2.Tactics
import Dregg2.Crypto.ConcreteSecurity

open Dregg2.Crypto.ConcreteSecurity

namespace Dregg2.Crypto.ParameterSecurity

/-! ## `advOf` — the advantage-in-bits calculus. -/

/-- **`advOf b = 2^(−b)`** — an advantage of `b` BITS of security. The single object the whole
parameter-level composition is arithmetic in. -/
noncomputable def advOf (b : ℝ) : ℝ := (2 : ℝ) ^ (-b)

theorem advOf_pos (b : ℝ) : 0 < advOf b := Real.rpow_pos_of_pos (by norm_num) _

/-- `advOf a · advOf b = advOf (a+b)` — the UNION / product law: multiplying advantages ADDS bit-losses. -/
theorem advOf_mul (a b : ℝ) : advOf a * advOf b = advOf (a + b) := by
  unfold advOf
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1; ring

/-- `advOf (-(n)) = 2^n` — a NEGATIVE bit-count is a power blow-up (the `2^sessions` / `2^consensus` /
`2^log2q` factors). -/
theorem advOf_negNat (n : ℕ) : advOf (-(n:ℝ)) = (2:ℝ) ^ n := by
  unfold advOf; rw [neg_neg, Real.rpow_natCast]

/-- `advOf (-1) = 2`. -/
theorem advOf_negOne : advOf (-1) = 2 := by
  unfold advOf; rw [neg_neg, Real.rpow_one]

/-- `2^k · advOf x = advOf (x − k)` — a `k`-bit blow-up EATS `k` bits of an advantage. -/
theorem natpow_mul_advOf (k : ℕ) (x : ℝ) : (2:ℝ) ^ k * advOf x = advOf (x - (k:ℝ)) := by
  rw [← advOf_negNat, advOf_mul]; congr 1; ring

/-- `√(advOf b) = advOf (b/2)` — THE SQUARE-ROOT LOSS: the forking-lemma / O2H reduction HALVES the bits. -/
theorem advOf_sqrt (b : ℝ) : Real.sqrt (advOf b) = advOf (b / 2) := by
  rw [Real.sqrt_eq_rpow]
  unfold advOf
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1; ring

/-- `advOf` is ANTITONE: more bits ⟹ smaller advantage. -/
theorem advOf_antitone {a b : ℝ} (h : a ≤ b) : advOf b ≤ advOf a := by
  unfold advOf
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by linarith)

/-- `2 · advOf b = advOf (b − 1)`. -/
theorem two_mul_advOf (b : ℝ) : 2 * advOf b = advOf (b - 1) := by
  rw [← advOf_negOne, advOf_mul]; congr 1; ring

/-- **TWO-TERM UNION.** `advOf a + advOf b ≤ advOf (min a b − 1)` — summing two advantages costs one bit. -/
theorem advOf_add_le (a b : ℝ) : advOf a + advOf b ≤ advOf (min a b - 1) := by
  have h1 : advOf a ≤ advOf (min a b) := advOf_antitone (min_le_left a b)
  have h2 : advOf b ≤ advOf (min a b) := advOf_antitone (min_le_right a b)
  calc advOf a + advOf b ≤ 2 * advOf (min a b) := by linarith
    _ = advOf (min a b - 1) := two_mul_advOf _

/-- **THREE-TERM UNION.** `advOf a + advOf b + advOf c ≤ advOf (min a (min b c) − 2)` — summing three
advantages costs two bits (`3 ≤ 4 = 2²`). The FO chain's O2H + CPA + correctness fold. -/
theorem advOf_add3_le (a b c : ℝ) :
    advOf a + advOf b + advOf c ≤ advOf (min a (min b c) - 2) := by
  set m := min a (min b c) with hm
  have ha : advOf a ≤ advOf m := advOf_antitone (min_le_left _ _)
  have hb : advOf b ≤ advOf m := advOf_antitone (le_trans (min_le_right a (min b c)) (min_le_left b c))
  have hc : advOf c ≤ advOf m := advOf_antitone (le_trans (min_le_right a (min b c)) (min_le_right b c))
  have hpos := advOf_pos m
  have e4 : (4:ℝ) * advOf m = advOf (m - 2) := by
    have : (4:ℝ) * advOf m = 2 * (2 * advOf m) := by ring
    rw [this, two_mul_advOf, two_mul_advOf]; congr 1; ring
  calc advOf a + advOf b + advOf c ≤ 4 * advOf m := by linarith
    _ = advOf (m - 2) := e4

/-- `advOf (n : ℝ) = 1/2^n` — the bridge to `ConcreteSecurity.Negl`. -/
theorem advOf_natCast (n : ℕ) : advOf (n : ℝ) = 1 / (2:ℝ) ^ n := by
  unfold advOf
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]

/-- **(TOOTH — ties `advOf` into the concrete-security substrate.)** The ensemble `λ ↦ advOf λ = 2^(−λ)` is
NEGLIGIBLE — the parameter-level advantage, taken as a family in the security parameter, lands in the
`ConcreteSecurity.Negl` algebra. -/
theorem negl_advOf : Negl (fun n : ℕ => advOf (n : ℝ)) := by
  have h : (fun n : ℕ => advOf (n:ℝ)) = (fun n : ℕ => 1 / (2:ℝ) ^ n) := by
    funext n; exact advOf_natCast n
  rw [h]; exact negl_two_pow

end Dregg2.Crypto.ParameterSecurity
