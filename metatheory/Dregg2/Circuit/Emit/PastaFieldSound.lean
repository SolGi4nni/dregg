/-
# Dregg2.Circuit.Emit.PastaFieldSound — a Pasta multiply that is sound IN THE FIELD THE PROVER
CHECKS, not only over ℤ.

## The defect this file repairs, measured

`Dregg2.Circuit.Emit.PastaField` encodes a Pasta field element as `9 × 30` bits and emits ONE
degree-2 gate per multiply, `xVal·yVal − p·qVal − zVal = 0`. Its forcing lemma
(`fpMulCore_forces`) is true and it is **about ℤ**. The deployed prover reads gate bodies in
BabyBear (`P = 2013265921`), and there the gate forces nothing: the nine quotient limbs enter with
weights `p·2^(30 i)`, all units mod `P`, and nothing pins those columns.

`circuit/tests/pasta_field_felt_soundness.rs::the_deployed_prover_accepts_a_nonzero_integer_body`
is that gap as a WITNESS, not a description: two cells of the Lean-emitted honest 64-row fixture
move (quotient limbs 0 and 1 of constraint 4, by `939524097` and `1`), the gate body goes from `0`
to a **nonzero 285-bit integer**, and `prove_vm_descriptor2` + `verify_vm_descriptor2` both accept.
That is the pre-image everything below has to refuse.

⚑ **AND WIRING `pastaLimbRange` IN WOULD NOT HAVE FIXED IT.** Ranges bound the search; the `9×30`
body still reaches `2^508`, so `body ≡ 0 (mod P)` still admits every witness whose ℤ body is a
nonzero multiple of `P`. Ranges are the PREREQUISITE for the fix, not the fix. The fix is an
encoding whose every gate body FITS a felt, so that the two readings coincide.

## The encoding, and why these three numbers

`SB = 8` bits per limb, `SK = 32` limbs (capacity 256 ≥ 255), carries range-checked at `CB = 16`
bits with offset `COFF = 2^15`. A multiply emits `2·SK − 1 = 63` coefficient gates

    Σ_{i+j=m} x_i·y_j  −  Σ_{i+j=m} q_i·p_j  −  z_m  +  c_{m−1}  −  2^8·c_m  =  0

plus one range lookup per limb and per carry. Every one of those bodies is bounded (crudely, by
the whole 1024-pair product list rather than the ≤32-long antidiagonal) by

    2·1024·255² + 255 + 2^15 + 2^8·2^15  =  141 592 831  <  P = 2 013 265 921

(`coefBody_abs_lt_P`, 7% of the field even at the crude bound), so `P ∣ body` FORCES `body = 0`
over ℤ — and the telescope of the 63 integer identities is exactly `X·Y − p·Q − Z = 0`. That is
`felt_gates_force_congruence`, the theorem this file exists for: its hypothesis is the mod-`P`
reading the prover actually checks, and its conclusion is the Pasta congruence.

### Why `8` and `16` and not `12` and `19`

The choice is MEASURED against the deployed range realization, not taste. `descriptor_ir2.rs`
(`MainLayout::build`, `eval_decomp`) compiles a range lookup to a nibble decomposition: at
`bits % 4 = 0` it is `bits/4` columns and **one** `assert_zero`; at `bits % 4 ≠ 0` it is
`⌈bits/4⌉ + (bits mod 4)` columns and `(bits mod 4) + 2` constraints. So a 19-bit carry costs
**five** constraints and a 16-bit carry costs **one**. Against `SB = 12, SK = 22, CB = 19`
(43 gates, 44 + 42 lookups) that is `43 + 44 + 210 = 297` constraints; this shape is
`63 + 64 + 62 = 189`. Fewer limbs is NOT cheaper here, because the decomposition columns of a
ranged 255-bit quantity are `SK · (SB/4) ≈ 64` whatever `SB` is.

### The alternative that is NOT available, and that is a finding

The cheap escape from `O(limbs²)` is a randomized-challenge identity — check
`a·b − q·p − r = 0` at a verifier-drawn point (Schwartz–Zippel), `O(limbs)` constraints. **It is
not expressible in this IR.** The constraint expression grammars are closed:
`lean_descriptor_air.rs::LeanExpr` is `Var | Const | Add | Mul` and `DescriptorIR2.WindowExpr` is
`Loc | Nxt | Const | Add | Mul`. There is no challenge leaf, and public inputs are reachable only
through `VmConstraint.piBinding` — a pin of a COLUMN to a PI, not an expression leaf. The LogUp
randomness exists but is walled inside the gadget (`Ir2RowLocalBuilder.permutation_randomness`
returns `&[]`). Adding a challenge leaf is a change to the IR and the prover, not to a descriptor.
So: **schoolbook with bounded limbs is not merely the cheaper option here, it is the only sound
one this vocabulary can say.** The CRT-over-small-moduli variant IS expressible and is strictly
worse — every extra modulus needs its own witnessed reduction, and `Π mⱼ` has to exceed the same
`2^508`.

## Range widths (House rule: 29 is the ceiling, and it is proved)

Both declared widths are `≤ 29`, so both are wrap-free
(`RangeFieldContainment.wrap_free_iff_le_29`); `sb_wrapfree` / `cb_wrapfree` instantiate it here
rather than leaving it to a reader's arithmetic. `EffectAirIR.LimbsLeg.mainRailOk` REFUSES anything
`≥ 30`, so the compiler is the enforcement and these two theorems are the reason it passes.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. Facts are NAMED THEOREMS, not `#guard`s.
-/
import Dregg2.Circuit.Emit.PastaField
import Dregg2.Circuit.Emit.EffectLowerCore
import Dregg2.Circuit.RangeFieldContainment

namespace Dregg2.Circuit.Emit.PastaFieldSound

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectLower (P)
open Dregg2.Circuit.Emit.PastaField (pN qN)

set_option autoImplicit false
-- the emitted descriptor's spine (63 gate legs, 190 columns) and the 32-limb recompositions are
-- kernel-reduced, which the default 512 does not reach.
set_option maxRecDepth 40000

/-! ## §0 — The parameters, and the two range widths. -/

/-- Bits per SOUND limb. A byte: `8 % 4 = 0`, so the deployed nibble realization costs one
constraint and two columns per lookup. -/
def SB : Nat := 8
/-- Limbs per Pasta field element at `SB`: `8 · 32 = 256 ≥ 255`. -/
def SK : Nat := 32
/-- The carry range width. `16 % 4 = 0` — one constraint, four columns. -/
def CB : Nat := 16
/-- The carry offset: a carry column holds `c + COFF ∈ [0, 2^16)`, so `c ∈ [−2^15, 2^15)`. -/
def COFF : ℤ := 2 ^ 15
/-- Coefficient gates per multiply: `2·SK − 1 = 63`. -/
def NG : Nat := 2 * SK - 1

theorem NG_eq : NG = 63 := rfl

/-- The encoding reaches 256 bits, and both Pasta primes are 255-bit — so a canonical field
element has an `SK`-limb representation and the quotient does too. -/
theorem capacity_covers_pasta : pN < 2 ^ (SB * SK) ∧ qN < 2 ^ (SB * SK) := by
  constructor <;> norm_num [pN, qN, SB, SK]

/-- **Both declared widths are wrap-free**, so a slack the prover wants to be negative does not
ride in as `P − k`. This is the `≤ 29` ceiling instantiated, not assumed. -/
theorem sb_wrapfree : Dregg2.Circuit.RangeFieldContainment.Wrapfree SB :=
  (Dregg2.Circuit.RangeFieldContainment.wrap_free_iff_le_29 SB).mpr (by decide)

theorem cb_wrapfree : Dregg2.Circuit.RangeFieldContainment.Wrapfree CB :=
  (Dregg2.Circuit.RangeFieldContainment.wrap_free_iff_le_29 CB).mpr (by decide)

/-! ## §1 — List-sum plumbing (the emitted heads fold over lists; the arithmetic needs sums). -/

/-- The sum of `f` over a list. -/
def sumL {α : Type} (l : List α) (f : α → ℤ) : ℤ := (l.map f).sum

@[simp] theorem sumL_nil {α : Type} (f : α → ℤ) : sumL ([] : List α) f = 0 := rfl

@[simp] theorem sumL_cons {α : Type} (x : α) (l : List α) (f : α → ℤ) :
    sumL (x :: l) f = f x + sumL l f := by simp [sumL]

theorem sumL_append {α : Type} (l1 l2 : List α) (f : α → ℤ) :
    sumL (l1 ++ l2) f = sumL l1 f + sumL l2 f := by
  simp [sumL, List.map_append, List.sum_append]

theorem sumL_zero {α : Type} (l : List α) : sumL l (fun _ => (0 : ℤ)) = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [sumL_cons, ih]

theorem sumL_congr {α : Type} (l : List α) (f g : α → ℤ) (h : ∀ x ∈ l, f x = g x) :
    sumL l f = sumL l g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [sumL_cons, h x (by simp)]
    rw [ih (fun y hy => h y (by simp [hy]))]

/-- Pulling a filter into an `if`. This is the bridge between the EMITTED head (which folds over
the filtered antidiagonal, so no zero terms are written) and the arithmetic (which sums over the
whole product list). -/
theorem sumL_filter {α : Type} (l : List α) (Pr : α → Bool) (f : α → ℤ) :
    sumL (l.filter Pr) f = sumL l (fun x => if Pr x then f x else 0) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : Pr x = true
    · simp [h, ih]
    · simp only [Bool.not_eq_true] at h
      simp [h, ih]

theorem sumL_add {α : Type} (l : List α) (f g : α → ℤ) :
    sumL l (fun x => f x + g x) = sumL l f + sumL l g := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [sumL_cons, ih]; ring

theorem sumL_sub {α : Type} (l : List α) (f g : α → ℤ) :
    sumL l (fun x => f x - g x) = sumL l f - sumL l g := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [sumL_cons, ih]; ring

theorem sumL_smul {α : Type} (l : List α) (k : ℤ) (f : α → ℤ) :
    sumL l (fun x => k * f x) = k * sumL l f := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [sumL_cons, ih]; ring

/-- Swap two list sums. -/
theorem sumL_comm {α β : Type} (l1 : List α) (l2 : List β) (F : α → β → ℤ) :
    sumL l1 (fun x => sumL l2 (F x)) = sumL l2 (fun y => sumL l1 (fun x => F x y)) := by
  induction l1 with
  | nil => simp [sumL_zero]
  | cons x xs ih =>
    simp only [sumL_cons, ih]
    rw [← sumL_add]

/-- A sum over a product list is the nested sum. -/
theorem sumL_product_nested {α β : Type} (l1 : List α) (l2 : List β) (F : α × β → ℤ) :
    sumL (l1 ×ˢ l2) F = sumL l1 (fun x => sumL l2 (fun y => F (x, y))) := by
  induction l1 with
  | nil => simp [sumL]
  | cons x xs ih =>
    rw [List.product_cons, sumL_append, ih, sumL_cons]
    congr 1
    simp [sumL, List.map_map, Function.comp_def]

/-- The product list's sum FACTORS when the summand is `f(left) · g(right)`. -/
theorem sumL_product {α β : Type} (l1 : List α) (l2 : List β) (f : α → ℤ) (g : β → ℤ) :
    sumL (l1 ×ˢ l2) (fun pr => f pr.1 * g pr.2) = sumL l1 f * sumL l2 g := by
  rw [sumL_product_nested]
  have h1 : ∀ x ∈ l1, sumL l2 (fun y => f x * g y) = f x * sumL l2 g :=
    fun x _ => sumL_smul l2 (f x) g
  rw [sumL_congr _ _ _ h1]
  have h2 : ∀ x ∈ l1, f x * sumL l2 g = sumL l2 g * f x := fun x _ => mul_comm _ _
  rw [sumL_congr _ _ _ h2, sumL_smul]
  ring

/-- A sum over `List.range n` of an indicator collapses to the single matching index. -/
theorem sumL_range_ite (n j : Nat) (g : Nat → ℤ) (hj : j < n) :
    sumL (List.range n) (fun m => if j = m then g m else 0) = g j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, sumL_append, sumL_cons, sumL_nil]
    rcases Nat.lt_or_ge j n with h | h
    · rw [show ((if j = n then g n else 0) : ℤ) = 0 from if_neg (by omega)]
      rw [ih h]; ring
    · have hjn : j = n := by omega
      subst hjn
      have hz : sumL (List.range j) (fun m => if j = m then g m else 0) = 0 := by
        rw [sumL_congr _ _ (fun _ => (0 : ℤ))
          (fun m hm => if_neg (by have := List.mem_range.mp hm; omega))]
        exact sumL_zero _
      rw [hz]; simp

/-- `|u + v| ≤ |u| + |v|`, stated locally so no Mathlib rename can silently move it. -/
theorem abs_add_le' (u v : ℤ) : |u + v| ≤ |u| + |v| := by
  rcases abs_cases u with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases abs_cases v with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rcases abs_cases (u + v) with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> linarith

/-- `|u − v| ≤ |u| + |v|`. -/
theorem abs_sub_le' (u v : ℤ) : |u - v| ≤ |u| + |v| := by
  rcases abs_cases u with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases abs_cases v with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rcases abs_cases (u - v) with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> linarith

/-- The absolute value of a list sum is bounded by `length · max`. -/
theorem sumL_abs_le {α : Type} (l : List α) (f : α → ℤ) (M : ℤ) (hM : ∀ x ∈ l, |f x| ≤ M)
    (hM0 : 0 ≤ M) : |sumL l f| ≤ (l.length : ℤ) * M := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx : |f x| ≤ M := hM x (by simp)
    have hrest := ih (fun y hy => hM y (by simp [hy]))
    have hsplit : |sumL (x :: xs) f| ≤ |f x| + |sumL xs f| := by
      simpa [sumL_cons] using abs_add_le' (f x) (sumL xs f)
    have hlen : ((x :: xs).length : ℤ) * M = M + (xs.length : ℤ) * M := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
    rw [hlen]
    linarith

/-! ## §2 — The limb encoding and the value it denotes. -/

/-- The `i`-th `SB`-bit limb of a natural as an integer. -/
def limbAt (v i : Nat) : ℤ := (((v / 2 ^ (SB * i)) % 2 ^ SB : Nat) : ℤ)

/-- The value the `SK` columns at `base` reconstruct: `Σ_{i<SK} (2^SB)^i · a(base+i)`. -/
def sVal (a : Assignment) (base : Nat) : ℤ :=
  sumL (List.range SK) (fun i => ((2 : ℤ) ^ SB) ^ i * a (base + i))

/-- The `SB`-bit limbs of the Pasta prime `p` — gate CONSTANTS, all `< 2^8`. -/
def pLimb (j : Nat) : ℤ := limbAt pN j
/-- …and of `q`. -/
def qLimb (j : Nat) : ℤ := limbAt qN j

theorem limbAt_bounds (v i : Nat) : 0 ≤ limbAt v i ∧ limbAt v i < 2 ^ SB := by
  refine ⟨Int.natCast_nonneg _, ?_⟩
  have h : (v / 2 ^ (SB * i)) % 2 ^ SB < 2 ^ SB := Nat.mod_lt _ (by positivity)
  unfold limbAt
  exact_mod_cast h

theorem pLimb_bounds (j : Nat) : 0 ≤ pLimb j ∧ pLimb j < 2 ^ SB := limbAt_bounds pN j
theorem qLimb_bounds (j : Nat) : 0 ≤ qLimb j ∧ qLimb j < 2 ^ SB := limbAt_bounds qN j

/-! ## §3 — The antidiagonal, the digit, and the carry chain. -/

/-- All `(i, j)` limb-index pairs. -/
def allPairs : List (Nat × Nat) := (List.range SK) ×ˢ (List.range SK)

theorem allPairs_length : allPairs.length = 1024 := by
  simp [allPairs, SK, List.length_product]

/-- The `m`-th antidiagonal: the pairs whose indices sum to `m`. This is what a gate folds over,
so the emitted head carries exactly the nonzero cross-products (≤ 32 of the 1024). -/
def convPairs (m : Nat) : List (Nat × Nat) := allPairs.filter (fun pr => pr.1 + pr.2 == m)

theorem convPairs_mem {m : Nat} {pr : Nat × Nat} (h : pr ∈ convPairs m) :
    pr.1 < SK ∧ pr.2 < SK ∧ pr.1 + pr.2 = m := by
  rw [convPairs, List.mem_filter] at h
  obtain ⟨hmem, heq⟩ := h
  rw [allPairs, List.mem_product] at hmem
  exact ⟨List.mem_range.mp hmem.1, List.mem_range.mp hmem.2, by simpa using heq⟩

/-- A crude but sufficient cardinality bound: the antidiagonal is a sublist of the 1024-long
product list. (The true length is ≤ 32; the crude bound already lands at 7% of the field, so the
tighter one buys nothing and costs a `Nodup` argument.) -/
theorem convPairs_length_le (m : Nat) : ((convPairs m).length : ℤ) ≤ 1024 := by
  have h := List.length_filter_le (fun pr : Nat × Nat => pr.1 + pr.2 == m) allPairs
  rw [allPairs_length] at h
  exact_mod_cast h

/-- The `m`-th digit of the integer body `x·y − M·q − z`, read off the trace. -/
def digitVal (a : Assignment) (xB yB zB qB : Nat) (pl : Nat → ℤ) (m : Nat) : ℤ :=
  sumL (convPairs m) (fun pr => a (xB + pr.1) * a (yB + pr.2))
    - sumL (convPairs m) (fun pr => a (qB + pr.1) * pl pr.2)
    - (if m < SK then a (zB + m) else 0)

/-- The carry chain read off the trace: `S 0 = 0`, `S m = a(cB + m − 1) − COFF` for
`1 ≤ m ≤ NG − 1`, and `S NG = 0`. ⚑ The chain is pinned closed at both ends **by construction** —
there is no column for `S 0` or `S NG`, so no witness can open them. That is why this file needs
no boundary gate and no boolean pin on the ends. -/
def chainVal (a : Assignment) (cB m : Nat) : ℤ :=
  if m = 0 then 0 else if m ≤ NG - 1 then a (cB + m - 1) - COFF else 0

theorem chainVal_zero (a : Assignment) (cB : Nat) : chainVal a cB 0 = 0 := rfl

theorem chainVal_top (a : Assignment) (cB : Nat) : chainVal a cB NG = 0 := by
  unfold chainVal NG SK; norm_num

/-- The gate body at index `m`: digit + carry-in − radix · carry-out. -/
def coefBody (a : Assignment) (xB yB zB qB cB : Nat) (pl : Nat → ℤ) (m : Nat) : ℤ :=
  digitVal a xB yB zB qB pl m + chainVal a cB m - (2 : ℤ) ^ SB * chainVal a cB (m + 1)

/-! ## §4 — THE TELESCOPE and THE CONVOLUTION (the two arithmetic facts). -/

/-- **The telescope.** A chain of `S m + T m = b·S (m+1)` links sums to `b^M·S M − S 0`.
This is where the 63 separate integer identities become one. -/
theorem telescope (b : ℤ) (T S : Nat → ℤ) (h : ∀ m, S m + T m = b * S (m + 1)) (M : Nat) :
    sumL (List.range M) (fun m => b ^ m * T m) = b ^ M * S M - S 0 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [List.range_succ, sumL_append, sumL_cons, sumL_nil, ih]
    have hM := h M
    have key : b ^ M * (S M + T M) = b ^ M * (b * S (M + 1)) := by rw [hM]
    have hp : b ^ (M + 1) = b ^ M * b := by ring
    rw [hp]
    linear_combination key

/-- **The convolution.** The base-`b` recomposition of the antidiagonal sums IS the product of the
two recompositions. This is the reason a coefficient-wise check certifies a 508-bit product. -/
theorem conv_recompose (b : ℤ) (f g : Nat → ℤ) :
    sumL (List.range NG) (fun m => b ^ m * sumL (convPairs m) (fun pr => f pr.1 * g pr.2))
      = sumL (List.range SK) (fun i => b ^ i * f i)
        * sumL (List.range SK) (fun j => b ^ j * g j) := by
  have step1 : ∀ m ∈ List.range NG,
      b ^ m * sumL (convPairs m) (fun pr => f pr.1 * g pr.2)
        = sumL allPairs (fun pr => if pr.1 + pr.2 = m then b ^ m * (f pr.1 * g pr.2) else 0) := by
    intro m _
    rw [convPairs, sumL_filter, ← sumL_smul]
    refine sumL_congr _ _ _ (fun pr _ => ?_)
    by_cases h : pr.1 + pr.2 = m <;> simp [h]
  rw [sumL_congr (List.range NG) _ _ step1, sumL_comm]
  have step2 : ∀ pr ∈ allPairs,
      sumL (List.range NG) (fun m => if pr.1 + pr.2 = m then b ^ m * (f pr.1 * g pr.2) else 0)
        = b ^ pr.1 * f pr.1 * (b ^ pr.2 * g pr.2) := by
    intro pr hpr
    rw [allPairs, List.mem_product] at hpr
    have h1 := List.mem_range.mp hpr.1
    have h2 := List.mem_range.mp hpr.2
    have hlt : pr.1 + pr.2 < NG := by unfold NG SK at *; omega
    rw [sumL_range_ite NG (pr.1 + pr.2) _ hlt, pow_add]
    ring
  rw [sumL_congr allPairs _ _ step2]
  exact sumL_product (List.range SK) (List.range SK)
    (fun i => b ^ i * f i) (fun j => b ^ j * g j)

/-- The `z` block occupies only the low `SK` positions, so extending its sum to `NG` positions
does not change it. -/
theorem z_extend (b : ℤ) (h : Nat → ℤ) :
    sumL (List.range NG) (fun m => b ^ m * (if m < SK then h m else 0))
      = sumL (List.range SK) (fun m => b ^ m * h m) := by
  have hsplit : NG = SK + (NG - SK) := by unfold NG SK; norm_num
  rw [hsplit, List.range_add, sumL_append]
  have hlow : ∀ m ∈ List.range SK,
      b ^ m * (if m < SK then h m else 0) = b ^ m * h m :=
    fun m hm => by rw [if_pos (List.mem_range.mp hm)]
  have hhigh : ∀ m ∈ (List.range (NG - SK)).map (SK + ·),
      b ^ m * (if m < SK then h m else 0) = 0 := by
    intro m hm
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
    simp
  rw [sumL_congr _ _ _ hlow, sumL_congr _ _ (fun _ => (0 : ℤ)) hhigh, sumL_zero]
  ring

/-! ## §5 — THE THEOREM: the mod-`P` reading forces the Pasta congruence. -/

/-- The digit is bounded. -/
theorem digitVal_abs_le (a : Assignment) (xB yB zB qB : Nat) (pl : Nat → ℤ) (m : Nat)
    (hx : ∀ i, i < SK → 0 ≤ a (xB + i) ∧ a (xB + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (yB + i) ∧ a (yB + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ a (zB + i) ∧ a (zB + i) < 2 ^ SB)
    (hq : ∀ i, i < SK → 0 ≤ a (qB + i) ∧ a (qB + i) < 2 ^ SB)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB) :
    |digitVal a xB yB zB qB pl m|
      ≤ 2 * 1024 * (((2 : ℤ) ^ SB - 1) * ((2 : ℤ) ^ SB - 1)) + ((2 : ℤ) ^ SB - 1) := by
  have hM : (0 : ℤ) ≤ ((2 : ℤ) ^ SB - 1) * ((2 : ℤ) ^ SB - 1) := by norm_num [SB]
  have hlen := convPairs_length_le m
  have hxy : |sumL (convPairs m) (fun pr => a (xB + pr.1) * a (yB + pr.2))|
      ≤ 1024 * (((2 : ℤ) ^ SB - 1) * ((2 : ℤ) ^ SB - 1)) := by
    refine le_trans (sumL_abs_le _ _ _ (fun pr hpr => ?_) hM) (by nlinarith)
    obtain ⟨h1, h2, _⟩ := convPairs_mem hpr
    obtain ⟨hx0, hx1⟩ := hx pr.1 h1
    obtain ⟨hy0, hy1⟩ := hy pr.2 h2
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have hqp : |sumL (convPairs m) (fun pr => a (qB + pr.1) * pl pr.2)|
      ≤ 1024 * (((2 : ℤ) ^ SB - 1) * ((2 : ℤ) ^ SB - 1)) := by
    refine le_trans (sumL_abs_le _ _ _ (fun pr hpr => ?_) hM) (by nlinarith)
    obtain ⟨h1, _, _⟩ := convPairs_mem hpr
    obtain ⟨hq0, hq1⟩ := hq pr.1 h1
    obtain ⟨hp0, hp1⟩ := hpl pr.2
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have hzz : |(if m < SK then a (zB + m) else 0)| ≤ (2 : ℤ) ^ SB - 1 := by
    by_cases h : m < SK
    · obtain ⟨h0, h1⟩ := hz m h
      rw [if_pos h, abs_of_nonneg h0]; omega
    · rw [if_neg h]; norm_num [SB]
  unfold digitVal
  have s1 := abs_sub_le' (sumL (convPairs m) (fun pr => a (xB + pr.1) * a (yB + pr.2))
      - sumL (convPairs m) (fun pr => a (qB + pr.1) * pl pr.2))
    (if m < SK then a (zB + m) else 0)
  have s2 := abs_sub_le' (sumL (convPairs m) (fun pr => a (xB + pr.1) * a (yB + pr.2)))
    (sumL (convPairs m) (fun pr => a (qB + pr.1) * pl pr.2))
  linarith

/-- The carry is bounded by the declared range width. -/
theorem chainVal_abs_le (a : Assignment) (cB m : Nat)
    (hc : ∀ i, i < NG - 1 → 0 ≤ a (cB + i) ∧ a (cB + i) < 2 ^ CB) :
    |chainVal a cB m| ≤ COFF := by
  unfold chainVal
  by_cases h0 : m = 0
  · rw [if_pos h0]; simp [COFF]
  by_cases h1 : m ≤ NG - 1
  · rw [if_neg h0, if_pos h1]
    obtain ⟨hl, hr⟩ := hc (m - 1) (by omega)
    have hidx : cB + m - 1 = cB + (m - 1) := by omega
    have hCB : (2 : ℤ) ^ CB = 2 * COFF := by norm_num [CB, COFF]
    rw [hidx, abs_le]
    constructor <;> linarith
  · rw [if_neg h0, if_neg h1]; simp [COFF]

/-- ⚑ **EVERY GATE BODY FITS A FELT** — `141 592 831 < 2 013 265 921`. This is the whole repair in
one line: at `9 × 30` the same body reached `2^508`. -/
theorem coefBody_abs_lt_P (a : Assignment) (xB yB zB qB cB : Nat) (pl : Nat → ℤ) (m : Nat)
    (hx : ∀ i, i < SK → 0 ≤ a (xB + i) ∧ a (xB + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (yB + i) ∧ a (yB + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ a (zB + i) ∧ a (zB + i) < 2 ^ SB)
    (hq : ∀ i, i < SK → 0 ≤ a (qB + i) ∧ a (qB + i) < 2 ^ SB)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hc : ∀ i, i < NG - 1 → 0 ≤ a (cB + i) ∧ a (cB + i) < 2 ^ CB) :
    |coefBody a xB yB zB qB cB pl m| < P := by
  have hd := digitVal_abs_le a xB yB zB qB pl m hx hy hz hq hpl
  have hc1 := chainVal_abs_le a cB m hc
  have hc2 := chainVal_abs_le a cB (m + 1) hc
  have hscale : |(2 : ℤ) ^ SB * chainVal a cB (m + 1)| ≤ (2 : ℤ) ^ SB * COFF := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (2 : ℤ) ^ SB)]
    exact mul_le_mul_of_nonneg_left hc2 (by positivity)
  have hnum : 2 * 1024 * (((2 : ℤ) ^ SB - 1) * ((2 : ℤ) ^ SB - 1)) + ((2 : ℤ) ^ SB - 1)
      + COFF + (2 : ℤ) ^ SB * COFF < P := by
    norm_num [SB, COFF, Dregg2.Circuit.Emit.EffectLower.P]
  unfold coefBody
  have h1 := abs_sub_le' (digitVal a xB yB zB qB pl m + chainVal a cB m)
    ((2 : ℤ) ^ SB * chainVal a cB (m + 1))
  have h2 := abs_add_le' (digitVal a xB yB zB qB pl m) (chainVal a cB m)
  linarith

/-- ⚑ **THE THEOREM.** From the reading the DEPLOYED PROVER performs — every coefficient gate body
`≡ 0 (mod P)` — together with the range facts the declared lookups supply, the modular congruence
`x·y ≡ z (mod M)` follows, where `M` is whatever modulus the constant limb vector `pl` recomposes
to.

The `9×30` gate's forcing lemma needed `body = 0` **over ℤ** and had no way to get it; this one is
handed `P ∣ body` and DERIVES `body = 0`, because the body fits. `pl` is a parameter, so the same
statement covers `p` (`pLimb`) and `q` (`qLimb`) — the encoding is field-independent and only the
constant vector moves. -/
theorem felt_gates_force_congruence
    (a : Assignment) (xB yB zB qB cB : Nat) (pl : Nat → ℤ) (M : ℤ)
    (hx : ∀ i, i < SK → 0 ≤ a (xB + i) ∧ a (xB + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (yB + i) ∧ a (yB + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ a (zB + i) ∧ a (zB + i) < 2 ^ SB)
    (hq : ∀ i, i < SK → 0 ≤ a (qB + i) ∧ a (qB + i) < 2 ^ SB)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hplM : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = M)
    (hc : ∀ i, i < NG - 1 → 0 ≤ a (cB + i) ∧ a (cB + i) < 2 ^ CB)
    -- ⚑ the DEPLOYED reading: the prover checks each body in BabyBear, not over ℤ.
    (hgates : ∀ m, m < NG → P ∣ coefBody a xB yB zB qB cB pl m) :
    M ∣ (sVal a xB * sVal a yB - sVal a zB) := by
  -- Step 1: each body FITS a felt, so `P ∣ body` forces `body = 0` over ℤ.
  have hzero : ∀ m, m < NG → coefBody a xB yB zB qB cB pl m = 0 := by
    intro m hm
    have hlt := coefBody_abs_lt_P a xB yB zB qB cB pl m hx hy hz hq hpl hc
    rcases hgates m hm with ⟨t, ht⟩
    by_contra hne
    have ht0 : t ≠ 0 := by rintro rfl; rw [mul_zero] at ht; exact hne ht
    have hP0 : (0 : ℤ) < P := by norm_num [Dregg2.Circuit.Emit.EffectLower.P]
    have h1 : (1 : ℤ) ≤ |t| := by
      rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    have : P ≤ |coefBody a xB yB zB qB cB pl m| := by
      rw [ht, abs_mul, abs_of_nonneg (le_of_lt hP0)]
      nlinarith
    linarith
  -- Step 2: the chain telescopes; both ends are pinned by construction.
  have hchain : ∀ m, chainVal a cB m + digitVal a xB yB zB qB pl m
      = (2 : ℤ) ^ SB * chainVal a cB (m + 1) := by
    intro m
    by_cases hm : m < NG
    · have := hzero m hm; unfold coefBody at this; linarith
    · have hNG : NG = 63 := rfl
      have hSK : SK = 32 := rfl
      have hm' : 63 ≤ m := by omega
      have h1 : chainVal a cB m = 0 := by
        unfold chainVal; rw [if_neg (by omega), if_neg (by omega)]
      have h2 : chainVal a cB (m + 1) = 0 := by
        unfold chainVal; rw [if_neg (by omega), if_neg (by omega)]
      have h3 : digitVal a xB yB zB qB pl m = 0 := by
        unfold digitVal
        have e1 : convPairs m = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro pr hpr
          obtain ⟨u, v, w⟩ := convPairs_mem hpr
          omega
        rw [e1, if_neg (by omega)]
        simp
      rw [h1, h2, h3]; ring
  have htel := telescope ((2 : ℤ) ^ SB) (digitVal a xB yB zB qB pl) (chainVal a cB) hchain NG
  rw [chainVal_top, chainVal_zero, mul_zero, sub_zero] at htel
  -- Step 3: that recomposition IS `x·y − M·q − z`.
  have hd : ∀ m ∈ List.range NG,
      ((2 : ℤ) ^ SB) ^ m * digitVal a xB yB zB qB pl m
        = ((2 : ℤ) ^ SB) ^ m * sumL (convPairs m) (fun pr => a (xB + pr.1) * a (yB + pr.2))
          - ((2 : ℤ) ^ SB) ^ m * sumL (convPairs m) (fun pr => a (qB + pr.1) * pl pr.2)
          - ((2 : ℤ) ^ SB) ^ m * (if m < SK then a (zB + m) else 0) := by
    intro m _; unfold digitVal; ring
  rw [sumL_congr _ _ _ hd, sumL_sub, sumL_sub,
    conv_recompose ((2 : ℤ) ^ SB) (fun i => a (xB + i)) (fun j => a (yB + j)),
    conv_recompose ((2 : ℤ) ^ SB) (fun i => a (qB + i)) pl,
    z_extend ((2 : ℤ) ^ SB) (fun m => a (zB + m)), hplM] at htel
  exact ⟨sVal a qB, by unfold sVal; linarith⟩

/-! ## §6 — THE EMITTED AIR, through the compiler (`EffectLower.lowerAir` of an `EffectAir`).

House Law #1 in its endpoint form: the descriptor below is not a hand-written `VmConstraint2`
list, it is `lowerAir` of a source `EffectAir`. The range legs go through `LimbsLeg`, whose
`mainRailOk` REFUSES a width `≥ 30` — so the ≤29 ceiling is enforced by the compiler and
`sb_wrapfree`/`cb_wrapfree` are the reason this block passes it. -/

open Dregg2.Circuit (Expr Constraint ConstraintSystem)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 TableDef TableId mainTableDef VmConstraint2)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LimbsLeg)
open Dregg2.Circuit.Emit.EffectLower (lowerAir P)

/-- The WIDTH-TAGGED range table id, matching the deployed `rangeTidW` family
(`EffectVmEmitV2.rangeTidW b = .custom (RANGE_W_TID_BASE + b)` for `b ≠ BAL_LIMB_BITS`; the Rust
wire id is `+5`, so these are wires `77` and `85`). Restated here rather than imported so this
module keeps `AirBuilder + EffectAirIR + DescriptorIR2` as its whole dependency cone. -/
def rangeTidW (bits : Nat) : TableId := .custom (64 + bits)

theorem rangeTid_w8 : rangeTidW SB = TableId.custom 72 := rfl
theorem rangeTid_w16 : rangeTidW CB = TableId.custom 80 := rfl

/-- Evaluating a left-folded sum of expressions. -/
theorem foldl_add_eval {α : Type} (a : Assignment) (l : List α) (F : α → Expr) (e0 : Expr) :
    (l.foldl (fun e x => Expr.add e (F x)) e0).eval a = e0.eval a + sumL l (fun x => (F x).eval a) := by
  induction l generalizing e0 with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, ih, sumL_cons, Expr.eval]; ring

/-- The `Σ_{i+j=m} x_i·y_j` cross-product expression — folded over the ANTIDIAGONAL, so only the
≤ 32 nonzero products are written (not the 1024-pair square). -/
def convExpr (xB yB m : Nat) : Expr :=
  (convPairs m).foldl (fun e pr => .add e (.mul (.var (xB + pr.1)) (.var (yB + pr.2)))) (.const 0)

/-- The `Σ_{i+j=m} q_i·p_j` expression. `p_j` is a CONSTANT, so this leg is linear in `q`. -/
def qpExpr (qB m : Nat) (pl : Nat → ℤ) : Expr :=
  (convPairs m).foldl (fun e pr => .add e (.mul (.const (pl pr.2)) (.var (qB + pr.1)))) (.const 0)

/-- The carry term at index `m` — `.const 0` at both ends, which is how the chain is pinned closed
without a boundary gate. -/
def chainExpr (cB m : Nat) : Expr :=
  if m = 0 then .const 0
  else if m ≤ NG - 1 then .add (.var (cB + m - 1)) (.const (-COFF))
  else .const 0

/-- **The coefficient gate expression at index `m`.** -/
def coefExpr (xB yB zB qB cB : Nat) (pl : Nat → ℤ) (m : Nat) : Expr :=
  .add (.add (.add (convExpr xB yB m) (.mul (.const (-1)) (qpExpr qB m pl)))
             (if m < SK then .mul (.const (-1)) (.var (zB + m)) else .const 0))
       (.add (chainExpr cB m) (.mul (.const (-((2 : ℤ) ^ SB))) (chainExpr cB (m + 1))))

theorem chainExpr_eval (a : Assignment) (cB m : Nat) :
    (chainExpr cB m).eval a = chainVal a cB m := by
  unfold chainExpr chainVal
  by_cases h0 : m = 0
  · simp [h0, Expr.eval]
  by_cases h1 : m ≤ NG - 1
  · simp [h0, h1, Expr.eval, sub_eq_add_neg]
  · simp [h0, h1, Expr.eval]

/-- ⚑ **THE BRIDGE.** The emitted gate expression evaluates to exactly the body the soundness
theorem quantifies over. Without this the theorem would be about a different object than the one
the descriptor carries. -/
theorem coefExpr_eval (a : Assignment) (xB yB zB qB cB : Nat) (pl : Nat → ℤ) (m : Nat) :
    (coefExpr xB yB zB qB cB pl m).eval a = coefBody a xB yB zB qB cB pl m := by
  have hswap : sumL (convPairs m) (fun pr => pl pr.2 * a (qB + pr.1))
      = sumL (convPairs m) (fun pr => a (qB + pr.1) * pl pr.2) :=
    sumL_congr _ _ _ (fun _ _ => mul_comm _ _)
  unfold coefExpr coefBody digitVal
  simp only [Expr.eval, convExpr, qpExpr, foldl_add_eval, chainExpr_eval, hswap]
  by_cases h : m < SK
  · simp only [if_pos h, Expr.eval]; ring
  · simp only [if_neg h, Expr.eval]; ring

/-- The `SK` limb columns at `base`. -/
def limbCols (base : Nat) : List Nat := (List.range SK).map (base + ·)
/-- The `NG − 1` carry columns at `cB`. -/
def carryCols (cB : Nat) : List Nat := (List.range (NG - 1)).map (cB + ·)

/-! ### The one-multiply layout (the measurement unit and the falsifier target). -/

def X_BASE : Nat := 0
def Y_BASE : Nat := SK
def Z_BASE : Nat := 2 * SK
def Q_BASE : Nat := 3 * SK
def C_BASE : Nat := 4 * SK
/-- `4·32 + 62 = 190` main columns. The IR-v2 path enforces no width cap (`MAX_TRACE_WIDTH` is a
v1/DSL constant `descriptor_ir2.rs` never consults), and `pasta_derive_prove` measures 2 131
columns parsing, checking and proving. -/
def MUL_WIDTH : Nat := 4 * SK + (NG - 1)

theorem MUL_WIDTH_eq : MUL_WIDTH = 190 := rfl

/-- **The source AIR of one sound Pasta multiply**, modulus-parametric in the limb vector `pl`. -/
def soundMulAir (pl : Nat → ℤ) : EffectAir :=
  { tables := [ mainTableDef MUL_WIDTH
              , ⟨rangeTidW SB, "range_w8", 1, .rangeLimb SB⟩
              , ⟨rangeTidW CB, "range_w16", 1, .rangeLimb CB⟩ ]
  , legs := (List.range NG).map
              (fun m => AirLeg.gate ⟨coefExpr X_BASE Y_BASE Z_BASE Q_BASE C_BASE pl m, .const 0⟩)
            ++ [ AirLeg.limbs ⟨limbCols X_BASE, SB, rangeTidW SB⟩
               , AirLeg.limbs ⟨limbCols Y_BASE, SB, rangeTidW SB⟩
               , AirLeg.limbs ⟨limbCols Z_BASE, SB, rangeTidW SB⟩
               , AirLeg.limbs ⟨limbCols Q_BASE, SB, rangeTidW SB⟩
               , AirLeg.limbs ⟨carryCols C_BASE, CB, rangeTidW CB⟩ ] }

/-- ⚑ **The compiler ACCEPTS this block** — every leg has a deployed main-rail image, which for the
five `limbs` legs is exactly the `0 < bits ≤ 29` verdict. A width of 30 would emit
`refuseConstraints` instead, and this theorem would be false. -/
theorem soundMulAir_mainRailOk (pl : Nat → ℤ) : (soundMulAir pl).mainRailOk = true := by
  unfold soundMulAir EffectAir.mainRailOk
  simp only [List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true]
  refine ⟨?_, by decide⟩
  intro m _
  rfl

/-- The `fpMul` descriptor: `x·y ≡ z (mod p)` (Pallas base / Vesta scalar). -/
def fpMulSoundDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-pasta-fpmul-sound::v1" MUL_WIDTH 0 [] (soundMulAir pLimb)

/-- The `fqMul` descriptor: same shape, `q` limbs. The encoding is field-independent. -/
def fqMulSoundDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-pasta-fqmul-sound::v1" MUL_WIDTH 0 [] (soundMulAir qLimb)

/-- ⚑ **THE EMITTED COST, as a theorem rather than a caption.** `63` coefficient gates + `4·32`
limb lookups + `62` carry lookups = **`253`** constraints for a standalone multiply (`189` when the
operands are already range-checked by whatever produced them). The emitted `9×30` gate was **1**,
and `PastaField` §6.4's own estimate for a sound one was `≈10³`. -/
theorem fpMulSoundDesc_constraint_count : fpMulSoundDesc.constraints.length = 253 := by
  unfold fpMulSoundDesc lowerAir Dregg2.Circuit.Emit.EffectLower.assemble
  simp only [List.map_nil, List.nil_append, List.append_nil]
  rfl

theorem fqMulSoundDesc_constraint_count : fqMulSoundDesc.constraints.length = 253 := by
  unfold fqMulSoundDesc lowerAir Dregg2.Circuit.Emit.EffectLower.assemble
  simp only [List.map_nil, List.nil_append, List.append_nil]
  rfl

/-! ## §7 — the descriptor's gates force the Pasta congruence AT `p_felt`. -/

/-- The limb vector of `p` recomposes to `p`. -/
theorem pLimb_recomposes : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pLimb j) = (pN : ℤ) := by
  decide

/-- …and of `q` to `q`. -/
theorem qLimb_recomposes : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * qLimb j) = (qN : ℤ) := by
  decide

/-- ⚑ **THE REPAIR, STATED AT THE EMITTED OBJECT.** Hypotheses: the DEPLOYED row denotation of
every emitted coefficient gate (`body ≡ 0 [ZMOD P]` — what `prove_vm_descriptor2` checks) plus the
range facts the five emitted `limbs` legs supply. Conclusion: the Pasta congruence.

Contrast `PastaField.fpMulCore_forces`, whose hypothesis is `evalH … = 0` **over ℤ** — a fact no
proof object establishes, which is why the falsifier exists. -/
theorem fpMulSound_forces (a : Assignment)
    (hx : ∀ i, i < SK → 0 ≤ a (X_BASE + i) ∧ a (X_BASE + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (Y_BASE + i) ∧ a (Y_BASE + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ a (Z_BASE + i) ∧ a (Z_BASE + i) < 2 ^ SB)
    (hq : ∀ i, i < SK → 0 ≤ a (Q_BASE + i) ∧ a (Q_BASE + i) < 2 ^ SB)
    (hc : ∀ i, i < NG - 1 → 0 ≤ a (C_BASE + i) ∧ a (C_BASE + i) < 2 ^ CB)
    (hgates : ∀ m, m < NG →
      ((coefExpr X_BASE Y_BASE Z_BASE Q_BASE C_BASE pLimb m).eval a ≡ 0 [ZMOD P])) :
    (pN : ℤ) ∣ (sVal a X_BASE * sVal a Y_BASE - sVal a Z_BASE) := by
  refine felt_gates_force_congruence a _ _ _ _ _ pLimb (pN : ℤ)
    hx hy hz hq pLimb_bounds pLimb_recomposes hc (fun m hm => ?_)
  have h := hgates m hm
  rw [coefExpr_eval] at h
  exact Int.modEq_zero_iff_dvd.mp h

/-- The same statement at the Vesta-base / Pallas-scalar modulus. -/
theorem fqMulSound_forces (a : Assignment)
    (hx : ∀ i, i < SK → 0 ≤ a (X_BASE + i) ∧ a (X_BASE + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (Y_BASE + i) ∧ a (Y_BASE + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ a (Z_BASE + i) ∧ a (Z_BASE + i) < 2 ^ SB)
    (hq : ∀ i, i < SK → 0 ≤ a (Q_BASE + i) ∧ a (Q_BASE + i) < 2 ^ SB)
    (hc : ∀ i, i < NG - 1 → 0 ≤ a (C_BASE + i) ∧ a (C_BASE + i) < 2 ^ CB)
    (hgates : ∀ m, m < NG → P ∣ (coefExpr X_BASE Y_BASE Z_BASE Q_BASE C_BASE qLimb m).eval a) :
    (qN : ℤ) ∣ (sVal a X_BASE * sVal a Y_BASE - sVal a Z_BASE) :=
  felt_gates_force_congruence a _ _ _ _ _ qLimb (qN : ℤ)
    hx hy hz hq qLimb_bounds qLimb_recomposes hc
    (fun m hm => by rw [← coefExpr_eval]; exact hgates m hm)

/-! ## §8 — the HONEST witness, generated here (Rust fills cells, it does not author them). -/

/-- The limb block of an honest `(x, y, z, q)` — columns `0..127`. -/
def mulLimbs (Xv Yv Zv Qv : Nat) : Assignment := fun col =>
  if col < SK then limbAt Xv col
  else if col < 2 * SK then limbAt Yv (col - SK)
  else if col < 3 * SK then limbAt Zv (col - 2 * SK)
  else if col < 4 * SK then limbAt Qv (col - 3 * SK)
  else 0

/-- The carry chain of the honest witness: `S 0 = 0`, `S (m+1) = (S m + T m) / 2^SB`. Every
division is exact BECAUSE the integer body is zero — that is the content, not a convenience. -/
def carryOf (Xv Yv Zv Qv : Nat) (pl : Nat → ℤ) : Nat → ℤ
  | 0 => 0
  | (m + 1) =>
      (carryOf Xv Yv Zv Qv pl m
        + digitVal (mulLimbs Xv Yv Zv Qv) X_BASE Y_BASE Z_BASE Q_BASE pl m) / (2 : ℤ) ^ SB

/-- The full honest assignment: limbs, then the offset carries at `C_BASE`. -/
def mulAsg (Xv Yv Zv Qv : Nat) (pl : Nat → ℤ) : Assignment := fun col =>
  if col < 4 * SK then mulLimbs Xv Yv Zv Qv col
  else if col < MUL_WIDTH then carryOf Xv Yv Zv Qv pl (col - 4 * SK + 1) + COFF
  else 0

/-- The honest `fpMul` witness at the `PastaField` KAT operands. -/
def fpHonest : Assignment :=
  mulAsg PastaField.Ref.X PastaField.Ref.Y (PastaField.Ref.fpMul PastaField.Ref.X PastaField.Ref.Y)
    ((PastaField.Ref.X * PastaField.Ref.Y - PastaField.Ref.fpMul PastaField.Ref.X PastaField.Ref.Y)
      / pN) pLimb

/-- ⚑ **THE HONEST POLARITY, as a named theorem.** Every one of the 63 emitted gate bodies is
EXACTLY zero over ℤ on the generated witness — a fortiori zero mod `P`, so the deployed prover
accepts it. (`decide`, kernel-reduced; no `native_decide`.) -/
theorem fpHonest_satisfies_gates :
    ((List.range NG).all fun m =>
      decide (coefBody fpHonest X_BASE Y_BASE Z_BASE Q_BASE C_BASE pLimb m = 0)) = true := by
  decide

/-- ⚑ **AND THE RANGES BITE ON IT** — every carry column lands inside the declared 16-bit table,
so the honest witness is not merely gate-satisfying but LOOKUP-satisfying. A witness that needed a
17-bit carry would prove nothing here and the bound `coefBody_abs_lt_P` would be about a shape the
prover cannot carry. -/
theorem fpHonest_carries_in_range :
    ((List.range (NG - 1)).all fun i =>
      decide (0 ≤ fpHonest (C_BASE + i) ∧ fpHonest (C_BASE + i) < 2 ^ CB)) = true := by
  decide

/-- ⚑ **AND THE FALSIFIER IS REFUSED.** The `9×30` forgery adds `−p·(δ₀ + 2^30·δ₁)`, a nonzero
multiple of `P`, to a gate body and stays invisible. Here the analogous move — bump quotient limb 0
by any nonzero `d` — moves gate 0's body by `−p₀·d` with `|p₀·d| ≤ 255·(2^8−1) < P`, so it can no
longer hide: the body is nonzero and `P ∤ body`. This exhibits it at `d = 1`. -/
theorem fpHonest_quotient_bump_is_caught :
    coefBody (fun c => if c = Q_BASE then fpHonest c + 1 else fpHonest c)
      X_BASE Y_BASE Z_BASE Q_BASE C_BASE pLimb 0 ≠ 0 := by
  decide

#assert_axioms fpHonest_satisfies_gates
#assert_axioms fpHonest_carries_in_range
#assert_axioms fpHonest_quotient_bump_is_caught

/-- The trace row of the honest witness (`MUL_WIDTH` felts, canonical). -/
def honestRow (pl : Nat → ℤ) (Xv Yv Zv Qv : Nat) : List ℤ :=
  (List.range MUL_WIDTH).map (mulAsg Xv Yv Zv Qv pl)

/-- The `fpMul` honest row, as the emit driver renders it. -/
def fpHonestRow : List ℤ := (List.range MUL_WIDTH).map fpHonest

/-- ⚑ Every emitted cell is a CANONICAL BabyBear felt (`0 ≤ v < P`) — so the Rust fixture parses as
`u32` and no cell is silently folded on the way in. -/
theorem fpHonestRow_canonical : (fpHonestRow.all fun v => decide (0 ≤ v ∧ v < P)) = true := by
  decide

#assert_axioms fpHonestRow_canonical

#assert_axioms telescope
#assert_axioms conv_recompose
#assert_axioms coefBody_abs_lt_P
#assert_axioms felt_gates_force_congruence
#assert_axioms coefExpr_eval
#assert_axioms soundMulAir_mainRailOk
#assert_axioms fpMulSoundDesc_constraint_count
#assert_axioms sb_wrapfree
#assert_axioms cb_wrapfree

end Dregg2.Circuit.Emit.PastaFieldSound
