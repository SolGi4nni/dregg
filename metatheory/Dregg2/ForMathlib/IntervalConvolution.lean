/-
# `Dregg2.ForMathlib.IntervalConvolution` — certified interval convolution + rigorous tail upper bound.

Built on `Dregg2.ForMathlib.CertifiedInterval` (signed rational interval arithmetic with outward rounding).
This file lifts the finite integer-distribution convolution (little-endian coefficient-list multiplication —
the exact law of a sum of independent bounded-support integer variables, `Dregg2.Crypto.MlKemDelta.cvMul`) to
INTERVAL coefficient lists, and proves the enclosure property: the interval convolution's `k`-th interval
**contains** the exact convolution's `k`-th coefficient. From that, a certified tail UPPER BOUND: the sum of
`hi`-endpoints over the escaping indices upper-bounds the exact tail mass.

## Why this exists (the "known-true but too big for the kernel" wall)

`MlKemDelta` §16 reduces the FIPS ML-KEM-768 `δ` bound to an EXACT convolution tail — residual **R1** — whose
value is the `2304`-fold convolution `prodCounts^{⊛2304} ⊛ cbdCounts ⊛ cErrLaw`, support `≈20000` wide, with
exact rational counts of `≈18000` bits (denominator `256^2304 ≈ 10^5550`). That exact object is kernel-`decide`
infeasible. The certified-interval route replaces the exact `18000`-bit integers by dyadic intervals at BOUNDED
precision (`CertifiedInterval.round`), computes a rigorous UPPER BOUND on the tail, and asks only whether that
bound clears `2^(-174)·total`. This module is the reusable machinery for that route (and any future such wall);
the frequency-domain FFT acceleration is scoped/named in the assessment section at the end.

## What is proved (containment is genuine — the interval brackets the exact value)

* `icvAdd_contains`, `icvMul_contains` — the interval convolution ENCLOSES the exact rational convolution
  (`qcvAdd`/`qcvMul`), pointwise, via `List.Forall₂` of `Contains`.
* `qcvMul_cast` — the exact rational convolution of cast integer lists IS the cast of `MlKemDelta.cvMul`, so the
  enclosure is genuinely about the ML-KEM count convolution.
* `qTailSum_le_ivTailSum` — the interval `hi`-endpoint tail sum upper-bounds the exact tail sum.
* `exactTailFrac_of_interval` — the certified capstone: an interval enclosure of the count list plus a checked
  arithmetic inequality on `ivTailSum` yields the exact tail-fraction bound `tail·den ≤ num·total`.
* `icvPow_contains` — the `n`-fold self-convolution power; `icvPow (prodCounts.map …) 2304` IS §16's R1 object.
* Small-case validation (`icvMul_cbd_self_exact`, `icvMul_contains_cbd_with_slack`, …) — the machinery
  reproduces §16's exact `cbd_selfconv`/`prodCounts` convolutions and encloses them from slack inputs, proved
  from the general enclosure theorems (NOT `decide`: ℚ-`decide` stalls on `Rat` gcd-normalization — itself an
  instance of the wall this module targets).
* §7 assessment — the `δ` scaling cost and the certified interval-FFT acceleration as the named remaining lane.

Kernel-clean (verified: every theorem's axioms ⊆ `{propext, Classical.choice, Quot.sound}`); no `sorry`, no
`native_decide`.
-/
import Mathlib
import Dregg2.ForMathlib.CertifiedInterval
import Dregg2.Crypto.MlKemDelta

namespace Dregg2.ForMathlib.IntervalConvolution

open Dregg2.ForMathlib.CertifiedInterval
open Dregg2.ForMathlib.CertifiedInterval.Interval

/-- Explicit element-wise `ℕ → ℚ` cast. Named (not the bare coercion `fun n => (n : ℚ)`) because the latter,
mapped over a `List ℕ`, triggers Lean's *list-level* coercion `List ℕ → List ℚ` and collapses the lambda to `id`,
blocking `List.map_cons`. `qcast` keeps the map element-wise. -/
def qcast : ℕ → ℚ := Nat.cast

/-- The enclosure relation between an interval list and an exact rational coefficient list: pointwise
`Contains`, same length (via `List.Forall₂`). -/
abbrev IContains (Is : List Interval) (xs : List ℚ) : Prop :=
  List.Forall₂ (fun (I : Interval) (x : ℚ) => I.Contains x) Is xs

/-! ## §1 — the exact rational convolution (what intervals must enclose) -/

/-- Elementwise add of two rational coefficient lists (padding the shorter with `0`) — the ℚ analog of
`MlKemDelta.cvAdd`, identical control flow. -/
def qcvAdd : List ℚ → List ℚ → List ℚ
  | [], g => g
  | f, [] => f
  | a :: f, b :: g => (a + b) :: qcvAdd f g

/-- Rational little-endian convolution (polynomial multiply) — the ℚ analog of `MlKemDelta.cvMul`. -/
def qcvMul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: f, g => qcvAdd (g.map (a * ·)) (0 :: qcvMul f g)

/-! ## §2 — the interval convolution -/

/-- Interval elementwise add (padding with the point interval `pt 0`). -/
def icvAdd : List Interval → List Interval → List Interval
  | [], G => G
  | F, [] => F
  | A :: F, B :: G => (add A B) :: icvAdd F G

/-- Interval little-endian convolution: schoolbook polynomial multiply over interval coefficients. -/
def icvMul : List Interval → List Interval → List Interval
  | [], _ => []
  | A :: F, G => icvAdd (G.map (fun B => mul A B)) (pt 0 :: icvMul F G)

/-! ## §3 — the enclosure (containment) theorems -/

/-- The interval sum encloses the exact rational sum. -/
theorem icvAdd_contains : ∀ {Is xs Js ys}, IContains Is xs → IContains Js ys →
    IContains (icvAdd Is Js) (qcvAdd xs ys) := by
  intro Is xs Js ys hI hJ
  induction hI generalizing Js ys with
  | nil => simpa [icvAdd, qcvAdd] using hJ
  | cons hhead htail ih =>
      cases hJ with
      | nil => simpa [icvAdd, qcvAdd] using List.Forall₂.cons hhead htail
      | cons hBb hJ' =>
          simp only [icvAdd, qcvAdd]
          exact List.Forall₂.cons (add_contains hhead hBb) (ih hJ')

/-- Scaling a contained list by a contained scalar (the inner `map` of the convolution). -/
theorem map_mul_contains {A : Interval} {a : ℚ} (hAa : A.Contains a) :
    ∀ {Js ys}, IContains Js ys → IContains (Js.map (fun B => mul A B)) (ys.map (a * ·)) := by
  intro Js ys h
  induction h with
  | nil => simp
  | cons hhead htail ih =>
      simp only [List.map_cons]
      exact List.Forall₂.cons (mul_contains hAa hhead) ih

/-- **THE CORE ENCLOSURE.** The interval convolution encloses the exact rational convolution, pointwise. -/
theorem icvMul_contains : ∀ {Is xs Js ys}, IContains Is xs → IContains Js ys →
    IContains (icvMul Is Js) (qcvMul xs ys) := by
  intro Is xs Js ys hI hJ
  induction hI with
  | nil => simp [icvMul, qcvMul]
  | cons hhead htail ih =>
      simp only [icvMul, qcvMul]
      exact icvAdd_contains (map_mul_contains hhead hJ)
        (List.Forall₂.cons (pt_contains (0 : ℚ)) ih)

/-! ## §4 — the bridge to `MlKemDelta.cvMul` (the enclosure is about the real ML-KEM count convolution) -/

/-- Casting an integer count list to ℚ commutes with `qcvAdd` / `cvAdd`. -/
theorem qcvAdd_cast (f g : List ℕ) :
    qcvAdd (f.map qcast) (g.map qcast)
      = (Dregg2.Crypto.MlKemDelta.cvAdd f g).map qcast := by
  induction f generalizing g with
  | nil => cases g <;> simp [qcvAdd, Dregg2.Crypto.MlKemDelta.cvAdd]
  | cons a f ih =>
      cases g with
      | nil => simp [qcvAdd, Dregg2.Crypto.MlKemDelta.cvAdd]
      | cons b g =>
          simp only [List.map_cons, qcvAdd, Dregg2.Crypto.MlKemDelta.cvAdd]
          rw [ih]; simp [qcast]

/-- Casting an integer count list to ℚ commutes with `qcvMul` / `cvMul` — so the exact rational convolution the
intervals enclose IS the cast of the exact ML-KEM integer convolution. -/
theorem qcvMul_cast (f g : List ℕ) :
    qcvMul (f.map qcast) (g.map qcast)
      = (Dregg2.Crypto.MlKemDelta.cvMul f g).map qcast := by
  induction f generalizing g with
  | nil => simp [qcvMul, Dregg2.Crypto.MlKemDelta.cvMul]
  | cons a f ih =>
      have h1 : (g.map qcast).map (fun x => qcast a * x)
              = (g.map (fun x => a * x)).map qcast := by
        rw [List.map_map, List.map_map]
        exact List.map_congr_left (fun n _ => by simp only [Function.comp_apply, qcast]; push_cast; ring)
      have h2 : (0 :: Dregg2.Crypto.MlKemDelta.cvMul f g).map qcast
              = (0 : ℚ) :: (Dregg2.Crypto.MlKemDelta.cvMul f g).map qcast := by simp [qcast]
      rw [List.map_cons]
      simp only [qcvMul, Dregg2.Crypto.MlKemDelta.cvMul]
      rw [h1, ih, ← h2, ← qcvAdd_cast]

/-- Point-interval enclosure of a rational list: `xs.map pt` encloses `xs` exactly. -/
theorem iContains_map_pt (xs : List ℚ) : IContains (xs.map pt) xs := by
  induction xs with
  | nil => simp
  | cons a xs ih => exact List.Forall₂.cons (pt_contains a) ih

/-- Enclosure of two maps over the same list, from a pointwise enclosure of the mapping functions. -/
theorem iContains_map_of {α : Type*} (l : List α) (f : α → Interval) (g : α → ℚ)
    (h : ∀ a, (f a).Contains (g a)) : IContains (l.map f) (l.map g) := by
  induction l with
  | nil => simp
  | cons a l ih => exact List.Forall₂.cons (h a) ih

/-- Point-interval convolution IS the point interval of the exact rational convolution (add). -/
theorem icvAdd_pt (xs ys : List ℚ) : icvAdd (xs.map pt) (ys.map pt) = (qcvAdd xs ys).map pt := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [icvAdd, qcvAdd]
  | cons a xs ih =>
      cases ys with
      | nil => simp [icvAdd, qcvAdd]
      | cons b ys => simp [icvAdd, qcvAdd, ih]

/-- Point-interval convolution IS the point interval of the exact rational convolution (mul). -/
theorem icvMul_pt (xs ys : List ℚ) : icvMul (xs.map pt) (ys.map pt) = (qcvMul xs ys).map pt := by
  induction xs generalizing ys with
  | nil => simp [icvMul, qcvMul]
  | cons a xs ih =>
      simp only [List.map_cons, icvMul, qcvMul]
      rw [← icvAdd_pt]
      congr 1
      · rw [List.map_map, List.map_map]
        exact List.map_congr_left (fun b _ => by simp only [Function.comp_apply]; exact mul_pt a b)
      · simp [ih]

/-! ## §5 — convolution POWER (the `n`-fold self-convolution — the actual `δ` object) -/

/-- The exact rational `n`-fold self-convolution (the law of a sum of `n` i.i.d. terms). -/
def qcvPow (xs : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | n + 1 => qcvMul xs (qcvPow xs n)

/-- The interval `n`-fold self-convolution. `icvPow (prodCounts.map …) 2304` IS §16's residual-**R1** object —
`prodCounts^{⊛2304}` — expressed over intervals; the enclosure below is proved, only the kernel EVALUATION is
the wall (see the §7 assessment). -/
def icvPow (Is : List Interval) : ℕ → List Interval
  | 0 => [pt 1]
  | n + 1 => icvMul Is (icvPow Is n)

/-- **THE POWER ENCLOSURE (the `δ`-object containment).** The interval `n`-fold self-convolution encloses the
exact `n`-fold self-convolution — so a bounded-precision interval evaluation of `prodCounts^{⊛2304}` provably
brackets the exact (`18000`-bit) convolution, coefficient by coefficient. -/
theorem icvPow_contains {Is : List Interval} {xs : List ℚ} (h : IContains Is xs) :
    ∀ n, IContains (icvPow Is n) (qcvPow xs n)
  | 0 => List.Forall₂.cons (pt_contains 1) List.Forall₂.nil
  | n + 1 => icvMul_contains h (icvPow_contains h n)

/-! ## §5b — the certified tail upper bound -/

/-- Pointwise enclosure via `getD` — holds for EVERY index (out of range gives `(pt 0).Contains 0`, true). -/
theorem getD_contains {Is : List Interval} {xs : List ℚ} (h : IContains Is xs) :
    ∀ i, (Is.getD i (pt 0)).Contains (xs.getD i (0 : ℚ)) := by
  induction h with
  | nil => intro i; simp only [List.getD_nil]; exact pt_contains 0
  | cons hhead htail ih =>
      intro i
      cases i with
      | zero => simpa only [List.getD_cons_zero] using hhead
      | succ j => simpa only [List.getD_cons_succ] using ih j

/-- The exact tail mass of a rational coefficient list: the sum of coefficients at indices `i` whose value
`offset + i` escapes `|·| ≥ R`. -/
def qTailSum (xs : List ℚ) (offset R : ℤ) : ℚ :=
  ∑ i ∈ (Finset.range xs.length).filter (fun (i : ℕ) => R ≤ |offset + (i : ℤ)|), xs.getD i 0

/-- The certified tail UPPER bound: the sum of interval `hi`-endpoints over the escaping indices. -/
def ivTailSum (Is : List Interval) (offset R : ℤ) : ℚ :=
  ∑ i ∈ (Finset.range Is.length).filter (fun (i : ℕ) => R ≤ |offset + (i : ℤ)|), (Is.getD i (pt 0)).hi

/-- **THE CERTIFIED TAIL BOUND.** If the interval list encloses the exact list, the interval tail sum
upper-bounds the exact tail sum. This is what turns a bounded-precision interval computation into a rigorous
tail certificate. -/
theorem qTailSum_le_ivTailSum {Is : List Interval} {xs : List ℚ} (h : IContains Is xs) (offset R : ℤ) :
    qTailSum xs offset R ≤ ivTailSum Is offset R := by
  have hlen : Is.length = xs.length := h.length_eq
  rw [qTailSum, ivTailSum, hlen]
  exact Finset.sum_le_sum (fun i _ => (getD_contains h i).2)

/-- **THE CERTIFIED CAPSTONE (ℚ).** Given an interval enclosure `Is` of the cast count list `d`, and a CHECKED
arithmetic certificate `ivTailSum Is · den ≤ num · total` (with `total = d.sum`, the known exact mass), the exact
tail fraction obeys `tail · den ≤ num · total`. The hypotheses on the RHS are bounded-precision-computable; the
exact `18000`-bit convolution is never formed. -/
theorem exactTailFrac_of_interval {Is : List Interval} {xs : List ℚ} (h : IContains Is xs)
    (offset R : ℤ) (num den total : ℚ) (hden : 0 ≤ den)
    (hcert : ivTailSum Is offset R * den ≤ num * total) :
    qTailSum xs offset R * den ≤ num * total :=
  le_trans (mul_le_mul_of_nonneg_right (qTailSum_le_ivTailSum h offset R) hden) hcert

/-! ## §6 — small-case validation (reusing `MlKemDelta` §16; proved from the general theorems, no `decide`)

`decide` on ℚ is itself an instance of the "known-true but the kernel stalls" wall this module targets: `Rat`
equality/order reduce through gcd-normalization that the kernel `whnf` does not evaluate. So the validation is
proved from the GENERAL enclosure theorems above (a stronger check than a point `decide`): the interval machinery
provably reproduces §16's exact convolution, and encloses it even from nondegenerate/slack inputs. -/

/-- The CBD self-convolution `[1,8,28,56,70,56,28,8,1]` cast to ℚ (the value of `qcvMul` on the CBD counts). -/
theorem qcvMul_cbd_self :
    qcvMul (Dregg2.Crypto.MlKemDelta.cbdCounts.map qcast)
           (Dregg2.Crypto.MlKemDelta.cbdCounts.map qcast)
      = ([1, 8, 28, 56, 70, 56, 28, 8, 1] : List ℕ).map qcast := by
  rw [qcvMul_cast, Dregg2.Crypto.MlKemDelta.cbd_selfconv]

/-- **(VALIDATION — the interval machinery reproduces §16's exact `cbd_selfconv`.)** Convolving the CBD counts as
POINT intervals gives exactly the point intervals of `[1,8,28,56,70,56,28,8,1]` — the interval convolution
computes the exact convolution when inputs are exact. -/
theorem icvMul_cbd_self_exact :
    icvMul (Dregg2.Crypto.MlKemDelta.cbdCounts.map (fun n => pt (n : ℚ)))
           (Dregg2.Crypto.MlKemDelta.cbdCounts.map (fun n => pt (n : ℚ)))
      = ([1, 8, 28, 56, 70, 56, 28, 8, 1] : List ℕ).map (fun n => pt (n : ℚ)) := by
  have e1 : Dregg2.Crypto.MlKemDelta.cbdCounts.map (fun n => pt (n : ℚ))
      = (Dregg2.Crypto.MlKemDelta.cbdCounts.map qcast).map pt := by
    rw [List.map_map]; rfl
  rw [e1, icvMul_pt, qcvMul_cbd_self, List.map_map]; rfl

/-- **(VALIDATION — the enclosure fires with genuine slack.)** Widen each CBD count to the interval `[n-1, n+1]`;
the interval convolution still ENCLOSES the exact self-convolution `[1,8,…,1]`. This exercises the real signed
interval arithmetic (nondegenerate intervals) through the general `icvMul_contains`. -/
theorem icvMul_contains_cbd_with_slack :
    IContains
      (icvMul (Dregg2.Crypto.MlKemDelta.cbdCounts.map (fun (n : ℕ) => (⟨(n : ℚ) - 1, (n : ℚ) + 1⟩ : Interval)))
              (Dregg2.Crypto.MlKemDelta.cbdCounts.map (fun (n : ℕ) => (⟨(n : ℚ) - 1, (n : ℚ) + 1⟩ : Interval))))
      (([1, 8, 28, 56, 70, 56, 28, 8, 1] : List ℕ).map qcast) := by
  have hpt : IContains
      (Dregg2.Crypto.MlKemDelta.cbdCounts.map (fun (n : ℕ) => (⟨(n : ℚ) - 1, (n : ℚ) + 1⟩ : Interval)))
      (Dregg2.Crypto.MlKemDelta.cbdCounts.map qcast) :=
    iContains_map_of _ _ _ (fun n => ⟨by simp only [qcast]; linarith, by simp only [qcast]; linarith⟩)
  have h := icvMul_contains hpt hpt
  rwa [qcvMul_cbd_self] at h

/-- **(VALIDATION — the product-law self-convolution.)** The `prodCounts` law `[2,0,16,32,156,32,16,0,2]` (the
per-term law of every one of §16's `2304` cross-terms) self-convolved as point intervals reproduces the exact
2-fold product convolution, enclosed. -/
theorem icvMul_contains_prod_self :
    IContains
      (icvMul (Dregg2.Crypto.MlKemDelta.prodCounts.map (fun n => pt (n : ℚ)))
              (Dregg2.Crypto.MlKemDelta.prodCounts.map (fun n => pt (n : ℚ))))
      ((Dregg2.Crypto.MlKemDelta.cvMul Dregg2.Crypto.MlKemDelta.prodCounts
          Dregg2.Crypto.MlKemDelta.prodCounts).map qcast) := by
  have e1 : Dregg2.Crypto.MlKemDelta.prodCounts.map (fun n => pt (n : ℚ))
      = (Dregg2.Crypto.MlKemDelta.prodCounts.map qcast).map pt := by
    rw [List.map_map]; rfl
  rw [e1, icvMul_pt, qcvMul_cast]
  exact iContains_map_pt _

/-- **(VALIDATION — the certified tail bound fires on a nondegenerate input.)** The interval tail sum
upper-bounds the exact tail sum for the slack CBD self-convolution — `qTailSum_le_ivTailSum` end-to-end on real
interval data. -/
theorem tailSum_certificate_fires :
    qTailSum (([1, 8, 28, 56, 70, 56, 28, 8, 1] : List ℕ).map qcast) (-4) 3
      ≤ ivTailSum
          (icvMul (Dregg2.Crypto.MlKemDelta.cbdCounts.map (fun (n : ℕ) => (⟨(n : ℚ) - 1, (n : ℚ) + 1⟩ : Interval)))
                  (Dregg2.Crypto.MlKemDelta.cbdCounts.map (fun (n : ℕ) => (⟨(n : ℚ) - 1, (n : ℚ) + 1⟩ : Interval))))
          (-4) 3 :=
  qTailSum_le_ivTailSum icvMul_contains_cbd_with_slack (-4) 3

/-! ## §7 — ASSESSMENT: the `δ` scaling, and the FFT acceleration as the precisely-named remaining lane.

**What this module IS.** A reusable, kernel-clean CERTIFIED-INTERVAL CONVOLUTION: signed rational interval
arithmetic (`CertifiedInterval`, four-corner `mul`, `pow`, outward dyadic `round`), the *direct* (schoolbook)
interval convolution + power with a proved enclosure of the exact convolution (`icvMul_contains`,
`icvPow_contains`), and a certified tail upper bound (`qTailSum_le_ivTailSum`, `exactTailFrac_of_interval`).
`icvPow (prodCounts.map (round k ∘ pt ∘ qcast)) 2304` is *literally* §16's residual-**R1** object
`prodCounts^{⊛2304}`, and its enclosure of the exact convolution is a THEOREM here — the exact `18000`-bit
integers are never formed; each interval endpoint stays a `~k`-bit dyadic. Only the kernel EVALUATION of that
term is the wall.

**The `δ` object.** `MlKemDelta` §16/§18: the per-coefficient noise law is `prodCounts^{⊛2304} ⊛ cbdCounts ⊛
cErrLaw`, support `≈±9300` (`≈20000` wide), and `δ = Pr[832 ≤ |·|]` is its tail. FIPS needs `δ ≤ 2^(-164)`,
i.e. per-coeff tail `≤ 2^(-174)` after the `768·2` union; the true value is `≈2^(-180)` (a `~6`-bit margin), so
`~200`-bit interval precision is comfortable. §18 already supplies the TRUE `cErrLaw` (so §16's residual **R2** is
gone); the surviving wall is exactly **R1** — evaluating the tail of this convolution.

**Cost, honestly (why `decide` needs the FFT, not just intervals).**
* *Direct interval route (built here).* `prodCounts^{⊛2304}` by repeated squaring is `~14` convolutions
  (`2304 = 0b100100000000`); each is schoolbook `O(n²)` with `n≈20000`, so `≈4·10⁸` interval mults per
  convolution, `≈6·10⁹` interval mults total, each `~200`-bit. That is a RIGOROUS bounded-precision certificate
  (no `18000`-bit blowup) but `≈10³×` beyond kernel `decide`'s practical `~10⁶`–`10⁷`-op reach. So the direct
  route SHARPENS R1 from "`18000`-bit exact, hopeless" to "bounded-precision, `~10³×` over budget" — real
  progress, still not in-kernel.
* *Interval-FFT route (the acceleration — NOT built here).* One forward DFT `O(n log n) ≈ 3·10⁵` complex-interval
  ops, a pointwise `2304`-th power `≈ n·log 2304 ≈ 2·10⁵`, one inverse DFT `≈ 3·10⁵` — total `≈10⁶`
  complex-interval ops at `~200`-bit. That is `~10⁴×` cheaper than the direct route and lands at the EDGE of
  kernel `decide` feasibility (raised heartbeats, plausibly in-band). This is precisely why the title is
  interval-*FFT*: the FFT is the lever that could bring R1 in-kernel.

**The named remaining lane (to close FIPS `δ` by this route).** All of it REUSES this file's core unchanged:
1. **Complex intervals** = a box `⟨re : Interval, im : Interval⟩`; `+,·` inherit containment directly from
   `add_contains`/`mul_contains` (the four-corner signed `mul` is exactly what the complex product needs). Small.
2. **Certified roots of unity** `ω_N^k`: either rational-argument enclosures of `Complex.cos`/`sin` via
   Taylor-remainder interval bounds, or an algebraic recurrence `ω^{k+1} = ω·ω^k` from one certified seed `ω_N`
   with a per-step outward `round`. A self-contained sub-lane (Mathlib has `Real.cos`/`sin` but not rigorous
   rational enclosures).
3. **DFT/IDFT + the convolution theorem over intervals**: `IDFT(DFT f ⊙ DFT g)` encloses `f ⊛ g` (the standard
   circular-convolution identity, with the `1/N` scale and enough zero-padding that circular = linear). The
   math is classical; the certified-interval statement + kernel run is the multi-lane campaign.
4. **Run it**: evaluate `icvPow`-via-FFT on `prodCounts` to `~200` bits, convolve with `cbdCounts`/`cErrLaw`,
   feed `ivTailSum … ≤ 2^(-174)·total` into `exactTailFrac_of_interval` → `exactConvTailFrac_closes_delta`.

**Bottom line.** Interval arithmetic: BUILT + proven. Convolution theorem (enclosure/containment): BUILT +
proven, including the `2304`-fold power object. Small-case validation against §16's `cbd_selfconv`/`prodCounts`:
DONE (no `decide` — from the general theorems, dodging the ℚ-`decide` wall). δ scaling: the direct route is a
rigorous bounded-precision certificate `~10³×` over kernel budget; the FFT acceleration (steps 1–4 above) is the
`~10⁴×` lever that could bring R1 in-kernel and is the precisely-scoped remaining lane. -/

end Dregg2.ForMathlib.IntervalConvolution
