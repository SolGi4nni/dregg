/-
# Dregg2.Circuit.Emit.PastaAddSubSound — the Pasta ADD and SUB gates, sound IN THE FIELD THE
PROVER CHECKS.

## The defect, measured on the DEPLOYED artifact — not described

`PastaField.fpAddCore`/`fpSubCore` (and the `fq` pair) are ONE degree-1 gate each over the `9×30`
encoding:

    add:  Σ 2^(30 i)·(x_i + y_i − z_i)  −  p·c   =  0
    sub:  Σ 2^(30 i)·(x_i − y_i − z_i)  +  p·c   =  0

Their forcing lemmas (`fpAddCore_forces`, `fpSubCore_forces`, axiom-clean) are true and they are
**about ℤ**. The deployed prover reads gate bodies in BabyBear (`P = 2013265921`). There the gate
forces nothing: the nine `z` weights `2^(30 i)` and the carry weight `±p` are ALL units mod `P`,
`pastaLimbRange` is emitted nowhere, and nothing pins those columns.

This is the SAME defect the multiply had, and it is live on the same checked-in descriptor.
Measured on `circuit/descriptors/by-name/pasta-rcb-windowed.json` (45 constraints, 525 columns):

  * **19 of its 42 plain gates are Pasta add/sub** — zero var×var products, 28 columns, one column
    entering with coefficient exactly `±p` (the carry/borrow), at columns `423..441`. Fourteen
    carry `−p` (add) and five carry `+p` (sub).
  * Three of them (constraints **30**, **33**, **36** — a sub and two adds) own a nine-limb `z`
    block that appears in no OTHER plain gate: columns `234..242`, `261..269`, `288..296`. Those
    blocks are read by the three `on_transition` window gates 42/43/44 — which do not fire on the
    LAST row.
  * So: move two cells of the honest 64-row fixture's **last** row — `z` limb 0 by
    `(−2^240) mod P = 1450097237` and `z` limb 8 by `1`. The gate's integer body goes from `0` to a
    **240-bit** (sub, c30) / **241-bit** (add, c33) nonzero value, stays `0 mod P`, and **no other
    constraint on any row is disturbed**. The deployed prover proves it and the verifier accepts.

`circuit/tests/pasta_addsub_felt_soundness.rs` is that witness end to end. It is the pre-image
everything below has to refuse.

## The encoding, and ⚑ ITS OWN BOUND — recomputed, not inherited

`PastaFieldSound` proved a multiply sound at `SB = 8` bits × `SK = 32` limbs with 16-bit carries,
bounding each of its 63 coefficient-gate bodies by `2·1024·255² + 255 + 2^15 + 2^8·2^15 =
141 592 831`. **That bound does not transfer**: its dominant term is the 1024-pair convolution,
which add/sub does not have, and its `2^15` carry offset is sized for that convolution's carries.
Add/sub is re-derived from its OWN coefficient structure here.

Add/sub is a LINEAR identity, so it needs `NA = SK = 32` coefficient gates (not `2·SK − 1`), one
per limb position, and no antidiagonal:

    x_m  +  sy·y_m  −  z_m  +  sc·(p_m · c)  +  S_m  −  2^8·S_(m+1)  =  0        (m < 32)

with `(sy, sc) = (+1, −1)` for add and `(−1, +1)` for sub. The single witness column `c` is
lookup-pinned to **one bit** and the `p_m` are gate CONSTANTS `< 2^8`, so every term is a byte
product and the whole body is bounded by

    4·(2^8 − 1)  +  ACOFF  +  2^8·ACOFF  =  1020 + 128 + 32768  =  **33 916**  <  P

(`adBody_abs_lt_P` — 0.0017% of the field, four decimal orders below the multiply's margin because
there is no convolution). Because the body cannot reach `P`, `P ∣ body` FORCES `body = 0` over ℤ;
the 32 integer identities telescope, and the base-`2^8` recomposition is exactly
`X + sy·Y − Z + sc·c·M = 0`. That is `addsub_gates_force_congruence`.

### Why the carry is 8 bits, and why `c` is a separate one-bit table

The honest carry chain never leaves `{−1, 0, 1}` (both KAT fixtures below; `adAsg` generates it and
`decide` checks it). The DECLARED width only has to (a) hold the honest values and (b) keep the body
under `P`. `ACB = 8` does both with room, and `8 % 4 = 0` — so the deployed nibble realization
(`descriptor_ir2.rs::eval_decomp`, `limb_geom`) spends **one** `assert_zero` and two columns per
carry, and the carries reuse the SAME 8-bit table the limbs query. One extra table, one extra
column: the carry BIT at width 1, which costs `1 % 4 + 2 = 3` deployed constraints — the price of
saying "this is a bit" rather than "this is small".

⚑ The conclusion does NOT depend on `c` being a bit. `c` is a free witness exactly as the
multiply's quotient block is, and the congruence `M ∣ X + sy·Y − Z` follows for ANY `c` the range
admits. The one-bit pin is there because it is the true statement about the witness, and because it
is what a later canonicity (`z < p`) argument will need.

## Range widths (House rule: 29 is the ceiling, and it is proved)

`SB = 8`, `ACB = 8` and the carry-bit width `1` are all `≤ 29`, so all three are wrap-free
(`RangeFieldContainment.wrap_free_iff_le_29`); `acb_wrapfree`/`cbit_wrapfree` instantiate it here.
`EffectAirIR.LimbsLeg.mainRailOk` REFUSES `≥ 30`, so the compiler is the enforcement.

## What is REUSED and what is NEW

REUSED from `PastaFieldSound` (single source, no second copy): `SB`/`SK`, the `sumL` plumbing, the
`telescope` lemma, `abs_add_le'`/`abs_sub_le'`/`sumL_abs_le`, `limbAt`/`pLimb`/`qLimb` and their
bounds, `sVal`, `limbCols`, `rangeTidW`, `pLimb_recomposes`/`qLimb_recomposes`, `foldl_add_eval`.
NEW here: `NA`, `ACB`, `ACOFF`, the add/sub digit and its **own** bound, the linear recomposition
(`ad_recompose` — the analogue of `conv_recompose`, and much smaller), the four descriptors, and
the two generated honest witnesses.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. Facts are NAMED THEOREMS, not `#guard`s — this file adds zero guards.
-/
import Dregg2.Circuit.Emit.PastaFieldSound

namespace Dregg2.Circuit.Emit.PastaAddSubSound

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectLower (P)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaFieldSound

set_option autoImplicit false
-- the emitted descriptor's spine (32 gate legs, 128 columns) and the 32-limb recompositions are
-- kernel-reduced, which the default 512 does not reach.
set_option maxRecDepth 40000

/-! ## §0 — The parameters that are NEW here, and their wrap-freedom.

`SB = 8` and `SK = 32` come from `PastaFieldSound` unchanged — the limb encoding is the same one,
which is what makes an add's output usable as a multiply's operand without a re-encode. -/

/-- Coefficient gates per add/sub: `SK = 32`. ⚑ **Not `2·SK − 1`** — add/sub is linear, so the
result occupies the same `SK` limb positions as the operands and the top carry must vanish. -/
def NA : Nat := SK

theorem NA_eq : NA = 32 := rfl

/-- The carry range width. `8 % 4 = 0` — one deployed constraint, two columns — and it is the SAME
width the limbs use, so the carries query the same table. -/
def ACB : Nat := 8

/-- The carry offset: a carry column holds `S + ACOFF ∈ [0, 2^8)`, so `S ∈ [−128, 128)`. The honest
chain never leaves `{−1, 0, 1}` (`fpAddHonest_carries_in_range`, `fpSubHonest_carries_in_range`). -/
def ACOFF : ℤ := 2 ^ 7

/-- The width of the single carry/borrow witness column. -/
def CBITS : Nat := 1

theorem acb_wrapfree : Dregg2.Circuit.RangeFieldContainment.Wrapfree ACB :=
  (Dregg2.Circuit.RangeFieldContainment.wrap_free_iff_le_29 ACB).mpr (by decide)

theorem cbit_wrapfree : Dregg2.Circuit.RangeFieldContainment.Wrapfree CBITS :=
  (Dregg2.Circuit.RangeFieldContainment.wrap_free_iff_le_29 CBITS).mpr (by decide)

/-! ## §1 — The digit, the carry chain, and the body. -/

/-- The `m`-th digit of the integer body `x + sy·y − z + sc·c·M`, read off the trace.

`sy` is the sign on `y` and `sc` the sign on the reduction term; `(1, −1)` is add and `(−1, 1)` is
sub. Both are PARAMETERS, so one theorem covers all four emitted descriptors — the `p`/`q` split
rides on `pl` exactly as it does in the multiply. -/
def adDigit (a : Assignment) (xB yB zB cCol : Nat) (pl : Nat → ℤ) (sy sc : ℤ) (m : Nat) : ℤ :=
  if m < SK then
    a (xB + m) + sy * a (yB + m) - a (zB + m) + sc * (pl m * a cCol)
  else 0

/-- The carry chain read off the trace: `S 0 = 0`, `S m = a(cB + m − 1) − ACOFF` for
`1 ≤ m ≤ NA − 1`, and `S NA = 0`. ⚑ Both ends are pinned closed **by construction** — there is no
column for `S 0` or `S NA` — so this file needs no boundary gate. -/
def adChain (a : Assignment) (cB m : Nat) : ℤ :=
  if m = 0 then 0 else if m ≤ NA - 1 then a (cB + m - 1) - ACOFF else 0

theorem adChain_zero (a : Assignment) (cB : Nat) : adChain a cB 0 = 0 := rfl

theorem adChain_top (a : Assignment) (cB : Nat) : adChain a cB NA = 0 := by
  unfold adChain NA SK; norm_num

/-- The gate body at index `m`: digit + carry-in − radix · carry-out. -/
def adBody (a : Assignment) (xB yB zB cCol cB : Nat) (pl : Nat → ℤ) (sy sc : ℤ) (m : Nat) : ℤ :=
  adDigit a xB yB zB cCol pl sy sc m + adChain a cB m - (2 : ℤ) ^ SB * adChain a cB (m + 1)

/-! ## §2 — THE RECOMPOSITION (add/sub's analogue of `conv_recompose`, and far smaller). -/

/-- **The recomposition.** The base-`2^SB` fold of the 32 digits IS `X + sy·Y − Z + sc·c·M`. This is
the linear counterpart of the multiply's convolution: no antidiagonal, no product list, because the
identity is degree 1 in the trace apart from the single `c·constant` term. -/
theorem ad_recompose (a : Assignment) (xB yB zB cCol : Nat) (pl : Nat → ℤ) (sy sc M : ℤ)
    (hplM : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = M) :
    sumL (List.range NA) (fun m => ((2 : ℤ) ^ SB) ^ m * adDigit a xB yB zB cCol pl sy sc m)
      = sVal a xB + sy * sVal a yB - sVal a zB + sc * (M * a cCol) := by
  have hstep : ∀ m ∈ List.range NA,
      ((2 : ℤ) ^ SB) ^ m * adDigit a xB yB zB cCol pl sy sc m
        = (((2 : ℤ) ^ SB) ^ m * a (xB + m) + sy * (((2 : ℤ) ^ SB) ^ m * a (yB + m))
            - ((2 : ℤ) ^ SB) ^ m * a (zB + m))
          + (sc * a cCol) * (((2 : ℤ) ^ SB) ^ m * pl m) := by
    intro m hm
    have hlt : m < SK := by
      have := List.mem_range.mp hm; unfold NA at this; exact this
    unfold adDigit
    rw [if_pos hlt]
    ring
  rw [sumL_congr _ _ _ hstep, sumL_add, sumL_sub, sumL_add, sumL_smul, sumL_smul]
  unfold sVal NA
  rw [hplM]
  ring

/-! ## §3 — THE BOUND, recomputed from add/sub's own coefficient structure. -/

/-- The digit is bounded by **four bytes** — one for each of `x_m`, `y_m`, `z_m` and `p_m·c`.
⚑ This is where add/sub differs from the multiply: there is no `2·1024·255²` convolution term. -/
theorem adDigit_abs_le (a : Assignment) (xB yB zB cCol : Nat) (pl : Nat → ℤ) (sy sc : ℤ) (m : Nat)
    (hsy : sy = 1 ∨ sy = -1) (hsc : sc = 1 ∨ sc = -1)
    (hx : ∀ i, i < SK → 0 ≤ a (xB + i) ∧ a (xB + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (yB + i) ∧ a (yB + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ a (zB + i) ∧ a (zB + i) < 2 ^ SB)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hcb : 0 ≤ a cCol ∧ a cCol < 2) :
    |adDigit a xB yB zB cCol pl sy sc m| ≤ 4 * ((2 : ℤ) ^ SB - 1) := by
  unfold adDigit
  by_cases hm : m < SK
  · rw [if_pos hm]
    obtain ⟨hx0, hx1⟩ := hx m hm
    obtain ⟨hy0, hy1⟩ := hy m hm
    obtain ⟨hz0, hz1⟩ := hz m hm
    obtain ⟨hp0, hp1⟩ := hpl m
    obtain ⟨hc0, hc1⟩ := hcb
    have hB : (2 : ℤ) ^ SB = 256 := by norm_num [SB]
    rw [hB] at hx1 hy1 hz1 hp1 ⊢
    have hsyy : -255 ≤ sy * a (yB + m) ∧ sy * a (yB + m) ≤ 255 := by
      rcases hsy with rfl | rfl <;> constructor <;> nlinarith
    have hpc : 0 ≤ pl m * a cCol ∧ pl m * a cCol ≤ 255 := by
      constructor
      · positivity
      · nlinarith
    have hscpc : -255 ≤ sc * (pl m * a cCol) ∧ sc * (pl m * a cCol) ≤ 255 := by
      rcases hsc with rfl | rfl <;> constructor <;> nlinarith [hpc.1, hpc.2]
    rw [abs_le]
    constructor <;> linarith [hsyy.1, hsyy.2, hscpc.1, hscpc.2]
  · rw [if_neg hm]; norm_num [SB]

/-- The carry is bounded by the declared range width. -/
theorem adChain_abs_le (a : Assignment) (cB m : Nat)
    (hc : ∀ i, i < NA - 1 → 0 ≤ a (cB + i) ∧ a (cB + i) < 2 ^ ACB) :
    |adChain a cB m| ≤ ACOFF := by
  unfold adChain
  by_cases h0 : m = 0
  · rw [if_pos h0]; simp [ACOFF]
  by_cases h1 : m ≤ NA - 1
  · rw [if_neg h0, if_pos h1]
    obtain ⟨hl, hr⟩ := hc (m - 1) (by omega)
    have hidx : cB + m - 1 = cB + (m - 1) := by omega
    have hACB : (2 : ℤ) ^ ACB = 2 * ACOFF := by norm_num [ACB, ACOFF]
    rw [hidx, abs_le]
    constructor <;> linarith
  · rw [if_neg h0, if_neg h1]; simp [ACOFF]

/-- ⚑ **EVERY ADD/SUB GATE BODY FITS A FELT** — `33 916 < 2 013 265 921`. This is the whole repair
in one line, and the number is add/sub's OWN: `4·255 + 128 + 256·128`. At `9×30` the same body
reached `2^271`. -/
theorem adBody_abs_lt_P (a : Assignment) (xB yB zB cCol cB : Nat) (pl : Nat → ℤ) (sy sc : ℤ)
    (m : Nat)
    (hsy : sy = 1 ∨ sy = -1) (hsc : sc = 1 ∨ sc = -1)
    (hx : ∀ i, i < SK → 0 ≤ a (xB + i) ∧ a (xB + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (yB + i) ∧ a (yB + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ a (zB + i) ∧ a (zB + i) < 2 ^ SB)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hcb : 0 ≤ a cCol ∧ a cCol < 2)
    (hc : ∀ i, i < NA - 1 → 0 ≤ a (cB + i) ∧ a (cB + i) < 2 ^ ACB) :
    |adBody a xB yB zB cCol cB pl sy sc m| < P := by
  have hd := adDigit_abs_le a xB yB zB cCol pl sy sc m hsy hsc hx hy hz hpl hcb
  have hc1 := adChain_abs_le a cB m hc
  have hc2 := adChain_abs_le a cB (m + 1) hc
  have hscale : |(2 : ℤ) ^ SB * adChain a cB (m + 1)| ≤ (2 : ℤ) ^ SB * ACOFF := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (2 : ℤ) ^ SB)]
    exact mul_le_mul_of_nonneg_left hc2 (by positivity)
  have hnum : 4 * ((2 : ℤ) ^ SB - 1) + ACOFF + (2 : ℤ) ^ SB * ACOFF < P := by
    norm_num [SB, ACOFF, Dregg2.Circuit.Emit.EffectLower.P]
  unfold adBody
  have h1 := abs_sub_le' (adDigit a xB yB zB cCol pl sy sc m + adChain a cB m)
    ((2 : ℤ) ^ SB * adChain a cB (m + 1))
  have h2 := abs_add_le' (adDigit a xB yB zB cCol pl sy sc m) (adChain a cB m)
  linarith

/-- The exact numeric margin, named so it is not a caption a reader has to recompute. -/
theorem adBody_bound_value : 4 * ((2 : ℤ) ^ SB - 1) + ACOFF + (2 : ℤ) ^ SB * ACOFF = 33916 := by
  norm_num [SB, ACOFF]

/-! ## §4 — THE THEOREM: the mod-`P` reading forces the Pasta congruence. -/

/-- ⚑ **THE THEOREM.** From the reading the DEPLOYED PROVER performs — every one of the 32
coefficient gate bodies `≡ 0 (mod P)` — together with the range facts the emitted lookups supply,
the modular congruence `x + sy·y ≡ z (mod M)` follows, where `M` is whatever modulus the constant
limb vector `pl` recomposes to.

`fpAddCore_forces` needed `evalH … = 0` **over ℤ** and had no way to get it; this one is handed
`P ∣ body` and DERIVES `body = 0`, because the body fits. `pl`, `sy` and `sc` are parameters, so the
single statement covers `fp{Add,Sub}` and `fq{Add,Sub}`. -/
theorem addsub_gates_force_congruence
    (a : Assignment) (xB yB zB cCol cB : Nat) (pl : Nat → ℤ) (sy sc M : ℤ)
    (hsy : sy = 1 ∨ sy = -1) (hsc : sc = 1 ∨ sc = -1)
    (hx : ∀ i, i < SK → 0 ≤ a (xB + i) ∧ a (xB + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (yB + i) ∧ a (yB + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ a (zB + i) ∧ a (zB + i) < 2 ^ SB)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hplM : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = M)
    (hcb : 0 ≤ a cCol ∧ a cCol < 2)
    (hc : ∀ i, i < NA - 1 → 0 ≤ a (cB + i) ∧ a (cB + i) < 2 ^ ACB)
    -- ⚑ the DEPLOYED reading: the prover checks each body in BabyBear, not over ℤ.
    (hgates : ∀ m, m < NA → P ∣ adBody a xB yB zB cCol cB pl sy sc m) :
    M ∣ (sVal a xB + sy * sVal a yB - sVal a zB) := by
  -- Step 1: each body FITS a felt, so `P ∣ body` forces `body = 0` over ℤ.
  have hzero : ∀ m, m < NA → adBody a xB yB zB cCol cB pl sy sc m = 0 := by
    intro m hm
    have hlt := adBody_abs_lt_P a xB yB zB cCol cB pl sy sc m hsy hsc hx hy hz hpl hcb hc
    rcases hgates m hm with ⟨t, ht⟩
    by_contra hne
    have ht0 : t ≠ 0 := by rintro rfl; rw [mul_zero] at ht; exact hne ht
    have hP0 : (0 : ℤ) < P := by norm_num [Dregg2.Circuit.Emit.EffectLower.P]
    have h1 : (1 : ℤ) ≤ |t| := by
      rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    have : P ≤ |adBody a xB yB zB cCol cB pl sy sc m| := by
      rw [ht, abs_mul, abs_of_nonneg (le_of_lt hP0)]
      nlinarith
    linarith
  -- Step 2: the chain telescopes; both ends are pinned by construction.
  have hchain : ∀ m, adChain a cB m + adDigit a xB yB zB cCol pl sy sc m
      = (2 : ℤ) ^ SB * adChain a cB (m + 1) := by
    intro m
    by_cases hm : m < NA
    · have := hzero m hm; unfold adBody at this; linarith
    · have hNA : NA = 32 := rfl
      have hSK : SK = 32 := rfl
      have h1 : adChain a cB m = 0 := by
        unfold adChain; rw [if_neg (by omega), if_neg (by omega)]
      have h2 : adChain a cB (m + 1) = 0 := by
        unfold adChain; rw [if_neg (by omega), if_neg (by omega)]
      have h3 : adDigit a xB yB zB cCol pl sy sc m = 0 := by
        unfold adDigit; rw [if_neg (by omega)]
      rw [h1, h2, h3]; ring
  have htel := telescope ((2 : ℤ) ^ SB) (adDigit a xB yB zB cCol pl sy sc) (adChain a cB) hchain NA
  rw [adChain_top, adChain_zero, mul_zero, sub_zero] at htel
  -- Step 3: that recomposition IS `X + sy·Y − Z + sc·c·M`.
  rw [ad_recompose a xB yB zB cCol pl sy sc M hplM] at htel
  exact ⟨-(sc * a cCol), by linear_combination htel⟩

/-! ## §5 — THE EMITTED AIR, through the compiler (`EffectLower.lowerAir` of an `EffectAir`).

House Law #1 in its endpoint form: the four descriptors below are not hand-written `VmConstraint2`
lists, they are `lowerAir` of a source `EffectAir`. The range legs go through `LimbsLeg`, whose
`mainRailOk` REFUSES a width `≥ 30`. -/

open Dregg2.Circuit (Expr Constraint ConstraintSystem)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 TableDef TableId mainTableDef VmConstraint2)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LimbsLeg)
open Dregg2.Circuit.Emit.EffectLower (lowerAir)

theorem rangeTid_w1 : rangeTidW CBITS = TableId.custom 65 := rfl

/-- The digit expression at index `m`. `sy` is a gate CONSTANT and `sc * pl m` is a gate CONSTANT,
so this leg is linear in the trace: **zero var×var products in the whole descriptor.** -/
def adDigitExpr (xB yB zB cCol : Nat) (pl : Nat → ℤ) (sy sc : ℤ) (m : Nat) : Expr :=
  if m < SK then
    .add (.add (.add (.var (xB + m)) (.mul (.const sy) (.var (yB + m))))
               (.mul (.const (-1)) (.var (zB + m))))
         (.mul (.const (sc * pl m)) (.var cCol))
  else .const 0

/-- The carry term at index `m` — `.const 0` at both ends, which is how the chain is pinned closed
without a boundary gate. -/
def adChainExpr (cB m : Nat) : Expr :=
  if m = 0 then .const 0
  else if m ≤ NA - 1 then .add (.var (cB + m - 1)) (.const (-ACOFF))
  else .const 0

/-- **The coefficient gate expression at index `m`.** -/
def adExpr (xB yB zB cCol cB : Nat) (pl : Nat → ℤ) (sy sc : ℤ) (m : Nat) : Expr :=
  .add (adDigitExpr xB yB zB cCol pl sy sc m)
       (.add (adChainExpr cB m) (.mul (.const (-((2 : ℤ) ^ SB))) (adChainExpr cB (m + 1))))

theorem adChainExpr_eval (a : Assignment) (cB m : Nat) :
    (adChainExpr cB m).eval a = adChain a cB m := by
  unfold adChainExpr adChain
  by_cases h0 : m = 0
  · simp [h0, Expr.eval]
  by_cases h1 : m ≤ NA - 1
  · simp [h0, h1, Expr.eval, sub_eq_add_neg]
  · simp [h0, h1, Expr.eval]

/-- ⚑ **THE BRIDGE.** The emitted gate expression evaluates to exactly the body the soundness
theorem quantifies over. Without this the theorem would be about a different object than the one the
descriptor carries. -/
theorem adExpr_eval (a : Assignment) (xB yB zB cCol cB : Nat) (pl : Nat → ℤ) (sy sc : ℤ) (m : Nat) :
    (adExpr xB yB zB cCol cB pl sy sc m).eval a = adBody a xB yB zB cCol cB pl sy sc m := by
  unfold adExpr adBody adDigitExpr adDigit
  by_cases h : m < SK
  · simp only [if_pos h, Expr.eval, adChainExpr_eval]; ring
  · simp only [if_neg h, Expr.eval, adChainExpr_eval]; ring

/-! ### The one-operation layout (the measurement unit and the falsifier target). -/

def AX_BASE : Nat := 0
def AY_BASE : Nat := SK
def AZ_BASE : Nat := 2 * SK
/-- The single carry/borrow witness column — index `96`, lookup-pinned to one bit. -/
def AC_COL : Nat := 3 * SK
/-- The `NA − 1 = 31` carry columns start at `97`. -/
def ACAR_BASE : Nat := 3 * SK + 1
/-- `3·32 + 1 + 31 = 128` main columns — **62 fewer than the sound multiply's 190**, because there
is no quotient block. -/
def ADDSUB_WIDTH : Nat := 3 * SK + 1 + (NA - 1)

theorem ADDSUB_WIDTH_eq : ADDSUB_WIDTH = 128 := rfl

/-- The `NA − 1` carry columns at `cB`. -/
def acarryCols (cB : Nat) : List Nat := (List.range (NA - 1)).map (cB + ·)

/-- **The source AIR of one sound Pasta add/sub**, parametric in the limb vector `pl` (which field)
and the sign pair `(sy, sc)` (add or sub). -/
def soundAddSubAir (pl : Nat → ℤ) (sy sc : ℤ) : EffectAir :=
  { tables := [ mainTableDef ADDSUB_WIDTH
              , ⟨rangeTidW SB, "range_w8", 1, .rangeLimb SB⟩
              , ⟨rangeTidW CBITS, "range_w1", 1, .rangeLimb CBITS⟩ ]
  , legs := (List.range NA).map
              (fun m => AirLeg.gate
                ⟨adExpr AX_BASE AY_BASE AZ_BASE AC_COL ACAR_BASE pl sy sc m, .const 0⟩)
            ++ [ AirLeg.limbs ⟨limbCols AX_BASE, SB, rangeTidW SB⟩
               , AirLeg.limbs ⟨limbCols AY_BASE, SB, rangeTidW SB⟩
               , AirLeg.limbs ⟨limbCols AZ_BASE, SB, rangeTidW SB⟩
               , AirLeg.limbs ⟨[AC_COL], CBITS, rangeTidW CBITS⟩
               , AirLeg.limbs ⟨acarryCols ACAR_BASE, ACB, rangeTidW SB⟩ ] }

/-- ⚑ **The compiler ACCEPTS this block** — every leg has a deployed main-rail image, which for the
five `limbs` legs is exactly the `0 < bits ≤ 29` verdict. A width of 30 would emit
`refuseConstraints` instead, and this theorem would be false. -/
theorem soundAddSubAir_mainRailOk (pl : Nat → ℤ) (sy sc : ℤ) :
    (soundAddSubAir pl sy sc).mainRailOk = true := by
  unfold soundAddSubAir EffectAir.mainRailOk
  simp only [List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true]
  refine ⟨?_, by decide⟩
  intro m _
  rfl

/-- `fpAdd`: `x + y ≡ z (mod p)` (Pallas base / Vesta scalar). -/
def fpAddSoundDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-pasta-fpadd-sound::v1" ADDSUB_WIDTH 0 [] (soundAddSubAir pLimb 1 (-1))
/-- `fpSub`: `x − y ≡ z (mod p)`. -/
def fpSubSoundDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-pasta-fpsub-sound::v1" ADDSUB_WIDTH 0 [] (soundAddSubAir pLimb (-1) 1)
/-- `fqAdd`: the same shape at the Vesta-base / Pallas-scalar modulus. -/
def fqAddSoundDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-pasta-fqadd-sound::v1" ADDSUB_WIDTH 0 [] (soundAddSubAir qLimb 1 (-1))
/-- `fqSub`. -/
def fqSubSoundDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-pasta-fqsub-sound::v1" ADDSUB_WIDTH 0 [] (soundAddSubAir qLimb (-1) 1)

/-- ⚑ **THE EMITTED COST, as a theorem rather than a caption.** `32` coefficient gates + `3·32`
limb lookups + `1` carry-bit lookup + `31` carry lookups = **`160`** constraints for a standalone
add/sub (`64` when the two operands are already range-checked by whatever produced them). The
emitted `9×30` gate was **1**, and `PastaField` §Constraint-budget's own estimate for the full
generator was `281`. -/
theorem fpAddSoundDesc_constraint_count : fpAddSoundDesc.constraints.length = 160 := by
  unfold fpAddSoundDesc lowerAir Dregg2.Circuit.Emit.EffectLower.assemble
  simp only [List.map_nil, List.nil_append, List.append_nil]
  rfl

theorem fpSubSoundDesc_constraint_count : fpSubSoundDesc.constraints.length = 160 := by
  unfold fpSubSoundDesc lowerAir Dregg2.Circuit.Emit.EffectLower.assemble
  simp only [List.map_nil, List.nil_append, List.append_nil]
  rfl

theorem fqAddSoundDesc_constraint_count : fqAddSoundDesc.constraints.length = 160 := by
  unfold fqAddSoundDesc lowerAir Dregg2.Circuit.Emit.EffectLower.assemble
  simp only [List.map_nil, List.nil_append, List.append_nil]
  rfl

theorem fqSubSoundDesc_constraint_count : fqSubSoundDesc.constraints.length = 160 := by
  unfold fqSubSoundDesc lowerAir Dregg2.Circuit.Emit.EffectLower.assemble
  simp only [List.map_nil, List.nil_append, List.append_nil]
  rfl

/-! ## §6 — the descriptors' gates force the Pasta congruences AT `p_felt`. -/

/-- ⚑ **THE REPAIR, STATED AT THE EMITTED `fpAdd` OBJECT.** Hypotheses: the DEPLOYED row denotation
of every emitted coefficient gate (`P ∣ body` — what `prove_vm_descriptor2` checks) plus the range
facts the five emitted `limbs` legs supply. Conclusion: `x + y ≡ z (mod p)`. -/
theorem fpAddSound_forces (a : Assignment)
    (hx : ∀ i, i < SK → 0 ≤ a (AX_BASE + i) ∧ a (AX_BASE + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (AY_BASE + i) ∧ a (AY_BASE + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ a (AZ_BASE + i) ∧ a (AZ_BASE + i) < 2 ^ SB)
    (hcb : 0 ≤ a AC_COL ∧ a AC_COL < 2)
    (hc : ∀ i, i < NA - 1 → 0 ≤ a (ACAR_BASE + i) ∧ a (ACAR_BASE + i) < 2 ^ ACB)
    (hgates : ∀ m, m < NA →
      P ∣ (adExpr AX_BASE AY_BASE AZ_BASE AC_COL ACAR_BASE pLimb 1 (-1) m).eval a) :
    (pN : ℤ) ∣ (sVal a AX_BASE + sVal a AY_BASE - sVal a AZ_BASE) := by
  have h := addsub_gates_force_congruence a AX_BASE AY_BASE AZ_BASE AC_COL ACAR_BASE pLimb
    1 (-1) (pN : ℤ) (Or.inl rfl) (Or.inr rfl) hx hy hz pLimb_bounds pLimb_recomposes hcb hc
    (fun m hm => by rw [← adExpr_eval]; exact hgates m hm)
  simpa using h

/-- The same at `fpSub`: `x − y ≡ z (mod p)`. -/
theorem fpSubSound_forces (a : Assignment)
    (hx : ∀ i, i < SK → 0 ≤ a (AX_BASE + i) ∧ a (AX_BASE + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (AY_BASE + i) ∧ a (AY_BASE + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ a (AZ_BASE + i) ∧ a (AZ_BASE + i) < 2 ^ SB)
    (hcb : 0 ≤ a AC_COL ∧ a AC_COL < 2)
    (hc : ∀ i, i < NA - 1 → 0 ≤ a (ACAR_BASE + i) ∧ a (ACAR_BASE + i) < 2 ^ ACB)
    (hgates : ∀ m, m < NA →
      P ∣ (adExpr AX_BASE AY_BASE AZ_BASE AC_COL ACAR_BASE pLimb (-1) 1 m).eval a) :
    (pN : ℤ) ∣ (sVal a AX_BASE - sVal a AY_BASE - sVal a AZ_BASE) := by
  have h := addsub_gates_force_congruence a AX_BASE AY_BASE AZ_BASE AC_COL ACAR_BASE pLimb
    (-1) 1 (pN : ℤ) (Or.inr rfl) (Or.inl rfl) hx hy hz pLimb_bounds pLimb_recomposes hcb hc
    (fun m hm => by rw [← adExpr_eval]; exact hgates m hm)
  simpa [sub_eq_add_neg] using h

/-- `fqAdd`: `x + y ≡ z (mod q)`. -/
theorem fqAddSound_forces (a : Assignment)
    (hx : ∀ i, i < SK → 0 ≤ a (AX_BASE + i) ∧ a (AX_BASE + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (AY_BASE + i) ∧ a (AY_BASE + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ a (AZ_BASE + i) ∧ a (AZ_BASE + i) < 2 ^ SB)
    (hcb : 0 ≤ a AC_COL ∧ a AC_COL < 2)
    (hc : ∀ i, i < NA - 1 → 0 ≤ a (ACAR_BASE + i) ∧ a (ACAR_BASE + i) < 2 ^ ACB)
    (hgates : ∀ m, m < NA →
      P ∣ (adExpr AX_BASE AY_BASE AZ_BASE AC_COL ACAR_BASE qLimb 1 (-1) m).eval a) :
    (qN : ℤ) ∣ (sVal a AX_BASE + sVal a AY_BASE - sVal a AZ_BASE) := by
  have h := addsub_gates_force_congruence a AX_BASE AY_BASE AZ_BASE AC_COL ACAR_BASE qLimb
    1 (-1) (qN : ℤ) (Or.inl rfl) (Or.inr rfl) hx hy hz qLimb_bounds qLimb_recomposes hcb hc
    (fun m hm => by rw [← adExpr_eval]; exact hgates m hm)
  simpa using h

/-- `fqSub`: `x − y ≡ z (mod q)`. -/
theorem fqSubSound_forces (a : Assignment)
    (hx : ∀ i, i < SK → 0 ≤ a (AX_BASE + i) ∧ a (AX_BASE + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (AY_BASE + i) ∧ a (AY_BASE + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ a (AZ_BASE + i) ∧ a (AZ_BASE + i) < 2 ^ SB)
    (hcb : 0 ≤ a AC_COL ∧ a AC_COL < 2)
    (hc : ∀ i, i < NA - 1 → 0 ≤ a (ACAR_BASE + i) ∧ a (ACAR_BASE + i) < 2 ^ ACB)
    (hgates : ∀ m, m < NA →
      P ∣ (adExpr AX_BASE AY_BASE AZ_BASE AC_COL ACAR_BASE qLimb (-1) 1 m).eval a) :
    (qN : ℤ) ∣ (sVal a AX_BASE - sVal a AY_BASE - sVal a AZ_BASE) := by
  have h := addsub_gates_force_congruence a AX_BASE AY_BASE AZ_BASE AC_COL ACAR_BASE qLimb
    (-1) 1 (qN : ℤ) (Or.inr rfl) (Or.inl rfl) hx hy hz qLimb_bounds qLimb_recomposes hcb hc
    (fun m hm => by rw [← adExpr_eval]; exact hgates m hm)
  simpa [sub_eq_add_neg] using h

/-! ## §7 — the HONEST witnesses, generated here (Rust fills cells, it does not author them). -/

/-- The limb block plus the carry bit of an honest `(x, y, z, c)` — columns `0..96`. -/
def adLimbs (Xv Yv Zv : Nat) (cv : ℤ) : Assignment := fun col =>
  if col < SK then limbAt Xv col
  else if col < 2 * SK then limbAt Yv (col - SK)
  else if col < 3 * SK then limbAt Zv (col - 2 * SK)
  else if col = AC_COL then cv
  else 0

/-- The carry chain of the honest witness: `S 0 = 0`, `S (m+1) = (S m + T m) / 2^SB`. Every division
is exact BECAUSE the integer body is zero — that is the content, not a convenience. -/
def adCarryOf (Xv Yv Zv : Nat) (cv : ℤ) (pl : Nat → ℤ) (sy sc : ℤ) : Nat → ℤ
  | 0 => 0
  | (m + 1) =>
      (adCarryOf Xv Yv Zv cv pl sy sc m
        + adDigit (adLimbs Xv Yv Zv cv) AX_BASE AY_BASE AZ_BASE AC_COL pl sy sc m) / (2 : ℤ) ^ SB

/-- The full honest assignment: limbs, the carry bit, then the offset carries at `ACAR_BASE`. -/
def adAsg (Xv Yv Zv : Nat) (cv : ℤ) (pl : Nat → ℤ) (sy sc : ℤ) : Assignment := fun col =>
  if col ≤ AC_COL then adLimbs Xv Yv Zv cv col
  else if col < ADDSUB_WIDTH then adCarryOf Xv Yv Zv cv pl sy sc (col - ACAR_BASE + 1) + ACOFF
  else 0

/-- The honest `fpAdd` witness at the OVERFLOW boundary: `(p−1) + (p−1) = p−2` with carry `1`, so
the `−p·c` leg is exercised rather than sitting at zero (which is what the `Ref.X + Ref.Y` operands
would have given). -/
def fpAddHonest : Assignment :=
  adAsg (pN - 1) (pN - 1) (PastaField.Ref.fpAdd (pN - 1) (pN - 1)) 1 pLimb 1 (-1)

/-- The honest `fpSub` witness with a BORROW: `Y − X` where `Y < X`, so `c = 1`. -/
def fpSubHonest : Assignment :=
  adAsg PastaField.Ref.Y PastaField.Ref.X
    (PastaField.Ref.fpSub PastaField.Ref.Y PastaField.Ref.X) 1 pLimb (-1) 1

/-- ⚑ **THE HONEST ADD POLARITY, as a named theorem.** Every one of the 32 emitted gate bodies is
EXACTLY zero over ℤ on the generated witness — a fortiori zero mod `P`, so the deployed prover
accepts it. (`decide`, kernel-reduced; no `native_decide`.) -/
theorem fpAddHonest_satisfies_gates :
    ((List.range NA).all fun m =>
      decide (adBody fpAddHonest AX_BASE AY_BASE AZ_BASE AC_COL ACAR_BASE pLimb 1 (-1) m = 0))
      = true := by
  decide

/-- …and the SUB polarity, with the borrow set. -/
theorem fpSubHonest_satisfies_gates :
    ((List.range NA).all fun m =>
      decide (adBody fpSubHonest AX_BASE AY_BASE AZ_BASE AC_COL ACAR_BASE pLimb (-1) 1 m = 0))
      = true := by
  decide

/-- ⚑ **AND THE RANGES BITE ON THEM** — every carry column lands inside the declared 8-bit table and
the carry bit inside the 1-bit one, so the honest witnesses are not merely gate-satisfying but
LOOKUP-satisfying. A witness that needed a 9-bit carry would prove nothing here and
`adBody_abs_lt_P` would be about a shape the prover cannot carry. -/
theorem fpAddHonest_carries_in_range :
    ((List.range (NA - 1)).all fun i =>
      decide (0 ≤ fpAddHonest (ACAR_BASE + i) ∧ fpAddHonest (ACAR_BASE + i) < 2 ^ ACB)) = true := by
  decide

theorem fpSubHonest_carries_in_range :
    ((List.range (NA - 1)).all fun i =>
      decide (0 ≤ fpSubHonest (ACAR_BASE + i) ∧ fpSubHonest (ACAR_BASE + i) < 2 ^ ACB)) = true := by
  decide

theorem fpAddHonest_carry_bit : fpAddHonest AC_COL = 1 := by decide
theorem fpSubHonest_borrow_bit : fpSubHonest AC_COL = 1 := by decide

/-- ⚑ **AND THE FALSIFIER IS REFUSED.** The deployed `9×30` add/sub forgery moves two `z` limbs so
the body's change `−(δ₀ + 2^240·δ₈)` is a nonzero multiple of `P` — invisible. Here the analogous
move is dead twice over: the limbs are lookup-pinned to `[0, 2^8)` so the compensating `δ₀` does not
exist, and the smallest possible tamper — `+1` on `z` limb 0 — moves gate 0's body by `−1`, whose
absolute value is `1 < P`, so it CANNOT vanish mod `P`. This exhibits that at `d = 1`. -/
theorem fpAddHonest_z_bump_is_caught :
    adBody (fun c => if c = AZ_BASE then fpAddHonest c + 1 else fpAddHonest c)
      AX_BASE AY_BASE AZ_BASE AC_COL ACAR_BASE pLimb 1 (-1) 0 ≠ 0 := by
  decide

theorem fpSubHonest_z_bump_is_caught :
    adBody (fun c => if c = AZ_BASE then fpSubHonest c + 1 else fpSubHonest c)
      AX_BASE AY_BASE AZ_BASE AC_COL ACAR_BASE pLimb (-1) 1 0 ≠ 0 := by
  decide

/-- ⚑ **AND SO IS A CARRY-BIT FLIP.** At `9×30` the carry column entered with coefficient `±p`, a
unit mod `P`, and was the one column unique to its gate — but a single-column move by `d` changes
the body by `∓p·d`, which vanishes mod `P` only when `P ∣ d`, so the `9×30` forgery needed a
COMPENSATING `z` limb. Here `p₀ = 1` and the body moves by `∓1`, and there is no compensator inside
`[0, 2^8)`. -/
theorem fpAddHonest_carry_flip_is_caught :
    adBody (fun c => if c = AC_COL then fpAddHonest c - 1 else fpAddHonest c)
      AX_BASE AY_BASE AZ_BASE AC_COL ACAR_BASE pLimb 1 (-1) 0 ≠ 0 := by
  decide

#assert_axioms fpAddHonest_satisfies_gates
#assert_axioms fpSubHonest_satisfies_gates
#assert_axioms fpAddHonest_carries_in_range
#assert_axioms fpSubHonest_carries_in_range
#assert_axioms fpAddHonest_z_bump_is_caught
#assert_axioms fpSubHonest_z_bump_is_caught
#assert_axioms fpAddHonest_carry_flip_is_caught

/-- The `fpAdd` honest row, as the emit driver renders it. -/
def fpAddHonestRow : List ℤ := (List.range ADDSUB_WIDTH).map fpAddHonest
/-- The `fpSub` honest row. -/
def fpSubHonestRow : List ℤ := (List.range ADDSUB_WIDTH).map fpSubHonest

/-- ⚑ Every emitted cell is a CANONICAL BabyBear felt (`0 ≤ v < P`) — so the Rust fixture parses as
`u32` and no cell is silently folded on the way in. -/
theorem fpAddHonestRow_canonical : (fpAddHonestRow.all fun v => decide (0 ≤ v ∧ v < P)) = true := by
  decide

theorem fpSubHonestRow_canonical : (fpSubHonestRow.all fun v => decide (0 ≤ v ∧ v < P)) = true := by
  decide

#assert_axioms fpAddHonestRow_canonical
#assert_axioms fpSubHonestRow_canonical

#assert_axioms ad_recompose
#assert_axioms adDigit_abs_le
#assert_axioms adBody_abs_lt_P
#assert_axioms addsub_gates_force_congruence
#assert_axioms adExpr_eval
#assert_axioms soundAddSubAir_mainRailOk
#assert_axioms fpAddSoundDesc_constraint_count
#assert_axioms fpAddSound_forces
#assert_axioms fpSubSound_forces
#assert_axioms fqAddSound_forces
#assert_axioms fqSubSound_forces
#assert_axioms acb_wrapfree
#assert_axioms cbit_wrapfree

end Dregg2.Circuit.Emit.PastaAddSubSound
