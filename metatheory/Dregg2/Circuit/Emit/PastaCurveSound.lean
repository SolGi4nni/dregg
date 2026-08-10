/-
# `Dregg2.Circuit.Emit.PastaCurveSound` — the RCB complete addition ON THE SOUND FIELD CORES, and
the TYPE BRIDGE that made it sayable.

## ⚑ THE OBSTRUCTION, and why it was a type fact and not a cost

`MinaWrapXiScalarWeld.lean:238-242` recorded the blocker:

> *"The blocker is a TYPE obstruction and not a cost: `swCompleteAddGadget` takes gate CONSTRUCTORS
> while `PastaFieldSound`/`PastaAddSubSound` are `EffectAir`s lowered through `EffectLower.lowerAir`,
> so no sound complete-add and no sound `smul` core exist in this tree at all."*

The two types, read at source:

* `PastaCurveComplete.swCompleteAddGadget` (`:267-269`) is parametric over
  `mulC addC subC : Nat → Nat → Nat → Nat → VmConstraint2` — **four column bases to ONE
  constraint** — and returns `List VmConstraint2 × (Nat × Nat × Nat) × Nat`.
* `PastaFieldSound.soundMulAir` (`:637`) is an `EffectAir` — `⟨tables, legs, ranges, extraPi⟩`,
  `EffectAirIR.lean:275` — whose `legs` are `63 × AirLeg.gate` **plus five `AirLeg.limbs`**, and it
  becomes a descriptor only through `EffectLower.lowerAir` (`EffectLowerCore.lean:437`).

⚑ **The mismatch is THREE things, and only the first is arity.**

1. **Arity.** A sound multiply is 68 legs, not one constraint. There is no injection
   `List AirLeg → VmConstraint2`.
2. **KIND, and this is the one that matters.** Five of those legs are `AirLeg.limbs` — range
   LOOKUPS against a table the AIR must *declare*. `lowerLimbsLeg` emits `.lookup ⟨l.table, …⟩`
   (`EffectLowerCore.lean:319`), and the `TableDef` it queries lives in `EffectAir.tables`, a field
   the gadget's return type **has no channel for**: `pallasCompleteAddDesc` (`PastaCurveComplete
   .lean:596`) carries `tables := []`. So even a widened `… → List VmConstraint2` would emit
   lookups against nothing.
3. **And the lookups are LOAD-BEARING, not plumbing.** `felt_gates_force_congruence` takes
   `hx hy hz hq hc` — the byte-ranges — as HYPOTHESES; they are what makes `|body| < P`, which is
   the whole repair. Dropping them to fit `VmConstraint2` drops the SOUNDNESS, not the packaging.
   `fpMulCore` needs no lookups precisely because it forces nothing.

A fourth, quieter one: `swCompleteAddGadget`'s layout arithmetic is **baked to the unsound
encoding** — `fresh + 9·idx`, nine-limb quotient groups, one-column carries. The sound encoding is
32 limbs per value, a 32-limb quotient plus 62 carries per multiply.

## ⚑ THE BUILDABLE DIRECTION — a `SoundCore`, not a constructor and not an `EffectAir`

Neither of the two shapes the weld guessed at is the one that works.

* *A constructor that emits the sound descriptor's constraint block* (`… → List VmConstraint2`)
  loses the table channel — obstruction (2).
* *An `EffectAir` formulation of each op* would be 33 descriptors, not one row; `EffectAir` carries
  a `mainTableDef` width and a lowering, and 33 of them do not compose into a row.

What composes is the **leg block**: the core's return type widens from `VmConstraint2` to
`List AirLeg`, the op's private witness columns become a block whose width the core DECLARES, and
the *gadget* returns the legs; the table declarations are hoisted to the composed AIR and
`lowerAir` runs **once**, at the end. That is `SoundCore` (§2) and `swCompleteAddSoundAir` (§4).

## ⚑ WHAT WAS MISSING ENTIRELY: the `smul` core

RCB Algorithm 7 multiplies by the constant `b3 = 3b = 15` twice, and **no sound constant-multiply
existed** — `PastaMsmBucketed.lean:1206-1208` says so and prices the two ops at the full multiply's
shape *by assumption*. §3 builds it. A constant-multiply is LINEAR: the quotient of `cx·x` by the
modulus is a SINGLE column, not a 32-limb block, so the core is add/sub-shaped (32 gates, 31
carries) and not multiply-shaped (63 gates, 62 carries). That assumption was an over-estimate of
**93 constraints and 62 columns per constant-multiply**, and §6 measures the corrected figure.

## ⚑ WHY THE SCHOOLBOOK AND NOT SCHWARTZ–ZIPPEL — updated 2026-08-09: the hole is CLOSED, the
adoption is now a real (and separate) pass

`PastaSzMul` collapses a multiply's 63 algebraic gates to 2 (its two-point form; batched, to one
gate for `N` multiplies) at identical columns and lookups. When this file was written it could not
build on it, for a reason that was a MISSING THEOREM rather than a preference: `PastaSzMul` credited
itself with the polynomial-identity ⟹ integer-congruence step (`szPoly_forces_congruence`) and
`git grep` found exactly one occurrence — the credit. **That phantom is closed**: as of 2026-08-09
`PastaSzMul.szPoly_forces_congruence` exists, is stated base- and modulus-parametric on the
faithful carrier (`ChalExpr.evalIn` / `ChalConstraint.holdsIn`, the deployed `assert_zero_ext`
reading), discharges into the same `felt_gates_force_congruence` this file's cores use as their
terminal lemma, and is `#assert_axioms`-clean — together with the emitted-gate welds
(`szBodyAt_evalIn`, `fpSzMulDesc_carries_the_gates`) and the ε ledger (`2^−117.7` per check,
`2^−98.5` single-gate wrap-union — below the bar, hence two gates — `2^−197.0` two-point).

So the reason THIS file still carries schoolbook multiply cores is no longer a hole; it is
sequencing. Adopting sz here means swapping each multiply core's 63 gate legs for two relocated
challenge gates (`szBodyAt` at the core's bases) and restating the composed `_forces` theorems with
`holdsIn`-at-a-draw hypotheses plus a per-row non-exceptionality disjunction — a statement-shape
change for the whole row, not a leg splice, and it rides `DescriptorIR2.chalIndicesDistinctOk` for
the two draws. `felt_gates_force_congruence` stays the terminal lemma either way, so the adoption
is a swap of which certified body feeds it. §7 prices the SZ row; the swap is the named follow-on,
now unblocked.

## What is proved here

* `smul_gates_force_congruence` — the new core, from the mod-`P` reading the prover performs.
* `pallasCompleteAddSound_forces` / `vestaCompleteAddSound_forces` — the 33 leg blocks' DEPLOYED
  satisfaction forces `(X3,Y3,Z3) ≡ rcbTraceZ(P,Q)` mod the real prime. Same `CZm` chain as
  `PastaCurveComplete`'s, over `sVal` instead of `fpVal`.
* The emitted counts, as theorems on the lowered descriptors.
* `pallasCompleteAddSoundDesc_all_forced` — every row gate has a forced ℤ meaning, by
  `PastaConeCensus.unforcedGates`, against the unsound row's `33 of 33`.

## Axiom hygiene

`#assert_axioms`-clean; no `sorry`/`admit`/`native_decide`; zero `#guard`s.
-/
import Dregg2.Circuit.Emit.PastaAddSubSound
import Dregg2.Circuit.Emit.PastaCurveComplete
import Dregg2.Circuit.Emit.EffectLowerCertified
-- ⚑ §10: the certified Schwartz–Zippel multiply body, relocated into this row.
import Dregg2.Circuit.Emit.PastaSzMul

namespace Dregg2.Circuit.Emit.PastaCurveSound

open Dregg2.Circuit (Assignment Expr Constraint)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 TableDef TableId mainTableDef VmConstraint2)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LimbsLeg)
open Dregg2.Circuit.Emit.EffectLower (lowerAir P)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaFieldSound
open Dregg2.Circuit.Emit.PastaAddSubSound
open Dregg2.Circuit.Emit.PastaCurve (CZm CZp CZq)
open Dregg2.Circuit.Emit.PastaCurveComplete (curveB3 RcbT rcbTraceZ)

set_option autoImplicit false
set_option maxRecDepth 40000

/-! ## §1 — the ranged-block predicate, so 39 limb blocks are one word rather than 39. -/

/-- **A value block is byte-ranged.** This is exactly the hypothesis shape
`felt_gates_force_congruence` and `addsub_gates_force_congruence` take, named once so the composed
statement can quantify over blocks instead of listing them. -/
def Ranged (a : Assignment) (b : Nat) : Prop := ∀ i, i < SK → 0 ≤ a (b + i) ∧ a (b + i) < 2 ^ SB

/-- A witness block of `n` columns is ranged at width `w`. -/
def RangedAt (a : Assignment) (b n w : Nat) : Prop :=
  ∀ i, i < n → 0 ≤ a (b + i) ∧ a (b + i) < 2 ^ w

/-! ## §2 — ⚑ THE BRIDGE TYPE.

A sound field core is a **leg block plus a private-witness width**. The width is what lets a caller
allocate; the legs are what `lowerAir` consumes. Compare `swCompleteAddGadget`'s
`Nat → Nat → Nat → Nat → VmConstraint2` (`PastaCurveComplete.lean:267`): same four bases, and the
fourth is still "where the op's own witness lives" — what changes is that the return type can now
hold a range lookup and the core can say how wide its witness is. -/

/-- ⚑ **A SOUND FIELD CORE.** `legs xB yB zB wB` is the op's whole AIR block: its coefficient gates,
the range lookup on its RESULT block, and the range lookups on its private witness at `wB`. `width`
is how many columns that witness occupies. -/
structure SoundCore where
  /-- The op's legs: operand bases `xB`, `yB`, result base `zB`, private-witness base `wB`. -/
  legs  : Nat → Nat → Nat → Nat → List AirLeg
  /-- Columns the private witness block at `wB` occupies. -/
  width : Nat

/-! ### The two cores that already exist, wrapped.

⚑ **The result block's range lookup rides with the op that PRODUCES it**, not with the ops that
consume it. That is the whole accounting rule: 33 intermediates, 33 producing ops, one lookup each —
so `hz` for op `i` and `hx`/`hy` for its consumers are the SAME 32 lookups, counted once. The six
INPUT blocks have no producer and are ranged by the gadget (§4). -/

/-- ⚑ **The sound multiply as a `SoundCore`.** Witness block: 32 quotient limbs at `wB`, then the
62 carries at `wB + SK`. `94` columns. Legs: the 63 coefficient gates of `soundMulAir` relocated to
`(xB, yB, zB, wB, wB+SK)`, plus the result, quotient and carry lookups. -/
def mulCore (pl : Nat → ℤ) : SoundCore :=
  { legs := fun xB yB zB wB =>
      (List.range NG).map (fun m => AirLeg.gate ⟨coefExpr xB yB zB wB (wB + SK) pl m, .const 0⟩)
      ++ [ AirLeg.limbs ⟨limbCols zB, SB, rangeTidW SB⟩
         , AirLeg.limbs ⟨limbCols wB, SB, rangeTidW SB⟩
         , AirLeg.limbs ⟨carryCols (wB + SK), CB, rangeTidW CB⟩ ]
  , width := SK + (NG - 1) }

/-- ⚑ **The sound add/sub as a `SoundCore`**, `sy`/`sc` selecting the polarity exactly as
`soundAddSubAir` does. Witness block: the one-bit carry/borrow at `wB`, then 31 carries at
`wB + 1`. `32` columns. -/
def addSubCore (pl : Nat → ℤ) (sy sc : ℤ) : SoundCore :=
  { legs := fun xB yB zB wB =>
      (List.range NA).map
        (fun m => AirLeg.gate ⟨adExpr xB yB zB wB (wB + 1) pl sy sc m, .const 0⟩)
      ++ [ AirLeg.limbs ⟨limbCols zB, SB, rangeTidW SB⟩
         , AirLeg.limbs ⟨[wB], CBITS, rangeTidW CBITS⟩
         , AirLeg.limbs ⟨acarryCols (wB + 1), ACB, rangeTidW SB⟩ ]
  , width := 1 + (NA - 1) }

/-! ## §3 — ⚑ THE CORE THAT DID NOT EXIST: a sound CONSTANT multiply.

`PastaMsmBucketed.lean:1206-1208`: *"no sound `smul` core exists at all, so the 2 constant-multiplies
are priced at the full multiply's shape by assumption. That is an over-estimate of unknown size, and
it is an ASSUMPTION, not a measurement."* This is the measurement.

`cx · x ≡ z (mod M)` with `cx` a gate CONSTANT is LINEAR — the reduction quotient
`q = (cx·x − z)/M` is bounded by `cx`, so it is **one column**, not a 32-limb block, and the identity
needs `SK = 32` coefficient gates rather than `2·SK − 1 = 63`:

    cx·x_m  −  z_m  −  p_m·q  +  S_m  −  2^8·S_(m+1)  =  0        (m < 32)

⚑ **Its bound is its own, recomputed and not inherited** (the lesson `PastaAddSubSound` §"The
encoding, and ITS OWN BOUND" spends a paragraph on). With `cx` and `q` both bytes,

    (2^8−1)² + (2^8−1) + (2^8−1)² + COFF + 2^8·COFF  =  65 025 + 255 + 65 025 + 32 768 + 8 388 608
                                                     =  **8 551 681**  <  P

— 0.42% of the field. The carries are 16-bit at offset `2^15`, the SAME table `PastaFieldSound`
already declares, because the digit reaches `2^17` where add/sub's reached `2^10`: an 8-bit carry
would NOT hold this chain, and reusing add/sub's `ACB = 8` here would have been the inherited-bound
mistake one file over. -/

/-- The `m`-th digit of the const-multiply body `cx·x − z − M·q`. -/
def smDigit (a : Assignment) (xB zB qCol : Nat) (pl : Nat → ℤ) (cx : ℤ) (m : Nat) : ℤ :=
  if m < SK then cx * a (xB + m) - a (zB + m) - pl m * a qCol else 0

/-- The carry chain: `S 0 = 0`, `S m = a(cB + m − 1) − COFF` for `1 ≤ m ≤ SK − 1`, `S SK = 0`.
⚑ Both ends are pinned closed BY CONSTRUCTION — there is no column for either — so no boundary
gate and no end pin is needed. -/
def smChain (a : Assignment) (cB m : Nat) : ℤ :=
  if m = 0 then 0 else if m ≤ SK - 1 then a (cB + m - 1) - COFF else 0

theorem smChain_zero (a : Assignment) (cB : Nat) : smChain a cB 0 = 0 := rfl

theorem smChain_top (a : Assignment) (cB : Nat) : smChain a cB SK = 0 := by
  unfold smChain SK; norm_num

/-- The gate body at index `m`. -/
def smBody (a : Assignment) (xB zB qCol cB : Nat) (pl : Nat → ℤ) (cx : ℤ) (m : Nat) : ℤ :=
  smDigit a xB zB qCol pl cx m + smChain a cB m - (2 : ℤ) ^ SB * smChain a cB (m + 1)

/-- **The recomposition.** The base-`2^SB` fold of the 32 digits IS `cx·X − Z − M·q`. -/
theorem sm_recompose (a : Assignment) (xB zB qCol : Nat) (pl : Nat → ℤ) (cx M : ℤ)
    (hplM : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = M) :
    sumL (List.range SK) (fun m => ((2 : ℤ) ^ SB) ^ m * smDigit a xB zB qCol pl cx m)
      = cx * sVal a xB - sVal a zB - M * a qCol := by
  have hstep : ∀ m ∈ List.range SK,
      ((2 : ℤ) ^ SB) ^ m * smDigit a xB zB qCol pl cx m
        = (cx * (((2 : ℤ) ^ SB) ^ m * a (xB + m)) - ((2 : ℤ) ^ SB) ^ m * a (zB + m))
          - a qCol * (((2 : ℤ) ^ SB) ^ m * pl m) := by
    intro m hm
    have hlt : m < SK := List.mem_range.mp hm
    unfold smDigit
    rw [if_pos hlt]
    ring
  rw [sumL_congr _ _ _ hstep, sumL_sub, sumL_sub, sumL_smul, sumL_smul]
  unfold sVal
  rw [hplM]
  ring

/-- The digit is bounded by **two byte-products and a byte**. -/
theorem smDigit_abs_le (a : Assignment) (xB zB qCol : Nat) (pl : Nat → ℤ) (cx : ℤ) (m : Nat)
    (hcx : 0 ≤ cx ∧ cx < 2 ^ SB)
    (hx : Ranged a xB) (hz : Ranged a zB)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hq : 0 ≤ a qCol ∧ a qCol < 2 ^ SB) :
    |smDigit a xB zB qCol pl cx m|
      ≤ 2 * (((2 : ℤ) ^ SB - 1) * ((2 : ℤ) ^ SB - 1)) + ((2 : ℤ) ^ SB - 1) := by
  unfold smDigit
  by_cases hm : m < SK
  · rw [if_pos hm]
    obtain ⟨hx0, hx1⟩ := hx m hm
    obtain ⟨hz0, hz1⟩ := hz m hm
    obtain ⟨hp0, hp1⟩ := hpl m
    obtain ⟨hc0, hc1⟩ := hcx
    obtain ⟨hq0, hq1⟩ := hq
    have hB : (2 : ℤ) ^ SB = 256 := by norm_num [SB]
    rw [hB] at hx1 hz1 hp1 hc1 hq1 ⊢
    rw [abs_le]
    constructor <;> nlinarith
  · rw [if_neg hm]; norm_num [SB]

/-- The carry is bounded by the declared 16-bit width. -/
theorem smChain_abs_le (a : Assignment) (cB m : Nat)
    (hc : RangedAt a cB (SK - 1) CB) : |smChain a cB m| ≤ COFF := by
  unfold smChain
  by_cases h0 : m = 0
  · rw [if_pos h0]; simp [COFF]
  by_cases h1 : m ≤ SK - 1
  · rw [if_neg h0, if_pos h1]
    obtain ⟨hl, hr⟩ := hc (m - 1) (by omega)
    have hidx : cB + m - 1 = cB + (m - 1) := by omega
    have hCB : (2 : ℤ) ^ CB = 2 * COFF := by norm_num [CB, COFF]
    rw [hidx, abs_le]
    constructor <;> linarith
  · rw [if_neg h0, if_neg h1]; simp [COFF]

/-- ⚑ **EVERY CONSTANT-MULTIPLY GATE BODY FITS A FELT** — `8 551 681 < 2 013 265 921`. -/
theorem smBody_abs_lt_P (a : Assignment) (xB zB qCol cB : Nat) (pl : Nat → ℤ) (cx : ℤ) (m : Nat)
    (hcx : 0 ≤ cx ∧ cx < 2 ^ SB)
    (hx : Ranged a xB) (hz : Ranged a zB)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hq : 0 ≤ a qCol ∧ a qCol < 2 ^ SB)
    (hc : RangedAt a cB (SK - 1) CB) :
    |smBody a xB zB qCol cB pl cx m| < P := by
  have hd := smDigit_abs_le a xB zB qCol pl cx m hcx hx hz hpl hq
  have hc1 := smChain_abs_le a cB m hc
  have hc2 := smChain_abs_le a cB (m + 1) hc
  have hscale : |(2 : ℤ) ^ SB * smChain a cB (m + 1)| ≤ (2 : ℤ) ^ SB * COFF := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (2 : ℤ) ^ SB)]
    exact mul_le_mul_of_nonneg_left hc2 (by positivity)
  have hnum : 2 * (((2 : ℤ) ^ SB - 1) * ((2 : ℤ) ^ SB - 1)) + ((2 : ℤ) ^ SB - 1)
      + COFF + (2 : ℤ) ^ SB * COFF < P := by
    norm_num [SB, COFF, Dregg2.Circuit.Emit.EffectLower.P]
  unfold smBody
  have h1 := abs_sub_le' (smDigit a xB zB qCol pl cx m + smChain a cB m)
    ((2 : ℤ) ^ SB * smChain a cB (m + 1))
  have h2 := abs_add_le' (smDigit a xB zB qCol pl cx m) (smChain a cB m)
  linarith

/-- The exact margin, named so it is not a caption a reader has to recompute. -/
theorem smBody_bound_value :
    2 * (((2 : ℤ) ^ SB - 1) * ((2 : ℤ) ^ SB - 1)) + ((2 : ℤ) ^ SB - 1)
      + COFF + (2 : ℤ) ^ SB * COFF = 8551681 := by
  norm_num [SB, COFF]

/-- ⚑ **THE THEOREM.** From the reading the DEPLOYED PROVER performs — every one of the 32
coefficient gate bodies `≡ 0 (mod P)` — plus the range facts the emitted lookups supply, the
congruence `cx·x ≡ z (mod M)` follows. -/
theorem smul_gates_force_congruence
    (a : Assignment) (xB zB qCol cB : Nat) (pl : Nat → ℤ) (cx M : ℤ)
    (hcx : 0 ≤ cx ∧ cx < 2 ^ SB)
    (hx : Ranged a xB) (hz : Ranged a zB)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hplM : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = M)
    (hq : 0 ≤ a qCol ∧ a qCol < 2 ^ SB)
    (hc : RangedAt a cB (SK - 1) CB)
    (hgates : ∀ m, m < SK → P ∣ smBody a xB zB qCol cB pl cx m) :
    M ∣ (cx * sVal a xB - sVal a zB) := by
  have hzero : ∀ m, m < SK → smBody a xB zB qCol cB pl cx m = 0 := by
    intro m hm
    have hlt := smBody_abs_lt_P a xB zB qCol cB pl cx m hcx hx hz hpl hq hc
    rcases hgates m hm with ⟨t, ht⟩
    by_contra hne
    have ht0 : t ≠ 0 := by rintro rfl; rw [mul_zero] at ht; exact hne ht
    have hP0 : (0 : ℤ) < P := by norm_num [Dregg2.Circuit.Emit.EffectLower.P]
    have h1 : (1 : ℤ) ≤ |t| := by rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    have : P ≤ |smBody a xB zB qCol cB pl cx m| := by
      rw [ht, abs_mul, abs_of_nonneg (le_of_lt hP0)]
      nlinarith
    linarith
  have hchain : ∀ m, smChain a cB m + smDigit a xB zB qCol pl cx m
      = (2 : ℤ) ^ SB * smChain a cB (m + 1) := by
    intro m
    by_cases hm : m < SK
    · have := hzero m hm; unfold smBody at this; linarith
    · have hSK : SK = 32 := rfl
      have h1 : smChain a cB m = 0 := by
        unfold smChain; rw [if_neg (by omega), if_neg (by omega)]
      have h2 : smChain a cB (m + 1) = 0 := by
        unfold smChain; rw [if_neg (by omega), if_neg (by omega)]
      have h3 : smDigit a xB zB qCol pl cx m = 0 := by
        unfold smDigit; rw [if_neg (by omega)]
      rw [h1, h2, h3]; ring
  have htel := telescope ((2 : ℤ) ^ SB) (smDigit a xB zB qCol pl cx) (smChain a cB) hchain SK
  rw [smChain_top, smChain_zero, mul_zero, sub_zero] at htel
  rw [sm_recompose a xB zB qCol pl cx M hplM] at htel
  exact ⟨a qCol, by linarith⟩

/-! ### The emitted const-multiply gate, and the bridge to the body above. -/

/-- The digit expression at index `m`. `cx` and `pl m` are gate CONSTANTS, so this leg is LINEAR in
the trace — **zero var×var products in the whole constant-multiply.** -/
def smDigitExpr (xB zB qCol : Nat) (pl : Nat → ℤ) (cx : ℤ) (m : Nat) : Expr :=
  if m < SK then
    .add (.add (.mul (.const cx) (.var (xB + m))) (.mul (.const (-1)) (.var (zB + m))))
         (.mul (.const (-(pl m))) (.var qCol))
  else .const 0

/-- The carry term at index `m` — `.const 0` at both ends. -/
def smChainExpr (cB m : Nat) : Expr :=
  if m = 0 then .const 0
  else if m ≤ SK - 1 then .add (.var (cB + m - 1)) (.const (-COFF))
  else .const 0

/-- **The coefficient gate expression at index `m`.** -/
def smExpr (xB zB qCol cB : Nat) (pl : Nat → ℤ) (cx : ℤ) (m : Nat) : Expr :=
  .add (smDigitExpr xB zB qCol pl cx m)
       (.add (smChainExpr cB m) (.mul (.const (-((2 : ℤ) ^ SB))) (smChainExpr cB (m + 1))))

theorem smChainExpr_eval (a : Assignment) (cB m : Nat) :
    (smChainExpr cB m).eval a = smChain a cB m := by
  unfold smChainExpr smChain
  by_cases h0 : m = 0
  · simp [h0, Expr.eval]
  by_cases h1 : m ≤ SK - 1
  · simp [h0, h1, Expr.eval, sub_eq_add_neg]
  · simp [h0, h1, Expr.eval]

/-- ⚑ **THE BRIDGE.** The emitted gate expression evaluates to exactly the body the soundness
theorem quantifies over. -/
theorem smExpr_eval (a : Assignment) (xB zB qCol cB : Nat) (pl : Nat → ℤ) (cx : ℤ) (m : Nat) :
    (smExpr xB zB qCol cB pl cx m).eval a = smBody a xB zB qCol cB pl cx m := by
  unfold smExpr smBody smDigitExpr smDigit
  by_cases h : m < SK
  · simp only [if_pos h, Expr.eval, smChainExpr_eval]; ring
  · simp only [if_neg h, Expr.eval, smChainExpr_eval]; ring

/-- ⚑ **The constant multiply as a `SoundCore`.** Witness block: the one reduction-quotient column
at `wB`, then 31 carries at `wB + 1`. **`32` columns — not the multiply's `94`.** -/
def smulCore (pl : Nat → ℤ) (cx : ℤ) : SoundCore :=
  { legs := fun xB _yB zB wB =>
      (List.range SK).map (fun m => AirLeg.gate ⟨smExpr xB zB wB (wB + 1) pl cx m, .const 0⟩)
      ++ [ AirLeg.limbs ⟨limbCols zB, SB, rangeTidW SB⟩
         , AirLeg.limbs ⟨[wB], SB, rangeTidW SB⟩
         , AirLeg.limbs ⟨acarryCols (wB + 1), CB, rangeTidW CB⟩ ]
  , width := 1 + (SK - 1) }

/-! ## §4 — ⚑ THE GADGET, on the bridge type.

Line for line the SSA of `PastaCurveComplete.swCompleteAddGadget` (`:281-313`) — the same 33 ops in
the same order, `12 mul + 2 smul + 14 add + 5 sub`. What changed is the layout stride (32 limbs a
value, not 9) and the fact that each op contributes a leg BLOCK.

⚑ **The six INPUT blocks are NOT ranged here.** In a ladder the inputs of a complete-add are the
outputs of the previous one and are already lookup-pinned by the op that produced them; ranging them
again would double-count. `§5`'s standalone descriptor adds those six lookups, so the two figures —
the marginal cost of a row in a chain, and the cost of a row on its own — are both stated and
neither is inferred from the other. -/

/-- The `i`-th SSA intermediate's limb block. -/
def vBase (fresh i : Nat) : Nat := fresh + SK * i
/-- The `k`-th MULTIPLY witness block: 32 quotient limbs then 62 carries. -/
def mWit (fresh k : Nat) : Nat := fresh + SK * 33 + (SK + (NG - 1)) * k
/-- The `k`-th CONSTANT-MULTIPLY witness block: one quotient column then 31 carries. -/
def sWit (fresh k : Nat) : Nat := fresh + SK * 33 + (SK + (NG - 1)) * 12 + SK * k
/-- The `k`-th ADD/SUB witness block: the carry/borrow bit then 31 carries. -/
def aWit (fresh k : Nat) : Nat := fresh + SK * 33 + (SK + (NG - 1)) * 12 + SK * 2 + SK * k

/-- Columns one complete add consumes beyond its six input blocks. -/
def RCB_FRESH : Nat := SK * 33 + (SK + (NG - 1)) * 12 + SK * 2 + SK * 19

theorem rcb_fresh_eq : RCB_FRESH = 2856 := by decide

/-- ⚑ **THE SOUND RCB COMPLETE ADDITION**, generic over the four `SoundCore`s. Returns the leg
block, the `(X3, Y3, Z3)` result bases, and the next free column — the same triple
`swCompleteAddGadget` returns, with `List VmConstraint2` widened to `List AirLeg`. -/
def swCompleteAddSoundLegs (mulC addC subC : SoundCore) (smulC : SoundCore)
    (X1 Y1 Z1 X2 Y2 Z2 fresh : Nat) : List AirLeg × (Nat × Nat × Nat) × Nat :=
  let v := vBase fresh; let m := mWit fresh; let s := sWit fresh; let b := aWit fresh
  ( mulC.legs  X1     X2     (v 0)  (m 0)                      -- t0a = X1·X2
    ++ mulC.legs  Y1     Y2     (v 1)  (m 1)                   -- t1a = Y1·Y2
    ++ mulC.legs  Z1     Z2     (v 2)  (m 2)                   -- t2a = Z1·Z2
    ++ addC.legs  X1     Y1     (v 3)  (b 0)                   -- t3a = X1+Y1
    ++ addC.legs  X2     Y2     (v 4)  (b 1)                   -- t4a = X2+Y2
    ++ mulC.legs  (v 3)  (v 4)  (v 5)  (m 3)                   -- t3b = t3a·t4a
    ++ addC.legs  (v 0)  (v 1)  (v 6)  (b 2)                   -- t4b = t0a+t1a
    ++ subC.legs  (v 5)  (v 6)  (v 7)  (b 3)                   -- t3c = t3b−t4b
    ++ addC.legs  Y1     Z1     (v 8)  (b 4)                   -- t4c = Y1+Z1
    ++ addC.legs  Y2     Z2     (v 9)  (b 5)                   -- X3a = Y2+Z2
    ++ mulC.legs  (v 8)  (v 9)  (v 10) (m 4)                   -- t4d = t4c·X3a
    ++ addC.legs  (v 1)  (v 2)  (v 11) (b 6)                   -- X3b = t1a+t2a
    ++ subC.legs  (v 10) (v 11) (v 12) (b 7)                   -- t4e = t4d−X3b
    ++ addC.legs  X1     Z1     (v 13) (b 8)                   -- X3c = X1+Z1
    ++ addC.legs  X2     Z2     (v 14) (b 9)                   -- Y3a = X2+Z2
    ++ mulC.legs  (v 13) (v 14) (v 15) (m 5)                   -- X3d = X3c·Y3a
    ++ addC.legs  (v 0)  (v 2)  (v 16) (b 10)                  -- Y3b = t0a+t2a
    ++ subC.legs  (v 15) (v 16) (v 17) (b 11)                  -- Y3c = X3d−Y3b
    ++ addC.legs  (v 0)  (v 0)  (v 18) (b 12)                  -- X3e = t0a+t0a
    ++ addC.legs  (v 18) (v 0)  (v 19) (b 13)                  -- t0b = X3e+t0a
    ++ smulC.legs (v 2)  (v 2)  (v 20) (s 0)                   -- t2b = b3·t2a
    ++ addC.legs  (v 1)  (v 20) (v 21) (b 14)                  -- Z3a = t1a+t2b
    ++ subC.legs  (v 1)  (v 20) (v 22) (b 15)                  -- t1b = t1a−t2b
    ++ smulC.legs (v 17) (v 17) (v 23) (s 1)                   -- Y3d = b3·Y3c
    ++ mulC.legs  (v 12) (v 23) (v 24) (m 6)                   -- X3f = t4e·Y3d
    ++ mulC.legs  (v 7)  (v 22) (v 25) (m 7)                   -- t2c = t3c·t1b
    ++ subC.legs  (v 25) (v 24) (v 26) (b 16)                  -- X3g = t2c−X3f  (= X3)
    ++ mulC.legs  (v 23) (v 19) (v 27) (m 8)                   -- Y3e = Y3d·t0b
    ++ mulC.legs  (v 22) (v 21) (v 28) (m 9)                   -- t1c = t1b·Z3a
    ++ addC.legs  (v 28) (v 27) (v 29) (b 17)                  -- Y3f = t1c+Y3e  (= Y3)
    ++ mulC.legs  (v 19) (v 7)  (v 30) (m 10)                  -- t0c = t0b·t3c
    ++ mulC.legs  (v 21) (v 12) (v 31) (m 11)                  -- Z3b = Z3a·t4e
    ++ addC.legs  (v 31) (v 30) (v 32) (b 18)                  -- Z3c = Z3b+t0c  (= Z3)
  , (v 26, v 29, v 32), fresh + RCB_FRESH )

/-- **Pallas** (modulus `p`), `b3 = 15`. -/
def pallasCompleteAddSoundLegs : Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    List AirLeg × (Nat × Nat × Nat) × Nat :=
  swCompleteAddSoundLegs (mulCore pLimb) (addSubCore pLimb 1 (-1)) (addSubCore pLimb (-1) 1)
    (smulCore pLimb (curveB3 : ℤ))

/-- **Vesta** (modulus `q`) — the accumulator leg is Step/Tick on Vesta, so this is not optional. -/
def vestaCompleteAddSoundLegs : Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    List AirLeg × (Nat × Nat × Nat) × Nat :=
  swCompleteAddSoundLegs (mulCore qLimb) (addSubCore qLimb 1 (-1)) (addSubCore qLimb (-1) 1)
    (smulCore qLimb (curveB3 : ℤ))

/-! ## §5 — the standalone descriptors, and THE PRICE MEASURED ON THEM. -/

/-- The six input blocks live at `0, 32, 64, 96, 128, 160`; the gadget's scratch starts at `192`. -/
def IN_BASE : Nat := 6 * SK
/-- `192 + 2 856 = 3 048` declared main columns for one standalone complete add. -/
def RCB_WIDTH : Nat := IN_BASE + RCB_FRESH

theorem rcb_width_eq : RCB_WIDTH = 3048 := by decide

/-- The three range tables this row declares — exactly the UNION of what `soundMulAir` and
`soundAddSubAir` declare, and nothing new: the constant-multiply was deliberately sized onto the
`w8`/`w16` pair rather than inventing a fourth width. -/
def rcbTables : List TableDef :=
  [ mainTableDef RCB_WIDTH
  , ⟨rangeTidW SB, "range_w8", 1, .rangeLimb SB⟩
  , ⟨rangeTidW CB, "range_w16", 1, .rangeLimb CB⟩
  , ⟨rangeTidW CBITS, "range_w1", 1, .rangeLimb CBITS⟩ ]

/-- The six input blocks' range lookups — the ones a chained row does NOT pay for. -/
def inputLimbLegs : List AirLeg :=
  (List.range 6).map (fun i => AirLeg.limbs ⟨limbCols (SK * i), SB, rangeTidW SB⟩)

/-- **The source AIR of one standalone sound Pallas complete addition.** -/
def pallasCompleteAddSoundAir : EffectAir :=
  { tables := rcbTables
  , legs := inputLimbLegs
      ++ (pallasCompleteAddSoundLegs 0 SK (2*SK) (3*SK) (4*SK) (5*SK) IN_BASE).1 }

/-- …and the Vesta twin. -/
def vestaCompleteAddSoundAir : EffectAir :=
  { tables := rcbTables
  , legs := inputLimbLegs
      ++ (vestaCompleteAddSoundLegs 0 SK (2*SK) (3*SK) (4*SK) (5*SK) IN_BASE).1 }

/-- ⚑ **THE COMPILER ACCEPTS BOTH BLOCKS.** Every leg has a deployed main-rail image, which for the
limbs legs is the `0 < bits ≤ 29` verdict. A width of 30 anywhere would emit `refuseConstraints`
instead and this theorem would be false. -/
theorem pallasCompleteAddSoundAir_mainRailOk : pallasCompleteAddSoundAir.mainRailOk = true := by
  decide

theorem vestaCompleteAddSoundAir_mainRailOk : vestaCompleteAddSoundAir.mainRailOk = true := by
  decide

/-- ⚑ **THE TIED SOURCE** — `pallasCompleteAddSoundAir` carrying its two decidable verdicts in its TYPE:
`mainRailOk` (main-rail expressible) and `pinsTied` (every published column is DERIVED by another
leg). A `TiedAir` cannot be built for a block that publishes a column nothing else constrains, so a
decorative pin is unrepresentable here rather than detectable by a census afterwards. -/
def pallasCompleteAddTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air := pallasCompleteAddSoundAir

def pallasCompleteAddSoundDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-pallas-complete-add-sound::v1" RCB_WIDTH 0 [] pallasCompleteAddTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — `AirLeg.forces`, stated in the
SOURCE's vocabulary and never mentioning the lowering, so it is not `P → P`. Not re-derived here.

**Zero bytes move**: `lowerTiedAir … |>.val` is `lowerAir …` by `rfl`. -/
theorem pallasCompleteAddSoundDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines pallasCompleteAddSoundDesc [] pallasCompleteAddSoundAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-pallas-complete-add-sound::v1" RCB_WIDTH 0 [] pallasCompleteAddTiedAir).property

/-- ⚑ **THE ZERO.** The certified lowering emits the term the bare lowering emitted, by `rfl` — so
the migration changed what this definition PROVES, not what it PRODUCES. No re-emit, no VK rotation.
Also the unfolding lemma for the cost/shape proofs below, which reason through `lowerAir`. -/
theorem pallasCompleteAddSoundDesc_eq_lowerAir :
    pallasCompleteAddSoundDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-pasta-pallas-complete-add-sound::v1" RCB_WIDTH 0 [] pallasCompleteAddSoundAir := rfl

/-- ⚑ **THE TIED SOURCE** — `vestaCompleteAddSoundAir` carrying its two decidable verdicts in its TYPE:
`mainRailOk` (main-rail expressible) and `pinsTied` (every published column is DERIVED by another
leg). A `TiedAir` cannot be built for a block that publishes a column nothing else constrains, so a
decorative pin is unrepresentable here rather than detectable by a census afterwards. -/
def vestaCompleteAddTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air := vestaCompleteAddSoundAir

def vestaCompleteAddSoundDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-vesta-complete-add-sound::v1" RCB_WIDTH 0 [] vestaCompleteAddTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — `AirLeg.forces`, stated in the
SOURCE's vocabulary and never mentioning the lowering, so it is not `P → P`. Not re-derived here.

**Zero bytes move**: `lowerTiedAir … |>.val` is `lowerAir …` by `rfl`. -/
theorem vestaCompleteAddSoundDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines vestaCompleteAddSoundDesc [] vestaCompleteAddSoundAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-vesta-complete-add-sound::v1" RCB_WIDTH 0 [] vestaCompleteAddTiedAir).property

/-- ⚑ **THE ZERO.** The certified lowering emits the term the bare lowering emitted, by `rfl` — so
the migration changed what this definition PROVES, not what it PRODUCES. No re-emit, no VK rotation.
Also the unfolding lemma for the cost/shape proofs below, which reason through `lowerAir`. -/
theorem vestaCompleteAddSoundDesc_eq_lowerAir :
    vestaCompleteAddSoundDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-pasta-vesta-complete-add-sound::v1" RCB_WIDTH 0 [] vestaCompleteAddSoundAir := rfl

/-! ## §6 — ⚑ FORCING: the 33 leg blocks' DEPLOYED satisfaction forces the RCB formula.

The hypotheses are stated at the EMITTED expressions (`coefExpr`, `adExpr`, `smExpr`) and in the
reading `prove_vm_descriptor2` actually performs — `P ∣ body`, not `body = 0` over ℤ. That is the
whole difference from `PastaCurveComplete.pallasCompleteAdd_forces`, whose 33 hypotheses are
`evalH … = 0` over ℤ: a fact no proof object establishes, which is why the falsifiers exist.

The `CZm` algebra is REUSED from `PastaCurve` (single source) — it is a statement about ℤ and
divisibility, so it carries from `fpVal` to `sVal` untouched. -/

/-- Op-level: the multiply's 63 emitted gate bodies vanish mod `P`. -/
def MulSat (a : Assignment) (pl : Nat → ℤ) (xB yB zB wB : Nat) : Prop :=
  ∀ m, m < NG → P ∣ (coefExpr xB yB zB wB (wB + SK) pl m).eval a

/-- Op-level: the add/sub's 32 emitted gate bodies vanish mod `P`. -/
def AddSubSat (a : Assignment) (pl : Nat → ℤ) (sy sc : ℤ) (xB yB zB wB : Nat) : Prop :=
  ∀ m, m < NA → P ∣ (adExpr xB yB zB wB (wB + 1) pl sy sc m).eval a

/-- Op-level: the constant multiply's 32 emitted gate bodies vanish mod `P`. -/
def SmulSat (a : Assignment) (pl : Nat → ℤ) (cx : ℤ) (xB zB wB : Nat) : Prop :=
  ∀ m, m < SK → P ∣ (smExpr xB zB wB (wB + 1) pl cx m).eval a

/-- A multiply's private witness: 32 quotient limbs then 62 sixteen-bit carries. -/
def MulWitRanged (a : Assignment) (wB : Nat) : Prop :=
  Ranged a wB ∧ RangedAt a (wB + SK) (NG - 1) CB
/-- An add/sub's private witness: the carry BIT then 31 eight-bit carries. -/
def AddSubWitRanged (a : Assignment) (wB : Nat) : Prop :=
  (0 ≤ a wB ∧ a wB < 2) ∧ RangedAt a (wB + 1) (NA - 1) ACB
/-- A constant multiply's private witness: one byte-ranged quotient then 31 sixteen-bit carries. -/
def SmulWitRanged (a : Assignment) (wB : Nat) : Prop :=
  (0 ≤ a wB ∧ a wB < 2 ^ SB) ∧ RangedAt a (wB + 1) (SK - 1) CB

/-- ⚑ **The satisfaction predicates ARE the emitted gate legs.** Without this the theorems below
would be about a different object than the AIR carries. -/
theorem mulCore_legs_are_the_gates (pl : Nat → ℤ) (xB yB zB wB : Nat) :
    (mulCore pl).legs xB yB zB wB
      = (List.range NG).map
          (fun m => AirLeg.gate ⟨coefExpr xB yB zB wB (wB + SK) pl m, .const 0⟩)
        ++ [ AirLeg.limbs ⟨limbCols zB, SB, rangeTidW SB⟩
           , AirLeg.limbs ⟨limbCols wB, SB, rangeTidW SB⟩
           , AirLeg.limbs ⟨carryCols (wB + SK), CB, rangeTidW CB⟩ ] := rfl

theorem smulCore_legs_are_the_gates (pl : Nat → ℤ) (cx : ℤ) (xB yB zB wB : Nat) :
    (smulCore pl cx).legs xB yB zB wB
      = (List.range SK).map (fun m => AirLeg.gate ⟨smExpr xB zB wB (wB + 1) pl cx m, .const 0⟩)
        ++ [ AirLeg.limbs ⟨limbCols zB, SB, rangeTidW SB⟩
           , AirLeg.limbs ⟨[wB], SB, rangeTidW SB⟩
           , AirLeg.limbs ⟨acarryCols (wB + 1), CB, rangeTidW CB⟩ ] := rfl

/-! ### The four per-op forcing lemmas. -/

theorem mulCore_forces (a : Assignment) (pl : Nat → ℤ) (M : ℤ)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hplM : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = M)
    (xB yB zB wB : Nat)
    (hx : Ranged a xB) (hy : Ranged a yB) (hz : Ranged a zB)
    (hw : MulWitRanged a wB) (hg : MulSat a pl xB yB zB wB) :
    CZm M (sVal a zB) (sVal a xB * sVal a yB) :=
  CZm.symm (felt_gates_force_congruence a xB yB zB wB (wB + SK) pl M hx hy hz hw.1 hpl hplM hw.2
    (fun m hm => by have := hg m hm; rwa [coefExpr_eval] at this))

theorem addCore_forces (a : Assignment) (pl : Nat → ℤ) (M : ℤ)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hplM : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = M)
    (xB yB zB wB : Nat)
    (hx : Ranged a xB) (hy : Ranged a yB) (hz : Ranged a zB)
    (hw : AddSubWitRanged a wB) (hg : AddSubSat a pl 1 (-1) xB yB zB wB) :
    CZm M (sVal a zB) (sVal a xB + sVal a yB) := by
  have h := addsub_gates_force_congruence a xB yB zB wB (wB + 1) pl 1 (-1) M
    (Or.inl rfl) (Or.inr rfl) hx hy hz hpl hplM hw.1 hw.2
    (fun m hm => by have := hg m hm; rwa [adExpr_eval] at this)
  unfold CZm
  rw [show sVal a zB - (sVal a xB + sVal a yB)
        = -(sVal a xB + 1 * sVal a yB - sVal a zB) by ring]
  exact dvd_neg.mpr h

theorem subCore_forces (a : Assignment) (pl : Nat → ℤ) (M : ℤ)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hplM : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = M)
    (xB yB zB wB : Nat)
    (hx : Ranged a xB) (hy : Ranged a yB) (hz : Ranged a zB)
    (hw : AddSubWitRanged a wB) (hg : AddSubSat a pl (-1) 1 xB yB zB wB) :
    CZm M (sVal a zB) (sVal a xB - sVal a yB) := by
  have h := addsub_gates_force_congruence a xB yB zB wB (wB + 1) pl (-1) 1 M
    (Or.inr rfl) (Or.inl rfl) hx hy hz hpl hplM hw.1 hw.2
    (fun m hm => by have := hg m hm; rwa [adExpr_eval] at this)
  unfold CZm
  rw [show sVal a zB - (sVal a xB - sVal a yB)
        = -(sVal a xB + (-1) * sVal a yB - sVal a zB) by ring]
  exact dvd_neg.mpr h

theorem smulCore_forces (a : Assignment) (pl : Nat → ℤ) (M : ℤ) (cx : ℤ)
    (hcx : 0 ≤ cx ∧ cx < 2 ^ SB)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hplM : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = M)
    (xB zB wB : Nat)
    (hx : Ranged a xB) (hz : Ranged a zB)
    (hw : SmulWitRanged a wB) (hg : SmulSat a pl cx xB zB wB) :
    CZm M (sVal a zB) (cx * sVal a xB) := by
  have h := smul_gates_force_congruence a xB zB wB (wB + 1) pl cx M hcx hx hz hpl hplM hw.1 hw.2
    (fun m hm => by have := hg m hm; rwa [smExpr_eval] at this)
  unfold CZm
  rw [show sVal a zB - cx * sVal a xB = -(cx * sVal a xB - sVal a zB) by ring]
  exact dvd_neg.mpr h

/-! ### ⚑ THE COMPOSED THEOREM.

Modulus-generic in `pl`/`M`, exactly as `felt_gates_force_congruence` and
`addsub_gates_force_congruence` are — so ONE theorem covers Pallas and Vesta and §6b's two
instantiations are corollaries rather than a second copy of the chain. -/

/-- ⚑ **THE 33 GATE-BLOCK HYPOTHESES, as one named object.** Field `hgN` is op `N` of
`swCompleteAddSoundLegs`, in the same SSA order, at the same column bases. It is a `Prop` structure
rather than a conjunction so a caller supplying it has to name each op. -/
structure RcbSat (a : Assignment) (pl : Nat → ℤ) (b3 : ℤ)
    (X1 Y1 Z1 X2 Y2 Z2 fresh : Nat) : Prop where
  hg0 : MulSat a pl X1 X2 (vBase fresh 0) (mWit fresh 0)
  hg1 : MulSat a pl Y1 Y2 (vBase fresh 1) (mWit fresh 1)
  hg2 : MulSat a pl Z1 Z2 (vBase fresh 2) (mWit fresh 2)
  hg3 : AddSubSat a pl 1 (-1) X1 Y1 (vBase fresh 3) (aWit fresh 0)
  hg4 : AddSubSat a pl 1 (-1) X2 Y2 (vBase fresh 4) (aWit fresh 1)
  hg5 : MulSat a pl (vBase fresh 3) (vBase fresh 4) (vBase fresh 5) (mWit fresh 3)
  hg6 : AddSubSat a pl 1 (-1) (vBase fresh 0) (vBase fresh 1) (vBase fresh 6) (aWit fresh 2)
  hg7 : AddSubSat a pl (-1) 1 (vBase fresh 5) (vBase fresh 6) (vBase fresh 7) (aWit fresh 3)
  hg8 : AddSubSat a pl 1 (-1) Y1 Z1 (vBase fresh 8) (aWit fresh 4)
  hg9 : AddSubSat a pl 1 (-1) Y2 Z2 (vBase fresh 9) (aWit fresh 5)
  hg10 : MulSat a pl (vBase fresh 8) (vBase fresh 9) (vBase fresh 10) (mWit fresh 4)
  hg11 : AddSubSat a pl 1 (-1) (vBase fresh 1) (vBase fresh 2) (vBase fresh 11) (aWit fresh 6)
  hg12 : AddSubSat a pl (-1) 1 (vBase fresh 10) (vBase fresh 11) (vBase fresh 12) (aWit fresh 7)
  hg13 : AddSubSat a pl 1 (-1) X1 Z1 (vBase fresh 13) (aWit fresh 8)
  hg14 : AddSubSat a pl 1 (-1) X2 Z2 (vBase fresh 14) (aWit fresh 9)
  hg15 : MulSat a pl (vBase fresh 13) (vBase fresh 14) (vBase fresh 15) (mWit fresh 5)
  hg16 : AddSubSat a pl 1 (-1) (vBase fresh 0) (vBase fresh 2) (vBase fresh 16) (aWit fresh 10)
  hg17 : AddSubSat a pl (-1) 1 (vBase fresh 15) (vBase fresh 16) (vBase fresh 17) (aWit fresh 11)
  hg18 : AddSubSat a pl 1 (-1) (vBase fresh 0) (vBase fresh 0) (vBase fresh 18) (aWit fresh 12)
  hg19 : AddSubSat a pl 1 (-1) (vBase fresh 18) (vBase fresh 0) (vBase fresh 19) (aWit fresh 13)
  hg20 : SmulSat a pl b3 (vBase fresh 2) (vBase fresh 20) (sWit fresh 0)
  hg21 : AddSubSat a pl 1 (-1) (vBase fresh 1) (vBase fresh 20) (vBase fresh 21) (aWit fresh 14)
  hg22 : AddSubSat a pl (-1) 1 (vBase fresh 1) (vBase fresh 20) (vBase fresh 22) (aWit fresh 15)
  hg23 : SmulSat a pl b3 (vBase fresh 17) (vBase fresh 23) (sWit fresh 1)
  hg24 : MulSat a pl (vBase fresh 12) (vBase fresh 23) (vBase fresh 24) (mWit fresh 6)
  hg25 : MulSat a pl (vBase fresh 7) (vBase fresh 22) (vBase fresh 25) (mWit fresh 7)
  hg26 : AddSubSat a pl (-1) 1 (vBase fresh 25) (vBase fresh 24) (vBase fresh 26) (aWit fresh 16)
  hg27 : MulSat a pl (vBase fresh 23) (vBase fresh 19) (vBase fresh 27) (mWit fresh 8)
  hg28 : MulSat a pl (vBase fresh 22) (vBase fresh 21) (vBase fresh 28) (mWit fresh 9)
  hg29 : AddSubSat a pl 1 (-1) (vBase fresh 28) (vBase fresh 27) (vBase fresh 29) (aWit fresh 17)
  hg30 : MulSat a pl (vBase fresh 19) (vBase fresh 7) (vBase fresh 30) (mWit fresh 10)
  hg31 : MulSat a pl (vBase fresh 21) (vBase fresh 12) (vBase fresh 31) (mWit fresh 11)
  hg32 : AddSubSat a pl 1 (-1) (vBase fresh 31) (vBase fresh 30) (vBase fresh 32) (aWit fresh 18)

/-- ⚑ **THE COMPOSED THEOREM.** The `CZm` algebra is `PastaCurve`'s, reused verbatim; what changed is that
every link is now a congruence forced by a MOD-`P` reading over range-pinned limbs rather than by
an ℤ-equality nothing establishes. -/
theorem RcbSat.apply {X1 Y1 Z1 X2 Y2 Z2 fresh : Nat} {b3 : ℤ}
    {a : Assignment} {pl : Nat → ℤ}
    (hG : RcbSat a pl b3 X1 Y1 Z1 X2 Y2 Z2 fresh) (M : ℤ)
    (hb3 : 0 ≤ b3 ∧ b3 < 2 ^ SB)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hplM : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = M)
    (hX1 : Ranged a X1) (hY1 : Ranged a Y1) (hZ1 : Ranged a Z1)
    (hX2 : Ranged a X2) (hY2 : Ranged a Y2) (hZ2 : Ranged a Z2)
    (hv : ∀ i, i < 33 → Ranged a (vBase fresh i))
    (hm : ∀ k, k < 12 → MulWitRanged a (mWit fresh k))
    (hs : ∀ k, k < 2 → SmulWitRanged a (sWit fresh k))
    (hb : ∀ k, k < 19 → AddSubWitRanged a (aWit fresh k)) :
    CZm M (sVal a (vBase fresh 26))
        (rcbTraceZ b3 (sVal a X1) (sVal a Y1) (sVal a Z1)
                      (sVal a X2) (sVal a Y2) (sVal a Z2)).X3g
      ∧ CZm M (sVal a (vBase fresh 29))
        (rcbTraceZ b3 (sVal a X1) (sVal a Y1) (sVal a Z1)
                      (sVal a X2) (sVal a Y2) (sVal a Z2)).Y3f
      ∧ CZm M (sVal a (vBase fresh 32))
        (rcbTraceZ b3 (sVal a X1) (sVal a Y1) (sVal a Z1)
                      (sVal a X2) (sVal a Y2) (sVal a Z2)).Z3c := by
  let T := rcbTraceZ b3 (sVal a X1) (sVal a Y1) (sVal a Z1)
             (sVal a X2) (sVal a Y2) (sVal a Z2)
  have f0 : CZm M (sVal a (vBase fresh 0)) T.t0a := mulCore_forces a pl M hpl hplM X1 X2 (vBase fresh 0) (mWit fresh 0) hX1 hX2 (hv 0 (by decide)) (hm 0 (by decide)) hG.hg0
  have f1 : CZm M (sVal a (vBase fresh 1)) T.t1a := mulCore_forces a pl M hpl hplM Y1 Y2 (vBase fresh 1) (mWit fresh 1) hY1 hY2 (hv 1 (by decide)) (hm 1 (by decide)) hG.hg1
  have f2 : CZm M (sVal a (vBase fresh 2)) T.t2a := mulCore_forces a pl M hpl hplM Z1 Z2 (vBase fresh 2) (mWit fresh 2) hZ1 hZ2 (hv 2 (by decide)) (hm 2 (by decide)) hG.hg2
  have f3 : CZm M (sVal a (vBase fresh 3)) T.t3a := addCore_forces a pl M hpl hplM X1 Y1 (vBase fresh 3) (aWit fresh 0) hX1 hY1 (hv 3 (by decide)) (hb 0 (by decide)) hG.hg3
  have f4 : CZm M (sVal a (vBase fresh 4)) T.t4a := addCore_forces a pl M hpl hplM X2 Y2 (vBase fresh 4) (aWit fresh 1) hX2 hY2 (hv 4 (by decide)) (hb 1 (by decide)) hG.hg4
  have f5 : CZm M (sVal a (vBase fresh 5)) T.t3b := CZm.trans (mulCore_forces a pl M hpl hplM (vBase fresh 3) (vBase fresh 4) (vBase fresh 5) (mWit fresh 3) (hv 3 (by decide)) (hv 4 (by decide)) (hv 5 (by decide)) (hm 3 (by decide)) hG.hg5) (CZm.mul f3 f4)
  have f6 : CZm M (sVal a (vBase fresh 6)) T.t4b := CZm.trans (addCore_forces a pl M hpl hplM (vBase fresh 0) (vBase fresh 1) (vBase fresh 6) (aWit fresh 2) (hv 0 (by decide)) (hv 1 (by decide)) (hv 6 (by decide)) (hb 2 (by decide)) hG.hg6) (CZm.add f0 f1)
  have f7 : CZm M (sVal a (vBase fresh 7)) T.t3c := CZm.trans (subCore_forces a pl M hpl hplM (vBase fresh 5) (vBase fresh 6) (vBase fresh 7) (aWit fresh 3) (hv 5 (by decide)) (hv 6 (by decide)) (hv 7 (by decide)) (hb 3 (by decide)) hG.hg7) (CZm.sub f5 f6)
  have f8 : CZm M (sVal a (vBase fresh 8)) T.t4c := addCore_forces a pl M hpl hplM Y1 Z1 (vBase fresh 8) (aWit fresh 4) hY1 hZ1 (hv 8 (by decide)) (hb 4 (by decide)) hG.hg8
  have f9 : CZm M (sVal a (vBase fresh 9)) T.X3a := addCore_forces a pl M hpl hplM Y2 Z2 (vBase fresh 9) (aWit fresh 5) hY2 hZ2 (hv 9 (by decide)) (hb 5 (by decide)) hG.hg9
  have f10 : CZm M (sVal a (vBase fresh 10)) T.t4d := CZm.trans (mulCore_forces a pl M hpl hplM (vBase fresh 8) (vBase fresh 9) (vBase fresh 10) (mWit fresh 4) (hv 8 (by decide)) (hv 9 (by decide)) (hv 10 (by decide)) (hm 4 (by decide)) hG.hg10) (CZm.mul f8 f9)
  have f11 : CZm M (sVal a (vBase fresh 11)) T.X3b := CZm.trans (addCore_forces a pl M hpl hplM (vBase fresh 1) (vBase fresh 2) (vBase fresh 11) (aWit fresh 6) (hv 1 (by decide)) (hv 2 (by decide)) (hv 11 (by decide)) (hb 6 (by decide)) hG.hg11) (CZm.add f1 f2)
  have f12 : CZm M (sVal a (vBase fresh 12)) T.t4e := CZm.trans (subCore_forces a pl M hpl hplM (vBase fresh 10) (vBase fresh 11) (vBase fresh 12) (aWit fresh 7) (hv 10 (by decide)) (hv 11 (by decide)) (hv 12 (by decide)) (hb 7 (by decide)) hG.hg12) (CZm.sub f10 f11)
  have f13 : CZm M (sVal a (vBase fresh 13)) T.X3c := addCore_forces a pl M hpl hplM X1 Z1 (vBase fresh 13) (aWit fresh 8) hX1 hZ1 (hv 13 (by decide)) (hb 8 (by decide)) hG.hg13
  have f14 : CZm M (sVal a (vBase fresh 14)) T.Y3a := addCore_forces a pl M hpl hplM X2 Z2 (vBase fresh 14) (aWit fresh 9) hX2 hZ2 (hv 14 (by decide)) (hb 9 (by decide)) hG.hg14
  have f15 : CZm M (sVal a (vBase fresh 15)) T.X3d := CZm.trans (mulCore_forces a pl M hpl hplM (vBase fresh 13) (vBase fresh 14) (vBase fresh 15) (mWit fresh 5) (hv 13 (by decide)) (hv 14 (by decide)) (hv 15 (by decide)) (hm 5 (by decide)) hG.hg15) (CZm.mul f13 f14)
  have f16 : CZm M (sVal a (vBase fresh 16)) T.Y3b := CZm.trans (addCore_forces a pl M hpl hplM (vBase fresh 0) (vBase fresh 2) (vBase fresh 16) (aWit fresh 10) (hv 0 (by decide)) (hv 2 (by decide)) (hv 16 (by decide)) (hb 10 (by decide)) hG.hg16) (CZm.add f0 f2)
  have f17 : CZm M (sVal a (vBase fresh 17)) T.Y3c := CZm.trans (subCore_forces a pl M hpl hplM (vBase fresh 15) (vBase fresh 16) (vBase fresh 17) (aWit fresh 11) (hv 15 (by decide)) (hv 16 (by decide)) (hv 17 (by decide)) (hb 11 (by decide)) hG.hg17) (CZm.sub f15 f16)
  have f18 : CZm M (sVal a (vBase fresh 18)) T.X3e := CZm.trans (addCore_forces a pl M hpl hplM (vBase fresh 0) (vBase fresh 0) (vBase fresh 18) (aWit fresh 12) (hv 0 (by decide)) (hv 0 (by decide)) (hv 18 (by decide)) (hb 12 (by decide)) hG.hg18) (CZm.add f0 f0)
  have f19 : CZm M (sVal a (vBase fresh 19)) T.t0b := CZm.trans (addCore_forces a pl M hpl hplM (vBase fresh 18) (vBase fresh 0) (vBase fresh 19) (aWit fresh 13) (hv 18 (by decide)) (hv 0 (by decide)) (hv 19 (by decide)) (hb 13 (by decide)) hG.hg19) (CZm.add f18 f0)
  have f20 : CZm M (sVal a (vBase fresh 20)) T.t2b := CZm.trans (smulCore_forces a pl M b3 hb3 hpl hplM (vBase fresh 2) (vBase fresh 20) (sWit fresh 0) (hv 2 (by decide)) (hv 20 (by decide)) (hs 0 (by decide)) hG.hg20) (CZm.mul (CZm.refl _) (f2))
  have f21 : CZm M (sVal a (vBase fresh 21)) T.Z3a := CZm.trans (addCore_forces a pl M hpl hplM (vBase fresh 1) (vBase fresh 20) (vBase fresh 21) (aWit fresh 14) (hv 1 (by decide)) (hv 20 (by decide)) (hv 21 (by decide)) (hb 14 (by decide)) hG.hg21) (CZm.add f1 f20)
  have f22 : CZm M (sVal a (vBase fresh 22)) T.t1b := CZm.trans (subCore_forces a pl M hpl hplM (vBase fresh 1) (vBase fresh 20) (vBase fresh 22) (aWit fresh 15) (hv 1 (by decide)) (hv 20 (by decide)) (hv 22 (by decide)) (hb 15 (by decide)) hG.hg22) (CZm.sub f1 f20)
  have f23 : CZm M (sVal a (vBase fresh 23)) T.Y3d := CZm.trans (smulCore_forces a pl M b3 hb3 hpl hplM (vBase fresh 17) (vBase fresh 23) (sWit fresh 1) (hv 17 (by decide)) (hv 23 (by decide)) (hs 1 (by decide)) hG.hg23) (CZm.mul (CZm.refl _) (f17))
  have f24 : CZm M (sVal a (vBase fresh 24)) T.X3f := CZm.trans (mulCore_forces a pl M hpl hplM (vBase fresh 12) (vBase fresh 23) (vBase fresh 24) (mWit fresh 6) (hv 12 (by decide)) (hv 23 (by decide)) (hv 24 (by decide)) (hm 6 (by decide)) hG.hg24) (CZm.mul f12 f23)
  have f25 : CZm M (sVal a (vBase fresh 25)) T.t2c := CZm.trans (mulCore_forces a pl M hpl hplM (vBase fresh 7) (vBase fresh 22) (vBase fresh 25) (mWit fresh 7) (hv 7 (by decide)) (hv 22 (by decide)) (hv 25 (by decide)) (hm 7 (by decide)) hG.hg25) (CZm.mul f7 f22)
  have f26 : CZm M (sVal a (vBase fresh 26)) T.X3g := CZm.trans (subCore_forces a pl M hpl hplM (vBase fresh 25) (vBase fresh 24) (vBase fresh 26) (aWit fresh 16) (hv 25 (by decide)) (hv 24 (by decide)) (hv 26 (by decide)) (hb 16 (by decide)) hG.hg26) (CZm.sub f25 f24)
  have f27 : CZm M (sVal a (vBase fresh 27)) T.Y3e := CZm.trans (mulCore_forces a pl M hpl hplM (vBase fresh 23) (vBase fresh 19) (vBase fresh 27) (mWit fresh 8) (hv 23 (by decide)) (hv 19 (by decide)) (hv 27 (by decide)) (hm 8 (by decide)) hG.hg27) (CZm.mul f23 f19)
  have f28 : CZm M (sVal a (vBase fresh 28)) T.t1c := CZm.trans (mulCore_forces a pl M hpl hplM (vBase fresh 22) (vBase fresh 21) (vBase fresh 28) (mWit fresh 9) (hv 22 (by decide)) (hv 21 (by decide)) (hv 28 (by decide)) (hm 9 (by decide)) hG.hg28) (CZm.mul f22 f21)
  have f29 : CZm M (sVal a (vBase fresh 29)) T.Y3f := CZm.trans (addCore_forces a pl M hpl hplM (vBase fresh 28) (vBase fresh 27) (vBase fresh 29) (aWit fresh 17) (hv 28 (by decide)) (hv 27 (by decide)) (hv 29 (by decide)) (hb 17 (by decide)) hG.hg29) (CZm.add f28 f27)
  have f30 : CZm M (sVal a (vBase fresh 30)) T.t0c := CZm.trans (mulCore_forces a pl M hpl hplM (vBase fresh 19) (vBase fresh 7) (vBase fresh 30) (mWit fresh 10) (hv 19 (by decide)) (hv 7 (by decide)) (hv 30 (by decide)) (hm 10 (by decide)) hG.hg30) (CZm.mul f19 f7)
  have f31 : CZm M (sVal a (vBase fresh 31)) T.Z3b := CZm.trans (mulCore_forces a pl M hpl hplM (vBase fresh 21) (vBase fresh 12) (vBase fresh 31) (mWit fresh 11) (hv 21 (by decide)) (hv 12 (by decide)) (hv 31 (by decide)) (hm 11 (by decide)) hG.hg31) (CZm.mul f21 f12)
  have f32 : CZm M (sVal a (vBase fresh 32)) T.Z3c := CZm.trans (addCore_forces a pl M hpl hplM (vBase fresh 31) (vBase fresh 30) (vBase fresh 32) (aWit fresh 18) (hv 31 (by decide)) (hv 30 (by decide)) (hv 32 (by decide)) (hb 18 (by decide)) hG.hg32) (CZm.add f31 f30)
  exact ⟨f26, f29, f32⟩

/-! ### §6b — the two curves.

⚑ **Both, because the accumulator leg is Step/Tick on Vesta.** A Pallas-only repair would leave
half the recursion boundary on the gate that enforces nothing. -/

/-- ⚑ **`pallasCompleteAddSound_forces`** — the DEPLOYED satisfaction of the 33 sound leg blocks
forces `(X3,Y3,Z3) ≡ rcbTraceZ 15 (P,Q)` mod the real Pallas-base prime `p`. -/
theorem pallasCompleteAddSound_forces (a : Assignment)
    (X1 Y1 Z1 X2 Y2 Z2 fresh : Nat)
    (hX1 : Ranged a X1) (hY1 : Ranged a Y1) (hZ1 : Ranged a Z1)
    (hX2 : Ranged a X2) (hY2 : Ranged a Y2) (hZ2 : Ranged a Z2)
    (hv : ∀ i, i < 33 → Ranged a (vBase fresh i))
    (hm : ∀ k, k < 12 → MulWitRanged a (mWit fresh k))
    (hs : ∀ k, k < 2 → SmulWitRanged a (sWit fresh k))
    (hb : ∀ k, k < 19 → AddSubWitRanged a (aWit fresh k))
    (hG : RcbSat a pLimb (curveB3 : ℤ) X1 Y1 Z1 X2 Y2 Z2 fresh) :
    CZp (sVal a (vBase fresh 26))
        (rcbTraceZ (curveB3 : ℤ) (sVal a X1) (sVal a Y1) (sVal a Z1)
                   (sVal a X2) (sVal a Y2) (sVal a Z2)).X3g
    ∧ CZp (sVal a (vBase fresh 29))
        (rcbTraceZ (curveB3 : ℤ) (sVal a X1) (sVal a Y1) (sVal a Z1)
                   (sVal a X2) (sVal a Y2) (sVal a Z2)).Y3f
    ∧ CZp (sVal a (vBase fresh 32))
        (rcbTraceZ (curveB3 : ℤ) (sVal a X1) (sVal a Y1) (sVal a Z1)
                   (sVal a X2) (sVal a Y2) (sVal a Z2)).Z3c :=
  hG.apply (pN : ℤ) (by decide) pLimb_bounds pLimb_recomposes
    hX1 hY1 hZ1 hX2 hY2 hZ2 hv hm hs hb

/-- ⚑ **`vestaCompleteAddSound_forces`** — the same at the Vesta-base / Pallas-scalar prime `q`. -/
theorem vestaCompleteAddSound_forces (a : Assignment)
    (X1 Y1 Z1 X2 Y2 Z2 fresh : Nat)
    (hX1 : Ranged a X1) (hY1 : Ranged a Y1) (hZ1 : Ranged a Z1)
    (hX2 : Ranged a X2) (hY2 : Ranged a Y2) (hZ2 : Ranged a Z2)
    (hv : ∀ i, i < 33 → Ranged a (vBase fresh i))
    (hm : ∀ k, k < 12 → MulWitRanged a (mWit fresh k))
    (hs : ∀ k, k < 2 → SmulWitRanged a (sWit fresh k))
    (hb : ∀ k, k < 19 → AddSubWitRanged a (aWit fresh k))
    (hG : RcbSat a qLimb (curveB3 : ℤ) X1 Y1 Z1 X2 Y2 Z2 fresh) :
    CZq (sVal a (vBase fresh 26))
        (rcbTraceZ (curveB3 : ℤ) (sVal a X1) (sVal a Y1) (sVal a Z1)
                   (sVal a X2) (sVal a Y2) (sVal a Z2)).X3g
    ∧ CZq (sVal a (vBase fresh 29))
        (rcbTraceZ (curveB3 : ℤ) (sVal a X1) (sVal a Y1) (sVal a Z1)
                   (sVal a X2) (sVal a Y2) (sVal a Z2)).Y3f
    ∧ CZq (sVal a (vBase fresh 32))
        (rcbTraceZ (curveB3 : ℤ) (sVal a X1) (sVal a Y1) (sVal a Z1)
                   (sVal a X2) (sVal a Y2) (sVal a Z2)).Z3c :=
  hG.apply (qN : ℤ) (by decide) qLimb_bounds qLimb_recomposes
    hX1 hY1 hZ1 hX2 hY2 hZ2 hv hm hs hb

/-! ## §7 — ⚑ THE PRICE, MEASURED ON THE EMITTED OBJECT.

⚠ **Every figure below is a re-derivation, not an inheritance.** Three prices for this row are on
record and they disagree:

| source | constraints | columns |
|---|---|---|
| `PastaMsmBucketed` §7.2 / `PastaMsmLayouts` | `≈1.6 · 10⁴` | — |
| `Dregg2.lean:1670` / `PastaMsmBucketed` §6d `soundRcbConstraintsHigh` | `4 470` | `442 → 2 980` |
| `PastaMsmBucketed` §6d `soundRcbConstraintsLow` | `3 862` | — |
| **this file, on the built descriptor** | **`4 476`** | **`496 → 3 048`** |

The `1.6 · 10⁴` is an estimate for *"a 13-bit/20-limb shape nobody built"* and §6d already retired
it. The interesting one is `4 470`, which lands within **0.13%** of the truth — ⚑ **by two
compensating errors of opposite sign**, which is exactly the reading a single close number hides:

* `14 · 189 + 19 · 96` prices BOTH constant-multiplies at the full multiply's marginal `189`.
  The real `smulCore` is `96`. That over-charges by `2 · 93 = 186`.
* …and it omits the six INPUT limb blocks entirely, `6 · 32 = 192`.

`192 − 186 = +6`, and `4 470 + 6 = 4 476`. The `13.6%` spread §6d reports between its High and Low
readings is settled in favour of High: `96` is right and `64` is not, because the result block's
range lookup is what the NEXT op's `hz`/`hx` hypothesis consumes — drop it and
`addsub_gates_force_congruence` has no premise.

The COLUMN figure is the one that actually moved: `2 980 → 2 856`, `124 = 2 · 62` fewer — the two
constant-multiplies' 62-wide carry blocks that the multiply-shaped pricing charged for and a linear
identity does not need. -/

/-- The bridge from the emitted constraint list's length to a per-leg sum, so the counts below can
be decided WITHOUT normalising 1 428 gate bodies through the `Head` builder. (`rfl` on the fully
normalised list proves the same thing and costs 17× more; the arithmetic is identical because
`lowerAirLegs` is a `flatMap`.) -/
theorem lowered_length (name : String) (w pi : Nat) (air : EffectAir) :
    (lowerAir name w pi [] air).constraints.length
      = (air.legs.map (fun l => (Dregg2.Circuit.Emit.EffectLower.lowerLeg l).length)).sum := by
  unfold lowerAir Dregg2.Circuit.Emit.EffectLower.assemble
    Dregg2.Circuit.Emit.EffectLower.lowerAirLegs
  simp [List.length_flatMap]

/-- ⚑ **THE MEASURED COST OF A STANDALONE SOUND PALLAS COMPLETE ADD: 4 476 constraints.**

`6·32` input lookups `+ 12·189` multiplies `+ 2·96` constant-multiplies `+ 19·96` add/subs. -/
theorem pallasCompleteAddSoundDesc_constraint_count :
    pallasCompleteAddSoundDesc.constraints.length = 4476 := by
  rw [pallasCompleteAddSoundDesc_eq_lowerAir, lowered_length]; decide

theorem vestaCompleteAddSoundDesc_constraint_count :
    vestaCompleteAddSoundDesc.constraints.length = 4476 := by
  rw [vestaCompleteAddSoundDesc_eq_lowerAir, lowered_length]; decide

/-- …and the declared width. -/
theorem pallasCompleteAddSoundDesc_width : pallasCompleteAddSoundDesc.traceWidth = 3048 := rfl
theorem vestaCompleteAddSoundDesc_width : vestaCompleteAddSoundDesc.traceWidth = 3048 := rfl

/-- The four op prices, as the terms the total decomposes into. -/
def SOUND_MUL_MARGINAL : Nat := NG + SK + SK + (NG - 1)
def SOUND_ADDSUB_MARGINAL : Nat := NA + SK + 1 + (NA - 1)
def SOUND_SMUL_MARGINAL : Nat := SK + SK + 1 + (SK - 1)
def SOUND_INPUT_BLOCKS : Nat := 6 * SK

/-- ⚑ **THE CONSTANT MULTIPLY IS ADD/SUB-PRICED, NOT MULTIPLY-PRICED** — `96`, not `189`. This is
the assumption `PastaMsmBucketed.lean:1206-1208` flagged as *"an over-estimate of unknown size"*;
the size is **93 constraints and 62 columns per constant-multiply.** -/
theorem smul_is_not_multiply_priced :
    SOUND_SMUL_MARGINAL = 96
      ∧ SOUND_MUL_MARGINAL = 189
      ∧ SOUND_ADDSUB_MARGINAL = 96
      ∧ SOUND_MUL_MARGINAL - SOUND_SMUL_MARGINAL = 93
      ∧ (smulCore pLimb (curveB3 : ℤ)).width + 62 = (mulCore pLimb).width := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **THE TOTAL, DECOMPOSED** — so the 4 476 is a sum of named op prices rather than a number
read off a build. -/
theorem rcb_price_decomposes :
    SOUND_INPUT_BLOCKS + 12 * SOUND_MUL_MARGINAL + 2 * SOUND_SMUL_MARGINAL
        + 19 * SOUND_ADDSUB_MARGINAL = 4476
      ∧ 12 * SOUND_MUL_MARGINAL + 2 * SOUND_SMUL_MARGINAL
        + 19 * SOUND_ADDSUB_MARGINAL = 4284 := by
  constructor <;> decide

/-- ⚑ **AND THE IN-TREE FIGURE'S TWO ERRORS CANCEL TO 6.** Stated as a theorem because the
near-agreement is the trap: `4 470` is close to `4 476` and is not a correct derivation of it. -/
theorem the_in_tree_figure_is_right_for_two_wrong_reasons :
    14 * SOUND_MUL_MARGINAL + 19 * SOUND_ADDSUB_MARGINAL = 4470
      ∧ 2 * (SOUND_MUL_MARGINAL - SOUND_SMUL_MARGINAL) = 186
      ∧ SOUND_INPUT_BLOCKS = 192
      ∧ 4470 + SOUND_INPUT_BLOCKS - 2 * (SOUND_MUL_MARGINAL - SOUND_SMUL_MARGINAL) = 4476 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **THE COLUMN FIGURE, AND THE 124 THAT COME OFF IT.** `Dregg2.lean` prices the scratch block
at `442 → 2 980`; it is `2 856`, and the difference is exactly the two constant-multiplies' 62-wide
carry blocks. Total width `496 → 3 048`, so the row is **6.15×** wide, not 6.7×. -/
theorem rcb_columns_measured :
    RCB_FRESH = 2856
      ∧ 2980 - RCB_FRESH = 2 * (NG - 1)
      ∧ RCB_WIDTH = 3048
      ∧ 6 * 496 < RCB_WIDTH ∧ RCB_WIDTH < 7 * 496 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **135.6× the gate it replaces**, on the two objects rather than on an estimate: the unsound
row is `PastaCurveComplete.pallasCompleteAddDesc`, 33 constraints and 496 columns. -/
theorem sound_rcb_against_the_unsound_one :
    Dregg2.Circuit.Emit.PastaCurveComplete.pallasCompleteAddDesc.constraints.length = 33
      ∧ Dregg2.Circuit.Emit.PastaCurveComplete.pallasCompleteAddDesc.traceWidth = 496
      ∧ 135 * 33 < 4476 ∧ 4476 < 136 * 33 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §7b — ⚑⚑ AGAINST UPSTREAM, GADGET BY GADGET (read at source, 2026-08-06,
`~/dev/proof-systems` HEAD `f6d958dc`).

**The row above is 4 476 constraints and 3 048 columns. Kimchi does a complete addition in ONE row
of a fifteen-column grid, 11 cells and 7 constraints** (`kimchi/src/circuits/polynomials/
complete_add.rs:4-16` layout, `:101` `CONSTRAINTS = 7`). Some of that gap is forced and some of it
is ours, and the two have to be told apart or the number means nothing.

### NECESSARY — a consequence of BabyBear simulating Pasta, not of a choice made here

Kimchi's curve gates do their arithmetic in the **native** proving field: a Kimchi proof over Vesta
has constraint field `Fp = Pallas::BaseField` (`curves/src/pasta/curves/pallas.rs:21-23`), so a
Pallas point is literally two witness cells and a slope is one. There are no limbs, no range checks
and no lookups anywhere in `complete_add.rs`, `varbasemul.rs`, `endosclmul.rs` or
`endomul_scalar.rs`. **That is the Pasta 2-cycle, and we do not have one**: a BabyBear STARK
verifying Mina must simulate a 255-bit field in a 31-bit one, and `capacity_covers_pasta` /
`felt_gates_force_congruence` are what that costs. This term is not recoverable by any layout.

⚑ **AND KIMCHI'S OWN FOREIGN-FIELD TRICK DOES NOT PORT, for a reason that is arithmetic.**
`foreign_field_mul` is 2 gate rows and 11 constraints because its constraint C5
(`foreign_field_mul/circuitgates.rs:338-342`) discharges the *entire upper half* of the product in
ONE native identity — `a_n·b_n + q_n·f'_n − r_n − q_n·2^264 = 0` — which works because a whole
255-bit value fits one native element, so `2^264 · n ≥ f²`. At `n = P = 2 013 265 921` that leg
carries **31 bits, not 255**: closing `2^t · n ≥ 2^510` needs `t ≥ 479`, i.e. sixty 8-bit limbs of
binary modulus, which IS the schoolbook this file emits. `PastaFieldSound`'s header reaches the same
place from the other side (the CRT-over-small-moduli variant is expressible and strictly worse), and
this is the independent confirmation.

Likewise `varbasemul`'s headline trick — never witnessing the intermediate point's Y-coordinate,
4 constraints per bit (`varbasemul.rs:108-117`) — is bought with a **degree-6** constraint
(`varbasemul.rs:245-260`, cleared by multiplying through by `t²`). Our per-limb gates are degree 2,
so the intermediate has to be materialised. Not portable.

### AVOIDABLE — and the largest one is that this row is PROJECTIVE

⚑ **RCB Alg. 7 exists to avoid an inversion. A circuit does not need to avoid inversions.**
`docs/MINA-KIMCHI-VERIFIER-PLAN.md:61-70` chose between three *Explicit-Formulas-Database* entries —
naive Jacobian doubling, `add-2007-bl`, `add-2015-rcb` — whose cost model is "a field inversion is
expensive". In a constraint system an inversion is a **witnessed column plus one multiplication
check**, which is exactly what Kimchi does: `zero_check(x21, x21_inv, same_x)`
(`complete_add.rs:28-37`) is `z_inv·z = 1 − r` and `r·z = 0`, two degree-2 constraints, and it
delivers the `x1 = x2` indicator for free. Completeness is then one degree-3 multiplexed slope
constraint (`complete_add.rs:138-144`) rather than a strongly-unified formula.

Ported into this file's own op vocabulary — the same `mulCore`/`smulCore`/`addSubCore` at the same
`SOUND_MUL_MARGINAL = 189`, `SOUND_SMUL_MARGINAL = SOUND_ADDSUB_MARGINAL = 96` — an affine complete
add is **7 multiplies, 1 constant-multiply, ~12 add/subs and 5 boolean-selected limb blocks**
against this file's **12 + 2 + 19**: roughly `2 957` constraints and `1 908` columns, `1.5×` and
`1.6×` under the projective row. ⚠ That is a DERIVATION off the op census, not a measurement, and
nothing here proves such a gadget sound; what is measured is that the thing being avoided (an
inversion) is not expensive in the setting this row lives in.

⚑ **AND THE 19 ADD/SUBS ARE 40.8% OF THE ROW, spent reducing intermediates Kimchi does not
reduce.** `19 · SOUND_ADDSUB_MARGINAL = 1 824` of `4 476`, and `19 · 64 = 1 216` of `3 048` columns
(witness plus result block). Kimchi's `foreign_field_add` chains additions *without* a per-op
reduction and bounds only at the end of the chain (`book/docs/kimchi/foreign_field_add.md:378-386`).
The enabler here is arithmetic and it is already on disk: `PastaFieldSound.digitVal_abs_le` bounds
the coefficient body by the **whole 1 024-pair product list** where the antidiagonal is `≤ 32` long,
so the gate body is charged `141 592 831` (7.0% of `P`) against a tight `≈12 583 231` (0.63%). The
crude bound leaves `14.2×` of headroom under `P`; the antidiagonal one leaves **`160×`, i.e. 7.3
bits** — `3.5` bits more, and enough for the RCB DAG's add depth including the `b3 = 15`
constant-multiply's `3.9`. That is a strictly TIGHTER theorem, not a weaker one, and it is the
prerequisite rather than the saving.

### AND THE THIRD LEVER IS NOT IN THIS FILE AT ALL

`3 048` is the DECLARED width; the prover commits `10 756`, because `MainLayout::build` compiles
every declared range lookup into a nibble aux block at `LIMB_BITS = 4` — a sixteen-row byte table,
one aux column per FOUR bits. **71.7% of the committed row is range-check decomposition.** Kimchi
range-checks against a 4 096-row table (`kimchi/src/circuits/lookup/tables/range_check.rs:11`,
`RANGE_CHECK_UPPERBOUND = 1 << 12`). Measured in `circuit-prove/tests/mina_accumulator_leaf_anatomy.
rs::the_wrap_cost_tracks_committed_width_not_declared_width`: at radix 8 the aux block HALVES
(`7 708 → 3 873`), and 12/16 are worse because `eval_decomp`'s partial-top-limb path bit-decomposes
a value narrower than one limb. `ByteTableEmit.gates_admit_every_height` already records that the
table AIR does not bound its own height — the pin is `verify_vm_descriptor2`'s — so the radix is one
constant and a VK epoch, with no descriptor and no witness re-emit.
-/

/-! ## §8 — the HONEST witness, generated HERE (Rust fills cells, it does not author them).

`PastaFieldSound` §8's rule, at the row scale: the 3 048 cells of an honest complete-add row are
computed in Lean from `PastaCurveComplete.rcbTraceM` — the SAME per-op-reduced `Nat` reference the
unsound gadget's KAT uses — and the emit driver renders them. The Rust test parses felts.

The per-op value tables below are DERIVED from the same op table `swCompleteAddSoundLegs` walks, so
a slip between the gate layout and the witness layout is a Lean error, not a silent wrong cell. -/

/-- The 12 multiplies `(x, y, z)` in `mWit` index order. -/
def mulVals (I G : Nat → Nat) : List (Nat × Nat × Nat) :=
  [ (I 0, I 3, G 0), (I 1, I 4, G 1), (I 2, I 5, G 2),
    (G 3, G 4, G 5), (G 8, G 9, G 10), (G 13, G 14, G 15),
    (G 12, G 23, G 24), (G 7, G 22, G 25), (G 23, G 19, G 27),
    (G 22, G 21, G 28), (G 19, G 7, G 30), (G 21, G 12, G 31) ]

/-- The 2 constant multiplies `(x, z)` in `sWit` index order. -/
def smulVals (I G : Nat → Nat) : List (Nat × Nat) := [ (G 2, G 20), (G 17, G 23) ]

/-- The 19 add/subs `(isSub, x, y, z)` in `aWit` index order. -/
def addSubVals (I G : Nat → Nat) : List (Bool × Nat × Nat × Nat) :=
  [ (false, I 0, I 1, G 3), (false, I 3, I 4, G 4),
    (false, G 0, G 1, G 6), (true, G 5, G 6, G 7),
    (false, I 1, I 2, G 8), (false, I 4, I 5, G 9),
    (false, G 1, G 2, G 11), (true, G 10, G 11, G 12),
    (false, I 0, I 2, G 13), (false, I 3, I 5, G 14),
    (false, G 0, G 2, G 16), (true, G 15, G 16, G 17),
    (false, G 0, G 0, G 18), (false, G 18, G 0, G 19),
    (false, G 1, G 20, G 21), (true, G 1, G 20, G 22),
    (true, G 25, G 24, G 26), (false, G 28, G 27, G 29),
    (false, G 31, G 30, G 32) ]

/-- The 33 SSA intermediates of `rcbTraceM`, in the gadget's allocation order. -/
def rcbVals (M b3 X1v Y1v Z1v X2v Y2v Z2v : Nat) : List Nat :=
  let t := Dregg2.Circuit.Emit.PastaCurveComplete.rcbTraceM M b3 X1v Y1v Z1v X2v Y2v Z2v
  [t.t0a, t.t1a, t.t2a, t.t3a, t.t4a, t.t3b, t.t4b, t.t3c, t.t4c, t.X3a, t.t4d, t.X3b, t.t4e,
   t.X3c, t.Y3a, t.X3d, t.Y3b, t.Y3c, t.X3e, t.t0b, t.t2b, t.Z3a, t.t1b, t.Y3d, t.X3f, t.t2c,
   t.X3g, t.Y3e, t.t1c, t.Y3f, t.t0c, t.Z3b, t.Z3c]

/-- A local `(x, z, q)` assignment for the constant multiply, so its carry chain can be generated
by the same recursion the multiply's and the add/sub's use. -/
def smLimbs (Xv Zv Qv : Nat) : Assignment := fun col =>
  if col < SK then limbAt Xv col
  else if col < 2 * SK then limbAt Zv (col - SK)
  else if col = 2 * SK then (Qv : ℤ)
  else 0

/-- The honest constant-multiply carry chain: `S 0 = 0`, `S (m+1) = (S m + T m) / 2^SB`. Every
division is exact BECAUSE the integer body is zero — that is the content, not a convenience. -/
def smCarryOf (Xv Zv Qv : Nat) (pl : Nat → ℤ) (cx : ℤ) : Nat → ℤ
  | 0 => 0
  | (m + 1) =>
      (smCarryOf Xv Zv Qv pl cx m
        + smDigit (smLimbs Xv Zv Qv) 0 SK (2 * SK) pl cx m) / (2 : ℤ) ^ SB

/-- The `SK` limbs of a value. -/
def limbBlock (v : Nat) : List ℤ := (List.range SK).map (limbAt v)

/-- ⚑ **THE HONEST ROW** — `RCB_WIDTH` cells: six input blocks, 33 intermediates, then the twelve
multiply witnesses, the two constant-multiply witnesses and the nineteen add/sub witnesses, in the
gadget's own allocation order. -/
def rcbSoundRow (M b3 : Nat) (pl : Nat → ℤ) (X1v Y1v Z1v X2v Y2v Z2v : Nat) : List ℤ :=
  let ins : List Nat := [X1v, Y1v, Z1v, X2v, Y2v, Z2v]
  let vs := rcbVals M b3 X1v Y1v Z1v X2v Y2v Z2v
  let I : Nat → Nat := fun i => ins.getD i 0
  let G : Nat → Nat := fun i => vs.getD i 0
  (ins.flatMap limbBlock)
  ++ (vs.flatMap limbBlock)
  ++ ((mulVals I G).flatMap (fun t =>
        let xv := t.1; let yv := t.2.1; let zv := t.2.2
        let qv := (xv * yv - zv) / M
        limbBlock qv
        ++ (List.range (NG - 1)).map (fun i => carryOf xv yv zv qv pl (i + 1) + COFF)))
  ++ ((smulVals I G).flatMap (fun t =>
        let xv := t.1; let zv := t.2
        let qv := (b3 * xv - zv) / M
        (qv : ℤ)
          :: (List.range (SK - 1)).map (fun i => smCarryOf xv zv qv pl (b3 : ℤ) (i + 1) + COFF)))
  ++ ((addSubVals I G).flatMap (fun t =>
        let isSub := t.1; let xv := t.2.1; let yv := t.2.2.1; let zv := t.2.2.2
        let cv : ℤ := if isSub then ((zv + yv - xv) / M : Nat) else ((xv + yv - zv) / M : Nat)
        let sy : ℤ := if isSub then -1 else 1
        let sc : ℤ := if isSub then 1 else -1
        cv :: (List.range (NA - 1)).map
                (fun i => adCarryOf xv yv zv cv pl sy sc (i + 1) + ACOFF)))

/-- The honest Pallas row at `G + G` — the DOUBLING case, so strong unification is exercised and the
row is the one `PastaCurveComplete`'s own KAT doubles with. -/
def pallasHonestRow : List ℤ :=
  rcbSoundRow pN Dregg2.Circuit.Emit.PastaCurveComplete.curveB3 pLimb
    Dregg2.Circuit.Emit.PastaCurve.Gp.1 Dregg2.Circuit.Emit.PastaCurve.Gp.2 1
    Dregg2.Circuit.Emit.PastaCurve.Gp.1 Dregg2.Circuit.Emit.PastaCurve.Gp.2 1

/-- The honest Vesta row at `G + G`. -/
def vestaHonestRow : List ℤ :=
  rcbSoundRow qN Dregg2.Circuit.Emit.PastaCurveComplete.curveB3 qLimb
    Dregg2.Circuit.Emit.PastaCurve.Gv.1 Dregg2.Circuit.Emit.PastaCurve.Gv.2 1
    Dregg2.Circuit.Emit.PastaCurve.Gv.1 Dregg2.Circuit.Emit.PastaCurve.Gv.2 1

#assert_axioms sm_recompose
#assert_axioms smDigit_abs_le
#assert_axioms smBody_abs_lt_P
#assert_axioms smBody_bound_value
#assert_axioms smul_gates_force_congruence
#assert_axioms smExpr_eval
#assert_axioms mulCore_legs_are_the_gates
#assert_axioms smulCore_legs_are_the_gates
#assert_axioms mulCore_forces
#assert_axioms addCore_forces
#assert_axioms subCore_forces
#assert_axioms smulCore_forces
#assert_axioms RcbSat.apply
#assert_axioms pallasCompleteAddSound_forces
#assert_axioms vestaCompleteAddSound_forces
#assert_axioms pallasCompleteAddSoundAir_mainRailOk
#assert_axioms vestaCompleteAddSoundAir_mainRailOk
#assert_axioms lowered_length
#assert_axioms pallasCompleteAddSoundDesc_constraint_count
#assert_axioms vestaCompleteAddSoundDesc_constraint_count
#assert_axioms smul_is_not_multiply_priced
#assert_axioms rcb_price_decomposes
#assert_axioms the_in_tree_figure_is_right_for_two_wrong_reasons
#assert_axioms rcb_columns_measured
#assert_axioms sound_rcb_against_the_unsound_one

/-! ## §9 — ⚑ THE `smul` LADDER: what is no longer blocked, and what now is.

`MinaWrapXiScalarWeld` named "no sound `smul` core" alongside "no sound complete-add". Two different
things wear that name and this file settles them differently.

**The CONSTANT multiply** — `swCompleteAddGadget`'s `smulC` parameter, RCB's two `b3 = 15` ops — did
not exist and now does (§3). That one is closed.

**The scalar-mul LADDER** (`PastaScalarMul.ladderStep`, `[k]P`) is where an MSM row's price actually
lives, and it is NOT closed. ⚑ **But it is no longer blocked by a TYPE obstruction.** `ladderStep`
hardcodes `pallasCompleteAdd` and the `9×30` layout's `+234/+261/+288/+442` offsets; it needs
exactly the parametrisation `swCompleteAddGadget` needed, and the `SoundCore` bridge supplies it —
a sound step is two `swCompleteAddSoundLegs` calls at `RCB_FRESH` stride.

⚑ **WHAT BLOCKS IT IS THE LAYOUT, AND THE NUMBER SAYS SO.** `PastaMsmAir.ladderGatesFrom_counts`
proves the ladder is ROW-LOCAL: `66·n` gates and `884·n` FRESH COLUMNS, all in ONE row. On the sound
gate a step is `2 · 4 284 = 8 568` constraints and `2 · 2 856 = 5 712` columns, so a 128-step GLV
joint ladder is **731 136 columns in a single row** — against the deployed `pasta_derive_prove`
measuring 2 131. The unsound ladder is `113 152` columns at the same depth: implausible already, and
6.5× smaller.

So a sound ladder needs the accumulator threaded ACROSS rows through an `AirLeg.window .transition`
gate — a layout the existing ladder also lacks and has never had. That is a real next step and a
buildable one; it is not a type obstruction, and it is not a cost estimate standing in for a
constraint. -/

/-- One sound ladder step = double + add = two chained complete adds. -/
def SOUND_LADDER_STEP_CONSTRAINTS : Nat :=
  2 * (12 * SOUND_MUL_MARGINAL + 2 * SOUND_SMUL_MARGINAL + 19 * SOUND_ADDSUB_MARGINAL)
/-- …and its fresh columns. -/
def SOUND_LADDER_STEP_COLUMNS : Nat := 2 * RCB_FRESH
/-- The GLV joint ladder's depth (two ~128-bit halves, Shamir). -/
def GLV_STEPS : Nat := 128

/-- ⚑ **THE ROW-LOCALITY WALL, as a number rather than a worry.** -/
theorem sound_ladder_does_not_fit_a_row :
    SOUND_LADDER_STEP_CONSTRAINTS = 8568
      ∧ SOUND_LADDER_STEP_COLUMNS = 5712
      ∧ GLV_STEPS * SOUND_LADDER_STEP_COLUMNS = 731136
      ∧ GLV_STEPS * SOUND_LADDER_STEP_CONSTRAINTS = 1096704
      -- the unsound ladder at the same depth: `884 · n` fresh columns
      -- (`PastaMsmAir.ladderGatesFrom_counts`), so the sound one is 6.46× wider.
      ∧ 6 * (GLV_STEPS * 884) < GLV_STEPS * SOUND_LADDER_STEP_COLUMNS
      ∧ GLV_STEPS * SOUND_LADDER_STEP_COLUMNS < 7 * (GLV_STEPS * 884) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

#assert_axioms sound_ladder_does_not_fit_a_row

/-! ## §10 — ⚑⚑ THE ADOPTION: the certified SCHWARTZ–ZIPPEL body, swapped into this row.

§"WHY THE SCHOOLBOOK AND NOT SCHWARTZ–ZIPPEL" named the remaining work exactly — *"swapping each
multiply core's 63 gate legs for two relocated challenge gates (`szBodyAt` at the core's bases) and
restating the composed `_forces` theorems with `holdsIn`-at-a-draw hypotheses plus a per-row
non-exceptionality disjunction — a statement-shape change for the whole row, not a leg splice."*
This is that change, and `PastaSzMul`'s theorems are stated at GENERAL bases (`szBodyAt pl zi xB yB
zB qB cB`) precisely so it is a relocation and not a re-proof.

⚑ **THE STATEMENT SHAPE IS THE WORK, AND IT MOVES IN THREE PLACES.**

1. **The carrier.** The schoolbook's `MulSat` is `P ∣ (gate body).eval a` — a fact about ONE
   BabyBear lane, over an `Assignment`. The sz gate's DEPLOYED reading is
   `ChalConstraint.holdsIn env z isLast` — the `assert_zero_ext` denotation over an arbitrary
   `CommRing K`, which the deployed prover instantiates at `BinomialExtensionField<BabyBear,4>`.
   Stating it on the base lane would silently price the draw at `2^31` instead of `2^123.63`; the
   identity-carrier lesson, so the hypothesis carrier is `VmRowEnv` plus a draw `z : Nat → K`.
2. **The disjunction.** Each relocated multiply carries its own NON-EXCEPTIONALITY hypothesis —
   `z CHAL_Z` or `z CHAL_Z2` outside that multiply's residual's `≤ 62`-root exceptional set. That
   is the ONLY place randomness enters this file, it is a hypothesis and not a lemma, and
   `PastaSzMul` §6d is where it is priced. `sz_single_challenge_is_below_the_bar` is a theorem that
   ONE draw unions to `2^−98.5` across the wrap workload — below this repo's ~124-bit bar — which is
   why `szMulCore` carries TWO challenge gates and why the single-challenge form is not offered
   here at all.
3. **`felt_gates_force_congruence` is UNCHANGED and still terminal.** `szPoly_forces_congruence`
   discharges into it. The swap is which certified body feeds it, exactly as the header said.

⚑ **AND SAY WHAT IT BUYS, IN THE RIGHT CURRENCY.** `4 476 → 3 744` constraints (`12 × 61`), and
`12 × 2 206 → 12 × 442` multiplication nodes in the emitted bodies. **The declared width does not
move: `3 048` before and `3 048` after**, and neither does the range-lookup count — `szMulCore.width
= mulCore.width` by `rfl`, and the three limbs legs are the same three. `PastaSzMul`'s
`width_and_lookups_unchanged` says this one op at a time; `szRcbWidthIsUnchanged` below says it for
the composed row. **Anyone selling this as a trace-size win is quoting the wrong currency:** the
committed row is `10 756` cells of which 71.7% is range decomposition, and none of that moved.

⚠ **WHAT THE DRAW RESTS ON, AND IT IS NOT PROVED HERE OR ANYWHERE.** That the two challenges are
uniform, post-commitment and drawn from the quartic extension is READ off pinned Plonky3 `82cfad7`
(`p3-batch-stark/src/{prover,transcript}.rs`), cited in `DescriptorIR2` §2.6, and modelled by
nothing. `chalIndicesDistinctOk` is the decidable half of it — the `(α, β)` of ONE lookup context,
the only pairing the measured sampler guarantees — and it is discharged on the emitted objects
below at `(0, 1)`. The probability that a drawn point is non-exceptional is the one thing a
Schwartz–Zippel argument NEVER discharges; it enters every theorem below as a HYPOTHESIS.

⚠ **BOTH ROWS STAY EMITTED, and that is not a compatibility hedge.** They are two AIRs with two
DIFFERENT soundness ledgers: the schoolbook row forces the congruence unconditionally given the
range legs, the sz row forces it at `1 − 2^−197.0` over the draw. A reader who needs the
unconditional statement uses `pallasCompleteAddSoundDesc`; a reader who wants the cheap one uses
`pallasCompleteAddSzDesc` and inherits the ledger. The before/after cost comparison is a
measurement ON THE PAIR, which is the second reason both exist. -/

section SzAdoption

open Dregg2.Circuit.DescriptorIR2
  (ChalExpr ChalConstraint challengeCount chalGateCount chalIndicesDistinctOk)
open Dregg2.Circuit.EffectAirIR (ChalLeg)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.OodQuotientConsistency (exceptionalSet)
open Dregg2.Circuit.Emit.PastaSzMul
  (CHAL_Z CHAL_Z2 szBodyAt szResidual szGate_holdsIn_forces_congruence chalMuls schoolbookMuls)

/-! ### §10a — the core. -/

/-- ⚑ **THE SCHWARTZ–ZIPPEL MULTIPLY AS A `SoundCore`** — the SAME columns, the SAME three range
lookups, the SAME private-witness width as `mulCore`, and TWO relocated challenge gates where the
schoolbook has 63 coefficient gates. `szBodyAt` is `PastaSzMul`'s emitted body at arbitrary block
bases, which is why this is a relocation of a proved object and not a second authoring of it.

⚑ The witness block is `(wB, wB + SK)` — quotient limbs then the 62 OFFSET-ENCODED carries — read
by `szBodyAt`'s `hornerChalOff` at `COFF`, i.e. the same cells `mulCore`'s `coefExpr` reads and the
same cells `rcbSoundRow` (§8) already writes. **The honest witness generator does not move.** -/
def szMulCore (pl : Nat → ℤ) : SoundCore :=
  { legs := fun xB yB zB wB =>
      [ AirLeg.chal ⟨.all, szBodyAt pl CHAL_Z  xB yB zB wB (wB + SK)⟩
      , AirLeg.chal ⟨.all, szBodyAt pl CHAL_Z2 xB yB zB wB (wB + SK)⟩
      , AirLeg.limbs ⟨limbCols zB, SB, rangeTidW SB⟩
      , AirLeg.limbs ⟨limbCols wB, SB, rangeTidW SB⟩
      , AirLeg.limbs ⟨carryCols (wB + SK), CB, rangeTidW CB⟩ ]
  , width := SK + (NG - 1) }

/-- ⚑ **THE WITNESS BLOCK IS BYTE-IDENTICAL** — same width, so `mWit`/`sWit`/`aWit`, `RCB_FRESH`
and `rcbSoundRow` are unchanged and the emitted honest row of §8 is the honest row of BOTH AIRs. -/
theorem szMulCore_width_unchanged (pl : Nat → ℤ) :
    (szMulCore pl).width = (mulCore pl).width := rfl

/-- ⚑ **AND THE THREE RANGE LOOKUPS ARE THE SAME THREE.** The carries survive Schwartz–Zippel:
lifting `𝔽_p[X] → ℤ[X]` needs the same per-coefficient felt-fitting bound the schoolbook needed. -/
theorem szMulCore_keeps_the_lookups (pl : Nat → ℤ) (xB yB zB wB : Nat) :
    ((szMulCore pl).legs xB yB zB wB).filter (fun l => match l with | .limbs _ => true | _ => false)
      = ((mulCore pl).legs xB yB zB wB).filter
          (fun l => match l with | .limbs _ => true | _ => false) := by
  simp [szMulCore, mulCore, List.filter_append, List.filter_map]

/-- The gate legs collapse `63 → 2`, on the cores themselves. -/
theorem szMulCore_gate_collapse (pl : Nat → ℤ) (xB yB zB wB : Nat) :
    ((mulCore pl).legs xB yB zB wB).length = 66
      ∧ ((szMulCore pl).legs xB yB zB wB).length = 5 := ⟨rfl, rfl⟩

/-! ### §10b — the emitted rows. The gadget is generic over `SoundCore`, so this is an
instantiation and not a second layout: the same 33 ops in the same SSA order at the same bases. -/

def pallasCompleteAddSzLegs : Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    List AirLeg × (Nat × Nat × Nat) × Nat :=
  swCompleteAddSoundLegs (szMulCore pLimb) (addSubCore pLimb 1 (-1)) (addSubCore pLimb (-1) 1)
    (smulCore pLimb (curveB3 : ℤ))

def vestaCompleteAddSzLegs : Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    List AirLeg × (Nat × Nat × Nat) × Nat :=
  swCompleteAddSoundLegs (szMulCore qLimb) (addSubCore qLimb 1 (-1)) (addSubCore qLimb (-1) 1)
    (smulCore qLimb (curveB3 : ℤ))

/-- ⚑ **THE LAYOUT IS THE SCHOOLBOOK ROW'S, COLUMN FOR COLUMN.** Same `fresh` arithmetic, same
result bases, same next-free column — so a witness for one row is a witness for the other and the
cost comparison is about two AIRs over ONE trace shape. -/
theorem szLegs_layout_unchanged (X1 Y1 Z1 X2 Y2 Z2 fresh : Nat) :
    (pallasCompleteAddSzLegs X1 Y1 Z1 X2 Y2 Z2 fresh).2
      = (pallasCompleteAddSoundLegs X1 Y1 Z1 X2 Y2 Z2 fresh).2 := rfl

def pallasCompleteAddSzAir : EffectAir :=
  { tables := rcbTables
  , legs := inputLimbLegs
      ++ (pallasCompleteAddSzLegs 0 SK (2*SK) (3*SK) (4*SK) (5*SK) IN_BASE).1 }

def vestaCompleteAddSzAir : EffectAir :=
  { tables := rcbTables
  , legs := inputLimbLegs
      ++ (vestaCompleteAddSzLegs 0 SK (2*SK) (3*SK) (4*SK) (5*SK) IN_BASE).1 }

set_option maxHeartbeats 4000000 in
/-- ⚑ **THE COMPILER ACCEPTS BOTH BLOCKS — and for the challenge legs it is a REAL verdict.**
`ChalLeg.mainRailOk` refuses `.first`/`.last` OUTRIGHT (the target's `chalGate` is two-row only)
and refuses an `.all` body that reads `nxt`. All 24 relocated gates are `.all` over bodies that
read no `nxt`, so they have a deployed image; a `.transition`-scoped one would lower to a gate that
fires somewhere else. -/
theorem pallasCompleteAddSzAir_mainRailOk : pallasCompleteAddSzAir.mainRailOk = true := by decide

set_option maxHeartbeats 4000000 in
theorem vestaCompleteAddSzAir_mainRailOk : vestaCompleteAddSzAir.mainRailOk = true := by decide

def pallasCompleteAddSzTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air := pallasCompleteAddSzAir
  ok  := pallasCompleteAddSzAir_mainRailOk

def pallasCompleteAddSzDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-pallas-complete-add-sz::v1" RCB_WIDTH 0 [] pallasCompleteAddSzTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source — including the two
relocated challenge gates of each multiply — is FORCED by the emitted descriptor's constraints on
any row window that satisfies them, stated in the SOURCE's vocabulary. -/
theorem pallasCompleteAddSzDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines pallasCompleteAddSzDesc []
      pallasCompleteAddSzAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-pallas-complete-add-sz::v1" RCB_WIDTH 0 [] pallasCompleteAddSzTiedAir).property

theorem pallasCompleteAddSzDesc_eq_lowerAir :
    pallasCompleteAddSzDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-pasta-pallas-complete-add-sz::v1" RCB_WIDTH 0 [] pallasCompleteAddSzAir := rfl

def vestaCompleteAddSzTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air := vestaCompleteAddSzAir
  ok  := vestaCompleteAddSzAir_mainRailOk

def vestaCompleteAddSzDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-vesta-complete-add-sz::v1" RCB_WIDTH 0 [] vestaCompleteAddSzTiedAir).val

theorem vestaCompleteAddSzDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines vestaCompleteAddSzDesc []
      vestaCompleteAddSzAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-vesta-complete-add-sz::v1" RCB_WIDTH 0 [] vestaCompleteAddSzTiedAir).property

theorem vestaCompleteAddSzDesc_eq_lowerAir :
    vestaCompleteAddSzDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-pasta-vesta-complete-add-sz::v1" RCB_WIDTH 0 [] vestaCompleteAddSzAir := rfl

/-! ### §10c — ⚑ THE PRICE, RE-DERIVED ON THE EMITTED OBJECTS.

⚠ **Nothing here is inherited from `PastaSzMul`'s one-multiply table.** `192 → 128` is that file's
`253 → 192` restated at the composed row's marginal accounting (a chained row does not re-pay for
its operands' limb lookups), and the row total is decided on the built descriptor by the same
`lowered_length` bridge §7 uses. -/

/-- The marginal price of ONE relocated multiply: 2 challenge gates + `32 + 32 + 62` lookups. -/
def SZ_MUL_MARGINAL : Nat := 2 + SK + SK + (NG - 1)

/-- ⚑ **`189 → 128` PER MULTIPLY, and the 61 that come off it are the 63 gates minus the 2.** -/
theorem sz_mul_is_cheaper_by_sixty_one :
    SZ_MUL_MARGINAL = 128
      ∧ SOUND_MUL_MARGINAL - SZ_MUL_MARGINAL = 61
      ∧ SOUND_MUL_MARGINAL - SZ_MUL_MARGINAL = NG - 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑ **THE MEASURED COST OF A STANDALONE SZ PALLAS COMPLETE ADD: 3 744 constraints**, against the
schoolbook row's 4 476. `6·32` input lookups `+ 12·128` multiplies `+ 2·96` constant-multiplies
`+ 19·96` add/subs. -/
theorem pallasCompleteAddSzDesc_constraint_count :
    pallasCompleteAddSzDesc.constraints.length = 3744 := by
  rw [pallasCompleteAddSzDesc_eq_lowerAir, lowered_length]; decide

theorem vestaCompleteAddSzDesc_constraint_count :
    vestaCompleteAddSzDesc.constraints.length = 3744 := by
  rw [vestaCompleteAddSzDesc_eq_lowerAir, lowered_length]; decide

/-- ⚑⚑ **AND THE WIDTH DOES NOT MOVE.** `3 048` before, `3 048` after — the number that decides
trace size and the LDE domain. This theorem is the one that stops the constraint saving being
read as a memory saving. -/
theorem szRcbWidthIsUnchanged :
    pallasCompleteAddSzDesc.traceWidth = 3048
      ∧ vestaCompleteAddSzDesc.traceWidth = 3048
      ∧ pallasCompleteAddSzDesc.traceWidth = pallasCompleteAddSoundDesc.traceWidth := by
  refine ⟨rfl, rfl, rfl⟩

/-- ⚑ **THE TOTAL, DECOMPOSED** — a sum of named op prices, and the 732 it saves is `12 · 61`. -/
theorem sz_rcb_price_decomposes :
    SOUND_INPUT_BLOCKS + 12 * SZ_MUL_MARGINAL + 2 * SOUND_SMUL_MARGINAL
        + 19 * SOUND_ADDSUB_MARGINAL = 3744
      ∧ 4476 - 3744 = 12 * (SOUND_MUL_MARGINAL - SZ_MUL_MARGINAL)
      ∧ 12 * (SOUND_MUL_MARGINAL - SZ_MUL_MARGINAL) = 732 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑ **THE ARITHMETIC, WHICH IS THE CURRENCY THAT ACTUALLY MOVES.** Multiplication nodes in the
twelve multiplies' emitted bodies: `12 · 2 206 = 26 472` for the schoolbook, `12 · 442 = 5 304` for
the two-point sz row — **4.99×** less per-row evaluation arithmetic at the same constraint degree.
Counted by `PastaSzMul`'s own two measures on the two emitted body families, so both sides of the
comparison are counted by one rule. -/
theorem sz_rcb_arithmetic_collapse :
    12 * schoolbookMuls = 26472
      ∧ 12 * (chalMuls (szBodyAt pLimb CHAL_Z X_BASE Y_BASE Z_BASE Q_BASE C_BASE)
              + chalMuls (szBodyAt pLimb CHAL_Z2 X_BASE Y_BASE Z_BASE Q_BASE C_BASE)) = 5304
      ∧ 4 * 5304 < 12 * schoolbookMuls ∧ 12 * schoolbookMuls < 5 * 5304 := by
  refine ⟨by rw [Dregg2.Circuit.Emit.PastaSzMul.schoolbook_arithmetic_is_quadratic], ?_, ?_, ?_⟩
    <;> decide

/-- ⚑ **THE INDEPENDENCE LICENCE, DISCHARGED ON THE EMITTED COMPOSED ROW.** `(CHAL_Z, CHAL_Z2) =
(0, 1)` are the `α` and `β` of the instance's FIRST lookup context — the one pairing the measured
sampler guarantees is two distinct post-commitment draws, and the ONLY pairing
`chalIndicesDistinctOk` licenses. A pairing like `(0, 2)` — same slot, different contexts — is
REFUSED, and rightly: under global-bus sharing those can be the identical value, and every range
limb of this row rides the one byte bus. -/
theorem pallasCompleteAddSzDesc_chal_indices_distinct :
    chalIndicesDistinctOk pallasCompleteAddSzDesc CHAL_Z CHAL_Z2 = true := by
  rw [pallasCompleteAddSzDesc_eq_lowerAir]; decide

theorem vestaCompleteAddSzDesc_chal_indices_distinct :
    chalIndicesDistinctOk vestaCompleteAddSzDesc CHAL_Z CHAL_Z2 = true := by
  rw [vestaCompleteAddSzDesc_eq_lowerAir]; decide

/-- The row declares two challenges and carries 24 challenge gates — twelve multiplies, two draws
each. A descriptor that read a challenge it did not declare is refused by `check_descriptor2`. -/
theorem pallasCompleteAddSzDesc_declares_two_challenges :
    challengeCount pallasCompleteAddSzDesc = 2
      ∧ chalGateCount pallasCompleteAddSzDesc = 24 := by
  rw [pallasCompleteAddSzDesc_eq_lowerAir]
  constructor <;> decide

/-! ### §10d — ⚑ THE COMPOSED FORCING THEOREM, in the new statement shape. -/

/-- ⚑ **ONE RELOCATED MULTIPLY'S DEPLOYED HYPOTHESIS.** The two emitted challenge gates' FAITHFUL
`K`-denotations at the drawn point — what `assert_zero_ext` asserts — plus the non-exceptionality
DISJUNCTION. It is a structure and not a conjunction so that a caller supplying it has to name all
three, and in particular cannot leave the disjunction implicit: that field is where the `2^−197.0`
lives and it is the whole difference from the schoolbook's `MulSat`. -/
structure SzMulAt {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    (env : VmRowEnv) (z : Nat → K) (isLast : Bool) (pl : Nat → ℤ) (xB yB zB wB : Nat) : Prop where
  /-- The gate at the FIRST draw, `permutation_randomness()[0]`. -/
  gateZ  : ChalConstraint.holdsIn env z isLast ⟨szBodyAt pl CHAL_Z  xB yB zB wB (wB + SK), false⟩
  /-- The gate at the SECOND draw, `permutation_randomness()[1]` — the same context's `β`. -/
  gateZ2 : ChalConstraint.holdsIn env z isLast ⟨szBodyAt pl CHAL_Z2 xB yB zB wB (wB + SK), false⟩
  /-- ⚑ EITHER draw lands outside this multiply's residual's `≤ 62`-root exceptional set. Failing
  BOTH is the event `sz_two_point_clears_the_bar` prices at `2^−197.0`. -/
  nonexc :
    z CHAL_Z ∉ exceptionalSet
        ((szResidual env.loc xB yB zB wB (wB + SK) pl).map (Int.castRingHom K))
      ∨ z CHAL_Z2 ∉ exceptionalSet
        ((szResidual env.loc xB yB zB wB (wB + SK) pl).map (Int.castRingHom K))

/-- ⚑ **THE RELOCATED CORE FORCES THE CONGRUENCE** — the sz twin of `mulCore_forces`, with the
same conclusion in the same `CZm` vocabulary, so the composed chain below is the SAME chain. -/
theorem szMulCore_forces {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    [CharP K 2013265921]
    (env : VmRowEnv) (z : Nat → K) (isLast : Bool) (pl : Nat → ℤ) (M : ℤ)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hplM : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = M)
    (xB yB zB wB : Nat)
    (hx : Ranged env.loc xB) (hy : Ranged env.loc yB) (hz : Ranged env.loc zB)
    (hw : MulWitRanged env.loc wB) (hg : SzMulAt env z isLast pl xB yB zB wB) :
    CZm M (sVal env.loc zB) (sVal env.loc xB * sVal env.loc yB) :=
  CZm.symm (by
    rcases hg.nonexc with h | h
    · exact szGate_holdsIn_forces_congruence env z isLast CHAL_Z xB yB zB wB (wB + SK) pl M
        hg.gateZ h hx hy hz hw.1 hpl hplM hw.2
    · exact szGate_holdsIn_forces_congruence env z isLast CHAL_Z2 xB yB zB wB (wB + SK) pl M
        hg.gateZ2 h hx hy hz hw.1 hpl hplM hw.2)

/-- ⚑ **THE 33 LEG-BLOCK HYPOTHESES OF THE SZ ROW, as one named object.** Field `hgN` is op `N` of
`swCompleteAddSoundLegs`, in the same SSA order at the same column bases as `RcbSat`'s — twelve of
them now `SzMulAt` over a draw, twenty-one unchanged over `env.loc`. -/
structure SzRcbSat {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    (env : VmRowEnv) (z : Nat → K) (isLast : Bool) (pl : Nat → ℤ) (b3 : ℤ)
    (X1 Y1 Z1 X2 Y2 Z2 fresh : Nat) : Prop where
  hg0 : SzMulAt env z isLast pl X1 X2 (vBase fresh 0) (mWit fresh 0)
  hg1 : SzMulAt env z isLast pl Y1 Y2 (vBase fresh 1) (mWit fresh 1)
  hg2 : SzMulAt env z isLast pl Z1 Z2 (vBase fresh 2) (mWit fresh 2)
  hg3 : AddSubSat env.loc pl 1 (-1) X1 Y1 (vBase fresh 3) (aWit fresh 0)
  hg4 : AddSubSat env.loc pl 1 (-1) X2 Y2 (vBase fresh 4) (aWit fresh 1)
  hg5 : SzMulAt env z isLast pl (vBase fresh 3) (vBase fresh 4) (vBase fresh 5) (mWit fresh 3)
  hg6 : AddSubSat env.loc pl 1 (-1) (vBase fresh 0) (vBase fresh 1) (vBase fresh 6) (aWit fresh 2)
  hg7 : AddSubSat env.loc pl (-1) 1 (vBase fresh 5) (vBase fresh 6) (vBase fresh 7) (aWit fresh 3)
  hg8 : AddSubSat env.loc pl 1 (-1) Y1 Z1 (vBase fresh 8) (aWit fresh 4)
  hg9 : AddSubSat env.loc pl 1 (-1) Y2 Z2 (vBase fresh 9) (aWit fresh 5)
  hg10 : SzMulAt env z isLast pl (vBase fresh 8) (vBase fresh 9) (vBase fresh 10) (mWit fresh 4)
  hg11 : AddSubSat env.loc pl 1 (-1) (vBase fresh 1) (vBase fresh 2) (vBase fresh 11) (aWit fresh 6)
  hg12 : AddSubSat env.loc pl (-1) 1 (vBase fresh 10) (vBase fresh 11) (vBase fresh 12) (aWit fresh 7)
  hg13 : AddSubSat env.loc pl 1 (-1) X1 Z1 (vBase fresh 13) (aWit fresh 8)
  hg14 : AddSubSat env.loc pl 1 (-1) X2 Z2 (vBase fresh 14) (aWit fresh 9)
  hg15 : SzMulAt env z isLast pl (vBase fresh 13) (vBase fresh 14) (vBase fresh 15) (mWit fresh 5)
  hg16 : AddSubSat env.loc pl 1 (-1) (vBase fresh 0) (vBase fresh 2) (vBase fresh 16) (aWit fresh 10)
  hg17 : AddSubSat env.loc pl (-1) 1 (vBase fresh 15) (vBase fresh 16) (vBase fresh 17) (aWit fresh 11)
  hg18 : AddSubSat env.loc pl 1 (-1) (vBase fresh 0) (vBase fresh 0) (vBase fresh 18) (aWit fresh 12)
  hg19 : AddSubSat env.loc pl 1 (-1) (vBase fresh 18) (vBase fresh 0) (vBase fresh 19) (aWit fresh 13)
  hg20 : SmulSat env.loc pl b3 (vBase fresh 2) (vBase fresh 20) (sWit fresh 0)
  hg21 : AddSubSat env.loc pl 1 (-1) (vBase fresh 1) (vBase fresh 20) (vBase fresh 21) (aWit fresh 14)
  hg22 : AddSubSat env.loc pl (-1) 1 (vBase fresh 1) (vBase fresh 20) (vBase fresh 22) (aWit fresh 15)
  hg23 : SmulSat env.loc pl b3 (vBase fresh 17) (vBase fresh 23) (sWit fresh 1)
  hg24 : SzMulAt env z isLast pl (vBase fresh 12) (vBase fresh 23) (vBase fresh 24) (mWit fresh 6)
  hg25 : SzMulAt env z isLast pl (vBase fresh 7) (vBase fresh 22) (vBase fresh 25) (mWit fresh 7)
  hg26 : AddSubSat env.loc pl (-1) 1 (vBase fresh 25) (vBase fresh 24) (vBase fresh 26) (aWit fresh 16)
  hg27 : SzMulAt env z isLast pl (vBase fresh 23) (vBase fresh 19) (vBase fresh 27) (mWit fresh 8)
  hg28 : SzMulAt env z isLast pl (vBase fresh 22) (vBase fresh 21) (vBase fresh 28) (mWit fresh 9)
  hg29 : AddSubSat env.loc pl 1 (-1) (vBase fresh 28) (vBase fresh 27) (vBase fresh 29) (aWit fresh 17)
  hg30 : SzMulAt env z isLast pl (vBase fresh 19) (vBase fresh 7) (vBase fresh 30) (mWit fresh 10)
  hg31 : SzMulAt env z isLast pl (vBase fresh 21) (vBase fresh 12) (vBase fresh 31) (mWit fresh 11)
  hg32 : AddSubSat env.loc pl 1 (-1) (vBase fresh 31) (vBase fresh 30) (vBase fresh 32) (aWit fresh 18)

/-- ⚑ **THE COMPOSED THEOREM, IN THE NEW SHAPE.** The `CZm` chain is `PastaCurve`'s, link for link
the same as `RcbSat.apply`'s; what changed is that twelve of its links are now forced by a
challenge gate at a non-exceptional draw instead of by 63 coefficient gates. -/
theorem SzRcbSat.apply {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K] [CharP K 2013265921]
    {X1 Y1 Z1 X2 Y2 Z2 fresh : Nat} {b3 : ℤ}
    {env : VmRowEnv} {z : Nat → K} {isLast : Bool} {pl : Nat → ℤ}
    (hG : SzRcbSat env z isLast pl b3 X1 Y1 Z1 X2 Y2 Z2 fresh) (M : ℤ)
    (hb3 : 0 ≤ b3 ∧ b3 < 2 ^ SB)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hplM : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = M)
    (hX1 : Ranged env.loc X1) (hY1 : Ranged env.loc Y1) (hZ1 : Ranged env.loc Z1)
    (hX2 : Ranged env.loc X2) (hY2 : Ranged env.loc Y2) (hZ2 : Ranged env.loc Z2)
    (hv : ∀ i, i < 33 → Ranged env.loc (vBase fresh i))
    (hm : ∀ k, k < 12 → MulWitRanged env.loc (mWit fresh k))
    (hs : ∀ k, k < 2 → SmulWitRanged env.loc (sWit fresh k))
    (hb : ∀ k, k < 19 → AddSubWitRanged env.loc (aWit fresh k)) :
    CZm M (sVal env.loc (vBase fresh 26))
        (rcbTraceZ b3 (sVal env.loc X1) (sVal env.loc Y1) (sVal env.loc Z1)
                      (sVal env.loc X2) (sVal env.loc Y2) (sVal env.loc Z2)).X3g
      ∧ CZm M (sVal env.loc (vBase fresh 29))
        (rcbTraceZ b3 (sVal env.loc X1) (sVal env.loc Y1) (sVal env.loc Z1)
                      (sVal env.loc X2) (sVal env.loc Y2) (sVal env.loc Z2)).Y3f
      ∧ CZm M (sVal env.loc (vBase fresh 32))
        (rcbTraceZ b3 (sVal env.loc X1) (sVal env.loc Y1) (sVal env.loc Z1)
                      (sVal env.loc X2) (sVal env.loc Y2) (sVal env.loc Z2)).Z3c := by
  let T := rcbTraceZ b3 (sVal env.loc X1) (sVal env.loc Y1) (sVal env.loc Z1)
             (sVal env.loc X2) (sVal env.loc Y2) (sVal env.loc Z2)
  have f0 : CZm M (sVal env.loc (vBase fresh 0)) T.t0a := szMulCore_forces env z isLast pl M hpl hplM X1 X2 (vBase fresh 0) (mWit fresh 0) hX1 hX2 (hv 0 (by decide)) (hm 0 (by decide)) hG.hg0
  have f1 : CZm M (sVal env.loc (vBase fresh 1)) T.t1a := szMulCore_forces env z isLast pl M hpl hplM Y1 Y2 (vBase fresh 1) (mWit fresh 1) hY1 hY2 (hv 1 (by decide)) (hm 1 (by decide)) hG.hg1
  have f2 : CZm M (sVal env.loc (vBase fresh 2)) T.t2a := szMulCore_forces env z isLast pl M hpl hplM Z1 Z2 (vBase fresh 2) (mWit fresh 2) hZ1 hZ2 (hv 2 (by decide)) (hm 2 (by decide)) hG.hg2
  have f3 : CZm M (sVal env.loc (vBase fresh 3)) T.t3a := addCore_forces env.loc pl M hpl hplM X1 Y1 (vBase fresh 3) (aWit fresh 0) hX1 hY1 (hv 3 (by decide)) (hb 0 (by decide)) hG.hg3
  have f4 : CZm M (sVal env.loc (vBase fresh 4)) T.t4a := addCore_forces env.loc pl M hpl hplM X2 Y2 (vBase fresh 4) (aWit fresh 1) hX2 hY2 (hv 4 (by decide)) (hb 1 (by decide)) hG.hg4
  have f5 : CZm M (sVal env.loc (vBase fresh 5)) T.t3b := CZm.trans (szMulCore_forces env z isLast pl M hpl hplM (vBase fresh 3) (vBase fresh 4) (vBase fresh 5) (mWit fresh 3) (hv 3 (by decide)) (hv 4 (by decide)) (hv 5 (by decide)) (hm 3 (by decide)) hG.hg5) (CZm.mul f3 f4)
  have f6 : CZm M (sVal env.loc (vBase fresh 6)) T.t4b := CZm.trans (addCore_forces env.loc pl M hpl hplM (vBase fresh 0) (vBase fresh 1) (vBase fresh 6) (aWit fresh 2) (hv 0 (by decide)) (hv 1 (by decide)) (hv 6 (by decide)) (hb 2 (by decide)) hG.hg6) (CZm.add f0 f1)
  have f7 : CZm M (sVal env.loc (vBase fresh 7)) T.t3c := CZm.trans (subCore_forces env.loc pl M hpl hplM (vBase fresh 5) (vBase fresh 6) (vBase fresh 7) (aWit fresh 3) (hv 5 (by decide)) (hv 6 (by decide)) (hv 7 (by decide)) (hb 3 (by decide)) hG.hg7) (CZm.sub f5 f6)
  have f8 : CZm M (sVal env.loc (vBase fresh 8)) T.t4c := addCore_forces env.loc pl M hpl hplM Y1 Z1 (vBase fresh 8) (aWit fresh 4) hY1 hZ1 (hv 8 (by decide)) (hb 4 (by decide)) hG.hg8
  have f9 : CZm M (sVal env.loc (vBase fresh 9)) T.X3a := addCore_forces env.loc pl M hpl hplM Y2 Z2 (vBase fresh 9) (aWit fresh 5) hY2 hZ2 (hv 9 (by decide)) (hb 5 (by decide)) hG.hg9
  have f10 : CZm M (sVal env.loc (vBase fresh 10)) T.t4d := CZm.trans (szMulCore_forces env z isLast pl M hpl hplM (vBase fresh 8) (vBase fresh 9) (vBase fresh 10) (mWit fresh 4) (hv 8 (by decide)) (hv 9 (by decide)) (hv 10 (by decide)) (hm 4 (by decide)) hG.hg10) (CZm.mul f8 f9)
  have f11 : CZm M (sVal env.loc (vBase fresh 11)) T.X3b := CZm.trans (addCore_forces env.loc pl M hpl hplM (vBase fresh 1) (vBase fresh 2) (vBase fresh 11) (aWit fresh 6) (hv 1 (by decide)) (hv 2 (by decide)) (hv 11 (by decide)) (hb 6 (by decide)) hG.hg11) (CZm.add f1 f2)
  have f12 : CZm M (sVal env.loc (vBase fresh 12)) T.t4e := CZm.trans (subCore_forces env.loc pl M hpl hplM (vBase fresh 10) (vBase fresh 11) (vBase fresh 12) (aWit fresh 7) (hv 10 (by decide)) (hv 11 (by decide)) (hv 12 (by decide)) (hb 7 (by decide)) hG.hg12) (CZm.sub f10 f11)
  have f13 : CZm M (sVal env.loc (vBase fresh 13)) T.X3c := addCore_forces env.loc pl M hpl hplM X1 Z1 (vBase fresh 13) (aWit fresh 8) hX1 hZ1 (hv 13 (by decide)) (hb 8 (by decide)) hG.hg13
  have f14 : CZm M (sVal env.loc (vBase fresh 14)) T.Y3a := addCore_forces env.loc pl M hpl hplM X2 Z2 (vBase fresh 14) (aWit fresh 9) hX2 hZ2 (hv 14 (by decide)) (hb 9 (by decide)) hG.hg14
  have f15 : CZm M (sVal env.loc (vBase fresh 15)) T.X3d := CZm.trans (szMulCore_forces env z isLast pl M hpl hplM (vBase fresh 13) (vBase fresh 14) (vBase fresh 15) (mWit fresh 5) (hv 13 (by decide)) (hv 14 (by decide)) (hv 15 (by decide)) (hm 5 (by decide)) hG.hg15) (CZm.mul f13 f14)
  have f16 : CZm M (sVal env.loc (vBase fresh 16)) T.Y3b := CZm.trans (addCore_forces env.loc pl M hpl hplM (vBase fresh 0) (vBase fresh 2) (vBase fresh 16) (aWit fresh 10) (hv 0 (by decide)) (hv 2 (by decide)) (hv 16 (by decide)) (hb 10 (by decide)) hG.hg16) (CZm.add f0 f2)
  have f17 : CZm M (sVal env.loc (vBase fresh 17)) T.Y3c := CZm.trans (subCore_forces env.loc pl M hpl hplM (vBase fresh 15) (vBase fresh 16) (vBase fresh 17) (aWit fresh 11) (hv 15 (by decide)) (hv 16 (by decide)) (hv 17 (by decide)) (hb 11 (by decide)) hG.hg17) (CZm.sub f15 f16)
  have f18 : CZm M (sVal env.loc (vBase fresh 18)) T.X3e := CZm.trans (addCore_forces env.loc pl M hpl hplM (vBase fresh 0) (vBase fresh 0) (vBase fresh 18) (aWit fresh 12) (hv 0 (by decide)) (hv 0 (by decide)) (hv 18 (by decide)) (hb 12 (by decide)) hG.hg18) (CZm.add f0 f0)
  have f19 : CZm M (sVal env.loc (vBase fresh 19)) T.t0b := CZm.trans (addCore_forces env.loc pl M hpl hplM (vBase fresh 18) (vBase fresh 0) (vBase fresh 19) (aWit fresh 13) (hv 18 (by decide)) (hv 0 (by decide)) (hv 19 (by decide)) (hb 13 (by decide)) hG.hg19) (CZm.add f18 f0)
  have f20 : CZm M (sVal env.loc (vBase fresh 20)) T.t2b := CZm.trans (smulCore_forces env.loc pl M b3 hb3 hpl hplM (vBase fresh 2) (vBase fresh 20) (sWit fresh 0) (hv 2 (by decide)) (hv 20 (by decide)) (hs 0 (by decide)) hG.hg20) (CZm.mul (CZm.refl _) (f2))
  have f21 : CZm M (sVal env.loc (vBase fresh 21)) T.Z3a := CZm.trans (addCore_forces env.loc pl M hpl hplM (vBase fresh 1) (vBase fresh 20) (vBase fresh 21) (aWit fresh 14) (hv 1 (by decide)) (hv 20 (by decide)) (hv 21 (by decide)) (hb 14 (by decide)) hG.hg21) (CZm.add f1 f20)
  have f22 : CZm M (sVal env.loc (vBase fresh 22)) T.t1b := CZm.trans (subCore_forces env.loc pl M hpl hplM (vBase fresh 1) (vBase fresh 20) (vBase fresh 22) (aWit fresh 15) (hv 1 (by decide)) (hv 20 (by decide)) (hv 22 (by decide)) (hb 15 (by decide)) hG.hg22) (CZm.sub f1 f20)
  have f23 : CZm M (sVal env.loc (vBase fresh 23)) T.Y3d := CZm.trans (smulCore_forces env.loc pl M b3 hb3 hpl hplM (vBase fresh 17) (vBase fresh 23) (sWit fresh 1) (hv 17 (by decide)) (hv 23 (by decide)) (hs 1 (by decide)) hG.hg23) (CZm.mul (CZm.refl _) (f17))
  have f24 : CZm M (sVal env.loc (vBase fresh 24)) T.X3f := CZm.trans (szMulCore_forces env z isLast pl M hpl hplM (vBase fresh 12) (vBase fresh 23) (vBase fresh 24) (mWit fresh 6) (hv 12 (by decide)) (hv 23 (by decide)) (hv 24 (by decide)) (hm 6 (by decide)) hG.hg24) (CZm.mul f12 f23)
  have f25 : CZm M (sVal env.loc (vBase fresh 25)) T.t2c := CZm.trans (szMulCore_forces env z isLast pl M hpl hplM (vBase fresh 7) (vBase fresh 22) (vBase fresh 25) (mWit fresh 7) (hv 7 (by decide)) (hv 22 (by decide)) (hv 25 (by decide)) (hm 7 (by decide)) hG.hg25) (CZm.mul f7 f22)
  have f26 : CZm M (sVal env.loc (vBase fresh 26)) T.X3g := CZm.trans (subCore_forces env.loc pl M hpl hplM (vBase fresh 25) (vBase fresh 24) (vBase fresh 26) (aWit fresh 16) (hv 25 (by decide)) (hv 24 (by decide)) (hv 26 (by decide)) (hb 16 (by decide)) hG.hg26) (CZm.sub f25 f24)
  have f27 : CZm M (sVal env.loc (vBase fresh 27)) T.Y3e := CZm.trans (szMulCore_forces env z isLast pl M hpl hplM (vBase fresh 23) (vBase fresh 19) (vBase fresh 27) (mWit fresh 8) (hv 23 (by decide)) (hv 19 (by decide)) (hv 27 (by decide)) (hm 8 (by decide)) hG.hg27) (CZm.mul f23 f19)
  have f28 : CZm M (sVal env.loc (vBase fresh 28)) T.t1c := CZm.trans (szMulCore_forces env z isLast pl M hpl hplM (vBase fresh 22) (vBase fresh 21) (vBase fresh 28) (mWit fresh 9) (hv 22 (by decide)) (hv 21 (by decide)) (hv 28 (by decide)) (hm 9 (by decide)) hG.hg28) (CZm.mul f22 f21)
  have f29 : CZm M (sVal env.loc (vBase fresh 29)) T.Y3f := CZm.trans (addCore_forces env.loc pl M hpl hplM (vBase fresh 28) (vBase fresh 27) (vBase fresh 29) (aWit fresh 17) (hv 28 (by decide)) (hv 27 (by decide)) (hv 29 (by decide)) (hb 17 (by decide)) hG.hg29) (CZm.add f28 f27)
  have f30 : CZm M (sVal env.loc (vBase fresh 30)) T.t0c := CZm.trans (szMulCore_forces env z isLast pl M hpl hplM (vBase fresh 19) (vBase fresh 7) (vBase fresh 30) (mWit fresh 10) (hv 19 (by decide)) (hv 7 (by decide)) (hv 30 (by decide)) (hm 10 (by decide)) hG.hg30) (CZm.mul f19 f7)
  have f31 : CZm M (sVal env.loc (vBase fresh 31)) T.Z3b := CZm.trans (szMulCore_forces env z isLast pl M hpl hplM (vBase fresh 21) (vBase fresh 12) (vBase fresh 31) (mWit fresh 11) (hv 21 (by decide)) (hv 12 (by decide)) (hv 31 (by decide)) (hm 11 (by decide)) hG.hg31) (CZm.mul f21 f12)
  have f32 : CZm M (sVal env.loc (vBase fresh 32)) T.Z3c := CZm.trans (addCore_forces env.loc pl M hpl hplM (vBase fresh 31) (vBase fresh 30) (vBase fresh 32) (aWit fresh 18) (hv 31 (by decide)) (hv 30 (by decide)) (hv 32 (by decide)) (hb 18 (by decide)) hG.hg32) (CZm.add f31 f30)
  exact ⟨f26, f29, f32⟩

/-- ⚑ **`pallasCompleteAddSz_forces`** — the DEPLOYED satisfaction of the sz row's 33 leg blocks,
at a draw whose twelve non-exceptionality disjunctions hold, forces
`(X3,Y3,Z3) ≡ rcbTraceZ 15 (P,Q)` mod the real Pallas-base prime `p`. Same conclusion as
`pallasCompleteAddSound_forces`, at 3 744 constraints instead of 4 476 and at
`1 − 2^−197.0` over the draw instead of unconditionally. -/
theorem pallasCompleteAddSz_forces {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    [CharP K 2013265921]
    (env : VmRowEnv) (z : Nat → K) (isLast : Bool) (X1 Y1 Z1 X2 Y2 Z2 fresh : Nat)
    (hX1 : Ranged env.loc X1) (hY1 : Ranged env.loc Y1) (hZ1 : Ranged env.loc Z1)
    (hX2 : Ranged env.loc X2) (hY2 : Ranged env.loc Y2) (hZ2 : Ranged env.loc Z2)
    (hv : ∀ i, i < 33 → Ranged env.loc (vBase fresh i))
    (hm : ∀ k, k < 12 → MulWitRanged env.loc (mWit fresh k))
    (hs : ∀ k, k < 2 → SmulWitRanged env.loc (sWit fresh k))
    (hb : ∀ k, k < 19 → AddSubWitRanged env.loc (aWit fresh k))
    (hG : SzRcbSat env z isLast pLimb (curveB3 : ℤ) X1 Y1 Z1 X2 Y2 Z2 fresh) :
    CZp (sVal env.loc (vBase fresh 26))
        (rcbTraceZ (curveB3 : ℤ) (sVal env.loc X1) (sVal env.loc Y1) (sVal env.loc Z1)
                   (sVal env.loc X2) (sVal env.loc Y2) (sVal env.loc Z2)).X3g
    ∧ CZp (sVal env.loc (vBase fresh 29))
        (rcbTraceZ (curveB3 : ℤ) (sVal env.loc X1) (sVal env.loc Y1) (sVal env.loc Z1)
                   (sVal env.loc X2) (sVal env.loc Y2) (sVal env.loc Z2)).Y3f
    ∧ CZp (sVal env.loc (vBase fresh 32))
        (rcbTraceZ (curveB3 : ℤ) (sVal env.loc X1) (sVal env.loc Y1) (sVal env.loc Z1)
                   (sVal env.loc X2) (sVal env.loc Y2) (sVal env.loc Z2)).Z3c :=
  hG.apply (pN : ℤ) (by decide) pLimb_bounds pLimb_recomposes
    hX1 hY1 hZ1 hX2 hY2 hZ2 hv hm hs hb

/-- ⚑ **`vestaCompleteAddSz_forces`** — the same at the Vesta-base / Pallas-scalar prime `q`. Both,
because the accumulator leg is Step/Tick on Vesta: a Pallas-only adoption would leave half the
recursion boundary on the expensive row. -/
theorem vestaCompleteAddSz_forces {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    [CharP K 2013265921]
    (env : VmRowEnv) (z : Nat → K) (isLast : Bool) (X1 Y1 Z1 X2 Y2 Z2 fresh : Nat)
    (hX1 : Ranged env.loc X1) (hY1 : Ranged env.loc Y1) (hZ1 : Ranged env.loc Z1)
    (hX2 : Ranged env.loc X2) (hY2 : Ranged env.loc Y2) (hZ2 : Ranged env.loc Z2)
    (hv : ∀ i, i < 33 → Ranged env.loc (vBase fresh i))
    (hm : ∀ k, k < 12 → MulWitRanged env.loc (mWit fresh k))
    (hs : ∀ k, k < 2 → SmulWitRanged env.loc (sWit fresh k))
    (hb : ∀ k, k < 19 → AddSubWitRanged env.loc (aWit fresh k))
    (hG : SzRcbSat env z isLast qLimb (curveB3 : ℤ) X1 Y1 Z1 X2 Y2 Z2 fresh) :
    CZq (sVal env.loc (vBase fresh 26))
        (rcbTraceZ (curveB3 : ℤ) (sVal env.loc X1) (sVal env.loc Y1) (sVal env.loc Z1)
                   (sVal env.loc X2) (sVal env.loc Y2) (sVal env.loc Z2)).X3g
    ∧ CZq (sVal env.loc (vBase fresh 29))
        (rcbTraceZ (curveB3 : ℤ) (sVal env.loc X1) (sVal env.loc Y1) (sVal env.loc Z1)
                   (sVal env.loc X2) (sVal env.loc Y2) (sVal env.loc Z2)).Y3f
    ∧ CZq (sVal env.loc (vBase fresh 32))
        (rcbTraceZ (curveB3 : ℤ) (sVal env.loc X1) (sVal env.loc Y1) (sVal env.loc Z1)
                   (sVal env.loc X2) (sVal env.loc Y2) (sVal env.loc Z2)).Z3c :=
  hG.apply (qN : ℤ) (by decide) qLimb_bounds qLimb_recomposes
    hX1 hY1 hZ1 hX2 hY2 hZ2 hv hm hs hb

end SzAdoption

#assert_axioms szMulCore_width_unchanged
#assert_axioms szMulCore_keeps_the_lookups
#assert_axioms szMulCore_gate_collapse
#assert_axioms szLegs_layout_unchanged
#assert_axioms pallasCompleteAddSzAir_mainRailOk
#assert_axioms vestaCompleteAddSzAir_mainRailOk
#assert_axioms pallasCompleteAddSzDesc_constraint_count
#assert_axioms vestaCompleteAddSzDesc_constraint_count
#assert_axioms szRcbWidthIsUnchanged
#assert_axioms sz_mul_is_cheaper_by_sixty_one
#assert_axioms sz_rcb_price_decomposes
#assert_axioms sz_rcb_arithmetic_collapse
#assert_axioms pallasCompleteAddSzDesc_chal_indices_distinct
#assert_axioms vestaCompleteAddSzDesc_chal_indices_distinct
#assert_axioms pallasCompleteAddSzDesc_declares_two_challenges
#assert_axioms szMulCore_forces
#assert_axioms SzRcbSat.apply
#assert_axioms pallasCompleteAddSz_forces
#assert_axioms vestaCompleteAddSz_forces

end Dregg2.Circuit.Emit.PastaCurveSound
