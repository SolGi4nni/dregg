/-
# Dregg2.Bignum.DigitInjective — positional notation is INJECTIVE, at any width.

`Dregg2.Circuit.CaveatBignum.bignumVal B` is the base-`B` little-endian limb integer and
`Ranged B` the per-limb range check.  Everything in the bignum stack so far reasons about the
VALUE those limbs denote (compare / add / sub / mul / mod, each with an `_iff` keystone).  The
one fact nobody had stated is the DUAL: the map from limbs to value is INJECTIVE once the limbs
are ranged — a base-`B` representation of a given length has exactly one limb vector.

That is the fact every "pack `n` small fields into one felt and commit to the pack" argument
needs, and until now each such argument re-derived it by WRITING THE SUM OUT and handing eight
bound hypotheses to `omega`.  That style does not survive a parameter change: it is quadratic in
the limb count, and at 16 limbs it does not terminate in any useful time.  Here it is proved
ONCE, by induction on the limb list, with no term enumeration and no bound on the width.

The argument is the schoolbook one: `x + B·X = y + B·Y` with `0 ≤ x,y < B` forces `x − y` to be
a multiple of `B` strictly inside `(−B, B)`, hence `x = y`, hence `B·X = B·Y`, hence `X = Y` by
cancellation in `ℤ` — then recurse.  Two corollaries package the uses:

  * `chunkedVal_injective` — a LIST of equal-length ranged limb blocks is determined by the list
    of block values.  This is the multi-FELT commitment shape: one felt per block.
  * `bignumVal_eq_zero_iff` — a block's value is `0` iff every limb is `0`.  This is the exact
    "can a live leaf collide with the padding constant" question, answered by proof: an all-pad
    block is the ONLY block worth zero.

Pure, `Int`-valued, no field wraparound in the model (the range checks are what force the
realization to match), `sorry`-free.
-/
import Dregg2.Circuit.CaveatBignumCompare

namespace Dregg2.Bignum.DigitInjective

open Dregg2.Circuit.CaveatBignum

set_option autoImplicit false

/-! ## §1 — The keystone: ranged limbs are determined by their value. -/

/-- **`bignumVal_injective`** — base-`B` positional notation is injective on equal-length ranged
limb lists.  Proved by induction on the limbs: no enumeration of terms, no bound on the width,
so it holds at 4 limbs and at 16 limbs and at 4096 limbs with the same proof. -/
theorem bignumVal_injective {B : ℤ} (hB : 0 < B) :
    ∀ (xs ys : List ℤ), xs.length = ys.length → Ranged B xs → Ranged B ys →
      bignumVal B xs = bignumVal B ys → xs = ys
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _, _ => by simp at hlen
  | x :: xs, y :: ys, hlen, hrx, hry, hval => by
      have hxr : 0 ≤ x ∧ x < B := hrx x List.mem_cons_self
      have hyr : 0 ≤ y ∧ y < B := hry y List.mem_cons_self
      have hrx' : Ranged B xs := fun z hz => hrx z (List.mem_cons_of_mem _ hz)
      have hry' : Ranged B ys := fun z hz => hry z (List.mem_cons_of_mem _ hz)
      have hlen' : xs.length = ys.length := by simpa using hlen
      simp only [bignumVal_cons] at hval
      -- `x − y` is `B` times an integer, and lies strictly inside `(−B, B)`.
      have hk : x - y = B * (bignumVal B ys - bignumVal B xs) := by
        rw [mul_sub]
        linarith [hval]
      have hxy : x = y := by
        rcases lt_trichotomy (bignumVal B ys - bignumVal B xs) 0 with h | h | h
        · have hd : bignumVal B ys - bignumVal B xs ≤ -1 := by omega
          have hmul : B * (bignumVal B ys - bignumVal B xs) ≤ B * (-1) :=
            mul_le_mul_of_nonneg_left hd (le_of_lt hB)
          rw [← hk] at hmul
          linarith [hxr.1, hyr.2]
        · rw [h, mul_zero] at hk
          omega
        · have hd : (1 : ℤ) ≤ bignumVal B ys - bignumVal B xs := by omega
          have hmul : B * 1 ≤ B * (bignumVal B ys - bignumVal B xs) :=
            mul_le_mul_of_nonneg_left hd (le_of_lt hB)
          rw [← hk] at hmul
          linarith [hxr.2, hyr.1]
      subst hxy
      have hmul : B * bignumVal B xs = B * bignumVal B ys := by linarith [hval]
      have htail : bignumVal B xs = bignumVal B ys :=
        mul_left_cancel₀ (ne_of_gt hB) hmul
      rw [bignumVal_injective hB xs ys hlen' hrx' hry' htail]

/-- The `Function.Injective` phrasing, on a fixed width. -/
theorem bignumVal_injOn {B : ℤ} (hB : 0 < B) (width : Nat)
    {xs ys : List ℤ} (hx : xs.length = width) (hy : ys.length = width)
    (hrx : Ranged B xs) (hry : Ranged B ys)
    (hval : bignumVal B xs = bignumVal B ys) : xs = ys :=
  bignumVal_injective hB xs ys (hx.trans hy.symm) hrx hry hval

/-! ## §2 — Zero is the unique all-zero block (the padding question). -/

/-- A ranged limb block denotes `0` **iff** every one of its limbs is `0`.  So there is no
"live" limb vector whose packed value coincides with the all-padding constant: the padding
value is reached by the padding vector and by nothing else.  This is the multi-limb form of the
question "can a live leaf digest collide with the padding constant" — answered NO, by proof,
for the PACKING layer (the hash layer is a separate, computational, assumption). -/
theorem bignumVal_eq_zero_iff {B : ℤ} (hB : 0 < B) (xs : List ℤ) (hrx : Ranged B xs) :
    bignumVal B xs = 0 ↔ ∀ x ∈ xs, x = 0 := by
  constructor
  · intro hval
    have hzero : Ranged B (List.replicate xs.length 0) := by
      intro z hz
      have : z = 0 := List.eq_of_mem_replicate hz
      omega
    have hlen : xs.length = (List.replicate xs.length (0 : ℤ)).length := by simp
    have hvz : bignumVal B (List.replicate xs.length (0 : ℤ)) = 0 := by
      induction xs.length with
      | zero => simp
      | succ n ih => simp [List.replicate_succ, ih]
    have := bignumVal_injective hB xs (List.replicate xs.length 0) hlen hrx hzero
      (by rw [hval, hvz])
    intro x hx
    rw [this] at hx
    exact List.eq_of_mem_replicate hx
  · intro hall
    induction xs with
    | nil => simp
    | cons x xs ih =>
        have hx : x = 0 := hall x List.mem_cons_self
        have htail : ∀ z ∈ xs, z = 0 := fun z hz => hall z (List.mem_cons_of_mem _ hz)
        have hrx' : Ranged B xs := fun z hz => hrx z (List.mem_cons_of_mem _ hz)
        simp [hx, ih hrx' htail]

/-! ## §3 — The multi-FELT shape: a list of equal-width blocks. -/

/-- **`chunkedVal_injective`** — a list of equal-length ranged blocks is determined by the list
of the blocks' values.  This is exactly the multi-felt commitment: one BabyBear felt per block of
`width` limbs, the felt list absorbed by the hash.  Injectivity of the felt list on the padded
domain reduces to `bignumVal_injective` per block; nothing about the felt COUNT is enumerated. -/
theorem chunkedVal_injective {B : ℤ} (hB : 0 < B) (width : Nat) :
    ∀ (xss yss : List (List ℤ)),
      xss.length = yss.length →
      (∀ xs ∈ xss, xs.length = width) → (∀ ys ∈ yss, ys.length = width) →
      (∀ xs ∈ xss, Ranged B xs) → (∀ ys ∈ yss, Ranged B ys) →
      xss.map (bignumVal B) = yss.map (bignumVal B) → xss = yss
  | [], [], _, _, _, _, _, _ => rfl
  | [], _ :: _, hlen, _, _, _, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _, _, _, _ => by simp at hlen
  | xs :: xss, ys :: yss, hlen, hwx, hwy, hrx, hry, hval => by
      simp only [List.map_cons, List.cons.injEq] at hval
      have hhead : xs = ys :=
        bignumVal_injOn hB width (hwx xs List.mem_cons_self) (hwy ys List.mem_cons_self)
          (hrx xs List.mem_cons_self) (hry ys List.mem_cons_self) hval.1
      have htail : xss = yss :=
        chunkedVal_injective hB width xss yss (by simpa using hlen)
          (fun z hz => hwx z (List.mem_cons_of_mem _ hz))
          (fun z hz => hwy z (List.mem_cons_of_mem _ hz))
          (fun z hz => hrx z (List.mem_cons_of_mem _ hz))
          (fun z hz => hry z (List.mem_cons_of_mem _ hz))
          hval.2
      rw [hhead, htail]

/-! ## §4 — Non-vacuity, both poles. -/

/-- POSITIVE: distinct base-128 four-limb vectors have distinct values. -/
example : bignumVal 128 [1, 0, 0, 0] ≠ bignumVal 128 [0, 1, 0, 0] := by decide

/-- The keystone's TOOTH, in the contrapositive form a commitment argument actually consumes:
two ranged base-128 limb vectors of the same length that DIFFER anywhere have DIFFERENT values.
(An `xs = xs` instance would prove nothing — it is `rfl` with the keystone spelt over it.) -/
example {xs ys : List ℤ} (hlen : xs.length = ys.length)
    (hx : Ranged 128 xs) (hy : Ranged 128 ys) (hne : xs ≠ ys) :
    bignumVal 128 xs ≠ bignumVal 128 ys :=
  fun h => hne (bignumVal_injective (by norm_num) xs ys hlen hx hy h)

/-- NEGATIVE (the range check is LOAD-BEARING, not decoration): drop `Ranged` and the
conclusion is FALSE — `[128, 0]` and `[0, 1]` are distinct limb vectors with the SAME base-128
value.  A "packing injectivity" theorem stated without the per-limb range check would be wrong,
not merely weak. -/
example : bignumVal 128 [128, 0] = bignumVal 128 [0, 1] ∧ ([128, 0] : List ℤ) ≠ [0, 1] := by
  refine ⟨by decide, by decide⟩

/-- The padding pole: an all-zero block is worth zero, and (by `bignumVal_eq_zero_iff`) it is
the only ranged block that is. -/
example : bignumVal 128 [0, 0, 0, 0] = 0 := by decide

#guard decide (bignumVal 4096 [1, 0] = 1)
#guard decide (bignumVal 4096 [0, 1] = 4096)

#assert_axioms bignumVal_injective
#assert_axioms bignumVal_injOn
#assert_axioms bignumVal_eq_zero_iff
#assert_axioms chunkedVal_injective

end Dregg2.Bignum.DigitInjective
