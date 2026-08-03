/-
# Dregg2.Circuit.RangeFieldContainment — what a declared range width MEANS at BabyBear, and the
exact width above which it means NOTHING.

## The wound this file exists to state as a theorem

Every `EffectVmDescriptor2` range table is a declared bit width `b`, and its rows are `[v]` for
`v ∈ [0, 2^b)` (`DescriptorIR2.rangeRows` / `range_row_mem_iff`). Every Emit module's `airAccepts`
reads that as an interval over `ℤ`, where `−1 ∉ [0, 2^b)` for every `b` and the tooth looks sharp.

**The deployed reading is not over `ℤ`.** The prover's wires are BabyBear felts, `p = 2013265921`,
and a slack the prover "wanted" to be `−k` is the field element `p − k`. So the question a range
declaration actually answers is: *is `p − k` in `[0, 2^b)`?* — and for `b ≥ 31` the answer is YES
FOR EVERY FIELD ELEMENT, because `p < 2^31`. A 31-bit-or-wider range table over BabyBear declares
an interval that already contains the whole field. It refuses nothing. It is not a weak check; it
is not a check.

`range_vacuous_at_or_above_31` is that statement, over ALL widths `b ≥ 31` and ALL field elements —
not a witness, not an example.

## The census that motivated it (MEASURED 2026-08-03, `circuit/descriptors/**/*.json`)

404 declared range widths across the descriptor tree. Exactly **three** sit at `b ≥ 31`, and all
three are peer-chain light-client verify AIRs:

| descriptor                                | declared `bits` | ranged wires                    |
|-------------------------------------------|-----------------|---------------------------------|
| `dregg-tm-lightclient-verify::v1`         | 64              | `TDIFF TW_MONO TW_DRIFT TW_TRUST` |
| `dregg-solana-lightclient-verify::v1`     | 128             | `QDIFF TPOS`                    |
| `dregg-midnight-lightclient-verify::v1`   | 128             | `WDIFF TPOS`                    |

Eight lookups, refusing nothing. The other 401 declarations are `≤ 30`.

## ⚑ AND 30 IS NOT SAFE EITHER — the wrap-free ceiling is 29

Containment (`2^b < p`) is the WEAKER property and holds up to `b = 30`. The property the slack
teeth actually need is stronger: that a prover who wants slack `−k`, for a magnitude `k` within the
interval's own reach, finds `p − k` OUTSIDE the interval. That is `Wrapfree b`, and

    Wrapfree b  ↔  2^(b+1) ≤ p      (`wrap_free_iff`)

so the maximum wrap-free width at BabyBear is **29** (`2^30 = 1073741824 ≤ p`), and **30 fails**
(`2^31 = 2147483648 > p`): at `b = 30` a slack of `−939524098` rides as `p − 939524098 =
1073741823 < 2^30` and is ADMITTED (`wrap_admitted_at_30`). The 83 descriptors declaring 30 bits are
NOT vacuous — they refuse every negative of magnitude `≤ p − 2^30 = 939524097` — but they are not
wrap-free, and this file says so rather than leaving it implied by a constant.

⚠ Said plainly and not laundered: `Wrapfree` bounds the magnitudes the interval can itself reach. No
width is wrap-free against a completely unconstrained `k`, because `p − k` is small when `k` is near
`p`. What makes a slack tooth bite is `Wrapfree` PLUS the gate tying the slack to columns that are
themselves bounded. This file proves the first half; the gate is the second half and lives in each
chain's Emit module.

## ⚑ AND WHAT THE DEPLOYED PROVER DID, WHICH IS THE OPPOSITE (MEASURED 2026-08-03)

The theorems here are about the DENOTATION: `rangeRows b` for `b ≥ 31` contains every field element,
so the tooth refuses nothing. The deployed Rust prover, run against the same declared constant, does
the reverse. Its layout bound is

    (v as u64) >= (1u64 << rb.bits)          -- circuit/src/descriptor_ir2.rs:4310

and a `u64` shift by 64 is masked to a shift by 0 in a release build, so at `bits = 64` the test
collapses to `v >= 1` and EVERY nonzero value on a ranged wire is REFUSED. The two 128-bit siblings
are hit identically (`128 % 64 = 0`).

So the three censused descriptors were vacuous in the denotation and UNPROVABLE in the prover — the
same declared constant read two ways that disagree maximally. **That is the mechanical reason none
of them had ever been proved: the first honest attempt would have been refused.** Measured in
`circuit/tests/tendermint_lightclient_proves.rs`
(`the_shipped_64_bit_width_refuses_even_an_honest_header`), where the honest header that proves at
29 bits is refused at 64.

⚠ Widths 32..63 shift fine and ARE vacuous in both readings — that is what the same file's
`..._is_admitted_at_a_vacuous_width` exhibits, at 32. The overflow is a second, separate defect
stacked on the first, not the same one; neither is a substitute for the other.

⚠ This is the SHAPE of a check over a prime field, not an assurance claim. Nothing here discharges
the inherited FRI/IPA floor, and none of it is "machine-checked" end to end.
-/

import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectLowerCore

namespace Dregg2.Circuit.RangeFieldContainment

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectLower (P)

/-! ## §1 — the field, at the resolution the question needs. -/

/-- BabyBear's modulus, restated where the range argument reads it. -/
theorem babybear_modulus : P = 2013265921 := rfl

/-- ⚑ **THE FIELD IS 30.9 BITS.** `2^30 < p < 2^31` — so a 30-bit interval fits inside it with room,
and a 31-bit interval already covers it whole. Every statement below turns on this one line. -/
theorem field_is_between_30_and_31_bits : (2 : ℤ) ^ 30 < P ∧ P < (2 : ℤ) ^ 31 := by
  constructor <;> norm_num [babybear_modulus]

/-! ## §2 — VACUITY: a range table at 31 bits or wider refuses nothing. -/

/-- ⚑ **THE VACUITY THEOREM.** For EVERY declared width `b ≥ 31` and EVERY field element `v`, the
row `[v]` is in the table. A lookup against such a table is satisfied by whatever the prover put on
the wire; it eliminates no assignment.

This is stated over all `b ≥ 31` and all `v ∈ [0, p)` — it is not an exhibited witness, and there is
no assignment it fails to cover. -/
theorem range_vacuous_at_or_above_31 (b : Nat) (hb : 31 ≤ b) (v : ℤ)
    (h0 : 0 ≤ v) (hp : v < P) : [v] ∈ rangeRows b := by
  rw [range_row_mem_iff]
  refine ⟨h0, lt_of_lt_of_le hp ?_⟩
  calc (P : ℤ) ≤ (2 : ℤ) ^ 31 := le_of_lt field_is_between_30_and_31_bits.2
    _ ≤ (2 : ℤ) ^ b := pow_le_pow_right₀ (by norm_num) hb

/-- The contrapositive, in the form a reader checks a descriptor against: at `b ≥ 31` there is NO
field element the table refuses. -/
theorem no_field_element_refused_at_or_above_31 (b : Nat) (hb : 31 ≤ b) :
    ¬ ∃ v : ℤ, 0 ≤ v ∧ v < P ∧ [v] ∉ rangeRows b := by
  rintro ⟨v, h0, hp, hmem⟩
  exact hmem (range_vacuous_at_or_above_31 b hb v h0 hp)

/-- The three declared widths the census found above the ceiling, each named. `TM_BITS = 64`,
`LightClientSolanaAir.RANGE_BITS = 128`, `LightClientMidnightAir.RANGE_BITS = 128` — as they stood
before this repair. -/
theorem the_three_censused_widths_were_vacuous (v : ℤ) (h0 : 0 ≤ v) (hp : v < P) :
    [v] ∈ rangeRows 64 ∧ [v] ∈ rangeRows 128 :=
  ⟨range_vacuous_at_or_above_31 64 (by norm_num) v h0 hp,
   range_vacuous_at_or_above_31 128 (by norm_num) v h0 hp⟩

/-! ## §3 — CONTAINMENT: the interval sits strictly inside the field. -/

/-- The interval is inside the field exactly up to width 30. -/
theorem range_inside_the_field (b : Nat) (hb : b ≤ 30) : (2 : ℤ) ^ b < P :=
  lt_of_le_of_lt (pow_le_pow_right₀ (by norm_num) hb) field_is_between_30_and_31_bits.1

/-- …and not one bit further: containment FAILS at 31. A floor that cannot fail is decoration; this
is the refutation that makes `range_inside_the_field`'s bound the real one. -/
theorem range_not_inside_the_field_at_31 : ¬ ((2 : ℤ) ^ 31 < P) := by
  norm_num [babybear_modulus]

/-! ## §4 — WRAP-FREEDOM: the property a slack tooth actually needs, and its exact ceiling. -/

/-- **The wrapped-slack property at width `b`.** A prover who wants a slack of `−k`, for a magnitude
`k` the interval can itself reach, puts the field element `p − k` on the wire — and that element is
OUTSIDE `[0, 2^b)`. This, not containment, is what makes a range lookup an `≤` relation. -/
def Wrapfree (b : Nat) : Prop :=
  ∀ k : ℤ, 0 < k → k ≤ (2 : ℤ) ^ b → ¬ (0 ≤ P - k ∧ P - k < (2 : ℤ) ^ b)

/-- ⚑ **THE EXACT CEILING.** `Wrapfree b ↔ 2^(b+1) ≤ p`. Both directions: the forward direction
exhibits `k = 2^b` as the admitted wrap when the field is too small, and the reverse direction is the
arithmetic that makes the interval and its complement disjoint. -/
theorem wrap_free_iff (b : Nat) : Wrapfree b ↔ (2 : ℤ) ^ (b + 1) ≤ P := by
  constructor
  · intro hwf
    by_contra hlt
    push Not at hlt
    have hpow : (2 : ℤ) ^ (b + 1) = 2 * (2 : ℤ) ^ b := by ring
    have hb0 : (0 : ℤ) < (2 : ℤ) ^ b := pow_pos (by norm_num) b
    -- `k = 2^b` is admitted: `p − 2^b ≥ 0` (since `2^b < 2^(b+1) ≤ ...`) and `< 2^b` (since
    -- `p < 2·2^b`). The first needs `2^b ≤ p`, which follows from `2·2^b > p` being FALSE for
    -- the two-case split below.
    rcases le_or_gt ((2 : ℤ) ^ b) P with hle | hgt
    · exact hwf ((2 : ℤ) ^ b) hb0 le_rfl ⟨by linarith, by rw [hpow] at hlt; linarith⟩
    · -- `2^b > p`: then `k = 1` wraps in, since `p − 1 ≥ 0` and `p − 1 < p < 2^b`.
      have hp1 : (1 : ℤ) ≤ (2 : ℤ) ^ b := by omega
      exact hwf 1 (by norm_num) hp1 ⟨by norm_num [babybear_modulus], by
        have : (P : ℤ) = 2013265921 := babybear_modulus
        linarith⟩
  · intro hge k hk hk' ⟨_, hlt⟩
    have hpow : (2 : ℤ) ^ (b + 1) = 2 * (2 : ℤ) ^ b := by ring
    rw [hpow] at hge
    linarith

/-- **29 IS WRAP-FREE** — `2^30 = 1073741824 ≤ p`. -/
theorem wrap_free_at_29 : Wrapfree 29 := by
  rw [wrap_free_iff]; norm_num [babybear_modulus]

/-- ⚑ **AND 30 IS NOT** — `2^31 = 2147483648 > p`. The floor is REFUTABLE, and this is the
refutation: 29 is not a taste, it is the last width at which the property is true. -/
theorem not_wrap_free_at_30 : ¬ Wrapfree 30 := by
  rw [wrap_free_iff]; norm_num [babybear_modulus]

/-- The maximality statement in one line: wrap-freedom holds at `b` exactly when `b ≤ 29`. -/
theorem wrap_free_iff_le_29 (b : Nat) : Wrapfree b ↔ b ≤ 29 := by
  rw [wrap_free_iff]
  constructor
  · intro h
    by_contra hb
    push Not at hb
    have : (2 : ℤ) ^ 31 ≤ (2 : ℤ) ^ (b + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hp : (P : ℤ) = 2013265921 := babybear_modulus
    have : (2 : ℤ) ^ 31 ≤ P := le_trans this h
    norm_num [hp] at this
  · intro hb
    calc (2 : ℤ) ^ (b + 1) ≤ (2 : ℤ) ^ 30 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ P := by norm_num [babybear_modulus]

/-! ## §5 — THE ADMITTED VALUES, exhibited. A repair with no exhibited value is a constant. -/

/-- ⚑ **THE VALUE A 64-BIT TABLE ADMITS.** `2013265920` is `p − 1` — the field encoding of the slack
`−1`, which is exactly what a Tendermint / Midnight strict-`>2/3` identity fills to at the
EXACTLY-2/3 boundary. The 64-bit table admits it: the sub-quorum passes. -/
theorem minus_one_admitted_at_64 : ([2013265920] : List ℤ) ∈ rangeRows 64 := by
  rw [range_row_mem_iff]; norm_num

/-- …and the 29-bit table REFUSES it. `2013265920 ≥ 2^29 = 536870912`. This pair is the bite. -/
theorem minus_one_refused_at_29 : ([2013265920] : List ℤ) ∉ rangeRows 29 := by
  rw [range_row_mem_iff]; norm_num

/-- The same pair at 128 bits (Solana / Midnight, as they stood). -/
theorem minus_one_admitted_at_128 : ([2013265920] : List ℤ) ∈ rangeRows 128 := by
  rw [range_row_mem_iff]; norm_num

/-- ⚑ **AND THE 30-BIT ADMISSION**, so the "83 descriptors at 30 bits" line is measured and not
assumed: the slack `−939524098` rides as `p − 939524098 = 1073741823`, inside `[0, 2^30)`. Those
tables are not vacuous, but they are not wrap-free. -/
theorem large_negative_admitted_at_30 : ([1073741823] : List ℤ) ∈ rangeRows 30 := by
  rw [range_row_mem_iff]; norm_num

/-- …and that same element is refused at 29. -/
theorem large_negative_refused_at_29 : ([1073741823] : List ℤ) ∉ rangeRows 29 := by
  rw [range_row_mem_iff]; norm_num

/-- The honest complement, so nothing here reads wider than it is: at 30 bits the negatives that ARE
refused are exactly those of magnitude `≤ p − 2^30 = 939524097`. -/
theorem small_negative_refused_at_30 (k : ℤ) (hk : 0 < k) (hk' : k ≤ 939524097) :
    ([P - k] : List ℤ) ∉ rangeRows 30 := by
  rw [range_row_mem_iff]
  rintro ⟨_, hlt⟩
  have hp : (P : ℤ) = 2013265921 := babybear_modulus
  rw [hp] at hlt
  norm_num at hlt
  omega

/-! ## §6 — axiom hygiene. -/

#assert_axioms range_vacuous_at_or_above_31
#assert_axioms wrap_free_iff
#assert_axioms wrap_free_iff_le_29
#assert_axioms minus_one_admitted_at_64
#assert_axioms minus_one_refused_at_29

end Dregg2.Circuit.RangeFieldContainment
