/-
# `Dregg2.Crypto.Fips204BitPack` — FIPS 204 Algorithms 9 / 10 / 16 / 28 as BIT-ADDRESSED
standard-side objects, and the theorem that the deployed mixed-radix bignum packer emits exactly
Algorithm 28's byte string.

## Why this file exists

`Fips204ChallengeHash.challengeHashSpec` is FIPS 204 Algorithm 8 line 5 with BOTH halves standard-side:
`H = Keccak.Fips202.SHAKE256` (the bit-addressed FIPS 202 §6.2 sponge) and the encoder `w1Encode`.
For the encoder half to carry content, `w1Encode` on the SPEC side must be written from the standard,
in objects that mention `MlDsaCodec.packBits` NOWHERE — otherwise the "refinement" is `rfl` on the
implementation's own expression, which is exactly the vacuity `VerifyCoreHashFrame`'s ledger records
twice. That object is `w1EncodeSpec` below, and `w1Encode_eq_spec` is the theorem that the deployed
packer agrees with it.

## The two encoders, and why neither reduces to the other

* **DEPLOYED** (`MlDsaCodec.packBits`, `MlDsaVerifyReal.w1Encode`): accumulate the little-endian
  mixed-radix bignum `N = Σᵢ (cᵢ mod 2⁴)·16ⁱ` over a whole 256-coefficient row, then emit `N`'s
  base-256 digits. Nothing in it mentions a bit.
* **STANDARD** (`w1EncodeSpec` here): Algorithm 9 `IntegerToBits(x, α)` produces `α` bits
  `⌊x/2ⁱ⌋ mod 2`; Algorithm 16 `SimpleBitPack` concatenates those per coefficient into a bit string;
  Algorithm 10 `BitsToBytes` reads that bit string back eight bits at a time, LSB first; Algorithm 28
  concatenates the `k = 6` rows. Nothing in it mentions a bignum.

The bridge is the positional-numeral theorem `packNat_bit`: bit `m` of the deployed bignum is bit
`m mod c` of coefficient `m / c`. That is a real `∀`-statement about `Nat`, proved by induction, and a
wrong width, endianness, digit order, or coefficient mask on either side falsifies it.

## What is REUSED rather than re-derived

The loop-level facts about `packBits` — `VerifyCoreEqSpec.packNat` (the packed integer),
`packBits_size`, `packBits_getElem` (byte `m` is base-256 digit `m` of `packNat`), and the base-`b`
positional facts `extract_digit` / `digit_reconstruct` — are already proved in
`Dregg2.Crypto.VerifyCoreEqSpec` for the `t1`/`z` codec round-trip. This file adds ONLY the missing
layer: the base-`2^c` ↔ base-`2` re-basing (`mixedRadix_eq_bitSum`, `packNat_bit`, `window_eq_bitSum`)
and the FIPS 204 Algorithm 9/10/16/28 transcription. No second bignum packer is defined here.

## The honest FIPS 204 correspondence

`w1Encode_eq_spec` establishes a machine-checked `∀`-equality between the deployed byte string and the
Algorithm 9/10/16/28 transcription written in this file. What it CANNOT establish — no theorem can —
is that the transcription is a faithful reading of the printed standard. That residue is deliberately
made as small and as diffable as possible:

* Algorithm 9's `y[i] ← x mod 2; x ← ⌊x/2⌋` is `integerToBits x α = (range α).map (x.testBit ·)`;
* Algorithm 10's `z[i] ← Σⱼ y[8i+j]·2ʲ` is `bitsToBytes` verbatim;
* Algorithm 16's `z ← z ‖ IntegerToBits(w[i], c)` is `simpleBitPackBits`, and the theorem
  `simpleBitPackBits_getD` re-derives its bit-indexed form rather than assuming it;
* Algorithm 28's width is NOT the literal `4`: `w1Bits = bitlen((q−1)/(2γ₂) − 1)` is computed from
  `MlDsaRing.q` and `MlDsaVerifyReal.gamma2`, and `w1Bits_eq_four` is a theorem. Change either
  parameter and the width — and the refinement — move with it.

One further transcription is retired outright: FIPS 204 Algorithm 10 and FIPS 202 §B.1 use the same
byte↔bit convention. That is not assumed here, it is PROVED — `bitsOfBytes_bitsToBytes` shows the
§B.1 byte reader inverts the Algorithm 10 byte writer, which is what makes `challengeHashSpec`'s
`SHAKE256 (bitsOfBytes (μ ++ w1EncodeSpec w1))` composition mean what it says.

## Floors

NONE introduced by this file. `w1Encode_eq_spec` and everything it rests on are
`#assert_axioms`-clean (⊆ `propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no `axiom`, no
`native_decide`. The teeth at the bottom are KERNEL `decide` on small literals.

The FIPS 204 leg's floors live elsewhere and are untouched by this file: SHAKE256 collision resistance
(the `HashSig`/`FoQrom` axis), `VerifyCoreHashFrame.HighBitsStableK` (Dilithium high-bits stability
over `R_q`), and the transcription of Algorithm 8 line 5 itself.
-/
import Dregg2.Crypto.VerifyCoreEqSpec
import Dregg2.Crypto.Keccak.Fips202Sponge

namespace Dregg2.Crypto.Fips204BitPack

open Dregg2.Crypto.MlDsaRing (Poly q)
open Dregg2.Crypto.MlDsaCodec (packBits paramK)
open Dregg2.Crypto.MlDsaVerifyReal (w1Encode gamma2)
open Dregg2.Crypto.VerifyCoreEqSpec (packNat packBits_size packBits_getElem extract_digit)
open Dregg2.Crypto.Keccak.Fips202 (bitsOfBytes bitsOfBytes_getD bitsOfBytes_length getD_append_lt)

/-! ## PART 0 — `Nat` bit arithmetic: the re-basing facts.

Everything in this part is about `Nat` alone. It is the content that lets a base-`2^c` positional
number be read as a base-`2` one, which is precisely the difference between the deployed packer and
the standard's bit string. -/

/-- `(x.testBit i).toNat = ⌊x / 2^i⌋ mod 2` — the arithmetic form of a bit. -/
theorem toNat_testBit (x i : Nat) : (x.testBit i).toNat = x / 2 ^ i % 2 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> simp [h]

/-- Every bit contributes a digit `< 2`. -/
theorem toNat_testBit_lt_two (x i : Nat) : (x.testBit i).toNat < 2 := by
  cases x.testBit i <;> decide

/-- **The bit-window law — a real `∀`.** The `w`-bit field of `x` starting at bit `k` is the
little-endian sum `Σ_{j<w} bit(k+j)·2ʲ` of its own bits. Specialised at `k = 8n`, `w = 8` this says a
base-256 digit is a byte's worth of bits; specialised at `k = 0` it says `x mod 2^w` is the sum of
`x`'s low `w` bits (FIPS 204 Algorithm 9's output, read as a number). -/
theorem window_eq_bitSum (x k : Nat) : ∀ w : Nat,
    x / 2 ^ k % 2 ^ w = ∑ j ∈ Finset.range w, (x.testBit (k + j)).toNat * 2 ^ j := by
  intro w
  induction w with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, toNat_testBit, pow_succ, Nat.mod_mul,
      Nat.div_div_eq_div_mul, ← pow_add]
    ring

/-- **FIPS 204 Algorithm 9, read as a number.** The `c` bits Algorithm 9 emits for `x` are the
little-endian digits of `x mod 2^c` — which is exactly the truncation `MlDsaCodec.packBits` applies. -/
theorem mod_two_pow_eq_bitSum (x c : Nat) :
    x % 2 ^ c = ∑ j ∈ Finset.range c, (x.testBit j).toNat * 2 ^ j := by
  simpa using window_eq_bitSum x 0 c

/-- **The positional-numeral core (`packNat_bit`'s engine) — a real `∀`.** A little-endian base-`2^c`
number whose digits are `c`-bit truncations IS the base-2 number of those digits' bits, in FIPS 204
Algorithm 9's order (coefficient `m / c`, bit `m mod c`). Proved by induction on the number of
coefficients; the step is exactly "the top coefficient's `c` bits land at positions `[nc, nc+c)`". -/
theorem mixedRadix_eq_bitSum (c : Nat) (hc : 0 < c) (a : Nat → Nat) : ∀ n : Nat,
    (∑ i ∈ Finset.range n, (a i % 2 ^ c) * (2 ^ c) ^ i)
      = ∑ m ∈ Finset.range (n * c), ((a (m / c)).testBit (m % c)).toNat * 2 ^ m := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, show (k + 1) * c = k * c + c from by ring,
      Finset.sum_range_add]
    refine congrArg (_ + ·) ?_
    have hidx : ∀ j ∈ Finset.range c,
        ((a ((k * c + j) / c)).testBit ((k * c + j) % c)).toNat * 2 ^ (k * c + j)
          = 2 ^ (k * c) * (((a k).testBit j).toNat * 2 ^ j) := by
      intro j hj
      have hjc : j < c := Finset.mem_range.mp hj
      rw [show k * c + j = c * k + j from by ring, Nat.mul_add_div hc, Nat.mul_add_mod,
        Nat.div_eq_of_lt hjc, Nat.mod_eq_of_lt hjc, Nat.add_zero,
        show c * k + j = k * c + j from by ring, pow_add]
      ring
    rw [Finset.sum_congr rfl hidx, ← Finset.mul_sum, ← mod_two_pow_eq_bitSum,
      ← pow_mul, Nat.mul_comm k c]
    ring

/-- **`packNat_bit` — bit `m` of the DEPLOYED bignum is bit `m mod c` of coefficient `m / c`.**
This is the whole encoder bridge in one line: the little-endian mixed-radix integer
`MlDsaCodec.packBits` accumulates carries exactly the bits FIPS 204 Algorithm 9 / 16 lay down, in
exactly that order. No coefficient range hypothesis is needed — Algorithm 9's `x mod 2` loop and
`packBits`'s `% 2^c` truncate identically. -/
theorem packNat_bit (coeffs : Array Nat) (c : Nat) (hc : 0 < c) (m : Nat)
    (hm : m < coeffs.size * c) :
    (packNat coeffs c).testBit m = (coeffs[m / c]!).testBit (m % c) := by
  have hbits : packNat coeffs c
      = ∑ m' ∈ Finset.range (coeffs.size * c),
          ((coeffs[m' / c]!).testBit (m' % c)).toNat * 2 ^ m' :=
    mixedRadix_eq_bitSum c hc (fun i => coeffs[i]!) coeffs.size
  have hkey := extract_digit 2 (by norm_num)
    (fun m' => ((coeffs[m' / c]!).testBit (m' % c)).toNat)
    (fun i => toNat_testBit_lt_two _ _) (coeffs.size * c) m hm
  rw [Nat.testBit_eq_decide_div_mod_eq, hbits,
    show (∑ m' ∈ Finset.range (coeffs.size * c),
          ((coeffs[m' / c]!).testBit (m' % c)).toNat * 2 ^ m') / 2 ^ m % 2
        = ((coeffs[m / c]!).testBit (m % c)).toNat from hkey]
  cases (coeffs[m / c]!).testBit (m % c) <;> simp

/-! ## PART 1 — FIPS 204 Algorithms 9, 10, 16 and 28, transcribed.

These four definitions mention no executable: not `MlDsaCodec.packBits`, not `bytesToNatLE`, not
`MlDsaVerifyReal.w1Encode`. They are the objects a reader diffs against the printed standard. -/

/-- **FIPS 204 Algorithm 9 `IntegerToBits(x, α)`.** The standard's loop is
`for i = 0 … α−1: y[i] ← x mod 2; x ← ⌊x/2⌋`, i.e. bit `i` of `y` is `⌊x/2ⁱ⌋ mod 2` — least
significant bit FIRST. Values `≥ 2^α` are truncated, exactly as the standard's loop truncates them. -/
def integerToBits (x α : Nat) : List Bool := (List.range α).map (fun i => x.testBit i)

/-- **FIPS 204 Algorithm 10 `BitsToBytes(y)`.** The standard's loop is
`z[⌊i/8⌋] ← z[⌊i/8⌋] + y[i]·2^(i mod 8)`, i.e. byte `n` is `Σ_{j<8} y[8n+j]·2ʲ` — least significant
bit first within each byte. Bits past the end of `y` read as `0`, which is unreachable for a `y` whose
length is a multiple of 8 (the only case Algorithm 10 is applied to). -/
def bitsToBytes (y : List Bool) : List UInt8 :=
  (List.range (y.length / 8)).map (fun n =>
    UInt8.ofNat (∑ j ∈ Finset.range 8, (y.getD (8 * n + j) false).toNat * 2 ^ j))

/-- Algorithm 16's intermediate bit string `z ← z ‖ IntegerToBits(w[i], c)` over all coefficients. -/
def simpleBitPackBits (w : Poly) (c : Nat) : List Bool :=
  (List.range w.size).flatMap (fun i => integerToBits (w[i]!) c)

/-- **FIPS 204 Algorithm 16 `SimpleBitPack(w, b)`** at bit width `c = bitlen b`: concatenate each
coefficient's `c` bits (Algorithm 9), then pack the bit string into bytes (Algorithm 10). -/
def simpleBitPack (w : Poly) (c : Nat) : List UInt8 := bitsToBytes (simpleBitPackBits w c)

/-- **FIPS 204 §2.3 `bitlen b = ⌊log₂ b⌋ + 1`** — the number of bits needed to write `b`. -/
def bitlen (b : Nat) : Nat := Nat.log 2 b + 1

/-- **The Algorithm 28 bit width, DERIVED — not the literal `4`.** FIPS 204 Algorithm 28 calls
`SimpleBitPack(w₁[i], (q−1)/(2γ₂) − 1)`, so the width is `bitlen((q−1)/(2γ₂) − 1)`, computed here from
`MlDsaRing.q` and `MlDsaVerifyReal.gamma2`. If either deployed parameter were wrong, this width — and
with it `w1Encode_eq_spec` — would move. -/
def w1Bits : Nat := bitlen ((q - 1) / (2 * gamma2) - 1)

/-- At ML-DSA-65 (`q = 8380417`, `γ₂ = 261888`) the Algorithm 28 width is `bitlen 15 = 4`. A THEOREM,
computed from the parameters, not a transcribed constant. -/
theorem w1Bits_eq_four : w1Bits = 4 := by
  have hb : (q - 1) / (2 * gamma2) - 1 = 15 := by decide
  rw [w1Bits, hb, bitlen,
    show Nat.log 2 15 = 3 from Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)]

/-- **FIPS 204 Algorithm 28 `w1Encode(w₁)`.** Concatenate `SimpleBitPack(w₁[i], (q−1)/(2γ₂) − 1)` over
the `k = 6` rows. No executable definition occurs in this term. -/
def w1EncodeSpec (w1 : Array Poly) : List UInt8 :=
  (List.range paramK).flatMap (fun i => simpleBitPack (w1[i]!) w1Bits)

/-! ## PART 2 — indexing laws for the transcribed algorithms. -/

@[simp] theorem integerToBits_length (x α : Nat) : (integerToBits x α).length = α := by
  simp [integerToBits]

theorem integerToBits_getD (x α i : Nat) (hi : i < α) :
    (integerToBits x α).getD i false = x.testBit i := by
  simp [integerToBits, List.getD_eq_getElem?_getD, hi]

/-- A `range`-indexed `flatMap` of equal-length blocks has the expected length. -/
theorem flatMap_range_length (g : Nat → List Bool) (c : Nat) (hg : ∀ i, (g i).length = c) :
    ∀ n : Nat, ((List.range n).flatMap g).length = n * c := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp [hg]
    ring

/-- **The block-indexing law.** Position `m` of a `range`-indexed `flatMap` of `c`-long blocks is
position `m mod c` of block `m / c`. This is what turns Algorithm 16's `‖`-concatenation into the
bit-indexed form the arithmetic needs — derived, not assumed. -/
theorem flatMap_range_getD (g : Nat → List Bool) (c : Nat) (hc : 0 < c)
    (hg : ∀ i, (g i).length = c) : ∀ (n m : Nat), m < n * c →
      ((List.range n).flatMap g).getD m false = (g (m / c)).getD (m % c) false := by
  intro n
  induction n with
  | zero => intro m hm; omega
  | succ k ih =>
    intro m hm
    rw [show (k + 1) * c = k * c + c from by ring] at hm
    rw [List.range_succ, List.flatMap_append]
    have hlen : ((List.range k).flatMap g).length = k * c := flatMap_range_length g c hg k
    by_cases h : m < k * c
    · rw [getD_append_lt _ _ _ _ (by omega)]
      exact ih m h
    · have hge : k * c ≤ m := by omega
      have hlt : m - k * c < c := by omega
      have hsplit : m = c * k + (m - k * c) := by rw [Nat.mul_comm c k]; omega
      have hdiv : m / c = k := by
        conv_lhs => rw [hsplit]
        rw [Nat.mul_add_div hc, Nat.div_eq_of_lt hlt, Nat.add_zero]
      have hmod : m % c = m - k * c := by
        conv_lhs => rw [hsplit]
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by rw [hlen]; exact hge), hlen, hdiv, hmod]
      simp [List.getD_eq_getElem?_getD]

/-- **Algorithm 16's bit string, bit-indexed.** Bit `m` of `SimpleBitPack`'s intermediate string is
bit `m mod c` of coefficient `m / c` — the standard's `‖ IntegerToBits(w[i], c)` read positionally. -/
theorem simpleBitPackBits_getD (w : Poly) (c : Nat) (hc : 0 < c) (m : Nat) (hm : m < w.size * c) :
    (simpleBitPackBits w c).getD m false = (w[m / c]!).testBit (m % c) := by
  rw [simpleBitPackBits,
    flatMap_range_getD (fun i => integerToBits (w[i]!) c) c hc (fun i => by simp) w.size m hm]
  exact integerToBits_getD _ _ _ (Nat.mod_lt _ hc)

@[simp] theorem simpleBitPackBits_length (w : Poly) (c : Nat) :
    (simpleBitPackBits w c).length = w.size * c :=
  flatMap_range_length _ c (fun i => by simp) w.size

/-! ## PART 3 — THE ENCODER REFINEMENT.

`simpleBitPack_eq_packBits` is the row-level theorem; `w1Encode_eq_spec` assembles the `k = 6` rows.
Both are real `∀`-statements whose two sides share no computational content. -/

/-- **Algorithm 16 IS the deployed packer, one row — a real `∀`, and not `rfl`.** For EVERY
coefficient array and EVERY bit width `c` whose total bit-count is a whole number of bytes, FIPS 204
Algorithm 16 (`IntegerToBits` per coefficient, concatenated, then `BitsToBytes`) and
`MlDsaCodec.packBits` (accumulate `Σᵢ (cᵢ mod 2^c)·(2^c)ⁱ`, emit base-256 digits) produce the SAME
byte list.

NO coefficient-range hypothesis: both sides truncate to `c` bits, the standard's Algorithm 9 by its
`x mod 2` loop and `packBits` by `% 2^c`, so the agreement is unconditional in the coefficients. -/
theorem simpleBitPack_eq_packBits (w : Poly) (c : Nat) (hc : 0 < c) (h8 : w.size * c % 8 = 0) :
    simpleBitPack w c = (packBits w c).toList := by
  have hnb : 8 * (w.size * c / 8) = w.size * c := by omega
  apply List.ext_getElem
  · rw [show (packBits w c).toList.length = w.size * c / 8 from by
        rw [Array.length_toList, packBits_size]]
    simp [simpleBitPack, bitsToBytes, simpleBitPackBits_length]
  · intro n h1 h2
    have hn : n < w.size * c / 8 := by
      simpa [simpleBitPack, bitsToBytes, simpleBitPackBits_length] using h1
    have hwin : ∀ j ∈ Finset.range 8,
        ((simpleBitPackBits w c).getD (8 * n + j) false).toNat * 2 ^ j
          = ((packNat w c).testBit (8 * n + j)).toNat * 2 ^ j := by
      intro j hj
      have hj8 : j < 8 := Finset.mem_range.mp hj
      have hlt : 8 * n + j < w.size * c := by omega
      rw [simpleBitPackBits_getD w c hc _ hlt, packNat_bit w c hc _ hlt]
    have hsz : n < (packBits w c).size := by rw [packBits_size]; exact hn
    have hbyte : (packBits w c).toList[n]'h2 = (packBits w c)[n]! := by
      rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hsz]
      simp
    rw [hbyte, packBits_getElem w c n hn]
    simp only [simpleBitPack, bitsToBytes, List.getElem_map, List.getElem_range]
    refine congrArg UInt8.ofNat ?_
    rw [Finset.sum_congr rfl hwin, ← window_eq_bitSum (packNat w c) (8 * n) 8,
      show (2 : Nat) ^ 8 = 256 from by norm_num,
      show (2 : Nat) ^ (8 * n) = 256 ^ n from by rw [pow_mul]; norm_num]

/-- **FIPS 204 Algorithm 28 IS the deployed `w1Encode` — a real `∀`, and not `rfl`.** For EVERY
`k = 6`-row high-bits array whose rows carry 256 coefficients, the deployed
`MlDsaVerifyReal.w1Encode` (six `packBits _ 4` bignum packings, concatenated) emits exactly the byte
string FIPS 204 Algorithm 28 specifies (six `SimpleBitPack(·, (q−1)/(2γ₂) − 1)` bit packings,
concatenated).

This is the theorem `Fips204ChallengeHash.challengeHash_frames` consumes for its ENCODER leg. A wrong
packing width, endianness, row order or coefficient mask on either side falsifies it. -/
theorem w1Encode_eq_spec (w1 : Array Poly) (hrow : ∀ i, i < paramK → (w1[i]!).size = 256) :
    w1Encode w1 = w1EncodeSpec w1 := by
  have hshape : w1Encode w1
      = (packBits (w1[0]!) 4 ++ packBits (w1[1]!) 4 ++ packBits (w1[2]!) 4
          ++ packBits (w1[3]!) 4 ++ packBits (w1[4]!) 4 ++ packBits (w1[5]!) 4).toList := by
    unfold w1Encode
    simp [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, paramK,
      List.range']
  have hrowpack : ∀ i, i < paramK →
      simpleBitPack (w1[i]!) w1Bits = (packBits (w1[i]!) 4).toList := by
    intro i hi
    rw [w1Bits_eq_four]
    exact simpleBitPack_eq_packBits (w1[i]!) 4 (by norm_num) (by simp [hrow i hi])
  have hr : List.range paramK = [0, 1, 2, 3, 4, 5] := by decide
  rw [hshape, w1EncodeSpec, hr]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Array.toList_append,
    hrowpack 0 (by decide), hrowpack 1 (by decide), hrowpack 2 (by decide),
    hrowpack 3 (by decide), hrowpack 4 (by decide), hrowpack 5 (by decide),
    List.append_assoc]

/-! ## PART 4 — the cross-standard tie: FIPS 204 Algorithm 10 vs FIPS 202 §B.1.

`Fips204ChallengeHash.challengeHashSpec` feeds `w1EncodeSpec`'s BYTES back through FIPS 202 §B.1's
`bitsOfBytes` into the bit sponge. If FIPS 204's Algorithm 10 and FIPS 202's §B.1 disagreed about
which bit of which byte is which, that composition would silently re-scramble the encoding. They do
NOT disagree — and that is a theorem here, not a transcription. -/

/-- Bit `i < 8` of the byte `UInt8.ofNat s` is bit `i` of `s` (the `mod 256` truncation is invisible
below bit 8). -/
theorem getLsbD_ofNat_lt (s i : Nat) (hi : i < 8) :
    (UInt8.ofNat s).toBitVec.getLsbD i = s.testBit i := by
  simp only [UInt8.ofNat, BitVec.getLsbD, BitVec.toNat_ofNat]
  rw [show (2 : Nat) ^ 8 = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow]
  simp [hi]

/-- **Algorithm 10 and §B.1 are mutually inverse — a real `∀`.** Reading an Algorithm 10 byte string
back with FIPS 202 §B.1's `bitsOfBytes` recovers the original bit string, for EVERY bit string whose
length is a whole number of bytes. This is what licenses `challengeHashSpec`'s
`SHAKE256 (bitsOfBytes (μ ++ w1EncodeSpec w₁))`: the sponge sees exactly the bits Algorithm 16 laid
down. A byte-order or bit-order mismatch between the two standards' conventions would falsify it. -/
theorem bitsOfBytes_bitsToBytes (y : List Bool) (h8 : y.length % 8 = 0) :
    bitsOfBytes (bitsToBytes y) = y := by
  have hlen : (bitsToBytes y).length = y.length / 8 := by simp [bitsToBytes]
  apply List.ext_getElem
  · rw [bitsOfBytes_length, hlen]; omega
  · intro m h1 h2
    have hq : m / 8 < (bitsToBytes y).length := by rw [hlen]; omega
    have hmod8 : m % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have hcomp : 8 * (m / 8) + m % 8 = m := by omega
    rw [← List.getD_eq_getElem _ false h1, ← List.getD_eq_getElem _ false h2,
      bitsOfBytes_getD, List.getD_eq_getElem _ _ hq,
      show (bitsToBytes y)[m / 8]
          = UInt8.ofNat (∑ j ∈ Finset.range 8, (y.getD (8 * (m / 8) + j) false).toNat * 2 ^ j)
        from by simp [bitsToBytes]]
    have hdig : ∀ i, (y.getD (8 * (m / 8) + i) false).toNat < 2 := by
      intro i; cases y.getD (8 * (m / 8) + i) false <;> decide
    have hkey := extract_digit 2 (by norm_num)
      (fun j => (y.getD (8 * (m / 8) + j) false).toNat) hdig 8 (m % 8) hmod8
    rw [getLsbD_ofNat_lt _ _ hmod8, Nat.testBit_eq_decide_div_mod_eq,
      show (∑ j ∈ Finset.range 8, (y.getD (8 * (m / 8) + j) false).toNat * 2 ^ j)
            / 2 ^ (m % 8) % 2
          = (y.getD (8 * (m / 8) + m % 8) false).toNat from hkey, hcomp]
    cases y.getD m false <;> simp

/-! ## PART 5 — TEETH.

Every definition above COMPUTES, and the values are pinned by KERNEL `decide` — no `native_decide`,
no compiled-evaluation trust. These are the anti-vacuity anchors for the encoder side of
`Fips204ChallengeHash.challengeHashSpec`. -/

/-- Algorithm 9 emits LEAST SIGNIFICANT BIT FIRST. Flip the endianness and this fails. -/
example : integerToBits 8 4 = [false, false, false, true] := by decide
example : integerToBits 15 4 = [true, true, true, true] := by decide
/-- Algorithm 9 truncates above `2^α`, exactly as the standard's `x ← ⌊x/2⌋` loop does. -/
example : integerToBits 31 4 = integerToBits 15 4 := by decide

/-- **The Algorithm 16 evaluation anchor.** Four 4-bit coefficients `1,2,3,4` pack to `0x21 0x43`:
the bit string is `1000 0100 1100 0010`, whose first byte is `1+2⁵ = 0x21`. -/
example : simpleBitPack #[1, 2, 3, 4] 4 = [0x21, 0x43] := by decide

/-- The DEPLOYED packer produces the same two bytes — `simpleBitPack_eq_packBits` is non-vacuous at a
point where both sides do real work. -/
example : (packBits #[1, 2, 3, 4] 4).toList = [0x21, 0x43] := by
  rw [← simpleBitPack_eq_packBits #[1, 2, 3, 4] 4 (by norm_num) (by decide)]
  decide

/-- Algorithm 16 is ORDER-SENSITIVE: reversing the coefficients changes the bytes. A stub, a constant,
or a symmetric encoder could not satisfy this. -/
example : simpleBitPack #[1, 2, 3, 4] 4 ≠ simpleBitPack #[4, 3, 2, 1] 4 := by decide

/-- Algorithm 16 is WIDTH-SENSITIVE: the same coefficients at 8 bits/coeff give different bytes. -/
example : simpleBitPack #[1, 2, 3, 4] 4 ≠ simpleBitPack #[1, 2, 3, 4] 8 := by decide

/-- The §B.1 ↔ Algorithm 10 tie FIRES on the SHAKE domain-separation bytes (`0x1F`, `0x80`), whose bit
patterns are exactly what the padding rule depends on. -/
example : bitsToBytes (bitsOfBytes [0x1F, 0x80]) = [0x1F, 0x80] := by decide

#assert_axioms toNat_testBit
#assert_axioms window_eq_bitSum
#assert_axioms mod_two_pow_eq_bitSum
#assert_axioms mixedRadix_eq_bitSum
#assert_axioms packNat_bit
#assert_axioms flatMap_range_length
#assert_axioms flatMap_range_getD
#assert_axioms simpleBitPackBits_getD
#assert_axioms w1Bits_eq_four
#assert_axioms simpleBitPack_eq_packBits
#assert_axioms w1Encode_eq_spec
#assert_axioms bitsOfBytes_bitsToBytes

end Dregg2.Crypto.Fips204BitPack
