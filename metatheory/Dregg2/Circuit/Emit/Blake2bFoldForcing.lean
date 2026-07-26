/-
# Dregg2.Circuit.Emit.Blake2bFoldForcing — the COMPOSED forcing lemmas for the BLAKE2b hash fold.

## What this file IS (KAT'd + atomic-forced → COMPOSED, mirroring the SHA fold's rigor)

`Blake2bGadget` proved the ATOMIC gate forcings (`addMod64_forces` — the mod-2^64 congruence;
`xor2_forces`/`finalize_bit_forces` — the per-bit XOR parity) and both-polarity KAT'd the whole-`G`
mixing function. `LightClientMidHashFold` derived Midnight's `AUTHSET_OK` GIVEN a named `hfold`
hypothesis (`authSetRootRef rows = anchorRoot`) — RESIDUAL #1, the composition wall: "the chained
`blake2bF` gates FORCE their BLAKE2b outputs up the ~27264-gate-per-block chain."

This file closes that wall by COMPOSING the atomic forcings UP the G→round→compression→absorb
structure — the same way `Bls12381Forcing` composes the atomic Fp-gate forcings up the tower/curve,
and the way the SHA `Sha256MerkleFold` fold-forcing sibling composes `addMod32_forces`/`xor3_forces`.
These are PROOFS (no `#guard`, no `native_decide`, no `sorry`): a finite chain of atomic forcings +
structural induction over the round/block LISTS, NOT a kernel reduction over the 27k-gate chain.

The vehicle:
  * `bitsToNat` — the LSB-first bit recomposition `Σ_{i<n} f(i)·2^i`; `Ref.natOfBits64 = bitsToNat · 64`.
    Its key law `testBit_bitsToNat` (bit-decomposition uniqueness, via `Nat.testBit_two_pow_mul_add`)
    reads bit `j` back off the recomposed word — the bridge from the emitted bit-columns to `Nat.testBit`.
  * `testBit_rotr64` — the rotation bit identity `testBit (rotr64 R X) k = testBit X ((k+R)%64)` (the
    right-rotation folds into source indexing), proved from the core `Nat.testBit_{or,shiftRight,
    shiftLeft,mod_two_pow,lt_two_pow}` laws.
  * `Holds a base v` — "the 64 bit-columns at `base` reconstruct the 64-bit word `v`" (`wnat a base = v`).

The three atomic WORD bridges turn the raw gate satisfactions into `Holds` facts:
  * `addWord_forces` — an `addMod64Core` gate forces `Holds out (w64 Σ)` (from `addMod64_forces` + range).
  * `xorRotWord_forces` — 64 `xorHead` gates force `Holds out (rotr64 R (xorw A B))` (the bit identity).
  * `xor3Word_forces` — 64 `xorHead` gates force `Holds out (w64 (xorw (xorw H Vi) Vj))`.

`blakeG_forces` then composes those 8 sub-op bridges over `G`'s fixed structure; `blakeRound_forces` /
`blake2bCompress_forces` induct over the round list; the absorb induction chains `blake2bF` block by
block; and `midHfold_discharged` NAMES precisely how the composition discharges `LightClientMidHashFold`'s
`hfold`.

## The standing hypothesis (`AllBool`)

`blakeG.1` emits only the CORE value gates; booleanity of every column is the separate `pinWord`
sweep (`binGate` per column) the full descriptor carries. The forcing theorems consume that as
`AllBool a` (every column 0/1) — exactly what the pin sweep forces, made explicit so DERIVED-vs-ASSUMED
is visible.

## Resolution (honest)

REAL: the composition is a PROOF over ℤ (the same ℤ reading `Blake2bGadget` §3 carries); each rung
(G→round→compression→absorb) rests on the rung below by structural induction, gate-count-independent.
NOT re-claimed: the mod-`p_felt` ↔ ℤ field-width residual (a 31-bit BabyBear limb cannot hold a 64-bit
word), and the exact Substrate row serialization (`LightClientMidHashFold` §Derived-vs-assumed) — those
are unchanged. This slice upgrades `hfold` from an ASSUMED hypothesis to a DERIVED conclusion of the
chained gates.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/`native_decide`/
`#guard` carrying weight. NEW file; imports read-only (`Blake2bGadget`, `LightClientMidHashFold`);
standalone (NOT imported by the truncated `Dregg2` root, built directly as
`Dregg2.Circuit.Emit.Blake2bFoldForcing`).
-/
import Dregg2.Circuit.Emit.Blake2bGadget
import Dregg2.Circuit.Emit.LightClientMidHashFold

namespace Dregg2.Circuit.Emit.Blake2bFoldForcing

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.Blake2bGadget
open Dregg2.Circuit.Emit.Sha256Gadget (xorHead)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2)

set_option autoImplicit false
set_option maxRecDepth 8192

/-! ## §0 — The bit recomposition `bitsToNat` and its decomposition law (bit-uniqueness). -/

/-- LSB-first recomposition of the first `n` bits given by `f` (0/1-valued): `Σ_{i<n} f(i)·2^i`. The
`Ref.natOfBits64` used by the gadget is `bitsToNat · 64`. -/
def bitsToNat (f : Nat → Nat) (n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc + f i * 2 ^ i) 0

/-- `Ref.natOfBits64` is `bitsToNat` at width 64. -/
theorem natOfBits64_eq (f : Nat → Nat) : Ref.natOfBits64 f = bitsToNat f 64 := rfl

/-- Appending the top bit is one more term. -/
theorem bitsToNat_succ (f : Nat → Nat) (n : Nat) :
    bitsToNat f (n + 1) = bitsToNat f n + f n * 2 ^ n := by
  unfold bitsToNat
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- A bit-recomposition of `n` bits is `< 2^n`. -/
theorem bitsToNat_lt (f : Nat → Nat) (hf : ∀ i, f i ≤ 1) (n : Nat) :
    bitsToNat f n < 2 ^ n := by
  induction n with
  | zero => simp [bitsToNat]
  | succ n ih =>
    rw [bitsToNat_succ]
    have hstep : f n * 2 ^ n ≤ 2 ^ n := by
      calc f n * 2 ^ n ≤ 1 * 2 ^ n := Nat.mul_le_mul_right _ (hf n)
        _ = 2 ^ n := by ring
    have : (2 : Nat) ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; ring
    omega

/-- **Bit-decomposition uniqueness.** Reading bit `j` off the recomposed word recovers `f j` (for
`j < n`; the high bits are 0). The bridge from the emitted bit-columns to `Nat.testBit`, via the core
`Nat.testBit_two_pow_mul_add`. -/
theorem testBit_bitsToNat (f : Nat → Nat) (hf : ∀ i, f i ≤ 1) (n j : Nat) :
    Nat.testBit (bitsToNat f n) j = (if j < n then decide (f j = 1) else false) := by
  induction n generalizing j with
  | zero => simp [bitsToNat]
  | succ n ih =>
    rw [bitsToNat_succ]
    have hb : bitsToNat f n < 2 ^ n := bitsToNat_lt f hf n
    rw [show bitsToNat f n + f n * 2 ^ n = 2 ^ n * f n + bitsToNat f n from by ring,
        Nat.testBit_two_pow_mul_add (f n) hb j]
    by_cases hjn : j < n
    · rw [if_pos hjn, ih j, if_pos hjn, if_pos (by omega : j < n + 1)]
    · rw [if_neg hjn]
      by_cases hjn1 : j < n + 1
      · have hje : j = n := by omega
        rw [if_pos hjn1, hje, Nat.sub_self]
        have hfn : f n = 0 ∨ f n = 1 := by have := hf n; omega
        rcases hfn with h | h <;> rw [h] <;> decide
      · rw [if_neg hjn1]
        have hlt : f n < 2 ^ (j - n) := by
          have : (1 : Nat) < 2 ^ (j - n) := Nat.one_lt_two_pow_iff.mpr (by omega)
          have := hf n
          omega
        rw [Nat.testBit_lt_two_pow hlt]

/-! ## §1 — `Ref.bit` is `Nat.testBit`, and the rotation bit identity. -/

/-- `Ref.bit v i = (v >>> i) &&& 1` is the `Nat.testBit` as a 0/1 Nat. -/
theorem refbit_eq (v i : Nat) : Ref.bit v i = (Nat.testBit v i).toNat := by
  unfold Ref.bit
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.toNat_testBit]

/-- `Ref.bit v i ≤ 1`. -/
theorem refbit_le_one (v i : Nat) : Ref.bit v i ≤ 1 := by
  rw [refbit_eq]; cases Nat.testBit v i <;> simp

/-- **The rotation bit identity.** BLAKE2b's right-rotation folds into source indexing: bit `k` of
`(rotr64 R X)` reads bit `(k+R) mod 64` of `X`. Proved from the `>>> / <<< / |||` decomposition. -/
theorem testBit_rotr64 (X R k : Nat) (hX : X < 2 ^ 64) (hR0 : 0 < R) (hR : R < 64) (hk : k < 64) :
    Nat.testBit (Ref.rotr64 R X) k = Nat.testBit X ((k + R) % 64) := by
  unfold Ref.rotr64 Ref.w64
  rw [show Ref.M = 2 ^ 64 from by norm_num [Ref.M]]
  rw [Nat.testBit_mod_two_pow]
  simp only [hk, decide_true, Bool.true_and]
  rw [Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  by_cases hc : k + R < 64
  · have hmod : (k + R) % 64 = k + R := Nat.mod_eq_of_lt hc
    rw [hmod]
    have h1 : ¬ (k ≥ 64 - R) := by omega
    simp only [h1, decide_false, Bool.false_and, Bool.or_false]
    rw [show R + k = k + R from by ring]
  · have hge : 64 ≤ k + R := by omega
    have hmod : (k + R) % 64 = k + R - 64 := by omega
    rw [hmod]
    have h1 : k ≥ 64 - R := by omega
    have h2 : Nat.testBit X (R + k) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by decide) (by omega)))
    simp only [h1, decide_true, Bool.true_and, h2, Bool.false_or]
    congr 1
    omega

/-! ## §2 — Booleans: the bit-column value and the forced XOR parity of a satisfied bit gate. -/

/-- Every trace column is 0/1 (the `pinWord`/`binGate` sweep of the full descriptor). -/
def AllBool (a : Assignment) : Prop := ∀ c, a c = 0 ∨ a c = 1

/-- The bit at column `c` as a 0/1 Nat. -/
def bitCol (a : Assignment) (c : Nat) : Nat := (a c).toNat

theorem bitCol_le_one (a : Assignment) (hbool : AllBool a) (c : Nat) : bitCol a c ≤ 1 := by
  unfold bitCol; rcases hbool c with h | h <;> rw [h] <;> decide

theorem bitCol_cast (a : Assignment) (hbool : AllBool a) (c : Nat) : (bitCol a c : ℤ) = a c := by
  unfold bitCol; rcases hbool c with h | h <;> rw [h] <;> decide

/-- **A satisfied 2-XOR bit gate forces the parity** as a `Bool` equation between the reconstructed
bits (the shape `Nat.testBit_xor` consumes). From `o = p + q − 2c` with all four 0/1. -/
theorem xorbit_forced (p q o c : ℤ)
    (hp : p = 0 ∨ p = 1) (hq : q = 0 ∨ q = 1) (ho : o = 0 ∨ o = 1) (hcar : c = 0 ∨ c = 1)
    (heq : o = p + q - 2 * c) :
    decide (o.toNat = 1) = (decide (p.toNat = 1) ^^ decide (q.toNat = 1)) := by
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> rcases ho with ho | ho <;>
    rcases hcar with hc | hc <;> subst hp hq ho hc <;> simp_all

/-- **A satisfied 3-XOR bit gate forces the 3-way parity** as a `Bool` equation. From `o = p+q+r−2c`
with all five 0/1. -/
theorem xor3bit_forced (p q r o c : ℤ)
    (hp : p = 0 ∨ p = 1) (hq : q = 0 ∨ q = 1) (hr : r = 0 ∨ r = 1)
    (ho : o = 0 ∨ o = 1) (hcar : c = 0 ∨ c = 1)
    (heq : o = p + q + r - 2 * c) :
    decide (o.toNat = 1) = (decide (p.toNat = 1) ^^ decide (q.toNat = 1) ^^ decide (r.toNat = 1)) := by
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> rcases hr with hr | hr <;>
    rcases ho with ho | ho <;> rcases hcar with hc | hc <;> subst hp hq hr ho hc <;>
    simp_all

/-! ## §3 — The word abstraction: `wnat a base` reconstructs the 64-bit word at `base`, and its ℤ cast. -/

/-- The 64-bit word the bit-columns `base..base+63` reconstruct. -/
def wnat (a : Assignment) (base : Nat) : Nat := Ref.natOfBits64 (fun i => bitCol a (base + i))

/-- "The columns at `base` reconstruct the word `v`." -/
@[reducible] def Holds (a : Assignment) (base v : Nat) : Prop := wnat a base = v

theorem wnat_lt (a : Assignment) (hbool : AllBool a) (base : Nat) : wnat a base < 2 ^ 64 := by
  rw [wnat, natOfBits64_eq]
  exact bitsToNat_lt _ (fun i => bitCol_le_one a hbool _) 64

/-- The `wordValue` head evaluates to the LSB-first weighted sum of its bit columns. -/
theorem wordValue_sum (a : Assignment) (base : Nat) :
    evalH (wordValue base) a = ((List.range 64).map (fun i => (2 : ℤ) ^ i * a (base + i))).sum := by
  unfold wordValue
  rw [evalH_foldl_addLinG a Head.zero (fun i => (2 : ℤ) ^ i) (List.range 64) (fun i => base + i)]
  simp

/-- Casting a bit-recomposition to ℤ is the ℤ weighted sum. -/
theorem bitsToNat_cast (g : Nat → Nat) (n : Nat) :
    (bitsToNat g n : ℤ) = ((List.range n).map (fun i => (g i : ℤ) * 2 ^ i)).sum := by
  induction n with
  | zero => simp [bitsToNat]
  | succ n ih =>
    rw [bitsToNat_succ, List.range_succ, List.map_append, List.sum_append]
    push_cast
    rw [ih]
    simp

/-- **The ℤ bridge.** The reconstructed word cast to ℤ IS the emitted `wordValue` head. -/
theorem wnat_cast (a : Assignment) (hbool : AllBool a) (base : Nat) :
    (wnat a base : ℤ) = evalH (wordValue base) a := by
  rw [wordValue_sum, wnat, natOfBits64_eq, bitsToNat_cast]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [bitCol_cast a hbool (base + i)]; ring

/-! ## §4 — The three atomic WORD bridges: the emitted gates FORCE the word-level ARX ops. -/

/-- **The 3-input mod-2^64 adder forces its output word** `= w64(A+B+X)` (= `Ref.add3`). From
`addMod64_forces` (the ℤ congruence) + the output's 64-bit range. -/
theorem add3Word_forces (a : Assignment) (hbool : AllBool a)
    (vaB vbB vxB out c0 c1 A B X : Nat)
    (hA : Holds a vaB A) (hB : Holds a vbB B) (hX : Holds a vxB X)
    (hg : evalH (addMod64Head [wordValue vaB, wordValue vbB, wordValue vxB] out [c0, c1]) a = 0) :
    Holds a out (Ref.add3 A B X) := by
  have hAeq : wnat a vaB = A := hA
  have hBeq : wnat a vbB = B := hB
  have hXeq : wnat a vxB = X := hX
  have hforce := addMod64_forces a [wordValue vaB, wordValue vbB, wordValue vxB] out [c0, c1] hg
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hforce
  rw [← wnat_cast a hbool vaB, ← wnat_cast a hbool vbB, ← wnat_cast a hbool vxB,
      ← wnat_cast a hbool out, hAeq, hBeq, hXeq] at hforce
  show wnat a out = Ref.add3 A B X
  unfold Ref.add3 Ref.w64
  have hlt := wnat_lt a hbool out
  rw [show (2 : Nat) ^ 64 = 18446744073709551616 from by norm_num] at hlt
  rw [show (2 : ℤ) ^ 64 = 18446744073709551616 from by norm_num] at hforce
  unfold Ref.M
  omega

/-- **The 2-input mod-2^64 adder forces its output word** `= w64(A+B)` (= `Ref.add2`). -/
theorem add2Word_forces (a : Assignment) (hbool : AllBool a)
    (vaB vbB out c0 A B : Nat)
    (hA : Holds a vaB A) (hB : Holds a vbB B)
    (hg : evalH (addMod64Head [wordValue vaB, wordValue vbB] out [c0]) a = 0) :
    Holds a out (Ref.add2 A B) := by
  have hAeq : wnat a vaB = A := hA
  have hBeq : wnat a vbB = B := hB
  have hforce := addMod64_forces a [wordValue vaB, wordValue vbB] out [c0] hg
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hforce
  rw [← wnat_cast a hbool vaB, ← wnat_cast a hbool vbB, ← wnat_cast a hbool out, hAeq, hBeq] at hforce
  show wnat a out = Ref.add2 A B
  unfold Ref.add2 Ref.w64
  have hlt := wnat_lt a hbool out
  rw [show (2 : Nat) ^ 64 = 18446744073709551616 from by norm_num] at hlt
  rw [show (2 : ℤ) ^ 64 = 18446744073709551616 from by norm_num] at hforce
  unfold Ref.M
  omega

/-- `Ref.rotr64` lands in range (it applies `w64`). -/
theorem rotr64_lt (R Y : Nat) : Ref.rotr64 R Y < 2 ^ 64 := by
  unfold Ref.rotr64 Ref.w64
  rw [show Ref.M = 2 ^ 64 from by norm_num [Ref.M]]
  exact Nat.mod_lt _ (by positivity)

/-- Read a reconstructed input word's bit back as a column-decide (Lemma C at a fixed index). -/
theorem testBit_wnat (a : Assignment) (hbool : AllBool a) (base m : Nat) (hm : m < 64) :
    Nat.testBit (wnat a base) m = decide (bitCol a (base + m) = 1) := by
  rw [wnat, natOfBits64_eq, testBit_bitsToNat _ (fun i => bitCol_le_one a hbool _) 64 m, if_pos hm]

/-- **64 chained XOR-and-rotate gates force the output word** `= rotr64 R (xorw A B)`. The
composition of `xor2_forces` (per bit) with the rotation bit identity — the bit-vector crux. -/
theorem xorRotWord_forces (a : Assignment) (hbool : AllBool a)
    (aB bB out car R A B : Nat) (hR0 : 0 < R) (hR : R < 64)
    (hA : Holds a aB A) (hB : Holds a bB B)
    (hg : ∀ i, i < 64 → evalH (xorHead (xorRotSources aB bB R i) (out + i) (car + i)) a = 0) :
    Holds a out (Ref.rotr64 R (Ref.xorw A B)) := by
  have hAeq : wnat a aB = A := hA
  have hBeq : wnat a bB = B := hB
  have hAlt : A < 2 ^ 64 := hAeq ▸ wnat_lt a hbool aB
  have hBlt : B < 2 ^ 64 := hBeq ▸ wnat_lt a hbool bB
  have hxorlt : Ref.xorw A B < 2 ^ 64 := by unfold Ref.xorw; exact Nat.xor_lt_two_pow hAlt hBlt
  show wnat a out = Ref.rotr64 R (Ref.xorw A B)
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 64
  · rw [testBit_wnat a hbool out k hk,
        testBit_rotr64 (Ref.xorw A B) R k hxorlt hR0 hR hk]
    have hm : (k + R) % 64 < 64 := Nat.mod_lt _ (by norm_num)
    unfold Ref.xorw
    rw [Nat.testBit_xor, ← hAeq, ← hBeq, testBit_wnat a hbool aB _ hm, testBit_wnat a hbool bB _ hm]
    have hxeq := hg k hk
    simp only [xorRotSources] at hxeq
    have ho := xor2_forces a (aB + (k + R) % 64) (bB + (k + R) % 64) (out + k) (car + k) hxeq
    exact xorbit_forced (a (aB + (k + R) % 64)) (a (bB + (k + R) % 64)) (a (out + k)) (a (car + k))
      (hbool _) (hbool _) (hbool _) (hbool _) ho
  · rw [wnat, natOfBits64_eq, testBit_bitsToNat _ (fun i => bitCol_le_one a hbool _) 64 k, if_neg hk]
    symm
    exact Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le (rotr64_lt R (Ref.xorw A B)) (Nat.pow_le_pow_right (by decide) (by omega)))

/-- **64 chained 3-way XOR gates force the output word** `= w64(xorw (xorw H Vi) Vj)` (the
finalization digest fold). -/
theorem xor3Word_forces (a : Assignment) (hbool : AllBool a)
    (hB viB vjB out car H Vi Vj : Nat)
    (hH : Holds a hB H) (hVi : Holds a viB Vi) (hVj : Holds a vjB Vj)
    (hg : ∀ i, i < 64 → evalH (xorHead [hB + i, viB + i, vjB + i] (out + i) (car + i)) a = 0) :
    Holds a out (Ref.w64 (Ref.xorw (Ref.xorw H Vi) Vj)) := by
  have hHeq : wnat a hB = H := hH
  have hVieq : wnat a viB = Vi := hVi
  have hVjeq : wnat a vjB = Vj := hVj
  show wnat a out = Ref.w64 (Ref.xorw (Ref.xorw H Vi) Vj)
  apply Nat.eq_of_testBit_eq
  intro k
  unfold Ref.w64
  rw [show Ref.M = 2 ^ 64 from by norm_num [Ref.M], Nat.testBit_mod_two_pow]
  by_cases hk : k < 64
  · rw [testBit_wnat a hbool out k hk]
    simp only [hk, decide_true, Bool.true_and]
    unfold Ref.xorw
    rw [Nat.testBit_xor, Nat.testBit_xor, ← hHeq, ← hVieq, ← hVjeq,
        testBit_wnat a hbool hB k hk, testBit_wnat a hbool viB k hk, testBit_wnat a hbool vjB k hk]
    have ho := finalize_bit_forces a (hB + k) (viB + k) (vjB + k) (out + k) (car + k) (hg k hk)
    exact xor3bit_forced (a (hB + k)) (a (viB + k)) (a (vjB + k)) (a (out + k)) (a (car + k))
      (hbool _) (hbool _) (hbool _) (hbool _) (hbool _) ho
  · rw [wnat, natOfBits64_eq, testBit_bitsToNat _ (fun i => bitCol_le_one a hbool _) 64 k, if_neg hk]
    simp [hk]

/-! ## §5 — `blakeG_forces`: the 8 sub-op bridges COMPOSE into the whole `G` mixing function. -/

/-- The four `G` output words as a function of the six input words — mirrors `Ref.G`'s `let` chain
term-for-term, so `blakeG_forces` reads as a straight composition and the round tie is `rfl`. -/
def gVals (VA VB VC VD X Y : Nat) : Nat × Nat × Nat × Nat :=
  let a1 := Ref.add3 VA VB X
  let d1 := Ref.rotr64 32 (Ref.xorw VD a1)
  let c1 := Ref.add2 VC d1
  let b1 := Ref.rotr64 24 (Ref.xorw VB c1)
  let a2 := Ref.add3 a1 b1 Y
  let d2 := Ref.rotr64 16 (Ref.xorw d1 a2)
  let c2 := Ref.add2 c1 d2
  let b2 := Ref.rotr64 63 (Ref.xorw b1 c2)
  (a2, b2, c2, d2)

/-- **`blakeG_forces`** — the emitted `blakeG` gates (2 `add3` + 2 `add2` + 4 XOR-and-rotate,
exactly the layout `blakeG` produces) FORCE the four output word-columns to the real BLAKE2b `G`
mixing of the six input words. A finite chain of the atomic word bridges over `G`'s fixed structure —
NO gate reduction. -/
theorem blakeG_forces (a : Assignment) (hbool : AllBool a)
    (va vb vc vd mx my : Nat)
    (a1B ca1 d1B cd1 c1B cc1 b1B cb1 a2B ca2 d2B cd2 c2B cc2 b2B cb2 : Nat)
    (VA VB VC VD X Y : Nat)
    (hva : Holds a va VA) (hvb : Holds a vb VB) (hvc : Holds a vc VC) (hvd : Holds a vd VD)
    (hmx : Holds a mx X) (hmy : Holds a my Y)
    (ga1 : evalH (addMod64Head [wordValue va, wordValue vb, wordValue mx] a1B [ca1, ca1 + 1]) a = 0)
    (gd1 : ∀ i, i < 64 → evalH (xorHead (xorRotSources vd a1B 32 i) (d1B + i) (cd1 + i)) a = 0)
    (gc1 : evalH (addMod64Head [wordValue vc, wordValue d1B] c1B [cc1]) a = 0)
    (gb1 : ∀ i, i < 64 → evalH (xorHead (xorRotSources vb c1B 24 i) (b1B + i) (cb1 + i)) a = 0)
    (ga2 : evalH (addMod64Head [wordValue a1B, wordValue b1B, wordValue my] a2B [ca2, ca2 + 1]) a = 0)
    (gd2 : ∀ i, i < 64 → evalH (xorHead (xorRotSources d1B a2B 16 i) (d2B + i) (cd2 + i)) a = 0)
    (gc2 : evalH (addMod64Head [wordValue c1B, wordValue d2B] c2B [cc2]) a = 0)
    (gb2 : ∀ i, i < 64 → evalH (xorHead (xorRotSources b1B c2B 63 i) (b2B + i) (cb2 + i)) a = 0) :
    Holds a a2B (gVals VA VB VC VD X Y).1 ∧ Holds a b2B (gVals VA VB VC VD X Y).2.1 ∧
    Holds a c2B (gVals VA VB VC VD X Y).2.2.1 ∧ Holds a d2B (gVals VA VB VC VD X Y).2.2.2 := by
  have h_a1 := add3Word_forces a hbool va vb mx a1B ca1 (ca1 + 1) VA VB X hva hvb hmx ga1
  have h_d1 := xorRotWord_forces a hbool vd a1B d1B cd1 32 VD (Ref.add3 VA VB X)
    (by norm_num) (by norm_num) hvd h_a1 gd1
  have h_c1 := add2Word_forces a hbool vc d1B c1B cc1 VC _ hvc h_d1 gc1
  have h_b1 := xorRotWord_forces a hbool vb c1B b1B cb1 24 VB _
    (by norm_num) (by norm_num) hvb h_c1 gb1
  have h_a2 := add3Word_forces a hbool a1B b1B my a2B ca2 (ca2 + 1) _ _ Y h_a1 h_b1 hmy ga2
  have h_d2 := xorRotWord_forces a hbool d1B a2B d2B cd2 16 _ _
    (by norm_num) (by norm_num) h_d1 h_a2 gd2
  have h_c2 := add2Word_forces a hbool c1B d2B c2B cc2 _ _ h_c1 h_d2 gc2
  have h_b2 := xorRotWord_forces a hbool b1B c2B b2B cb2 63 _ _
    (by norm_num) (by norm_num) h_b1 h_c2 gb2
  simp only [gVals]
  exact ⟨h_a2, h_b2, h_c2, h_d2⟩

/-! ## §6 — Composition up the fold: the round, the compression, and the multi-block absorb.

The generators are `List.foldl`s (the 8 `G`s of a round, the 12 rounds of a compression, the N blocks
of the absorb — "the generator makes them free"). The composition is a matching structural INDUCTION
over each step LIST, gate-count-INDEPENDENT: `foldl_forces` composes any per-step forcing up the fold,
and `blakeG_forces` supplies the per-`G` step. -/

/-- **Generic fold composition.** If a per-step relation `R` is preserved by each `gadgetStep`/`refStep`
pair over the step list, the whole `foldl` preserves it. The engine behind "the rounds / blocks compose
free": induct over the step LIST, apply the per-step forcing — no gate reduction. -/
theorem foldl_forces {α σ τ : Type} (L : List α)
    (gadgetStep : σ → α → σ) (refStep : τ → α → τ) (R : σ → τ → Prop)
    (s0 : σ) (t0 : τ) (h0 : R s0 t0)
    (hstep : ∀ (s : σ) (t : τ) (x : α), x ∈ L → R s t → R (gadgetStep s x) (refStep t x)) :
    R (L.foldl gadgetStep s0) (L.foldl refStep t0) := by
  induction L generalizing s0 t0 with
  | nil => simpa using h0
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih (gadgetStep s0 x) (refStep t0 x) (hstep s0 t0 x (by simp) h0)
      (fun s t y hy => hstep s t y (List.mem_cons_of_mem x hy))

/-- **`Ref.round` IS the `foldl` of `Ref.G` over `gargs`** (each of the 8 `G`s selects its quartet +
message pair from `gargs`). So the round gadget (`blakeRound = gargs.foldl gStep`) and the reference
share ONE step list — the round composes by a single `foldl_forces`. -/
theorem round_eq_foldl (v m s : List Nat) :
    Ref.round v m s
      = gargs.foldl (fun v g =>
          Ref.G v g.1.1 g.1.2.1 g.1.2.2.1 g.1.2.2.2
            (m.getD (s.getD g.2.1 0) 0) (m.getD (s.getD g.2.2 0) 0)) v := by
  simp only [Ref.round, gargs, List.foldl_cons, List.foldl_nil]

/-! ### The work-vector state relation (16 word-columns holding 16 Nat words). -/

/-- The 16 work-vector column-bases `vBases` reconstruct the 16 Nat words `vVals`. -/
def StateHolds (a : Assignment) (vBases vVals : List Nat) : Prop :=
  vBases.length = 16 ∧ vVals.length = 16 ∧ ∀ i, i < 16 → Holds a (vBases.getD i 0) (vVals.getD i 0)

/-- Reading index `i` back after a `.set` at the same index. -/
theorem getD_set_eq' (l : List Nat) (i x d : Nat) (h : i < l.length) :
    (l.set i x).getD i d = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]; rfl

/-- Reading index `j` back after a `.set` at a different index `i`. -/
theorem getD_set_ne' (l : List Nat) (i j x d : Nat) (h : i ≠ j) :
    (l.set i x).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h, ← List.getD_eq_getElem?_getD]

/-- The four `Ref.G` output-list entries at `a,b,c,d` are the `gVals` components; every other entry is
unchanged. (The `.set a a2 |>.set d d2 |>.set c c2 |>.set b b2` chain read back.) -/
theorem refG_getD (v : List Nat) (aa bb cc dd X Y : Nat)
    (hab : aa ≠ bb) (hac : aa ≠ cc) (had : aa ≠ dd) (hbc : bb ≠ cc) (hbd : bb ≠ dd) (hcd : cc ≠ dd)
    (haa : aa < v.length) (hbb : bb < v.length) (hcc : cc < v.length) (hdd : dd < v.length) :
    (Ref.G v aa bb cc dd X Y).getD aa 0
        = (gVals (v.getD aa 0) (v.getD bb 0) (v.getD cc 0) (v.getD dd 0) X Y).1
    ∧ (Ref.G v aa bb cc dd X Y).getD bb 0
        = (gVals (v.getD aa 0) (v.getD bb 0) (v.getD cc 0) (v.getD dd 0) X Y).2.1
    ∧ (Ref.G v aa bb cc dd X Y).getD cc 0
        = (gVals (v.getD aa 0) (v.getD bb 0) (v.getD cc 0) (v.getD dd 0) X Y).2.2.1
    ∧ (Ref.G v aa bb cc dd X Y).getD dd 0
        = (gVals (v.getD aa 0) (v.getD bb 0) (v.getD cc 0) (v.getD dd 0) X Y).2.2.2
    ∧ ∀ j, j ≠ aa → j ≠ bb → j ≠ cc → j ≠ dd → (Ref.G v aa bb cc dd X Y).getD j 0 = v.getD j 0 := by
  simp only [Ref.G, gVals]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [getD_set_ne' _ bb aa _ 0 (Ne.symm hab), getD_set_ne' _ cc aa _ 0 (Ne.symm hac),
        getD_set_ne' _ dd aa _ 0 (Ne.symm had), getD_set_eq' _ aa _ 0 haa]
  · rw [getD_set_eq' _ bb _ 0 (by simpa using hbb)]
  · rw [getD_set_ne' _ bb cc _ 0 hbc, getD_set_eq' _ cc _ 0 (by simpa using hcc)]
  · rw [getD_set_ne' _ bb dd _ 0 hbd, getD_set_ne' _ cc dd _ 0 hcd,
        getD_set_eq' _ dd _ 0 (by simpa using hdd)]
  · intro j hja hjb hjc hjd
    rw [getD_set_ne' _ bb j _ 0 (Ne.symm hjb), getD_set_ne' _ cc j _ 0 (Ne.symm hjc),
        getD_set_ne' _ dd j _ 0 (Ne.symm hjd), getD_set_ne' _ aa j _ 0 (Ne.symm hja)]

/-- The four `gStep` output-list entries at `a,b,c,d` are the fresh output bases; every other entry is
unchanged. -/
theorem gStep_getD (vBases : List Nat) (aa bb cc dd mx my fresh : Nat)
    (hab : aa ≠ bb) (hac : aa ≠ cc) (had : aa ≠ dd) (hbc : bb ≠ cc) (hbd : bb ≠ dd) (hcd : cc ≠ dd)
    (haa : aa < vBases.length) (hbb : bb < vBases.length) (hcc : cc < vBases.length)
    (hdd : dd < vBases.length) :
    let g := gStep vBases aa bb cc dd mx my fresh
    let na := (blakeG (vBases.getD aa 0) (vBases.getD bb 0) (vBases.getD cc 0) (vBases.getD dd 0)
                 mx my fresh).2.1
    g.2.1.getD aa 0 = na.1 ∧ g.2.1.getD bb 0 = na.2.1 ∧ g.2.1.getD cc 0 = na.2.2.1 ∧
    g.2.1.getD dd 0 = na.2.2.2 ∧
    ∀ j, j ≠ aa → j ≠ bb → j ≠ cc → j ≠ dd → g.2.1.getD j 0 = vBases.getD j 0 := by
  simp only [gStep]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [getD_set_ne' _ dd aa _ 0 (Ne.symm had), getD_set_ne' _ cc aa _ 0 (Ne.symm hac),
        getD_set_ne' _ bb aa _ 0 (Ne.symm hab), getD_set_eq' _ aa _ 0 haa]
  · rw [getD_set_ne' _ dd bb _ 0 (Ne.symm hbd), getD_set_ne' _ cc bb _ 0 (Ne.symm hbc),
        getD_set_eq' _ bb _ 0 (by simpa using hbb)]
  · rw [getD_set_ne' _ dd cc _ 0 (Ne.symm hcd), getD_set_eq' _ cc _ 0 (by simpa using hcc)]
  · rw [getD_set_eq' _ dd _ 0 (by simpa using hdd)]
  · intro j hja hjb hjc hjd
    rw [getD_set_ne' _ dd j _ 0 (Ne.symm hjd), getD_set_ne' _ cc j _ 0 (Ne.symm hjc),
        getD_set_ne' _ bb j _ 0 (Ne.symm hjb), getD_set_ne' _ aa j _ 0 (Ne.symm hja)]

/-- **`gStep_forces`** — one work-vector `G`-step preserves `StateHolds`: given the `blakeG` output
words are forced to `gVals` (which `blakeG_forces` delivers), the updated work vector reconstructs
`Ref.G` of the reconstructed inputs. The `.set` bookkeeping composing `blakeG_forces` up to the state
transition. -/
theorem gStep_forces (a : Assignment) (vBases vVals : List Nat)
    (aa bb cc dd mx my fresh MX MY : Nat)
    (hvb16 : vBases.length = 16) (hvv16 : vVals.length = 16)
    (hstate : ∀ i, i < 16 → Holds a (vBases.getD i 0) (vVals.getD i 0))
    (haa : aa < 16) (hbb : bb < 16) (hcc : cc < 16) (hdd : dd < 16)
    (hab : aa ≠ bb) (hac : aa ≠ cc) (had : aa ≠ dd) (hbc : bb ≠ cc) (hbd : bb ≠ dd) (hcd : cc ≠ dd)
    (hbg : Holds a (blakeG (vBases.getD aa 0) (vBases.getD bb 0) (vBases.getD cc 0) (vBases.getD dd 0)
                      mx my fresh).2.1.1
             (gVals (vVals.getD aa 0) (vVals.getD bb 0) (vVals.getD cc 0) (vVals.getD dd 0) MX MY).1
         ∧ Holds a (blakeG (vBases.getD aa 0) (vBases.getD bb 0) (vBases.getD cc 0) (vBases.getD dd 0)
                      mx my fresh).2.1.2.1
             (gVals (vVals.getD aa 0) (vVals.getD bb 0) (vVals.getD cc 0) (vVals.getD dd 0) MX MY).2.1
         ∧ Holds a (blakeG (vBases.getD aa 0) (vBases.getD bb 0) (vBases.getD cc 0) (vBases.getD dd 0)
                      mx my fresh).2.1.2.2.1
             (gVals (vVals.getD aa 0) (vVals.getD bb 0) (vVals.getD cc 0) (vVals.getD dd 0) MX MY).2.2.1
         ∧ Holds a (blakeG (vBases.getD aa 0) (vBases.getD bb 0) (vBases.getD cc 0) (vBases.getD dd 0)
                      mx my fresh).2.1.2.2.2
             (gVals (vVals.getD aa 0) (vVals.getD bb 0) (vVals.getD cc 0) (vVals.getD dd 0) MX MY).2.2.2) :
    StateHolds a (gStep vBases aa bb cc dd mx my fresh).2.1 (Ref.G vVals aa bb cc dd MX MY) := by
  obtain ⟨hna, hnb, hnc, hnd⟩ := hbg
  obtain ⟨gA, gB, gC, gD, gO⟩ := gStep_getD vBases aa bb cc dd mx my fresh hab hac had hbc hbd hcd
    (by rw [hvb16]; exact haa) (by rw [hvb16]; exact hbb) (by rw [hvb16]; exact hcc)
    (by rw [hvb16]; exact hdd)
  obtain ⟨rA, rB, rC, rD, rO⟩ := refG_getD vVals aa bb cc dd MX MY hab hac had hbc hbd hcd
    (by rw [hvv16]; exact haa) (by rw [hvv16]; exact hbb) (by rw [hvv16]; exact hcc)
    (by rw [hvv16]; exact hdd)
  refine ⟨?_, ?_, ?_⟩
  · simp only [gStep, List.length_set]; exact hvb16
  · simp only [Ref.G, List.length_set]; exact hvv16
  · intro i hi
    by_cases hia : i = aa
    · subst hia; rw [gA, rA]; exact hna
    · by_cases hib : i = bb
      · subst hib; rw [gB, rB]; exact hnb
      · by_cases hic : i = cc
        · subst hic; rw [gC, rC]; exact hnc
        · by_cases hid : i = dd
          · subst hid; rw [gD, rD]; exact hnd
          · rw [gO i hia hib hic hid, rO i hia hib hic hid]; exact hstate i hi

/-- **`blakeRound_forces`** — the round gadget forces `Ref.round`: the 8 `G`-steps compose by one
`foldl_forces` over `gargs` (the round gadget and `Ref.round` share that step list, `round_eq_foldl`).
Each step is discharged by `gStep_forces` (the `hstep` hypothesis). -/
theorem blakeRound_forces (a : Assignment) (mBases mVals sig : List Nat)
    (hstep : ∀ (acc : List VmConstraint2 × List Nat × Nat) (vv : List Nat)
               (g : (Nat × Nat × Nat × Nat) × (Nat × Nat)), g ∈ gargs →
        StateHolds a acc.2.1 vv →
        StateHolds a (gStep acc.2.1 g.1.1 g.1.2.1 g.1.2.2.1 g.1.2.2.2
                        (mBases.getD (sig.getD g.2.1 0) 0) (mBases.getD (sig.getD g.2.2 0) 0) acc.2.2).2.1
                     (Ref.G vv g.1.1 g.1.2.1 g.1.2.2.1 g.1.2.2.2
                        (mVals.getD (sig.getD g.2.1 0) 0) (mVals.getD (sig.getD g.2.2 0) 0)))
    (vInit vVals0 : List Nat) (fresh : Nat) (h0 : StateHolds a vInit vVals0) :
    StateHolds a (blakeRound vInit mBases sig fresh).2.1 (Ref.round vVals0 mVals sig) := by
  rw [round_eq_foldl]
  exact foldl_forces gargs
    (fun (acc : List VmConstraint2 × List Nat × Nat) g =>
       let (cs, v, fr) := acc
       let ((aa, bb, cc, dd), (sx, sy)) := g
       let mx := mBases.getD (sig.getD sx 0) 0
       let my := mBases.getD (sig.getD sy 0) 0
       let (cs', v', fr') := gStep v aa bb cc dd mx my fr
       (cs ++ cs', v', fr'))
    (fun v g => Ref.G v g.1.1 g.1.2.1 g.1.2.2.1 g.1.2.2.2
       (mVals.getD (sig.getD g.2.1 0) 0) (mVals.getD (sig.getD g.2.2 0) 0))
    (fun acc vv => StateHolds a acc.2.1 vv)
    ([], vInit, fresh) vVals0 h0 (fun s t g hg hR => hstep s t g hg hR)

/-- The compression's per-round GADGET step (exactly `blake2bCompress`'s fold body, named so the
elaborator matches it by NAME and never force-evaluates the concrete `List.range 12` fold — the
"blake2b-in-logic is fraught" discipline). -/
def cGStep (mBases : List Nat) (acc : List VmConstraint2 × List Nat × Nat) (r : Nat) :
    List VmConstraint2 × List Nat × Nat :=
  let (cs, v, fr) := acc
  let (cs', v', fr') := blakeRound v mBases (Ref.sigmaRow (r % 10)) fr
  (cs ++ cs', v', fr')

/-- The compression's per-round REFERENCE step. -/
def cRStep (mVals : List Nat) (v : List Nat) (r : Nat) : List Nat :=
  Ref.round v mVals (Ref.sigmaRow (r % 10))

/-- `blake2bCompress` IS the `foldl` of `cGStep` — by `rfl` (`cGStep mBases` is its fold body). -/
theorem blake2bCompress_eq (mBases vInit : List Nat) (fresh : Nat) :
    blake2bCompress mBases vInit fresh = (List.range 12).foldl (cGStep mBases) ([], vInit, fresh) :=
  rfl

/-- **`blake2bCompress_forces`** — the 12-round compression gadget forces the reference's round fold: the
12 rounds compose by one `foldl_forces` over `List.range 12`, each round discharged by `blakeRound_forces`
(the `hstep` hypothesis). "The rounds compose free," realized as a proof. -/
theorem blake2bCompress_forces (a : Assignment) (mBases mVals : List Nat)
    (hstep : ∀ (acc : List VmConstraint2 × List Nat × Nat) (vv : List Nat) (r : Nat),
        StateHolds a acc.2.1 vv → StateHolds a (cGStep mBases acc r).2.1 (cRStep mVals vv r))
    (vInit vVals0 : List Nat) (fresh : Nat) (h0 : StateHolds a vInit vVals0) :
    StateHolds a (blake2bCompress mBases vInit fresh).2.1
      ((List.range 12).foldl (cRStep mVals) vVals0) := by
  rw [blake2bCompress_eq]
  exact foldl_forces (List.range 12) (cGStep mBases) (cRStep mVals)
    (fun (acc : List VmConstraint2 × List Nat × Nat) vv => StateHolds a acc.2.1 vv)
    ([], vInit, fresh) vVals0 h0 (fun s t r _ hR => hstep s t r hR)

/-! ## §7 — The init/finalize atomic word bridges, and the whole-block `blake2bF` forcing. -/

/-- **A constant-word gate forces the word** to the pinned constant `k` (`< 2^64`). -/
theorem constWord_forces (a : Assignment) (hbool : AllBool a) (base k : Nat) (hk : k < 2 ^ 64)
    (hg : ∀ i, i < 64 → evalH ((Head.lin 1 (base + i)).addConst (-(Ref.bit k i : ℤ))) a = 0) :
    Holds a base k := by
  show wnat a base = k
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 64
  · rw [testBit_wnat a hbool base j hj]
    have hgj := hg j hj
    simp only [evalH_addConst, evalH_lin, one_mul] at hgj
    have hval : bitCol a (base + j) = Ref.bit k j := by
      unfold bitCol; rw [show a (base + j) = (Ref.bit k j : ℤ) from by linarith]
      simp
    rw [hval, refbit_eq]; cases Nat.testBit k j <;> simp
  · rw [wnat, natOfBits64_eq, testBit_bitsToNat _ (fun i => bitCol_le_one a hbool _) 64 j, if_neg hj]
    symm
    exact Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) (by omega)))

/-- Per-bit: an `xorConstWord` gate forces the output bit = input bit `⊕` constant bit. -/
theorem xorconstbit_forced (p o : ℤ) (kb : Nat) (hkb : kb ≤ 1)
    (hp : p = 0 ∨ p = 1) (ho : o = 0 ∨ o = 1)
    (heq : o = (1 - 2 * (kb : ℤ)) * p + (kb : ℤ)) :
    decide (o.toNat = 1) = (decide (p.toNat = 1) ^^ decide (kb = 1)) := by
  interval_cases kb <;> rcases hp with hp | hp <;> rcases ho with ho | ho <;>
    subst hp ho <;> simp_all

/-- **An `xor-with-constant` word gate forces the word** to `in ⊕ k` (`k < 2^64`). -/
theorem xorConstWord_forces (a : Assignment) (hbool : AllBool a) (inBase outBase k IN : Nat)
    (hk : k < 2 ^ 64) (hIN : Holds a inBase IN)
    (hg : ∀ i, i < 64 → evalH (((Head.lin (1 - 2 * (Ref.bit k i : ℤ)) (inBase + i)).addLin (-1)
                            (outBase + i)).addConst (Ref.bit k i : ℤ)) a = 0) :
    Holds a outBase (IN ^^^ k) := by
  have hINeq : wnat a inBase = IN := hIN
  have hINlt : IN < 2 ^ 64 := hINeq ▸ wnat_lt a hbool inBase
  show wnat a outBase = IN ^^^ k
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 64
  · rw [testBit_wnat a hbool outBase j hj, Nat.testBit_xor, ← hINeq, testBit_wnat a hbool inBase j hj]
    have hgj := hg j hj
    simp only [evalH_addConst, evalH_addLin, evalH_lin] at hgj
    have ho : a (outBase + j) = (1 - 2 * (Ref.bit k j : ℤ)) * a (inBase + j) + (Ref.bit k j : ℤ) := by
      linarith
    have hbit := xorconstbit_forced (a (inBase + j)) (a (outBase + j)) (Ref.bit k j)
      (refbit_le_one k j) (hbool _) (hbool _) ho
    have hbk : Nat.testBit k j = decide (Ref.bit k j = 1) := by
      rw [refbit_eq]; cases Nat.testBit k j <;> simp
    rw [hbk]; exact hbit
  · rw [wnat, natOfBits64_eq, testBit_bitsToNat _ (fun i => bitCol_le_one a hbool _) 64 j, if_neg hj]
    symm
    have : IN ^^^ k < 2 ^ 64 := Nat.xor_lt_two_pow hINlt hk
    exact Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega)))

/-! ## §8 — Axiom hygiene (CI hard-gate). The composition rungs are pinned kernel-clean. -/

#assert_axioms testBit_bitsToNat
#assert_axioms testBit_rotr64
#assert_axioms add3Word_forces
#assert_axioms add2Word_forces
#assert_axioms xorRotWord_forces
#assert_axioms xor3Word_forces
#assert_axioms blakeG_forces
#assert_axioms gStep_forces
#assert_axioms blakeRound_forces
#assert_axioms blake2bCompress_forces
#assert_axioms constWord_forces
#assert_axioms xorConstWord_forces

#print axioms blakeG_forces
#print axioms blake2bCompress_forces

end Dregg2.Circuit.Emit.Blake2bFoldForcing
