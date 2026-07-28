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

## ⚑ What was WRONG here until 2026-07-27, and what the repair is

The revision that landed this file contained the string `acceptB` ZERO times across 895 lines and 47
theorems. Nothing related *gates being satisfied* to *anything*: `blakeG_forces` took 8 raw
`evalH … = 0` equations over FREE column bases and never mentioned `blakeG`; `blakeRound_forces`,
`blake2bCompress_forces`, `blake2bF_forces` and `absorb_forces` took the rung below them as an
ASSUMED `hstep`; not one rung was ever instantiated. The cause is on the record: three lanes hit the
same `whnf` heartbeat wall on the concrete folds, and two of them made the fold steps opaque `def`s
so the elaborator would never reduce them — **the move that made the build green is the move that
severed the theorems from the gadget**, and it was reported as craft ("Key technique") under the
headline "DISCHARGED end-to-end". It was not discharged.

§4½ is the repair, and it copies the shape of the sibling that broke the identical wall honestly
(`Sha256FoldForcing`, `foldl_cstep_forces`): ACCEPTANCE-SPLITTING induction. Every rung below now
takes `acceptB <the generator applied to its real arguments>` as a hypothesis and peels it apart
along the generator's own `++` / `List.map` structure. The induction is over the step LIST, so it is
gate-count-INDEPENDENT and no gate is ever reduced — the wall falls without opacity.

TIED to gate acceptance: `blakeG_forces`, `gStep_forces`, `blakeRound_forces`,
`blake2bCompress_forces`, `blake2bInit_forces`, `blake2bFinalize_forces`, `blake2bF_forces`,
`absorb_forces`. The old free-base forms survive as the honestly-named helpers `blakeG_core_forces`,
`gStep_of_blakeG` and `blake2bInit_of_words`, which the tied rungs instantiate.

STILL A NAMED HYPOTHESIS, not a theorem: `AllBool a` (below), and the row-serialization tie that
would instantiate `absorbGadget`'s block list with Midnight's `authSetBlocks`/`sched` — see
`absorb_forces`'s docstring. `midHfold_discharged` remains what it always was: `Holds`-functionality
turning a reconstructed root plus a root pin into the anchor equality; what changed is that its
`hchain` is now PRODUCIBLE from a satisfied gate list rather than only assumable.

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

Every rung named above carries an in-file `#assert_axioms` (§10) — the check runs, it is not a
docstring claim. No `sorry`/`admit`/`native_decide`. Imports are read-only (`Blake2bGadget`,
`LightClientMidHashFold`, `Sha256FoldForcing` for the shared `acceptB` algebra). This file IS
root-imported (`Dregg2.lean:1529`), so §10 elaborates in the root build; the old header's
"standalone / NOT imported by the truncated `Dregg2` root" was stale and is deleted.
-/
import Dregg2.Circuit.Emit.Blake2bGadget
import Dregg2.Circuit.Emit.LightClientMidHashFold
import Dregg2.Circuit.Emit.Sha256FoldForcing

namespace Dregg2.Circuit.Emit.Blake2bFoldForcing

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.Blake2bGadget
open Dregg2.Circuit.Emit.Sha256Gadget (xorHead acceptB gateBodyEvalZero)
open Dregg2.Circuit.Emit.Sha256FoldForcing
  (acceptB_append acceptB_cons gateBodyEvalZero_cgH head_of_acceptB_map)
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

/-! ## §4½ — ACCEPTANCE SPLITTING: the `Sha256FoldForcing` discipline, over BLAKE2b's generators.

A forcing theorem is TIED to its gadget exactly when it CONSUMES `acceptB <the generator applied to
its real arguments>`. Everything in this section peels that acceptance apart along the generator's
OWN `++` / `List.map` structure — never by reducing a gate, so it is gate-count-INDEPENDENT, the
same move `Sha256FoldForcing.foldl_cstep_forces` makes on the 64 SHA rounds.

This is the section whose absence was the defect: the previous revision of this file made the fold
steps opaque `def`s so the elaborator would never reduce them, which made the build green by
severing every theorem from the gates. Opacity that prevents the gates from ever being related to
the reference is not a technique; the `acceptB` split below is the replacement. -/

/-- A singleton emitted head is accepted iff it evaluates to zero. -/
theorem head_of_acceptB_singleton (h : Head) (a : Assignment)
    (hacc : acceptB [cgH h] a = true) : evalH h a = 0 := by
  rw [acceptB, List.all_eq_true] at hacc
  have hb := hacc (cgH h) (by simp)
  rw [gateBodyEvalZero_cgH] at hb
  exact of_decide_eq_true hb

/-- **`xorRotCore`'s 64 emitted gates, from its acceptance.** -/
theorem gates_of_xorRotCore (a : Assignment) (aB bB out car R : Nat)
    (h : acceptB (xorRotCore aB bB out car R) a = true) :
    ∀ i, i < 64 → evalH (xorHead (xorRotSources aB bB R i) (out + i) (car + i)) a = 0 := by
  intro i hi
  exact head_of_acceptB_map (List.range 64)
    (fun i => xorHead (xorRotSources aB bB R i) (out + i) (car + i)) a h i (List.mem_range.mpr hi)

/-- **`xor3Core`'s 64 emitted gates, from its acceptance.** -/
theorem gates_of_xor3Core (a : Assignment) (aB bB cB out car : Nat)
    (h : acceptB (xor3Core aB bB cB out car) a = true) :
    ∀ i, i < 64 → evalH (xorHead [aB + i, bB + i, cB + i] (out + i) (car + i)) a = 0 := by
  intro i hi
  exact head_of_acceptB_map (List.range 64)
    (fun i => xorHead [aB + i, bB + i, cB + i] (out + i) (car + i)) a h i (List.mem_range.mpr hi)

/-- **`constWordGate`'s 64 emitted gates, from its acceptance.** -/
theorem gates_of_constWordGate (a : Assignment) (base k : Nat)
    (h : acceptB (constWordGate base k) a = true) :
    ∀ i, i < 64 → evalH ((Head.lin 1 (base + i)).addConst (-(Ref.bit k i : ℤ))) a = 0 := by
  intro i hi
  exact head_of_acceptB_map (List.range 64)
    (fun i => (Head.lin 1 (base + i)).addConst (-(Ref.bit k i : ℤ))) a h i (List.mem_range.mpr hi)

/-- **`xorConstWord`'s 64 value gates, from its acceptance** (its second segment is the output pins). -/
theorem gates_of_xorConstWord (a : Assignment) (inBase outBase k : Nat)
    (h : acceptB (xorConstWord inBase outBase k) a = true) :
    ∀ i, i < 64 → evalH (((Head.lin (1 - 2 * (Ref.bit k i : ℤ)) (inBase + i)).addLin (-1)
                        (outBase + i)).addConst (Ref.bit k i : ℤ)) a = 0 := by
  intro i hi
  rw [xorConstWord, acceptB_append, Bool.and_eq_true] at h
  exact head_of_acceptB_map (List.range 64)
    (fun i => ((Head.lin (1 - 2 * (Ref.bit k i : ℤ)) (inBase + i)).addLin (-1)
      (outBase + i)).addConst (Ref.bit k i : ℤ)) a h.1 i (List.mem_range.mpr hi)

/-! ### The FOLD engine. Every BLAKE2b generator above `blakeG` is a `List.foldl` whose body appends
its own step's gates and threads a state. `hF` below is that shape, proved `rfl` at the LAMBDA BODY
(free variables only — the fold is never evaluated, which is what keeps the elaborator out of the
`whnf` heartbeat wall the previous revision hit). -/

/-- The accumulated gate list keeps the starting list as a PREFIX, and the threaded state does not
depend on it. (The generic form of `Sha256FoldForcing.cstep_prefix`.) -/
theorem foldl_F_split {α σ : Type}
    (F : List VmConstraint2 × σ → α → List VmConstraint2 × σ)
    (g : σ → α → List VmConstraint2 × σ)
    (hF : ∀ cs s x, F (cs, s) x = (cs ++ (g s x).1, (g s x).2)) :
    ∀ (L : List α) (cs : List VmConstraint2) (s : σ),
      L.foldl F (cs, s) = (cs ++ (L.foldl F ([], s)).1, (L.foldl F ([], s)).2) := by
  intro L
  induction L with
  | nil => intro cs s; simp
  | cons x xs ih =>
    intro cs s
    rw [List.foldl_cons, List.foldl_cons, hF, hF, List.nil_append,
        ih (cs ++ (g s x).1) (g s x).2, ih (g s x).1 (g s x).2]
    simp [List.append_assoc]

/-- **Acceptance splits along the fold.** From acceptance of the WHOLE accumulated gate list, every
step's own emitted gates are accepted — at the state that step actually ran at. -/
theorem foldl_F_mem_accept {α σ : Type} (a : Assignment)
    (F : List VmConstraint2 × σ → α → List VmConstraint2 × σ)
    (g : σ → α → List VmConstraint2 × σ)
    (hF : ∀ cs s x, F (cs, s) x = (cs ++ (g s x).1, (g s x).2)) :
    ∀ (L : List α) (cs0 : List VmConstraint2) (s0 : σ),
      acceptB (L.foldl F (cs0, s0)).1 a = true →
      ∀ x ∈ L, ∃ s : σ, acceptB (g s x).1 a = true := by
  intro L
  induction L with
  | nil => intro cs0 s0 _ x hx; cases hx
  | cons y ys ih =>
    intro cs0 s0 hacc x hx
    rw [List.foldl_cons, hF] at hacc
    have hpre := foldl_F_split F g hF ys (cs0 ++ (g s0 y).1) (g s0 y).2
    have hy : acceptB (g s0 y).1 a = true := by
      have h0 := hacc
      rw [hpre, acceptB_append, Bool.and_eq_true, acceptB_append, Bool.and_eq_true] at h0
      exact h0.1.2
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨s0, hy⟩
    · exact ih (cs0 ++ (g s0 y).1) (g s0 y).2 hacc x hx'

/-- **THE COMPOSITION ENGINE.** If each step's OWN accepted gates carry the relation `R` from the
step's input state to the reference step's, then the whole fold's ACCEPTANCE carries `R` across the
whole fold. Gate-count-INDEPENDENT: the induction is over the step LIST, and no gate is reduced.
This is `Sha256FoldForcing.foldl_cstep_forces` with the SHA round abstracted out. -/
theorem foldl_F_forces {α σ τ : Type} (a : Assignment)
    (F : List VmConstraint2 × σ → α → List VmConstraint2 × σ)
    (g : σ → α → List VmConstraint2 × σ)
    (hF : ∀ cs s x, F (cs, s) x = (cs ++ (g s x).1, (g s x).2))
    (refStep : τ → α → τ) (R : σ → τ → Prop) (P : α → Prop)
    (hstep : ∀ (s : σ) (t : τ) (x : α), P x → R s t → acceptB (g s x).1 a = true →
        R (g s x).2 (refStep t x)) :
    ∀ (L : List α), (∀ x ∈ L, P x) →
      ∀ (cs0 : List VmConstraint2) (s0 : σ) (t0 : τ), R s0 t0 →
      acceptB (L.foldl F (cs0, s0)).1 a = true →
      R (L.foldl F (cs0, s0)).2 (L.foldl refStep t0) := by
  intro L
  induction L with
  | nil => intro _ cs0 s0 t0 h0 _; exact h0
  | cons y ys ih =>
    intro hP cs0 s0 t0 h0 hacc
    rw [List.foldl_cons, hF] at hacc
    rw [List.foldl_cons, List.foldl_cons, hF]
    have hpre := foldl_F_split F g hF ys (cs0 ++ (g s0 y).1) (g s0 y).2
    have hy : acceptB (g s0 y).1 a = true := by
      have h0' := hacc
      rw [hpre, acceptB_append, Bool.and_eq_true, acceptB_append, Bool.and_eq_true] at h0'
      exact h0'.1.2
    exact ih (fun x hx => hP x (List.mem_cons_of_mem y hx)) (cs0 ++ (g s0 y).1) (g s0 y).2
      (refStep t0 y) (hstep s0 t0 y (hP y List.mem_cons_self) h0 hy) hacc

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

/-- **`blakeG_core_forces`** — the HELPER form: given the 8 sub-op gate equations over ARBITRARY
column bases, the four output words are the real BLAKE2b `G` mixing of the six input words. A finite
chain of the atomic word bridges over `G`'s fixed structure — NO gate reduction.

⚠ This form is NOT tied to `blakeG`: its bases are free parameters and `blakeG` does not appear.
It was named `blakeG_forces` until 2026-07-27; that name is now carried by the acceptance-tied
`blakeG_forces` below, which instantiates this at `blakeG`'s OWN emitted layout (`GLayout`). -/
theorem blakeG_core_forces (a : Assignment) (hbool : AllBool a)
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

/-! ### `blakeG`'s emitted COLUMN LAYOUT, named.

These 16 offsets lived only inside `blakeG`'s `let` chain, so no theorem could mention them and the
forcing lemma's bases stayed free parameters — audit finding F6. Naming them is exactly what lets a
forcing theorem be stated ABOUT the emitted layout rather than about an arbitrary one. -/

namespace GLayout
/-- `v[a] + v[b] + x` output word. -/ def a1 (f : Nat) : Nat := f
/-- its two carry bits, at `ca1` and `ca1 + 1`. -/ def ca1 (f : Nat) : Nat := a1 f + 64
/-- `(v[d] ^ a1) >>> 32`. -/ def d1 (f : Nat) : Nat := ca1 f + 2
def cd1 (f : Nat) : Nat := d1 f + 64
/-- `v[c] + d1`. -/ def c1 (f : Nat) : Nat := cd1 f + 64
def cc1 (f : Nat) : Nat := c1 f + 64
/-- `(v[b] ^ c1) >>> 24`. -/ def b1 (f : Nat) : Nat := cc1 f + 1
def cb1 (f : Nat) : Nat := b1 f + 64
/-- `a1 + b1 + y` — the `G` output `a`. -/ def a2 (f : Nat) : Nat := cb1 f + 64
def ca2 (f : Nat) : Nat := a2 f + 64
/-- `(d1 ^ a2) >>> 16` — the `G` output `d`. -/ def d2 (f : Nat) : Nat := ca2 f + 2
def cd2 (f : Nat) : Nat := d2 f + 64
/-- `c1 + d2` — the `G` output `c`. -/ def c2 (f : Nat) : Nat := cd2 f + 64
def cc2 (f : Nat) : Nat := c2 f + 64
/-- `(b1 ^ c2) >>> 63` — the `G` output `b`. -/ def b2 (f : Nat) : Nat := cc2 f + 1
def cb2 (f : Nat) : Nat := b2 f + 64
end GLayout

/-- **`blakeG`'s emitted gate list IS its 8 sub-op segments at `GLayout`'s columns** — by `rfl`, the
generator's own structure. This is the bridge from `acceptB (blakeG …).1` to the gate equations
`blakeG_core_forces` consumes. -/
theorem blakeG_split (va vb vc vd mx my fresh : Nat) :
    (blakeG va vb vc vd mx my fresh).1
      = [addMod64Core [wordValue va, wordValue vb, wordValue mx] (GLayout.a1 fresh)
            [GLayout.ca1 fresh, GLayout.ca1 fresh + 1]]
        ++ xorRotCore vd (GLayout.a1 fresh) (GLayout.d1 fresh) (GLayout.cd1 fresh) 32
        ++ [addMod64Core [wordValue vc, wordValue (GLayout.d1 fresh)] (GLayout.c1 fresh)
              [GLayout.cc1 fresh]]
        ++ xorRotCore vb (GLayout.c1 fresh) (GLayout.b1 fresh) (GLayout.cb1 fresh) 24
        ++ [addMod64Core [wordValue (GLayout.a1 fresh), wordValue (GLayout.b1 fresh), wordValue my]
              (GLayout.a2 fresh) [GLayout.ca2 fresh, GLayout.ca2 fresh + 1]]
        ++ xorRotCore (GLayout.d1 fresh) (GLayout.a2 fresh) (GLayout.d2 fresh) (GLayout.cd2 fresh) 16
        ++ [addMod64Core [wordValue (GLayout.c1 fresh), wordValue (GLayout.d2 fresh)]
              (GLayout.c2 fresh) [GLayout.cc2 fresh]]
        ++ xorRotCore (GLayout.b1 fresh) (GLayout.c2 fresh) (GLayout.b2 fresh)
              (GLayout.cb2 fresh) 63 := rfl

/-- **`blakeG`'s returned output word bases ARE `GLayout`'s `(a2, b2, c2, d2)`** — by `rfl`. -/
theorem blakeG_out (va vb vc vd mx my fresh : Nat) :
    (blakeG va vb vc vd mx my fresh).2.1
      = (GLayout.a2 fresh, GLayout.b2 fresh, GLayout.c2 fresh, GLayout.d2 fresh) := rfl

/-- **`blakeG_forces` — the TIED rung.** GIVEN the emitted `blakeG` gate list is ACCEPTED (`acceptB`,
the ℤ reading of the gate bodies, on the generator applied to its real arguments) and the six input
word-columns hold `VA…Y`, the four columns `blakeG` RETURNS hold the real BLAKE2b `G` mixing.

The acceptance is destructured against `blakeG`'s own `++` structure (`blakeG_split`), so `blakeG`
appears in the hypothesis, in the conclusion, and in the proof. `AllBool a` is the separate
`pinWord`/`binGate` column sweep (`blakeG` emits CORE value gates only) — a named hypothesis, not a
derived one. -/
theorem blakeG_forces (a : Assignment) (hbool : AllBool a)
    (va vb vc vd mx my fresh : Nat) (VA VB VC VD X Y : Nat)
    (hva : Holds a va VA) (hvb : Holds a vb VB) (hvc : Holds a vc VC) (hvd : Holds a vd VD)
    (hmx : Holds a mx X) (hmy : Holds a my Y)
    (hacc : acceptB (blakeG va vb vc vd mx my fresh).1 a = true) :
    Holds a (blakeG va vb vc vd mx my fresh).2.1.1 (gVals VA VB VC VD X Y).1 ∧
    Holds a (blakeG va vb vc vd mx my fresh).2.1.2.1 (gVals VA VB VC VD X Y).2.1 ∧
    Holds a (blakeG va vb vc vd mx my fresh).2.1.2.2.1 (gVals VA VB VC VD X Y).2.2.1 ∧
    Holds a (blakeG va vb vc vd mx my fresh).2.1.2.2.2 (gVals VA VB VC VD X Y).2.2.2 := by
  rw [blakeG_split] at hacc
  simp only [acceptB_append, Bool.and_eq_true] at hacc
  obtain ⟨⟨⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩, g7⟩, g8⟩ := hacc
  simp only [blakeG_out]
  exact blakeG_core_forces a hbool va vb vc vd mx my
    (GLayout.a1 fresh) (GLayout.ca1 fresh) (GLayout.d1 fresh) (GLayout.cd1 fresh)
    (GLayout.c1 fresh) (GLayout.cc1 fresh) (GLayout.b1 fresh) (GLayout.cb1 fresh)
    (GLayout.a2 fresh) (GLayout.ca2 fresh) (GLayout.d2 fresh) (GLayout.cd2 fresh)
    (GLayout.c2 fresh) (GLayout.cc2 fresh) (GLayout.b2 fresh) (GLayout.cb2 fresh)
    VA VB VC VD X Y hva hvb hvc hvd hmx hmy
    (head_of_acceptB_singleton _ a g1)
    (gates_of_xorRotCore a vd _ _ _ 32 g2)
    (head_of_acceptB_singleton _ a g3)
    (gates_of_xorRotCore a vb _ _ _ 24 g4)
    (head_of_acceptB_singleton _ a g5)
    (gates_of_xorRotCore a _ _ _ _ 16 g6)
    (head_of_acceptB_singleton _ a g7)
    (gates_of_xorRotCore a _ _ _ _ 63 g8)

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

/-- **`gStep_of_blakeG`** — the `.set` bookkeeping: given the `blakeG` output words are forced to
`gVals` (which the tied `blakeG_forces` delivers), the updated work vector reconstructs `Ref.G` of
the reconstructed inputs. The helper form; `gStep_forces` below is the acceptance-tied rung. -/
theorem gStep_of_blakeG (a : Assignment) (vBases vVals : List Nat)
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

/-- **`gStep_forces` — the TIED rung.** The `G`-step gadget's OWN accepted gates (`gStep`'s emitted
list IS `blakeG`'s) carry `StateHolds` across the work-vector update. -/
theorem gStep_forces (a : Assignment) (hbool : AllBool a) (vBases vVals : List Nat)
    (aa bb cc dd mx my fresh MX MY : Nat)
    (hvb16 : vBases.length = 16) (hvv16 : vVals.length = 16)
    (hstate : ∀ i, i < 16 → Holds a (vBases.getD i 0) (vVals.getD i 0))
    (haa : aa < 16) (hbb : bb < 16) (hcc : cc < 16) (hdd : dd < 16)
    (hab : aa ≠ bb) (hac : aa ≠ cc) (had : aa ≠ dd) (hbc : bb ≠ cc) (hbd : bb ≠ dd) (hcd : cc ≠ dd)
    (hmx : Holds a mx MX) (hmy : Holds a my MY)
    (hacc : acceptB (gStep vBases aa bb cc dd mx my fresh).1 a = true) :
    StateHolds a (gStep vBases aa bb cc dd mx my fresh).2.1 (Ref.G vVals aa bb cc dd MX MY) :=
  gStep_of_blakeG a vBases vVals aa bb cc dd mx my fresh MX MY hvb16 hvv16 hstate
    haa hbb hcc hdd hab hac had hbc hbd hcd
    (blakeG_forces a hbool (vBases.getD aa 0) (vBases.getD bb 0) (vBases.getD cc 0)
      (vBases.getD dd 0) mx my fresh _ _ _ _ MX MY
      (hstate aa haa) (hstate bb hbb) (hstate cc hcc) (hstate dd hdd) hmx hmy hacc)

/-- Every `G`-argument quartet in a round is in range and pairwise distinct, and both its message
indices are in range — the side conditions `gStep_forces` needs, discharged for the WHOLE round. -/
theorem gargs_ok : ∀ g ∈ gargs,
    g.1.1 < 16 ∧ g.1.2.1 < 16 ∧ g.1.2.2.1 < 16 ∧ g.1.2.2.2 < 16 ∧
    g.1.1 ≠ g.1.2.1 ∧ g.1.1 ≠ g.1.2.2.1 ∧ g.1.1 ≠ g.1.2.2.2 ∧
    g.1.2.1 ≠ g.1.2.2.1 ∧ g.1.2.1 ≠ g.1.2.2.2 ∧ g.1.2.2.1 ≠ g.1.2.2.2 ∧
    g.2.1 < 16 ∧ g.2.2 < 16 := by decide

/-- The round's per-`G` GADGET step, in the `foldl_F_*` shape: it emits its own `gStep` gates and
threads `(work-vector bases, next free column)`. -/
def rgStep (mBases sig : List Nat) (s : List Nat × Nat)
    (g : (Nat × Nat × Nat × Nat) × (Nat × Nat)) : List VmConstraint2 × (List Nat × Nat) :=
  let r := gStep s.1 g.1.1 g.1.2.1 g.1.2.2.1 g.1.2.2.2
             (mBases.getD (sig.getD g.2.1 0) 0) (mBases.getD (sig.getD g.2.2 0) 0) s.2
  (r.1, r.2)

/-- **`blakeRound_forces` — the TIED rung.** GIVEN the round gadget's emitted gate list is ACCEPTED
and the 16 message-word columns hold the reference message words at the schedule's positions, the
round gadget's work vector holds `Ref.round`. The 8 `G`-steps are peeled out of the WHOLE round's
acceptance by `foldl_F_forces` over `gargs` — the step list the gadget and `Ref.round` share
(`round_eq_foldl`) — and each is discharged by the tied `gStep_forces`. No gate is reduced. -/
theorem blakeRound_forces (a : Assignment) (hbool : AllBool a) (mBases mVals sig : List Nat)
    (hm : ∀ j, j < 16 → Holds a (mBases.getD (sig.getD j 0) 0) (mVals.getD (sig.getD j 0) 0))
    (vInit vVals0 : List Nat) (fresh : Nat) (h0 : StateHolds a vInit vVals0)
    (hacc : acceptB (blakeRound vInit mBases sig fresh).1 a = true) :
    StateHolds a (blakeRound vInit mBases sig fresh).2.1 (Ref.round vVals0 mVals sig) := by
  rw [round_eq_foldl]
  unfold blakeRound at hacc ⊢
  refine foldl_F_forces a _ (rgStep mBases sig) (by intro cs s x; rfl)
    (fun v g => Ref.G v g.1.1 g.1.2.1 g.1.2.2.1 g.1.2.2.2
       (mVals.getD (sig.getD g.2.1 0) 0) (mVals.getD (sig.getD g.2.2 0) 0))
    (fun s vv => StateHolds a s.1 vv) (fun g => g ∈ gargs) ?_ gargs (fun _ h => h)
    [] (vInit, fresh) vVals0 h0 hacc
  rintro s vv g hg ⟨hb16, hv16, hst⟩ hgacc
  obtain ⟨ha, hb, hc, hd, nab, nac, nad, nbc, nbd, ncd, hsx, hsy⟩ := gargs_ok g hg
  exact gStep_forces a hbool s.1 vv g.1.1 g.1.2.1 g.1.2.2.1 g.1.2.2.2 _ _ s.2 _ _
    hb16 hv16 hst ha hb hc hd nab nac nad nbc nbd ncd
    (hm g.2.1 hsx) (hm g.2.2 hsy) hgacc

/-- The compression's per-round REFERENCE step. -/
def cRStep (mVals : List Nat) (v : List Nat) (r : Nat) : List Nat :=
  Ref.round v mVals (Ref.sigmaRow (r % 10))

/-- The compression's per-round GADGET step, in the `foldl_F_*` shape. -/
def cgStep (mBases : List Nat) (s : List Nat × Nat) (r : Nat) :
    List VmConstraint2 × (List Nat × Nat) :=
  let br := blakeRound s.1 mBases (Ref.sigmaRow (r % 10)) s.2
  (br.1, br.2)

/-- Every `SIGMA` row is a permutation of `0…15`, so every schedule entry a round reads is a legal
message-word index. Discharges `blakeRound_forces`'s schedule side condition for all 12 rounds. -/
theorem sigmaRow_lt : ∀ r, r < 10 → ∀ j, j < 16 → (Ref.sigmaRow r).getD j 0 < 16 := by decide

/-- **`blake2bCompress_forces` — the TIED rung.** GIVEN the WHOLE 12-round compression's emitted
gate list is ACCEPTED (~24960 gates) and the 16 message-word columns hold `mVals`, the compression
gadget's final work vector holds the reference 12-round `Ref.round` fold. The rounds are peeled out
of the whole compression's acceptance by `foldl_F_forces` over `List.range 12` and each is
discharged by the tied `blakeRound_forces` — gate-count-INDEPENDENT, so the ~25k-gate wall falls
the same way `Sha256FoldForcing.sha256Compress'_forces` breaks the ~30k-gate SHA one. -/
theorem blake2bCompress_forces (a : Assignment) (hbool : AllBool a) (mBases mVals : List Nat)
    (hm : ∀ k, k < 16 → Holds a (mBases.getD k 0) (mVals.getD k 0))
    (vInit vVals0 : List Nat) (fresh : Nat) (h0 : StateHolds a vInit vVals0)
    (hacc : acceptB (blake2bCompress mBases vInit fresh).1 a = true) :
    StateHolds a (blake2bCompress mBases vInit fresh).2.1
      ((List.range 12).foldl (cRStep mVals) vVals0) := by
  unfold blake2bCompress at hacc ⊢
  refine foldl_F_forces a _ (cgStep mBases) (by intro cs s x; rfl) (cRStep mVals)
    (fun s vv => StateHolds a s.1 vv) (fun _ => True) ?_ (List.range 12) (fun _ _ => trivial)
    [] (vInit, fresh) vVals0 h0 hacc
  intro s vv r _ hR hracc
  exact blakeRound_forces a hbool mBases mVals (Ref.sigmaRow (r % 10))
    (fun j hj => hm _ (sigmaRow_lt (r % 10) (Nat.mod_lt _ (by norm_num)) j hj))
    s.1 vv s.2 hR hracc

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

/-! ## §8 — The whole-block `blake2bF` forcing (init ⊕ compress ⊕ finalize), tied to `Ref.compress`. -/

/-- `Ref.compress`'s initial work vector (the `h ++ IV` load with the counter/flag XOR-folded into
`v[12..15]`) — named so `Ref.compress` reformulates by `rfl`. -/
def refInitV (hVals : List Nat) (t0 t1 f0 f1 : Nat) : List Nat :=
  let v := hVals ++ Ref.IV
  let v := v.set 12 (Ref.xorw (v.getD 12 0) t0)
  let v := v.set 13 (Ref.xorw (v.getD 13 0) t1)
  let v := v.set 14 (Ref.xorw (v.getD 14 0) f0)
  v.set 15 (Ref.xorw (v.getD 15 0) f1)

/-- `Ref.compress`'s digest fold `out_i = h_i ⊕ vf_i ⊕ vf_{i+8}`. -/
def refDigest (hVals vf : List Nat) : List Nat :=
  (List.range 8).map (fun i =>
    Ref.w64 (Ref.xorw (Ref.xorw (hVals.getD i 0) (vf.getD i 0)) (vf.getD (i + 8) 0)))

/-- **`Ref.compress` IS digest ∘ (12-round fold) ∘ init** — by `rfl` (the named pieces are its body). -/
theorem refCompress_eq (hVals mVals : List Nat) (t0 t1 f0 f1 : Nat) :
    Ref.compress hVals mVals t0 t1 f0 f1
      = refDigest hVals ((List.range 12).foldl (cRStep mVals) (refInitV hVals t0 t1 f0 f1)) :=
  rfl

/-- `((List.range n).map f).getD i 0 = f i` for `i < n`. -/
theorem getD_map_range (f : Nat → Nat) (n i : Nat) (hi : i < n) :
    ((List.range n).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- `getD` on the left half of an append. -/
theorem gdaL (l1 l2 : List Nat) (i : Nat) (h : i < l1.length) :
    (l1 ++ l2).getD i 0 = l1.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

/-- `getD` on the right half of an append. -/
theorem gdaR (l1 l2 : List Nat) (i : Nat) (h : l1.length ≤ i) :
    (l1 ++ l2).getD i 0 = l2.getD (i - l1.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, ← List.getD_eq_getElem?_getD]

/-- **`refInitV` in append form**: the input state `hVals` followed by `[IV0..3, IV4⊕t0, IV5⊕t1,
IV6⊕f0, IV7⊕f1]` — for clean per-index reads in the init forcing. -/
theorem refInitV_eq_append (hVals : List Nat) (t0 t1 f0 f1 : Nat) (hlen : hVals.length = 8) :
    refInitV hVals t0 t1 f0 f1 = hVals ++
      [Ref.IV.getD 0 0, Ref.IV.getD 1 0, Ref.IV.getD 2 0, Ref.IV.getD 3 0,
       Ref.xorw (Ref.IV.getD 4 0) t0, Ref.xorw (Ref.IV.getD 5 0) t1,
       Ref.xorw (Ref.IV.getD 6 0) f0, Ref.xorw (Ref.IV.getD 7 0) f1] := by
  have g12 : (hVals ++ Ref.IV).getD 12 0 = Ref.IV.getD 4 0 := by rw [gdaR _ _ 12 (by omega), hlen]
  have g13 : (hVals ++ Ref.IV).getD 13 0 = Ref.IV.getD 5 0 := by rw [gdaR _ _ 13 (by omega), hlen]
  have g14 : (hVals ++ Ref.IV).getD 14 0 = Ref.IV.getD 6 0 := by rw [gdaR _ _ 14 (by omega), hlen]
  have g15 : (hVals ++ Ref.IV).getD 15 0 = Ref.IV.getD 7 0 := by rw [gdaR _ _ 15 (by omega), hlen]
  simp only [refInitV]
  rw [g12, getD_set_ne' _ 12 13 _ 0 (by decide), g13,
      getD_set_ne' _ 13 14 _ 0 (by decide), getD_set_ne' _ 12 14 _ 0 (by decide), g14,
      getD_set_ne' _ 14 15 _ 0 (by decide), getD_set_ne' _ 13 15 _ 0 (by decide),
      getD_set_ne' _ 12 15 _ 0 (by decide), g15,
      List.set_append_right _ _ (by omega), List.set_append_right _ _ (by omega),
      List.set_append_right _ _ (by omega), List.set_append_right _ _ (by omega)]
  simp only [hlen]
  rfl

/-- The digest fold's per-word GADGET step, in the `foldl_F_*` shape. -/
def finStep (hBases vFinal outBases : List Nat) (fr : Nat) (i : Nat) : List VmConstraint2 × Nat :=
  (xor3Word (hBases.getD i 0) (vFinal.getD i 0) (vFinal.getD (i + 8) 0) (outBases.getD i 0) fr,
   fr + 64)

/-- **`blake2bFinalize_forces` — the TIED rung.** GIVEN the digest-fold gadget's emitted gate list is
ACCEPTED, each of the 8 output words is `h_i ⊕ vf_i ⊕ vf_{i+8}` (`= (refDigest hVals vf)_i`). The 8
per-word `xor3Word` gadgets are peeled out of the whole fold's acceptance by `foldl_F_mem_accept`. -/
theorem blake2bFinalize_forces (a : Assignment) (hbool : AllBool a)
    (hBases vFinal outBases hVals vfVals : List Nat) (fresh : Nat)
    (hh : ∀ i, i < 8 → Holds a (hBases.getD i 0) (hVals.getD i 0))
    (hv : ∀ i, i < 16 → Holds a (vFinal.getD i 0) (vfVals.getD i 0))
    (hacc : acceptB (blake2bFinalize hBases vFinal outBases fresh).1 a = true) :
    ∀ i, i < 8 → Holds a (outBases.getD i 0) ((refDigest hVals vfVals).getD i 0) := by
  intro i hi
  unfold blake2bFinalize at hacc
  obtain ⟨fr, hfr⟩ := foldl_F_mem_accept a _ (finStep hBases vFinal outBases)
    (by intro cs s x; rfl) (List.range 8) [] fresh hacc i (List.mem_range.mpr hi)
  simp only [finStep, xor3Word, acceptB_append, Bool.and_eq_true] at hfr
  have hforce := xor3Word_forces a hbool (hBases.getD i 0) (vFinal.getD i 0) (vFinal.getD (i + 8) 0)
    (outBases.getD i 0) fr (hVals.getD i 0) (vfVals.getD i 0) (vfVals.getD (i + 8) 0)
    (hh i hi) (hv i (by omega)) (hv (i + 8) (by omega))
    (gates_of_xor3Core a _ _ _ _ _ hfr.1.1)
  rw [refDigest, getD_map_range _ 8 i hi]
  exact hforce

/-- **`blake2bInit_of_words`** — the HELPER form: the `.set`/append bookkeeping that assembles the
16-word initial work vector `refInitV` out of the 8 relabelled input words plus the 8 forced `IV`
words. `blake2bInit_forces` below derives `h8 … h15` from the init gadget's own accepted gates. -/
theorem blake2bInit_of_words (a : Assignment) (hBases : List Nat) (t0B t1B f0B f1B fresh : Nat)
    (hVals : List Nat) (t0 t1 f0 f1 : Nat) (hlen : hVals.length = 8)
    (hh : ∀ i, i < 8 → Holds a (hBases.getD i 0) (hVals.getD i 0))
    (h8 : Holds a fresh (Ref.IV.getD 0 0)) (h9 : Holds a (fresh + 64) (Ref.IV.getD 1 0))
    (h10 : Holds a (fresh + 128) (Ref.IV.getD 2 0)) (h11 : Holds a (fresh + 192) (Ref.IV.getD 3 0))
    (h12 : Holds a (fresh + 256) (t0 ^^^ Ref.IV.getD 4 0))
    (h13 : Holds a (fresh + 320) (t1 ^^^ Ref.IV.getD 5 0))
    (h14 : Holds a (fresh + 384) (f0 ^^^ Ref.IV.getD 6 0))
    (h15 : Holds a (fresh + 448) (f1 ^^^ Ref.IV.getD 7 0)) :
    StateHolds a (blake2bInit hBases t0B t1B f0B f1B fresh).2.1 (refInitV hVals t0 t1 f0 f1) := by
  have hvB : (blake2bInit hBases t0B t1B f0B f1B fresh).2.1 =
      [hBases.getD 0 0, hBases.getD 1 0, hBases.getD 2 0, hBases.getD 3 0, hBases.getD 4 0,
       hBases.getD 5 0, hBases.getD 6 0, hBases.getD 7 0, fresh, fresh + 64, fresh + 128,
       fresh + 192, fresh + 256, fresh + 320, fresh + 384, fresh + 448] := rfl
  refine ⟨by simp [hvB], ?_, ?_⟩
  · rw [refInitV_eq_append _ _ _ _ _ hlen]; simp [hlen]
  · intro i hi
    rw [hvB, refInitV_eq_append _ _ _ _ _ hlen]
    rcases Nat.lt_or_ge i 8 with h8i | h8i
    · rw [gdaL _ _ i (by omega)]
      interval_cases i <;>
        simp only [List.getD_cons_zero, List.getD_cons_succ] <;> exact hh _ (by omega)
    · rw [gdaR _ _ i (by omega), hlen]
      interval_cases i <;>
        simp only [List.getD_cons_zero, List.getD_cons_succ] <;>
        first
          | exact h8 | exact h9 | exact h10 | exact h11
          | (unfold Ref.xorw; rw [Nat.xor_comm]; exact h12)
          | (unfold Ref.xorw; rw [Nat.xor_comm]; exact h13)
          | (unfold Ref.xorw; rw [Nat.xor_comm]; exact h14)
          | (unfold Ref.xorw; rw [Nat.xor_comm]; exact h15)

/-- **`blake2bInit`'s emitted gate list IS its 8 word segments** — by `rfl`, the generator's own
structure. -/
theorem blake2bInit_split (hBases : List Nat) (t0B t1B f0B f1B fresh : Nat) :
    (blake2bInit hBases t0B t1B f0B f1B fresh).1
      = constWordGate fresh (Ref.IV.getD 0 0) ++ constWordGate (fresh + 64) (Ref.IV.getD 1 0)
        ++ constWordGate (fresh + 128) (Ref.IV.getD 2 0)
        ++ constWordGate (fresh + 192) (Ref.IV.getD 3 0)
        ++ xorConstWord t0B (fresh + 256) (Ref.IV.getD 4 0)
        ++ xorConstWord t1B (fresh + 320) (Ref.IV.getD 5 0)
        ++ xorConstWord f0B (fresh + 384) (Ref.IV.getD 6 0)
        ++ xorConstWord f1B (fresh + 448) (Ref.IV.getD 7 0) := rfl

/-- Each `IV` word is a 64-bit word (the `constWord_forces`/`xorConstWord_forces` obligation). -/
theorem IV_lt : ∀ i, i < 8 → Ref.IV.getD i 0 < 2 ^ 64 := by decide

/-- **`blake2bInit_forces` — the TIED rung.** GIVEN the init gadget's emitted gate list is ACCEPTED
and the counter/flag word-columns hold `t0,t1,f0,f1`, the 16 work-vector columns the gadget RETURNS
hold `refInitV` — `v[8..11]` forced to the pinned `IV[0..3]` by `constWord_forces`, `v[12..15]` to
the counter/flag XOR-folded into `IV[4..7]` by `xorConstWord_forces`. -/
theorem blake2bInit_forces (a : Assignment) (hbool : AllBool a) (hBases : List Nat)
    (t0B t1B f0B f1B fresh : Nat) (hVals : List Nat) (t0 t1 f0 f1 : Nat) (hlen : hVals.length = 8)
    (hh : ∀ i, i < 8 → Holds a (hBases.getD i 0) (hVals.getD i 0))
    (ht0 : Holds a t0B t0) (ht1 : Holds a t1B t1) (hf0 : Holds a f0B f0) (hf1 : Holds a f1B f1)
    (hacc : acceptB (blake2bInit hBases t0B t1B f0B f1B fresh).1 a = true) :
    StateHolds a (blake2bInit hBases t0B t1B f0B f1B fresh).2.1 (refInitV hVals t0 t1 f0 f1) := by
  rw [blake2bInit_split] at hacc
  simp only [acceptB_append, Bool.and_eq_true] at hacc
  obtain ⟨⟨⟨⟨⟨⟨⟨c8, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩, c15⟩ := hacc
  exact blake2bInit_of_words a hBases t0B t1B f0B f1B fresh hVals t0 t1 f0 f1 hlen hh
    (constWord_forces a hbool fresh _ (IV_lt 0 (by norm_num)) (gates_of_constWordGate a _ _ c8))
    (constWord_forces a hbool _ _ (IV_lt 1 (by norm_num)) (gates_of_constWordGate a _ _ c9))
    (constWord_forces a hbool _ _ (IV_lt 2 (by norm_num)) (gates_of_constWordGate a _ _ c10))
    (constWord_forces a hbool _ _ (IV_lt 3 (by norm_num)) (gates_of_constWordGate a _ _ c11))
    (xorConstWord_forces a hbool t0B _ _ t0 (IV_lt 4 (by norm_num)) ht0
      (gates_of_xorConstWord a _ _ _ c12))
    (xorConstWord_forces a hbool t1B _ _ t1 (IV_lt 5 (by norm_num)) ht1
      (gates_of_xorConstWord a _ _ _ c13))
    (xorConstWord_forces a hbool f0B _ _ f0 (IV_lt 6 (by norm_num)) hf0
      (gates_of_xorConstWord a _ _ _ c14))
    (xorConstWord_forces a hbool f1B _ _ f1 (IV_lt 7 (by norm_num)) hf1
      (gates_of_xorConstWord a _ _ _ c15))

/-- **`blake2bF`'s emitted gate list IS init ‖ compress ‖ finalize** — by `rfl`. -/
theorem blake2bF_split (hBases mBases : List Nat) (t0B t1B f0B f1B : Nat)
    (outBases : List Nat) (fresh : Nat) :
    (blake2bF hBases mBases t0B t1B f0B f1B outBases fresh).1
      = (blake2bInit hBases t0B t1B f0B f1B fresh).1
        ++ (blake2bCompress mBases (blake2bInit hBases t0B t1B f0B f1B fresh).2.1
              (blake2bInit hBases t0B t1B f0B f1B fresh).2.2).1
        ++ (blake2bFinalize hBases
              (blake2bCompress mBases (blake2bInit hBases t0B t1B f0B f1B fresh).2.1
                 (blake2bInit hBases t0B t1B f0B f1B fresh).2.2).2.1
              outBases
              (blake2bCompress mBases (blake2bInit hBases t0B t1B f0B f1B fresh).2.1
                 (blake2bInit hBases t0B t1B f0B f1B fresh).2.2).2.2).1 := rfl

/-- `Ref.compress` always returns 8 words. -/
theorem refCompress_length (hVals mVals : List Nat) (t0 t1 f0 f1 : Nat) :
    (Ref.compress hVals mVals t0 t1 f0 f1).length = 8 := by
  rw [refCompress_eq, refDigest]; simp

/-- **`blake2bF_forces` — the TIED rung.** GIVEN the WHOLE 27264-gate block gadget's emitted list is
ACCEPTED, and the input-state / message / counter / flag columns hold their reference words, the 8
output columns hold `Ref.compress` of those words. The three segments (init ‖ 12-round compression ‖
digest fold) are peeled off the block's acceptance by `acceptB_append` and each discharged by its own
TIED rung. This is ONE block of the multi-block absorb, gate-count-independently. -/
theorem blake2bF_forces (a : Assignment) (hbool : AllBool a)
    (hBases mBases outBases hVals mVals : List Nat) (t0B t1B f0B f1B : Nat)
    (t0 t1 f0 f1 fresh : Nat) (hlen : hVals.length = 8)
    (hh : ∀ i, i < 8 → Holds a (hBases.getD i 0) (hVals.getD i 0))
    (hm : ∀ k, k < 16 → Holds a (mBases.getD k 0) (mVals.getD k 0))
    (ht0 : Holds a t0B t0) (ht1 : Holds a t1B t1) (hf0 : Holds a f0B f0) (hf1 : Holds a f1B f1)
    (hacc : acceptB (blake2bF hBases mBases t0B t1B f0B f1B outBases fresh).1 a = true) :
    ∀ i, i < 8 → Holds a (outBases.getD i 0) ((Ref.compress hVals mVals t0 t1 f0 f1).getD i 0) := by
  rw [blake2bF_split] at hacc
  simp only [acceptB_append, Bool.and_eq_true] at hacc
  obtain ⟨⟨hi0, hi1⟩, hi2⟩ := hacc
  have hinit := blake2bInit_forces a hbool hBases t0B t1B f0B f1B fresh hVals t0 t1 f0 f1 hlen hh
    ht0 ht1 hf0 hf1 hi0
  have hcomp := blake2bCompress_forces a hbool mBases mVals hm _ _ _ hinit hi1
  obtain ⟨_, _, hvf⟩ := hcomp
  have hfinal := blake2bFinalize_forces a hbool hBases _ outBases hVals _ _ hh hvf hi2
  intro i hi
  rw [refCompress_eq]
  exact hfinal i hi

/-! ## §9 — The multi-block absorb and the discharge of Midnight's `hfold`. -/

/-- The reconstructed 8-word BLAKE2b state at a list of 8 column-bases. -/
def Holds8 (a : Assignment) (bases vals : List Nat) : Prop :=
  vals.length = 8 ∧ ∀ i, i < 8 → Holds a (bases.getD i 0) (vals.getD i 0)

/-- One absorbed block: the emitted COLUMN LAYOUT of the block — its 16 message-word columns, its
counter/flag word columns, and the 8-word digest slab it writes — PAIRED with the reference values
that layout is required to hold. -/
structure AbsorbBlock where
  /-- the 16 message-word column bases -/ mBases : List Nat
  /-- counter-low word column -/ t0B : Nat
  /-- counter-high word column -/ t1B : Nat
  /-- final-flag word column -/ f0B : Nat
  /-- second flag word column -/ f1B : Nat
  /-- the 8 digest word columns this block writes -/ outBases : List Nat
  /-- the 16 reference message words -/ mVals : List Nat
  /-- the reference counter -/ t0 : Nat
  /-- the reference final flag -/ f0 : Nat

/-- One block of the multi-block absorb, EMITTED: `blake2bF` at the current fresh column, with block
`k`'s 8 digest columns becoming block `k+1`'s input-state columns. (`t1 = f1 = 0`, exactly as
`LightClientMidHashFold.absorb` fixes them.) -/
def absorbStep (s : List Nat × Nat) (b : AbsorbBlock) : List VmConstraint2 × (List Nat × Nat) :=
  let r := blake2bF s.1 b.mBases b.t0B b.t1B b.f0B b.f1B b.outBases s.2
  (r.1, (b.outBases, r.2))

/-- **The multi-block absorb AS AN EMITTED GATE LIST** — `#blocks × 27264` core gates, chained. This
generator is what `LightClientMidHashFold.lean:365-369` describes in a comment and measures with a
length `#guard`; nothing in the tree emitted it before, which is why `absorb_forces` previously
quantified over an abstract `nextBases` instead of naming a gadget. -/
def absorbGadget (bs : List AbsorbBlock) (h0Bases : List Nat) (fresh : Nat) :
    List VmConstraint2 × (List Nat × Nat) :=
  bs.foldl (fun acc b => (acc.1 ++ (absorbStep acc.2 b).1, (absorbStep acc.2 b).2))
    ([], h0Bases, fresh)

/-- Per-block word hypotheses: the block's emitted message / counter / flag columns hold its values,
and its `t1`/`f1` columns hold the zeros the absorb schedule fixes. -/
def BlockHolds (a : Assignment) (b : AbsorbBlock) : Prop :=
  b.mVals.length = 16 ∧
  (∀ k, k < 16 → Holds a (b.mBases.getD k 0) (b.mVals.getD k 0)) ∧
  Holds a b.t0B b.t0 ∧ Holds a b.t1B 0 ∧ Holds a b.f0B b.f0 ∧ Holds a b.f1B 0

/-- **`absorb_forces` — the TIED rung.** GIVEN the WHOLE chained absorb gadget's emitted gate list is
ACCEPTED and every block's word-columns hold its message/counter/flag values, the 8 columns the chain
ENDS on hold `LightClientMidHashFold.absorb` of the block values. The blocks are peeled out of the
whole chain's acceptance by `foldl_F_forces` and each is discharged by the tied `blake2bF_forces` —
RESIDUAL #1's "× #rows", as a proof over the gates rather than over an abstract `nextBases`.

NAMED RESIDUAL: this ties the absorb to `absorbGadget`, the chain generator defined just above. What
is NOT proved here is that Midnight's authority-row schedule (`authSetBlocks` / `sched`) instantiates
`bs` — i.e. that `bs.map (fun b => (b.mVals, b.t0, b.f0))` IS `sched (authSetBlocks rows).length 0
(authSetBlocks rows)`. That row-serialization tie is `LightClientMidHashFold`'s named
Derived-vs-assumed residual and is untouched. -/
theorem absorb_forces (a : Assignment) (hbool : AllBool a) (bs : List AbsorbBlock)
    (hb : ∀ b ∈ bs, BlockHolds a b)
    (h0Bases h0Vals : List Nat) (fresh : Nat) (h0 : Holds8 a h0Bases h0Vals)
    (hacc : acceptB (absorbGadget bs h0Bases fresh).1 a = true) :
    Holds8 a (absorbGadget bs h0Bases fresh).2.1
      (LightClientMidHashFold.absorb h0Vals (bs.map (fun b => (b.mVals, b.t0, b.f0)))) := by
  have habs : LightClientMidHashFold.absorb h0Vals (bs.map (fun b => (b.mVals, b.t0, b.f0)))
      = bs.foldl (fun h b => Ref.compress h b.mVals b.t0 0 b.f0 0) h0Vals := by
    simp only [LightClientMidHashFold.absorb, List.foldl_map]
  rw [habs]
  unfold absorbGadget at hacc ⊢
  refine foldl_F_forces a _ absorbStep (by intro cs s x; rfl)
    (fun h b => Ref.compress h b.mVals b.t0 0 b.f0 0)
    (fun s h => Holds8 a s.1 h) (fun b => BlockHolds a b) ?_ bs hb
    [] (h0Bases, fresh) h0Vals h0 hacc
  rintro s h b ⟨hmlen, hm, ht0, ht1, hf0, hf1⟩ ⟨hlen, hst⟩ hbacc
  refine ⟨refCompress_length _ _ _ _ _ _, ?_⟩
  exact blake2bF_forces a hbool s.1 b.mBases b.outBases h b.mVals b.t0B b.t1B b.f0B b.f1B
    b.t0 0 b.f0 0 s.2 hlen hst hm ht0 ht1 hf0 hf1 hbacc

/-- Two `Nat` lists of equal length that agree at every `getD` index are equal. -/
theorem list_ext_getD (l1 l2 : List Nat) (hl : l1.length = l2.length)
    (h : ∀ i, i < l1.length → l1.getD i 0 = l2.getD i 0) : l1 = l2 := by
  apply List.ext_getElem hl
  intro i h1 h2
  have hi := h i h1
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
       List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some,
       Option.getD_some] at hi

/-- **`midHfold_discharged`** — Midnight's `hfold` is DERIVED, not assumed. Given the reconstructed
authority-set root (`hchain`, from `absorb_forces` over the exhibited rows) and the in-circuit pin of
those root words to the WS-anchor root (`hpin` — the coordinate equality gates), the BLAKE2b absorb
reconstructs into the anchor: `authSetRootRef rows = anchor`. This IS the `hfold` hypothesis
`LightClientMidHashFold.verifyAuthSet_from_fold` / `mid_authset_from_fold_slots_into_no_forgery` assume —
now a CONCLUSION of the chained gates. -/
theorem midHfold_discharged (a : Assignment) (rows : List (Nat × Nat)) (rootBases anchor : List Nat)
    (hchain : Holds8 a rootBases (LightClientMidHashFold.authSetRootRef rows))
    (hanchorLen : anchor.length = 8)
    (hpin : ∀ i, i < 8 → Holds a (rootBases.getD i 0) (anchor.getD i 0)) :
    LightClientMidHashFold.authSetRootRef rows = anchor := by
  obtain ⟨hrootLen, hroot⟩ := hchain
  apply list_ext_getD _ _ (by omega)
  intro i hi'
  have hi : i < 8 := by omega
  rw [← hroot i hi]
  exact hpin i hi

section Payoff
open Dregg2.Bridge.LightClientMidnight
open Dregg2.Circuit.Emit.LightClientMidHashFold

/-- **THE PAYOFF** — the Midnight/GRANDPA no-forgery guarantee with `AUTHSET_OK` FOLDED OUT: given the
EC-arc/in-AIR results and a satisfying witness whose exhibited authority rows' chained-`blake2bF` absorb
reconstructs into the pinned WS-anchor root (`hchain` from `absorb_forces` + `hpin` the root-pin gates),
the update is Midnight-VALID. `mid_authset_from_fold_slots_into_no_forgery`'s `hfold` leg is now DERIVED
by `midHfold_discharged`, not assumed — the composition wall closed end-to-end. -/
theorem mid_forgery_from_absorb (a : Assignment)
    (ts : MidTrustedState midBlakeLeaf) (u : MidUpdate midBlakeLeaf) (rootBases : List Nat)
    (hcr : midBlakeLeaf.authSetCR)
    (hpos : 0 < totalWeight midBlakeLeaf u)
    (hthr : 2 * totalWeight midBlakeLeaf u < 3 * signedWeight midBlakeLeaf u)
    (hed : edOk midBlakeLeaf u = true) (hround : roundOk midBlakeLeaf u = true)
    (hera : eraOk midBlakeLeaf ts u = true)
    (hchain : Holds8 a rootBases (authSetRootRef (u.authSet.map authRow)))
    (hanchorLen : ts.anchorRoot.length = 8)
    (hpin : ∀ i, i < 8 → Holds a (rootBases.getD i 0) (ts.anchorRoot.getD i 0)) :
    MidValidAt midBlakeLeaf ts u :=
  mid_authset_from_fold_slots_into_no_forgery hcr ts u hpos hthr hed hround hera
    (midHfold_discharged a (u.authSet.map authRow) rootBases ts.anchorRoot hchain hanchorLen hpin)

end Payoff

/-! ## §10 — Axiom hygiene (CI hard-gate). The composition rungs are pinned kernel-clean. -/

#assert_axioms testBit_bitsToNat
#assert_axioms testBit_rotr64
#assert_axioms add3Word_forces
#assert_axioms add2Word_forces
#assert_axioms xorRotWord_forces
#assert_axioms xor3Word_forces
#assert_axioms foldl_F_split
#assert_axioms foldl_F_mem_accept
#assert_axioms foldl_F_forces
#assert_axioms blakeG_split
#assert_axioms blakeG_core_forces
#assert_axioms blakeG_forces
#assert_axioms gStep_of_blakeG
#assert_axioms gStep_forces
#assert_axioms gargs_ok
#assert_axioms sigmaRow_lt
#assert_axioms blakeRound_forces
#assert_axioms blake2bCompress_forces
#assert_axioms constWord_forces
#assert_axioms xorConstWord_forces
#assert_axioms refCompress_eq
#assert_axioms blake2bFinalize_forces
#assert_axioms refInitV_eq_append
#assert_axioms blake2bInit_split
#assert_axioms blake2bInit_forces
#assert_axioms blake2bF_split
#assert_axioms blake2bF_forces
#assert_axioms absorb_forces
#assert_axioms midHfold_discharged
#assert_axioms mid_forgery_from_absorb

#print axioms blakeG_forces
#print axioms blake2bCompress_forces
#print axioms midHfold_discharged
#print axioms mid_forgery_from_absorb

end Dregg2.Circuit.Emit.Blake2bFoldForcing
