/-
# `Dregg2.Crypto.Keccak.Fips202Sponge` — a FAITHFUL, bit-addressed FIPS 202 SPONGE specification.

`Fips202Spec` specifies the PERMUTATION Keccak-p[1600,24] = Keccak-f[1600] (FIPS 202 §3), and
`Fips202Round.keccakF_refines_spec` proves the executable permutation refines it. This file is the
SPEC HALF of the layer ABOVE the permutation: the sponge construction of

  NIST FIPS 202, "SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions",
  Aug 2015, https://doi.org/10.6028/NIST.FIPS.202

specifically §5.1 (`pad10*1`, Algorithm 9), §4 (`SPONGE[f, pad, r](N, d)`, Algorithm 8), §5.2
(`KECCAK[c]`), §6.1/§6.2 (SHA-3 and SHAKE), and §B.1 (the byte-string ↔ bit-string conversion).

Everything here is a bit-string / bit-function object: messages are `List Bool` (bit `0` first, as in
FIPS 202's `N[0] N[1] …`) and the state is `Fips202.KState = Fin 5 → Fin 5 → Fin 64 → Bool`. NOTHING
here mentions the executable `Dregg2.Crypto.Keccak` — no `UInt64` lanes, no `Array` state, no
`Keccak.absorb`/`Keccak.squeeze`. The only `UInt8` occurrences are in the §B.1 byte-encoding
section, which is itself part of the standard. The refinement of the executable byte-addressed
sponge to this spec lives in `Dregg2.Crypto.Keccak.Fips202SpongeRefine`.

Imports only `Fips202Spec` (no Mathlib): no `sorry`, no `axiom`, only `Bool`/`Fin`/`Nat`/`List`.
-/
import Dregg2.Crypto.Keccak.Fips202Spec

namespace Dregg2.Crypto.Keccak.Fips202

/-! ## `List.getD` plumbing (general, default-valued indexing)

The spec indexes bit strings with `List.getD … false`, which reads `false` past the end — exactly
FIPS 202's zero-extension `P_i || 0^c`. These four are the general lemmas that lets that indexing
commute with `++`, `take` and `drop`. -/

theorem getD_append_lt {α} (l l' : List α) (d : α) (n : Nat) (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_ge {α} (l l' : List α) (d : α) (n : Nat) (h : l.length ≤ n) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_take {α} (l : List α) (n i : Nat) (d : α) :
    (l.take n).getD i d = if i < n then l.getD i d else d := by
  by_cases h : i < n
  · rw [if_pos h]
    simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]
  · rw [if_neg h, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega)]
    rfl

theorem getD_drop {α} (l : List α) (n i : Nat) (d : α) :
    (l.drop n).getD i d = l.getD (n + i) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-! ## §3.1.2 — the state ↔ string correspondence

FIPS 202 §3.1.2: for a 1600-bit string `S`, the state array is `A[x, y, z] = S[w(5y + x) + z]`
with `w = 64`. So string index `i` names the bit `x = (i / 64) mod 5`, `y = (i / 64) / 5`,
`z = i mod 64`. `bitIdx` is the forward map and `stateBit` the backward one; `stateBit_bitIdx`
proves they are an inverse pair. -/

/-- FIPS 202 §3.1.2: the position in the 1600-bit string of state bit `A[x, y, z]`, i.e.
`w(5y + x) + z` for `w = 64`. -/
def bitIdx (x y : Fin 5) (z : Fin 64) : Nat := 64 * (5 * y.val + x.val) + z.val

/-- FIPS 202 §3.1.2, read backwards: bit `i` of the 1600-bit string denoted by a state. -/
def stateBit (S : KState) (i : Nat) : Bool :=
  S (m5 (i / 64)) (m5 (i / 64 / 5)) ⟨i % 64, Nat.mod_lt _ (by decide)⟩

/-- The §3.1.2 correspondence is a genuine inverse pair: reading string position `bitIdx x y z`
out of a state gives back `A[x, y, z]`. -/
@[simp] theorem stateBit_bitIdx (S : KState) (x y : Fin 5) (z : Fin 64) :
    stateBit S (bitIdx x y z) = S x y z := by
  have hx : x.val < 5 := x.isLt
  have hy : y.val < 5 := y.isLt
  have hz : z.val < 64 := z.isLt
  unfold stateBit bitIdx
  rw [show (64 * (5 * y.val + x.val) + z.val) / 64 = 5 * y.val + x.val by omega,
      show (5 * y.val + x.val) / 5 = y.val by omega,
      show m5 (5 * y.val + x.val) = x from Fin.ext (by simp only [m5]; omega),
      show m5 y.val = y from Fin.ext (by simp only [m5]; omega)]
  exact congrArg _ (Fin.ext (by simp only []; omega))

/-- `bitIdx` lands inside the 1600-bit state string. -/
theorem bitIdx_lt (x y : Fin 5) (z : Fin 64) : bitIdx x y z < 1600 := by
  have := x.isLt; have := y.isLt; have := z.isLt
  simp only [bitIdx]; omega

/-- The all-zero state `0^b` of FIPS 202 Algorithm 8 step 5. -/
def zeroState : KState := fun _ _ _ => false

/-! ## §4 Algorithm 8 — the sponge

```
SPONGE[f, pad, r](N, d):
  1. P = N || pad(r, len(N))
  2. n = len(P) / r
  3. c = b − r
  4. Let P_0, …, P_{n−1} be the r-bit blocks of P
  5. S = 0^b
  6. For i from 0 to n−1: S = f(S ⊕ (P_i || 0^c))
  7. Z = the empty string
  8. Z = Z || Trunc_r(S)
  9. If d ≤ |Z|, return Trunc_d(Z); else S = f(S), continue at step 8.
```
-/

/-- Algorithm 8 step 6, the per-block state update *before* `f`: `S ⊕ (P_i || 0^c)`. The zero
extension `|| 0^c` is exactly `List.getD … false` reading past the end of the `r`-bit block `P`. -/
def xorBlock (S : KState) (P : List Bool) : KState :=
  fun x y z => xor (S x y z) (P.getD (bitIdx x y z) false)

/-- Algorithm 8 step 4: the `i`-th `r`-bit block `P_i` of `P`. -/
def blockAt (r : Nat) (P : List Bool) (i : Nat) : List Bool := (P.drop (i * r)).take r

/-- Reading inside a block is reading `P` at the block's absolute offset; past the block's `r` bits
it is the `0^c` zero extension. -/
theorem blockAt_getD (r : Nat) (P : List Bool) (i k : Nat) :
    (blockAt r P i).getD k false = if k < r then P.getD (i * r + k) false else false := by
  simp only [blockAt, getD_take, getD_drop]

/-- Algorithm 8 steps 5–6 (the ABSORB phase): starting from `0^b`, for each of the `n = |P| / r`
blocks XOR `P_i || 0^c` into the state and apply `f = Keccak-f[1600]`. -/
def spongeAbsorb (r : Nat) (P : List Bool) : KState :=
  (List.range (P.length / r)).foldl
    (fun S i => keccakF (xorBlock S (blockAt r P i))) zeroState

/-- Algorithm 8 step 8's `Trunc_r(S)`: the first `r` bits of the state's string. -/
def truncR (r : Nat) (S : KState) : List Bool := (List.range r).map (stateBit S)

/-- Algorithm 8 steps 7–9, unrolled: the concatenation `Trunc_r(S) || Trunc_r(f S) || …` of `n`
squeezed blocks, applying `f` BETWEEN blocks (step 9 applies `f` only when another block is
needed — hence no `f` after the last block). -/
def squeezeBlocks (r : Nat) : Nat → KState → List Bool
  | 0, _ => []
  | n + 1, S => truncR r S ++ squeezeBlocks r n (keccakF S)

/-- The number of squeeze blocks the step-9 test `d ≤ |Z|` demands: the least `n` with `n·r ≥ d`,
i.e. `⌈d / r⌉`. (At `d = 0` FIPS 202 emits one block and truncates it away; `⌈0/r⌉ = 0` blocks
gives the same empty output.) -/
def numBlocks (r d : Nat) : Nat := (d + r - 1) / r

/-- Algorithm 8 steps 7–10 (the SQUEEZE phase): emit `⌈d/r⌉` rate-blocks with `f` between them,
then `Trunc_d`. -/
def spongeSqueeze (r : Nat) (S : KState) (d : Nat) : List Bool :=
  (squeezeBlocks r (numBlocks r d) S).take d

@[simp] theorem truncR_length (r : Nat) (S : KState) : (truncR r S).length = r := by
  simp [truncR]

theorem squeezeBlocks_length (r n : Nat) (S : KState) :
    (squeezeBlocks r n S).length = n * r := by
  induction n generalizing S with
  | zero => simp [squeezeBlocks]
  | succ n ih =>
    simp only [squeezeBlocks, List.length_append, truncR_length, ih, Nat.succ_mul]
    omega

/-- The squeeze really does produce `d` bits (the step-9 loop runs long enough). -/
theorem spongeSqueeze_length (r : Nat) (S : KState) (d : Nat) (hr : 0 < r) :
    (spongeSqueeze r S d).length = d := by
  have h : d ≤ numBlocks r d * r := by
    simp only [numBlocks]
    have h1 := Nat.div_add_mod (d + r - 1) r
    have h2 := Nat.mod_lt (d + r - 1) hr
    have h3 : (d + r - 1) / r * r = r * ((d + r - 1) / r) := Nat.mul_comm _ _
    omega
  simp only [spongeSqueeze, List.length_take, squeezeBlocks_length]
  omega

/-! ## §5.1 Algorithm 9 — `pad10*1` -/

/-- The arithmetic of Algorithm 9's `j = (−m − 2) mod x`, in `Nat`: adding `(x − n mod x) mod x`
to `n` lands on a multiple of `x`. -/
theorem add_negMod_mod (x n : Nat) (hx : 0 < x) : (n + (x - n % x) % x) % x = 0 := by
  by_cases h : n % x = 0
  · simp [h, Nat.mod_self]
  · have hlt : n % x < x := Nat.mod_lt _ hx
    have h1 : (x - n % x) % x = x - n % x := Nat.mod_eq_of_lt (by omega)
    rw [Nat.add_mod]
    simp only [h1]
    rw [show n % x + (x - n % x) = x by omega, Nat.mod_self]

/-- FIPS 202 §5.1 Algorithm 9, `pad10*1(x, m)`: `j = (−m − 2) mod x`; return `1 || 0^j || 1`.
The negative modulus is written in `Nat` as `(x − (m + 2) mod x) mod x`. -/
def pad10s1 (x m : Nat) : List Bool :=
  true :: (List.replicate ((x - (m + 2) % x) % x) false ++ [true])

theorem pad10s1_length_eq (x m : Nat) :
    (pad10s1 x m).length = (x - (m + 2) % x) % x + 2 := by
  simp [pad10s1]

/-- Algorithm 9's defining property: the padding brings the total length up to a multiple of the
rate (for `x > 0`). -/
theorem pad10s1_length (x m : Nat) (hx : 0 < x) :
    (m + (pad10s1 x m).length) % x = 0 := by
  rw [pad10s1_length_eq,
    show m + ((x - (m + 2) % x) % x + 2) = (m + 2) + (x - (m + 2) % x) % x by omega]
  exact add_negMod_mod x (m + 2) hx

/-- Algorithm 8 step 1: `P = N || pad10*1(r, |N|)`. -/
def padded (r : Nat) (N : List Bool) : List Bool := N ++ pad10s1 r N.length

/-- **The FIPS 202 §4 sponge** `SPONGE[Keccak-p[1600,24], pad10*1, r](N, d)`. -/
def sponge (r : Nat) (N : List Bool) (d : Nat) : List Bool :=
  spongeSqueeze r (spongeAbsorb r (padded r N)) d

/-! ## §5.2 / §6 — `KECCAK[c]`, SHA-3 and SHAKE -/

/-- FIPS 202 §5.2: `KECCAK[c](N, d) = SPONGE[Keccak-p[1600, 24], pad10*1, 1600 − c](N, d)`. -/
def keccakC (c : Nat) (N : List Bool) (d : Nat) : List Bool := sponge (1600 - c) N d

/-- FIPS 202 §6.2: `SHAKE128(M, d) = KECCAK[256](M || 1111, d)` — rate `1600 − 256 = 1344` bits
(168 bytes). -/
def SHAKE128 (M : List Bool) (d : Nat) : List Bool :=
  keccakC 256 (M ++ [true, true, true, true]) d

/-- FIPS 202 §6.2: `SHAKE256(M, d) = KECCAK[512](M || 1111, d)` — rate `1600 − 512 = 1088` bits
(136 bytes). -/
def SHAKE256 (M : List Bool) (d : Nat) : List Bool :=
  keccakC 512 (M ++ [true, true, true, true]) d

/-- FIPS 202 §6.1: `SHA3-256(M) = KECCAK[512](M || 01, 256)`. -/
def SHA3_256 (M : List Bool) : List Bool := keccakC 512 (M ++ [false, true]) 256

/-- FIPS 202 §6.1: `SHA3-512(M) = KECCAK[1024](M || 01, 512)`. -/
def SHA3_512 (M : List Bool) : List Bool := keccakC 1024 (M ++ [false, true]) 512

/-! ## §B.1 — bytes ↔ bits

FIPS 202 §B.1 converts a byte (hex) string to a bit string LITTLE-ENDIAN WITHIN EACH BYTE: byte `i`
of the stream supplies bits `8i … 8i+7` of the bit string, LEAST significant bit of the byte first.
(This is what makes the SHAKE domain byte `0x1F` denote the four bits `1111` followed by the
`pad10*1` leading `1`, and the terminator byte `0x80` denote `0000000 1`.) -/

/-- FIPS 202 §B.1: the 8 bits of one byte, least-significant first. -/
def bitsOfByte (b : UInt8) : List Bool := (List.range 8).map (fun i => b.toBitVec.getLsbD i)

/-- FIPS 202 §B.1: a byte stream as a bit string. -/
def bitsOfBytes (bs : List UInt8) : List Bool := bs.flatMap bitsOfByte

@[simp] theorem bitsOfByte_length (b : UInt8) : (bitsOfByte b).length = 8 := by
  simp [bitsOfByte]

@[simp] theorem bitsOfBytes_length (bs : List UInt8) : (bitsOfBytes bs).length = 8 * bs.length := by
  induction bs with
  | nil => simp [bitsOfBytes]
  | cons b bs ih =>
    simp only [bitsOfBytes, List.flatMap_cons, List.length_append, bitsOfByte_length,
      List.length_cons] at *
    omega

@[simp] theorem bitsOfBytes_append (bs cs : List UInt8) :
    bitsOfBytes (bs ++ cs) = bitsOfBytes bs ++ bitsOfBytes cs := by
  simp [bitsOfBytes, List.flatMap_append]

theorem bitsOfByte_getD (b : UInt8) (i : Nat) (h : i < 8) :
    (bitsOfByte b).getD i false = b.toBitVec.getLsbD i := by
  simp [bitsOfByte, List.getD_eq_getElem?_getD, h]

/-- **The §B.1 indexing law.** Bit `i` of the bit string is bit `i mod 8` of byte `i / 8`. Holds
for ALL `i`: out of range both sides are `false`, since `getD` defaults to `0` / `false`. -/
theorem bitsOfBytes_getD (bs : List UInt8) (i : Nat) :
    (bitsOfBytes bs).getD i false = (bs.getD (i / 8) 0).toBitVec.getLsbD (i % 8) := by
  induction bs generalizing i with
  | nil => simp [bitsOfBytes, List.getD]
  | cons b bs ih =>
    by_cases h : i < 8
    · have hd : i / 8 = 0 := Nat.div_eq_of_lt h
      have hm : i % 8 = i := Nat.mod_eq_of_lt h
      simp only [bitsOfBytes, List.flatMap_cons, hd, hm, List.getD_cons_zero]
      rw [getD_append_lt _ _ _ _ (by simp [h])]
      exact bitsOfByte_getD b i h
    · have hd : i / 8 = (i - 8) / 8 + 1 := by omega
      have hm : i % 8 = (i - 8) % 8 := by omega
      simp only [bitsOfBytes, List.flatMap_cons, hd, hm, List.getD_cons_succ]
      rw [getD_append_ge _ _ _ _ (by simp; omega)]
      simp only [bitsOfByte_length]
      exact ih (i - 8)

end Dregg2.Crypto.Keccak.Fips202
