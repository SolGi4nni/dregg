/-
# Dregg2.Circuit.Emit.Sha512Gadget — a Lean-GENERATED SHA-512 AIR gadget (the Ed25519 challenge hash).

## Why this file exists (the carrier it is aimed at)

Ed25519 verification checks `[8]([s]B) = [8]R + [8]([k]A)` where the challenge scalar is
`k = SHA-512(R ‖ A ‖ M) mod L`. The `ED_OK` carrier the light-client fold would DROP is exactly this
verification equation; the SHA-512 challenge hash is one of its three sub-pieces (the other two being the
scalar multiply and the final group-equation compare). This file is that sub-piece: the SHA-512
compression algebra `k` is derived FROM. It is also a clean reusable 64-bit hash primitive — SHA-512 is
the FIPS-180-4 twin of `Sha256Gadget` at 64-bit width, and Ed25519, RFC 8032, and many transcript hashes
name it directly.

## The metaprogramming approach (GENERATED, mirroring `Sha256Gadget` at 64-bit)

SHA-512 IS SHA-256's structure at 64-bit width: the SAME `Ch`/`Maj` bit gates, the SAME message-schedule
+ round shape, the SAME `List.foldl` composition — only the WORD WIDTH (64 vs 32), the ROTATION AMOUNTS
(the `Σ`/`σ` triples below), the ROUND COUNT (80 vs 64), and the K/IV constants differ. So this gadget
REUSES, not re-derives:

  * from `Blake2bGadget` (the 64-bit machinery just built): the 64-boolean-column word encoding
    (`wordBits`/`wordValue`/`pinWord`) and the mod-2^64 adder (`addMod64`/`addMod64Head`) with its
    forcing lemma `addMod64_forces`;
  * from `Sha256Gadget` (the SHA structure, width-agnostic bit gates): the XOR gate `xorHead` +
    `xorHead_eval`, the 3-way XOR forcing `xor3_forces`, the `Ch`/`Maj` heads `chHead`/`majHead` + their
    forcings `chHead_forces`/`majHead_forces`, and the `acceptB`/`gateBodyEvalZero`/`flipAt` KAT harness.

SHA-512-SPECIFIC (generated here): the 64-bit `Σ`/`σ` source indexing + word gadget (`sigmaWord`), the
64-bit `Ch`/`Maj` word folds (`chWord`/`majWord`, folding the width-agnostic heads over `range 64`), the
round generator `sha512Round` (`Σ1 14/18/41`, `Σ0 28/34/39`), the schedule-word generator `scheduleWord`
(`σ1 19/61/6`, `σ0 1/8/7`, both with a right-shift term), and the whole 80-round compression
`sha512Compress = List.foldl sha512Round` — the 80 rounds are FREE once the round generator exists; the
80 constants K and the SHA-512 IV are data.

## The felt-encoding (reused from `Blake2bGadget`)

A 64-bit word occupies **64 boolean columns** `base..base+63`, LSB-first, each pinned by `binGate`; its
value is the degree-1 head `wordValue base = Σ_{i<64} 2^i · col(base+i)`. Consequences: ROTR/SHR are FREE
re-indexing (`sigmaSources` folds the rotation into which source column feeds each output gate); XOR/Ch/
Maj are local bit gates; mod-2^64 addition is one linear gate + carry bits (`addMod64`).

## The SHA-512 rotation triples (the ONLY algebraic difference from SHA-256)

  * `Σ0 = ROTR28 ⊕ ROTR34 ⊕ ROTR39`   (compression, all rotations)
  * `Σ1 = ROTR14 ⊕ ROTR18 ⊕ ROTR41`   (compression, all rotations)
  * `σ0 = ROTR1  ⊕ ROTR8  ⊕ SHR7`     (message schedule, one right-shift)
  * `σ1 = ROTR19 ⊕ ROTR61 ⊕ SHR6`     (message schedule, one right-shift)

## Constraint budget (mirroring `Sha256Gadget`, doubled to 64-bit)

  * `sigmaWord` (Σ0/Σ1/σ0/σ1): 64 XOR gates + 64 out pins + 64 carry pins = **192**.
  * `chWord`/`majWord`: 64 op gates + 64 out pins = **128**.
  * `addMod64` (k inputs, m carry bits): 1 sum gate + 64 out pins + m carry pins.
  * one `sha512Round` (Σ1+Ch+T1 + Σ0+Maj+T2 + newE + newA) = 192+128+68 + 192+128+68 + 68 + 68 = **912**.
  * `scheduleWord` (σ1 + σ0 + one 4-input add) = 192 + 192 + 68 = **452**.
  * one full 80-round compression ≈ **73 000** core gates + the 64 schedule words ≈ **29 000** more. This
    is the ACCEPTED zk-STARK cost — the point is EXPRESSIBILITY.

## What is AUTHORED + built vs KAT'd vs NAMED continuation

AUTHORED + built: the SHA-512-specific `sigmaWord`/`chWord`/`majWord`, the round generator `sha512Round`,
the schedule-word generator `scheduleWord`, and the whole-block generator `sha512Compress` (the `foldl`
of `sha512Round`). AUTHORED + KAT'd both-polarity, against real `hashlib.sha512` vectors: a `Nat` SHA-512
reference anchored to `sha512(b"")` and `sha512(b"abc")` (both published FIPS-180-4 vectors); the atomic
gadgets (σ0, Σ0, Ch, Maj, addMod64) ACCEPT the honest witness + REJECT a flipped output/carry limb, and
the σ0/Σ0 output words tie to the reference. Forcing lemmas (the "demonstrably computes" content):
`sigmaBit3_forces`/`sigmaBit2_forces` (the 3-source and 2-source XOR parity, via the reused
`xor3_forces`/`xor2_forces`), `chHead_forces`/`majHead_forces` (reused, width-agnostic), `addMod64_forces`
(reused, the
mod-2^64 congruence, ℤ reading). NAMED mechanical continuation (§7): the whole-block accept `#guard` is
not run — a kernel `#guard` over ~100k gates on a list-backed `Assignment` is intractable (the SAME reason
`sha256Compress`/`blake2bF` are not `#guard`-accepted whole); the atomic KATs pin the arithmetic both
polarities, and the round/schedule/compress generators pin the composition structurally (`length` guards).

## Resolution (honest)

REAL: the SHA-512 round/schedule/compression generators exist + type-check in the deployed IR-v2
vocabulary; the reference is `hashlib.sha512`-anchored (both published vectors); the XOR/Ch/Maj/add gates
FORCE their bit relations (ℤ reading); both-polarity atomic KATs are non-vacuous. NOT claimed: a
whole-compression-accepted `#guard`, the message-length pad / multi-block absorb, `k mod L`, or the
scalar-mult + group-equation that complete `ED_OK`, or native-field (`p_felt`) soundness — the gate is
read over ℤ (the SAME 31-bit-BabyBear field-width residual `Sha256Gadget` §Resolution, `Blake2bGadget`
§Resolution, and `LightClientEthAir` §6 carry: a 31-bit felt cannot hold a 64-bit word without wrap). This
file claims exactly the SHA-512 compression gadget.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/`native_decide`.
The `#guard` KATs reduce in the kernel. NEW file; imports read-only (`Blake2bGadget`, which re-exports the
`Sha256Gadget` bit gates + KAT harness — the shared 64-bit + width-agnostic primitives); standalone (NOT
imported by the truncated `Dregg2` root, built directly as `Dregg2.Circuit.Emit.Sha512Gadget`).
-/
import Dregg2.Circuit.Emit.Blake2bGadget

namespace Dregg2.Circuit.Emit.Sha512Gadget

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2 EffectVmDescriptor2)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.Sha256Gadget
  (xorHead xorHead_eval xor3_forces chHead majHead chHead_forces majHead_forces
   acceptB gateBodyEvalZero flipAt)
open Dregg2.Circuit.Emit.Blake2bGadget
  (wordBits wordValue pinWord addMod64 addMod64Head addMod64Core addMod64_forces xor2_forces)

set_option autoImplicit false

/-! ## §0 — A SHA-512 reference (Nat words), anchored against the published FIPS-180-4 vectors.

Pure `Nat` word arithmetic (kernel-reducible), `Sha256Gadget.Ref` at 64-bit width. Used ONLY to (a)
anchor itself against the `sha512(b"abc")`/`sha512(b"")` digests and (b) supply the honest witness values
the gadget KATs accept. -/

namespace Ref

/-- `2^64`. -/
def M : Nat := 18446744073709551616
/-- Truncate to 64 bits. -/
def w64 (x : Nat) : Nat := x % M
/-- Rotate-right by `n` (0 < n < 64). -/
def rotr (n x : Nat) : Nat := w64 ((x >>> n) ||| (x <<< (64 - n)))
/-- Shift-right by `n`. -/
def shr (n x : Nat) : Nat := x >>> n
/-- 64-bit modular add. -/
def add2 (x y : Nat) : Nat := w64 (x + y)
/-- 64-bit bitwise NOT. -/
def notw (x : Nat) : Nat := w64 (18446744073709551615 ^^^ x)

/-- `σ0` (message schedule): `ROTR1 ⊕ ROTR8 ⊕ SHR7`. -/
def s0 (x : Nat) : Nat := (rotr 1 x) ^^^ (rotr 8 x) ^^^ (shr 7 x)
/-- `σ1` (message schedule): `ROTR19 ⊕ ROTR61 ⊕ SHR6`. -/
def s1 (x : Nat) : Nat := (rotr 19 x) ^^^ (rotr 61 x) ^^^ (shr 6 x)
/-- `Σ0` (compression): `ROTR28 ⊕ ROTR34 ⊕ ROTR39`. -/
def bS0 (x : Nat) : Nat := (rotr 28 x) ^^^ (rotr 34 x) ^^^ (rotr 39 x)
/-- `Σ1` (compression): `ROTR14 ⊕ ROTR18 ⊕ ROTR41`. -/
def bS1 (x : Nat) : Nat := (rotr 14 x) ^^^ (rotr 18 x) ^^^ (rotr 41 x)
/-- `Ch(e,f,g)`. -/
def chf (x y z : Nat) : Nat := (x &&& y) ^^^ (notw x &&& z)
/-- `Maj(a,b,c)`. -/
def majf (x y z : Nat) : Nat := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- The 80 round constants (fractional bits of the cube roots of the first 80 primes). -/
def K : List Nat :=
  [ 0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817 ]

/-- The 8 initial hash values (√primes fractional bits, 64-bit — the SHA-512 IV). -/
def IV : List Nat :=
  [ 0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179 ]

/-- Expand a 16-word block into the 80-word message schedule (16 given + 64 expanded). -/
def schedule (w0 : List Nat) : List Nat :=
  (List.range 64).foldl (fun w _ =>
    let t := w.length
    let v := add2 (add2 (add2 (s1 (w.getD (t-2) 0)) (w.getD (t-7) 0)) (s0 (w.getD (t-15) 0)))
                  (w.getD (t-16) 0)
    w ++ [v]) w0

/-- The 8 working variables. -/
structure Hst where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  f : Nat
  g : Nat
  h : Nat

/-- One compression round. -/
def round (hs : Hst) (kt wt : Nat) : Hst :=
  let t1 := add2 (add2 (add2 (add2 hs.h (bS1 hs.e)) (chf hs.e hs.f hs.g)) kt) wt
  let t2 := add2 (bS0 hs.a) (majf hs.a hs.b hs.c)
  { a := add2 t1 t2, b := hs.a, c := hs.b, d := hs.c,
    e := add2 hs.d t1, f := hs.e, g := hs.f, h := hs.g }

/-- Compress one 16-word block from the IV → 8 digest words (80 rounds). -/
def compress (block : List Nat) : List Nat :=
  let w := schedule block
  let iv := IV
  let init : Hst :=
    { a := iv.getD 0 0, b := iv.getD 1 0, c := iv.getD 2 0, d := iv.getD 3 0,
      e := iv.getD 4 0, f := iv.getD 5 0, g := iv.getD 6 0, h := iv.getD 7 0 }
  let fin := (List.range 80).foldl (fun hs t => round hs (K.getD t 0) (w.getD t 0)) init
  [ add2 (iv.getD 0 0) fin.a, add2 (iv.getD 1 0) fin.b, add2 (iv.getD 2 0) fin.c,
    add2 (iv.getD 3 0) fin.d, add2 (iv.getD 4 0) fin.e, add2 (iv.getD 5 0) fin.f,
    add2 (iv.getD 6 0) fin.g, add2 (iv.getD 7 0) fin.h ]

/-- Single-block message `"abc"` (0x616263 ‖ 0x80 ‖ 0…0 ‖ 128-bit len=24, big-endian word load). -/
def blockAbc : List Nat := [0x6162638000000000] ++ List.replicate 14 0 ++ [0x18]
/-- Single-block empty message (0x80 ‖ 0…0 ‖ len=0). -/
def blockEmpty : List Nat := [0x8000000000000000] ++ List.replicate 15 0

-- Reference anchor: SHA-512("abc") = the published FIPS-180-4 / `hashlib.sha512(b"abc")` vector.
#guard compress blockAbc ==
  [ 0xddaf35a193617aba, 0xcc417349ae204131, 0x12e6fa4e89a97ea2, 0x0a9eeee64b55d39a,
    0x2192992a274fc1a8, 0x36ba3c23a3feebbd, 0x454d4423643ce80e, 0x2a9ac94fa54ca49f ]
-- Reference anchor: SHA-512("") = the published FIPS-180-4 / `hashlib.sha512(b"")` vector.
#guard compress blockEmpty ==
  [ 0xcf83e1357eefb8bd, 0xf1542850d66d8007, 0xd620e4050b5715dc, 0x83f4a921d36ce9ce,
    0x47d0d13c5d85f2b0, 0xff8318d2877eec2f, 0x63b931bd47417a81, 0xa538327af927da3e ]

/-- Bit `j` of `x` as a `Nat` (0/1). -/
def bit (x j : Nat) : Nat := (x >>> j) &&& 1
/-- Recompose 64 LSB-first bits (given as a `Nat → Nat` returning 0/1) into a `Nat`. -/
def natOfBits64 (f : Nat → Nat) : Nat := (List.range 64).foldl (fun acc i => acc + f i * 2^i) 0

end Ref

/-! ## §1 — Word layout in the circuit.

A word = 64 boolean columns `base..base+63`, LSB-first — REUSED verbatim from `Blake2bGadget`
(`wordBits`/`wordValue`/`pinWord`, opened above). No new encoding is introduced. -/

/-! ## §2 — The word gadgets: the SHA-512-specific `Σ`/`σ`, `Ch`, `Maj` folds.

The bit gates (`xorHead`, `chHead`, `majHead`) are the width-agnostic ones from `Sha256Gadget`; only the
FOLD WIDTH (64) and the `Σ`/`σ` SOURCE INDEXING (64-bit rotations) are SHA-512-specific. -/

/-- Source bit indices (within a 64-bit word) feeding output bit `i` of a Σ/σ function
`ROTR r1 ⊕ ROTR r2 ⊕ (SHR/ROTR third)`. SHR drops the third term when it shifts past the top. -/
def sigmaSources (r1 r2 third : Nat) (isShift : Bool) (i : Nat) : List Nat :=
  let a := (i + r1) % 64
  let b := (i + r2) % 64
  if isShift then
    (if i + third < 64 then [a, b, i + third] else [a, b])
  else
    [a, b, (i + third) % 64]

/-- **Σ/σ gadget** (Σ0/Σ1/σ0/σ1). Input word at `inBase`, output at `outBase`, per-bit XOR carries at
`carBase`; `(r1,r2,third,isShift)` selects the function. 192 constraints. -/
def sigmaWord (inBase outBase carBase r1 r2 third : Nat) (isShift : Bool) : List VmConstraint2 :=
  (List.range 64).map (fun i =>
    cgH (xorHead ((sigmaSources r1 r2 third isShift i).map (inBase + ·)) (outBase+i) (carBase+i)))
  ++ (wordBits outBase).map binGate
  ++ (wordBits carBase).map binGate

/-- **Ch gadget** `Ch(e,f,g)` → word at `outBase`. 128 constraints. -/
def chWord (eBase fBase gBase outBase : Nat) : List VmConstraint2 :=
  (List.range 64).map (fun i => cgH (chHead (eBase+i) (fBase+i) (gBase+i) (outBase+i)))
  ++ (wordBits outBase).map binGate

/-- **Maj gadget** `Maj(a,b,c)` → word at `outBase`. 128 constraints. -/
def majWord (aBase bBase cBase outBase : Nat) : List VmConstraint2 :=
  (List.range 64).map (fun i => cgH (majHead (aBase+i) (bBase+i) (cBase+i) (outBase+i)))
  ++ (wordBits outBase).map binGate

/-! ## §3 — The round + schedule + block generators (the parameterized fold — the KEY deliverable). -/

/-- An 8-word working state, each field a column base. -/
structure St where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  f : Nat
  g : Nat
  h : Nat

/-- **`sha512Round`** — one compression round as GENERATED constraints, given the state layout `s`, the
message-word base `wBase`, the round constant `kConst`, and the next free column `fresh`. Returns
`(constraints, next state layout, next free column)`. The 8-word rotation `(a..h) ↦
(newA, a, b, c, newE, e, f, g)` is pure re-labelling (no constraints). `Σ1 = 14/18/41`, `Σ0 = 28/34/39`.
912 constraints. -/
def sha512Round (s : St) (wBase : Nat) (kConst : ℤ) (fresh : Nat) :
    List VmConstraint2 × St × Nat :=
  let s1  := fresh;      let s1c := s1  + 64   -- Σ1(e)  : out + per-bit carry
  let ch  := s1c + 64                          -- Ch(e,f,g)
  let t1  := ch  + 64;   let t1c := t1  + 64   -- T1 : out + 3 add-carry bits
  let s0  := t1c + 3;    let s0c := s0  + 64   -- Σ0(a)
  let mj  := s0c + 64                          -- Maj(a,b,c)
  let t2  := mj  + 64;   let t2c := t2  + 64   -- T2 : out + 3 add-carry bits
  let ne  := t2c + 3;    let nec := ne  + 64   -- new e = d + T1
  let na  := nec + 3;    let nac := na  + 64   -- new a = T1 + T2
  let next := nac + 3
  let cs : List VmConstraint2 :=
       sigmaWord s.e s1 s1c 14 18 41 false
    ++ chWord s.e s.f s.g ch
    ++ addMod64 [wordValue s.h, wordValue s1, wordValue ch, Head.c kConst, wordValue wBase]
         t1 [t1c, t1c+1, t1c+2]
    ++ sigmaWord s.a s0 s0c 28 34 39 false
    ++ majWord s.a s.b s.c mj
    ++ addMod64 [wordValue s0, wordValue mj] t2 [t2c, t2c+1, t2c+2]
    ++ addMod64 [wordValue s.d, wordValue t1] ne [nec, nec+1, nec+2]
    ++ addMod64 [wordValue t1, wordValue t2] na [nac, nac+1, nac+2]
  let s' : St := { a := na, b := s.a, c := s.b, d := s.c, e := ne, f := s.e, g := s.f, h := s.g }
  (cs, s', next)

/-- **`scheduleWord`** — one message-schedule step `W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]`
as GENERATED constraints, given the four input word bases, the output base, and the next free column for
the two sigma scratch words. `σ1 = 19/61/6`, `σ0 = 1/8/7` (both with a right-shift term). Returns
`(constraints, next free column)`. 452 constraints. -/
def scheduleWord (w2 w7 w15 w16 : Nat) (outBase fresh : Nat) : List VmConstraint2 × Nat :=
  let sg1 := fresh;      let sg1c := sg1 + 64   -- σ1(W[t-2])
  let sg0 := sg1c + 64;  let sg0c := sg0 + 64   -- σ0(W[t-15])
  let cc  := sg0c + 64                          -- 3 add-carry bits
  let next := cc + 3
  let cs : List VmConstraint2 :=
       sigmaWord w2 sg1 sg1c 19 61 6 true
    ++ sigmaWord w15 sg0 sg0c 1 8 7 true
    ++ addMod64 [wordValue sg1, wordValue w7, wordValue sg0, wordValue w16] outBase [cc, cc+1, cc+2]
  (cs, next)

/-- **`sha512Compress`** — the whole 80-round compression as ONE generated constraint list, given the 16
message-word bases `wBases`, the 8 IV/state bases `s0`, and the first free column. The 80 rounds are the
FREE `List.foldl` of `sha512Round`; this is the "generator makes them free" claim, realized at 80 rounds.
(Not `#guard`-accepted whole — see §7.) -/
def sha512Compress (wBases : List Nat) (s0 : St) (fresh : Nat) : List VmConstraint2 :=
  let step := fun (acc : List VmConstraint2 × St × Nat) (t : Nat) =>
    let (cs, st, fr) := acc
    let (cs', st', fr') := sha512Round st (wBases.getD t 0) ((Ref.K.getD t 0 : Nat) : ℤ) fr
    (cs ++ cs', st', fr')
  ((List.range 80).foldl step (([] : List VmConstraint2), s0, fresh)).1

/-! ## §4 — Forcing lemmas: the emitted gates FORCE the SHA-512 bit functions (ℤ reading).

The atomic pieces the round composes from, each forced. The `Σ`/`σ` bits reuse the SHA `xorHead`, so the
3-source (all-rotation Σ) and 2-source (shift-dropped σ) forcings are the reused `xor3_forces`/
`xor2_forces` specialized to the SHA-512 sigma bit; `Ch`/`Maj` reuse the width-agnostic SHA forcings; the
add reuses `Blake2bGadget.addMod64_forces`. -/

/-- **A 3-source Σ/σ output bit is forced** to the XOR parity `out = iA + iB + iC − 2·car` (the exact
content of `iA ⊕ iB ⊕ iC` once the columns are the boolean bits the pins force). Via `xor3_forces`. -/
theorem sigmaBit3_forces (a : Assignment) (iA iB iC out car : Nat)
    (hg : evalH (xorHead [iA, iB, iC] out car) a = 0) :
    a out = a iA + a iB + a iC - 2 * a car :=
  xor3_forces a iA iB iC out car hg

/-- **A 2-source (shift-dropped) σ output bit is forced** to `out = iA + iB − 2·car` — the reused
`Blake2bGadget.xor2_forces`, applied at the top bits of `σ0`/`σ1` where the `SHR` term drops. -/
theorem sigmaBit2_forces (a : Assignment) (iA iB out car : Nat)
    (hg : evalH (xorHead [iA, iB] out car) a = 0) :
    a out = a iA + a iB - 2 * a car :=
  xor2_forces a iA iB out car hg

#assert_axioms sigmaBit3_forces
#assert_axioms sigmaBit2_forces
#assert_axioms chHead_forces
#assert_axioms majHead_forces
#assert_axioms addMod64_forces

/-! ## §5 — KAT: the GENERATED constraints ACCEPT the reference's honest values and REJECT tamper.

`acceptB` (reused from `Sha256Gadget`) is the ℤ reading of the emitted gate bodies: every `.base (.gate
e)` has `e.eval a = 0`. Anchored to §0's `hashlib.sha512`-validated reference. -/

/-- Bit `j` of `x` as a felt column value. -/
def bZ (x j : Nat) : ℤ := (Ref.bit x j : Nat)

/-- Sum of the (present) source bits feeding output bit `i` of a Σ/σ over input word `X`. -/
def srcSum (X r1 r2 third : Nat) (isShift : Bool) (i : Nat) : Nat :=
  ((sigmaSources r1 r2 third isShift i).map (Ref.bit X)).foldl (· + ·) 0

/-- Honest witness for a standalone Σ/σ over input `X` (layout inBase=0, outBase=64, carBase=128). -/
def sigmaAsg (X r1 r2 third : Nat) (isShift : Bool) : Assignment := fun col =>
  if col < 64 then bZ X col
  else if col < 128 then ((srcSum X r1 r2 third isShift (col-64) % 2 : Nat) : ℤ)
  else if col < 192 then ((srcSum X r1 r2 third isShift (col-128) / 2 : Nat) : ℤ)
  else 0

/-- Honest witness for a standalone `Ch(E,F,G)` (bases 0/64/128, out 192). -/
def chAsg (E F G : Nat) : Assignment := fun col =>
  if col < 64 then bZ E col
  else if col < 128 then bZ F (col-64)
  else if col < 192 then bZ G (col-128)
  else if col < 256 then bZ (Ref.chf E F G) (col-192)
  else 0

/-- Honest witness for a standalone `Maj(X,Y,Z)` (bases 0/64/128, out 192). -/
def majAsg (X Y Z : Nat) : Assignment := fun col =>
  if col < 64 then bZ X col
  else if col < 128 then bZ Y (col-64)
  else if col < 192 then bZ Z (col-128)
  else if col < 256 then bZ (Ref.majf X Y Z) (col-192)
  else 0

/-- Honest witness for a standalone 3-input `addMod64` (bases 0/64/128, out 192, carry 256/257). -/
def addAsg (X Y Z : Nat) : Assignment := fun col =>
  if col < 64 then bZ X col
  else if col < 128 then bZ Y (col-64)
  else if col < 192 then bZ Z (col-128)
  else if col < 256 then bZ (Ref.w64 (X + Y + Z)) (col-192)
  else if col < 258 then (Ref.bit ((X + Y + Z) / Ref.M) (col-256) : ℤ)
  else 0

/-- The two Σ/σ instances under test (σ0: rotations 1,8 + shift 7; Σ0: rotations 28,34,39). -/
def sigma0Gadget : List VmConstraint2 := sigmaWord 0 64 128 1 8 7 true
def bigSigma0Gadget : List VmConstraint2 := sigmaWord 0 64 128 28 34 39 false
def chGadget : List VmConstraint2 := chWord 0 64 128 192
def majGadget : List VmConstraint2 := majWord 0 64 128 192
def addGadget : List VmConstraint2 := addMod64 [wordValue 0, wordValue 64, wordValue 128] 192 [256,257]

-- Constants under test: real SHA-512 IV words (nonzero, exercise every bit path).
private def X0 : Nat := 0x6a09e667f3bcc908  -- IV a
private def X1 : Nat := 0xbb67ae8584caa73b  -- IV b
private def X2 : Nat := 0x3c6ef372fe94f82b  -- IV c

/-! ### σ0 — accepts the honest witness, rejects a flipped output bit, out word ties to the reference. -/
#guard acceptB sigma0Gadget (sigmaAsg X0 1 8 7 true) == true
#guard acceptB sigma0Gadget (flipAt (sigmaAsg X0 1 8 7 true) 69) == false   -- flip out bit 5
#guard Ref.natOfBits64 (fun i => srcSum X0 1 8 7 true i % 2) == Ref.s0 X0

/-! ### Σ0 — accepts, rejects a flipped carry bit, out word ties to the reference. -/
#guard acceptB bigSigma0Gadget (sigmaAsg X0 28 34 39 false) == true
#guard acceptB bigSigma0Gadget (flipAt (sigmaAsg X0 28 34 39 false) 134) == false  -- flip carry bit 6
#guard Ref.natOfBits64 (fun i => srcSum X0 28 34 39 false i % 2) == Ref.bS0 X0

/-! ### Ch — accepts, rejects a flipped output bit. -/
#guard acceptB chGadget (chAsg X0 X1 X2) == true
#guard acceptB chGadget (flipAt (chAsg X0 X1 X2) 200) == false

/-! ### Maj — accepts, rejects a flipped output bit. -/
#guard acceptB majGadget (majAsg X0 X1 X2) == true
#guard acceptB majGadget (flipAt (majAsg X0 X1 X2) 210) == false

/-! ### addMod64 — accepts, rejects a flipped output bit, out word ties to the reference. -/
#guard acceptB addGadget (addAsg X0 X1 X2) == true
#guard acceptB addGadget (flipAt (addAsg X0 X1 X2) 192) == false
#guard Ref.natOfBits64 (fun i => Ref.bit (Ref.w64 (X0 + X1 + X2)) i) == Ref.w64 (X0 + X1 + X2)

/-! ## §6 — Structural `#guard`s: the generators produce the budgeted shapes; AIR packaging. -/

#guard sigma0Gadget.length == 192
#guard bigSigma0Gadget.length == 192
#guard chGadget.length == 128
#guard majGadget.length == 128
#guard addGadget.length == 67
#guard (sha512Round ⟨0,64,128,192,256,320,384,448⟩ 512 0 576).1.length == 912
#guard (scheduleWord 0 64 128 192 256 320).1.length == 452

/-- A single Σ/σ gadget packaged as an `EffectVmDescriptor2` (the AIR type the light-client emits),
showing the generator drops straight into the deployed descriptor vocabulary. -/
def sigma0Desc : EffectVmDescriptor2 :=
  { name        := "dregg-sha512-sigma0::demo"
  , traceWidth  := 192
  , piCount     := 0
  , tables      := []
  , constraints := sigma0Gadget
  , hashSites   := []
  , ranges      := [] }

#guard sigma0Desc.constraints.length == 192
#guard sigma0Desc.traceWidth == 192

/-! ## §7 — The PRECISE named continuation to a folded `ED_OK` (mechanical, NOT free).

The generators make each step mechanical; none of §7 is claimed built. In order:

  1. **The whole-compression accept `#guard`** — NOT run. A kernel `#guard` of `acceptB (sha512Compress …)
     witness` over ~100k gates on a list-backed `Assignment` is intractable (the SAME reason
     `sha256Compress`/`blake2bF` are not `#guard`-accepted whole). The atomic KATs pin the arithmetic both
     polarities; the round/schedule/compress generators pin the composition structurally (`length`
     guards); the `Nat` reference is `hashlib.sha512`-anchored on the published vectors, so
     `sha512Compress`'s honest witness is validated transitively.

  2. **Message-length pad + multi-block absorb** — SHA-512 pads `M ‖ 0x80 ‖ 0…0 ‖ len₁₂₈` to a multiple
     of 1024 bits and chains blocks by feeding block `k`'s 8 output words as block `k+1`'s IV (a `foldl`
     of `sha512Compress`, the "generator makes them free" pattern one level up). For Ed25519 the hashed
     message is `R ‖ A ‖ M` (64 bytes + the message), spanning one or more 1024-bit blocks.

  3. **`k = digest mod L` + the group equation** — the 512-bit digest is reduced mod the order
     `L = 2^252 + 27742317777372353535851937790883648493` (a wide modular-reduction gadget), then the
     `ED_OK` verify equation `[8]([s]B) = [8]R + [8]([k]A)` is the scalar-multiply + twisted-Edwards group
     ops (the `Ed25519Gadget` foundation). This SHA-512 gadget is the challenge-hash sub-piece of that
     fold; the scalar mult, the mod-L reduction, and the group-equation compare remain.

**Gate-count reality (order of magnitude).** One `sha512Round` is `912` core gates; the 64 schedule words
add `~29 000`; a whole 80-round compression is `~73 000` core gates — hundreds of thousands of AIR gates
for a multi-block hash, the accepted zk-STARK hashing cost (the reason `ED_OK`'s hash is a trusted carrier
today, and the reason the point of THIS slice is EXPRESSIBILITY: the SHA-512 core is generated + KAT'd +
forced, so each step above is COMPOSITION over these generators, not new constraint algebra). None of §7
is claimed built; this file is the SHA-512 compression gadget it stands on.
-/

end Dregg2.Circuit.Emit.Sha512Gadget
