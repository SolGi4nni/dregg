/-
# Dregg2.Circuit.Emit.Blake2bGadget — a Lean-GENERATED BLAKE2b AIR gadget (the LAST hash primitive).

## Why this file exists (the carrier it is aimed at)

The Midnight light-client (`LightClientMidnight`) carries a trusted `authSetOk` CARRIER: the authority-set
ROOT is a domain-separated BLAKE2b commitment over the sorted `(authorityId, weight)` rows, checked
against the WS-anchor-pinned root (`authSetCommit == anchor.authoritySetRoot`). It is asserted as a
witnessed boolean the same way `Sha256Gadget` was aimed at the ETH `FIN_OK`/`EXEC_OK` fold. Midnight is
a Substrate chain whose hash is BLAKE2b (64-bit words), NOT SHA-256 — so the in-circuit derivation that
would DROP `authSetOk` needs a BLAKE2b gadget. This file is that gadget: the compression `F` the
authority-set root is derived FROM.

With this file, all four chains have their HASH primitives GENERATED in Lean: SHA-256 (`Sha256Gadget`)
for eth/tm/sol, BLAKE2b (here) for mid. Only the EC signature aggregates remain (`BLS_OK` via
`Bls12381Tower`, `ED_OK` via `Ed25519Gadget` — the foundations already laid).

## The metaprogramming approach (GENERATED, mirroring `Sha256Gadget`)

BLAKE2b is ARX with the SAME bit-gate vocabulary SHA uses: XOR, mod-2^w add, and rotations. A 64-bit
word is 64 boolean columns (SHA's 32, doubled); rotations are FREE re-indexing; XOR reuses the SHA
`xorHead`; mod-2^64 add is `addMod64` (SHA's `addMod32` at 2^64). Everything is a `def`-GENERATOR over
`AirBuilder.Head` (`Σ coeff·∏cols + const`), each constraint a per-row gate `cgH head` reusing
`AirBuilder.headToExpr_eval`. The `G` mixing function, the round (8 `G` over the `SIGMA` schedule), and
the whole 12-round compression are a `List.foldl` of the round generator — the 12 rounds are FREE once
`blakeG` exists; nothing is authored per-round or per-instance (the "generator makes them free" claim,
realized as in `sha256Compress`). Reuses from `Sha256Gadget` (imported): `xorHead`/`xorHead_eval`
(the XOR gate + its evaluation), `xor3_forces` (the 3-way XOR forcing, for the finalization), and the
`acceptB`/`gateBodyEvalZero`/`flipAt` KAT harness.

## The felt-encoding

A 64-bit word occupies **64 boolean columns** `base..base+63`, LSB-first (SHA's 32-bit doubled). Its
value is the degree-1 head `wordValue base = Σ_{i<64} 2^i·col(base+i)`. Consequences:

  * ROTR^n is FREE — pure re-indexing of which bit column feeds the next gate (`xorRotSources`): the
    BLAKE2b rotations (32/24/16/63, all RIGHT-rotations) are applied to a XOR result `(A^B) >>> R`, so
    output bit `i` reads source bit `(i+R) mod 64` of each input — the rotation folds into the XOR's
    source indexing, NO extra gate.
  * XOR is the reused SHA `xorHead` bit gate: for a 2-input XOR `iA+iB = out + 2·car` pins `out = iA⊕iB`,
    `car = iA∧iB`; the 3-input finalization `iA+iB+iC = out + 2·car` pins `out` the parity, `car` the
    majority-count bit.
  * mod-2^64 addition is one linear gate over the input value-heads plus explicit carry bits
    (`addMod64`): `Σ inputs − Σ 2^i·out_i − 2^64·Σ 2^t·carBit_t = 0`, carry range-bounded by its bits
    (2 bits for the 3-summand adds `v[a]+v[b]+x`; 1 bit for the 2-summand adds `v[c]+v[d]`).

## The G mixing function (the ARX core) and the round

`G(v; a,b,c,d, x,y)` is 4 mod-2^64 adds + 4 XOR-and-rotate steps:
```
  v[a] = v[a]+v[b]+x ;  v[d] = (v[d]^v[a]) >>> 32
  v[c] = v[c]+v[d]   ;  v[b] = (v[b]^v[c]) >>> 24
  v[a] = v[a]+v[b]+y ;  v[d] = (v[d]^v[a]) >>> 16
  v[c] = v[c]+v[d]   ;  v[b] = (v[b]^v[c]) >>> 63
```
Each mutation writes FRESH single-assignment columns (as `sha256Round` does). A round is 8 `G` calls (4
column + 4 diagonal) over a permuted message schedule `SIGMA[r%10]`; the compression `F` folds 12 rounds
then finalizes `h_i ← h_i ^ v_i ^ v_{i+8}` (the reused 3-way XOR). `blake2bInit` folds IV + counter +
final-flag into the initial work vector (the BLAKE2b `v[8..15]`).

## Constraint budget (core value/bit gates)

  * `xorRotWord` (XOR+rotate): 64 XOR gates + 64 out pins + 64 carry pins = **192**.
  * `xor3Word` (finalization): 64 + 64 + 64 = **192**.
  * `addMod64` (k inputs, m carry bits): 1 sum gate + 64 out pins + m carry pins.
  * one `blakeG` CORE (4 add gates + 4·64 XOR gates) = **260** core gates.
  * one round (8 `blakeG`) = **2080**; a full 12-round compression = **24960** core gates; the whole
    `F` (init 768 + compress 24960 + finalize 1536) = **27264**. This is the ACCEPTED zk-STARK cost —
    the point is EXPRESSIBILITY.

## What is AUTHORED + built vs KAT'd vs NAMED continuation

AUTHORED + built: the encoding `wordValue`; `xorRotWord`/`xor3Word`/`addMod64` gadgets; the `G` core
generator `blakeG`; the round generator `blakeRound` (8 `G` over `SIGMA`); the whole-block generator
`blake2bCompress` (the `foldl` of `blakeRound` — the "rounds compose free" realized); `blake2bInit`
(IV/counter/flag fold) and `blake2bFinalize` (the `h ^ v_i ^ v_{i+8}` digest, the candidate authority-set
root); the full `blake2bF`. AUTHORED + KAT'd both-polarity, against real `hashlib.blake2b` vectors: a
`Nat` BLAKE2b reference anchored to `blake2b(b"")` and `blake2b(b"abc")`; the atomic gadgets
(`xorRotWord`/`addMod64`/`xor3Word`) accept the honest witness and reject a flipped output bit; and the
WHOLE `blakeG` mixing function accepts the honest trace of a real first-round `G` (from the `abc`
compression) and rejects a flipped output limb. Forcing lemmas (the "demonstrably computes" content):
`xor2_forces` (parity, via the reused `xorHead_eval`), `finalize_bit_forces` (via the reused
`xor3_forces`), `addMod64_forces` (the mod-2^64 congruence, ℤ reading). NAMED mechanical continuation
(§8): the whole-`F` accept `#guard` (a kernel `#guard` over ~27k gates on a list-backed assignment is
intractable — the atomic + `G` KATs pin the arithmetic and the round/block generators pin the
composition), and the multi-block absorb + root-compare that DERIVES Midnight's `authSetOk`.

## Resolution (honest)

REAL: the `G`/round/compression generators exist + type-check in the deployed IR-v2 vocabulary; the
reference is `hashlib.blake2b`-anchored (both published vectors); the XOR/add gates FORCE their bit
relations (ℤ reading); both-polarity KATs (atomic + whole `G`) are non-vacuous. NOT claimed: a
whole-`F`-accepted `#guard`, a folded `authSetOk`, or native-field (`p_felt`) soundness — the gate is
read over ℤ (the SAME field-width residual `Sha256Gadget` §Resolution and `LightClientEthAir` §6 carry:
a 31-bit BabyBear felt cannot hold a 64-bit word without wrap), and the AUTHSET_OK root-compare is §8's
arc, not built.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/`native_decide`.
The `#guard` KATs reduce in the kernel. NEW file; imports read-only (`Sha256Gadget`, for the reused XOR
gate + KAT harness — the shared bit-gate primitives); standalone (NOT imported by the truncated `Dregg2`
root, built directly as `Dregg2.Circuit.Emit.Blake2bGadget`).
-/
import Dregg2.Circuit.Emit.Sha256Gadget

namespace Dregg2.Circuit.Emit.Blake2bGadget

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2 EffectVmDescriptor2)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.Sha256Gadget (xorHead xorHead_eval xor3_forces acceptB gateBodyEvalZero flipAt)

set_option autoImplicit false

/-! ## §0 — A BLAKE2b reference (Nat words), anchored against the published `hashlib.blake2b` vectors.

Pure `Nat` word arithmetic (kernel-reducible). Used ONLY to (a) anchor itself against the
`blake2b(b"")`/`blake2b(b"abc")` digests and (b) supply the honest witness values the gadget KATs
accept. -/

namespace Ref

/-- `2^64`. -/
def M : Nat := 18446744073709551616
/-- Truncate to 64 bits. -/
def w64 (x : Nat) : Nat := x % M
/-- Rotate-right by `n` (0 < n < 64). -/
def rotr64 (n x : Nat) : Nat := w64 ((x >>> n) ||| (x <<< (64 - n)))
/-- 64-bit bitwise XOR. -/
def xorw (x y : Nat) : Nat := x ^^^ y
/-- 64-bit modular add of two words. -/
def add2 (x y : Nat) : Nat := w64 (x + y)
/-- 64-bit modular add of three words. -/
def add3 (x y z : Nat) : Nat := w64 (x + y + z)
/-- Bit `j` of `x` as a `Nat` (0/1). -/
def bit (x j : Nat) : Nat := (x >>> j) &&& 1
/-- Recompose 64 LSB-first bits (given as a `Nat → Nat` returning 0/1) into a `Nat`. -/
def natOfBits64 (f : Nat → Nat) : Nat := (List.range 64).foldl (fun acc i => acc + f i * 2 ^ i) 0

/-- The 8 initial hash values (BLAKE2b IV = √primes fractional bits, 64-bit — same as SHA-512). -/
def IV : List Nat :=
  [ 0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179 ]

/-- The 10 message-schedule permutations (`SIGMA`); round `r` uses `SIGMA[r % 10]`. -/
def sigma : List (List Nat) :=
  [ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0] ]

/-- The `SIGMA` row for round `r` (already reduced mod 10 by the caller). -/
def sigmaRow (r : Nat) : List Nat := sigma.getD r []

/-- One `G` mixing step on the 16-word work vector `v` at indices `a,b,c,d` with message words `x,y`. -/
def G (v : List Nat) (a b c d x y : Nat) : List Nat :=
  let a1 := add3 (v.getD a 0) (v.getD b 0) x
  let d1 := rotr64 32 (xorw (v.getD d 0) a1)
  let c1 := add2 (v.getD c 0) d1
  let b1 := rotr64 24 (xorw (v.getD b 0) c1)
  let a2 := add3 a1 b1 y
  let d2 := rotr64 16 (xorw d1 a2)
  let c2 := add2 c1 d2
  let b2 := rotr64 63 (xorw b1 c2)
  ((((v.set a a2).set d d2).set c c2).set b b2)

/-- One round: 8 `G` calls (4 column + 4 diagonal) over the schedule `s`. -/
def round (v m s : List Nat) : List Nat :=
  let v := G v 0 4 8 12 (m.getD (s.getD 0 0) 0) (m.getD (s.getD 1 0) 0)
  let v := G v 1 5 9 13 (m.getD (s.getD 2 0) 0) (m.getD (s.getD 3 0) 0)
  let v := G v 2 6 10 14 (m.getD (s.getD 4 0) 0) (m.getD (s.getD 5 0) 0)
  let v := G v 3 7 11 15 (m.getD (s.getD 6 0) 0) (m.getD (s.getD 7 0) 0)
  let v := G v 0 5 10 15 (m.getD (s.getD 8 0) 0) (m.getD (s.getD 9 0) 0)
  let v := G v 1 6 11 12 (m.getD (s.getD 10 0) 0) (m.getD (s.getD 11 0) 0)
  let v := G v 2 7 8 13 (m.getD (s.getD 12 0) 0) (m.getD (s.getD 13 0) 0)
  let v := G v 3 4 9 14 (m.getD (s.getD 14 0) 0) (m.getD (s.getD 15 0) 0)
  v

/-- Compress one 16-word message block into the 8-word state, given the initial state `h`, the counter
`(t0,t1)`, and the final-block flags `(f0,f1)`. -/
def compress (h m : List Nat) (t0 t1 f0 f1 : Nat) : List Nat :=
  let v := h ++ IV
  let v := v.set 12 (xorw (v.getD 12 0) t0)
  let v := v.set 13 (xorw (v.getD 13 0) t1)
  let v := v.set 14 (xorw (v.getD 14 0) f0)
  let v := v.set 15 (xorw (v.getD 15 0) f1)
  let vf := (List.range 12).foldl (fun v r => round v m (sigmaRow (r % 10))) v
  (List.range 8).map (fun i => w64 (xorw (xorw (h.getD i 0) (vf.getD i 0)) (vf.getD (i + 8) 0)))

/-- The default-parameter initial state: `IV` with `IV[0] ^= 0x01010040` (`0x01010000 | (kk<<8) | nn`
for key length `kk=0` and digest size `nn=64`). -/
def h0Default : List Nat := IV.set 0 (xorw (IV.getD 0 0) 0x01010040)

/-- The single-block message `"abc"` (little-endian word load, zero-padded to 128 bytes). -/
def blockAbc : List Nat := 0x636261 :: List.replicate 15 0
/-- The single-block empty message (zero-padded to 128 bytes). -/
def blockEmpty : List Nat := List.replicate 16 0
/-- The final-block flag `f0 = 0xFFFF…FF`. -/
def FF : Nat := 0xFFFFFFFFFFFFFFFF

-- Reference anchor: BLAKE2b("abc") = the `hashlib.blake2b(b"abc").digest()` vector (8 LE words).
#guard compress h0Default blockAbc 3 0 FF 0 ==
  [ 0x0d4d1c983fa580ba, 0xe9f6129fb697276a, 0xb7c45a68142f214c, 0xd1a2ffdb6fbb124b,
    0x2d79ab2a39c5877d, 0x95cc3345ded552c2, 0x5a92f1dba88ad318, 0x239900d4ed8623b9 ]
-- Reference anchor: BLAKE2b("") = the `hashlib.blake2b(b"").digest()` vector (8 LE words).
#guard compress h0Default blockEmpty 0 0 FF 0 ==
  [ 0x03590142f7026a78, 0x72d2522585fdc6c6, 0x614758e140472f91, 0x19541ff717e2868a,
    0x5358eeaf31105ed2, 0x4bb04e9344648913, 0x55b748145b683a90, 0xcee29bfe1a706fd5 ]

end Ref

/-! ## §1 — Word layout in the circuit. A word = 64 boolean columns `base..base+63`, LSB-first. -/

/-- The 64 bit columns of the word at `base`. -/
def wordBits (base : Nat) : List Nat := (List.range 64).map (base + ·)

/-- The value head `Σ_{i<64} 2^i · col(base+i)` (degree 1; no packed-felt column). -/
def wordValue (base : Nat) : Head :=
  (List.range 64).foldl (fun h i => h.addLin (2 ^ i : ℤ) (base + i)) Head.zero

/-- Boolean pins for every bit of the word at `base`. -/
def pinWord (base : Nat) : List VmConstraint2 := (wordBits base).map binGate

/-! ## §2 — The word gadgets: XOR-with-rotate, 3-way XOR, and the mod-2^64 adder. -/

/-- Source bit indices feeding output bit `i` of `(A ^ B) >>> R`: the right-rotation folds into the
XOR's source indexing, so output bit `i` reads bit `(i+R) mod 64` of each input word. -/
def xorRotSources (aBase bBase R i : Nat) : List Nat :=
  [aBase + (i + R) % 64, bBase + (i + R) % 64]

/-- **XOR-and-rotate CORE** — `(A ^ B) >>> R` into `outBase`, per-bit XOR carries at `carBase`. 64
gates (the rotation is free re-indexing). -/
def xorRotCore (aBase bBase outBase carBase R : Nat) : List VmConstraint2 :=
  (List.range 64).map (fun i => cgH (xorHead (xorRotSources aBase bBase R i) (outBase + i) (carBase + i)))

/-- **XOR-and-rotate gadget** — core + output pins + carry pins. 192 constraints. -/
def xorRotWord (aBase bBase outBase carBase R : Nat) : List VmConstraint2 :=
  xorRotCore aBase bBase outBase carBase R
  ++ (wordBits outBase).map binGate
  ++ (wordBits carBase).map binGate

/-- **3-way XOR CORE** — `A ^ B ^ C` into `outBase` (the finalization `h ^ v_i ^ v_{i+8}`), per-bit
carries at `carBase`. 64 gates. -/
def xor3Core (aBase bBase cBase outBase carBase : Nat) : List VmConstraint2 :=
  (List.range 64).map (fun i => cgH (xorHead [aBase + i, bBase + i, cBase + i] (outBase + i) (carBase + i)))

/-- **3-way XOR gadget** — core + output pins + carry pins. 192 constraints. -/
def xor3Word (aBase bBase cBase outBase carBase : Nat) : List VmConstraint2 :=
  xor3Core aBase bBase cBase outBase carBase
  ++ (wordBits outBase).map binGate
  ++ (wordBits carBase).map binGate

/-- The mod-2^64 add head `Σ inputs − wordValue(out) − 2^64·Σ 2^t·carBit_t`. -/
def addMod64Head (ins : List Head) (outBase : Nat) (carBits : List Nat) : Head :=
  let sumIns := ins.foldl Head.append Head.zero
  let h1 := sumIns.append ((wordValue outBase).scale (-1))
  carBits.zipIdx.foldl (fun h (p : Nat × Nat) => h.addLin (-((2 : ℤ) ^ 64 * (2 : ℤ) ^ p.2)) p.1) h1

/-- `addMod64` value gate. -/
def addMod64Core (ins : List Head) (outBase : Nat) (carBits : List Nat) : VmConstraint2 :=
  cgH (addMod64Head ins outBase carBits)

/-- **Modular adder** `out ≡ Σ inputs (mod 2^64)`, output at `outBase`, carry decomposed over
`carBits` (2 bits for ≤ 3 summands, 1 bit for 2 summands). `1 + 64 + |carBits|` constraints. -/
def addMod64 (ins : List Head) (outBase : Nat) (carBits : List Nat) : List VmConstraint2 :=
  addMod64Core ins outBase carBits :: (wordBits outBase).map binGate ++ carBits.map binGate

/-! ## §3 — Forcing lemmas: the emitted gates FORCE the ARX bit relations (ℤ reading). -/

/-- **The 2-way XOR gate forces the parity relation** `out = iA + iB − 2·car` (the exact content of
`iA ⊕ iB` once the columns are the boolean bits the pins force; `car = iA ∧ iB`). Via the reused SHA
`xorHead_eval`. -/
theorem xor2_forces (a : Assignment) (iA iB out car : Nat)
    (hg : evalH (xorHead [iA, iB] out car) a = 0) :
    a out = a iA + a iB - 2 * a car := by
  rw [xorHead_eval] at hg
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hg
  omega

/-- **The finalization 3-way XOR gate forces** `out = h + v_i + v_{i+8} − 2·car` — the reused SHA
`xor3_forces`, applied at the digest-fold bit. -/
theorem finalize_bit_forces (a : Assignment) (h vi vj out car : Nat)
    (hg : evalH (xorHead [h, vi, vj] out car) a = 0) :
    a out = a h + a vi + a vj - 2 * a car :=
  xor3_forces a h vi vj out car hg

/-- Folding `Head.append` over a list sums the head values. -/
theorem evalH_foldl_append (a : Assignment) (hs : List Head) (acc : Head) :
    evalH (hs.foldl Head.append acc) a = evalH acc a + (hs.map (fun h => evalH h a)).sum := by
  induction hs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, evalH_append, List.map_cons, List.sum_cons]; ring

/-- The carry-bit sum factors the `2^64` out (the reduction's carry linearity). -/
theorem addCarry_sum (a : Assignment) (l : List (Nat × Nat)) :
    (l.map (fun p => -((2 : ℤ) ^ 64 * (2 : ℤ) ^ p.2) * a p.1)).sum
      = -(2 : ℤ) ^ 64 * (l.map (fun p => (2 : ℤ) ^ p.2 * a p.1)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- **`addMod64` forces the mod-2^64 congruence** `Σ inputs ≡ out (mod 2^64)`: the gate's zero pins the
reconstructed output word to the truncated sum of the reconstructed inputs. `2^64 ∣ (Σ inputs − out)`.
(The ℤ reading; the mod-`p_felt` ↔ ℤ gap is the shared field-width residual.) -/
theorem addMod64_forces (a : Assignment) (ins : List Head) (outBase : Nat) (carBits : List Nat)
    (hg : evalH (addMod64Head ins outBase carBits) a = 0) :
    (2 : ℤ) ^ 64 ∣ ((ins.map (fun h => evalH h a)).sum - evalH (wordValue outBase) a) := by
  simp only [addMod64Head, evalH_foldl_addLinG, evalH_append, evalH_scale, evalH_foldl_append,
    evalH_zero, zero_add] at hg
  rw [addCarry_sum] at hg
  exact ⟨(carBits.zipIdx.map (fun p => (2 : ℤ) ^ p.2 * a p.1)).sum, by linear_combination hg⟩

#assert_axioms xor2_forces
#assert_axioms finalize_bit_forces
#assert_axioms evalH_foldl_append
#assert_axioms addCarry_sum
#assert_axioms addMod64_forces

/-! ## §4 — The `G` + round + block generators (the parameterized fold — the KEY deliverable). -/

/-- **`blakeG`** — one `G` mixing step as GENERATED core constraints, given the four work-vector word
bases `va,vb,vc,vd`, the message-word bases `mx,my`, and the next free column `fresh`. Returns
`(constraints, (newA, newB, newC, newD), next free column)`. Each of the 8 sub-steps writes a FRESH
single-assignment word (the layout `let`s below); the 4-add/4-XOR-rotate structure is the whole ARX
core. 260 core gates (4 add value gates + 4·64 XOR gates); the boolean pins are the per-column `pinWord`
sweep (demonstrated atomically by `xorRotWord`/`addMod64`/`xor3Word` in §5). -/
def blakeG (va vb vc vd mx my fresh : Nat) : List VmConstraint2 × (Nat × Nat × Nat × Nat) × Nat :=
  let a1  := fresh;        let ca1 := a1  + 64   -- v[a] = v[a]+v[b]+x : out + 2 carry bits
  let d1  := ca1 + 2;      let cd1 := d1  + 64   -- v[d] = (v[d]^v[a1]) >>> 32
  let c1  := cd1 + 64;     let cc1 := c1  + 64   -- v[c] = v[c]+v[d1] : out + 1 carry bit
  let b1  := cc1 + 1;      let cb1 := b1  + 64   -- v[b] = (v[b]^v[c1]) >>> 24
  let a2  := cb1 + 64;     let ca2 := a2  + 64   -- v[a1] = v[a1]+v[b1]+y : out + 2 carry bits
  let d2  := ca2 + 2;      let cd2 := d2  + 64   -- v[d1] = (v[d1]^v[a2]) >>> 16
  let c2  := cd2 + 64;     let cc2 := c2  + 64   -- v[c1] = v[c1]+v[d2] : out + 1 carry bit
  let b2  := cc2 + 1;      let cb2 := b2  + 64   -- v[b1] = (v[b1]^v[c2]) >>> 63
  let next := cb2 + 64
  let cs : List VmConstraint2 :=
       [addMod64Core [wordValue va, wordValue vb, wordValue mx] a1 [ca1, ca1 + 1]]
    ++ xorRotCore vd a1 d1 cd1 32
    ++ [addMod64Core [wordValue vc, wordValue d1] c1 [cc1]]
    ++ xorRotCore vb c1 b1 cb1 24
    ++ [addMod64Core [wordValue a1, wordValue b1, wordValue my] a2 [ca2, ca2 + 1]]
    ++ xorRotCore d1 a2 d2 cd2 16
    ++ [addMod64Core [wordValue c1, wordValue d2] c2 [cc2]]
    ++ xorRotCore b1 c2 b2 cb2 63
  (cs, (a2, b2, c2, d2), next)

/-- Apply one `G` to the work-vector layout `v` (a list of 16 word bases), updating indices `a,b,c,d`
with the fresh output words. -/
def gStep (v : List Nat) (a b c d mx my fresh : Nat) : List VmConstraint2 × List Nat × Nat :=
  let (cs, tup, fr) := blakeG (v.getD a 0) (v.getD b 0) (v.getD c 0) (v.getD d 0) mx my fresh
  let (na, nb, nc, nd) := tup
  (cs, ((((v.set a na).set b nb).set c nc).set d nd), fr)

/-- The 8 `G` calls of a round: the `(a,b,c,d)` word quartet + the `(sx,sy)` indices into the `SIGMA`
row that select the two message words. -/
def gargs : List ((Nat × Nat × Nat × Nat) × (Nat × Nat)) :=
  [ ((0, 4, 8, 12), (0, 1)), ((1, 5, 9, 13), (2, 3)), ((2, 6, 10, 14), (4, 5)), ((3, 7, 11, 15), (6, 7)),
    ((0, 5, 10, 15), (8, 9)), ((1, 6, 11, 12), (10, 11)), ((2, 7, 8, 13), (12, 13)),
    ((3, 4, 9, 14), (14, 15)) ]

/-- **`blakeRound`** — one round as GENERATED constraints: the 8 `G` calls over the schedule `sig`,
threading the work-vector layout and the free column. `8·260 = 2080` core gates. -/
def blakeRound (vInit mBases sig : List Nat) (fresh : Nat) : List VmConstraint2 × List Nat × Nat :=
  gargs.foldl (fun (acc : List VmConstraint2 × List Nat × Nat) g =>
    let (cs, v, fr) := acc
    let ((a, b, c, d), (sx, sy)) := g
    let mx := mBases.getD (sig.getD sx 0) 0
    let my := mBases.getD (sig.getD sy 0) 0
    let (cs', v', fr') := gStep v a b c d mx my fr
    (cs ++ cs', v', fr')) ([], vInit, fresh)

/-- **`blake2bCompress`** — the whole 12-round compression as ONE generated constraint list: the 12
rounds are the FREE `List.foldl` of `blakeRound` over `SIGMA[r%10]`. This is the "generator makes them
free" claim, realized. Returns `(constraints, final work vector, next free column)`. (Not `#guard`-
accepted whole — see §8.) -/
def blake2bCompress (mBases vInit : List Nat) (fresh : Nat) : List VmConstraint2 × List Nat × Nat :=
  (List.range 12).foldl (fun (acc : List VmConstraint2 × List Nat × Nat) r =>
    let (cs, v, fr) := acc
    let (cs', v', fr') := blakeRound v mBases (Ref.sigmaRow (r % 10)) fr
    (cs ++ cs', v', fr')) ([], vInit, fresh)

/-- A word pinned to the public constant `k`, bit by bit (`col(base+i) = bit(k,i)`). Used for the IV
words `v[8..11]`. 64 gates. -/
def constWordGate (base k : Nat) : List VmConstraint2 :=
  (List.range 64).map (fun i => cgH ((Head.lin 1 (base + i)).addConst (-(Ref.bit k i : ℤ))))

/-- A word XOR'd with a public constant `k` (`out = in ^ k`): per bit, a constant bit `kb` gives
`(1−2·kb)·in − out + kb = 0` (`kb=0 ⇒ out=in`; `kb=1 ⇒ out=1−in`) — NO carry (one operand constant).
Plus output pins. Used for `v[12..15] = (counter/flag) ^ IV[4..7]`. 128 gates. -/
def xorConstWord (inBase outBase k : Nat) : List VmConstraint2 :=
  (List.range 64).map (fun i =>
    cgH (((Head.lin (1 - 2 * (Ref.bit k i : ℤ)) (inBase + i)).addLin (-1) (outBase + i)).addConst
      (Ref.bit k i : ℤ)))
  ++ (wordBits outBase).map binGate

/-- **`blake2bInit`** — fold the IV, counter `(t0,t1)`, and final-flag `(f0,f1)` into the initial
16-word work vector: `v[0..7] = h` (relabel), `v[8..11] = IV[0..3]` (constant), `v[12..15] =
(t0,t1,f0,f1) ^ IV[4..7]`. Returns `(constraints, the 16 work-vector bases, next free column)`.
`4·64 + 4·128 = 768` gates. -/
def blake2bInit (hBases : List Nat) (t0B t1B f0B f1B fresh : Nat) :
    List VmConstraint2 × List Nat × Nat :=
  let v8  := fresh;        let v9  := fresh + 64
  let v10 := fresh + 128;  let v11 := fresh + 192
  let v12 := fresh + 256;  let v13 := fresh + 320
  let v14 := fresh + 384;  let v15 := fresh + 448
  let next := fresh + 512
  let cs : List VmConstraint2 :=
       constWordGate v8 (Ref.IV.getD 0 0)  ++ constWordGate v9 (Ref.IV.getD 1 0)
    ++ constWordGate v10 (Ref.IV.getD 2 0) ++ constWordGate v11 (Ref.IV.getD 3 0)
    ++ xorConstWord t0B v12 (Ref.IV.getD 4 0) ++ xorConstWord t1B v13 (Ref.IV.getD 5 0)
    ++ xorConstWord f0B v14 (Ref.IV.getD 6 0) ++ xorConstWord f1B v15 (Ref.IV.getD 7 0)
  let vBases : List Nat :=
    [hBases.getD 0 0, hBases.getD 1 0, hBases.getD 2 0, hBases.getD 3 0,
     hBases.getD 4 0, hBases.getD 5 0, hBases.getD 6 0, hBases.getD 7 0,
     v8, v9, v10, v11, v12, v13, v14, v15]
  (cs, vBases, next)

/-- **`blake2bFinalize`** — the digest fold `out_i = h_i ^ v_i ^ v_{i+8}` (`i<8`), the reused 3-way XOR.
The 8 output words ARE the BLAKE2b digest (the candidate authority-set root feeding `authSetOk`, §8).
`8·192 = 1536` gates. -/
def blake2bFinalize (hBases vFinal outBases : List Nat) (fresh : Nat) : List VmConstraint2 × Nat :=
  (List.range 8).foldl (fun (acc : List VmConstraint2 × Nat) i =>
    let (cs, fr) := acc
    let cs' := xor3Word (hBases.getD i 0) (vFinal.getD i 0) (vFinal.getD (i + 8) 0) (outBases.getD i 0) fr
    (cs ++ cs', fr + 64)) ([], fresh)

/-- **`blake2bF`** — the whole BLAKE2b compression `F`: init ⊕ 12 rounds ⊕ finalize. `768 + 24960 +
1536 = 27264` gates.

⚠ The three stages are bound by PROJECTION (`i.2.1`), not by pattern-destructuring
(`let (cs1, vFinal, fr1) := …`). That is load-bearing, not style: `blake2bCompress`'s body head is a
`List.foldl`, so destructuring it forces `whnf` to DRIVE the whole 24960-gate fold, and any lemma
relating `(blake2bF …).1` to its three segments then dies at the `isDefEq` heartbeat wall (measured
2026-07-27). With projections the segments fall out by zeta + iota and
`Blake2bFoldForcing.blake2bF_split` is `rfl` for free — which is what lets `blake2bF_forces` consume
gate ACCEPTANCE instead of assuming its stages. -/
def blake2bF (hBases mBases : List Nat) (t0B t1B f0B f1B : Nat) (outBases : List Nat) (fresh : Nat) :
    List VmConstraint2 × Nat :=
  let i := blake2bInit hBases t0B t1B f0B f1B fresh
  let c := blake2bCompress mBases i.2.1 i.2.2
  let f := blake2bFinalize hBases c.2.1 outBases c.2.2
  (i.1 ++ c.1 ++ f.1, f.2)

/-! ## §5 — KAT: the GENERATED constraints ACCEPT the reference's honest values and REJECT tamper.

`acceptB` (reused from `Sha256Gadget`) is the ℤ reading of the emitted gate bodies: every `.base (.gate
e)` has `e.eval a = 0`. Anchored to §0's `hashlib.blake2b`-validated reference. -/

/-- Bit `j` of `x` as a felt column value. -/
def bZ (x j : Nat) : ℤ := (Ref.bit x j : Nat)

/-- The output word of `(A ^ B) >>> R` (the honest `xorRotWord` output). -/
def xrOut (A B R : Nat) : Nat := Ref.rotr64 R (Ref.xorw A B)

/-- The honest per-bit XOR carry of `(A ^ B) >>> R` at output bit `i`: `bit A ((i+R)%64) ∧ bit B ((i+R)
%64)`. -/
def xrCarBit (A B R i : Nat) : ℤ := ((Ref.bit A ((i + R) % 64)) * (Ref.bit B ((i + R) % 64)) : Nat)

/-- The honest per-bit 3-way XOR carry (majority-count bit) of `A ^ B ^ C` at bit `i`. -/
def xor3Car (A B C i : Nat) : ℤ := (((Ref.bit A i + Ref.bit B i + Ref.bit C i) / 2 : Nat) : ℤ)

/-! ### `addMod64` — 3-input adder. Layout x=0, y=64, z=128, out=192, carry 256/257. Carry-exercising
case `(2^64−1)+(2^64−1)+(2^64−1)` (carry = 2, both bits set). -/

/-- Honest 3-input `addMod64` witness. -/
def add3Asg (Xv Yv Zv : Nat) : Assignment := fun col =>
  let O := Ref.w64 (Xv + Yv + Zv)
  let C := (Xv + Yv + Zv) / Ref.M
  if col < 64 then bZ Xv col
  else if col < 128 then bZ Yv (col - 64)
  else if col < 192 then bZ Zv (col - 128)
  else if col < 256 then bZ O (col - 192)
  else if col < 258 then (Ref.bit C (col - 256) : ℤ)
  else 0

def addGadget : List VmConstraint2 := addMod64 [wordValue 0, wordValue 64, wordValue 128] 192 [256, 257]

#guard acceptB addGadget (add3Asg (Ref.M - 1) (Ref.M - 1) (Ref.M - 1)) == true
#guard acceptB addGadget (flipAt (add3Asg (Ref.M - 1) (Ref.M - 1) (Ref.M - 1)) 192) == false  -- out bit 0
#guard Ref.natOfBits64 (fun i => Ref.bit (Ref.w64 (Ref.M - 1 + (Ref.M - 1) + (Ref.M - 1))) i)
  == Ref.w64 (Ref.M - 1 + (Ref.M - 1) + (Ref.M - 1))

/-! ### `xorRotWord` — `(A ^ B) >>> 32` on real IV words. Layout a=0, b=64, out=128, car=192. -/

/-- Honest `xorRotWord` witness. -/
def xorRotAsg (Av Bv R : Nat) : Assignment := fun col =>
  if col < 64 then bZ Av col
  else if col < 128 then bZ Bv (col - 64)
  else if col < 192 then bZ (xrOut Av Bv R) (col - 128)
  else if col < 256 then xrCarBit Av Bv R (col - 192)
  else 0

def xorRotGadget : List VmConstraint2 := xorRotWord 0 64 128 192 32

#guard acceptB xorRotGadget (xorRotAsg (Ref.IV.getD 0 0) (Ref.IV.getD 1 0) 32) == true
#guard acceptB xorRotGadget (flipAt (xorRotAsg (Ref.IV.getD 0 0) (Ref.IV.getD 1 0) 32) 128) == false
#guard Ref.natOfBits64 (fun i => Ref.bit (xrOut (Ref.IV.getD 0 0) (Ref.IV.getD 1 0) 32) i)
  == xrOut (Ref.IV.getD 0 0) (Ref.IV.getD 1 0) 32   -- gate output word ties to the reference rotation

/-! ### `xor3Word` — the finalization `A ^ B ^ C` on real IV words. Layout a=0, b=64, c=128, out=192,
car=256. -/

/-- Honest `xor3Word` witness. -/
def xor3Asg (Av Bv Cv : Nat) : Assignment := fun col =>
  if col < 64 then bZ Av col
  else if col < 128 then bZ Bv (col - 64)
  else if col < 192 then bZ Cv (col - 128)
  else if col < 256 then bZ (Ref.xorw (Ref.xorw Av Bv) Cv) (col - 192)
  else if col < 320 then xor3Car Av Bv Cv (col - 256)
  else 0

def xor3Gadget : List VmConstraint2 := xor3Word 0 64 128 192 256

#guard acceptB xor3Gadget (xor3Asg (Ref.IV.getD 0 0) (Ref.IV.getD 1 0) (Ref.IV.getD 2 0)) == true
#guard acceptB xor3Gadget (flipAt (xor3Asg (Ref.IV.getD 0 0) (Ref.IV.getD 1 0) (Ref.IV.getD 2 0)) 192)
  == false

/-! ### The WHOLE `G` mixing function — accepts the honest trace of a REAL first-round `G` (from the
`abc` compression) and rejects a flipped output limb. Inputs `va,vb,vc,vd` at `0/64/128/192`, message
words `mx,my` at `256/320`, scratch from `384`. -/

-- The first `G(v,0,4,8,12, m[0], m[1])` of round 0 of the BLAKE2b("abc") compression (from §0's Ref /
-- hashlib.blake2b): the work-vector words `v[0],v[4],v[8],v[12]` after the counter/flag fold, and
-- `m[0]=0x636261, m[1]=0`.
def gVa : Nat := 0x6a09e667f2bdc948
def gVb : Nat := 0x510e527fade682d1
def gVc : Nat := 0x6a09e667f3bcc908
def gVd : Nat := 0x510e527fade682d2
def gMx : Nat := 0x636261
def gMy : Nat := 0

/-- Honest full `blakeG` trace witness for `G(va,vb,vc,vd, mx,my)`, layout matching `blakeG _ _ _ _ _ _
384` (every intermediate word / add-carry / XOR-carry the 260 core gates reference). -/
def gAsg (vaV vbV vcV vdV mxV myV : Nat) : Assignment := fun col =>
  let a1V := Ref.add3 vaV vbV mxV
  let d1V := xrOut vdV a1V 32
  let c1V := Ref.add2 vcV d1V
  let b1V := xrOut vbV c1V 24
  let a2V := Ref.add3 a1V b1V myV
  let d2V := xrOut d1V a2V 16
  let c2V := Ref.add2 c1V d2V
  let b2V := xrOut b1V c2V 63
  if col < 64 then bZ vaV col
  else if col < 128 then bZ vbV (col - 64)
  else if col < 192 then bZ vcV (col - 128)
  else if col < 256 then bZ vdV (col - 192)
  else if col < 320 then bZ mxV (col - 256)
  else if col < 384 then bZ myV (col - 320)
  else if col < 448 then bZ a1V (col - 384)
  else if col < 450 then (Ref.bit ((vaV + vbV + mxV) / Ref.M) (col - 448) : ℤ)
  else if col < 514 then bZ d1V (col - 450)
  else if col < 578 then xrCarBit vdV a1V 32 (col - 514)
  else if col < 642 then bZ c1V (col - 578)
  else if col < 643 then (Ref.bit ((vcV + d1V) / Ref.M) (col - 642) : ℤ)
  else if col < 707 then bZ b1V (col - 643)
  else if col < 771 then xrCarBit vbV c1V 24 (col - 707)
  else if col < 835 then bZ a2V (col - 771)
  else if col < 837 then (Ref.bit ((a1V + b1V + myV) / Ref.M) (col - 835) : ℤ)
  else if col < 901 then bZ d2V (col - 837)
  else if col < 965 then xrCarBit d1V a2V 16 (col - 901)
  else if col < 1029 then bZ c2V (col - 965)
  else if col < 1030 then (Ref.bit ((c1V + d2V) / Ref.M) (col - 1029) : ℤ)
  else if col < 1094 then bZ b2V (col - 1030)
  else if col < 1158 then xrCarBit b1V c2V 63 (col - 1094)
  else 0

-- THE G GADGET ACCEPTS THE HONEST TRACE of the real abc-round-0 G.
#guard acceptB (blakeG 0 64 128 192 256 320 384).1 (gAsg gVa gVb gVc gVd gMx gMy) == true
-- AND REJECTS A FLIPPED OUTPUT LIMB (a2 = new v[a], bit 0 at column 771).
#guard acceptB (blakeG 0 64 128 192 256 320 384).1 (flipAt (gAsg gVa gVb gVc gVd gMx gMy) 771) == false

/-! ## §6 — Structural `#guard`s: the generators produce the budgeted shapes; AIR packaging. -/

#guard (xorRotWord 0 64 128 192 32).length == 192
#guard (xor3Word 0 64 128 192 256).length == 192
#guard (addMod64 [wordValue 0, wordValue 64, wordValue 128] 192 [256, 257]).length == 67
#guard (addMod64 [wordValue 0, wordValue 64] 128 [192]).length == 66
#guard (blakeG 0 64 128 192 256 320 384).1.length == 260
#guard (blakeRound (List.range 16) (List.range 16) (Ref.sigmaRow 0) 10000).1.length == 2080
#guard (blake2bCompress (List.range 16) (List.range 16) 10000).1.length == 24960
#guard (blake2bInit (List.range 8) 100 101 102 103 10000).1.length == 768
#guard (blake2bFinalize (List.range 8) (List.range 16) (List.range 8) 10000).1.length == 1536
#guard (blake2bF (List.range 8) (List.range 16) 100 101 102 103 (List.range 8) 20000).1.length == 27264

/-- A single `blakeG` core packaged as an `EffectVmDescriptor2` (the AIR type the light-client emits),
showing the generator drops straight into the deployed descriptor vocabulary. -/
def gDesc : EffectVmDescriptor2 :=
  { name        := "dregg-blake2b-g::demo"
  , traceWidth  := 1158
  , piCount     := 0
  , tables      := []
  , constraints := (blakeG 0 64 128 192 256 320 384).1
  , hashSites   := []
  , ranges      := [] }

#guard gDesc.constraints.length == 260
#guard gDesc.traceWidth == 1158

/-! ## §7 — Axiom hygiene (CI hard-gate). The forcing lemmas are pinned kernel-clean; the KAT `#guard`s
reduce in the kernel (no `native_decide`). -/

#print axioms addMod64_forces
#print axioms xor2_forces
#print axioms finalize_bit_forces

/-! ## §8 — The PRECISE named continuation to a folded `authSetOk` (mechanical, NOT free).

The generators make each step mechanical; none of §8 is claimed built. In order:

  1. **The whole-`F` accept `#guard`** — NOT run. A kernel `#guard` of `acceptB (blake2bF …) witness` over
     ~27k gates on a list-backed `Assignment` is intractable (the same reason `sha256Compress`'s whole
     block is not `#guard`-accepted). The atomic KATs (`addMod64`/`xorRotWord`/`xor3Word`) pin the
     arithmetic both polarities, the WHOLE-`G` KAT pins the ARX mixing both polarities, and the
     round/block generators (`blakeRound`/`blake2bCompress`) pin the composition structurally
     (`length` guards); the `Nat` reference is `hashlib.blake2b`-anchored on the published vectors, so
     `blake2bF`'s honest witness is validated transitively.

  2. **Multi-block absorb** — the authority-set commitment `authSetCommit (authSet.map authRow)` hashes
     the domain-separated serialization of the sorted `(authorityId, weight)` rows, which for a real
     authority set spans MANY 128-byte blocks. BLAKE2b absorbs them by chaining `blake2bF`: the digest
     state `h` of block `k` (its 8 output words) is the `hBases` input of block `k+1`, with the counter
     `t` = total bytes absorbed and the final-flag set ONLY on the last block. This is a `foldl` of
     `blake2bF` over the message blocks — the SAME "generator makes them free" pattern as the 12 rounds,
     one level up. Each block is `27264` gates; a `b`-block authority set is `≈ 27264·b` gates.

  3. **The root-compare (the `authSetOk` rewrite)** — the final 8-word digest (the `blake2bFinalize`
     output) is the reconstructed authority-set ROOT. `authSetOk` is `L.dBeq (authSetCommit …)
     anchorRoot`; in-circuit it becomes a coordinate-wise equality gate `digest_i − pi(anchorRoot)_i =
     0` for each of the 8 words (an `AirBuilder.pinPi` binding of the anchor root's words + a
     `wordValue`-difference gate per word). That boolean IS the `authSetOk` carrier, DERIVED — dropping
     the trusted bit, exactly as the ETH `FIN_OK` Merkle-branch fold + root PI-binding drops `FIN_OK`.
     `mid_no_forgery`'s `anchorBinds` leg (`authSetCommit (authSet.map authRow) = anchorRoot`) is then
     discharged BY the in-circuit derivation instead of asserted as `authSetOk`.

**Gate-count reality (order of magnitude).** One `blakeG` is `260` core gates (with pins ≈ `1034`); one
`F` is `27264` core gates; a multi-block authority-set root is `≈ 27264·b` for `b` blocks — hundreds of
thousands of AIR gates, the accepted zk-STARK hashing cost (the reason `authSetOk` is a trusted carrier
today, and the reason the point of THIS slice is EXPRESSIBILITY: the ARX core is generated + KAT'd +
forced, so each step above is COMPOSITION over these generators, not new constraint algebra). None of §8
is claimed built; this file is the BLAKE2b compression gadget it stands on.
-/

end Dregg2.Circuit.Emit.Blake2bGadget
