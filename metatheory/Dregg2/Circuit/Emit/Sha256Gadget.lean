/-
# Dregg2.Circuit.Emit.Sha256Gadget — a Lean-GENERATED SHA-256 AIR gadget (the first crypto fold).

## Why this file exists (the carrier it is aimed at)

The four light-client AIRs (`LightClient{Eth,Tendermint,Solana,Midnight}Air`) prove the consensus
LOGIC given crypto results asserted as witnessed boolean CARRIERS. `LightClientEthAir` draws the line
explicitly: `FIN_OK` / `EXEC_OK` are carrier bits standing for a **SHA-256 Merkle-branch
reconstruction compare** (a fold of `sha256(left ‖ right)` up a branch into an attested root), and the
AIR forces them `= 1` for accept without re-deriving the hash in-circuit. That is correct for
VALIDATOR mode (the node runs the native SHA). For FULL-LIGHT-VIA-PROOF mode the carrier must be
REPLACED by an in-circuit SHA-256 derivation so the STARK stands alone. This file is the SHA-256
half of that replacement: the constraint algebra `FIN_OK` would be derived FROM.

## The metaprogramming approach (how the gadget is GENERATED, not hand-written)

Everything here is produced by Lean `def`-GENERATORS over parameters — the same idiom the tree already
uses for `AirBuilder.rangeNonneg`/`forcedGe0` and `MerkleEmit.merklePathData d`, and the tier below
`ArithmetizeTypedPredicate`'s `#arithmetizeTypedPredicate` elaborator. A generator maps a small
parameter (a rotation/shift triple, a round index `t`, an 8-word state layout) to a
`List VmConstraint2` in the deployed IR-v2 vocabulary. Instantiating the full 64-round compression is
then a `List.foldl` of `sha256Round` — the 64 rounds are FREE once the round generator exists; nothing
is authored per-round or per-instance.

Every constraint is a per-row gate `.base (.gate (headToExpr h))` built from `AirBuilder.Head`
(`Σ coeff·∏cols + const`), so it reuses `AirBuilder.headToExpr_eval` — the emitted gate polynomial
evaluates to exactly the head value, and the deployed AIR reads it as the SAME `body ≡ 0 [ZMOD p]`
tooth every other emitted gate carries.

## The felt-encoding

A 32-bit word occupies **32 boolean columns** `base .. base+31`, LSB-first, each pinned by the
`x·(x−1)=0` `binGate`. Its "value" is the degree-1 head `Σ_{i<32} 2^i · col(base+i)` (`wordValue`);
no separate packed-felt column is needed. Consequences:

  * ROTR^n / SHR^n are FREE — pure re-indexing of which bit column feeds the next gate (`sigmaSources`).
  * XOR / AND / NOT are LOCAL bit gates (below).
  * mod-2^32 addition is one linear gate over the input value-heads plus an explicit carry
    (`addMod32`): `Σ inputs − Σ 2^i·out_i − 2^32·carry = 0`, carry range-bounded by its own bits.

The bit gates:

  * 3-way XOR (the Σ/σ cores): output bit `s` + carry `c`, gate `iA+iB+iC = s + 2c` — over booleans
    `s` is the parity `iA⊕iB⊕iC` and `c` the majority. Degree 1. (2-way falls out when SHR drops a term.)
  * `Ch(e,f,g)` bit: `out = e·f + (1−e)·g` — the two AND terms are mutually exclusive, so no XOR
    carry is needed. Degree 2.
  * `Maj(a,b,c)` bit: `out = ab + bc + ca − 2abc`. Degree 3.

## Constraint budget

Per 32-bit word: 32 booleanity pins. Per gadget instance:

  * `sigmaWord` (Σ0/Σ1/σ0/σ1): 32 XOR gates + 32 out-bit pins + 32 carry-bit pins = **96**.
  * `chWord`/`majWord`: 32 op gates + 32 out-bit pins = **64**.
  * `addMod32` (k inputs, 3 carry bits): 1 sum gate + 32 out-bit pins + 3 carry pins = **36**.
  * one `sha256Round` (Σ1 + Ch + T1 + Σ0 + Maj + T2 + newE + newA) = 96+64+36+96+64+36+36+36 = **464**.
  * one full 64-round compression ≈ **29 700** gate constraints (the message schedule adds ~48 words ×
    ~230 each ≈ 11 000). This is the ACCEPTED zk-STARK cost — the point is EXPRESSIBILITY.

## What is authored vs named-mechanical-continuation

AUTHORED + built: the bit gates, `sigmaWord`/`chWord`/`majWord`/`addMod32`, the round generator
`sha256Round`, the schedule-word generator `scheduleWord`, and the whole-block generator
`sha256Compress` (the `foldl` of `sha256Round`). AUTHORED + KAT'd both-polarity below: σ0, Σ0, Ch,
Maj, addMod32 on real SHA-256 constants. NAMED mechanical continuation: the full-block ACCEPT `#guard`
is not run — a kernel `#guard` over ~30k gates on a list-backed assignment is intractable; the atomic
gadget KATs pin the arithmetic and the round/block generators pin the composition.

## Resolution (honest)

A KAT'd GENERATOR is a real start; it is NOT a full refinement and NOT an end-to-end in-AIR SHA-256
replacing `FIN_OK`. Specifically:
  * The KAT shows the GENERATED constraints accept exactly the (digest-anchored) reference's
    intermediate values and reject a tampered bit — i.e. the gadget COMPUTES SHA-256 arithmetic, both
    polarities, non-vacuously. The digest KATs (`abc`, empty) anchor the reference itself against the
    published FIPS-180-4 vectors.
  * The deployed gate denotation is `body ≡ 0 [ZMOD 2013265921]`; the KAT checks the stronger ℤ
    reading `body = 0`. The mod-p ↔ ℤ gap is the SAME field-soundness residual `LightClientEthAir` §6
    already carries (a 31-bit prime cannot hold a 32-bit word without wrap) — closing it needs the
    bit-decomposition to be the sole reading, which this encoding is BUILT for but does not yet prove.
  * Wiring `sha256Compress`'s output word bits to a Merkle-branch fold and PI-binding the resulting
    root — the shape that lets a verifier drop `FIN_OK` — is the next slice.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/`native_decide`.
The `#guard` KATs reduce in the kernel. NEW file; imports read-only (`AirBuilder`).
-/
import Dregg2.Circuit.Emit.AirBuilder

namespace Dregg2.Circuit.Emit.Sha256Gadget

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2 EffectVmDescriptor2)
open Dregg2.Circuit.Emit.AirBuilder

set_option autoImplicit false

/-! ## §0 — A SHA-256 reference (Nat words), anchored against the published FIPS-180-4 vectors.

Pure `Nat` word arithmetic (kernel-reducible). Used ONLY to (a) anchor itself against the published
`abc`/empty digests and (b) supply the honest witness values the gadget KATs accept. -/

namespace Ref

/-- `2^32`. -/
def M : Nat := 4294967296
/-- Truncate to 32 bits. -/
def w32 (x : Nat) : Nat := x % M
/-- Rotate-right by `n` (n < 32). -/
def rotr (n x : Nat) : Nat := w32 ((x >>> n) ||| (x <<< (32 - n)))
/-- Shift-right by `n`. -/
def shr (n x : Nat) : Nat := x >>> n
/-- 32-bit modular add. -/
def add2 (x y : Nat) : Nat := w32 (x + y)
/-- 32-bit bitwise NOT. -/
def notw (x : Nat) : Nat := w32 (4294967295 ^^^ x)

/-- `σ0` (message schedule). -/
def s0 (x : Nat) : Nat := (rotr 7 x) ^^^ (rotr 18 x) ^^^ (shr 3 x)
/-- `σ1` (message schedule). -/
def s1 (x : Nat) : Nat := (rotr 17 x) ^^^ (rotr 19 x) ^^^ (shr 10 x)
/-- `Σ0` (compression). -/
def bS0 (x : Nat) : Nat := (rotr 2 x) ^^^ (rotr 13 x) ^^^ (rotr 22 x)
/-- `Σ1` (compression). -/
def bS1 (x : Nat) : Nat := (rotr 6 x) ^^^ (rotr 11 x) ^^^ (rotr 25 x)
/-- `Ch(e,f,g)`. -/
def chf (x y z : Nat) : Nat := (x &&& y) ^^^ (notw x &&& z)
/-- `Maj(a,b,c)`. -/
def majf (x y z : Nat) : Nat := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- The 64 round constants. -/
def K : List Nat :=
  [ 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 ]

/-- The 8 initial hash values (√primes fractional bits). -/
def IV : List Nat :=
  [ 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]

/-- Expand a 16-word block into the 64-word message schedule. -/
def schedule (w0 : List Nat) : List Nat :=
  (List.range 48).foldl (fun w _ =>
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

/-- Compress one 16-word block from an ARBITRARY chaining value → 8 words. This is the
Merkle–Damgård compression function; `compress` is it at the IV, and a multi-block message folds it
over the blocks. -/
def compressFrom (iv : List Nat) (block : List Nat) : List Nat :=
  let w := schedule block
  let init : Hst :=
    { a := iv.getD 0 0, b := iv.getD 1 0, c := iv.getD 2 0, d := iv.getD 3 0,
      e := iv.getD 4 0, f := iv.getD 5 0, g := iv.getD 6 0, h := iv.getD 7 0 }
  let fin := (List.range 64).foldl (fun hs t => round hs (K.getD t 0) (w.getD t 0)) init
  [ add2 (iv.getD 0 0) fin.a, add2 (iv.getD 1 0) fin.b, add2 (iv.getD 2 0) fin.c,
    add2 (iv.getD 3 0) fin.d, add2 (iv.getD 4 0) fin.e, add2 (iv.getD 5 0) fin.f,
    add2 (iv.getD 6 0) fin.g, add2 (iv.getD 7 0) fin.h ]

/-- Compress one 16-word block from the IV → 8 digest words. -/
def compress (block : List Nat) : List Nat := compressFrom IV block

/-- Single-block message `"abc"` (0x61 0x62 0x63 ‖ 0x80 ‖ 0…0 ‖ len=24). -/
def blockAbc : List Nat := [0x61626380] ++ List.replicate 14 0 ++ [0x18]
/-- Single-block empty message (0x80 ‖ 0…0 ‖ len=0). -/
def blockEmpty : List Nat := [0x80000000] ++ List.replicate 15 0

-- Reference anchor: SHA-256("abc") = the published FIPS-180-4 vector.
#guard compress blockAbc ==
  [0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223, 0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad]
-- Reference anchor: SHA-256("") = the published FIPS-180-4 vector.
#guard compress blockEmpty ==
  [0xe3b0c442, 0x98fc1c14, 0x9afbf4c8, 0x996fb924, 0x27ae41e4, 0x649b934c, 0xa495991b, 0x7852b855]

/-- Bit `j` of `x` as a `Nat` (0/1). -/
def bit (x j : Nat) : Nat := (x >>> j) &&& 1
/-- Recompose 32 LSB-first bits (given as a `Nat → Nat` returning 0/1) into a `Nat`. -/
def natOfBits32 (f : Nat → Nat) : Nat := (List.range 32).foldl (fun acc i => acc + f i * 2^i) 0

end Ref

/-! ## §1 — Word layout in the circuit. A word = 32 boolean columns `base..base+31`, LSB-first. -/

/-- The 32 bit columns of the word at `base`. -/
def wordBits (base : Nat) : List Nat := (List.range 32).map (base + ·)

/-- The value head `Σ_{i<32} 2^i · col(base+i)` (degree 1; no packed-felt column). -/
def wordValue (base : Nat) : Head :=
  (List.range 32).foldl (fun h i => h.addLin (2^i : ℤ) (base+i)) Head.zero

/-- Boolean pins for every bit of the word at `base`. -/
def pinWord (base : Nat) : List VmConstraint2 := (wordBits base).map binGate

/-! ## §2 — The bit gates (GENERATED per bit position by the word gadgets in §3). -/

/-- The XOR head `Σ_{c∈ins} col(c) − out − 2·car` (its zero forces `out = ⊕ ins`, `car = maj`). -/
def xorHead (ins : List Nat) (out car : Nat) : Head :=
  ((ins.foldl (fun h c => h.addLin 1 c) Head.zero).addLin (-1) out).addLin (-2) car

/-- The `Ch` head `out − e·f − g + e·g` (zero forces `out = e·f + (1−e)·g`). -/
def chHead (e f g out : Nat) : Head :=
  (((Head.lin 1 out).addProd (-1) [e, f]).addLin (-1) g).addProd 1 [e, g]

/-- The `Maj` head `out − a·b − b·c − c·a + 2·a·b·c`. -/
def majHead (a b c out : Nat) : Head :=
  ((((Head.lin 1 out).addProd (-1) [a, b]).addProd (-1) [b, c]).addProd (-1) [c, a]).addProd 2 [a, b, c]

/-! ## §3 — The word gadgets: `def`-generators that FOLD a bit gate over the 32 positions. -/

/-- Source bit indices (within a 32-bit word) feeding output bit `i` of a Σ/σ function
`ROTR r1 ⊕ ROTR r2 ⊕ (SHR/ROTR third)`. SHR drops the third term when it shifts past the top. -/
def sigmaSources (r1 r2 third : Nat) (isShift : Bool) (i : Nat) : List Nat :=
  let a := (i + r1) % 32
  let b := (i + r2) % 32
  if isShift then
    (if i + third < 32 then [a, b, i + third] else [a, b])
  else
    [a, b, (i + third) % 32]

/-- **Σ/σ gadget** (Σ0/Σ1/σ0/σ1). Input word at `inBase`, output at `outBase`, per-bit XOR carries
at `carBase`; `(r1,r2,third,isShift)` selects the function. 96 constraints. -/
def sigmaWord (inBase outBase carBase r1 r2 third : Nat) (isShift : Bool) : List VmConstraint2 :=
  (List.range 32).map (fun i =>
    cgH (xorHead ((sigmaSources r1 r2 third isShift i).map (inBase + ·)) (outBase+i) (carBase+i)))
  ++ (wordBits outBase).map binGate
  ++ (wordBits carBase).map binGate

/-- **Ch gadget** `Ch(e,f,g)` → word at `outBase`. 64 constraints. -/
def chWord (eBase fBase gBase outBase : Nat) : List VmConstraint2 :=
  (List.range 32).map (fun i => cgH (chHead (eBase+i) (fBase+i) (gBase+i) (outBase+i)))
  ++ (wordBits outBase).map binGate

/-- **Maj gadget** `Maj(a,b,c)` → word at `outBase`. 64 constraints. -/
def majWord (aBase bBase cBase outBase : Nat) : List VmConstraint2 :=
  (List.range 32).map (fun i => cgH (majHead (aBase+i) (bBase+i) (cBase+i) (outBase+i)))
  ++ (wordBits outBase).map binGate

/-- The mod-2^32 add head `Σ inputs − wordValue(out) − 2^32·Σ 2^t·carBit_t`. -/
def addMod32Head (ins : List Head) (outBase : Nat) (carBits : List Nat) : Head :=
  let sumIns := ins.foldl Head.append Head.zero
  let h1 := sumIns.append ((wordValue outBase).scale (-1))
  carBits.zipIdx.foldl (fun h (p : Nat × Nat) => h.addLin (-(2^32 * 2^p.2 : ℤ)) p.1) h1

/-- **Modular adder** `out ≡ Σ inputs (mod 2^32)`, output at `outBase`, carry decomposed over
`carBits` (3 bits suffice for ≤ 6 summands). `1 + 32 + |carBits|` constraints. -/
def addMod32 (ins : List Head) (outBase : Nat) (carBits : List Nat) : List VmConstraint2 :=
  cgH (addMod32Head ins outBase carBits)
  :: (wordBits outBase).map binGate
  ++ carBits.map binGate

/-! ## §4 — The round + block generators (the parameterized fold — the KEY deliverable). -/

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

/-- **`sha256Round`** — one compression round as GENERATED constraints, given the state layout `s`,
the message-word base `wBase`, the round constant `kConst`, and the next free column `fresh`.
Returns `(constraints, next state layout, next free column)`. The 8-word rotation `(a..h) ↦
(newA, a, b, c, newE, e, f, g)` is pure re-labelling (no constraints). 464 constraints. -/
def sha256Round (s : St) (wBase : Nat) (kConst : ℤ) (fresh : Nat) :
    List VmConstraint2 × St × Nat :=
  let s1  := fresh;      let s1c := s1  + 32   -- Σ1(e)  : out + per-bit carry
  let ch  := s1c + 32                          -- Ch(e,f,g)
  let t1  := ch  + 32;   let t1c := t1  + 32   -- T1 : out + 3 add-carry bits
  let s0  := t1c + 3;    let s0c := s0  + 32   -- Σ0(a)
  let mj  := s0c + 32                          -- Maj(a,b,c)
  let t2  := mj  + 32;   let t2c := t2  + 32   -- T2 : out + 3 add-carry bits
  let ne  := t2c + 3;    let nec := ne  + 32   -- new e = d + T1
  let na  := nec + 3;    let nac := na  + 32   -- new a = T1 + T2
  let next := nac + 3
  let cs : List VmConstraint2 :=
       sigmaWord s.e s1 s1c 6 11 25 false
    ++ chWord s.e s.f s.g ch
    ++ addMod32 [wordValue s.h, wordValue s1, wordValue ch, Head.c kConst, wordValue wBase]
         t1 [t1c, t1c+1, t1c+2]
    ++ sigmaWord s.a s0 s0c 2 13 22 false
    ++ majWord s.a s.b s.c mj
    ++ addMod32 [wordValue s0, wordValue mj] t2 [t2c, t2c+1, t2c+2]
    ++ addMod32 [wordValue s.d, wordValue t1] ne [nec, nec+1, nec+2]
    ++ addMod32 [wordValue t1, wordValue t2] na [nac, nac+1, nac+2]
  let s' : St := { a := na, b := s.a, c := s.b, d := s.c, e := ne, f := s.e, g := s.f, h := s.g }
  (cs, s', next)

/-- **`scheduleWord`** — one message-schedule step `W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]`
as GENERATED constraints, given the four input word bases, the output base, and the next free column
for the two sigma scratch words. Returns `(constraints, next free column)`. -/
def scheduleWord (w2 w7 w15 w16 : Nat) (outBase fresh : Nat) : List VmConstraint2 × Nat :=
  let sg1 := fresh;      let sg1c := sg1 + 32   -- σ1(W[t-2])
  let sg0 := sg1c + 32;  let sg0c := sg0 + 32   -- σ0(W[t-15])
  let cc  := sg0c + 32                          -- 3 add-carry bits
  let next := cc + 3
  let cs : List VmConstraint2 :=
       sigmaWord w2 sg1 sg1c 17 19 10 true
    ++ sigmaWord w15 sg0 sg0c 7 18 3 true
    ++ addMod32 [wordValue sg1, wordValue w7, wordValue sg0, wordValue w16] outBase [cc, cc+1, cc+2]
  (cs, next)

/-- **`sha256Compress`** — the whole 64-round compression as ONE generated constraint list, given the
16 message-word bases `wBases`, the 8 IV/state bases `s0`, and the first free column. The 64 rounds
are the FREE `List.foldl` of `sha256Round`; this is the "generator makes them free" claim, realized.
(Not `#guard`-accepted whole — see the header's resolution note.) -/
def sha256Compress (wBases : List Nat) (s0 : St) (fresh : Nat) : List VmConstraint2 :=
  let step := fun (acc : List VmConstraint2 × St × Nat) (t : Nat) =>
    let (cs, st, fr) := acc
    let (cs', st', fr') := sha256Round st (wBases.getD t 0) ((Ref.K.getD t 0 : Nat) : ℤ) fr
    (cs ++ cs', st', fr')
  ((List.range 64).foldl step (([] : List VmConstraint2), s0, fresh)).1

/-! ## §5 — Semantic lemmas: the emitted gates FORCE the SHA-256 bit functions (ℤ reading).

These are the "demonstrably computes, not just type-checks" content: each gate's zero pins the output
column to exactly the arithmetic of its inputs, and (for the boolean inputs the surrounding pins
force) to the actual XOR / Ch / Maj. No `native_decide`. -/

/-- The XOR gate's forced equation: `Σ ins − out − 2·car = 0`. So a satisfying assignment pins
`out = (Σ ins) − 2·car`; with the input/output/carry columns boolean (the surrounding `binGate`s),
`out` is the parity `⊕ ins` and `car` the majority. -/
theorem xorHead_eval (a : Assignment) (ins : List Nat) (out car : Nat) :
    evalH (xorHead ins out car) a = (ins.map a).sum - a out - 2 * a car := by
  unfold xorHead
  simp only [evalH_addLin, evalH_foldl_addLin, evalH_zero]
  ring

/-- **The 3-way XOR gate forces the parity relation** `out = iA + iB + iC − 2·car` (the exact content
of `iA ⊕ iB ⊕ iC` once the columns are the boolean bits the pins force). -/
theorem xor3_forces (a : Assignment) (iA iB iC out car : Nat)
    (hg : evalH (xorHead [iA, iB, iC] out car) a = 0) :
    a out = a iA + a iB + a iC - 2 * a car := by
  rw [xorHead_eval] at hg
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hg
  omega

/-- The `Ch` gate's forced equation: `out = e·f + (1−e)·g` — i.e. `if e then f else g` on bits. -/
theorem chHead_forces (a : Assignment) (e f g out : Nat)
    (hg : evalH (chHead e f g out) a = 0) :
    a out = a e * a f + (1 - a e) * a g := by
  simp only [chHead, evalH_addProd, evalH_addLin, evalH_lin, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil] at hg
  linear_combination hg

/-- The `Maj` gate's forced equation: `out = a·b + b·c + c·a − 2·a·b·c` — the majority on bits. -/
theorem majHead_forces (a : Assignment) (x y z out : Nat)
    (hg : evalH (majHead x y z out) a = 0) :
    a out = a x * a y + a y * a z + a z * a x - 2 * (a x * a y * a z) := by
  simp only [majHead, evalH_addProd, evalH_lin, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil] at hg
  linear_combination hg

#assert_axioms xorHead_eval
#assert_axioms xor3_forces
#assert_axioms chHead_forces
#assert_axioms majHead_forces

/-! ## §6 — KAT: the GENERATED constraints ACCEPT the reference's honest values and REJECT tamper.

`acceptB` is the ℤ reading of the emitted gate bodies (like `LightClientEthAir.airAccepts`): every
`.base (.gate e)` has `e.eval a = 0`. Anchored to §0's digest-validated reference. -/

/-- The ℤ reading of one emitted constraint (non-gates are addressing, treated as vacuously true). -/
def gateBodyEvalZero (a : Assignment) : VmConstraint2 → Bool
  | .base (.gate e) => decide (e.eval a = 0)
  | _ => true

/-- The ℤ acceptance predicate over a generated constraint list. -/
def acceptB (gs : List VmConstraint2) (a : Assignment) : Bool := gs.all (gateBodyEvalZero a)

/-- Bit `j` of `x` as a felt column value. -/
def bZ (x j : Nat) : ℤ := (Ref.bit x j : Nat)

/-- Sum of the (present) source bits feeding output bit `i` of a Σ/σ over input word `X`. -/
def srcSum (X r1 r2 third : Nat) (isShift : Bool) (i : Nat) : Nat :=
  ((sigmaSources r1 r2 third isShift i).map (Ref.bit X)).foldl (· + ·) 0

/-- Honest witness for a standalone Σ/σ over input `X` (layout inBase=0, outBase=32, carBase=64). -/
def sigmaAsg (X r1 r2 third : Nat) (isShift : Bool) : Assignment := fun col =>
  if col < 32 then bZ X col
  else if col < 64 then ((srcSum X r1 r2 third isShift (col-32) % 2 : Nat) : ℤ)
  else if col < 96 then ((srcSum X r1 r2 third isShift (col-64) / 2 : Nat) : ℤ)
  else 0

/-- Honest witness for a standalone `Ch(E,F,G)` (bases 0/32/64, out 96). -/
def chAsg (E F G : Nat) : Assignment := fun col =>
  if col < 32 then bZ E col
  else if col < 64 then bZ F (col-32)
  else if col < 96 then bZ G (col-64)
  else if col < 128 then bZ (Ref.chf E F G) (col-96)
  else 0

/-- Honest witness for a standalone `Maj(X,Y,Z)` (bases 0/32/64, out 96). -/
def majAsg (X Y Z : Nat) : Assignment := fun col =>
  if col < 32 then bZ X col
  else if col < 64 then bZ Y (col-32)
  else if col < 96 then bZ Z (col-64)
  else if col < 128 then bZ (Ref.majf X Y Z) (col-96)
  else 0

/-- Honest witness for a standalone 3-input `addMod32` (bases 0/32/64, out 96, carry 128..130). -/
def addAsg (X Y Z : Nat) : Assignment := fun col =>
  if col < 32 then bZ X col
  else if col < 64 then bZ Y (col-32)
  else if col < 96 then bZ Z (col-64)
  else if col < 128 then bZ (Ref.w32 (X + Y + Z)) (col-96)
  else if col < 131 then (Ref.bit ((X + Y + Z) / Ref.M) (col-128) : ℤ)
  else 0

/-- Flip the felt at column `c` between 0 and 1 (to forge a witness). -/
def flipAt (a : Assignment) (c : Nat) : Assignment := fun col => if col = c then 1 - a col else a col

/-- The two Σ/σ instances under test (σ0: rotations 7,18 + shift 3; Σ0: rotations 2,13,22). -/
def sigma0Gadget : List VmConstraint2 := sigmaWord 0 32 64 7 18 3 true
def bigSigma0Gadget : List VmConstraint2 := sigmaWord 0 32 64 2 13 22 false
def chGadget : List VmConstraint2 := chWord 0 32 64 96
def majGadget : List VmConstraint2 := majWord 0 32 64 96
def addGadget : List VmConstraint2 := addMod32 [wordValue 0, wordValue 32, wordValue 64] 96 [128,129,130]

-- Constants under test: real SHA-256 IV / K words (nonzero, exercise every bit path).
private def X0 : Nat := 0x6a09e667  -- IV a
private def X1 : Nat := 0xbb67ae85  -- IV b
private def X2 : Nat := 0x3c6ef372  -- IV c

/-! ### σ0 — accepts the honest witness, rejects a flipped output bit, out word ties to the reference. -/
#guard acceptB sigma0Gadget (sigmaAsg X0 7 18 3 true) == true
#guard acceptB sigma0Gadget (flipAt (sigmaAsg X0 7 18 3 true) 37) == false   -- flip out bit 5
#guard Ref.natOfBits32 (fun i => srcSum X0 7 18 3 true i % 2) == Ref.s0 X0

/-! ### Σ0 — accepts, rejects a flipped carry bit, out word ties to the reference. -/
#guard acceptB bigSigma0Gadget (sigmaAsg X0 2 13 22 false) == true
#guard acceptB bigSigma0Gadget (flipAt (sigmaAsg X0 2 13 22 false) 70) == false  -- flip carry bit 6
#guard Ref.natOfBits32 (fun i => srcSum X0 2 13 22 false i % 2) == Ref.bS0 X0

/-! ### Ch — accepts, rejects a flipped output bit. -/
#guard acceptB chGadget (chAsg X0 X1 X2) == true
#guard acceptB chGadget (flipAt (chAsg X0 X1 X2) 100) == false

/-! ### Maj — accepts, rejects a flipped output bit. -/
#guard acceptB majGadget (majAsg X0 X1 X2) == true
#guard acceptB majGadget (flipAt (majAsg X0 X1 X2) 110) == false

/-! ### addMod32 — accepts, rejects a flipped output bit, out word ties to the reference. -/
#guard acceptB addGadget (addAsg X0 X1 X2) == true
#guard acceptB addGadget (flipAt (addAsg X0 X1 X2) 96) == false
#guard Ref.natOfBits32 (fun i => Ref.bit (Ref.w32 (X0 + X1 + X2)) i) == Ref.w32 (X0 + X1 + X2)

/-! ## §7 — Structural `#guard`s: the generators produce the budgeted shapes; AIR packaging. -/

#guard sigma0Gadget.length == 96
#guard chGadget.length == 64
#guard majGadget.length == 64
#guard addGadget.length == 36
#guard (sha256Round ⟨0,32,64,96,128,160,192,224⟩ 256 0 288).1.length == 464
#guard (scheduleWord 0 32 64 96 128 160).1.length == 228   -- 96 + 96 + 36

/-- A single Σ/σ gadget packaged as an `EffectVmDescriptor2` (the AIR type the light-client emits),
showing the generator drops straight into the deployed descriptor vocabulary. -/
def sigma0Desc : EffectVmDescriptor2 :=
  { name        := "dregg-sha256-sigma0::demo"
  , traceWidth  := 96
  , piCount     := 0
  , tables      := []
  , constraints := sigma0Gadget
  , hashSites   := []
  , ranges      := [] }

#guard sigma0Desc.constraints.length == 96
#guard sigma0Desc.traceWidth == 96

end Dregg2.Circuit.Emit.Sha256Gadget
