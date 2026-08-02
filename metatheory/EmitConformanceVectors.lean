/-
# EmitConformanceVectors — the LEAN HALF of the Lean↔Rust Pickles conformance differential.

⚑ **WHAT THIS IS.** `metatheory/fixtures/pickles-crossimpl-harness/` drives o1-labs'
`proof-systems` 0.3.0 — the Rust that Mina devnet/mainnet run and the tag openmina links — over a
deterministic sweep of inputs and dumps one TSV record per case. THIS file drives dregg's Lean over
the SAME sweep and dumps the SAME shape. `scripts/pickles-crossimpl-differential.sh` requires the
two files to be **byte-identical**.

The existing conformance evidence in this tree is a handful of `#guard`s comparing a Lean value to
ONE devnet block's wire word. That is evidence about *a value at one input*. This is evidence about
*the function*: same inputs, same outputs, 2000+ of them, including adversarial ones.

⚑ **THE INPUTS ARE IN THE VECTOR TOO.** Both sides emit the inputs they used. A generator that
drifted between the two languages is therefore itself a RED diff, not a silent
comparison-of-different-things. The generator (SplitMix64 + a fixed adversarial bank) is written
twice on purpose; if the two writings disagree the diff says so at the input column.

⚑ **NOT A SOUNDNESS RESULT.** This is a FIDELITY differential. Two implementations agreeing on
2000 inputs is strong evidence they compute the same function and no evidence that the function is
the right one. Where dregg's Lean and o1-labs' Rust are BOTH wrong in the same way, this is silent.

⚑ **SUBSTRATE.** No AIR, no gate, no constraint. This file only *calls* value-returning functions
that already exist (`KimchiVerify`, `MinaWrapDeferred`, `TickShifts`, `PastaPoseidonFq`) and
`IO.print`s their results. It defines no verification logic and is imported by nothing.

RUN:  cd metatheory && lake env lean --run EmitConformanceVectors.lean > /tmp/lean-vectors.tsv

⚠ COST, and where it BITES. This runs under the Lean INTERPRETER, so every `ZMod pN` multiplication
is an interpreted bignum `Nat.mod`. `zkPolyR` reaches `omega ^ (n−3)` through `Monoid.npow`, which
is LINEAR recursion: at the real step domain n = 2^16 that is 196k interpreted multiplications and
~65k frames of non-tail recursion PER CASE, so the `zkpoly` sweep stops at 2^10. The `permof`
sweep does NOT: `MinaWrapDeferred.permOf` computes the same `omega ^ (n−3)` through `powMod`
(square-and-multiply), so it reaches log2 = 16 — the real domain — and carries the same zk
polynomial with it.

⚑ THE `[Field F]` LAYER IS REACHED — the claim that stood here until 2026-08-02 was STALE.

This header used to say: "`KimchiVerify.publicEval`, `ftEval0`, `permScalar`, `combinedInnerProduct`,
`zkPoly`, `ipaB0` and `ftComm` are declared under `variable {F : Type} [Field F]`, and this tree has
NO `Field (ZMod pN)` instance … they cannot be instantiated at the deployed field AT ALL, so no
differential can reach them."

**Measured 2026-08-02: `Field (ZMod pN)` synthesizes, and it is COMPUTABLE.**
`Dregg2/Circuit/Emit/PastaBasePrime.lean:122` has installed `instance : Fact (Nat.Prime pN)` since
2026-07-29 (commit `8ba2591c3`) — a kernel-checked recursive Lucas/Pratt certificate, `#assert_axioms`-
clean, no `native_decide` — and Mathlib's `ZMod.instField` fires off it. `(7 : ZMod pN)⁻¹ * 7`
evaluates to `1` under the interpreter without a `noncomputable` marker. What was missing was one
`import` line in THIS file, not an instance in the tree. The line is below.

So the `[Field F]` layer is now swept at the deployed field: `permscalar` (`permScalar`),
`publiceval` (`publicEval`) and `ipab0` (`ipaB0`) in §15. That matters because their evidence before
this was: two `#guard`s at `ℚ` for `publicEval`, one at `ℚ` for `ipaB0`, one at `ℚ` plus one
`[Field K]`-generic `rfl` for `permScalar` — and NO theorem anywhere in the tree mentions
`publicEval` or `ipaB0` at all.

⚑ AND THE Fq SIDE IS NOW SWEPT TOO. This header used to say: "STILL UNREACHED, and named rather
than papered over: there is **no `Fact (Nat.Prime qN)`**, so `ZMod qN` — the field
`MinaRealBlockGate` and `MinaWrapFtEval0` work at — is still not a `Field`."
`Dregg2/Circuit/Emit/PastaScalarPrime.lean` supplies it, by the same kernel-checked Lucas/Pratt
route and in 2.81 s of elaboration. §18 sweeps `rootunity_fq`, `zkpoly_fq`, `permscalar_fq`,
`publiceval_fq` and `ipab0_fq` — and Fq is the field the WRAP verifier computes in, so this is the
deployed instantiation and not a symmetry exercise.

⚑ AND `gateLinConst` HAS A THIRD REFERENCE, in §19. It is the most defect-prone definition in this
tree — it carried a `.take 11` over-count AND the wrong cube-root endo, and every fixture stayed
green because every fixture sat at `emulSel = 0`. §7 (`linconst`) gave it a second reference,
kimchi's `PolishToken::evaluate(constant_term)`. §19 gives it openmina's, which builds its own
linearization and runs its own `Expr` evaluator with no `PolishToken` anywhere, plus `ft0_om`:
`ftEval0R` fed `gateLinConst` against openmina's `ft_eval0` computing ITS constant term internally.

Measured 2026-08-02 by re-emitting this file with each historical defect put back:
  `.take 11` → take-12       linconst 214/276 · linconst_om 238/420 · ft0_om 110/120
  base endo → `er` (= endo²) linconst   0/276 · linconst_om 238/420 · ft0_om 110/120
The `linconst` zero is not a miss — §7 FEEDS the endo as a swept input, so a Lean side that DERIVED
the wrong endo is outside what it measures. §19 pins it and catches that half.

⚑ THE SECOND SPONGE, also new in §15. The `sponge_fp`/`sponge_fq`/`challenge` pairs drive
`PastaPoseidonFq.SpongeSt`. `KimchiVerify.frSpongeDigest`/`frSqueezePair` — what C3's `challengesOk`
actually runs on — are built on `PastaPoseidon.Ref.absorbAll`, a different Lean spelling that nothing
was diffing. `Dregg2/Circuit/Emit/PastaSpongeWeld.lean` proves the two spellings equal for every
input; `frdigest`, `frpair` and `frphase2` here measure that function against o1-labs'
`DefaultFrSponge`. `frphase2` is the first thing that tests `frEvalPointOrder` against kimchi's own
`absorb_evaluations` — its only previous check was a `decide` on the first seven entries.
-/
import Dregg2.Circuit.Emit.KimchiVerify
import Dregg2.Bridge.MinaWrapDeferred
import Dregg2.Bridge.TickShifts
import Dregg2.Circuit.Emit.PastaPoseidonFq
import Dregg2.Circuit.Emit.PicklesRecursion
-- ⚑ THE ONE LINE THAT MAKES THE `[Field F]` LAYER REACHABLE: `Fact (Nat.Prime pN)`, hence
-- `Field (ZMod pN)` by Mathlib's `ZMod.instField`.
import Dregg2.Circuit.Emit.PastaBasePrime
-- ⚑ AND THE SAME LINE FOR THE SCALAR FIELD: `Fact (Nat.Prime qN)`, hence `Field (ZMod qN)`. This is
-- what §18 needs; without it `permScalar`/`publicEval`/`ipaB0` do not TYPE at `ZMod qN` at all.
import Dregg2.Circuit.Emit.PastaScalarPrime

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Dregg2.ConformanceVectors

open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.KimchiVerify
  (endoMap bEvalSq cipR zkPolyR gateLinConst GateEvals ftEval0R
   publicEval permScalar ipaB0 frSqueezePair frSpongeDigest frEvalPointOrder)
open Dregg2.Bridge.MinaWrapDeferred (endoLift bPolyMod rootOfUnity permOf shiftType1 unshiftType1)
open Dregg2.Circuit.Emit.PicklesRecursion
  (type1OfField type1ToField type2OfField type2ToField shift1Fp shift2Fq)
open Dregg2.Bridge.MinaWrapFtEval0 (powFast)
open Dregg2.Bridge.TickShifts (tickShiftsFp)
open Dregg2.Circuit.Emit.PastaPoseidonFq
  (Params fpParams fqParams SpongeSt newSponge absorb1 squeeze1 challenge)

/-! ## §0 — SplitMix64 over `Nat`. MIRRORS `pickles-crossimpl-harness/src/main.rs` §0 VERBATIM. -/

/-- The 64-bit mask; every product and sum below is reduced through it, which is what Rust's
`wrapping_*` does. -/
def M64 : Nat := 2 ^ 64 - 1

/-- One SplitMix64 step: advance the state by the odd golden-ratio constant, then run the
finaliser. Returns `(state', output)`. -/
def smNext (s : Nat) : Nat × Nat :=
  let s' := (s + 0x9E3779B97F4A7C15) &&& M64
  let z0 := s'
  let z1 := ((z0 ^^^ (z0 >>> 30)) * 0xBF58476D1CE4E5B9) &&& M64
  let z2 := ((z1 ^^^ (z1 >>> 27)) * 0x94D049BB133111EB) &&& M64
  (s', z2 ^^^ (z2 >>> 31))

/-- `n` successive outputs, with the advanced state. -/
def smWords (s : Nat) : Nat → Nat × List Nat
  | 0 => (s, [])
  | k + 1 =>
      let (s1, w) := smNext s
      let (s2, ws) := smWords s1 k
      (s2, w :: ws)

/-- A field element in `ZMod m`: four little-endian 64-bit words assembled and reduced — exactly
`Fp::from_le_bytes_mod_order` over the same 32 bytes. -/
def smFe (m : Nat) (s : Nat) : Nat × Nat :=
  let (s', ws) := smWords s 4
  let n := ws.getD 0 0 + ws.getD 1 0 * 2 ^ 64 + ws.getD 2 0 * 2 ^ 128 + ws.getD 3 0 * 2 ^ 192
  (s', n % m)

/-- A raw 128-bit challenge: two little-endian words. -/
def smChal (s : Nat) : Nat × Nat :=
  let (s', ws) := smWords s 2
  (s', ws.getD 0 0 + ws.getD 1 0 * 2 ^ 64)

/-- `next_u64() % m`. -/
def smBelow (s m : Nat) : Nat × Nat :=
  let (s', w) := smNext s
  (s', w % m)

/-! ## §1 — 64-char big-endian lowercase hex; total, and the same on both sides. -/

def hexDigit (d : Nat) : Char :=
  if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

/-- 32 bytes, big-endian, as 64 lowercase hex characters. Values ≥ 2^256 are truncated — no value
emitted here is that large (every one is a `< 2^256` field representative or a small counter). -/
def strOf (cs : List Char) : String := cs.foldl (fun acc c => acc.push c) ""

def hx (n : Nat) : String :=
  strOf ((List.range 64).map (fun i => hexDigit ((n >>> (4 * (63 - i))) &&& 15)))

/-- Rust's `{:04}`. -/
def pad4 (n : Nat) : String :=
  let s := toString n
  if s.length ≥ 4 then s else strOf (List.replicate (4 - s.length) '0') ++ s

/-- One record: `pair \t case \t in,in,… \t out,out,…`. -/
def mkRec (pair : String) (case : Nat) (ins outs : List Nat) : String :=
  pair ++ "\t" ++ pad4 case ++ "\t"
    ++ String.intercalate "," (ins.map hx) ++ "\t"
    ++ String.intercalate "," (outs.map hx)

/-! ## §2 — the adversarial banks. MIRRORS the harness's `edge_fp` / `edge_fq` / `edge_chal`. -/

/-- Field-element edge bank in a FIXED order: zero, one, two, `p−1`, `p−2`, `(p−1)/2`, `2^128`,
`2^128−1`, `2^255 mod p` (the Type2 shift constant), `(2^255+1) mod p` (the Type1 shift constant
`c`), `2^254`, and a small generator. Both sides of the Type1/Type2 shift boundary are in here on
purpose. -/
def edgeOf (m : Nat) : List Nat :=
  [0, 1, 2, m - 1, m - 2, (m - 1) / 2, 2 ^ 128 % m, (2 ^ 128 - 1) % m,
   2 ^ 255 % m, (2 ^ 255 + 1) % m, 2 ^ 254 % m, 5]

def edgeFp : List Nat := edgeOf pN
def edgeFq : List Nat := edgeOf qN

/-- 128-bit challenge edge bank, FIXED order. The ≥ 2^128 regime is covered by sub-sweep B of the
`endo` pair, which feeds a full 255-bit field element as the challenge. -/
def edgeChal : List Nat :=
  [0, 1, 2, 3, 2 ^ 128 - 1, 2 ^ 128 - 2, 2 ^ 127, 2 ^ 127 - 1,
   0x55555555555555555555555555555555, 0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA]

/-- `bank[i % bank.length]`, the harness's indexing. -/
def bk (bank : List Nat) (i : Nat) : Nat := bank.getD (i % bank.length) 0

/-! ## §3 — coercion helpers. -/

def toFp (n : Nat) : ZMod pN := (n : ZMod pN)
def toFq (n : Nat) : ZMod qN := (n : ZMod qN)
def ofFp (x : ZMod pN) : Nat := x.val
def ofFq (x : ZMod qN) : Nat := x.val

/-! ## §4 — `endo`: `KimchiVerify.endoMap` over `ZMod pN` and `ZMod qN`. -/

def emitEndo : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  -- A: edge endo × edge 128-bit challenge
  for e in edgeFp do
    for c in edgeChal do
      out := out ++ [mkRec "endo" case [e, c] [ofFp (endoMap (toFp e) c)]]
      case := case + 1
  -- B: edge endo × FULL 255-bit challenge (the ≥2^128 adversarial regime: `to_field_with_length`
  -- reads bits 0..127 of the canonical bigint and must ignore the high bits)
  for e in edgeFp do
    for c in edgeFp do
      out := out ++ [mkRec "endo" case [e, c] [ofFp (endoMap (toFp e) c)]]
      case := case + 1
  -- C: random
  let mut s := 1
  for _ in List.range 256 do
    let (s1, e) := smFe pN s
    let (s2, c) := smChal s1
    s := s2
    out := out ++ [mkRec "endo" case [e, c] [ofFp (endoMap (toFp e) c)]]
    case := case + 1
  return out

def emitEndoFq : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  for e in edgeFq do
    for c in edgeChal do
      out := out ++ [mkRec "endo_fq" case [e, c] [ofFq (endoMap (toFq e) c)]]
      case := case + 1
  let mut s := 2
  for _ in List.range 128 do
    let (s1, e) := smFe qN s
    let (s2, c) := smChal s1
    s := s2
    out := out ++ [mkRec "endo_fq" case [e, c] [ofFq (endoMap (toFq e) c)]]
    case := case + 1
  return out

/-- ⚑ dregg's SECOND copy of the endomorphism lift: `MinaWrapDeferred.endoLift`, which bakes the
`ENDO` constant in rather than taking it as a parameter. Two copies that agree today are two that
disagree later; this is the block that would say so. -/
def emitEndoLift : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  for c in edgeChal do
    out := out ++ [mkRec "endolift" case [c] [endoLift c]]
    case := case + 1
  for c in edgeFp do
    out := out ++ [mkRec "endolift" case [c] [endoLift c]]
    case := case + 1
  let mut s := 10
  for _ in List.range 192 do
    let (s1, c) := smChal s
    s := s1
    out := out ++ [mkRec "endolift" case [c] [endoLift c]]
    case := case + 1
  return out

/-! ## §5 — `bpoly`: `KimchiVerify.bEvalSq` and `MinaWrapDeferred.bPolyMod` vs `b_poly`. -/

def bpolyLens : List Nat := [0, 1, 2, 3, 15, 16]

/-- Both Lean copies run over the SAME generated inputs (same seed), emitted as two blocks. -/
def emitBpoly (name : String) (useMod : Bool) : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  let ev : Nat → List Nat → Nat :=
    fun x cs => if useMod then bPolyMod x cs else ofFp (bEvalSq (toFp x) (cs.map toFp))
  for k in bpolyLens do
    for x in edgeFp do
      let chals := (List.range k).map (fun i => bk edgeFp i)
      out := out ++ [mkRec name case ([k, x] ++ chals) [ev x chals]]
      case := case + 1
  let mut s := 3
  for _ in List.range 192 do
    let (s1, ki) := smBelow s bpolyLens.length
    let k := bpolyLens.getD ki 0
    let (s2, x) := smFe pN s1
    let mut s3 := s2
    let mut chals : List Nat := []
    for _ in List.range k do
      let (s4, c) := smFe pN s3
      s3 := s4
      chals := chals ++ [c]
    s := s3
    out := out ++ [mkRec name case ([k, x] ++ chals) [ev x chals]]
    case := case + 1
  return out

/-! ## §6 — `cip`: `KimchiVerify.cipR` vs `combined_inner_product` (chunk_size = 1). -/

def cipWidths : List Nat := [0, 1, 2, 47]

def emitCip : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  for m in cipWidths do
    for bi in List.range edgeFp.length do
      let ps := edgeFp.getD bi 0
      let es := bk edgeFp (bi + 1)
      let z := (List.range m).map (fun i => bk edgeFp i)
      let w := (List.range m).map (fun i => bk edgeFp (i + 3))
      let v := ofFp (cipR (toFp ps) (toFp es) (z.map toFp) (w.map toFp))
      out := out ++ [mkRec "cip" case ([m, ps, es] ++ z ++ w) [v]]
      case := case + 1
  let mut s := 4
  for _ in List.range 96 do
    let (s1, mi) := smBelow s cipWidths.length
    let m := cipWidths.getD mi 0
    let (s2, ps) := smFe pN s1
    let (s3, es) := smFe pN s2
    let mut s4 := s3
    let mut z : List Nat := []
    for _ in List.range m do
      let (s5, v) := smFe pN s4
      s4 := s5
      z := z ++ [v]
    let mut w : List Nat := []
    for _ in List.range m do
      let (s5, v) := smFe pN s4
      s4 := s5
      w := w ++ [v]
    s := s4
    let v := ofFp (cipR (toFp ps) (toFp es) (z.map toFp) (w.map toFp))
    out := out ++ [mkRec "cip" case ([m, ps, es] ++ z ++ w) [v]]
    case := case + 1
  return out

/-! ## §7 — `linconst`: ⚑ THE FLAGSHIP. `KimchiVerify.gateLinConst` vs kimchi's
`PolishToken::evaluate(linearization.constant_term)`.

The Rust side builds the linearization from o1-labs' own `constraints_expr` — generic 2, poseidon
15, complete_add 7, varbasemul 21, endosclmul **11**, endomul_scalar 11, one shared α block from
α^0, `index_terms = []` — and runs its RPN evaluator. The Lean side runs six hand-transcribed
constraint bodies. Nothing is shared but the paper.

⚑ THE `.take 11` LIVES EXACTLY HERE, and the structured half runs seven selector patterns
including `emulSel = 1` and all-hot, so a `.take` that drifted is RED — which one devnet block with
`emulSel = 0` could never show. The MDS and the endo coefficient are SWEPT (the random half uses a
random MDS), so a Lean side that hardcoded `fp_kimchi`'s would pass a fixed-MDS test and fail here.
-/

/-- The three `EndomulScalar` quotient constants `11/6, −5/2, 2/3` as `ZMod pN` elements. The
inverse is Fermat's (`x ^ (p−2)` through the square-and-multiply ladder) rather than a `Field`
division, because the tree has NO `Field (ZMod pN)` instance. -/
def cAV : ZMod pN := (11 : ZMod pN) * powFast (6 : ZMod pN) (pN - 2)
def cBV : ZMod pN := (-5 : ZMod pN) * powFast (2 : ZMod pN) (pN - 2)
def cCV : ZMod pN := (2 : ZMod pN) * powFast (3 : ZMod pN) (pN - 2)

/-- `fp_kimchi`'s MDS, as dregg carries it. If this is not o1-labs' matrix, the INPUT column of
every `linconst` structured case diverges — which is a finding, not a false alarm. -/
def realMds : List (List Nat) := Dregg2.Circuit.Emit.PastaPoseidon.mdsN

def linGate (alpha endo : Nat) (mds : List (List Nat)) (coeff w wn sel : List Nat) :
    GateEvals (ZMod pN) :=
  { alpha := toFp alpha, endo := toFp endo, mds := mds.map (fun r => r.map toFp),
    coeff := coeff.map toFp, w := w.map toFp, wNext := wn.map toFp,
    cA := cAV, cB := cBV, cC := cCV,
    genSel := toFp (sel.getD 0 0), posSel := toFp (sel.getD 1 0),
    caddSel := toFp (sel.getD 2 0), mulSel := toFp (sel.getD 3 0),
    emulSel := toFp (sel.getD 4 0), emulScalarSel := toFp (sel.getD 5 0) }

def emitLinconst : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  let mkIns : Nat → Nat → Nat → Nat → Nat → List (List Nat) → List Nat → List Nat → List Nat →
      List Nat → List Nat :=
    fun a b g e zt mds coeff w wn sel =>
      [a, b, g, e, zt] ++ mds.flatten ++ coeff ++ w ++ wn ++ sel
  for hot in List.range 7 do
    for bi in List.range edgeFp.length do
      let sel := (List.range 6).map (fun i => if hot = 6 || hot = i then 1 else 0)
      let coeff := (List.range 15).map (fun i => bk edgeFp (bi + i))
      let w := (List.range 15).map (fun i => bk edgeFp (bi + 2 * i + 1))
      let wn := (List.range 15).map (fun i => bk edgeFp (bi + 3 * i + 5))
      let a := bk edgeFp (bi + 1)
      let b := bk edgeFp (bi + 2)
      let g := bk edgeFp (bi + 4)
      let e := bk edgeFp (bi + 7)
      let zt := bk edgeFp (bi + 9)
      let v := ofFp (gateLinConst (linGate a e realMds coeff w wn sel))
      out := out ++ [mkRec "linconst" case (mkIns a b g e zt realMds coeff w wn sel) [v]]
      case := case + 1
  let mut s := 5
  for _ in List.range 192 do
    -- ⚠ THE DRAW ORDER IS LOAD-BEARING: mds(9), coeff(15), w(15), wn(15), sel(6), then
    -- alpha, beta, gamma, endo, zeta — exactly `pair_linconst`'s random branch.
    let mut st := s
    let mut mds : List (List Nat) := []
    for _ in List.range 3 do
      let mut row : List Nat := []
      for _ in List.range 3 do
        let (s1, v) := smFe pN st
        st := s1
        row := row ++ [v]
      mds := mds ++ [row]
    let mut coeff : List Nat := []
    for _ in List.range 15 do
      let (s1, v) := smFe pN st; st := s1; coeff := coeff ++ [v]
    let mut w : List Nat := []
    for _ in List.range 15 do
      let (s1, v) := smFe pN st; st := s1; w := w ++ [v]
    let mut wn : List Nat := []
    for _ in List.range 15 do
      let (s1, v) := smFe pN st; st := s1; wn := wn ++ [v]
    let mut sel : List Nat := []
    for _ in List.range 6 do
      let (s1, v) := smFe pN st; st := s1; sel := sel ++ [v]
    let (sa, a) := smFe pN st
    let (sb, b) := smFe pN sa
    let (sg, g) := smFe pN sb
    let (se, e) := smFe pN sg
    let (sz, zt) := smFe pN se
    s := sz
    let v := ofFp (gateLinConst (linGate a e mds coeff w wn sel))
    out := out ++ [mkRec "linconst" case (mkIns a b g e zt mds coeff w wn sel) [v]]
    case := case + 1
  return out

/-! ## §8 — `zkpoly` / `rootunity` / `permscalar`.

⚑ `omega` is NOT read back from the Rust vector: the Lean side DERIVES it with
`MinaWrapDeferred.rootOfUnity` and emits it as an INPUT column. So a root-of-unity that drifted from
arkworks' `Radix2EvaluationDomain::group_gen` is red at the input column of every one of these
cases, and `rootunity` localises it. -/

def zkLogs : List Nat := [2, 3, 4, 5, 6, 7, 8, 9, 10]
def permLogs : List Nat := [2, 4, 8, 12, 16]

def emitZkpoly : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  let mut s := 6
  for l in zkLogs do
    let n := 2 ^ l
    let om := rootOfUnity l
    for z in edgeFp do
      let v := ofFp (zkPolyR n (toFp om) (toFp z))
      out := out ++ [mkRec "zkpoly" case [l, om, z] [v]]
      case := case + 1
    for _ in List.range 8 do
      let (s1, z) := smFe pN s
      s := s1
      let v := ofFp (zkPolyR n (toFp om) (toFp z))
      out := out ++ [mkRec "zkpoly" case [l, om, z] [v]]
      case := case + 1
  return out

def emitRootUnity : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  for l in List.range 25 do
    out := out ++ [mkRec "rootunity" case [l + 1] [rootOfUnity (l + 1)]]
    case := case + 1
  return out

/-- ⚑ `permof` — `MinaWrapDeferred.permOf` vs kimchi's `ConstraintSystem::perm_scalars`.

⚠ THIS DOCSTRING WAS STALE AND IS CORRECTED. It said: "NOT `KimchiVerify.permScalar`: that one is
declared under `variable {F : Type} [Field F]` and the tree has no `Field (ZMod pN)` instance, so it
is UNEVALUABLE at the deployed field and cannot be differentially tested at all." `permScalar` IS
swept — by `permscalar` at `ZMod pN` (§15) and `permscalar_fq` at `ZMod qN` (§18), over these exact
inputs. `permOf` is dregg's `Nat`-with-explicit-modulus copy of the same `derive_plonk` scalar and
it is the copy the Wrap public input goes through, which is why BOTH are emitted.

`permOf` bakes `alpha ^ PERM_ALPHA0` (α^21) rather than taking `alpha0`, so the Rust is fed
`alpha.pow(21)`. And because `permOf` reaches `omega ^ (n−3)` through `powMod`
(square-and-multiply), the sweep here REACHES log2 = 16 — the real Tick/step domain — which the
`npow`-bound `zkpoly` pair cannot. -/
def emitPermOf : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  let mut s := 7
  for l in permLogs do
    let n := 2 ^ l
    let om := rootOfUnity l
    for bi in List.range edgeFp.length do
      let zeta := edgeFp.getD bi 0
      let alpha := bk edgeFp (bi + 1)
      let beta := bk edgeFp (bi + 2)
      let gamma := bk edgeFp (bi + 3)
      let w := (List.range 15).map (fun i => bk edgeFp (bi + i))
      let sg := (List.range 6).map (fun i => bk edgeFp (bi + 2 * i + 4))
      let zzo := bk edgeFp (bi + 5)
      let v := permOf n om zeta alpha beta gamma w sg zzo
      out := out ++ [mkRec "permof" case ([l, om, zeta, alpha, beta, gamma, zzo] ++ w ++ sg) [v]]
      case := case + 1
    for _ in List.range 12 do
      let (s1, zeta) := smFe pN s
      let (s2, alpha) := smFe pN s1
      let (s3, beta) := smFe pN s2
      let (s4, gamma) := smFe pN s3
      let mut st := s4
      let mut w : List Nat := []
      for _ in List.range 15 do
        let (sx, v) := smFe pN st; st := sx; w := w ++ [v]
      let mut sg : List Nat := []
      for _ in List.range 6 do
        let (sx, v) := smFe pN st; st := sx; sg := sg ++ [v]
      let (s5, zzo) := smFe pN st
      s := s5
      let v := permOf n om zeta alpha beta gamma w sg zzo
      out := out ++ [mkRec "permof" case ([l, om, zeta, alpha, beta, gamma, zzo] ++ w ++ sg) [v]]
      case := case + 1
  return out

/-! ## §9 — `shifts`: `TickShifts.tickShiftsFp` vs `permutation::Shifts::new(&domain).shifts()`.

⚑ THE WHOLE POINT OF SWEEPING THE DOMAIN. `TickShifts` carries ONE oracle (`log2 = 16`), so its
`#guard` pins a single point of a REJECTION-SAMPLING loop. The counter stream, the
quadratic-non-residue test and the in-domain test only interact at OTHER domain sizes: a candidate
that is a QNR but lies in a smaller domain is rejected there and accepted at 16. -/

def emitShifts : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  for l in List.range 16 do
    let sh := (tickShiftsFp (l + 1)).map (fun x => x.val)
    out := out ++ [mkRec "shifts" case [l + 1] sh]
    case := case + 1
  return out

/-! ## §10 — the sponges. `PastaPoseidonFq.absorb1` / `squeeze1` vs `ArithmeticSponge`.

Driven through an INTERLEAVED absorb/squeeze script — bit `j` of the script selects absorb (0) or
squeeze (1) at step `j` — so the `Absorbed(n)` / `Squeezed(n)` state machine and the rate-boundary
permutation are exercised, not just `hash`. Every 6-step script is enumerated (64), then random
12-step ones. -/

def emitSponge (name : String) (P : Params) (bank : List Nat) (rnd : Nat) (seed : Nat) :
    List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  for script in List.range 64 do
    let mut sp : SpongeSt := newSponge
    let mut ins : List Nat := [script]
    let mut outs : List Nat := []
    let mut ai := 0
    for step in List.range 6 do
      if (script >>> step) &&& 1 = 0 then
        let x := bk bank (script + ai)
        ins := ins ++ [x]
        sp := absorb1 P sp x
        ai := ai + 1
      else
        let r := squeeze1 P sp
        sp := r.1
        outs := outs ++ [r.2]
    if outs.isEmpty then outs := [0]
    out := out ++ [mkRec name case ins outs]
    case := case + 1
  let mut s := seed
  for _ in List.range rnd do
    let (s1, sw) := smNext s
    let script := sw &&& 0xFFF
    let mut st := s1
    let mut sp : SpongeSt := newSponge
    let mut ins : List Nat := [script]
    let mut outs : List Nat := []
    for step in List.range 12 do
      if (script >>> step) &&& 1 = 0 then
        let (s2, x) := smFe P.modulus st
        st := s2
        ins := ins ++ [x]
        sp := absorb1 P sp x
      else
        let r := squeeze1 P sp
        sp := r.1
        outs := outs ++ [r.2]
    s := st
    if outs.isEmpty then outs := [0]
    out := out ++ [mkRec name case ins outs]
    case := case + 1
  return out

/-! ## §11 — `challenge`: three successive `challenge()`s of one `Fp` sponge.

⚑ `HIGH_ENTROPY_LIMBS = CHALLENGE_LENGTH_IN_LIMBS = 2`, so one `challenge()` drains the limb cache
and consecutive challenges are consecutive LANES of ONE permuted state, not two permutations. THREE
in a row measures that: lane 0, lane 1, then a fresh permute. A reading that permuted twice would
produce a correct first challenge and a wrong second — exactly the half-right this separates. -/

def emitChallenge : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  for nabs in List.range 8 do
    for bi in List.range edgeFp.length do
      let xs := (List.range nabs).map (fun i => bk edgeFp (bi + i))
      let mut sp : SpongeSt := newSponge
      for x in xs do
        sp := absorb1 fpParams sp x
      let r0 := challenge fpParams sp
      let r1 := challenge fpParams r0.1
      let r2 := challenge fpParams r1.1
      out := out ++ [mkRec "challenge" case ([nabs] ++ xs) [r0.2, r1.2, r2.2]]
      case := case + 1
  let mut s := 9
  for _ in List.range 32 do
    let (s1, nabs) := smBelow s 9
    let mut st := s1
    let mut xs : List Nat := []
    for _ in List.range nabs do
      let (s2, x) := smFe pN st; st := s2; xs := xs ++ [x]
    s := st
    let mut sp : SpongeSt := newSponge
    for x in xs do
      sp := absorb1 fpParams sp x
    let r0 := challenge fpParams sp
    let r1 := challenge fpParams r0.1
    let r2 := challenge fpParams r1.1
    out := out ++ [mkRec "challenge" case ([nabs] ++ xs) [r0.2, r1.2, r2.2]]
    case := case + 1
  return out

/-! ## §12 — the three `EndomulScalar` quotient constants, alone, so a bad modular inverse does not
show up only as an unlocalisable `linconst` red. -/

def emitEmulConsts : List String :=
  [mkRec "emulconsts" 0 [0] [cAV.val, cBV.val, cCV.val]]

/-! ## §13 — the OPENMINA half (`pickles-openmina-harness`), appended to the same stream.

The reference for these is openmina (`mina-tree`), an INDEPENDENT Rust rendering of Pickles — not
kimchi. `om_endo` is a THIRD spelling of the endomorphism lift (openmina writes it as
`u128::reverse_bits()` + a forward pair iterator where kimchi writes a reversed `get_bit` loop and
this tree writes a `List.range 64 |>.reverse` fold). `om_bpoly` is a second reading of the same
product. The four shift pairs are the Type1/Type2 bridge kimchi does not carry at all.

⚑ THE SHIFT BOUNDARY IS THE POINT. Type1 is `(x − (2^255+1))·2⁻¹` over Fp; Type2 is `x − 2^255` over
Fq. The bank feeds `2^255`, `2^255+1` (the constant itself, whose image is 0), `2^254`, `p−1` and
`(p−1)/2` — values that STRADDLE the boundary, where an off-by-one in `c` or a dropped halving lands
on a perfectly canonical field element and is invisible to any single-value pin.

⚑ AND BOTH LEAN COPIES OF TYPE1 RUN. `MinaWrapDeferred.shiftType1` and
`PicklesRecursion.type1OfField shift1Fp` are two independent renderings in this tree; they are
emitted as `shift1` and `shift1b` over IDENTICAL inputs, so a divergence between them shows up as
exactly one of the two blocks going red. -/

def omBpolyLens : List Nat := [1, 2, 3, 15, 16]

def emitOmEndo : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  for c in edgeChal do
    out := out ++ [mkRec "om_endo" case [c] [endoLift c]]
    case := case + 1
  let mut s := 0x11
  for _ in List.range 192 do
    let (s1, c) := smChal s
    s := s1
    out := out ++ [mkRec "om_endo" case [c] [endoLift c]]
    case := case + 1
  return out

def emitOmBpoly : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  for k in omBpolyLens do
    for x in edgeFp do
      let chals := (List.range k).map (fun i => bk edgeFp i)
      out := out ++ [mkRec "om_bpoly" case ([k, x] ++ chals) [bPolyMod x chals]]
      case := case + 1
  let mut s := 0x12
  for _ in List.range 128 do
    let (s1, ki) := smBelow s omBpolyLens.length
    let k := omBpolyLens.getD ki 0
    let (s2, x) := smFe pN s1
    let mut st := s2
    let mut chals : List Nat := []
    for _ in List.range k do
      let (s3, c) := smFe pN st; st := s3; chals := chals ++ [c]
    s := st
    out := out ++ [mkRec "om_bpoly" case ([k, x] ++ chals) [bPolyMod x chals]]
    case := case + 1
  return out

/-- The shared input vector for all four Type1 blocks: the Fp edge bank then 128 random elements. -/
def shift1Inputs : List Nat := Id.run do
  let mut xs := edgeFp
  let mut s := 0x13
  for _ in List.range 128 do
    let (s1, x) := smFe pN s; s := s1; xs := xs ++ [x]
  return xs

/-- …and for the two Type2 blocks, over Fq. -/
def shift2Inputs : List Nat := Id.run do
  let mut xs := edgeFq
  let mut s := 0x14
  for _ in List.range 128 do
    let (s1, x) := smFe qN s; s := s1; xs := xs ++ [x]
  return xs

def emitBlock (name : String) (xs : List Nat) (f : Nat → Nat) : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  for x in xs do
    out := out ++ [mkRec name case [x] [f x]]
    case := case + 1
  return out

def emitShifts1 : List String :=
  emitBlock "shift1" shift1Inputs shiftType1
  ++ emitBlock "unshift1" shift1Inputs unshiftType1
  ++ emitBlock "shift1b" shift1Inputs (fun x => (type1OfField shift1Fp (toFp x)).val)
  ++ emitBlock "unshift1b" shift1Inputs (fun t => (type1ToField shift1Fp (toFp t)).val)

def emitShifts2 : List String :=
  emitBlock "shift2" shift2Inputs (fun x => (type2OfField shift2Fq (toFq x)).val)
  ++ emitBlock "unshift2" shift2Inputs (fun t => (type2ToField shift2Fq (toFq t)).val)

/-! ## §15 — THE `[Field F]` LAYER, at the deployed field.

`permScalar`, `publicEval` and `ipaB0` are the three definitions the 2026-08-01 cross-impl lane
reported as "unreachable at the deployed field, no CommRing mirror, no differential can reach them".
The stated reason — no `Field (ZMod pN)` instance — was measured false (see this file's header).
They are swept here.

⚑ `permscalar` runs over the SAME inputs as `permof`, from the same seed, so the two records differ
only in which Lean definition produced the output column. `MinaWrapDeferred.permOf` and
`KimchiVerify.permScalar` are two spellings of one `derive_plonk` scalar and NOTHING welds them
(`derivePlonk_perm_is_K5_permScalar` welds `permScalarR`, not `permOf`); this is the first thing that
compares them, and it does it through o1-labs' `perm_scalars` rather than to each other. -/

/-- α^21 in `ZMod pN`, the `PERM_ALPHA0` power `permOf` bakes and `permScalar` takes as `alpha0`.
`powFast` (square-and-multiply) rather than `Monoid.npow`, for the same interpreter reason §8 gives. -/
def alpha21 (a : Nat) : ZMod pN := powFast (toFp a) 21

/-- ⚑ `permscalar` — `KimchiVerify.permScalar` at `ZMod pN`, over `emitPermOf`'s exact sweep. -/
def emitPermScalar : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  let mut s := 7
  for l in permLogs do
    let n := 2 ^ l
    let om := rootOfUnity l
    for bi in List.range edgeFp.length do
      let zeta := edgeFp.getD bi 0
      let alpha := bk edgeFp (bi + 1)
      let beta := bk edgeFp (bi + 2)
      let gamma := bk edgeFp (bi + 3)
      let w := (List.range 15).map (fun i => bk edgeFp (bi + i))
      let sg := (List.range 6).map (fun i => bk edgeFp (bi + 2 * i + 4))
      let zzo := bk edgeFp (bi + 5)
      let v := ofFp (permScalar n (toFp om) (toFp zeta) (toFp beta) (toFp gamma) (alpha21 alpha)
        (w.map toFp) (sg.map toFp) (toFp zzo))
      out := out ++ [mkRec "permscalar" case ([l, om, zeta, alpha, beta, gamma, zzo] ++ w ++ sg) [v]]
      case := case + 1
    for _ in List.range 12 do
      let (s1, zeta) := smFe pN s
      let (s2, alpha) := smFe pN s1
      let (s3, beta) := smFe pN s2
      let (s4, gamma) := smFe pN s3
      let mut st := s4
      let mut w : List Nat := []
      for _ in List.range 15 do
        let (sx, v) := smFe pN st; st := sx; w := w ++ [v]
      let mut sg : List Nat := []
      for _ in List.range 6 do
        let (sx, v) := smFe pN st; st := sx; sg := sg ++ [v]
      let (s5, zzo) := smFe pN st
      s := s5
      let v := ofFp (permScalar n (toFp om) (toFp zeta) (toFp beta) (toFp gamma) (alpha21 alpha)
        (w.map toFp) (sg.map toFp) (toFp zzo))
      out := out ++ [mkRec "permscalar" case ([l, om, zeta, alpha, beta, gamma, zzo] ++ w ++ sg) [v]]
      case := case + 1
  return out

/-- ⚑ `publiceval` — `KimchiVerify.publicEval` at `ZMod pN` against ark-poly's
`evaluate_all_lagrange_coefficients` dotted with the negated public inputs.

⚠ OFF-DOMAIN ONLY, by the SAME predicate on both sides (`x^n ≠ 1`), because at a domain point the
two genuinely disagree: ark-poly detects `Z_H(x) = 0` and returns the indicator vector (giving the
correct `p(ω^i) = −pubᵢ`), while the closed form kimchi and `publicEval` share carries a `(xⁿ − 1)`
factor that is zero there and returns 0 regardless of `pub`. `publicEval` is therefore faithful to
the DEPLOYED verifier and not to the mathematics — a real property of kimchi, pinned by §16 below
and by `public_eval_on_domain_split_is_measured` on the Rust side, not swept under the sweep. -/
def pubLens : List Nat := [0, 1, 2, 5]

def emitPublicEval : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  for l in List.range 6 do
    let ll := l + 1
    let n := 2 ^ ll
    let om := rootOfUnity ll
    for m in pubLens do
      if m ≤ n then
        for bi in List.range edgeFp.length do
          let x := edgeFp.getD bi 0
          if powFast (toFp x) n != 1 then
            let pubs := (List.range m).map (fun i => bk edgeFp (bi + i + 1))
            let v := ofFp (publicEval n (toFp om) (toFp x) (pubs.map toFp))
            out := out ++ [mkRec "publiceval" case ([ll, om, x] ++ pubs) [v]]
            case := case + 1
  let mut s := 0x21
  for _ in List.range 128 do
    let (s1, li) := smBelow s 6
    let ll := li + 1
    let n := 2 ^ ll
    let om := rootOfUnity ll
    let (s2, m0) := smBelow s1 6
    let m := min m0 n
    let (s3, x) := smFe pN s2
    let mut st := s3
    let mut pubs : List Nat := []
    for _ in List.range m do
      let (sx, p) := smFe pN st; st := sx; pubs := pubs ++ [p]
    s := st
    if powFast (toFp x) n != 1 then
      let v := ofFp (publicEval n (toFp om) (toFp x) (pubs.map toFp))
      out := out ++ [mkRec "publiceval" case ([ll, om, x] ++ pubs) [v]]
      case := case + 1
  return out

/-- ⚑ `ipab0` — `KimchiVerify.ipaB0` at `ZMod pN` against `b_poly` composed by kimchi's own
`combined_inner_product` at `polyscale = 1`. First differential that runs `bEval` itself: the
`bpoly` pair diffs `bEvalSq`, and `bEvalSq_eq_bEval` is the only thing joining them. -/
def ipaB0Lens : List Nat := [0, 1, 2, 3, 15, 16]

def emitIpaB0 : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  for k in ipaB0Lens do
    for bi in List.range edgeFp.length do
      let evalscale := edgeFp.getD bi 0
      let zeta := bk edgeFp (bi + 1)
      let zetaw := bk edgeFp (bi + 2)
      let chals := (List.range k).map (fun i => bk edgeFp (bi + i + 3))
      let v := ofFp (ipaB0 (toFp evalscale) (toFp zeta) (toFp zetaw) (chals.map toFp))
      out := out ++ [mkRec "ipab0" case ([k, evalscale, zeta, zetaw] ++ chals) [v]]
      case := case + 1
  let mut s := 0x22
  for _ in List.range 128 do
    let (s1, ki) := smBelow s ipaB0Lens.length
    let k := ipaB0Lens.getD ki 0
    let (s2, evalscale) := smFe pN s1
    let (s3, zeta) := smFe pN s2
    let (s4, zetaw) := smFe pN s3
    let mut st := s4
    let mut chals : List Nat := []
    for _ in List.range k do
      let (sx, c) := smFe pN st; st := sx; chals := chals ++ [c]
    s := st
    let v := ofFp (ipaB0 (toFp evalscale) (toFp zeta) (toFp zetaw) (chals.map toFp))
    out := out ++ [mkRec "ipab0" case ([k, evalscale, zeta, zetaw] ++ chals) [v]]
    case := case + 1
  return out

/-! ## §16 — THE SECOND SPONGE COPY, diffed for the first time.

`sponge_fp`/`sponge_fq`/`challenge` drive `PastaPoseidonFq.SpongeSt`. `frSpongeDigest` and
`frSqueezePair` — what C3 runs on — are built on `PastaPoseidon.Ref.absorbAll`.
`Dregg2/Circuit/Emit/PastaSpongeWeld.lean` proves the two Lean spellings equal at every input
(`two_sponge_copies_agree`, `frSqueezePair_is_two_challenges`, `frSpongeDigest_is_squeeze`); these
three pairs measure that function against o1-labs' `DefaultFrSponge`, which is the half a theorem
between two Lean definitions cannot supply. -/

def emitFrDigest : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  for k in List.range 7 do
    for bi in List.range edgeFp.length do
      let xs := (List.range k).map (fun i => bk edgeFp (bi + i))
      out := out ++ [mkRec "frdigest" case ([k] ++ xs)
        [Dregg2.Circuit.Emit.PastaPoseidon.Ref.hash xs]]
      case := case + 1
  let mut s := 0x23
  for _ in List.range 64 do
    let (s1, k) := smBelow s 9
    let mut st := s1
    let mut xs : List Nat := []
    for _ in List.range k do
      let (sx, x) := smFe pN st; st := sx; xs := xs ++ [x]
    s := st
    out := out ++ [mkRec "frdigest" case ([k] ++ xs)
      [Dregg2.Circuit.Emit.PastaPoseidon.Ref.hash xs]]
    case := case + 1
  return out

def emitFrPair : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  for k in List.range 7 do
    for bi in List.range edgeFp.length do
      let xs := (List.range k).map (fun i => bk edgeFp (bi + i))
      let c := frSqueezePair xs
      out := out ++ [mkRec "frpair" case ([k] ++ xs) [c.1, c.2]]
      case := case + 1
  let mut s := 0x24
  for _ in List.range 64 do
    let (s1, k) := smBelow s 9
    let mut st := s1
    let mut xs : List Nat := []
    for _ in List.range k do
      let (sx, x) := smFe pN st; st := sx; xs := xs ++ [x]
    s := st
    let c := frSqueezePair xs
    out := out ++ [mkRec "frpair" case ([k] ++ xs) [c.1, c.2]]
    case := case + 1
  return out

/-- The number of `absorb_evaluations` points; `frEvalPointOrder.length`, written out so the
harness's `FR_PTS` and this agree by a number that is checked below rather than by coincidence. -/
def frPts : Nat := frEvalPointOrder.length

#guard frPts == 43

def emitFrPhase2 : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  for bi in List.range edgeFp.length do
    let digest := edgeFp.getD bi 0
    let ft1 := bk edgeFp (bi + 1)
    let pz := bk edgeFp (bi + 2)
    let pzw := bk edgeFp (bi + 3)
    let evZ := (List.range frPts).map (fun i => bk edgeFp (bi + i))
    let evZW := (List.range frPts).map (fun i => bk edgeFp (bi + 2 * i + 1))
    out := out ++ [mkRec "frphase2" case ([digest, ft1, pz, pzw] ++ evZ ++ evZW)
      [frSpongeDigest digest ft1 pz pzw evZ evZW]]
    case := case + 1
  let mut s := 0x25
  for _ in List.range 12 do
    let (s1, digest) := smFe pN s
    let (s2, ft1) := smFe pN s1
    let (s3, pz) := smFe pN s2
    let (s4, pzw) := smFe pN s3
    let mut st := s4
    let mut evZ : List Nat := []
    let mut evZW : List Nat := []
    for _ in List.range frPts do
      let (sa, a) := smFe pN st
      let (sb, b) := smFe pN sa
      st := sb
      evZ := evZ ++ [a]
      evZW := evZW ++ [b]
    s := st
    out := out ++ [mkRec "frphase2" case ([digest, ft1, pz, pzw] ++ evZ ++ evZW)
      [frSpongeDigest digest ft1 pz pzw evZ evZW]]
    case := case + 1
  return out

/-! ## §17 — the on-domain split of `publicEval`, PINNED.

The `publiceval` pair sweeps `x ∉ H` because ark-poly and kimchi disagree there. A documented
divergence no gate can see is not a detected one, so the Lean half of the split is asserted here (and
the Rust half in `public_eval_on_domain_split_is_measured`). These run on every invocation of
`scripts/pickles-crossimpl-differential.sh`, because a `#guard` that fails prints an elaboration
error and the driver refuses any vector file containing the word `error`.

⚑ WHAT THIS SAYS: at every domain point `publicEval` returns 0 no matter what the public input is —
faithful to `verifier.rs:332-379`, whose `batch_inversion` maps `0 ↦ 0` and whose `(ζⁿ − 1)` factor
vanishes, and NOT to the Lagrange value `−pubᵢ` that ark-poly returns. It is a property of the
deployed verifier that ζ is assumed to be sponge-derived and therefore off-domain. -/

#guard (List.range 8).all (fun i =>
  publicEval 8 (toFp (rootOfUnity 3)) (powFast (toFp (rootOfUnity 3)) i)
    [(1 : ZMod pN), 2, 3, 4] == 0)

-- non-vacuity: OFF the domain the same call is NOT zero, so the guard above is about the domain and
-- not about `publicEval` being constantly zero.
#guard publicEval 8 (toFp (rootOfUnity 3)) (7 : ZMod pN) [(1 : ZMod pN), 2, 3, 4] != 0

-- and the deployed field really is a `Field`: the inverse `publicEval` needs is the real one.
#guard ((7 : ZMod pN)⁻¹ * 7) == 1

/-! ## §18 — ⚑ THE Fq SIDE OF THE `[Field F]` LAYER.

`permScalar`, `publicEval` and `ipaB0` have NO `[CommRing R]` mirror — unlike `cipR` / `ftEval0R` /
`zkPolyR`, which `cipR_eq` / `ftEval0R_eq` weld to their `[Field F]` originals. Instantiating them
needs a genuine `Field` instance at the modulus. §15 got the Fp half on 2026-08-02 off
`Fact (Nat.Prime pN)`; this is the Fq half, off `Fact (Nat.Prime qN)`
(`Dregg2/Circuit/Emit/PastaScalarPrime.lean`, kernel-checked Lucas/Pratt, no `native_decide`).

⚑ AND Fq IS THE DEPLOYED ONE FOR THE WRAP SIDE. Pallas's SCALAR field is where the Wrap verifier's
ζ, α, β, γ, claimed evaluations and IPA challenges all live — `MinaWrapFtEval0` and
`MinaRealBlockGate` compute at `ZMod qN` for exactly that reason. Until `Fact (Nat.Prime qN)` the
Lean side could not TYPE the shipped `[Field F]` definitions there, so every Fq check in this tree
was a `#guard` on ONE block. These five pairs sweep the function.

⚑ THE ROOT OF UNITY IS DERIVED HERE TOO, AND AT `qN` FOR THE FIRST TIME OVER A SWEEP.
`MinaWrapFtEval0.rootOfUnity` is modulus-parametric; its only previous check at `qN` was one
`#guard` at log2 = 14 against a carried block constant (`MinaWrapFtEval0Weld.lean:154`).
`rootunity_fq` measures it against arkworks at 25 sizes, and the other four feed it as an INPUT
column, so a drift is red at the input rather than silently shared. -/

/-- The `2^log2n`-th root of unity of `ZMod qN`, as a `Nat`. ⚠ Fully qualified on purpose: this
file already has `rootOfUnity` bound to `MinaWrapDeferred`'s `pN`-only spelling. -/
def rootOfUnityFq (log2n : Nat) : Nat :=
  (Dregg2.Bridge.MinaWrapFtEval0.rootOfUnity qN log2n).val

/-- α^21 in `ZMod qN`. -/
def alpha21Fq (a : Nat) : ZMod qN := powFast (toFq a) 21

def emitRootUnityFq : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  for l in List.range 25 do
    out := out ++ [mkRec "rootunity_fq" case [l + 1] [rootOfUnityFq (l + 1)]]
    case := case + 1
  return out

def emitZkpolyFq : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  let mut s := 0x16
  for l in zkLogs do
    let n := 2 ^ l
    let om := rootOfUnityFq l
    for z in edgeFq do
      let v := ofFq (zkPolyR n (toFq om) (toFq z))
      out := out ++ [mkRec "zkpoly_fq" case [l, om, z] [v]]
      case := case + 1
    for _ in List.range 8 do
      let (s1, z) := smFe qN s
      s := s1
      let v := ofFq (zkPolyR n (toFq om) (toFq z))
      out := out ++ [mkRec "zkpoly_fq" case [l, om, z] [v]]
      case := case + 1
  return out

def emitPermScalarFq : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  let mut s := 0x17
  for l in permLogs do
    let n := 2 ^ l
    let om := rootOfUnityFq l
    for bi in List.range edgeFq.length do
      let zeta := edgeFq.getD bi 0
      let alpha := bk edgeFq (bi + 1)
      let beta := bk edgeFq (bi + 2)
      let gamma := bk edgeFq (bi + 3)
      let w := (List.range 15).map (fun i => bk edgeFq (bi + i))
      let sg := (List.range 6).map (fun i => bk edgeFq (bi + 2 * i + 4))
      let zzo := bk edgeFq (bi + 5)
      let v := ofFq (permScalar n (toFq om) (toFq zeta) (toFq beta) (toFq gamma) (alpha21Fq alpha)
        (w.map toFq) (sg.map toFq) (toFq zzo))
      out := out ++ [mkRec "permscalar_fq" case
        ([l, om, zeta, alpha, beta, gamma, zzo] ++ w ++ sg) [v]]
      case := case + 1
    for _ in List.range 12 do
      let (s1, zeta) := smFe qN s
      let (s2, alpha) := smFe qN s1
      let (s3, beta) := smFe qN s2
      let (s4, gamma) := smFe qN s3
      let mut st := s4
      let mut w : List Nat := []
      for _ in List.range 15 do
        let (sx, v) := smFe qN st; st := sx; w := w ++ [v]
      let mut sg : List Nat := []
      for _ in List.range 6 do
        let (sx, v) := smFe qN st; st := sx; sg := sg ++ [v]
      let (s5, zzo) := smFe qN st
      s := s5
      let v := ofFq (permScalar n (toFq om) (toFq zeta) (toFq beta) (toFq gamma) (alpha21Fq alpha)
        (w.map toFq) (sg.map toFq) (toFq zzo))
      out := out ++ [mkRec "permscalar_fq" case
        ([l, om, zeta, alpha, beta, gamma, zzo] ++ w ++ sg) [v]]
      case := case + 1
  return out

def emitPublicEvalFq : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  for l in List.range 6 do
    let ll := l + 1
    let n := 2 ^ ll
    let om := rootOfUnityFq ll
    for m in pubLens do
      if m ≤ n then
        for bi in List.range edgeFq.length do
          let x := edgeFq.getD bi 0
          if powFast (toFq x) n != 1 then
            let pubs := (List.range m).map (fun i => bk edgeFq (bi + i + 1))
            let v := ofFq (publicEval n (toFq om) (toFq x) (pubs.map toFq))
            out := out ++ [mkRec "publiceval_fq" case ([ll, om, x] ++ pubs) [v]]
            case := case + 1
  let mut s := 0x31
  for _ in List.range 128 do
    let (s1, li) := smBelow s 6
    let ll := li + 1
    let n := 2 ^ ll
    let om := rootOfUnityFq ll
    let (s2, m0) := smBelow s1 6
    let m := min m0 n
    let (s3, x) := smFe qN s2
    let mut st := s3
    let mut pubs : List Nat := []
    for _ in List.range m do
      let (sx, p) := smFe qN st; st := sx; pubs := pubs ++ [p]
    s := st
    if powFast (toFq x) n != 1 then
      let v := ofFq (publicEval n (toFq om) (toFq x) (pubs.map toFq))
      out := out ++ [mkRec "publiceval_fq" case ([ll, om, x] ++ pubs) [v]]
      case := case + 1
  return out

def emitIpaB0Fq : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  for k in ipaB0Lens do
    for bi in List.range edgeFq.length do
      let evalscale := edgeFq.getD bi 0
      let zeta := bk edgeFq (bi + 1)
      let zetaw := bk edgeFq (bi + 2)
      let chals := (List.range k).map (fun i => bk edgeFq (bi + i + 3))
      let v := ofFq (ipaB0 (toFq evalscale) (toFq zeta) (toFq zetaw) (chals.map toFq))
      out := out ++ [mkRec "ipab0_fq" case ([k, evalscale, zeta, zetaw] ++ chals) [v]]
      case := case + 1
  let mut s := 0x32
  for _ in List.range 128 do
    let (s1, ki) := smBelow s ipaB0Lens.length
    let k := ipaB0Lens.getD ki 0
    let (s2, evalscale) := smFe qN s1
    let (s3, zeta) := smFe qN s2
    let (s4, zetaw) := smFe qN s3
    let mut st := s4
    let mut chals : List Nat := []
    for _ in List.range k do
      let (sx, c) := smFe qN st; st := sx; chals := chals ++ [c]
    s := st
    let v := ofFq (ipaB0 (toFq evalscale) (toFq zeta) (toFq zetaw) (chals.map toFq))
    out := out ++ [mkRec "ipab0_fq" case ([k, evalscale, zeta, zetaw] ++ chals) [v]]
    case := case + 1
  return out

/-! ## §19 — ⚑ THE THIRD REFERENCE FOR THE LINEARIZATION CONSTANT TERM, and `ft_eval0` composed.

`gateLinConst` is the most defect-prone definition in this tree: it carried a `.take 11` over-count
AND the wrong cube-root endo, and every fixture stayed green because every one of them sat at
`emulSel = 0`. §7 gave it a second reference (kimchi's `PolishToken::evaluate(constant_term)`).
These two pairs give it a THIRD — openmina's, which builds its own linearization and runs its own
`Expr` evaluator with no `PolishToken` anywhere.

⚑ `linconst_om` — `gateLinConst` against openmina's constant term.
⚑ `ft0_om`      — `ftEval0R` (fed `gateLinConst`) against openmina's `plonk_checks::ft_eval0`
                   (which computes ITS constant term internally). The composed object, both sides.

⚠ TWO INPUTS ARE PINNED, NOT SWEPT, and it is the reference that pins them: `scalars::compute`
reads the endo coefficient from `endos::<F>()` and the MDS from `sponge_params()` rather than
taking them as parameters. So both are held at openmina's values here and emitted as INPUT
columns — DERIVED independently on this side (`endoFp` below, `realMds`), so a drift is red at the
input column rather than silently compared. §7's `linconst` keeps the swept version. -/

/-- The base endo coefficient at `Fp`: `GENERATOR^((p−1)/3)` with `GENERATOR = 5`
(`mina_poseidon/src/sponge.rs:110-114`). This is the constant `scalars::compute` installs as
`Constants::endo_coefficient` — the BASE endo, a cube root of unity, and **not** `er`
(`ScalarChallenge::to_field`'s scalar endo). Conflating the two was half the historical
`gateLinConst` defect; here they cannot be conflated, because this value is compared byte-for-byte
against `endos::<Fp>().0` at every record. -/
def endoFp : ZMod pN := powFast ((5 : Nat) : ZMod pN) ((pN - 1) / 3)

-- It really is a cube root of unity — the property `er` does not have.
#guard endoFp ^ 3 == (1 : ZMod pN)

/-- `linconst_om`'s input columns: α β γ endo, the 9 MDS entries, then coeff/w/wNext/sel. -/
def ctIns (a b g : Nat) (coeff w wn sel : List Nat) : List Nat :=
  [a, b, g, endoFp.val] ++ realMds.flatten ++ coeff ++ w ++ wn ++ sel

/-- ⚑ `linconst_om`. Block A is §7's structured half verbatim, so the two references are compared
on identical data; block B turns each gate on IN TURN with a nonzero random selector over random
witness data — the regime every pre-existing fixture missed; block C makes all six live at once. -/
def emitLinconstOm : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  -- A: one selector hot at a time, plus all-hot, over the edge bank
  for hot in List.range 7 do
    for bi in List.range edgeFp.length do
      let sel := (List.range 6).map (fun i => if hot = 6 || hot = i then 1 else 0)
      let coeff := (List.range 15).map (fun i => bk edgeFp (bi + i))
      let w := (List.range 15).map (fun i => bk edgeFp (bi + 2 * i + 1))
      let wn := (List.range 15).map (fun i => bk edgeFp (bi + 3 * i + 5))
      let a := bk edgeFp (bi + 1)
      let b := bk edgeFp (bi + 2)
      let g := bk edgeFp (bi + 4)
      let v := ofFp (gateLinConst (linGate a endoFp.val realMds coeff w wn sel))
      out := out ++ [mkRec "linconst_om" case (ctIns a b g coeff w wn sel) [v]]
      case := case + 1
  let mut s := 0x21
  -- B: ⚑ each gate NONZERO IN TURN over RANDOM data. ⚠ DRAW ORDER: coeff, w, wn, sel-value,
  -- alpha, beta, gamma — exactly `pair_linconst_om`'s block B.
  for gate in List.range 6 do
    for _ in List.range 24 do
      let mut st := s
      let mut coeff : List Nat := []
      for _ in List.range 15 do
        let (s1, v) := smFe pN st; st := s1; coeff := coeff ++ [v]
      let mut w : List Nat := []
      for _ in List.range 15 do
        let (s1, v) := smFe pN st; st := s1; w := w ++ [v]
      let mut wn : List Nat := []
      for _ in List.range 15 do
        let (s1, v) := smFe pN st; st := s1; wn := wn ++ [v]
      let (s1, sv0) := smFe pN st
      let sv := if sv0 = 0 then 1 else sv0
      let (s2, a) := smFe pN s1
      let (s3, b) := smFe pN s2
      let (s4, g) := smFe pN s3
      s := s4
      let sel := (List.range 6).map (fun i => if i = gate then sv else 0)
      let v := ofFp (gateLinConst (linGate a endoFp.val realMds coeff w wn sel))
      out := out ++ [mkRec "linconst_om" case (ctIns a b g coeff w wn sel) [v]]
      case := case + 1
  -- C: everything random, every selector live at once
  for _ in List.range 192 do
    let mut st := s
    let mut coeff : List Nat := []
    for _ in List.range 15 do
      let (s1, v) := smFe pN st; st := s1; coeff := coeff ++ [v]
    let mut w : List Nat := []
    for _ in List.range 15 do
      let (s1, v) := smFe pN st; st := s1; w := w ++ [v]
    let mut wn : List Nat := []
    for _ in List.range 15 do
      let (s1, v) := smFe pN st; st := s1; wn := wn ++ [v]
    let mut sel : List Nat := []
    for _ in List.range 6 do
      let (s1, v) := smFe pN st; st := s1; sel := sel ++ [v]
    let (s1, a) := smFe pN st
    let (s2, b) := smFe pN s1
    let (s3, g) := smFe pN s2
    s := s3
    let v := ofFp (gateLinConst (linGate a endoFp.val realMds coeff w wn sel))
    out := out ++ [mkRec "linconst_om" case (ctIns a b g coeff w wn sel) [v]]
    case := case + 1
  return out

/-! ### `ft0_om` — the composed `ft_eval0`.

⚠ ζ IS NUDGED off `ftEval0R`'s two witnessed-inverse poles (`ζ = 1` and `ζ = ω^{n−3}`), by the same
deterministic `+1` walk on both sides. Those are the points where `denomInv` does not exist; they
are not a regime a value pair can compare, and saying so is cheaper than a silent skip. -/

def ft0Logs : List Nat := [2, 3, 4, 6, 8]

/-- The deterministic ζ walk. Fuel 8; the Rust side asserts the loop never runs that long. -/
def nudgeZeta (omnm3 : ZMod pN) : Nat → ZMod pN → ZMod pN
  | 0, z => z
  | k + 1, z => if z = 1 ∨ z = omnm3 then nudgeZeta omnm3 k (z + 1) else z

/-- ⚑ `ft0_om`: `KimchiVerify.ftEval0R` over `gateLinConst` against openmina's `ft_eval0` over its
own internally-computed constant term. ω and the seven coset shifts are DERIVED here
(`rootOfUnity` / `tickShiftsFp`) and emitted as input columns, not read back from the Rust. -/
def emitFt0Om : List String := Id.run do
  let mut out : List String := []
  let mut case := 0
  let mut s := 0x22
  for l in ft0Logs do
    let n := 2 ^ l
    let om := rootOfUnity l
    let omnm3 := powFast (toFp om) (n - 3)
    let sh := tickShiftsFp l
    -- ⚠ `c` is an ARGUMENT, not a capture: a `do`-block closure freezes `let mut case` at its
    -- definition site, which silently numbered every record of a domain identically.
    let mk : Nat → Nat → Nat → Nat → Nat → List Nat → List Nat → List Nat → List Nat →
        Nat → Nat → Nat → List Nat → String :=
      fun c zeta0 a b g coeff w wn sg zz zzw pz sel =>
        let zeta := nudgeZeta omnm3 8 (toFp zeta0)
        let lct := gateLinConst (linGate a endoFp.val realMds coeff w wn sel)
        let dinv := ((zeta - omnm3) * (zeta - 1))⁻¹
        let ft := ftEval0R n (toFp om) zeta (toFp b) (toFp g)
          (powFast (toFp a) 21) (powFast (toFp a) 22) (powFast (toFp a) 23)
          (w.map toFp) (sg.map toFp) sh (toFp zz) (toFp zzw) (toFp pz) lct dinv
        mkRec "ft0_om" c
          ([l, om, zeta.val, a, b, g, endoFp.val] ++ realMds.flatten ++ sh.map ZMod.val
            ++ coeff ++ w ++ wn ++ sg ++ [zz, zzw, pz] ++ sel) [ofFp ft]
    for bi in List.range edgeFp.length do
      let coeff := (List.range 15).map (fun i => bk edgeFp (bi + i))
      let w := (List.range 15).map (fun i => bk edgeFp (bi + 2 * i + 1))
      let wn := (List.range 15).map (fun i => bk edgeFp (bi + 3 * i + 5))
      let sg := (List.range 6).map (fun i => bk edgeFp (bi + i + 2))
      let sel := (List.range 6).map (fun i => bk edgeFp (bi + i + 1))
      out := out ++ [mk case (bk edgeFp (bi + 9)) (bk edgeFp (bi + 1)) (bk edgeFp (bi + 2))
        (bk edgeFp (bi + 4)) coeff w wn sg (bk edgeFp (bi + 6)) (bk edgeFp (bi + 7))
        (bk edgeFp (bi + 8)) sel]
      case := case + 1
    for _ in List.range 12 do
      -- ⚠ DRAW ORDER: coeff, w, wn, s, sel, ζ, α, β, γ, z(ζ), z(ζω), p(ζ).
      let mut st := s
      let mut coeff : List Nat := []
      for _ in List.range 15 do
        let (s1, v) := smFe pN st; st := s1; coeff := coeff ++ [v]
      let mut w : List Nat := []
      for _ in List.range 15 do
        let (s1, v) := smFe pN st; st := s1; w := w ++ [v]
      let mut wn : List Nat := []
      for _ in List.range 15 do
        let (s1, v) := smFe pN st; st := s1; wn := wn ++ [v]
      let mut sg : List Nat := []
      for _ in List.range 6 do
        let (s1, v) := smFe pN st; st := s1; sg := sg ++ [v]
      let mut sel : List Nat := []
      for _ in List.range 6 do
        let (s1, v) := smFe pN st; st := s1; sel := sel ++ [v]
      let (s1, zeta0) := smFe pN st
      let (s2, a) := smFe pN s1
      let (s3, b) := smFe pN s2
      let (s4, g) := smFe pN s3
      let (s5, zz) := smFe pN s4
      let (s6, zzw) := smFe pN s5
      let (s7, pz) := smFe pN s6
      s := s7
      out := out ++ [mk case zeta0 a b g coeff w wn sg zz zzw pz sel]
      case := case + 1
  return out

/-! ## §14 — the whole emission, in the harnesses' order. -/

def allRecords : List String :=
  emitEndo ++ emitEndoFq ++ emitEndoLift
    ++ emitBpoly "bpoly" false ++ emitBpoly "bpolymod" true
    ++ emitCip ++ emitLinconst ++ emitZkpoly ++ emitRootUnity
    ++ emitPermOf ++ emitPermScalar
    ++ emitShifts
    ++ emitSponge "sponge_fp" fpParams edgeFp 48 8
    ++ emitSponge "sponge_fq" fqParams edgeFq 0 0
    ++ emitChallenge ++ emitEmulConsts
    -- the `[Field F]` layer, reachable since `PastaBasePrime` installed `Fact (Nat.Prime pN)`
    ++ emitPublicEval ++ emitIpaB0
    -- the SECOND sponge copy — the one the Fr-sponge weld is built on
    ++ emitFrDigest ++ emitFrPair ++ emitFrPhase2
    -- ⚑ the Fq side of the `[Field F]` layer, reachable since `PastaScalarPrime` installed
    -- `Fact (Nat.Prime qN)`. Pallas' SCALAR field is where the Wrap verifier computes.
    ++ emitRootUnityFq ++ emitZkpolyFq ++ emitPermScalarFq ++ emitPublicEvalFq ++ emitIpaB0Fq
    -- the openmina half
    ++ emitOmEndo ++ emitOmBpoly ++ emitShifts1 ++ emitShifts2
    -- ⚑ the THIRD reference for the linearization constant term, and `ft_eval0` composed
    ++ emitLinconstOm ++ emitFt0Om

def emitAll : IO Unit := do
  let h ← IO.getStdout
  for r in allRecords do
    h.putStrLn r

end Dregg2.ConformanceVectors

def main : IO Unit := Dregg2.ConformanceVectors.emitAll
