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

⚠ WHAT IS UNEVALUABLE, and it is a finding. `KimchiVerify.publicEval`, `ftEval0`, `permScalar`,
`combinedInnerProduct`, `zkPoly`, `ipaB0` and `ftComm` are declared under
`variable {F : Type} [Field F]`, and this tree has NO `Field (ZMod pN)` instance (no in-kernel
primality proof of the 255-bit Pasta prime; `native_decide` forbidden). They cannot be instantiated
at the deployed field AT ALL, so no differential can reach them. The ones with a CommRing mirror
(`cipR`, `zkPolyR`, `ftEval0R`) are reached through the mirror. `publicEval`, `permScalar` and
`ipaB0` have NO mirror and are named as uncovered by `scripts/pickles-crossimpl-differential.sh`.
-/
import Dregg2.Circuit.Emit.KimchiVerify
import Dregg2.Bridge.MinaWrapDeferred
import Dregg2.Bridge.TickShifts
import Dregg2.Circuit.Emit.PastaPoseidonFq

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Dregg2.ConformanceVectors

open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.KimchiVerify
  (endoMap bEvalSq cipR zkPolyR gateLinConst GateEvals)
open Dregg2.Bridge.MinaWrapDeferred (endoLift bPolyMod rootOfUnity permOf)
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

NOT `KimchiVerify.permScalar`: that one is declared under `variable {F : Type} [Field F]` and the
tree has no `Field (ZMod pN)` instance, so it is UNEVALUABLE at the deployed field and cannot be
differentially tested at all. `permOf` is dregg's `Nat`-with-explicit-modulus copy of the same
`derive_plonk` scalar, it IS evaluable, and it is the copy the Wrap public input goes through.

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

/-! ## §13 — the whole emission, in the harness's order. -/

def allRecords : List String :=
  emitEndo ++ emitEndoFq ++ emitEndoLift
    ++ emitBpoly "bpoly" false ++ emitBpoly "bpolymod" true
    ++ emitCip ++ emitLinconst ++ emitZkpoly ++ emitRootUnity ++ emitPermOf
    ++ emitShifts
    ++ emitSponge "sponge_fp" fpParams edgeFp 48 8
    ++ emitSponge "sponge_fq" fqParams edgeFq 0 0
    ++ emitChallenge ++ emitEmulConsts

def emitAll : IO Unit := do
  let h ← IO.getStdout
  for r in allRecords do
    h.putStrLn r

end Dregg2.ConformanceVectors

def main : IO Unit := Dregg2.ConformanceVectors.emitAll
