/-
# `Dregg2.Circuit.Emit.MinaFinalizeScalarsProg` — the finalize-scalars PROGRAM: value space,
straight-line ops, denotation, and the §5 references. **Now including stage 11, the
gate-linearization leaf that closes the `LCT` port.**

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** Every op below is authored here and lowered by
`EffectLower.lowerAir` (in `MinaFinalizeScalars.lean`, which imports this file and carries the
tables, the legs, the descriptor and the censuses). Rust parses the emitted descriptor and runs
the deployed prover; it authors no constraint. House Law #1.

## Why the split

This file is the PROGRAM half of what was one file: the table renderer
(`FsAllocRender.lean`) must import the program to run `AirColumnAlloc.allocate` on it, and it
cannot import the table file whose literal tables are exactly the thing being regenerated —
mid-render they are stale and every `by decide` there would refuse. Program here, layout there,
renderer against this file only. Same namespace on purpose: importers of
`MinaFinalizeScalars` see one module surface.

## ⚑⚑ STAGE 11 — THE GATE-LINEARIZATION LEAF (the `LCT` port, CLOSED)

Through `d09e89817` the linearization constant term was a PI-pinned PORT welded to NOTHING: the
`lct-shift` adversarial trace — `LCT` bumped, the cip claim recomputed — PROVED AND VERIFIED,
a one-parameter family of accepting cip claims (`cipActualOf` is affine in `LCT`). Stage 11 is
the named closure: `KimchiVerify.gateLinConst`'s SIX transcribed bodies — generic (2 constraints),
Poseidon (15), complete_add (7), varbasemul (21), endomul `.take 11`, endomul_scalar (11) —
rendered as 744 further ops over the same 86 welded eval blocks, with the α-combination as a
Horner walk (`hornerAlpha`, ring-equal to `KimchiVerify.alphaCombine`) and each body weighted by
the wire's own selector eval. The closing `eq` op forces the `LCT` claim block against the
derived value, which is what turns the `lct-shift` family from ACCEPTED into REFUSED. `LCT` is
now a CLAIM in exactly `CIP_CLAIM`/`PERM_CLAIM`'s standing: published, decoded, and compared by
gate against the trace's own derivation.

⚠ The measured price against the brief's estimate: the brief priced this leaf at "~320 more ops";
the transcription lands at **745** (631 body ops + 100 Horner ops + 5 selector weights + 5 sum
adds + the closing eq + 3 shared-source folds' extras), because the five custom-gate bodies are
65 constraints whose every multiply is one row. The estimate under-counted the ARITHMETIC this
time, not the pin surface — no new PI block exists (the six selectors, 15+15 witness, 15
coefficient columns were already ports of stages 0–10), and the only new inputs are 16 constant
blocks (endo, the nine `fq_kimchi` MDS entries, the three `EndomulScalar` quotient constants,
and the literals 3/6/11).

## ⚠ THE SIDE, SAID ONCE MORE

Wrap-side: `ZMod qN`, domain `2^14`, Tock shifts, the 47-entry `es` order
`[bp0, bp1, public, ft, z, sel(6), w(15), coeff(15), σ(6)]`. NOT `KimchiStepMainCore`'s
`ftProgOf` (`FT_LOG2N = 16`, Tick, hardcoded `pN`). The endo constant is the BASE endomorphism
eigenvalue `5^((q−1)/3)` (`vi.endo`), NOT `er` — the exact two-part defect
`Bridge/MinaWrapFtEval0Weld` §2b-head closed on 2026-08-01.
-/
import Dregg2.Circuit.Emit.KimchiVerify
import Dregg2.Circuit.Emit.PicklesFinalize
import Dregg2.Circuit.Emit.AirColumnAlloc

namespace Dregg2.Circuit.Emit.MinaFinalizeScalars

open Dregg2.Circuit.Emit.AirColumnAlloc (SsaOp)
open Dregg2.Circuit.Emit.KimchiVerify (PERMUTS ftEval0R cipR zkPolyR GateEvals gateLinConst)
open Dregg2.Circuit.Emit.PicklesFinalize (permScalarR)

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! ## §1 — THE VALUE SPACE.

Values are `Nat` indices. `0 … NPI−1` are the PI-pinned input blocks, `NPI … NIN−1` the
constant blocks, and op `i` defines value `NIN + i` — every op defines exactly one fresh value,
so the program is SSA by construction and `dst` is never written down (a hand-numbered `dst`
table at 1046 ops is 1046 chances to alias two values). -/

-- The 43 evaluation columns at ζ, wire order `[z] ++ sel(6) ++ w(15) ++ coeff(15) ++ s(6)`.
def vEZ (k : Nat) : Nat := k
-- …and at ζω.
def vEW (k : Nat) : Nat := 43 + k
/-- `ft_eval1` — tape element 2. -/
def vFT1 : Nat := 86
/-- `public_evals[0]` (ζ) — tape element 3. -/
def vPUBZ : Nat := 87
/-- `public_evals[1]` (ζω) — tape element 4. -/
def vPUBW : Nat := 88
/-- β, RAW (low-128; limbs 16..31 zero-pinned in-leaf). -/
def vBETA : Nat := 89
/-- γ, RAW. -/
def vGAMMA : Nat := 90
/-- α, endo-MAPPED (the lift instance's output). -/
def vALPHA : Nat := 91
/-- ζ, endo-MAPPED. -/
def vZETA : Nat := 92
/-- ξ (polyscale), endo-MAPPED. -/
def vXI : Nat := 93
/-- r (evalscale), endo-MAPPED. -/
def vRSQ : Nat := 94
/-- The four b-poly prefix PORTS — `es[0..1]` at both points. Never recomputed here. -/
def vBP0Z : Nat := 95
def vBP1Z : Nat := 96
def vBP0W : Nat := 97
def vBP1W : Nat := 98
/-- The claimed `combined_inner_product`, DECODED. -/
def vCIPCL : Nat := 99
/-- The claimed `perm`, DECODED. -/
def vPERMCL : Nat := 100
/-- The witnessed inverse of `(ζ − ω^{n−3})(ζ − 1)`. -/
def vDINV : Nat := 101
/-- ⚑ THE LINEARIZATION-CONSTANT CLAIM (through `d09e89817`: the open PORT). Stage 11's closing
`eq` gate now forces this block against the in-AIR `gateLinConst` derivation, so it stands
exactly where `vCIPCL`/`vPERMCL` stand: a published claim the trace's own arithmetic refuses
when it lies. The `lct-shift` family that used to ACCEPT is refused at this gate. -/
def vLCT : Nat := 102

/-- The number of PI-pinned input blocks. -/
def NPI_BLOCKS : Nat := 103

-- The constant blocks, forced by `.first` window pins and carried like any value.
def vONE : Nat := 103
def vZERO : Nat := 104
/-- `ω^{n−3}`, `ω^{n−2}`, `ω^{n−1}` — `zkPolyR`'s three roots, as constants of the fixed
Wrap domain (`log2n = 14`). -/
def vOM3 : Nat := 105
def vOM2 : Nat := 106
def vOM1 : Nat := 107
/-- The seven Tock coset shifts. -/
def vSH (i : Nat) : Nat := 108 + i
/-- ⚑ `vi.endo` — the BASE endomorphism eigenvalue `5^((q−1)/3)`, the endomul body's only config
read. NOT `er` (the scalar-challenge endo): conflating the two cube roots was half of the
2026-08-01 `gateLinConst` defect, and the AIR file derives the literal (`ENDO_Q`) rather than
carrying it. -/
def vENDO : Nat := 115
/-- The `fq_kimchi` Poseidon MDS, row-major flat — `Constants::mds` of the field the Wrap
circuit is over (`PastaPoseidonFq.mdsQ`), read by the 15 Poseidon lanes. -/
def vMDS (i : Nat) : Nat := 116 + i
/-- The three `EndomulScalar` quotient constants `11/6, −5/2, 2/3` — descriptor literals whose
ring checks (`6·cA = 11`, `2·cB = −5`, `3·cC = 2` — `endomulScalarConstsOk`'s content) are named
theorems in the AIR file, the same witnessed-quotient device as `vDINV`. -/
def vCA : Nat := 125
def vCB : Nat := 126
def vCC : Nat := 127
/-- Small literals the `EndomulScalar` `df`/crumb polynomials read. -/
def vC3 : Nat := 128
def vC6 : Nat := 129
def vC11 : Nat := 130

/-- Values that pre-exist the program: 103 PI blocks + 28 constants. -/
def NIN_VALS : Nat := 131

/-! ## §2 — THE PROGRAM.

Four op kinds. `eq` defines a fresh (dead) value so that "op `i` defines value `NIN_VALS + i`"
stays uniform; its gates read its two sources and write nothing. -/

inductive FKind where
  | mul | add | sub | eq
  deriving Repr, DecidableEq

/-- One op: the kind and the two source VALUES. The destination is implicit (`NIN_VALS + i`). -/
structure FOp where
  k : FKind
  x : Nat
  y : Nat
  deriving Repr, DecidableEq

/-- The builder state: ops emitted so far. `emit` returns the value the op defines. -/
abbrev BB := List FOp

@[inline] def emitOp (b : BB) (k : FKind) (x y : Nat) : BB × Nat :=
  (b ++ [⟨k, x, y⟩], NIN_VALS + b.length)

def bMul (b : BB) (x y : Nat) : BB × Nat := emitOp b .mul x y
def bAdd (b : BB) (x y : Nat) : BB × Nat := emitOp b .add x y
def bSub (b : BB) (x y : Nat) : BB × Nat := emitOp b .sub x y
def bEq (b : BB) (x y : Nat) : BB × Nat := emitOp b .eq x y

/-- Wire-column helpers, `MinaWrapFtEval0`'s own offsets: `w` columns start at 7, σ at 37. -/
def wCol (i : Nat) : Nat := vEZ (7 + i)
def sCol (i : Nat) : Nat := vEZ (37 + i)
/-- The six gate selectors at ζ — wire columns 1..6 (`MinaWrapFtEval0.IDX_SEL`), in order
`[generic, poseidon, complete_add, mul, emul, endomul_scalar]`. -/
def selCol (i : Nat) : Nat := vEZ (1 + i)
/-- The 15 coefficient evals at ζ — wire columns 22..36. -/
def cCol (i : Nat) : Nat := vEZ (22 + i)
/-- The 15 witness evals at ζω — what the Poseidon/varbasemul/endomul bodies read as `wNext`. -/
def wnCol (i : Nat) : Nat := vEW (7 + i)

/-- The Wrap domain: `log2n = 14`. -/
def LOG2N : Nat := 14
def DOMN : Nat := 2 ^ LOG2N

/-! ### Stage 0 — `ζ^n` by 14 squarings. Returns (ops, ζ^{2^14}). -/

def sqChain (b : BB) (x : Nat) : Nat → BB × Nat
  | 0 => (b, x)
  | n + 1 =>
      let (b1, x2) := bMul b x x
      sqChain b1 x2 n

def stZN (b : BB) : BB × Nat := sqChain b vZETA LOG2N

/-! ### Stage 1 — `zkPolyR`, the C5 denominator, the witnessed inverse, `ζⁿ − 1`. -/

structure St1 where
  zkp : Nat
  d3 : Nat        -- ζ − ω^{n−3}
  zm1 : Nat       -- ζ − 1
  den : Nat       -- d3 · zm1
  zeta1m1 : Nat   -- ζⁿ − 1

def stZk (b : BB) (zn : Nat) : BB × St1 :=
  let (b, d3) := bSub b vZETA vOM3
  let (b, d2) := bSub b vZETA vOM2
  let (b, d1) := bSub b vZETA vOM1
  let (b, zk0) := bMul b d3 d2
  let (b, zkp) := bMul b zk0 d1
  let (b, zm1) := bSub b vZETA vONE
  let (b, den) := bMul b d3 zm1
  let (b, dchk) := bMul b den vDINV
  let (b, _) := bEq b dchk vONE
  let (b, zeta1m1) := bSub b zn vONE
  (b, ⟨zkp, d3, zm1, den, zeta1m1⟩)

/-! ### Stage 2 — the α ladder to α²¹, α²², α²³. -/

structure StA where
  a21 : Nat
  a22 : Nat
  a23 : Nat

def stAlpha (b : BB) : BB × StA :=
  let (b, a2) := bMul b vALPHA vALPHA
  let (b, a4) := bMul b a2 a2
  let (b, a5) := bMul b a4 vALPHA
  let (b, a10) := bMul b a5 a5
  let (b, a20) := bMul b a10 a10
  let (b, a21) := bMul b a20 vALPHA
  let (b, a22) := bMul b a21 vALPHA
  let (b, a23) := bMul b a22 vALPHA
  (b, ⟨a21, a22, a23⟩)

/-! ### Stage 3 — the C5 NUMERATOR fold, and its six per-σ factors (shared with `perm`).

`init = (w₆ + γ)·z(ζω)·α²¹·zkp`, then six rounds of `acc · (β·sᵢ + wᵢ + γ)`. The six factors are
returned so stage 9 REUSES them — `permScalarR`'s fold factor is the same value, and computing it
twice would be 18 wasted rows. -/

def numerRound (bf : BB × Nat × List Nat) (i : Nat) : BB × Nat × List Nat :=
  let (b, acc, fs) := bf
  let (b, bs) := bMul b vBETA (sCol i)
  let (b, bsw) := bAdd b bs (wCol i)
  let (b, f) := bAdd b bsw vGAMMA
  let (b, acc') := bMul b acc f
  (b, acc', fs ++ [f])

def stNumer (b : BB) (a : StA) (s1 : St1) : BB × Nat × List Nat :=
  let (b, t0) := bAdd b (wCol 6) vGAMMA
  let (b, i1) := bMul b t0 (vEW 0)
  let (b, i2) := bMul b i1 a.a21
  let (b, i3) := bMul b i2 s1.zkp
  (List.range (PERMUTS - 1)).foldl numerRound (b, i3, [])

/-! ### Stage 4/5 — the public subtraction and the C5 DENOMINATOR fold. -/

def denomRound (bp : BB × Nat × Nat) (i : Nat) : BB × Nat × Nat :=
  let (b, bz, acc) := bp
  let (b, u1) := bMul b bz (vSH i)
  let (b, u2) := bAdd b u1 vGAMMA
  let (b, u3) := bAdd b u2 (wCol i)
  let (b, acc') := bMul b acc u3
  (b, bz, acc')

def stDenom (b : BB) (a : StA) (s1 : St1) : BB × Nat :=
  let (b, bz) := bMul b vBETA vZETA
  let (b, e1) := bMul b a.a21 s1.zkp
  let (b, e2) := bMul b e1 (vEZ 0)
  let (b, _, acc) := (List.range PERMUTS).foldl denomRound (b, bz, e2)
  (b, acc)

/-! ### Stage 7 — the zk-row numerator and `ft_eval0` itself.

⚠ `ft_eval0`'s closing subtraction reads the CLAIM block `vLCT` — deliberately, unchanged from
v1: the claim is what upstream's `ft_eval0` subtracts, and stage 11's eq gate is what forces the
claim to BE the gate linearization. Reading the derived value here instead would be equivalent
under that gate and would hide the claim's role. -/

def stFt (b : BB) (a : StA) (s1 : St1) (numer pubZ denom : Nat) : BB × Nat :=
  let (b, afterPub) := bSub b numer pubZ
  let (b, afterDenom) := bSub b afterPub denom
  let (b, n1) := bMul b s1.zeta1m1 a.a22
  let (b, n1b) := bMul b n1 s1.d3
  let (b, n2) := bMul b s1.zeta1m1 a.a23
  let (b, n2b) := bMul b n2 s1.zm1
  let (b, ns) := bAdd b n1b n2b
  let (b, omz) := bSub b vONE (vEZ 0)
  let (b, nsz) := bMul b ns omz
  let (b, nd) := bMul b nsz vDINV
  let (b, azk) := bAdd b afterDenom nd
  let (b, ft0) := bSub b azk vLCT
  (b, ft0)

/-! ### Stage 9 — `permScalarR`, reusing stage 3's six factors, and its forcing. -/

def stPerm (b : BB) (a : StA) (s1 : St1) (factors : List Nat) : BB :=
  let (b, p1) := bMul b (vEW 0) vBETA
  let (b, p2) := bMul b p1 a.a21
  let (b, p3) := bMul b p2 s1.zkp
  let (b, p) := factors.foldl (fun (bp : BB × Nat) f =>
    let (b, acc) := bp
    bMul b acc f) (b, p3)
  let (b, pneg) := bSub b vZERO p
  (bEq b vPERMCL pneg).1

/-! ### Stage 10 — the 47-entry ξ-fold (C8), Horner from the top, and its forcing.

`es` index `k`'s ζ-column and ζω-column values, with the in-AIR `ft0` in slot 3. -/

def esZ (ft0 : Nat) (k : Nat) : Nat :=
  if k = 0 then vBP0Z else if k = 1 then vBP1Z else if k = 2 then vPUBZ
  else if k = 3 then ft0 else vEZ (k - 4)

def esW (k : Nat) : Nat :=
  if k = 0 then vBP0W else if k = 1 then vBP1W else if k = 2 then vPUBW
  else if k = 3 then vFT1 else vEW (k - 4)

/-- The number of `es` entries on the Wrap side: 2 prefix + public + ft + 43 columns. -/
def NES : Nat := 47

/-- One Horner entry: `t_k = ez_k + r·ew_k`. -/
def esTerm (b : BB) (ft0 k : Nat) : BB × Nat :=
  let (b, m) := bMul b vRSQ (esW k)
  bAdd b (esZ ft0 k) m

/-- The Horner walk from entry `NES−1` down to 0: `acc ← acc·ξ + t_k`. -/
def cipHorner (b : BB) (ft0 : Nat) (acc : Nat) : Nat → BB × Nat
  | 0 => (b, acc)
  | j + 1 =>
      let (b, am) := bMul b acc vXI
      let (b, t) := esTerm b ft0 j
      let (b, acc') := bAdd b am t
      cipHorner b ft0 acc' j

def stCip (b : BB) (ft0 : Nat) : BB :=
  let (b, t46) := esTerm b ft0 (NES - 1)
  let (b, cip) := cipHorner b ft0 t46 (NES - 1)
  (bEq b vCIPCL cip).1

/-! ### ⚑⚑ Stage 11 — THE GATE-LINEARIZATION LEAF: `gateLinConst`'s six transcribed bodies.

The reference is `KimchiVerify.gateLinConst` — the WHOLE linearization constant term
(`linearization.rs:364`: `index_terms = []`). Each body's constraint list is rendered in the
reference's own emission order; the α-combination `Σᵢ αⁱ·cᵢ` is a Horner walk from the head
(`hornerAlpha`, ring-equal to `alphaCombine`); each of the five custom bodies is weighted by its
selector eval and summed onto the selector-scaled generic gate. The closing `eq` op forces the
`LCT` claim against the derived sum — the weld that refuses the `lct-shift` family. -/

/-- `Σ αⁱ·csᵢ` as ops — Horner from the head (`h(c :: rest) = c + α·h(rest)`), ring-equal to
`KimchiVerify.alphaCombine`. `n` constraints cost `2(n−1)` ops. -/
def hornerAlpha (b : BB) : List Nat → BB × Nat
  | [] => (b, vZERO)
  | [c] => (b, c)
  | c :: rest =>
      let (b, r) := hornerAlpha b rest
      let (b, m) := bMul b vALPHA r
      bAdd b c m

/-- The double-generic gate, selector-scaled and α-combined
(`KimchiVerify.genericGateConstraint`): `genSel·(constraint1 + α·constraint2)` with
`constraintₖ = c₅ₖ·w₃ₖ + c₅ₖ₊₁·w₃ₖ₊₁ + c₅ₖ₊₂·w₃ₖ₊₂ + c₅ₖ₊₃·(w₃ₖ·w₃ₖ₊₁) + c₅ₖ₊₄`. 21 ops. -/
def stGenericBody (b : BB) : BB × Nat :=
  let (b, m0) := bMul b (cCol 0) (wCol 0)
  let (b, m1) := bMul b (cCol 1) (wCol 1)
  let (b, a1) := bAdd b m0 m1
  let (b, m2) := bMul b (cCol 2) (wCol 2)
  let (b, a2) := bAdd b a1 m2
  let (b, w01) := bMul b (wCol 0) (wCol 1)
  let (b, m3) := bMul b (cCol 3) w01
  let (b, a3) := bAdd b a2 m3
  let (b, con1) := bAdd b a3 (cCol 4)
  let (b, n0) := bMul b (cCol 5) (wCol 3)
  let (b, n1) := bMul b (cCol 6) (wCol 4)
  let (b, e1) := bAdd b n0 n1
  let (b, n2) := bMul b (cCol 7) (wCol 5)
  let (b, e2) := bAdd b e1 n2
  let (b, w34) := bMul b (wCol 3) (wCol 4)
  let (b, n3) := bMul b (cCol 8) w34
  let (b, e3) := bAdd b e2 n3
  let (b, con2) := bAdd b e3 (cCol 9)
  let (b, am) := bMul b vALPHA con2
  let (b, cc) := bAdd b con1 am
  bMul b (selCol 0) cc

/-- Kimchi Poseidon S-box `x⁷` — 4 multiplies. -/
def bSbox (b : BB) (x : Nat) : BB × Nat :=
  let (b, x2) := bMul b x x
  let (b, x3) := bMul b x2 x
  let (b, x6) := bMul b x3 x3
  bMul b x6 x

/-- One Poseidon lane (`KimchiVerify.poseidonLaneConstraint`): `target − (rc + mdsRow·sboxed)`.
`j` is the MDS row; `s0 s1 s2` are the ALREADY-SBOXED source values. 7 ops. -/
def bPosLane (b : BB) (j rc s0 s1 s2 target : Nat) : BB × Nat :=
  let (b, t0) := bMul b (vMDS (3 * j)) s0
  let (b, t1) := bMul b (vMDS (3 * j + 1)) s1
  let (b, t2) := bMul b (vMDS (3 * j + 2)) s2
  let (b, a0) := bAdd b rc t0
  let (b, a1) := bAdd b a0 t1
  let (b, a2) := bAdd b a1 t2
  bSub b target a2

/-- The Poseidon body: the 15 constraints of `KimchiVerify.poseidonConstraints` in emission
order (sources `s0=[w₀,w₁,w₂] s1=[w₆,w₇,w₈] s2=[w₉,w₁₀,w₁₁] s3=[w₁₂,w₁₃,w₁₄] s4=[w₃,w₄,w₅]`,
the last three targets on the NEXT row), sboxes shared across each source's three lanes,
α-combined. 193 ops. -/
def stPoseidonBody (b : BB) : BB × Nat :=
  let (b, p00) := bSbox b (wCol 0)
  let (b, p01) := bSbox b (wCol 1)
  let (b, p02) := bSbox b (wCol 2)
  let (b, p10) := bSbox b (wCol 6)
  let (b, p11) := bSbox b (wCol 7)
  let (b, p12) := bSbox b (wCol 8)
  let (b, p20) := bSbox b (wCol 9)
  let (b, p21) := bSbox b (wCol 10)
  let (b, p22) := bSbox b (wCol 11)
  let (b, p30) := bSbox b (wCol 12)
  let (b, p31) := bSbox b (wCol 13)
  let (b, p32) := bSbox b (wCol 14)
  let (b, p40) := bSbox b (wCol 3)
  let (b, p41) := bSbox b (wCol 4)
  let (b, p42) := bSbox b (wCol 5)
  let (b, c0) := bPosLane b 0 (cCol 0) p00 p01 p02 (wCol 6)
  let (b, c1) := bPosLane b 1 (cCol 1) p00 p01 p02 (wCol 7)
  let (b, c2) := bPosLane b 2 (cCol 2) p00 p01 p02 (wCol 8)
  let (b, c3) := bPosLane b 0 (cCol 3) p10 p11 p12 (wCol 9)
  let (b, c4) := bPosLane b 1 (cCol 4) p10 p11 p12 (wCol 10)
  let (b, c5) := bPosLane b 2 (cCol 5) p10 p11 p12 (wCol 11)
  let (b, c6) := bPosLane b 0 (cCol 6) p20 p21 p22 (wCol 12)
  let (b, c7) := bPosLane b 1 (cCol 7) p20 p21 p22 (wCol 13)
  let (b, c8) := bPosLane b 2 (cCol 8) p20 p21 p22 (wCol 14)
  let (b, c9) := bPosLane b 0 (cCol 9) p30 p31 p32 (wCol 3)
  let (b, c10) := bPosLane b 1 (cCol 10) p30 p31 p32 (wCol 4)
  let (b, c11) := bPosLane b 2 (cCol 11) p30 p31 p32 (wCol 5)
  let (b, c12) := bPosLane b 0 (cCol 12) p40 p41 p42 (wnCol 0)
  let (b, c13) := bPosLane b 1 (cCol 13) p40 p41 p42 (wnCol 1)
  let (b, c14) := bPosLane b 2 (cCol 14) p40 p41 p42 (wnCol 2)
  hornerAlpha b [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14]

/-- The `CompleteAdd` body: `KimchiVerify.completeAddConstraints`' 7 constraints, single-row,
no coefficients (columns `x1 y1 x2 y2 x3 y3 inf same_x s inf_z x21_inv = w₀..w₁₀`), α-combined.
41 ops. -/
def stCompleteAddBody (b : BB) : BB × Nat :=
  let x1 := wCol 0
  let y1 := wCol 1
  let x2 := wCol 2
  let y2 := wCol 3
  let x3 := wCol 4
  let y3 := wCol 5
  let inf := wCol 6
  let sameX := wCol 7
  let s := wCol 8
  let infZ := wCol 9
  let x21Inv := wCol 10
  let (b, x21) := bSub b x2 x1
  let (b, y21) := bSub b y2 y1
  let (b, x1sq) := bMul b x1 x1
  let (b, oneMs) := bSub b vONE sameX
  -- c0 = x21Inv·x21 − (1 − sameX)
  let (b, t0) := bMul b x21Inv x21
  let (b, c0) := bSub b t0 oneMs
  -- c1 = sameX·x21
  let (b, c1) := bMul b sameX x21
  -- c2 = sameX·((s+s)·y1 − 3·x1²) + (1−sameX)·(x21·s − y21)
  let (b, ss) := bAdd b s s
  let (b, sy) := bMul b ss y1
  let (b, d2) := bAdd b x1sq x1sq
  let (b, d3) := bAdd b d2 x1sq
  let (b, dl) := bSub b sy d3
  let (b, lhs) := bMul b sameX dl
  let (b, xs) := bMul b x21 s
  let (b, xsy) := bSub b xs y21
  let (b, rhs) := bMul b oneMs xsy
  let (b, c2) := bAdd b lhs rhs
  -- c3 = x1 + x2 + x3 − s²
  let (b, a0) := bAdd b x1 x2
  let (b, a1) := bAdd b a0 x3
  let (b, ssq) := bMul b s s
  let (b, c3) := bSub b a1 ssq
  -- c4 = s·(x1 − x3) − y1 − y3
  let (b, dx) := bSub b x1 x3
  let (b, sdx) := bMul b s dx
  let (b, e0) := bSub b sdx y1
  let (b, c4) := bSub b e0 y3
  -- c5 = y21·(sameX − inf)
  let (b, si) := bSub b sameX inf
  let (b, c5) := bMul b y21 si
  -- c6 = y21·infZ − inf
  let (b, yz) := bMul b y21 infZ
  let (b, c6) := bSub b yz inf
  hornerAlpha b [c0, c1, c2, c3, c4, c5, c6]

/-- One `VarbaseMul` bit group (`KimchiVerify.varBaseMulConstraints`' `single_bit`): the 4
constraints `[booleanity, slope, output.x, output.y]` for one bit. 27 ops. -/
def bVbmBit (b : BB) (bit sl ix iy ox oy : Nat) : BB × List Nat :=
  let xT := wCol 0
  let yT := wCol 1
  let (b, bb) := bMul b bit bit
  let (b, cBool) := bSub b bb bit
  let (b, b2) := bAdd b bit bit
  let (b, bSign) := bSub b b2 vONE
  let (b, ssq) := bMul b sl sl
  let (b, r1) := bSub b ssq ix
  let (b, rx) := bSub b r1 xT
  let (b, t) := bSub b ix rx
  let (b, iy2) := bAdd b iy iy
  let (b, ts) := bMul b t sl
  let (b, u) := bSub b iy2 ts
  -- slope: (ix − xT)·s − (iy − bSign·yT)
  let (b, ixt) := bSub b ix xT
  let (b, m1) := bMul b ixt sl
  let (b, byv) := bMul b bSign yT
  let (b, iyb) := bSub b iy byv
  let (b, cS) := bSub b m1 iyb
  -- output.x: u² − t²·(ox − xT + s²)
  let (b, uu) := bMul b u u
  let (b, tt) := bMul b t t
  let (b, oxt) := bSub b ox xT
  let (b, oxs) := bAdd b oxt ssq
  let (b, m2) := bMul b tt oxs
  let (b, cX) := bSub b uu m2
  -- output.y: (oy + iy)·t − (ix − ox)·u
  let (b, oi) := bAdd b oy iy
  let (b, m3) := bMul b oi t
  let (b, io) := bSub b ix ox
  let (b, m4) := bMul b io u
  let (b, cY) := bSub b m3 m4
  (b, [cBool, cS, cX, cY])

/-- The `VarbaseMul` body: the 21 constraints (`dec :: 5 bit groups × 4`), accumulator chain
`(w₂,w₃) (w₇,w₈) (w₉,w₁₀) (w₁₁,w₁₂) (w₁₃,w₁₄)` CURR → `(w'₀,w'₁)` NEXT, bits `w'₂..w'₆`,
slopes `w'₇..w'₁₁`, `n = w₄`, `n' = w₅`, α-combined. 186 ops. -/
def stVarBaseMulBody (b : BB) : BB × Nat :=
  let accX := fun (i : Nat) => [wCol 2, wCol 7, wCol 9, wCol 11, wCol 13, wnCol 0].getD i 0
  let accY := fun (i : Nat) => [wCol 3, wCol 8, wCol 10, wCol 12, wCol 14, wnCol 1].getD i 0
  let bitV := fun (i : Nat) => wnCol (2 + i)
  let slV := fun (i : Nat) => wnCol (7 + i)
  -- dec = n' − fold(bit + 2·acc) from n
  let (b, acc) := (List.range 5).foldl (fun (p : BB × Nat) i =>
    let (b, acc) := p
    let (b, a2) := bAdd b acc acc
    bAdd b (bitV i) a2) (b, wCol 4)
  let (b, dec) := bSub b (wCol 5) acc
  let (b, g0) := bVbmBit b (bitV 0) (slV 0) (accX 0) (accY 0) (accX 1) (accY 1)
  let (b, g1) := bVbmBit b (bitV 1) (slV 1) (accX 1) (accY 1) (accX 2) (accY 2)
  let (b, g2) := bVbmBit b (bitV 2) (slV 2) (accX 2) (accY 2) (accX 3) (accY 3)
  let (b, g3) := bVbmBit b (bitV 3) (slV 3) (accX 3) (accY 3) (accX 4) (accY 4)
  let (b, g4) := bVbmBit b (bitV 4) (slV 4) (accX 4) (accY 4) (accX 5) (accY 5)
  hornerAlpha b (dec :: (g0 ++ g1 ++ g2 ++ g3 ++ g4))

/-- The `EndosclMul` body: the DEPLOYED 11 constraints (`.take 11` — `proof-systems` 0.3.0's
`EndosclMul::CONSTRAINTS = 11`; the 12th distinct-point witness is NOT in the deployed
linearization). Columns CURR `xt=w₀ yt=w₁ xp=w₄ yp=w₅ n=w₆ xr=w₇ yr=w₈ s1=w₉ s3=w₁₀
b1..b4=w₁₁..w₁₄`; NEXT `xs=w'₄ ys=w'₅ n'=w'₆`. Reads `vENDO` (the BASE endo). α-combined.
94 ops. -/
def stEndoMulBody (b : BB) : BB × Nat :=
  let xt := wCol 0
  let yt := wCol 1
  let xp := wCol 4
  let yp := wCol 5
  let n := wCol 6
  let xr := wCol 7
  let yr := wCol 8
  let s1 := wCol 9
  let s3 := wCol 10
  let b1 := wCol 11
  let b2 := wCol 12
  let b3 := wCol 13
  let b4 := wCol 14
  let xs := wnCol 4
  let ys := wnCol 5
  let nNext := wnCol 6
  let (b, em1) := bSub b vENDO vONE
  let (b, q1a) := bMul b b1 em1
  let (b, q1b) := bAdd b vONE q1a
  let (b, xq1) := bMul b q1b xt
  let (b, q2a) := bMul b b3 em1
  let (b, q2b) := bAdd b vONE q2a
  let (b, xq2) := bMul b q2b xt
  let (b, y1a) := bAdd b b2 b2
  let (b, y1b) := bSub b y1a vONE
  let (b, yq1) := bMul b y1b yt
  let (b, y2a) := bAdd b b4 b4
  let (b, y2b) := bSub b y2a vONE
  let (b, yq2) := bMul b y2b yt
  let (b, s1sq) := bMul b s1 s1
  let (b, s3sq) := bMul b s3 s3
  let (b, d1a) := bAdd b n n
  let (b, d1) := bAdd b d1a b1
  let (b, d2a) := bAdd b d1 d1
  let (b, d2) := bAdd b d2a b2
  let (b, d3a) := bAdd b d2 d2
  let (b, d3) := bAdd b d3a b3
  let (b, d4a) := bAdd b d3 d3
  let (b, d4) := bAdd b d4a b4
  let (b, cN) := bSub b d4 nNext
  let (b, xpxr) := bSub b xp xr
  let (b, xrxs) := bSub b xr xs
  let (b, ysyr) := bAdd b ys yr
  let (b, yryp) := bAdd b yr yp
  let (b, bb1) := bMul b b1 b1
  let (b, cB1) := bSub b bb1 b1
  let (b, bb2) := bMul b b2 b2
  let (b, cB2) := bSub b bb2 b2
  let (b, bb3) := bMul b b3 b3
  let (b, cB3) := bSub b bb3 b3
  let (b, bb4) := bMul b b4 b4
  let (b, cB4) := bSub b bb4 b4
  -- c4 = (xq1 − xp)·s1 − (yq1 − yp)
  let (b, t4a) := bSub b xq1 xp
  let (b, t4b) := bMul b t4a s1
  let (b, t4c) := bSub b yq1 yp
  let (b, c4) := bSub b t4b t4c
  -- c5 = ((xp+xp − s1²) + xq1)·(xpxr·s1 + yryp) − (yp+yp)·xpxr
  let (b, f5a) := bAdd b xp xp
  let (b, f5b) := bSub b f5a s1sq
  let (b, f5c) := bAdd b f5b xq1
  let (b, f5d) := bMul b xpxr s1
  let (b, f5e) := bAdd b f5d yryp
  let (b, f5f) := bMul b f5c f5e
  let (b, f5g) := bAdd b yp yp
  let (b, f5h) := bMul b f5g xpxr
  let (b, c5) := bSub b f5f f5h
  -- c6 = yryp² − xpxr²·((s1² − xq1) + xr)
  let (b, f6a) := bMul b yryp yryp
  let (b, f6b) := bMul b xpxr xpxr
  let (b, f6c) := bSub b s1sq xq1
  let (b, f6d) := bAdd b f6c xr
  let (b, f6e) := bMul b f6b f6d
  let (b, c6) := bSub b f6a f6e
  -- c7 = (xq2 − xr)·s3 − (yq2 − yr)
  let (b, t7a) := bSub b xq2 xr
  let (b, t7b) := bMul b t7a s3
  let (b, t7c) := bSub b yq2 yr
  let (b, c7) := bSub b t7b t7c
  -- c8 = ((xr+xr − s3²) + xq2)·(xrxs·s3 + ysyr) − (yr+yr)·xrxs
  let (b, f8a) := bAdd b xr xr
  let (b, f8b) := bSub b f8a s3sq
  let (b, f8c) := bAdd b f8b xq2
  let (b, f8d) := bMul b xrxs s3
  let (b, f8e) := bAdd b f8d ysyr
  let (b, f8f) := bMul b f8c f8e
  let (b, f8g) := bAdd b yr yr
  let (b, f8h) := bMul b f8g xrxs
  let (b, c8) := bSub b f8f f8h
  -- c9 = ysyr² − xrxs²·((s3² − xq2) + xs)
  let (b, f9a) := bMul b ysyr ysyr
  let (b, f9b) := bMul b xrxs xrxs
  let (b, f9c) := bSub b s3sq xq2
  let (b, f9d) := bAdd b f9c xs
  let (b, f9e) := bMul b f9b f9d
  let (b, c9) := bSub b f9a f9e
  hornerAlpha b [cB1, cB2, cB3, cB4, c4, c5, c6, c7, c8, c9, cN]

/-- The `EndomulScalar` body: the 11 constraints (`n₈`/`a₈`/`b₈` folds + 8 crumbs), columns
`n0=w₀ n8=w₁ a0=w₂ b0=w₃ a8=w₄ b8=w₅ x₀..x₇=w₆..w₁₃`. `cf(x) = ((cC·x + cB)·x + cA)·x` is
computed ONCE per crumb and shared between the `a₈` and `b₈` folds (`df = cf + ((3−x)·x − 1)`);
the crumb is the EXPANDED Horner form `(((x−6)·x+11)·x−6)·x`. α-combined. 199 ops. -/
def stEndomulScalarBody (b : BB) : BB × Nat :=
  let n0 := wCol 0
  let n8 := wCol 1
  let a0 := wCol 2
  let b0 := wCol 3
  let a8 := wCol 4
  let b8 := wCol 5
  let xV := fun (i : Nat) => wCol (6 + i)
  -- the shared cf(xᵢ)
  let (b, cfs) := (List.range 8).foldl (fun (p : BB × List Nat) i =>
    let (b, acc) := p
    let x := xV i
    let (b, t1) := bMul b vCC x
    let (b, t2) := bAdd b t1 vCB
    let (b, t3) := bMul b t2 x
    let (b, t4) := bAdd b t3 vCA
    let (b, cf) := bMul b t4 x
    (b, acc ++ [cf])) (b, [])
  let cf := fun (i : Nat) => cfs.getD i 0
  -- n8e: acc ← 4·acc + xᵢ
  let (b, n8e) := (List.range 8).foldl (fun (p : BB × Nat) i =>
    let (b, acc) := p
    let (b, a2) := bAdd b acc acc
    let (b, a4) := bAdd b a2 a2
    bAdd b a4 (xV i)) (b, n0)
  let (b, cN8) := bSub b n8e n8
  -- a8e: acc ← 2·acc + cf(xᵢ)
  let (b, a8e) := (List.range 8).foldl (fun (p : BB × Nat) i =>
    let (b, acc) := p
    let (b, a2) := bAdd b acc acc
    bAdd b a2 (cf i)) (b, a0)
  let (b, cA8) := bSub b a8e a8
  -- b8e: acc ← 2·acc + df(xᵢ), df = cf + ((3 − x)·x − 1)
  let (b, b8e) := (List.range 8).foldl (fun (p : BB × Nat) i =>
    let (b, acc) := p
    let x := xV i
    let (b, t5) := bSub b vC3 x
    let (b, t6) := bMul b t5 x
    let (b, t7) := bSub b t6 vONE
    let (b, df) := bAdd b (cf i) t7
    let (b, a2) := bAdd b acc acc
    bAdd b a2 df) (b, b0)
  let (b, cB8) := bSub b b8e b8
  -- crumbs: (((x − 6)·x + 11)·x − 6)·x
  let (b, crumbs) := (List.range 8).foldl (fun (p : BB × List Nat) i =>
    let (b, acc) := p
    let x := xV i
    let (b, u1) := bSub b x vC6
    let (b, u2) := bMul b u1 x
    let (b, u3) := bAdd b u2 vC11
    let (b, u4) := bMul b u3 x
    let (b, u5) := bSub b u4 vC6
    let (b, cr) := bMul b u5 x
    (b, acc ++ [cr])) (b, [])
  hornerAlpha b ([cN8, cA8, cB8] ++ crumbs)

/-- The whole `gateLinConst` derivation: the six bodies, the five selector weights, the sum —
mirror of `KimchiVerify.gateLinConst`'s own shape (the generic body carries its selector
internally, as the reference does). Returns the derived linearization constant term. -/
def stGateLin (b : BB) : BB × Nat :=
  let (b, gGen) := stGenericBody b
  let (b, pos) := stPoseidonBody b
  let (b, gPos) := bMul b (selCol 1) pos
  let (b, cadd) := stCompleteAddBody b
  let (b, gCadd) := bMul b (selCol 2) cadd
  let (b, vbm) := stVarBaseMulBody b
  let (b, gVbm) := bMul b (selCol 3) vbm
  let (b, emul) := stEndoMulBody b
  let (b, gEmul) := bMul b (selCol 4) emul
  let (b, esc) := stEndomulScalarBody b
  let (b, gEsc) := bMul b (selCol 5) esc
  let (b, t1) := bAdd b gGen gPos
  let (b, t2) := bAdd b t1 gCadd
  let (b, t3) := bAdd b t2 gVbm
  let (b, t4) := bAdd b t3 gEmul
  bAdd b t4 gEsc

/-! ### THE WHOLE PROGRAM. -/

def finalizeProg : List FOp :=
  let b : BB := []
  let (b, zn) := stZN b
  let (b, s1) := stZk b zn
  let (b, a) := stAlpha b
  let (b, numer, factors) := stNumer b a s1
  let (b, denom) := stDenom b a s1
  let (b, ft0) := stFt b a s1 numer vPUBZ denom
  let b := stPerm b a s1 factors
  let b := stCip b ft0
  let (b, lct) := stGateLin b
  (bEq b vLCT lct).1

set_option maxHeartbeats 400000000 in
/-- The op count, pinned. 1046 ops: the v1 301 (14 + 10 + 8 + 28 + 31 + 12 + 11 + 187) + stage
11's 745 (generic 21 + Poseidon 193 + complete_add 41 + varbasemul 186 + endomul 94 +
endomul_scalar 199 + 5 selector weights + 5 sum adds + the closing eq). -/
theorem finalizeProg_length : finalizeProg.length = 1046 := by decide

/-- The trace height: the next power of two with an idle tail. -/
def NROWS : Nat := 2048

set_option maxHeartbeats 400000000 in
theorem the_rows_hold_the_program : finalizeProg.length + 1 ≤ NROWS ∧ NROWS = 2 ^ 11 := by decide

/-! ## §3 — THE DENOTATION, generic over `[CommRing R]`.

`progEval` extends an environment one op at a time; op `i` writes index `NIN_VALS + i`. The `eq`
op writes its FIRST source's value (a dead value; nothing reads it) — writing SOMETHING keeps the
recursion uniform. -/

def stepEval {R : Type} [CommRing R] (env : Nat → R) (o : FOp) (dst : Nat) : Nat → R :=
  fun v =>
    if v = dst then
      match o.k with
      | .mul => env o.x * env o.y
      | .add => env o.x + env o.y
      | .sub => env o.x - env o.y
      | .eq => env o.x
    else env v

def progEvalFrom {R : Type} [CommRing R] (env : Nat → R) (base : Nat) : List FOp → (Nat → R)
  | [] => env
  | o :: rest => progEvalFrom (stepEval env o base) (base + 1) rest

/-- The whole program's environment, from the 131 input/constant values. -/
def progEval {R : Type} [CommRing R] (env0 : Nat → R) : Nat → R :=
  progEvalFrom env0 NIN_VALS finalizeProg

/-! ## §3b — THE SCHEDULE AS SSA, for the allocator and the renderer. -/

/-- Op `i` as an `SsaOp` — dst `NIN_VALS + i`, reads its two sources. Emit-time tooling and the
weld's tie-point; the AIR file's legs never call it. -/
def finalizeSsa : List SsaOp :=
  (List.range finalizeProg.length).map (fun i =>
    match finalizeProg[i]? with
    | some o => ⟨NIN_VALS + i, [o.x, o.y]⟩
    | none => ⟨NIN_VALS + i, []⟩)

/-- The number of values: 131 inputs/constants + one per op. -/
def NVALS : Nat := NIN_VALS + finalizeProg.length

set_option maxHeartbeats 400000000 in
theorem nvals_eq : NVALS = 1177 := by decide

/-! ## §5 — THE REFERENCE the program claims to compute, and the standing of the tie.

`cipRef`/`ftRef`/`permRef`/`lctRef` below are thin compositions of the SHIPPED bodies
(`KimchiVerify.cipR`/`ftEval0R`/`gateLinConst`, `PicklesFinalize.permScalarR`) — no arithmetic is
re-authored, so there is no twin to drift. What ties `progEval` to them:

  * TODAY (in `MinaFinalizeScalarsWeld`, kernel decide): at the real block's environment, both
    sides land on upstream's own `combined_inner_product`, `perm_scalars` AND `linConstTerm`
    numbers, and each input that should move them moves them; the six selector bumps
    additionally pin program-vs-reference at six more points, which isolates each gate body's
    value individually. A differential at seven points, both sides upstream-derived — not a
    proof about all inputs.
  * ⚠ PENDING, NAMED: the generic `progEval = reference` theorem at every `[CommRing R]` and
    every environment. Its shape is staged — `progEvalFrom_append` + a frame lemma for reads
    below the extension base, per-stage lemmas, and `bFoldFrom`-style inductions for the folds
    (`numerRound`/`denomRound`/`cipHorner`/`hornerAlpha`/the three `EndomulScalar` folds).
    Undone work with a shape, not a theorem of the model; until it lands, do not cite this file
    as proving the program computes the reference — cite the weld's differential, at its
    resolution. -/

/-- The reference: what the program CLAIMS to compute, as one thin composition of the shipped
bodies. `esZref`/`esWref` are the 47-entry lists `cipR` folds, with `ftEval0R`'s value in slot 3.
No arithmetic is re-authored: every body is `KimchiVerify`'s / `PicklesFinalize`'s. -/
def esZref {R : Type} [CommRing R] (env0 : Nat → R) (ft : R) : List R :=
  (List.range NES).map (fun k =>
    if k = 0 then env0 vBP0Z else if k = 1 then env0 vBP1Z else if k = 2 then env0 vPUBZ
    else if k = 3 then ft else env0 (vEZ (k - 4)))

def esWref {R : Type} [CommRing R] (env0 : Nat → R) : List R :=
  (List.range NES).map (fun k =>
    if k = 0 then env0 vBP0W else if k = 1 then env0 vBP1W else if k = 2 then env0 vPUBW
    else if k = 3 then env0 vFT1 else env0 (vEW (k - 4)))

/-- The `w` and σ eval lists as `ftEval0R`/`permScalarR` want them. -/
def wListRef {R : Type} [CommRing R] (env0 : Nat → R) : List R :=
  (List.range 15).map (fun i => env0 (wCol i))
def sListRef {R : Type} [CommRing R] (env0 : Nat → R) : List R :=
  (List.range 6).map (fun i => env0 (sCol i))
def shListRef {R : Type} [CommRing R] (env0 : Nat → R) : List R :=
  (List.range PERMUTS).map (fun i => env0 (vSH i))

/-- The reference `ft_eval0`: `KimchiVerify.ftEval0R` at the environment's own values, with the
domain generator entering ONLY through the three constant blocks (`zkPolyR`'s roots) — which is
why the statement takes them as hypotheses rather than recomputing `ω`. -/
def ftRef {R : Type} [CommRing R] (env0 : Nat → R) (omega : R) : R :=
  ftEval0R DOMN omega (env0 vZETA) (env0 vBETA) (env0 vGAMMA)
    (env0 vALPHA ^ 21) (env0 vALPHA ^ 22) (env0 vALPHA ^ 23)
    (wListRef env0) (sListRef env0) (shListRef env0)
    (env0 (vEZ 0)) (env0 (vEW 0)) (env0 vPUBZ) (env0 vLCT) (env0 vDINV)

def cipRef {R : Type} [CommRing R] (env0 : Nat → R) (omega : R) : R :=
  cipR (env0 vXI) (env0 vRSQ) (esZref env0 (ftRef env0 omega)) (esWref env0)

def permRef {R : Type} [CommRing R] (env0 : Nat → R) (omega : R) : R :=
  permScalarR DOMN omega (env0 vZETA) (env0 vBETA) (env0 vGAMMA) (env0 vALPHA ^ 21)
    (wListRef env0) (sListRef env0) (env0 (vEW 0))

/-- ⚑ The gate-constraint environment stage 11 claims to evaluate: `KimchiVerify.GateEvals`
assembled from the environment's own blocks — the same slicing `MinaWrapFtEval0.gateEvalsOf`
does on the wire (`IDX_SEL = 1`, `IDX_W = 7`, `IDX_COEFF = 22`), stated over value indices. -/
def gateEvalsRef {R : Type} [CommRing R] (env0 : Nat → R) : GateEvals R :=
  { alpha := env0 vALPHA
    endo := env0 vENDO
    mds := [[env0 (vMDS 0), env0 (vMDS 1), env0 (vMDS 2)],
            [env0 (vMDS 3), env0 (vMDS 4), env0 (vMDS 5)],
            [env0 (vMDS 6), env0 (vMDS 7), env0 (vMDS 8)]]
    coeff := (List.range 15).map (fun i => env0 (cCol i))
    w := (List.range 15).map (fun i => env0 (wCol i))
    wNext := (List.range 15).map (fun i => env0 (wnCol i))
    cA := env0 vCA
    cB := env0 vCB
    cC := env0 vCC
    genSel := env0 (selCol 0)
    posSel := env0 (selCol 1)
    caddSel := env0 (selCol 2)
    mulSel := env0 (selCol 3)
    emulSel := env0 (selCol 4)
    emulScalarSel := env0 (selCol 5) }

/-- ⚑ The reference linearization constant term: `KimchiVerify.gateLinConst` — the value stage
11's closing eq gate forces the `LCT` claim to be. -/
def lctRef {R : Type} [CommRing R] (env0 : Nat → R) : R :=
  gateLinConst (gateEvalsRef env0)

#assert_axioms finalizeProg_length
#assert_axioms the_rows_hold_the_program
#assert_axioms nvals_eq

end Dregg2.Circuit.Emit.MinaFinalizeScalars
