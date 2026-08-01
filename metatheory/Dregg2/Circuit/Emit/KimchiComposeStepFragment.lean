/-
# Dregg2.Circuit.Emit.KimchiComposeStepFragment — a REAL multi-step `step_main` component

## ⚑ THE RUNG THIS IS, AND WHAT IT IS NOT

`KimchiComposeMSM` proved the SMALLEST cross-gate composition: ONE `var_base_mul` feeding ONE
`complete_add` through ONE σ class (4 rows). That rung established the *mechanism* — gates wire across
TYPES, `place` needs no special-casing because σ operates on cells. **This file is the SCALE-UP.** It
assembles the actual in-circuit MSM accumulation a `step_main` runs:

  * `K` **multi-chunk `var_base_mul` scalar multiplications** — each `C` chunks of 5 bits, the chunks
    CHAINED to one another by the copy-permutation (chunk `j`'s output accumulator `(x5,y5)` on its
    `Zero` row is the SAME VARIABLE as chunk `j+1`'s input accumulator `(x0,y0)`; chunk `j`'s scalar
    counter `n'` is the SAME VARIABLE as chunk `j+1`'s `n`), with the base point `T` a SINGLE variable
    fanned out into all `C` chunk rows;
  * ONE **multi-block `endo_mul`** scalar multiplication of `E` 4-bit blocks — a DIFFERENT chaining
    pattern: consecutive `EndoMul` rows OVERLAP (row `r+1` is simultaneously block `r`'s `Next` and
    block `r+1`'s `Curr`), so the accumulator flows through SHARED CELLS, not through σ;
  * a **chain of `complete_add`s** accumulating `R ← R + Pᵢ` over all `K+1` term outputs — each add's
    output `(x3,y3)` is the SAME VARIABLE as the next add's input `(x1,y1)`, so the running sum is a
    σ chain threading the whole circuit, and each term's output crosses a gate TYPE boundary
    (`var_base_mul`/`endo_mul` → `complete_add`) on the way in.

Four gate types, hundreds of cells, dozens of σ classes, four structurally distinct wiring patterns.
It is built from the landed pieces read-only: the gate semantics/witness generators of
`KimchiRenderVarBaseMul` / `KimchiRenderCompleteAdd` / `KimchiRenderEndoMul`, the placement pass
`KimchiPlacement.place`, the renderer `KimchiRenderVarBaseMul.renderCircuit`, and — for the composed
grid — `WitnessBuilder.compose`/`gateVarWitness`, which fills every cell of a variable's class from ONE
`VarEnv` entry, so a copy class is single-valued BY CONSTRUCTION rather than by coincidence.

It is **NOT** a soundness proof, **NOT** "machine-checked Pickles", **NOT** a Mina-valid proof, and it
is **NOT** `step_main` — it is a `step_main`-shaped FRAGMENT. The kimchi proof the harness produces is
an INNER proof. The reportable increment is INNER-KIMCHI FIDELITY AT SCALE: the Lean-authored
multi-gate, multi-row assembly is accepted by a pure-Rust kimchi prover, and its cross-gate wiring
GENUINELY BINDS mid-chain (a σ-only desync deep inside the accumulator is rejected; the same flip with
the wire removed is accepted).

## ⚑ THE CLEAN MID-CHAIN WIRING PROBES

Every load-bearing shared cell is ALSO gate-read (a `var_base_mul` output is read by its own gate; a
`complete_add` output is read by `complete_add`), so flipping one cannot ISOLATE σ — a gate rejects it
too. So each accumulator value is ALSO materialized in a standalone `Zero` **probe row** placed into
the SAME class. A `Zero` gate reads nothing and no gate reads a probe row, so a probe cell is
constrained **by σ and by nothing else**. Probes sit throughout the circuit, including deep mid-chain,
and the `…Unwired` variant is identical EXCEPT the probe rows are not in any class — the control that
turns "rejected" into "rejected BY THE WIRE".

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored synthesis.** The gate list, the cross-gate placement, the variable allocation
and the witness are authored in Lean. `proof-systems` RUNS the artifact and authors no constraint. The
`VarBaseMul`/`CompleteAdd`/`EndoMul` constraint polynomials are proof-systems' fixed gate semantics;
the SAME polynomials are transcribed read-only in `KimchiVerify` — and the `#guard`s below evaluate
them against the **assembled grid** (`gridRow`), not against the intermediate Lean lists, so a
placement bug that never reaches the grid cannot hide.

## Axiom hygiene / build

NO `main` (roots cleanly into `PicklesSynthesis`; the emit driver is `EmitStepFragmentJson.lean`).
`#guard`s reduce in the interpreter; no `sorry`/`native_decide`, no `decide` over the big grid.
-/
import Dregg2.Circuit.Emit.KimchiPlacement
import Dregg2.Circuit.Emit.WitnessBuilder
import Dregg2.Circuit.Emit.KimchiRenderVarBaseMul
import Dregg2.Circuit.Emit.KimchiRenderCompleteAdd
import Dregg2.Circuit.Emit.KimchiRenderEndoMul
import Dregg2.Circuit.Emit.KimchiVerify
import Dregg2.Circuit.Emit.PastaCurve

namespace Dregg2.Circuit.Emit.KimchiComposeStepFragment

open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder
  (VarEnv GateWitness gridAt gateVarWitness envIndex gateVarWitnessAt compose toGrid)
open Dregg2.Circuit.Emit.KimchiRenderVarBaseMul (fAdd fSub fMul fInv stepVbm renderCircuit)
open Dregg2.Circuit.Emit.KimchiRenderCompleteAdd (completeAddWitness)
open Dregg2.Circuit.Emit.KimchiVerify
  (varBaseMulConstraints completeAddConstraints endoMulConstraints)
open Dregg2.Circuit.Emit.PastaCurve (Gp dblTraceM addTraceM jacEqM oncurveM scMulM)
open Dregg2.Circuit.Emit.PastaField (pN)

set_option autoImplicit false
set_option maxRecDepth 10000

/-! ## §1 — the shape, and the affine / Jacobian helpers.

`Shape` parameterizes the fragment so the same assembly can be instantiated at several sizes (the
scale ladder the emit driver measures). Everything downstream is a function of it. -/

/-- The fragment's size: `terms` var_base_mul scalar multiplications of `chunks` 5-bit chunks each,
plus one endo_mul scalar multiplication of `endoBlocks` 4-bit blocks, all summed by a chain of
`terms` `complete_add`s. Requires `terms ≥ 2`. -/
structure Shape where
  terms : Nat
  chunks : Nat
  endoBlocks : Nat
  deriving Repr, Inhabited, DecidableEq

/-- Affine point negation over `Fp`. -/
def negA (P : Nat × Nat) : Nat × Nat := (P.1, fSub 0 P.2)

/-- Affine addition, taken from the `complete_add` witness generator's OUTPUT cells `(x₃,y₃)` — so the
points fed to the gate and the points used to schedule the circuit come from ONE routine. -/
def addA (P Q : Nat × Nat) : Nat × Nat :=
  let c := completeAddWitness P.1 P.2 Q.1 Q.2
  (c.getD 4 0, c.getD 5 0)

/-- Affine doubling (`KimchiRenderVarBaseMul.dbl`, read-only). -/
def dblA (P : Nat × Nat) : Nat × Nat := KimchiRenderVarBaseMul.dbl P

/-- On-curve test `y² = x³ + 5` over `Fp`. -/
def onCurveA (P : Nat × Nat) : Bool :=
  fMul P.2 P.2 == fAdd (fMul P.1 (fMul P.1 P.1)) 5

/-! ### Jacobian helpers — the INDEPENDENT oracle.

The gate witness is computed with the affine `add_fast`/`single_bit` formulas. The semantic `#guard`s
below check the SAME points with `PastaCurve`'s Jacobian traces (`dblTraceM`/`addTraceM`, an entirely
separate formula family), compared without inversion by `jacEqM`. A shared bug in the affine formulas
would have to be mirrored in the Jacobian ones to pass. -/

/-- Lift an affine point to Jacobian (`Z = 1`). -/
def jOf (P : Nat × Nat) : Nat × Nat × Nat := (P.1, P.2, 1)
def jDbl (P : Nat × Nat × Nat) : Nat × Nat × Nat := (dblTraceM pN P.1 P.2.1 P.2.2).toPt
def jAdd (P Q : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (addTraceM pN P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2).toPt
def jNeg (P : Nat × Nat × Nat) : Nat × Nat × Nat := (P.1, fSub 0 P.2.1, P.2.2)

/-! ## §2 — the scalar bits.

Deterministic, mixed 0/1 (so both slope signs and both endo branches are exercised in every chain),
and reproducible: the circuit is a fixture, not a random test. -/

/-- A deterministic bit mixer (an affine hash on `(a,b)`, bit 4 of the mix). -/
def bitMix (a b : Nat) : Nat := ((a * 2654435761 + b * 40503 + 12345) / 16) % 2

/-- Term `i`'s `5·chunks` scalar bits, MSB-first. -/
def termBits (sh : Shape) (i : Nat) : List Nat :=
  (List.range (5 * sh.chunks)).map (fun k => bitMix (i + 1) (k + 1))

/-- The endo term's `4·endoBlocks` scalar bits. -/
def endoBitsOf (sh : Shape) : List Nat :=
  (List.range (4 * sh.endoBlocks)).map (fun k => bitMix 7771 (k + 1))

/-! ## §3 — the computed chain data (ONE pass; every derived object reads this).

`Frag` is the fully-evaluated witness data for a `Shape`. It exists so the assembly does not
recompute a scalar chain per row: `mkFrag` runs once and every row spec, env entry and `#guard`
indexes into the result. -/

/-- One var_base_mul term: base point, the `5C+1` per-bit accumulators, the `5C` slopes, and the
`5C+1` running scalar counters `n` (the `n`/`n'` cells at chunk boundaries). -/
structure TermData where
  T : Nat × Nat
  accs : List (Nat × Nat)
  slopes : List Nat
  ns : List Nat
  deriving Repr, Inhabited

/-- Run the per-bit `var_base_mul` chain (`stepVbm`, read-only from `KimchiRenderVarBaseMul`):
`accₖ₊₁ = [2]accₖ + (2bₖ−1)·T`, `nₖ₊₁ = 2nₖ + bₖ`. -/
def runVbm (T acc0 : Nat × Nat) (bits : List Nat) : TermData :=
  let st := bits.foldl
    (fun (st : List (Nat × Nat) × List Nat × List Nat) b =>
      let cur := st.1.getLastD (0, 0)
      let r := stepVbm T.1 T.2 cur.1 cur.2 b
      (st.1 ++ [(r.2.1, r.2.2)], st.2.1 ++ [r.1], st.2.2 ++ [2 * st.2.2.getLastD 0 + b]))
    ([acc0], [], [0])
  { T := T, accs := st.1, slopes := st.2.1, ns := st.2.2 }

/-- One `endo_mul` 4-bit block's stored cells (`endosclmul.rs:48-56`): the intermediate point
`(xr,yr)`, the two stored slopes `s1,s3`, the distinct-point inverse `inv = w₂`, the output
`(xs,ys)`, and the four bits. `s2`/`s4` are constraint intermediates and are NOT stored. -/
structure EndoBlock where
  xr : Nat
  yr : Nat
  s1 : Nat
  s3 : Nat
  inv : Nat
  xs : Nat
  ys : Nat
  b1 : Nat
  b2 : Nat
  b3 : Nat
  b4 : Nat
  deriving Repr, Inhabited

/-- One `endo_mul` block: `acc ← [2]([2]acc + Q₁) + Q₂` with `Qₖ = (2b_even−1)·φ^{b_odd}(T)`
(the endomorphism-selected, sign-selected base point). Formulas transcribed read-only from
`KimchiRenderEndoMul` (`xqOf`/`yqOf` reused directly). -/
def endoStep (xt yt xp yp b1 b2 b3 b4 : Nat) : EndoBlock :=
  let xq1 := KimchiRenderEndoMul.xqOf b1 xt
  let yq1 := KimchiRenderEndoMul.yqOf b2 yt
  let s1 := fMul (fSub yq1 yp) (fInv (fSub xq1 xp))
  let s2 := fSub (fMul (fMul 2 yp) (fInv (fSub (fAdd (fMul 2 xp) xq1) (fMul s1 s1)))) s1
  let xr := fSub (fAdd xq1 (fMul s2 s2)) (fMul s1 s1)
  let yr := fSub (fMul (fSub xp xr) s2) yp
  let xq2 := KimchiRenderEndoMul.xqOf b3 xt
  let yq2 := KimchiRenderEndoMul.yqOf b4 yt
  let s3 := fMul (fSub yq2 yr) (fInv (fSub xq2 xr))
  let s4 := fSub (fMul (fMul 2 yr) (fInv (fSub (fAdd (fMul 2 xr) xq2) (fMul s3 s3)))) s3
  let xs := fSub (fAdd xq2 (fMul s4 s4)) (fMul s3 s3)
  let ys := fSub (fMul (fSub xr xs) s4) yr
  let inv := fInv (fMul (fSub xp xr) (fSub xr xs))
  { xr := xr, yr := yr, s1 := s1, s3 := s3, inv := inv, xs := xs, ys := ys
  , b1 := b1, b2 := b2, b3 := b3, b4 := b4 }

/-- The whole computed fragment. -/
structure Frag where
  sh : Shape
  terms : List TermData
  endoT : Nat × Nat
  endoAccs : List (Nat × Nat)
  endoBlks : List EndoBlock
  endoNs : List Nat
  sums : List (Nat × Nat)
  addCells : List (List Nat)
  deriving Repr, Inhabited

/-- `n` distinct base points: `[3]G, [4]G, …` built by repeated affine addition (each on-curve,
pairwise distinct — pinned below). -/
def basePts (n : Nat) : List (Nat × Nat) :=
  (List.range n).foldl
    (fun acc _ =>
      match acc with
      | [] => [addA Gp (dblA Gp)]
      | _ => acc ++ [addA (acc.getLastD Gp) Gp])
    []

/-- **The one-pass evaluator.** Runs every scalar chain, then the `complete_add` accumulator chain
`R₀ = P₀ + P₁`, `Rₐ = Rₐ₋₁ + Pₐ₊₁`, with the LAST add consuming the endo_mul term's output. -/
def mkFrag (sh : Shape) : Frag :=
  let bases := basePts (sh.terms + 1)
  let tds := (List.range sh.terms).map (fun i =>
    let T := bases.getD i Gp
    runVbm T (dblA T) (termBits sh i))
  let eT := bases.getD sh.terms Gp
  let eBits := endoBitsOf sh
  let est := (List.range sh.endoBlocks).foldl
    (fun (st : List (Nat × Nat) × List EndoBlock × List Nat) e =>
      let cur := st.1.getLastD (0, 0)
      let b := endoStep eT.1 eT.2 cur.1 cur.2
        (eBits.getD (4 * e) 0) (eBits.getD (4 * e + 1) 0)
        (eBits.getD (4 * e + 2) 0) (eBits.getD (4 * e + 3) 0)
      (st.1 ++ [(b.xs, b.ys)], st.2.1 ++ [b],
       st.2.2 ++ [16 * st.2.2.getLastD 0 + 8 * b.b1 + 4 * b.b2 + 2 * b.b3 + b.b4]))
    ([dblA eT], [], [0])
  -- the `terms` term outputs, then the endo term output — the `terms+1` MSM addends.
  let pts := (List.range sh.terms).map (fun i => (tds.getD i default).accs.getLastD (0, 0))
             ++ [est.1.getLastD (0, 0)]
  let accSt := (List.range sh.terms).foldl
    (fun (st : List (Nat × Nat) × List (List Nat)) a =>
      let l := if a == 0 then pts.getD 0 (0, 0) else st.1.getLastD (0, 0)
      let r := pts.getD (a + 1) (0, 0)
      let cells := completeAddWitness l.1 l.2 r.1 r.2
      (st.1 ++ [(cells.getD 4 0, cells.getD 5 0)], st.2 ++ [cells]))
    ([], [])
  { sh := sh, terms := tds, endoT := eT, endoAccs := est.1, endoBlks := est.2.1
  , endoNs := est.2.2, sums := accSt.1, addCells := accSt.2 }

/-! ## §4 — the variable allocation.

One flat `PVar.external` id space, laid out so a collision is impossible by construction: point `p`'s
coordinates are `2p` and `2p+1`; scalar counters live above `2·numPoints`. The distinct-variable
count is pinned below, so any collision (which would MERGE two classes and shrink the count) goes
red. -/

/-- Point-id of term `i`'s base point `Tᵢ` (one variable, fanned into all `C` of its chunk rows). -/
def pT (sh : Shape) (i : Nat) : Nat := i * (sh.chunks + 2)
/-- Point-id of term `i`'s accumulator at chunk boundary `j` (`j = 0..C`). -/
def pAcc (sh : Shape) (i j : Nat) : Nat := i * (sh.chunks + 2) + 1 + j
/-- Point-id of the endo term's base point. -/
def pEndoT (sh : Shape) : Nat := sh.terms * (sh.chunks + 2)
/-- Point-id of the endo term's accumulator after `e` blocks (`e = 0..E`). -/
def pEndoAcc (sh : Shape) (e : Nat) : Nat := sh.terms * (sh.chunks + 2) + 1 + e
/-- Point-id of the running MSM sum `Rₐ` (`a = 0..K−1`). -/
def pSum (sh : Shape) (a : Nat) : Nat :=
  sh.terms * (sh.chunks + 2) + (sh.endoBlocks + 2) + a
/-- Total point ids (the base of the scalar id space). -/
def numPoints (sh : Shape) : Nat :=
  sh.terms * (sh.chunks + 2) + (sh.endoBlocks + 2) + sh.terms

/-- Point `p`'s x-coordinate variable. -/
def px (p : Nat) : PVar := .external (2 * p)
/-- Point `p`'s y-coordinate variable. -/
def py (p : Nat) : PVar := .external (2 * p + 1)
/-- Scalar variable `s` (already offset past the point space). -/
def sv (s : Nat) : PVar := .external s

/-- Scalar id of term `i`'s counter at chunk boundary `j` — the SAME variable is chunk `j−1`'s `n'`
(col 5) and chunk `j`'s `n` (col 4). That identity IS the scalar chaining wire. -/
def sN (sh : Shape) (i j : Nat) : Nat := 2 * numPoints sh + i * (sh.chunks + 1) + j
/-- Scalar id of the endo term's counter after `e` blocks. -/
def sEn (sh : Shape) (e : Nat) : Nat :=
  2 * numPoints sh + sh.terms * (sh.chunks + 1) + e

/-! ## §5 — the row schedule.

A `RowSpec` is one circuit row: its gate `kind`, its `K_PERMUTS = 7` permutation-column variables
(`none` = unwired ⇒ `place` self-wires it), and its ADVICE cells — the `(col, value)` placements for
columns no variable owns (cols 7..14, plus permutation columns deliberately left unwired such as the
`var_base_mul` bit/slope cells). The witness is `gateVarWitness` (env-driven, over `perm`) ++ the
advice, composed by `WitnessBuilder`. -/

structure RowSpec where
  kind : KGateType
  perm : List (Option PVar)
  advice : List (Nat × Int)
  /-- `true` only for the standalone `Zero` wiring probes of §5 — the rows the WIRED and UNWIRED
  variants differ on, and the only rows a harness tamper is allowed to isolate σ from. -/
  probe : Bool := false
  deriving Repr, Inhabited

/-- Seven unwired permutation columns. -/
def noPerm : List (Option PVar) := List.replicate K_PERMUTS none

/-- **A PROBE row.** A standalone `Zero` gate whose cols 0,1 hold a copy of some accumulator point
and, in the WIRED variant, sit in that point's σ class. `Zero` reads nothing and no gate reads this
row, so these two cells are constrained by σ and by NOTHING ELSE — the clean wiring probe. In the
UNWIRED variant the row is in no class at all (the control). -/
def probeSpec (wired : Bool) (p : Nat) : RowSpec :=
  { kind := .zero
  , perm := if wired then [some (px p), some (py p), none, none, none, none, none] else noPerm
  , advice := []
  , probe := true }

/-- The two rows of term `i`'s chunk `j`: the `VarBaseMul` row and its `Zero` `Next` row.

CURR: `w₀=xT w₁=yT w₂=x₀ w₃=y₀ w₄=n w₅=n' w₆=Ø w₇..w₁₄ = x₁y₁x₂y₂x₃y₃x₄y₄` (the four intra-chunk
accumulators). NEXT: `w₀=x₅ w₁=y₅ w₂..w₆=b₀..b₄ w₇..w₁₁=s₀..s₄`.

The permutation columns carry: `T` (ONE variable across all `C` chunks), the chunk-boundary
accumulator points (SHARED with the neighbouring chunk), and the scalar counters `n`/`n'` (SHARED
with the neighbouring chunk). -/
def vbmChunkRows (f : Frag) (i j : Nat) : List RowSpec :=
  let sh := f.sh
  let td := f.terms.getD i default
  let ax : Nat → Int := fun k => ((td.accs.getD k (0, 0)).1 : Int)
  let ay : Nat → Int := fun k => ((td.accs.getD k (0, 0)).2 : Int)
  let bt : Nat → Int := fun k => (td.slopes.getD k 0 : Int)
  let bits := termBits sh i
  let bi : Nat → Int := fun k => (bits.getD k 0 : Int)
  [ { kind := .varBaseMul
    , perm := [ some (px (pT sh i)), some (py (pT sh i))
              , some (px (pAcc sh i j)), some (py (pAcc sh i j))
              , some (sv (sN sh i j)), some (sv (sN sh i (j + 1))), none ]
    , advice := [ (7, ax (5 * j + 1)), (8, ay (5 * j + 1))
                , (9, ax (5 * j + 2)), (10, ay (5 * j + 2))
                , (11, ax (5 * j + 3)), (12, ay (5 * j + 3))
                , (13, ax (5 * j + 4)), (14, ay (5 * j + 4)) ] }
  , { kind := .zero
    , perm := [ some (px (pAcc sh i (j + 1))), some (py (pAcc sh i (j + 1)))
              , none, none, none, none, none ]
    , advice := [ (2, bi (5 * j)), (3, bi (5 * j + 1)), (4, bi (5 * j + 2))
                , (5, bi (5 * j + 3)), (6, bi (5 * j + 4))
                , (7, bt (5 * j)), (8, bt (5 * j + 1)), (9, bt (5 * j + 2))
                , (10, bt (5 * j + 3)), (11, bt (5 * j + 4)) ] } ]

/-- The endo_mul chain: `E` `EndoMul` rows then one `Zero` tail.

⚑ THE OVERLAP. Row `r+1` is block `r`'s `Next` (`w'₄=xs w'₅=ys w'₆=n'`) AND block `r+1`'s `Curr`
(`w₄=xp w₅=yp w₆=n`) — the SAME three cells. So the endo accumulator chains through SHARED CELLS,
a structurally different pattern from var_base_mul's σ hop, and one no prior rung exercised. The base
point `(xt,yt)` at cols 0,1 IS a σ class of `E` cells. -/
def endoRows (f : Frag) (_wired : Bool) : List RowSpec :=
  let sh := f.sh
  (List.range sh.endoBlocks).map (fun e =>
    let b := f.endoBlks.getD e default
    { kind := .endoMul
    , perm := [ some (px (pEndoT sh)), some (py (pEndoT sh)), none, none
              , some (px (pEndoAcc sh e)), some (py (pEndoAcc sh e)), some (sv (sEn sh e)) ]
    , advice := [ (2, (b.inv : Int)), (3, 0)
                , (7, (b.xr : Int)), (8, (b.yr : Int))
                , (9, (b.s1 : Int)), (10, (b.s3 : Int))
                , (11, (b.b1 : Int)), (12, (b.b2 : Int))
                , (13, (b.b3 : Int)), (14, (b.b4 : Int)) ] : RowSpec })
  ++ [ { kind := .zero
       , perm := [ none, none, none, none
                 , some (px (pEndoAcc sh sh.endoBlocks)), some (py (pEndoAcc sh sh.endoBlocks))
                 , some (sv (sEn sh sh.endoBlocks)) ]
       , advice := [] } ]

/-- The `a`-th `complete_add` row of the MSM accumulator chain: `Rₐ = Lₐ + Pₐ₊₁` where `L₀ = P₀` and
`Lₐ = Rₐ₋₁`. Cols 0..5 are `x₁ y₁ x₂ y₂ x₃ y₃` — ALL permutation columns, so the input point, the
addend and the OUTPUT are each shared variables: the running sum is a σ chain, and the addend crosses
a gate-TYPE boundary (its producer is a `var_base_mul` `Zero` row, or the `endo_mul` tail). Col 6
(`inf`) is left unwired at 0 (pinned below: every add is the distinct-x `add_fast` case). -/
def addRowSpec (f : Frag) (a : Nat) : RowSpec :=
  let sh := f.sh
  let lp := if a == 0 then pAcc sh 0 sh.chunks else pSum sh (a - 1)
  let rp := if a + 1 == sh.terms then pEndoAcc sh sh.endoBlocks else pAcc sh (a + 1) sh.chunks
  let op := pSum sh a
  let c := f.addCells.getD a []
  { kind := .completeAdd
  , perm := [ some (px lp), some (py lp), some (px rp), some (py rp)
            , some (px op), some (py op), none ]
  , advice := [ (7, (c.getD 7 0 : Int)), (8, (c.getD 8 0 : Int))
              , (9, (c.getD 9 0 : Int)), (10, (c.getD 10 0 : Int)) ] }

/-- **THE ROW SCHEDULE.** Straight-line, in the order a `step_main` would emit it: term 0's chain,
then for each later term its chain followed immediately by the add that folds it into the running
sum, then the endo_mul chain and the final add. Probe rows follow every accumulator that leaves a
block. -/
def fragRows (f : Frag) (wired : Bool) : List RowSpec :=
  let sh := f.sh
  ((List.range sh.chunks).flatMap (vbmChunkRows f 0))
  ++ [probeSpec wired (pAcc sh 0 sh.chunks)]
  ++ (List.range (sh.terms - 1)).flatMap (fun t =>
        let i := t + 1
        ((List.range sh.chunks).flatMap (vbmChunkRows f i))
        ++ [probeSpec wired (pAcc sh i sh.chunks)]
        ++ [addRowSpec f t]
        ++ [probeSpec wired (pSum sh t)])
  ++ endoRows f wired
  ++ [probeSpec wired (pEndoAcc sh sh.endoBlocks)]
  ++ [addRowSpec f (sh.terms - 1)]
  ++ [probeSpec wired (pSum sh (sh.terms - 1))]

/-! ## §6 — the environment, the placement, and the composed grid. -/

/-- The variable → value assignment. `WitnessBuilder.gateVarWitness` fills EVERY cell of a variable's
class from THIS ONE entry, so a copy class is single-valued by construction — the property the whole
assembly rests on and the reason the grid is not hand-rolled. -/
def fragEnv (f : Frag) : VarEnv :=
  let sh := f.sh
  (List.range sh.terms).flatMap (fun i =>
    let td := f.terms.getD i default
    [ (px (pT sh i), (td.T.1 : Int)), (py (pT sh i), (td.T.2 : Int)) ]
    ++ (List.range (sh.chunks + 1)).flatMap (fun j =>
        let a := td.accs.getD (5 * j) (0, 0)
        [ (px (pAcc sh i j), (a.1 : Int)), (py (pAcc sh i j), (a.2 : Int)) ])
    ++ (List.range (sh.chunks + 1)).map (fun j =>
        (sv (sN sh i j), (td.ns.getD (5 * j) 0 : Int))))
  ++ [ (px (pEndoT sh), (f.endoT.1 : Int)), (py (pEndoT sh), (f.endoT.2 : Int)) ]
  ++ (List.range (sh.endoBlocks + 1)).flatMap (fun e =>
      let a := f.endoAccs.getD e (0, 0)
      [ (px (pEndoAcc sh e), (a.1 : Int)), (py (pEndoAcc sh e), (a.2 : Int)) ])
  ++ (List.range (sh.endoBlocks + 1)).map (fun e =>
      (sv (sEn sh e), (f.endoNs.getD e 0 : Int)))
  ++ (List.range sh.terms).flatMap (fun a =>
      let s := f.sums.getD a (0, 0)
      [ (px (pSum sh a), (s.1 : Int)), (py (pSum sh a), (s.2 : Int)) ])

def fragGates (rows : List RowSpec) : List PGate :=
  rows.map (fun r => { kind := r.kind, permVars := r.perm, coeffs := [] })

/-- The composed 15 × `nRows` witness grid, via `WitnessBuilder.compose`: per-row, the env-driven
permutation cells ++ the advice cells, all laid into the grid ONCE.

⚑ `gateVarWitnessAt (envIndex env)`, not `gateVarWitness … env`. The two produce the SAME cells
(pinned in `WitnessBuilder`, both polarities); the difference is that `envLookup`'s `find?` walks the
WHOLE env per cell, so composing R rows costs O(R·|env|) — and `|env|` grows with the circuit, one
entry per variable. MEASURED on hbox at the four scale rungs, that pass was 21 / 210 / 2602 / 15515 ms
at 132 / 454 / 1674 / 4058 rows (fitted exponent **2.02**) and, once `place`/`toGrid` were indexed,
**97% of the whole Lean-side assembly**. `envIndex` is built ONCE per circuit. -/
def fragWitness (f : Frag) : List (List Int) :=
  let rows := fragRows f true
  let ix := envIndex (fragEnv f)
  let n := rows.length
  compose 15 n
    ((rows.zip (List.range n)).map (fun ri =>
      gateVarWitnessAt ix ri.2 { kind := ri.1.kind, permVars := ri.1.perm, coeffs := [] }
      ++ ri.1.advice.map (fun cv => ((⟨ri.2, cv.1⟩ : Cell), cv.2))))

/-- Read circuit row `r` out of the ASSEMBLED column-major grid (all 15 columns). The gate `#guard`s
below answer to THIS, not to the intermediate Lean lists. -/
def gridRow (w : List (List Int)) (r : Nat) : List Nat :=
  (List.range 15).map (fun c => (gridAt w ⟨r, c⟩).toNat)

/-- Render a fragment to the harness JSON, reusing `KimchiRenderVarBaseMul.renderCircuit`
(read-only) rather than a fifth copy of the renderer. -/
def fragJson (f : Frag) (name : String) (wired : Bool) : String :=
  let rows := fragRows f wired
  renderCircuit name 0 rows.length (place 0 (fragGates rows)) (fragWitness f)

/-! ## §7 — the committed instance.

Nullary `def`s so the interpreter evaluates each ONCE (a `Frag`-taking function would re-run every
scalar chain per `#guard`). The emit driver instantiates the larger scale rungs itself. -/

/-- The committed shape: 6 var_base_mul terms × 8 chunks (240 scalar bits), one endo_mul term of 16
4-bit blocks (64 bits), and a 6-long `complete_add` accumulator chain. -/
def shapeS : Shape := { terms := 6, chunks := 8, endoBlocks := 16 }

def fragS : Frag := mkFrag shapeS
def rowsS : List RowSpec := fragRows fragS true
def rowsUnwiredS : List RowSpec := fragRows fragS false
def nRowsS : Nat := rowsS.length
def gatesS : List PGate := fragGates rowsS
def gatesUnwiredS : List PGate := fragGates rowsUnwiredS
def posS : List (PVar × Cell) := circuitPositions 0 gatesS
def posUnwiredS : List (PVar × Cell) := circuitPositions 0 gatesUnwiredS
def pairsS : List (Cell × Cell) := permPairs posS
def pairsUnwiredS : List (Cell × Cell) := permPairs posUnwiredS
def placedS : List PlacedGate := place 0 gatesS
def placedUnwiredS : List PlacedGate := place 0 gatesUnwiredS
def witnessS : List (List Int) := fragWitness fragS

/-- The WIRED fragment JSON. -/
def stepFragmentJson : String :=
  renderCircuit "stepFragment_msm_K6_C8_E16" 0 nRowsS placedS witnessS
/-- The UNWIRED control: identical rows, identical witness, probe rows in NO σ class. -/
def stepFragmentUnwiredJson : String :=
  renderCircuit "stepFragment_msm_K6_C8_E16_UNWIRED" 0 nRowsS placedUnwiredS witnessS

/-! ### The rows of interest — the harness's probe coordinates.

`probeRowsS` are the absolute rows of the standalone `Zero` probes, in schedule order:
`[P₀, P₁, R₀, P₂, R₁, …, P_endo, R_{K−1}]`. The harness flips col 0 of a MID-CHAIN one. -/
def probeRowsS : List Nat :=
  ((rowsS.zip (List.range nRowsS)).filter (fun ri => ri.1.probe)).map (·.2)

/-- The absolute row the endo_mul chain starts at (after term 0's block + probe and the `terms − 1`
inner term blocks). Derived from the schedule, then pinned against the row's actual gate kind — the
harness needs it and a schedule drift must not silently move it. -/
def endoStartS : Nat :=
  2 * shapeS.chunks + 1 + (shapeS.terms - 1) * (2 * shapeS.chunks + 3)

/-! ## §8 — the in-CI pins (`#guard`; interpreter-reduced). -/

-- ── Structure ────────────────────────────────────────────────────────────────────────────────
-- 6 terms × 8 chunks × 2 rows = 96 var_base_mul rows, + 1 probe; 5 × (16 + 3) inner-term rows;
-- 16 endo rows + tail; 3 closing rows. 132 rows total.
#guard nRowsS == 132
#guard placedS.length == nRowsS
#guard placedUnwiredS.length == nRowsS
#guard (placedS.map (fun g => g.wires.length)).all (· == 7)
#guard witnessS.length == 15
#guard (witnessS.map (·.length)).all (· == nRowsS)

-- ⚑ FOUR GATE TYPES, and the exact census (a schedule drift changes these).
#guard (placedS.filter (fun g => g.kind == KGateType.varBaseMul)).length == 48
#guard (placedS.filter (fun g => g.kind == KGateType.endoMul)).length == 16
#guard (placedS.filter (fun g => g.kind == KGateType.completeAdd)).length == 6
#guard (placedS.filter (fun g => g.kind == KGateType.zero)).length == 62
#guard (placedS.map (fun g => g.coeffs.length)).all (· == 0)   -- every gate coeff-free

-- The probe schedule, absolutely: 1 (term 0's output) + 5 × (term output, running sum) + the endo
-- output + the final sum = 13, at these rows. They are spread from row 16 to row 131 — the harness's
-- mid-chain tamper targets one deep inside (row 73, the running sum after the third add).
#guard probeRowsS == [16, 33, 35, 52, 54, 71, 73, 90, 92, 109, 111, 129, 131]
-- The endo chain's location, pinned against the actual gate kinds (not against its own definition).
#guard endoStartS == 112
#guard (rowsS.getD endoStartS default).kind == KGateType.endoMul
#guard (rowsS.getD (endoStartS + shapeS.endoBlocks - 1) default).kind == KGateType.endoMul
#guard (rowsS.getD (endoStartS + shapeS.endoBlocks) default).kind == KGateType.zero  -- the tail

-- ── The copy-permutation, on the EMITTED object ──────────────────────────────────────────────
-- ⚑ σ IS A PERMUTATION of the circuit's 7·132 = 924 permutation cells: the wiring neither drops,
-- duplicates nor invents a cell.
#guard sortCells (allWires placedS) == sortCells (allCells nRowsS)
#guard sortCells (allWires placedUnwiredS) == sortCells (allCells nRowsS)

-- ⚑ THE COMPOSED GRID SATISFIES σ. Every σ-linked pair of cells holds the same value in the
-- `WitnessBuilder`-composed witness — the property the whole assembly rests on, checked against
-- `place`'s ACTUAL permutation.
#guard pairsS.all (fun pr => gridAt witnessS pr.1 == gridAt witnessS pr.2)
#guard pairsUnwiredS.all (fun pr => gridAt witnessS pr.1 == gridAt witnessS pr.2)

-- ⚑ IT CAN GO RED. Desync ONE mid-chain probe cell and the σ check FAILS (so the `= true` above is
-- a gate, not a tautology). `toGrid` is first-wins, so the prepended override lands.
#guard
  (let probe : Nat := probeRowsS.getD 6 0
   let broken := toGrid 15 nRowsS
     ((⟨probe, 0⟩, (7 : Int)) :: ((fragRows fragS true).zip (List.range nRowsS)).flatMap
       (fun ri => gateVarWitness ri.2
                    { kind := ri.1.kind, permVars := ri.1.perm, coeffs := [] } (fragEnv fragS)
                  ++ ri.1.advice.map (fun cv => ((⟨ri.2, cv.1⟩ : Cell), cv.2))))
   (pairsS.all (fun pr => gridAt broken pr.1 == gridAt broken pr.2)) == false)

-- ⚑ THE WIRED/UNWIRED DIFFERENCE IS EXACTLY THE PROBES. Every probe cell is in a σ cycle in the
-- WIRED circuit and self-wired (in NO cycle) in the UNWIRED one — so a probe flip that the wired
-- circuit rejects and the unwired one accepts isolates the WIRE.
#guard probeRowsS.all (fun r => permLookup pairsS ⟨r, 0⟩ != (⟨r, 0⟩ : Cell))
#guard probeRowsS.all (fun r => permLookup pairsS ⟨r, 1⟩ != (⟨r, 1⟩ : Cell))
#guard probeRowsS.all (fun r => permLookup pairsUnwiredS ⟨r, 0⟩ == (⟨r, 0⟩ : Cell))
#guard probeRowsS.all (fun r => permLookup pairsUnwiredS ⟨r, 1⟩ == (⟨r, 1⟩ : Cell))
-- …and NOTHING else moved except the OTHER endpoints of the probes' own classes. Dropping a probe
-- cell shrinks its class (3-cycle → 2-cycle, or the final sum's 2-cycle → a singleton), which re-aims
-- the surviving cells' wires — so the differing rows are exactly each probe plus its class partners
-- (the producing `Zero`/`complete_add` row), and nothing else in the 132.
#guard (((placedS.zip placedUnwiredS).zip (List.range nRowsS)).filter
          (fun z => z.1.1.wires != z.1.2.wires)).map (·.2)
        == [15, 16, 32, 33, 34, 35, 51, 52, 53, 54, 70, 71, 72, 73,
            89, 90, 91, 92, 108, 109, 110, 111, 128, 129, 130, 131]

-- ⚑ THE CLASSES ARE BIG AND CROSS-ROW — this is not a pile of 2-cycles.
-- Term 0's base point `T₀` is ONE variable fanned into all 8 of its chunk rows, plus… nothing else:
-- an 8-cell class spanning 14 rows.
#guard (classCells posS (px (pT shapeS 0))).length == 8
-- A mid-chain accumulator's class: chunk 3's output = chunk 4's input + its probe? (no probe here) —
-- the boundary accumulators are 2-cell cross-row classes, the TERM output is 3-cell (Zero row,
-- complete_add input, probe row).
#guard (classCells posS (px (pAcc shapeS 0 4))).length == 2
#guard (classCells posS (px (pAcc shapeS 1 shapeS.chunks))).length == 3
-- The running sum `R₀` lands in 3 cells: this add's output, the NEXT add's input, and its probe.
#guard (classCells posS (px (pSum shapeS 0))).length == 3
-- The endo base point is a 16-cell class (one per endo row).
#guard (classCells posS (px (pEndoT shapeS))).length == 16
-- ⚑ THE ENDO ROW-OVERLAP, exactly. A mid-chain endo accumulator is ONE cell: block 7's `Next` col 4
-- and block 8's `Curr` col 4 are literally the SAME cell of the grid, so the variable's class is a
-- singleton and σ self-wires it. Two `EndoMul` gates read that one cell — a chaining pattern that
-- needs no copy wire at all, and that no prior rung exercised.
#guard classCells posS (px (pEndoAcc shapeS 8)) == [(⟨endoStartS + 8, 4⟩ : Cell)]
#guard permLookup pairsS ⟨endoStartS + 8, 4⟩ == (⟨endoStartS + 8, 4⟩ : Cell)
#guard (rowsS.getD (endoStartS + 7) default).kind == KGateType.endoMul   -- reads it as `Next`
#guard (rowsS.getD (endoStartS + 8) default).kind == KGateType.endoMul   -- reads it as `Curr`
-- The endo term's FINAL accumulator, by contrast, DOES hop: tail Zero row → complete_add → probe.
#guard (classCells posS (px (pEndoAcc shapeS shapeS.endoBlocks))).length == 3
-- Cross-ROW σ pairs (a pair whose two cells are in different rows) — the cross-gate wiring count.
-- Removing the 13 probes costs 28 of them (−1 per 3-cell class × 24 coords, −2 per coord for the
-- final sum's 2-cell class, which becomes a singleton).
#guard (pairsS.filter (fun pr => pr.1.row != pr.2.row)).length == 456
#guard (pairsUnwiredS.filter (fun pr => pr.1.row != pr.2.row)).length == 428
-- No variable-id collision (a collision MERGES classes and shrinks this): 6 terms × (T + 9 accs)
-- × 2 coords + 6 × 9 scalar counters + endo (T + 17 accs) × 2 + 17 endo counters + 6 sums × 2 = 239.
#guard (distinctVars posS).length == 239
#guard posS.length == 529

-- ── The GATE constraints, evaluated on the ASSEMBLED GRID ─────────────────────────────────────
-- ⚑ NON-VACUITY IN LEAN, at scale and per gate type: every emitted row satisfies the SAME
-- constraint bodies the real proof uses (`KimchiVerify`, read-only), over `ZMod pN`, read out of the
-- composed 15×132 witness. A placement bug that never reaches the grid cannot hide from these.
#guard ((rowsS.zip (List.range nRowsS)).filter (fun ri => ri.1.kind == KGateType.varBaseMul)).all
  (fun ri => (varBaseMulConstraints (R := ZMod pN)
      ((gridRow witnessS ri.2).map (fun n => (n : ZMod pN)))
      ((gridRow witnessS (ri.2 + 1)).map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0)))

#guard ((rowsS.zip (List.range nRowsS)).filter (fun ri => ri.1.kind == KGateType.completeAdd)).all
  (fun ri => (completeAddConstraints (R := ZMod pN)
      ((gridRow witnessS ri.2).map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0)))

#guard ((rowsS.zip (List.range nRowsS)).filter (fun ri => ri.1.kind == KGateType.endoMul)).all
  (fun ri => (endoMulConstraints (R := ZMod pN) (KimchiRenderEndoMul.endo : ZMod pN)
      ((gridRow witnessS ri.2).map (fun n => (n : ZMod pN)))
      ((gridRow witnessS (ri.2 + 1)).map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0)))

-- ── The SEMANTICS: this really is an MSM, cross-checked in Jacobian coordinates ──────────────
-- Base points: distinct, on-curve.
#guard (basePts (shapeS.terms + 1)).all onCurveA
#guard ((basePts (shapeS.terms + 1)).map (·.1)).dedup.length == shapeS.terms + 1

-- ⚑ EVERY var_base_mul BIT STEP is `accₖ₊₁ = [2]accₖ + (2bₖ−1)·T`, checked with PastaCurve's
-- INDEPENDENT Jacobian double/add (a different formula family from the affine `stepVbm` that
-- produced the witness), compared without inversion by `jacEqM`.
#guard (List.range shapeS.terms).all (fun i =>
  let td := fragS.terms.getD i default
  let bits := termBits shapeS i
  (List.range (5 * shapeS.chunks)).all (fun k =>
    let a := td.accs.getD k (0, 0)
    let a' := td.accs.getD (k + 1) (0, 0)
    let q := if bits.getD k 0 == 1 then jOf td.T else jNeg (jOf td.T)
    jacEqM pN (jOf a') (jAdd (jDbl (jOf a)) q)))

-- ⚑ EVERY endo_mul BLOCK is `accₑ₊₁ = [2]([2]accₑ + Q₁) + Q₂` with `Qₖ = ±φ^{b}(T)` — the
-- endomorphism selection included — same independent Jacobian oracle.
#guard (List.range shapeS.endoBlocks).all (fun e =>
  let b := fragS.endoBlks.getD e default
  let a := fragS.endoAccs.getD e (0, 0)
  let a' := fragS.endoAccs.getD (e + 1) (0, 0)
  let q1raw : Nat × Nat := (KimchiRenderEndoMul.xqOf b.b1 fragS.endoT.1, fragS.endoT.2)
  let q2raw : Nat × Nat := (KimchiRenderEndoMul.xqOf b.b3 fragS.endoT.1, fragS.endoT.2)
  let q1 := if b.b2 == 1 then jOf q1raw else jNeg (jOf q1raw)
  let q2 := if b.b4 == 1 then jOf q2raw else jNeg (jOf q2raw)
  jacEqM pN (jOf a') (jAdd (jDbl (jAdd (jDbl (jOf a)) q1)) q2))

-- ⚑ THE SCALAR CELL IS TIED TO THE POINT. With `acc₀ = [2]T`, the 5C-bit chain closes to
-- `acc_final = [2^{5C} + 2n + 1]·T` where `n` is EXACTLY the value carried in the last chunk's `n'`
-- cell. So the `n`/`n'` chaining wire is not decoration: the point output and the scalar counter
-- agree, checked against `PastaCurve.scMulM` (an independent 255-bit double-and-add).
#guard (List.range shapeS.terms).all (fun i =>
  let td := fragS.terms.getD i default
  let n := td.ns.getLastD 0
  let k := 2 ^ (5 * shapeS.chunks) + 2 * n + 1
  match scMulM pN k (jOf td.T) with
  | none => false
  | some R => jacEqM pN (jOf (td.accs.getLastD (0, 0))) R)

-- ⚑ THE ACCUMULATOR CHAIN REALLY SUMS THE TERMS. The final `complete_add` output equals the
-- Jacobian fold of all 7 addends (6 var_base_mul outputs + the endo_mul output).
#guard
  (let pts := (List.range shapeS.terms).map (fun i =>
        (fragS.terms.getD i default).accs.getLastD (0, 0))
      ++ [fragS.endoAccs.getLastD (0, 0)]
   let tot := (pts.drop 1).foldl (fun acc p => jAdd acc (jOf p)) (jOf (pts.getD 0 (0, 0)))
   jacEqM pN (jOf (fragS.sums.getLastD (0, 0))) tot)

-- Every add is the distinct-x `add_fast` case: `inf = 0`, `same_x = 0` (so leaving col 6 unwired at
-- 0 is correct, and no add silently lands on the point at infinity).
#guard fragS.addCells.all (fun c => c.getD 6 0 == 0 && c.getD 7 0 == 0)
-- Every accumulator point in every chain is on the Pallas curve.
#guard (List.range shapeS.terms).all (fun i => ((fragS.terms.getD i default).accs).all onCurveA)
#guard fragS.endoAccs.all onCurveA
#guard fragS.sums.all onCurveA
-- The chains are non-degenerate: both bit values occur in every term (both slope signs exercised).
#guard (List.range shapeS.terms).all (fun i =>
  (termBits shapeS i).contains 0 && (termBits shapeS i).contains 1)
#guard (endoBitsOf shapeS).contains 0 && (endoBitsOf shapeS).contains 1

end Dregg2.Circuit.Emit.KimchiComposeStepFragment
