/-
# Dregg2.Bridge.StepMainFtEval0RealBlock — **the SYNTHESIZED `ft_eval0` circuit, run on devnet block
539508's Step side, reproduces `FT_EVAL0` byte-for-byte.**

## WHAT IS NEW HERE, and what is not

`MinaWrapFtEval0Weld` §6 already showed that `KimchiVerify`'s **value layer** — `gateLinConst` over
the six transcribed gate bodies, then `ftEval0R`'s fold — reproduces block 539508's Step-side
`ft_eval0` and linearization constant term. That is a claim about two Lean `def`s.

`KimchiStepMain` §8d compiles that same arithmetic into a STRAIGHT-LINE PROGRAM whose slots become
`Generic` rows of a kimchi circuit (rung `r6_ft_eval0`), and §13 pins the program's values against
the value layer at a synthetic fixture. That is a claim about the compiler, at a fixture we chose.

**This file closes the gap between them.** It instantiates `KimchiStepMain.ftBuild` — the SAME
program the circuit's rows execute, with every wire input a `.lit` of the block's own field value —
at block 539508's Step side, and checks the compiled `ft_eval0` and `linConstTerm` slots against the
anchors `MinaWrapDeferredWeld.FT_EVAL0` and `lct_true`. So the circuit arithmetic is exercised on a
REAL Mina proof's wire, not only on `evVal`.

⚠ WHAT THIS IS NOT. It is not a proof that the circuit ACCEPTS the block: the block's values are
compiled in as constants here, whereas the assembled rung reads its ζ/α/β/γ from the sponge and its
columns from R5's variables. It is not a Mina-valid proof, and it is not soundness. It is
SYNTHESIS-fidelity of the emitted arithmetic against a real block, on the inherited IPA/FRI floor.

## Axiom hygiene / build

`#guard` only, no `sorry`, no `native_decide`. Rooted through `Dregg2.MinaBridgeGuards` (with
`MinaWrapFtEval0Weld` itself), NOT through `Dregg2/FFI.lean`: it pulls the one-block fixtures, whose
kernel cost belongs off the archive's hot path — the same split the weld documents.
-/
import Dregg2.Bridge.MinaWrapFtEval0Weld
import Dregg2.Circuit.Emit.KimchiStepMain
import Dregg2.Bridge.MinaMultiBlockConformance

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Dregg2.Bridge.StepMainFtEval0RealBlock

open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.KimchiVerify (endoMap)
open Dregg2.Circuit.Emit.KimchiStepMain
  (AOp FtWire FtCfg FtProg ftProgOf aEval)
open Dregg2.Bridge.MinaWrapFtEval0 (rootOfUnity quotientConsts)
open Dregg2.Bridge.MinaWrapFtEval0Weld (S539508 OUT_STEP)

/-! ## §1 — block 539508's Step side, as the ft program's WIRE.

Every field is a `.lit`: the compiled program is the same one `r6_ft_eval0`'s rows execute, but here
its inputs are the block's own values rather than the assembly's variables. The slicing (`ez k` is
column `k` of the 43, `IDX_*` index after the four-entry prefix) is `MinaWrapFtEval0`'s, shared. -/

/-! ### §1a — ⚑ THE PROGRAM, AS A FUNCTION OF A BLOCK.

Everything below §1a used to bake block 539508 into the wire, the config AND the two passes, so the
straight-line program the circuit rows execute could only ever be run on one block — the exact
shape that makes a fitted constant invisible. `compiledFtLctOf` takes the SAME `SideWire` the value
layer takes, so `Dregg2.Bridge.MinaMultiBlockConformance` runs the emitted program on every fixture
and the 539508 definitions below are one instance of it rather than the only one. -/

/-- The emitted straight-line program at an arbitrary Step wire: both passes (the placeholder pass
that reads `ω^{n−3}` and the actual `perm` scalar off, then the real one with those witnessed), and
the `(ft_eval0, linConstTerm)` it lands on. ⚑ The domain, the coset shifts, the endo and the MDS all
come from `W`, so nothing here is a constant of one block. -/
def compiledFtLctOf (W : Dregg2.Bridge.MinaWrapFtEval0.SideWire pN) : Nat × Nat :=
  let om := (rootOfUnity pN W.log2n).val
  let zt := (endoMap W.er W.zetaChal).val
  let wire : FtWire :=
    { ez := fun k => .lit (W.ez.getD k 0).val
    , ew := fun k => .lit (W.ew.getD k 0).val
    , zeta := .lit zt
    , alpha := .lit (endoMap W.er W.alphaChal).val
    , beta := .lit (W.betaChal % pN)
    , gamma := .lit (W.gammaChal % pN)
    , pZeta := .lit W.pZeta.val }
  let cfg : Nat → FtCfg := fun dInv =>
    { log2n := W.log2n
    , omega := om
    , omegaInv := Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv om
    , shifts := W.sh.map (·.val)
    , mds9 := W.mds9.map (·.val)
    , endo := W.endo.val
    , cA := match quotientConsts pN with | some (a, _, _) => a.val | none => 0
    , cB := match quotientConsts pN with | some (_, b, _) => b.val | none => 0
    , cC := match quotientConsts pN with | some (_, _, c) => c.val | none => 0
    , denomInv := dInv }
  let p0 := ftProgOf wire (cfg 1)
  let v0 := aEval (fun _ => 0) p0.prog
  let dinv := Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv
    (Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fMul
      (Dregg2.Circuit.Emit.KimchiStepMain.fSub zt (v0.getD p0.slots.omInv3 0))
      (Dregg2.Circuit.Emit.KimchiStepMain.fSub zt 1))
  let p1 := ftProgOf wire (cfg dinv)
  let v1 := aEval (fun _ => 0) p1.prog
  (v1.getD p1.slots.ftEval0 0, v1.getD p1.slots.linConst 0)

/-- ζ, LIFTED — `ScalarChallenge::to_field` with the block's `er`, exactly as `deriveSide` lifts it. -/
def ZETA_STEP : Nat := (endoMap S539508.er S539508.zetaChal).val
/-- α, LIFTED. -/
def ALPHA_STEP : Nat := (endoMap S539508.er S539508.alphaChal).val
/-- β and γ are RAW squeezes, not lifted (`MinaWrapDeferred` §8's slot-5/6/7 correction). -/
def BETA_STEP : Nat := S539508.betaChal % pN
def GAMMA_STEP : Nat := S539508.gammaChal % pN

def OMEGA_STEP : Nat := (rootOfUnity pN S539508.log2n).val
def OMEGA_INV_STEP : Nat := Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv OMEGA_STEP

def W539508 : FtWire :=
  { ez := fun k => .lit (S539508.ez.getD k 0).val
  , ew := fun k => .lit (S539508.ew.getD k 0).val
  , zeta := .lit ZETA_STEP
  , alpha := .lit ALPHA_STEP
  , beta := .lit BETA_STEP
  , gamma := .lit GAMMA_STEP
  , pZeta := .lit S539508.pZeta.val }

/-- The block's CONFIG: its own `domain_log2`, the DERIVED Tick coset shifts (`TickShifts`), the
`fp_kimchi` MDS and the BASE endo `5^((p−1)/3)` the weld corrected to. -/
def C539508 (shifts : List Nat) (dInv : Nat) : FtCfg :=
  { log2n := S539508.log2n
  , omega := OMEGA_STEP
  , omegaInv := OMEGA_INV_STEP
  , shifts := shifts
  , mds9 := S539508.mds9.map (·.val)
  , endo := S539508.endo.val
  , cA := match quotientConsts pN with | some (a, _, _) => a.val | none => 0
  , cB := match quotientConsts pN with | some (_, b, _) => b.val | none => 0
  , cC := match quotientConsts pN with | some (_, _, c) => c.val | none => 0
  , denomInv := dInv }

def SHIFTS_STEP : List Nat := S539508.sh.map (·.val)

/-! ## §2 — the two passes.

The program takes `denomInv` and the deferred `perm` scalar as WITNESSES and CHECKS them with rows
(`denom·denomInv = 1`, `perm_actual = perm_claimed`). Neither witness feeds the values that produce
them, so one pass with placeholders reads them off and the second is the emitted program. -/

/-- The placeholder pass, only to read `ω^{n−3}` and the actual `perm` scalar. -/
def P0 : FtProg := ftProgOf W539508 (C539508 SHIFTS_STEP 1)
def V0 : Array Nat := aEval (fun _ => 0) P0.prog

/-- `(ζ − ω^{n−3})(ζ − 1)`'s inverse — the ONE field inverse `ft_eval0` needs. -/
def DENOM_INV_STEP : Nat :=
  Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv
    (Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fMul
      (Dregg2.Circuit.Emit.KimchiStepMain.fSub ZETA_STEP (V0.getD P0.slots.omInv3 0))
      (Dregg2.Circuit.Emit.KimchiStepMain.fSub ZETA_STEP 1))

/-- **The emitted program**, at block 539508's Step wire. -/
def P1 : FtProg := ftProgOf W539508 (C539508 SHIFTS_STEP DENOM_INV_STEP)
def V1 : Array Nat := aEval (fun _ => 0) P1.prog

/-- The compiled `ft_eval0`. -/
def FT_COMPILED : Nat := V1.getD P1.slots.ftEval0 0
/-- The compiled linearization constant term. -/
def LCT_COMPILED : Nat := V1.getD P1.slots.linConst 0

/-! ## §3 — ⚑ THE ANCHORS. -/

/-- The value `MinaWrapDeferredWeld` SOLVED from public-input slot 0 and `MinaWrapFtEval0Weld` §6a
then reproduced from the wire. -/
def FT_ANCHOR : Nat := Dregg2.Bridge.MinaWrapDeferredWeld.FT_EVAL0
/-- `Scalars.Tick.constant_term` on this block (`MinaWrapFtEval0Weld` §6a's `lct_true`). -/
def LCT_ANCHOR : Nat :=
  20345071543763246608538509185165536352110693439382108600930896203194519173047

-- The wire really is the block's: 43 columns each side, the derived seven shifts, `domain_log2 = 16`.
#guard S539508.ez.length == 43
#guard S539508.ew.length == 43
#guard SHIFTS_STEP.length == 7
#guard S539508.log2n == 16
#guard S539508.mds9.length == 9
-- …and every one of the six gate selectors FIRES on it, so no body of the constant term is
-- multiplied by zero (`MinaWrapFtEval0Weld` §1b's finding, on the Step side).
#guard (List.range 6).all (fun i =>
  S539508.ez.getD (Dregg2.Bridge.MinaWrapFtEval0.IDX_SEL + i) 0 != 0)
-- …and the witnessed inverse is genuine (the row `denom·denomInv = 1` is what the circuit checks).
#guard Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fMul
        (Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fMul
          (Dregg2.Circuit.Emit.KimchiStepMain.fSub ZETA_STEP (V0.getD P0.slots.omInv3 0))
          (Dregg2.Circuit.Emit.KimchiStepMain.fSub ZETA_STEP 1))
        DENOM_INV_STEP == 1

-- ⚑⚑ **THE COMPILED CIRCUIT ARITHMETIC REPRODUCES THE BLOCK.** The straight-line program whose
-- slots ARE `r6_ft_eval0`'s `Generic` rows returns block 539508's `ft_eval0` and its linearization
-- constant term, byte-for-byte.
#guard FT_COMPILED == FT_ANCHOR
#guard LCT_COMPILED == LCT_ANCHOR

-- ⚑ …and the BLOCK-PARAMETRIC entry point (§1a) lands on the same pair at this block's wire, so
-- the seven-fixture sweep in `Dregg2.Bridge.MinaMultiBlockConformance` runs THIS program and not a
-- re-transcription of it. Without this the two could drift and only the 539508 one would be pinned.
#guard compiledFtLctOf S539508 == (FT_ANCHOR, LCT_ANCHOR)

-- …and it agrees with the VALUE LAYER's own answer on the same block, so the compiler and
-- `deriveSide` are two routes to one number rather than one route quoted twice.
#guard match OUT_STEP with
       | some o => o.ftEval0.val == FT_COMPILED && o.linConstTerm.val == LCT_COMPILED
       | none => false

/-! ## §4 — the RED PATHS. Each anchor above is a gate, not an identity.

`MinaWrapFtEval0Weld` §6b showed a bent coset shift moves the value layer's `ft_eval0`. These show it
moves the COMPILED one — i.e. the shifts, the endo and the constant term are load-bearing INSIDE the
program the circuit rows execute. -/

/-- Re-run the program with one input bent. ⚑ A THIN WRAPPER over [`compiledFtLctOf`], so the
"unbent re-run IS the anchor" pin below is about the same code path any block runs. -/
def compiledAt (shifts : List Nat) (endoV : Nat) : Nat :=
  (compiledFtLctOf { S539508 with sh := shifts.map (fun x => (x : ZMod pN))
                                  endo := ((endoV : Nat) : ZMod pN) }).1

/- The unbent re-run IS the anchor (so `compiledAt` is the same program, and the reds below are
about the bend and not about the helper). -/
#guard compiledAt SHIFTS_STEP S539508.endo.val == FT_ANCHOR
/- ⚑ A single bent coset shift moves it. -/
#guard compiledAt (SHIFTS_STEP.set 1 ((SHIFTS_STEP.getD 1 0) + 1)) S539508.endo.val != FT_ANCHOR
/- ⚑ The identity placeholder — seven 1s where cosets belong — moves it. -/
#guard compiledAt (List.replicate 7 1) S539508.endo.val != FT_ANCHOR
/- ⚑ THE ENDO CONFLATION SHOWS HERE. `er` (the scalar-challenge endo) in place of the BASE endo
`5^((p−1)/3)` is the exact defect `MinaWrapFtEval0Weld` closed; the compiled program refuses it. -/
#guard compiledAt SHIFTS_STEP S539508.er.val != FT_ANCHOR
#guard S539508.er.val != S539508.endo.val
/- …and both really are cube roots of unity, so the two are a genuine near-miss and not a typo. -/
#guard (S539508.endo : ZMod pN) ^ 3 == (1 : ZMod pN)
#guard (S539508.er : ZMod pN) ^ 3 == (1 : ZMod pN)

/-! ## §5 — the program is the one the CIRCUIT runs.

`r6_ft_eval0`'s rows are `aRows (baseFtS s) prog` for the program `ftBuild` returns; the only thing
that differs here is where the wire values come from. These pin that: the two programs have the SAME
operation sequence up to their `.inp`/`.lit` sources, so the row schedule this file's values flow
through is the emitted one. -/

/-- The assembled instance's program, at the CI smoke shape. -/
def PA : FtProg := Dregg2.Circuit.Emit.KimchiStepMain.tS.ft.fp

/-- Erase a program's leaf SOURCES, keeping its operation skeleton. -/
def skeleton (prog : Array AOp) : List AOp :=
  prog.toList.map (fun o => match o with
    | .inp _ => .lit 0
    | .wit _ => .lit 0
    | .lit _ => .lit 0
    | o => o)

#guard skeleton P1.prog == skeleton PA.prog
#guard P1.slots.ftEval0 == PA.slots.ftEval0
#guard P1.slots.linConst == PA.slots.linConst
#guard P1.slots.perm == PA.slots.perm
/- …and the skeleton is not trivially equal to everything: a program built at a DIFFERENT domain has
a different one (`ζ^n` is `log2n` squarings), so the pin above is discriminating. -/
#guard (skeleton (ftProgOf W539508 (C539508 SHIFTS_STEP 1)).prog
         == skeleton (ftProgOf W539508 { C539508 SHIFTS_STEP 1 with log2n := 15 }).prog) == false

/-! ## §6 — R8's `Shifted_value.Type1` shift, from TWO independent sources.

`KimchiStepMain` §8f defines its own `shiftT1`/`unshiftT1` because that module must not import the
deferred-values bridge. A constant checked against its own definition is decoration; these check the
circuit's shift against `MinaWrapDeferred`'s — which is the map whose output `MinaWrapDeferredWeld`
compares to block 539508's ACTUAL public-input words. So the unshifts R8 emits are the encoding a
real Wrap statement wears, not a locally-consistent one. -/

open Dregg2.Circuit.Emit.KimchiStepMain (SHIFT_C shiftT1 unshiftT1 shiftT2)

#guard SHIFT_C == Dregg2.Bridge.MinaWrapDeferred.SHIFT_C
#guard (List.range 8).all (fun i =>
  let x := (7 + 1000003 * i) % pN
  shiftT1 x == Dregg2.Bridge.MinaWrapDeferred.shiftType1 x
  && unshiftT1 (shiftT1 x) == x
  && Dregg2.Bridge.MinaWrapDeferred.unshiftType1 (shiftT1 x) == x)
-- …and the two anchors of this file wear it too: `FT_EVAL0` shifted and unshifted round-trips, and
-- the Type2 (subtract-only) reading of the SAME word is a different field element.
#guard unshiftT1 (shiftT1 FT_ANCHOR) == FT_ANCHOR
#guard shiftT1 FT_ANCHOR != shiftT2 FT_ANCHOR
#guard shiftT1 FT_ANCHOR != FT_ANCHOR

/-! ## §5 — ⚑⚑ THE EMITTED PROGRAM ON EVERY FIXTURE, NOT ONLY ON 539508.

Everything above this section is about ONE block. `Dregg2.Bridge.MinaMultiBlockConformance` carries
seven — five devnet (including the hardfork genesis), one mainnet, and 539508 as the control — each
with its OWN inputs from an independent binprot re-walk and its OWN targets from openmina. This
section runs the SAME compiled program (`compiledFtLctOf`, §1a) on each of them.

⚑ What this adds over that module's own §1: that module checks the VALUE LAYER (`deriveSide`). This
checks the STRAIGHT-LINE PROGRAM whose slots become `r6_ft_eval0`'s `Generic` rows — and then feeds
ITS output through `expandDeferred` to the block's six `expand_deferred` words. So the arithmetic
the circuit rows execute is what reaches openmina's answer, on seven blocks. -/

open Dregg2.Bridge.MinaMultiBlockConformance (StepBlock STEP_BLOCKS stepWire evalsOf stepFtEval0)

/-- The COMPILED `ft_eval0` at a fixture's Step wire. -/
def compiledFtOf (b : StepBlock) : Nat := (compiledFtLctOf (stepWire b)).1

/-- ⚑ The compiler and the value layer land on ONE number, AND that number carries the block's six
deferred words to openmina's own `expand_deferred` answers. -/
def compiledAgrees (b : StepBlock) : Bool :=
  stepFtEval0 b == some (compiledFtOf b) &&
  (let d := Dregg2.Bridge.MinaWrapDeferred.expandDeferred (evalsOf b) (compiledFtOf b)
   d.cip == b.tCip && d.b == b.tB && d.zetaToSrsLength == b.tZsrs
   && d.zetaToDomainSize == b.tZdom && d.perm == b.tPerm && d.xi == b.tXi)

/- ⚑⚑ **THE RESULT.** The emitted circuit program reproduces every fixture's `ft_eval0`, and that
`ft_eval0` reproduces every fixture's six deferred words. Until this line the program had been run
on exactly one block. -/
#guard STEP_BLOCKS.all compiledAgrees
#guard STEP_BLOCKS.length == 7

/- …and the sweep is a GATE, not an identity: bending an input of the first fixture refuses. -/
#guard match STEP_BLOCKS with
       | b :: _ => !(compiledAgrees { b with evals := b.evals.set 37 (0, 0) })
       | [] => false
#guard match STEP_BLOCKS with
       | b :: _ => !(compiledAgrees { b with domainLog2 := 15 })
       | [] => false
/- ⚑ …and one fixture's compiled answer is not another's, so the seven are seven measurements. -/
#guard (STEP_BLOCKS.map compiledFtOf).dedup.length == STEP_BLOCKS.length

/-! ### §5b — ⚠ THE ONE THING SEVEN BLOCKS CANNOT SETTLE, said plainly.

§3b's `skeleton P1.prog == skeleton PA.prog` pins that the program run here IS the one the assembly
emits. It holds because `S539508.log2n` and `KimchiStepMain.FT_LOG2N` are BOTH 16 — and the file's
own §3b discriminator shows the skeletons differ across domains. **Measured over 40 consecutive
devnet blocks: every blockchain-SNARK Wrap proof carries `branch_data.domain_log2 = 16`**, because
that is a property of the Pickles RULE and not of the instance. So no additional block proof can
separate those two 16s, and the sweep above must not be read as evidence that it does. What the
sweep does establish is that every OTHER input of the program — the columns, the challenges, the
coset shifts, the endo, `p(ζ)` — is genuinely read per block. -/

end Dregg2.Bridge.StepMainFtEval0RealBlock
