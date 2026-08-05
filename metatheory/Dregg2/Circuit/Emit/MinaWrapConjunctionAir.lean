/-
# `Dregg2.Circuit.Emit.MinaWrapConjunctionAir` — ONE emitted object that makes the conjunction
upstream's verifier makes, and a precise statement of what it does and does not force.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** Every column index, every gate body, the bind leg and the emitted
descriptor are authored here and go through `EffectLower.lowerAir` of an `EffectAirIR.EffectAir`.
There is no hand-written `VmConstraint2` in this file. Rust PROVES the artifact and authors no
constraint. House Law #1.

## THE GAP THIS CLOSES

Upstream's wrap verifier makes ONE decision out of TWO halves — `verify.ml`'s
`finalize_other_proof ∧ bulletproof_success`. This tree had both halves and no conjunction:

* `PicklesFinalize.finalizeOtherProof` (`:278`) is a Lean `Bool` over `[CommRing R]`, in **no
  `EffectAir`, no `lowerAir`, no descriptor** — pure spec.
* `MinaWrapOpeningGate.openingResidual` (`:599`) is a **kernel evaluation on one real block**, not
  an AIR; the AIR that does exist for it (`PastaMsmAir.minaOpeningCheckDesc`) is **row-local and
  would be refused by the deployed prover** (`traceWidth := 442` against constraints addressing
  columns near `10^7`; `circuit/src/descriptor_ir2.rs:1555`).

Two objects that each prove and never meet. This file is the object where they meet.

## ⚑ WHERE THE TWO HALVES ACTUALLY TOUCH — and it is not a bus, it is three scalars

The conjunction is not "put both circuits in one file". It is the fact that the SAME deferred
values are the ones finalize checks arithmetically and the ones the bulletproof consumes as scalars.
Read off `MinaWrapOpeningGate.residualTerms` (`:588-595`), the opening's term list is

    lrTerms c chals chalInvs
      ++ [(c, cc), (c·cip − z1·b0, ub), (−z1, sg), (−z2, SRS_H)]

and the three coefficients that are NOT free are exactly finalize's checked slots:

| the opening consumes | finalize checks it in |
|---|---|
| `b0` — in the `ub` coefficient `c·cip − z1·b0` | `bCorrect` (`decode dv.b = bActualOf …`) |
| `cip` — in the same coefficient | `cipCorrect` |
| the 15 `chals` — scaling every `L_j`/`R_j` in `lrTerms` | `bActualOf`, via `bEval` over the SAME list |

⚑ **So the seam is the `ub` coefficient and the challenge vector**, and a conjunction that shares
those columns is the conjunction; one that re-pins them from public inputs on each side is two
descriptors wearing one name. This file shares the COLUMNS: `bEvalLegs` recomputes `b0` from the
challenge blocks `CHAL 0 … CHAL 14`, and `lrCoefLegs` scales `L_j`/`R_j` by `c` times **those same
blocks**. There is one challenge vector in this trace and both halves read it.

## ⚑ WHAT THIS OBJECT FORCES — stated at this tree's resolution, not at the name's

Emitted and forced (`conjunction_forces`):

1. **`xiCorrect`** — at full fidelity (`op.xiSqueeze = dv.xi`).
2. **`bCorrect`** — at full fidelity. The b-polynomial `bEval` is recomputed IN CIRCUIT at ζ and at
   ζω over the 15 shared challenge blocks, combined by `r`, and compared to the claimed `b` slot,
   every step on `PastaFieldSound`/`PastaAddSubSound`'s SOUND cores at the Pallas-scalar prime `q`.
   **This is the conjunct that shares state with the opening**, which is why it is the one built at
   full depth.
3. **The challenge/inverse reciprocity** — `chal_j · chalinv_j ≡ 1 (mod q)` for all 15, so the
   inverses `lrTerms` scales `L_j` by are the inverses OF the challenges `bEval` consumed. Without
   it the two halves could read two unrelated 15-vectors while every gate passed.
4. **The opening's non-free coefficients** — `c·cip − z1·b0`, `−z1`, `−z2`, and the 30 `c·chal`/
   `c·chalinv` products, each computed by a sound core from the SHARED columns.
5. **The MSM itself, by recursion** — one `AirLeg.bind` whose `bound` lanes are this row's own
   coefficient columns, so the sub-proof's public-input commitment is tied to the values this row
   computed rather than to a public input the prover chooses. That is the phase-2 chain's lesson
   applied at the AIR level: state carried INSIDE the recursion.

⚠ **NOT emitted, and named rather than stubbed: `cipCorrect` and `plonkChecksPassed`.**

`cipCorrect` compares the claimed `combined_inner_product` against `cipActualOf`, whose `ft_eval0`
slot is `ftEval0Of` — K5's gate linearization. **A gate comparing `cip` against a ξ-fold with a FREE
`ft_eval0` column would force nothing at all**: `ft_eval0` free makes the fold's value free, so the
comparison accepts every `cip`. That is the `∃`-image vacuity this tree has already shipped once and
it is not shipped here. The honest cost of the real one is the linearization chain, which
`PicklesFinalize` has as a spec and no emitter has as legs; it is the next lane, not a caveat on
this one. `plonkChecksPassed`'s `permScalarR` is the same shape and smaller.

So the plain answer to *"does one object now make the claim upstream's verifier makes"* is: **it
makes two of finalize's four conjuncts, the reciprocity that welds the two halves' challenge
vectors, and the opening's coefficient seam — in one descriptor, over shared columns.** It does not
yet make `cipCorrect ∧ plonkChecksPassed`. Upstream's conjunction is a four-way AND with the
opening; this is a two-way AND with the opening, and the missing two are LOCATED (the K5
linearization chain), not hand-waved.

⚠ **AND SAY THE OTHER THING PRECISELY.** `G`/`z₁`/`z₂` are **free witnesses in `openings_proof`,
and that is FAITHFUL to upstream** (`wrap_main.ml:357-382`): one equation over three free legs,
bound by the *next* proof's `finalize_other_proof`. So `equal_g` refuses no on-curve substitution,
and neither does this object. That is not a defect of this emission and it is not to be "fixed" —
it is what the recursion means, and the binding arrives one proof later.

## Axiom hygiene

`#assert_axioms`-clean; no `sorry`/`admit`/`native_decide`; zero `#guard`s.
-/
import Dregg2.Circuit.Emit.PastaLadderThread
import Dregg2.Circuit.Emit.PastaIPA

namespace Dregg2.Circuit.Emit.MinaWrapConjunctionAir

open Dregg2.Circuit (Assignment Expr Constraint)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 TableDef TableId mainTableDef VmConstraint2)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LimbsLeg BindLeg)
open Dregg2.Circuit.Emit.EffectLower (lowerAir P)
open Dregg2.Circuit.Emit.PastaField (qN)
open Dregg2.Circuit.Emit.PastaFieldSound
open Dregg2.Circuit.Emit.PastaAddSubSound
open Dregg2.Circuit.Emit.PastaCurve (CZm CZq)
open Dregg2.Circuit.Emit.PastaCurveSound

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §1 — THE SHARED TRANSCRIPT, as columns.

Every quantity is a `SK = 32`-limb sound-encoded field element at the Pallas-SCALAR prime `q` —
which is the right field: `residualTerms` reduces every coefficient `% qN`, and `finalize`'s
deferred scalars are the same field. The GROUP side is mod `p` and lives in the sub-proof this row
binds to (`PastaLadderThread`), which is why the two moduli never meet inside one gate. -/

/-- The number of IPA round challenges the block carries (`MinaWrapOpeningGate.CHAL.length`). -/
def NCHAL : Nat := 15

/-- Block `i`'s base column. -/
def blk (i : Nat) : Nat := SK * i

/-- `op.xiSqueeze` — the squeezed ξ. -/
def XI_SQ : Nat := blk 0
/-- `dv.xi` — the ξ the deferred record CLAIMS. -/
def XI_CL : Nat := blk 1
/-- `decode dv.b` — the claimed `b0`. -/
def B_CL : Nat := blk 2
/-- `z1` from `openings_proof`. -/
def Z1 : Nat := blk 3
/-- `z2` from `openings_proof`. -/
def Z2 : Nat := blk 4
/-- the IPA evaluation-point challenge `c`. -/
def C_COL : Nat := blk 5
/-- `decode dv.combinedInnerProduct`. -/
def CIP : Nat := blk 6
/-- ζ, endo-mapped. -/
def ZETA : Nat := blk 7
/-- ζω. -/
def ZETAW : Nat := blk 8
/-- the `r` squeeze that combines the two evaluation columns. -/
def RSQ : Nat := blk 9
/-- The constant `1`, as a block — a sound core adds two BLOCKS, so `1 + c·x^k` needs one. -/
def ONE : Nat := blk 10
/-- The constant `0`, for the two negations `−z1`, `−z2`. -/
def ZERO : Nat := blk 11

/-- The `j`-th IPA round challenge. -/
def CHAL (j : Nat) : Nat := blk (12 + j)
/-- The `j`-th round challenge's INVERSE — the scalar `lrTerms` puts on `L_j`. -/
def CHALINV (j : Nat) : Nat := blk (12 + NCHAL + j)

/-- Input blocks: 12 named + 15 challenges + 15 inverses. -/
def NIN : Nat := 12 + 2 * NCHAL
/-- …and the column where the scratch begins. -/
def SCRATCH : Nat := SK * NIN

theorem nin_eq : NIN = 42 := by decide
theorem scratch_eq : SCRATCH = 1344 := by decide

/-! ## §2 — THE SSA ALLOCATOR.

Same discipline as `PastaCurveSound.{vBase, mWit, sWit, aWit}`: value blocks first, then the
multiply witnesses, then the add/sub witnesses, each at its own stride, so a caller can allocate by
index and every base is a closed-form `Nat`. -/

/-- Value blocks this AIR computes. Counted in §4 and pinned by `chain_shape`. -/
def NVAL : Nat := 200
/-- Multiplies. -/
def NMUL : Nat := 140
/-- Add/subs. -/
def NADD : Nat := 40

/-- The `i`-th computed value block. -/
def vB (i : Nat) : Nat := SCRATCH + SK * i
/-- The `k`-th multiply's private witness: 32 quotient limbs then 62 carries. -/
def mW (k : Nat) : Nat := SCRATCH + SK * NVAL + (SK + (NG - 1)) * k
/-- The `k`-th add/sub's private witness: the carry bit then 31 carries. -/
def aW (k : Nat) : Nat := SCRATCH + SK * NVAL + (SK + (NG - 1)) * NMUL + SK * k

/-- The declared main width. -/
def CJ_WIDTH : Nat := SCRATCH + SK * NVAL + (SK + (NG - 1)) * NMUL + SK * NADD

theorem cj_width_eq : CJ_WIDTH = 22184 := by decide

/-! ## §3 — THE CORES, at the Pallas-scalar prime `q`. -/

/-- The sound multiply at `q`. -/
def mulQ : SoundCore := mulCore qLimb
/-- The sound add at `q`. -/
def addQ : SoundCore := addSubCore qLimb 1 (-1)
/-- The sound subtract at `q`. -/
def subQ : SoundCore := addSubCore qLimb (-1) 1

/-- `z := x · y`, at value slot `i` and multiply witness `k`. -/
def mulAt (xB yB i k : Nat) : List AirLeg := mulQ.legs xB yB (vB i) (mW k)
/-- `z := x + y`. -/
def addAt (xB yB i k : Nat) : List AirLeg := addQ.legs xB yB (vB i) (aW k)
/-- `z := x − y`. -/
def subAt (xB yB i k : Nat) : List AirLeg := subQ.legs xB yB (vB i) (aW k)

/-- ⚑ **LIMBWISE EQUALITY** between two blocks — `SK` flat gates.

This is STRICTLY STRONGER than the spec's field equality: two blocks may be congruent mod `q` and
differ limbwise. The direction that matters for a verifier is the one that holds — a satisfying
assignment forces limbwise equality, which forces `sVal` equality, which forces the congruence the
spec asks for. Completeness holds for the canonical witness the honest prover writes, which is the
only one `EmitMinaConjunction` generates. -/
def eqBlock (aB bB : Nat) : List AirLeg :=
  (List.range SK).map (fun i =>
    AirLeg.gate ⟨.add (.var (aB + i)) (.mul (.const (-1)) (.var (bB + i))), .const 0⟩)

/-- A block pinned to a small constant: limb 0 is `k`, limbs `1 …` are `0`. -/
def constBlock (bB k : Nat) : List AirLeg :=
  AirLeg.gate ⟨.add (.var bB) (.const (-(k : ℤ))), .const 0⟩
  :: (List.range (SK - 1)).map (fun i => AirLeg.gate ⟨.var (bB + 1 + i), .const 0⟩)

/-! ## §4 — ⚑ THE b-POLYNOMIAL, IN CIRCUIT.

`PastaIPA.bEval x (c :: rest) = bEval x rest * (1 + c · x^(2^|rest|))`. Over a 15-element list the
factors need `x^(2^m)` for `m = 0 … 14`, which is 14 repeated squarings; then one product and one
add per challenge, then 14 multiplies to fold. **43 multiplies and 15 adds per evaluation point.**

The allocation below is explicit rather than monadic on purpose: an `Array` in `whnf` is its `List`
model, so nothing built in `StateM (Array _)` is kernel-reachable, and every base here has to be a
closed-form `Nat` for `decide` to see through it. -/

/-- Squaring chain slot: `sq e m` is `x_e^(2^m)`, for evaluation point `e ∈ {0, 1}`. `m = 0` is the
point itself and is NOT a computed slot. -/
def SQ (e m : Nat) : Nat := 0 + e * 14 + (m - 1)
/-- The product slot `c_j · x_e^(2^(14-j))`. -/
def PRD (e j : Nat) : Nat := 28 + e * NCHAL + j
/-- The `1 + …` slot. -/
def SUM (e j : Nat) : Nat := 58 + e * NCHAL + j
/-- The running-product slot: `FLD e j = ∏_{i ≤ j} (1 + c_i · …)`. -/
def FLD (e j : Nat) : Nat := 88 + e * NCHAL + j

/-- Multiply-witness indices, disjoint by construction and pinned by `chain_shape`. -/
def MK_SQ (e m : Nat) : Nat := 0 + e * 14 + (m - 1)
def MK_PRD (e j : Nat) : Nat := 28 + e * NCHAL + j
def MK_FLD (e j : Nat) : Nat := 58 + e * NCHAL + j
def AK_SUM (e j : Nat) : Nat := 0 + e * NCHAL + j

/-- The evaluation point's own block: ζ for `e = 0`, ζω for `e = 1`. -/
def PT (e : Nat) : Nat := if e = 0 then ZETA else ZETAW

/-- `x^(2^m)`'s column: `m = 0` is the point itself, else the squaring slot. -/
def powCol (e m : Nat) : Nat := if m = 0 then PT e else vB (SQ e m)

/-- The 14 squarings for evaluation point `e`. -/
def sqLegs (e : Nat) : List AirLeg :=
  (List.range 14).flatMap (fun m =>
    mulAt (powCol e m) (powCol e m) (SQ e (m + 1)) (MK_SQ e (m + 1)))

/-- The 15 products `c_j · x^(2^(14-j))`. Head of the challenge list is the HIGHEST round, matching
`bEval`'s outer-to-inner order, so challenge `j` pairs with exponent `2^(14-j)`. -/
def prdLegs (e : Nat) : List AirLeg :=
  (List.range NCHAL).flatMap (fun j =>
    mulAt (CHAL j) (powCol e (NCHAL - 1 - j)) (PRD e j) (MK_PRD e j))

/-- The 15 adds `1 + c_j · x^(2^(14-j))`. -/
def sumLegs (e : Nat) : List AirLeg :=
  (List.range NCHAL).flatMap (fun j =>
    addAt ONE (vB (PRD e j)) (SUM e j) (AK_SUM e j))

/-- The 14-multiply fold. `FLD e 0` is a copy of `SUM e 0` (one limbwise equality, no multiply);
`FLD e (j+1) = FLD e j · SUM e (j+1)`. -/
def fldLegs (e : Nat) : List AirLeg :=
  eqBlock (vB (FLD e 0)) (vB (SUM e 0))
  ++ (List.range (NCHAL - 1)).flatMap (fun j =>
      mulAt (vB (FLD e j)) (vB (SUM e (j + 1))) (FLD e (j + 1)) (MK_FLD e j))

/-- `bEval x_e chals` lands in `vB (FLD e 14)`. -/
def bEvalCol (e : Nat) : Nat := vB (FLD e (NCHAL - 1))

/-- The whole b-polynomial evaluation at point `e`. -/
def bEvalLegs (e : Nat) : List AirLeg := sqLegs e ++ prdLegs e ++ sumLegs e ++ fldLegs e

/-- ⚑ **`bActualOf` = `bEval(ζ) + r · bEval(ζω)`** — the last two ops, then the comparison against
the claimed slot. This is `bCorrect`, emitted. -/
def RB_SLOT : Nat := 118
def B_ACT : Nat := 119
def MK_RB : Nat := 88
def AK_B : Nat := 30

def bCorrectLegs : List AirLeg :=
  bEvalLegs 0 ++ bEvalLegs 1
  ++ mulAt RSQ (bEvalCol 1) RB_SLOT MK_RB
  ++ addAt (bEvalCol 0) (vB RB_SLOT) B_ACT AK_B
  ++ eqBlock (vB B_ACT) B_CL

/-! ## §5 — ⚑ THE RECIPROCITY, which is what welds the two halves' challenge vectors.

`bEval` consumes `CHAL j`; `lrTerms` scales `L_j` by `c · chalinv_j`. Nothing so far says those are
the same 15 values in inverse pairs — and if nothing does, the opening and the finalize check read
two unrelated vectors while every gate passes. `chal_j · chalinv_j ≡ 1 (mod q)` is the weld, one
sound multiply and one limbwise comparison against the pinned `ONE` block, fifteen times. -/

def RCP (j : Nat) : Nat := 120 + j
def MK_RCP (j : Nat) : Nat := 89 + j

def reciprocityLegs : List AirLeg :=
  (List.range NCHAL).flatMap (fun j =>
    mulAt (CHAL j) (CHALINV j) (RCP j) (MK_RCP j) ++ eqBlock (vB (RCP j)) ONE)

/-! ## §6 — ⚑ THE OPENING'S NON-FREE COEFFICIENTS.

`residualTerms`' four tail terms and its 30 `lrTerms` scalars, computed from the SHARED columns. The
`ub` coefficient `c·cip − z1·b0` is the one that reads BOTH finalize-checked slots, and it is the
single expression in which the two halves of upstream's conjunction are the same arithmetic. -/

def CCIP : Nat := 135
def Z1B0 : Nat := 136
def UBC : Nat := 137
def NEG_Z1 : Nat := 138
def NEG_Z2 : Nat := 139
def LC (j : Nat) : Nat := 140 + j
def RC (j : Nat) : Nat := 155 + j

def MK_CCIP : Nat := 104
def MK_Z1B0 : Nat := 105
def MK_LC (j : Nat) : Nat := 106 + j
def MK_RC (j : Nat) : Nat := 121 + j
def AK_UBC : Nat := 31
def AK_NZ1 : Nat := 32
def AK_NZ2 : Nat := 33

/-- ⚑ **THE SEAM ITSELF**: `ubc = c·cip − z1·b0`, over the same `CIP` and `B_CL` columns
`cipCorrect` and `bCorrect` name. -/
def ubCoefLegs : List AirLeg :=
  mulAt C_COL CIP CCIP MK_CCIP
  ++ mulAt Z1 B_CL Z1B0 MK_Z1B0
  ++ subAt (vB CCIP) (vB Z1B0) UBC AK_UBC

/-- `−z1` and `−z2`, as `0 − z`. -/
def negCoefLegs : List AirLeg :=
  subAt ZERO Z1 NEG_Z1 AK_NZ1 ++ subAt ZERO Z2 NEG_Z2 AK_NZ2

/-- The 30 `lrTerms` scalars `c·chalinv_j` (on `L_j`) and `c·chal_j` (on `R_j`) — the SAME challenge
blocks the b-polynomial consumed. -/
def lrCoefLegs : List AirLeg :=
  (List.range NCHAL).flatMap (fun j => mulAt C_COL (CHALINV j) (LC j) (MK_LC j))
  ++ (List.range NCHAL).flatMap (fun j => mulAt C_COL (CHAL j) (RC j) (MK_RC j))

/-! ## §7 — ⚑ THE RECURSION BIND: the MSM, folded, with the state INSIDE.

The 34-term MSM is the threaded ladder (`PastaLadderThread.pallasThreadDesc`), and this row declares
that a VERIFYING sub-proof of it exists whose public-input commitment is **this row's own
coefficient columns**. That is the distinction the phase-2 chain paid for: `bound` is a list of ROW
EXPRESSIONS, not a public input, so the fold cannot be satisfied by re-pinning agreed values on both
sides — the committed lanes are the very cells `ubCoefLegs` and `lrCoefLegs` just forced.

`BindLeg.mainRailOk` refuses a seam that pins neither program nor commitment, and one narrower than
`PROOF_BIND_MIN_LANES = 8` (a limb tie is worth `2^31` against a ~124-bit bar). Eight lanes are
declared and the guard is the pinned `ONE` block's limb 0. -/

/-- The program VK lanes of the threaded-ladder sub-proof, as a block. -/
def LADDER_VK : Nat := 170
/-- The sub-proof's PI-commitment lanes, as a block. -/
def LADDER_COMMIT : Nat := 171

/-- The eight lanes the seam ties: the `ub` coefficient, the two negations, and the first five
`lrTerms` scalars — all of them cells this row's own gates forced. -/
def boundLanes : List Expr :=
  [ .var (vB UBC), .var (vB NEG_Z1), .var (vB NEG_Z2)
  , .var (vB (LC 0)), .var (vB (LC 1)), .var (vB (RC 0)), .var (vB (RC 1)), .var (vB CCIP) ]

/-- ⚑ **THE COMMITMENT IS PINNED; THE PROGRAM IS NOT — and that is stated, not fabricated.**

`BindLeg.mainRailOk` accepts a leg that pins EITHER half. This one pins `bound` — the eight lanes
are this row's own forced coefficient cells — and leaves `vkPin := none`.

⚠ **So the seam says "a verifying proof of SOME program about exactly these coefficients", not "of
THE threaded-ladder program".** The honest reason is that the program's VK is a digest of the built
artifact, which this file cannot compute and must not invent: an eight-lane literal written here
would be a pin against nothing, and this campaign has already found a ROM binding discharged over a
carrier whose docblock claimed more than its statement. The pin belongs to the emitter, which reads
the built `dregg-pasta-pallas-rcb-thread::v1` and fills it. Until it does, the sub-proof's PROGRAM
is unpinned and this file says so here rather than in a summary. -/
def bindLeg : AirLeg :=
  .bind { guard := .var ONE
        , commit := (List.range 8).map (fun i => .var (vB LADDER_COMMIT + i))
        , vk := (List.range 8).map (fun i => .var (vB LADDER_VK + i))
        , vkPin := none
        , bound := some boundLanes }

/-! ## §8 — THE AIR. -/

/-- The three range tables — the union `PastaFieldSound` and `PastaAddSubSound` declare, and nothing
new. -/
def cjTables : List TableDef :=
  [ mainTableDef CJ_WIDTH
  , ⟨rangeTidW SB, "range_w8", 1, .rangeLimb SB⟩
  , ⟨rangeTidW CB, "range_w16", 1, .rangeLimb CB⟩
  , ⟨rangeTidW CBITS, "range_w1", 1, .rangeLimb CBITS⟩ ]

/-- The input blocks' range lookups — the shared transcript is a WITNESS and every limb of it is
range-checked, which is what makes the sound cores' bounds hold on it. -/
def inputRangeLegs : List AirLeg :=
  (List.range NIN).map (fun i => AirLeg.limbs ⟨limbCols (blk i), SB, rangeTidW SB⟩)

/-- The two pinned constants. -/
def constLegs : List AirLeg := constBlock ONE 1 ++ constBlock ZERO 0

/-- ⚑ **`xiCorrect`, emitted** — `op.xiSqueeze = dv.xi`, limbwise. The one conjunct of
`finalizeOtherProof` that is pure equality and needs no recomputation. -/
def xiCorrectLegs : List AirLeg := eqBlock XI_SQ XI_CL

/-- ⚑ **THE CONJUNCTION AIR.** One object: finalize's `xiCorrect` and `bCorrect`, the reciprocity
weld, the opening's non-free coefficients, and the recursion bind to the threaded MSM. -/
def conjunctionAir : EffectAir :=
  { tables := cjTables
  , legs := inputRangeLegs ++ constLegs
      ++ xiCorrectLegs
      ++ bCorrectLegs
      ++ reciprocityLegs
      ++ ubCoefLegs ++ negCoefLegs ++ lrCoefLegs
      ++ [bindLeg] }

/-- ⚑ **THE COMPILER ACCEPTS IT.** Every leg has a deployed main-rail image — for the limbs legs the
`0 < bits ≤ 29` verdict, for the bind leg the pinned-and-wide-enough verdict. A seam narrower than
eight lanes, or one pinning neither program nor commitment, would emit `refuseConstraints` and this
would be false. -/
theorem conjunctionAir_mainRailOk : conjunctionAir.mainRailOk = true := by decide

/-- ⚑ **EXACTLY ONE SEAM, AND IT IS NOT THE DECLARATIVE SHAPE.** One bind leg; its commitment half
is pinned to eight row expressions and its lane count meets `PROOF_BIND_MIN_LANES`. A leg pinning
NEITHER half is `ProofBind.isDeclarative` — an existential over every program and every statement —
and `mainRailOk` refuses it; that refusal is what `conjunctionAir_mainRailOk` rides on.

⚠ The `vkPin` half is `none` here, deliberately and for the reason given at `bindLeg`. -/
theorem conjunctionAir_bind_shape :
    conjunctionAir.bindCount = 1
    ∧ boundLanes.length = 8
    ∧ (match bindLeg with | .bind b => b.bound.isSome ∧ b.vkPin.isNone | _ => False) := by
  refine ⟨by decide, by decide, ?_⟩
  exact ⟨by decide, by decide⟩

def conjunctionDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-mina-wrap-conjunction::v1" CJ_WIDTH 0 [] conjunctionAir

theorem conjunctionDesc_width : conjunctionDesc.traceWidth = CJ_WIDTH := rfl

/-! ## §9 — ⚑ WHAT SATISFACTION FORCES.

The bridge from the emitted legs to `PicklesFinalize`'s `Bool`. Same shape as
`LightClientEthAir.ethLcAir_sound`: a `Prop` reading of the source constraints, then a theorem that
it implies the spec's decision. -/

/-- `eqBlock`'s gates, read as a fact about an assignment. -/
def BlockEq (a : Assignment) (xB yB : Nat) : Prop := ∀ i, i < SK → a (xB + i) = a (yB + i)

/-- The `i`-th gate `eqBlock` emits, as a `Constraint`. -/
def eqConstr (xB yB i : Nat) : Constraint :=
  ⟨.add (.var (xB + i)) (.mul (.const (-1)) (.var (yB + i))), .const 0⟩

/-- ⚑ **THE EMITTED LEG IS THAT GATE** — by `rfl`, so the bridge below is about the object the
compiler lowers and not about a re-description of it. -/
theorem eqBlock_is_eqConstrs (xB yB : Nat) :
    eqBlock xB yB = (List.range SK).map (fun i => AirLeg.gate (eqConstr xB yB i)) := rfl

/-- ⚑ **AND SATISFYING IT IS LIMBWISE EQUALITY** — the `iff`, so the gate cannot be satisfied by
anything else. This is the step that makes `conjunction_forces` a statement about the DEPLOYED
constraint rather than about a `Prop` invented alongside it. -/
theorem eqConstr_holds_iff (a : Assignment) (xB yB i : Nat) :
    (eqConstr xB yB i).holds a ↔ a (xB + i) = a (yB + i) := by
  unfold Constraint.holds eqConstr
  simp only [Expr.eval]
  constructor <;> intro h <;> linarith

/-- The whole block's gates holding IS `BlockEq`. -/
theorem blockEq_of_gates (a : Assignment) (xB yB : Nat)
    (h : ∀ i, i < SK → (eqConstr xB yB i).holds a) : BlockEq a xB yB :=
  fun i hi => (eqConstr_holds_iff a xB yB i).mp (h i hi)

/-- Limbwise equality forces the VALUE equality the spec compares. -/
theorem blockEq_sVal (a : Assignment) (xB yB : Nat) (h : BlockEq a xB yB) :
    sVal a xB = sVal a yB :=
  Dregg2.Circuit.Emit.PastaLadderThread.sVal_congr a a xB yB h

/-- ⚑ **`xi_forced`** — a trace satisfying the emitted `xiCorrect` legs has
`sVal a XI_SQ = sVal a XI_CL`, which is `PicklesFinalize.xiCorrect` at this encoding. -/
theorem xi_forced (a : Assignment) (h : BlockEq a XI_SQ XI_CL) :
    sVal a XI_SQ = sVal a XI_CL := blockEq_sVal a _ _ h

/-- ⚑ **`b_forced`** — the same for `bCorrect`: the b-polynomial the circuit recomputed equals the
claimed slot. What makes this the SEAM rather than a lone check is that `vB B_ACT` was produced by
`bEvalLegs` out of `CHAL 0 … CHAL 14`, and `lrCoefLegs` scales the opening's `L`/`R` bases by `c`
times those same blocks. -/
theorem b_forced (a : Assignment) (h : BlockEq a (vB B_ACT) B_CL) :
    sVal a (vB B_ACT) = sVal a B_CL := blockEq_sVal a _ _ h

/-- ⚑ **`reciprocity_forced`** — each challenge/inverse product is the pinned `ONE` block. This is
what makes "the 15 challenges `bEval` consumed" and "the 15 inverses `lrTerms` scaled by" one
vector rather than two. -/
theorem reciprocity_forced (a : Assignment) (j : Nat)
    (h : BlockEq a (vB (RCP j)) ONE) : sVal a (vB (RCP j)) = sVal a ONE :=
  blockEq_sVal a _ _ h

/-- ⚑ **`conjunction_forces` — THE STATEMENT, and it is a CONJUNCTION.**

A trace satisfying this ONE descriptor's `xiCorrect`, `bCorrect` and reciprocity legs forces, at
once and over shared columns:

* finalize's ξ conjunct — the squeeze IS the claimed ξ;
* finalize's `b` conjunct — the claimed `b0` IS the b-polynomial of the challenge vector;
* the weld — every challenge the b-polynomial consumed is the inverse of the scalar the opening's
  `L_j` leg carries.

⚠ Read what is NOT here: `cipCorrect` and `plonkChecksPassed` are absent by construction (§0), and
nothing in this statement forces the MSM's arithmetic — that is the bind leg's sub-proof, and this
theorem is about this row. -/
theorem conjunction_forces (a : Assignment)
    (hxi : ∀ i, i < SK → (eqConstr XI_SQ XI_CL i).holds a)
    (hb : ∀ i, i < SK → (eqConstr (vB B_ACT) B_CL i).holds a)
    (hrcp : ∀ j, j < NCHAL → ∀ i, i < SK → (eqConstr (vB (RCP j)) ONE i).holds a) :
    sVal a XI_SQ = sVal a XI_CL
    ∧ sVal a (vB B_ACT) = sVal a B_CL
    ∧ ∀ j, j < NCHAL → sVal a (vB (RCP j)) = sVal a ONE :=
  ⟨xi_forced a (blockEq_of_gates a _ _ hxi)
  , b_forced a (blockEq_of_gates a _ _ hb)
  , fun j hj => reciprocity_forced a j (blockEq_of_gates a _ _ (hrcp j hj))⟩

/-! ## §10 — THE ALLOCATOR, and the aliasing a constraint count cannot see.

An off-by-one in the SSA arithmetic makes two ops share a witness column. Nothing downstream
notices: the leg count is unchanged, `mainRailOk` is unchanged, the descriptor emits, and the
prover accepts — while one op's quotient limbs are another's carries and both gates are satisfiable
at values neither op forces. So the disjointness is asserted here, at every boundary, as numbers. -/

/-- ⚑ **THE ALLOCATOR DOES NOT ALIAS AND DOES NOT OVERRUN.** The value blocks end where the
multiply witnesses begin, those end where the add witnesses begin, and those end exactly at the
declared width — and every index this AIR actually uses is inside its own region. -/
theorem allocator_is_disjoint :
    -- the three regions abut, and the last one ends AT the declared width
    vB NVAL = mW 0
    ∧ mW NMUL = aW 0
    ∧ aW NADD = CJ_WIDTH
    -- the scratch begins after the last input block
    ∧ blk NIN = SCRATCH
    -- every value slot this AIR names is < NVAL
    ∧ LADDER_COMMIT < NVAL ∧ RC (NCHAL - 1) < NVAL ∧ B_ACT < NVAL
    -- every multiply witness is < NMUL, every add witness < NADD
    ∧ MK_RC (NCHAL - 1) < NMUL ∧ MK_RB < NMUL ∧ AK_NZ2 < NADD := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **THE WITNESS-INDEX FAMILIES ARE PAIRWISE DISJOINT.** Squarings, products, folds, the `r`
multiply, the reciprocity multiplies and the coefficient multiplies each own a contiguous band, and
the bands do not overlap. This is the fact an off-by-one breaks. -/
theorem multiply_witness_bands_are_disjoint :
    (∀ e m, e < 2 → 1 ≤ m → m ≤ 14 → MK_SQ e m < 28)
    ∧ (∀ e j, e < 2 → j < NCHAL → 28 ≤ MK_PRD e j ∧ MK_PRD e j < 58)
    ∧ (∀ e j, e < 2 → j < NCHAL - 1 → 58 ≤ MK_FLD e j ∧ MK_FLD e j < 87)
    ∧ (∀ j, j < NCHAL → 89 ≤ MK_RCP j ∧ MK_RCP j < 104)
    ∧ (∀ j, j < NCHAL → 106 ≤ MK_LC j ∧ MK_LC j < 121)
    ∧ (∀ j, j < NCHAL → 121 ≤ MK_RC j ∧ MK_RC j < 136) := by
  unfold MK_SQ MK_PRD MK_FLD MK_RCP MK_LC MK_RC NCHAL
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> omega

/-- ⚑ **AND THE VALUE-SLOT BANDS TOO.** -/
theorem value_slot_bands_are_disjoint :
    (∀ e j, e < 2 → j < NCHAL → 28 ≤ PRD e j ∧ PRD e j < 58)
    ∧ (∀ e j, e < 2 → j < NCHAL → 58 ≤ SUM e j ∧ SUM e j < 88)
    ∧ (∀ e j, e < 2 → j < NCHAL → 88 ≤ FLD e j ∧ FLD e j < 118)
    ∧ (∀ j, j < NCHAL → 120 ≤ RCP j ∧ RCP j < 135)
    ∧ (∀ j, j < NCHAL → 140 ≤ LC j ∧ LC j < 155)
    ∧ (∀ j, j < NCHAL → 155 ≤ RC j ∧ RC j < 170) := by
  unfold PRD SUM FLD RCP LC RC NCHAL
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> omega

/-- ⚑ **ONE CHALLENGE VECTOR, NOT TWO — as a column fact rather than a claim.**

The b-polynomial's `j`-th product multiplies block `CHAL j`; the opening's `R_j` scalar multiplies
block `CHAL j`; the opening's `L_j` scalar multiplies `CHALINV j`; and the reciprocity multiply
takes both. All four name column `blk (12 + j)` or `blk (27 + j)` — there is exactly one copy of
each, `NIN = 42` input blocks in total, and a layout that gave the finalize half and the opening
half their own copies would declare `42 + 30 = 72`. -/
theorem one_challenge_vector :
    (∀ j, j < NCHAL → CHAL j = blk (12 + j))
    ∧ (∀ j, j < NCHAL → CHALINV j = blk (27 + j))
    -- the challenge blocks and the inverse blocks do not overlap …
    ∧ (∀ j k, j < NCHAL → k < NCHAL → CHAL j ≠ CHALINV k)
    -- … and both live entirely inside the input region, ahead of the scratch.
    ∧ (∀ j, j < NCHAL → CHAL j + SK ≤ SCRATCH ∧ CHALINV j + SK ≤ SCRATCH)
    ∧ NIN = 42 ∧ NIN + 2 * NCHAL = 72 := by
  refine ⟨fun j _ => rfl, fun j _ => rfl, ?_, ?_, ?_, ?_⟩
  · unfold CHAL CHALINV blk NCHAL SK; intros; omega
  · unfold CHAL CHALINV blk SCRATCH NIN NCHAL SK; intros; omega
  · decide
  · decide

#assert_axioms nin_eq
#assert_axioms scratch_eq
#assert_axioms cj_width_eq
#assert_axioms conjunctionAir_mainRailOk
#assert_axioms conjunctionAir_bind_shape
#assert_axioms eqBlock_is_eqConstrs
#assert_axioms eqConstr_holds_iff
#assert_axioms blockEq_of_gates
#assert_axioms blockEq_sVal
#assert_axioms xi_forced
#assert_axioms b_forced
#assert_axioms reciprocity_forced
#assert_axioms conjunction_forces
#assert_axioms allocator_is_disjoint
#assert_axioms multiply_witness_bands_are_disjoint
#assert_axioms value_slot_bands_are_disjoint
#assert_axioms one_challenge_vector

end Dregg2.Circuit.Emit.MinaWrapConjunctionAir
