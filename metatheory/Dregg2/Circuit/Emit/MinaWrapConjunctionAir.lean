/-
# `Dregg2.Circuit.Emit.MinaWrapConjunctionAir` — the conjunction upstream's verifier makes, as a
THREADED FOLD: the b-polynomial's 15 rounds are 15 ROWS, and the width is flat in the round count.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** Every column index, every gate body, every window leg, the bind leg
and the two emitted descriptors are authored here and go through `EffectLower.lowerAir` of an
`EffectAirIR.EffectAir`. There is no hand-written `VmConstraint2` in this file. Rust PROVES the
artifacts and authors no constraint. House Law #1.

## THE LAYOUT THIS FILE REPLACES, and it was refuted by its own author

The first cut of this object was ROW-LOCAL: the b-polynomial's 118 side-by-side operations at both
evaluation points, 15 reciprocity multiplies and 30 `lrTerms` scalars all in ONE row —
**22 184 columns, 30 607 constraints, a 24 MB artifact**, ten times the largest descriptor in the
tree. `EmitByName.lean` withheld the routing row rather than check in that shape, and named the fix:

> *"thread the conjunction's b-polynomial chain the way the ladder now is — 15 rounds is a natural
> fold, ~4 ops per row instead of 118 side by side."*

This file is that fix. `PastaLadderThread` is the precedent it copies, down to the shape of the
induction; `MinaPhase2Chain` is the other one (a fold that carries state INSIDE the recursion rather
than re-pinning agreed public inputs on both sides).

⚑ **AND THE PRECEDENT IS NOT NOVEL IN THIS TREE.** `PastaCurveSound.lean:1064` calls a threaded
accumulator *"a layout the existing ladder also lacks and has never had"*; that is true of
`PastaMsmAir` and FALSE of the tree — `dregg-mina-scalar-mul-ladder::v1`
(`MinaWrapCommitStages.ladderDesc`) is a register-file machine whose whole program runs on
`on_transition` gates and shipped before either of these files existed. What was new in
`PastaLadderThread` was threading the SOUND (limbed, range-checked) encoding, and that is what is
new here too.

## ⚑ WHAT A THREAD BUYS, AS THE NUMBER

`bFoldRef` is a fixed-length sequential accumulator with O(1) carried state — two blocks per
evaluation point, `sq` and `fld`, with

    sq_(r+1) = sq_r²                        (so sq_r = x^(2^r))
    fld_(r+1) = fld_r · (1 + c_(14−r) · sq_r)

— three multiplies and one add per round per point. Row-locally that is `1 326` fresh columns per
round (`rowLocalConjWidth`); threaded it is **ZERO**, because the depth is rows:
`threaded_conj_width_is_flat`. At Mina's 15 rounds the row-local layout used 20 532 columns and
declared 22 184; this one declares **2 536, at every round count.**

⚠ **AND IT IS A TRADE, NOT A SAVING** (`PastaLadderThread`'s own lesson, restated here because it is
easy to quote the flattering half): threading moves work from columns to ROWS. The threaded object
is `2 536 × 16 = 40 576` cells against the row-local `22 184`, which is MORE. What collapses is the
DESCRIPTOR — 4 157 constraints against 30 607, so the checked-in artifact is ~7× smaller and the
width no longer grows with the round count. That is the whole claim.

## ⚑ THE ROW COUNT IS THE ROUND COUNT PLUS ONE, AND THAT IS NOT A FUDGE

`.transition` fires on every row but the last, so a 16-row trace has exactly **15 transitions** —
Mina's 15 IPA rounds — and one terminal row that READS the finished register. The deployed prover
requires a power-of-two height (`descriptor_ir2.rs`, "base trace height must be a power of two"), and
`15 + 1 = 16`. The fit is exact: no padding convention, no spare rows.

## ⚑ WHERE THE TWO HALVES TOUCH — unchanged, and now a PER-ROW fact

Read off `MinaWrapOpeningGate.residualTerms` (`:588-595`), the opening's term list is

    lrTerms c chals chalInvs
      ++ [(c, cc), (c·cip − z1·b0, ub), (−z1, sg), (−z2, SRS_H)]

and the three coefficients that are NOT free are exactly finalize's checked slots: `b0` and `cip` in
the `ub` coefficient, and the 15 `chals` scaling every `L_j`/`R_j`. The row-local layout had to
argue that its 15 challenge blocks were the same 15 the b-polynomial consumed. Here there is nothing
to argue: **row `r` has ONE challenge block and ONE inverse block**, and the round's product, the
reciprocity multiply, the `L` scalar and the `R` scalar all read those two columns
(`one_challenge_pair_per_row`). A layout that gave the two halves their own copies would need two
CHAL blocks per row and would say so in `NIN`.

## ⚑ WHAT THIS OBJECT FORCES — stated at this tree's resolution, not at the name's

1. **`xiCorrect`** — `op.xiSqueeze = dv.xi`, limbwise, over blocks the thread holds constant.
2. **`bCorrect`, at full fidelity and now against `PastaIPA.bEval` ITSELF.** `conjunction_forces`
   concludes `dv.b ≡ bEval ζ chals + r · bEval ζω chals (mod q)` where `chals` is the vector the
   trace's own rows supplied — not a re-description of the circuit's arithmetic, but the spec
   function `PicklesFinalize` compares against. The bridge is `bFoldFrom_snd_eq_bEval`.
3. **The challenge/inverse reciprocity** — `chal_r · chalinv_r ≡ 1 (mod q)` on every round row.
4. **The opening's non-free coefficients** — `c·cip − z1·b0`, `−z1`, `−z2`, and the round's
   `c·chal` / `c·chalinv`, each computed by a sound core from the shared columns.
5. **The MSM itself, by recursion** — one `AirLeg.bind` whose `bound` lanes are the row's own
   forced coefficient cells.

⚠ **NOT emitted, and named rather than stubbed: `cipCorrect` and `plonkChecksPassed`.**

`cipCorrect` compares the claimed `combined_inner_product` against `cipActualOf`, whose `ft_eval0`
slot is K5's gate linearization. **A gate comparing `cip` against a ξ-fold with a FREE `ft_eval0`
column would force nothing at all** — `ft_eval0` free makes the fold's value free, so the comparison
accepts every `cip`. That is the `∃`-image vacuity this tree has already shipped once and it is not
shipped here. `plonkChecksPassed`'s `permScalarR` is the same shape and smaller.

So the plain answer to *"does one object now make the claim upstream's verifier makes"* is: **it
makes TWO of finalize's four conjuncts, the reciprocity that welds the two halves' challenge
vectors, and the opening's coefficient seam — in one descriptor, over shared columns, at a width
that does not grow with the round count.** Upstream's conjunction is a FOUR-way AND with the
opening; **this is a TWO-way AND with the opening**, and the missing two are LOCATED (the K5
linearization chain), not hand-waved.

⚠ **AND SAY THE OTHER THING PRECISELY.** `G`/`z₁`/`z₂` are **free witnesses in `openings_proof`, and
that is FAITHFUL to upstream** (`wrap_main.ml:357-382`): one equation over three free legs, bound by
the *next* proof's `finalize_other_proof`. So `equal_g` refuses no on-curve substitution, and neither
does this object. That is not a defect of this emission and it is not to be "fixed" — it is what the
recursion means, and the binding arrives one proof later.

## ⚑ ONE THING IS STRICTLY STRONGER THAN THE FILE IT REPLACES

Every satisfaction predicate here is stated in the **DEPLOYED reading** — `P ∣ body`, the mod-`P`
check `prove_vm_descriptor2` performs — and never as an ℤ equality. The row-local file read its
equality gates over ℤ (`Constraint.holds`), which is a STRONGER hypothesis and therefore a WEAKER
theorem. `smallDvd_forces_eq` is the step that recovers limbwise equality from `P ∣ (u − v)` plus the
byte ranges the declared lookups supply, and it is used at every equality in this file.

## What is proved here

* `bFoldFrom_snd_eq_bEval` — the threaded fold IS `PastaIPA.bEval`, over the reversed row order.
* `bStep_congr` — the fold step respects congruence (the analogue of `rcbTraceZ_congr`; it holds for
  the same reason, that the step is a POLYNOMIAL and has no inversion in it).
* `threadedBFold_forces` — the n-row induction: rows satisfied + threads held force the register
  entering row `n` to be the n-fold chain. No row's output is quoted.
* `conjunction_forces` — ξ, `b` against `bEval`, and the per-round reciprocity, together.
* `threaded_conj_width_is_flat` / `the_thread_is_what_collapses_the_artifact` — the layout facts.
* `conjunctionAir_mainRailOk`, the bind shape, the selector census, and the allocator disjointness.

## Axiom hygiene

`#assert_axioms`-clean; no `sorry`/`admit`/`native_decide`; zero `#guard`s.
-/
import Dregg2.Circuit.Emit.PastaLadderThread
import Dregg2.Circuit.Emit.PastaIPA
import Dregg2.Circuit.Emit.EffectLowerCertified

namespace Dregg2.Circuit.Emit.MinaWrapConjunctionAir

open Dregg2.Circuit (Assignment Expr Constraint)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 TableDef TableId mainTableDef VmConstraint2
  WindowExpr)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LimbsLeg BindLeg WindowLeg)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Circuit.Emit.EffectLower (lowerAir P)
open Dregg2.Circuit.Emit.PastaField (qN)
open Dregg2.Circuit.Emit.PastaFieldSound
open Dregg2.Circuit.Emit.PastaAddSubSound
open Dregg2.Circuit.Emit.PastaCurve (CZm)
open Dregg2.Circuit.Emit.PastaCurveSound

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §1 — THE ROW, and the three kinds of column on it.

Every quantity is a `SK = 32`-limb sound-encoded field element at the Pallas-SCALAR prime `q` —
which is the right field: `residualTerms` reduces every coefficient `% qN`, and `finalize`'s
deferred scalars are the same field. The GROUP side is mod `p` and lives in the sub-proof this row
binds to (`PastaLadderThread`), which is why the two moduli never meet inside one gate.

The columns split three ways, and the split is the layout:

* **GLOBAL** blocks — one value per proof. Held across rows by a `.transition` thread, so a gate
  about them on any row is a gate about the one value.
* **REGISTER** blocks — the fold's carried state, `sq` and `fld` at each of the two evaluation
  points. Threaded from row `r`'s computed OUT to row `r+1`'s IN.
* **PER-ROW** blocks — the round's challenge and its inverse. A fresh, range-checked witness each
  row, exactly as the ladder's addend is.
-/

/-- The number of IPA round challenges the block carries (`MinaWrapOpeningGate.CHAL.length`). -/
def NCHAL : Nat := 15

/-- ⚑ **THE ROW COUNT.** One row per round plus the terminal row that reads the finished register.
`.transition` fires on every row but the last, so `NROWS = NCHAL + 1` is exactly `NCHAL` threads —
and `16` is the power of two the deployed prover requires of a trace height. -/
def NROWS : Nat := NCHAL + 1

theorem the_rows_are_the_rounds_plus_the_read_row :
    NROWS = 16 ∧ NROWS = NCHAL + 1 ∧ NROWS = 2 ^ 4 := by
  refine ⟨by decide, rfl, by decide⟩

/-- Block `i`'s base column. -/
def blk (i : Nat) : Nat := SK * i

/-- `op.xiSqueeze` — the squeezed ξ. GLOBAL. -/
def XI_SQ : Nat := blk 0
/-- `dv.xi` — the ξ the deferred record CLAIMS. GLOBAL. -/
def XI_CL : Nat := blk 1
/-- `decode dv.b` — the claimed `b0`. GLOBAL. -/
def B_CL : Nat := blk 2
/-- `z1` from `openings_proof`. GLOBAL. -/
def Z1 : Nat := blk 3
/-- `z2` from `openings_proof`. GLOBAL. -/
def Z2 : Nat := blk 4
/-- the IPA evaluation-point challenge `c`. GLOBAL. -/
def C_COL : Nat := blk 5
/-- `decode dv.combinedInnerProduct`. GLOBAL. -/
def CIP : Nat := blk 6
/-- ζ, endo-mapped — the FIRST evaluation point, and the seed of register 0. GLOBAL. -/
def ZETA : Nat := blk 7
/-- ζω — the SECOND evaluation point. GLOBAL. -/
def ZETAW : Nat := blk 8
/-- the `r` squeeze that combines the two evaluation columns. GLOBAL. -/
def RSQ : Nat := blk 9
/-- The constant `1`, as a block — a sound core adds two BLOCKS, so `1 + c·x^k` needs one. -/
def ONE : Nat := blk 10
/-- The constant `0`, for the two negations `−z1`, `−z2`. -/
def ZERO : Nat := blk 11

/-- ⚑ **THE SQUARING REGISTER** at evaluation point `e` — `x_e^(2^r)` on row `r`. -/
def SQ_IN (e : Nat) : Nat := blk (12 + e)
/-- ⚑ **THE PRODUCT REGISTER** at evaluation point `e` — `∏_{i<r} (1 + c_(14−i)·x_e^(2^i))`. -/
def FLD_IN (e : Nat) : Nat := blk (14 + e)

/-- This ROW's IPA round challenge. Row `r` carries `chals[NCHAL − 1 − r]`, so the round's exponent
`x^(2^r)` is the one `bEval` pairs it with. -/
def CHAL : Nat := blk 16
/-- …and its inverse — the scalar `lrTerms` puts on `L`. -/
def CHALINV : Nat := blk 17

/-- The evaluation point that seeds register `e`: ζ for `e = 0`, ζω for `e = 1`. -/
def PT (e : Nat) : Nat := blk (7 + e)

theorem pt_is_the_two_points : PT 0 = ZETA ∧ PT 1 = ZETAW := ⟨rfl, rfl⟩

/-- Input blocks: 10 global + 2 constant + 4 register + 2 per-row. ⚑ **`NIN` does NOT grow with the
round count** — the row-local layout's was `12 + 2·NCHAL`. -/
def NIN : Nat := 18
/-- …and the column where the scratch begins. -/
def SCRATCH : Nat := SK * NIN

theorem nin_eq : NIN = 18 := rfl
theorem scratch_eq : SCRATCH = 576 := by decide

/-! ## §2 — THE SSA ALLOCATOR.

Same discipline as `PastaCurveSound.{vBase, mWit, aWit}`: value blocks first, then the multiply
witnesses, then the add/sub witnesses, each at its own stride, so a caller can allocate by index and
every base is a closed-form `Nat`. -/

/-- Value blocks this AIR computes. Counted in §4 and pinned by `allocator_is_disjoint`. -/
def NVAL : Nat := 20
/-- Multiplies. -/
def NMUL : Nat := 12
/-- Add/subs. -/
def NADD : Nat := 6

/-- The `i`-th computed value block. -/
def vB (i : Nat) : Nat := SCRATCH + SK * i
/-- The `k`-th multiply's private witness: 32 quotient limbs then 62 carries. -/
def mW (k : Nat) : Nat := SCRATCH + SK * NVAL + (SK + (NG - 1)) * k
/-- The `k`-th add/sub's private witness: the carry bit then 31 carries. -/
def aW (k : Nat) : Nat := SCRATCH + SK * NVAL + (SK + (NG - 1)) * NMUL + SK * k

/-- The declared main width. ⚑ **Flat in `NCHAL`** — see `threaded_conj_width_is_flat`. -/
def CJ_WIDTH : Nat := SCRATCH + SK * NVAL + (SK + (NG - 1)) * NMUL + SK * NADD

theorem cj_width_eq : CJ_WIDTH = 2536 := by decide

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

/-! ### The value slots. -/

/-- `sq_out = sq_in²` at evaluation point `e`. -/
def SQ_OUT (e : Nat) : Nat := 0 + e
/-- `prd = chal · sq_in`. -/
def PRD (e : Nat) : Nat := 2 + e
/-- `sum = 1 + prd`. -/
def SUM (e : Nat) : Nat := 4 + e
/-- `fld_out = fld_in · sum`. -/
def FLD_OUT (e : Nat) : Nat := 6 + e
/-- `rcp = chal · chalinv` — the reciprocity weld's product. -/
def RCP : Nat := 8
/-- `lc = c · chalinv` — this round's scalar on `L`. -/
def LC : Nat := 9
/-- `rc = c · chal` — this round's scalar on `R`. -/
def RC : Nat := 10
/-- `rb = r · fld_in(ζω)` — the terminal combination's first half. -/
def RB : Nat := 11
/-- `b_act = fld_in(ζ) + rb` — `bActualOf`, at the terminal row. -/
def B_ACT : Nat := 12
/-- `ccip = c · cip`. -/
def CCIP : Nat := 13
/-- `z1b0 = z1 · b0`. -/
def Z1B0 : Nat := 14
/-- `ubc = ccip − z1b0` — ⚑ THE SEAM. -/
def UBC : Nat := 15
/-- `−z1`. -/
def NEG_Z1 : Nat := 16
/-- `−z2`. -/
def NEG_Z2 : Nat := 17
/-- The threaded-ladder sub-proof's program-VK lanes, as a block. -/
def LADDER_VK : Nat := 18
/-- The sub-proof's PI-commitment lanes, as a block. -/
def LADDER_COMMIT : Nat := 19

/-! ### The witness slots, one band per op family. -/

def MK_SQ (e : Nat) : Nat := 0 + e
def MK_PRD (e : Nat) : Nat := 2 + e
def MK_FLD (e : Nat) : Nat := 4 + e
def MK_RCP : Nat := 6
def MK_LC : Nat := 7
def MK_RC : Nat := 8
def MK_RB : Nat := 9
def MK_CCIP : Nat := 10
def MK_Z1B0 : Nat := 11

def AK_SUM (e : Nat) : Nat := 0 + e
def AK_B : Nat := 2
def AK_UBC : Nat := 3
def AK_NZ1 : Nat := 4
def AK_NZ2 : Nat := 5

/-! ## §4 — THE EQUALITY, THE PIN AND THE THREAD, as legs.

Three scopes, and the scope is content: an every-row gate, a boundary gate at one end, and a
`.transition` window gate that relates two rows. `WindowLeg.mainRailOk` refuses a `nxt` read outside
`.transition` (on the last row p3's `next` is the WRAP row), and `.first`/`.last` lower to
`VmConstraint.boundary`, whose body reads `env.loc` alone. -/

/-- ⚑ **LIMBWISE EQUALITY** between two blocks, on EVERY row — `SK` flat gates.

This is STRICTLY STRONGER than the spec's field equality: two blocks may be congruent mod `q` and
differ limbwise. The direction that matters for a verifier is the one that holds — a satisfying
assignment forces limbwise equality, which forces `sVal` equality, which forces the congruence the
spec asks for. -/
def eqBlock (aB bB : Nat) : List AirLeg :=
  (List.range SK).map (fun i =>
    AirLeg.gate ⟨.add (.var (aB + i)) (.mul (.const (-1)) (.var (bB + i))), .const 0⟩)

/-- The same equality asserted on the FIRST row only — a boundary gate. This is what SEEDS the fold:
row 0's register is not quoted, it is PINNED. -/
def firstEqBlock (aB bB : Nat) : List AirLeg :=
  (List.range SK).map (fun i =>
    AirLeg.window ⟨RowSel.first,
      .add (.loc (aB + i)) (.mul (.const (-1)) (.loc (bB + i)))⟩)

/-- …and on the LAST row only — where the finished register is READ. -/
def lastEqBlock (aB bB : Nat) : List AirLeg :=
  (List.range SK).map (fun i =>
    AirLeg.window ⟨RowSel.last,
      .add (.loc (aB + i)) (.mul (.const (-1)) (.loc (bB + i)))⟩)

/-- A block pinned to a small constant: limb 0 is `k`, limbs `1 …` are `0`. -/
def constBlock (bB k : Nat) : List AirLeg :=
  AirLeg.gate ⟨.add (.var bB) (.const (-(k : ℤ))), .const 0⟩
  :: (List.range (SK - 1)).map (fun i => AirLeg.gate ⟨.var (bB + 1 + i), .const 0⟩)

/-- ⚑ **ONE CARRY LEG.** The `i`-th limb of the block at `dst` on the NEXT row is the `i`-th limb of
the block at `src` on THIS row. `.transition` is the ONLY selector under which `nxt` is the genuine
successor. ⚑ `GateExpr.gThread` at the window view. -/
def carryLeg (dst src i : Nat) : AirLeg :=
  .window ⟨RowSel.transition,
    Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow
      (Dregg2.Circuit.GateExpr.gThread (dst + i) (src + i))⟩

theorem carryLeg_eq (dst src i : Nat) :
    carryLeg dst src i = .window ⟨RowSel.transition,
      WindowExpr.add (.nxt (dst + i)) (.mul (.const (-1)) (.loc (src + i)))⟩ := rfl

/-- A whole block carried across the seam. -/
def carryBlock (dst src : Nat) : List AirLeg :=
  (List.range SK).map (carryLeg dst src)

/-- A GLOBAL block: carried to itself, so every row holds the same value. -/
def holdBlock (b : Nat) : List AirLeg := carryBlock b b

/-! ## §5 — ⚑ THE ROUND, and it is four ops per evaluation point.

`PastaIPA.bEval x (c :: rest) = bEval x rest * (1 + c · x^(2^|rest|))`. Read from the INNER end —
which is the order the recursion actually associates in — that is a left fold whose carried state is
the pair `(x^(2^r), running product)`:

    sq_(r+1) = sq_r · sq_r
    prd_r    = chal_r · sq_r
    sum_r    = 1 + prd_r
    fld_(r+1) = fld_r · sum_r

Three multiplies and one add, per point, per row. The row-local layout wrote all 118 of them side by
side; this writes 8 and lets `.transition` do the rest. -/

/-- The four ops of one round at evaluation point `e`. -/
def roundLegsAt (e : Nat) : List AirLeg :=
  mulAt (SQ_IN e) (SQ_IN e) (SQ_OUT e) (MK_SQ e)
  ++ mulAt CHAL (SQ_IN e) (PRD e) (MK_PRD e)
  ++ addAt ONE (vB (PRD e)) (SUM e) (AK_SUM e)
  ++ mulAt (FLD_IN e) (vB (SUM e)) (FLD_OUT e) (MK_FLD e)

/-- Both evaluation points' rounds. -/
def roundLegs : List AirLeg := roundLegsAt 0 ++ roundLegsAt 1

/-! ## §6 — ⚑ THE RECIPROCITY, per row, which is what welds the two halves' challenge vectors.

The round's product consumes `CHAL`; `lrTerms` scales `L` by `c · CHALINV`. Nothing so far says
those are one value and its inverse — and if nothing does, the opening and the finalize check read
two unrelated vectors while every gate passes. `chal · chalinv ≡ 1 (mod q)` is the weld: one sound
multiply and one limbwise comparison against the pinned `ONE` block, on every round row. -/

def reciprocityLegs : List AirLeg :=
  mulAt CHAL CHALINV RCP MK_RCP ++ eqBlock (vB RCP) ONE

/-- The round's two `lrTerms` scalars — over the SAME two blocks the round and the weld read. -/
def lrCoefLegs : List AirLeg :=
  mulAt C_COL CHALINV LC MK_LC ++ mulAt C_COL CHAL RC MK_RC

/-! ## §7 — ⚑ THE TERMINAL COMBINATION and the opening's global coefficients.

`bActualOf = bEval(ζ) + r · bEval(ζω)`. The two `bEval`s are the REGISTERS entering the terminal
row, so the combination is two ops on row `NCHAL` and the comparison against the claimed slot is a
`.last` boundary block. Everything else here reads only GLOBAL blocks, so a gate on any row is a
gate about the one value the thread holds. -/

def bTerminalLegs : List AirLeg :=
  mulAt RSQ (FLD_IN 1) RB MK_RB
  ++ addAt (FLD_IN 0) (vB RB) B_ACT AK_B

/-- ⚑ **THE SEAM ITSELF**: `ubc = c·cip − z1·b0`, over the same `CIP` and `B_CL` columns
`cipCorrect` and `bCorrect` name. -/
def ubCoefLegs : List AirLeg :=
  mulAt C_COL CIP CCIP MK_CCIP
  ++ mulAt Z1 B_CL Z1B0 MK_Z1B0
  ++ subAt (vB CCIP) (vB Z1B0) UBC AK_UBC

/-- `−z1` and `−z2`, as `0 − z`. -/
def negCoefLegs : List AirLeg :=
  subAt ZERO Z1 NEG_Z1 AK_NZ1 ++ subAt ZERO Z2 NEG_Z2 AK_NZ2

/-! ## §8 — ⚑ THE THREAD.

Fourteen blocks cross the seam: the four registers, carried from this row's OUT to the next row's
IN, and the ten globals, held. `448` window legs, all `.transition`. -/

/-- The four register carries. -/
def registerThread : List AirLeg :=
  carryBlock (SQ_IN 0) (vB (SQ_OUT 0))
  ++ carryBlock (SQ_IN 1) (vB (SQ_OUT 1))
  ++ carryBlock (FLD_IN 0) (vB (FLD_OUT 0))
  ++ carryBlock (FLD_IN 1) (vB (FLD_OUT 1))

/-- The ten global blocks, held constant down the trace. ⚑ `ONE`/`ZERO` are absent on purpose: they
are re-pinned by `constLegs` on every row, so a hold leg would say nothing new. -/
def globalThread : List AirLeg :=
  [XI_SQ, XI_CL, B_CL, Z1, Z2, C_COL, CIP, ZETA, ZETAW, RSQ].flatMap holdBlock

def threadLegs : List AirLeg := registerThread ++ globalThread

theorem threadLegs_length : threadLegs.length = 448 := by decide

/-- ⚑ **THE SEED.** Row 0's registers are PINNED, not quoted: the squaring register starts at the
named evaluation-point column and the product register starts at the pinned `ONE`. This is what
makes `conjunction_forces` a statement about `bEval` at ζ rather than about "whatever row 0 held". -/
def seedLegs : List AirLeg :=
  firstEqBlock (SQ_IN 0) (PT 0)
  ++ firstEqBlock (SQ_IN 1) (PT 1)
  ++ firstEqBlock (FLD_IN 0) ONE
  ++ firstEqBlock (FLD_IN 1) ONE

theorem seedLegs_length : seedLegs.length = 128 := by decide

/-! ## §9 — ⚑ THE RECURSION BIND: the MSM, with the state INSIDE.

The MSM is the threaded ladder (`PastaLadderThread.pallasThreadDesc`), and this row declares that a
VERIFYING sub-proof of it exists whose public-input commitment is **this row's own coefficient
columns**. `bound` is a list of ROW EXPRESSIONS, not a public input, so the fold cannot be satisfied
by re-pinning agreed values on both sides — the committed lanes are the very cells `ubCoefLegs`,
`lrCoefLegs` and `bTerminalLegs` just forced.

`BindLeg.mainRailOk` refuses a seam that pins neither program nor commitment, and one narrower than
`PROOF_BIND_MIN_LANES = 8` (a limb tie is worth `2^31` against a ~124-bit bar). Eight lanes are
declared and the guard is the pinned `ONE` block's limb 0. -/

/-- The eight lanes the seam ties — all of them cells this row's own gates forced. ⚑ The `L`/`R`
scalars are this ROUND's, which is the threading showing through: row `r` binds a sub-proof about
row `r`'s contribution to the MSM rather than about a 30-scalar block. -/
def boundLanes : List Expr :=
  [ .var (vB UBC), .var (vB NEG_Z1), .var (vB NEG_Z2), .var (vB CCIP)
  , .var (vB Z1B0), .var (vB LC), .var (vB RC), .var (vB B_ACT) ]

/-- ⚑ **THE COMMITMENT IS PINNED; THE PROGRAM IS NOT — and that is stated, not fabricated.**

`BindLeg.mainRailOk` accepts a leg that pins EITHER half. This one pins `bound` and leaves
`vkPin := none`.

⚠ **So the seam says "a verifying proof of SOME program about exactly these coefficients", not "of
THE threaded-ladder program".** The honest reason is that the program's VK is a digest of the built
artifact, which this file cannot compute and must not invent: an eight-lane literal written here
would be a pin against nothing, and this campaign has already found a ROM binding discharged over a
carrier whose docblock claimed more than its statement. The pin belongs to the emitter, which reads
the built `dregg-pasta-pallas-rcb-thread::v1` and fills it. Until it does, the sub-proof's PROGRAM is
unpinned and this file says so here rather than in a summary. -/
def bindLeg : AirLeg :=
  .bind { guard := .var ONE
        , commit := (List.range 8).map (fun i => .var (vB LADDER_COMMIT + i))
        , vk := (List.range 8).map (fun i => .var (vB LADDER_VK + i))
        , vkPin := none
        , bound := some boundLanes }

/-! ## §10 — THE AIR, and its unthreaded TWIN. -/

/-- The three range tables — the union `PastaFieldSound` and `PastaAddSubSound` declare, and nothing
new. -/
def cjTables : List TableDef :=
  [ mainTableDef CJ_WIDTH
  , ⟨rangeTidW SB, "range_w8", 1, .rangeLimb SB⟩
  , ⟨rangeTidW CB, "range_w16", 1, .rangeLimb CB⟩
  , ⟨rangeTidW CBITS, "range_w1", 1, .rangeLimb CBITS⟩ ]

/-- The input blocks' range lookups — the shared transcript is a WITNESS and every limb of it is
range-checked, which is what makes the sound cores' bounds hold on it AND what makes a mod-`P`
equality gate force a limbwise one (`smallDvd_forces_eq`). -/
def inputRangeLegs : List AirLeg :=
  (List.range NIN).map (fun i => AirLeg.limbs ⟨limbCols (blk i), SB, rangeTidW SB⟩)

/-- The two pinned constants. -/
def constLegs : List AirLeg := constBlock ONE 1 ++ constBlock ZERO 0

/-- ⚑ **`xiCorrect`, emitted** — `op.xiSqueeze = dv.xi`, limbwise, on every row (both blocks are
held by the thread, so this is one statement, not sixteen). -/
def xiCorrectLegs : List AirLeg := eqBlock XI_SQ XI_CL

/-- ⚑ **`bCorrect`, emitted** — the finished register's combination against the claimed slot, at the
row where the register is finished. -/
def bCorrectLegs : List AirLeg := lastEqBlock (vB B_ACT) B_CL

/-- Everything except the thread. Named separately because it is exactly what the unthreaded twin
carries, so the twin is this AIR MINUS the thread rather than a second authoring of it. -/
def bodyLegs : List AirLeg :=
  inputRangeLegs ++ constLegs
  ++ xiCorrectLegs
  ++ roundLegs
  ++ reciprocityLegs
  ++ lrCoefLegs
  ++ bTerminalLegs
  ++ ubCoefLegs ++ negCoefLegs
  ++ seedLegs
  ++ bCorrectLegs
  ++ [bindLeg]

/-- ⚑ **THE THREADED CONJUNCTION AIR.** -/
def conjunctionAir : EffectAir := { tables := cjTables, legs := bodyLegs ++ threadLegs }

/-- ⚑ **AND ITS UNTHREADED TWIN — the NEGATIVE CONTROL, emitted rather than mutated in Rust.**

Byte-for-byte the threaded AIR minus the 448 window legs. It exists so the falsifier's refusal can be
attributed: the same forged trace that the threaded descriptor REFUSES is ACCEPTED here, which is
what makes the refusal a statement about the thread rather than about the fixture. Building it in
Rust by filtering constraints out of a parsed descriptor would be Rust authoring AIR; this is the
Lean object. -/
def conjunctionAirUnthreaded : EffectAir := { tables := cjTables, legs := bodyLegs }

/-- ⚑ **THE COMPILER ACCEPTS IT.** Every leg has a deployed main-rail image — for the limbs legs the
`0 < bits ≤ 29` verdict, for the `.first`/`.last` window legs the "body reads no `nxt`" verdict, for
the bind leg the pinned-and-wide-enough verdict. A seam narrower than eight lanes, one pinning
neither program nor commitment, or a boundary leg reading the next row would emit `refuseConstraints`
and this would be false. -/
theorem conjunctionAir_mainRailOk : conjunctionAir.mainRailOk = true := by decide

theorem conjunctionAirUnthreaded_mainRailOk : conjunctionAirUnthreaded.mainRailOk = true := by
  decide

/-- ⚑ **THE SELECTOR CENSUS.** The 448 carries are `.transition` and NOTHING else is; the 128 seed
pins are `.first`; the 32 `bCorrect` comparisons are `.last`; and there is no `.all` window leg at
all. A `.transition → .all` re-scope is byte-identical algebra that accepts STRICTLY MORE
(`TableAirIR.TableGate.transition_strictly_weaker`), so it is invisible to a constraint count and
visible here. -/
theorem conjunctionAir_window_selectors :
    conjunctionAir.windowCountSel RowSel.transition = 448
    ∧ conjunctionAir.windowCountSel RowSel.first = 128
    ∧ conjunctionAir.windowCountSel RowSel.last = 32
    ∧ conjunctionAir.windowCountSel RowSel.all = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **AND THE TWIN IS THE SAME OBJECT MINUS THE THREAD** — not a re-authoring. Its own selector
census is the threaded one with the `.transition` column zeroed, so nothing else moved. -/
theorem the_twin_is_the_thread_removed :
    conjunctionAirUnthreaded.legs.length + threadLegs.length = conjunctionAir.legs.length
    ∧ conjunctionAirUnthreaded.windowCountSel RowSel.transition = 0
    ∧ conjunctionAirUnthreaded.windowCountSel RowSel.first = 128
    ∧ conjunctionAirUnthreaded.windowCountSel RowSel.last = 32 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [conjunctionAir, conjunctionAirUnthreaded]
  · decide
  · decide
  · decide

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

/-- ⚑ **THE TIED SOURCE** — `conjunctionAir` carrying its two decidable verdicts in its TYPE:
`mainRailOk` (main-rail expressible) and `pinsTied` (every published column is DERIVED by another
leg). A `TiedAir` cannot be built for a block that publishes a column nothing else constrains, so a
decorative pin is unrepresentable here rather than detectable by a census afterwards. -/
def conjunctionTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air := conjunctionAir

def conjunctionDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-wrap-conjunction::v1" CJ_WIDTH 0 [] conjunctionTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — `AirLeg.forces`, stated in the
SOURCE's vocabulary and never mentioning the lowering, so it is not `P → P`. Not re-derived here.

**Zero bytes move**: `lowerTiedAir … |>.val` is `lowerAir …` by `rfl`. -/
theorem conjunctionDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines conjunctionDesc [] conjunctionAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-wrap-conjunction::v1" CJ_WIDTH 0 [] conjunctionTiedAir).property

/-- ⚑ **THE ZERO.** The certified lowering emits the term the bare lowering emitted, by `rfl` — so
the migration changed what this definition PROVES, not what it PRODUCES. No re-emit, no VK rotation.
Also the unfolding lemma for the cost/shape proofs below, which reason through `lowerAir`. -/
theorem conjunctionDesc_eq_lowerAir :
    conjunctionDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-mina-wrap-conjunction::v1" CJ_WIDTH 0 [] conjunctionAir := rfl

/-- ⚑ **THE TIED SOURCE** — `conjunctionAirUnthreaded` carrying its two decidable verdicts in its TYPE:
`mainRailOk` (main-rail expressible) and `pinsTied` (every published column is DERIVED by another
leg). A `TiedAir` cannot be built for a block that publishes a column nothing else constrains, so a
decorative pin is unrepresentable here rather than detectable by a census afterwards. -/
def conjunctionUnthreadedTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air := conjunctionAirUnthreaded

def conjunctionUnthreadedDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-wrap-conjunction-unthreaded::v1" CJ_WIDTH 0 [] conjunctionUnthreadedTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — `AirLeg.forces`, stated in the
SOURCE's vocabulary and never mentioning the lowering, so it is not `P → P`. Not re-derived here.

**Zero bytes move**: `lowerTiedAir … |>.val` is `lowerAir …` by `rfl`. -/
theorem conjunctionUnthreadedDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines conjunctionUnthreadedDesc [] conjunctionAirUnthreaded :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-wrap-conjunction-unthreaded::v1" CJ_WIDTH 0 [] conjunctionUnthreadedTiedAir).property

/-- ⚑ **THE ZERO.** The certified lowering emits the term the bare lowering emitted, by `rfl` — so
the migration changed what this definition PROVES, not what it PRODUCES. No re-emit, no VK rotation.
Also the unfolding lemma for the cost/shape proofs below, which reason through `lowerAir`. -/
theorem conjunctionUnthreadedDesc_eq_lowerAir :
    conjunctionUnthreadedDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-mina-wrap-conjunction-unthreaded::v1" CJ_WIDTH 0 [] conjunctionAirUnthreaded := rfl

theorem conjunctionDesc_width : conjunctionDesc.traceWidth = 2536 := rfl
theorem conjunctionUnthreadedDesc_width : conjunctionUnthreadedDesc.traceWidth = 2536 := rfl

/-- ⚑ **THE EMITTED COUNT, AND THE TWIN IS EXACTLY 448 SHORTER.** -/
theorem conjunctionDesc_constraint_count :
    conjunctionDesc.constraints.length = 4157
    ∧ conjunctionUnthreadedDesc.constraints.length = 4157 - 448 := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## §11 — ⚑ THE LAYOUT FACT, as numbers rather than as a worry.

The row-local layout put every round's ops in one row, so its width grew with the round count. This
one does not. -/

/-- The row-local layout's width at `n` rounds: `12 + 2n` input blocks, `11n + 7` value blocks,
`9n − 1` multiplies and `2n + 4` add/subs — the marginal figures the refuted file's own allocator
produces. (It DECLARED `22 184`, over-allocating `NVAL/NMUL/NADD`; the used figure is what a formula
can honestly track.) -/
def rowLocalConjWidth (n : Nat) : Nat :=
  SK * (12 + 2 * n) + SK * (11 * n + 7) + (SK + (NG - 1)) * (9 * n - 1) + SK * (2 * n + 4)

/-- The threaded layout's width at `n` rounds — the row width, whatever `n` is. -/
def threadedConjWidth (_n : Nat) : Nat := CJ_WIDTH

/-- Rows the threaded layout needs at `n` rounds: one per round, plus the read row. -/
def threadedConjRows (n : Nat) : Nat := n + 1

/-- ⚑ **THE WIDTH IS FLAT.** Not "smaller" — INDEPENDENT of the round count, which is the property a
`.transition` thread buys and a wider row never can. -/
theorem threaded_conj_width_is_flat : ∀ n : Nat, threadedConjWidth n = 2536 := fun _ => rfl

/-- ⚑ **AND THE ROW-LOCAL ONE IS LINEAR** — every extra round costs `1 326` columns there and none
here. Stated as the step so it is a growth fact and not two sampled numbers. -/
theorem the_row_local_layout_is_linear_in_the_round_count :
    ∀ n : Nat, rowLocalConjWidth (n + 2) = rowLocalConjWidth (n + 1) + 1326 := by
  intro n
  unfold rowLocalConjWidth
  have hs : SK = 32 := rfl
  have hw : SK + (NG - 1) = 94 := by decide
  have h1 : 9 * (n + 2) - 1 = 9 * n + 17 := by omega
  have h2 : 9 * (n + 1) - 1 = 9 * n + 8 := by omega
  rw [h1, h2, hw, hs]
  omega

/-- ⚑ **THE THREAD IS WHAT COLLAPSES THE ARTIFACT**, at Mina's own round count.

`20 532` used columns (declared `22 184`) and `30 607` constraints against `2 536` columns and
`4 157` constraints — a descriptor `7.36×` smaller, and one whose width does not move when the round
count does. -/
theorem the_thread_is_what_collapses_the_artifact :
    rowLocalConjWidth NCHAL = 20532
    ∧ threadedConjWidth NCHAL = 2536
    ∧ threadedConjRows NCHAL = NROWS
    -- the refuted instance, as the numbers `EmitByName.lean` withheld the routing row over
    ∧ 8 * threadedConjWidth NCHAL < 22184
    ∧ 7 * conjunctionDesc.constraints.length < 30607
    ∧ 30607 < 8 * conjunctionDesc.constraints.length := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **AND THE CELL COUNT IS THE SAME TRADE, NOT A SAVING** (`PastaLadderThread`'s lesson, restated
because quoting only the flattering half is how a below-bar result reads as a win). Threading moves
the work from columns to rows; it does not remove it. The threaded object is `2 536 × 16` cells,
which is MORE than the row-local `22 184`. What shrinks is the DESCRIPTOR and the width's dependence
on the round count — which is what was blocking the routing row. -/
theorem threading_trades_columns_for_rows_and_cells :
    threadedConjWidth NCHAL * threadedConjRows NCHAL = 40576
    ∧ 22184 < threadedConjWidth NCHAL * threadedConjRows NCHAL := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## §12 — THE ALLOCATOR, and the aliasing a constraint count cannot see.

An off-by-one in the SSA arithmetic makes two ops share a witness column. Nothing downstream
notices: the leg count is unchanged, `mainRailOk` is unchanged, the descriptor emits, and the prover
accepts — while one op's quotient limbs are another's carries and both gates are satisfiable at
values neither op forces. So the disjointness is asserted here, at every boundary, as numbers. -/

/-- ⚑ **THE ALLOCATOR DOES NOT ALIAS AND DOES NOT OVERRUN.** -/
theorem allocator_is_disjoint :
    vB NVAL = mW 0
    ∧ mW NMUL = aW 0
    ∧ aW NADD = CJ_WIDTH
    ∧ blk NIN = SCRATCH
    ∧ (∀ e, e < 2 → SQ_OUT e < NVAL ∧ PRD e < NVAL ∧ SUM e < NVAL ∧ FLD_OUT e < NVAL)
    ∧ LADDER_COMMIT < NVAL ∧ NEG_Z2 < NVAL ∧ B_ACT < NVAL
    ∧ (∀ e, e < 2 → MK_SQ e < NMUL ∧ MK_PRD e < NMUL ∧ MK_FLD e < NMUL ∧ AK_SUM e < NADD)
    ∧ MK_Z1B0 < NMUL ∧ AK_NZ2 < NADD := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, by decide, by decide, by decide, ?_,
    by decide, by decide⟩
  · intro e he; interval_cases e <;> exact ⟨by decide, by decide, by decide, by decide⟩
  · intro e he; interval_cases e <;> exact ⟨by decide, by decide, by decide, by decide⟩

/-- ⚑ **THE WITNESS-INDEX FAMILIES ARE PAIRWISE DISJOINT.** Each op family owns a contiguous band
and the bands do not overlap. This is the fact an off-by-one breaks. -/
theorem witness_bands_are_disjoint :
    (∀ e, e < 2 → MK_SQ e < 2)
    ∧ (∀ e, e < 2 → 2 ≤ MK_PRD e ∧ MK_PRD e < 4)
    ∧ (∀ e, e < 2 → 4 ≤ MK_FLD e ∧ MK_FLD e < 6)
    ∧ (∀ e, e < 2 → AK_SUM e < 2)
    ∧ (6 ≤ MK_RCP ∧ MK_RCP < NMUL) ∧ (2 ≤ AK_B ∧ AK_B < NADD) := by
  refine ⟨?_, ?_, ?_, ?_, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩ <;>
    (intro e he; simp only [MK_SQ, MK_PRD, MK_FLD, AK_SUM]; omega)

/-- ⚑ **ONE CHALLENGE PAIR PER ROW — as a column fact rather than a claim.**

The round's product multiplies block `CHAL`; the opening's `R` scalar multiplies block `CHAL`; the
opening's `L` scalar multiplies `CHALINV`; and the reciprocity multiply takes both. All four name
`blk 16` or `blk 17` — there is exactly one copy of each on the row, and `NIN` does not grow with the
round count, so a layout that gave the finalize half and the opening half their own copies could not
hide inside this width. -/
theorem one_challenge_pair_per_row :
    CHAL = blk 16 ∧ CHALINV = blk 17 ∧ CHAL ≠ CHALINV
    ∧ CHAL + SK ≤ SCRATCH ∧ CHALINV + SK ≤ SCRATCH
    ∧ NIN = 18 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, rfl⟩

/-! ## §13 — ⚑ THE DEPLOYED READING, and the step that recovers an equality from it.

Every predicate below is stated as `P ∣ body` — what `prove_vm_descriptor2` checks, in BabyBear —
and never as an ℤ equality. `smallDvd_forces_eq` is what turns the deployed reading of an equality
gate back into limbwise equality, and it needs the RANGE facts: without them `P ∣ (u − v)` says
nothing. That is why every block this file compares is either an input block (ranged by
`inputRangeLegs`) or the RESULT of a sound core (ranged by the core's own result lookup). -/

/-- A divisor of something smaller than the modulus is zero. -/
theorem smallDvd_zero {d : ℤ} (h : P ∣ d) (hb : |d| < P) : d = 0 := by
  rcases h with ⟨t, ht⟩
  by_contra hne
  have ht0 : t ≠ 0 := by rintro rfl; rw [mul_zero] at ht; exact hne ht
  have hP0 : (0 : ℤ) < P := by norm_num [Dregg2.Circuit.Emit.EffectLower.P]
  have h1 : (1 : ℤ) ≤ |t| := by rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have : P ≤ |d| := by
    rw [ht, abs_mul, abs_of_nonneg (le_of_lt hP0)]
    nlinarith
  linarith

/-- ⚑ **A MOD-`P` EQUALITY BETWEEN TWO BYTES IS AN EQUALITY.** The gate the prover checks is
`P ∣ (u − v)`; the declared range lookups make `|u − v| < 2^8`; `2^8 < P`. -/
theorem smallDvd_forces_eq {u v : ℤ}
    (hu : 0 ≤ u ∧ u < 2 ^ SB) (hv : 0 ≤ v ∧ v < 2 ^ SB) (h : P ∣ (u - v)) : u = v := by
  have hB : (2 : ℤ) ^ SB = 256 := by norm_num [SB]
  rw [hB] at hu hv
  have hlt : |u - v| < P := by
    rw [abs_lt]
    constructor <;> [skip; skip] <;>
      · norm_num [Dregg2.Circuit.Emit.EffectLower.P]; omega
  have := smallDvd_zero h hlt
  omega

/-- ⚑ **THE DEPLOYED READING OF `eqBlock`** — the `SK` gate bodies vanish mod `P`. -/
def BlockEqP (a : Assignment) (xB yB : Nat) : Prop :=
  ∀ i, i < SK → P ∣ (a (xB + i) - a (yB + i))

/-- The `i`-th gate `eqBlock` emits, as a `Constraint`. -/
def eqConstr (xB yB i : Nat) : Constraint :=
  ⟨.add (.var (xB + i)) (.mul (.const (-1)) (.var (yB + i))), .const 0⟩

/-- ⚑ **THE EMITTED LEG IS THAT GATE** — by `rfl`, so the bridge below is about the object the
compiler lowers and not about a re-description of it. -/
theorem eqBlock_is_eqConstrs (xB yB : Nat) :
    eqBlock xB yB = (List.range SK).map (fun i => AirLeg.gate (eqConstr xB yB i)) := rfl

/-- …and the `.first`/`.last` blocks are the same body under a boundary selector. -/
theorem firstEqBlock_is_the_local_body (xB yB : Nat) :
    firstEqBlock xB yB = (List.range SK).map (fun i =>
      AirLeg.window ⟨RowSel.first,
        .add (.loc (xB + i)) (.mul (.const (-1)) (.loc (yB + i)))⟩) := rfl

theorem lastEqBlock_is_the_local_body (xB yB : Nat) :
    lastEqBlock xB yB = (List.range SK).map (fun i =>
      AirLeg.window ⟨RowSel.last,
        .add (.loc (xB + i)) (.mul (.const (-1)) (.loc (yB + i)))⟩) := rfl

/-- ⚑ **AND SATISFYING IT MOD `P` IS THE DIVISIBILITY** — the `iff`, so the gate cannot be satisfied
by anything else. -/
theorem eqConstr_dvd_iff (a : Assignment) (xB yB i : Nat) :
    P ∣ (eqConstr xB yB i).lhs.eval a ↔ P ∣ (a (xB + i) - a (yB + i)) := by
  unfold eqConstr
  simp only [Expr.eval]
  rw [show a (xB + i) + (-1) * a (yB + i) = a (xB + i) - a (yB + i) by ring]

/-- Limbwise equality of two RANGED blocks, from the deployed reading. -/
theorem blockEq_of_dvd (a : Assignment) (xB yB : Nat)
    (hx : Ranged a xB) (hy : Ranged a yB) (h : BlockEqP a xB yB) :
    ∀ i, i < SK → a (xB + i) = a (yB + i) :=
  fun i hi => smallDvd_forces_eq (hx i hi) (hy i hi) (h i hi)

/-- …and therefore of the VALUES the spec compares. -/
theorem blockEqP_sVal (a : Assignment) (xB yB : Nat)
    (hx : Ranged a xB) (hy : Ranged a yB) (h : BlockEqP a xB yB) :
    sVal a xB = sVal a yB :=
  Dregg2.Circuit.Emit.PastaLadderThread.sVal_congr a a xB yB (blockEq_of_dvd a xB yB hx hy h)

/-! ### The constant block, forced. -/

/-- The deployed reading of `constBlock bB k`: limb 0 is `k` and the rest vanish, mod `P`. -/
def ConstBlockP (a : Assignment) (bB k : Nat) : Prop :=
  P ∣ (a bB - (k : ℤ)) ∧ ∀ i, i < SK - 1 → P ∣ a (bB + 1 + i)

/-- ⚑ **THE PINNED BLOCK RECONSTRUCTS TO ITS CONSTANT.** `sVal` reads `SK` columns; limb 0 carries
the constant and every other limb is zero, so the base-`2^8` fold is the constant itself. -/
theorem constBlock_forces_sVal (a : Assignment) (bB k : Nat)
    (hk : (k : ℤ) < 2 ^ SB) (hr : Ranged a bB) (h : ConstBlockP a bB k) :
    sVal a bB = (k : ℤ) := by
  have h0 : a bB = (k : ℤ) :=
    smallDvd_forces_eq (hr 0 (by decide)) ⟨Int.natCast_nonneg k, hk⟩ (by simpa using h.1)
  have hz : ∀ i, 0 < i → i < SK → a (bB + i) = 0 := by
    intro i hi0 hiK
    have hidx : bB + i = bB + 1 + (i - 1) := by omega
    have hd := h.2 (i - 1) (by omega)
    rw [hidx]
    have hrange := hr i hiK
    rw [hidx] at hrange
    exact smallDvd_forces_eq hrange ⟨le_refl 0, by norm_num [SB]⟩ (by simpa using hd)
  unfold sVal
  have hc : ∀ m ∈ List.range SK,
      ((2 : ℤ) ^ SB) ^ m * a (bB + m) = (if 0 = m then (k : ℤ) else 0) := by
    intro m hm
    have hmK : m < SK := List.mem_range.mp hm
    by_cases h0m : m = 0
    · subst h0m; simp [h0]
    · rw [if_neg (by omega), hz m (by omega) hmK]; ring
  rw [sumL_congr _ _ _ hc]
  exact sumL_range_ite SK 0 (fun _ => (k : ℤ)) (by decide)

/-! ## §14 — ⚑ THE REFERENCE FOLD, and that it IS `PastaIPA.bEval`.

`bStep` is the round's arithmetic over ℤ; `bFoldFrom` iterates it. The point of §14 is the second
theorem: the object this circuit computes is the SPEC function, not a re-description of the gates. -/

/-- One round of the fold: square the power, multiply the running product by `1 + c·power`. -/
def bStep (c : ℤ) (st : ℤ × ℤ) : ℤ × ℤ := (st.1 * st.1, st.2 * (1 + c * st.1))

/-- `n` rounds of it, from a starting state, over the row-indexed challenge sequence `q`. -/
def bFoldFrom (q : Nat → ℤ) (st : ℤ × ℤ) : Nat → ℤ × ℤ
  | 0 => st
  | n + 1 => bStep (q n) (bFoldFrom q st n)

/-- The squaring register after `n` rounds is `x^(2^n)` — the doubling `sqTower` the kimchi
`b_poly` walks. -/
theorem bFoldFrom_fst (q : Nat → ℤ) (x f : ℤ) :
    ∀ n : Nat, (bFoldFrom q (x, f) n).1 = x ^ (2 ^ n)
  | 0 => by simp [bFoldFrom]
  | n + 1 => by
      have ih := bFoldFrom_fst q x f n
      simp only [bFoldFrom, bStep, ih]
      rw [← pow_add]
      congr 1
      omega

/-- ⚑ **THE THREADED FOLD IS `PastaIPA.bEval`.**

`bEval x (c :: rest) = bEval x rest * (1 + c · x^(2^|rest|))` associates from the INNER end, which is
exactly a left fold whose `r`-th step uses the challenge at index `|cs| − 1 − r` and the power
`x^(2^r)`. So the circuit's row order is the REVERSE of the challenge list's, and this is the
theorem that says so rather than a comment claiming it. -/
theorem bFoldFrom_snd_eq_bEval (q : Nat → ℤ) (x : ℤ) :
    ∀ n : Nat,
      (bFoldFrom q (x, 1) n).2 = Dregg2.Circuit.Emit.PastaIPA.bEval x (((List.range n).map q).reverse)
  | 0 => by simp [bFoldFrom, Dregg2.Circuit.Emit.PastaIPA.bEval]
  | n + 1 => by
      have ih := bFoldFrom_snd_eq_bEval q x n
      have hfst := bFoldFrom_fst q x 1 n
      have hlist : ((List.range (n + 1)).map q).reverse
          = q n :: ((List.range n).map q).reverse := by
        rw [List.range_succ, List.map_append]
        simp
      have hlen : (((List.range n).map q).reverse).length = n := by simp
      rw [hlist]
      simp only [bFoldFrom, bStep, Dregg2.Circuit.Emit.PastaIPA.bEval, hlen, ih, hfst]

/-! ## §15 — ⚑ THE THREADED CHAIN, and what its satisfaction forces.

A TRACE is `Nat → Assignment`: row `r`'s columns are `tr r`. That is the shape the deployed prover
fills and the shape `.transition` reads two of at a time. -/

/-- A multi-row trace: row index to that row's column assignment. -/
abbrev Trace := Nat → Assignment

/-- Congruence of a fold state, componentwise. -/
def CZ2 (m : ℤ) (P Q : ℤ × ℤ) : Prop := CZm m P.1 Q.1 ∧ CZm m P.2 Q.2

theorem CZ2.refl {m : ℤ} (P : ℤ × ℤ) : CZ2 m P P := ⟨CZm.refl _, CZm.refl _⟩

theorem CZ2.trans {m : ℤ} {P Q R : ℤ × ℤ} (h1 : CZ2 m P Q) (h2 : CZ2 m Q R) : CZ2 m P R :=
  ⟨CZm.trans h1.1 h2.1, CZm.trans h1.2 h2.2⟩

/-- ⚑ **THE ENABLING LEMMA: the fold step respects congruence.**

`mulCore_forces` concludes a CONGRUENCE (`CZm q z (x·y)`), not an equality, so chaining `n` of them
needs the step to send congruent states to congruent states. `bStep` is built from `+`, `·` and
constants and nothing else — there is no inversion in it, which is the same property that made
`rcbTraceZ_congr` provable for the complete addition formula — so the two `CZm` homomorphism lemmas
are the whole proof. It is the lemma the induction below turns on. -/
theorem bStep_congr {m : ℤ} (c : ℤ) {Pst Qst : ℤ × ℤ} (h : CZ2 m Pst Qst) :
    CZ2 m (bStep c Pst) (bStep c Qst) :=
  ⟨CZm.mul h.1 h.1,
   CZm.mul h.2 (CZm.add (CZm.refl 1) (CZm.mul (CZm.refl c) h.1))⟩

/-- The fold state this trace carries INTO row `r` at evaluation point `e`. -/
def regIn (tr : Trace) (e r : Nat) : ℤ × ℤ :=
  (sVal (tr r) (SQ_IN e), sVal (tr r) (FLD_IN e))

/-- …and the one row `r` produces. -/
def regOut (tr : Trace) (e r : Nat) : ℤ × ℤ :=
  (sVal (tr r) (vB (SQ_OUT e)), sVal (tr r) (vB (FLD_OUT e)))

/-- The challenge row `r` supplies. -/
def chalOf (tr : Trace) (r : Nat) : ℤ := sVal (tr r) CHAL

/-- **The reference chain** — the fold, from whatever state the trace carries into row 0. This is
what the circuit CLAIMS to compute; nothing below asserts it, the theorem forces it. -/
def bChainRef (tr : Trace) (e : Nat) (n : Nat) : ℤ × ℤ :=
  bFoldFrom (chalOf tr) (regIn tr e 0) n

/-- ⚑ **THE THREAD, AS THE PROVER SATISFIES IT.** The four register carries vanish mod `P` between
rows `r` and `r+1` exactly when every limb of the next row's register input matches the matching limb
of this row's computed output. This is `carryLeg`'s body read as a fact about the trace, in the
DEPLOYED reading. -/
def Threaded (tr : Trace) (e r : Nat) : Prop :=
  ∀ i, i < SK →
    P ∣ (tr (r + 1) (SQ_IN e + i) - tr r (vB (SQ_OUT e) + i))
    ∧ P ∣ (tr (r + 1) (FLD_IN e + i) - tr r (vB (FLD_OUT e) + i))

/-- ⚑ **THE ROW'S DEPLOYED SATISFACTION**, packaged so the induction quantifies over rows rather
than re-listing the range blocks each time. Field for field this is exactly what the four per-op
forcing lemmas consume. -/
structure RowSound (tr : Trace) (e r : Nat) : Prop where
  /-- The pinned `1` block reconstructs to `1` — supplied by `constBlock_forces_sVal`. -/
  hone : sVal (tr r) ONE = 1
  honeR : Ranged (tr r) ONE
  hsq : Ranged (tr r) (SQ_IN e)
  hfld : Ranged (tr r) (FLD_IN e)
  hchal : Ranged (tr r) CHAL
  hsqo : Ranged (tr r) (vB (SQ_OUT e))
  hprd : Ranged (tr r) (vB (PRD e))
  hsum : Ranged (tr r) (vB (SUM e))
  hfldo : Ranged (tr r) (vB (FLD_OUT e))
  hwsq : MulWitRanged (tr r) (mW (MK_SQ e))
  hwprd : MulWitRanged (tr r) (mW (MK_PRD e))
  hwfld : MulWitRanged (tr r) (mW (MK_FLD e))
  hwsum : AddSubWitRanged (tr r) (aW (AK_SUM e))
  gsq : MulSat (tr r) qLimb (SQ_IN e) (SQ_IN e) (vB (SQ_OUT e)) (mW (MK_SQ e))
  gprd : MulSat (tr r) qLimb CHAL (SQ_IN e) (vB (PRD e)) (mW (MK_PRD e))
  gsum : AddSubSat (tr r) qLimb 1 (-1) ONE (vB (PRD e)) (vB (SUM e)) (aW (AK_SUM e))
  gfld : MulSat (tr r) qLimb (FLD_IN e) (vB (SUM e)) (vB (FLD_OUT e)) (mW (MK_FLD e))

/-- One row, forced: the output state is congruent to one fold step on this row's input state and
this row's challenge. -/
theorem row_forces (tr : Trace) (e r : Nat) (hR : RowSound tr e r) :
    CZ2 (qN : ℤ) (regOut tr e r) (bStep (chalOf tr r) (regIn tr e r)) := by
  have hq := qLimb_bounds
  have hM := qLimb_recomposes
  -- the squaring
  have fsq : CZm (qN : ℤ) (sVal (tr r) (vB (SQ_OUT e)))
      (sVal (tr r) (SQ_IN e) * sVal (tr r) (SQ_IN e)) :=
    mulCore_forces (tr r) qLimb (qN : ℤ) hq hM _ _ _ _ hR.hsq hR.hsq hR.hsqo hR.hwsq hR.gsq
  -- the product
  have fprd : CZm (qN : ℤ) (sVal (tr r) (vB (PRD e)))
      (sVal (tr r) CHAL * sVal (tr r) (SQ_IN e)) :=
    mulCore_forces (tr r) qLimb (qN : ℤ) hq hM _ _ _ _ hR.hchal hR.hsq hR.hprd hR.hwprd hR.gprd
  -- the `1 +`
  have fsum0 : CZm (qN : ℤ) (sVal (tr r) (vB (SUM e)))
      (sVal (tr r) ONE + sVal (tr r) (vB (PRD e))) :=
    addCore_forces (tr r) qLimb (qN : ℤ) hq hM _ _ _ _ hR.honeR hR.hprd hR.hsum hR.hwsum hR.gsum
  have fsum : CZm (qN : ℤ) (sVal (tr r) (vB (SUM e)))
      (1 + sVal (tr r) CHAL * sVal (tr r) (SQ_IN e)) :=
    CZm.trans fsum0 (by rw [← hR.hone]; exact CZm.add (CZm.refl _) fprd)
  -- the fold multiply
  have ffld0 : CZm (qN : ℤ) (sVal (tr r) (vB (FLD_OUT e)))
      (sVal (tr r) (FLD_IN e) * sVal (tr r) (vB (SUM e))) :=
    mulCore_forces (tr r) qLimb (qN : ℤ) hq hM _ _ _ _ hR.hfld hR.hsum hR.hfldo hR.hwfld hR.gfld
  exact ⟨fsq, CZm.trans ffld0 (CZm.mul (CZm.refl _) fsum)⟩

/-- ⚑ **A HELD THREAD MOVES THE VALUE, NOT JUST THE LIMBS.** -/
theorem threaded_carries (tr : Trace) (e r : Nat)
    (hsq : Ranged (tr (r + 1)) (SQ_IN e)) (hfld : Ranged (tr (r + 1)) (FLD_IN e))
    (hsqo : Ranged (tr r) (vB (SQ_OUT e))) (hfldo : Ranged (tr r) (vB (FLD_OUT e)))
    (h : Threaded tr e r) : regIn tr e (r + 1) = regOut tr e r := by
  unfold regIn regOut
  refine Prod.ext ?_ ?_
  · exact Dregg2.Circuit.Emit.PastaLadderThread.sVal_congr _ _ _ _
      (fun i hi => smallDvd_forces_eq (hsq i hi) (hsqo i hi) (h i hi).1)
  · exact Dregg2.Circuit.Emit.PastaLadderThread.sVal_congr _ _ _ _
      (fun i hi => smallDvd_forces_eq (hfld i hi) (hfldo i hi) (h i hi).2)

/-- ⚑ **`threadedBFold_forces` — THE COMPOSITION THEOREM.**

`n` rows of DEPLOYED satisfaction, plus `n` held threads, force the fold state entering row `n` to be
congruent — mod the real Pallas-scalar prime — to the `n`-fold chain over the challenges the trace
supplied. The register is never read from a public input and never re-pinned; each row's output is
FORCED by that row's gates and CARRIED by that row's thread.

⚠ What it does NOT say: nothing here forces the CHALLENGES to be anything in particular. A fold that
means `bEval` at Mina's transcript additionally needs row `r`'s challenge to be the transcript's
`chals[NCHAL − 1 − r]` — that is the sponge half, and it lives upstream in `MinaWrapVerifierSponge`.
This theorem is the accumulator half, which is the half the layout wall was blocking. -/
theorem threadedBFold_forces (tr : Trace) (e : Nat) : ∀ n : Nat,
    (∀ r, r < n → RowSound tr e r) → (∀ r, r < n → Threaded tr e r) →
    (∀ r, r ≤ n → Ranged (tr r) (SQ_IN e) ∧ Ranged (tr r) (FLD_IN e)) →
    CZ2 (qN : ℤ) (regIn tr e n) (bChainRef tr e n)
  | 0, _, _, _ => CZ2.refl _
  | n + 1, hrow, hthread, hrng => by
      have ih : CZ2 (qN : ℤ) (regIn tr e n) (bChainRef tr e n) :=
        threadedBFold_forces tr e n (fun r hr => hrow r (Nat.lt_succ_of_lt hr))
          (fun r hr => hthread r (Nat.lt_succ_of_lt hr))
          (fun r hr => hrng r (Nat.le_succ_of_le hr))
      have hrowN := hrow n (Nat.lt_succ_self n)
      have hcarry : regIn tr e (n + 1) = regOut tr e n :=
        threaded_carries tr e n (hrng (n + 1) (le_refl _)).1 (hrng (n + 1) (le_refl _)).2
          hrowN.hsqo hrowN.hfldo (hthread n (Nat.lt_succ_self n))
      have hrowf := row_forces tr e n hrowN
      have hstep : CZ2 (qN : ℤ) (bStep (chalOf tr n) (regIn tr e n)) (bChainRef tr e (n + 1)) :=
        bStep_congr _ ih
      rw [hcarry]
      exact CZ2.trans hrowf hstep

/-- ⚑ **AND IT IS NOT VACUOUS.** At `n = 0` the statement is reflexivity, so the content is entirely
in the step — which is why this instance is stated: `n = 1` says the FIRST row's forced output is the
chain's first value, and it consumes a `RowSound` and a `Threaded`. A theorem that held for every
trace with no rows satisfied would prove nothing; this one needs the hypotheses at `r = 0`. -/
theorem threadedBFold_forces_one (tr : Trace) (e : Nat)
    (hrow : RowSound tr e 0) (hthread : Threaded tr e 0)
    (hrng : ∀ r, r ≤ 1 → Ranged (tr r) (SQ_IN e) ∧ Ranged (tr r) (FLD_IN e)) :
    CZ2 (qN : ℤ) (regIn tr e 1) (bStep (chalOf tr 0) (regIn tr e 0)) :=
  threadedBFold_forces tr e 1
    (fun r hr => by rwa [Nat.lt_one_iff.mp hr])
    (fun r hr => by rwa [Nat.lt_one_iff.mp hr]) hrng

/-! ## §16 — ⚑ THE SEED, and the chain read as `bEval`. -/

/-- The challenge vector this trace supplies, in `bEval`'s OWN order (head = highest round). Row `r`
carries index `NCHAL − 1 − r`, so the list is the row order reversed. -/
def chalVec (tr : Trace) : List ℤ := ((List.range NCHAL).map (chalOf tr)).reverse

/-- ⚑ **THE SEEDED CHAIN IS THE b-POLYNOMIAL.** With row 0's registers pinned by `seedLegs` — the
squaring register at the named evaluation-point column, the product register at the pinned `1` — the
`NCHAL`-fold chain's second component IS `PastaIPA.bEval` at that point over that challenge vector.

This is the step the row-local file could not take: it compared a circuit value against a circuit
value. This compares it against the SPEC function `PicklesFinalize.bCorrect` reads. -/
theorem bChainRef_is_bEval (tr : Trace) (e : Nat)
    (hseedSq : sVal (tr 0) (SQ_IN e) = sVal (tr 0) (PT e))
    (hseedFld : sVal (tr 0) (FLD_IN e) = 1) :
    (bChainRef tr e NCHAL).2
      = Dregg2.Circuit.Emit.PastaIPA.bEval (sVal (tr 0) (PT e)) (chalVec tr) := by
  unfold bChainRef chalVec
  rw [show regIn tr e 0 = (sVal (tr 0) (PT e), 1) by
    unfold regIn; rw [hseedSq, hseedFld]]
  exact bFoldFrom_snd_eq_bEval (chalOf tr) _ NCHAL

/-! ## §17 — ⚑ THE TERMINAL ROW, and the weld, and the capstone. -/

/-- The terminal row's two ops: `rb = r · fld(ζω)` and `b_act = fld(ζ) + rb`. -/
structure TerminalSound (tr : Trace) : Prop where
  hfld0 : Ranged (tr NCHAL) (FLD_IN 0)
  hfld1 : Ranged (tr NCHAL) (FLD_IN 1)
  hrsq : Ranged (tr NCHAL) RSQ
  hrb : Ranged (tr NCHAL) (vB RB)
  hbact : Ranged (tr NCHAL) (vB B_ACT)
  hbcl : Ranged (tr NCHAL) B_CL
  hwrb : MulWitRanged (tr NCHAL) (mW MK_RB)
  hwb : AddSubWitRanged (tr NCHAL) (aW AK_B)
  grb : MulSat (tr NCHAL) qLimb RSQ (FLD_IN 1) (vB RB) (mW MK_RB)
  gb : AddSubSat (tr NCHAL) qLimb 1 (-1) (FLD_IN 0) (vB RB) (vB B_ACT) (aW AK_B)
  /-- The `.last` boundary block: the computed `bActualOf` equals the claimed slot. -/
  gcmp : BlockEqP (tr NCHAL) (vB B_ACT) B_CL

/-- The terminal row forces the claimed `b` to be the combination of the two registers. -/
theorem terminal_forces (tr : Trace) (hT : TerminalSound tr) :
    CZm (qN : ℤ) (sVal (tr NCHAL) B_CL)
      (sVal (tr NCHAL) (FLD_IN 0) + sVal (tr NCHAL) RSQ * sVal (tr NCHAL) (FLD_IN 1)) := by
  have hq := qLimb_bounds
  have hM := qLimb_recomposes
  have frb : CZm (qN : ℤ) (sVal (tr NCHAL) (vB RB))
      (sVal (tr NCHAL) RSQ * sVal (tr NCHAL) (FLD_IN 1)) :=
    mulCore_forces (tr NCHAL) qLimb (qN : ℤ) hq hM _ _ _ _ hT.hrsq hT.hfld1 hT.hrb hT.hwrb hT.grb
  have fb : CZm (qN : ℤ) (sVal (tr NCHAL) (vB B_ACT))
      (sVal (tr NCHAL) (FLD_IN 0) + sVal (tr NCHAL) (vB RB)) :=
    addCore_forces (tr NCHAL) qLimb (qN : ℤ) hq hM _ _ _ _ hT.hfld0 hT.hrb hT.hbact hT.hwb hT.gb
  have heq : sVal (tr NCHAL) (vB B_ACT) = sVal (tr NCHAL) B_CL :=
    blockEqP_sVal _ _ _ hT.hbact hT.hbcl hT.gcmp
  rw [← heq]
  exact CZm.trans fb (CZm.add (CZm.refl _) frb)

/-- The reciprocity weld on one row: the round's challenge and inverse multiply to the pinned `1`. -/
structure WeldSound (tr : Trace) (r : Nat) : Prop where
  hone : sVal (tr r) ONE = 1
  honeR : Ranged (tr r) ONE
  hchal : Ranged (tr r) CHAL
  hinv : Ranged (tr r) CHALINV
  hrcp : Ranged (tr r) (vB RCP)
  hwrcp : MulWitRanged (tr r) (mW MK_RCP)
  grcp : MulSat (tr r) qLimb CHAL CHALINV (vB RCP) (mW MK_RCP)
  /-- The every-row comparison against the pinned `ONE` block. -/
  gcmp : BlockEqP (tr r) (vB RCP) ONE

/-- ⚑ **`reciprocity_forced`** — `chal · chalinv ≡ 1 (mod q)`, on the row's own two columns. This is
what makes "the challenge the fold consumed" and "the inverse the opening's `L` leg carries" one
value and its inverse rather than two unrelated witnesses. -/
theorem reciprocity_forced (tr : Trace) (r : Nat) (hW : WeldSound tr r) :
    CZm (qN : ℤ) (sVal (tr r) CHAL * sVal (tr r) CHALINV) 1 := by
  have frcp : CZm (qN : ℤ) (sVal (tr r) (vB RCP))
      (sVal (tr r) CHAL * sVal (tr r) CHALINV) :=
    mulCore_forces (tr r) qLimb (qN : ℤ) qLimb_bounds qLimb_recomposes _ _ _ _
      hW.hchal hW.hinv hW.hrcp hW.hwrcp hW.grcp
  have heq : sVal (tr r) (vB RCP) = sVal (tr r) ONE :=
    blockEqP_sVal _ _ _ hW.hrcp hW.honeR hW.gcmp
  rw [heq, hW.hone] at frcp
  exact CZm.symm frcp

/-- ⚑ **`conjunction_forces` — THE STATEMENT, and it is a CONJUNCTION.**

A trace satisfying this ONE descriptor's round rows, threads, seed pins, terminal combination,
`xiCorrect` gates and per-row welds forces, at once and over shared columns:

* finalize's ξ conjunct — the squeeze IS the claimed ξ;
* finalize's `b` conjunct — **the claimed `b0` is `bEval ζ chals + r · bEval ζω chals`, against
  `PastaIPA.bEval` itself**, over the challenge vector the trace's own rows supplied;
* the weld — every challenge the fold consumed is the inverse of the scalar the opening's `L` leg
  carries.

⚠ Read what is NOT here: `cipCorrect` and `plonkChecksPassed` are absent by construction (§0), and
nothing in this statement forces the MSM's arithmetic — that is the bind leg's sub-proof. **This is a
TWO-way AND with the opening, not upstream's four-way.** -/
theorem conjunction_forces (tr : Trace)
    (hrow : ∀ e r, e < 2 → r < NCHAL → RowSound tr e r)
    (hthread : ∀ e r, e < 2 → r < NCHAL → Threaded tr e r)
    (hrng : ∀ e r, e < 2 → r ≤ NCHAL → Ranged (tr r) (SQ_IN e) ∧ Ranged (tr r) (FLD_IN e))
    (hseedSq : ∀ e, e < 2 → sVal (tr 0) (SQ_IN e) = sVal (tr 0) (PT e))
    (hseedFld : ∀ e, e < 2 → sVal (tr 0) (FLD_IN e) = 1)
    (hxiR : Ranged (tr NCHAL) XI_SQ ∧ Ranged (tr NCHAL) XI_CL)
    (hxi : BlockEqP (tr NCHAL) XI_SQ XI_CL)
    (hterm : TerminalSound tr)
    (hweld : ∀ r, r < NCHAL → WeldSound tr r) :
    sVal (tr NCHAL) XI_SQ = sVal (tr NCHAL) XI_CL
    ∧ CZm (qN : ℤ) (sVal (tr NCHAL) B_CL)
        (Dregg2.Circuit.Emit.PastaIPA.bEval (sVal (tr 0) (PT 0)) (chalVec tr)
          + sVal (tr NCHAL) RSQ
            * Dregg2.Circuit.Emit.PastaIPA.bEval (sVal (tr 0) (PT 1)) (chalVec tr))
    ∧ ∀ r, r < NCHAL → CZm (qN : ℤ) (sVal (tr r) CHAL * sVal (tr r) CHALINV) 1 := by
  refine ⟨blockEqP_sVal _ _ _ hxiR.1 hxiR.2 hxi, ?_, fun r hr => reciprocity_forced tr r (hweld r hr)⟩
  -- the two registers, forced to the two folds
  have f0 : CZ2 (qN : ℤ) (regIn tr 0 NCHAL) (bChainRef tr 0 NCHAL) :=
    threadedBFold_forces tr 0 NCHAL (fun r hr => hrow 0 r (by decide) hr)
      (fun r hr => hthread 0 r (by decide) hr) (fun r hr => hrng 0 r (by decide) hr)
  have f1 : CZ2 (qN : ℤ) (regIn tr 1 NCHAL) (bChainRef tr 1 NCHAL) :=
    threadedBFold_forces tr 1 NCHAL (fun r hr => hrow 1 r (by decide) hr)
      (fun r hr => hthread 1 r (by decide) hr) (fun r hr => hrng 1 r (by decide) hr)
  have e0 := bChainRef_is_bEval tr 0 (hseedSq 0 (by decide)) (hseedFld 0 (by decide))
  have e1 := bChainRef_is_bEval tr 1 (hseedSq 1 (by decide)) (hseedFld 1 (by decide))
  have g0 : CZm (qN : ℤ) (sVal (tr NCHAL) (FLD_IN 0))
      (Dregg2.Circuit.Emit.PastaIPA.bEval (sVal (tr 0) (PT 0)) (chalVec tr)) := by
    have := f0.2; rwa [e0] at this
  have g1 : CZm (qN : ℤ) (sVal (tr NCHAL) (FLD_IN 1))
      (Dregg2.Circuit.Emit.PastaIPA.bEval (sVal (tr 0) (PT 1)) (chalVec tr)) := by
    have := f1.2; rwa [e1] at this
  exact CZm.trans (terminal_forces tr hterm)
    (CZm.add g0 (CZm.mul (CZm.refl _) g1))

/-! ## §18 — the HONEST witness, generated HERE (Rust fills cells, it does not author them).

`PastaCurveSound` §8's rule, at the fold scale: the `CJ_WIDTH` cells of an honest row are computed in
Lean from the same op table the legs walk, and the emit driver renders them. The Rust test parses
felts. A slip between the gate layout and the witness layout is a Lean error, not a silent wrong
cell. -/

/-- The `SK` limbs of a value. -/
def limbBlock (v : Nat) : List ℤ := (List.range SK).map (limbAt v)

/-- A multiply's private witness block: 32 quotient limbs then 62 offset carries. -/
def mulWitBlock (M : Nat) (pl : Nat → ℤ) (xv yv zv : Nat) : List ℤ :=
  let qv := (xv * yv - zv) / M
  limbBlock qv ++ (List.range (NG - 1)).map (fun i => carryOf xv yv zv qv pl (i + 1) + COFF)

/-- An add/sub's private witness block: the carry/borrow bit then 31 offset carries. -/
def addSubWitBlock (M : Nat) (pl : Nat → ℤ) (isSub : Bool) (xv yv zv : Nat) : List ℤ :=
  let cv : ℤ := if isSub then ((zv + yv - xv) / M : Nat) else ((xv + yv - zv) / M : Nat)
  let sy : ℤ := if isSub then -1 else 1
  let sc : ℤ := if isSub then 1 else -1
  cv :: (List.range (NA - 1)).map (fun i => adCarryOf xv yv zv cv pl sy sc (i + 1) + ACOFF)

/-- The 18 input values of one row, in block order. -/
structure RowIn where
  xiSq : Nat
  xiCl : Nat
  bCl : Nat
  z1 : Nat
  z2 : Nat
  c : Nat
  cip : Nat
  zeta : Nat
  zetaw : Nat
  rsq : Nat
  sq0 : Nat
  sq1 : Nat
  fld0 : Nat
  fld1 : Nat
  chal : Nat
  chalinv : Nat

/-- The 18 ARITHMETIC value slots this row computes, in slot order. (`LADDER_VK` and
`LADDER_COMMIT` are the seam's declared lanes, not computed values; `conjunctionRow` writes them
separately because `commit` must carry the eight BOUND lane cells rather than a limbed number.) -/
def rowVals (M : Nat) (i : RowIn) : List Nat :=
  let sqo0 := i.sq0 * i.sq0 % M
  let sqo1 := i.sq1 * i.sq1 % M
  let prd0 := i.chal * i.sq0 % M
  let prd1 := i.chal * i.sq1 % M
  let sum0 := (1 + prd0) % M
  let sum1 := (1 + prd1) % M
  let fldo0 := i.fld0 * sum0 % M
  let fldo1 := i.fld1 * sum1 % M
  let rcp := i.chal * i.chalinv % M
  let lc := i.c * i.chalinv % M
  let rc := i.c * i.chal % M
  let rb := i.rsq * i.fld1 % M
  let bact := (i.fld0 + rb) % M
  let ccip := i.c * i.cip % M
  let z1b0 := i.z1 * i.bCl % M
  let ubc := (ccip + M - z1b0) % M
  let nz1 := (M - i.z1) % M
  let nz2 := (M - i.z2) % M
  [sqo0, sqo1, prd0, prd1, sum0, sum1, fldo0, fldo1, rcp, lc, rc, rb, bact, ccip, z1b0, ubc,
   nz1, nz2]

/-- ⚑ **THE SEAM'S COMMITMENT BLOCK, which is the whole point of `bound`.**

`bindLeg`'s eight `commit` lanes are columns `vB LADDER_COMMIT … +7` and its eight `bound` lanes are
limb 0 of `UBC`, `NEG_Z1`, `NEG_Z2`, `CCIP`, `Z1B0`, `LC`, `RC`, `B_ACT`. The deployed AIR asserts
`guard · (commit − bound) = 0` lane by lane, so an honest witness cannot leave this block zero — the
commitment IS this row's own forced coefficient cells, which is exactly the property that
distinguishes a state-carrying fold from a re-pin. -/
def commitBlock (M : Nat) (i : RowIn) : List ℤ :=
  let vs := rowVals M i
  let g : Nat → Nat := fun k => vs.getD k 0
  [UBC, NEG_Z1, NEG_Z2, CCIP, Z1B0, LC, RC, B_ACT].map (fun k => limbAt (g k) 0)
  ++ (List.range (SK - 8)).map (fun _ => (0 : ℤ))

/-- ⚑ **THE HONEST ROW** — `CJ_WIDTH` cells: the 18 input blocks, the 20 value blocks, the 12
multiply witnesses and the 6 add/sub witnesses, in the allocator's own order. -/
def conjunctionRow (M : Nat) (pl : Nat → ℤ) (i : RowIn) : List ℤ :=
  let ins : List Nat :=
    [i.xiSq, i.xiCl, i.bCl, i.z1, i.z2, i.c, i.cip, i.zeta, i.zetaw, i.rsq,
     1, 0, i.sq0, i.sq1, i.fld0, i.fld1, i.chal, i.chalinv]
  let vs := rowVals M i
  let g : Nat → Nat := fun k => vs.getD k 0
  (ins.flatMap limbBlock)
  ++ (vs.flatMap limbBlock)
  -- `LADDER_VK`: the sub-proof's program-VK lanes. `vkPin` is `none`, so the seam pins nothing
  -- here and an honest witness leaves them zero — which is the unpinned PROGRAM half, said in
  -- cells rather than in prose.
  ++ (List.range SK).map (fun _ => (0 : ℤ))
  -- `LADDER_COMMIT`: the eight lanes the seam TIES to this row's own forced coefficients.
  ++ commitBlock M i
  -- the twelve multiplies, in `mW` index order
  ++ mulWitBlock M pl i.sq0 i.sq0 (g (SQ_OUT 0))
  ++ mulWitBlock M pl i.sq1 i.sq1 (g (SQ_OUT 1))
  ++ mulWitBlock M pl i.chal i.sq0 (g (PRD 0))
  ++ mulWitBlock M pl i.chal i.sq1 (g (PRD 1))
  ++ mulWitBlock M pl i.fld0 (g (SUM 0)) (g (FLD_OUT 0))
  ++ mulWitBlock M pl i.fld1 (g (SUM 1)) (g (FLD_OUT 1))
  ++ mulWitBlock M pl i.chal i.chalinv (g RCP)
  ++ mulWitBlock M pl i.c i.chalinv (g LC)
  ++ mulWitBlock M pl i.c i.chal (g RC)
  ++ mulWitBlock M pl i.rsq i.fld1 (g RB)
  ++ mulWitBlock M pl i.c i.cip (g CCIP)
  ++ mulWitBlock M pl i.z1 i.bCl (g Z1B0)
  -- the six add/subs, in `aW` index order
  ++ addSubWitBlock M pl false 1 (g (PRD 0)) (g (SUM 0))
  ++ addSubWitBlock M pl false 1 (g (PRD 1)) (g (SUM 1))
  ++ addSubWitBlock M pl false i.fld0 (g RB) (g B_ACT)
  ++ addSubWitBlock M pl true (g CCIP) (g Z1B0) (g UBC)
  ++ addSubWitBlock M pl true 0 i.z1 (g NEG_Z1)
  ++ addSubWitBlock M pl true 0 i.z2 (g NEG_Z2)

/-- The next row's register values: the fold advanced by one round. -/
def stepRegs (M : Nat) (i : RowIn) : Nat × Nat × Nat × Nat :=
  (i.sq0 * i.sq0 % M, i.sq1 * i.sq1 % M,
   i.fld0 * ((1 + i.chal * i.sq0 % M) % M) % M,
   i.fld1 * ((1 + i.chal * i.sq1 % M) % M) % M)

#assert_axioms the_rows_are_the_rounds_plus_the_read_row
#assert_axioms nin_eq
#assert_axioms scratch_eq
#assert_axioms cj_width_eq
#assert_axioms threadLegs_length
#assert_axioms seedLegs_length
#assert_axioms conjunctionAir_mainRailOk
#assert_axioms conjunctionAirUnthreaded_mainRailOk
#assert_axioms conjunctionAir_window_selectors
#assert_axioms the_twin_is_the_thread_removed
#assert_axioms conjunctionAir_bind_shape
#assert_axioms conjunctionDesc_constraint_count
#assert_axioms threaded_conj_width_is_flat
#assert_axioms the_row_local_layout_is_linear_in_the_round_count
#assert_axioms the_thread_is_what_collapses_the_artifact
#assert_axioms threading_trades_columns_for_rows_and_cells
#assert_axioms allocator_is_disjoint
#assert_axioms witness_bands_are_disjoint
#assert_axioms one_challenge_pair_per_row
#assert_axioms smallDvd_zero
#assert_axioms smallDvd_forces_eq
#assert_axioms eqBlock_is_eqConstrs
#assert_axioms firstEqBlock_is_the_local_body
#assert_axioms lastEqBlock_is_the_local_body
#assert_axioms eqConstr_dvd_iff
#assert_axioms blockEq_of_dvd
#assert_axioms blockEqP_sVal
#assert_axioms constBlock_forces_sVal
#assert_axioms bFoldFrom_fst
#assert_axioms bFoldFrom_snd_eq_bEval
#assert_axioms bStep_congr
#assert_axioms row_forces
#assert_axioms threaded_carries
#assert_axioms threadedBFold_forces
#assert_axioms threadedBFold_forces_one
#assert_axioms bChainRef_is_bEval
#assert_axioms terminal_forces
#assert_axioms reciprocity_forced
#assert_axioms conjunction_forces

end Dregg2.Circuit.Emit.MinaWrapConjunctionAir
