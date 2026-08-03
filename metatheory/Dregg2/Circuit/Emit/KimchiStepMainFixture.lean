/-
`KimchiStepMain` — THE FIXTURE LAYER for §12–§18: every value the pins are stated about
(the smoke assembly `tS` and its grid, the forged/bent variants, the compiled value layers,
the `check_bulletproof` exhibit points), in the file's own order.

⚑ THE RULE, so the next lane does not have to guess: a `def` goes HERE, a `#guard` goes in a
`…PinsNN`. That is what makes the thirteen pin modules mutually independent and hence PARALLEL —
before the split all 838 guards sat in one 8,900-line file that elaborated serially.
-/
import Dregg2.Circuit.Emit.KimchiStepMainCore

namespace Dregg2.Circuit.Emit.KimchiStepMain

open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder
  (VarEnv GateWitness gridAt envIndex envLookupAt gateVarWitnessAt compose)
open Dregg2.Circuit.Emit.KimchiRenderVarBaseMul (fAdd fMul)
open Dregg2.Circuit.Emit.KimchiRenderCompleteAdd (completeAddWitness)
open Dregg2.Circuit.Emit.KimchiCustomGates (poseidonRowCoeffs)
open Dregg2.Circuit.Emit.KimchiRenderEndoMulScalar (cFuncFp dFuncFp)
open Dregg2.Circuit.Emit.KimchiComposeStepFragment
  (TermData EndoBlock runVbm endoStep dblA addA onCurveA jOf jDbl jAdd jNeg)
open Dregg2.Circuit.Emit.KimchiVerify
  (varBaseMulConstraints completeAddConstraints endoMulConstraints endomulScalarConstraints)
open Dregg2.Circuit.Emit.PastaCurve (jacEqM scMulM)
open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaPoseidon (rcsN)
open Dregg2.Bridge.MinaWrapFtEval0 (IDX_Z IDX_SEL IDX_W IDX_COEFF IDX_S)

set_option autoImplicit false
set_option maxRecDepth 100000

-- ── the values §12 pins ────────────────────────────────────────
def tS : StepData := mkStep shapeSmoke

def rowsS : List SRow := rungRows tS .opening true

def rowsUS : List SRow := rungRows tS .opening false

def nRowsS : Nat := rowsS.length

def pubS : Nat := shapeSmoke.pubWords

def gatesS : List PGate := stepGates rowsS

def gatesUS : List PGate := stepGates rowsUS

def placedS : List PlacedGate := placedOf pubS gatesS

def placedUS : List PlacedGate := placedOf pubS gatesUS

def posS : List (PVar × Cell) := circuitPositions pubS gatesS

def posUS : List (PVar × Cell) := circuitPositions pubS gatesUS

def pairsS : List (Cell × Cell) := permPairs posS

def pairsUS : List (Cell × Cell) := permPairs posUS

def witS : List (List Int) := stepWitness tS pubS rowsS

def totalRowsS : Nat := pubS + nRowsS

def rowKindAt (r : Nat) : KGateType := (rowsS.getD (r - pubS) default).kind

-- ── the values §12a pins ────────────────────────────────────────
def sq1S : Nat := frSqueezeVal tS.segB tS.specB

def sq2S : Nat := frSqueeze2Val tS.segB tS.specB

def xiFoldS : Nat := tS.defc.lift shapeSmoke 0

def rFoldS : Nat := tS.defc.lift shapeSmoke 1

/-- The multiplier a given fr-sponge squeeze would produce: `lowest_128_bits`, then
`to_field_checked` — the whole §8g chain, as a value. -/
def foldMulOf (sq : Nat) : ZMod pN :=
  Dregg2.Circuit.Emit.KimchiVerify.endoMap ((ENDO_R : Nat) : ZMod pN)
    (Dregg2.Circuit.Emit.KimchiVerify.low128 sq)

def cipEzS : List (ZMod pN) := tS.df.ez.map (fun n => (n : ZMod pN))

def cipEwS : List (ZMod pN) := tS.df.ew.map (fun n => (n : ZMod pN))

-- ── the values §12i pins ────────────────────────────────────────
def spNoCip : SpongeData := runSponge shapeSmoke (stepBases shapeSmoke) (0, 0)

-- ── the values §12j pins ────────────────────────────────────────
/-- The absolute row of a `CompleteAdd` whose LEFT operand is `v` — the emitted row itself, found in
the schedule rather than counted by hand. -/
def caRowIxOf (v : PVar) : Nat :=
  (((rowsS.zip (List.range nRowsS)).find? (fun ri =>
      ri.1.kind == KGateType.completeAdd && ri.1.perm.getD 0 none == some v)).map (·.2)).getD 0

/-- …its 15 cells off the composed grid, with cols `i`/`i+1` overridden. -/
def caCellsAt (ix : Nat) (i : Nat) (p : Nat × Nat) : List Nat :=
  let r := gridRow witS (pubS + ix)
  (List.range r.length).map (fun j =>
    if j == i then p.1 else if j == i + 1 then p.2 else r.getD j 0)

def caHolds (cells : List Nat) : Bool :=
  (completeAddConstraints (R := ZMod pN) (cells.map (fun n => (n : ZMod pN)))).all
    (fun z => decide (z = 0))

/-- ⚑ THE WITNESS: another of the block's OWN on-curve commitments. `assert_on_curve` cannot refuse
it and neither can any curve gate — which is precisely why a fold that never READ the accumulator's
starting point could be handed any of them. -/
def sgAlt : Nat × Nat := Dregg2.Bridge.MinaStepPrevCommitments.GAMMA_XY.getD 29 (0, 0)

/-- ⚑ THE WITNESS: the prover absorbs the honest `cip` and CLAIMS a different one — or claims the
honest one and absorbs a different one. Before, the two were unrelated objects: `vCipShift` was a
statement word R8 compared, `oCip`'s lane was a `msgVal` fixture, and NO cell joined them. -/
def cipForged : Nat := fAdd tS.fin.cipShift 1

def spCip : SpongeData :=
  runSpongeAt shapeSmoke (stepBases shapeSmoke) indexDigest (cipForged, cipForged % 2)
    (oCip shapeSmoke) 0 cipForged

/-- ⚑ THE WITNESS: another real on-curve point in `delta`'s slot. Membership cannot refuse it; only
a row that READS it can. -/
def delAlt : Nat × Nat := Dregg2.Bridge.MinaStepPrevCommitments.GAMMA_XY.getD 28 (0, 0)

/-- The first absorbed fold round, and the first constant one. -/
def absR0 : Nat := (absRoundList shapeSmoke).headD 0

def constR0 : Nat :=
  ((List.range shapeSmoke.ipaRounds).filter
     (fun r => ipaSrc shapeSmoke r == BaseSrc.const)).headD 0

def nTrans : Nat := pubS + (transcriptRows shapeSmoke tS.sp true).length

/-- The supplied commitments with base `k` replaced by ANOTHER of the real block's points — a prover
who hands `verify_one` a different, perfectly valid, on-curve commitment. -/
def basesSwapped (s : StepShape) (k : Nat) : List (Nat × Nat) :=
  let bs := stepBases s
  (List.range bs.length).map (fun i =>
    if i == k then Dregg2.Bridge.MinaStepPrevCommitments.GAMMA_XY.getD 29 (0, 0)
    else bs.getD i (0, 0))

def tSwapAbs : StepData :=
  mkStepWith shapeSmoke (basesSwapped shapeSmoke (shapeSmoke.msmTerms + absR0))

def tSwapConst : StepData :=
  mkStepWith shapeSmoke (basesSwapped shapeSmoke (shapeSmoke.msmTerms + constR0))

def pinRowOf (r : Nat) : SRow :=
  baseConstRow (ipx shapeSmoke (qT shapeSmoke r)) (ipy shapeSmoke (qT shapeSmoke r))
    (tS.ipa.bases.getD r (0, 0))

def pinBody (row : SRow) (p : Nat × Nat) : ZMod pN :=
  Dregg2.Circuit.Emit.KimchiVerify.genericGateConstraint (1 : ZMod pN) (3 : ZMod pN)
    (row.coeffs.map (fun c => ((c : Int) : ZMod pN)))
    [(p.1 : ZMod pN), 0, 0, (p.2 : ZMod pN), 0, 0]

-- ── the values §12b′ pins ────────────────────────────────────────
/-- ⚑ THE FORGERY THE MISSING CHECK ALLOWED: absorbed base `absR0`'s `y` bumped by one — a point
that is NOT on Pallas. Nothing else changes; the prover absorbs what he supplies, so the transcript
still swallows exactly these two coordinates and every downstream value is internally consistent. -/
def basesOffCurve (s : StepShape) : List (Nat × Nat) :=
  let bs := stepBases s
  let k := s.msmTerms + absR0
  (List.range bs.length).map (fun i =>
    let p := bs.getD i (0, 0)
    if i == k then (p.1, fAdd p.2 1) else p)

def tOffCurve : StepData := mkStepWith shapeSmoke (basesOffCurve shapeSmoke)

def offPt : Nat × Nat := tOffCurve.ipa.bases.getD absR0 (0, 0)

def honPt : Nat × Nat := tS.ipa.bases.getD absR0 (0, 0)

/-- The bent instance's R4 rung, composed. -/
def rowsOff : List SRow := rungRows tOffCurve .ipa true

def witOff : List (List Int) := stepWitness tOffCurve 0 rowsOff

/-- The absolute row of R4's FIRST `assert_on_curve` row, in the `.ipa` rung. -/
def onCRow0 : Nat := (rungRows tS .msm true).length + (ipaBaseRows shapeSmoke tS.ipa).length
                     + (ipaSeedPinRows shapeSmoke).length

def nOnCRows : Nat := (onCurveRows shapeSmoke).length

/-- A row's own double-`Generic` body, read out of a composed grid. -/
def genBodyAt (rows : List SRow) (w : List (List Int)) (pub r : Nat) : ZMod pN :=
  Dregg2.Circuit.Emit.KimchiVerify.genericGateConstraint (1 : ZMod pN) (3 : ZMod pN)
    ((rows.getD (r - pub) default).coeffs.map (fun c => ((c : Int) : ZMod pN)))
    ((gridRow w r).take 6 |>.map (fun n => (n : ZMod pN)))

-- ── the values §12c pins ────────────────────────────────────────
/-- The transcript squeeze challenge `c` is split out of. -/
def sqOf (c : Nat) : Nat := sqValOf shapeSmoke tS.sp c

/-- The honest `(combined_inner_product, bit)` pair transcript block `oCip` absorbs — the statement
word R8 binds, so a control that re-runs the sponge feeds it what the assembly feeds it. -/
def cipWordOf (t : StepData) : Nat × Nat := (t.fin.cipShift, t.fin.cipShift % 2)

def TWO128 : Nat := 2 ^ 128 % pN

def INV_TWO128 : Nat := Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv TWO128

/-- ⚑ THE FORGERY THE MISSING CHECK ALLOWED: the prover picks ANY 128-bit low part and the
decomposition row hands back the high part that makes it hold. -/
def forgedLo : Nat := (chalOf shapeSmoke tS.sp 0 + 1) % 2 ^ 128

def forgedHi : Nat := fMul (fSub (sqOf 0) forgedLo) INV_TWO128

-- ── the values §12c′ pins ────────────────────────────────────────
/-- R8's own `lowest_128_bits` cells, as circuit variables. -/
def finHiVar : PVar := aVarAt (baseFin shapeSmoke tS.ft) tS.fin.fp.prog tS.fin.fp.slots.xiHi

def finLoVar : PVar := aVarAt (baseFin shapeSmoke tS.ft) tS.fin.fp.prog tS.fin.fp.slots.xiActual

/-- Re-run R8's finalize program with a CHOSEN ξ: the statement word set to `xi'` and
`lowest_128_bits`' high part set to `hi'`. Every other input, and every `Field.equal` witness, is
the honest one — so what this measures is whether R8's own gadget accepts, not whether some other
leg was sabotaged. Returns `(out, xi_correct, xi_actual)`; `out` is the value the rung's last row
ASSERTS equals 1. -/
def finAtChosenXi (xi' hi' : Nat) : Nat × Nat × Nat :=
  let s := shapeSmoke
  let env := (finInputEnv s tS.sp tS.ft tS.df tS.segB tS.specB rFoldS tS.bp.ver).map
    (fun p => if p.1 == vXiStmt s then (p.1, (xi' : Int)) else p)
  let p := finProgOf (finWireOf s tS.ft) (finCfgOf s hi')
  let vs := aEval (envLookupAt (envIndex env)) p.prog
  (vs.getD p.slots.out 0, vs.getD p.slots.xc 0, vs.getD p.slots.xiActual 0)

/-- ⚑ THE FORGERY R8's MISSING HIGH CHAIN ALLOWED: the prover names the ξ he wants and the
decomposition row hands back the high part that makes `xi_correct` hold. -/
def forgedXi : Nat := (tS.fin.xiStmt + 1) % 2 ^ 128

def forgedXiHi : Nat := fMul (fSub sq1S forgedXi) INV_TWO128

-- ── the values §12d pins ────────────────────────────────────────
/-- The state entering the LAST index absorb block: everything before it is untouched by the word
the prover grinds, so a candidate costs ONE permutation rather than fifty-eight. ⚑ ONE since the
lazy re-model: `Sponge.squeeze_field (Sponge.copy sponge_after_index)` performs the 28th permutation
itself (`sponge.ml:322-325`), where the eager model spent a 29th on top of it. -/
def idxPreLast : List Nat := (idxStatesWith idxWordAt).getD (N_IDX_COMMS - 1) []

/-- `index_digest` when the LAST index word is `w` and every earlier one is honest. -/
def idxDigestAtLast (w : Nat) : Nat :=
  (Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm
      [ (idxPreLast.getD 0 0 + idxWordAt (N_IDX_WORDS - 2)) % pN
      , (idxPreLast.getD 1 0 + w) % pN, idxPreLast.getD 2 0 ]).getD 0 0

/-- ⚑ THE TARGET THE PROVER CHOOSES. Any predicate on the squeeze will do; this one asks for a
digest divisible by 16, which the honest key does not give. -/
def GRIND_MOD : Nat := 16

def grindCand (t : Nat) : Nat := (idxWordAt (N_IDX_WORDS - 1) + t) % pN

/-- …and the SEARCH: the first offset whose digest hits it. This is the attack, run. -/
def grindT : Nat :=
  (((List.range 48).map (· + 1)).find?
     (fun t => idxDigestAtLast (grindCand t) % GRIND_MOD == 0)).getD 0

def groundWord : Nat := grindCand grindT

def groundDigest : Nat := idxDigestAtLast groundWord

/-- R1's transcript at the GROUND digest — the assembly's own `runSpongeWith`, one word changed. -/
def spGround : SpongeData :=
  runSpongeWith shapeSmoke (stepBases shapeSmoke) groundDigest (cipWordOf tS)

/-- Segment C re-run with the ground word in the last index slot. -/
def segCGround : SegData :=
  runSeg { tS.specC with
           ws := tS.specC.ws.set (N_IDX_WORDS - 1) (idxVar shapeSmoke 27 1, groundWord) }

/-- The `Inner_curve.constant` row §3c emits for index commitment `k`. -/
def idxPinRow (k : Nat) : SRow :=
  baseConstRow (vIdxX shapeSmoke k) (vIdxY shapeSmoke k)
    (Dregg2.Bridge.MinaStepPrevCommitments.INDEX_XY.getD k (0, 0))

-- ── the values §12e pins ────────────────────────────────────────
/-- `[2^n]·P` in Jacobian. -/
def jPow2 (n : Nat) (P : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (List.range n).foldl (fun Q _ => jDbl Q) P

/-- `[s + 2^255]·g` — `scale_fast2`'s own semantics (`plonk_curve_ops.ml:236-249`;
`shifted_value.ml:140-150`: `to_field t = t + 2^{size_in_bits}`), computed by `PastaCurve`'s
INVERSION-FREE Jacobian double-and-add, an entirely separate formula family from the affine ladder. -/
def ftcJacScale (g : Nat × Nat) (sv : Nat) : Nat × Nat × Nat :=
  match scMulM pN sv (jOf g) with
  | some R => jAdd (jPow2 255 (jOf g)) R
  | none => jPow2 255 (jOf g)

/-- `Common.ft_comm` re-run with `t_comm[i]` replaced by another of the real block's points — a
prover who hands `verify_one` a different, perfectly valid, ON-CURVE quotient commitment. -/
def tcSwapped (i : Nat) : Nat → Nat × Nat := fun k =>
  if k == i then Dregg2.Bridge.MinaStepPrevCommitments.GAMMA_XY.getD 29 (0, 0) else ftcTc k

def ftcSwap0 : FtcData := runFtcWith shapeSmoke tS.ftw (tcSwapped 0)

def ftcHornerReal : Dregg2.Circuit.Emit.MinaWrapGroupGate.Pt :=
  (List.range (N_TCOMM - 1)).foldl
    (fun acc j =>
      Dregg2.Circuit.Emit.MinaWrapGroupGate.padd
        (Dregg2.Circuit.Emit.MinaWrapGroupGate.TCHUNKS.getD (N_TCOMM - 2 - j) (0, 0, 0))
        (Dregg2.Circuit.Emit.MinaWrapGroupGate.smul
          Dregg2.Circuit.Emit.MinaWrapGroupGate.ZETA_SRS acc))
    (Dregg2.Circuit.Emit.MinaWrapGroupGate.TCHUNKS.getD (N_TCOMM - 1) (0, 0, 0))

/-- `common.ml:246,255-256` at the real block, with `zeta_to_domain_size` as a PARAMETER so the
Maller-factor conflation is a red control and not a coincidence. -/
def ftcRealAt (zDom : Nat) : Dregg2.Circuit.Emit.MinaWrapGroupGate.Pt :=
  Dregg2.Circuit.Emit.MinaWrapGroupGate.padd
    (Dregg2.Circuit.Emit.MinaWrapGroupGate.padd
      (Dregg2.Circuit.Emit.MinaWrapGroupGate.smul
        Dregg2.Circuit.Emit.MinaWrapGroupGate.PERM_SCALAR
        Dregg2.Circuit.Emit.MinaWrapGroupGate.SIGMA6)
      ftcHornerReal)
    (Dregg2.Circuit.Emit.MinaWrapGroupGate.pneg
      (Dregg2.Circuit.Emit.MinaWrapGroupGate.smul zDom ftcHornerReal))

/-- `zeta_to_domain_size = ζⁿ`, i.e. one MORE than the Maller factor the gate carries. -/
def ZETA_DOM : Nat := Dregg2.Circuit.Emit.MinaWrapGroupGate.ZETA_DOM_M1 + 1

-- ── the values §12e′ pins ────────────────────────────────────────
/-- The absorb SOURCE `t_comm`'s LAST chunk is — the last one before ζ, so a candidate costs ONE
permutation rather than twelve. -/
def tcOrd : Nat := oCip shapeSmoke - 1

/-- …as a BLOCK index, and the LANE its second word lands in. ⚑ Since the lazy re-model a candidate
costs **ONE** permutation, not two: ζ's squeeze (`:568`, immediately after `receive without t_comm`
at `:567`) IS this block's own permutation (`sponge.ml:322-325`, the `Absorbed _` arm), where the
eager model spent a second one on top. -/
def tcBlk : Nat := (itemAt shapeSmoke tcOrd 1).1
def tcLane : Nat := (itemAt shapeSmoke tcOrd 1).2

def tcHon : Nat := (ftcTc (tCommN shapeSmoke - 1)).2

/-- ζ when that word is `w` and every earlier one is honest — ONE permutation of the state entering
`tcBlk`, with the block's own two items in their `spLay` lanes and `w` in the bent one. -/
def tcChalAt (w : Nat) : Nat :=
  let L := spLay shapeSmoke
  let pre := tS.sp.states.getD tcBlk []
  let ws := (blockWordsL L tcBlk).map (fun o =>
    match o with
    | none => 0
    | some (a, j) =>
        if a == tcOrd && j == 1 then w
        else msgValOf shapeSmoke (stepBases shapeSmoke) (cipWordOf tS) a j)
  ((Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm
      [ (pre.getD 0 0 + ws.getD 0 0) % pN, (pre.getD 1 0 + ws.getD 1 0) % pN
      , pre.getD 2 0 ]).getD 0 0) % 2 ^ shapeSmoke.chalBits

/-- …and the SEARCH: the first additive offset whose challenge hits the prover's target. -/
def tcGrindT : Nat :=
  (((List.range 64).map (· + 1)).find? (fun t =>
     tcChalAt ((tcHon + t) % pN) % GRIND_MOD == 0)).getD 0

def tcGround : Nat := (tcHon + tcGrindT) % pN

/-- R1's transcript at the ground word — the assembly's OWN `runSpongeAt`, one word changed. -/
def spTc : SpongeData :=
  runSpongeAt shapeSmoke (stepBases shapeSmoke) indexDigest (cipWordOf tS) tcOrd 1 tcGround

/-- `assert_on_curve`'s `assert_square` half as its OWN `Generic` body — `y·y − x³ − b`
(`snarky_curve.ml:212-217`), the third half `onCurveHalves` emits. -/
def tcSqBody (p : Nat × Nat) : ZMod pN :=
  Dregg2.Circuit.Emit.KimchiVerify.genericGateConstraint (1 : ZMod pN) (3 : ZMod pN)
    ((([0, 0, -1, 1, -(PALLAS_B : Int)] : List Int) ++ cNil).map (fun c => ((c : Int) : ZMod pN)))
    [(p.2 : ZMod pN), (p.2 : ZMod pN)
    , ((fMul (fMul p.1 p.1) p.1 : Nat) : ZMod pN), 0, 0, 0]

-- ── the values §12f pins ────────────────────────────────────────
/-- MSM term 0's base — an SRS Lagrange constant PINNED by `msmBaseRows` (§12b), so the exhibit
cannot be mistaken for "the prover swapped the base". -/
def msmT0 : Nat × Nat := (tS.msm.terms.getD 0 default).T

/-- …the HONEST seed, `add_fast base base` = `[2]T`. -/
def msmSeedHon : Nat × Nat := dblA msmT0

/-- ⚑ **THE PROVER'S SEED**: `[3]T`. On the curve, so `Inner_curve.typ`'s check would not object
either — and ANY point works, which is the whole content of the hole. -/
def msmSeedForged : Nat × Nat := addA msmSeedHon msmT0

/-- Term 0's ladder from an arbitrary seed — `runVbm`, the assembly's OWN generator, at the
assembly's own bits. -/
def msmFrom (seed : Nat × Nat) : TermData := runVbm msmT0 seed (tS.msm.bits.getD 0 [])

def msmForged : TermData := msmFrom msmSeedForged

/-- The 15 CURR and 15 NEXT cells of one `VarBaseMul` chunk, laid out as `msmChunkRows` emits them
(`varbasemul.rs:310-331`): base `(w₀,w₁)`, accumulators `(w₂,w₃) (w₇,w₈) (w₉,w₁₀) (w₁₁,w₁₂)
(w₁₃,w₁₄)` on CURR and `(w'₀,w'₁)` on NEXT, `n = w₄`, `n' = w₅`, bits `w'₂..w'₆`, slopes
`w'₇..w'₁₁`. -/
def vbmChunkCells (td : TermData) (bits : List Nat) (j : Nat) : List Nat × List Nat :=
  let ax : Nat → Nat := fun k => (td.accs.getD k (0, 0)).1
  let ay : Nat → Nat := fun k => (td.accs.getD k (0, 0)).2
  ( [ td.T.1, td.T.2, ax (5*j), ay (5*j), td.ns.getD (5*j) 0, td.ns.getD (5*(j+1)) 0, 0
    , ax (5*j+1), ay (5*j+1), ax (5*j+2), ay (5*j+2)
    , ax (5*j+3), ay (5*j+3), ax (5*j+4), ay (5*j+4) ]
  , [ ax (5*(j+1)), ay (5*(j+1))
    , bits.getD (5*j) 0, bits.getD (5*j+1) 0, bits.getD (5*j+2) 0, bits.getD (5*j+3) 0
    , bits.getD (5*j+4) 0
    , td.slopes.getD (5*j) 0, td.slopes.getD (5*j+1) 0, td.slopes.getD (5*j+2) 0
    , td.slopes.getD (5*j+3) 0, td.slopes.getD (5*j+4) 0, 0, 0, 0 ] )

/-- …answered to `varBaseMulConstraints`, proof-systems' own 21 constraints, read-only. -/
def vbmOk (c : List Nat × List Nat) : Bool :=
  (varBaseMulConstraints (R := ZMod pN) (c.1.map (fun n => (n : ZMod pN)))
      (c.2.map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0))

/-- The seed row's eleven `CompleteAdd` cells with the OUTPUT replaced by the point a prover
claims — `msmDblRow`'s own witness, one substitution. -/
def msmDblCellsAt (seed : Nat × Nat) : List Nat :=
  ((completeAddWitness msmT0.1 msmT0.2 msmT0.1 msmT0.2).set 4 seed.1).set 5 seed.2

def caOk (c : List Nat) : Bool :=
  (completeAddConstraints (R := ZMod pN) (c.map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0))

/-- The counter trace `nₖ₊₁ = 2nₖ + bₖ` (`plonk_curve_ops.ml:170`) from an ARBITRARY seed. -/
def nTraceFrom (n0 : Nat) (bits : List Nat) : List Nat :=
  bits.foldl (fun acc b => acc ++ [(2 * acc.getLastD 0 + b) % pN]) [n0]

/-- ⚑ The honest bits with the MSB flipped — a DIFFERENT multiplier, hence a different ladder
output. -/
def msmBitsForged : List Nat :=
  (tS.msm.bits.getD 0 []).set 0 (1 - (tS.msm.bits.getD 0 []).headD 0)

/-- …and the counter seed that makes the chain still close on the SAME challenge cell:
`n₀ = (n_final − N(bits′))·2^{−5·msmChunksAt 0}`, one field inversion. -/
def msmN0Forged : Nat :=
  fMul (fSub ((tS.msm.terms.getD 0 default).ns.getLastD 0)
             ((nTraceFrom 0 msmBitsForged).getLastD 0))
       (Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv (2 ^ (5 * msmChunksAt 0) % pN))

/-- `msmNZeroRows`' first row, as its own `Generic` body — half 1 is `w₀ = 0` over `vSN i 0`. -/
def msmNZeroRow0 : SRow := (msmNZeroRows shapeSmoke).headD default

def nZeroBody (v : Nat) : ZMod pN :=
  Dregg2.Circuit.Emit.KimchiVerify.genericGateConstraint (1 : ZMod pN) (3 : ZMod pN)
    (msmNZeroRow0.coeffs.map (fun c => ((c : Int) : ZMod pN)))
    [(v : ZMod pN), 0, 0, 0, 0, 0]

-- ── the values §12g pins ────────────────────────────────────────
def ipaT0 : Nat × Nat := tS.ipa.bases.getD absR0 (0, 0)

def ipaSeedForged : Nat × Nat := addA (endoSeed ipaT0) ipaT0

/-- Round `absR0`'s endo blocks from an ARBITRARY accumulator seed — `endoStep`, the assembly's own
generator, at the assembly's own bits. -/
def ipaBlocksFrom (seed : Nat × Nat) : List EndoBlock :=
  let bits := endoBitsOf shapeSmoke (chalOf shapeSmoke tS.sp (shapeSmoke.ipaChal absR0))
  ((List.range shapeSmoke.ipaBlocks).foldl
    (fun (st : List (Nat × Nat) × List EndoBlock) e =>
      let cur := st.1.getLastD (0, 0)
      let b := endoStep ipaT0.1 ipaT0.2 cur.1 cur.2
        (bits.getD (4*e) 0) (bits.getD (4*e+1) 0) (bits.getD (4*e+2) 0) (bits.getD (4*e+3) 0)
      (st.1 ++ [(b.xs, b.ys)], st.2 ++ [b]))
    ([seed], [])).2

/-- The 15 CURR / 15 NEXT cells of endo block `e`, as `ipaRoundRows` lays them out. -/
def emCells (blks : List EndoBlock) (accs : List (Nat × Nat)) (ns : List Nat) (e : Nat)
    : List Nat × List Nat :=
  let b := blks.getD e default
  let a := accs.getD e (0, 0)
  let a' := accs.getD (e + 1) (0, 0)
  ( [ ipaT0.1, ipaT0.2, b.inv, 0, a.1, a.2, ns.getD e 0
    , b.xr, b.yr, b.s1, b.s3, b.b1, b.b2, b.b3, b.b4 ]
  , [ 0, 0, 0, 0, a'.1, a'.2, ns.getD (e + 1) 0, 0, 0, 0, 0, 0, 0, 0, 0 ] )

def emOk (c : List Nat × List Nat) : Bool :=
  ((endoMulConstraints (R := ZMod pN) (Dregg2.Circuit.Emit.KimchiRenderEndoMul.endo : ZMod pN)
      (c.1.map (fun n => (n : ZMod pN))) (c.2.map (fun n => (n : ZMod pN)))).take 11).all
    (fun z => decide (z = 0))

/-- Block accumulators from an arbitrary seed. -/
def ipaAccsFrom (seed : Nat × Nat) : List (Nat × Nat) :=
  let bits := endoBitsOf shapeSmoke (chalOf shapeSmoke tS.sp (shapeSmoke.ipaChal absR0))
  (List.range shapeSmoke.ipaBlocks).foldl
    (fun (st : List (Nat × Nat)) e =>
      let cur := st.getLastD (0, 0)
      let b := endoStep ipaT0.1 ipaT0.2 cur.1 cur.2
        (bits.getD (4*e) 0) (bits.getD (4*e+1) 0) (bits.getD (4*e+2) 0) (bits.getD (4*e+3) 0)
      st ++ [(b.xs, b.ys)])
    [seed]

def ipaDblCellsAt (seed : Nat × Nat) : List Nat :=
  let p := endoP ipaT0
  ((completeAddWitness p.1 p.2 p.1 p.2).set 4 seed.1).set 5 seed.2

-- ── the values §13 pins ────────────────────────────────────────
/-- The ft program's slot values at the smoke instance. -/
def ftS : FtData := tS.ft

def ftVal (i : Nat) : Nat := ftS.vals.getD i 0

/-- The ft program's inputs, resolved the way the program resolves them. -/
def ftLkS : PVar → Int := envLookupAt (envIndex (ftInputEnv shapeSmoke tS.sp))

def ftInp (v : PVar) : Nat := (ftLkS v).toNat % pN

def zetaS : Nat := ftInp (vLift shapeSmoke shapeSmoke.zetaChal)

def alphaS : Nat := ftInp (vLift shapeSmoke shapeSmoke.alphaChal)

def betaS : Nat := ftInp (vN shapeSmoke shapeSmoke.betaChal shapeSmoke.emsRows)

def gammaS : Nat := ftInp (vN shapeSmoke shapeSmoke.gammaChal shapeSmoke.emsRows)

/-- The 43 columns, as the `GateEvals` slicing sees them. -/
def colZ (k : Nat) : ZMod pN := ((evZOf ftS.out (EV_PREFIX + k) : Nat) : ZMod pN)

def colW (k : Nat) : ZMod pN := ((evVal (EV_PREFIX + k) 1 : Nat) : ZMod pN)

def wZ : List (ZMod pN) := (List.range 15).map (fun i => colZ (IDX_W + i))

def wW : List (ZMod pN) := (List.range 15).map (fun i => colW (IDX_W + i))

def coeffZ : List (ZMod pN) := (List.range 15).map (fun i => colZ (IDX_COEFF + i))

def sZ : List (ZMod pN) := (List.range 6).map (fun i => colZ (IDX_S + i))

def mdsS3 : List (List (ZMod pN)) :=
  (List.range 3).map (fun j => (List.range 3).map (fun i => ((FT_MDS9.getD (3 * j + i) 0 : Nat) : ZMod pN)))

/-- The `GateEvals` the linearization constant term is evaluated against — assembled from the SAME
column variables the circuit reads. -/
def gS : Dregg2.Circuit.Emit.KimchiVerify.GateEvals (ZMod pN) :=
  { alpha := (alphaS : ZMod pN), endo := ((FT_ENDO : Nat) : ZMod pN), mds := mdsS3
    coeff := coeffZ, w := wZ, wNext := wW
    cA := ((FT_QUOT.1 : Nat) : ZMod pN), cB := ((FT_QUOT.2.1 : Nat) : ZMod pN)
    cC := ((FT_QUOT.2.2 : Nat) : ZMod pN)
    genSel := colZ (IDX_SEL + 0), posSel := colZ (IDX_SEL + 1)
    caddSel := colZ (IDX_SEL + 2), mulSel := colZ (IDX_SEL + 3)
    emulSel := colZ (IDX_SEL + 4), emulScalarSel := colZ (IDX_SEL + 5) }

/-- Compile one body in isolation and read its constraint slots' values. -/
def bodyVals (b : AM (List Nat)) : List (ZMod pN) :=
  let r := b.run #[]
  let vs := aEval ftLkS r.2
  r.1.map (fun i => ((vs.getD i 0 : Nat) : ZMod pN))

/-- The slots every body shares, emitted once at the head of an isolated program. -/
structure WireSlots where
  one : Nat
  negOne : Nat
  three : Nat
  six : Nat
  eleven : Nat
  endo : Nat
  cA : Nat
  cB : Nat
  cC : Nat
  mdsS : List (List Nat)
  coeff : List Nat
  w : List Nat
  wNext : List Nat
  deriving Inhabited

def wireSlots (endoV : Nat) : AM WireSlots := do
  let one ← eLit 1
  let negOne ← eLit (pN - 1)
  let three ← eLit 3
  let six ← eLit 6
  let eleven ← eLit 11
  let endo ← eLit endoV
  let cA ← eLit FT_QUOT.1
  let cB ← eLit FT_QUOT.2.1
  let cC ← eLit FT_QUOT.2.2
  let mdsS ← (List.range 3).foldlM (fun acc j => do
      let row ← (List.range 3).foldlM
        (fun r i => do let v ← eLit (FT_MDS9.getD (3 * j + i) 0); pure (r ++ [v])) []
      pure (acc ++ [row])) []
  let ez ← (List.range 43).foldlM
    (fun acc i => do let v ← eInp (vColZ shapeSmoke i); pure (acc ++ [v])) []
  let ew ← (List.range 43).foldlM
    (fun acc i => do let v ← eInp (vColW shapeSmoke i); pure (acc ++ [v])) []
  pure { one, negOne, three, six, eleven, endo, cA, cB, cC, mdsS
       , coeff := (List.range 15).map (fun i => ez.getD (IDX_COEFF + i) 0)
       , w := (List.range 15).map (fun i => ez.getD (IDX_W + i) 0)
       , wNext := (List.range 15).map (fun i => ew.getD (IDX_W + i) 0) }

def bodyCompleteAdd : AM (List Nat) := do
  let q ← wireSlots FT_ENDO; pCompleteAdd q.one q.w

def bodyVarBaseMul : AM (List Nat) := do
  let q ← wireSlots FT_ENDO; pVarBaseMul q.one q.w q.wNext

def bodyEndoMul (endoV : Nat) : AM (List Nat) := do
  let q ← wireSlots endoV; pEndoMul q.one q.endo q.w q.wNext

def bodyEmScalar : AM (List Nat) := do
  let q ← wireSlots FT_ENDO
  pEmScalar q.cA q.cB q.cC q.negOne q.three q.six q.eleven q.w

def bodyPoseidon : AM (List Nat) := do
  let q ← wireSlots FT_ENDO; pPoseidon q.mdsS q.coeff q.w q.wNext

-- ── the values §14a pins ────────────────────────────────────────
def maskReaders (i : Nat) : Nat :=
  ((List.range (nbA shapeSmoke)).filter (fun b => optProofOf shapeSmoke b == i)).length
  + ((List.range tS.specC.nb).filter
       (fun b => tS.specC.maskedAt b && (hmKeepAt shapeSmoke MASK_BITS b).1 == vMask shapeSmoke i)
     ).length

def segAWith (bits : List Nat) : SegData :=
  runSeg { tS.specA with keep := fun b => (xv 0, bits.getD (optProofOf shapeSmoke b) 0) }

def segADigest (bits : List Nat) : Nat := ((segAWith bits).states.getLastD []).getD 0 0

def segCWith (bits : List Nat) : SegData :=
  runSeg { tS.specC with keep := fun b => (xv 0, (hmKeepAt shapeSmoke bits b).2) }

def segCDigest (bits : List Nat) : Nat := ((segCWith bits).states.getLastD []).getD 0 0

-- ── the values §12k pins ────────────────────────────────────────
/-- Segment C's digest under a word-list transform — the object both directions compare. -/
def segCDigestOf (ws : List (PVar × Nat)) : Nat :=
  ((runSeg { tS.specC with ws := ws }).states.getLastD []).getD 0 0

/-- …and the MIS-WIRED segment's, likewise. -/
def segCMisSpec : SegSpec := hmSpecMiswired shapeSmoke tS.msm tS.ipa

def segCMisDigestOf (ws : List (PVar × Nat)) : Nat :=
  ((runSeg { segCMisSpec with ws := ws }).states.getLastD []).getD 0 0

/-- Bend word `i`'s VALUE by one, leaving its variable and every other word alone. -/
def bendW (ws : List (PVar × Nat)) (i : Nat) : List (PVar × Nat) :=
  ws.set i ((ws.getD i (xv 0, 0)).1, fAdd (ws.getD i (xv 0, 0)).2 1)

/-- The four word POSITIONS at issue, in each layout. -/
def wSgOld0 : Nat := N_HM_FIX

def wSgOld1 : Nat := N_HM_FIX + 2 + shapeSmoke.bRounds

/-- In the MIS-WIRED layout the four commitment coordinates were contiguous at `N_HM_FIX`: x_hat's
sum first, then the fold output. -/
def wXhat : Nat := N_HM_FIX

def wFold : Nat := N_HM_FIX + 2

def wsConcat : List (PVar × Nat) :=
  tS.specC.ws.take N_HM_FIX
  ++ [ tS.specC.ws.getD wSgOld0 (xv 0, 0), tS.specC.ws.getD (wSgOld0 + 1) (xv 0, 0)
     , tS.specC.ws.getD wSgOld1 (xv 0, 0), tS.specC.ws.getD (wSgOld1 + 1) (xv 0, 0) ]
  ++ (List.range (2 * shapeSmoke.bRounds)).map (fun i =>
      (vPrevChal shapeSmoke i, prevChalVal i))

-- ── the values §12l pins ────────────────────────────────────────
/-- `combined_inner_product` as this assembly computes it under a SUPPLIED mask — the same `runDef`
the emitter runs, with only `ms` varying, so every measurement below is about the emitted fold. -/
def cipAtMask (ms : List Nat) : Nat :=
  (runDef shapeSmoke tS.sp ftS.out xiFoldS rFoldS FT_OMEGA prevChalVal ms).ca.getLastD 0

/-- ⚑ **THE WHOLE LEGAL DOMAIN OF THE MASK.** `Prefix_mask.there`
(`pickles_base/proofs_verified.ml:75-81`) is `N0 ↦ [ff;ff] · N1 ↦ [ff;tt] · N2 ↦ [tt;tt]`, and
`Prefix_mask.back` (`:83-91`) `invalid_arg`s on anything else — `[1,0]` in particular is NOT a mask
the circuit can legally see. So a quantifier over this list ranges over EVERY mask, and the ∀ §12l
states is not three transcribed instances that happen to be all of them. -/
def LEGAL_MASKS : List (List Nat) := [[1, 1], [0, 1], [0, 0]]

/-- How many of `combine`'s `Maybe` prefix slots a mask DROPS. ⚑ Because `pcs_batch.ml:85-94` folds
from the list's TAIL and `common.ml:271`'s `else_` is bare `acc`, a dropped slot is not a zeroed
term: `d` is the ξ-power SHIFT applied to every survivor. -/
def dropOf (ms : List Nat) : Nat :=
  (List.range N_CIP_MASKED).countP (fun j => ms.getD j 0 == 0)

/-- …and `cipR` — the READ-ONLY transcription of `verifier.rs` — over the sub-list a mask keeps. -/
def cipRKept (ms : List Nat) : ZMod pN :=
  Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf sq1S) (foldMulOf sq2S)
    (cipEzS.drop (dropOf ms)) (cipEwS.drop (dropOf ms))

/-- `cipR` over the FULL 47 — what `cipRows` computed until 2026-08-02, i.e. the value this rung
CORRECTS. -/
def cipRFull : ZMod pN :=
  Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf sq1S) (foldMulOf sq2S) cipEzS cipEwS

/-- The "zero the dropped entries and still fold all 47" reading — the mux a careless emission
writes, and a THIRD field element distinct from both of the above wherever the mask drops. -/
def cipRZeroed (ms : List Nat) : ZMod pN :=
  Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf sq1S) (foldMulOf sq2S)
    ((List.range cipEzS.length).map (fun i => if i < dropOf ms then 0 else cipEzS.getD i 0))
    ((List.range cipEwS.length).map (fun i => if i < dropOf ms then 0 else cipEwS.getD i 0))

/-- Upstream's TWO-fold form at a mask (`step_verifier.ml:1097-1101`): `combine … + r · combine …`
over the kept sub-list. This region runs ONE fused fold over `cₖ = evₖ(ζ) + r·evₖ(ζω)`; that the two
agree is the fusion commuting with the mux, and §12l states it at every legal mask. -/
def cipFusedAt (ms : List Nat) : ZMod pN :=
  (List.range (shapeSmoke.cipEvals - dropOf ms)).foldl
      (fun acc k => acc + (foldMulOf sq1S) ^ k * (cipEzS.drop (dropOf ms)).getD k 0) 0
    + (foldMulOf sq2S)
      * (List.range (shapeSmoke.cipEvals - dropOf ms)).foldl
          (fun acc k => acc + (foldMulOf sq1S) ^ k * (cipEwS.drop (dropOf ms)).getD k 0) 0

def dfBent0 (ms : List Nat) : DefData :=
  runDef shapeSmoke tS.sp ftS.out xiFoldS rFoldS FT_OMEGA
    (fun i => if i == 0 then fAdd (prevChalVal i) 1 else prevChalVal i) ms

/-- ⚑⚑ **THE LAW OF `combine`'s MUX, AT EVERY MASK THE CIRCUIT CAN LEGALLY SEE.** Six facts at each
of the three legal masks. §12l carried TEN of the eighteen as hand-written `#guard` instances; the
instances could not see the shape of their own domain — a mask silently omitted from the battery is
indistinguishable from a mask that holds, and clauses (iv) and (v) were stated only at the DEPLOYED
mask, so nothing said they hold at `[0,0]` too. The quantifier cannot omit a mask. -/
def cipMaskLaw : Bool :=
  LEGAL_MASKS.all (fun m =>
    -- (i) the EMITTED fold IS `cipR` over the sub-list the mask KEEPS.
    ((cipAtMask m : ZMod pN) == cipRKept m)
    -- (ii) …and the single fused fold IS upstream's two combined folds.
    && ((cipAtMask m : ZMod pN) == cipFusedAt m)
    -- (iii) bending slot 0's carried challenges moves `cip` EXACTLY when the mask KEEPS slot 0 —
    --       so the pin is the mask refusing the term, not the bend failing to reach the ladder.
    && (((dfBent0 m).ca.getLastD 0 != cipAtMask m) == (m.getD 0 0 == 1))
    -- (iv) ⚑ THE FINDING. It is `cipR` over the full 47 EXACTLY when the mask drops nothing, so at
    --      EVERY dropping mask the value this rung emits is NOT the value it emitted before.
    && (((cipAtMask m : ZMod pN) == cipRFull) == (dropOf m == 0))
    -- (v) …and never the "zero the entry" reading, wherever the two can differ at all.
    && (dropOf m == 0 || ((cipAtMask m : ZMod pN) != cipRZeroed m))
    -- (vi) …and no two legal masks give the same circuit output, so the mask is not a parameter the
    --      value quietly ignores.
    && LEGAL_MASKS.all (fun m' => (m == m') || (cipAtMask m != cipAtMask m')))

def cipRowVars : List PVar :=
  (cipRows shapeSmoke true).flatMap (fun r => r.perm.filterMap id)

/-- ⚑ **∀-GAIN over the MASKED SLOTS.** `cipRows` reads each mask bit exactly once — stated for
every `j < N_CIP_MASKED` rather than as one transcribed line per slot, so a slot the emitter forgets
to mux cannot pass by being absent from the battery. -/
def cipReadsEachMaskBitOnce : Bool :=
  (List.range N_CIP_MASKED).all (fun j => cipRowVars.countP (· == vMask shapeSmoke j) == 1)

-- ── the values §15 pins ────────────────────────────────────────
def posAt (k : Rung) : List (PVar × Cell) :=
  circuitPositions (rungPub shapeSmoke k) (stepGates (rungRows tS k true))

-- ── the values §16 pins ────────────────────────────────────────
def finS : FinData := tS.fin

def finVal (i : Nat) : Nat := finS.vals.getD i 0

def zetaLS : Nat := liftOf shapeSmoke tS.sp shapeSmoke.zetaChal

/-- ⚑ `r` is §8g's DEFERRED challenge — `to_field_checked` of the fr-sponge's SECOND squeeze
(`step_verifier.ml:1008,1013`), not a transcript challenge. -/
def rLS : Nat := rFoldS

/-- The lifted bulletproof challenges, in `bEval`'s own list order (factor `k` carries the exponent
`2^{bRounds−1−k}`). -/
def usS : List (ZMod pN) :=
  (List.range shapeSmoke.bRounds).map (fun k =>
    ((liftOf shapeSmoke tS.sp (shapeSmoke.uChal k) : Nat) : ZMod pN))

/-- Re-run R8's program with ONE statement word bent and the `Field.equal` witnesses set the way an
HONEST prover would then have to set them (`bit = 0`, `inv = d⁻¹`), so the control is about the
CHECK and not about a witness nobody could produce. Returns the `out` slot — the value the last row
asserts equals 1. -/
def finOutBent (which : Nat) (sv : Nat) : Nat :=
  let s := shapeSmoke
  let d := tS.sp
  let sqv := frSqueezeVal tS.segB tS.specB
  let base := finInputEnv s d tS.ft tS.df tS.segB tS.specB rFoldS tS.bp.ver
  -- bend the `which`-th statement word (0 = cip, 1 = b, 2 = perm, 3 = xi)
  let tgt : PVar :=
    match which with
    | 0 => vCipShift s | 1 => vBShift s | 2 => vPermShift s | _ => vXiStmt s
  -- ⚑ `should_verify` is bent through the ENVIRONMENT, because since §8f it is a STATEMENT WORD
  -- and not a `FinCfg` witness: selecting the dummy branch is a public claim, not a private one.
  let env := base.map (fun p =>
    if p.1 == tgt then (p.1, p.2 + 1)
    else if p.1 == vShouldVerify s then (p.1, (sv : Int)) else p)
  -- the honest witnesses for the bent instance: the bent leg's difference is `±2` (an unshift
  -- doubles) or `−1` (the raw ξ word), so `bit = 0` and `inv = d⁻¹` there, `bit = 1` elsewhere.
  let dv : Nat := if which == 3 then pN - 1 else 2
  let inv := Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv dv
  let idx : Nat := match which with | 0 => 2 | 1 => 1 | 2 => 3 | _ => 0
  let C : FinCfg :=
    { finCfgOf s (sqv / 2 ^ 128) with
      eqInv := (List.replicate 4 0).set idx inv
      eqBit := (List.replicate 4 1).set idx 0 }
  let p := finProgOf (finWireOf s tS.ft) C
  (aEval (envLookupAt (envIndex env)) p.prog).getD p.slots.out 0

-- ── the values §17 pins ────────────────────────────────────────
/-- `z₁` and `z₂`, the opening's response scalars. ⚑ Since §19 these are the assembly's OWN witness
cells (`bpZ1`/`bpZ2`) and not exhibit-only fixtures — deterministic BECAUSE they are witnesses with
no upstream binder, which is the point of the exhibit. -/
def BP_Z1 : Nat := BP_Z1_VAL

def BP_Z2 : Nat := BP_Z2_VAL

/-- `lhs = Scalar_challenge.endo q c + delta` — R4's `qLhsOut`, read off the assembly. -/
def bpLhsOf (t : StepData) : Nat × Nat := (t.ipa.lhsAdd.getD 4 0, t.ipa.lhsAdd.getD 5 0)

/-- `u = group_map (squeeze)` on the assembly's own transcript. ⚑ **CORRECTED 2026-08-03**: this read
`chalOf` — the LOW 128 bits — where `step_verifier.ml:264` is `Sponge.squeeze_field`, the FULL
element. §19 emits `group_map` over `uSqueezeVar`, and this is the same value the emitted rows carry
(pinned as an equality against the emitted cell, not restated). -/
def bpUOf (t : StepData) : Nat × Nat := gmapFp (uSqueezeVal t.sh t.sp)

/-- `advice.b` — R8's statement word. -/
def bpBOf (t : StepData) : Nat := t.fin.bShift

/-- The `G` an honest prover hands `verify_one`: the one that makes the opening close. -/
def bpGHonest : Nat × Nat × Nat :=
  bpSolveG (bpUOf tS) GENERATORS_H (bpLhsOf tS) (bpBOf tS) BP_Z1 BP_Z2

def bpGResolved : Nat × Nat × Nat :=
  bpSolveG (bpUOf tSwapAbs) GENERATORS_H (bpLhsOf tSwapAbs) (bpBOf tSwapAbs) BP_Z1 BP_Z2

/-- Jacobian → affine. ⚑ Since §19 this is Core's `jAffOf` — the assembly's OWN conversion, the one
`solveG` runs, so the exhibit and the emitted witness cannot drift into two spellings. -/
def jAff (P : Nat × Nat × Nat) : Nat × Nat := jAffOf P

/-- The honest `G` and the re-solved one, as curve points segment D can absorb. -/
def bpGHonestA : Nat × Nat := jAff bpGHonest

def bpGResolvedA : Nat × Nat := jAff bpGResolved

-- ── the values §18 pins ────────────────────────────────────────
/-- ⚑ Segment C's spec with each slot's contents supplied, so the CHAIN can be evaluated at step
`N`'s outputs rather than at this instance's own fixtures. Structurally identical to `hmSpec` — the
variables, the length, the mask and the interleave are the same objects, only the VALUES differ, and
the first `#guard` below pins that by comparing the two word lists. -/
def hmChainSpec (s : StepShape) (app : Nat → Nat)
    (G0 : Nat × Nat) (ch0 : Nat → Nat) (G1 : Nat × Nat) (ch1 : Nat → Nat) : SegSpec :=
  { ws := (List.range N_IDX_WORDS).map (fun i => (idxVar s (i / 2) (i % 2), idxVal (i / 2) (i % 2)))
      ++ (List.range N_HM_APP).map (fun i => (vHm s i, app i))
      ++ [ (sgOldVar s 0 0, G0.1), (sgOldVar s 0 1, G0.2) ]
      ++ (List.range s.bRounds).map (fun k => (vPrevChal s k, ch0 k))
      ++ [ (sgOldVar s 1 0, G1.1), (sgOldVar s 1 1, G1.2) ]
      ++ (List.range s.bRounds).map (fun k => (vPrevChal s (s.bRounds + k), ch1 k))
  , squeezes := 1, masked := true, maskFrom := N_HM_FIX / 2, keep := hmKeepAt s MASK_BITS }

/-- Segment C's squeeze on chained inputs — step `N+1`'s reconstruction of step `N`'s statement. -/
def hmChainDigest (s : StepShape) (app : Nat → Nat)
    (G0 : Nat × Nat) (ch0 : Nat → Nat) (G1 : Nat × Nat) (ch1 : Nat → Nat) : Nat :=
  ((runSeg (hmChainSpec s app G0 ch0 G1 ch1)).states.getLastD []).getD 0 0

/-- Step `N`'s `old_bulletproof_challenges` — `finalize_other_proof`'s RETURNED vector
(`step_main.ml:563-565`), which in this assembly is `vLift (uChal k)`. These are the words segment D
absorbs, and therefore the words step `N+1` must carry as `prev_challenges`. -/
def chainChals (s : StepShape) (d : SpongeData) (k : Nat) : Nat := liftOf s d (s.uChal k)

/-- Segment C's own slot-0 contents, unchanged — the `Wrap_hack` dummy slot. -/
def chainSlot0 (_s : StepShape) (v : IpaData) : (Nat × Nat) × (Nat → Nat) :=
  ((sgOldVal v 0 0, sgOldVal v 0 1), fun k => prevChalVal k)

/-- ⚑ The chained reconstruction under a SUPPLIED mask, so the `Wrap_hack`-dummy control in (e) can
be run at `[1,1]` — the `N2` instance's own legal prefix mask — without restating the schedule. -/
def hmChainDigestMask (s : StepShape) (ms : List Nat) (app : Nat → Nat)
    (G0 : Nat × Nat) (ch0 : Nat → Nat) (G1 : Nat × Nat) (ch1 : Nat → Nat) : Nat :=
  ((runSeg { hmChainSpec s app G0 ch0 G1 ch1 with keep := hmKeepAt s ms }).states.getLastD []).getD 0 0

/-- Step `N`'s public word 7 as a function of the commitment in segment D's slot — §17(d)'s object,
named here so the two sides of the tie are two named quantities. -/
def wordSeven (t : StepData) (G : Nat × Nat) : Nat := hmOutDigestOf shapeSmoke t.sp G

def bpG11 : Nat × Nat :=
  jAff (bpSolveG (bpUOf tSwapAbs) GENERATORS_H (bpLhsOf tSwapAbs) (bpBOf tSwapAbs) 1 1)

/-- `f_c` over the KEPT slot's carried challenges, in `bEvalSq`'s own list order. -/
def prevUs : List (ZMod pN) :=
  (List.range shapeSmoke.bRounds).map (fun k =>
    ((prevChalVal (shapeSmoke.bRounds + k) : Nat) : ZMod pN))

/-- …and over the OTHER slot's — the `Wrap_hack` dummy. -/
def prevUs0 : List (ZMod pN) :=
  (List.range shapeSmoke.bRounds).map (fun k => ((prevChalVal k : Nat) : ZMod pN))

/-- ζω, as a value: `Field.mul domain#generator plonk.zeta` (`step_verifier.ml:934`). -/
def zetawLS : Nat := fMul FT_OMEGA zetaLS

def ecRowVars : List PVar :=
  (sgEvalRows shapeSmoke FT_OMEGA true).flatMap (fun r => r.perm.filterMap id)

def defRowVars : List PVar :=
  (deferredRows shapeSmoke true).flatMap (fun r => r.perm.filterMap id)

def dfBent : DefData :=
  runDef shapeSmoke tS.sp ftS.out xiFoldS rFoldS FT_OMEGA
    (fun i => if i == shapeSmoke.bRounds then fAdd (prevChalVal i) 1 else prevChalVal i)
    MASK_BITS

def dfConflated : DefData :=
  runDef shapeSmoke tS.sp ftS.out xiFoldS rFoldS FT_OMEGA
    (fun i => chainChals shapeSmoke tS.sp (i % shapeSmoke.bRounds)) MASK_BITS

-- ── §21 — `multiscale_known`'s SCALARS ARE THE WRAP STATEMENT'S WORDS ──────────────────────────

/-- The transcript's challenge accessor, and the same with challenge `c` bent by one. Bending the
ACCESSOR rather than the sponge is what isolates the wiring: it asks which challenges the scalar
vector READS, not what a different transcript would produce. -/
def chalS : Nat → Nat := chalOf shapeSmoke tS.sp
/-- …with challenge `c` bent by one. -/
def chalSBent (c : Nat) : Nat → Nat := fun k => if k == c then chalS k + 1 else chalS k

/-- ⚑ §22 — `sponge_digest_before_evaluations`, the value word 10 now CARRIES: lane 1 of the state
ζ's squeeze produced, read off the smoke assembly's own transcript. -/
def sdS : Nat := digestBeforeEvalsVal shapeSmoke tS.sp

/-- ⚑ The HONEST scalar vector — the packed Wrap statement, at the smoke assembly's own data. -/
def scalHon : Nat → Nat := msmScalars shapeSmoke chalS sdS tS.ft tS.fin tS.segC
/-- …with statement word `w` bent by one, and NOTHING else touched. -/
def scalBentW (w : Nat) : Nat → Nat := fun i => if i == w then scalHon i + 1 else scalHon i
/-- …and the honest vector recomputed under a bent transcript challenge. -/
def scalHonBentChal (c : Nat) : Nat → Nat :=
  msmScalars shapeSmoke (chalSBent c) sdS tS.ft tS.fin tS.segC

/-- ⚠ **THE RETIRED WIRING** — `vSN i (msmChunksAt i) = vN (i % chals) emsRows`, i.e. term `i`'s
scalar is transcript challenge `i % chals`. Kept HERE and nowhere else, because it is the thing §21's
control refutes. -/
def scalOld : Nat → Nat := fun i => chalS (i % shapeSmoke.chals)
/-- …and the retired wiring under a bent transcript challenge. -/
def scalOldBentChal (c : Nat) : Nat → Nat := fun i => chalSBent c (i % shapeSmoke.chals)

/-- The x_hat MSM run at an arbitrary scalar vector, on the honest bases. -/
def msmAt (f : Nat → Nat) : MsmData := runMsm shapeSmoke (stepBases shapeSmoke) f
/-- …and its OUTPUT, `multiscale_known`'s sum — the point that becomes `x_hat`. -/
def xhatAt (f : Nat → Nat) : Nat × Nat := (msmAt f).sums.getLastD (0, 0)

/-- ⚑ The COMMITTED shape's scalar vector as a function of the challenge accessor and, since §22, of
`sponge_digest_before_evaluations` (word 10) — so the seed can be bent independently of every
challenge. The three data arguments are `default` deliberately: the claim under test is which
arguments the vector DEPENDS ON, and a real `FtData`/`FinData`/`SegData` at `shapeStep` would cost
the whole 10k-row assembly to say the same thing.

`SD_PROBE` is a distinctive constant: it must not collide with a `chalInj` value, or "word 10 moved"
and "some challenge word moved" would be indistinguishable in the list comparison. -/
def SD_PROBE : Nat := 424242
def stepScalSd (ch : Nat → Nat) (sd : Nat) : List Nat :=
  (List.range shapeStep.msmTerms).map
    (msmScalars shapeStep ch sd (default : FtData) (default : FinData) (default : SegData))
def stepScal (ch : Nat → Nat) : List Nat := stepScalSd ch SD_PROBE
/-- A challenge accessor that is injective on `0..chals`, and the same bent at `c`. -/
def chalInj : Nat → Nat := fun c => 1000 + c
def chalInjBent (c : Nat) : Nat → Nat := fun k => if k == c then 1001 + k else 1000 + k

/-- R6's compiled ft program at the COMMITTED shape, built here so §21 can pin `FT_SLOT_ZETAN`
against the program's own slot without running `mkStep shapeStep`. -/
def ftProgStep : FtProg := ftProgOf (ftWireOf shapeStep) (ftCfgRaw 1)

/-- ⚑ **THE COMMITTED SHAPE'S OWN ASSEMBLY.** Every other fixture here is the smoke one, because the
pins are about SHAPE and smoke is cheap. This exists for exactly one claim §21 cannot make at smoke:
that all FORTY packed statement words fit the ladders §20 sized for them. Smoke reaches three. -/
def tStep : StepData := mkStep shapeStep

/-- …and the forty scalars it hands `multiscale_known`. -/
def stepScalHon : Nat → Nat :=
  msmScalars shapeStep (chalOf shapeStep tStep.sp)
    (digestBeforeEvalsVal shapeStep tStep.sp) tStep.ft tStep.fin tStep.segC

-- ── §22 — THE fr-SPONGE's SEED ABSORB ──────────────────────────────────────────────────────────

/-! ⚑ Everything below is stated on the SMOKE assembly's own segment B, re-run under one bent word.
`runSeg` is the emitter's own evaluator, so a "the squeeze moved" claim is about the emitted
trajectory and not about a parallel model of it. -/

/-- Segment B with the word at position `k` bent by one — `bendW` is §12k's own transform. -/
def segBBent (k : Nat) : SegData := runSeg { tS.specB with ws := bendW tS.specB.ws k }

/-- …and the two squeezes off it. `tS.specB` supplies `nb`/`squeezes`, which the bend does not
move, so `frSqueezeVal` reads the same block of a different trajectory. -/
def frSq1Bent (k : Nat) : Nat := frSqueezeVal (segBBent k) tS.specB
def frSq2Bent (k : Nat) : Nat := frSqueeze2Val (segBBent k) tS.specB

/-- ⚠ **THE RETIRED WIRING** — segment B WITHOUT the seed, i.e. `frSpec` as it stood before
2026-08-03: the fr-sponge starting at `challenge_digest`. Kept HERE and nowhere else, because it is
the thing §22's control refutes. Its `ws` is `tS.specB`'s with the first word dropped, so the two
differ in exactly the seed and in nothing else. -/
def specBNoSeed : SegSpec := { tS.specB with ws := tS.specB.ws.drop 1 }
def segBNoSeed : SegData := runSeg specBNoSeed
/-- …and the retired segment under a bent SEED. The seed is not in its word list at all, so this is
the leg that says the instrument would have been blind: the same bend, and nothing to bend. -/
def segBNoSeedBentSeed : SegData :=
  runSeg { specBNoSeed with ws := bendW tS.specB.ws 0 |>.drop 1 }

/-- ⚑ The honest `xi_correct` comparand — `lowest_128_bits` of the fr-sponge's first squeeze, which
R8 compares against statement word 9. -/
def xiActualOf (sq : Nat) : Nat := sq % 2 ^ 128

/-- ⚑⚑ **R8 AT A BENT SEED.** The prover moves Wrap statement word 10 and NOTHING else: the fr-sponge
is re-run with the bent seed, and every other input — `vXiStmt` above all — stays at the value the
honest assembly holds. The `Field.equal` witnesses are set the way an honest prover would have to set
them for the bent instance (`bit = 0`, `inv = d⁻¹` on the ξ leg), so what this measures is R8's own
gadget refusing, not a witness nobody could produce. Returns the `out` slot — the value R8's last row
asserts equals 1. -/
def finOutAtBentSeed : Nat :=
  let s := shapeSmoke
  let sqBent := frSq1Bent 0
  -- the honest env, with ONLY the fr-sponge's first squeeze moved: `vXiStmt` stays honest.
  let env := (finInputEnv s tS.sp tS.ft tS.df tS.segB tS.specB rFoldS tS.bp.ver).map
    (fun p => if p.1 == frSqueezeVar s then (p.1, (sqBent : Int)) else p)
  let d := fSub (xiActualOf sqBent) tS.fin.xiStmt
  let C : FinCfg :=
    { finCfgOf s (sqBent / 2 ^ 128) with
      eqInv := (List.replicate 4 0).set 0 (Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv d)
      eqBit := (List.replicate 4 1).set 0 0 }
  let p := finProgOf (finWireOf s tS.ft) C
  (aEval (envLookupAt (envIndex env)) p.prog).getD p.slots.out 0

/-- ⚑ The transcript with the word absorbed at ordinal `a`, lane `j`, bent by one — `runSpongeAt` is
the assembly's OWN generator, so this is the emitted transcript at one changed input. -/
def spWordBent (a j : Nat) (w : Nat) : SpongeData :=
  runSpongeAt shapeSmoke (stepBases shapeSmoke) indexDigest (cipWordOf tS) a j w

/-- ⚑ The LAST `t_comm` chunk — absorbed at `:567`, i.e. strictly BEFORE ζ's squeeze at `:568`, so
the digest lane is downstream of it. §12e′ already grinds this same word. -/
def sdPreZetaBent : Nat :=
  digestBeforeEvalsVal shapeSmoke (spWordBent tcOrd 1 (fAdd tcHon 1))

/-- ⚑ …and the `combined_inner_product` word, absorbed at `:256` — strictly AFTER ζ's squeeze, so
the digest lane is UPSTREAM of it and must not move. This is the same object `spCip` bends. -/
def sdPostZetaBent : Nat := digestBeforeEvalsVal shapeSmoke spCip

end Dregg2.Circuit.Emit.KimchiStepMain
