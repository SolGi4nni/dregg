/-
`KimchiStepMain` pins — §15.

The values these are stated about are in `…Fixture`; the emission is in `…Core`.
-/
import Dregg2.Circuit.Emit.KimchiStepMainFixture

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

/-! ## §15 — the LADDER is monotone, REACHED BY THE EMITTER, and each rung really adds its
sub-circuit.

⚑ THE REACHED-BY-THE-EMITTER PINS ARE THE FIRST BLOCK, and they exist because of a measured defect:
`cipRows` once lived in a function `rungRows` never called, so `r5_full` was proved seven times
without the `combined_inner_product` chain its own commit subject named, and `vCa cipEvals` reached
the public tie as a FREE variable — while every σ probe, every control and every public-input leg
passed. A length identity per rung, stated as the SUM OF ITS OWN SUB-LISTS, is what turns that from
a silence into a red; `stepRows == rungRows .finalize` closes the same hole on the other emitter. -/

-- Each rung IS the rung below plus exactly its own sub-circuit's rows.
#guard (rungRows tS .challenges true).length
        == (rungRows tS .transcript true).length + (endoConstRow shapeSmoke).length
           + ((List.range shapeSmoke.chals).flatMap (challengeRows shapeSmoke tS.sp true)).length
#guard (rungRows tS .msm true).length
        == (rungRows tS .challenges true).length + (msmRows shapeSmoke tS.msm true).length
           + (ftcRows shapeSmoke tS.ftw tS.ftc true).length
#guard (rungRows tS .ipa true).length
        == (rungRows tS .msm true).length + (ipaRows shapeSmoke tS.ipa true).length
#guard (rungRows tS .full true).length
        == (rungRows tS .ipa true).length + (deferredRows shapeSmoke true).length
           + (sgEvalRows shapeSmoke FT_OMEGA true).length
           + (branchRows shapeSmoke true).length + (xiDefRows shapeSmoke tS.defc true).length
           + (cipRows shapeSmoke true).length + (closingRows shapeSmoke).length
#guard (rungRows tS .ftEval0 true).length
        == (rungRows tS .full true).length + (ftRows shapeSmoke tS.ft true).length
#guard (rungRows tS .absorb true).length
        == (rungRows tS .ftEval0 true).length + (absRows tS true).length
#guard (rungRows tS .finalize true).length
        == (rungRows tS .absorb true).length + (finRows shapeSmoke tS.ft tS.fin true).length
-- …and the OTHER emitter (`stepRows`, the schedule) is the top rung, row for row.
#guard (stepRows tS true).map (fun r => r.kind) == (rungRows tS .finalize true).map (fun r => r.kind)
#guard (stepRows tS true).length == (rungRows tS .finalize true).length
-- …and each sub-list is NON-EMPTY, so "the sum matches" cannot be satisfied by a vanished rung.
#guard (cipRows shapeSmoke true).length > 0 && (deferredRows shapeSmoke true).length > 0
/-- ⚑ `cipRows`' own length as a CLOSED FORM of what it emits, so the mux cannot quietly lose a
masked step: the `acc₀ = 0` pin, one A-row per column, then the B-fold packed two halves to a row at
`2` halves per `Some` step and `5` per `Maybe` one, then two probes and the `cip` bit's booleanity
row with its probe. Gains a NAME, not a ∀ — `shapeSmoke` is the one assembly this file measures. -/
theorem cipRows_length_closed_form :
    (cipRows shapeSmoke true).length
      = 1 + shapeSmoke.cipEvals
        + (2 * (shapeSmoke.cipEvals - N_CIP_MASKED) + 5 * N_CIP_MASKED + 1) / 2
        + 4 := by native_decide
#assert_compiled cipRows_length_closed_form

/-- …and the mux is what makes it longer than the unconditional fold would be. Stated as the DELTA
against the shape this rung replaced — `1 + cipEvals` A-rows, `cipEvals` unconditional B-rows and
the three-row trailer — because four rows is the whole cost of this rung. -/
theorem cipRows_length_is_the_unmuxed_shape_plus_four :
    (cipRows shapeSmoke true).length
      = (1 + shapeSmoke.cipEvals + shapeSmoke.cipEvals + 3) + 4 := by native_decide
#assert_compiled cipRows_length_is_the_unmuxed_shape_plus_four
-- ⚑ …and §8i's own sub-list, which is the rung this file last added. Its length is stated as the
-- CLOSED FORM of what it emits — the `zetaw` row, ζω's `bRounds − 1` squaring halves packed two to
-- a row, `N_EC · bRounds` fused factor rows and `N_EC` probes — so a ladder that quietly loses a
-- slot or a point reds here rather than shrinking silently.
#guard (sgEvalRows shapeSmoke FT_OMEGA true).length
        == 1 + (shapeSmoke.bRounds - 1 + 1) / 2 + N_EC * shapeSmoke.bRounds + N_EC
#guard (ftRows shapeSmoke tS.ft true).length > 0 && (absRows tS true).length > 0
#guard (finRows shapeSmoke tS.ft tS.fin true).length > 0 && (endoConstRow shapeSmoke).length > 0
#guard (xiDefRows shapeSmoke tS.defc true).length > 0
        && (rDefRows shapeSmoke tS.defc true).length > 0
-- ⚑ …and R7's own sub-list really is the FOUR segments, §3c's index pins and digest permutation,
-- and §8g's `r` chain. Stated as an equality over every summand, so a dropped sub-list reds here.
#guard (absRows tS true).length
        == (segRows (baseSegA shapeSmoke) tS.specA tS.segA true).length
           + (segRows (baseSegB shapeSmoke) tS.specB tS.segB true).length
           + (idxConstRows shapeSmoke).length
           + (segRows (baseSegC shapeSmoke) tS.specC tS.segC true).length
           + (segRows (baseSegD shapeSmoke) tS.specD tS.segD true).length
           + (idxDigestRows shapeSmoke true).length
           + (rDefRows shapeSmoke tS.defc true).length
-- ⚑ …and segment D is NON-EMPTY and is exactly `blocks` permutations' worth of rows with NO init
-- pin row, which is what `Sponge.copy` means here: `nbD` absorb blocks (13 rows each, the last one
-- +1 for its probe) and one squeeze block (12 + probe).
#guard (segRows (baseSegD shapeSmoke) tS.specD tS.segD true).length
        == 13 * nbD shapeSmoke + 1 + 13
#guard tS.specD.copyFrom.isSome && tS.specA.copyFrom.isNone && tS.specC.copyFrom.isNone
-- …and neither §3c sub-list is empty: 12 rows of permutation + a probe, and one `Generic` pin per
-- index commitment this shape must hold itself.
#guard (idxDigestRows shapeSmoke true).length == 13
#guard (idxConstRows shapeSmoke).length == (idxOwn shapeSmoke).length

-- ⚑ **WHICH RUNG BINDS WHICH MULTIPLIER** (#10's honest residue, machine-checked). ξ's chain rides
-- with R5 because its source is a STATEMENT word, so `vDLift 0` has a computing row from `r5_full`
-- up. `r`'s source is the fr-sponge's second squeeze, an R7 variable, so `vDLift 1` has NO computing
-- row below `r7_absorption` and has one at and above it. Stated as a pin so the ladder position is
-- a fact rather than a sentence in a header.
-- ⚑ THE SEGMENT-C DIGEST's LADDER POSITION, stated the same way. It is a public word from `r5_full`
-- up, but the rows that COMPUTE it are R7's, so below `r7_absorption` its class is the closing tie
-- and nothing else — a free witness, exactly as `vDLift 1` is. Equalities, not floors.
#guard (classCells (posAt .full) (hmDigestVar shapeSmoke)).length == 1
#guard (classCells (posAt .ftEval0) (hmDigestVar shapeSmoke)).length == 1
#guard (classCells (posAt .absorb) (hmDigestVar shapeSmoke)).length == 3
#guard (classCells (posAt .finalize) (hmDigestVar shapeSmoke)).length == 3
-- ⚑ …and the OUTER digest reads exactly the same way, so segment D inherits the same caveat and
-- gets it said rather than assumed.
#guard (classCells (posAt .full) (hmOutDigestVar shapeSmoke)).length == 1
#guard (classCells (posAt .ftEval0) (hmOutDigestVar shapeSmoke)).length == 1
#guard (classCells (posAt .absorb) (hmOutDigestVar shapeSmoke)).length == 3
#guard (classCells (posAt .finalize) (hmOutDigestVar shapeSmoke)).length == 3
-- ⚑ **`G`'s LADDER POSITION, and it is the honest statement of what segment D bought.** From
-- `r4_ipa` (where `assert_on_curve` lands) to `r6_ft_eval0`, `G`'s whole class is those three
-- halves — a witness the circuit checks is on the curve and reads NOWHERE ELSE. `r7_absorption` is
-- the rung that adds the absorption, and it adds exactly ONE cell per coordinate. Below `r4` it has
-- no cell at all, which is what "zero occurrences" meant before this rung.
#guard (classCells (posAt .msm) (vGx shapeSmoke)).length == 0
#guard (classCells (posAt .ipa) (vGx shapeSmoke)).length == 3
#guard (classCells (posAt .ftEval0) (vGx shapeSmoke)).length == 3
#guard (classCells (posAt .absorb) (vGx shapeSmoke)).length == 4
#guard (classCells (posAt .finalize) (vGx shapeSmoke)).length == 4
-- ⚠ ⚑ **AND `index_digest` HAS THE SAME LADDER POSITION, so say it rather than let the retirement
-- read as unconditional.** §3c's derivation lives in R7 — the permutation is squeezed off segment
-- C's own state, and segment C is an R7 sub-circuit — while R1 ABSORBS the result at block 0. So
-- from `r1_transcript` to `r6_ft_eval0` `vIdxD 0` is a free witness the transcript eats (class = the
-- absorb row alone), and it is DERIVED at `r7_absorption` and `r8_finalize` (the permutation's
-- closing `Zero`, its σ probe, the absorb row). The reportable object is the full assembly; the
-- lower rungs are sub-circuits and this is where that costs something.
#guard (classCells (posAt .transcript) (vIdxD shapeSmoke 0)).length == 1
#guard (classCells (posAt .ftEval0) (vIdxD shapeSmoke 0)).length == 1
#guard (classCells (posAt .absorb) (vIdxD shapeSmoke 0)).length == 3
#guard (classCells (posAt .finalize) (vIdxD shapeSmoke 0)).length == 3
-- …and the plonk-index pin rows are R7's too, so the same reading applies to the 56 absorbed words.
#guard (classCells (posAt .ftEval0) (vIdxX shapeSmoke 27)).length == 0
#guard (classCells (posAt .absorb) (vIdxX shapeSmoke 27)).length == 2

-- ⚑ **§6b's LADDER POSITION, and it is the honest half of the retirement.** `ft_comm`'s scalars are
-- R6's OWN cells, and R6's rows arrive at `r6_ft_eval0`. So from `r3_msm` to `r5_full` the `perm`
-- and `ζ^n` cells are FREE WITNESSES — read by §6b's `Shifted_value.Type2` split row and by NOTHING
-- else — and they are DERIVED at `r6_ft_eval0` and above. Stated the way `index_digest`'s and
-- `vDLift 1`'s are, because the reportable object is the full assembly and the lower rungs are
-- sub-circuits. Equalities, not floors.
#guard (classCells (posAt .msm) tS.ftw.permV).length == 1
#guard (classCells (posAt .ipa) tS.ftw.permV).length == 1
#guard (classCells (posAt .ftEval0) tS.ftw.permV).length == 4
#guard (classCells (posAt .msm) tS.ftw.zetaV).length == 1
#guard (classCells (posAt .ipa) tS.ftw.zetaV).length == 1
#guard (classCells (posAt .ftEval0) tS.ftw.zetaV).length == 3
-- …and `sigma_comm_last`'s `Inner_curve.constant` pin is R7's (§3c), so term 0's BASE reads the same
-- way: the ladder, the doubling and the odd-branch add at `r3_msm`, plus the pin and segment C's
-- absorb from `r7_absorption`.
#guard (classCells (posAt .msm) (vIdxX shapeSmoke 6)).length == FTC_CHUNKS + 3
#guard (classCells (posAt .absorb) (vIdxX shapeSmoke 6)).length == FTC_CHUNKS + 5
-- ⚑ …whereas `t_comm`'s own words are ABSORBED at `r1_transcript` and CONSUMED from `r3_msm` up —
-- no ladder position at all, which is what makes the retirement unconditional for them.
#guard (classCells (posAt .transcript) (vTcX shapeSmoke 0)).length == 1
#guard (classCells (posAt .msm) (vTcX shapeSmoke 0)).length == 2
#guard (classCells (posAt .ipa) (vTcX shapeSmoke 0)).length == 5

-- ξ's class is COMPLETE at `r5_full`: nothing above r5 adds a cell to it, because its chain is
-- already there. (A floor `≥ 2` would pass here even with the chain deleted — the fold's own reads
-- alone give 47 — so this is stated as an EQUALITY against the top rung.)
#guard (classCells (posAt .full) (vDLift shapeSmoke 0)).length
        == (classCells (posAt .finalize) (vDLift shapeSmoke 0)).length
#guard (classCells (posAt .full) (vDLift shapeSmoke 0)).length == shapeSmoke.cipEvals + 2
-- r's is NOT: below the fr-sponge it is exactly the fold's `cipEvals` reads and NO defining row;
-- `r7_absorption` is the rung that adds the chain's lift row and its probe.
#guard (classCells (posAt .full) (vDLift shapeSmoke 1)).length == shapeSmoke.cipEvals
#guard (classCells (posAt .ftEval0) (vDLift shapeSmoke 1)).length == shapeSmoke.cipEvals
#guard (classCells (posAt .absorb) (vDLift shapeSmoke 1)).length == shapeSmoke.cipEvals + 2
#guard (classCells (posAt .finalize) (vDLift shapeSmoke 1)).length == shapeSmoke.cipEvals + 3
-- …and the ξ chain's `EndoMulScalar` rows are in r5 while the r chain's are not.
#guard ((rungRows tS .full true).filter (fun r => r.kind == KGateType.endoMulScalar)).length
        == (2 * shapeSmoke.chals + 1) * shapeSmoke.emsRows
#guard ((rungRows tS .ftEval0 true).filter (fun r => r.kind == KGateType.endoMulScalar)).length
        == (2 * shapeSmoke.chals + 1) * shapeSmoke.emsRows
-- …and R7 adds TWO: `r_actual`'s own chain and the `assert_128_bits` of its high part.
#guard ((rungRows tS .absorb true).filter (fun r => r.kind == KGateType.endoMulScalar)).length
        == (2 * shapeSmoke.chals + 3) * shapeSmoke.emsRows
-- ⚑ …and R8 adds TWO MORE — the THIRD `lowest_128_bits`, `xi_actual`'s, both parts (§12c′). This is
-- the pin that would have caught the hole: before it landed, R8's EndoMulScalar delta was ZERO and
-- the finalize rung split a field element with nothing constraining either half.
#guard ((rungRows tS .finalize true).filter (fun r => r.kind == KGateType.endoMulScalar)).length
        == (2 * shapeSmoke.chals + 5) * shapeSmoke.emsRows

#guard (rungRows tS .full true).length < (rungRows tS .ftEval0 true).length
#guard (rungRows tS .ftEval0 true).length < (rungRows tS .absorb true).length
#guard (rungRows tS .absorb true).length < (rungRows tS .finalize true).length
-- R8 over R7 is scalar arithmetic + the boolean gadgets + the two `assert_128_bits` chains of its
-- own `lowest_128_bits` (§12c′) — so `Generic`/`Zero`/`EndoMulScalar` and NOT ONE CURVE GATE. It
-- was `Generic`/`Zero` only until the third high chain landed; that is a stated change, not drift.
#guard ((rungRows tS .finalize true).drop (rungRows tS .absorb true).length).all
        (fun r => r.kind == KGateType.generic || r.kind == KGateType.zero
                  || r.kind == KGateType.endoMulScalar)
#guard (List.range 4).all (fun i =>
  let k : KGateType := [KGateType.completeAdd, .varBaseMul, .endoMul, .poseidon].getD i .zero
  ((rungRows tS .finalize true).filter (fun r => r.kind == k)).length
    == ((rungRows tS .absorb true).filter (fun r => r.kind == k)).length)
-- R6 is `Generic`-only (it is scalar arithmetic; every other gate family is unchanged by it).
#guard ((rungRows tS .ftEval0 true).drop (rungRows tS .full true).length).all
        (fun r => r.kind == KGateType.generic || r.kind == KGateType.zero)
-- R7 adds `Poseidon` (11 rows per permutation, upstream's own run length) and — since §8g — exactly
-- ONE further `to_field_checked` chain, `r_actual`'s. No curve gate, no second chain.
#guard ((rungRows tS .absorb true).filter (fun r => r.kind == KGateType.poseidon)).length
        == 11 * (shapeSmoke.blocks + tS.specA.blocks + tS.specB.blocks + tS.specC.blocks
                 + tS.specD.blocks + 1)
#guard ((rungRows tS .full true).filter (fun r => r.kind == KGateType.poseidon)).length
        == 11 * shapeSmoke.blocks
#guard (List.range 4).all (fun i =>
  let k : KGateType := [KGateType.completeAdd, .varBaseMul, .endoMul, .zero].getD i .zero
  ((rungRows tS .absorb true).filter (fun r => r.kind == k)).length
    ≥ ((rungRows tS .ftEval0 true).filter (fun r => r.kind == k)).length)
#guard (List.range 3).all (fun i =>
  let k : KGateType := [KGateType.completeAdd, .varBaseMul, .endoMul].getD i .zero
  ((rungRows tS .absorb true).filter (fun r => r.kind == k)).length
    == ((rungRows tS .ftEval0 true).filter (fun r => r.kind == k)).length)
-- …and the compiled ft program is a real program, not a stub.
#guard ftS.fp.prog.size ≥ 900
#guard (aHalfSlots ftS.fp.prog).length ≥ 700

end Dregg2.Circuit.Emit.KimchiStepMain
