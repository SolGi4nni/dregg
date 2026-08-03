/-
`KimchiStepMain` pins — §12a §12b §12i.

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

-- ── §12a — ⚑ THE FOLD IS FED BY THE FR-SPONGE (simplification #10, retired) ────────────────────
-- The multipliers the C8 fold uses are §8g's DEFERRED challenges. Named once, so every pin below
-- reads the same two values the `Generic` halves of `cipRows` multiply by.

-- ⚑ **ξ IS `endoMap` OF R7's FIRST SQUEEZE, r IS `endoMap` OF ITS SECOND.** `xi_correct` binds the
-- statement's ξ word to the first squeeze (§16d) and §8g's chain 0 lifts THAT word, so the composite
-- the fold multiplies by is exactly this. Upstream's own two-step, `step_verifier.ml:1010-1013`.
#guard ((xiFoldS : Nat) : ZMod pN) == foldMulOf sq1S
#guard ((rFoldS : Nat) : ZMod pN) == foldMulOf sq2S
-- …the two squeezes are different field elements, so ξ ≠ r is a fact about the sponge and not luck.
#guard sq1S != sq2S && xiFoldS != rFoldS
-- …and the lift is not the identity (a degenerate endo would make the chain decoration).
#guard xiFoldS != tS.defc.pre.getD 0 0 && rFoldS != tS.defc.pre.getD 1 0

-- ⚑ THE ASSEMBLED `combined_inner_product` IS THE VERIFIER'S — **OVER THE SLOTS `combine` KEEPS.**
-- The Horner chain the `Generic` rows compute equals `KimchiVerify.cipR` applied to the SAME ξ, r
-- and evaluation columns — and `cipR` IS the shipped `combinedInnerProduct` (`KimchiVerify.cipR_eq`,
-- `rfl`, for every field; the CommRing mirror exists precisely so a `ZMod pN` instance can answer to
-- it). So the deferred rung answers to the READ-ONLY transcription of `verifier.rs`, not to its own
-- definition.
--
-- ⚠ ⚑ **THE `.drop 1` IS THE MUX, AND IT IS NOT COSMETIC.** Since 2026-08-02 `cipRows` honours
-- `branch_data.proofs_verified_mask` (`common.ml:270-271`), and `Prefix_mask.there N1 = [0,1]`
-- (`pickles_base/proofs_verified.ml:78-79`) DROPS slot 0. Because `mul_and_add`'s `else_` branch is
-- bare `acc`, a dropped slot consumes NO ξ power, so the masked fold is `cipR` over the KEPT
-- SUB-LIST — one shorter, with every surviving term one ξ power lower. The next pin is the same
-- statement as a refutation: `cipR` over the FULL 47 is a different field element.
#guard
  ((tS.df.ca.getLastD 0 : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf sq1S) (foldMulOf sq2S)
         (cipEzS.drop 1) (cipEwS.drop 1))
-- ⚑⚑ **AND THE UNMASKED FOLD — the object this rung emitted until 2026-08-02 — IS NOT IT.** This is
-- the measurement that `combine`'s mux moves the value AT THE DEPLOYED MASK, where "slot 0 is the
-- `Wrap_hack` dummy" would predict a no-op. It is not a no-op: the dummy's VALUE never mattered, the
-- ξ-power shift does.
#guard
  (((tS.df.ca.getLastD 0 : ZMod pN)
     == Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf sq1S) (foldMulOf sq2S) cipEzS cipEwS)
   == false)
-- …and it CAN go red: swapping ξ for r gives a different value (so the equality is discriminating,
-- not two names for zero).
#guard
  (((tS.df.ca.getLastD 0 : ZMod pN)
     == Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf sq2S) (foldMulOf sq2S)
          (cipEzS.drop 1) (cipEwS.drop 1)) == false)

-- ⚑⚑ **THE BITING RED CONTROL FOR #10: BENDING R7's SQUEEZE MOVES THE FOLD.** Before §8g the fold's
-- multipliers were R1 transcript challenges and this could not bite — the fr-sponge reached
-- `xi_correct` and nothing else, so a bent squeeze left `combined_inner_product` exactly where it
-- was. Now each squeeze is the SOURCE of a `to_field_checked` chain, and a one-unit bend in either
-- one moves the folded value.
#guard
  (((tS.df.ca.getLastD 0 : ZMod pN)
     == Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf (sq1S + 1)) (foldMulOf sq2S)
          (cipEzS.drop 1) (cipEwS.drop 1)) == false)
#guard
  (((tS.df.ca.getLastD 0 : ZMod pN)
     == Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf sq1S) (foldMulOf (sq2S + 1))
          (cipEzS.drop 1) (cipEwS.drop 1)) == false)
-- ⚑ …and the RETIRED reading — the last two R1 transcript challenges, which is what the fold
-- multiplied by until 2026-08-02 — is a DIFFERENT value. Derived, not fixed.
#guard
  (((tS.df.ca.getLastD 0 : ZMod pN)
     == Dregg2.Circuit.Emit.KimchiVerify.cipR
          ((liftOf shapeSmoke tS.sp (shapeSmoke.chals - 1) : ZMod pN))
          ((liftOf shapeSmoke tS.sp (shapeSmoke.chals - 2) : ZMod pN))
          (cipEzS.drop 1) (cipEwS.drop 1)) == false)
#guard xiFoldS != liftOf shapeSmoke tS.sp (shapeSmoke.chals - 1)
#guard rFoldS != liftOf shapeSmoke tS.sp (shapeSmoke.chals - 2)

-- ⚑ …and it is a WIRE, not just an arithmetic identity: the variable `cipRows` Horners over is in a
-- σ class that also holds §8g chain 0's lift row, and the statement ξ word's class reaches THREE
-- rows (the chain's `Field.Assert.equal`, the closing public tie, and R8's `xi_correct` gadget).
-- Exact counts, not floors: ξ's class is the `cipEvals` Horner reads + its own lift row + its probe;
-- r's is the `cipEvals` `r·evₖ(ζω)` reads + lift + probe + R8's `b_correct` read. A chain that
-- vanished, or a fold that stopped reading it, moves these.
#guard (classCells posS (vDLift shapeSmoke 0)).length == shapeSmoke.cipEvals + 2
#guard (classCells posS (vDLift shapeSmoke 1)).length == shapeSmoke.cipEvals + 3
-- …and the statement ξ word is read by EXACTLY three rows: §8g chain 0's `Field.Assert.equal`, the
-- closing public tie, and R8's `xi_correct` gadget. Drop any one and this is 2.
#guard (classCells posS (vXiStmt shapeSmoke)).length == 3
-- …the r chain's source really is segment B's SECOND squeeze cell (a state lane the sponge rows own).
#guard (classCells posS (frSqueeze2Var shapeSmoke)).length ≥ 2
#guard frSqueeze2Var shapeSmoke != frSqueezeVar shapeSmoke

-- ── §12b — ⚑ THE BASES ARE A REAL PROOF'S COMMITMENTS (simplification #3, retired) ─────────────
-- Until 2026-08-02 every curve base was a free witness variable holding a `basePts` fixture
-- (`[3]G, [4]G, …`), and R1 absorbed `2·absorbs` unrelated `msgVal` words. Two things were wrong at
-- once and this block is the pair of them: the bases are now **Mina devnet block 539508's own Wrap
-- commitments**, and each one is either PINNED (`Inner_curve.constant`) or ABSORBED (its two
-- variables ARE the transcript's absorbed words).

-- ⚑ THE VALUES ARE THE REAL BLOCK'S, at the committed shape, in the order the assembly consumes
-- them: 40 SRS Lagrange commitments, `combine_split_commitments`' 46, `bullet_reduce`'s 30.
#guard stepBases shapeStep == Dregg2.Bridge.MinaStepPrevCommitments.ALL_XY
#guard (stepBases shapeStep).length == shapeStep.msmTerms + shapeStep.ipaRounds
#guard shapeStep.msmTerms == Dregg2.Bridge.MinaStepPrevCommitments.LAGRANGE_XY.length
#guard shapeStep.ipaRounds == REAL_IPA_XY.length
-- …and the smoke shape's are a genuine PREFIX of the same list, not a second fixture family.
#guard stepBases shapeSmoke
        == (Dregg2.Bridge.MinaStepPrevCommitments.LAGRANGE_XY.take shapeSmoke.msmTerms
            ++ REAL_IPA_XY.take shapeSmoke.ipaRounds)

-- ⚑ THE PROVENANCE CENSUS IS EXERCISED — every round upstream absorbs really does get a transcript
-- block, at BOTH shapes. ⚑ Stated as a MULTISET equality against the `ipaAbsorbs` filter and as a
-- LIST **in**equality against it, because since the R1 interleaving `absRoundList` is upstream's
-- absorption ORDER (`w_comm` before `z_comm`, `t_comm` before the gammas) and the filter's ascending
-- order is NOT: a sponge is order-sensitive, so "same set" is the wrong pin on its own.
#guard (absRoundList shapeStep).mergeSort (· ≤ ·)
        == (List.range shapeStep.ipaRounds).filter ipaAbsorbs
#guard (absRoundList shapeSmoke).mergeSort (· ≤ ·)
        == (List.range shapeSmoke.ipaRounds).filter ipaAbsorbs
#guard absRoundList shapeStep != (List.range shapeStep.ipaRounds).filter ipaAbsorbs
-- …and the order really is `sg_old[1] · x_hat · w_comm ×15 · z_comm · gammas ×30`.
#guard (absRoundList shapeStep).take 3 == [0, 1, 10]
#guard (absRoundList shapeStep).getD 16 0 == 24 && (absRoundList shapeStep).getD 17 0 == 3
#guard (absRoundList shapeStep).drop 18 == List.range' (N_WDB - 1) 30
-- …and BOTH provenances really occur at the committed shape: 18 fold commitments + 30
-- `bullet_reduce` gammas absorbed, 28 verifier-key / computed constants.
#guard (absRoundList shapeStep).length == 48
#guard ((List.range shapeStep.ipaRounds).filter
          (fun r => ipaSrc shapeStep r == BaseSrc.const)).length == 27
-- ⚑ …and EXACTLY ONE round is COMPUTED — `ft_comm`, which was the 28th constant until §6b.
#guard ((List.range shapeStep.ipaRounds).filter
          (fun r => ipaSrc shapeStep r == BaseSrc.computed)) == [FTC_ROUND]
#guard (absRoundList shapeSmoke).length == 3
-- …and R3 carries NO absorbed base, which is `multiscale_known`'s own shape.
#guard (List.range shapeStep.msmTerms).all (fun i => msmSrc i == BaseSrc.const)
-- ⚠ ⚑ …and the COUNT OF STILL-FREE TRANSCRIPT WORDS, pinned so it cannot drift silently. A free word
-- is a `msgVal` fixture no row pins. Of `2·absorbs = 118` absorbed words **ONE** is free — the pad
-- lane an odd item count forces — where 7 were before the R1 interleaving, 31 at `absorbs = 71` and
-- 45 before §6b. EQUALITY, so un-assembling any consumer moves this number.
#guard shapeStep.absorbs - (absRoundList shapeStep).length == 11
#guard (List.range shapeStep.absorbs).countP (fun b => blockRound shapeStep b == none) == 11
#guard (List.range shapeStep.absorbs).foldl
        (fun n b => n + (List.range 2).countP (fun j =>
           msgVar shapeStep b j == vMsg shapeStep b j)) 0 == 1
-- ⚑ …and the SIX that left the free list are exactly the three closures, block for block and lane
-- for lane, each against the variable its CONSUMER reads.
#guard msgVar shapeStep oSgOld0 0 == ipx shapeStep (qInit shapeStep)
        && msgVar shapeStep oSgOld0 1 == ipy shapeStep (qInit shapeStep)
#guard msgVar shapeStep (oCip shapeStep) 0 == vCipShift shapeStep
        && msgVar shapeStep (oCip shapeStep) 1 == vCipBit shapeStep
#guard msgVar shapeStep (oDelta shapeStep) 0 == ipx shapeStep (qDel shapeStep)
        && msgVar shapeStep (oDelta shapeStep) 1 == ipy shapeStep (qDel shapeStep)
-- ⚑ …and `t_comm`'s FOURTEEN, block for block and lane for lane, at their SCHEDULE position (after
-- `z_comm`/α and before ζ, `step_verifier.ml:567`) rather than after the gammas.
#guard (List.range shapeStep.absorbs).foldl
        (fun n b => n + (List.range 2).countP (fun _ => tCommBlock shapeStep b != none)) 0 == 14
#guard (List.range (tCommN shapeStep)).all (fun i =>
  let b := oTc shapeStep + i
  tCommBlock shapeStep b == some i
  && msgVar shapeStep b 0 == vTcX shapeStep i && msgVar shapeStep b 1 == vTcY shapeStep i
  && msgValOf shapeStep (stepBases shapeStep) (0, 0) b 0 == (ftcTc i).1
  && msgValOf shapeStep (stepBases shapeStep) (0, 0) b 1 == (ftcTc i).2)
-- …and exactly ONE absorbed word of R1's transcript is `index_digest`, at BLOCK 0 — upstream's own
-- position (`absorb sponge Field index_digest` precedes `Vector.iter ~f:(absorb sponge PC) sg_old`,
-- `step_verifier.ml:534,538`).
#guard (List.range shapeStep.absorbs).foldl
        (fun n b => n + (List.range 2).countP (fun j =>
           msgVar shapeStep b j == vIdxD shapeStep 0)) 0 == 1
#guard msgVar shapeStep 0 0 == vIdxD shapeStep 0
#guard msgValOf shapeStep (stepBases shapeStep) (0, 0) 0 0 == indexDigest
-- ── ⚑ THE ABSORB SHAPE IS `verify_one`'s OWN ITEM COUNT, AND SO IS ITS ORDER ───────────────────
-- `absorbs` is `⌈117/2⌉` AND is now DERIVED from the schedule, so the shape, the item census and the
-- absorption ORDER agree by construction rather than by three numbers someone chose. Every pin is an
-- EQUALITY: widening `absorbs` back out, or reordering a run, reds several at once.
#guard N_ABSORB_ITEMS == 117
#guard (ABSORB_ITEMS.map (·.2)) == [1, 4, 2, 30, 2, 14, 2, 60, 2]
#guard absorbBlocksNeeded == 59
#guard shapeStep.absorbs == absorbBlocksNeeded
#guard shapeStep.absorbs == absorbBlocksOf shapeStep
#guard shapeSmoke.absorbs == absorbBlocksOf shapeSmoke
#guard 2 * shapeStep.absorbs == 118
-- ⚑ …and the residue is ONE pad lane. 117 is odd, `index_digest` is the single unpaired `Field`,
-- every later item is a point or a `(field, bit)` pair, and this file models ONE per rate-2 block.
-- **That is STRUCTURAL — there is no absorption behind it to close.**
#guard 2 * shapeStep.absorbs - N_ABSORB_ITEMS == 1
-- ⚑⚑ **THE ITEM CENSUS AND THE WIRING CENSUS AGREE, AS AN EQUALITY, AND `UNWIRED_ITEMS` IS EMPTY.**
-- Every item `verify_one` absorbs is a word some row here reads: `index_digest` + `sg_old[0]` + the
-- 48 fold commitments + `t_comm`'s 7 chunks + `cip` (field+bit) + `delta` = 117.
#guard N_UNWIRED_ITEMS == 0 && UNWIRED_ITEMS == []
#guard N_ABSORB_ITEMS
        == 1 + 2 + 2 * (absRoundList shapeStep).length + 2 * tCommN shapeStep + 2 + 2
#guard 2 * shapeStep.absorbs - N_ABSORB_ITEMS == N_UNWIRED_ITEMS + 1
-- …and the `t_comm` cap does not bind: `tCommN` is 7 because `N_TCOMM` is 7.
#guard tCommN shapeStep == N_TCOMM && shapeStep.tComms == N_TCOMM

-- ── ⚑⚑ §12i — **THE SCHEDULE, AND WHY `combined_inner_product` IS NOT A CYCLE** ────────────────
-- `absorb sponge Scalar advice.combined_inner_product` is at `step_verifier.ml:256`, INSIDE
-- `check_bulletproof`, which runs on the sponge forked at `:573` — after `let zeta = sample_scalar
-- ()` at `:568`. So β, γ, α and ζ are fixed before it. The previous rung's diagnosis stopped at "R1
-- runs all absorb blocks before all squeezes"; that was true and not the whole blocker (segment A
-- absorbing R1's own challenges was the other half, see `vPrevChal`). These pin BOTH halves.
#guard sqBlock shapeStep shapeStep.betaChal == absBlock shapeStep (oZ shapeStep - 1) + 1
#guard sqBlock shapeStep shapeStep.gammaChal == sqBlock shapeStep shapeStep.betaChal + 1
#guard sqBlock shapeStep shapeStep.alphaChal == absBlock shapeStep (oTc shapeStep - 1) + 1
#guard sqBlock shapeStep shapeStep.zetaChal == absBlock shapeStep (oCip shapeStep - 1) + 1
-- ⚑ the four are squeezed STRICTLY BEFORE `cip`'s block, and every later squeeze strictly after.
#guard (List.range 4).all (fun c => sqBlock shapeStep c < absBlock shapeStep (oCip shapeStep))
#guard ((List.range shapeStep.chals).drop 4).all
        (fun c => absBlock shapeStep (oCip shapeStep) < sqBlock shapeStep c)
-- ⚑ `c` is the squeeze that FOLLOWS `delta` (`:321-322`), and it is the last scheduled one.
#guard sqBlock shapeStep shapeStep.cChal == absBlock shapeStep (oDelta shapeStep) + 1
#guard shapeStep.cChal == sqScheduled shapeStep - 1 && sqScheduled shapeStep == 21
-- ⚑ …and the schedule really is `absorbs + chals` blocks with the absorb ordinals in order.
#guard (tSched shapeStep).length == shapeStep.blocks
#guard (tSched shapeStep).filterMap id == List.range shapeStep.absorbs
#guard (tSched shapeSmoke).filterMap id == List.range shapeSmoke.absorbs
#guard (sqBlocks shapeStep).length == shapeStep.chals
-- ⚑⚑ **AND THE NON-CIRCULARITY, MEASURED.** Re-run R1 with the `cip` word set to ZERO: β, γ, α, ζ
-- are IDENTICAL (so `ft_eval0`, the fr-sponge, ξ, r and the Horner chain that produces `cip` are
-- all unchanged, which is what makes the two-pass assembly exact) — and every squeeze after it
-- MOVES, so the absorption is live rather than inert.
#guard (List.range 4).all (fun c => chalOf shapeSmoke spNoCip c == chalOf shapeSmoke tS.sp c)
-- ⚑ …so R6's `ft_eval0` — which reads ζ, α, β, γ and NOTHING else off the transcript — is the same
-- value in both passes. That is the fact the two-pass `mkStepWith` rests on, stated on the value
-- rather than on the four inputs, so a future R6 that reached a later squeeze would red HERE.
#guard (runFt shapeSmoke spNoCip).out == tS.ft.out
#guard ((List.range shapeSmoke.chals).drop 4).all (fun c =>
  chalOf shapeSmoke spNoCip c != chalOf shapeSmoke tS.sp c)
-- ⚑ …and the word the transcript actually swallowed IS the statement word R8 binds — which is what
-- makes it a CONSUMED absorption and not one more thing the sponge eats.
#guard (tS.sp.msgs.getD (absBlock shapeSmoke (oCip shapeSmoke)) []).getD 0 0 == tS.fin.cipShift
#guard (tS.sp.msgs.getD (absBlock shapeSmoke (oCip shapeSmoke)) []).getD 1 0 == CIP_BIT
#guard tS.fin.cipShift == shiftT1 (tS.df.ca.getLastD 0)

end Dregg2.Circuit.Emit.KimchiStepMain
