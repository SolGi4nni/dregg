/-
`KimchiStepMain` pins — §12k §12l.

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

-- ── ⚑⚑ §12k — **THE SEGMENT-C MIS-WIRE, IN BOTH DIRECTIONS, ON THE EMITTED DIGEST** ─────────────
-- A correction without an exhibited alternative is a claim. `hmSpecMiswired` is the segment exactly
-- as it stood; `hmSpec` is the corrected one. The control has to BITE BOTH WAYS: what upstream
-- absorbs must now move the digest, and what it does not must now leave it alone.

-- the two layouts really are different objects and both are the same LENGTH, so nothing below is
-- comparing a longer list with a shorter one.
#guard tS.specC.ws.length == segCMisSpec.ws.length
#guard tS.specC.ws != segCMisSpec.ws
#guard segCDigestOf tS.specC.ws == (tS.segC.states.getLastD []).getD 0 0
#guard segCMisDigestOf segCMisSpec.ws != segCDigestOf tS.specC.ws

-- ⚑⚑ **(→) THE CORRECTED SLOT BITES.** Bending either coordinate of `sg_old[1]` moves segment C's
-- digest, which is public word 6. The mis-wired segment never held that variable at all.
#guard segCDigestOf (bendW tS.specC.ws wSgOld1) != segCDigestOf tS.specC.ws
#guard segCDigestOf (bendW tS.specC.ws (wSgOld1 + 1)) != segCDigestOf tS.specC.ws
#guard (segCMisSpec.ws.map (·.1)).all (fun v =>
  v != ipx shapeSmoke (qInit shapeSmoke) && v != ipy shapeSmoke (qInit shapeSmoke)
  && v != ipx shapeSmoke (qT shapeSmoke 0) && v != ipy shapeSmoke (qT shapeSmoke 0))

-- ⚠ ⚑ **AND SLOT 0 DOES NOT BITE — SAY IT, BECAUSE IT IS THE MASK DOING ITS JOB AND NOT A HOLE.**
-- `MASK_BITS = Prefix_mask.there N1 = [0,1]`: with ONE previous proof the kept slot is the SUFFIX
-- one, so slot 0 is the dummy `Wrap_hack` pad and its whole run — commitment AND challenges — is
-- muxed out of the state (`step_verifier.ml:1180-1186`, `:998-1003`). Bending it therefore moves
-- nothing, at either layout. A control that claimed both slots bite would be measuring the wrong
-- instance.
#guard MASK_BITS == [0, 1]
#guard segCDigestOf (bendW tS.specC.ws wSgOld0) == segCDigestOf tS.specC.ws
#guard segCDigestOf (bendW tS.specC.ws (wSgOld0 + 1)) == segCDigestOf tS.specC.ws
-- …and it is the MASK and not the wiring: flip both bits on and slot 0 bites too.
#guard (hmKeepAt shapeSmoke [1, 1] (N_HM_FIX / 2)).2 == 1
#guard ((runSeg { tS.specC with ws := bendW tS.specC.ws wSgOld0
                              , keep := fun b => (xv 0, (hmKeepAt shapeSmoke [1, 1] b).2) }
        ).states.getLastD []).getD 0 0
        != ((runSeg { tS.specC with keep := fun b => (xv 0, (hmKeepAt shapeSmoke [1, 1] b).2) }
            ).states.getLastD []).getD 0 0

-- ⚑⚑ **(←) THE WRONGLY-WIRED WORD NO LONGER BITES.** In the mis-wired layout the fold output `q`
-- sat in the KEPT slot, so bending it moved this public digest — which is exactly what made the
-- wrong wire invisible: a bent word DID move a public output, just not the one upstream moves. In
-- the corrected segment that variable is absent, so no bend of it can reach this digest.
#guard segCMisDigestOf (bendW segCMisSpec.ws wFold) != segCMisDigestOf segCMisSpec.ws
#guard (segCMisSpec.ws.getD wFold (xv 0, 0)).1
        == ipx shapeSmoke (qSum shapeSmoke (shapeSmoke.ipaRounds - 1))
-- (the x_hat pair sat in the DROPPED slot under the old `keep` map, so it never bit either — the
-- old wire put one computed quantity where upstream puts a dummy and the other where upstream puts
-- the live commitment.)
#guard segCMisDigestOf (bendW segCMisSpec.ws wXhat) == segCMisDigestOf segCMisSpec.ws
#guard (segCMisSpec.ws.getD wXhat (xv 0, 0)).1
        == mpx shapeSmoke (pSum shapeSmoke (shapeSmoke.msmTerms - 2))
-- …and both of them are public words of their OWN at the committed shape, so nothing was lost by
-- taking them out of this hash — they were never unobserved.
#guard (exposedVars shapeStep).getD 14 (xv 0)
        == mpx shapeStep (pSum shapeStep (shapeStep.msmTerms - 2))
#guard (exposedVars shapeStep).getD 16 (xv 0)
        == ipx shapeStep (qSum shapeStep (shapeStep.ipaRounds - 1))

-- ⚑ …and the CORRECTION IS NOT VACUOUS at the level of the public vector: the digest word moved.
-- (Both layouts absorb the same 58-word prefix and the same 2·bRounds challenges; only the four
-- commitment coordinates and their ORDER differ, and that is enough.)
#guard (stepPublic tS).getD 6 0 == ((tS.segC.states.getLastD []).getD 0 0 : Int)
#guard (stepPublic tS).getD 6 0 != (segCMisDigestOf segCMisSpec.ws : Int)

-- ⚑ …and the ORDER is load-bearing on its own, stated separately from the SLOTS. The concatenated
-- layout over the SAME four correct words gives a different digest from the interleaved one, so
-- "the right words" would not have been enough.
#guard wsConcat.length == tS.specC.ws.length
#guard wsConcat != tS.specC.ws
#guard segCDigestOf wsConcat != segCDigestOf tS.specC.ws

-- ── ⚑⚑ §12l — **`combine`'s `Opt.Maybe` MUX: THE MASK'S LAST IGNORING CONSUMER, CLOSED** ─────────
-- READ AT SOURCE FIRST, because the shape of the whole result follows from one line:
--
--   * `step_verifier.ml:916`   `let actual_width_mask = branch_data.proofs_verified_mask`
--   * `:940-948`               `sg_evals pt = Vector.map2 mask sg_olds ~f:(fun keep f -> (keep, f pt))`
--   * `:1080-1095`             `sg_evals` become `[| Opt.Maybe (keep, eval) |]`, PREPENDED to
--                              `[x_hat] :: [ft] :: a` — so they are prefix entries 0 and 1
--   * `common.ml:270-271`      `| Maybe (b, fx) -> Field.if_ b ~then_:(fx + (xi * acc)) ~else_:acc`
--   * `pcs_batch.ml:88-94`     flatten · REVERSE · seed `init` with the last · fold the rest
--   * `proofs_verified.ml:75-81`  `there`: N0↦[ff;ff] · N1↦[ff;tt] · N2↦[tt;tt] — a set bit is a
--                              SUFFIX, so the deployed `N1` instance DROPS SLOT 0
--   * `wrap_hack.ml:26-28`     `pad_vector` = `Vector.extend_front_exn`, so slot 0 IS the dummy
--
-- ⚑⚑ **THE FINDING, AND IT INVERTS THE EXPECTATION THIS RUNG WAS QUEUED ON.** "Slot 0 is the
-- `Wrap_hack` dummy, so at the deployed mask dropping it is a no-op on the value" is FALSE.
-- `mul_and_add`'s `else_` branch is bare `acc` — it does not multiply by ξ — and the fold runs from
-- the list's TAIL, so slot 0 is the LAST step. Dropping it removes `c₀` AND takes one ξ power off
-- every one of the other 46 terms. The dummy's VALUE is what the mask makes irrelevant; the ξ-power
-- shift is what it does not. So this rung MOVES public word 9 at the deployed mask, and the three
-- legal masks give three different values.

-- ⚑ THE THREE LEGAL MASKS, each against `cipR` over ITS OWN kept sub-list. `Prefix_mask.back`
-- (`proofs_verified.ml:83-91`) admits exactly these three and REFUSES `[1,0]`, so this is the whole
-- domain and not a sample of it.
#guard ((cipAtMask [1, 1] : ZMod pN)) == cipRKept [1, 1]
#guard ((cipAtMask [0, 1] : ZMod pN)) == cipRKept [0, 1]
#guard ((cipAtMask [0, 0] : ZMod pN)) == cipRKept [0, 0]
-- …and the emitted assembly runs the DEPLOYED one.
#guard cipAtMask MASK_BITS == tS.df.ca.getLastD 0 && MASK_BITS == [0, 1]

-- ⚑⚑ **RED CONTROL 1 — AT A MASK WHERE SLOT 0 IS NOT THE DUMMY (`[1,1]`, the `N2` instance),
-- DROPPING SLOT 0 vs FOLDING IT GIVES A DIFFERENT `combined_inner_product`.** This is the control
-- the brief asked for and it bites: at `[1,1]` slot 0 carries a live previous proof's `E_c`.
#guard cipAtMask [1, 1] != cipAtMask [0, 1]
-- ⚑⚑ **RED CONTROL 2 — AND IT BITES AT THE DEPLOYED MASK TOO, which is the finding.** The value
-- this rung emits is NOT the value it emitted before, even though slot 0 is the dummy at `[0,1]`.
-- Stated against `cipR` over the FULL 47 — which is what `cipRows` computed until 2026-08-02 and is
-- also exactly `cipAtMask [1,1]`, so RED CONTROL 1 and this one are one fact seen from two sides.
#guard ((cipAtMask [0, 1] : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf sq1S) (foldMulOf sq2S)
              cipEzS cipEwS) == false
-- …and all THREE are pairwise different, so no two masks are the same circuit output.
#guard [cipAtMask [1, 1], cipAtMask [0, 1], cipAtMask [0, 0]].dedup.length == 3
-- ⚠ …and it is NOT the "zero the entry" reading, which is the mux a careless emission would write.
-- Zeroing slot 0's `E_c` and folding all 47 gives a THIRD value, different from both.
#guard ((cipAtMask [0, 1] : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf sq1S) (foldMulOf sq2S)
              (cipEzS.set 0 0) (cipEwS.set 0 0)) == false

-- ⚑⚑ **BOTH DIRECTIONS ON THE VALUES.** Bending a slot the mask EXCLUDES must not move the fold;
-- bending a slot it KEEPS must. `dfBent` above bends slot 1 (kept) and moves `ca`; this is the
-- other half, on slot 0's carried challenges — which DO move `E_c` at slot 0 and DO move segments
-- A and C's inputs, and must now leave `combined_inner_product` exactly where it was.
#guard (dfBent0 MASK_BITS).ez.getD 0 0 != tS.df.ez.getD 0 0
#guard (dfBent0 MASK_BITS).ew.getD 0 0 != tS.df.ew.getD 0 0
#guard (dfBent0 MASK_BITS).ca.getLastD 0 == tS.df.ca.getLastD 0
-- …and at `[1,1]`, where the mask keeps slot 0, the SAME bend does move it. So the pin above is the
-- mask refusing the term, not the bend failing to reach the ladder.
#guard (dfBent0 [1, 1]).ca.getLastD 0 != cipAtMask [1, 1]
-- …and the KEPT slot's bend still moves it at the deployed mask — the pair of this control.
-- (§18(f)'s `dfBent` is the same bend at index `bRounds`; stated here too so the two directions
-- read as one measurement rather than as two sections that happen to agree.)
#guard (runDef shapeSmoke tS.sp ftS.out xiFoldS rFoldS FT_OMEGA
          (fun i => if i == shapeSmoke.bRounds then fAdd (prevChalVal i) 1 else prevChalVal i)
          MASK_BITS).ca.getLastD 0 != tS.df.ca.getLastD 0

-- ⚑⚑ **BENDING A MASK BIT MOVES WHAT THE MUX SELECTS — ON THE EMITTED ROWS, not only the values.**
-- `vMask j` is §8h's derived bit and `cipRows` reads it: bit 0's σ class gains the mux's product
-- half, bit 1's likewise. Exact counts, not floors — §8h's booleanity row reads each bit three
-- times, `Checked.pack` once, its probe once, segment A's and segment C's muxes once per masked
-- block, and now `combine` once.
#guard cipRowVars.countP (· == vMask shapeSmoke 0) == 1
#guard cipRowVars.countP (· == vMask shapeSmoke 1) == 1
-- …and the mux cells are read exactly where they are written: `sⱼ` twice (its own half and the
-- difference), `dⱼ` twice, `pⱼ` twice plus its probe.
#guard (List.range N_CIP_MASKED).all (fun j =>
  cipRowVars.countP (· == vCs shapeSmoke j) == 2
  && cipRowVars.countP (· == vCd shapeSmoke j) == 2
  && cipRowVars.countP (· == vCp shapeSmoke j) == 3)
-- ⚑ …and the mask bit really is IN a σ class with §8h's rows and not a second variable that happens
-- to hold the same number: `vMask 0`'s class spans `branchRows`' booleanity + pack + probe, the two
-- masked segments' muxes, and `combine`'s.
#guard (classCells posS (vMask shapeSmoke 0)).length
        > (classCells posUS (vMask shapeSmoke 0)).length
-- (the CLOSED FORM of that class — `5 + 3·maskReaders i + 1`, the trailing `1` being this mux — is
-- §14a's `maskReaders` pin, which already enumerated every other consumer; it is not restated here.)
-- ⚑ …and the UNMASKED slots are untouched: `combine` folds `j ≥ 2` with `Some`, so no `vMask` cell
-- appears in their halves and `vCk 2`'s class is exactly the A-row and the B-step that reads it.
#guard (classCells posS (vCk shapeSmoke 2)).length == 2

-- ⚑ **THE FUSION COMMUTES WITH THE MUX**, stated as an identity rather than as the prose above.
-- Upstream runs `combine … + r * combine …` (`step_verifier.ml:1097-1101`) — TWO muxed folds — and
-- this region runs ONE over `cₖ = evₖ(ζ) + r·evₖ(ζω)`. Both `combine` calls take the SAME `keep`,
-- so the two agree; `cipR` over the kept sub-list IS the two-fold form, which is what the pins above
-- compare against.
#guard (List.range 3).all (fun t =>
  let ms : List Nat := [[1,1],[0,1],[0,0]].getD t []
  let d := (List.range N_CIP_MASKED).countP (fun j => ms.getD j 0 == 0)
  ((cipAtMask ms : ZMod pN))
    == (List.range (shapeSmoke.cipEvals - d)).foldl
         (fun acc k => acc + (foldMulOf sq1S) ^ k * (cipEzS.drop d).getD k 0) 0
       + (foldMulOf sq2S)
         * (List.range (shapeSmoke.cipEvals - d)).foldl
             (fun acc k => acc + (foldMulOf sq1S) ^ k * (cipEwS.drop d).getD k 0) 0)

end Dregg2.Circuit.Emit.KimchiStepMain
