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
-- ⚑ CORRECTED 2026-08-03 (§19): the exposed point at 16/17 is `q = p_prime + lr_prod`, the one
-- `Scalar_challenge.endo q c` reads, not the bare fold sum. `uc` is inside it now.
/-- **`the_exposed_opening_words_are_the_derived_points`** — slots 14, 16 and 17 of the committed
statement carry VARIABLES this assembly derives, not witnesses: 14 is the MSM fold's `x`, and the
16/17 pair is `q = p_prime + lr_prod`'s. Stated together because they are one claim about one
region, and because a slot silently ceasing to be derived is invisible when each is its own guard.
⚠ Three `#guard`s, converted 2026-08-03 (`metatheory/docs/GUARD-DISCIPLINE.md`): the expressions
are unchanged, and the gain is a NAMED TERM the axiom sweep can see. -/
theorem the_exposed_opening_words_are_the_derived_points :
    ((exposedVars shapeStep).getD 14 (xv 0)
        == mpx shapeStep (pSum shapeStep (shapeStep.msmTerms - 2))
     && (exposedVars shapeStep).getD 16 (xv 0) == ipx shapeStep (qPrime shapeStep)
     && (exposedVars shapeStep).getD 17 (xv 0) == ipy shapeStep (qPrime shapeStep)) = true := by
  native_decide

#assert_compiled the_exposed_opening_words_are_the_derived_points

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

/-- ⚑⚑ **THE ∀-GAIN: TEN TRANSCRIBED INSTANCES BECOME ONE BOUNDED QUANTIFIER OVER THE WHOLE LEGAL
DOMAIN.** `cipMaskLaw` (the `…Fixture`) is `LEGAL_MASKS.all` of six clauses, and it replaces exactly
these ten `#guard` lines:

  * three `cipAtMask m == cipRKept m`, one per mask                      → clause (i)
  * one `(List.range 3).all` fusion identity over an INLINE literal list → clause (ii)
  * two `dfBent0` controls (`== ` at the deployed mask, `!=` at `[1,1]`) → clause (iii)
  * one "not `cipR` over the full 47", stated only at `[0,1]`            → clause (iv)
  * one "not the zero-the-entry reading", stated only at `[0,1]`         → clause (v)
  * `cipAtMask [1,1] != cipAtMask [0,1]` and the three-way `dedup`       → clause (vi)

⚑ **AND IT IS STRICTLY STRONGER, in two ways that matter here.** (a) The instances could not see the
shape of their own domain: a mask omitted from the battery is indistinguishable from a mask that
holds, and the reader had to know by eye that `Prefix_mask.back` admits three. The quantifier ranges
over `LEGAL_MASKS`, whose docstring IS the source reading that says three is all of them. (b)
Clauses (iv) and (v) — the FINDING — were asserted only at the deployed `[0,1]`. Nothing said they
hold at `[0,0]`, the other dropping mask. Now they do, and as a biconditional against `dropOf m == 0`
rather than as a single inequality, so the `[1,1]` direction (where the emitted value IS the full
47-term fold) is asserted too instead of being left unstated. -/
theorem cip_mask_law : cipMaskLaw = true := by native_decide
#assert_compiled cip_mask_law

/-- The Prop-level reading of clause (i), so a consumer can CITE it rather than re-derive it: at
EVERY legal mask the emitted `combined_inner_product` is `cipR` over the sub-list the mask keeps. -/
theorem cipAtMask_eq_cipRKept (m : List Nat) (hm : m ∈ LEGAL_MASKS) :
    ((cipAtMask m : ZMod pN)) = cipRKept m := by
  have h := cip_mask_law
  simp only [cipMaskLaw, List.all_eq_true] at h
  have hm' := h m (by simpa using hm)
  simp only [Bool.and_eq_true, beq_iff_eq] at hm'
  exact hm'.1.1.1.1.1

/-- ⚠ The two sides of the next theorem are CLOSED, enormous terms (`cipRFull` is the whole 47-term
fold over the smoke assembly). A `rw`/`▸`/`simp` step on them asks the elaborator to `whnf` the fold
and it times out. This lemma does the Bool bookkeeping over VARIABLES — pure `Eq.trans`, no motive —
so the concrete instance is only ever an APPLICATION and nothing is ever evaluated. -/
private theorem iff_of_beq_eq_beq {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    {a a' : α} {b b' : β} (h : (a == a') = (b == b')) : a = a' ↔ b = b' :=
  ⟨fun he => eq_of_beq (h.symm.trans (beq_of_eq he)),
   fun he => eq_of_beq (h.trans (beq_of_eq he))⟩

/-- ⚑ The Prop-level reading of clause (iv) — **THE FINDING**, citable: the emitted value is the
full 47-term fold EXACTLY when the mask drops nothing. Contrapositive: at both dropping masks (the
deployed `[0,1]` included) `cipRows` now emits a DIFFERENT field element than it did before. -/
theorem cipAtMask_eq_cipRFull_iff_drops_nothing (m : List Nat) (hm : m ∈ LEGAL_MASKS) :
    ((cipAtMask m : ZMod pN)) = cipRFull ↔ dropOf m = 0 := by
  have h := cip_mask_law
  simp only [cipMaskLaw, List.all_eq_true] at h
  have hm' := h m (by simpa using hm)
  simp only [Bool.and_eq_true] at hm'
  exact iff_of_beq_eq_beq (eq_of_beq hm'.1.1.2)

-- …and the emitted assembly runs the DEPLOYED one, which is the instance the ∀ does not name.
theorem cip_deployed_mask_is_the_assembly :
    (cipAtMask MASK_BITS == tS.df.ca.getLastD 0 && MASK_BITS == [0, 1]) = true := by native_decide
#assert_compiled cip_deployed_mask_is_the_assembly

-- ⚑⚑ **THE BEND REACHES THE LADDER.** Clause (iii) says slot 0's bend moves `cip` exactly when the
-- mask keeps slot 0. That is only informative if the bend reaches `E_c` AT ALL, which these two say:
-- at the deployed mask it moves slot 0's `ez`/`ew` — it is the MASK refusing the term downstream,
-- not a bend that never landed.
theorem slot0_bend_reaches_Ec :
    ((dfBent0 MASK_BITS).ez.getD 0 0 != tS.df.ez.getD 0 0
     && (dfBent0 MASK_BITS).ew.getD 0 0 != tS.df.ew.getD 0 0) = true := by native_decide
#assert_compiled slot0_bend_reaches_Ec

/-- …and the KEPT slot's bend still moves `cip` at the deployed mask — the pair of that control.
(§18(f)'s `dfBent` is the same bend at index `bRounds`; stated here too so the two directions read
as one measurement rather than as two sections that happen to agree.) -/
theorem kept_slot_bend_moves_cip :
    ((runDef shapeSmoke tS.sp ftS.out xiFoldS rFoldS FT_OMEGA
        (fun i => if i == shapeSmoke.bRounds then fAdd (prevChalVal i) 1 else prevChalVal i)
        MASK_BITS).ca.getLastD 0 != tS.df.ca.getLastD 0) = true := by native_decide
#assert_compiled kept_slot_bend_moves_cip

/-- ⚑ **∀-GAIN over the MASKED SLOTS.** `cipRows` reads each mask bit EXACTLY once — two transcribed
lines (`vMask 0`, `vMask 1`) become one quantifier over `List.range N_CIP_MASKED`, so a slot the
emitter forgets to mux cannot pass by being absent from the battery. -/
theorem cip_reads_each_mask_bit_once : cipReadsEachMaskBitOnce = true := by native_decide
#assert_compiled cip_reads_each_mask_bit_once

/-- …and the mux cells are read exactly where they are written: `sⱼ` twice (its own half and the
difference), `dⱼ` twice, `pⱼ` twice plus its probe. Already quantified over the masked slots; it
gains a NAME, not a ∀. -/
theorem cip_mux_cells_read_where_written :
    ((List.range N_CIP_MASKED).all (fun j =>
      cipRowVars.countP (· == vCs shapeSmoke j) == 2
      && cipRowVars.countP (· == vCd shapeSmoke j) == 2
      && cipRowVars.countP (· == vCp shapeSmoke j) == 3)) = true := by native_decide
#assert_compiled cip_mux_cells_read_where_written

/-- ⚑ …and the mask bit really is IN a σ class with §8h's rows and not a second variable that
happens to hold the same number: `vMask 0`'s class spans `branchRows`' booleanity + pack + probe, the
two masked segments' muxes, and `combine`'s. (The CLOSED FORM — `5 + 3·maskReaders i + 1`, the
trailing `1` being this mux — is §14a's `maskReaders` pin, which already enumerated every other
consumer; it is not restated here.) -/
theorem mask_bit_class_grows_with_the_mux :
    ((classCells posS (vMask shapeSmoke 0)).length
      > (classCells posUS (vMask shapeSmoke 0)).length) = true := by native_decide
#assert_compiled mask_bit_class_grows_with_the_mux

/-- ⚑ …and the UNMASKED slots are untouched: `combine` folds `j ≥ 2` with `Some`, so no `vMask` cell
appears in their halves and `vCk 2`'s class is exactly the A-row and the B-step that reads it. -/
theorem unmasked_slot_class_untouched :
    (classCells posS (vCk shapeSmoke 2)).length = 2 := by native_decide
#assert_compiled unmasked_slot_class_untouched

end Dregg2.Circuit.Emit.KimchiStepMain
