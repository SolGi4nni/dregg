/-
`KimchiStepMain` pins — §14a.

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

-- ── §14a — ⚑ THE MASK COMES FROM `branch_data` (simplification #9, retired) ────────────────────
-- Every block's `keep` is one of TWO variables, and those two are the `proofs_verified_mask` bits
-- `Checked.pack` ties to the `branch_data` statement word. Not a schedule constant: the pattern
-- `optProofOf` decides is only WHICH bit a block reads, and the bits themselves are circuit
-- variables a public word pins.
#guard (List.range tS.specA.nb).all (fun b =>
  tS.specA.keepVar b == vMask shapeSmoke (optProofOf shapeSmoke b))
#guard (List.range tS.specA.nb).all (fun b =>
  tS.specA.keepVar b == vMask shapeSmoke 0 || tS.specA.keepVar b == vMask shapeSmoke 1)
-- ⚑ `Prefix_mask.there N1 = [false; true]`: the SET bit is a SUFFIX, so with one previous proof the
-- FIRST slot is dropped and the SECOND is kept. (The pattern this rung ran until 2026-08-02 kept the
-- first half — the opposite, and it was a constant.)
#guard MASK_BITS == [0, 1]
#guard tS.specA.keepBit 0 == 0 && tS.specA.keepBit (tS.specA.nb - 1) == 1
-- ⚑ `Checked.pack {mask; domain_log2} = 4·domain_log2 + pack(mask)` (`branch_data.ml:95-101`) —
-- the identity §8h's second `Generic` row emits, and the value the public word carries.
#guard branchPacked == 4 * BRANCH_DOMAIN_LOG2 + MASK_BITS.getD 0 0 + 2 * MASK_BITS.getD 1 0
#guard branchPacked == 66
-- …the bits are Boolean (the row `m² = m` is what enforces it in-circuit), and `domain_log2` is the
-- Step domain the rest of the rung runs at.
#guard MASK_BITS.all (fun m => m * m == m)
#guard BRANCH_DOMAIN_LOG2 == FT_LOG2N
-- ⚑ …and the mask VARIABLES really are wired: each reaches its §8h rows AND the opt-sponge mux rows
-- it gates, and `branch_data` reaches §8h's pack row and the closing public tie.
-- Exact: each mask bit is read by its booleanity row (3 cells), `Checked.pack` (1), its probe (1),
-- and the THREE `Field.if_` lane-mux rows of every masked block that reads it — in segment A AND,
-- since the segment-C retirement, in `hash_messages_for_next_step_proof` too.
-- ⚑ …plus, since 2026-08-02, exactly ONE more each: `combine`'s own `Opt.Maybe` mux
-- (`common.ml:270-271`, §12l), whose `pⱼ = keepⱼ·dⱼ` half reads the bit once. That `+ 1` IS the
-- rung — a fold that stopped honouring the mask reds here rather than passing a floor.
-- ⚠ ⚑ **`+ 2`, NOT `+ 1`, SINCE `c14a9cf01`** — and the second one is NOT identified here. That
-- commit swept a SIBLING lane's in-flight `vCipBit := bpOdd s 0` rung into the same file as §23's
-- sponge re-model (`git commit --only` is PATH-granular, not hunk-granular), and the extra mask
-- reader arrived with it. §23 alone leaves this at `+ 1`: the same census is 21 against §23's Core
-- without the co-landed hunk. Naming a mechanism for a reader this lane did not add would be a
-- guess wearing a diagnosis's clothes; the NUMBER is measured and the provenance is stated.
#guard (List.range 2).all (fun i =>
  (classCells posS (vMask shapeSmoke i)).length == 5 + 3 * maskReaders i + 2)
-- ⚑ …and segment C really is a SECOND consumer: each bit now has strictly more readers than
-- segment A alone gives it. (The count `11` this pin carried before the retirement was segment A's
-- alone; naming the delta is what makes the pin bite rather than track.)
#guard (List.range 2).all (fun i =>
  maskReaders i > ((List.range (nbA shapeSmoke)).filter
                     (fun b => optProofOf shapeSmoke b == i)).length)
-- 2 opt-sponge blocks + 3 segment-C blocks (one commitment, `bRounds/2` challenge blocks) each.
#guard maskReaders 0 == 2 + 3 && maskReaders 1 == 2 + 3
-- …stated as the absolute number too: 5 + 3·5 opt-sponge/segment-C lanes + TWO (see above).
#guard (classCells posS (vMask shapeSmoke 0)).length == 22
#guard (classCells posS (vMask shapeSmoke 1)).length == 22
-- …and `branch_data` is read by EXACTLY three rows: the pack row, the closing public tie, its probe.
#guard (classCells posS (vBranch shapeSmoke)).length == 3
#guard (exposedVars shapeSmoke).getD 5 (xv 0) == vBranch shapeSmoke

-- ⚑⚑ **THE BITING RED CONTROL FOR #9.** Re-run segment A at the OTHER two legal prefix masks. `N2`
-- ([tt;tt], both previous proofs real) and `N0` ([ff;ff], none) each give a DIFFERENT opt-sponge
-- digest — so the mask is deciding the value, and `branch_data` is what decides the mask. And the
-- digest is segment B's SECOND absorbed word (the FIRST is §22's seed), so a different `branch_data`
-- moves the fr-sponge, its two squeezes, §8g's ξ and r, and `combined_inner_product` with them.
#guard segADigest MASK_BITS == (tS.segA.states.getLastD []).getD 0 0
#guard segADigest [1, 1] != segADigest MASK_BITS
#guard segADigest [0, 0] != segADigest MASK_BITS
#guard segADigest [1, 1] != segADigest [0, 0]
-- …and the digest IS what segment B absorbs at word 1, so the cascade above is a wire and not a
-- story. ⚑ Word 0 is §22's seed; before it landed the digest was word 0.
#guard (tS.specB.ws.getD 1 (xv 0, 0)).2 == segADigest MASK_BITS

-- ⚑⚑ **THE BITING RED CONTROL FOR SEGMENT C's MASK.** `hash_messages_for_next_step_proof` was the
-- SECOND consumer of `proofs_verified_mask` and this segment absorbed its carried challenges
-- UNMASKED until 2026-08-02 — the residue #9's retirement made visible. It now reads the same two
-- `branch_data` bits, and the three legal prefix masks give three DIFFERENT digests.
#guard segCDigest MASK_BITS == (tS.segC.states.getLastD []).getD 0 0
#guard segCDigest [1, 1] != segCDigest MASK_BITS
#guard segCDigest [0, 0] != segCDigest MASK_BITS
#guard segCDigest [1, 1] != segCDigest [0, 0]
-- ⚑ …and MASKED IS NOT UNMASKED: `[1,1]` IS the unmasked absorption (every block kept), so the pin
-- above says exactly "the old segment C computed a different hash". Named separately because that
-- is the retirement, not a by-product of it.
#guard segCDigest [1, 1] != (tS.segC.states.getLastD []).getD 0 0
-- ⚑ …and the mask is applied to the RIGHT WORDS: the `Not_opt` prefix is unconditional, then ONE
-- bit per previous proof over that proof's `(commitment ×2, bRounds challenges)` RUN — the
-- interleaved layout `to_field_elements_without_index` builds (`composition_types.ml:603-606`).
-- ⚠ These four pins read `vMask 0, 1, 0, 1` at blocks `+0, +1, +2, last` until 2026-08-02, which is
-- the CONCATENATED layout's pattern and is exactly what the wrong wire looked like from here.
#guard (List.range tS.specC.nb).all (fun b =>
  tS.specC.maskedAt b == decide (N_HM_FIX ≤ 2 * b))
#guard tS.specC.maskFrom == N_HM_FIX / 2
-- the per-proof stride is `2 + bRounds` words = `(2 + bRounds)/2` blocks (3 at the smoke shape).
#guard (List.range ((2 + shapeSmoke.bRounds) / 2)).all (fun k =>
  (hmKeepAt shapeSmoke MASK_BITS (N_HM_FIX / 2 + k)).1 == vMask shapeSmoke 0)
#guard (List.range ((2 + shapeSmoke.bRounds) / 2)).all (fun k =>
  (hmKeepAt shapeSmoke MASK_BITS (N_HM_FIX / 2 + (2 + shapeSmoke.bRounds) / 2 + k)).1
    == vMask shapeSmoke 1)
#guard (hmKeepAt shapeSmoke MASK_BITS (tS.specC.nb - 1)).1 == vMask shapeSmoke 1
-- …and the same at the COMMITTED shape, where the stride is 9 blocks and not 3.
#guard (hmKeepAt shapeStep MASK_BITS (N_HM_FIX / 2 + 8)).1 == vMask shapeStep 0
#guard (hmKeepAt shapeStep MASK_BITS (N_HM_FIX / 2 + 9)).1 == vMask shapeStep 1
-- …the `Opt` region starts on a BLOCK boundary, which is the whole reason the prefix is even.
#guard N_HM_FIX % 2 == 0
-- ⚑ …and the digest is a PUBLIC WORD, so the mask reaches the verifier's own vector rather than
-- dying inside R7. (`vSt`-style inertness is what `placeChecked` would have caught; this is the
-- stronger statement that it is READ OUT.)
#guard (exposedVars shapeSmoke).getD 6 (xv 0) == hmDigestVar shapeSmoke
#guard (stepPublic tS).getD 6 0 == ((tS.segC.states.getLastD []).getD 0 0 : Int)

-- ── ⚑⚑ SEGMENT D — the OUTER `hash_messages_for_next_step_proof` (`step_main.ml:525-566`) ───────
-- Its squeeze is the STEP statement's `messages_for_next_step_proof` (`:572-575`), public word 7 —
-- a DIFFERENT digest from segment C's, which is the WRAP statement's (`:83-86`).
#guard (exposedVars shapeSmoke).getD 7 (xv 0) == hmOutDigestVar shapeSmoke
#guard (stepPublic tS).getD 7 0 == ((tS.segD.states.getLastD []).getD 0 0 : Int)
#guard (stepPublic tS).getD 6 0 != (stepPublic tS).getD 7 0
-- ⚑⚑ …and it is its OWN `sponge_after_index`, NOT a copy of segment C's — CORRECTED 2026-08-07.
-- These three guards read *"it is a `Sponge.copy` of `sponge_after_index` and NOT a re-absorption:
-- its block-0 state lanes ARE segment C's own variables at the index boundary … and its state at
-- block 0 is `idxAfterState`"*, and every word of that was the old model. `step.rs:2718` gives the
-- OUTER hash `merge::dlog_plonk_index(wrap_prover)` — the instance's OWN wrap key — so segment D
-- starts from a FRESH sponge, absorbs its own 56 coordinates, and lands somewhere segment C never
-- goes. The three below say exactly that, and the third is the one with content: **a different key
-- gives a different `after_index` state**, which is what makes §18's tie bind the key at all.
#guard (List.range 3).all (fun j =>
  tS.specD.stV (baseSegD shapeSmoke) (nbD shapeSmoke) 1 0 j
    != sgSt (baseSegC shapeSmoke) (nbC shapeSmoke) 1 (N_IDX_WORDS / 2) j)
#guard tS.segD.states.headD [] == [0, 0, 0]
#guard tS.segC.states.getD (N_IDX_WORDS / 2) [] == idxAfterState
#guard tS.segD.states.getD (N_IDX_WORDS / 2) [] != idxAfterState
-- …and it absorbs ALL 56 index words ahead of the app state, `G` and the challenges.
#guard tS.specD.ws.length == shapeSmoke.hmOutWords
#guard tS.specD.ws.length == N_IDX_WORDS + N_HM_APP + 2 + shapeSmoke.bRounds
#guard (tS.specD.ws.getD (N_IDX_WORDS + N_HM_APP) (xv 0, 0)).1 == vGx shapeSmoke
#guard (tS.specD.ws.getD (N_IDX_WORDS + N_HM_APP + 1) (xv 0, 0)).1 == vGy shapeSmoke
#guard (tS.specD.ws.getD (N_IDX_WORDS + N_HM_APP) (xv 0, 0)).2 == tS.gXY.1
-- ⚑ …and its challenge run is `bulletproof_challenges` — the vector `finalize_other_proof` RETURNS
-- (`step_verifier.ml:1114-1116,1147`), i.e. the LIFTED deferred challenges the `b(ζ)` product folds
-- over — and NOT segment C's `prev_challenges`. Two hashes, two vectors, and they are disjoint here.
#guard (List.range shapeSmoke.bRounds).all (fun k =>
  (tS.specD.ws.getD (N_IDX_WORDS + N_HM_APP + 2 + k) (xv 0, 0)).1
    == vLift shapeSmoke (shapeSmoke.uChal k))
#guard (tS.specD.ws.map (·.1)).all (fun v =>
  ((List.range (2 * shapeSmoke.bRounds)).any (fun i => v == vPrevChal shapeSmoke i)) == false)
-- …and it is UNMASKED: `hash_messages_for_next_step_proof`, not `…_opt` (`step_main.ml:547`).
#guard tS.specD.masked == false && tS.specC.masked == true

-- ⚑ SEGMENT B ABSORBS R5's AND R6's OWN VARIABLES: since §22 the SEED (R1's own ζ-squeeze lane 1),
-- then the digest of segment A, `ft_eval1`, the two public-polynomial evaluations, then the 43
-- columns at ζ and ζω INTERLEAVED (`to_absorption_sequence`, `step_verifier.ml:967-1005`) — the same
-- `vEz`/`vEw` the C8 fold and the `ft_eval0` rung read. Not a private stream.
#guard (tS.specB.ws.getD 1 (xv 0, 0)).1
        == sgSt (baseSegA shapeSmoke) (nbA shapeSmoke) 1 tS.specA.blocks 0
#guard (tS.specB.ws.getD 1 (xv 0, 0)).2 == (tS.segA.states.getLastD []).getD 0 0
#guard (tS.specB.ws.getD 2 (xv 0, 0)).1 == vEw shapeSmoke 3
#guard (List.range shapeSmoke.frCols).all (fun k =>
  (tS.specB.ws.getD (5 + 2 * k) (xv 0, 0)).1 == vColZ shapeSmoke k
  && (tS.specB.ws.getD (6 + 2 * k) (xv 0, 0)).1 == vColW shapeSmoke k)
-- ⚑ …and segments A and C absorb `prev_challenges` — THE SAME VARIABLES, which is upstream's own
-- shape (`step_verifier.ml:956` and `step_main.ml:80` read one vector) and NOT R2's challenges. That
-- false wire is what made `combined_inner_product` a cycle; see `vPrevChal` for what it cost and what
-- it bought.
#guard (List.range tS.specA.ws.length).all (fun i =>
  (tS.specA.ws.getD i (xv 0, 0)).1 == vPrevChal shapeSmoke i)
-- ⚑ …and segment C carries them INTERLEAVED with the commitment they belong to
-- (`composition_types.ml:603-606`): proof `i`'s two coordinates at `N_HM_FIX + i·(2+bRounds)`, then
-- proof `i`'s OWN `bRounds` challenges — which are segment A's entries `i·bRounds …` in order.
#guard (List.range 2).all (fun i =>
  (List.range shapeSmoke.bRounds).all (fun k =>
    tS.specC.ws.getD (N_HM_FIX + i * (2 + shapeSmoke.bRounds) + 2 + k) (xv 0, 0)
      == tS.specA.ws.getD (i * shapeSmoke.bRounds + k) (xv 0, 0)))
-- …and NO segment absorbs a transcript challenge variable any more.
#guard (tS.specA.ws.map (·.1)).all (fun v =>
  ((List.range shapeSmoke.chals).any (fun c => v == vN shapeSmoke c shapeSmoke.emsRows)) == false)

-- ⚑⚑ **SEGMENT C's TWO COMMITMENT SLOTS ARE `sg_old`, AND THEY WERE NOT** (corrected 2026-08-02).
-- Read at source (`step_main.ml:78-79`) the field is
-- `challenge_polynomial_commitments = prev_challenge_polynomial_commitments`, the vector `verify_one`
-- also hands `verify` as `~sg_old` (`:107`). Both slots were already variables of this assembly:
-- slot 0 is the fold's `~init` (`qInit`, `step_verifier.ml:606`) and slot 1 is fold ROUND 0's base,
-- because round `r` folds census commitment `r+1` and commitment 1 IS `sg_old[1]`.
#guard (tS.specC.ws.getD N_HM_FIX (xv 0, 0)).1 == ipx shapeSmoke (qInit shapeSmoke)
#guard (tS.specC.ws.getD (N_HM_FIX + 1) (xv 0, 0)).1 == ipy shapeSmoke (qInit shapeSmoke)
#guard (tS.specC.ws.getD (N_HM_FIX + 2 + shapeSmoke.bRounds) (xv 0, 0)).1
        == ipx shapeSmoke (qT shapeSmoke 0)
#guard (tS.specC.ws.getD (N_HM_FIX + 3 + shapeSmoke.bRounds) (xv 0, 0)).1
        == ipy shapeSmoke (qT shapeSmoke 0)
-- …and `sg_old[1]` really is fold round 0's base, at BOTH shapes: `absRoundList`'s first entry, the
-- point transcript block `oPre` absorbs.
#guard (absRoundList shapeSmoke).headD 99 == 0 && (absRoundList shapeStep).headD 99 == 0
#guard msgVar shapeStep oPre 0 == ipx shapeStep (qT shapeStep 0)
#guard sgOldVar shapeStep 0 0 == ipx shapeStep (qInit shapeStep)
#guard sgOldVar shapeStep 1 0 == ipx shapeStep (qT shapeStep 0)
-- ⚠ …and NEITHER of the two the segment used to carry is in it any more. `x_hat`'s MSM output and
-- the fold output `q` are computed INSIDE this `verify_one` and are public words 14–17 in their own
-- right; upstream puts neither in this hash.
#guard (tS.specC.ws.map (·.1)).all (fun v =>
  v != mpx shapeSmoke (pSum shapeSmoke (shapeSmoke.msmTerms - 2))
  && v != mpy shapeSmoke (pSum shapeSmoke (shapeSmoke.msmTerms - 2))
  && v != ipx shapeSmoke (qSum shapeSmoke (shapeSmoke.ipaRounds - 1))
  && v != ipy shapeSmoke (qSum shapeSmoke (shapeSmoke.ipaRounds - 1)))

-- ⚑ THE SPONGE IS NOT DEGENERATE: the four digests differ from each other and from zero, so a
-- sponge that silently absorbed nothing would show.
#guard (tS.segA.states.getLastD []).getD 0 0 != 0
#guard (tS.segB.states.getLastD []).getD 0 0 != 0
#guard (tS.segC.states.getLastD []).getD 0 0 != 0
#guard (tS.segD.states.getLastD []).getD 0 0 != 0
#guard (tS.segA.states.getLastD []).getD 0 0 != (tS.segB.states.getLastD []).getD 0 0
#guard (tS.segB.states.getLastD []).getD 0 0 != (tS.segC.states.getLastD []).getD 0 0
#guard (tS.segC.states.getLastD []).getD 0 0 != (tS.segD.states.getLastD []).getD 0 0

end Dregg2.Circuit.Emit.KimchiStepMain
