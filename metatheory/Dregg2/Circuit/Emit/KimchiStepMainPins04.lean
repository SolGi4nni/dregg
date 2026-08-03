/-
`KimchiStepMain` pins — §12c §12c′ §12d.

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

-- ── §12c — ⚑ THE CHALLENGE HIGH PART IS RANGE-CHECKED (simplification #1, retired) ─────────────
-- `lowest_128_bits ~constrain_low_bits:true` asserts BOTH parts (`util.ml:98-99`) and
-- `assert_n_bits ~n:128` is `ignore (to_field_checked … ~num_bits:128)` — the chain emits, only the
-- value is dropped (`step_verifier.ml:88-97`). R2 emitted the LOW chain and the decomposition row
-- and stopped there, which left the decomposition row as one equation in two unknowns.

-- The forged pair satisfies the decomposition row EXACTLY as the honest pair does…
#guard fAdd forgedLo (fMul TWO128 forgedHi) == sqOf 0 % pN
#guard fAdd (chalOf shapeSmoke tS.sp 0) (fMul TWO128 (hiOf shapeSmoke tS.sp 0)) == sqOf 0 % pN
-- …the forged LOW part passes its own `to_field_checked` chain (it is a 128-bit value, so the
-- `EndoMulScalar` fold reconstructs it)…
#guard forgedLo < 2 ^ 128
#guard ((emsAccs shapeSmoke forgedLo).getLastD (0, 2, 2)).1 == forgedLo
-- …and it is a DIFFERENT challenge from the honest one. That is the whole attack: Fiat-Shamir
-- becomes prover-chosen.
#guard forgedLo != chalOf shapeSmoke tS.sp 0

-- ⚑⚑ **THE BITING RED CONTROL FOR #1.** The forced high part does NOT fit in 128 bits, so the new
-- chain's `EndoMulScalar` fold cannot reconstruct it and `Field.Assert.equal n scalar` fails. An
-- out-of-range challenge is REFUSED where it was accepted this morning.
#guard 2 ^ 128 ≤ forgedHi
#guard ((emsAccs shapeSmoke forgedHi).getLastD (0, 2, 2)).1 != forgedHi
-- …and the check is SATISFIABLE as well as refutable: the honest high part fits and its own chain
-- reconstructs it, at every challenge.
#guard (List.range shapeSmoke.chals).all (fun c => hiOf shapeSmoke tS.sp c < 2 ^ 128)
#guard (List.range shapeSmoke.chals).all (fun c =>
  ((emsAccs shapeSmoke (hiOf shapeSmoke tS.sp c)).getLastD (0, 2, 2)).1 == hiOf shapeSmoke tS.sp c)
#guard tS.defc.hi.getD 1 0 < 2 ^ 128
#guard ((emsAccs shapeSmoke (tS.defc.hi.getD 1 0)).getLastD (0, 2, 2)).1 == tS.defc.hi.getD 1 0

-- ⚑ …and the chain is WIRED TO THE DECOMPOSITION ROW's OWN `hi` CELL, not to a fresh copy: `vHi c`
-- is read by exactly two rows — the split row that produced it and the range chain's tie. Equality,
-- because a floor of `≥ 1` holds with the whole chain deleted.
#guard (List.range shapeSmoke.chals).all (fun c =>
  (classCells posS (vHi shapeSmoke c)).length == 2)
#guard (classCells posS (vDHi shapeSmoke 1)).length == 2
-- …and §8g's ξ chain has NO high part at all, because its source is already a `Challenge.t` —
-- upstream splits nothing there either (`let xi = scalar xi`).
#guard (classCells posS (vDHi shapeSmoke 0)).length == 0

-- ── §12c′ — ⚑ THE THIRD `lowest_128_bits`: R8's, AND IT WAS THE WORST OF THE THREE ─────────────
-- The two above are R2's transcript squeezes and §8g's `r`. The THIRD lives INSIDE the compiled
-- finalize program (§8f): `xi_actual = lowest_128_bits (squeeze fr_sponge)`
-- (`step_verifier.ml:821-822`; `lowest_128_bits` at `:99-101`, `Util.lowest_128_bits` at
-- `util.ml:78-101`), where the high part is an `AOp.wit` — a cell NO row defines.
-- It is the worst of the three because §8g's chain 0 lifts the very word `xi_correct` compares
-- against INTO THE FOLD, so a prover who chooses ξ chooses `combined_inner_product`'s multiplier.

-- The forged pair satisfies R8's decomposition EXACTLY as the honest pair does…
#guard fAdd forgedXi (fMul TWO128 forgedXiHi) == sq1S % pN
#guard fAdd tS.fin.xiStmt (fMul TWO128 tS.fin.xiHi) == sq1S % pN
-- …the forged ξ is a legal `Challenge.t`, so §8g's chain 0 (`Field.Assert.equal n scalar`, no
-- split) reconstructs it and the FOLD accepts it as its multiplier…
#guard forgedXi < 2 ^ 128
#guard ((emsAccs shapeSmoke forgedXi).getLastD (0, 2, 2)).1 == forgedXi
-- …and it is a DIFFERENT ξ from the honest one.
#guard forgedXi != tS.fin.xiStmt

-- ⚑⚑ **THE EXHIBIT: R8's PROGRAM ACCEPTS IT.** `out = 1` — the value the rung's last row asserts —
-- with `xi_correct = 1` and `xi_actual` equal to the ξ the prover named. Every other leg honest.
#guard finAtChosenXi forgedXi forgedXiHi == (1, 1, forgedXi)
-- …and the honest pair does the same, so the helper is measuring the gadget and not a broken input.
#guard finAtChosenXi tS.fin.xiStmt tS.fin.xiHi == (1, 1, tS.fin.xiStmt)
-- ⚑ …and the forgery is NOT a no-op: the fold's own multiplier moves, and so does
-- `combined_inner_product` — this is Fiat-Shamir becoming prover-chosen, not a relabelling.
#guard (Dregg2.Circuit.Emit.KimchiVerify.endoMap ((ENDO_R : Nat) : ZMod pN) forgedXi
         == foldMulOf sq1S) == false
#guard (Dregg2.Circuit.Emit.KimchiVerify.cipR
          (Dregg2.Circuit.Emit.KimchiVerify.endoMap ((ENDO_R : Nat) : ZMod pN) forgedXi)
          (foldMulOf sq2S)
          (tS.df.ez.map (fun n => (n : ZMod pN))) (tS.df.ew.map (fun n => (n : ZMod pN)))
        == Dregg2.Circuit.Emit.KimchiVerify.cipR (foldMulOf sq1S) (foldMulOf sq2S)
             (tS.df.ez.map (fun n => (n : ZMod pN)))
             (tS.df.ew.map (fun n => (n : ZMod pN)))) == false

-- ⚑⚑ **AND THE NEW HIGH CHAIN REFUSES IT.** The forced high part does not fit in 128 bits, so its
-- `EndoMulScalar` fold cannot reconstruct it and the chain's `Field.Assert.equal n scalar` fails.
-- Accepted before, REFUSED after — the same shape §12c has for R2.
#guard 2 ^ 128 ≤ forgedXiHi
#guard ((emsAccs shapeSmoke forgedXiHi).getLastD (0, 2, 2)).1 != forgedXiHi
-- …and the chain is SATISFIABLE: the honest high part fits and its own chain reconstructs it, as
-- does the honest low part (`~constrain_low_bits:true` asserts that one too, `util.ml:99`).
#guard tS.fin.xiHi < 2 ^ 128 && tS.fin.xiStmt < 2 ^ 128
#guard ((emsAccs shapeSmoke tS.fin.xiHi).getLastD (0, 2, 2)).1 == tS.fin.xiHi
#guard ((emsAccs shapeSmoke tS.fin.xiStmt).getLastD (0, 2, 2)).1 == tS.fin.xiStmt
-- …and the split is doing work: the squeeze is NOT already 128 bits, so `hi ≠ 0`.
#guard tS.fin.xiHi != 0

-- ⚑ …and the chains are wired to the PROGRAM's OWN cells, not to fresh copies. `hi` is an
-- `AOp.wit`: with the chain gone its class is ONE cell (the `hi·2¹²⁸` multiply that reads it) and
-- nothing else in the assembly touches it — so this equality, unlike a floor, cannot survive the
-- chain's deletion.
#guard (classCells posS finHiVar).length == 2
-- `xi_actual`'s four: the `sub` row that defines it, `xi_correct`'s own difference row, its σ-only
-- probe, and the new low chain's tie.
#guard (classCells posS finLoVar).length == 4
-- …and they really are the finalize program's slots, not a parallel pair: the values agree.
#guard tS.fin.vals.getD tS.fin.fp.slots.xiHi 0 == tS.fin.xiHi
#guard tS.fin.vals.getD tS.fin.fp.slots.xiActual 0 == tS.fin.xiStmt

-- ── §12d — ⚑ THE SPONGE **INPUT** IS DERIVED: `sponge_after_index` ─────────────────────────────
-- §12c and §12c′ close one half of Fiat–Shamir: GIVEN the sponge state, no challenge here is
-- prover-chosen. This is the other half. Until 2026-08-02 the plonk index the transcript starts
-- from was 58 `hmVal` fixtures no row pinned, so a prover chose the sponge's INPUT and steered every
-- squeeze without breaking a single decomposition. `step_verifier.ml:1149-1157` derives it —
-- `Sponge.absorb` of `index_to_field_elements index`, the wrap verifier key's 28 commitments — and
-- `:529-535` squeezes a copy of that sponge and absorbs the result as the transcript's FIRST word.

-- ⚑ THE 56 ABSORBED WORDS ARE THE PLONK INDEX, in `index_to_field_elements` order
-- (`side_loaded_verification_key.ml:159-183`: `sigma_comm @ coefficients_comm @` six selectors).
#guard Dregg2.Bridge.MinaStepPrevCommitments.INDEX_XY.length == N_IDX_COMMS
#guard (List.range N_IDX_WORDS).all (fun i =>
  idxWordAt i == Dregg2.Bridge.MinaStepPrevCommitments.INDEX_WORDS.getD i 0)

-- ⚑ …AND 27 OF THE 28 **ARE THE FOLD'S OWN `.const` BASES** — the plonk index the sponge hashes and
-- the plonk index `combine_split_commitments` multiplies by are ONE object, not two copies that
-- agree today. Stated at `shapeStep`: the smoke shape's 3 IPA rounds cannot reach round 40, so it
-- pins all 28 itself, which is why the σ pins below are smoke and the census pins are step.
#guard (List.range N_IDX_COMMS).countP (fun k => idxSrc shapeStep k != none) == 27
#guard idxOwn shapeStep == [6]
-- …and the smoke shape reaches exactly ONE of them (round 4 = `generic_comm`, index commitment 22),
-- so both legs of `idxVar` are exercised at both scales.
#guard idxOwn shapeSmoke == (List.range N_IDX_COMMS).filter (fun k => k != 22)
#guard (List.range N_IDX_COMMS).all (fun k =>
  match idxSrc shapeStep k with
  | some r => ipaSrc shapeStep r == BaseSrc.const
              && REAL_IPA_XY.getD r (0, 0)
                 == Dregg2.Bridge.MinaStepPrevCommitments.INDEX_XY.getD k (0, 0)
  | none => k == 6)
-- …27 DISTINCT rounds, so two index words cannot be quietly sharing one base.
#guard ((List.range N_IDX_COMMS).filterMap (idxSrc shapeStep)).dedup.length == 27
-- ⚑ …and there is now NO constant fold round the index census fails to claim: the fold's 27
-- constants are EXACTLY the plonk index minus `sigma_comm[6]`, because the twenty-eighth —
-- `COMBINE_XY[3]`, `ft_comm` — stopped being a constant when §6b computed it. (This pin read
-- `== [2]` until 2026-08-02; that `2` was the residue, and it is the round §6b writes.)
#guard ((List.range shapeStep.ipaRounds).filter (fun r =>
          ipaSrc shapeStep r == BaseSrc.const
          && !(((List.range N_IDX_COMMS).filterMap (idxSrc shapeStep)).contains r))) == []
-- …and the 28th index commitment, `sigma_comm[6]`, is the one `Vector.split m.sigma_comm` hands to
-- `Common.ft_comm` as `sigma_comm_last` (`common.ml:243-246`) — hence pinned here and not routed.
#guard idxSrc shapeStep 6 == none && idxRoundOf 6 == none

-- ⚑ SEGMENT C's `Not_opt` PREFIX **IS** `sponge_after_index`. Its state after the 28 index blocks
-- is exactly the state the copy's `Sponge.squeeze_field` produces (`:531-532`) — the 28th
-- permutation is the one that squeeze TRIGGERS (`sponge.ml:322-325`), and segment C's own block 27
-- already performs it. ⚑ CORRECTED 2026-08-03: this said `index_digest` is "one more permutation of
-- that state", i.e. a 29th, which is not what a lazy sponge does. `…Pins18` states the fix against
-- `Ref.hash`, the o1js-KAT'd machine, and refutes the old value.
#guard tS.segC.states.getD (N_IDX_WORDS / 2) [] == idxAfterState
#guard idxDigestState == idxAfterState
#guard indexDigest == idxDigestState.getD 0 0
-- …and it is not degenerate: the state moved off zero, the digest is nonzero, and it is a DIFFERENT
-- value from segment C's own final squeeze (which absorbs 30 more words after it).
#guard idxAfterState != [0, 0, 0]
#guard indexDigest != 0
#guard indexDigest != (tS.segC.states.getLastD []).getD 0 0

-- ⚑ THE WIRES. Each pinned index coordinate is read by its `Inner_curve.constant` row and by
-- segment C's own absorb row — two cells, an equality, so deleting either leg reds.
-- ⚑ …with TWO exceptions the census names. Commitment 22 owns NO variable at this shape — `idxVar`
-- routes it to the fold's round-4 base, which is the whole substance of §3c. And commitment 6,
-- `sigma_comm_last`, is also §6b's term-0 BASE: `FTC_CHUNKS` `VarBaseMul` reads, the doubling's two
-- and the odd-branch add's one, on top of the pin row and segment C's absorb.
#guard (List.range N_IDX_COMMS).all (fun k =>
  if k == 22 then (classCells posS (vIdxX shapeSmoke k)).length == 0
                  && (classCells posS (vIdxY shapeSmoke k)).length == 0
  else if k == 6 then (classCells posS (vIdxX shapeSmoke k)).length == FTC_CHUNKS + 5
                      && (classCells posS (vIdxY shapeSmoke k)).length == FTC_CHUNKS + 5
  else (classCells posS (vIdxX shapeSmoke k)).length == 2
       && (classCells posS (vIdxY shapeSmoke k)).length == 2)
#guard idxVar shapeSmoke 22 0 == ipx shapeSmoke (qT shapeSmoke constR0)
#guard (classCells posS (idxVar shapeSmoke 22 0)).length == shapeSmoke.ipaBlocks + 4

-- …and `index_digest`'s three lanes. ⚑ SINCE 2026-08-03 THESE ARE SEGMENT C's OWN block-28 state
-- cells (`vIdxD` is `sgSt … 28 j`): the copy's `squeeze` performs segment C's block-27 permutation
-- and nothing more, so there is no digest block of its own. Lane 0's FOUR cells are that block's
-- closing `Zero` row, block 28's absorb row, the σ-only probe on the state — AND R1's block-0
-- absorb row, which is the whole point and what a `.length ≥ 2` floor would not have caught.
#guard (classCells posS (vIdxD shapeSmoke 0)).length == 4
#guard (classCells posS (vIdxD shapeSmoke 1)).length == 3
#guard (classCells posS (vIdxD shapeSmoke 2)).length == 3
#guard ((classCells posS (vIdxD shapeSmoke 0)).filter (fun c => c.row < nTrans)).length == 1

-- the helper reproduces the assembly's own digest on the honest word, so what follows measures the
-- grind and not a second sponge.
#guard idxDigestAtLast (idxWordAt (N_IDX_WORDS - 1)) == indexDigest

-- ⚑⚑ **THE EXHIBIT: THE GRIND SUCCEEDS.** The honest key MISSES the chosen target; the prover finds
-- an input that HITS it, by addition, in under 48 tries — and the resulting `index_digest` is a
-- different value from the honest one.
#guard indexDigest % GRIND_MOD != 0
#guard grindT != 0
#guard groundDigest % GRIND_MOD == 0
#guard groundDigest != indexDigest
#guard groundWord != idxWordAt (N_IDX_WORDS - 1)

-- ⚑⚑ **AND IT STEERS EVERY SQUEEZE.** One plonk-index word, chosen by the prover, and EVERY
-- transcript challenge moves — β, γ, α, ζ, ξ, and with them the x_hat MSM's scalars, the fold's
-- weights and `combined_inner_product`. That is Fiat–Shamir's input becoming prover-chosen, which
-- is the attack the range checks of §12c/§12c′ do not touch.
#guard (List.range shapeSmoke.chals).all (fun c =>
  chalOf shapeSmoke spGround c != chalOf shapeSmoke tS.sp c)
#guard (spGround.states.getLastD []).getD 0 0 != (tS.sp.states.getLastD []).getD 0 0

-- ⚑ **THE HOLE, ON THE EMITTED OBJECT.** The sponge itself never objects: with the ground word in
-- place, every one of segment C's blocks is still exactly `Ref.perm` of its absorbed state (or the
-- state unchanged, where the mask drops it). A `Poseidon` gate constrains the permutation and NOT
-- what was fed to it, so before §3c there was nothing in the assembly that could refuse this.
#guard (List.range tS.specC.blocks).all (fun b =>
  let ws := tS.specC.ws.set (N_IDX_WORDS - 1) (idxVar shapeSmoke 27 1, groundWord)
  let pre := segCGround.states.getD b []
  let post := if b < tS.specC.nb then
      [ fAdd (pre.getD 0 0) ((ws.getD (2 * b) (xv 0, 0)).2)
      , fAdd (pre.getD 1 0) ((ws.getD (2 * b + 1) (xv 0, 0)).2), pre.getD 2 0 ]
    else pre
  if b < tS.specC.nb && tS.specC.maskedAt b && tS.specC.keepBit b == 0 then
    segCGround.states.getD (b + 1) [] == pre
  else segCGround.states.getD (b + 1) [] == Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm post)
-- …and it really is a different sponge, so the pin above is not comparing the honest run to itself.
#guard (segCGround.states.getLastD []).getD 0 0 != (tS.segC.states.getLastD []).getD 0 0

-- ⚑⚑ **AND THE DERIVED VERSION REFUSES IT.** The pin row's OWN generic-gate body —
-- `KimchiVerify.genericGateConstraint`, proof-systems' polynomial, read-only — is 0 on the verifier
-- key's coordinates and NONZERO on the ground one. Accepted this morning, refused now.
#guard pinBody (idxPinRow 27) (idxVal 27 0, idxVal 27 1) == 0
#guard (pinBody (idxPinRow 27) (idxVal 27 0, groundWord) == 0) == false
-- …and the check is SATISFIABLE at every one of the 28, not just the one the grind used.
#guard (List.range N_IDX_COMMS).all (fun k => pinBody (idxPinRow k) (idxVal k 0, idxVal k 1) == 0)
-- ⚑ …and at the COMMITTED shape the same word is refused TWICE, because it is not a private
-- variable there: index commitment 27 is `endomul_scalar_comm`, which is fold round 9's base, so
-- bending it moves `combine_split_commitments` as well as failing round 9's own pin row.
#guard idxSrc shapeStep 27 == some 9
#guard idxVar shapeStep 27 1 == ipy shapeStep (qT shapeStep 9)
#guard REAL_IPA_XY.getD 9 (0, 0)
        == Dregg2.Bridge.MinaStepPrevCommitments.INDEX_XY.getD 27 (0, 0)

end Dregg2.Circuit.Emit.KimchiStepMain
