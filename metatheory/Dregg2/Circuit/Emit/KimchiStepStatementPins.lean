/-
# `KimchiStepMain` pins — §24, **the public input IS a `Types.Step.Statement`.**

`PicklesStepStatement` establishes the SHAPE at source (OCaml `composition_types.ml` +
openmina's two independent Rust implementations) and is kernel-clean. `KimchiStepMainCore` §24 is
the MAP from that shape to this assembly's variables. These are the facts about the EMITTED object.

⚑ **WHY THE WIDTH THEOREM IS THE LOAD-BEARING ONE.** The wrap circuit scales lagrange base `i` by
step public word `i` (`wrap_verifier.ml:539-609`), under `Ops.scale_fast2' ~num_bits` whose top-bit
asserts refuse an over-wide word (`plonk_curve_ops.ml:262-265`) and under
`assert_ (Constraint.boolean b)` on the one-bit entries (`:574`). A statement whose LAYOUT is right
and whose WIDTHS are not is a proof no wrap circuit can be built over.
-/
import Dregg2.Circuit.Emit.KimchiStepMainFixture

namespace Dregg2.Circuit.Emit.KimchiStepMain

open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder (envIndex envLookupAt)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PicklesStepStatement
  (PP_WORDS STMT_WORDS STMT_PREVS PP_FIELDS PP_BP_LOG2 SLOT_MSG_NEXT_STEP
   Slot slotOf slotBits realBlocks)

set_option autoImplicit false
set_option maxRecDepth 100000

/-- **`the_committed_shape_carries_a_statement_and_the_smoke_shape_says_it_does_not`** — ⚑ the
dispatch, and it is DERIVED. `carriesStatement` reads the transcript schedule: a statement needs
`PP_BP_LOG2 = 15` `bullet_reduce` squeezes to fill `bulletproof_challenges` from, and the smoke
shape's five-round IPA never reaches `combine_split_commitments`' end, so it has none. A smoke shape
that claimed a statement would name challenge cells belonging to other variables. -/
theorem the_committed_shape_carries_a_statement_and_the_smoke_shape_says_it_does_not :
    (carriesStatement shapeStep
     && !carriesStatement shapeSmoke
     && shapeStep.pubWords == STMT_WORDS
     && (exposedVars shapeStep).length == STMT_WORDS
     && (exposedVars shapeSmoke).length == shapeSmoke.pubWords
     && shapeSmoke.pubWords != STMT_WORDS
     -- …and the emitted vectors really are the two different objects
     && (exposedVars shapeStep) == stmtExposedVars shapeStep
     && (exposedVars shapeSmoke) == smokePublicVars shapeSmoke) = true := by
  native_decide

#assert_compiled the_committed_shape_carries_a_statement_and_the_smoke_shape_says_it_does_not

/-- **`the_public_vector_is_to_datas_order_slot_by_slot`** — ⚑ the MAP, spelled out for the REAL
block against `Per_proof.In_circuit.to_data` (`composition_types.ml:1279-1315`) and
`Step_verifier.verify` (`step_verifier.ml:1224-1286`), which is what ties each of them to the
transcript. Block **1** is the real one — `Vector.extend_front` puts the padding at the FRONT
(`step_main.ml:568-570`) — so these are slots `32 + j`.

⚠ ⚑⚑ **SLOTS 32–41 AND 47 MOVED ON 2026-08-07, AND THE MOVE IS THE POINT OF THIS THEOREM NOW.**
They read `bpDiv2/bpOdd 0,1`, `ftcDiv2/ftcOdd 1`, `ftcDiv2/ftcOdd 0` and `vXiStmt` — every one of
them a **WRAP statement** word (`stmtVar 0,1,2,3,4,9`), i.e. the Fp deferred values of the wrap
proof-state THIS circuit verifies, published where the Fq deferred values ABOUT that wrap proof
belong. `KimchiStepMainCore` §1f is the de-aliasing; the last two conjuncts here are the refusal
that the old cells are back, so a revert cannot pass by re-satisfying the shape. -/
theorem the_public_vector_is_to_datas_order_slot_by_slot :
    (((exposedVars shapeStep).getD 32 (xv 0) == vStmtDef shapeStep 0)        -- cip, hi
     && ((exposedVars shapeStep).getD 33 (xv 0) == vStmtDef shapeStep 1)     -- cip, parity
     && ((exposedVars shapeStep).getD 34 (xv 0) == vStmtDef shapeStep 2)     -- b, hi
     && ((exposedVars shapeStep).getD 35 (xv 0) == vStmtDef shapeStep 3)     -- b, parity
     && ((exposedVars shapeStep).getD 36 (xv 0) == vStmtDef shapeStep 4)     -- zeta_to_srs_length
     && ((exposedVars shapeStep).getD 37 (xv 0) == vStmtDef shapeStep 5)
     && ((exposedVars shapeStep).getD 38 (xv 0) == vStmtDef shapeStep 6)     -- zeta_to_domain_size
     && ((exposedVars shapeStep).getD 39 (xv 0) == vStmtDef shapeStep 7)
     && ((exposedVars shapeStep).getD 40 (xv 0) == vStmtDef shapeStep 8)     -- perm, hi
     && ((exposedVars shapeStep).getD 41 (xv 0) == vStmtDef shapeStep 9)     -- perm, parity
     -- ⚑ …and NOT the wrap statement's words, which is the defect this replaced. A `vStmtDef` map
     -- that happened to alias one of them again would satisfy every line above.
     && ((List.range (2 * PP_FIELDS)).all (fun j =>
           !((List.range 40).map (stmtVar shapeStep)).contains
              ((exposedVars shapeStep).getD (32 + j) (xv 0))))
     && !((List.range 40).map (stmtVar shapeStep)).contains
           ((exposedVars shapeStep).getD 47 (xv 0))
     && ((exposedVars shapeStep).getD 42 (xv 0) == digestBeforeEvalsVar shapeStep)
     && ((exposedVars shapeStep).getD 43 (xv 0)
           == vN shapeStep shapeStep.betaChal shapeStep.emsRows)
     && ((exposedVars shapeStep).getD 44 (xv 0)
           == vN shapeStep shapeStep.gammaChal shapeStep.emsRows)
     && ((exposedVars shapeStep).getD 45 (xv 0)
           == vN shapeStep shapeStep.alphaChal shapeStep.emsRows)
     && ((exposedVars shapeStep).getD 46 (xv 0)
           == vN shapeStep shapeStep.zetaChal shapeStep.emsRows)
     && ((exposedVars shapeStep).getD 47 (xv 0) == vStmtDef shapeStep (2 * PP_FIELDS))
     && ((List.range PP_BP_LOG2).all (fun k =>
           (exposedVars shapeStep).getD (48 + k) (xv 0)
             == vN shapeStep (shapeStep.bulletChal k) shapeStep.emsRows))
     && ((exposedVars shapeStep).getD 63 (xv 0) == vShouldVerify shapeStep)
     && ((exposedVars shapeStep).getD 64 (xv 0) == hmOutDigestVar shapeStep)
     && ((exposedVars shapeStep).getD 65 (xv 0) == vStmtWrapMsg0 shapeStep)
     && ((exposedVars shapeStep).getD 66 (xv 0) == vStmtWrapMsgs shapeStep)) = true := by
  native_decide

#assert_compiled the_public_vector_is_to_datas_order_slot_by_slot

/-- ⚑⚑ **`the_statement_slots_are_all_distinct`** — the distinctness pin `…Pins01` used to carry as
a `#guard` against `pubWords`, and it is a STRICTLY STRONGER statement than the one it replaced
(2026-08-07).

It was `the_statement_slots_are_distinct_except_the_shared_zeta_power`: `67 − 2`, with slots 36/38
and 37/39 named as one legitimate coincidence, because `zeta_to_srs_length` and
`zeta_to_domain_size` were one derived `ftcDiv2 1` cell and upstream "carries two unconstrained
words that agree at `log2n = srs_length_log2`". ⚠ **Both halves of that were wrong about this
object.** `ftcDiv2 1` is §6b's own **Fp** `ζ^n` — the WRAP statement's word 2/3 — so the shared cell
was an ALIAS across two statements and two fields, not a faithful sharing; and the wrap proof these
slots are about sits at `domain_log2 = 14` under a `2^15` tock SRS, so its two words are two
DIFFERENT field elements (`MinaWrapProofDeferredWords.the_two_zeta_powers_differ`) and no single
cell could have carried both. Sixty-seven slots over sixty-seven variables now, with no exception to
name. -/
theorem the_statement_slots_are_all_distinct :
    (((exposedVars shapeStep).map varIx).eraseDups.length == STMT_WORDS
     -- …the pair that used to be the exception is two cells and two values
     && (exposedVars shapeStep).getD 36 (xv 0) != (exposedVars shapeStep).getD 38 (xv 0)
     && (stepPublic tStep).getD 36 0 != (stepPublic tStep).getD 38 0
     -- …and BOTH blocks' ten `B Field` halves are ten different cells apiece
     && (((List.range (2 * PP_FIELDS)).map (fun j =>
           varIx ((exposedVars shapeStep).getD j (xv 0)))).eraseDups.length
         == 2 * PP_FIELDS)
     && (((List.range (2 * PP_FIELDS)).map (fun j =>
           varIx ((exposedVars shapeStep).getD (PP_WORDS + j) (xv 0)))).eraseDups.length
         == 2 * PP_FIELDS)) = true := by
  native_decide

#assert_compiled the_statement_slots_are_all_distinct

/-- **`the_step_statements_wrap_message_is_the_wrap_statements_word_eleven`** — ⚑ ONE object where
upstream has one. `step_main.ml:85` substitutes `verify_one`'s `messages_for_next_wrap_proof`
argument into the WRAP statement it builds, and that argument is the step statement's own
`messages_for_next_wrap_proof.(1)` for the block being verified. So step-statement slot 66 and wrap-
statement word 11 are the SAME cell, and a second cell for either would be two objects where the
protocol has one. ⚠ Slot 65 is the padding block's and has its own cell, as it must. -/
theorem the_step_statements_wrap_message_is_the_wrap_statements_word_eleven :
    ((exposedVars shapeStep).getD 66 (xv 0) == stmtVar shapeStep 11
     && (exposedVars shapeStep).getD 65 (xv 0) != stmtVar shapeStep 11
     && vStmtWrapMsgs shapeStep == stmtVar shapeStep 11) = true := by
  native_decide

#assert_compiled the_step_statements_wrap_message_is_the_wrap_statements_word_eleven

/-- **`the_statement_split_reads_the_ladders_own_scalar`** — §24a's two hoisted split rows are
written against `vCipShift`/`vBShift` because `bpScalV` is declared below them; this is the tie, so
the hoist is a gate between two expressions rather than a second name for one. -/
theorem the_statement_split_reads_the_ladders_own_scalar :
    bpScalV shapeStep 0 = vCipShift shapeStep
    ∧ bpScalV shapeStep 1 = vBShift shapeStep := ⟨rfl, rfl⟩

#assert_axioms the_statement_split_reads_the_ladders_own_scalar

/-- How many `Generic` HALVES of `rows` carry the split `x = 2·hi + odd` on `(x, hi)`. ⚑ Either
half: `packHalves` pairs consecutive halves, so a row's split can sit at perm 0/1/2 or at 3/4/5, and
a filter that looked only at the first half would count one of two hoisted rows and read as a
duplicate that was not there. -/
def splitHalves (rows : List SRow) (x hi : PVar) : Nat :=
  ((rows.filter (fun r =>
      (r.perm.getD 0 none == some x && r.perm.getD 1 none == some hi
        && r.coeffs.take 5 == cSplit 1)
      || (r.perm.getD 3 none == some x && r.perm.getD 4 none == some hi
        && r.coeffs.drop 5 == cSplit 1))).length)

/-- **`the_statement_split_rows_are_emitted_exactly_once`** — ⚑ MOVED, not duplicated. Ladders 0 and
1's `Shifted_value.Type2` split rows left `bpRows` (`r9_opening`) for `stmtRows` (`r5_full`), and a
row emitted in both places would put two `Field.Assert.equal`s on one class and read as harmless.
This counts them in the TOP rung's row list and at `r5_full`, where both mistakes are visible.

⚠ ⚑ **THE REASON THEY ARE HOISTED CHANGED ON 2026-08-07, THOUGH THE COUNT DID NOT.** It was *"their
cells are statement slots 32–35 and the public vector is tied at the closing rung"*; those slots are
`vStmtDef 0..3` now (`KimchiStepMainCore` §1f) and no public word names `bpDiv2`/`bpOdd 0,1` at all.
What holds the hoist up is `vCipBit = bpOdd 0`, absorbed by the transcript at every rung while the
EMITTED rung is `r8_finalize` — see §24a. Keeping the theorem while its premise changed is exactly
what this repo calls a cost verdict outliving its premise, so the premise is restated at both ends
rather than left to a reader to notice. -/
theorem the_statement_split_rows_are_emitted_exactly_once :
    (splitHalves (rungRows tStep .opening true) (vCipShift shapeStep) (bpDiv2 shapeStep 0) == 1
     && splitHalves (rungRows tStep .opening true) (vBShift shapeStep) (bpDiv2 shapeStep 1) == 1
     -- …and they are already there at the CLOSING rung, four rungs below `.opening`
     && splitHalves (rungRows tStep .full true) (vCipShift shapeStep) (bpDiv2 shapeStep 0) == 1
     && splitHalves (rungRows tStep .full true) (vBShift shapeStep) (bpDiv2 shapeStep 1) == 1) = true := by
  native_decide

#assert_compiled the_statement_split_rows_are_emitted_exactly_once

/-- ⚑⚑ **`the_public_words_respect_their_slot_widths`** — THE OBLIGATION THE WRAP CIRCUIT ENFORCES,
discharged on the emitted vector. Every 255-bit slot is a legal `Fp` element, every 128-bit slot is
`< 2^128` (`scale_fast2`'s top-bit asserts, `plonk_curve_ops.ml:262-265`), and every one-bit slot is
`0` or `1` (`Constraint.boolean`, `wrap_verifier.ml:574`). ⚠ A layout that is right and a width that
is not is a proof no wrap circuit can be built over — which is exactly the failure `x_hat`'s
`Cond_add` partition would report as an unsatisfiable witness rather than as a shape error. -/
theorem the_public_words_respect_their_slot_widths :
    ((List.range STMT_WORDS).all (fun i =>
        decide ((stepPublic tStep).getD i 0 ≥ 0)
        && decide (((stepPublic tStep).getD i 0).toNat < 2 ^ slotBits i)
        && decide (((stepPublic tStep).getD i 0).toNat < pN))) = true := by
  native_decide

#assert_compiled the_public_words_respect_their_slot_widths

/-- ⚑⚑ **`the_split_pairs_recompose_their_packed_word`** — `split_field`'s identity
`2·hi + is_odd = x` (`wrap_main.ml:51-81`; `Step.Other_field.typ_unchecked`'s `~there` at
`impls.ml:94-101`; openmina's `to_high_low` at `to_field_elements.rs:226-230`) on the EMITTED words,
for all ten `B Field` pairs.

⚠ ⚑⚑ **AND WHAT THE PAIR RECOMPOSES TO IS AN `Fq` ELEMENT, WHICH IS WHY THE SPLIT EXISTS AT ALL.**
The version of this theorem that stood until 2026-08-07 ended with two conjuncts saying the real
block's slots 32–35 recompose to `vCipShift` and `vBShift` — and those are **the WRAP statement's**
`combined_inner_product` and `b`, Fp values this circuit derives. That is the aliasing
`KimchiStepMainCore` §1f retired, written down as a green pin: *the theorem was true, about the
wrong object.* `Other_field.typ_unchecked` splits because `q > p` and an Fq word does not fit one Fp
cell; a pair whose recomposition is an Fp value it could have carried whole is the tell.

The legs, in order: every `hi` slot's successor is a BIT; every pair recomposes below `qN`, the
field the word belongs to; the live block's five recompose to `MinaWrapProofDeferredWords`' five, by
name; ⚑ and none of the five is a wrap-statement word any more — the refusal that makes a revert
red rather than merely different. The ladders' own split is a separate object and stays one:
`2·bpDiv2 0 + bpOdd 0` is still `vCipShift`, at cells no public word names. -/
theorem the_split_pairs_recompose_their_packed_word :
    (-- every `hi` slot's successor is its parity, and the pair recomposes inside `Fq`
     ((List.range STMT_WORDS).all (fun i =>
        match slotOf i with
        | .fieldHi _ _ =>
            decide ((stepPublic tStep).getD (i + 1) 0 == 0
                    || (stepPublic tStep).getD (i + 1) 0 == 1)
              && decide (2 * ((stepPublic tStep).getD i 0).toNat
                           + ((stepPublic tStep).getD (i + 1) 0).toNat < qN)
        | _ => true))
     -- …and the LIVE block's five ARE the wrap proof's own deferred words, by name
     && ((List.range PP_FIELDS).all (fun f =>
          2 * ((stepPublic tStep).getD (PP_WORDS + 2 * f) 0).toNat
            + ((stepPublic tStep).getD (PP_WORDS + 2 * f + 1) 0).toNat
          == Dregg2.Circuit.Emit.MinaWrapProofDeferredWords.FIELD_WORDS.getD f 0))
     && ((stepPublic tStep).getD 47 0
           == (Dregg2.Circuit.Emit.MinaWrapProofDeferredWords.W_XI : Int))
     -- ⚑ REFUSAL: not one of them is a WRAP statement word's value. The old theorem asserted the
     -- opposite of this for two of them and read as a tie.
     && ((List.range PP_FIELDS).all (fun f =>
          !((List.range 40).map (fun i =>
              envLookupAt (envIndex (circuitEnv tStep)) (stmtVar shapeStep i))).contains
            ((2 * ((stepPublic tStep).getD (PP_WORDS + 2 * f) 0)
               + ((stepPublic tStep).getD (PP_WORDS + 2 * f + 1) 0)))))
     -- …while the ladder's own split is untouched: `Field.Assert.equal (2·s_div_2 + s_odd) s`,
     -- `plonk_curve_ops.ml:290-291`, on cells no public word names.
     && (2 * envLookupAt (envIndex (circuitEnv tStep)) (bpDiv2 shapeStep 0)
           + envLookupAt (envIndex (circuitEnv tStep)) (bpOdd shapeStep 0)
           == envLookupAt (envIndex (circuitEnv tStep)) (vCipShift shapeStep))
     && (2 * envLookupAt (envIndex (circuitEnv tStep)) (bpDiv2 shapeStep 1)
           + envLookupAt (envIndex (circuitEnv tStep)) (bpOdd shapeStep 1)
           == envLookupAt (envIndex (circuitEnv tStep)) (vBShift shapeStep))) = true := by
  native_decide

#assert_compiled the_split_pairs_recompose_their_packed_word

/-- ⚑⚑ **`the_witnessed_slots_are_the_padding_block_and_the_live_blocks_deferred_values`** — the
honest census, so "every field derived" is a claim with a number attached rather than a mood.

⚠ ⚑ **IT WAS `the_padding_block_is_the_only_witnessed_one` AND THAT NAME BECAME FALSE ON
2026-08-07, so it is renamed rather than left to describe a tree it no longer describes.** Eleven of
the live block's thirty-two slots are witnesses now (`vStmtDef`, `KimchiStepMainCore` §1f) — the
five `B Field` deferred values and ξ. That is not a loss of derivation: it is the recognition that
those words are **Fq** deferred values about the wrap proof, which a step circuit cannot compute
(`exists ~request:Req.Proof_state` upstream) and whose checker is `wrap_main.ml:335`'s
`Boolean.Assert.any [finalized; not should_finalize]`. Deriving them here was deriving a DIFFERENT
statement's words into these slots.

The census now: the padding block's thirty-two are `vStmtDummy`, exactly as upstream's
`Unfinalized.Constant.dummy ()` (`step_main.ml:568-570`) is a witness discharged by
`wrap_main.ml:333`; the live block's eleven deferred slots are `vStmtDef`; its other twenty-one and
the `messages_for_next_step_proof` digest are variables OTHER rows define; and
`messages_for_next_wrap_proof` is a requested witness on BOTH sides (`step_main.ml:364-366`).

⚠ **THE ONE OBLIGATION A PADDING BLOCK CARRIES IS ITS BIT, AND IT IS NOT WITNESSED HERE**: slot 31
is `cConst 0`. ⚑ And BOTH blocks' five parity halves carry `b² = b`, which is the whole in-circuit
obligation on a witnessed deferred word — the last two conjuncts. -/
theorem the_witnessed_slots_are_the_padding_block_and_the_live_blocks_deferred_values :
    -- the padding block is EXACTLY slots 0..PP_WORDS−1, in order, and nowhere else
    (((List.range PP_WORDS).all (fun j =>
        (exposedVars shapeStep).getD j (xv 0) == vStmtDummy shapeStep j))
     && ((List.range PP_WORDS).all (fun j =>
          !((exposedVars shapeStep).drop PP_WORDS).contains (vStmtDummy shapeStep j)))
     -- …the padding block's `should_finalize` is DERIVED — a `cConst 0` row — and its value is 0
     && (stepPublic tStep).getD (PP_WORDS - 1) 0 == 0
     && ((rungRows tStep .full true).filter (fun r =>
          (r.perm.getD 0 none == some (vStmtDummy shapeStep (PP_WORDS - 1))
             && r.coeffs.take 5 == cConst 0)
          || (r.perm.getD 3 none == some (vStmtDummy shapeStep (PP_WORDS - 1))
             && r.coeffs.drop 5 == cConst 0))).length == 1
     -- …and the five parity halves it publishes carry `b² = b`
     && ((List.range PP_FIELDS).all (fun f =>
          (stepPublic tStep).getD (2 * f + 1) 0 * (stepPublic tStep).getD (2 * f + 1) 0
            == (stepPublic tStep).getD (2 * f + 1) 0))
     -- ⚑ …and so do the LIVE block's, which are witnesses too since §1f
     && ((List.range PP_FIELDS).all (fun f =>
          (stepPublic tStep).getD (PP_WORDS + 2 * f + 1) 0
            * (stepPublic tStep).getD (PP_WORDS + 2 * f + 1) 0
            == (stepPublic tStep).getD (PP_WORDS + 2 * f + 1) 0))
     -- ⚑ …the live block's eleven deferred slots are `vStmtDef` cells, in order, and nowhere else
     && ((List.range N_STMT_DEF).all (fun j =>
          (exposedVars shapeStep).getD (PP_WORDS + (if j == 2 * PP_FIELDS then 15 else j)) (xv 0)
            == vStmtDef shapeStep j))
     && ((List.range N_STMT_DEF).all (fun j =>
          ((exposedVars shapeStep).filter (fun v => v == vStmtDef shapeStep j)).length == 1))
     -- ⚑ …and the `b² = b` rows for both blocks' ten parity halves are emitted, ten of them
     && ((List.range PP_FIELDS).all (fun f =>
          ((rungRows tStep .full true).filter (fun r =>
             (r.perm.getD 0 none == some (vStmtDef shapeStep (2 * f + 1))
                && r.coeffs.take 5 == cMul)
             || (r.perm.getD 3 none == some (vStmtDef shapeStep (2 * f + 1))
                && r.coeffs.drop 5 == cMul))).length == 1))) = true := by
  native_decide

#assert_compiled the_witnessed_slots_are_the_padding_block_and_the_live_blocks_deferred_values

/-- ⚑⚑⚑ **`the_padding_blocks_fifteen_are_minas_own_dummy_wrap_prechallenges`** — the pad slot of
the WRAP proof's kimchi `prev_challenges` is a slot Mina's own reader REBUILDS FROM A CONSTANT, and
these fifteen emitted words are that constant's preimage.

`wrap.rs:729-737` (prover) and `prover.rs:130-140` (reader) both front-pad
`challenge_polynomial_commitments` to `Max_proofs_verified.n` with `dummy_ipa_wrap_sg()` and zip the
result, in order, against the wrap record's `old_bulletproof_challenges` — which `wrap_main.ml:421
-431` builds out of THIS block's `deferred_values.bulletproof_challenges`. `dummy_ipa_wrap_sg()` is
`commit(b_poly(Dummy.Ipa.Wrap.challenges_computed))`, and `MinaWrapHackDummySg.DUMMY_WRAP_PRECHALS`
is the prechallenge preimage of `challenges_computed` (asserted in the generator that exports both).
So these fifteen words are the ONLY values for which the pad slot Mina reconstructs is the pad slot
we committed. `gates::gate_a2` is that reconstruction run on the marshalled object; before
2026-08-10 it reported slot 0 red and no other instrument in the tree could see it, because
`accumulator_check` is a different pair entirely.

The legs, in order, and each one is a way the repair could have been done wrongly:

* the emitted vector's fifteen `.bpChallenge 0 _` words ARE `DUMMY_WRAP_PRECHALS`, in order — read
  off `stepPublic tStep`, the vector a verifier is handed, not off `stmtDummyVal`;
* `getD`'s fallback is UNREACHABLE — the list is exactly `PP_BP_LOG2` long, so no slot silently
  publishes a `0`;
* ⚑ the window the marshaller reads is these slots and not neighbours: `step_statement_pre
  challenges` takes entry `32·p + 16 + j`, and slot `16 + j` of block 0 is `.bpChallenge 0 j`;
* every one clears `marshal::ACCUMULATOR_PRECHALLENGE_MIN_BITS = 100` — a published slot's
  prechallenges are `Ro.scalar_chal ()` draws and the floor refuses anything narrower;
* ⚑⚑ **THE REFUSAL, and it is the reason the discrimination is on `slotOf`:** no OTHER 128-bit slot
  of either block carries one of these fifteen. `W_CHAL` also covers `beta`/`gamma` and
  `alpha`/`zeta`/`xi`, five slots per block that no commitment is paired with; a width-keyed rule
  would have filled them with `DUMMY_WRAP_PRECHALS` too and this conjunct would be false. -/
theorem the_padding_blocks_fifteen_are_minas_own_dummy_wrap_prechallenges :
    -- the emitted words, in order, ARE Mina's own dummy prechallenges
    (((List.range PP_BP_LOG2).all (fun k =>
        (stepPublic tStep).getD (2 * PP_FIELDS + PP_DIGESTS + PP_CHALLENGES
                                   + PP_SCALAR_CHALLENGES + k) 0
          == (Dregg2.Circuit.Emit.MinaWrapHackDummySg.DUMMY_WRAP_PRECHALS.getD k 0 : Int)))
     -- …the `getD` fallback in `stmtDummyVal` is unreachable: the list is exactly as long as the
     -- vector it fills, so no slot publishes a silent `0`
     && Dregg2.Circuit.Emit.MinaWrapHackDummySg.DUMMY_WRAP_PRECHALS.length == PP_BP_LOG2
     && !Dregg2.Circuit.Emit.MinaWrapHackDummySg.DUMMY_WRAP_PRECHALS.contains 0
     -- ⚑ …and the window the MARSHALLER reads is exactly those slots: entry `32·p + 16 + j`
     && ((List.range PP_BP_LOG2).all (fun j => slotOf (PP_WORDS * 0 + 16 + j) == .bpChallenge 0 j))
     && ((List.range PP_BP_LOG2).all (fun j => slotOf (PP_WORDS * 1 + 16 + j) == .bpChallenge 1 j))
     -- …every one clears the floor a PUBLISHED accumulator slot's prechallenges must clear
     && ((List.range PP_BP_LOG2).all (fun k =>
          decide (2 ^ 99 ≤ Dregg2.Circuit.Emit.MinaWrapHackDummySg.DUMMY_WRAP_PRECHALS.getD k 0)
            && decide (Dregg2.Circuit.Emit.MinaWrapHackDummySg.DUMMY_WRAP_PRECHALS.getD k 0
                         < 2 ^ W_CHAL)))
     -- ⚑⚑ THE REFUSAL: no OTHER 128-bit slot of either block carries one of the fifteen. This is
     -- the conjunct a `slotBits`-keyed repair makes false.
     && ((List.range STMT_WORDS).all (fun i =>
          match slotOf i with
          | .challenge _ _ | .scalarChallenge _ _ =>
              !Dregg2.Circuit.Emit.MinaWrapHackDummySg.DUMMY_WRAP_PRECHALS.contains
                ((stepPublic tStep).getD i 0).toNat
          | _ => true))) = true := by
  native_decide

#assert_compiled the_padding_blocks_fifteen_are_minas_own_dummy_wrap_prechallenges

end Dregg2.Circuit.Emit.KimchiStepMain
