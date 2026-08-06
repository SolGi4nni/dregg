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
open Dregg2.Circuit.Emit.PastaField (pN)
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
(`step_main.ml:568-570`) — so these are slots `32 + j`. -/
theorem the_public_vector_is_to_datas_order_slot_by_slot :
    (((exposedVars shapeStep).getD 32 (xv 0) == bpDiv2 shapeStep 0)          -- cip, hi
     && ((exposedVars shapeStep).getD 33 (xv 0) == bpOdd shapeStep 0)        -- cip, parity
     && ((exposedVars shapeStep).getD 34 (xv 0) == bpDiv2 shapeStep 1)       -- b, hi
     && ((exposedVars shapeStep).getD 35 (xv 0) == bpOdd shapeStep 1)        -- b, parity
     && ((exposedVars shapeStep).getD 36 (xv 0) == ftcDiv2 shapeStep 1)      -- zeta_to_srs_length
     && ((exposedVars shapeStep).getD 38 (xv 0) == ftcDiv2 shapeStep 1)      -- zeta_to_domain_size
     && ((exposedVars shapeStep).getD 40 (xv 0) == ftcDiv2 shapeStep 0)      -- perm, hi
     && ((exposedVars shapeStep).getD 41 (xv 0) == ftcOdd shapeStep 0)       -- perm, parity
     && ((exposedVars shapeStep).getD 42 (xv 0) == digestBeforeEvalsVar shapeStep)
     && ((exposedVars shapeStep).getD 43 (xv 0)
           == vN shapeStep shapeStep.betaChal shapeStep.emsRows)
     && ((exposedVars shapeStep).getD 44 (xv 0)
           == vN shapeStep shapeStep.gammaChal shapeStep.emsRows)
     && ((exposedVars shapeStep).getD 45 (xv 0)
           == vN shapeStep shapeStep.alphaChal shapeStep.emsRows)
     && ((exposedVars shapeStep).getD 46 (xv 0)
           == vN shapeStep shapeStep.zetaChal shapeStep.emsRows)
     && ((exposedVars shapeStep).getD 47 (xv 0) == vXiStmt shapeStep)
     && ((List.range PP_BP_LOG2).all (fun k =>
           (exposedVars shapeStep).getD (48 + k) (xv 0)
             == vN shapeStep (shapeStep.bulletChal k) shapeStep.emsRows))
     && ((exposedVars shapeStep).getD 63 (xv 0) == vShouldVerify shapeStep)
     && ((exposedVars shapeStep).getD 64 (xv 0) == hmOutDigestVar shapeStep)
     && ((exposedVars shapeStep).getD 65 (xv 0) == vStmtWrapMsg0 shapeStep)
     && ((exposedVars shapeStep).getD 66 (xv 0) == vStmtWrapMsgs shapeStep)) = true := by
  native_decide

#assert_compiled the_public_vector_is_to_datas_order_slot_by_slot

/-- **`the_statement_slots_are_distinct_except_the_shared_zeta_power`** — ⚑ the distinctness pin
`…Pins01` used to carry as a `#guard` against `pubWords`, restated so the ONE legitimate coincidence
is named and every other one still reds. Sixty-seven slots over sixty-five variables: slots 4/6 and
5/7 are `zeta_to_srs_length` and `zeta_to_domain_size`, which upstream carries as two unconstrained
words that agree at `log2n = srs_length_log2` (`plonk_checks.ml:496-497`) and which this assembly
derives from one `ζ^n` cell (§2c's divergence, one level up). The same pair repeats in the padding
block at 36/38 and 37/39 — ⚠ no: the padding block's ten `B Field` halves are ten DISTINCT
`vStmtDummy` cells, because a padding block has no `ζ^n` to share. So the count is `67 − 2`. -/
theorem the_statement_slots_are_distinct_except_the_shared_zeta_power :
    (((exposedVars shapeStep).map varIx).eraseDups.length + 2 == STMT_WORDS
     && (exposedVars shapeStep).getD 36 (xv 0) == (exposedVars shapeStep).getD 38 (xv 0)
     && (exposedVars shapeStep).getD 37 (xv 0) == (exposedVars shapeStep).getD 39 (xv 0)
     -- …and the padding block's ten `B Field` halves are ten different cells
     && (((List.range (2 * PP_FIELDS)).map (fun j =>
           varIx ((exposedVars shapeStep).getD j (xv 0)))).eraseDups.length
         == 2 * PP_FIELDS)) = true := by
  native_decide

#assert_compiled the_statement_slots_are_distinct_except_the_shared_zeta_power

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
1's `Shifted_value.Type2` split rows left `bpRows` (`r9_opening`) for `stmtRows` (`r5_full`) because
their cells are statement slots 32–35 and the public vector is tied at the closing rung. A row
emitted in both places would put two `Field.Assert.equal`s on one class and read as harmless; a row
emitted in neither would leave four public words on cells nothing defines. This counts them in the
TOP rung's row list, where both mistakes are visible. -/
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

/-- **`the_split_pairs_recompose_their_packed_word`** — `split_field`'s identity `2·hi + is_odd = x`
(`wrap_main.ml:51-81`; `Step.Other_field.typ_unchecked`'s `~there` at `impls.ml:94-101`;
openmina's `to_high_low` at `to_field_elements.rs:226-230`) holds on the EMITTED words for all ten
`B Field` pairs — five in the real block, five in the padding one. This is what makes `w7_split` an
identity on the step proof's own public input rather than a definition of a downward-derived cell. -/
theorem the_split_pairs_recompose_their_packed_word :
    (-- every `hi` slot's successor is its parity, and the pair recomposes inside `Fp`
     ((List.range STMT_WORDS).all (fun i =>
        match slotOf i with
        | .fieldHi _ _ =>
            decide ((stepPublic tStep).getD (i + 1) 0 == 0
                    || (stepPublic tStep).getD (i + 1) 0 == 1)
              && decide (2 * ((stepPublic tStep).getD i 0).toNat
                           + ((stepPublic tStep).getD (i + 1) 0).toNat < pN)
        | _ => true))
     -- …and for the REAL block's `combined_inner_product` and `b` the recomposition IS the value the
     -- ladder multiplies by — `Field.Assert.equal (2·s_div_2 + s_odd) s`, `plonk_curve_ops.ml:290-291`
     && (2 * (stepPublic tStep).getD 32 0 + (stepPublic tStep).getD 33 0
           == envLookupAt (envIndex (circuitEnv tStep)) (vCipShift shapeStep))
     && (2 * (stepPublic tStep).getD 34 0 + (stepPublic tStep).getD 35 0
           == envLookupAt (envIndex (circuitEnv tStep)) (vBShift shapeStep))) = true := by
  native_decide

#assert_compiled the_split_pairs_recompose_their_packed_word

/-- **`the_padding_block_is_the_only_witnessed_one`** — ⚑ the honest census, so "every field derived"
is a claim with a number attached rather than a mood. The REAL block's thirty-two slots and the
`messages_for_next_step_proof` digest are variables OTHER rows define; the padding block's
thirty-two are `vStmtDummy` cells, exactly as upstream's `Unfinalized.Constant.dummy ()`
(`step_main.ml:568-570`) is a witness discharged by `wrap_main.ml:333`; and
`messages_for_next_wrap_proof` is a requested witness on BOTH sides (`step_main.ml:364-366`).

⚠ **THE ONE OBLIGATION A PADDING BLOCK CARRIES IS ITS BIT, AND IT IS NOT WITNESSED HERE**: slot 31
is `cConst 0`. The last conjunct is that. -/
theorem the_padding_block_is_the_only_witnessed_one :
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
            == (stepPublic tStep).getD (2 * f + 1) 0))) = true := by
  native_decide

#assert_compiled the_padding_block_is_the_only_witnessed_one

end Dregg2.Circuit.Emit.KimchiStepMain
