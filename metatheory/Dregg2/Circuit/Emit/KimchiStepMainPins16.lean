/-
`KimchiStepMain` pins — §21: **`multiscale_known`'s SCALARS ARE THE WRAP STATEMENT'S WORDS**, and the
retirement of simplification #2's SECOND half.

⚑ NAMED THEOREMS, NOT `#guard` (`metatheory/docs/GUARD-DISCIPLINE.md`). This module adds no guard.

## WHAT §21 IS ABOUT

§20 gave statement word `i` its own WIDTH and said, in its own closing paragraph, what it had not
done:

> Term `i`'s scalar is still `vN (msmChal i) emsRows` — a shared transcript challenge — and NOT Wrap
> statement word `i`; a 255-bit width over a value that is structurally `< 2¹²⁸` is shape-faithful
> and semantically EMPTY until the provenance lands too.

This is the provenance. `StepShape.msmChal` is DELETED; `vSN i (msmChunksAt i)` is `stmtVar i`
(Core §2c), read off `Types.Wrap.Statement.In_circuit.to_data`
(`composition_types.ml:823-880`) and `Spec.pack`'s `pack_basic` (`spec.ml:358-395`) AT SOURCE.

## ⚑ THE REALITY GATE — TWO INDEPENDENT SOURCES AT EVERY JOINT

* The ORDER and the widths: Mina's OCaml, read by hand, against the ladder census of
  `step-zkapp-proved` — the o1-labs circuit blob (§20's `x_hat_widths_are_minas_own_compiled_ladders`,
  unchanged and re-run here).
* `FT_SLOT_ZETAN` (word 2/3's cell): a LITERAL in Core against R6's own compiled program's slot,
  at the committed shape.
* Word 12's cell: `stmtVar`'s own spelled-out expression against `hmDigestVar`, which §8e derives
  from segment C's block schedule.
* The **thirty-add fold chain**: `msmLive` (this file's partition of the census) against the single
  run of THIRTY consecutive `CompleteAdd` rows in Mina's compiled step circuit. Forty terms would
  give thirty-nine.

## ⚑ WHAT §21 CORRECTS IN THE RECORD

* `pack_basic`'s `Field` arm is `` [| `Field x |] ``, **not** `` `Packed_bits (x, 255) ``
  (`spec.ml:373-374`); `multiscale_known` scales THAT case at `~num_bits:Field.size_in_bits`
  (`step_verifier.ml:159-165`). §1b's docblock said `Packed_bits` and was wrong at source. The width
  is 255 either way, so `msmBits` does not move.
* `Plonk_checks.checked` compares the list **`[ perm ]` and nothing else**
  (`plonk_checks.ml:537-544`). `zeta_to_srs_length` / `zeta_to_domain_size` are never checked
  in-circuit upstream at all — so wiring words 2/3 to R6's DERIVED `ζ^n` is strictly more
  constrained than upstream, not less, and it is the same cell §6b already feeds `ft_comm` from.
* Words 13–28 are the STEP proof's sixteen IPA challenges carried in the WRAP statement
  (`per_proof_witness.ml:66-72`, `Types.Step_bp_vec`), and `finalize_other_proof`'s `b_correct`
  folds exactly them (`step_verifier.ml:1113-1128`). They are the same sixteen this assembly's
  `deferredRows` folds, so the wire is to a value R8 already binds — not to a fresh witness.
* The scalars are `Bulletproof_challenge.pack`'s PRECHALLENGE (`Sc.inner`), so they are `vN c
  emsRows` and NOT `vLift c`. The lift is what the curve gadgets consume; the prechallenge is what
  the statement carries, and it is the one that fits a 130-bit ladder.

## ⚠ WHAT §21 DOES NOT CLOSE

**Three of the forty words have no in-circuit source** and their ladders' scalars are therefore the
prover's here: word 10 `sponge_digest_before_evaluations`, word 11 `messages_for_next_wrap_proof`,
word 39 the lookup `Opt`'s inner `Scalar Challenge`. Each is named at its own cell rather than
aliased to a convenient challenge, and word 10's absence is a MEASURABLE gap one rung out: upstream
seeds the fr-sponge with it (`step_main.ml:41-46`) and segment B here starts at `challenge_digest`.

⚑ **§22 CLOSED WORD 10 (2026-08-03).** The residue is TWO, and the theorem below is renamed to say
so. See `…Pins17`. -/
import Dregg2.Circuit.Emit.KimchiStepMainFixture

namespace Dregg2.Circuit.Emit.KimchiStepMain

open Dregg2.Circuit.Emit.KimchiTarget (KGateType)

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ### ⚑ (a) THE WIRING — every terminal counter cell is a statement word's cell. -/

/-- ⚑ **THE LADDER CLOSES ON THE STATEMENT WORD'S OWN VALUE.** `runVbm`'s counter chain ends at
`ns.getLastD`, the cell `vSN i (msmChunksAt i)` names, and that cell IS `stmtVar i`. So this equality
says the multiplier `VarBaseMul` actually used is the packed statement word — the whole content of
§21, stated on the emitted witness rather than on the wiring diagram. -/
theorem msm_counters_close_on_the_packed_statement_words :
    (List.range shapeSmoke.msmTerms).all (fun i =>
      (tS.msm.terms.getD i default).ns.getLastD 0 == scalHon i) = true := by
  native_decide
#assert_compiled msm_counters_close_on_the_packed_statement_words

/-- ⚑ **AND EVERY SCALAR FITS ITS OWN LADDER.** The chunk rows constrain `n' = 32·n + Σ bits` over
`5·msmChunksAt i` bits with `n₀` pinned to zero, so a word whose value exceeded `2^{5·chunks}` could
not close and the emitted witness would be rejected. This is the arithmetic side of "the widths can
only be taken together with the provenance": at a `Challenge` word the value is a 128-bit
prechallenge under a 130-bit ladder, at a `Field` word a field element under 255 bits. -/
theorem every_statement_word_fits_its_own_ladder :
    (List.range shapeSmoke.msmTerms).all (fun i =>
      scalHon i < 2 ^ (5 * msmChunksAt i)) = true := by
  native_decide
#assert_compiled every_statement_word_fits_its_own_ladder

/-- ⚑⚑ **AND AT THE COMMITTED SHAPE ALL FORTY FIT — the closure condition, where the widths §20
sized actually have to hold values.** Word 0's is a field element under 255 bits, word 5's a 128-bit
prechallenge under a 130-bit ladder, word 29's a 10-bit `branch_data` under 10. The zero-chunk words
carry `2^0 = 1 > 0`, which is the degenerate case stated rather than skipped. A word that overflowed
its ladder would emit a witness the prover REJECTS while every row-count and σ-class pin stayed
green — the exact failure mode `circuitEnv`'s `qPrime` regression was.

⚠ This is the ONE claim that needs `mkStep shapeStep` — the whole 11k-row assembly — because the
values are what is under test. Smoke reaches three of the forty. -/
theorem all_forty_committed_scalars_fit_their_ladders :
    (List.range shapeStep.msmTerms).all (fun i =>
      stepScalHon i < 2 ^ (5 * msmChunksAt i)) = true := by
  native_decide
#assert_compiled all_forty_committed_scalars_fit_their_ladders

/-- …and the committed assembly's own ladders really did close on them, so the scalar vector above is
not a parallel computation of what R3 used but the thing itself. -/
theorem the_committed_ladders_close_on_those_forty_words :
    (msmLive shapeStep).all (fun i =>
      (tStep.msm.terms.getD i default).ns.getLastD 0 == stepScalHon i) = true := by
  native_decide
#assert_compiled the_committed_ladders_close_on_those_forty_words

/-- ⚑ **ALL FORTY TERMINAL CELLS LEFT THE ROUND-ROBIN.** `StepShape.msmChal i = i % chals` is gone;
this is the statement that not one term still lands where it did. A partial cutover — the failure
mode this repo has hit before — would show up as a count below forty. -/
theorem every_terminal_cell_left_the_retired_round_robin :
    (List.range 40).countP (fun i =>
      stmtVar shapeStep i != vN shapeStep (i % shapeStep.chals) shapeStep.emsRows) = 40 := by
  native_decide
#assert_compiled every_terminal_cell_left_the_retired_round_robin

/-- ⚑ **FORTY WORDS, THIRTY-NINE CELLS — and the ONE collision is named, not silent.** Words 2 and 3
are `zeta_to_srs_length` and `zeta_to_domain_size`, equal field elements at
`log2n = srs_length_log2 = 16` (`plonk_checks.ml:496-497`) and ONE derived cell here where Snarky has
two unconstrained statement variables. That is a divergence in σ, stated. Any OTHER collision would
drop this count below 39. -/
theorem the_forty_words_are_thirty_nine_cells_and_the_collision_is_the_zeta_powers :
    (((List.range 40).map (stmtVar shapeStep)).eraseDups.length = 39
     ∧ stmtVar shapeStep 2 = stmtVar shapeStep 3) := by
  native_decide
#assert_compiled the_forty_words_are_thirty_nine_cells_and_the_collision_is_the_zeta_powers

/-- ⚑ **WORDS 2/3's CELL IS R6's OWN COMPILED SLOT, AND THE CONSTANT IS CHECKED AGAINST IT.**
`FT_SLOT_ZETAN` is a literal in Core; `ftProgStep.slots.zetaN` is `ftBuild`'s own numbering of the
`log2n`-fold squaring of ζ. Two sources, and the second is rebuilt at the COMMITTED shape rather
than reused from the smoke one. -/
theorem statement_words_two_and_three_are_r6s_compiled_zeta_n :
    (ftProgStep.slots.zetaN = FT_SLOT_ZETAN
     ∧ stmtVar shapeStep 2
         = aVarAt (baseFtS shapeStep) ftProgStep.prog ftProgStep.slots.zetaN
     ∧ stmtVar shapeSmoke 2 = tS.ftw.zetaV) := by
  native_decide
#assert_compiled statement_words_two_and_three_are_r6s_compiled_zeta_n

/-- ⚑ **WORD 12 IS SEGMENT C's SQUEEZE.** `stmtVar` spells the cell out of `baseSegC`/`nbC` because
`sgSt` is §8e and below it; `hmDigestVar` is §8e's own name for the same cell. The equality is the
gate between the two spellings, at BOTH committed shapes. -/
theorem statement_word_twelve_is_segment_cs_squeeze :
    (stmtVar shapeStep 12 = hmDigestVar shapeStep
     ∧ stmtVar shapeSmoke 12 = hmDigestVar shapeSmoke) := by
  native_decide
#assert_compiled statement_word_twelve_is_segment_cs_squeeze

/-- ⚑ **WORDS 13–28 ARE THE SIXTEEN CHALLENGES `b_correct` ALREADY FOLDS, AND THEY ARE THE
PRECHALLENGES.** `finalize_other_proof` runs `compute_challenges ~scalar bulletproof_challenges` on
the statement's own vector and evaluates `challenge_polynomial` at ζ and ζω over the result
(`step_verifier.ml:1113-1128`); `pack_basic`'s `Bulletproof_challenge` arm packs `Sc.inner`, the
value BEFORE that lift (`spec.ml:390-393`). So the ladder's scalar is `vN (uChal k) emsRows` and the
fold's multiplier is `vLift (uChal k)` — the SECOND conjunct is what stops a future lane from
"simplifying" the two into one and putting a `> 2¹²⁸` value under a 130-bit ladder. -/
theorem the_sixteen_bulletproof_words_are_b_corrects_own_prechallenges :
    ((List.range 16).all (fun k =>
        stmtVar shapeStep (13 + k) == vN shapeStep (shapeStep.uChal k) shapeStep.emsRows)
     ∧ (List.range 16).all (fun k =>
        stmtVar shapeStep (13 + k) != vLift shapeStep (shapeStep.uChal k))) = true := by
  native_decide
#assert_compiled the_sixteen_bulletproof_words_are_b_corrects_own_prechallenges

/-- ⚠ ⚑ **THE RESIDUE, COUNTED — TWO WORDS SINCE §22, AND WORD 10 IS NO LONGER ONE OF THEM.** Words
11 and 39 get their own cells in the statement region, and those cells occur at exactly one statement
index each — so the residue is two ladders whose scalar this circuit does not derive, and not a
shared cell quietly doing duty for several. `msmChunksAt` on them is 51 and 26, i.e. they are LADDERS
and not the nine folded-out one-bit words. Word 10's cell is now `digestBeforeEvalsVar`, R1's own
ζ-squeeze lane 1 (§22), and this pins that it is not a statement cell any more. -/
theorem exactly_two_statement_words_have_no_in_circuit_source :
    (stmtVar shapeStep 11 = vStmtWrapMsgs shapeStep
     ∧ stmtVar shapeStep 39 = vStmtLookup shapeStep
     ∧ stmtVar shapeStep 10 = digestBeforeEvalsVar shapeStep
     ∧ [11, 39].all (fun w =>
          (List.range 40).countP (fun i => stmtVar shapeStep i == stmtVar shapeStep w) == 1)
     ∧ [msmChunksAt 10, msmChunksAt 11, msmChunksAt 39] = [51, 51, 26]) := by
  native_decide
#assert_compiled exactly_two_statement_words_have_no_in_circuit_source

/-! ### ⚑⚑ (b) THE RED CONTROL — bend the word, x_hat moves; bend a challenge no word carries, it
does not. Neither held before §21. -/

/-- ⚑ **BEND A STATEMENT WORD, `x_hat` MOVES.** One added to word `w`'s value and nothing else
touched: the ladder's bits change, its output point changes, and the `complete_add` chain's last sum
— `multiscale_known`'s result, which becomes `x_hat` — changes with it. Under the retired wiring this
was a statement about a transcript challenge and said nothing about the statement at all. -/
theorem bending_a_statement_word_moves_x_hat :
    (List.range shapeSmoke.msmTerms).all (fun w =>
      xhatAt (scalBentW w) != xhatAt scalHon) = true := by
  native_decide
#assert_compiled bending_a_statement_word_moves_x_hat

/-- ⚑⚑ **AND BENDING A TRANSCRIPT CHALLENGE THAT IS NOT ONE OF THE WORDS MOVES NOTHING — WHILE THE
SAME BEND MOVES THE RETIRED WIRING.** Three legs, and the middle one is what makes the first
non-vacuous:

  1. the NEW vector under a bent challenge 0 gives the SAME `x_hat` (at the smoke shape only words
     0–2 are in range, and none of them is a prechallenge);
  2. the RETIRED round-robin under the SAME bend gives a DIFFERENT one — so the bend is real and the
     instrument is not simply blind;
  3. the two wirings do not agree in the first place.

Leg 1 alone would be satisfied by an `x_hat` that depends on nothing. -/
theorem bending_an_unread_challenge_moves_nothing_and_the_retired_wiring_moves :
    (xhatAt (scalHonBentChal 0) = xhatAt scalHon
     ∧ xhatAt (scalOldBentChal 0) ≠ xhatAt scalOld
     ∧ xhatAt scalOld ≠ xhatAt scalHon) := by
  native_decide
#assert_compiled bending_an_unread_challenge_moves_nothing_and_the_retired_wiring_moves

/-- ⚑ **AT THE COMMITTED SHAPE, BOTH DIRECTIONS.** Forty terms reach the challenge-shaped words, so
the pair can be stated where it bites: challenges 0 and 3 are β and ζ (words 5 and 8), challenge 19
is the last `bullet_reduce` prechallenge (word 28) — bending any of them MOVES the scalar vector.
Challenge 20 is `c`, `check_bulletproof`'s own squeeze, and 21/22 are ξ and r; **no statement word
carries them and bending them moves NOTHING.** Under `msmChal i = i % 23` every one of the
twenty-three moved forty terms. -/
theorem the_committed_shapes_scalar_vector_reads_exactly_the_prechallenge_words :
    (stepScal (chalInjBent 0) ≠ stepScal chalInj
     ∧ stepScal (chalInjBent 3) ≠ stepScal chalInj
     ∧ stepScal (chalInjBent 19) ≠ stepScal chalInj
     ∧ stepScal (chalInjBent 20) = stepScal chalInj
     ∧ stepScal (chalInjBent 21) = stepScal chalInj
     ∧ stepScal (chalInjBent 22) = stepScal chalInj) := by
  native_decide
#assert_compiled the_committed_shapes_scalar_vector_reads_exactly_the_prechallenge_words

/-! ### ⚑ (c) THE CONSTANT PARTITION — the nine one-bit words leave the circuit entirely. -/

/-- ⚑⚑ **THE NINE CONSTANT WORDS NO LONGER CARRY A SEED OR A FOLD ADD.** §20's
`the_constant_words_still_carry_a_seed_and_an_add` is what this replaces, and the number that decides
it is not ours: `multiscale_known` partitions on `` `Field (Constant c) | `Packed_bits (Constant c,
_) `` and folds those bases OUTSIDE the circuit (`step_verifier.ml:133-152`), so its
`List.reduce_exn` over `non_constant_part` (`:180-182`) is `|non_constant| − 1` `CompleteAdd` rows in
ONE contiguous run — and **Mina's compiled `step-zkapp-proved` has exactly one run of THIRTY**. Forty
terms would give thirty-nine. So the fold is 31 terms and 30 adds, and the seeds
(`plonk_curve_ops.ml:157`) and base pins are 31 each.

⚠ `Ops.scale_fast2' ~num_bits:1` would still emit `add_fast base base` — a one-bit VARIABLE word
costs a seed upstream too. The nine are dropped because they are `Spec.T.Constant` /
`Field.zero` (`composition_types.ml:794-812`, `spec.ml:397`), i.e. because of the PARTITION, not
because of the width. -/
theorem the_constant_words_emit_no_base_no_seed_and_no_add :
    ((msmLive shapeStep).length = 31
     ∧ (msmBaseRows shapeStep (default : MsmData)).length = 31
     ∧ ((msmRows shapeStep (default : MsmData) true).filter
          (fun r => r.kind == KGateType.completeAdd)).length = 31 + 30) := by
  native_decide
#assert_compiled the_constant_words_emit_no_base_no_seed_and_no_add

/-- …and the ladder census §20 pinned is UNCHANGED by that removal, which is the point: the nine
emitted no `VarBaseMul` row to begin with, so dropping their seeds and adds cannot move Mina's own
`51,51,51,51,51, 26,26,26,26,26, 51,51,51, 26×16, 2, 26`. -/
theorem the_ladder_census_is_untouched_by_the_partition :
    (((msmRows shapeStep (default : MsmData) true).filter
        (fun r => r.kind == KGateType.varBaseMul)).length = 982
     ∧ ((List.range 40).filter (fun i => msmChunksAt i != 0)).map msmChunksAt
         = [51, 51, 51, 51, 51, 26, 26, 26, 26, 26, 51, 51, 51,
            26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 2, 26]) := by
  native_decide
#assert_compiled the_ladder_census_is_untouched_by_the_partition

/-- ⚑ …and the SMOKE shape is unmoved in both respects — its three terms are words 0, 1 and 2, all
`Field`, so it has no constant partition at all and `r9_opening` keeps its row count. That is why the
harness fixture and every smoke row census below are untouched by (c). -/
theorem the_smoke_shape_has_no_constant_partition :
    ((msmLive shapeSmoke).length = shapeSmoke.msmTerms
     ∧ shapeSmoke.msmTerms = 3
     ∧ (List.range 3).all (fun i => msmChunksAt i == 51) = true) := by
  native_decide
#assert_compiled the_smoke_shape_has_no_constant_partition

end Dregg2.Circuit.Emit.KimchiStepMain
