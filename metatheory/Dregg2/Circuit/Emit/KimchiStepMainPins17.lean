/-
`KimchiStepMain` pins — §22: **THE fr-SPONGE's SEED ABSORB**, and Wrap statement word 10 stops being
prover-chosen.

⚑ NAMED THEOREMS, NOT `#guard` (`metatheory/docs/GUARD-DISCIPLINE.md`). This module adds no guard.

## WHAT §22 IS ABOUT

§21 made `multiscale_known`'s scalars the Wrap statement's own words and named its residue in its own
closing paragraph:

> word 10's absence is a MEASURABLE gap one rung out: upstream seeds the fr-sponge with it
> (`step_main.ml:41-46`) and segment B here starts at `challenge_digest`.

This is that rung, and it turned out to be two facts rather than one.

## ⚑⚑ READ AT SOURCE, AND BOTH HALVES ARE FREE

**(1) THE SEED.** `step_main.ml:41-46` is exactly what §21 said:

    let sponge_digest = proof_state.sponge_digest_before_evaluations in
    let sponge = let sponge = Sponge.create sponge_params in
                 Sponge.absorb sponge (`Field sponge_digest) ; sponge in
    finalize_other_proof … ~sponge …

so `finalize_other_proof` is handed a sponge that has ALREADY eaten Wrap statement word 10, and its
own absorbs (`step_verifier.ml:962-965`) start at `challenge_digest` on top of that. `frSpec` now
carries the seed as word 0; the segment absorbs 5 + 2·43 = **91** field elements.

**(2) THE WORD IS A CELL THIS TRANSCRIPT ALREADY COMPUTES — and §21 recorded the opposite.** §21's
note said `sponge_digest_before_evaluations_actual` "is a different object … compared against
`unfinalized`'s copy at `:1269-1271`, not against this statement word." The comparison is real
(`step_verifier.ml:1271-1272`), but this assembly holds ONE cell per statement field where upstream
holds a `proof_state` copy and an `unfinalized` copy — the same identification it already makes for
ξ, whose single `vXiStmt` serves both `finalize_other_proof`'s `deferred_values.xi` and
`incrementally_verify_proof`'s `~xi`. Under that identification `:1271` IS a wire from word 10 to
`incrementally_verify_proof`'s returned digest, and `Field.Assert.equal` on two plain variables emits
no row at all (`Union_find.union`) — it is a σ class.

And the digest costs no permutation either. Mina's sponge is a LAZY rate-2 state machine
(`snarky/sponge/sponge.ml:294`, `rate = m − capacity = 3 − 1 = 2`):

    | Squeezed n -> if n = rate then (permute; Squeezed 1; state.(0))
                    else (Squeezed (n+1); state.(n))          (`:314-321`)
    | Absorbed _ -> permute; Squeezed 1; state.(0)            (`:322-325`)

ζ at `:568` is a `Sponge.squeeze` on an `Absorbed` state: it permutes and returns `state.(0)`. The
`squeeze_field` at `:574` then finds `Squeezed 1`, `n ≠ rate`, and takes the `else` branch — **no
permutation, `state.(1)`.** ζ and `sponge_digest_before_evaluations` are lane 0 and lane 1 of ONE
permutation output, and this assembly's ζ-squeeze block already emits both lanes.

So word 10 needed no new variable, no new row and no new block. It needed to be NAMED
(`digestBeforeEvalsVar`, §2b) and to be FED to the fr-sponge (`frSpec`'s seed).

## ⚑ WHAT §22 CORRECTS IN THE RECORD

* `verify_one` DOES consume `sponge_digest_before_evaluations_actual` — `step_verifier.ml:1271-1272`
  asserts it equal to a statement copy. §2b's docblock said "nothing here consumes it".
* **Word 11 is not an absence of this assembly.** `step_main.ml:85` substitutes it from
  `verify_one`'s argument, and that argument is `exists … ~request:Req.Messages_for_next_wrap_proof`
  at **`step_main.ml:364-366`** — a requested WITNESS of the whole step circuit. Upstream derives it
  nowhere; its only in-circuit consumer upstream is the same x_hat ladder it has here. Faithful as it
  stands.
* **Word 39 was probed and the probe was REFUTED, which is why it is still open.** `Spec.pack`'s
  `Opt` `None` arm (`spec.ml:123-128`) packs `dummy2` = `Sc.create lookup_parameters.zero.var
  .challenge`, and `step_main.ml:91` sets that to `Field.zero`; a `` `Packed_bits (Constant 0, _) ``
  is dropped outright by `multiscale_known`'s partition (`step_verifier.ml:138-140`), which would
  make word 39 a CONSTANT with no ladder. **Mina's own compiled `step-zkapp-proved` says otherwise:**
  its x_hat cluster is `2×1 26×22 51×8` = 31 ladders / 982 chunks, and `26×22` is five challenge
  words + sixteen bulletproof words + ONE MORE — word 39. So the `None` arm is not what that circuit
  compiles, the ladder is live, and closing word 39 needs the lookup sub-circuit this assembly does
  not model. The inference is recorded because it was made, not because it held.

## ⚠ WHAT §22 DOES NOT CLOSE

* **Word 11** — see above: prover-chosen here AND upstream.
* ✅ **Word 39** — SETTLED at source by §23: it is `lookup.joint_combiner.inner`, the `Opt`'s
  `Scalar Challenge` under the `Maybe` arm, and it is a REQUESTED WITNESS of the whole step circuit
  (`step_main.ml:353-355`) that `lookup_verification_enabled = false` (`step_verifier.ml:12`) leaves
  derived NOWHERE upstream either. **Faithful as it stands — word 11's verdict.** See `…Pins18`.
* ✅ **THE SPONGE MODEL WAS EAGER WHERE MINA'S IS LAZY — CLOSED BY §23 (`…Pins18`), 2026-08-03.**
  §22 read the `Squeezed n` branch for one cell and named the rest as its own rung. It was THREE
  divergences, not two: one extra permutation per squeeze; ξ′/r′ two permutations apart; and the item
  stream paired per SOURCE rather than per ITEM, which is what the transcript's `msgVal` pad lane was.
  The transcript now permutes `⌈117/2⌉ = 59` at upstream's 21 squeezes (60 at this file's 23), the
  pre-fix count was `absorbs + chals` = 80 / 82, and `index_digest` lost a 29th permutation it had
  over 56 EVEN absorbed words. See `…Pins18`.
-/
import Dregg2.Circuit.Emit.KimchiStepMainFixture

namespace Dregg2.Circuit.Emit.KimchiStepMain

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ### ⚑ (a) THE WIRING — word 10 is a cell the circuit DERIVES, and the fr-sponge EATS it. -/

/-- ⚑⚑ **WORD 10 IS R1's OWN ζ-SQUEEZE LANE 1.** `stmtVar` spells the cell out of the block schedule
(`vSt s (sqStBlock s zetaChal) 1`) because `digestBeforeEvalsVar` is §1c and `stmtVar` is §2c;
the equality is the gate between the two spellings, at BOTH committed shapes. And the lane is not
some free cell: lane 0 of the SAME state is ζ itself, which is the whole content of
`step_verifier.ml:573-574` reading `state.(1)` where `:568` read `state.(0)`. -/
theorem statement_word_ten_is_r1s_own_zeta_squeeze_lane_one :
    (stmtVar shapeStep 10 = digestBeforeEvalsVar shapeStep
     ∧ stmtVar shapeSmoke 10 = digestBeforeEvalsVar shapeSmoke
     ∧ digestBeforeEvalsVar shapeStep
         = vSt shapeStep (sqStBlock shapeStep shapeStep.zetaChal) 1
     ∧ uSqueezeVar shapeSmoke ≠ digestBeforeEvalsVar shapeSmoke) := by
  native_decide
#assert_compiled statement_word_ten_is_r1s_own_zeta_squeeze_lane_one

/-- ⚑⚑ **AND THE fr-SPONGE'S FIRST ABSORBED WORD IS THAT CELL** (`step_main.ml:45`). Both halves —
the VARIABLE and the VALUE — because a segment that absorbed the right variable carrying a different
number would emit a witness the prover rejects, and one that absorbed the right number under a
different variable would be a σ class to nothing. -/
theorem the_fr_sponges_seed_is_that_same_cell :
    ((tS.specB.ws.getD 0 (xv 0, 0)).1 = digestBeforeEvalsVar shapeSmoke
     ∧ (tS.specB.ws.getD 0 (xv 0, 0)).2 = sdS
     ∧ scalHon 10 = sdS
     ∧ (tS.specB.ws.getD 1 (xv 0, 0)).1
         = sgSt (baseSegA shapeSmoke) (nbA shapeSmoke) 1 tS.specA.blocks 0) := by
  native_decide
#assert_compiled the_fr_sponges_seed_is_that_same_cell

/-- ⚑ **AND THE SEED IS THE SAME IN BOTH TRANSCRIPT PASSES**, which is why it closes no cycle.
`mkStepWith` runs the transcript twice — once at `cip = 0` to reach the fr-sponge, once carrying the
real `combined_inner_product` — and the `cip` absorb is block `oCip`, AFTER ζ's squeeze
(`step_verifier.ml:256` vs `:568`). So the state this word is read out of is identical across the
two, and the second pass cannot move the seed the first pass fed the fr-sponge. -/
theorem the_seed_is_identical_across_both_transcript_passes :
    digestBeforeEvalsVal shapeSmoke spNoCip = sdS := by
  native_decide
#assert_compiled the_seed_is_identical_across_both_transcript_passes

/-- ⚑ **THE PAD LANE IS SEGMENT B's OWN PINNED CELL, AND VARIABLE ZERO LEFT THE SEGMENT.** 91 is odd,
so the last absorb block has an empty lane 1. `segRows`' addend default used to be `xv 0` — the
TRANSCRIPT's own pinned init lane — so the first odd segment this assembly ever emitted would have
wired a σ class from segment B's last block into R1's block-0 state. `sgPad` is the segment's own
reserved cell, it occurs in exactly two rows (the `w = 0` pin and the addend), and `xv 0` occurs in
none. -/
theorem the_pad_lane_is_pinned_and_variable_zero_left_segment_b :
    (((segRows (baseSegB shapeSmoke) tS.specB tS.segB true).any
        (fun r => r.perm.contains (some (xv 0)))) = false
     ∧ ((segRows (baseSegB shapeSmoke) tS.specB tS.segB true).countP
         (fun r => r.perm.contains (some (sgPad (baseSegB shapeSmoke) (nbB shapeSmoke) 2)))) = 2
     ∧ sgPad (baseSegB shapeSmoke) (nbB shapeSmoke) 2
         = xv (baseSegB shapeSmoke + 3 * (nbB shapeSmoke + 3) + 11 * nbB shapeSmoke)
     ∧ baseSegC shapeSmoke - baseSegB shapeSmoke = segVarCount (nbB shapeSmoke) 2) := by
  native_decide
#assert_compiled the_pad_lane_is_pinned_and_variable_zero_left_segment_b

/-! ### ⚑⚑ (b) THE RED CONTROL, BOTH DIRECTIONS — with the RETIRED WIRING as the middle leg. -/

/-- ⚑⚑ **BEND WORD 10, THE fr-SPONGE MOVES — AND UNDER THE RETIRED SEEDLESS WIRING THE SAME BEND
MOVES NOTHING.** Four legs, and the middle two are what make the first non-vacuous:

  1. the seed bent by one moves BOTH squeezes of segment B — ξ′ and r′;
  2. **the RETIRED wiring** (`specBNoSeed`, `frSpec` as it stood before 2026-08-03: the fr-sponge
     starting at `challenge_digest`) does not move under the same bend, because the word it would
     have to read is not in its list at all;
  3. …and the two wirings do not agree in the first place, so leg 2 is a blindness and not a
     coincidence;
  4. the multipliers the C8 fold actually uses — §8g's LIFTED ξ and r — move with the squeezes.

Leg 1 alone would be satisfied by a squeeze that depends on everything, and leg 2 alone by a wiring
that computes nothing. -/
theorem bending_word_ten_moves_the_fr_sponge_and_the_retired_wiring_is_blind :
    (frSq1Bent 0 ≠ frSqueezeVal tS.segB tS.specB
     ∧ frSq2Bent 0 ≠ frSqueeze2Val tS.segB tS.specB
     ∧ frSqueezeVal segBNoSeedBentSeed specBNoSeed = frSqueezeVal segBNoSeed specBNoSeed
     ∧ frSqueeze2Val segBNoSeedBentSeed specBNoSeed = frSqueeze2Val segBNoSeed specBNoSeed
     ∧ frSqueezeVal tS.segB tS.specB ≠ frSqueezeVal segBNoSeed specBNoSeed
     ∧ (runDefc (segBBent 0) tS.specB).lift shapeSmoke 0 ≠ tS.defc.lift shapeSmoke 0
     ∧ (runDefc (segBBent 0) tS.specB).lift shapeSmoke 1 ≠ tS.defc.lift shapeSmoke 1) := by
  native_decide
#assert_compiled bending_word_ten_moves_the_fr_sponge_and_the_retired_wiring_is_blind

/-- ⚑⚑ **AND R8 REFUSES IT.** The prover moves Wrap statement word 10 and nothing else; the fr-sponge
is re-run and every other input, `vXiStmt` above all, stays honest. `xi_correct` compares
`lowest_128_bits` of the moved squeeze against the unmoved statement word, the comparison fails, and
the `out` slot R8's last row asserts equals 1 comes out ZERO. The honest instance's own `out` is 1 in
the same breath, so this is a refusal and not a program that never accepts.

⚠ Note what this is and is not. It does not say word 10 is DERIVED — that is
`statement_word_ten_is_r1s_own_zeta_squeeze_lane_one`, which says the cell is R1's. It says that
having become a consumed word, moving it alone is refused. -/
theorem r8_refuses_a_bent_word_ten :
    (tS.fin.vals.getD tS.fin.fp.slots.out 0 = 1
     ∧ finOutAtBentSeed = 0
     ∧ xiActualOf (frSq1Bent 0) ≠ tS.fin.xiStmt) := by
  native_decide
#assert_compiled r8_refuses_a_bent_word_ten

/-- ⚑⚑ **THE DERIVATION, BOTH DIRECTIONS: WORD 10 IS A FUNCTION OF EXACTLY THE TRANSCRIPT PREFIX
THROUGH ζ.** Bending the last `t_comm` chunk — absorbed at `step_verifier.ml:567`, one block before
ζ's squeeze at `:568` — MOVES the digest; bending `combined_inner_product`, absorbed at `:256` which
is AFTER ζ, does NOT. That pair is the content of "`Sponge.squeeze_field` at `:574` reads the state
ζ's permutation left": a digest that moved with the `cip` absorb would be a later state's, and one
that did not move with `t_comm` would be nobody's. -/
theorem word_ten_is_the_transcript_prefix_through_zeta_and_no_more :
    (sdPreZetaBent ≠ sdS ∧ sdPostZetaBent = sdS) := by
  native_decide
#assert_compiled word_ten_is_the_transcript_prefix_through_zeta_and_no_more

/-- ⚑ **THE SPONGE IS ORDER-SENSITIVE AND THE SEED IS FIRST.** Swapping the seed with
`challenge_digest` — the same two words, the other way round — gives a different squeeze. So "the
seed absorb landed" is a claim about POSITION 0 and not merely about the word being present
somewhere in the list, which is the failure a re-ordering refactor would introduce silently. -/
theorem the_seed_is_first_and_the_order_is_load_bearing :
    frSqueezeVal (runSeg { tS.specB with
        ws := (tS.specB.ws.set 0 (tS.specB.ws.getD 1 (xv 0, 0))).set 1
                (tS.specB.ws.getD 0 (xv 0, 0)) }) tS.specB
      ≠ frSqueezeVal tS.segB tS.specB := by
  native_decide
#assert_compiled the_seed_is_first_and_the_order_is_load_bearing

/-! ### ⚑ (c) THE x_hat SIDE — at the COMMITTED shape, where forty terms exist. -/

/-- ⚑⚑ **BENDING WORD 10 MOVES `multiscale_known`'s SCALAR VECTOR, AT EXACTLY ONE INDEX — TEN.**
§21 made term `i`'s scalar the statement's word `i`; this says the word whose provenance §22 supplied
is the one that moved, and that supplying it did not smear across the other thirty-nine. The smoke
shape carries three terms and cannot state this at all — words 0–2 are all it reaches. -/
theorem bending_word_ten_moves_the_scalar_vector_at_index_ten_alone :
    ((List.range 40).filter (fun i =>
        (stepScalSd chalInj (SD_PROBE + 1)).getD i 0 ≠ (stepScalSd chalInj SD_PROBE).getD i 0)
       = [10]) := by
  native_decide
#assert_compiled bending_word_ten_moves_the_scalar_vector_at_index_ten_alone

/-- ⚑ **AND NO TRANSCRIPT CHALLENGE MOVES IT.** The other direction of the same wire: word 10's
scalar is the DIGEST, a full 255-bit `Digest` lane, and not one of the `chalBits`-masked squeezes
`chalOf` hands out — so bending any of the twenty-three challenges leaves index 10 alone. Under a
round-robin `msmChal` every challenge moved every word, which is exactly the shape §21 retired. -/
theorem no_transcript_challenge_moves_word_tens_scalar :
    (List.range shapeStep.chals).all (fun c =>
      (stepScalSd (chalInjBent c) SD_PROBE).getD 10 0
        == (stepScalSd chalInj SD_PROBE).getD 10 0) = true := by
  native_decide
#assert_compiled no_transcript_challenge_moves_word_tens_scalar

/-- ⚑ **THE COUNT, RESTATED WHERE A READER WILL LOOK FOR IT: TWO OF THE FORTY REMAIN
PROVER-CHOSEN.** Word 10 left the statement region entirely — its cell is R1's — and words 11 and 39
still hold their own cells, each occurring at exactly one statement index.

⚠ ⚑ **THE `N_STMT = 22` CONJUNCT IS NOW `N_STMT_WRAP` AND THE REGION GREW, WHICH IS §24 AND NOT A
REGRESSION.** The number this theorem was about is the WRAP statement's cell count, and its point was
that word 10's deletion was a deletion. That is still `N_STMT_WRAP = 22`. What changed is that the
same region now also holds the STEP statement's own cells — the padding block's `PP_WORDS` and
`messages_for_next_wrap_proof.(0)` — so `N_STMT` is `N_STMT_WRAP + PP_WORDS + 1`. Reading the
deletion off `N_STMT` would now report the growth as a failure of the deletion; reading it off
`N_STMT_WRAP` says what it always meant, and the second conjunct pins the arithmetic so a future
widening of either half cannot be mistaken for the other. -/
theorem the_residue_is_two_words_and_the_statement_region_shrank :
    (N_STMT_WRAP = 22
     ∧ N_STMT = N_STMT_WRAP + Dregg2.Circuit.Emit.PicklesStepStatement.PP_WORDS + 1
     ∧ (List.range 40).countP (fun i => stmtVar shapeStep i == vStmtWrapMsgs shapeStep) = 1
     ∧ (List.range 40).countP (fun i => stmtVar shapeStep i == vStmtLookup shapeStep) = 1
     ∧ (List.range 40).countP (fun i => stmtVar shapeStep i == digestBeforeEvalsVar shapeStep) = 1
     ∧ ((List.range 40).map (stmtVar shapeStep)).eraseDups.length = 39) := by
  native_decide
#assert_compiled the_residue_is_two_words_and_the_statement_region_shrank

end Dregg2.Circuit.Emit.KimchiStepMain
