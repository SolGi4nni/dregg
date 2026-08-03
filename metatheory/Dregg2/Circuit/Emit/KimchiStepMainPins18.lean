/-
`KimchiStepMain` pins — **§12s, THE LAZY SPONGE**, and §23's word-39 verdict.

# ⚑⚑ THE RUNG: our sponge was EAGER where Mina's is LAZY, and it moved every segment

§22 read `snarky/sponge/sponge.ml`'s `Squeezed n` branch for the first time and named the divergence
without fixing it. This module is the fix's exhibit. The mechanism, verbatim (`sponge.ml:280-326`,
`rate = m − capacity = 3 − 1 = 2` at `:294`):

    let absorb t x = match t.sponge_state with
      | Absorbed n -> if n = rate then (block_cipher; add_assign 0 x; Absorbed 1)
                      else (add_assign n x; Absorbed (n + 1))
      | Squeezed _ -> add_assign 0 x ; Absorbed 1
    let squeeze t = match t.sponge_state with
      | Squeezed n -> if n = rate then (block_cipher; Squeezed 1; state.(0))
                      else (Squeezed (n + 1); state.(n))
      | Absorbed _ -> block_cipher ; Squeezed 1 ; state.(0)

**The permutation is triggered by an ARRIVING element and never on the way out.** Three consequences,
all three of which this file had wrong until 2026-08-03:

1. a squeeze from `Absorbed _` SUPPLIES the pending block's permutation — it does not add one;
2. a SECOND consecutive squeeze is free (`state.(1)`), and only a third permutes again;
3. an absorb from `Squeezed _` lands in lane 0 without permuting, so the rate counter restarts at
   every squeeze and the item stream re-pairs — `index_digest` shares block 0 with `sg_old[0]`'s x.

⚑ **THE REALITY GATE IS `PastaPoseidon.Ref`, WHICH IS o1js-KAT'd AND ALREADY CARRIES THIS SCAR.**
`Ref.absorbFrom`'s own header records that an EAGER variant "permuted twice on every input of nonzero
EVEN length" and failed **exactly the two even-length o1js gold vectors**, `[123456789, 987654321]`
and `[p−1, p−1]`. `index_digest_is_the_o1js_katted_hash` below is that same test at `verify_one`
scale: `sponge_after_index` absorbs 56 (EVEN) field elements and the copy's squeeze is its 28th
permutation, not a 29th — and the pre-fix value is exhibited as a REFUTATION, not merely absent.

# ⚑ §23 — WORD 39, READ AT SOURCE, AND THE ANSWER IS THE SAME AS WORD 11's

§22 inferred word 39 was `Spec.pack`'s `Opt` `None` arm — a dropped constant — then refuted its own
inference against Mina's compiled blob and stopped. Read at source, the arm is **`Maybe`**, and
everything follows:

* **Word 39 is `lookup.joint_combiner.inner`**, the `Opt`'s `Struct [Scalar Challenge]`
  (`composition_types.ml:655-665`; `Lookup.t = { joint_combiner }` at `:82,85`). 128 bits, 26 chunks.
* **The arm is `Maybe`, not `None`.** `use = Plonk_checks.lookup_tables_used d.feature_flags`
  (`step_main.ml:88-92`) and the `proved` rule's only predecessor is the SIDE-LOADED tag
  (`transaction_snark.ml:2111-2112`), whose eight feature flags are all `Opt.Flag.Maybe`
  (`transaction_snark.ml:609-620`). Under `Maybe` the value is a witness `Field.t`, not
  `Cvar.Constant`, so `multiscale_known`'s partition (`step_verifier.ml:134-151`, which drops on
  `` `Field (Constant c) | `Packed_bits (Constant c, _) `` and nothing else) does NOT drop it.
* ⚑ **IT IS A REQUESTED WITNESS OF THE WHOLE STEP CIRCUIT, DERIVED NOWHERE IN-CIRCUIT.**
  `prevs = exists (Prev_typ.f prev_proof_typs) ~request:(fun () -> Req.Proof_with_datas)`
  (`step_main.ml:353-355`); `Per_proof_witness.typ … ~feature_flags` carries
  `deferred_values.plonk.lookup` (`per_proof_witness.ml:60-77,145-168`), and `step_main.ml:83-86`
  re-wraps that very object as the statement. The only place a `joint_combiner` could be DERIVED is
  dead: `let lookup_verification_enabled = false` (`step_verifier.ml:12`) makes it
  `if lookup_verification_enabled then failwith "TODO" else None` (`:631-633`), and
  `assert_eq_deferred_values` then receives `joint_combiner = None` on BOTH sides and asserts only
  β, γ, α, ζ (`:634-648`, `:342-363`). `wrap_verifier.ml:12,486` is the mirror image.
  **So word 39 is FAITHFUL AS IT STANDS — prover-chosen here and prover-chosen upstream, exactly as
  word 11 turned out to be (`step_main.ml:364-366`).** There is nothing to derive.

⚠ **AND TWO CORRECTIONS TO §21/§22's READING OF THE SAME CENSUS.**

* `2×1 26×22 51×8` is **chunks × count**: ONE ladder of 2 chunks (`branch_data`, 10 bits), 22 of 26,
  8 of 51 = **31 ladders / 982 chunks**. §22 read it as "2 ladders of 1 chunk", which would make the
  ladder count 32. `msmChunksAt` was already right; the prose was not.
* ⚑ **THE NINE ONE-BIT WORDS ARE NOT DROPPED CONSTANTS.** §1b says they are, and gives
  `multiscale_known`'s constant partition as the reason. At the side-loaded tag every flag is
  `Maybe`, so `maybe_constant` yields `Spec.T.B Bool` and NOT `Spec.T.Constant`
  (`composition_types.ml:794-802`), and the `Opt` header at `Maybe` packs `p.pack Bool b` — a
  witness (`spec.ml:137-140`). `constant_part` is **EMPTY** in this circuit. The nine are live
  **ZERO-CHUNK ladders**: `chunks_needed ~num_bits:(1−1) = 0`, so they emit no scale chunks but
  still emit two `add_fast`es, an `EC_scale` with an empty round array and the
  `2·s_div_2 + s_odd = s` tie (`plonk_curve_ops.ml:202-208,291`). The chunk census is unchanged and
  the emitted ROWS are not: Mina has **40** ladders where this assembly emits 31. That is a named
  residue with a corrected mechanism, not a closure.
-/
import Dregg2.Circuit.Emit.KimchiStepMainFixture

namespace Dregg2.Circuit.Emit.KimchiStepMain

open Dregg2.Circuit.Emit.KimchiTarget (KGateType)

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ### ⚑ (a) THE PERMUTATION COUNT — exhibited on the emitted object, both directions. -/

/-- The committed shape with upstream's OWN squeeze count (21) rather than the 23 this file still
allocates for the round-robin ξ/r sharing (§2b). At 21 every squeeze run has length ≤ 2, which is
the regime in which `⌈items/2⌉` is exact. -/
def shapeStep21 : StepShape := { shapeStep with chals := 21 }

/-- ⚑⚑ **MINA PERMUTES `⌈items/2⌉` TIMES, AND SO DOES THIS TRANSCRIPT NOW.** At upstream's own 21
squeezes the transcript performs exactly `⌈117/2⌉ = 59` permutations — the number `absorbBlocksNeeded`
has named since 2026-08-02 without the emission agreeing with it. -/
theorem the_transcript_permutes_ceil_items_over_two :
    (tBlocks shapeStep21 = absorbBlocksNeeded
     ∧ absorbBlocksNeeded = (N_ABSORB_ITEMS + 1) / 2
     ∧ tBlocks shapeStep21 = 59
     ∧ N_ABSORB_ITEMS = 117) := by native_decide
#assert_compiled the_transcript_permutes_ceil_items_over_two

/-- ⚑⚑ **AND THE PRE-FIX MODEL DIFFERS — BY 21 AT UPSTREAM'S SQUEEZE COUNT, BY 22 AT THIS SHAPE'S.**
The eager count was `absorbs + chals`: one permutation per absorb block PLUS one per squeeze. This
is the RED CONTROL for the whole rung, stated as the two numbers and their difference rather than as
"the model changed". ⚑ The 23rd squeeze (`r`, the third consecutive after `c` and ξ) DOES permute —
`Squeezed 2 = rate` — which is why `shapeStep` is 60 and not 59, and why the difference is 22 and
not 23. -/
theorem the_eager_model_permuted_more_and_this_is_by_how_much :
    (shapeStep21.absorbs + shapeStep21.chals = 80
     ∧ tBlocks shapeStep21 = 59
     ∧ shapeStep.absorbs + shapeStep.chals = 82
     ∧ tBlocks shapeStep = 60
     ∧ shapeSmoke.absorbs + shapeSmoke.chals = 18
     ∧ tBlocks shapeSmoke ≠ shapeSmoke.absorbs + shapeSmoke.chals) := by native_decide
#assert_compiled the_eager_model_permuted_more_and_this_is_by_how_much

/-- ⚑ **EVERY BLOCK IS A PERMUTATION AND EVERY SQUEEZE IS A READ.** The layout's own closure: the
number of `Poseidon` blocks R1 emits equals `tBlocks`, no squeeze owns a block, and every squeeze
reads a state some block produced (`sqStBlock c ≤ tBlocks`) at lane 0 or lane 1 — never a third. -/
theorem every_squeeze_reads_an_existing_state_lane :
    ((List.range shapeStep.chals).all (fun c =>
        sqStBlock shapeStep c ≤ tBlocks shapeStep && sqStLane shapeStep c < RATE)
     ∧ (List.range shapeSmoke.chals).all (fun c =>
        sqStBlock shapeSmoke c ≤ tBlocks shapeSmoke && sqStLane shapeSmoke c < RATE)) := by
  native_decide
#assert_compiled every_squeeze_reads_an_existing_state_lane

/-- ⚑⚑ **A SECOND CONSECUTIVE SQUEEZE COSTS NOTHING — β AND γ ARE TWO LANES OF ONE PERMUTATION.**
`let beta = sample () in let gamma = sample ()` (`step_verifier.ml:563-564`) with no absorb between
them, so the second finds `Squeezed 1`, `n ≠ rate`, and takes the `else` branch. α (which follows an
absorb) does not, and neither does ζ. -/
theorem beta_and_gamma_are_two_lanes_of_one_permutation :
    (sqStBlock shapeStep shapeStep.gammaChal = sqStBlock shapeStep shapeStep.betaChal
     ∧ sqStLane shapeStep shapeStep.betaChal = 0
     ∧ sqStLane shapeStep shapeStep.gammaChal = 1
     ∧ sqStBlock shapeStep shapeStep.alphaChal ≠ sqStBlock shapeStep shapeStep.gammaChal
     ∧ sqStLane shapeStep shapeStep.alphaChal = 0
     ∧ sqStLane shapeStep shapeStep.zetaChal = 0) := by native_decide
#assert_compiled beta_and_gamma_are_two_lanes_of_one_permutation

/-- …and they are DIFFERENT field elements, so "one permutation" is not "one challenge". -/
theorem beta_and_gamma_are_still_distinct_challenges :
    (chalOf shapeSmoke tS.sp shapeSmoke.betaChal
       ≠ chalOf shapeSmoke tS.sp shapeSmoke.gammaChal
     ∧ sqValOf shapeSmoke tS.sp shapeSmoke.betaChal
       ≠ sqValOf shapeSmoke tS.sp shapeSmoke.gammaChal) := by native_decide
#assert_compiled beta_and_gamma_are_still_distinct_challenges

/-! ### ⚑ (b) THE SEGMENTS — `⌈words/2⌉` each, and ξ′/r′ one permutation apart no longer. -/

/-- ⚑⚑ **EVERY SEGMENT PERMUTES `⌈|ws|/2⌉` TIMES.** One squeeze or two, the count is the same: the
first squeeze supplies the last absorb block's permutation and the second is free. It was
`⌈|ws|/2⌉ + squeezes`. -/
theorem every_segment_permutes_ceil_words_over_two :
    (tS.specA.blocks = (tS.specA.ws.length + 1) / 2
     ∧ tS.specB.blocks = (tS.specB.ws.length + 1) / 2
     ∧ tS.specC.blocks = (tS.specC.ws.length + 1) / 2
     ∧ tS.specD.blocks = (tS.specD.ws.length + 1) / 2
     ∧ tS.specB.squeezes = 2 ∧ tS.specA.squeezes = 1) := by native_decide
#assert_compiled every_segment_permutes_ceil_words_over_two

/-- ⚑⚑ **ξ′ AND r′ ARE `state.(0)` AND `state.(1)` OF ONE PERMUTATION** (`step_verifier.ml:1007-1009`,
`squeeze_challenge = lowest_128_bits (Sponge.squeeze …)` at `:186-187`). They were TWO permutations
apart. Both halves — the two VARIABLES are the two lanes of one state, and the two VALUES are that
state's two lanes — because equal variables carrying a recomputed pair would still be wrong. -/
theorem xi_and_r_are_two_lanes_of_one_fr_sponge_permutation :
    (frSqueezeVar shapeSmoke = sgSt (baseSegB shapeSmoke) (nbB shapeSmoke) 2 (nbB shapeSmoke) 0
     ∧ frSqueeze2Var shapeSmoke = sgSt (baseSegB shapeSmoke) (nbB shapeSmoke) 2 (nbB shapeSmoke) 1
     ∧ frSqueezeVal tS.segB tS.specB = (tS.segB.states.getD tS.specB.nb []).getD 0 0
     ∧ frSqueeze2Val tS.segB tS.specB = (tS.segB.states.getD tS.specB.nb []).getD 1 0
     ∧ frSqueezeVal tS.segB tS.specB ≠ frSqueeze2Val tS.segB tS.specB) := by native_decide
#assert_compiled xi_and_r_are_two_lanes_of_one_fr_sponge_permutation

/-- …and the PRE-FIX pair — lane 0 of two consecutive permutations — is a DIFFERENT pair of field
elements, so the change is measurable on the values and not only on the block count. -/
theorem the_pre_fix_fr_squeezes_were_different_field_elements :
    ((Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm
        (tS.segB.states.getD tS.specB.nb [])).getD 0 0
       ≠ frSqueeze2Val tS.segB tS.specB) := by native_decide
#assert_compiled the_pre_fix_fr_squeezes_were_different_field_elements

/-! ### ⚑ (c) `index_digest` — THE REALITY GATE, against the o1js-KAT'd reference. -/

/-- ⚑⚑ **`index_digest` IS `Ref.hash` OF THE 56 INDEX WORDS.** `Ref.hash` is `absorbAll` + lane 0,
the state machine whose nine o1js `Poseidon.hash` gold vectors `PastaPoseidon`'s §5 pins — including
both EVEN-length ones, which is precisely the case an eager sponge gets wrong. `sponge_after_index`
absorbs 56 words, so `Sponge.squeeze_field (Sponge.copy …)` (`step_verifier.ml:531-532`) performs the
28th permutation and reads `state.(0)`.

⚠ **AND THE PRE-FIX VALUE IS EXHIBITED AS A REFUTATION.** Until 2026-08-03 `indexDigest` was
`(Ref.perm idxAfterState).getD 0 0` — a 29th permutation — and the first thing the transcript
absorbs was therefore a value `Ref.hash` disagrees with. Every transcript challenge moved with it. -/
theorem index_digest_is_the_o1js_katted_hash :
    (indexDigest
       = Dregg2.Circuit.Emit.PastaPoseidon.Ref.hash
           ((List.range (2 * N_IDX_COMMS)).map idxWordAt)
     ∧ indexDigest
         ≠ (Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm idxAfterState).getD 0 0
     ∧ indexDigest ≠ 0) := by native_decide
#assert_compiled index_digest_is_the_o1js_katted_hash

/-- ⚑ …and it costs NO ROWS. The copy's squeeze is segment C's own block-27 permutation, so `vIdxD`
names segment C's block-28 state lanes and `idxDigestRows` is empty. -/
theorem the_index_digest_is_a_read_of_segment_cs_own_state :
    ((idxDigestRows shapeSmoke true).length = 0
     ∧ vIdxD shapeSmoke 0
         = sgSt (baseSegC shapeSmoke) (nbC shapeSmoke) 1 (N_IDX_WORDS / 2) 0
     ∧ tS.segC.states.getD (N_IDX_WORDS / 2) [] = idxAfterState
     ∧ msgVar shapeSmoke oDigest 0 = vIdxD shapeSmoke 0) := by native_decide
#assert_compiled the_index_digest_is_a_read_of_segment_cs_own_state

/-! ### ⚑ (d) THE PAD LANE MOVED, AND THE LAST FREE TRANSCRIPT WORD IS GONE. -/

/-- ⚑⚑ **NO TRANSCRIPT WORD IS A FREE WITNESS ANY MORE.** Every one of the `N_ABSORB_ITEMS` items is
a variable some sub-circuit reads; the one rate-2 lane an odd item count leaves without an arrival is
`tPadCell`, which is not an item at all and is pinned to zero by one `Generic` row. The old model
paired per SOURCE and put a `msgVal` FIXTURE in block 0's second lane — a word `verify_one` never
feeds the sponge, absorbed anyway.

⚑ Stated as: the pad exists, it is exactly ONE lane, it is NOT in block 0, and no absorbed item's
variable is the pad cell. -/
theorem the_transcript_has_exactly_one_pad_lane_and_no_free_word :
    ((tPadCell shapeStep).isSome
     ∧ (tPadCell shapeStep).map (·.1) ≠ some 0
     ∧ ((List.range shapeStep.absorbs).all (fun a =>
          (List.range (srcItems a)).all (fun j => msgVar shapeStep a j != vTPad shapeStep)))
     ∧ ((List.range shapeSmoke.absorbs).all (fun a =>
          (List.range (srcItems a)).all (fun j => msgVar shapeSmoke a j != vTPad shapeSmoke))))
    := by native_decide
#assert_compiled the_transcript_has_exactly_one_pad_lane_and_no_free_word

/-- ⚑ …and `index_digest` now SHARES its block with `sg_old[0]`'s x, which is the item-level pairing
made visible: `absorb sponge Field index_digest` (`:534`) feeds ONE element and
`Vector.iter ~f:(absorb sponge PC) sg_old` (`:538`) continues into lane 1 of the same block. -/
theorem the_pad_is_the_last_lane_of_the_pre_beta_run :
    (tPadCell shapeStep = some (18, 1)
     ∧ tPadCell shapeSmoke = some (3, 1)
     ∧ itemAt shapeStep (oZ shapeStep - 1) 1 = (18, 0)) := by native_decide
#assert_compiled the_pad_is_the_last_lane_of_the_pre_beta_run

/-- ⚑ …and `index_digest` now SHARES its block with `sg_old[0]`'s x. -/
theorem index_digest_shares_block_zero_with_sg_old :
    (itemAt shapeStep oDigest 0 = (0, 0)
     ∧ itemAt shapeStep oSgOld0 0 = (0, 1)
     ∧ itemAt shapeStep oSgOld0 1 = (1, 0)) := by native_decide
#assert_compiled index_digest_shares_block_zero_with_sg_old

/-! ### ⚑ (e) THE ROW COUNTS, AS EQUALITIES. -/

/-- ⚑ R1's rows: two init pins, one pad pin, one `Generic` addend per block that swallows anything,
twelve rows per permutation, and one σ-only probe per state a squeeze reads. An equality at both
shapes, so a block that stops permuting or a probe that stops being emitted reds here. -/
theorem the_transcript_row_count_is_the_layouts_own_arithmetic :
    ((transcriptRows shapeSmoke tS.sp true).length
       = 2 + 1
         + ((spLay shapeSmoke).put.map (·.1)).eraseDups.length
         + 12 * tBlocks shapeSmoke
         + (List.range (tBlocks shapeSmoke)).countP (tProbeAfter shapeSmoke)
     ∧ (transcriptRows shapeSmoke tS.sp true).length = 151
     -- …against the EAGER arithmetic, which is 237 at this shape: `2 + absorbs + 12·(absorbs+chals)
     -- + (1 + chals)`. The rung's whole row movement in R1 is this difference.
     ∧ 2 + shapeSmoke.absorbs + 12 * (shapeSmoke.absorbs + shapeSmoke.chals)
         + (1 + shapeSmoke.chals) = 237) := by
  native_decide
#assert_compiled the_transcript_row_count_is_the_layouts_own_arithmetic

/-- ⚑ …and the whole assembly's `Poseidon` census is the five sponges' permutation counts and
NOTHING else — no `+ 1` for `index_digest` any more. -/
theorem the_poseidon_census_is_five_sponges_and_no_spare_permutation :
    ((rowsS.filter (fun r => r.kind == KGateType.poseidon)).length
       = 11 * (tBlocks shapeSmoke + tS.specA.blocks + tS.specB.blocks
               + tS.specC.blocks + tS.specD.blocks)) := by native_decide
#assert_compiled the_poseidon_census_is_five_sponges_and_no_spare_permutation

/-! ### ⚑ (f) §23 — WORD 39's LADDER, AND THE NINE ZERO-CHUNK ONES. -/

/-- ⚑⚑ **THE x_hat CENSUS, READ AS `chunks × count`.** Eight 51-chunk ladders (five `Field`, three
`Digest`), twenty-two 26-chunk (β, γ, α, ζ, ξ, sixteen bulletproof challenges **and word 39, the
lookup `Opt`'s `joint_combiner`**), ONE 2-chunk (`branch_data`, 10 bits) and NINE zero-chunk (the
eight feature flags and the `Opt`'s own presence bit). 982 chunks, 31 ladders with chunks.

⚠ **AND `40 − 31 = 9` IS NOT A DROP COUNT.** Under the side-loaded tag's all-`Maybe` flags those
nine words are `Spec.T.B Bool` witnesses, so `multiscale_known`'s `constant_part` is EMPTY and Mina
emits **40** ladders — nine of them with no scale chunks but with gates. This assembly emits 31.
Named here as a residue with the corrected mechanism; §1b said "dropped constants" and that reason
was wrong at source. -/
theorem the_x_hat_ladder_census_is_chunks_times_count :
    (((List.range 40).filter (fun i => msmChunksAt i == 51)).length = 8
     ∧ ((List.range 40).filter (fun i => msmChunksAt i == 26)).length = 22
     ∧ ((List.range 40).filter (fun i => msmChunksAt i == 2)).length = 1
     ∧ ((List.range 40).filter (fun i => msmChunksAt i == 0)).length = 9
     ∧ msmChunkPrefix 40 = 982
     ∧ ((List.range 40).filter (fun i => msmChunksAt i ≠ 0)).length = 31) := by native_decide
#assert_compiled the_x_hat_ladder_census_is_chunks_times_count

/-- ⚑ **WORD 39 IS THE LOOKUP `Opt`'s `Scalar Challenge` — 128 bits, 26 chunks, and the 22nd member
of the 26-chunk family.** The Lean-side consequence of the source read in this file's header; what it
is NOT derivable from is a fact about `step_verifier.ml:12,631-648` and cannot be stated here. -/
theorem word_thirty_nine_is_the_lookup_scalar_challenge :
    (msmBits 39 = W_CHAL
     ∧ msmChunksAt 39 = 26
     ∧ ((List.range 40).filter (fun i => msmChunksAt i == 26)).getLast? = some 39
     ∧ msmBits 38 = W_BOOL ∧ msmChunksAt 38 = 0
     ∧ msmBits 29 = W_BRANCH ∧ msmChunksAt 29 = 2) := by native_decide
#assert_compiled word_thirty_nine_is_the_lookup_scalar_challenge

end Dregg2.Circuit.Emit.KimchiStepMain
