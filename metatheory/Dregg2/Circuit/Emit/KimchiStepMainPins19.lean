/-
`KimchiStepMain` pins — **§19b: THE BLOCK'S OWN OPENING IS ON DISK, AND IT DOES NOT CLOSE THIS
ASSEMBLY.**

⚑ NAMED THEOREMS, NOT `#guard` (`metatheory/docs/GUARD-DISCIPLINE.md`). This module adds no guard.

The values these are stated about are in `…Fixture`; the emission is in `…Core`; the block's opening
is in `Dregg2.Bridge.MinaStepPrevCommitments`, which `…Core` already imports.

# ⚑⚑ WHAT THIS SECTION RETIRES

`solveG`'s docblock and §18b's verdict both carried the same diagnosis, in the same words:

> *"The assembly has no IPA opening to take a real `G` from."*

**That was false at HEAD.** Mina devnet block 539508's `opening` — the very proof this assembly's
`stepBases` are the commitments of — has been fully extracted since `MinaWrapOpeningGate` landed:
`sg`, `z1`, `z2`, `delta`, the fifteen `(L, R)` pairs, `srs.h`, the fifteen prechallenges. Two of
those families are ALREADY CONSUMED by the emitted rows (`GAMMA_XY` is R4 rounds 46…75; `DELTA_XY`
is the absorbed `delta`), and `MinaStepPrevCommitments` now names the other two on its own surface
(`SG_XY`, `Z1`, `Z2`, `SRS_H_XY`) so that "it is not here" cannot be said again.

**What is actually missing is a TRANSCRIPT, not a datum**, and this section names the three cells
where the two transcripts come apart. That is a different piece of work, with a different owner, and
saying so is the point: an extraction lane cannot close slot 12, and a lane briefed to extract would
have found the data already there and had nothing to report.

# ⚑ THE SHAPE OF THE MISS

`check_bulletproof`'s closing equation (`step_verifier.ml:325-337`) is

    lhs = Scalar_challenge.endo q c + delta        rhs = z₁·(sg + b·u) + z₂·H

and the two sides read **seven** inputs. Measured on the committed shape `shapeStep`:

| input | this assembly | block 539508 | agree |
|---|---|---|---|
| `H` | `GENERATORS_H` | `SRS_H_XY` | ⚑ **YES** |
| the fold's BASES | `stepBases` | `LAGRANGE/COMBINE/GAMMA_XY` | ⚑ **YES**, by construction |
| `delta` | absorbed, unwired | `DELTA_XY` | **YES** as a datum |
| `t = challenge_fq()` | `uSqueezeVal` | `T_FQ` | **NO** |
| `u = group_map t` | `bpUOf` | `U_BASE` | **NO** (a function of the row above) |
| `b` | `bActualOf`, shifted | `B0` | **NO** |
| `(sg, z₁, z₂)` | SOLVED off `lhs` | `SG_XY`, `Z1`, `Z2` | — the thing at issue |

So the assembly holds the block's POINTS and squeezes its own SCALARS, and `lhs` is therefore this
assembly's `c·Q + delta` and not the block's. `bpCloses` at the block's own `(sg, z₁, z₂)` is
**false** below, and it is false for the reason the table gives rather than for an unlocated one.

⚠ ⚑ **AND THE ROUTE THAT LOOKS LIKE AN ESCAPE IS THE SAME WALL.** §19's rows are the `.opening`
rung's, and the rung that is EMITTED and PROVED is `.finalize` — so `equal_g` is not a constraint of
the step proof at all, and one could set `G := SG_XY`, leave `verified` the free witness it already
is at `.finalize`, and move segment D's word 54 onto the block's real accumulator. That closes
nothing: `messages_for_next_step_proof.challenge_polynomial_commitments[0]` on the wire is the WRAP
proof's kimchi recursion-slot commitment, which kimchi forces to `commit(b_poly(chals))` over the
slot's OWN challenges — and those challenges are tied, since 2026-08-06, to the step statement's
published words (`step_statement_prechallenges`, the tie slot 11 rests on). For that commitment to be
`SG_XY` the step circuit's published bulletproof challenges would have to BE block 539508's fifteen.
Which is the transcript again. **Every route to slot 12 terminates at the same place**, and the last
theorem here is the arity fact that decides which of them is even expressible.

# ⚑⚑ §19c (2026-08-09) — THE TRANSCRIPT HALF CLOSES; WHAT REMAINS IS NOT A TRANSCRIPT

Measured on the assembly's own generator (`mkStepAtAdvice`, `mkStepWith`'s second pass at a
supplied advice pair), against the same block:

  * Feed the sponge the ONE absorbed pair that was not already the block's — `absorb_fr`'s real
    stream `(CIP_SHIFTED/2, CIP_SHIFTED%2)` in the `oCip` slot — and the assembly's own run
    squeezes the block's ENTIRE opening transcript: `t = T_FQ`, `group_map t = U_BASE`, all
    fifteen prechallenges `= IPA_PRECHALS`, `c′ = C_PRE`. The other 115 absorbed words were
    already the block's; the SCHEDULE needed no repair, only the fused advice value did. (d)

  * The block's `(sg, z₁, z₂, b₀)`, in the shifted representation §19's ladders consume, CLOSE the
    block's own `lhs` under this assembly's `bpCloses` — and a moved `sg`, `z₁` or `b` refuses.
    The predicate, the shift conventions and the algebra are exact. (e)

  * AND STILL `bpCloses` refuses on the assembly's OWN `lhs` at that corrected transcript. The
    residue is measured on the shape, not conjectured: R4 keys its 46 combine rounds on 23
    round-robin transcript cells and SUMS independent endo-scalings, where upstream Horner-nests
    ONE ξ taken from `unfinalized.deferred_values` (`scale_and_add`, `step_verifier.ml:270-299`;
    `pcs_batch.ml combine_split_commitments`); 28 of the 30 `bullet_reduce` rounds are keyed off a
    cell that is not their own round's squeeze, and the L-halves lack `endo_inv`
    (`step_verifier.ml:203-206`: the round term is `endo_inv l pre + endo r pre`); and the advice
    cells are FUSED — `vCipShift`/`vBShift` each serve the absorbed Wrap advice, R8's deferred
    word and §19's ladder scalar at once, three objects upstream keeps apart
    (`{ xi; combined_inner_product; b } = unfinalized.deferred_values`, `:1253-1255`). (f)

So the diagnosis this module opened with — "what is missing is a transcript" — was half right and
is now retired in BOTH directions: the transcript's half is CLOSED, and the remaining obstruction
is an R4 rebuild (ξ-Horner + `endo_inv` + per-round prechallenge keying) plus an advice-cell
split, not a value anyone can swap. `G` therefore STAYS `solveG`'s output **in §19's ladder** —
swapping it alone would leave `equal_g = 0` under the emitted rows, a stapled slot in place of a
closed one — and `solveG`'s docblock carries the same flag.

⚠⚑ **CORRECTED 2026-08-10: THAT SENTENCE SAID "IN SEGMENT D'S PREIMAGE", AND SEGMENT D IS NO LONGER
WHERE IT IS TRUE.** The two were one cell when this was written, so naming either named both. They
are now two (`vGx` for §19, `vGaX` for segment D), and segment D absorbs
`MinaStepOwnAccumulator.ACC_XY` — the WRAP proof's published recursion-slot commitment, which kimchi
forces to `commit(b_poly(chals))` and which `gates::gate_a2` re-derives (⚠ NOT `accumulator_check`:
that reads the WRAP record's Vesta commitment and is blind to this family). **Nothing
above is weakened by that**: this module's subject is `equal_g` and the refusal of `SG_XY`, both
unchanged, and the accumulator is emphatically not `SG_XY` — see `KimchiStepMainCore.vGaX`. What
changed is only which cell the sentence is about.
-/
import Dregg2.Circuit.Emit.KimchiStepMainFixture

namespace Dregg2.Circuit.Emit.KimchiStepMain

open Dregg2.Circuit.Emit.KimchiComposeStepFragment (jOf onCurveA)
open Dregg2.Bridge.MinaStepPrevCommitments (SG_XY SRS_H_XY DELTA_XY Z1 Z2 IPA_PRECHALS)
open Dregg2.Circuit.Emit.MinaWrapOpeningGate (T_FQ B0 U_BASE CIP_SHIFTED C_PRE)
open Dregg2.Circuit.Emit.PastaField (pN qN)

set_option autoImplicit false
set_option maxRecDepth 100000

/-- `u_base`, affine — `MinaWrapOpeningGate` carries it projective at `z = 1`. -/
def U_BASE_A : Nat × Nat := (U_BASE.1, U_BASE.2.1)

/-- ⚑⚑ **(a) THE BLOCK'S OWN OPENING DOES NOT CLOSE THIS ASSEMBLY'S `check_bulletproof` — AND THE
SOLVE DOES.**

Both polarities in one statement, because either alone is worthless: a `false` on its own could be a
broken `bpCloses`, and a `true` on its own is what §17 already measured. Stated at `shapeStep`, the
COMMITTED shape — slot 12 is about that assembly and not about the smoke one.

⚑ **`H` is pinned equal in the same breath.** `GENERATORS_H` was measured off `SRS::<Pallas>::create`
and `SRS_H_XY` is read out of the block's own opening object; if those had disagreed, the `false`
below would have been about the wrong thing entirely and would have read as evidence for a much
larger gap than the one there is. -/
theorem the_blocks_own_opening_does_not_close_this_assemblys_transcript :
    (-- the block's `(sg, z₁, z₂)`, on this assembly's `lhs`: REFUSED.
     (bpCloses (bpUOf tStep) GENERATORS_H (bpLhsOf tStep) (jOf SG_XY) (bpBOf tStep) Z1 Z2) == false
     -- …and the SOLVE, on the same `lhs`: accepted. So the predicate discriminates.
     && bpCloses (bpUOf tStep) GENERATORS_H (bpLhsOf tStep) (jOf tStep.gXY) (bpBOf tStep)
          BP_Z1_VAL BP_Z2_VAL
     -- …and it is not `H` that differs: the two sources of `srs.h` are one point.
     && GENERATORS_H == SRS_H_XY
     -- …and `sg` is a real point of the field the ladder runs in, so "it was refused because the
     -- base is not on the curve" is excluded.
     && onCurveA SG_XY
     -- …and it is not the point the assembly emits, which is what makes the first leg a MISS rather
     -- than a tautology about two names for one number.
     && SG_XY != tStep.gXY) = true := by
  native_decide

#assert_compiled the_blocks_own_opening_does_not_close_this_assemblys_transcript

/-- ⚑⚑ **(b) THE THREE CELLS WHERE THE TWO TRANSCRIPTS COME APART, NAMED.**

`t` is `challenge_fq()`, the FULL squeeze that `group_map` is applied to; `u` is that map's output;
`b` is `advice.b`, R8's statement word. Every other operand of the closing equation is a point this
assembly takes from the block. So the miss in (a) is located at three cells and not "somewhere in the
sponge" — which is the difference between a next lane having a target and having a search.

⚠ `u` is a FUNCTION of `t`, so the second leg is not independent evidence; it is here because `u` is
what the ladder actually consumes, and a repair that moved `t` without moving `u` would be a repair
of the wrong cell.

⚑ **AND THE POSITIVE HALF IS IN THE SAME THEOREM**, because a section that only reported disagreement
would read as "the assembly has nothing of the block's" — which is the false diagnosis this module
exists to retire. `delta` and the thirty `bullet_reduce` gammas ARE the block's, exactly. -/
theorem the_two_transcripts_differ_at_t_and_u_and_b_and_nowhere_in_the_points :
    (-- ── the three that differ ──
     uSqueezeVal shapeStep tStep.sp != T_FQ
     && bpUOf tStep != U_BASE_A
     && bpBOf tStep != B0
     -- ── and what does NOT differ: the opening's own geometry ──
     && DELTA_XY == ((Dregg2.Circuit.Emit.MinaWrapOpeningGate.DELTA).1,
                     (Dregg2.Circuit.Emit.MinaWrapOpeningGate.DELTA).2.1)
     && Dregg2.Bridge.MinaStepPrevCommitments.GAMMA_XY.length == 30
     && IPA_PRECHALS.length == 15
     -- …and `t` is a full-width squeeze on both sides, so the miss is a VALUE miss and not a width
     -- one — a truncated `t` would be a different (and much cheaper) defect.
     && decide (uSqueezeVal shapeStep tStep.sp > 2 ^ 200)
     && decide (T_FQ > 2 ^ 200)) = true := by
  native_decide

#assert_compiled the_two_transcripts_differ_at_t_and_u_and_b_and_nowhere_in_the_points

/-- ⚑⚑ **(c) THE SIXTEEN ARE A HASH PREIMAGE, NOT STATEMENT WORDS — SETTLED AT SOURCE 2026-08-10,
AND THE "MISSING `uChal 0`" WAS A THREE-FAMILY CONFLATION.**

This entry was named `the_published_statement_carries_fifteen_of_segment_ds_sixteen` and concluded
*"`uChal 0` is published NOWHERE … either the statement grows a word or the sixteenth travels out of
band"*. **Both horns are wrong**, and the name was the reason: upstream (`mina-rust @ 82480cd46`)
has **THREE** challenge vectors here, of two lengths over two fields, and no two are prefixes of one
another.

  1. **the wrap statement's SIXTEEN** — `DeferredValues<Fp>.bulletproof_challenges`, the STEP
     proof's own IPA prechallenges, RAW. `wrap.rs:397-411` takes them from
     `oracle.opening_prechallenges`; `wrap.rs:450` asserts the length is
     `BACKEND_TICK_ROUNDS_N = 16` (`mod.rs:33`, `Fp::NROUNDS` at `field.rs:105`);
     `prepared_statement.rs:126` packs **all sixteen** into the forty at **slots 13…28**.
  2. **the per-proof `Unfinalized`'s FIFTEEN** — `unfinalized.rs:103-108`'s `DeferredValues`, which
     is `Plonk<Fq>`-shaped, i.e. about a WRAP proof: the wrap proof's own IPA prechallenges, Tock,
     `BACKEND_TOCK_ROUNDS_N = 15` (`mod.rs:34`, `Fq::NROUNDS` at `field.rs:124`), read back as
     `[Fq; 15]` at `wrap.rs:688-696`. These are the entries `32·p + 16 + j`, `j < 15`.
  3. **`messages_for_next_step_proof.old_bulletproof_challenges`** — `Vec<[Fp; 16]>`
     (`transaction.rs:3746`), LIFTED by `ScalarChallenge::array_to_fields`
     (`scalar_challenge.rs:97-100`, the `to_field` endo expansion at `scalar_challenge.ml:139`).
     **This is the family segment D absorbs, and the family the marshaller's `step_pre` is.**

⚑⚑ **AND (3) IS NEVER A STATEMENT WORD, ANYWHERE.** `MessagesForNextStepProof::to_fields`
(`transaction.rs:3770-3805`) lays the sixteen beside each `sg` in a **Poseidon preimage** and only
the DIGEST is published — `four_u64_to_field` at `prepared_statement.rs:123`, the forty's **slot
12**, and one Fp through `make_public_input` (`wrap.rs:493-516`) at entry **64** of the sixty-seven.
Upstream builds that record inside the STEP circuit (`step.rs:2845-2855`) and the wrap only re-hashes
it (`wrap.rs:610-625`). So "READABLE from the emitted artifact" was never the right test for (3), and
**there is no word for the statement to grow**.

⚑ **AND `uChal 0` IS PUBLISHED — AT SLOT 13 OF THE FORTY, AND IT AGREES WITH MINA.** The assembly's
`uChal 0 … uChal 15` are family (1): `KimchiStepMainPins16` pins `stmtVar (13 + k)` to the RAW
`vN (uChal k)`, and `KimchiWrapMainPins12.the_forty_agree_at_every_slot` proves the emitted
forty differs from `WRAP_PUBLIC_INPUT_MEASURED` at slot 12 **and nowhere else** — so all sixteen,
`k = 0` included, are published AND correct against the referee. The absence measured below is an
absence from the SIXTY-SEVEN, where family (1) does not belong.

⚠ **WHAT CONJUNCT (1) ACTUALLY SHOWS IS AN ALIASING, and it is a fidelity defect of this assembly.**
Entries 48…62 are `32·1 + 16 + j`, which upstream is family (2) — the previous WRAP proof's fifteen
Tock challenges, the window `step_statement_prechallenges` reads and the one slot 11 rests on
(`KimchiWrapHackDigest.WH_ROUNDS = 15`, `KimchiWrapMainField.FIN_W_CHAL = 11`). This assembly fills
that window with `uChal 1 … uChal 15` — family (1) with its head dropped. **Sixteen laid into a
fifteen-wide window is what manufactured the "sixteenth is missing" symptom**; the statement is not
one word short, the model is one family over.

⚑ **SO THE SIXTEEN-HALF OF SLOT 12 IS A ONE-VECTOR DECISION AND NOT A STATEMENT CHANGE.** Both sides
need family (3) to name ONE object; conjunct (2) already proves all sixteen of the assembly's raw
prechallenges are wire-shaped (below `2^128`, nonzero), so the emitted vector can be handed to
`pickles_kimchi_marshal`'s `step_pre` — today a `k·0x9E3779B97F4A7C15 | 1` ladder chosen in
`prove_step` — with no extraction from either statement and no arity blocker. ⚠ **It does not close
slot 12 on its own:** cells 58–59 (`G`) remain, and those are the accumulator leg (item #11), priced
in `KimchiStepMainPins13` §18b.

⚠ **The lifted values are in no published entry either**, which is the leg that says the wire must
carry PRECHALLENGES and let `ScalarChallenge::limbs_to_field` do the lift — as `extract_bulletproof`
(`util.rs:35-56`) in fact does. A `step_pre` filled with lifted values would be a 255-bit number in a
128-bit wire slot. -/
theorem the_statement_window_is_the_wrap_sides_fifteen_not_segment_ds_sixteen :
    (let pub := stepPublic tStep
     let raw : Nat → Nat := fun k => chalOf shapeStep tStep.sp (shapeStep.uChal k)
     let lif : Nat → Nat := fun k => liftOf shapeStep tStep.sp (shapeStep.uChal k)
     -- (1) ⚠ the ALIASING: entries 48…62 — upstream's family (2), the previous WRAP proof's
     -- fifteen Tock challenges — are filled with `uChal 1 … uChal 15`, family (1) beheaded.
     (List.range 15).all (fun j => pub.getD (48 + j) 0 == (raw (j + 1) : Int))
     -- (2) ⚑ …and all sixteen raw prechallenges fit the wire's two `u64` limbs, which is what says
     -- the emitted vector can BE `step_pre` with no extraction from either statement.
     && (List.range 16).all (fun k => raw k < 2 ^ 128 && raw k != 0)
     -- (3) ⚑ …and `uChal 0` is in no entry of the SIXTY-SEVEN — where family (1) does not belong.
     -- It IS published, at slot 13 of the FORTY (`…WrapMainPins12.the_forty_agree_at_every_slot`).
     && (pub.contains (raw 0 : Int)) == false
     -- (4) …and NO lifted value is published, so the wire slot is a prechallenge slot.
     && (List.range 16).all (fun k => (pub.contains (lif k : Int)) == false)
     -- (5) …and the lift is not the identity here, or (4) would be (3) sixteen times over.
     && (List.range 16).all (fun k => lif k != raw k)
     -- (6) the shape the whole claim is about.
     && pub.length == 67 && shapeStep.bRounds == 16) = true := by
  native_decide

#assert_compiled the_statement_window_is_the_wrap_sides_fifteen_not_segment_ds_sixteen

/-- ⚑⚑ **(d) THE TRANSCRIPT HALF CLOSES: ONE REAL ABSORBED PAIR, AND THE ASSEMBLY'S OWN SPONGE
SQUEEZES THE BLOCK'S ENTIRE OPENING TRANSCRIPT.**

`tRealAdvice` is `mkStepWith`'s own second pass (`mkStepAtAdvice`) with the `oCip` absorb set to
`absorb_fr`'s real stream — `(CIP_SHIFTED/2, CIP_SHIFTED%2)`, the split `Other_field` pair
(`sponge.rs:221-252`; `MinaWrapOpeningGate.absorbFr`) — and NOTHING else changed. That this
suffices for `t`, `u`, all fifteen prechallenges AND `c′` is the measurement that retires
"the modeled sponge's absorb list is fixture data": the other 115 absorbed words and the whole
schedule were already the block's, and (b)'s three-cell miss was, on the sponge side, ONE fused
value.

⚑ `t` FALLS OUT of the assembly's own sponge run over the corrected absorb data — `uSqueezeVal` on
`tRealAdvice.sp`, the same accessor every other pin reads — not out of a constant substituted into
the squeeze slot. The two bend conjuncts are what say the pair is load-bearing in BOTH halves, and
the last conjunct keeps (a)/(b)'s contrast alive: the assembly's OWN emitted pair (R5's Horner
through the fused cell) does NOT reach `T_FQ`. -/
theorem the_transcript_half_closes_at_the_blocks_own_advice_pair :
    (-- the u-squeeze IS the block's `t`…
     uSqueezeVal shapeStep tRealAdvice.sp == T_FQ
     -- …and `u = group_map t` IS the block's `u_base`…
     && bpUOf tRealAdvice == U_BASE_A
     -- …and the fifteen `bullet_reduce` squeezes are the block's prechallenges, in order…
     && (List.range 15).all (fun k =>
          chalOf shapeStep tRealAdvice.sp (shapeStep.bulletChal k) == IPA_PRECHALS.getD k 0)
     -- …and the closing squeeze is the block's `c′`…
     && chalOf shapeStep tRealAdvice.sp shapeStep.cChal == C_PRE
     -- …and the pair is load-bearing in its FIELD half…
     && uSqueezeVal shapeStep
          (runSponge shapeStep (stepBases shapeStep)
            (CIP_SHIFTED / 2 + 1, CIP_SHIFTED % 2)) != T_FQ
     -- …and in its BIT half…
     && uSqueezeVal shapeStep
          (runSponge shapeStep (stepBases shapeStep)
            (CIP_SHIFTED / 2, 1 - CIP_SHIFTED % 2)) != T_FQ
     -- …and the assembly's own emitted pair is NOT it — the (a)/(b) miss, as the contrast.
     && uSqueezeVal shapeStep tStep.sp != T_FQ) = true := by
  native_decide

#assert_compiled the_transcript_half_closes_at_the_blocks_own_advice_pair

/-- ⚑⚑ **(e) THE BLOCK'S OWN SCALARS CLOSE THE BLOCK'S OWN `lhs` UNDER THIS ASSEMBLY'S ALGEBRA —
AND A MOVED `sg`, `z₁` OR `b` REFUSES.**

`lhsRealOpening` is `z₁·(sg + b₀·u) + z₂·H` at the block's scalars through `bpRhs` — §19's own
ladder algebra — and `MinaWrapOpeningGate.opening_relation_holds` (the 34-ladder kernel residual)
is what says the block's `c·Q + delta` IS that point, so the closing conjunct is two independent
code paths meeting, not one definition read twice. The unshift ties pin the representation:
`bpK` (add `2^255` mod `q`) really recovers `B0`, `Z1`, `Z2` from the shifted cells, and each
shifted cell fits below `pN` — the single-cell form §19's ladders read. The three refusal
conjuncts are the anti-vacuity: the predicate discriminates AT the real point. -/
theorem the_blocks_own_scalars_close_the_blocks_own_lhs :
    (-- the closure, at the block's own `(sg, b₀, z₁, z₂)` in shifted form…
     bpCloses U_BASE_A GENERATORS_H lhsRealOpening (jOf SG_XY) B0_SHIFTED Z1_SHIFTED Z2_SHIFTED
     -- …the three unshift ties…
     && (2 ^ 255 + B0_SHIFTED) % qN == B0
     && (2 ^ 255 + Z1_SHIFTED) % qN == Z1
     && (2 ^ 255 + Z2_SHIFTED) % qN == Z2
     -- …the cells are single-`Fp`-cell representable…
     && decide (B0_SHIFTED < pN) && decide (Z1_SHIFTED < pN) && decide (Z2_SHIFTED < pN)
     && onCurveA lhsRealOpening
     -- …and a moved `sg` / `z₁` / `b` refuses, so the predicate discriminates here.
     && bpCloses U_BASE_A GENERATORS_H lhsRealOpening (jOf sgAlt)
          B0_SHIFTED Z1_SHIFTED Z2_SHIFTED == false
     && bpCloses U_BASE_A GENERATORS_H lhsRealOpening (jOf SG_XY)
          B0_SHIFTED ((Z1_SHIFTED + 1) % qN) Z2_SHIFTED == false
     && bpCloses U_BASE_A GENERATORS_H lhsRealOpening (jOf SG_XY)
          ((B0_SHIFTED + 1) % qN) Z1_SHIFTED Z2_SHIFTED == false) = true := by
  native_decide

#assert_compiled the_blocks_own_scalars_close_the_blocks_own_lhs

/-- ⚑⚑ **(f) AND STILL IT REFUSES — BUT THE RESIDUE IS NO LONGER THE FOLD'S SHAPE. RENAMED WITH THE
ROW REWIRING (2026-08-09), NOT ANNOTATED.**

This theorem was `…_and_the_residue_is_the_fold` and its two count conjuncts measured R4's
round-robin keying — 23 distinct cells across the 46 combine rounds, 2 of 30 bullet halves on their
own squeeze. **Those conjuncts stopped describing anything the day `runIpa` was rewired**: they are
facts about a retired expression, and leaving them in a live theorem would have been a falsifier
that stopped falsifying. `StepShape.ipaChal` is deleted; §19d's wiring is what the rows emit; and
the poles that refute the OLD shape live in `…Pins19d`, where they are red controls rather than
descriptions.

What is left, and it is smaller and named: at the corrected transcript the assembly's own `lhs` is
still not the block's, and `bpCloses` at the block's `(sg, z₁, z₂, b₀)` still refuses — for TWO
reasons, both conjuncts here.

  * **ξ's INSTANCE.** The fold now Horner-nests one ξ, but the ξ it nests is the assembly's own
    §8g chain 0 (`defc.pre 0` — the lift of `vXiStmt`, tied by R8's `xi_correct` to a fr-sponge
    running over FIXTURE evaluations), and that is not the block's ξ′. Segment B over the block's
    own evaluations is what would close it. ⚑ MEASURED IN `…Pins19d`, not here — see the conjunct
    comment below for why the import stays out of this module.
  * **THE FUSED ADVICE CELL.** R8's `Fp` fold (`bpBOf`, what the fused `vBShift` cell must carry)
    is neither the block's `b₀` nor its shifted form, at any transcript.

⚠ What this theorem does NOT license, unchanged: swapping `G := SG_XY` **in §19's ladder** while
this refusal stands would publish a foreign opening over `equal_g = 0` — a stapled slot. §19's `G`
stays `solveG`'s output until ξ's instance and the advice-cell split land; `solveG`'s docblock
carries the same flag, dated.

⚠⚑ **AND `SG_XY` IS STILL NOT WHAT SEGMENT D TOOK IN 2026-08-10.** Segment D now absorbs
`MinaStepOwnAccumulator.ACC_XY`, `⟨b_poly_coefficients(u⃗), get_srs::<Fp>().g⟩` at the assembly's own
sixteen. That is a DERIVED object of this pipeline, not block 539508's opening: it is exactly what
kimchi forces `prev_challenges[0].comm` to be and what Mina's `accumulator_check` recomputes, which
is why publishing it is required rather than optional. The `SG_XY` refusal this theorem carries is
untouched, and `KimchiStepMainCore.vGaX` states why the two roads are separate. -/
theorem the_corrected_transcript_still_refuses_and_the_residue_is_xi_and_the_fused_advice_cell :
    (-- (d)'s premise, restated on this theorem's own subject…
     uSqueezeVal shapeStep tRealAdvice.sp == T_FQ
     -- …the fold's output at that transcript is NOT the block's lhs…
     && bpLhsOf tRealAdvice != lhsRealOpening
     -- …and the block's own scalars are still refused on it…
     && bpCloses (bpUOf tRealAdvice) GENERATORS_H (bpLhsOf tRealAdvice) (jOf SG_XY)
          B0_SHIFTED Z1_SHIFTED Z2_SHIFTED == false
     -- …the rewired fold is nonetheless upstream's SHAPE: every combine round runs at ONE cell…
     && ((List.range (nCombine shapeStep)).map
           (fun r => ipaLadderCounter shapeStep r)).eraseDups.length == 1
     -- …and both halves of every `bullet_reduce` pair run at that pair's OWN squeeze…
     && (List.range 15).all (fun j =>
          ipaLadderCounter shapeStep (nCombine shapeStep + 2 * j)
            == vN shapeStep (shapeStep.bulletChal j) shapeStep.emsRows
          && ipaLadderCounter shapeStep (nCombine shapeStep + 2 * j + 1)
            == vN shapeStep (shapeStep.bulletChal j) shapeStep.emsRows)
     -- …so what is left is an INSTANCE and not a shape. ⚑ The ξ half is stated NEXT DOOR, in
     -- `…Pins19d.the_emitted_rows_are_the_rebuilt_fold`, and deliberately not here: naming the
     -- block's ξ′ needs `MinaWrapXiEndoLift`, whose import closure is 182 modules against this
     -- file's 186 — and importing it for one constant would put a whole second cone behind every
     -- one of THIS module's `native_decide`s. Pins19d already carries that cone.
     -- …what IS here is the other half: the fused `b` cell cannot say the block's `b₀` at ANY
     -- transcript, which needs nothing but this file's own fixture.
     && bpBOf tRealAdvice != B0_SHIFTED
     && bpBOf tRealAdvice != B0) = true := by
  native_decide

#assert_compiled the_corrected_transcript_still_refuses_and_the_residue_is_xi_and_the_fused_advice_cell

end Dregg2.Circuit.Emit.KimchiStepMain
