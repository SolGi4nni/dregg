/-
# Dregg2.Circuit.Emit.KimchiWrapMainPins09 — §21a — W-WRAPHACK

⚑ **ONE MODULE OF THE `KimchiWrapMain` SPLIT.** The namespace is unchanged
(`Dregg2.Circuit.Emit.KimchiWrapMain`), so nothing here is renamed and no consumer moves; the file
boundary exists only so a pin re-elaborates without the emitter's 5,000 lines of `def` behind it.
The in-file rule that keeps it stable is the step side's: **a `def` goes in `…Core`/`…Fixture`, a
pin goes in its section's `…PinsNN`.**

⚠ The `set_option` block below is VERBATIM `KimchiWrapMain`'s and must stay that way. `set_option`
does not cross an import, and `KimchiWrapFinalizeSpongeGate` shipped four proofs as `sorryAx` --
each still landing in the environment with the right statement -- because a split dropped it.

Pins only. Every `def` this section had is in `…Fixture`; the namespace-wide axiom pin is in the
`KimchiWrapMain` umbrella, which imports every one of these.

-/
import Dregg2.Circuit.Emit.KimchiWrapMainFixture

namespace Dregg2.Circuit.Emit.KimchiWrapMain
open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder
  (VarEnv GateWitness gridAt envIndex envLookupAt gateVarWitnessAt compose)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaPoseidonFq (fqParams rcsQ mdsQ)

set_option autoImplicit false
set_option maxRecDepth 100000
-- ⚠ §12/§14b reduce whole sponge trajectories IN THE KERNEL (`rfl`/`decide`), which is strictly
-- stronger than the `#guard`s they replace and correspondingly slower to elaborate.
set_option maxHeartbeats 4000000

/-! ### §21a — ⚑ THE PINS ON W-WRAPHACK, and the one that is the point. -/

/-! ### §21a′ — ⚑ **THE SLOT MAP.** The public vector sits in MINA'S layout, and these are the
checks that it is Mina's and not a forty-wide vector of our own devising. -/

/-- ⚑ **THE FOUR CHALLENGE SLOTS ARE THE TRANSCRIPT'S OWN SQUEEZE ORDER, β γ α ζ.**

This is the pin the §10 census names, and it exists because a rotation here is the exact defect the
module has already shipped once: **an object of the right kind under the right name at the wrong
slot, moving nothing any width signature can see** — all four are 128-bit challenges, so a swap of β
and α changes the committed statement and NOTHING else visibly.

Two independent readings must agree and both are exhibited:

  * MINA'S side — `Wrap.Statement.to_data` (`composition_types.ml:826-880`) lays the `challenge`
    bucket (β, γ) down BEFORE the `scalar_challenge` bucket (α, ζ). That reading is
    `Dregg2.Bridge.MinaWrapPublicInput.publicInputWords`, itself a MEASURED correction against block
    539508's binprot bytes (2026-07-30), and it puts β at 5, γ at 6, α at 7, ζ at 8.
  * OURS — `schedule`'s four `.chal` squeezes are β (`wrap_verifier.ml:620`), γ (`:621`), α (`:624`),
    ζ (`:631`) in that order, and `exposedVars` indexes the chains by it.

So `wrapSlots` is `5 + i` on the first four, and the last conjunct is the ORDER's own control: the
transcript's four squeezes ARE in that order, exhibited from the schedule rather than asserted. -/
theorem the_challenge_slots_are_the_transcript_order :
    (wrapSlots shapeSmoke).take 4 = [5, 6, 7, 8]
    ∧ (wrapSlots shapeWrap).take 4 = [5, 6, 7, 8]
    ∧ ((schedule shapeWrap).filter (fun e => match e with | .sq .chal => true | _ => false)).length
        = nChals shapeWrap
    -- ⚑ AND THE GAP STRUCTURE IS THE EVIDENCE, not the naming. The schedule positions of the first
    -- four `chal` squeezes: β and γ are BACK TO BACK (`wrap_verifier.ml:620-621`, positions 35/36,
    -- nothing absorbed between them), α comes only after `z_comm`'s two absorbs (`:623-624`,
    -- position 39) and ζ after `t_comm`'s fourteen (`:630-631`, position 54). That adjacency is
    -- exactly what makes the first two the `challenge` bucket and α/ζ `scalar_challenge`s — the
    -- split `Wrap.Statement.to_data` orders slots 5-8 on.
    -- ⚠ **THE FOUR POSITIONS SHIFTED BY TWO ON 2026-08-07 AND THE ADJACENCIES DID NOT**, which is
    -- the content: `shapeWrap.maxPrevs` went 2 → 1 with `marshal::STEP_RECURSION_SLOTS`, so the
    -- transcript absorbs one `sg_old` point fewer and every squeeze after it moves two slots
    -- earlier. A `[37, 38, 41, 56]` that survived would have meant the schedule did not read
    -- `maxPrevs` at all.
    ∧ (List.range 60).filter (fun i =>
        match (schedule shapeWrap).getD i default with | .sq .chal => true | _ => false)
       = [35, 36, 39, 54] := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rfl

/-- ⚑ **AND THE WHOLE MAP IS MINA'S**, at both committed shapes: every slot the ladder ties is one
`wrap_main` itself reads, the map is injective, and at the terminal rung the tied set IS
`WRAP_PINNED_SLOTS ∪ WRAP_PASSTHROUGH_SLOTS` — **thirty** of forty, in Pickles' own positions.

⚠ **THIS SAID `WRAP_PINNED_SLOTS` AND TWENTY-FOUR UNTIL 2026-08-05, AND THAT WAS A TRUE STATEMENT
ABOUT A CIRCUIT THAT READ SIX WORDS FEWER.** The six `~advice`/`~plonk`/`~xi` pass-throughs are tied
now, so a conjunct asserting every tied slot is PINNED is FALSE — it is not a stale number, it is a
different claim, and it is stated as the union rather than widened to something vacuous.

The injectivity conjunct is what stops a silent collision: two tied words on ONE public cell would
merge two σ classes and place, prove and commit without a word of complaint. -/
theorem the_slot_map_is_minas :
    (wrapSlotsAt shapeWrap .close).all (fun i =>
      WRAP_PINNED_SLOTS.contains i || WRAP_PASSTHROUGH_SLOTS.contains i) = true
    ∧ (wrapSlotsAt shapeWrap .close).dedup.length = (wrapSlotsAt shapeWrap .close).length
    ∧ (wrapSlotsAt shapeWrap .close).length = WRAP_PINNED_WORDS + WRAP_PASSTHROUGH_SLOTS.length
    ∧ ((List.range WRAP_PRIMARY_LEN).filter
        (fun i => (wrapSlotsAt shapeWrap .close).contains i))
      = (List.range WRAP_PRIMARY_LEN).filter (fun i =>
          WRAP_PINNED_SLOTS.contains i || WRAP_PASSTHROUGH_SLOTS.contains i)
    -- ⚑ …and the six are DISJOINT from the twenty-four, so the union is a real 30 and not a
    -- relabelling of the same slots.
    ∧ (WRAP_PASSTHROUGH_SLOTS.filter (fun i => WRAP_PINNED_SLOTS.contains i)) = []
    -- …and the SMOKE shape ties a strict SUBSET — which is why a smoke-shape emission is a layout
    -- demonstration and not a closed statement.
    ∧ (wrapSlotsAt shapeSmoke .bind) = [5, 6, 7, 8, 10, 13]
    ∧ (wrapSlotsAt shapeSmoke .close).all (fun i =>
        WRAP_PINNED_SLOTS.contains i || WRAP_PASSTHROUGH_SLOTS.contains i) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ **THE DECLARED-UNREAD SET IS THE COMPLEMENT, AND IT SHRINKS UP THE LADDER TO THE DEAD TEN.**
`w4_bind` admits to eighteen; `w8_ftcomm` gives back the `ft_comm` trio (slots 4, 2, 3); `w9_prev`
gives back 12; `w11_wraphack` gives back 11; `w10_combine` gives back ξ; `w11_bullet` gives back
`combined_inner_product` and `b`; and `w12_close` lands on exactly the ten `Spec.T.Constant` /
dead-lookup slots. A ladder that stopped moving here would be a ladder that stopped deriving.

⚠ **THE FLOOR WAS SIXTEEN UNTIL 2026-08-05 AND IS TEN NOW**, because six of that sixteen were words
`wrap_main` reads and this assembly declined to tie. The terminal conjunct is the one that matters:
what is left unread at the top of the ladder is the set nothing reads UPSTREAM either. -/
theorem the_declared_unread_set_shrinks_to_the_dead_ten :
    (wrapInertOk shapeWrap .bind).length = 18
    ∧ (wrapInertOk shapeWrap .ftcomm).length = 15
    ∧ (wrapInertOk shapeWrap .prev).length = 14
    ∧ (wrapInertOk shapeWrap .wraphack).length = 13
    ∧ (wrapInertOk shapeWrap .combine).length = 13
    ∧ (wrapInertOk shapeWrap .bullet).length = 11
    ∧ (wrapInertOk shapeWrap .close).length = 10
    ∧ ((List.range WRAP_PRIMARY_LEN).filter
        (fun i => (wrapInertOk shapeWrap .close).contains i)) = WRAP_UNPINNED_SLOTS := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#assert_axioms the_challenge_slots_are_the_transcript_order
#assert_axioms the_slot_map_is_minas
#assert_axioms the_declared_unread_set_shrinks_to_the_dead_ten

/-- ⚑ **THE TAPE IS `to_field_elements`'s, AND THE ORDER IS THE FACT.**
`composition_types.ml:411-418` flattens the old bulletproof challenges FIRST and appends the
commitment's `[x; y]` LAST. The last conjunct is the red control: the same 32 values in the step
side's order give a DIFFERENT digest, so "absorbed the right values" and "absorbed them in the right
order" are two facts and this file checks both. -/
theorem wraphack_tape_is_the_challenges_then_the_commitment :
    WH_ROUNDS = 15 ∧ WH_PADDED = 2 ∧ WH_ABSORBS = 32
    -- ⚑ AT EVERY SLOT OF THE RECORD, pad and real alike — the two have the same 30+2 width, which
    -- is what `messages.rs:85-105`'s `assert_eq!(fields.len(), NFIELDS)` says with `NFIELDS = 32`.
    -- ⚠ This read `whOldChals 0 / whSgOld 0` — ONE slot, and the one that is now the PAD — so it
    -- said nothing about the slot the real accumulator is in.
    ∧ ((List.range WH_PADDED).all (fun p =>
        let g := whSlotSgAt (mkWrap shapeWrap) p
        let cs := whSlotChals WH_REAL_SLOTS p
        ((whTape cs g).length == WH_ABSORBS)
        && ((whTape cs g).getD (WH_ABSORBS - 2) 0 == g.1)
        && ((whTape cs g).getD (WH_ABSORBS - 1) 0 == g.2)
        && ((List.range (WH_MLMB * WH_ROUNDS)).all (fun k =>
              (whTape cs g).getD k 0 == cs.getD k 0)))) = true
    -- ⚠ …and the order is a FACT: the same 32 values commitment-first give a different digest.
    ∧ ((List.range WH_PADDED).all (fun p =>
        let g := whSlotSgAt (mkWrap shapeWrap) p
        let cs := whSlotChals WH_REAL_SLOTS p
        (whDigestOf cs g == whDigestCommitmentFirst cs g) == false)) = true
    -- ⚑ …and the two slots are not one object: pad ≠ real, in both halves of the tape.
    ∧ (whSlotChals WH_REAL_SLOTS 0 == whSlotChals WH_REAL_SLOTS 1) = false
    ∧ (whSlotSgAt (mkWrap shapeWrap) 0 == whSlotSgAt (mkWrap shapeWrap) 1) = false := by
  refine ⟨rfl, rfl, rfl, by decide, by decide, by decide, by decide⟩

/-- ⚑ **THE FRONT PAD IS THE FRESH STATE, AND TWO EMITTED ROWS PIN IT.** `whPadVectors` is
`2 − max_proofs_verified` in general and `0` at the committed shape, so the opening state is
`Sponge.create`'s zeros — defect class 1 in the place `wrap_hack.ml:26-28` put it. The two `cConst 0`
rows are read off the EMITTED row list, exactly as `key_sponge_seed_is_pinned` does. -/
theorem wraphack_front_pad_is_the_fresh_state_and_the_rows_pin_it :
    whPadVectors WH_MLMB = 0 ∧ whPadVectors 1 = 1 ∧ whPadVectors 0 = 2
    ∧ ((whRows tWh true).getD 0 default).coeffs = cConst 0 ++ cConst 0
    ∧ ((whRows tWh true).getD 1 default).coeffs = cConst 0 ++ cNil
    ∧ ((whRows tWh true).getD 0 default).kind = KGateType.generic
    ∧ ((whRows tWh true).getD 1 default).kind = KGateType.generic := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ **THE ALIASING REFUTATION.** `baseWh` read `basePrev + nPrevVars` — which IS `baseFtc` — while
`rungsUpto .wraphack` contains `.ftcomm`, so two regions sat at one address in a circuit holding
both. This is the gate that says they no longer do, and it is stated over the EMITTED gates rather
than over the base arithmetic: **every external id `w8_ftcomm`'s whole rung references is strictly
below where W-WRAPHACK's region starts.** A base-vs-base equation would have been a pin against its
own definition; this one goes red if any row of any rung at or below `.ftcomm` reaches up. -/
theorem wraphack_region_is_above_ftcomms :
    baseWh shapeSmoke tWh.sp = baseFtc shapeSmoke tWh.sp + nFtcVars shapeSmoke tWh.sp
    ∧ baseFtc shapeSmoke tWh.sp < baseWh shapeSmoke tWh.sp
    ∧ ((externalRefs (wrapGates (rungRows tWh .ftcomm true))).all
        (fun i => decide (i < baseWh shapeSmoke tWh.sp))) = true := by
  refine ⟨rfl, by decide, rfl⟩

/-- The emitter's allocation FORMULA is what `runSpongeQ` actually allocates, for all three sponges
— so the three regions cannot silently overlap. -/
theorem wraphack_sponge_allocation :
    WH_PERMS = 16 ∧ WH_VARS = 115
    ∧ (whSpongeP tWh 0).next = WH_VARS
    ∧ (whSpongeP tWh 1).next = WH_VARS
    ∧ (whSpongeC tWh).next = WH_VARS := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ **THE GATE: THE EMITTED SQUEEZE IS THE VALUE §15c″ COMPUTES.** §15c″ computes the three digests
as VALUES and `runSpongeQ` computes them again as a TRAJECTORY of emitted rows; this says the two
agree. A disagreement would make `whRows`' tie rows unsatisfiable and every rung at or above
`w11_wraphack` fail to prove — a red the harness finds, but a red here is cheaper and says which of
the two moved.

⚠⚑ **AND THE SECOND HALF WAS A REFUSAL FOR ONE DAY. IT IS AN EQUALITY AGAIN — BUT NOT THE ONE
IT USED TO BE, AND THE DIFFERENCE IS THE WHOLE POINT.**

Until 2026-08-06 this theorem said the squeeze IS packed statement word `55 + p`, closed by kernel
`rfl`, and it was **half decoration**: `prevWordVal` had an override arm answering `whPrevDigest p`
at exactly those two words, so one side of the equation was the other side's definition. When
`xhatScalar` moved to the step proof's own `STEP_PUBLIC_IN` the override went and the equation became
a real question, whose answer was **no** — `stepmain_step_r8_finalize` published `160000365` and
`77001823` there, `w11_wraphack`'s tie row had no satisfying witness, and the rung sat in the
harness's `STATEMENT_BLOCKED` set. That paragraph also priced the repair as a FIXPOINT ("those words
are x_hat entries 65/66 and moving them moves every challenge below"); the first clause is true and
the inference is not, and MEASURED: re-emitting moved exactly two of the sixty-seven entries and left
every other packed word alone.

⚑ **IT IS YES NOW, AND IT IS A FACT ABOUT AN EMITTED PROOF RATHER THAN ABOUT THIS FILE.**
`KimchiStepMainCore.stmtWrapMsgVal` is `whPrevDigest`, the step circuit was re-emitted and re-proved,
and `prevWordVal` still recomposes `STEP_PUBLIC_IN` with **no override at 55/56**. So the two sides
are: a Poseidon squeeze this file computes, and two entries of a public input that
`kimchi::verifier::batch_verify` accepted on Vesta. A repair that reintroduced an override would make
this `rfl`-cheap again and mean nothing — which is what the two `STEP_PUBLIC_IN` conjuncts refuse.

⚠ **WHAT RE-EMITTED:** `stepmain_step_r8_finalize.json` entries 65/66, therefore the step proof,
therefore `KimchiStepWrapChainFixture` in full and `MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED`.

⚠ `native_decide`: the kernel `rfl` that used to close leg 1 worked because both sides unfolded to
ONE term; against a numeral it has to reduce sixteen Poseidon permutations and overflows the stack. -/
theorem wraphack_digest_is_the_emitted_squeeze :
    whDigestVal (whSpongeP tWh 0) = whPrevDigest 0
    ∧ whDigestVal (whSpongeP tWh 1) = whPrevDigest 1
    ∧ whDigestVal (whSpongeC tWh) = whCloseDigest tWh.sh
    -- ⚑⚑ …and the published statement CARRIES them (2026-08-06). This is the tie `whRows`
    -- emits at packed words 55 and 56, evaluated against the step proof's own public input.
    ∧ whPrevDigest 0 = prevWordVal (PREV_MSG_NEXT_STEP + 1)
    ∧ whPrevDigest 1 = prevWordVal (PREV_MSG_NEXT_STEP + 2)
    -- ⚠ …and it holds THROUGH THE PUBLISHED ENTRY and not through an override: word `55 + p` is
    -- entry `65 + p` of `STEP_PUBLIC_IN` verbatim, so a re-added `prevWordVal` arm reds here rather
    -- than quietly making the two conjuncts above true by construction.
    ∧ prevWordVal (PREV_MSG_NEXT_STEP + 1)
        = Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PUBLIC_IN.getD 65 0
    ∧ prevWordVal (PREV_MSG_NEXT_STEP + 2)
        = Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PUBLIC_IN.getD 66 0
    -- ⚠ ⚑ **THE FIELD BOUNDARY, AS A CHECK RATHER THAN A FOOTNOTE.** These digests are **Fq**
    -- (`Tock_field_sponge`) and a step statement word is **Fp**; `q > p`, so an Fq squeeze can exceed
    -- the field it must be published in and `Fp::from_str` would reduce it SILENTLY. Both fit.
    ∧ decide (whPrevDigest 0 < Dregg2.Circuit.Emit.PastaField.pN) = true
    ∧ decide (whPrevDigest 1 < Dregg2.Circuit.Emit.PastaField.pN) = true := by
  native_decide

#assert_compiled wraphack_digest_is_the_emitted_squeeze

/-- ⚑ …and the REAL slot's sponge runs on the TRANSCRIPT's own `sg_old` values, not a second copy of
them (`~sg_old:prev_step_accs`, `wrap_main.ml:412` against `wrap_verifier.ml:538`).

⚠ ⚑ **AT THE REAL SLOT, WHICH IS SLOT 1, AND THIS THEOREM USED TO SAY IT OF SLOT 0.** The record is
`[pad, real]` (`step.rs:2764-2772`), so record slot `whNPad + j` is transcript slot `j`; the PAD slot
absorbs `Dummy.Ipa.Step.sg`, which the transcript's `OptSponge` mask drops (`wrap.rs:2280-2300`) and
which therefore has no transcript cell to be equal to. The second half is that non-equality, stated
rather than left out. -/
theorem wraphack_real_slot_absorbs_the_transcripts_own_sg_old :
    ((List.range (WH_PADDED - whNPad WH_REAL_SLOTS)).all (fun j =>
      let a := whSpongeP tWh (whNPad WH_REAL_SLOTS + j)
      (a.evs.getD (WH_MLMB * WH_ROUNDS) default).word
        == itemVal T_SGOLD (2 * (whNPad WH_REAL_SLOTS + j))
      && (a.evs.getD (WH_MLMB * WH_ROUNDS + 1) default).word
        == itemVal T_SGOLD (2 * (whNPad WH_REAL_SLOTS + j) + 1)))
      = true
    -- ⚠ …and the PAD slot's last two absorbs are openmina's dummy, not a transcript cell.
    ∧ ((whSpongeP tWh 0).evs.getD (WH_MLMB * WH_ROUNDS) default).word = whPadSg.1
    ∧ ((whSpongeP tWh 0).evs.getD (WH_MLMB * WH_ROUNDS + 1) default).word = whPadSg.2
    -- ⚑ …and the pad is not the real accumulator, which is record slot 1 and item 2.
    ∧ whPadSg.1 ≠ itemVal T_SGOLD 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- ⚑ **RED CONTROL — the digest is a function of every input it absorbs.** Bending the first old
bulletproof challenge, the last one, or either coordinate of `sg_old` moves it. Without this the
theorem above is a number agreeing with a number. ⚠ Stated at the REAL slot, whose inputs are the
ones this pipeline derives; the pad's own controls are in `KimchiWrapHackDigest`. -/
theorem wraphack_digest_bends_at_every_probed_input :
    (let cs := whSlotChals WH_REAL_SLOTS 1
     let g := whSlotSg WH_REAL_SLOTS 1
     ((whDigestOf cs g == whDigestOf (cs.set 0 0) g) = false)
     ∧ ((whDigestOf cs g == whDigestOf (cs.set (WH_MLMB * WH_ROUNDS - 1) 0) g) = false)
     ∧ ((whDigestOf cs g == whDigestOf cs (qAdd g.1 1, g.2)) = false)
     ∧ ((whDigestOf cs g == whDigestOf cs (g.1, qAdd g.2 1)) = false)
     ∧ ((whPrevDigest 0 == whPrevDigest 1) = false)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑⚑⚑ **THE CLOSING SPONGE REPRODUCES MINA'S OWN SLOT 11, ON MINA'S OWN INPUTS.**

`whNewChals` was `wrapFixtureQ 42` until 2026-08-06 — a NAMED FIXTURE standing for
`new_bulletproof_challenges` — and §22a's own docblock concluded from that fixture that **"slot 11 is
blocked on W-FINALIZE's bulletproof challenges and on nothing else, so no amount of step-side
re-baking moves it."** This theorem is what refutes that, and it does it the only way a claim about
Mina can be settled: by handing this tree's own sponge Mina's own preimage.

`MinaWrapDeferredWords.WRAP_MSG_NEXT_WRAP_PRECHALS` is the thirty RAW prechallenges
`pickles_kimchi_marshal` put in `messages_for_next_wrap_proof.old_bulletproof_challenges`; `liftValQ`
is `Scalar_challenge.to_field_checked` at `ENDO_Q`, i.e. `compute_challenges`; `whSg` is the step
proof's `openings_proof.challenge_polynomial_commitment`. Hash them with `whDigestOf` — this file's
`hash_messages_for_next_wrap_proof`, front pad, tape order and all — and the result is
`WRAP_PUBLIC_INPUT_MEASURED.getD 11 0` **to the digit**, a number openmina's own
`MessagesForNextWrapProof::hash` produced from a `PreparedStatement::to_public_input(40)` we did not
write.

⚑ **SO THE SHAPE IS NOT WHAT BLOCKS SLOT 11.** The sponge, the lift, the instance-major flattening,
the commitment-last order and the fresh opening state are all right; what disagrees is the
step statement's own words 11–25 / 38–52, which `stepmain_step_r8_finalize` carries as small
synthetic numerals. That relocates slot 11 into exactly the class words 55/56 and slot 12 are already
in — a step-side statement gap — and out of the class "a wrap sub-circuit that was never assembled".

⚠ **THE RED CONTROLS ARE THE POINT, because one number agreeing with one number is not a gate.**
Bending one prechallenge, dropping the lift (absorbing the raw prechallenges instead), and moving the
commitment by one each break the identity. The third is what says `whSg` is load-bearing rather than
decorative; the second is what says the endo lift is. -/
theorem wraphack_closing_sponge_reproduces_minas_slot_eleven :
    whDigestOf
        ((Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_MSG_NEXT_WRAP_PRECHALS).map
          (liftValQ shapeWrap)) whSg
      = Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED.getD 11 0
    -- ⚑ …and it is the SAME lift `whNewChal` applies, at the same width.
    ∧ CHAL_BITS shapeWrap = WQ_CHAL ∧ shapeWrap.emsRows = shapeSmoke.emsRows
    -- ⚠ bend one prechallenge…
    ∧ whDigestOf
        (((Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_MSG_NEXT_WRAP_PRECHALS).set 0 1).map
          (liftValQ shapeWrap)) whSg
        ≠ Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED.getD 11 0
    -- ⚠ …drop the endo lift…
    ∧ whDigestOf Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_MSG_NEXT_WRAP_PRECHALS whSg
        ≠ Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED.getD 11 0
    -- ⚠ …and move the commitment.
    ∧ whDigestOf
        ((Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_MSG_NEXT_WRAP_PRECHALS).map
          (liftValQ shapeWrap)) (qAdd whSg.1 1, whSg.2)
        ≠ Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED.getD 11 0 := by
  native_decide

#assert_compiled wraphack_closing_sponge_reproduces_minas_slot_eleven

/-- ⚑⚑ **AND THE VECTOR THE CLOSING SPONGE ABSORBS IS THE ONE §20 ALREADY EMITS — AGREEMENT, NOT
COINCIDENCE.**

`whNewChals` and `finSpRows` step (4) are TWO constructions of `compute_challenges`' output: the
first is the closing sponge's tape, the second is fifteen `to_field_checked` chains per instance whose
`lift` cell `chainEnv` fills. Two constructions of one object is how a tie holds by accident — it is
precisely what `prevWordVal`'s override arms did to W-FINSPONGE and W-WRAPHACK, where one side of an
equation was the other side's definition and nothing had to reduce. So this reads the EMITTED
environment at the EMITTED variable and asks whether the number there is the number the sponge
absorbs, per instance and per round, and it checks the index arithmetic (`k / WH_ROUNDS`,
`k % WH_ROUNDS`) against the emission's own nested loop rather than restating it.

⚠ The last two legs are the anti-vacuity, and each is a different way the first leg could pass while
meaning nothing: a `contains` that accepts anything is not a check, so the same variable with the
value off by one must NOT be found; and the two instances' round-0 lift cells must be DIFFERENT
VARIABLES, because if the two instances' chain blocks aliased, thirty legs would be ranging over
fifteen cells.

⚠ `native_decide`: `finSpEnvW` is downstream of `finSpDataW`, the 1732-op programs §20b‴ already
confesses to. -/
theorem wraphack_new_challenges_are_the_finsponge_lifts :
    ((List.range (WH_MLMB * WH_ROUNDS)).all (fun k =>
      finSpEnvW.contains
        (finSpChalLiftVar (k / WH_ROUNDS) (k % WH_ROUNDS), (whNewChal tW.sh k : Int)))) = true
    ∧ (whNewChals tW.sh).length = WH_MLMB * WH_ROUNDS
    ∧ finSpEnvW.contains (finSpChalLiftVar 0 0, (whNewChal tW.sh 0 + 1 : Int)) = false
    ∧ finSpChalLiftVar 0 0 ≠ finSpChalLiftVar 1 0 := by
  native_decide

#assert_compiled wraphack_new_challenges_are_the_finsponge_lifts

/-- ⚑ **WORD 11's OBJECT, CHECKED AGAINST A REAL DEVNET WRAP PROOF — not its slot.**

This module has already shipped the other mistake once: twenty exposed words carried the 255-bit
endo lift where `spec.ml:374-392` packs the raw 128-bit prechallenge, and **the only word with a
different width was the only correct one, which is why nothing caught it.** So the object is checked
here and the instrument is INDEPENDENT: `MinaWrapPublicCommGate.PUBLIC_INPUT` is a Mina devnet
block's own forty Fq wrap words, decoded off the wire. In it, slots 5–8 (`β γ α ζ`, `Challenge` and
`Scalar Challenge`) all fit in `Challenge.length = 128` bits, and slots 10 and 11 — the two
`B Digest`s, `sponge_digest_before_evaluations` and `messages_for_next_wrap_proof` — do NOT. That is
the width tell, measured on a real proof rather than derived from our own layout; and the value this
rung exposes at slot 11 is likewise a full `squeeze_field`, not a truncation of one. -/
theorem wraphack_word_11_is_a_digest_not_a_challenge :
    ((List.range 4).all (fun j =>
      decide (Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD (5 + j) 0
                < 2 ^ WQ_CHAL))) = true
    ∧ decide (Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD 10 0 < 2 ^ WQ_CHAL)
        = false
    ∧ decide (Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD 11 0 < 2 ^ WQ_CHAL)
        = false
    ∧ decide (whCloseDigest shapeWrap < 2 ^ WQ_CHAL) = false
    ∧ decide (whCloseDigest shapeWrap < qN) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The rung's own public word: slot 11, tied to the closing sponge's squeeze. -/
theorem wraphack_public_word_11_is_the_closing_squeeze :
    rungPub shapeSmoke .wraphack = WRAP_PRIMARY_LEN
    ∧ slotVarAt tWh .wraphack (WH_PUB_SLOT shapeSmoke)
        = some (whDigestVar (whSpongeC tWh))
    ∧ WH_PUB_SLOT shapeSmoke = WRAP_SLOT_MSG_NEXT_WRAP
    ∧ slotVarAt tWh .prev WRAP_SLOT_MSG_NEXT_WRAP = none
    -- ⚠ the VALUE at that slot is `wraphack_digest_is_the_emitted_squeeze`'s third conjunct, stated
    -- there and not here: `wrapPublicAt` runs `envIndex` over `circuitEnvAt … .wraphack`, which
    -- carries every accumulator point and slope of §15's MSM, and reducing it blew 4 000 000
    -- heartbeats. That is the measurement the `circuitEnvAt` docblock above is about.
    -- ⚑ `pubWords + 2` UNTIL 2026-08-05, and `+ 5` now: this rung sits above `w8_ftcomm`, so it
    -- inherits the three `ft_comm` pass-throughs (slots 4, 2, 3) on top of its own slot 11 and
    -- W-PREV's slot 12. It does NOT sit above W-COMBINE or W-BULLET, so ξ and the bulletproof pair
    -- are not here — which is what makes `+ 5` rather than `+ 8` the load-bearing number.
    ∧ (exposedVarsAt tWh .wraphack).length = shapeSmoke.pubWords + 5
    ∧ (wrapSlotsAt shapeSmoke .wraphack).length = shapeSmoke.pubWords + 5
    -- …and the two stay POINTWISE, which is the property the pair of lengths exists to protect.
    ∧ (exposedVarsAt tWh .wraphack).length = (wrapSlotsAt shapeSmoke .wraphack).length := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The `w11_wraphack` rung is a strict superset of `w9_prev`, its length is the sum of its parts,
and the WIRED and UNWIRED emissions differ ONLY in the probe rows' permutation columns. -/
theorem wraphack_rung_extends_prev :
    (rungRows tWh .wraphack true).length
      = (rungRows tWh .prev true).length + (whRows tWh true).length
    ∧ (rungRows tWh .prev true).length < (rungRows tWh .wraphack true).length
    ∧ (((rungRows tWh .wraphack true).zip (rungRows tWh .wraphack false)).filter
        (fun p => p.1.perm != p.2.perm)).length
        = ((rungRows tWh .wraphack true).filter (fun r => r.probe)).length := by
  refine ⟨rfl, by decide, rfl⟩

/-- `placeChecked` ACCEPTS the `w11_wraphack` rung at its larger public size and no public word is
inert — and `w9_prev` is REFUSED at that size, because no `w9_prev` gate reads slot `pubWords + 1`.
That is what makes `AUXW`'s second reserved slot a gate rather than a comment. -/
theorem wraphack_rung_places_and_the_rung_below_it_does_not :
    refusalOf shapeSmoke .wraphack (rungPub shapeSmoke .wraphack)
        (wrapGates (rungRows tWh .wraphack true)) = none
    ∧ inertSlotsAt shapeSmoke .wraphack (wrapGates (rungRows tWh .wraphack true))
        = wrapInertOk shapeSmoke .wraphack
    ∧ inertPublicWordsBeyond (rungPub shapeSmoke .wraphack) (wrapInertOk shapeSmoke .wraphack)
        (wrapGates (rungRows tWh .prev true)) = [WH_PUB_SLOT shapeSmoke]
    ∧ refusalOf shapeSmoke .wraphack (rungPub shapeSmoke .wraphack)
        (wrapGates (rungRows tWh .prev true))
        = some (.inertPublicWord WRAP_SLOT_MSG_NEXT_WRAP) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- ⚑ **MINA'S FORTY SPLIT THREE WAYS: 24 CONSTRAINED, 6 READ, 10 DEAD — AND IT USED TO SPLIT TWO
WAYS BECAUSE SIX WORDS WERE FILED UNDER "NOTHING READS THESE".**

`WRAP_PINNED_SLOTS` is what `wrap_main` CONSTRAINS. `WRAP_PASSTHROUGH_SLOTS` is what it READS and
does not check — `~advice`/`~plonk`/`~xi`, checked by the next proof's `finalize_other_proof`.
`WRAP_UNPINNED_SLOTS` is what nothing reads at all, upstream or here.

⚠ **THE OLD STATEMENT WAS `PINNED != UNPINNED` OVER THE FORTY, AND IT IS FALSE NOW** — not off by a
count, but missing a category: six slots are in neither of those two lists. Restating it as a
three-way partition is the whole content of this repair, and the `dedup.length` and pairwise-
disjointness conjuncts are what stop "partition" from meaning "some list of forty things".

A run that reads "public inputs: ours 30, mina 40" and calls the remaining ten a gap in this
assembly would be reading a zero pad as work. -/
theorem wraphack_closes_every_pinned_statement_word :
    WRAP_PINNED_WORDS = 24
    ∧ WRAP_PINNED_SLOTS.length = 24
    ∧ WRAP_PASSTHROUGH_SLOTS.length = 6
    ∧ WRAP_UNPINNED_SLOTS.length = 10
    ∧ WRAP_PRIMARY_LEN - WRAP_PINNED_WORDS - WRAP_PASSTHROUGH_SLOTS.length = 10
    ∧ WRAP_UNPINNED.length = 2
    ∧ WRAP_PASSTHROUGH.length = 6
    ∧ rungPub shapeSmoke .wraphack = WRAP_PRIMARY_LEN
    -- ⚑ **THE THREE LISTS PARTITION MINA'S FORTY.** Each is written down rather than computed, so
    -- this is three independent readings of `wrap_main` agreeing, not a definition unfolding:
    -- 24 + 6 + 10 = 40, no slot in two of them, and together exactly `range 40`.
    ∧ (WRAP_PINNED_SLOTS ++ WRAP_PASSTHROUGH_SLOTS ++ WRAP_UNPINNED_SLOTS).dedup.length
        = WRAP_PRIMARY_LEN
    ∧ ((List.range WRAP_PRIMARY_LEN).all (fun i =>
        (if WRAP_PINNED_SLOTS.contains i then 1 else 0)
        + (if WRAP_PASSTHROUGH_SLOTS.contains i then 1 else 0)
        + (if WRAP_UNPINNED_SLOTS.contains i then 1 else 0) == 1)) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚠ ⚑ **THE CENSUS DID NOT MOVE, AND `sg_old`'s ENTRY IS REWRITTEN RATHER THAN STRUCK.**
W-WRAPHACK gives `sg_old` a real consumer — it is hashed into packed statement words 55/56, which the
x_hat MSM consumes as entries 65/66. It is still a FREE witness: the digest is a function of it, but
nothing forces the digest to any particular value, because what the MSM's output feeds is `x_hat`,
which is itself absorbed and unconsumed. A prover still chooses `sg_old` subject only to
`assert_on_curve`. Striking the entry here would be the metric-gaming this census exists to refuse.
The count stays **8**. -/
theorem wraphack_does_not_move_the_unconsumed_census :
    WRAP_UNCONSUMED.length = 8
    ∧ WRAP_UNCONSUMED_KEYS.getD 0 "" = "sg_old"
    ∧ WRAP_UNCONSUMED_KEYS.length = WRAP_UNCONSUMED.length := by
  refine ⟨rfl, rfl, rfl⟩

end Dregg2.Circuit.Emit.KimchiWrapMain
