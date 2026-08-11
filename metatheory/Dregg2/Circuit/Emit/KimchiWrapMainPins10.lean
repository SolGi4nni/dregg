/-
# Dregg2.Circuit.Emit.KimchiWrapMainPins10 — §22a — W-CLOSE

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

/-! ### §22a — ⚑ THE PINS ON W-CLOSE. -/

/-- **W-CLOSE emits the σ-TIE, `Boolean.Assert.is_true bulletproof_success`, and one σ-only probe.**

⚑ Row 0 is now one `Generic` DOUBLE gate carrying both halves: the tie joining `bpSuccessVar` to
`bullEqV s sp 12` — `equal_g`'s `Boolean.all` output — and the `cConst 1` assert. The first half's
two permutable slots are what makes it a tie and not a second constant. -/
theorem close_ties_and_asserts_bulletproof_success :
    (closeRows tWh true).length = 2
    ∧ ((closeRows tWh true).getD 0 default).kind = KGateType.generic
    ∧ ((closeRows tWh true).getD 0 default).coeffs = cEq ++ cConst 1
    ∧ ((closeRows tWh true).getD 0 default).perm.getD 0 none
        = some (bpSuccessVar shapeSmoke tWh.sp)
    ∧ ((closeRows tWh true).getD 0 default).perm.getD 1 none
        = some (bullEqV shapeSmoke tWh.sp 12)
    ∧ ((closeRows tWh true).getD 1 default).probe = true
    ∧ ((closeRows tWh true).getD 1 default).kind = KGateType.zero := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ …and the emitted coefficients REFUSE a failed opening: the half is satisfied at
`bulletproof_success = 1` and violated at `0`, which is the whole content of
`Boolean.Assert.is_true`.

⚠ **THE WITNESS IS NO LONGER A CONSTANT THIS FILE WROTE.** `closeEnv` used to answer `(1 : Int)`
outright, so this conjunct was a pin against its own definition. It now COMPUTES
`bullLhs t v == bullRhs t v` off `bullData` — the same expression `bulletEnv` gives `bullEqV s sp 12`
— so the `1` below is `equal_g`'s verdict at this key and not a decision made here. That is why this
leg moved to `native_decide`: `bullData` is 34 + 33 endo ladders, the same instrument
`bullet_solves_g_on_curve_and_equal_g_is_one` confesses to. -/
theorem close_refuses_a_failed_opening :
    genericHalfAt (cConst 1) 1 0 0 = 0
    ∧ genericHalfAt (cConst 1) 0 0 0 ≠ 0 := by
  refine ⟨rfl, by decide⟩

/-- ⚑⚑ **AND THE WITNESS IT PINS TO 1 IS W-BULLET'S OWN VERDICT** — the half of
`close_refuses_a_failed_opening` that `bullData` puts out of the kernel's reach. `closeEnv`'s single
entry and `bulletEnv`'s `bullEqV s sp 12` entry hold ONE value, which is what makes the σ-tie
satisfiable, and that value is `1` because `equal_g` computes 1 at Mina's step key. At the old
degenerate key it computed 0 — and then this theorem would be FALSE rather than the rung quietly
asserting a constant. -/
theorem close_witness_is_the_bullet_verdict :
    (closeEnv tWh).getD 0 ((.external 0 : PVar), (0 : Int))
      = (bpSuccessVar shapeSmoke tWh.sp, (1 : Int))
    ∧ (bulletEnv tWh).contains (bullEqV shapeSmoke tWh.sp 12, (1 : Int)) = true := by
  native_decide

#assert_compiled close_witness_is_the_bullet_verdict

/-- The `w12_close` rung is the ladder's top. ⚑ It extends `w11_bullet` and not `w11_wraphack` since
2026-08-05: `bulletproof_success` is `equal_g`'s output, so the rung that asserts it must carry the
rows that compute it. It adds W-WRAPHACK's own rows and its own two, and derives no new public word.

⚑⚑ **AND IT IS THE FIRST RUNG TO HOLD TWO BLOCK OWNERS** — `.wraphack` and `.combine` — which is why
§17b's `rungRegions` returns a LIST. The last two legs are that pair: the ladder really does hold two
owners, and `rungRegions .close` really does declare two blocks. A `rungRegions` that forgot
W-COMBINE would make the fourth leg `1` and red here, which is the failure the old single-block form
made unavoidable.

⚑ **GENERAL OVER EVERY `WrapData` AND EVERY POLARITY, AND KERNEL-CLEAN** — stronger than the shape
instance it replaced, and that is also what makes it affordable.

⚠ **`refusalOf`, `inertPublicWords` AND `regionEscape` ARE NOT PINNED HERE, and that is the file's
own division rather than a gap.** Each runs `placeChecked` or `externalRefs` over this rung's ~7 000
gates — which now include `bulletRows`' 67 endo ladders and `combRows`' 46 — and neither the kernel
nor the compiled evaluator finishes it in a budget worth paying on every build: MEASURED at >23 min
with four inline `rungRows tWh .close true`, and still >16 min after memoising into
`clRows`/`clGates`. Against 65 s while the rung stopped at W-WRAPHACK. **`EmitWrapMainJson` and
`EmitStepWrapChainJson` run all three at EVERY emission and STOP on any of them**, which is exactly
where `the_caps_are_the_blocks` already puts W-FINALIZE's fit: the kernel closes what it can reach,
the emit-time refusal closes the rest, and the two are named separately rather than blurred.
`clRows`/`clGates` stay in the fixture as the shared term those emissions — and any future pin that
can afford them — should use. -/
theorem close_rung_extends_bullet (t : WrapData) (wired : Bool) :
    rungRows t .close wired
      = rungRows t .bullet wired ++ rungOwn t wired .wraphack ++ rungOwn t wired .close
    ∧ rungPub t.sh .close = rungPub t.sh .wraphack
    ∧ ((rungsUpto .close).filter (fun r => COLLIDING_REGION_OWNERS.contains r)).length = 2
    ∧ (rungRegions t.sh t.sp .close).length = 2 :=
  ⟨rungRows_close_is_a_ladder t wired, rfl, by decide, rfl⟩

#assert_axioms close_rung_extends_bullet

/-- ⚑⚑⚑ **SLOT 11 AGREES WITH MINA'S FORTY (2026-08-06). SLOT 12 DOES NOT, AND WHAT BLOCKS IT IS
ONE VALUE — `G` — WHOSE REPAIR IS THE ACCUMULATOR CHECK'S OPENING LEG.**

⚠ This header read *"WHAT BLOCKS IT IS AN ARITY, NOT A VALUE"* until 2026-08-08. The arity was
refuted on 2026-08-07 and the name was never corrected; the entry below carries all three refuted
explanations and the measured one.

`wrap_main` is handed forty words, CONSTRAINS twenty-four and READS six more; the ten it neither
reads nor checks are `Spec.T.Constant` padding and the lookup `Opt` (§10). So the denominator is
**30**.

⚠ ⚑ **AND "REACHES" NEEDS ITS CRITERION SAID, BECAUSE IT HAS BEEN READ AS THE WRONG ONE.** A slot
is REACHED when the assembly puts a value there that is a DERIVATION over cells it also computes, or
one of the six Mina words `wrap_main` passes through unaltered — **not** when the emitted word equals
Mina's. Reaching is this assembly's own business; AGREEING is a fact about two implementations of one
statement, and the two counts are different numbers. Both are stated here so neither can stand in for
the other.

  * **REACHED: 29 of 30.** Only slot 12 is unreached — the wrap derives nothing for it, it reads
    packed word 54 and exposes it.
  * **AGREED: 29 of 30, and 39 of 40 counting the padding.** Measured slot by slot over
    `wrapPublicAt tChain .close` — `tChain = mkWrap shapeWrap`, the shape this ladder is about —
    against `WRAP_PUBLIC_INPUT_MEASURED`. It was 28 of 30 before slot 11 closed.
    `KimchiWrapMainPins12.the_forty_agree_at_every_slot` is the count as a theorem, with the
    disagreeing slot EXHIBITED rather than subtracted. ⚠ The citation here named
    `KimchiStepWrapChain.the_emitted_forty_agree_with_minas_at_every_slot_but_twelve` until
    2026-08-09; that theorem was DELETED as a duplicate the hour it was written
    (`KimchiStepWrapChain` §-, "deletion rather than a second copy"), and the name outlived it.
  * ⚑ **AND THE 39 IS RE-MEASURED, NOT CARRIED.** `0047cb876` rewired `runIpa` onto §19d's fold and
    `0aa6f7d49` re-baked `WRAP_PUBLIC_INPUT_MEASURED` from the re-proved step proof — **28 of the 40
    slots moved on MINA'S side**, so every count graded against the old referee was about an object
    that no longer exists. Re-run 2026-08-09 (`EmitWrapFortyAgreement`, both shapes): **still 39 of
    40, still missing at 12 alone.** The two sides moved TOGETHER at all 28, which is the fact the
    number now records — ours derive from the same re-proved step proof Mina's forty were read from.

⚠ ⚑⚑ **AND THE "SIX OF FORTY" THIS DOCBLOCK USED TO QUOTE WAS THE SMOKE SHAPE'S, WHICH IS NOT THE
SHAPE THE LADDER IS ABOUT.** `tWh` is `mkWrap shapeSmoke`: its `wrapSlots` is `.take
shapeSmoke.pubWords = 22`, so slots 14–28 and 29 are not in its slot table at all and read `0`, and
its transcript runs over fixture commitments rather than the step proof's tape. Six was a true
statement about a 22-word vector; quoting it as the ladder's agreement count made a re-measurement
read as a thirty-three-slot repair when the actual gap was two. Both numbers are kept, each next to
the object it is about.

  * ✅ **SLOT 11 — `messages_for_next_wrap_proof`.** ⚠ **THIS ENTRY HAS BEEN WRONG TWICE AND BOTH
    CORRECTIONS ARE KEPT, BECAUSE THE SECOND ONE IS THE INTERESTING ONE.** It first read: *"`whNewChals`
    is `wrapFixtureQ 42` — a NAMED FIXTURE standing for `new_bulletproof_challenges`… slot 11 is
    blocked on W-FINALIZE's bulletproof challenges and on nothing else, so no amount of step-side
    re-baking moves it."* Both halves were refuted on 2026-08-06: `new_bulletproof_challenges` is
    `compute_challenges` of the previous statement's own packed words `27·p + 11 … 25`, which §20
    already emits. It then read that the hash was right and **the step statement's words were
    wrong**. That was wrong too, and in the more expensive direction: `pickles_kimchi_marshal`
    **CHOSE** its thirty (`k·0x9E3779B97F4A7C15 | 1`, a ladder in `prove_wrap`) and handed the same
    ladder to the wrap proof's `create_recursive`, while the step circuit published its own fifteen
    per block. **Two vectors where `wrap_main.ml:421-431` has one**, and every instrument agreed with
    itself — `expand_prechallenge` matched the proof it was checked against, the accumulator matched
    its own challenge polynomial, the hash hashed what it was given. The marshaller reads the step
    statement now (`step_statement_prechallenges`), and the last conjunct below is the old refusal
    INVERTED: all thirty inputs coincide, and `whCloseDigest shapeWrap` **is** Mina's slot 11.
  * ⚠ **SLOT 12 — `messages_for_next_step_proof`. IT IS NOT AN ARITY GAP AND IT IS NOT A FIXPOINT.**
    §18's `prevRows` ties Mina's slot 12 to packed word 54 by `Field.Assert.equal`, and the wrap
    DERIVES NOTHING for it. This entry has now been wrong **three** times about WHY it misses, and
    all three wrong answers were the same shape — a structural explanation for what is a VALUE
    difference:

      1. *"the step assembly's outer hash against the marshaller's, closing when the outer hash
         produces what the marshaller computes"* — refuted by the index repair;
      2. *"two assemblies of one object at different ARITIES, closing when the marshaller reads the
         step proof and the two agree on how many slots the record has"* — refuted on 2026-08-07.
         The arities DO agree now (`marshal::STEP_RECURSION_SLOTS = gates::STEP_RULE_N_PREVIOUS = 1`,
         `gate_c` prints `MATCH=true`), the app state agrees (two words on both sides), the index
         agrees (`MinaWrapOwnVerifierKey`), **and slot 12 still misses.**
      3. ⚑ *"closing it is a FIXPOINT — making the wire record carry segment D's `G` and lifts moves
         the step proof's public input at word 54; the step transcript absorbs the public-input
         commitment; `solveG`'s output is derived from that transcript"* — **refuted on 2026-08-08
         by computing the cone.** `KimchiStepMainPins13
         .the_cone_of_word_fifty_four_holds_no_published_statement_entry` exhibits word 54's ENTIRE
         preimage — `hmOutSpec` names it, so it is not an approximation — as seventy-six cells:
         56 `MinaWrapOwnVerifierKey.INDEX_WORDS`, 2 app-state words, `G`, 16 `liftOf … (uChal k)`.
         **Not one of the sixty-seven published statement entries is in it, and neither is
         `STEP_PREVCOMM_XY`.** The step statement is not upstream of word 54; the pass order is
         `previous commitments → step transcript → {G, lifts} → segment D → word 54`, and word 54
         is settled at the third arrow. ⚠ The one link that *looks* circular — segment D absorbing
         dregg's own wrap verification key — is the same asymmetry §10b measures from the other
         side: the wrap pins the STEP key as `Inner_curve.constant` (coefficients), the step takes
         the WRAP key as `w.exists` (a WITNESS, `idxOVar`), and a witness does not enter a key.

    ⚑ **WHAT IS ACTUALLY LEFT, MEASURED BY `segd_slot12_probe` RATHER THAN INFERRED.** Hand
    openmina's own `MessagesForNextStepProof::hash()` segment D's OWN preimage — 56 index
    coordinates, `N_HM_APP = 2` app-state words, ONE `[Gx; Gy]`, `bRounds = 16` lifts — and it
    returns **3396651593405556290675030761129700631429897333743779176977354897227206574822**,
    which is segment D's squeeze and the emitted slot 12 **to the digit**. So there is no sponge
    gap, no arity gap and no index gap. What differs is WHICH VALUES fill the one slot: segment D
    absorbs the step assembly's own `G` (`solveG`'s output, §19) and its own sixteen
    `to_field_checked` lifts, while `gate_c` hashes the WIRE record's
    `challenge_polynomial_commitments` and `step_old_bulletproof_challenges`
    (`marshal.rs:578-608`) — the wrap proof's own kimchi recursion commitment and a chosen
    prechallenge ladder, neither of which the step assembly derived.

    ⚑⚑⚑ **THE FOURTH WRONG ANSWER, AND IT WAS THE REFEREE'S OWN — CLOSED 2026-08-08, AND SLOT 12
    SURVIVED IT.** Item 2 above says "the index agrees (`MinaWrapOwnVerifierKey`)", and that was a
    claim about which MODULE segment D reads, not about what was IN it.
    `MinaWrapOwnVerifierKey.lean` was last written at `8015b6f07` and the wrap circuit it is the key
    OF was re-emitted at `8c3c341d8`, **29 commits later**, so segment D had been hashing under a
    superseded key while `gate_c` hashed under the live one. `segd_slot12_probe` could not see it —
    it READS the tracked module and therefore agreed with the stale install by construction — and
    `WRAP_PUBLIC_INPUT_MEASURED`, baked on the other side of that re-emit, was stale at exactly the
    slot under investigation. `pickles_kimchi_marshal::installed_gate` now reds on the drift, and
    the run that first turned it red measured BOTH polarities in one pass: two tape modules
    byte-identical, one module drifted, `PROOF_MARSHAL_RESULT=RED (1 failures)`.

    ⚠ **INSTALLING IT DID NOT CLOSE SLOT 12, AND THAT IS THE MEASUREMENT AND NOT A GUESS.** The
    whole chain was carried — VK installed, `stepmain_step_r8_finalize.json` re-emitted (public
    entry **64** and only entry 64 moved), the step proof re-proved, `KimchiStepWrapChainFixture`
    re-installed, `WRAP_PUBLIC_INPUT_MEASURED` re-baked from that run's own
    `wrap-public-input.json`, `shapeSmoke.xhatXY` re-derived, all thirty wrap fixtures re-emitted —
    and `EmitWrapFortyAgreement` at `shapeWrap` still reports **AGREE at 39 of 40**, missing at 12
    alone. What the install bought is a SHARPER residue, not a smaller count: of slot 12's
    seventy-six cells **fifty-eight now agree** — the 56 index coordinates and the 2 app-state
    words — and the disagreement is confined to **cells 58–75**, the `[Gx; Gy]` pair and the
    sixteen challenges, printed side by side by `pickles_kimchi_marshal`'s `[gate C] cell NN` lines
    against `wip/SegDPreimage.lean`'s 58..75. That is exactly the two families the next paragraph
    prices, and it is now a measured perimeter rather than an inferred one.

    ⚠ ⚑⚑ **AND THE RESIDUE, NAMED: IT IS THE ACCUMULATOR CHECK'S OPENING LEG (#11) WEARING A PUBLIC
    WORD.** The sixteen close in one pass — `prove_step`'s `step_pre` is a
    `k·0x9E3779B97F4A7C15 | 1` ladder where the assembly's own sixteen prechallenges belong, and
    those are transcript-derived and unmoved by anything downstream. `G` does not. `record
    .challenge_polynomial_commitments[0]` is the wrap proof's kimchi recursion commitment, which
    kimchi forces to be `commit(b_poly(chals))` (`prove_wrap`: *"an unrelated point makes
    `batch_verify` return `OpenProof` — measured, first run"*), while segment D absorbs `solveG`'s
    SOLVE, because §17 measured that this assembly has no IPA opening to take a real
    `challenge_polynomial_commitment` from. **Pinning `G` to the real accumulator turns `equal_g`
    into the two-dimensional discrete log in `⟨G + b·u, H⟩`** —
    `KimchiStepMainPins12` §17(g) and `KimchiStepMainPins13` §18(g) already price exactly that, and
    call it item #11. So the last of the forty is an ASSUMPTION this assembly has never discharged,
    not an iteration and not a marshaller edit.

⚠ **AND THIS THEOREM WAS A REFUSAL SHAPED TO SHRINK, like `STATEMENT_BLOCKED`. IT SHRANK, 2026-08-11.**
Its second conjunct asserted a DISAGREEMENT so that closing slot 12 would go red at the place the
claim is made rather than leave a stale count standing. That is what happened: the conjunct is now an
EQUALITY and the counts above are rewritten.

⚑⚑⚑ **AND THE PARAGRAPH ABOVE IS RETIRED IN ITS OWN TERMS — WITHOUT `equal_g` MOVING.** It said the
last of the forty was "an ASSUMPTION this assembly has never discharged", because pinning `G` to the
real accumulator turns `equal_g` into the 2-D discrete log. **The assumption was not discharged and
`equal_g` was not touched.** What was wrong was the premise that ONE cell must serve both: upstream
`check_bulletproof`'s `sg` and the record's `challenge_polynomial_commitment` are one point because
the previous proof's IPA was honestly run, and this assembly has no such opening — so it now carries
TWO cells. §19's ladder keeps `solveG`'s solve (`vGx`); segment D absorbs the record's own
commitment (`vGaX`, `MinaStepOwnAccumulator.ACC_XY`), which kimchi forces and `gate_a2` re-derives.
Item #11 is exactly where it was; what closed is a VALUE disagreement between the statement this
assembly published and the record the prover marshalled — the published statement had been internally
false, which is a worse thing to have been carrying than an undischarged opening leg.

⚠ And the other half landed in the same flag day: `prove_step`'s `k·0x9E3779B97F4A7C15 | 1` ladder is
gone and the wire carries the assembly's own sixteen. Word 54 is ONE digest over all seventy-six
cells, so neither half could have landed alone. -/
theorem slot_eleven_and_slot_twelve_both_agree :
    Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED.getD 11 0
      = whCloseDigest shapeWrap
  ∧ Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED.getD 12 0
      = prevWordVal PREV_MSG_NEXT_STEP
  -- ⚑ ANTI-VACUITY on the new conjunct: slot 12 is a 255-bit Fq digest, not a zero both sides
  -- happen to carry.
  ∧ 2 ^ 250 < prevWordVal PREV_MSG_NEXT_STEP
  -- ⚑⚑ …and slot 11's agreement is not a digest coincidence: the thirty packed words the closing
  -- sponge reads ARE the thirty the marshaller hashes, all thirty of them. This conjunct read
  -- `= WH_MLMB * WH_ROUNDS` until 2026-08-06 — every one disagreed — and it is the same expression
  -- with the answer inverted, which is what makes the change visible rather than merely absent.
  ∧ ((List.range (WH_MLMB * WH_ROUNDS)).filter (fun k =>
      finBlockVal (k / WH_ROUNDS) (FIN_W_CHAL + k % WH_ROUNDS)
        != Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_MSG_NEXT_WRAP_PRECHALS.getD k 0)).length
      = 0
  -- ⚑ …and the denominator, so "29 of 30" is not a number in a dump: forty words, ten of which
  -- upstream neither reads nor checks.
  ∧ 40 - 10 = 30 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | decide | native_decide

-- ⚑ **KERNEL-CLEAN, AND THAT IS A STRENGTHENING THE CLOSURE BOUGHT.** This was `#assert_compiled`
-- while its slot-12 conjunct was a `≠` over `prevWordVal`; as an EQUALITY the whole conjunction
-- closes by `decide`, so the compiled evaluator is out of the trusted path entirely.
#assert_axioms slot_eleven_and_slot_twelve_both_agree

end Dregg2.Circuit.Emit.KimchiWrapMain
