/-
# Dregg2.Circuit.Emit.KimchiWrapMainPins01 — the CONSTANT PINS (§11, §11b endo scalar, §11c Branch_data.pack, §11d the field)

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

/-! ## §11 — the CONSTANT PINS, each against an INDEPENDENT source.

⚑ Defect class 4: "a constant pinned against its own definition is decoration; two INDEPENDENT
sources are a gate." Each pin below reads a value this file does not own.

### §11a — the Fq Poseidon constants.

The gate coefficients this file emits are `fq_kimchi`'s (`wrap_main_inputs.ml:12-13`,
`sponge/constants.ml:4011` `params_Pasta_q_kimchi`, 3×3 MDS and 55×3 round constants), NOT
`fp_kimchi`'s. A copy-paste of the step side's `rcsN` reds here, and so does a value that is not
reduced mod `qN`. -/

#guard poseidonRowCoeffsQ 0
       = (List.range 5).flatMap (fun i => (rcsQ.getD i []).map (fun n => (n : Int)))
#guard rcsQ.getD 0 [] != Dregg2.Circuit.Emit.PastaPoseidon.rcsN.getD 0 []
#guard mdsQ.getD 0 [] != Dregg2.Circuit.Emit.PastaPoseidon.mdsN.getD 0 []
#guard (poseidonRowCoeffsQ 0).length == 15
#guard (poseidonRowCoeffsQ 10).length == 15
#guard (poseidonRowCoeffsQ 0).all (fun c => decide (c ≥ 0) && decide (c < (qN : Int)))
#guard rcsQ.length == 55
#guard mdsQ.length == 3

/-! ### §11b — the endomorphism scalar.

`ENDO_Q` is `Endo.Step_inner_curve.scalar = Pasta_bindings.Pallas.endo_scalar ()` (`endo.ml:14-21`),
an element of `Backend.Tock.Field = Fq`, and `wrap_verifier.ml:134,143` is where the wrap circuit
scales `a₈` by it. `MinaRealBlockTranscript.ENDO_R` is the SAME Fq element arrived at independently
— the endo a real Mina Wrap proof's `ScalarChallenge::to_field` uses, validated THERE by
REPRODUCING that block's own α, ζ, v and u (`derived_alpha`, `derived_zeta`, `derived_v`,
`derived_u`). Two sources, one value.

⚠ ⚑ **AND GETTING IT BACKWARDS IS EASY, WHICH IS WHY BOTH DIRECTIONS ARE PINNED.**
`wrap_verifier.ml:121` instantiates the `Scalar_challenge` functor with **`Endo.Wrap_inner_curve`**
(Vesta's pair — `base ∈ Fq`, `scalar ∈ Fp`) for the in-circuit `endo`/`endo_inv` curve gadget, while
`:134` uses **`Endo.Step_inner_curve.scalar`** (Pallas's, in Fq) for `to_field_checked`. Two
different endos in one file, and only one of them is a scalar of this circuit's own field. -/

/-- ⚑ `ENDO_Q` against an INDEPENDENT source, both directions, and its defining algebraic property.

  * it IS `MinaRealBlockTranscript.ENDO_R`, arrived at by reproducing a real Mina Wrap proof's own
    α, ζ, v and u;
  * it is NOT the step side's `Endo.Wrap_inner_curve.scalar`, which lives in Fp
    (`bindings_js_test.ml:588-592`) — conflating the two is the `MinaWrapFtEval0Weld` defect, in the
    direction nothing had tested;
  * nor `Endo.Wrap_inner_curve.base`, the Fq element `wrap_verifier.ml:944`/`:121` uses for the CURVE
    endomorphism (`bindings_js_test.ml:583-587`). Both are Fq; only one is a scalar;
  * and it is a NONTRIVIAL cube root of unity in Fq — the property `endo_scalar` HAS
    (`poly-commitment/src/srs.rs:44-60`), checked rather than assumed. -/
theorem endo_q_is_pallas_endo_scalar :
    (ENDO_Q : Nat) = (Dregg2.Circuit.Emit.MinaRealBlockTranscript.ENDO_R).val
    ∧ ENDO_Q ≠ 8503465768106391777493614032514048814691664078728891710322960303815233784505
    ∧ ENDO_Q ≠ 2942865608506852014473558576493638302197734138389222805617480874486368177743
    ∧ qMul (qMul ENDO_Q ENDO_Q) ENDO_Q = 1
    ∧ ENDO_Q ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### §11c — `Branch_data.Checked.pack`.

`branch_data.ml:95-101`: `pack = 4·domain_log2 + Impl.Field.pack (Vector.to_list
proofs_verified_mask)`, where `Field.pack` is `project`, LSB-first. ⚑ **The mask term is 0/2/3, not
0/1/2**, because `Prefix_mask.there` is `N0 ↦ [ff;ff] · N1 ↦ [ff;tt] · N2 ↦ [tt;tt]`
(`pickles_base/proofs_verified.ml:75-81`) and `wrap_main.ml:172-180` builds it as
`ones_vector ~first_zero:w |> Vector.rev = [w>1; w>0]`. §9's `maskBit` is that. -/

-- ⚑ **THE INDEPENDENT SOURCE IS A REAL DEVNET WRAP PROOF'S OWN PUBLIC WORD 29.**
-- `MinaWrapPublicCommGate.PUBLIC_INPUT` is the forty Fq words of a Mina devnet block's Wrap proof,
-- decoded off the wire; slot 29 IS `branch_data`. That block was proved at `proofs_verified = N2`
-- (mask `[tt;tt]`, packing to 3) over a `domain_log2 = 16` step domain, so
-- `Branch_data.Checked.pack` must give `3 + 4·16 = 67` — and it does, which is what makes this a
-- gate rather than a constant agreeing with itself.
/-- ⚑ `Branch_data.Checked.pack` against a REAL devnet Wrap proof's own public word 29, and the
0/2/3 mask shape at all three legal widths. A `[1;0]` mask — the packing `0/1/2` would produce — is
NOT reachable from `ones_vector ∘ rev`, which is exactly why `Prefix_mask.back` can `invalid_arg` on
it out of circuit and no gate refuses it in one. -/
theorem branch_data_packing_matches_a_real_wrap_proof :
    Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD 29 0 = 67
    ∧ branchDataPacked 3 16 = Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD 29 0
    ∧ (runBranch shapeSmoke 2 [0,1,2] [16,16,16]).packedV
        = Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD 29 0
    ∧ (List.range 3).map (fun w => maskBit 2 w 0 + 2 * maskBit 2 w 1) = [0, 2, 3]
    ∧ (runBranch shapeSmoke 0 [0,1,2] [16,16,16]).packedV = 64
    ∧ (runBranch shapeSmoke 1 [0,1,2] [16,16,16]).packedV = 66 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### §11d — the field itself.

A wrap emission whose values were reduced mod `pN` would be accepted by nothing; this is the
tripwire that says which field the file is in.

⚑ **CONVERTED FROM FOUR `#guard`s.** They were four closed instances evaluated by
`unsafe evalExpr Bool`, leaving no term and invisible to the `#assert_namespace_axioms` sweep at the
foot of this file — a `native_decide` with the name, the term and the axiom record deleted. The
facts are pure `Fq` arithmetic on 254-bit literals and `decide` closes every one in the kernel, so
being guards bought nothing and cost the axiom accounting. -/

/-- **THE FIELD IS `Fq`, AND `Fq` IS A FIELD.** `qN ≠ pN` is the tripwire that says which of the two
Pasta primes this file reduces by — a wrap emission reduced mod `pN` is the one mistake that would
be accepted by nothing and visible in nothing. The other three are the ring identities the emitter
relies on every time it writes a negative coefficient as `qSub 0 k`. -/
theorem the_field_is_fq_and_wraps :
    qN ≠ pN
    ∧ qAdd (qN - 1) 1 = 0
    ∧ qMul (qN - 1) (qN - 1) = 1
    ∧ qSub 0 1 = qN - 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ### §11e — ⚑ **WHOSE PROOF THE TRANSCRIPT IS ABOUT.**

Landed 2026-08-05. Until then this pipeline carried **three different step proofs** and every shape
agreed, so nothing could go red:

  * the forty public words (`MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED`) came from
    `pickles_kimchi_marshal`'s step proof — Mina's own SRS, seeded prover;
  * the transcript's absorbed commitments (`RC_SGOLD`/`RC_WCOMM`/`RC_ZCOMM`/`RC_TCOMM`) came from a
    THIRD-PARTY `create_circuit(0,5)` export (`PastaPoseidonFq`);
  * `KimchiStepWrapChainFixture` came from a SECOND binary's own proof, over kimchi's TEST SRS and
    with **`OsRng`** — not reproducible at all.

`prevs = 2`, `wComms = 15`, `tComms = 7` on all three. ⚠ **Same-shape is not same-proof**, and a
census that only counts cannot tell them apart — which is exactly why the pins below compare VALUES,
elementwise, and why the red controls are against the specific objects that used to sit here.

⚑ And `lr`/`delta` were not a borrowed proof's — they were **not a proof's at all**:
`lrPointQ i = xhatBase (5 + i % 50)` made thirty-two of the thirty-three IPA points fifty SRS
Lagrange bases, cycled. `the_ipa_opening_is_not_srs_lagrange_bases` is the control for that. -/

/-- ⚑ **ALL 116 Fq WORDS THE TRANSCRIPT SOURCES ARE THIS PIPELINE'S OWN STEP PROOF'S**, elementwise,
at BOTH committed shapes. Not a length, not a digest, not a sample: `itemVal` is compared against
`KimchiStepWrapChainFixture`'s blocks at every index the schedule reads.

⚠ Two absorbed items are deliberately NOT here and are not claimed: `RC_DIGEST` is Mina's
`step-transaction` key's index digest (§14's `choose_key` anchor) and `x_hat` is §15's MSM output.
So this says the COMMITMENTS are this proof's — it does not say the emitted transcript's β/γ/α/ζ are
this proof's, and they are not. `KimchiStepWrapChain` is where that becomes a theorem. -/
theorem the_transcript_absorbs_this_pipelines_own_step_proof :
    (List.range (2 * shapeWrap.prevs)).all (fun i =>
      itemVal T_SGOLD i
        == Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PREVCOMM_XY.getD i 0) = true
    ∧ (List.range (2 * shapeWrap.wComms)).all (fun i =>
        itemVal T_WCOMM i
          == Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_WCOMM_XY.getD i 0) = true
    ∧ (List.range 2).all (fun i =>
        itemVal T_ZCOMM i
          == Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_ZCOMM_XY.getD i 0) = true
    ∧ (List.range (2 * shapeWrap.tComms)).all (fun i =>
        itemVal T_TCOMM i
          == Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_TCOMM_XY.getD i 0) = true
    ∧ (List.range (4 * shapeWrap.ipaRounds)).all (fun i =>
        itemVal T_LR i
          == Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_LR_XY.getD i 0) = true
    ∧ (List.range 2).all (fun i =>
        itemVal T_DELTA i
          == Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_DELTA_XY.getD i 0) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ **THE CENSUS THOSE WORDS MAKE: 57 POINTS, 114 WORDS**, and it is arithmetic over the SHAPE
rather than a number typed next to a claim. `sg_old 1 + w_comm 15 + z_comm 1 + t_comm 7 = 24` and
`lr 2·16 + delta 1 = 33`. ⚠ `x_hat` is not counted: `w6_xhat` made that pair §15's MSM output, so it
is derived rather than sourced, and counting it would inflate the fixture census by the one pair a
rung earned.

⚠ ⚑ **IT WAS 58 / 116 AND THE NAME SAID SO**, because `shapeWrap.prevs` was `2` while dregg's step
proof carried two recursion slots. `marshal::STEP_RECURSION_SLOTS = 1` took it to one, the transcript
absorbs one `sg_old` point, and `STEP_PREVCOMM_XY` went from four coordinates to two — so the pair of
numbers in the name moved with it. The old name is retired rather than annotated. -/
theorem the_sourced_transcript_census_is_57_points :
    shapeWrap.prevs + shapeWrap.wComms + 1 + shapeWrap.tComms = 24
    ∧ 2 * shapeWrap.ipaRounds + 1 = 33
    ∧ 2 * (shapeWrap.prevs + shapeWrap.wComms + 1 + shapeWrap.tComms)
        + 2 * (2 * shapeWrap.ipaRounds + 1) = 114
    ∧ Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PREVCOMM_XY.length = 2 * shapeWrap.prevs
    ∧ Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_WCOMM_XY.length = 2 * shapeWrap.wComms
    ∧ Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_ZCOMM_XY.length = 2
    ∧ Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_TCOMM_XY.length = 2 * shapeWrap.tComms
    ∧ Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_LR_XY.length
        = 4 * shapeWrap.ipaRounds
    ∧ Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_DELTA_XY.length = 2 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ **RED CONTROL — IT IS NOT THE BORROWED PROOF.** Every block the transcript used to absorb came
from `PastaPoseidonFq`, i.e. from `kimchi/examples/pickles_p6_fq_export.rs`'s `create_circuit(0,5)`
proof. If any of these four were still equal, `the_transcript_absorbs_…` above would be true of a
list that had simply been renamed. -/
theorem the_transcript_is_not_the_borrowed_proof :
    Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PREVCOMM_XY
      ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.PREVCOMM_XY
    ∧ Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_WCOMM_XY
        ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.WCOMM_XY
    ∧ Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_ZCOMM_XY
        ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.ZCOMM_XY
    ∧ Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_TCOMM_XY
        ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.TCOMM_XY := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **RED CONTROL — AND `lr`/`delta` ARE NOT SRS LAGRANGE BASES.** The filler these replaced was
`lrPointQ i = xhatBase (5 + i % 50)` and `deltaPointQ = xhatBase 60`: on-curve, so `Inner_curve.typ`
and `endo_inv` were satisfied, and therefore invisible to every check that existed. **`onCurveQ` was
never going to catch this** — which is the reason the control is an inequality against the specific
points rather than another curve predicate. -/
theorem the_ipa_opening_is_not_srs_lagrange_bases :
    (List.range (2 * shapeWrap.ipaRounds)).all (fun i =>
      lrPointQ i != xhatBase (5 + i % 50)) = true
    ∧ deltaPointQ ≠ xhatBase 60 := by
  refine ⟨rfl, ?_⟩
  decide

/-- ⚑ **AND ALL 58 ARE ON VESTA.** `Openings.Bulletproof.typ`'s `Inner_curve.typ` is `assert_on_curve`
upstream, and `Scalar_challenge.endo_inv` (`scalar_challenge.ml:343-354`) has **no witness at all**
over an off-curve `l` — its `res = [x⁻¹]·l` needs the group. A real opening satisfies this by
construction; measuring it is what makes that a fact about these numbers rather than a deduction
from their provenance. -/
theorem the_transcript_points_are_on_vesta :
    (List.range shapeWrap.prevs).all (fun p =>
      onCurveQ (itemVal T_SGOLD (2 * p), itemVal T_SGOLD (2 * p + 1))) = true
    ∧ (List.range shapeWrap.wComms).all (fun j =>
        onCurveQ (itemVal T_WCOMM (2 * j), itemVal T_WCOMM (2 * j + 1))) = true
    ∧ onCurveQ (itemVal T_ZCOMM 0, itemVal T_ZCOMM 1) = true
    ∧ (List.range shapeWrap.tComms).all (fun j =>
        onCurveQ (itemVal T_TCOMM (2 * j), itemVal T_TCOMM (2 * j + 1))) = true
    ∧ (List.range (2 * shapeWrap.ipaRounds)).all (fun i => onCurveQ (lrPointQ i)) = true
    ∧ onCurveQ deltaPointQ = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑⚑ **THE TRAJECTORY RECORDS THE SCHEDULE'S OWN WORDS — every absorb, both shapes.**

`runSpongeQ` takes a bend pair `(bt, bw)` so §12 can re-run the whole transcript on a prover's chosen
word; the HONEST instance is supposed to pass a `bt` that names no event. It did not.
`mkWrap`'s sentinel was `nItems s + 1` — the **absorb-only** count — while `runSpongeQ` compares it
against the index in the **full event list**, absorbs and squeezes interleaved. At `shapeSmoke` the
stale sentinel landed on a squeeze and did nothing; at `shapeWrap` it landed on `T_LR` item 49 and
replaced round 12's `L.y` with **zero**, putting an off-curve point into W-BULLET's witness. The
prover reported that as `Prover("rest of division by vanishing polynomial")`, which names neither the
word, nor the tag, nor this line.

⚠ **A COUNT COMPARED AGAINST A DIFFERENT NUMBERING'S INDEX** is the whole defect, and no arity
check could see it: both numbers are correct counts of the things they count.

This pin is the one that goes red for it: it compares the schedule's absorb payloads against the
words the trajectory recorded, in order, at both committed shapes. It is not a length and not a
sample — a single overridden word breaks the list equality. -/
theorem the_trajectory_records_the_schedules_own_words :
    ((schedule shapeWrap).filterMap (fun e => match e with | .abs _ w => some w | .sq _ => none))
      = (((mkWrap shapeWrap).sp.evs.filter (fun e => e.isAbs)).map (fun e => e.word))
    ∧ ((schedule shapeSmoke).filterMap (fun e => match e with | .abs _ w => some w | .sq _ => none))
        = (((mkWrap shapeSmoke).sp.evs.filter (fun e => e.isAbs)).map (fun e => e.word)) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ⚑ …and the bend machinery is still ARMED, which is the half that stops the repair above from
being "disable the feature". `mkWrapWith` at an in-range absorb index still moves that word, so §12's
red controls keep working; what changed is only that the HONEST instance can no longer name one. -/
theorem the_bend_still_bends_when_it_is_aimed :
    (mkWrapWith shapeWrap 0 7).sp.evs.head?.map (fun e => e.word) = some 7
    ∧ (mkWrap shapeWrap).sp.evs.head?.map (fun e => e.word) = some RC_DIGEST
    ∧ RC_DIGEST ≠ 7 := by
  refine ⟨rfl, rfl, by decide⟩

/-- ⚑ **ONE `sg_old`, NOT TWO — the defect the move exposed.** `whSgOld` fed `prevWordVal`, i.e.
packed statement words 55/56 and therefore x_hat MSM entries 65/66; `itemVal T_SGOLD` feeds the
TRANSCRIPT, whose cells §21's rows actually hash. The two were separate defs that happened to name
one list, and when `RC_SGOLD` moved to this pipeline's own step proof they came apart **silently** —
`xhatOut 67` did not move, so the emitter's `xhatXY` refusal stayed green while the emitted rows and
the packed words had stopped describing one `sg_old`. A green gate was evidence of the defect.

⚠ ⚑ **AND THE THEOREM THIS REPLACES WAS TRUE OF THE WRONG LIST, WHICH IS WORSE THAN FALSE.** It read
`whSgOld p == itemVal T_SGOLD (2p), (2p+1)` at every `p < prevs` — a statement that identifies the
RECORD's slot `p` with the TRANSCRIPT's slot `p`, and those are the same index only when nothing is
padded. `wrap.rs:476-491` prepends a whole dummy `MessagesForNextWrapProof` and
`wrap.rs:2280-2300` masks the padded slot out of the `OptSponge`, so on a one-`verify_one` rule the
record is `[pad, real]` while the transcript is `[real]`: **record slot `whNPad + j` is transcript
slot `j`.** The old name (`the_wraphack_sg_old_is_the_transcripts`) is retired rather than annotated,
because what it asserted is now false at slot 0 and true at slot 1 for a reason it could not say. -/
theorem the_record_pads_at_the_front_and_its_real_slots_are_the_transcripts :
    -- ⚑ every REAL slot reads the transcript's own cells, at the SHIFTED index…
    (List.range (WH_PADDED - whNPad shapeWrap.prevs)).all (fun j =>
      whSlotSgAt (mkWrap shapeWrap) (whNPad shapeWrap.prevs + j)
        == (itemVal T_SGOLD (2 * j), itemVal T_SGOLD (2 * j + 1))) = true
    -- ⚑ …and the PAD slot reads `Dummy.Ipa.Step.sg`, which is NOT a transcript cell.
    ∧ whNPad shapeWrap.prevs = 1
    ∧ whSlotSgAt (mkWrap shapeWrap) 0 = whPadSg
    ∧ whSlotSgAt (mkWrap shapeWrap) 0 ≠ (itemVal T_SGOLD 0, itemVal T_SGOLD 1)
    -- ⚑ …and the record is the PIPELINE's, not the shape's: the smoke shape gets the same
    -- `[pad, real]` because `whRows` ties slot `p`'s squeeze to packed statement word `55 + p` of
    -- the ONE step proof, whatever wrap shape is emitting.
    ∧ whSlotSgAt (mkWrap shapeSmoke) 0 = whPadSg
    ∧ whSlotSgAt (mkWrap shapeSmoke) 1 = (itemVal T_SGOLD 0, itemVal T_SGOLD 1)
    -- ⚠ ⚑ **AND THE SMOKE SHAPE HAS A TRANSCRIPT SLOT THE RECORD DOES NOT READ, WHICH IS AN OPEN
    -- INCOHERENCE AND IS STATED RATHER THAN AVOIDED.** `shapeSmoke.prevs = 2` while `RC_SGOLD` —
    -- `STEP_PREVCOMM_XY` — carries ONE point, so `itemVal T_SGOLD 2` falls through to a
    -- `wrapFixture`, which is not on the curve. `KimchiWrapMainPins08.prev_step_accs_are_on_vesta`
    -- is red on exactly that, and it is red at HEAD too: the shape was left at 2 when
    -- `marshal::STEP_RECURSION_SLOTS` took the fixture to one point, and
    -- `KimchiWrapMainField` being red kept every consumer from building and saying so.
    ∧ shapeSmoke.prevs = 2
    ∧ Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PREVCOMM_XY.length
        < 2 * shapeSmoke.prevs := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end Dregg2.Circuit.Emit.KimchiWrapMain
