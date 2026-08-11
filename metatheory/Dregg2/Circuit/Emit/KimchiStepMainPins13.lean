/-
`KimchiStepMain` pins — §18.

The values these are stated about are in `…Fixture`; the emission is in `…Core`.
-/
import Dregg2.Circuit.Emit.KimchiStepMainFixture
-- ⚑ §18b's cone reads the PUBLISHED statement and the marshaller's own accumulator, to show that
-- neither is in word 54's preimage. `KimchiStepWrapChainFixture` imports `PastaField` and nothing
-- else, so this edge cannot cycle; it is the same edge `KimchiWrapHackDigest` already carries and
-- names.
import Dregg2.Circuit.Emit.KimchiStepWrapChainFixture

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

/-! ## §18 — THE INTER-STEP TIE: segment D at step `N` against segment C at step `N+1`.

§17 ends on "the refusal belongs to the next step's `verify_one`, through segment C's reconstruction
and the wrap-proof tie". **This section builds that chain and measures whether it refuses.** It is an
EXHIBIT and not a row-set, for the same reason §17 is: the answer decides whether rows are the right
deliverable, and it decides against.

## ⚑ THE TIE, READ AT SOURCE — AND THERE IS NO `Field.Assert.equal` IN IT

`step_main.ml:65-87`, verbatim in shape:

    let statement =
      let prev_messages_for_next_step_proof =                                       (* :66 *)
        hash_messages_for_next_step_proof ~widths ~max_width
          ~proofs_verified_mask:(Vector.trim_front branch_data.proofs_verified_mask …)   (* :70-74 *)
          { app_state ; dlog_plonk_index = d.wrap_key
          ; challenge_polynomial_commitments = prev_challenge_polynomial_commitments   (* :78-79 *)
          ; old_bulletproof_challenges = prev_challenges }                             (* :80 *)
      in
      { Types.Wrap.Statement.messages_for_next_step_proof =
          prev_messages_for_next_step_proof                                          (* :83-84 *)
      ; proof_state = { proof_state with messages_for_next_wrap_proof } }             (* :85-86 *)
    in
    let verified = … verify … ~proof:wrap_proof … statement unfinalized               (* :88, :108 *)

⚑ **The "comparison" is a SUBSTITUTION, not an equality.** The reconstructed digest is placed INTO
the wrap statement (`:83-84`) and that statement is handed to `verify` (`:108`), which packs it
(`step_verifier.ml:1237-1245`, `Spec.pack … to_data statement`) into `public_input` and feeds it to
`multiscale_known` (`:543-545`) — the x_hat MSM — whose output is absorbed at `:560`. Read at source
(`composition_types.ml:854-882`) the packed order is `fp ×5 · challenge ×2 · scalar_challenge ×3 ·
digest ×3 · …`, and `messages_for_next_step_proof` is the THIRD digest, i.e. **word 12**. So the
reconstruction reaches the circuit through exactly one wire: term 12's MSM scalar.

⚠ **That wire is named simplification #2's open residue**, which is why this section can measure the
tie but not emit it: #2 is "term `i`'s scalar must BE Wrap statement word `i`", and a `Digest` packs
at 255 bits (`spec.ml:376-392`) where R3 runs a uniform 26 chunks. Emitting term 12 alone at 51
chunks is the per-word width vector #2 already prices. **It would not change the verdict below** —
see (c) — so it is not taken here.

## ⚑ THE CHAIN, AND WHY THE TWO HASHES ARE ONE OBJECT

Segment D at step `N` (`step_main.ml:525-566`) absorbs
`(dlog_plonk_index_N, app_state_N, G_N, bulletproof_challenges_N)`; its squeeze is step `N`'s public
`messages_for_next_step_proof` (`:572-573`). Segment C at step `N+1` (`:59-81`) absorbs
`(dlog_plonk_index_prev, app_state_N, sg_old, prev_challenges)`, masked. `per_proof_witness.ml:
90-97` says what those two witness fields are: `prev_challenges` are "the challenges c_0 … c_{k-1}
corresponding to each W_i" and `prev_challenge_polynomial_commitments` "the commitments to the
challenge polynomials … corresponding to each of the prev_challenges" — i.e. step `N`'s own
`G` and `bulletproof_challenges`.

⚑⚑ **AND THE TIE HAS A PREMISE — NAMED SINCE 2026-08-07, WHEN THE TWO PREFIXES STOPPED BEING ONE.**
This paragraph read *"onto a `Sponge.copy` of `sponge_after_index`"* and *"onto the SAME copy
point"*, and on that reading the index prefix cancelled: both hashes absorbed the same 56 words, so
the tie was a `Nat` equality with nothing to say about keys. It is not the same copy point.
`step.rs:2718` hands the OUTER hash `merge::dlog_plonk_index(wrap_prover)` — **the instance's own
wrap verification key** — while each `expand_proof` gets the PREVIOUS branch's (`:2725,2734`). So
the two prefixes are two different keys, and the honest-chain statement is:

> **step `N+1` reconstructs step `N`'s squeeze IFF the key it absorbs as the previous branch's IS
> step `N`'s own wrap key.**

Which is what an honest chain means, and is strictly more than the old equality said. `hmChainSpec`
therefore takes the absorbed `key` as a parameter and (a) below states the tie AT step `N`'s own key
(`idxOVal`) while (a′) states the REFUSAL at a different one (`idxVal`, block 539508's) — the leg
that says the tie BINDS the key rather than cancelling it.

It is pinned below and it is not a definition: the two segments have different
word lists, different lengths, different masks and different app-state fixtures, and they coincide
only if the mask, the interleave (`composition_types.ml:595-607`), the key and the block
alignment are all right.

## ⚑⚑ THE VERDICT — READ IT BEFORE QUOTING THE SECTION

**The inter-step tie does NOT refuse the substituted commitment. It PROPAGATES it.** A prover who
substitutes at step `N` and re-solves `G` moves step `N`'s public word 7; at step `N+1` he carries
`sg_old := G_resolved`, and the reconstruction reproduces the MOVED word exactly. (b) below measures
that on the emitted segments. What the tie buys is real and smaller than a refusal: it FORCES
`sg_old` at `N+1` to be the `G` the prover used at `N` — he cannot launder the fake commitment away
between steps — and (d) measures that direction as a refusal.

⚠ **So the brief's premise, and §17(f)(ii)'s wording, are corrected in place**: the reconstruction is
not what refuses a substituted `G`. What refuses it is one link FURTHER — the accumulator check that
`per_proof_witness.ml:12-32` states in prose:

> "This part of the accumulator state is finalized by checking that `challenge_polynomial_commitment`
> is a commitment to the polynomial `f_c := prod (1 + c_i x^{2^{k-1-i}})` … instead of checking this,
> we get an evaluation `E_c` at a random point zeta and check that `challenge_polynomial_commitment`
> **opens** to `E_c` at zeta. Then we will need to check that `E_c = f_c(zeta)`."

Two legs. **Since 2026-08-02 this assembly has the FIRST and not the second**, and the verdict below
is unchanged by that:

  * **`E_c = f_c(ζ)` — COMPUTED (§8i).** The `sg_evals` prefix entries `vEz 0/1` and `vEw 0/1` were
    `evVal` FIXTURES (simplification #4's residue verbatim); they are now the outputs of four `f_c`
    ladders over `vPrevChal` at ζ and ζω, and (f) below pins them against `KimchiVerify.bEvalSq`,
    pins that they are NOT `f_c` of the challenges segment D absorbs (the vacuous closure), and
    pins the read-set disjointness in both directions so a future conflation reds.
  * **`sg_old` OPENS to `E_c`** — the IPA opening at step `N+1`. That is `verified` (#11), and it is
    the same object §17 stops at. **It is an ASSUMPTION, not a gate**, at every step of the chain.

⚠ ⚑ **AND LEG ONE ALONE DOES NOT REFUSE THE SUBSTITUTION — (b) IS RE-RUN AND IS UNCHANGED.** `E_c`
is a function of `prev_challenges` and ζ; `sg_old` does not occur in it. A prover who substitutes an
absorbed commitment and re-solves `G` carries the SAME `prev_challenges` forward, so every one of the
four computed entries is the value it would have been, and the chain closes exactly as (b) measures.
What the leg buys is that the accumulator state the next step carries is now CONSTRAINED to be the
b-polynomial of the challenges it also hashes, instead of four free witnesses — i.e. it removes a
second, independent forgery surface (`E_c` chosen freely) rather than closing this one.

So the honest shape of the whole result is: `G` is bound to step `N`'s statement (§8e′), FORCED
forward into `sg_old` at step `N+1` (this section), `E_c` is now the right POLYNOMIAL EVALUATION
(§8i), and the two still MEET only through a commitment-opening that no rung of this assembly emits.
The substituted witness is accepted at every one of those rungs. -/

-- ⚑ **THE PARAMETERISATION IS FAITHFUL**: at this instance's own values AND AT SEGMENT C'S OWN KEY
-- `hmChainSpec` IS `hmSpec`, word for word — same variables, same order, same length. So every
-- measurement below is about the emitted segment C and not about a second model of it.
-- ⚠ `idxVal` and not `idxOVal` HERE, and the difference is the point: `hmSpec` is segment C, which
-- absorbs the PREVIOUS branch's key (`step.rs:2725,2734`). The chain legs above run at `idxOVal`
-- because there the absorbed key is step `N`'s own — see §18's premise.
#guard (hmChainSpec shapeSmoke idxVal hmVal (chainSlot0 shapeSmoke tS.ipa).1 (chainSlot0 shapeSmoke tS.ipa).2
          (sgOldVal tS.ipa 1 0, sgOldVal tS.ipa 1 1)
          (fun k => prevChalVal (shapeSmoke.bRounds + k))).ws == (hmSpec shapeSmoke tS.ipa).ws
#guard hmChainDigest shapeSmoke idxVal hmVal (chainSlot0 shapeSmoke tS.ipa).1 (chainSlot0 shapeSmoke tS.ipa).2
          (sgOldVal tS.ipa 1 0, sgOldVal tS.ipa 1 1)
          (fun k => prevChalVal (shapeSmoke.bRounds + k))
        == (tS.segC.states.getLastD []).getD 0 0

#guard wordSeven tS tS.gAccXY == (stepPublic tS).getD 7 0

-- ⚑⚑ **(a) THE HONEST CHAIN CLOSES.** Step `N+1`'s segment C, fed step `N`'s app state, `G` and
-- returned bulletproof challenges, reconstructs step `N`'s public word 7 EXACTLY. This is the
-- reconstruction-and-comparison, and it is the first time the two hashes are shown to be the two
-- ends of one chain rather than two sponges that happen to share a copy point.
#guard hmChainDigest shapeSmoke idxOVal hmOVal (chainSlot0 shapeSmoke tS.ipa).1
          (chainSlot0 shapeSmoke tS.ipa).2 tS.gAccXY (chainChals shapeSmoke tS.sp)
        == wordSeven tS tS.gAccXY
-- …and it is not trivially true: segment C's own app-state fixture gives a DIFFERENT digest, so the
-- identity is carrying the chained app state and not ignoring it.
#guard hmChainDigest shapeSmoke idxOVal hmVal (chainSlot0 shapeSmoke tS.ipa).1
          (chainSlot0 shapeSmoke tS.ipa).2 tS.gAccXY (chainChals shapeSmoke tS.sp)
        != wordSeven tS tS.gAccXY

/-- ⚑⚑ **(a′) THE TIE BINDS THE KEY — AND THIS IS THE LEG THAT DID NOT EXIST BEFORE 2026-08-07.**

The premise §18's header now names: step `N+1` reconstructs step `N`'s squeeze **iff** the
`dlog_plonk_index` it absorbs as the previous branch's IS step `N`'s own wrap key. (a) is the `iff`'s
forward half at `idxOVal`; this is the other half. `idxVal` is `MinaStepPrevCommitments`' 56 words —
Mina devnet block 539508's `wrap-transaction` key, i.e. a DIFFERENT branch's — and against it the
reconstruction must MISS.

⚠ **Until segment D got its own index this leg was not merely unproved, it was UNSTATABLE**:
`hmChainSpec` hard-coded `idxVal` on one side while `hmOutSpec` was a `Sponge.copy` of the other, so
both digests absorbed the same 56 words by construction and no choice of key could separate them. A
tie whose premise cannot be falsified is not a tie; it is a definition wearing one's clothes.

`segd_slot12_probe`'s CONTROL 2 is the same statement from the Rust side, against openmina's own
`MessagesForNextStepProof::hash()`. -/
theorem the_inter_step_tie_binds_the_absorbed_wrap_key :
    (hmChainDigest shapeSmoke idxOVal hmOVal (chainSlot0 shapeSmoke tS.ipa).1
        (chainSlot0 shapeSmoke tS.ipa).2 tS.gAccXY (chainChals shapeSmoke tS.sp)
       == wordSeven tS tS.gAccXY)
    ∧ (hmChainDigest shapeSmoke idxVal hmOVal (chainSlot0 shapeSmoke tS.ipa).1
        (chainSlot0 shapeSmoke tS.ipa).2 tS.gAccXY (chainChals shapeSmoke tS.sp)
       != wordSeven tS tS.gAccXY) := by
  native_decide

#assert_compiled the_inter_step_tie_binds_the_absorbed_wrap_key

-- ⚑⚑ **(b) THE DELIVERABLE. THE SUBSTITUTED CHAIN CLOSES TOO — THE TIE DOES NOT REFUSE IT.**
-- Step `N` is `tSwapAbs` with `G` re-solved (§17(c)/(e)); its public word 7 has MOVED (§17(d)).
-- Step `N+1` carries `sg_old := G_resolved` and step `N`'s challenges, and the reconstruction
-- reproduces the moved word. Nothing anywhere in the chain objects.
#guard hmChainDigest shapeSmoke idxOVal hmOVal (chainSlot0 shapeSmoke tSwapAbs.ipa).1
          (chainSlot0 shapeSmoke tSwapAbs.ipa).2 bpGResolvedA (chainChals shapeSmoke tSwapAbs.sp)
        == wordSeven tSwapAbs bpGResolvedA
-- …and this really is the §17(e) witness and not a re-run of the honest one: the two chains'
-- digests differ, and `equal_g` still closes on the substituted one.
#guard wordSeven tSwapAbs bpGResolvedA != wordSeven tS tS.gAccXY
#guard bpCloses (bpUOf tSwapAbs) GENERATORS_H (bpLhsOf tSwapAbs) bpGResolved
                (bpBOf tSwapAbs) BP_Z1 BP_Z2

-- ⚑ **(c) AND A WHOLE FAMILY OF CHAINS CLOSES, because `z₁`/`z₂` occur in NEITHER segment.**
-- Re-solving at `z₁ = z₂ = 1` reaches a third commitment; its chain closes just as well. So the tie
-- constrains WHICH `G` is carried forward, not WHETHER a satisfying `G` exists.
#guard onCurveA bpG11 && bpG11 != bpGResolvedA && bpG11 != bpGHonestA
#guard hmChainDigest shapeSmoke idxOVal hmOVal (chainSlot0 shapeSmoke tSwapAbs.ipa).1
          (chainSlot0 shapeSmoke tSwapAbs.ipa).2 bpG11 (chainChals shapeSmoke tSwapAbs.sp)
        == wordSeven tSwapAbs bpG11
-- …and the reason is structural: `G` is a word of segment D and of NEITHER other place, while `z₁`
-- and `z₂` are not variables of this assembly at all. So the chain can move with `G` and cannot move
-- with the response scalars.
-- ⚑ SINCE 2026-08-11 the cell is `vGaX`, not `vGx`: segment D absorbs the record's own accumulator
-- and §19's ladder keeps `solveG`'s solve, so the two `G`s are two cells (`KimchiStepMainCore.vGaX`).
-- The structural fact this states is unchanged — segment D has it and segment C does not — and it is
-- stated about the cell segment D actually carries. `vGx` is now in NEITHER segment.
#guard (tS.specD.ws.map (·.1)).countP (fun v => v == vGaX shapeSmoke) == 1
#guard (tS.specC.ws.map (·.1)).countP (fun v => v == vGaX shapeSmoke) == 0
#guard (tS.specD.ws.map (·.1)).countP (fun v => v == vGx shapeSmoke) == 0

-- ⚑⚑ **(d) THE DIRECTION THE TIE DOES REFUSE — and it is the reason the tie is not nothing.**
-- A prover who moves step `N`'s word 7 and then carries the HONEST `G` forward at step `N+1` is
-- REFUSED: the reconstruction no longer equals the word the wrap proof was made for. So the fake
-- commitment cannot be laundered away between steps; it must be carried.
#guard hmChainDigest shapeSmoke idxOVal hmOVal (chainSlot0 shapeSmoke tSwapAbs.ipa).1
          (chainSlot0 shapeSmoke tSwapAbs.ipa).2 tS.gAccXY (chainChals shapeSmoke tSwapAbs.sp)
        != wordSeven tSwapAbs bpGResolvedA
-- …and each of the other three chained quantities is covered in the same direction:
--   the carried challenges,
#guard hmChainDigest shapeSmoke idxOVal hmOVal (chainSlot0 shapeSmoke tSwapAbs.ipa).1
          (chainSlot0 shapeSmoke tSwapAbs.ipa).2 bpGResolvedA
          (fun k => if k == 0 then fAdd (chainChals shapeSmoke tSwapAbs.sp 0) 1
                    else chainChals shapeSmoke tSwapAbs.sp k)
        != wordSeven tSwapAbs bpGResolvedA
--   the app state,
#guard hmChainDigest shapeSmoke idxOVal (fun i => fAdd (hmOVal i) 1)
          (chainSlot0 shapeSmoke tSwapAbs.ipa).1 (chainSlot0 shapeSmoke tSwapAbs.ipa).2
          bpGResolvedA (chainChals shapeSmoke tSwapAbs.sp)
        != wordSeven tSwapAbs bpGResolvedA
--   and either coordinate of the carried commitment alone.
#guard hmChainDigest shapeSmoke idxOVal hmOVal (chainSlot0 shapeSmoke tSwapAbs.ipa).1
          (chainSlot0 shapeSmoke tSwapAbs.ipa).2 (fAdd bpGResolvedA.1 1, bpGResolvedA.2)
          (chainChals shapeSmoke tSwapAbs.sp)
        != wordSeven tSwapAbs bpGResolvedA
#guard hmChainDigest shapeSmoke idxOVal hmOVal (chainSlot0 shapeSmoke tSwapAbs.ipa).1
          (chainSlot0 shapeSmoke tSwapAbs.ipa).2 (bpGResolvedA.1, fAdd bpGResolvedA.2 1)
          (chainChals shapeSmoke tSwapAbs.sp)
        != wordSeven tSwapAbs bpGResolvedA

-- ⚑ **(e) THE OTHER DIRECTION: what the comparison does NOT cover, and the MASKED SLOT.**
-- With `Prefix_mask.there N1 = [0,1]` (`pickles_base/proofs_verified.ml:75-81`, §8h) slot 0 is the
-- `Wrap_hack` dummy: bending its commitment or ANY of its challenges leaves the reconstruction
-- exactly where it was. It bites only if both mask bits are on — which is the `N2` instance, not
-- this one.
#guard MASK_BITS == [0, 1]
#guard hmChainDigest shapeSmoke idxOVal hmOVal (fAdd (chainSlot0 shapeSmoke tSwapAbs.ipa).1.1 1,
            (chainSlot0 shapeSmoke tSwapAbs.ipa).1.2)
          (chainSlot0 shapeSmoke tSwapAbs.ipa).2 bpGResolvedA (chainChals shapeSmoke tSwapAbs.sp)
        == wordSeven tSwapAbs bpGResolvedA
#guard hmChainDigest shapeSmoke idxOVal hmOVal (chainSlot0 shapeSmoke tSwapAbs.ipa).1
          (fun k => fAdd (prevChalVal k) 1) bpGResolvedA (chainChals shapeSmoke tSwapAbs.sp)
        == wordSeven tSwapAbs bpGResolvedA
-- …and with BOTH bits on it does bite, so the control is about the mask and not about the slot.
#guard hmChainDigestMask shapeSmoke [1, 1] idxOVal hmOVal
          (fAdd (chainSlot0 shapeSmoke tSwapAbs.ipa).1.1 1,
           (chainSlot0 shapeSmoke tSwapAbs.ipa).1.2)
          (chainSlot0 shapeSmoke tSwapAbs.ipa).2 bpGResolvedA (chainChals shapeSmoke tSwapAbs.sp)
        != hmChainDigestMask shapeSmoke [1, 1] idxOVal hmOVal (chainSlot0 shapeSmoke tSwapAbs.ipa).1
          (chainSlot0 shapeSmoke tSwapAbs.ipa).2 bpGResolvedA (chainChals shapeSmoke tSwapAbs.sp)
-- …and the two quantities the MIS-WIRED segment C used to hash are in neither word list, so no
-- bend of `x_hat` or of the fold output `q` can reach this comparison at all (§12k's other half).
#guard (tS.specC.ws.map (·.1)).all (fun v =>
  v != mpx shapeSmoke (pSum shapeSmoke (shapeSmoke.msmTerms - 2))
  && v != ipx shapeSmoke (qSum shapeSmoke (shapeSmoke.ipaRounds - 1)))

/-! ### ⚑ (f) LEG ONE OF THE ACCUMULATOR CHECK — `E_c = f_c(ζ)` OVER `prev_challenges`, COMPUTED.

`per_proof_witness.ml:12-21`: the accumulator is finalised by checking that `sg_old` OPENS at ζ to
`E_c`, and that `E_c = f_c(ζ) = ∏_i (1 + c_i·ζ^{2^{k−1−i}})` over the CARRIED challenges. The
CONSTRUCTION is `step_verifier.ml:935-948` — `sg_olds = Vector.map prev_challenges ~f:
challenge_polynomial` and `sg_evals pt = Vector.map2 mask sg_olds ~f:(fun keep f -> (keep, f pt))`
at `plonk.zeta` and `zetaw` — and those two vectors are `combine`'s own prefix (`:1076-1102`,
`List.append sg_evals ([| Some x_hat |] :: [| Some ft |] :: a)`), i.e. exactly `EV_PREFIX`'s first
two entries. `challenge_polynomial` is `∏_i (1 + chals[i]·pt^{2^{k−1−i}})`
(`wrap_verifier.ml:16-36`), which is `bEvalSq`'s own convention.

⚑⚑ **AND SINCE §8i THAT PREFIX IS COMPUTED — this subsection is the measurement of leg ONE, not of
its absence.** `vEz 0/1` and `vEw 0/1` were `evVal` fixtures (#4's residue) until 2026-08-02; they
are now the outputs of four `f_c` ladders whose challenge operand is `vPrevChal`. What that buys and
what it does not:

  * `prev_challenges` reach the r5 sub-circuit AT ALL for the first time — below this they had no
    cell before `r7_absorption`, where segments A and C absorb them — and through `combine` they
    reach `combined_inner_product`, which is a PUBLIC WORD and a statement word R8 binds. That is the
    first time the carried accumulator state constrains anything this circuit outputs.
  * ⚠ **IT IS STILL NOT A REFUSAL OF THE SUBSTITUTION.** `E_c` is a function of `prev_challenges`
    and of ζ, and of NOTHING ELSE — `sg_old` does not occur in it. The relation between the
    commitment and the value it must open to is leg TWO, the opening, which is `verified` (#11), a
    witnessed boolean. (b) above is unchanged and re-runs unchanged: the substituted chain closes.
  * ⚠ **`prev_challenges` are still fixtures** (`prevChalVal`) and so is the app state, so what is
    measured here is the WIRE — that the emitted value IS `f_c` of THOSE cells — and not a value
    claim about a real accumulator.
  * ⚑⚑ **`combine`'s `Opt.Maybe` mux IS NOW EMITTED (2026-08-02, §12l) — and it MOVED public word 9,
    including at the deployed mask.** This bullet used to read "still not emitted; `cipRows` folds
    all `cipEvals` entries unconditionally". It does not any more: the two `Maybe` steps run
    `Field.if_ keepⱼ` off §8h's derived bits (`common.ml:270-271`), +3 `Generic` rows.
    ⚠ And the expectation that came with the residue was wrong at source. `mul_and_add`'s `else_`
    branch is bare `acc` — no ξ — and `Pcs_batch.combine_split_evaluations` folds the flattened list
    in REVERSE (`pcs_batch.ml:88-94`), so slot 0 is the LAST step and dropping it takes one ξ power
    off all 46 surviving terms. "Slot 0 is the `Wrap_hack` dummy, so at `[0,1]` this is a no-op" is
    FALSE; §12l measures all three legal masks and they are three different field elements.
    ⚠ **It changes no verdict here.** `combined_inner_product` is a value R8 ties to a statement
    word; moving it moves what an honest prover must claim, and (b) below is unchanged. -/

-- ⚑⚑ **LEG ONE, COMPUTED.** The four emitted prefix entries ARE `f_c` over the carried challenges —
-- against `KimchiVerify.bEvalSq`, the READ-ONLY transcription of `b_poly`, at the emitted ζ and the
-- emitted ζω. Not `runDef`'s own recursion restated: `bEvalSq` is a different definition in a
-- different module, tied to `bEval` by a theorem.
#guard ((tS.df.ez.getD 1 0 : Nat) : ZMod pN)
        == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) prevUs
#guard ((tS.df.ew.getD 1 0 : Nat) : ZMod pN)
        == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetawLS : Nat) : ZMod pN) prevUs
#guard ((tS.df.ez.getD 0 0 : Nat) : ZMod pN)
        == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) prevUs0
#guard ((tS.df.ew.getD 0 0 : Nat) : ZMod pN)
        == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetawLS : Nat) : ZMod pN) prevUs0
-- …and each of the four is a DIFFERENT value, so "all four are `f_c`" is not four names for one
-- number, and the two SLOTS really carry different challenge runs.
#guard [tS.df.ez.getD 0 0, tS.df.ez.getD 1 0, tS.df.ew.getD 0 0, tS.df.ew.getD 1 0].dedup.length == 4
-- …and NONE of them is the fixture it replaced, which is the retirement stated as a red control:
-- the previous four values are still computable and are still not `f_c`.
#guard (List.range 2).all (fun j =>
  tS.df.ez.getD j 0 != evVal j 0 && tS.df.ew.getD j 0 != evVal j 1)
#guard (((evVal 1 0 : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) prevUs) == false

-- ⚑⚑ **THE TRAP THIS RUNG IS BUILT AROUND, PINNED IN BOTH FORMS.** `f_c` over `prev_challenges` is
-- NOT `f_c` over the challenges segment D absorbs — upstream's own `step_verifier.ml:918`, "You use
-- the NEW bulletproof challenges to check b. Not the old ones." A conflation would close leg one
-- vacuously, and it now REDS: first as a value inequality, then as a read-set disjointness on the
-- emitted rows, which is the form a future edit is most likely to break.
#guard (Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) prevUs
         == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) usS) == false
#guard (((tS.df.ez.getD 1 0 : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) usS) == false
-- …and `b(ζ)` — the ladder over the NEW challenges, which R8's `b_correct` binds — is a different
-- number from every one of the four, so the two vectors are apart at the emitted values too.
#guard (List.range 2).all (fun j =>
  tS.df.accs.getLastD 0 != tS.df.ez.getD j 0 && tS.df.accs.getLastD 0 != tS.df.ew.getD j 0)
-- ⚑ **THE READ-SET, both directions.** §8i's rows read `vPrevChal` and NOT ONE `vLift (uChal k)`;
-- `deferredRows`' rows read every `vLift (uChal k)` and NOT ONE `vPrevChal`. Neither statement is a
-- floor. A future edit that wires the ladders to the transcript's own challenges — the vacuous
-- closure — breaks the first; one that drops the carried wire breaks it too.
#guard (List.range shapeSmoke.bRounds).all (fun k =>
  (ecRowVars.contains (vLift shapeSmoke (shapeSmoke.uChal k))) == false)
#guard (List.range shapeSmoke.bRounds).all (fun k =>
  defRowVars.contains (vLift shapeSmoke (shapeSmoke.uChal k)))
#guard (List.range (2 * shapeSmoke.bRounds)).all (fun i =>
  ecRowVars.contains (vPrevChal shapeSmoke i))
#guard (List.range (2 * shapeSmoke.bRounds)).all (fun i =>
  (defRowVars.contains (vPrevChal shapeSmoke i)) == false)

-- ⚑⚑ **THE RED CONTROL IN THE DIRECTION THAT MUST MOVE**: bend ONE carried challenge word and `E_c`
-- moves, its slot's BOTH points move, and `combined_inner_product` — a public word — moves with it.
-- Run on `runDef` at the assembly's own ζ, ξ and r, so only the carried vector differs.
#guard dfBent.ez.getD 1 0 != tS.df.ez.getD 1 0
#guard dfBent.ew.getD 1 0 != tS.df.ew.getD 1 0
#guard dfBent.ca.getLastD 0 != tS.df.ca.getLastD 0
-- …and it moves the KEPT slot ONLY — the dummy slot's two entries are untouched, so the bend is
-- reaching one ladder and not smearing across the region.
#guard dfBent.ez.getD 0 0 == tS.df.ez.getD 0 0 && dfBent.ew.getD 0 0 == tS.df.ew.getD 0 0
-- ⚑ **AND THE DIRECTION THAT MUST NOT MOVE**: substitute the challenges segment D absorbs — this
-- proof's OWN returned bulletproof challenges — for the carried vector and every one of the four
-- entries lands somewhere else. That is the conflation, priced on the emitted values.
#guard dfConflated.ez.getD 1 0 != tS.df.ez.getD 1 0
#guard dfConflated.ew.getD 1 0 != tS.df.ew.getD 1 0
#guard dfConflated.ca.getLastD 0 != tS.df.ca.getLastD 0
-- …and `b(ζ)`, which reads the NEW challenges, is IDENTICAL across all three — it is the other
-- vector's ladder and no bend of the carried one may touch it.
#guard dfBent.accs.getLastD 0 == tS.df.accs.getLastD 0
#guard dfConflated.accs.getLastD 0 == tS.df.accs.getLastD 0
-- ⚑ **`zetaw` IS ONE CELL.** `:934` binds it once; `sg_evals` (`:948`) and `b_correct` (`:1124`)
-- read that binding. R8's program no longer recomputes `ω·ζ` — its `zetaw` slot is an ALIAS of
-- §8i's `vZW 0`, which is what makes the two readings one σ class rather than two equal numbers.
#guard finS.fp.prog.getD finS.fp.slots.zetaw default == AOp.inp (vZW shapeSmoke 0)
#guard finVal finS.fp.slots.zetaw == zetawLS && tS.df.zws.getD 0 0 == zetawLS
-- …and ζω's ladder is `pow_two_pows`' own recurrence, at the length upstream computes.
#guard tS.df.zws.length == shapeSmoke.bRounds
#guard (List.range (shapeSmoke.bRounds - 1)).all (fun k =>
  tS.df.zws.getD (k + 1) 0 == fMul (tS.df.zws.getD k 0) (tS.df.zws.getD k 0))
-- …and ζω ≠ ζ, so the two points are two points (a degenerate ω would make half the region a copy).
#guard zetawLS != zetaLS && FT_OMEGA != 1

-- ⚑⚑ **THE LADDER POSITION — `prev_challenges` REACH THE CIRCUIT'S OUTPUT.** Below §8i a carried
-- challenge had NO cell at `r5_full`: its only consumers were segments A and C, which are R7's. It
-- now has exactly TWO there (its slot's ζ ladder and its slot's ζω ladder), and the class grows by
-- the two absorptions at `r7_absorption`. Equalities, not floors.
#guard (classCells (posAt .ipa) (vPrevChal shapeSmoke shapeSmoke.bRounds)).length == 0
#guard (classCells (posAt .full) (vPrevChal shapeSmoke shapeSmoke.bRounds)).length == 2
#guard (classCells (posAt .ftEval0) (vPrevChal shapeSmoke shapeSmoke.bRounds)).length == 2
#guard (classCells (posAt .absorb) (vPrevChal shapeSmoke shapeSmoke.bRounds)).length == 4
-- …and the prefix entries themselves went from FREE WITNESSES the fold read to DERIVED cells: at
-- `r5_full` `vEz 1`'s class is the fold's own read, its ladder's closing row and its probe.
#guard (classCells (posAt .full) (vEz shapeSmoke 1)).length == 3
#guard (classCells (posAt .full) (vEw shapeSmoke 1)).length == 3
-- …while the entries this leg does NOT cover — `x_hat` at 2, `ft_eval0` at 3 — keep exactly the one
-- fold read they had, so the pin says "two of four", which is what `combine`'s prefix is.
#guard (classCells (posAt .full) (vEz shapeSmoke 2)).length == 1
#guard (classCells (posAt .full) (vEw shapeSmoke 2)).length == 1
-- ⚑ …and the OUTPUT reach, stated as the wire it is: `combined_inner_product` is public word 9 and
-- `vCipShift` is public word 0, and R8's `combined_inner_product_correct` ties them. So a carried
-- challenge now reaches a public word through rows, not through a comment.
#guard (exposedVars shapeSmoke).getD 9 (xv 0) == vCa shapeSmoke shapeSmoke.cipEvals
#guard (exposedVars shapeSmoke).getD 0 (xv 0) == vCipShift shapeSmoke
#guard (stepPublic tS).getD 9 0 == (tS.df.ca.getLastD 0 : Int)

-- ⚑ **(g) AND THE OTHER LEG IS THE OPENING, WHICH IS `verified` (#11) AND AN ASSUMPTION.**
-- With `G` bound to the statement (§8e′) and FORCED forward by (a)/(d), what is left between the
-- substituted commitment and a refusal is: `G_resolved` must open at ζ to `f_c(ζ)`. No rung of this
-- assembly emits that opening — `rhs`/`equal_g` are not emitted (§17), and `verified` is a witnessed
-- boolean. ⚠ There is no `#guard` that says "that is hard"; what IS measurable is that the prover's
-- solve stays available in the direction he needs and closes on the substituted chain, which is (b),
-- and that with `G` held fixed it does not (§17(g)). The residue is the two-dimensional discrete log
-- in `⟨G + b·u, H⟩` and it is stated as an ASSUMPTION, not as a gate.
#guard bpCloses (bpUOf tSwapAbs) GENERATORS_H (bpLhsOf tSwapAbs)
                (jOf bpGResolvedA) (bpBOf tSwapAbs) BP_Z1 BP_Z2
#guard (jacEqM pN (bpRhs (bpUOf tSwapAbs) GENERATORS_H (jOf bpGHonestA) (bpBOf tSwapAbs)
                     BP_Z1 BP_Z2) (jOf (bpLhsOf tSwapAbs))) == false

/-! ### §18b — ⚑⚑⚑ **THE TRANSITIVE INPUT CONE OF PACKED WORD 54, COMPUTED RATHER THAN ASSERTED.**

Word 54 is `messages_for_next_step_proof`, and it is Mina's wrap public-input **slot 12** — the one
slot of the forty the emitted wrap vector does not agree with
(`KimchiWrapMainPins12.the_forty_agree_at_every_slot`, 39 of 40). Three
structural explanations for that miss have been written into `KimchiWrapMainPins10` and refuted at
source: the outer hash (refuted by the index repair), an arity gap (refuted 2026-08-07 —
`marshal::STEP_RECURSION_SLOTS = gates::STEP_RULE_N_PREVIOUS = 1`), and a **fixpoint**:

> *"Making the wire record carry segment D's `G` and lifts moves the step proof's PUBLIC INPUT at
> word 54; the step transcript absorbs the public-input commitment; `solveG`'s output is derived
> from that transcript."*

⚑ **THAT IS FALSE, AND THIS IS THE MEASUREMENT RATHER THAN A READING OF THE DEFINITION GRAPH.**
`hmOutSpec` names word 54's ENTIRE preimage, so the cone is not an approximation: it is the
`ws` list, seventy-six cells, and the theorem exhibits all four families at their own sources.

  * 56 — `MinaWrapOwnVerifierKey.INDEX_WORDS`, dregg's own wrap verification key. ⚠ This is the one
    link that *looks* circular and is not, for exactly the reason `§10b` measures on the other side:
    the wrap circuit pins the STEP key as `Inner_curve.constant` (coefficients), while the step
    circuit takes the WRAP key as `w.exists` (a **witness**, `idxOVar`). A witness does not enter a
    verification key, so the wrap VK is a function of the step VK and not conversely
    (`KimchiStepWrapChain.the_wrap_gates_carry_the_step_key_and_none_of_the_step_proofs_values`).
  * 2 — the app state, `hmOVal`, closed arithmetic.
  * 2 — `G`, `solveG`'s output, a function of the transcript over the PREVIOUS proof's commitments.
  * 16 — `liftOf … (uChal k)`, the same transcript's own prechallenges, lifted.

**And the negative leg is the whole point: not one of the sixty-seven published statement entries is
in the cone, and neither is `STEP_PREVCOMM_XY`** — the commitment the marshaller chose, which is what
words 55 and 56 are computed from (`whPrevDigest`). So word 54 is not downstream of the step
statement, of the step proof, or of the marshaller. **The dependency is a DAG and the pass order
terminates in ONE pass:**

    block 539508's commitments  →  step transcript  →  { G , the 16 lifts }  →  segment D  →  word 54
                                →  whPrevDigest → words 55/56 → step public input → step proof

Word 54 is settled at the third arrow; nothing after it re-enters. `whPrevDigest` hangs off the same
first arrow and off `STEP_PREVCOMM_XY`, which is an ARGUMENT to `create_recursive` rather than a
value it returns — that is `KimchiWrapMainPins12.the_wraphack_tape_reads_no_published_statement_entry`,
and it is why 55/56 closed in one re-prove on 2026-08-06.

⚠ ⚑ **SO WHAT DOES BLOCK SLOT 12 IS NOT A LOOP.** The two sides of slot 12 hash the same
seventy-six-cell shape (`segd_slot12_probe` reproduces this squeeze to the digit with openmina's own
`MessagesForNextStepProof::hash()`), so there is no sponge gap. They disagree on **TWO** of the four
families, and the two have different prices:

  * ⚑ **the sixteen challenges — a ONE-VECTOR DECISION, and the "arity blocker" was a conflation
    (SETTLED AT SOURCE 2026-08-10).** Segment D absorbs `liftOf … (uChal k)`; the marshaller's
    `step_pre` is a `k·0x9E3779B97F4A7C15 | 1` ladder chosen in `prove_step`. This bullet read
    *"only FIFTEEN of them are published … `uChal 0` is in no published entry"* and therefore
    *"either the statement grows a word or the sixteenth travels out of band"*. **Both are wrong.**
    Upstream's `messages_for_next_step_proof.old_bulletproof_challenges` (`transaction.rs:3746`) is
    never a statement word at all — `MessagesForNextStepProof::to_fields`
    (`transaction.rs:3770-3805`) lays it in a POSEIDON PREIMAGE and publishes only the digest
    (`prepared_statement.rs:123`, slot 12; entry 64 of the sixty-seven). And `uChal 0` **is**
    published — at **slot 13 of the FORTY**, agreeing with the referee
    (`KimchiWrapMainPins12.the_forty_agree_at_every_slot`). What the sixty-seven's entries
    48…62 hold upstream is a DIFFERENT family: the previous wrap proof's fifteen Tock challenges
    (`unfinalized.rs:103-108`, `BACKEND_TOCK_ROUNDS_N = 15`), which this assembly fills with
    `uChal 1 … uChal 15` — sixteen laid into a fifteen-wide window, which is what manufactured the
    symptom. `KimchiStepMainPins19
    .the_statement_window_is_the_wrap_sides_fifteen_not_segment_ds_sixteen` carries the measurement
    and the citations. So this half is a marshaller edit: hand `step_pre` the assembly's own sixteen
    (conjunct (2) proves all sixteen are wire-shaped), with no statement change.
  * ⚑⚑ **`G` — and the reason this paragraph gave for it was FALSE until 2026-08-08.** It read
    *"§17 measured that this assembly has no IPA opening to take a real
    `challenge_polynomial_commitment` from"*. There is one: block 539508's own `opening.sg`, in
    `MinaStepPrevCommitments.SG_XY` beside the `GAMMA_XY` and `DELTA_XY` the emitted rows already
    consume, off a module `KimchiStepMainCore` imports. What blocks it is that `bpCloses` at that
    `sg` — with the block's own `z₁`, `z₂` — is **FALSE** on this assembly's `lhs`, because the
    assembly squeezes its own `t`, `u` and `b` rather than the block's (§19b(a), (b)).

**And the two escapes both terminate there.** (i) §19's rows are the `.opening` rung's and the rung
that is PROVED is `.finalize`, so `equal_g` constrains no emitted witness and `G := SG_XY` would cost
no proof — but the wire's `challenge_polynomial_commitments[0]` is the WRAP proof's kimchi
recursion-slot commitment, forced to `commit(b_poly(chals))` over the slot's own challenges, which
are tied to the step statement's published words by the 2026-08-06 repair slot 11 rests on. For that
point to BE `SG_XY`, the published challenges would have to be block 539508's fifteen. (ii) Keeping
`lhs` and pinning `G` re-opens §17(g)/(g)'s two-dimensional discrete log in `⟨G + b·u, H⟩` — item
#11, an assumption. **Both roads end at the transcript**, which is the honest name for the last of
the forty and is a different work item from the one this section used to name.

⚑ Stated at `shapeStep` — the shape whose 67 published entries `KimchiStepWrapChainFixture` carries
and whose word 54 the wrap ladder ties Mina's slot 12 to. `tS` is the smoke assembly and its word 54
is a different number. -/
theorem the_cone_of_word_fifty_four_holds_no_published_statement_entry :
    (let cone := tStep.specD.ws.map (·.2)
     -- (1) the CONE IS the whole preimage, and it is 56 + 2 + 2 + 16.
     cone.length == N_IDX_WORDS + N_HM_APP + 2 + shapeStep.bRounds
     && cone.length == 76
     -- (2) …whose squeeze IS word 54, and word 54 IS published entry 64.
     && hmOutDigestOf shapeStep tStep.sp tStep.gAccXY
          == (tStep.segD.states.getLastD []).getD 0 0
     && Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PUBLIC_IN.getD 64 0
          == hmOutDigestOf shapeStep tStep.sp tStep.gAccXY
     -- (3) the four families, each against its OWN source rather than against a copy.
     && (List.range N_IDX_WORDS).all (fun i =>
          cone.getD i 0 == Dregg2.Circuit.Emit.MinaWrapOwnVerifierKey.INDEX_WORDS.getD i 0)
     && (List.range N_HM_APP).all (fun i => cone.getD (N_IDX_WORDS + i) 0 == hmOVal i)
     && cone.getD (N_IDX_WORDS + N_HM_APP) 0 == tStep.gAccXY.1
     && cone.getD (N_IDX_WORDS + N_HM_APP + 1) 0 == tStep.gAccXY.2
     && (List.range shapeStep.bRounds).all (fun k =>
          cone.getD (N_IDX_WORDS + N_HM_APP + 2 + k) 0
            == liftOf shapeStep tStep.sp (shapeStep.uChal k))
     -- (4) ⚑⚑ NOT ONE of the sixty-seven published entries is in it — including 64 itself, so the
     -- squeeze is not its own input either.
     && (cone.filter (fun v =>
          Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PUBLIC_IN.contains v)).length == 0
     && Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PUBLIC_IN.length == 67
     -- (5) …nor is `STEP_PREVCOMM_XY`, the accumulator the MARSHALLER chose and the only step-side
     -- object words 55/56 are a function of.
     && Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PREVCOMM_XY.all
          (fun v => !cone.contains v)
     && Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PREVCOMM_XY.length == 2
     -- (6) ⚑ ANTI-VACUITY. A cone of zeros, or one nothing reads, would satisfy (4) and (5) and say
     -- nothing: every one of the seventy-six is nonzero, and bending EITHER coordinate of the one
     -- family that disagrees with Mina moves word 54.
     && (cone.filter (fun v => v != 0)).length == 76
     && (hmOutDigestOf shapeStep tStep.sp (fAdd tStep.gAccXY.1 1, tStep.gAccXY.2)
          != hmOutDigestOf shapeStep tStep.sp tStep.gAccXY)
     && (hmOutDigestOf shapeStep tStep.sp (tStep.gAccXY.1, fAdd tStep.gAccXY.2 1)
          != hmOutDigestOf shapeStep tStep.sp tStep.gAccXY)) = true := by
  native_decide

#assert_compiled the_cone_of_word_fifty_four_holds_no_published_statement_entry

/-- ⚑⚑⚑ **CELLS 58–75 ARE THE WIRE RECORD'S OWN TWO FAMILIES — the residue of slot 12, stated as
the fact that closes it rather than as the count that reported it.**

Slot 12's seventy-six cells split 58 / 18. The first fifty-eight — 56 index coordinates and 2
app-state words — agreed from 2026-08-08. The remaining eighteen were the whole residue, and they
were the two families where THIS assembly and the marshalled wire record filled one preimage with
two different vectors:

  * **58–59, `G`.** Segment D absorbed `solveG`'s SOLVE while the record carried
    `proof.prev_challenges[0].comm`, which kimchi forces to `commit(b_poly(chals))`.
  * **60–75, the sixteen.** Segment D absorbed `liftOf … (uChal k)` while `prove_step` CHOSE a
    `k·0x9E3779B97F4A7C15 | 1` ladder.

Both are closed by this theorem's subject, and **they had to close together**: word 54 is ONE digest
over all seventy-six, so either family alone moves the number without landing it.

⚑ **WHAT EACH CONJUNCT IS FOR.**

  1. Cells 58–59 are `MinaStepOwnAccumulator.ACC_XY` — the point `step_accumulator_install`
     computes as `commit(b_poly(chals))` over the Tock SRS at the WRAP proof's published recursion
     slot, and which `pickles_kimchi_marshal` compares against that proof's own
     `prev_challenges[WRAP_PAD_SLOTS].comm`. So the circuit and the wire carry one point.
     ⚠ It is a **Pallas** point over `pN`; the first install put the STEP proof's Vesta commitment
     here and the step prover refused, which is why `onCurveA` is a conjunct below and not a
     comment.
  2. Cells 60–75 are the lifts of the SIXTEEN RAW prechallenges this assembly squeezes, i.e. of
     `chalOf … (uChal k)` — which is exactly the vector `stepmain_step_own_prechallenges.json`
     hands the marshaller and `marshal::read_own_prechallenges` refuses to expand differently.
  3. ⚠ **ANTI-VACUITY, and it is the conjunct that makes this a fact rather than a rename.** The two
     `G`s are DIFFERENT points: `gAccXY ≠ gXY`. Had the split been cosmetic — one cell read under
     two names — this would be false and the theorem would say nothing about which point segment D
     took. Both are on the curve, so neither is a degenerate fill.
  4. …and every one of the sixteen raw prechallenges is under `2 ^ 128`, which is what lets the wire
     carry them as `[u64; 2]` unchanged rather than as a truncation of something wider.

⚠ **WHAT IT DOES NOT SAY.** It does not say `equal_g` holds at `gAccXY` — it does not, and §19 keeps
`gXY` for exactly that reason (`KimchiStepMainCore.vGaX`, item #11). It does not say any row of this
assembly relates `gAccXY` to its fifteen: none does, and upstream none does either — that binding is
**gate A2** (`gates::gate_a2`), a native check one rung out, green at both slots. ⚠ NOT
`accumulator_check`, which reads the WRAP record's Vesta commitment and is blind to this family. -/
theorem cells_fifty_eight_to_seventy_five_are_the_records_own_accumulator_and_the_assemblys_own_sixteen :
    (let cone := tStep.specD.ws.map (·.2)
     -- (1) 58–59: the record's accumulator, from the module the marshaller pins to the proof.
     cone.getD (N_IDX_WORDS + N_HM_APP) 0
       == Dregg2.Circuit.Emit.MinaStepOwnAccumulator.ACC_X
     && cone.getD (N_IDX_WORDS + N_HM_APP + 1) 0
          == Dregg2.Circuit.Emit.MinaStepOwnAccumulator.ACC_Y
     && tStep.gAccXY == Dregg2.Circuit.Emit.MinaStepOwnAccumulator.ACC_XY
     -- (2) 60–75: the lifts OF THE RAW SIXTEEN this assembly squeezes — the vector the wire carries.
     && (List.range shapeStep.bRounds).all (fun k =>
          cone.getD (N_IDX_WORDS + N_HM_APP + 2 + k) 0
            == liftVal shapeStep (chalOf shapeStep tStep.sp (shapeStep.uChal k)))
     && shapeStep.bRounds == 16
     -- (3) ⚑ ANTI-VACUITY: the two `G`s are two POINTS, not one cell under two names — and both are
     -- on the curve, so the split did not fill segment D with a degenerate pair.
     && tStep.gAccXY != tStep.gXY
     && onCurveA tStep.gAccXY && onCurveA tStep.gXY
     -- (4) …and the sixteen raw prechallenges fit the two u64 limbs the wire spells them in.
     && (List.range shapeStep.bRounds).all (fun k =>
          chalOf shapeStep tStep.sp (shapeStep.uChal k) < 2 ^ 128)) = true := by
  native_decide

#assert_compiled cells_fifty_eight_to_seventy_five_are_the_records_own_accumulator_and_the_assemblys_own_sixteen

end Dregg2.Circuit.Emit.KimchiStepMain
