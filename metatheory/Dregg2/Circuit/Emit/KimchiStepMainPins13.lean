/-
`KimchiStepMain` pins — §18.

The values these are stated about are in `…Fixture`; the emission is in `…Core`.
-/
import Dregg2.Circuit.Emit.KimchiStepMainFixture

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

Segment D at step `N` (`step_main.ml:525-566`) absorbs `(app_state_N, G_N, bulletproof_challenges_N)`
onto a `Sponge.copy` of `sponge_after_index`; its squeeze is step `N`'s public
`messages_for_next_step_proof` (`:572-573`). Segment C at step `N+1` (`:59-81`) absorbs
`(app_state_N, sg_old, prev_challenges)` onto the SAME copy point, masked. `per_proof_witness.ml:
90-97` says what those two witness fields are: `prev_challenges` are "the challenges c_0 … c_{k-1}
corresponding to each W_i" and `prev_challenge_polynomial_commitments` "the commitments to the
challenge polynomials … corresponding to each of the prev_challenges" — i.e. step `N`'s own
`G` and `bulletproof_challenges`. **So on the honest chain the two digests are EQUAL**, and that
equality is the tie. It is pinned below and it is not a definition: the two segments have different
word lists, different lengths, different masks and different app-state fixtures, and they coincide
only if the mask, the interleave (`composition_types.ml:595-607`), the copy point and the block
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

-- ⚑ **THE PARAMETERISATION IS FAITHFUL**: at this instance's own values `hmChainSpec` IS `hmSpec`,
-- word for word — same variables, same order, same length. So every measurement below is about the
-- emitted segment C and not about a second model of it.
#guard (hmChainSpec shapeSmoke hmVal (chainSlot0 shapeSmoke tS.ipa).1 (chainSlot0 shapeSmoke tS.ipa).2
          (sgOldVal tS.ipa 1 0, sgOldVal tS.ipa 1 1)
          (fun k => prevChalVal (shapeSmoke.bRounds + k))).ws == (hmSpec shapeSmoke tS.ipa).ws
#guard hmChainDigest shapeSmoke hmVal (chainSlot0 shapeSmoke tS.ipa).1 (chainSlot0 shapeSmoke tS.ipa).2
          (sgOldVal tS.ipa 1 0, sgOldVal tS.ipa 1 1)
          (fun k => prevChalVal (shapeSmoke.bRounds + k))
        == (tS.segC.states.getLastD []).getD 0 0

#guard wordSeven tS G_XY == (stepPublic tS).getD 7 0

-- ⚑⚑ **(a) THE HONEST CHAIN CLOSES.** Step `N+1`'s segment C, fed step `N`'s app state, `G` and
-- returned bulletproof challenges, reconstructs step `N`'s public word 7 EXACTLY. This is the
-- reconstruction-and-comparison, and it is the first time the two hashes are shown to be the two
-- ends of one chain rather than two sponges that happen to share a copy point.
#guard hmChainDigest shapeSmoke hmOVal (chainSlot0 shapeSmoke tS.ipa).1
          (chainSlot0 shapeSmoke tS.ipa).2 G_XY (chainChals shapeSmoke tS.sp)
        == wordSeven tS G_XY
-- …and it is not trivially true: segment C's own app-state fixture gives a DIFFERENT digest, so the
-- identity is carrying the chained app state and not ignoring it.
#guard hmChainDigest shapeSmoke hmVal (chainSlot0 shapeSmoke tS.ipa).1
          (chainSlot0 shapeSmoke tS.ipa).2 G_XY (chainChals shapeSmoke tS.sp)
        != wordSeven tS G_XY

-- ⚑⚑ **(b) THE DELIVERABLE. THE SUBSTITUTED CHAIN CLOSES TOO — THE TIE DOES NOT REFUSE IT.**
-- Step `N` is `tSwapAbs` with `G` re-solved (§17(c)/(e)); its public word 7 has MOVED (§17(d)).
-- Step `N+1` carries `sg_old := G_resolved` and step `N`'s challenges, and the reconstruction
-- reproduces the moved word. Nothing anywhere in the chain objects.
#guard hmChainDigest shapeSmoke hmOVal (chainSlot0 shapeSmoke tSwapAbs.ipa).1
          (chainSlot0 shapeSmoke tSwapAbs.ipa).2 bpGResolvedA (chainChals shapeSmoke tSwapAbs.sp)
        == wordSeven tSwapAbs bpGResolvedA
-- …and this really is the §17(e) witness and not a re-run of the honest one: the two chains'
-- digests differ, and `equal_g` still closes on the substituted one.
#guard wordSeven tSwapAbs bpGResolvedA != wordSeven tS G_XY
#guard bpCloses (bpUOf tSwapAbs) GENERATORS_H (bpLhsOf tSwapAbs) bpGResolved
                (bpBOf tSwapAbs) BP_Z1 BP_Z2

-- ⚑ **(c) AND A WHOLE FAMILY OF CHAINS CLOSES, because `z₁`/`z₂` occur in NEITHER segment.**
-- Re-solving at `z₁ = z₂ = 1` reaches a third commitment; its chain closes just as well. So the tie
-- constrains WHICH `G` is carried forward, not WHETHER a satisfying `G` exists.
#guard onCurveA bpG11 && bpG11 != bpGResolvedA && bpG11 != bpGHonestA
#guard hmChainDigest shapeSmoke hmOVal (chainSlot0 shapeSmoke tSwapAbs.ipa).1
          (chainSlot0 shapeSmoke tSwapAbs.ipa).2 bpG11 (chainChals shapeSmoke tSwapAbs.sp)
        == wordSeven tSwapAbs bpG11
-- …and the reason is structural: `G` is a word of segment D and of NEITHER other place, while `z₁`
-- and `z₂` are not variables of this assembly at all. So the chain can move with `G` and cannot move
-- with the response scalars.
#guard (tS.specD.ws.map (·.1)).countP (fun v => v == vGx shapeSmoke) == 1
#guard (tS.specC.ws.map (·.1)).countP (fun v => v == vGx shapeSmoke) == 0

-- ⚑⚑ **(d) THE DIRECTION THE TIE DOES REFUSE — and it is the reason the tie is not nothing.**
-- A prover who moves step `N`'s word 7 and then carries the HONEST `G` forward at step `N+1` is
-- REFUSED: the reconstruction no longer equals the word the wrap proof was made for. So the fake
-- commitment cannot be laundered away between steps; it must be carried.
#guard hmChainDigest shapeSmoke hmOVal (chainSlot0 shapeSmoke tSwapAbs.ipa).1
          (chainSlot0 shapeSmoke tSwapAbs.ipa).2 G_XY (chainChals shapeSmoke tSwapAbs.sp)
        != wordSeven tSwapAbs bpGResolvedA
-- …and each of the other three chained quantities is covered in the same direction:
--   the carried challenges,
#guard hmChainDigest shapeSmoke hmOVal (chainSlot0 shapeSmoke tSwapAbs.ipa).1
          (chainSlot0 shapeSmoke tSwapAbs.ipa).2 bpGResolvedA
          (fun k => if k == 0 then fAdd (chainChals shapeSmoke tSwapAbs.sp 0) 1
                    else chainChals shapeSmoke tSwapAbs.sp k)
        != wordSeven tSwapAbs bpGResolvedA
--   the app state,
#guard hmChainDigest shapeSmoke (fun i => fAdd (hmOVal i) 1)
          (chainSlot0 shapeSmoke tSwapAbs.ipa).1 (chainSlot0 shapeSmoke tSwapAbs.ipa).2
          bpGResolvedA (chainChals shapeSmoke tSwapAbs.sp)
        != wordSeven tSwapAbs bpGResolvedA
--   and either coordinate of the carried commitment alone.
#guard hmChainDigest shapeSmoke hmOVal (chainSlot0 shapeSmoke tSwapAbs.ipa).1
          (chainSlot0 shapeSmoke tSwapAbs.ipa).2 (fAdd bpGResolvedA.1 1, bpGResolvedA.2)
          (chainChals shapeSmoke tSwapAbs.sp)
        != wordSeven tSwapAbs bpGResolvedA
#guard hmChainDigest shapeSmoke hmOVal (chainSlot0 shapeSmoke tSwapAbs.ipa).1
          (chainSlot0 shapeSmoke tSwapAbs.ipa).2 (bpGResolvedA.1, fAdd bpGResolvedA.2 1)
          (chainChals shapeSmoke tSwapAbs.sp)
        != wordSeven tSwapAbs bpGResolvedA

-- ⚑ **(e) THE OTHER DIRECTION: what the comparison does NOT cover, and the MASKED SLOT.**
-- With `Prefix_mask.there N1 = [0,1]` (`pickles_base/proofs_verified.ml:75-81`, §8h) slot 0 is the
-- `Wrap_hack` dummy: bending its commitment or ANY of its challenges leaves the reconstruction
-- exactly where it was. It bites only if both mask bits are on — which is the `N2` instance, not
-- this one.
#guard MASK_BITS == [0, 1]
#guard hmChainDigest shapeSmoke hmOVal (fAdd (chainSlot0 shapeSmoke tSwapAbs.ipa).1.1 1,
            (chainSlot0 shapeSmoke tSwapAbs.ipa).1.2)
          (chainSlot0 shapeSmoke tSwapAbs.ipa).2 bpGResolvedA (chainChals shapeSmoke tSwapAbs.sp)
        == wordSeven tSwapAbs bpGResolvedA
#guard hmChainDigest shapeSmoke hmOVal (chainSlot0 shapeSmoke tSwapAbs.ipa).1
          (fun k => fAdd (prevChalVal k) 1) bpGResolvedA (chainChals shapeSmoke tSwapAbs.sp)
        == wordSeven tSwapAbs bpGResolvedA
-- …and with BOTH bits on it does bite, so the control is about the mask and not about the slot.
#guard hmChainDigestMask shapeSmoke [1, 1] hmOVal
          (fAdd (chainSlot0 shapeSmoke tSwapAbs.ipa).1.1 1,
           (chainSlot0 shapeSmoke tSwapAbs.ipa).1.2)
          (chainSlot0 shapeSmoke tSwapAbs.ipa).2 bpGResolvedA (chainChals shapeSmoke tSwapAbs.sp)
        != hmChainDigestMask shapeSmoke [1, 1] hmOVal (chainSlot0 shapeSmoke tSwapAbs.ipa).1
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

end Dregg2.Circuit.Emit.KimchiStepMain
