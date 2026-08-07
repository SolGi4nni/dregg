/-
# KimchiWrapFinalizeSpongeGate — ⚑ the REALITY GATE for `KimchiWrapMain` §20.

`finalize_other_proof`'s sponge half, checked against a REAL accepted Mina block rather than against
a second spelling of `wrap_verifier.ml`. It is a separate module so that a rung's pins re-elaborate
without the emitter's 5,000 lines of `def` behind them — the same reason `KimchiStepMainPins01–13`
exist.

## ⚠ WHY THIS MODULE SHIPPED RED, AND WHAT IT COSTS TO SPLIT ONE OFF

⚑ **A `set_option` DOES NOT CROSS AN IMPORT.** `KimchiWrapMain` sets `maxRecDepth 100000` and
`maxHeartbeats 4000000` (`:389,:392`) because its pins reduce whole sponge trajectories in the
kernel. This file was split out carrying `maxRecDepth 8000` and the DEFAULT 200,000 heartbeats, so
four of its five proofs did not elaborate:

    :55  maximum recursion depth has been reached          (finalize_sponge_reproduces_…)
    :78  maximum recursion depth has been reached
    :122 (deterministic) timeout at `whnf`, 200000 heartbeats   (cip_fold_reproduces_…)
    :140 (deterministic) timeout at `whnf`, 200000 heartbeats   (cip_fold_direction_…)

⚑ **AND LEAN ADDED ALL FOUR TO THE ENVIRONMENT ANYWAY, PROVED BY `sorryAx`.** That is the whole
danger: a resource failure is an *error*, but the declaration still lands, still has the right
STATEMENT, and anything downstream that cites it type-checks. Nothing in this file contains the
token `sorry`. The only thing that turned it into a build failure was
`#assert_namespace_axioms` at the foot — which reported the LAST of the four and said `[sorryAx]`.

⚠ So do not read that hygiene failure as being about dependencies. It was about this preamble, and
the lesson generalises: **a module split off from a module with a `set_option` preamble must carry
that preamble, and must keep a namespace-wide axiom pin, or a proof that stops working comes back
as a green build with a sorry in it.**

⚑ **THE PINS ARE NOT ACTUALLY EXPENSIVE.** With the parent's budgets restored the whole file
elaborates in seconds, in the kernel, with no `native_decide`: `finChalSpongeOf`'s 16 permutations
and `finFrSpongeOf`'s 46 close by `rfl` at 13 s in an isolated probe. The `exit 137` that motivated
the split was the elaborator inside a 7,092-line module, not these reductions.

NEW standalone file. Import line for the root (do NOT edit `Dregg2.lean` from a lane):
`import Dregg2.Circuit.Emit.KimchiWrapFinalizeSpongeGate`
-/
import Dregg2.Circuit.Emit.KimchiWrapMain

namespace Dregg2.Circuit.Emit.KimchiWrapFinalizeSpongeGate

open Dregg2.Circuit.Emit.KimchiWrapMain

-- ⚑ VERBATIM `KimchiWrapMain.lean:389-392`. See the docblock: these do not cross the import, and
-- without them four proofs below become `sorryAx` while still landing in the environment.
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ### §12a′ — ⚑ **THE SECOND REALITY GATE: this file's FINALIZE sponge is upstream's too.**

§12a runs the emitter's state machine on a real accepted proof's PHASE-1 tape. §20 runs the SAME
machine on the PHASE-2 one — `finalize_other_proof`'s — and `MinaRealBlockTranscript` already holds
that tape for Mina devnet block 539508 (`openmina BlockVerifier + accumulator_check + kimchi verify
= Ok`): `CHALS_FLAT` is the 2 × 15 carried IPA challenges the NESTED sponge absorbs, `fqTape2` the
**91** elements the finalize sponge absorbs, and `V_CHAL`/`U_CHAL` the ξ′ and r′ that proof was
actually built with.

⚑ **TWO IMPLEMENTATIONS, ONE PAIR OF NUMBERS.** There the sponge is `PastaPoseidonFq`'s
`absorbMany`/`challenge`, a state fold with no circuit in it; here it is `runSpongeQ`, the trajectory
that EMITS `Poseidon` rows and allocates a variable per absorbed word. If §20's schedule put a
permutation anywhere else — and the two squeezes sharing ONE permutation is exactly where a block
model goes wrong — these would not agree. -/

/-- The nested challenge-digest sponge, driven on the real block's own carried challenges. -/
def blockFinChalSp : SpAcc :=
  finChalSpongeOf 0 Dregg2.Circuit.Emit.MinaRealBlockTranscript.CHALS_FLAT
/-- …and the finalize sponge, on its own 91-element tape. -/
def blockFinSp : SpAcc := finFrSpongeOf 0 Dregg2.Circuit.Emit.MinaRealBlockTranscript.fqTape2
/-- ξ′ and r′ as THIS file's emitter squeezes them. -/
def blockFinChals : List Nat := (chalSqueezes blockFinSp).map (fun e => e.2 % 2 ^ 128)
/-- the two squeeze EVENTS, for the permutation-placement pin. -/
def blockFinSqEvs : List SpEvt := blockFinSp.evs.filter (fun e => !e.isAbs)

/-- ⚑ **THE PREV-CHALLENGE DIGEST AND BOTH SQUEEZES OF A REAL ACCEPTED BLOCK, OUT OF §20's OWN
EMITTER.** Closed in the KERNEL. -/
theorem finalize_sponge_reproduces_the_accepted_block :
    whDigestVal blockFinChalSp = Dregg2.Circuit.Emit.MinaRealBlockTranscript.PREV_CHAL_DIGEST
    ∧ blockFinChals = [ Dregg2.Circuit.Emit.MinaRealBlockTranscript.V_CHAL
                      , Dregg2.Circuit.Emit.MinaRealBlockTranscript.U_CHAL ]
    ∧ Dregg2.Circuit.Emit.MinaRealBlockTranscript.fqTape2.length = 91
    ∧ Dregg2.Circuit.Emit.MinaRealBlockTranscript.CHALS_FLAT.length = WH_MLMB * WH_ROUNDS := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- ⚑ **AND ξ′ AND r′ COME OUT OF ONE PERMUTATION, AT LANES 0 AND 1.** `wrap_verifier.ml:892-894`
squeezes twice in a row; the rate-2 machine permutes for the first and reads lane 1 for the second.
A one-permutation-per-squeeze model would put them two permutations apart and every value below
would be a different number wearing the right name — which is the defect `SegSpec.blocks` carries on
the step side and the reason this is a pin and not a comment. -/
theorem finalize_sponge_squeezes_share_one_permutation :
    blockFinSqEvs.length = 2
    ∧ (blockFinSqEvs.getD 0 default).didPerm = true
    ∧ (blockFinSqEvs.getD 1 default).didPerm = false
    ∧ (blockFinSqEvs.getD 0 default).lane = 0
    ∧ (blockFinSqEvs.getD 1 default).lane = 1
    ∧ (blockFinSqEvs.getD 0 default).midV = (blockFinSqEvs.getD 1 default).midV := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ RED CONTROL. Bending the LAST absorbed evaluation moves both squeezes — so the pins above
measure a derivation over all 91 elements and not the first few. -/
def blockFinBent : List Nat :=
  (chalSqueezes (finFrSpongeOf 0
      (Dregg2.Circuit.Emit.MinaRealBlockTranscript.fqTape2.set 90 0))).map
    (fun e => e.2 % 2 ^ 128)

-- ⚠ `≠` + `decide`, NOT `(… == …) = false := rfl`. The `rfl` spelling makes the elaborator prove
-- `(blockFinBent == blockFinChals) =?= false` by `isDefEq`, which blows `maxRecDepth` even at
-- 100000 — while `decide` on the same two sponges closes in ~30 s. And `≠` is the stronger
-- statement: it is about the VALUES, not about the `BEq` instance that compares them.
theorem finalize_sponge_bends_on_one_absorbed_evaluation :
    blockFinBent ≠ blockFinChals := by decide

/-! ### §12a″ — ⚑ **AND THE `combined_inner_product` FOLD IS THE SAME BLOCK'S.**

`fnHorner` is the combinator `combined_inner_product_correct` is built out of, and
`Pcs_batch.combine_split_evaluations`'s DIRECTION is the one thing about it prose gets wrong
silently. `MinaRealBlockGate`'s `EVZ`/`EVZW` are that block's 47 C8 entries in
`wrap_verifier.ml:951-1009`'s own order — the two recursion challenge polynomials, the public
evaluation, `ft`, then the 43 columns — and `real_cip` already grounds the fold's VALUE there. This
grounds §20's compiled PROGRAM against the same number: the emitted rows, not a second spelling. -/

/-- §20's fold, over a supplied ξ, r and the two 47-entry evaluation lists. -/
def cipFoldProg (xi r : Nat) (ez ew : List Nat) : FM Nat := do
  let x ← fnLit xi
  let rr ← fnLit r
  let a ← ez.foldlM (fun acc v => do let t ← fnLit v; pure (acc ++ [t])) []
  let b ← ew.foldlM (fun acc v => do let t ← fnLit v; pure (acc ++ [t])) []
  let hz ← fnHorner x a
  let hw ← fnHorner x b
  let rh ← fnMul rr hw
  fnAdd hz rh

/-- …evaluated. Every op is a `.lit`, so the lookup is never called. -/
def cipFoldVal (xi r : Nat) (ez ew : List Nat) : Nat :=
  let res := (cipFoldProg xi r ez ew).run #[]
  (fnEval (fun _ => 0) res.2).getD res.1 0

/-- ξ and r as §5's `to_field_checked` chain lifts the block's own prechallenges. -/
def blockXiField : Nat := liftValQ shapeWrap Dregg2.Circuit.Emit.MinaRealBlockTranscript.V_CHAL
def blockRField : Nat := liftValQ shapeWrap Dregg2.Circuit.Emit.MinaRealBlockTranscript.U_CHAL

/-- ⚑ **THE LIFT AND THE ENTRY COUNT, AGAINST BLOCK 539508 — IN THE KERNEL.** This is the pin that
§5's `EndoMulScalar` chain IS `ScalarChallenge::to_field` at `ENDO_Q`: a second implementation
(`KimchiVerify.endoMap`, through `MinaRealBlockGate`'s own constants) of the map this file emits
eight `EndoMulScalar` rows for, agreeing on that block's own ξ′ and r′.

⚑ It is split out of `cip_fold_reproduces_the_accepted_block` on purpose. That theorem must be
compiler-trusted (see below) and `#assert_compiled` would then have covered these three conjuncts
too — labelling three kernel-clean facts as compiler-trusted and losing their real pin. Splitting
keeps the confession down to exactly the conjunct that earns it. -/
theorem cip_lift_reproduces_the_accepted_block :
    blockXiField = Dregg2.Circuit.Emit.MinaRealBlockGate.VV.val
    ∧ blockRField = Dregg2.Circuit.Emit.MinaRealBlockGate.UU.val
    ∧ Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZ_N.length = FIN_NCOLS + 4
    ∧ Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZW_N.length = FIN_NCOLS + 4 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ⚠ **THE TWO BELOW ARE COMPILER-TRUSTED, AND HERE IS THE MEASUREMENT.**

`cipFoldVal` is not a sponge — it BUILDS a straight-line program in `FM = StateM (Array FOp)` and
then interprets it. 47 + 47 `fnLit`s, two `fnHorner`s, a `fnMul` and a `fnAdd` is ~200 ops, and in
`whnf` an `Array` is its `List` model: ~200 `Array.push`es is a quadratic list append, and `fnEval`
then does a lookup per op over that same list, all carrying 254-bit literals with no sharing.
Measured 2026-08-05 on this box: **`(cipFoldProg …).run #[] |>.2.size` alone does not close at
1,000,000 heartbeats**, and the five `rfl`s together took the elaborator to **21.9 GB** before being
killed. This is the same wall §24's `bullData` hit, and it is a property of the `Array`-in-`whnf`
model, not of the module boundary — splitting the file does not make a `whnf` cheaper.

⚑ **THE SPONGES ARE NOT IN THIS CLASS AND ARE NOT PINNED HERE.** `finChalSpongeOf`'s 16 Fq
permutations and `finFrSpongeOf`'s 46 close by `rfl` IN THE KERNEL in ~13 s (probed separately), so
they stay `#assert_namespace_axioms`-clean above. Only the fold is confessed. -/

/-- ⚑ **THE `combined_inner_product` FOLD OF BLOCK 539508, BY COMPILED EVALUATION.** `#assert_compiled`
below records the compiler-trust rather than hiding it — which a `#guard` of the same expression
would not, being the same evaluation with the name, the term and the axiom record deleted. -/
theorem cip_fold_reproduces_the_accepted_block :
    cipFoldVal blockXiField blockRField
        Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZ_N
        Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZW_N
      = Dregg2.Circuit.Emit.MinaRealBlockGate.CIP.val := by
  native_decide

/-- ⚑ RED CONTROL — the fold is over EVERY entry and in ONE direction. Reversing the ζ list, or
bending one column, moves the result. A Horner whose direction is wrong reproduces nothing, which is
what makes the theorem above a measurement of `fnHorner` and not of the constants. -/
theorem cip_fold_direction_and_every_entry_are_load_bearing :
    (cipFoldVal blockXiField blockRField
        Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZ_N.reverse
        Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZW_N
      == Dregg2.Circuit.Emit.MinaRealBlockGate.CIP.val) = false
    ∧ (cipFoldVal blockXiField blockRField
        (Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZ_N.set 46 0)
        Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZW_N
      == Dregg2.Circuit.Emit.MinaRealBlockGate.CIP.val) = false
    ∧ (cipFoldVal blockXiField blockRField
        Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZ_N
        (Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZW_N.set 0 0)
      == Dregg2.Circuit.Emit.MinaRealBlockGate.CIP.val) = false := by
  native_decide

-- ⚑ Both halves of `#assert_compiled` are load-bearing here: a `sorry` still ERRORS, and a
-- kernel-clean fact ALSO errors — so if `whnf` over `Array` ever gets cheap enough for these to
-- close by `rfl`, these two lines go RED and force the pin back up to `#assert_axioms`.
#assert_compiled cip_fold_reproduces_the_accepted_block
#assert_compiled cip_fold_direction_and_every_entry_are_load_bearing

/-! ### §12a‴ — ⚑⚑⚑ **THE THIRD REALITY GATE, AND IT IS ABOUT THE EMISSION RATHER THAN THE MACHINE.**

⚠ **THE DISTINCTION §12a′ COULD NOT MAKE, SAID PLAINLY.** `finalize_sponge_reproduces_the_accepted
_block` drives `runSpongeQ` on `MinaRealBlockTranscript`'s own phase-2 tape and gets that block's ξ′
and r′ back. That is a fact about the STATE MACHINE, and it stayed true while the EMITTER absorbed
something else entirely — `finSpTape` is the tape §20's rows actually build, out of the assembly's
own cells, and the two were never compared. A sponge pinned against a tape nobody feeds it is the
`whOldChals` hazard one level up: every instrument agreeing with itself.

✅ ⚑⚑⚑ **SO THIS SECTION COMPARES THEM, SLOT BY SLOT, AND THE ANSWER IS NINETY-ONE OF NINETY-ONE.**
Slot 1 closed earlier on 2026-08-07 — `whOldChals` is `MinaRealBlockTranscript.CHALS_FLAT`, so §20's
nested challenge-digest sponge squeezes the value kimchi's own verifier computed at
`verifier.rs:290-299` rather than a mixer's. Slot **6** closed later the same day, and NOT on this
side: `KimchiStepMainCore` §1f stopped publishing the live per-proof block's `perm` out of
`ftcDiv2 0` — §6b's own Fp ft-comm scalar, the WRAP statement's word 4 — and gave it its own cell
carrying `Shifted_value.Type2.of_field` of the derived `perm`. `finZW0`'s ratio is 1 now, so the
solve is the identity and the tape it presents the sponge is the block's own. -/

/-- The 91-element tape §20's rows build at the live block, with the challenge digest the emitter's
own nested sponge squeezes. -/
def emittedFinTape : List Nat :=
  finSpTape FIN_LIVE_BLOCK (whDigestVal (finChalSponge 0 FIN_LIVE_BLOCK))

/-! ⚑⚑ **`unbentFinTape` IS DELETED WITH `finZW0` (2026-08-07), AND KEEPING IT WOULD HAVE BEEN THE
GREEN-PIN SIN.**

It read: *the same tape with `finZW0`'s solve removed — every entry read straight off Mina devnet
block 539508's own Wrap-proof evaluations.* Its whole job was to be the object `emittedFinTape` had
to become, and `emittedFinTape = unbentFinTape` was the theorem that said the bend was inert. With
`finZW0` gone, `finEvalTape` IS that list by definition, so the conjunct is `rfl` — a tautology
wearing the name of a measurement. It is removed rather than left standing green.

⚑ What survives is the leg that was always the content and can still go red:
`emittedFinTape = MinaRealBlockTranscript.fqTape2`, ninety-one entries against the accepted block's
own. -/

/-- ⚑⚑ **§20's NESTED CHALLENGE-DIGEST SPONGE, AS THE EMITTER DRIVES IT, IS THE ACCEPTED BLOCK'S.**

`finChalSponge` is what tape slot 1 absorbs, and `whOldChals` is what it absorbs OVER. Until
2026-08-07 that was `wrapFixtureQ 41` — a mixer, which is the honest shape for an upstream `exists`
with no `typ`, and which is also a value nothing outside this tree can disagree with. It is the
carried IPA challenges of the proof the live block DECLARES ITSELF TO BE
(`KimchiWrapMain.the_live_block_declares_itself_minas_own_wrap_proof`), so the squeeze is now
checkable against a number kimchi computed.

⚑ **THE THIRD CONJUNCT IS THE ANTI-VACUITY AND IT IS THE ONE THAT COULD GO RED.** The mixer this
replaced does NOT reproduce the digest, so the first two are a measurement of the INPUT and not of a
sponge that answers `PREV_CHAL_DIGEST` to anything. Closed in the KERNEL. -/
theorem the_emitted_challenge_digest_is_the_accepted_blocks :
    whOldChals FIN_LIVE_BLOCK = Dregg2.Circuit.Emit.MinaRealBlockTranscript.CHALS_FLAT
    ∧ whDigestVal (finChalSponge 0 FIN_LIVE_BLOCK)
        = Dregg2.Circuit.Emit.MinaRealBlockTranscript.PREV_CHAL_DIGEST
    ∧ whDigestVal (finChalSpongeOf 0
        ((List.range (WH_MLMB * WH_ROUNDS)).map (fun k => wrapFixtureQ 41 k)))
      ≠ Dregg2.Circuit.Emit.MinaRealBlockTranscript.PREV_CHAL_DIGEST := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- ⚑⚑⚑ **AND THE TAPE ITSELF, LESS ONE BEND, IS MINA'S OWN PHASE-2 TAPE — SO §20's TWO SQUEEZES
ARE THAT BLOCK'S ξ′ AND r′.**

This is the gate §20 has not had. `unbentFinTape` is built ENTIRELY from the emitter's own value
layer — `finBlockVal` (the published step statement), `finChalSponge` (this file's own sponge),
`finFtEval1Val`, `finPZetaVal`, `finPZetaWVal` and the 43 `finColVal` columns — and it comes out
EQUAL, element for element, to `MinaRealBlockTranscript.fqTape2`, which was extracted from the
block's bytes on a path that has never seen this assembly. Two constructions, ninety-one numbers.

✅ ⚑⚑ **AND SINCE `finZW0`'s DELETION IT IS ABOUT THE EMITTED TAPE, IN THE KERNEL.** This theorem
used to be stated over `unbentFinTape` — a by-hand list standing beside the emitter — precisely
because `emittedFinTape` ran the solve and could not be reduced by `rfl`. It was the KERNEL half of
a pair whose COMPILED half (`the_emitted_finalize_tape_is_minas`) said the same thing about the
emitter's own value layer. With the solve gone the two objects are one, so the hand-built list is
deleted and this is restated over `emittedFinTape`: **the same claim, one object, and `rfl` instead
of `native_decide` for the equality leg.** (Was
`the_unbent_finalize_tape_is_minas_and_squeezes_to_its_challenges`; renamed because "unbent" named a
distinction that no longer exists.)

⚠ Slot 1 still costs a nested sponge, so the SLOT-BY-SLOT form and the two squeezes stay in the
compiled theorem below; what moves into the kernel here is the ninety-one-element equality itself,
which is the leg a reader is entitled to want unconditioned on the compiler. -/
theorem the_emitted_finalize_tape_is_minas_in_the_kernel :
    emittedFinTape = Dregg2.Circuit.Emit.MinaRealBlockTranscript.fqTape2
    ∧ (chalSqueezes (finFrSpongeOf 0 emittedFinTape)).map (fun e => e.2 % 2 ^ 128)
        = [ Dregg2.Circuit.Emit.MinaRealBlockTranscript.V_CHAL
          , Dregg2.Circuit.Emit.MinaRealBlockTranscript.U_CHAL ] := by
  refine ⟨rfl, rfl⟩

/-- ✅ ⚑⚑⚑ **THE EMITTED TAPE, AGAINST MINA'S, SLOT BY SLOT: NO DISAGREEMENT AT ALL.**

⚠ **`= []` RATHER THAN `.length = 0`, for the same reason it was `= [6]` and not `.length = 1`.** A
count says a number; the list says WHICH, so a future edit that breaks slot 40 reds here with the
slot named instead of with an integer that moved.

⚠ ⚑ **THREE CONJUNCTS WERE DELETED FROM THIS STATEMENT ON 2026-08-07, AND THE DELETION IS THE
POINT.** They were `emittedFinTape = unbentFinTape`, `emittedFinTape.getD 6 0 = finZW0 …` and
`finZW0 … = finColVal …` — each of them a fact about the SOLVE, i.e. about a definition that no
longer exists. With `finZW0` deleted (`KimchiWrapMainCore` §19), `finEvalTape` reads the block's own
column unconditionally, so all three reduce to `rfl` and would have stood here as green lines
asserting nothing. **A conjunct that survives the removal of its subject is measuring the
tautology.**

⚑ **WHAT IS LEFT IS WHAT WAS ALWAYS THE CONTENT**: the tape §20's ROWS build — the emitter's own
value layer, not a list assembled by hand next to it — is the accepted block's, entry for entry, and
§20's two squeezes over it are that block's ξ′ and r′. Slot 6 was the disagreement until
`KimchiStepMainCore` §1f gave the live per-proof block's `perm` its own cell carrying
`Shifted_value.Type2.of_field` of the derived value; the solve became inert then, and is gone now.

⚑ Compiler-trusted, because slot 1's challenge digest runs a nested sponge and `whnf` models an
`Array` as its `List` model (`KimchiWrapMainPins12` §20b measured the same wall). -/
theorem the_emitted_finalize_tape_is_minas :
    ((List.range 91).filter (fun i =>
        emittedFinTape.getD i 0
          != Dregg2.Circuit.Emit.MinaRealBlockTranscript.fqTape2.getD i 0)) = []
    ∧ emittedFinTape = Dregg2.Circuit.Emit.MinaRealBlockTranscript.fqTape2
    -- ⚑ …and slot 6 — the one the deleted solve used to bend — is the block's own `z(ζω)`, named
    -- here against MINA'S entry rather than against this file's own `finColVal`, which is the only
    -- form of the claim that survives `finZW0`'s deletion with content in it.
    ∧ emittedFinTape.getD 6 0
        = Dregg2.Circuit.Emit.MinaRealBlockTranscript.fqTape2.getD 6 0
    -- ⚑ …and §20's two squeezes over the EMITTED tape are that block's ξ′ and r′.
    ∧ (chalSqueezes (finFrSpongeOf 0 emittedFinTape)).map (fun e => e.2 % 2 ^ 128)
        = [ Dregg2.Circuit.Emit.MinaRealBlockTranscript.V_CHAL
          , Dregg2.Circuit.Emit.MinaRealBlockTranscript.U_CHAL ] := by
  native_decide

/-- ✅ ⚑⚑⚑ **THE LIVE BLOCK PUBLISHES THE DERIVED `perm`, SO NO SOLVE IS NEEDED — AND THE SOLVE IS
DELETED, NOT MERELY INERT.** (Was `the_bend_is_gone_because_the_live_block_publishes_the_derived_perm`;
**renamed 2026-08-07 because the name became false**: nothing here is "gone because" any more, the
`finZW0` it named no longer exists.)

`finZW0` scaled `z(ζω)` by `permUsed / perm` so that §19's `Field.equal` leg would hold on the block
that claims `should_finalize`. `perm` is the derivation over Mina's own evaluations — the one
`finalize_reproduces_minas_own_ft_eval0` grounds against `FT0`, `LCT` and `PVP`. `permUsed` is
packed word `27·FIN_LIVE_BLOCK + 4` = **31**, read through `Shifted_value.Type2`. They AGREE, which
is why the scaling was removable; the theorem below is that agreement, stated over `finProbeData`'s
own slots and NOT over the deleted function.

⚠ ⚑ **WHY DELETION AND NOT AN INERT KEEP.** An identity solve is a compensator with no input yet: a
future word 31 that is NOT the derived `perm` would be silently ABSORBED by the ratio instead of
refusing at `w10_finalize`, and this theorem would go on being green about `finZW0 = finColVal`
while the emission drifted. The three conjuncts of this shape that named `finZW0` are removed with
it; what is left names `perm`, `permUsed` and the published word, which is where a drift would
actually show.

⚠ ⚑ **WHAT THE PREVIOUS VERSION OF THIS THEOREM GOT RIGHT, AND WHAT IT GOT WRONG.** It said, and
this was correct: *"word 31 must be `Shifted_value.Type2.of_field` of `perm` — `qSub perm
FIN_SHIFT2`."* It also said *"it is not free on the step side: `stepStmtVar` maps the live block's
`perm` hi/parity to `ftcDiv2 0`/`ftcOdd 0`, the split of §6b's OWN ft-comm `perm` scalar, which the
step assembly derives natively in Fp"* — true as a reading of the map, and the WRONG conclusion
drawn from it. Those cells are the **WRAP statement's** word 4; the step statement's word 31 was
merely aliased onto them and was never derived at all. Un-aliasing it (`KimchiStepMainCore` §1f) is
one cell, not a re-derivation, and the containment `finZW0` had become is retired rather than kept
alongside its replacement.

⚑ **THE LAST TWO CONJUNCTS ARE THE ANTI-VACUITY AND THEY ARE THE ONES THAT COULD GO RED.** The
PADDING block's own perm word is NOT its derived one, so `Field.equal` still runs at a nonzero
difference somewhere in this emission — which is what keeps its `(d⁻¹, 0)` branch instantiated. -/
theorem the_live_block_publishes_the_derived_perm_so_no_solve_is_needed :
    (let d := finProbeData tW.sh tW.sp FIN_LIVE_BLOCK
     d.vals.getD d.fp.slots.permUsed 0
         = qAdd (finBlockVal FIN_LIVE_BLOCK 4) FIN_SHIFT2
     ∧ d.vals.getD d.fp.slots.perm 0 = d.vals.getD d.fp.slots.permUsed 0
     -- ⚑ …the value the word map has to carry, and it does: `Shifted_value.Type2.of_field perm`.
     ∧ qSub (d.vals.getD d.fp.slots.perm 0) FIN_SHIFT2 = finBlockVal FIN_LIVE_BLOCK 4)
    -- ⚑ ANTI-VACUITY: the OTHER block is unchanged — its published `perm` is NOT its derivation, so
    -- `Field.equal` still runs at a nonzero difference somewhere in this emission.
    ∧ (let d := finProbeData tW.sh tW.sp (1 - FIN_LIVE_BLOCK)
       d.vals.getD d.fp.slots.perm 0 ≠ d.vals.getD d.fp.slots.permUsed 0
       ∧ qSub (d.vals.getD d.fp.slots.perm 0) FIN_SHIFT2
           ≠ finBlockVal (1 - FIN_LIVE_BLOCK) 4) := by
  native_decide

#assert_compiled the_emitted_finalize_tape_is_minas
#assert_compiled the_live_block_publishes_the_derived_perm_so_no_solve_is_needed

-- ⚠ The four named below are the ONLY compiler-trusted facts in this namespace, each pinned by
-- `#assert_compiled` at its own site (a RED path in both directions). Everything else — both
-- sponges, the emitted challenge digest and the unbent tape included — is closed by `rfl` or
-- `decide` in the kernel.
#assert_namespace_axioms Dregg2.Circuit.Emit.KimchiWrapFinalizeSpongeGate
  except cip_fold_reproduces_the_accepted_block
         cip_fold_direction_and_every_entry_are_load_bearing
         the_emitted_finalize_tape_is_minas
         the_live_block_publishes_the_derived_perm_so_no_solve_is_needed

end Dregg2.Circuit.Emit.KimchiWrapFinalizeSpongeGate
