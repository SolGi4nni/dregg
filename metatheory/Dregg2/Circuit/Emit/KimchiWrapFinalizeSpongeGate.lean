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

-- ⚠ The two named below are the ONLY compiler-trusted facts in this namespace, each pinned by
-- `#assert_compiled` at its own site (a RED path in both directions). Everything else — both
-- sponges included — is closed by `rfl` in the kernel.
#assert_namespace_axioms Dregg2.Circuit.Emit.KimchiWrapFinalizeSpongeGate
  except cip_fold_reproduces_the_accepted_block
         cip_fold_direction_and_every_entry_are_load_bearing

end Dregg2.Circuit.Emit.KimchiWrapFinalizeSpongeGate
