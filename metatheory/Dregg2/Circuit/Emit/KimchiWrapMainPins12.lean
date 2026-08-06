/-
# Dregg2.Circuit.Emit.KimchiWrapMainPins12 — §20b — W-FINSPONGE, and the memo it was supposed to discharge

⚑ **ONE MODULE OF THE `KimchiWrapMain` SPLIT.** The namespace is unchanged
(`Dregg2.Circuit.Emit.KimchiWrapMain`), so nothing here is renamed and no consumer moves; the file
boundary exists only so a pin re-elaborates without the emitter's 5,000 lines of `def` behind it.
The in-file rule that keeps it stable is the step side's: **a `def` goes in `…Core`/`…Fixture`, a
pin goes in its section's `…PinsNN`.**

⚠ The `set_option` block below is VERBATIM `KimchiWrapMain`'s and must stay that way. `set_option`
does not cross an import, and `KimchiWrapFinalizeSpongeGate` shipped four proofs as `sorryAx` —
each still landing in the environment with the right statement — because a split dropped it.

## ⚑ WHY THIS MODULE EXISTS: A THEOREM FOUR DOCBLOCKS CITED AND NOBODY WROTE

`FIN_DEFERRED_CIP` / `_B` / `_XI` are a MEMO — the three deferred words of the block that claims
`should_finalize`, written down as literals in `KimchiWrapMainField` because deriving them costs a
91-element Fq sponge and a 1732-op straight-line program. A memo is sound only while something
forces it to agree with the derivation, and FOUR places in this tree named that something:

    KimchiWrapMainCore:4403   "`fin_deferred_words_are_the_derivation` closes them by `rfl`"
    KimchiWrapMainCore:4855   "…and `fin_deferred_words_are_the_derivation` both read THIS function"
    KimchiWrapMainField:544   "closes them by `rfl` IN THE KERNEL against `finSpDerivedWords`"
    EmitWrapFinDeferred:8     "discharged by `fin_deferred_words_are_the_derivation` (kernel, `rfl`)"

**`fin_deferred_words_are_the_derivation` did not exist.** `grep` over the whole tree found the four
citations and no `theorem`. The only live discharge was `EmitWrapMainJson`'s runtime refusal — which
is a real fail-closed gate and fires before `writeAtomic`, but it is not what four docblocks said was
there, and it says nothing at all about a shape nobody emits.

⚠ **AND IT COULD NOT HAVE BEEN A KERNEL `rfl`.** `finSpDerivedWords` runs `finSpAll`, which is two
sponges and two compiled `Array FOp` programs per instance. In `whnf` an `Array` is its `List` model:
`KimchiWrapFinalizeSpongeGate` measured a **~200-op** program of exactly this shape failing to reduce
`.size` alone at 1,000,000 heartbeats and taking the elaborator to 21.9 GB. This program is **1732
ops**. So the theorem below is `native_decide` + `#assert_compiled`, the confession is at its own
site, and the four docblocks are corrected to say so. A citation of a kernel proof that is really a
compiled evaluation is the same laundering as a `#guard` — it just spent four docblocks doing it.

⚑ **WHAT IS KERNEL-CLEAN HERE, AND IT IS THE INVARIANT THAT MATTERS.** The 11-row / one-signature
Poseidon block law is proved GENERAL — over every input triple, every output triple and every round
tape any sponge in this file ever produces — so it is not a count that a future rung can regress past.
Everything downstream of `finZW0` (which runs §19's 1047-op probe program) is compiled-evaluated and
says so.
-/
import Dregg2.Circuit.Emit.KimchiWrapMainFixture

namespace Dregg2.Circuit.Emit.KimchiWrapMain
open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.PastaField (qN)

set_option autoImplicit false
set_option maxRecDepth 100000
-- ⚠ §12/§14b reduce whole sponge trajectories IN THE KERNEL (`rfl`/`decide`), which is strictly
-- stronger than the `#guard`s they replace and correspondingly slower to elaborate.
set_option maxHeartbeats 4000000

/-! ### §20b′ — ⚑ **THE POSEIDON BLOCK LAW, GENERAL.**

Rule: *every emitted Poseidon block is exactly 11 rows with ONE coefficient signature, closed by a
single `Zero`.* That invariant held across six rungs before W-FINSPONGE and W-FINSPONGE must not
regress it. Stated here over an ARBITRARY block rather than counted at a shape, because a count is
one instance of it and the thing that goes wrong — a permutation emitted half-open, a 7-row
"permutation", a signature that drifts by a round — is a fact about `permBlockRowsQ` and not about
how many times a rung calls it. Mina's own run-length family is `(Poseidon × 11, Zero)`; this is
that family, as a theorem. -/

/-- ⚑ **EVERY POSEIDON BLOCK THIS FILE CAN EMIT IS 11 + 1, AND ITS COEFFICIENTS ARE
`poseidonRowCoeffsQ` IN ORDER.** General over the six variables and the round tape, so no rung is
exempt and no future sponge can emit a partial block without turning this red. The last conjunct is
the one that keeps it a GATE rather than an arithmetic identity: the closing `Zero` carries
`probe := false`, so it is the block's own output row and not a σ-only probe — a permutation whose
terminator went missing would be spliced into the neighbouring run and the census would read a
different family. -/
theorem poseidon_block_is_eleven_rows_and_one_signature
    (i0 i1 i2 o0 o1 o2 : PVar) (ss : List (List Nat)) :
    (permBlockRowsQ i0 i1 i2 o0 o1 o2 ss).length = 12
    ∧ ((permBlockRowsQ i0 i1 i2 o0 o1 o2 ss).filter
        (fun r => r.kind == KGateType.poseidon)).length = 11
    ∧ ((permBlockRowsQ i0 i1 i2 o0 o1 o2 ss).map (fun r => r.coeffs))
        = (List.range 11).map poseidonRowCoeffsQ ++ [([] : List Int)]
    ∧ ((permBlockRowsQ i0 i1 i2 o0 o1 o2 ss).getLastD default).kind = KGateType.zero
    ∧ ((permBlockRowsQ i0 i1 i2 o0 o1 o2 ss).getLastD default).probe = false
    ∧ ((permBlockRowsQ i0 i1 i2 o0 o1 o2 ss).filter (fun r => r.probe)).length = 0 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### §20b″ — ⚑ **THE TAPES, BY LENGTH, IN THE KERNEL.**

The two sponge schedules are fixed by `FIN_NCOLS` and `WH_MLMB · WH_ROUNDS` and by nothing a witness
chooses, which is why the permutation count below is a shape fact rather than a measurement that
could move under a different fixture. -/

/-- ⚑ **91 AND 30**, from their own definitions rather than from the docblock that quotes them.
`wrap_verifier.ml:844-891` absorbs `sponge_digest_before_evaluations`, the nested challenge digest,
`ft_eval1` and both public evaluations, then `Evals.to_absorption_sequence`'s 43 columns at ζ and ζω
INTERLEAVED; the nested sponge absorbs the flattened old bulletproof challenges. -/
theorem fin_sponge_tape_lengths (s : WrapShape) (sp : SpAcc) (p cd : Nat) :
    (finSpTape s sp p cd).length = 5 + 2 * FIN_NCOLS
    ∧ 5 + 2 * FIN_NCOLS = 91
    ∧ (whOldChals p).length = WH_MLMB * WH_ROUNDS
    ∧ WH_MLMB * WH_ROUNDS = 30 := by
  refine ⟨?_, by decide, ?_, by decide⟩
  · simp [finSpTape, finEvalTape, FIN_NCOLS]
  · simp [whOldChals]

/-! ### §20b‴ — ⚠ **THE COMPILED HALF, AND WHY IT IS COMPILED.**

Everything below reads a slot of a 1732-op `Array FOp` program whose inputs come through `finZW0`'s
1047-op probe. `KimchiWrapFinalizeSpongeGate` measured the wall for exactly this shape: a ~200-op
program of the same kind does not reduce `.size` alone at 1,000,000 heartbeats, and five `rfl`s over
it took the elaborator to 21.9 GB. `#assert_compiled` records the trust at each site rather than
hiding it — and it is a RED PATH IN BOTH DIRECTIONS: a `sorry` errors, and so does a fact that
becomes kernel-clean, which would force these back up to `#assert_axioms`. -/

/-- ⚑⚑ **THE MEMO IS THE DERIVATION — the theorem four docblocks cited and nobody wrote.**

`FIN_DEFERRED_CIP` / `_B` / `_XI` are literals in `KimchiWrapMainField` and `xhatScalar` reads them
(packed statement words 27, 28 and 37 are x_hat MSM entries 32/33, 34/35 and 47), so a wrong triple
does not merely mis-state a value: it puts a scalar into the x_hat MSM that no row of W-FINSPONGE
computes and leaves `Boolean.Assert.any [finalized; not should_finalize]` with no honest witness at
all. This closes the memo against `finSpDerivedWords` — the very function `finSpRows` builds its
witness from and `EmitWrapMainJson` refuses on — so the literal and the emission cannot drift.

⚠ It is stated at the SMOKE shape, which is the shape that emits and proves. `EmitWrapMainJson`
re-derives the same triple at whatever shape it is given and throws before `writeAtomic`, so the
wrap shape is covered by a refusal rather than by a theorem; saying which is which is the point of
this note. -/
theorem fin_deferred_words_are_the_derivation :
    finSpDerivedWords tW = (FIN_DEFERRED_CIP, FIN_DEFERRED_B, FIN_DEFERRED_XI) := by
  native_decide

/-- ⚑⚑⚑ **W-FINSPONGE HAS NO SATISFYING WITNESS ON THE PUBLISHED STEP STATEMENT, AND THAT IS THE
STATEMENT OF THIS THEOREM RATHER THAN A CAVEAT ATTACHED TO A GREEN ONE.**

`finalize_other_proof` is `Boolean.all [xi_correct; b_correct; combined_inner_product_correct;
plonk_checks_passed]`, W-FINSPONGE emits the first three, and `wrap_main.ml:335` asserts
`(1 − finalized)·should_finalize = 0`. Measured on `stepmain_step_r8_finalize`'s own public input:

* `FIN_LIVE_BLOCK` — the block whose packed word 53 IS `should_finalize = 1` — has all three
  differences **NONZERO**, all three bits **zero**, `finalized` **zero**, and therefore the emitted
  assert evaluates to **`1 · 1 = 1 ≠ 0`**. The rung is **UNSATISFIABLE**.
* the other block is unchanged: `should_finalize = 0`, so its own assert is 0 whatever its legs say.

⚠ ⚑ **WHAT CHANGED ON 2026-08-06 AND WHY THE OLD THEOREM WAS WEAKER THAN IT LOOKED.** This used to
read `finSpLegsAt FIN_LIVE_BLOCK = (1,1,1,1,0)` and `finSpDiffsAt FIN_LIVE_BLOCK = (0,0,0)` — the
finalizing block's legs PASS. They passed because `KimchiWrapMainField.prevWordVal` had three
override arms answering `FIN_DEFERRED_CIP/_B/_XI` at exactly words 27, 28 and 37: the statement
CONTAINED the derivation because this file put it there. `xhatScalar` reads the step proof's own
`STEP_PUBLIC_IN` now, the overrides are gone, and the legs are a question for the first time.

⚠ **THE ANSWER IS NO, AND IT IS UNDONE WORK ON THE STEP SIDE, NOT A THEOREM OF THIS MODEL.** The step
proof has to be re-proved with a `Types.Step.Statement` whose finalizing block carries the wrap's own
`combined_inner_product`, `b` and `xi` — and that is a FIXPOINT, because those three words are x_hat
MSM entries 32/33, 34/35 and 47, so writing them moves `x_hat`, which moves every challenge below it,
which moves the derivation. Upstream Pickles closes that loop by construction. Until it is closed
here, everything at or above `w12_finsponge` is an emission that will not prove, and this theorem is
where that is written down — with `KimchiWrapMainField.the_published_statement_does_not_carry_the
_derived_words` naming all six words at issue.

⚑ **WHAT IS PRESERVED IS THE FALSIFIABILITY, and it is why the `(d⁻¹, 0)` branch conjuncts stay.**
`d7d0a150e` shipped a §19 whose `Field.equal` witness was HARDCODED to the agreeing answer, and every
σ-pin and both ladder theorems stayed green while the prover said `Prover("rest of division by
vanishing polynomial")`. A leg that can only be 1 is not a leg — and a leg that can only be 0 is not
one either, which is what the last conjunct is for: `finSpLegsAt` reaches `1` in its fifth component
here, so the tuple is not a constant zero. -/
theorem finsponge_has_no_witness_on_the_published_statement :
    finSpLegsAt FIN_LIVE_BLOCK = (0, 0, 0, 0, 1)
    ∧ (finSpDiffsAt FIN_LIVE_BLOCK).1 ≠ 0
    ∧ (finSpDiffsAt FIN_LIVE_BLOCK).2.1 ≠ 0
    ∧ (finSpDiffsAt FIN_LIVE_BLOCK).2.2 ≠ 0
    ∧ finSpLegsAt (1 - FIN_LIVE_BLOCK) = (0, 0, 0, 0, 0)
    ∧ (finSpDiffsAt (1 - FIN_LIVE_BLOCK)).1 ≠ 0
    ∧ (finSpDiffsAt (1 - FIN_LIVE_BLOCK)).2.1 ≠ 0
    ∧ (finSpDiffsAt (1 - FIN_LIVE_BLOCK)).2.2 ≠ 0
    -- ⚑ …and this is the emitted assert, evaluated: `(1 − finalized)·should_finalize = 1`.
    ∧ (let l := finSpLegsAt FIN_LIVE_BLOCK
       qMul (qSub 1 l.2.2.2.1) (finBlockVal FIN_LIVE_BLOCK PREV_SHOULD_FINALIZE) = 1) := by
  native_decide

/-- ⚑ **AND THE ASSERT CAN STILL GO RED.** `(1 − finalized)·should_finalize = 0` holds on the
non-finalizing block only because its `should_finalize` word is 0; its `finalized` is 0, so the same
row at `should_finalize = 1` is `1 · 1 = 1 ≠ 0` and the rung would be unsatisfiable. Stated as the
arithmetic rather than as a comment, because a refusal nothing has ever been shown to fire is not a
refusal — and because deriving the deferred words in EVERY block (the tempting simplification) would
force all four legs to 1 everywhere and delete this instance. -/
theorem finsponge_assert_reds_if_the_other_block_claims_should_finalize :
    finBlockVal FIN_LIVE_BLOCK PREV_SHOULD_FINALIZE = 1
    ∧ finBlockVal (1 - FIN_LIVE_BLOCK) PREV_SHOULD_FINALIZE = 0
    ∧ (let l := finSpLegsAt (1 - FIN_LIVE_BLOCK); qMul (qSub 1 l.2.2.2.1) 1 ≠ 0) := by
  native_decide

/-- ⚑⚑ **THE POSEIDON CENSUS THIS RUNG MOVES**, read off its OWN emitted rows.

Per instance the nested challenge-digest sponge absorbs `WH_MLMB · WH_ROUNDS = 30` elements and
squeezes once (**15** permutations: the rate-2 machine permutes before absorbs 3, 5, …, 29 — that is
14 — and once more for the squeeze, which arrives at `Absorbed 2`), and the finalize sponge absorbs
**91** and squeezes twice (**46**: 45 during the absorbs, one for the first squeeze; the second
squeeze reads lane 1 of the SAME permutation, which is `finalize_sponge_squeezes_share_one_permutation`
and is why this is 46 and not 47). **61 per instance, 122 at `prevs = 2`** — and `prevs = 2` at BOTH
committed shapes, so the wrap-scale figure is this figure.

Against Mina's `wrap-transaction`: **137 blocks before this rung, 259 of 261 after.** The two that
remain are not this sponge's.

⚠ The Zero count moves with it and that is stated rather than netted: every `(Poseidon × 11, Zero)`
block ends in its own `Zero`, and W-FINSPONGE's own σ-probe rows land after squeezes — so this rung
also grows the `Zero ≥ 2` run family that Mina's wrap does not have at all. Same row economy as the
transcript sponge, not a new one. -/
theorem finsponge_emits_one_hundred_and_twenty_two_poseidon_blocks :
    (finSpRowsW.filter (fun r => r.kind == KGateType.poseidon)).length = 122 * 11
    ∧ shapeSmoke.prevs = 2
    ∧ shapeWrap.prevs = 2
    ∧ 137 + 122 = 259 := by
  native_decide

-- ⚑ The four above are the ONLY compiler-trusted facts in this module and each is pinned at its own
-- site. The general Poseidon block law and the tape lengths are closed by `rfl`/`simp` in the
-- kernel above, which is the split `cip_lift_…` exists to make: a confession that swallows
-- kernel-clean conjuncts loses their pin.
#assert_compiled fin_deferred_words_are_the_derivation
#assert_compiled finsponge_has_no_witness_on_the_published_statement
#assert_compiled finsponge_assert_reds_if_the_other_block_claims_should_finalize
#assert_compiled finsponge_emits_one_hundred_and_twenty_two_poseidon_blocks

end Dregg2.Circuit.Emit.KimchiWrapMain
