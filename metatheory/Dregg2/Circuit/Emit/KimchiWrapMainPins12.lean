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
theorem fin_sponge_tape_lengths (p cd : Nat) :
    (finSpTape p cd).length = 5 + 2 * FIN_NCOLS
    ∧ 5 + 2 * FIN_NCOLS = 91
    ∧ (whOldChals p).length = WH_MLMB * WH_ROUNDS
    ∧ WH_MLMB * WH_ROUNDS = 30 := by
  refine ⟨?_, by decide, ?_, by decide⟩
  · simp [finSpTape, finEvalTape, FIN_NCOLS]
  · simp only [whOldChals]; decide

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

/-! ### §20b⁗ — ⚑⚑⚑ **THE EVALUATIONS ARE A REAL WRAP PROOF'S, AND §19 REPRODUCES ITS `ft_eval0`.**

Until 2026-08-06 both sides of the 27/28/37 disagreement ran on pseudo-random mixers — the wrap's on
`wrapFixtureQ`, the step's on `KimchiStepMainCore.evVal` — and four docblocks priced the repair as a
FIELD CROSSING that does not exist. The three theorems below replace that paragraph with facts. -/

/-- ⚑⚑ **THE BLOCK DECLARES WHICH PROOF IT IS ABOUT, AND IT IS MINA'S.** This is what makes the
choice of evaluations a measurement rather than a preference: the live block's own packed statement
words — its Fq-sponge digest and its β, γ, α′, ζ′ — ARE Mina devnet block 539508's Wrap proof's, to
the digit, and they came from `STEP_PUBLIC_IN`, the step proof's own public input, not from this
file. A block that says "I am that proof" must be finalized against that proof's evaluations.

✅ ⚑⚑⚑ **AND SINCE 2026-08-07 THE SAME BLOCK'S FIELD WORDS ARE THAT PROOF'S TOO — the conjuncts
that used to be `≠` are `=`.** They read: *"`combined_inner_product`, `b` and ξ′ disagree with the
derivation, and ξ′ disagrees with `V_CHAL` … the STEP assembly published a real block's challenges
beside its own mixer's scalars."*

⚠ **THE DIAGNOSIS IN THAT SENTENCE WAS WRONG AND IS RETIRED WITH IT.** It named
`KimchiStepMainCore.evVal` as the mixer and `MinaWrapDeferredWeld.EVALS` as the object it stands in
for. `evVal` IS a mixer and `EVALS` IS what it stands in for — but that is the **step** circuit's
own `finalize_other_proof`, over the WRAP statement's Fp deferred values, and pointing it at `EVALS`
would not have moved packed words 27/28/37 by one digit. Those words were **aliased onto the wrap
statement's cells**: `bpDiv2`/`bpOdd 0,1` and `vXiStmt`, R5/R6/R8's Fp outputs, published where the
Fq deferred values about the wrap proof belong. `KimchiStepMainCore` §1f gave them their own cells
and this theorem is the measurement of that: the live block now declares itself Mina's proof in its
challenges AND in its field words, ξ′ IS `V_CHAL`, and `combined_inner_product` unshifts to
`MinaRealBlockGate.CIP` — the number kimchi's own verifier computed.

⚑ **THE LAST CONJUNCT IS THE ANTI-VACUITY AND IT IS THE ONE THAT COULD GO RED**: the OTHER block
declares nothing of the kind, so this is a fact about a pairing and not about every block agreeing
with everything. -/
theorem the_live_block_declares_itself_minas_own_wrap_proof :
    finBlockVal FIN_LIVE_BLOCK FIN_W_DIGEST
      = Dregg2.Circuit.Emit.MinaRealBlockTranscript.FQ_DIGEST
  ∧ finBlockVal FIN_LIVE_BLOCK 6 = Dregg2.Circuit.Emit.MinaRealBlockTranscript.BETA_N
  ∧ finBlockVal FIN_LIVE_BLOCK 7 = Dregg2.Circuit.Emit.MinaRealBlockTranscript.GAMMA_N
  ∧ finBlockVal FIN_LIVE_BLOCK 8 = Dregg2.Circuit.Emit.MinaRealBlockTranscript.ALPHA_CHAL
  ∧ finBlockVal FIN_LIVE_BLOCK 9 = Dregg2.Circuit.Emit.MinaRealBlockTranscript.ZETA_CHAL
  -- ✅ ⚑ …and the SAME block's ξ′ IS that proof's, which is the step-side gap, CLOSED.
  ∧ finBlockVal FIN_LIVE_BLOCK FIN_W_XI
      = Dregg2.Circuit.Emit.MinaRealBlockTranscript.V_CHAL
  -- ✅ ⚑ …as is its `combined_inner_product`, read through `Shifted_value.Type2.to_field`.
  ∧ qAdd (finBlockVal FIN_LIVE_BLOCK FIN_W_CIP) FIN_SHIFT2
      = ZMod.val Dregg2.Circuit.Emit.MinaRealBlockGate.CIP
  -- ⚑ …and the OTHER block declares nothing of the kind, so this is not a property of every block.
  ∧ finBlockVal (1 - FIN_LIVE_BLOCK) FIN_W_DIGEST
      ≠ Dregg2.Circuit.Emit.MinaRealBlockTranscript.FQ_DIGEST := by
  native_decide

/-- ⚑⚑ **§19c READS THAT PROOF, AND NOT THE MIXER IT USED TO.** The four families are the real
block's `es` columns after the 4-entry prefix `verifier.rs:492-540` puts ahead of them (2 recursion
b-polynomials, the public polynomial, `ft`) — the same drop `MinaRealBlockTranscript.evalsTape`
takes from the other end, so the two readings are one convention rather than two.

⚑ **THE ANTI-VACUITY IS THE LAST THREE CONJUNCTS**, and they are the ones a future edit reds:
not one of the 43 columns coincides with the `wrapFixtureQ` value it replaced, at either point. A
theorem that only said "the columns equal `EVZ_N`" would stay green if someone re-pointed `EVZ_N`
at a mixer. -/
theorem the_finalize_evaluations_are_minas_own_wrap_proof :
    ((List.range FIN_NCOLS).all (fun k =>
        finColVal FIN_LIVE_BLOCK k 0
          == Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZ_N.getD (FIN_EV_PREFIX + k) 0
        && finColVal FIN_LIVE_BLOCK k 1
          == Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZW_N.getD (FIN_EV_PREFIX + k) 0)) = true
  ∧ finPZetaVal FIN_LIVE_BLOCK = ZMod.val Dregg2.Circuit.Emit.MinaRealBlockGate.PZ
  ∧ finFtEval1Val FIN_LIVE_BLOCK = ZMod.val Dregg2.Circuit.Emit.MinaRealBlockGate.FT1
  ∧ finPZetaWVal FIN_LIVE_BLOCK
      = Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZW_N.getD FIN_EV_PUB 0
  -- ⚑ ANTI-VACUITY: no column is the mixer's value, at ζ or at ζω, in either block.
  ∧ ((List.range FIN_NCOLS).filter (fun k =>
        finColVal FIN_LIVE_BLOCK k 0 == wrapFixtureQ (40 + 2 * FIN_LIVE_BLOCK) k
        || finColVal FIN_LIVE_BLOCK k 1
             == wrapFixtureQ (40 + 2 * FIN_LIVE_BLOCK + 1) k)).length = 0
  ∧ finPZetaVal FIN_LIVE_BLOCK ≠ wrapFixtureQ (44 + FIN_LIVE_BLOCK) 0
  ∧ finFtEval1Val FIN_LIVE_BLOCK ≠ wrapFixtureQ (60 + FIN_LIVE_BLOCK) 0
  -- ⚑⚑ …AND THE TAG COLLISION IS GONE, which is the part a reader would not guess. The old
  -- `wrapFixtureQ (40 + 2p + j)` family OVERLAPPED W-BULLET's: `finColVal 0 z 1` was
  -- `wrapFixtureQ 41 0`, which IS `bullScalVal 1` (`z₁`), and `finColVal 1 z 0` was
  -- `wrapFixtureQ 42 0`, which IS `bullScalVal 2` (`z₂`). Two sub-circuits' unrelated witness
  -- cells carried ONE number. They are distinct values now, and `z₁`/`z₂` stay free because free
  -- is their faithful shape (`wrap_main.ml:357-382`) — the defect was the aliasing, not the
  -- freeness.
  ∧ finColVal FIN_LIVE_BLOCK FIN_IDX_Z 1 ≠ bullScalVal 1
  ∧ finColVal FIN_LIVE_BLOCK FIN_IDX_Z 0 ≠ bullScalVal 2 := by
  native_decide

/-- ⚑⚑⚑ **AND NOTHING CROSSES A FIELD — THE THEOREM THAT REPLACES THE DELETED PARAGRAPH.**

`KimchiWrapMainField` §15c‴ and `…Pins12` §20 both said these evaluations are Fp and "enter only
through `Other_field` (`impls.ml:167-217`)", and that the encoding was the distance to the top of
the ladder. `wrap_main`'s `finalize_other_proof` finalizes deferred values about **wrap** proofs,
whose scalar field IS this circuit's native Fq, so there is nothing to encode. This states that as
a property of the block's own configuration rather than as a reading of OCaml:

  * every word §20's 91-element tape absorbs is already a legal Fq element — the whole obligation
    an `Other_field` encoding would exist to discharge, discharged by being vacuous;
  * the domain is the **wrap** one and the ω and coset shifts are that index's, digit for digit;
  * the closing shift is `Shifted_value.Type2` — the SAME-field shift. `Type1`, the one whose `c`
    is created over the other field, is what `wrap_main.ml:454` puts on `combined_inner_product`,
    and `KimchiStepWrapChain.cip_crosses_by_type1_over_Fp` is where that one lives;
  * ⚑ and the NEGATIVE CONTROL: the step proof's own `ft_eval1` — the Fp scalar the deleted
    paragraph named — is NOT what this rung reads. Naming the wrong object was the error, not
    getting the encoding wrong. -/
theorem the_finalize_evaluations_need_no_encoding :
    (finSpTape FIN_LIVE_BLOCK 0).all (fun w => decide (w < qN)) = true
  -- ⚑ the DOMAIN is the real Wrap index's own, stated against `MinaRealBlockGate.N` and not
  -- against `FIN_LOG2N`'s own definition — two sources, so it is a gate and not decoration.
  ∧ 2 ^ FIN_LOG2N = Dregg2.Circuit.Emit.MinaRealBlockGate.N
  ∧ FIN_OMEGA = ZMod.val Dregg2.Circuit.Emit.MinaRealBlockGate.OMEGA
  ∧ FIN_SHIFTS = Dregg2.Circuit.Emit.MinaRealBlockGate.SHIFT.map ZMod.val
  -- ⚑ and the shift is `Type2`'s and NOT `Type1`'s — `2^255` in Fq against `(2^255+1) mod p`, the
  -- constant `shifted_value.ml:124` creates over the OTHER field. Two constants, one inequality:
  -- naming `Type2` is the whole claim that nothing crosses.
  ∧ FIN_SHIFT2 = 2 ^ 255 % qN
  ∧ FIN_SHIFT2 ≠ (2 ^ 255 + 1) % Dregg2.Circuit.Emit.PastaField.pN
  ∧ finFtEval1Val FIN_LIVE_BLOCK
      ≠ Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_FT_EVAL1_FP := by
  native_decide

/-- ⚑⚑⚑ **THE REALITY GATE: §19's OWN PROGRAM REPRODUCES MINA'S `ft_eval0` AND ITS LINEARIZATION
CONSTANT, ON MINA'S OWN WRAP PROOF.**

This is the first time the finalize sub-circuit has been checkable against anything. `finProbeData`
runs the emitted 1047-op program on the RAW evaluations — before `finZW0` solves `z(ζω)` — with the
live block's own statement challenges, and three of its slots land on numbers `MinaRealBlockGate`
carries from the block's `oracles(...)`:

  * `linConst` = `LCT`, the `Scalars.Tock` constant term folded over the six always-on gate bodies —
    generic, poseidon, complete_add, var_base_mul, endomul, endomul_scalar. A wrong α power, a
    transposed MDS row or a missing selector multiply moves it;
  * `ftEval0` = `FT0` — the whole `plonk_checks.ml:420-460` body: the σ/w Horner numerator, the
    seven-shift denominator, the C5 quotient and the linearization subtraction;
  * `zkp` = `PVP`, the permutation vanishing polynomial at the real ζ.

`MinaRealBlockGate.real_ft_eval0` proves the same identity for `KimchiVerify`'s C5 — a SECOND,
independently written formula over the same inputs. Two implementations, one number, one real
proof.

⚠ ⚑ **WHAT THIS DOES NOT SAY, AND THE SEQUEL IT LOCATED.** It does not say `w11_finsponge` proves —
that is `finsponge_has_a_witness_on_the_published_statement`, and it says so as of 2026-08-07. When
this paragraph was written the `ft_eval0` leg was real and the sponge above it was not: `finSpTape`'s
challenge digest was over `whOldChals`, a `wrapFixtureQ` where `MinaRealBlockGate.CHALS0`/`CHALS1`
belong, and `finZW0` moved `z(ζω)` off the real value because packed word `27·FIN_LIVE_BLOCK + 4`
was not the derived `perm`. ✅ Both are closed: the digest is that block's, and word 31 carries
`Shifted_value.Type2.of_field perm`, so `finZW0`'s ratio is 1 and the bend is the identity.

✅ ⚑ **THE FIRST OF THOSE TWO CLOSED ON 2026-08-07 AND THE SPONGE HAS ITS OWN REALITY GATE NOW.**
`whOldChals` is `MinaRealBlockTranscript.CHALS_FLAT`, and `KimchiWrapFinalizeSpongeGate` measures
what that bought, against a referee this file cannot influence:

  * `the_emitted_challenge_digest_is_the_accepted_blocks` — §20's own nested sponge squeezes
    `PREV_CHAL_DIGEST`, and the mixer it replaced does not;
  * `the_emitted_finalize_tape_is_minas` — the emitted 91-element tape against
    `MinaRealBlockTranscript.fqTape2` disagrees in `[]` slots, and the emitted tape's own two
    squeezes ARE `V_CHAL` and `U_CHAL`. ⚠ It read `[6]` — WHICH slot rather than how many — until
    the step statement stopped aliasing packed word 31;
  * `the_unbent_finalize_tape_is_minas_and_squeezes_to_its_challenges` — with that one bend removed
    the tape IS `fqTape2` and §20's two squeezes ARE `V_CHAL` and `U_CHAL`.

✅ **AND `FIN_DEFERRED_XI` IS `V_CHAL` SINCE 2026-08-07**, because the single named statement word
that stood in the way — packed 31, the live block's `perm` — is the derived one now:
`the_live_block_publishes_the_derived_perm_so_no_solve_is_needed`. -/
theorem finalize_reproduces_minas_own_ft_eval0 :
    (let d := finProbeData tW.sh tW.sp FIN_LIVE_BLOCK
     d.vals.getD d.fp.slots.ftEval0 0 = ZMod.val Dregg2.Circuit.Emit.MinaRealBlockGate.FT0
     ∧ d.vals.getD d.fp.slots.linConst 0
         = ZMod.val Dregg2.Circuit.Emit.MinaRealBlockGate.LCT
     ∧ d.vals.getD d.fp.slots.zkp 0 = ZMod.val Dregg2.Circuit.Emit.MinaRealBlockGate.PVP)
  -- ⚑ …and the OTHER block, on the same evaluations at its own synthetic challenges, lands on
  -- NONE of the three — so this is a fact about the pair (proof, challenges), not about the
  -- program answering the same thing whatever it is fed.
  ∧ (let d := finProbeData tW.sh tW.sp (1 - FIN_LIVE_BLOCK)
     d.vals.getD d.fp.slots.ftEval0 0 ≠ ZMod.val Dregg2.Circuit.Emit.MinaRealBlockGate.FT0
     ∧ d.vals.getD d.fp.slots.linConst 0
         ≠ ZMod.val Dregg2.Circuit.Emit.MinaRealBlockGate.LCT
     ∧ d.vals.getD d.fp.slots.zkp 0 ≠ ZMod.val Dregg2.Circuit.Emit.MinaRealBlockGate.PVP) := by
  native_decide

/-- ✅ ⚑⚑⚑ **W-FINSPONGE HAS A SATISFYING WITNESS ON THE PUBLISHED STEP STATEMENT (2026-08-07), AND
THAT IS THE STATEMENT OF THIS THEOREM RATHER THAN A CAVEAT REMOVED FROM A RED ONE.**

`finalize_other_proof` is `Boolean.all [xi_correct; b_correct; combined_inner_product_correct;
plonk_checks_passed]`, W-FINSPONGE emits the first three, and `wrap_main.ml:335` asserts
`(1 − finalized)·should_finalize = 0`. Measured on `stepmain_step_r8_finalize`'s own public input:

* `FIN_LIVE_BLOCK` — the block whose packed word 53 IS `should_finalize = 1` — has all three
  differences **ZERO**, all three bits **one**, `finalized` **one**, and the emitted assert
  evaluates to **`0 · 1 = 0`**. The rung is **SATISFIABLE**.
* the other block is unchanged: its three differences are NONZERO, its bits are zero, and its own
  assert is 0 because `should_finalize` is 0. Both `Field.equal` branches stay live, which is what
  keeps the gadget falsifiable.

⚠ ⚑⚑ **WHAT IT WAS, AND WHAT THE WRONG DIAGNOSIS COST.** Until this commit it read
`finSpLegsAt FIN_LIVE_BLOCK = (0,0,0,0,1)`, an honest measurement of a rung with no witness, under a
paragraph that priced the repair as *"two derivations of one quantity … those three words are not
free on the step side — they are `bpDiv2`/`bpOdd` and `vXiStmt`, the step circuit's OWN
`combined_inner_product`, `b` and `xi`, so a statement carrying the wrap's numbers would make the
STEP circuit unsatisfiable rather than this one satisfiable."*

**Both clauses were true sentences about the wrong object.** `bpDiv2`/`bpOdd`/`vXiStmt` are the
step circuit's own deferred values — of the **WRAP proof-state it verifies**, Fp,
`Shifted_value.Type1`. Packed words 27/28/37 are a **step statement's** `unfinalized_proofs`
deferred values — Fq, `Type2`, about the wrap proof — which the step circuit cannot compute and
therefore DEFERS. They were never two derivations of one quantity; they were one set of cells
carrying two statements' words, in two fields. `KimchiStepMainCore` §1f gave the step statement's
live block its own eleven cells; nothing became unsatisfiable, and the step proof still verifies
(`pickles_kimchi_marshal`: `batch_verify = Ok`).

⚑ **AND THE PREVIOUS PARAGRAPH'S OWN PREDECESSOR WAS WRONG THE OTHER WAY** — it had priced the
repair as a FIXPOINT over `x_hat`. §20c refuted that (a stratification, no edges), and the
stratification is what made this land in ONE emit-and-re-prove pass rather than an iteration.

⚑ **WHAT IS PRESERVED IS THE FALSIFIABILITY, and it is why the `(d⁻¹, 0)` branch conjuncts stay.**
`d7d0a150e` shipped a §19 whose `Field.equal` witness was HARDCODED to the agreeing answer, and
every σ-pin stayed green while the prover said `Prover("rest of division by vanishing polynomial")`.
A leg that can only be 1 is not a leg. Block 0's three differences are nonzero here, so both
branches of the gadget are exercised by the same emission — and giving block 0 a `should_finalize`
of 1 makes this rung unsatisfiable, which is the instance that keeps the assert real. -/
theorem finsponge_has_a_witness_on_the_published_statement :
    finSpLegsAt FIN_LIVE_BLOCK = (1, 1, 1, 1, 0)
    ∧ (finSpDiffsAt FIN_LIVE_BLOCK).1 = 0
    ∧ (finSpDiffsAt FIN_LIVE_BLOCK).2.1 = 0
    ∧ (finSpDiffsAt FIN_LIVE_BLOCK).2.2 = 0
    ∧ finSpLegsAt (1 - FIN_LIVE_BLOCK) = (0, 0, 0, 0, 0)
    ∧ (finSpDiffsAt (1 - FIN_LIVE_BLOCK)).1 ≠ 0
    ∧ (finSpDiffsAt (1 - FIN_LIVE_BLOCK)).2.1 ≠ 0
    ∧ (finSpDiffsAt (1 - FIN_LIVE_BLOCK)).2.2 ≠ 0
    -- ⚑ …and this is the emitted assert, evaluated: `(1 − finalized)·should_finalize = 0`.
    ∧ (let l := finSpLegsAt FIN_LIVE_BLOCK
       qMul (qSub 1 l.2.2.2.1) (finBlockVal FIN_LIVE_BLOCK PREV_SHOULD_FINALIZE) = 0)
    -- ⚑⚑ …and the SAME assert on the OTHER block, at `should_finalize` forced to 1: `1 · 1 = 1`.
    -- The rung this emission proves is one whose assert CAN fail, and here is the input that fails
    -- it. Without this the tuple above is a green reading of a gadget that might accept anything.
    ∧ (let l := finSpLegsAt (1 - FIN_LIVE_BLOCK)
       qMul (qSub 1 l.2.2.2.1) 1 = 1) := by
  native_decide


/-! ### §20c — ⚑⚑⚑ **THE DEPENDENCY ORDER, AS A DATAFLOW FACT ABOUT THE EMITTED PROGRAM.**

The theorem above says the three deferred words have no witness. The next question is what it costs
to give them one, and until 2026-08-06 this file and `KimchiWrapMainField` both answered **"a
FIXPOINT, because those three words are x_hat MSM entries, so writing them moves `x_hat`, which
moves every challenge below it, which moves the derivation."**

⚠ **THAT ANSWER IS FALSE IN THIS MODEL, AND THE COST OF BELIEVING IT WAS THE REPAIR NOT HAPPENING.**
Its first clause is true — writing the words does move `x_hat` and every transcript challenge below
it, and `KimchiWrapMainCore` §20's own note lists what re-emits. Its second clause does not follow,
and it is the one that priced the repair as unbounded iteration: **no transcript squeeze value reaches
§19 or §20 at all.** The `sp : SpAcc` threaded through `finWireOf` and `finSpWireOf`
(⚑ and NO LONGER through `finSpTape`: `finZW0`'s deletion made that thread dead and it is gone)
supplies variable ADDRESSES (`prevW s sp w = .external (basePrev s sp + w)`), never values; §19's own
β and γ are `prevW s sp (finBlockWord p 6)` / `(… p 7)` — PACKED STATEMENT WORDS, not the transcript's
β and γ; and the finalize sponge is a FRESH `runSpongeQ` over `finSpTape`, whose 91 elements are one
statement word, a digest over `whOldChals`, and evaluation columns. ⚑ Both of those last two were
`wrapFixtureQ` when this was written and are Mina devnet block 539508's own since 2026-08-06/07; the
STRATIFICATION is unchanged by that, which is the point of stating it over the cone below rather than
over the provenance of the values.

So the loop the docblocks named **closes upstream in Pickles, where a step proof's deferred values are
the previous wrap's squeezes — not inside this model's definition graph.** Here it is a
STRATIFICATION with no edges between its levels, and it terminates in ONE evaluation:

    stratum 0   word 54                 derived by NOTHING on the wrap side. `prevRows`'
                                        `Field.Assert.equal` ties Mina's public slot 12 to it; the
                                        wrap reads it and exposes it, and computes no value for it.
    stratum 1   words 55, 56            `whPrevDigest 0/1` — a Poseidon squeeze over `whOldChals`
                                        (`wrapFixtureQ 41`) and `whSgOld` (`STEP_PREVCOMM_XY`, a
                                        RECURSION-CHALLENGE commitment, which is an INPUT to
                                        `create_recursive` and not one of its outputs). Reads no
                                        packed word; stable under re-proving the step circuit.
    stratum 2   words 27, 28, 37        the finalize derivation, over block-1 words 4, 6, 7, 8, 9,
                                        26 and 11–25 and word 5 — i.e. the OTHER 51 packed words —
                                        plus `wrapFixtureQ` evaluation columns.

⚠ ⚑⚑ **AND THE ORDER IS ONLY HALF THE ANSWER, BECAUSE THE OBVIOUS REPAIR IS IMPOSSIBLE FOR FOUR OF
THE SIX — WHICH IS THE FINDING, AND IT NAMES A DIFFERENT DEFECT.** "Re-prove the step circuit with
these six words written in" works only where the step side leaves the word FREE. Measured against
`KimchiStepMainCore.stepStmtVar` (`:4820`) and its `circuitEnv`:

    entry 65, 66   words 55, 56   `vStmtWrapMsg0` / `vStmtWrapMsgs`  FREE — sourceless constants,
                                  no row writes them (`occAt … = 1` and `2`, both READ-only).
                                  Writable. This stratum really is one edit and a re-prove.
    entry 32–35    words 27, 28   `bpDiv2/bpOdd 0` and `1`           CONSTRAINED — the STEP circuit's
                                  OWN `combined_inner_product` and `b`, off R5's Horner fold and
                                  `bActualOf`, split by `stmtRows`' `cSplit`.
    entry 47       word 37        `vXiStmt`                          CONSTRAINED — tied to the step's
                                  own fr-sponge squeeze by R8's `xi_correct`.
    entry 64       word 54        `hmOutDigestVar`                   CONSTRAINED — it IS segment D's
                                  Poseidon squeeze cell.

Writing the wrap's value at any of those five would make the STEP circuit unsatisfiable, not the wrap
circuit satisfiable. **So the disagreement at 27, 28, 37 is not a statement that needs re-baking; it
is TWO INDEPENDENT DERIVATIONS OF ONE QUANTITY THAT DISAGREE** — the step circuit computes
`combined_inner_product`, `b` and `xi` from its own transcript, and this rung recomputes them from
`finColVal`/`finPZetaVal`/`finPZetaWVal`/`finFtEval1Val`, which are `wrapFixtureQ` fixtures standing
in for `prev_proof.openings.evals`. `finalize_other_proof` is supposed to read the step proof's ACTUAL
evaluations. It reads a fixture, so it gets a different number, and no statement can satisfy both.

⚑ **THAT IS THE SAME DEFECT CLASS THIS CAMPAIGN SPENT THE DAY DELETING — a fixture where a real value
belongs, making two copies of one object — and it is what actually blocks these three rungs.**

⚠ ⚑ **THE PARAGRAPH THAT FOLLOWED PRICED THE REPAIR AS A FIELD BOUNDARY AND WAS WRONG ON BOTH
CLAUSES. IT IS DELETED, NOT SOFTENED.** It read: *"The repair is to wire §19/§20's evaluation inputs
to the step proof's own `evals`, not to re-bake a statement. And the reason that is not a one-line
change is a FIELD BOUNDARY, stated rather than discovered later: those evaluations are **Fp**,
Vesta's scalar field, while this circuit is native **Fq**, so they enter only through `Other_field`
(`impls.ml:167-217`, one Fq wire because `p < q`) — the encoding `KimchiStepWrapChainFixture`'s own
header names as the thing its negative-control items would need. That encoding is not assembled here.
It, and not a fixpoint, is the distance to the top of the ladder."*

`wrap_main.ml`'s `finalize_other_proof` finalizes the deferred scalar work of the proofs the STEP
verified, and those are **wrap** proofs over Pallas — scalar field Fq, this circuit's own. §19's
configuration had been saying so since it was written: `FIN_LOG2N = 14` is `Common.wrap_domains
~proofs_verified:1 |>.h`, `FIN_OMEGA`/`FIN_SHIFTS` are `MinaRealBlockGate.OMEGA`/`.SHIFT` digit for
digit, and `finBuild` closes with `Shifted_value.Type2`, the same-field shift. **Nothing crosses, and
the crossing was never the cost.** "The step proof's own `evals`" also names the wrong object: those
are Fp at the `2^16` step domain and belong to the NEXT step circuit's finalize. §19c reads Mina
devnet block 539508's own Wrap-proof evaluations since 2026-08-06 —
`MinaRealBlockGate.EVZ`/`EVZW`, in this tree the whole time, the same proof whose index supplies
`FIN_OMEGA` and whose transcript supplies packed words 32–36.

⚑ **AND THE THEOREM BELOW IS WHAT MAKES STRATUM 2 A FACT RATHER THAN A READING.** Prose about a
definition graph is exactly the instrument that was wrong before; this computes the transitive input
cone of the two values the rung DERIVES, over the ACTUAL 1732-op emitted program, and shows the three
cells it CHECKS are not in it. A future edit that wires a statement word — or a transcript squeeze —
into the derived side turns it red at the place the claim is made. -/

/-- ⚑ The transitive INPUT CONE of a set of slots in a straight-line `FOp` program: every slot whose
value the roots' values are computed from.

**ONE DESCENDING PASS IS COMPLETE**, and that is a property of `fnEm` rather than an approximation:
`modifyGet (fun st => (st.size, st.push o))` hands back the size BEFORE the push, so every operand
index a slot names is STRICTLY BELOW it. `List.foldr` over `List.range n` applies `n-1` innermost and
`0` outermost, which is that order.

⚠ `.aeq i j` contributes BOTH operands even though its value is slot `i`'s. That over-approximates the
cone, which is the conservative direction here: a theorem that a cell is ABSENT from a cone is only
strengthened by the cone being too big. -/
def fnCone (prog : Array FOp) (roots : List Nat) : Array Bool :=
  let n := prog.size
  let m0 := roots.foldl (fun (m : Array Bool) r => m.modify r (fun _ => true))
              (Array.replicate n false)
  (List.range n).foldr (fun i m =>
      if m.getD i false then
        match prog.getD i default with
        | .add a b | .sub a b | .mul a b | .aeq a b =>
            (m.modify a (fun _ => true)).modify b (fun _ => true)
        | _ => m
      else m) m0

/-- …and the CIRCUIT CELLS in that cone — the `.inp` aliases, i.e. everything outside the program
that the roots' values depend on. This is the list a dependency claim is actually about. -/
def fnConeInputs (prog : Array FOp) (roots : List Nat) : List PVar :=
  let m := fnCone prog roots
  ((List.range prog.size).filter (fun i => m.getD i false)).filterMap (fun i =>
    match prog.getD i default with | .inp v => some v | _ => none)

/-- ⚑⚑⚑ **W-FINSPONGE DERIVES ITS THREE WORDS WITHOUT READING THEM — SO THE REPAIR IS ONE PASS, NOT A
FIXPOINT.**

`finSpBuild` closes `bAct` (`:5083`) and `cipAct` (`:5105`) BEFORE `bStmt` and `cipStmt` are ever
aliased (`:5084`, `:5106`), and `xiRaw` is the finalize sponge's own squeeze cell rather than a
statement word. This states that as a fact about the emitted program instead of about the source
order, over the transitive cone.

  * **legs 1–3** — the three cells the rung CHECKS are absent from the cone of the two it DERIVES.
    Those cells are packed words `27·FIN_LIVE_BLOCK + {0, 1, 10}` = **27, 28 and 37**, the three
    `the_published_statement_carries_every_derived_word_but_the_arity_mismatched_one` names.
  * **leg 4** — and ξ's two sides are different cells, so `xi_correct` is not an identity either.
  * **legs 5–9, THE ANTI-VACUITY** — the cone is not empty and not a handful: it contains ζ, r, ξ,
    the first `compute_challenges` lift and the first evaluation column, and runs to more than
    seventy cells. A `fnCone` that returned nothing would satisfy legs 1–4 and say nothing, which is
    the shape a green gate takes when its subject has quietly left.

⚠ Stated at the SMOKE shape, which is the shape that emits and proves; the wrap shape's program is
the same builder at the same `WH_ROUNDS` and `FIN_NCOLS`, and its own emission is covered by
`EmitWrapMainJson`'s refusal. -/
theorem the_deferred_derivation_does_not_read_the_words_it_checks :
    (let fa := finAll tW
     let d := (finSpAll tW fa).getD FIN_LIVE_BLOCK default
     let W := finSpWireOf tW fa d FIN_LIVE_BLOCK
     let cone := fnConeInputs d.fp.prog [d.fp.slots.bAct, d.fp.slots.cipAct]
     cone.contains W.cipStmt = false
     ∧ cone.contains W.bStmt = false
     ∧ cone.contains W.xiStmt = false
     ∧ (W.xiRaw == W.xiStmt) = false
     ∧ cone.contains W.zeta = true
     ∧ cone.contains W.rF = true
     ∧ cone.contains W.xiF = true
     ∧ cone.contains (W.u 0) = true
     ∧ cone.contains (W.ez 0) = true
     ∧ decide (70 < cone.length) = true) := by
  native_decide

/-- ⚑ **STRATUM 1, MEASURED: NO PUBLISHED STATEMENT ENTRY REACHES THE WRAP-HACK TAPE.**

`whPrevDigest p` is what packed words 55 and 56 must become, and the whole reason it can be computed
ONCE — before the step proof is re-proved, and without iterating — is that its tape is disjoint from
the step statement. Its 32 elements are 30 `wrapFixtureQ 41` challenges and the two coordinates of
`STEP_PREVCOMM_XY`, which is a `RecursionChallenge` commitment: an argument to
`ProverProof::create_recursive`, not a value it returns. Re-proving with a different public input
moves `STEP_PUBCOMM_XY`, `STEP_WCOMM_XY` and every derived challenge; it does not move this.

⚠ **THE LAST CONJUNCT IS THE ONE THAT COULD GO RED AND THE FIRST TWO ARE ITS SETUP.** A tape entry
that coincided with a published entry would not by itself be a defect — but it is the only observable
this file has of the wiring mistake that already happened once here, when `whSgOld` and
`itemVal T_SGOLD` held one object through two literals and `RC_SGOLD` moved without it. ⚑ `whSgOld`
is GONE — `whSlotSg` reads the record itself — which is why the legs below name the record's slots
rather than a second copy of them. -/
theorem the_wraphack_tape_reads_no_published_statement_entry :
    (List.range WH_PADDED).all (fun p =>
      (whTape (whSlotChals WH_REAL_SLOTS p) (whSlotSg WH_REAL_SLOTS p)).length
        == WH_MLMB * WH_ROUNDS + 2) = true
  ∧ (((List.range WH_PADDED).flatMap (fun p =>
        whTape (whSlotChals WH_REAL_SLOTS p) (whSlotSg WH_REAL_SLOTS p))).filter
      (fun v => Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PUBLIC_IN.contains v)).length
      = 0
  -- ⚑ …and the two record slots really are DIFFERENT tapes, which is the leg that would have caught
  -- the pad reading a real accumulator (`whSlotSgAt`'s index shift) rather than agreeing with itself.
  ∧ whTape (whSlotChals WH_REAL_SLOTS 0) (whSlotSg WH_REAL_SLOTS 0)
      ≠ whTape (whSlotChals WH_REAL_SLOTS 1) (whSlotSg WH_REAL_SLOTS 1) := by
  native_decide

/-- ⚑ **AND THE SIX WORDS ARE INDEPENDENT OF EACH OTHER**, which is what makes the three strata an
ORDER rather than three names for one blockage: stratum 2's derivation reads block-1 words 4, 6, 7,
8, 9, 26 and 11–25 and word 5, and none of those is 27, 28, 37, 54, 55 or 56. Stated as the
arithmetic on the word map so it holds for the layout rather than for one reading of it. -/
theorem the_six_words_are_pairwise_independent_strata :
    ([4, 6, 7, 8, 9, PREV_SHOULD_FINALIZE, FIN_W_DIGEST]
      ++ (List.range WH_ROUNDS).map (fun k => FIN_W_CHAL + k)).all (fun w =>
        let g := finBlockWord FIN_LIVE_BLOCK w
        g != PREV_PER_PROOF_WORDS * FIN_LIVE_BLOCK
        && g != PREV_PER_PROOF_WORDS * FIN_LIVE_BLOCK + 1
        && g != PREV_PER_PROOF_WORDS * FIN_LIVE_BLOCK + 10
        && g != PREV_MSG_NEXT_STEP && g != PREV_MSG_NEXT_STEP + 1
        && g != PREV_MSG_NEXT_STEP + 2) = true
  -- ⚑ …and the three deferred words really are the ones the wire CHECKS, so the list above is the
  -- complement of the subject rather than an unrelated set that happens to miss it.
  ∧ (FIN_W_CIP, FIN_W_B, FIN_W_XI) = (0, 1, 10) := by
  refine ⟨?_, ?_⟩ <;> decide

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
and is why this is 46 and not 47). **61 per instance, 122 at `maxPrevs = 2`** — and
`Max_proofs_verified` is 2 at BOTH committed shapes because `wrap_main.ml:287-289` runs this loop
over `prev_proof_state.unfinalized_proofs`, whose own upstream comment is *"This is padded to
max_proofs_verified for the benefit of wrapping with dummy unfinalized proofs"*. So the wrap-scale
figure is this figure, and it does NOT follow `actual_proofs_verified`.

⚠ **SAY WHICH SHAPE THE CENSUS IS OF.** `finSpRowsW` is `tW = mkWrap shapeSmoke`, so the `122 * 11`
leg did NOT move when the shape field was set to `actual` on 2026-08-07 — `shapeSmoke` kept its 2.
What moved is the WRAP shape, where `finAll` would have run ONE instance against
`wrap_main.ml:287-289`'s `Max_proofs_verified`, and the leg that caught it is
`shapeWrap.maxPrevs = 2` and not the row count. Two legs, two shapes, and reading the row count as
evidence about `shapeWrap` is the misquote the `w12_close` docblock warns about one section over.

Against Mina's `wrap-transaction`: **137 blocks before this rung, 259 of 261 after.** The two that
remain are not this sponge's.

⚠ The Zero count moves with it and that is stated rather than netted: every `(Poseidon × 11, Zero)`
block ends in its own `Zero`, and W-FINSPONGE's own σ-probe rows land after squeezes — so this rung
also grows the `Zero ≥ 2` run family that Mina's wrap does not have at all. Same row economy as the
transcript sponge, not a new one. -/
theorem finsponge_emits_one_hundred_and_twenty_two_poseidon_blocks :
    (finSpRowsW.filter (fun r => r.kind == KGateType.poseidon)).length = 122 * 11
    ∧ shapeSmoke.maxPrevs = 2
    ∧ shapeWrap.maxPrevs = 2
    ∧ 137 + 122 = 259 := by
  native_decide

-- ⚑ The four above are the ONLY compiler-trusted facts in this module and each is pinned at its own
-- site. The general Poseidon block law and the tape lengths are closed by `rfl`/`simp` in the
-- kernel above, which is the split `cip_lift_…` exists to make: a confession that swallows
-- kernel-clean conjuncts loses their pin.
#assert_compiled the_deferred_derivation_does_not_read_the_words_it_checks
#assert_compiled the_wraphack_tape_reads_no_published_statement_entry
/-! ### §20b⁵ — ⚑⚑⚑ **AGREEMENT WITH MINA'S FORTY, AS A SET AND NOT AS A TOTAL.**

`KimchiWrapMainPins10`'s `w12_close` docblock said for a long time that the emitted forty and
`WRAP_PUBLIC_INPUT_MEASURED` "agree at exactly **six** slots — 0–4 and 9, the six taken from that
list by definition". That was true when written and had silently stopped being true: the tape work
made `RC_*` the real step proof's commitments and slot 11 stopped hashing a fixture, and nobody
re-measured. **Measured 2026-08-06 with `EmitWrapFortyAgreement`: it went to thirty-eight
(disagreeing at 11 and 12) and then, when a sibling lane closed slot 11 the same evening, to
THIRTY-NINE — only slot 12 is left. Both numbers were measured hours apart on the same day, which
is precisely why the theorem below is a SET.**

⚠ ⚑ **AND THE THEOREM BELOW IS A SET, NOT THAT TOTAL, ON PURPOSE.** A literal `= 38` is a count that
reds when a lane CLOSES slot 11 — i.e. it punishes exactly the progress it exists to track, and the
lane that closed it would have to edit this file to land. Stating "every slot outside {11, 12}
agrees" is strictly stronger where it matters (any transcript slot drifting reds it) and neutral
where it does not (slot 11 closing does not). The residual `≠` at slot 12 keeps it a refusal shaped
to shrink: close slot 12 and it goes red at the place the claim is made.

⚑ **NEITHER OF THE TWO IS A WRAP-SIDE DERIVATION.** Slot 12 is packed statement word 54, the step
assembly's own outer hash (`dccd4e030`); slot 11's closing wrap-hack digest is the sibling subject of
`…Pins10`. **This commit's change moves neither**, and cannot: `rungPub .close = rungPub .wraphack`
and W-FINSPONGE derives no public word, so no slot of the forty reads the finalize block at all.
The number is recorded here because it is the measurement the ladder is graded on, not because this
rung moved it. -/

/-- ⚑⚑⚑ **THE EMITTED FORTY DISAGREES WITH MINA'S AT SLOT 12 ALONE — 39 OF 40, AT `shapeWrap`.**

Graded the strict way — `emitted[i] == WRAP_PUBLIC_INPUT_MEASURED[i]`, not "does the assembly put a
derivation there". Both sides are about the SAME step proof (`stepmain_step_r8_finalize`): Mina's
side is openmina's `PreparedStatement::to_public_input(40)`, ours is `wrapPublicAt … .close`, so a
disagreement is a measurement and not a preference.

⚠ ⚑ **THE NUMBER IS `shapeWrap`'s AND ONLY `shapeWrap`'s.** The smoke-shape fixtures grade **17 of
40** against the same forty, because a smoke shape derives a fraction of the ladder — quoting that
one as "the agreement" is the misquote `KimchiWrapMainPins10`'s docblock warns about, and the reason
this theorem names `mkWrap shapeWrap` explicitly rather than reading `tW`.

⚑ **IT WAS `≠ 11 && ≠ 12` AND IT IS NOW A FILTER OVER ALL FORTY**, which is strictly stronger: slot
11 was excluded so that a lane closing it would not red this, and it closed (2026-08-06,
`wraphack_closing_sponge_reproduces_minas_slot_eleven`). Leaving the exclusion in would have hidden a
regression at 11 behind a green line about 38.

⚠ ⚑ **WHAT SLOT 12 IS — AND THE NAME THIS THEOREM CARRIED UNTIL 2026-08-08 WAS A REFUTED
DIAGNOSIS.** It was `the_forty_agree_but_for_the_arity_mismatched_slot`, and this paragraph read
*"`messages_for_next_step_proof` is an ARITY mismatch on both sides — segment D hashes 56+20 where
the marshaller's `MessagesForNextStepProof::hash()` hashes 56+36"*. **The arity closed on
2026-08-07** (`marshal::STEP_RECURSION_SLOTS = gates::STEP_RULE_N_PREVIOUS = 1`; `gate_c` reports
`MATCH=true` on every run), and `segd_slot12_probe` reproduces segment D's squeeze **to the digit**
with openmina's own hasher on the same 56+20 preimage — so there is no arity gap and no sponge gap.
The name outlived its own refutation, which is the class this campaign has now paid for twice; it is
renamed to the MEASUREMENT (`… but_for_slot_twelve`) rather than to a new diagnosis, because a name
that carries only what is measured cannot rot.

**What slot 12 actually is**: both sides hash the same seventy-six-cell shape and disagree about what
FILLS it, in two families — `G` (segment D absorbs `solveG`'s solve; the wire carries the wrap
proof's recursion-slot commitment) and the sixteen challenges (segment D's transcript lifts against
`prove_step`'s golden-ratio ladder). `KimchiStepMainPins19` §19b measures why the obvious repair does
not work: block 539508's real `sg`/`z₁`/`z₂` are on disk, and `bpCloses` at them is FALSE, because
this assembly squeezes its own `t`, `u` and `b`.

⚑⚑⚑ **A THIRD FAMILY WAS LIVE ON 2026-08-08 AND IS NOW CLOSED, AND CLOSING IT DID NOT MOVE THIS
COUNT.** `MinaWrapOwnVerifierKey.lean` (56 of the 76 cells) had not been re-installed when the wrap
circuit was re-emitted at `8c3c341d8` — **29 commits** after the module was last written — so
segment D hashed under a superseded key while `gate_c` hashed under the live one, and
`WRAP_PUBLIC_INPUT_MEASURED` below, baked before that re-emit, was stale at exactly the slot under
investigation. ⚠ `segd_slot12_probe` was structurally blind to it: it READS the tracked module, so
it agreed with the stale install by construction. `pickles_kimchi_marshal::installed_gate` reds on
that drift now, and it is what caught this one.

**The install landed and the whole chain was carried** — VK installed, `stepmain_step_r8_finalize`
re-emitted (public entry 64, and only entry 64, moved), the step proof re-proved, the tape fixture
re-installed, this referee re-baked from that run's own `wrap-public-input.json`, `shapeSmoke.xhatXY`
re-derived and all thirty wrap fixtures re-emitted. **The count below is 39 after all of it.** What
moved is the residue's SHAPE, not its size: fifty-eight of slot 12's seventy-six cells now agree (the
56 index coordinates and the 2 app-state words), and the disagreement is confined to **cells 58–75**
— the `[Gx; Gy]` pair and the sixteen challenges, the two families named above. So the stale key was
a real defect and a real referee failure, and it was **not** the thing holding slot 12.

⚑⚑⚑ **RE-MEASURED 2026-08-09 AGAINST A REFEREE THAT MOVED AT 28 OF 40 SLOTS, AND THE ANSWER IS THE
SAME NUMBER FOR A DIFFERENT REASON.** `0047cb876` rewired `runIpa` onto §19d's
`combine_split_commitments` + `endo_inv` fold, which moved `lhs`, hence `G = solveG lhs …`, hence
segment D's squeeze, hence the step statement — so the step proof changed and
`PreparedStatement::to_public_input(40)` with it. `0aa6f7d49` re-baked
`WRAP_PUBLIC_INPUT_MEASURED` from that run and recorded exactly which slots moved: **0–11 and
13–28, twenty-eight of the forty.** ⚠ A count graded before that re-bake is a count about an object
that no longer exists, and `0aa6f7d49` said so in its own message rather than leaving the 39 to be
read forward.

**Re-run at HEAD**, `EmitWrapFortyAgreement` over `mkWrap shapeWrap` at `.close`: **AGREE at 39 of
40, disagreeing at 12 alone** — the same four numbers this theorem asserts. The 39 does not survive
because nothing moved; it survives because **both sides moved together at all 28.** Ours are derived
from the same re-proved step proof Mina's forty were read out of, so a rewire that moves the step
statement moves the emitted transcript and the referee in lockstep. The emitted slot 12 moved
`3396651593… → 1053080512…` exactly as §17(d) requires and Mina's stayed `5075616743…`; the residue
is the same two families and the same size. ⚠ **"58 → 60" is NOT this pass's to quote** — the
seventy-six-cell split is `segd_slot12_probe`'s, and that probe REFUSED on its own freshness assert
when word 54 moved.

⚑ **AND THE ROUTE TO THE SMOKE CONJUNCT WAS BLOCKED, WHICH IS WHY THAT NUMBER IS ALSO RE-RUN.** The
thirty tracked wrap fixtures were not merely stale — they were UNEMITTABLE: `shapeSmoke.xhatXY` is a
literal pair and entry 64 is one of `xhatSel 5`'s five, so the same word-54 move that re-baked this
referee left the memo naming a point the MSM no longer produces.
`xhat_smoke_shape_absorbs_the_msm_output` (`KimchiWrapMainPins05`, a kernel `rfl`) was **red at
HEAD** for exactly that reason, and `EmitWrapMainJson`'s `⚑ xhatXY IS NOT THE MSM'S OUTPUT` refusal
— the fourth time it has caught this memo — is what surfaced it.

⚑⚑ **RE-MEASURED 2026-08-10 ACROSS THE PAD-SLOT FLAG DAY — TWENTY-EIGHT REFEREE SLOTS MOVED AGAIN
AND ALL FOUR NUMBERS ARE UNCHANGED.** `KimchiStepMainCore.stmtDummyVal` now emits
`MinaWrapHackDummySg.DUMMY_WRAP_PRECHALS` into the padding block's fifteen `.bpChallenge` slots
(`KimchiStepStatementPins.the_padding_blocks_fifteen_are_minas_own_dummy_wrap_prechallenges`), which
closed `gates::gate_a2` slot 0 — the wrap proof's pad recursion slot now commits the challenge
polynomial Mina's reader rebuilds from `dummy_ipa_wrap_sg()`, and `PROOF_MARSHAL_RESULT` is GREEN
for the first time with that rung in it. The step statement's entries 16…30 moved, therefore the
step proof, therefore `KimchiStepWrapChainFixture`, all thirty wrap fixtures, and this referee at
slots 0–11 and 13–28.

⚠ **AND SLOT 12 DID NOT MOVE ON EITHER SIDE — WHICH IS WHY 39 SURVIVING IS NOT PROGRESS.** Mina's
stayed `2685766687…` and ours stayed `1053080512…`, because `messages_for_next_step_proof` hashes
the STEP record — the real accumulator, the step-side sixteen, the app state — and the padding block
is nowhere in that preimage. The pad slot and slot 12 were two wounds in one file, not one wound
seen twice; closing the first moves twenty-eight numbers and leaves the twenty-ninth exactly where
it was. Anyone reading "39 of 40" forward across three re-bakes should read that as the residue
being STABLE under everything tried so far, not as it shrinking.

⚑ **THE LAST CONJUNCT IS THE ANTI-VACUITY**, and it is what makes this a fact about VALUES rather
than about a list of zeros: ten of the forty are `Spec.T.Constant` padding and the lookup `Opt` and
are zero on both sides, so an all-zero emission would satisfy the first conjunct at those ten.
Twenty-nine of the agreements are NONZERO. -/
theorem the_forty_agree_but_for_slot_twelve :
    (let em := (wrapPublicAt (mkWrap shapeWrap) .close).map (fun z => (z % (qN : Int)).toNat)
     let mn := Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED
     -- ⚑ WHICH slot disagrees, over ALL forty — a count says a number, this says which.
     ((List.range 40).filter (fun i => em.getD i 0 != mn.getD i 0)) = [12]
     ∧ ((List.range 40).filter (fun i => em.getD i 0 == mn.getD i 0)).length = 39
     -- ⚑ …and slot 12 still disagrees, so this is a refusal shaped to shrink and not a tautology.
     ∧ em.getD 12 0 != mn.getD 12 0
     -- ⚑ ANTI-VACUITY: the agreeing set is not the padding. Ten of the forty are `Spec.T.Constant`
     -- padding and the lookup `Opt` and are zero on both sides; twenty-nine agreements are NONZERO.
     ∧ ((List.range 40).filter (fun i =>
          em.getD i 0 == mn.getD i 0 && em.getD i 0 != 0)).length = 29
     -- ⚠ ⚑ …and the SMOKE shape grades 17, carried here so the two numbers cannot be confused by a
     -- reader who finds only one of them. It is not a worse measurement of the same thing; it is a
     -- measurement of a different, smaller circuit.
     ∧ ((List.range 40).filter (fun i =>
          ((wrapPublicAt tW .close).map (fun z => (z % (qN : Int)).toNat)).getD i 0
            == mn.getD i 0)).length = 17) := by
  native_decide

#assert_compiled the_forty_agree_but_for_slot_twelve

#assert_compiled fin_deferred_words_are_the_derivation
#assert_compiled the_live_block_declares_itself_minas_own_wrap_proof
#assert_compiled the_finalize_evaluations_are_minas_own_wrap_proof
#assert_compiled the_finalize_evaluations_need_no_encoding
#assert_compiled finalize_reproduces_minas_own_ft_eval0
#assert_compiled finsponge_has_a_witness_on_the_published_statement
#assert_compiled finsponge_assert_reds_if_the_other_block_claims_should_finalize
#assert_compiled finsponge_emits_one_hundred_and_twenty_two_poseidon_blocks

end Dregg2.Circuit.Emit.KimchiWrapMain
