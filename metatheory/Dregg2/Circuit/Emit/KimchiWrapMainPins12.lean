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

⚠ **THE ANSWER IS NO, AND IT IS UNDONE WORK — BUT NOT ON THE SIDE THIS PARAGRAPH USED TO NAME.** It
said the step proof had to be re-proved with a statement carrying the wrap's own
`combined_inner_product`, `b` and `xi`, "and that is a FIXPOINT, because those three words are x_hat
MSM entries 32/33, 34/35 and 47, so writing them moves `x_hat`, which moves every challenge below it,
which moves the derivation." §20c below refutes both halves: no transcript challenge reaches this
rung at all, so there is no loop; and those three words are **not free on the step side** — they are
`bpDiv2`/`bpOdd` and `vXiStmt`, the step circuit's OWN `combined_inner_product`, `b` and `xi`, so a
statement carrying the wrap's numbers would make the STEP circuit unsatisfiable rather than this one
satisfiable. What actually disagrees is two derivations of one quantity, one of which runs on
`wrapFixtureQ` evaluation columns where `prev_proof.openings.evals` belongs.
`KimchiWrapMainField.the_published_statement_does_not_carry_the_derived_words` names all six words at
issue; §20c names which of them can move and what the other four are waiting on.

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

/-! ### §20c — ⚑⚑⚑ **THE DEPENDENCY ORDER, AS A DATAFLOW FACT ABOUT THE EMITTED PROGRAM.**

The theorem above says the three deferred words have no witness. The next question is what it costs
to give them one, and until 2026-08-06 this file and `KimchiWrapMainField` both answered **"a
FIXPOINT, because those three words are x_hat MSM entries, so writing them moves `x_hat`, which
moves every challenge below it, which moves the derivation."**

⚠ **THAT ANSWER IS FALSE IN THIS MODEL, AND THE COST OF BELIEVING IT WAS THE REPAIR NOT HAPPENING.**
Its first clause is true — writing the words does move `x_hat` and every transcript challenge below
it, and `KimchiWrapMainCore` §20's own note lists what re-emits. Its second clause does not follow,
and it is the one that priced the repair as unbounded iteration: **no transcript squeeze value reaches
§19 or §20 at all.** The `sp : SpAcc` threaded through `finWireOf`, `finSpWireOf` and `finSpTape`
supplies variable ADDRESSES (`prevW s sp w = .external (basePrev s sp + w)`), never values; §19's own
β and γ are `prevW s sp (finBlockWord p 6)` / `(… p 7)` — PACKED STATEMENT WORDS, not the transcript's
β and γ; and the finalize sponge is a FRESH `runSpongeQ` over `finSpTape`, whose 91 elements are one
statement word, a digest over `whOldChals` (a `wrapFixtureQ`), and evaluation-column fixtures.

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
belongs, making two copies of one object — and it is what actually blocks these three rungs.** The
repair is to wire §19/§20's evaluation inputs to the step proof's own `evals`, not to re-bake a
statement. ⚠ **And the reason that is not a one-line change is a FIELD BOUNDARY, stated rather than
discovered later**: those evaluations are **Fp**, Vesta's scalar field, while this circuit is native
**Fq**, so they enter only through `Other_field` (`impls.ml:167-217`, one Fq wire because `p < q`) —
the encoding `KimchiStepWrapChainFixture`'s own header names as the thing its negative-control items
would need. That encoding is not assembled here. It, and not a fixpoint, is the distance to the top
of the ladder.

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
    `the_published_statement_does_not_carry_the_derived_words` names.
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
`itemVal T_SGOLD` held one object through two literals and `RC_SGOLD` moved without it. -/
theorem the_wraphack_tape_reads_no_published_statement_entry :
    (whTape (whOldChals 0) (whSgOld 0)).length = WH_MLMB * WH_ROUNDS + 2
  ∧ (whTape (whOldChals 1) (whSgOld 1)).length = WH_MLMB * WH_ROUNDS + 2
  ∧ ((whTape (whOldChals 0) (whSgOld 0) ++ whTape (whOldChals 1) (whSgOld 1)).filter
      (fun v => Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PUBLIC_IN.contains v)).length
      = 0 := by
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
#assert_compiled the_deferred_derivation_does_not_read_the_words_it_checks
#assert_compiled the_wraphack_tape_reads_no_published_statement_entry
#assert_compiled fin_deferred_words_are_the_derivation
#assert_compiled finsponge_has_no_witness_on_the_published_statement
#assert_compiled finsponge_assert_reds_if_the_other_block_claims_should_finalize
#assert_compiled finsponge_emits_one_hundred_and_twenty_two_poseidon_blocks

end Dregg2.Circuit.Emit.KimchiWrapMain
