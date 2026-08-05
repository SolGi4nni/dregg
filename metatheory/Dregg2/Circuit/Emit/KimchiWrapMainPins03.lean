/-
# Dregg2.Circuit.Emit.KimchiWrapMainPins03 — the smoke-instance pins (§12b ladder · §12c–§12e defect classes · §12f rate-2 · §12g/h census)

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

/-! ### §12b — the rungs are a LADDER and every row-set is REACHED.

The step side measured a sub-circuit whose row emitter was absent from `rungRows` while every probe
still passed — the rows the commit subject named were in NO proved circuit. These pin each rung's
length as the sum of its own sub-lists, so a dropped row-set is a red. -/

#guard (rungRows tW .transcript true).length
       == (transcriptRowsQ (baseSp shapeSmoke) tW.sp true).length
#guard (rungRows tW .challenges true).length
       == (rungRows tW .transcript true).length + (challengeRowsQ tW true).length
#guard (rungRows tW .branch true).length
       == (rungRows tW .challenges true).length
          + (branchRows shapeSmoke (baseBr shapeSmoke tW.sp) tW.br true).length
#guard (rungRows tW .bind true).length
       == (rungRows tW .branch true).length + (closingRows tW).length
-- Strictly monotone: every rung really adds rows.
#guard (rungRows tW .transcript true).length < (rungRows tW .challenges true).length
#guard (rungRows tW .challenges true).length < (rungRows tW .branch true).length
#guard (rungRows tW .branch true).length < (rungRows tW .bind true).length

/-! The WIRED and UNWIRED circuits differ ONLY in the probe rows' permutation columns — the control
that turns "rejected" into "rejected BY THE WIRE". -/
#guard rowsW.length == rowsUW.length
#guard (rowsW.zip rowsUW).all (fun p => p.1.kind == p.2.kind && p.1.coeffs == p.2.coeffs)
#guard (rowsW.zip rowsUW).all (fun p => p.1.probe == p.2.probe)
#guard ((rowsW.zip rowsUW).filter (fun p => p.1.perm != p.2.perm)).length
       == (rowsW.filter (fun r => r.probe)).length
#guard (rowsW.filter (fun r => r.probe)).length > 0

/-! The placement is ACCEPTED — no `auxOverlapsPublic`, no `referenceInGap`, no `inertPublicWord`.
⚑ That last one is the real gate: a wrap statement word no gate reads REFUSES here rather than
sitting inert in the public vector. -/
#guard refusalOf shapeSmoke shapeSmoke.pubWords gatesW == none
#guard placedW.length == shapeSmoke.pubWords + nRowsW
#guard inertPublicWords shapeSmoke.pubWords gatesW == []

/-! The witness grid is 15 columns of `pubWords + nRows`. -/
#guard gridW.length == 15
#guard (gridW.getD 0 []).length == shapeSmoke.pubWords + nRowsW

/-! ### §12c — DEFECT CLASS 1/6: the `EndoMulScalar` SEEDS are PINNED.

`scalar_challenge.ml:63-66` seeds `n₀ = 0, a₀ = 2, b₀ = 2`. Leaving any of the three a free witness
lets a prover choose the decoded scalar while the chain still closes — the same shape as the step
side's free `acc₀`/`n₀` (`plonk_curve_ops.ml:157-158`). All three are pinned by `Generic` rows
(`tfcRowsQ`'s first two), and this exhibits what a free seed would buy. -/

#guard seedBentN != seedHonestN
#guard seedRow0 == cConst 0 ++ cConst 2
#guard seedRow1 == cConst 2 ++ cNil

/-! ### §12d — DEFECT CLASS 2: BOTH halves of `lowest_128_bits` are range-checked.

`util.ml:88-101` witnesses `(lo, hi)`, then `assert_128_bits hi` UNCONDITIONALLY (`:98`) and
`assert_128_bits lo` only when `~constrain_low_bits` (`:99`), and closes with
`Field.Assert.equal x Field.(lo + scale hi (pow2 128))`. With only the LOW half constrained that
last line is one equation in two unknowns: for any `lo' < 2¹²⁸` a prover solves
`hi' = (x − lo')·2^{−128}` and the Fiat–Shamir challenge is his. The forged `hi'` is generically
≥ 2¹²⁸, so its OWN `to_field_checked` chain cannot reconstruct it — which is why `:98` is
unconditional, and why this file emits a SECOND chain per challenge. -/

/-! The honest split satisfies the decomposition row, stated on this assembly's own squeeze. -/
#guard qAdd loHonest (qMul hiHonest (2 ^ CHAL_BITS shapeSmoke)) == sqSample % qN
#guard loForged != loHonest
/-! ⚑ …and the HIGH chain refuses it: `emsAccsQ` reconstructs only `chalBits` bits, so a chain over
a value ≥ 2^chalBits cannot close its `Field.Assert.equal n scalar` tie. Exhibited on the honest
`hi` (which IS below the bound, so the chain closes) and on a forged one that is not. -/
#guard seedHonestN == 12345 % 2 ^ CHAL_BITS shapeSmoke
#guard ((emsAccsQ shapeSmoke (2 ^ CHAL_BITS shapeSmoke + 7)).getD shapeSmoke.emsRows (0, 2, 2)).1
       != 2 ^ CHAL_BITS shapeSmoke + 7
/-! The high chain IS emitted, one per challenge — `2 · nChals` chains of `emsRows` rows. -/
#guard (rowsW.filter (fun r => r.kind == KGateType.endoMulScalar)).length
       == 2 * nChals shapeSmoke * shapeSmoke.emsRows

/-! ### §12e — DEFECT CLASS 3: the UNCONSUMED census is REPORTED, not padded.

Every absorbed item is a variable and the sponge's own absorb row reads it; NONE is yet read by a
consumer, because W-XHAT / W-COMBINE / W-BULLET are not assembled. This pins the count, so
"closing" an item by wiring it to a gadget that merely re-reads it would not move the number. -/
#guard WRAP_UNCONSUMED.length == 8
#guard (tW.sp.evs.filter (fun e => e.isAbs)).length == nItems shapeSmoke
#guard ((chalSqueezes tBent.sp).getD 0 (.external 0, 0)).2
       != ((chalSqueezes tW.sp).getD 0 (.external 0, 0)).2
#guard ((chalSqueezes tBent.sp).getD 3 (.external 0, 0)).2
       != ((chalSqueezes tW.sp).getD 3 (.external 0, 0)).2

/-! ### §12f — ⚑ the RATE-2 STATE MACHINE, and what a block model gets wrong.

`poseidon.rs:107-146` (transcribed in `PastaPoseidonFq.absorb1`/`squeeze1`): β and γ come out of ONE
permutation — γ reads lane 1 with no permutation — and the `z_comm` absorbed right after them
re-enters at lane 0 without one. A one-permutation-per-squeeze model, which is what the step side's
R1 runs, would emit two extra permutations here and would make γ a function of a state upstream
never reaches. §12a is the measurement that this file does not. -/

#guard (sqEvts.getD 0 default).didPerm == true
#guard (sqEvts.getD 1 default).didPerm == false
#guard (sqEvts.getD 0 default).lane == 0
#guard (sqEvts.getD 1 default).lane == 1
/-! …and they are read out of the SAME state triple, which is what "one permutation" means. -/
#guard (sqEvts.getD 0 default).midN == (sqEvts.getD 1 default).midN

/-! ⚑ THE FORK. `sponge_before_evaluations = Sponge.copy sponge` (`wrap_verifier.ml:645`) is taken
BEFORE `sponge_digest_before_evaluations = Sponge.squeeze_field sponge` (`:646`), so the digest
squeeze does NOT advance the transcript: the state it carries forward is the one it entered with. -/
#guard (tW.sp.evs.filter (fun e => !e.isAbs && e.kind == SqKind.fork)).length == 1
#guard forkEvt.outN == forkEvt.inN
/-! …and it still COSTS its permutation, so the digest is a real squeeze and not a relabelled cell. -/
#guard forkEvt.didPerm == false
#guard forkEvt.val != 0

/-! ### §12g — the gate census.

The `wrap-transaction` blob's own histogram is
`Generic 3521 · Poseidon 2871 · Zero 2757 · EndoMul 2528 · VarBaseMul 2417 · EndoMulScalar 536 ·
CompleteAdd 492` (`mina-canonical-circuit-oracle.mjs --circuit wrap-transaction`), 15,122 gates at
PI 40. This assembly emits FOUR of those seven families; the three it does not are W-XHAT /
W-FTCOMM / W-COMBINE / W-BULLET's curve gadgets, named in §13. Saying so here is the point. -/

/-- ⚑ **THE `w4_bind` RUNG EMITS NO CURVE GATE, AND ITS TWO STRUCTURED FAMILIES RUN IN WHOLE
BLOCKS.** Poseidon rows come in 11-row permutations — the run-length family the conformance diff
compares — and `EndoMulScalar` in 8-row chains; a partial block would mean a permutation or a
`to_field_checked` chain was emitted half-open. ⚠ The curve families are zero HERE and non-zero from
`w6_xhat` up (`xhat_gate_census`, `ftc_gate_census`); this is the closing rung's census, not the
file's. -/
theorem bind_rung_gate_census :
    (rowsW.filter (fun r => r.kind == KGateType.varBaseMul)).length = 0
    ∧ (rowsW.filter (fun r => r.kind == KGateType.endoMul)).length = 0
    ∧ (rowsW.filter (fun r => r.kind == KGateType.completeAdd)).length = 0
    ∧ (rowsW.filter (fun r => r.kind == KGateType.poseidon)).length % 11 = 0
    ∧ (rowsW.filter (fun r => r.kind == KGateType.endoMulScalar)).length % 8 = 0 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### §12h — the emitted circuit is well-formed for the harness. -/

/-- ⚑ Every placed gate carries exactly `K_PERMUTS` wires, every witness column is as long as the
public words plus the rows, and every gate's `typ` ordinal is one of the seven kimchi kinds the
harness can deserialise. A violation of any of these is a JSON the Rust prover would reject at parse
time rather than a circuit it would refuse — which is why it is checked here and not there. -/
theorem bind_rung_is_well_formed_for_the_harness :
    placedW.all (fun g => g.wires.length == K_PERMUTS) = true
    ∧ gridW.all (fun col => col.length == shapeSmoke.pubWords + nRowsW) = true
    ∧ placedW.all (fun g => g.kind.ordinal < 7) = true := by
  refine ⟨rfl, rfl, rfl⟩

/-! ### §12i — ⚑ **`t_comm` IS THE ONE ABSORBED FAMILY WITH NO READER, AND IT SAYS SO IN A THEOREM.**

`WRAP_UNCONSUMED` carries eight entries and seven of them now name a rung that consumes the family.
`t_comm`'s entry says *"`ft_comm` EMITTED at `w8_ftcomm` (§17); its OUTPUT is W-COMBINE/W-BULLET's"*
— which is true and is not the same claim. §17 witnesses `t_comm` FRESH (`wrap_main.ml:387-396` →
`Plonk_types.Messages.typ`) and folds THOSE cells into `ft_comm`; the SEVEN chunks the transcript
absorbed at `wrap_verifier.ml:630` are read by the sponge and then by nothing at all.

⚠ **A CENSUS ENTRY IS PROSE AND CANNOT GO RED.** Three lanes edit `WRAP_UNCONSUMED`'s sentences, and
the last attempt to pin one used `String.startsWith`, which does not kernel-reduce — it went STUCK,
not false. So the fact is stated where it can be measured: over the CELLS, quantified over the whole
ladder. A rung that starts reading a `t_comm` transcript cell — which is what "a consumer landed"
MEANS — makes the second conjunct false and this file red, and whoever lands it strikes the census
entry at the same time.

⚑ The `.transcript` conjunct is the RED CONTROL and the reason the rest is a measurement rather than
a vacuous truth about an empty list: `.transcript` DOES read every one of them.

⚠ **THE SUBJECT IS W-COMBINE'S FOLD ARGUMENT, NOT "EVERY RUNG'S ROWS", AND THAT IS A CHOICE WITH A
MEASUREMENT BEHIND IT.** The first draft quantified `tCommReadsIn` over `ALL_RUNGS`; it does not
close — `(deterministic) timeout at whnf, 4000000 heartbeats`, because `rungOwn … .bullet` builds 33
endo ladders and `.combine` 46 in the kernel. `combPtVar` is the right subject anyway and does close:
it IS the list of transcript cells `Split_commitments.combine` folds over, the same object
`comb_reads_the_transcripts_own_commitment_cells` pins position by position. A consumer landing for
`t_comm` means a `combPtVar` index resolving to one of these cells, and that is exactly what goes
red. `.ftcomm` is pinned directly because §17 is the rung whose census entry names `t_comm`, and it
witnesses `t_comm` FRESH rather than reading the absorbed chunks. -/
theorem t_comm_is_absorbed_and_read_by_nothing_but_the_sponge :
    (tCommCells tW).length = 2 * shapeSmoke.tComms
    ∧ tCommReadsIn tW .transcript = 2 * shapeSmoke.tComms
    ∧ tCommReadsIn tW .ftcomm = 0
    ∧ (∀ k ∈ List.range (combTerms shapeSmoke),
        ((tCommCells tW).contains (combPtVar tW k).1
         || (tCommCells tW).contains (combPtVar tW k).2) = false)
    ∧ WRAP_UNCONSUMED_KEYS.getD 4 "" = "t_comm" := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Dregg2.Circuit.Emit.KimchiWrapMain
