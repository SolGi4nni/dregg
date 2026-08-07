/-
# Dregg2.Circuit.Emit.KimchiWrapMainPins11 — §23b/§24c — W-COMBINE and W-BULLET (carries the one `native_decide`)

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

/-! ### §23b/§24c — ⚑ **W-COMBINE'S AND W-BULLET'S PINS, AS NAMED THEOREMS.**

⚠ **AND WHAT IS *NOT* HERE, SAID FIRST.** The other sub-circuits' pin blocks read facts off the
EMITTED ROW LIST (`xhat_every_ladder_seed_is_pinned`, `ftc_every_ladder_seed_is_pinned`). These two
rungs cannot: `combRows`/`bulletRows` evaluate 34 and 7 thirty-two-block `EndoMul` ladders at the
smoke shape — five `qInv` a block, each a 254-bit modular exponentiation — and reducing that in the
KERNEL is the shape that took this module from 150 s to a 9.6 GB ceiling once before (§7's note on
`circuitEnvAt`). What IS closed in the kernel is the CENSUS and the LAYOUT, which is where the
mistakes that survive a green prove actually live; the row-level facts are established by the
harness's five polarities per rung, and that is a weaker instrument, stated rather than blurred. -/

/-- ⚑ **THE CENSUS THAT CLOSES `wrap-transaction`'s `EndoMul`.** Mina's own compiled `wrap_main`
carries **2528** `EndoMul` gates and this assembly carried **zero** before these two rungs. They are
`32 × (46 + 33)`: W-COMBINE's one ladder per fold step over `Nat.N45.n + Max_proofs_verified.n`
commitments, and W-BULLET's `endo_inv`+`endo` per IPA round plus `Scalar_challenge.endo q c`.
⚑ The last two conjuncts are what makes this a GATE rather than an arithmetic identity: a fold that
started at the FIRST commitment instead of `~init`, or `Tock`'s 15 rounds instead of `Tick`'s 16,
both miss — by one ladder and by two ladders respectively. -/
theorem comb_and_bullet_close_minas_endomul_census :
    combTerms shapeWrap = 47
    ∧ combSteps shapeWrap = 46
    ∧ bullNE shapeWrap = 33
    ∧ ENDO_BLOCKS * (combSteps shapeWrap + bullNE shapeWrap) = 2528
    ∧ ENDO_BLOCKS * (combTerms shapeWrap + bullNE shapeWrap) ≠ 2528
    ∧ ENDO_BLOCKS * (combSteps shapeWrap + (2 * 15 + 1)) ≠ 2528 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ …and the `VarBaseMul` census, which is now a THREE-WAY closure over three sub-circuits.
`wrap-transaction` carries 2417: W-XHAT's 1805, W-FTCOMM's `(tComms + 1) × 51 = 408`, and
W-BULLET's four `scale_fast` at 255 bits. If this rung lands 204 and the total is not 2417, something
else moved — which is exactly what the identity is for. -/
theorem bullet_closes_minas_var_base_mul_census :
    BULL_SF * SF_CHUNKS = 204
    ∧ 1805 + (shapeWrap.tComms + 1) * FTC_CHUNKS + BULL_SF * SF_CHUNKS = 2417
    ∧ SF_CHUNKS = FTC_BITS / BITS_PER_CHUNK
    ∧ 1805 + (shapeWrap.tComms + 1) * FTC_CHUNKS ≠ 2417 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **THE 47 ARE `wrap_verifier.ml:687-706`'s OWN LIST**, position by position — and the fold
runs BACKWARDS down it, so `combIdx` is a decreasing enumeration whose last two entries are the
`sg_old` pair. A fold that ran forwards would have identical gate counts and would put the mux at
the wrong end. -/
theorem comb_fold_runs_backwards_and_ends_on_sg_old :
    combIdx shapeWrap 0 = 45
    ∧ combIdx shapeWrap (combSteps shapeWrap - 1) = 0
    ∧ (List.range (combSteps shapeWrap)).filter (combIsMux shapeWrap)
        = [combSteps shapeWrap - 2, combSteps shapeWrap - 1]
    ∧ ((List.range (combSteps shapeWrap)).map (combIdx shapeWrap)).length = 46 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑⚑ **THE MUX DROPS THE PAD AND KEEPS THE ONE REAL `sg_old`, BECAUSE THE SELECTED RULE HAS ONE
ACCUMULATOR — AND THIS IS THE SITE THAT OWNS MINA'S PUBLIC SLOT 29.**

`first_zero` is `Pseudo.choose (which_branch, step_widths)` (`wrap_main.ml:173-180`): the SELECTED
branch's `actual_proofs_verified`, which for dregg's step rule is `WH_REAL_SLOTS = 1` — one
`verify_one`, `gates::STEP_RULE_N_PREVIOUS`, and `wrap.rs:666` reading that record's own length. So
`Vector.rev (ones_vector ~first_zero:1 2) = [0, 1]`: the PREPENDED pad (`wrap.rs:476-491`) is
dropped and the real accumulator is kept. The same mask is front-extended and packed at
`wrap_main.ml:186-198`, and `Prefix_mask.there N1 = [false; true]` (`proofs_verified.ml:70-78`)
packs `0b10` (`prepared_statement.rs:131-139`) — so `branch_data = 4·domain_log2 + 2`.

⚠ ⚑ **SAY WHAT MOVED AND WHAT IT COSTS.** `mkWrapWith` gave `KEY_CHAIN_BRANCH` the width `min 2 i`
until 2026-08-07, so `fz` was 2, the mask was `[1, 1]`, the pad was FOLDED IN, and slot 29 packed
`N2`. It agreed with `WRAP_PUBLIC_INPUT_MEASURED` — because the referee's own
`pickles_kimchi_marshal` hardcoded `PicklesBaseProofsVerifiedStableV1::N2`. Two wrong sides agreeing
is the exact shape a passing slot can hide in, and this is the only one of the forty where it was
true. Both sides now derive from `STEP_RULE_N_PREVIOUS` and slot 29 is 58.

⚑ **AND `keep` IS STILL A FUNCTION OF THE BRANCH's WIDTH, NOT A CONSTANT** — leg 3 exhibits a
branch whose width is `WH_PADDED`, where the mask really is `[1, 1]` and both `Inner_curve.if_` arms
are live. Restating this theorem as `[0, 1]` and stopping there would have deleted the falsifier and
called it a repair. -/
theorem comb_mux_keep_is_the_branch_selections :
    (List.range MASK_N).map (combKeepVal (mkWrap shapeSmoke)) = [0, 1]
    ∧ (List.range MASK_N).map (combKeepVal (mkWrap shapeWrap)) = [0, 1]
    ∧ (List.range MASK_N).map
        (combKeepVal { sh := shapeWrap, sp := (mkWrap shapeWrap).sp
                     , br := runBranch shapeWrap KEY_REAL_BRANCH
                               ((List.range shapeWrap.branches).map (fun _ => WH_PADDED))
                               ((List.range shapeWrap.branches).map (fun _ => 16)) })
        = [1, 1]
    ∧ (mkWrap shapeWrap).br.fz = WH_REAL_SLOTS
    ∧ (mkWrap shapeSmoke).br.fz = WH_REAL_SLOTS
    -- ⚑ …and that `fz` IS Mina's slot 29, arithmetic and all.
    ∧ (mkWrap shapeWrap).br.packedV
        = 4 * Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_DOMAIN_LOG2 + 2
    ∧ (mkWrap shapeWrap).br.packedV
        = Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED.getD
            WRAP_SLOT_BRANCH_DATA 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **ALL 46 LADDERS' COUNTERS LAND ON ONE CELL.** `Field.Assert.equal !n_acc scalar`
(`scalar_challenge.ml:305`) is emitted as a σ class rather than as a row, which is upstream's shape
and is what makes `xi` a single deferred value rather than 46 independent draws. The second
conjunct is the non-vacuity: the INTERIOR counters are all distinct from it and from each other. -/
theorem comb_all_ladders_share_one_xi :
    ((List.range (combSteps shapeSmoke)).map (fun a =>
        combN shapeSmoke (mkWrap shapeSmoke).sp a ENDO_BLOCKS)).all
      (· == combXiV shapeSmoke (mkWrap shapeSmoke).sp) = true
    ∧ ((List.range (combSteps shapeSmoke)).map (fun a =>
        combN shapeSmoke (mkWrap shapeSmoke).sp a 0)).all
      (· != combXiV shapeSmoke (mkWrap shapeSmoke).sp) = true
    ∧ combXiVal < 2 ^ ENDO_BITS := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑ **THE REGIONS DO NOT OVERLAP.** W-BULLET's cells start above W-COMBINE's last, and the two
together are EXACTLY W-COMBINE's block — `COMB_REGION_CAP` is `nCombVars + nBullVars`, so the block's
last cell is W-BULLET's last, general over every shape and every sponge.

⚠ **AND W-COMBINE'S BASE IS NO LONGER W-FTCOMM'S TOP.** It read `baseFtc + nFtcVars` — W-WRAPHACK's
address and W-FINALIZE's — until 2026-08-05; §17b stacks the three blocks on caps, so the third
conjunct is a strict inequality where an equation used to stand. The `rungsUpto` legs are kept
because they are true and worth citing, but they are no longer what makes the layout sound. -/
theorem comb_and_bullet_regions_are_disjoint (s : WrapShape) (sp : SpAcc) :
    baseBull s sp = baseComb s sp + nCombVars s
    ∧ baseBull s sp + nBullVars s = baseComb s sp + COMB_REGION_CAP s
    ∧ baseFtc shapeSmoke (mkWrap shapeSmoke).sp + nFtcVars shapeSmoke (mkWrap shapeSmoke).sp
        < baseComb shapeSmoke (mkWrap shapeSmoke).sp
    ∧ (rungsUpto .combine).contains .finalize = false
    ∧ (rungsUpto .bullet).contains .finalize = false
    ∧ (rungsUpto .bullet).contains .combine = true := by
  refine ⟨rfl, bullet_is_the_last_cell_of_the_combine_block s sp, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### ⚑ THE THREE-WAY BASE COLLISION — REPAIRED 2026-08-05, AND THE GATE STRENGTHENED WITH IT.

`baseWh` (§21a), `baseFin` (§19e) and `baseComb` (§23a) were **each literally
`baseFtc s sp + nFtcVars s sp`** — three sub-circuits' variable regions at ONE address. §21a's own
docblock conceded it was *"sound TODAY only"*, because `.wraphack`, `.finalize` and `.combine` were
assembled concurrently as SIBLING branches off `.prev` and no `rungsUpto` held two of them. A rung
composing W-WRAPHACK with W-FINALIZE, or W-CLOSE with W-COMBINE, would have aliased two regions:
`placeChecked` sees one variable where two were meant, merges two σ classes that were never meant to
meet, and emits a witness making cells agree that nothing asserted — the class §12 spends its whole
length refusing, in a base address.

⚑ **THE BASES ARE NOW STACKED (§17b)** on three shape-determined CAPS, each with a fail-closed
`EmitWrapMainJson` refusal (`regionEscape`). So the theorem below no longer certifies that no rung
*holds* two colliding regions and leans on that; it says the regions **cannot overlap at all**, for
every shape, every sponge and every cell, whatever any rung holds. The `rungsUpto` legs are KEPT —
they are true, they are still worth citing, and losing them would lose the ladder measurement — but
they have stopped being load-bearing, and that is the whole difference this repair made.

⚠ **WHY A CAP AND NOT THE TRUE SIZE**, since the question will come back: stacking on a region's
actual size needs that size, and W-FINALIZE's is `finStride fa = (fa.getD 0 default).fp.prog.size`
and `finSpSize`, both computed by RUNNING the program builder. Threading them into
`baseComb (s : WrapShape) (sp : SpAcc)` would drag a `finBuild` into every one of `combSlot`'s
reductions and take §23/§24's pins with it. A cap is a constant in the SHAPE, so every base reduces
without the builder — and the emit-time refusal is what keeps the cap honest: if a region ever
exceeds it the emission STOPS rather than silently overlapping. Neither half is optional. -/

/-- ⚑⚑ **NO CELL IS IN TWO OF THE THREE BLOCKS** — for every shape, every sponge and every cell, not
for the pairs someone wrote down and not merely for the rungs that exist today. This is the statement
that replaced *"no rung HOLDS two colliding regions"*: that one was true of the ladder and said
nothing about a rung not yet written, and the three regions really did share an address underneath
it.

The legs, in order: `ALL_RUNGS` is the whole type, so the bounded ∀ cannot go quietly weaker when a
constructor is added; no rung's `rungsUpto` holds two block owners (kept, no longer load-bearing);
the two stackings hold **by `rfl`**, so the blocks are the caps and not a coincidence of two shapes;
and then the three pairwise disjointness facts, which follow from those by arithmetic alone.

⚠ `.wraphack` is covered here, which the instance-pin this replaced never was — it named
`.combine`/`.finalize`, `.bullet`/`.finalize` and `.bullet`/`.combine` and said nothing at all about
W-WRAPHACK's region, the very one whose docblock carried the concession. -/
theorem no_rung_holds_two_colliding_regions (s : WrapShape) (sp : SpAcc) (x : Nat) :
    ALL_RUNGS.length = 15
    -- ⚑ **THE `≤ 1` CONJUNCT IS GONE, 2026-08-05, AND ITS RETIREMENT IS THE POINT.** It counted
    -- block owners per rung and was already marked "kept, no longer load-bearing"; then `w12_close`
    -- legitimately acquired two (`.wraphack` and `.combine`, because `.bullet` is under `.close`)
    -- and the count would have REFUSED it. A check that has stopped being load-bearing and starts
    -- refusing correct designs is worse than one that is absent. What replaced it is `rungRegions`
    -- DECLARING each block a rung may allocate in, plus the disjointness below — so two blocks in
    -- one rung are safe and an UNDECLARED block is still a refusal.
    ∧ (∀ k ∈ ALL_RUNGS,
        (rungRegions s sp k).length ≤ COLLIDING_REGION_OWNERS.length)
    ∧ baseFin s sp = baseWh s sp + WH_REGION_CAP s
    ∧ baseComb s sp = baseFin s sp + FIN_REGION_CAP s
    ∧ ¬(inBlock (baseWh s sp) (WH_REGION_CAP s) x ∧ inBlock (baseFin s sp) (FIN_REGION_CAP s) x)
    ∧ ¬(inBlock (baseFin s sp) (FIN_REGION_CAP s) x ∧ inBlock (baseComb s sp) (COMB_REGION_CAP s) x)
    ∧ ¬(inBlock (baseWh s sp) (WH_REGION_CAP s) x ∧ inBlock (baseComb s sp) (COMB_REGION_CAP s) x) := by
  refine ⟨by decide, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · intro k _
    cases k <;> simp [rungRegions, COLLIDING_REGION_OWNERS]
  all_goals simp only [inBlock, baseComb, baseFin]
  all_goals omega

/-- ⚑⚑ **THE LIST FORM IS THE SINGLE-BLOCK FORM WHEREVER THERE IS ONE BLOCK**, so nothing below
`w12_close` changed meaning when `rungRegion` became `rungRegions`. General over the wall, the block
and the gates — not an instance — because that is what makes it a statement about the GENERALIZATION
rather than about the two rungs someone checked. -/
theorem region_escape_list_is_the_single_block_one (wall b n : Nat) (gs : List PGate) :
    regionEscapeInAny wall [(b, n)] gs = regionEscapeIn wall b n gs := by
  simp [regionEscapeInAny, regionEscapeIn, List.any]

/-- ⚑ **AND `w12_close` IS THE RUNG THAT NEEDED IT**: it holds two block owners, declares two blocks,
and every other rung declares at most one. The middle conjunct is what a `rungRegions` that forgot
W-COMBINE would falsify — and forgetting it is exactly the failure the old single-block form made
unavoidable. -/
theorem close_declares_both_of_its_blocks (s : WrapShape) (sp : SpAcc) :
    ((rungsUpto .close).filter (fun r => COLLIDING_REGION_OWNERS.contains r)).length = 2
    ∧ rungRegions s sp .close
        = [(baseWh s sp, WH_REGION_CAP s), (baseComb s sp, COMB_REGION_CAP s)]
    ∧ ((ALL_RUNGS.filter (fun k => (rungRegions s sp k).length > 1))) = [Rung.close] := by
  refine ⟨by decide, rfl, ?_⟩
  simp [ALL_RUNGS, rungRegions]

/-- ⚑⚑ **RED CONTROL FOR THE DISJOINTNESS ITSELF, AND IT IS THE LAYOUT THIS REPAIR DELETED.** Take
the same three caps and re-stack them the way `baseWh`, `baseFin` and `baseComb` were written until
2026-08-05 — all three at ONE address — and EVERY such address is in all three blocks at once. So
`no_rung_holds_two_colliding_regions` above measures where the bases ARE; it is not an arithmetic
tautology about `inBlock`, and it goes red the moment any of the three is re-based onto another's
address.

⚠ The three cap values are stated here rather than as a pin of their own, because a constant against
its own definition is decoration: what they are doing in THIS theorem is carrying the non-vacuity —
a zero-width block would make the sharing claim empty, and 346 / 6694 / 5145 are why it is not. -/
theorem stacking_the_three_bases_at_one_address_shares_a_cell (b : Nat) :
    WH_REGION_CAP shapeSmoke = 346
    ∧ FIN_REGION_CAP shapeSmoke = 6694
    ∧ COMB_REGION_CAP shapeSmoke = 5145
    ∧ inBlock b (WH_REGION_CAP shapeSmoke) b
    ∧ inBlock b (FIN_REGION_CAP shapeSmoke) b
    ∧ inBlock b (COMB_REGION_CAP shapeSmoke) b := by
  have hw : WH_REGION_CAP shapeSmoke = 346 := by decide
  have hf : FIN_REGION_CAP shapeSmoke = 6694 := by decide
  have hc : COMB_REGION_CAP shapeSmoke = 5145 := by decide
  refine ⟨hw, hf, hc, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

/-- ⚑⚑ **AND THE EMIT REFUSAL ITSELF BITES — ON THE REAL EMITTED GATES, IN THE KERNEL.** The caps
above are only honest because `EmitWrapMainJson` STOPS when a region escapes one; a refusal nothing
has been shown to fire is a comment. So: `regionEscape` returns `none` on W-WRAPHACK's own gates at
its own block (the healthy case), `some` when the SAME gates are checked against a zero-width block
(the cap-outgrown direction), and `some` when they are checked against W-COMBINE's block instead of
their own (the reached-into-a-sibling direction, which a max-index check cannot see).

⚠ Only the LAST of those three is the one this whole layout exists to refuse, and it is the one an
"is anything above the ceiling?" check would have missed — W-WRAPHACK's cells are *below* every
address of W-COMBINE's block, so the escape is DOWNWARD. -/
theorem region_escape_bites_on_the_emitted_gates :
    regionEscape shapeSmoke tWh.sp .wraphack (wrapGates (whRows tWh true)) = none
    ∧ regionEscapeIn (baseWh shapeSmoke tWh.sp) (baseWh shapeSmoke tWh.sp) 0
        (wrapGates (whRows tWh true)) ≠ none
    ∧ regionEscapeIn (baseWh shapeSmoke tWh.sp) (baseComb shapeSmoke tWh.sp)
        (COMB_REGION_CAP shapeSmoke) (wrapGates (whRows tWh true)) ≠ none := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑ **WHAT THE KERNEL CLOSES ABOUT THE CAPS, AND WHAT IT CANNOT — SAID AS ONE STATEMENT.** Two of
the three caps are EXACT and their blocks' last cells are named here (`close_is_the_last_cell_…`,
`bullet_is_the_last_cell_…`, both general over shape and sponge). W-FINALIZE's is the one with
headroom, and its ceiling is `finProgBase` — pure shape arithmetic — plus `maxPrevs` copies of
`FIN_PROG_CAP + FINSP_BLOCK_CAP`.

⚠ **THE FIT OF THOSE TWO IS NOT CLOSED HERE AND CANNOT BE**, and that is not a hedge: reading
`finStride` or `finSpSize` in the kernel means whnf-ing an `Array FOp` a `StateM` builder produced,
and an `Array` in `whnf` is its `List` model — `.size` alone fails at 1 000 000 heartbeats. It is
`EmitWrapMainJson`'s `regionEscape` refusal that discharges it, at every emission, off the emitted
GATES. So: the kernel closes the layout ARITHMETIC and the two exact caps; the finalize block's fit
is an emit-time obligation with a fail-closed refusal, and it is one or the other, never blurred. -/
theorem the_caps_are_the_blocks (s : WrapShape) (sp : SpAcc) :
    baseClose s sp + 1 = baseWh s sp + WH_REGION_CAP s
    ∧ baseBull s sp + nBullVars s = baseComb s sp + COMB_REGION_CAP s
    ∧ baseFin s sp + FIN_REGION_CAP s
        = finProgBase s sp + s.maxPrevs * (FIN_PROG_CAP + FINSP_BLOCK_CAP) :=
  ⟨close_is_the_last_cell_of_the_wraphack_block s sp
  , bullet_is_the_last_cell_of_the_combine_block s sp
  , fin_block_ceiling_is_finProgBase_plus_the_two_caps s sp⟩

/-- ⚑ **THE COMMITMENTS THE FOLD READS ARE THE TRANSCRIPT'S OWN CELLS**, position by position —
`sg_old`, `x_hat`, `ft_comm`, `z_comm` and `w_comm` at `wrap_verifier.ml:687-706`'s offsets. This is
what "W-COMBINE consumes them" MEANS, and it is why §2c's entries can be rewritten: bend any one of
those words and 46 ladders' gate polynomials move.

⚠ ⚑ **AND IT IS PINNED ON THE VARIABLES, NOT ON THE PROSE.** The first draft of this theorem was a
`decide` over `String.startsWith` on `WRAP_UNCONSUMED`'s sentences. It did not go FALSE when another
lane reworded an entry — it went STUCK, because `String.startsWith` does not kernel-reduce, and
"stuck" reads like a build error rather than a broken claim. A census entry is prose three lanes
edit; a variable identity is not. ⚠ Three of those entries still read "needs W-COMBINE" for exactly
that reason — five pins in the W-WRAPHACK and W-FINALIZE blocks quote them verbatim, so rewording
them is a coordinated edit and not this rung's to make alone. -/
theorem comb_reads_the_transcripts_own_commitment_cells :
    -- ⚑ the fold's `sg_old` prefix is `Max_proofs_verified` long, so its REAL entry is at
    -- `whNPad`, and that one IS the transcript's own cell. (Slot 0 is the pad, whose cell is
    -- W-PREV's `prevPadSg` and which the tape never absorbs — `sgOldVar`.)
    (combPtVar (mkWrap shapeSmoke) (whNPad WH_REAL_SLOTS)).1
      = (((mkWrap shapeSmoke).sp.evs.filter (fun e => e.isAbs && e.tag == T_SGOLD)).getD 0
          default).wordV
    ∧ (combPtVar (mkWrap shapeSmoke) 0).1
      = prevPadSg shapeSmoke (mkWrap shapeSmoke).sp 0 0
    ∧ (combPtVar (mkWrap shapeSmoke) shapeSmoke.maxPrevs).1
      = (((mkWrap shapeSmoke).sp.evs.filter (fun e => e.isAbs && e.tag == T_XHAT)).getD 0
          default).wordV
    ∧ combPtVar (mkWrap shapeSmoke) (shapeSmoke.maxPrevs + 1)
      = ftcOutV shapeSmoke (mkWrap shapeSmoke).sp
    ∧ (combPtVar (mkWrap shapeSmoke) (shapeSmoke.maxPrevs + 2)).1
      = (((mkWrap shapeSmoke).sp.evs.filter (fun e => e.isAbs && e.tag == T_ZCOMM)).getD 0
          default).wordV
    ∧ (combPtVar (mkWrap shapeSmoke) (shapeSmoke.maxPrevs + 3 + KEY_SINGLES)).1
      = (((mkWrap shapeSmoke).sp.evs.filter (fun e => e.isAbs && e.tag == T_WCOMM)).getD 0
          default).wordV := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ **`lr` AND `delta` ARE ON THE CURVE NOW, AND THE OLD FILLER WAS NOT.** This is the flag day
§2d's `itemVal` carries, exhibited rather than described: the `wrapFixture` values that stood there
are not points, so `Scalar_challenge.endo_inv` had no witness over them at all. -/
theorem wrap_lr_and_delta_are_curve_points :
    onCurveQ (itemVal T_LR 0, itemVal T_LR 1) = true
    ∧ onCurveQ (itemVal T_LR 2, itemVal T_LR 3) = true
    ∧ onCurveQ (itemVal T_DELTA 0, itemVal T_DELTA 1) = true
    ∧ onCurveQ (wrapFixture T_LR 0, wrapFixture T_LR 1) = false
    ∧ onCurveQ (wrapFixture T_DELTA 0, wrapFixture T_DELTA 1) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **W-BULLET's LAYOUT IS ITS SOURCE'S SHAPE.** Four `scale_fast` (`uc`, `b_u`, `z₁·(G+b_u)`,
`z₂·H`), `2·ipaRounds + 1` endo ladders, and `3·ipaRounds + 2` points through `Inner_curve.typ`
(the `2·ipaRounds` `lr`, `delta`, the `ipaRounds` `endo_inv` witnesses, and
`challenge_polynomial_commitment`). ⚑ **The last one was `3·ipaRounds + 1` until 2026-08-04**: `G`
was the one point `Openings.Bulletproof.typ` checks that this rung did not, because at the degenerate
step key the honest witness for it was off-curve. §14's key closed that. -/
theorem bullet_layout_is_check_bulletproofs_shape :
    BULL_SF = 4
    ∧ bullNE shapeWrap = 2 * shapeWrap.ipaRounds + 1
    ∧ bullOCPts shapeWrap = 3 * shapeWrap.ipaRounds + 2
    ∧ shapeWrap.ipaRounds = 16
    ∧ EN_STRIDE = 3 + 2 * (ENDO_BLOCKS + 1) + ENDO_BLOCKS
    ∧ SF_STRIDE = 2 * (SF_CHUNKS + 1) + SF_CHUNKS := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑⚑ **THE CLOSING FACT, AND THE ONE THIS RUNG EXISTED WITHOUT FOR A DAY.** At Mina's
`step-transaction` key: W-COMBINE's fold output is ON VESTA, so `lhs` is, so the prover's solve for
`challenge_polynomial_commitment` lands on Vesta too — and `equal_g lhs rhs` computes **1**. Every
leg is read off the same `bullData` the emitted witness is built from, so this cannot drift into
being about a second spelling of the assembly.

⚠ The last two legs are the REFUTATION side of the new `assert_on_curve`: a `G` bent by one in either
coordinate is off the curve, so `cOnCurveQ`'s row has no satisfying assignment there. A check that
could only ever pass would be decoration. -/
theorem bullet_solves_g_on_curve_and_equal_g_is_one :
    onCurveQ (bullData (mkWrap shapeSmoke)).combOut = true
    ∧ onCurveQ (bullData (mkWrap shapeSmoke)).lhs = true
    ∧ onCurveQ (bullData (mkWrap shapeSmoke)).g = true
    ∧ bullOcVal (mkWrap shapeSmoke) (bullData (mkWrap shapeSmoke))
        (3 * shapeSmoke.ipaRounds + 1) = (bullData (mkWrap shapeSmoke)).g
    ∧ (bullData (mkWrap shapeSmoke)).lhs = (bullData (mkWrap shapeSmoke)).rhs
    ∧ onCurveQ (qAdd (bullData (mkWrap shapeSmoke)).g.1 1, (bullData (mkWrap shapeSmoke)).g.2)
        = false
    ∧ onCurveQ ((bullData (mkWrap shapeSmoke)).g.1, qAdd (bullData (mkWrap shapeSmoke)).g.2 1)
        = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ⚑ **AND IT IS THE ONE COMPILER-TRUSTED FACT IN THIS FILE, SAID OUT LOUD.** Closing the theorem
above in the kernel means whnf-ing `bullData` — 34 W-COMBINE ladders, 33 endo ladders and four
`scale_fast` at 51 chunks — and it times out at 4 000 000 heartbeats. `#assert_compiled` is the pin
for exactly that class (`Dregg2/Tactics.lean` §): it passes only if every axiom is kernel-clean or a
`native_decide` oracle AND at least one oracle is present, so the compiler-trust is recorded rather
than hidden. ⚠ A `#guard` here would have been the SAME compiled evaluation with the name, the term
and the axiom record deleted. -/
#assert_compiled bullet_solves_g_on_curve_and_equal_g_is_one

end Dregg2.Circuit.Emit.KimchiWrapMain
