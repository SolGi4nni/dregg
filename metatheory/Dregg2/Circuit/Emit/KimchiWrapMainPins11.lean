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

/-- ⚑ **BOTH ARMS OF `Inner_curve.if_` ARE LIVE IN THE HONEST WITNESS.** `mkWrapWith` witnesses
branch 1 at widths `[0,1,2,…]`, so `first_zero = 1` and `Vector.rev (ones_vector ~first_zero:1 2)`
is `[0, 1]` — one `sg_old` kept and one dropped. A `keep` that were constant would make the mux
dead weight and the rung's own distinguishing feature untested. -/
theorem comb_mux_takes_both_branches :
    (List.range MASK_N).map (combKeepVal (mkWrap shapeSmoke)) = [0, 1]
    ∧ (List.range MASK_N).map (combKeepVal (mkWrap shapeWrap)) = [0, 1] := by
  refine ⟨?_, ?_⟩ <;> decide

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

/-- ⚑ **THE REGIONS DO NOT OVERLAP.** W-COMBINE's cells start above W-FTCOMM's last and W-BULLET's
above W-COMBINE's last, at both shapes. ⚠ W-COMBINE's base is `baseFin`'s — see §23a: `.combine` and
`.finalize` are sibling branches off `.prev` and no `rungsUpto` contains both, so no emitted circuit
holds cells from both regions. This is the pin that would go red if that stopped being true and one
rung started emitting both. -/
theorem comb_and_bullet_regions_are_disjoint :
    baseComb shapeSmoke (mkWrap shapeSmoke).sp
      = baseFtc shapeSmoke (mkWrap shapeSmoke).sp + nFtcVars shapeSmoke (mkWrap shapeSmoke).sp
    ∧ baseBull shapeSmoke (mkWrap shapeSmoke).sp
      = baseComb shapeSmoke (mkWrap shapeSmoke).sp + nCombVars shapeSmoke
    ∧ (rungsUpto .combine).contains .finalize = false
    ∧ (rungsUpto .bullet).contains .finalize = false
    ∧ (rungsUpto .bullet).contains .combine = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### ⚑ THE THREE-WAY BASE COLLISION, AS A GATE OVER EVERY RUNG RATHER THAN THREE INSTANCES.

`baseWh` (§21a), `baseFin` (§19e) and `baseComb` (§23a) are **each literally
`baseFtc s sp + nFtcVars s sp`** — three sub-circuits' variable regions at ONE address. §21a's own
docblock concedes it is *"sound TODAY only"*, because `.wraphack`, `.finalize` and `.combine` were
assembled concurrently as SIBLING branches off `.prev` and no `rungsUpto` holds two of them.

⚠ **AND `comb_and_bullet_regions_are_disjoint` ABOVE DOES NOT COVER IT.** It names three specific
pairs — `.combine`/`.finalize`, `.bullet`/`.finalize`, `.bullet`/`.combine` — and says nothing at all
about `.wraphack`. A rung composing W-WRAPHACK with W-FINALIZE, or W-CLOSE with W-COMBINE, aliases
two regions and passes every pin in this file. `placeChecked` would see one variable where two were
meant, merge two σ classes that were never meant to meet, and emit a witness making cells agree that
nothing asserted — the class §12 spends its whole length refusing, in a base address.

⚑ So the pin is the GENERAL fact over the whole ladder, not an instance of it. It goes red the
moment a composed rung lands, which is exactly when the aliasing becomes real, and it is the thing
whichever lane closes the ladder has to satisfy.

⚠ **THIS IS A DETECTOR, NOT THE REPAIR.** The repair is disjoint bases, and it is not a one-liner
for a measured reason: stacking `baseComb` above the finalize region needs that region's SIZE, and
`finStride fa = (fa.getD 0 default).fp.prog.size` / `finSpSize` are computed by running the program
builder. Threading them into `baseComb (s : WrapShape) (sp : SpAcc)` would drag a `finBuild` into
every one of `combSlot`'s reductions and take the §23/§24 pins with it. The shape that works is the
one this file already uses twice — a shape-determined CAP per region (`WrapShape.xhatXY`,
`FIN_DEFERRED_*`), with the obligation discharged by a kernel `rfl` AND an `EmitWrapMainJson`
refusal. That moves `w10_finalize`, `w11_finsponge`, `w10_combine` and `w11_bullet`, so it re-emits
and re-proves those four rungs, and it is the next piece of work on this file — not a caveat. -/

/-- ⚑ **NO RUNG HOLDS TWO OF THE THREE COLLIDING REGIONS** — over EVERY rung, not over the pairs
someone wrote down. The first conjunct is the pin that `ALL_RUNGS` really is the whole type, so the
bounded ∀ cannot go quietly weaker when a constructor is added; the third states the collision
itself, so it is a named fact something can cite rather than a property of three definitions that
happen to agree. -/
theorem no_rung_holds_two_colliding_regions :
    ALL_RUNGS.length = 15
    ∧ (∀ k ∈ ALL_RUNGS,
        ((rungsUpto k).filter (fun r => COLLIDING_REGION_OWNERS.contains r)).length ≤ 1)
    ∧ baseWh shapeSmoke (mkWrap shapeSmoke).sp = baseFin shapeSmoke (mkWrap shapeSmoke).sp
    ∧ baseFin shapeSmoke (mkWrap shapeSmoke).sp = baseComb shapeSmoke (mkWrap shapeSmoke).sp := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ RED CONTROL for the gate above: a rung that DID hold two of them fails the same test, so the
∀ is a measurement of the ladder and not a vacuous truth about a list of singletons. -/
theorem two_colliding_regions_in_one_rung_would_be_caught :
    (([Rung.transcript, .prev, .wraphack, .finalize].filter
        (fun r => COLLIDING_REGION_OWNERS.contains r)).length ≤ 1) = False := by
  decide

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
    (combPtVar (mkWrap shapeSmoke) 0).1
      = (((mkWrap shapeSmoke).sp.evs.filter (fun e => e.isAbs && e.tag == T_SGOLD)).getD 0
          default).wordV
    ∧ (combPtVar (mkWrap shapeSmoke) shapeSmoke.prevs).1
      = (((mkWrap shapeSmoke).sp.evs.filter (fun e => e.isAbs && e.tag == T_XHAT)).getD 0
          default).wordV
    ∧ combPtVar (mkWrap shapeSmoke) (shapeSmoke.prevs + 1)
      = ftcOutV shapeSmoke (mkWrap shapeSmoke).sp
    ∧ (combPtVar (mkWrap shapeSmoke) (shapeSmoke.prevs + 2)).1
      = (((mkWrap shapeSmoke).sp.evs.filter (fun e => e.isAbs && e.tag == T_ZCOMM)).getD 0
          default).wordV
    ∧ (combPtVar (mkWrap shapeSmoke) (shapeSmoke.prevs + 3 + KEY_SINGLES)).1
      = (((mkWrap shapeSmoke).sp.evs.filter (fun e => e.isAbs && e.tag == T_WCOMM)).getD 0
          default).wordV := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

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
