/-
# `KimchiStepMainPins19d` — ⚑⚑ THE R4 FOLD REBUILT, AND IT CLOSES AT THE BLOCK'S OWN OPENING

## SAY THE SUBSTRATE OUT LOUD

Lean-authored throughout. Every arithmetic below runs on the assembly's OWN gadgets — `runEndo`
(R4's emitted `EndoMul` ladder) and `addA` (`Ops.add_fast`) — over the assembly's OWN bases,
which are Mina devnet block **539508**'s Wrap-proof commitments. Nothing is re-implemented in
Rust; no `#guard`; every fact is a named theorem.

## What §19c left, and what this closes

`…Pins19.the_corrected_transcript_still_refuses_and_the_residue_is_the_fold` measured that ONE
corrected absorb pair makes the assembly's own sponge squeeze the block's **entire** opening
transcript (`t`, `u`, all fifteen prechallenges, `c′`) — and that `bpCloses` at the block's own
`(sg, z₁, z₂)` STILL refuses, because R4 is not upstream's fold:

  * 46 combine rounds keyed on **23 round-robin cells** and SUMMED, where
    `combine_split_commitments` Horner-nests **one ξ** on the accumulator;
  * 28 of 30 `bullet_reduce` halves keyed off a foreign cell, and no `endo_inv` on the L halves.

`KimchiStepMainCore` §19d is that fold, written once, in the assembly's own algebra. This module
states what it does, in three theorems and a refutation pole for each named defect.

## ⚑ THE RESULT, plainly

  * **`the_ladder_is_multiplication_by_the_pallas_lift`** — `runEndo` at a prechallenge IS
    multiplication by `endoMap λ_Pallas` in `Fq`, `endo_inv`'s own assert closes at all fifteen
    pairs, and the `Fp`/`λ_Vesta` fold `liftVal` is a DIFFERENT scalar. Without this leg the two
    theorems under it would be about an arithmetic nobody had checked.
  * **`the_rebuilt_combine_reproduces_o1labs_own_aggregate`** — the Horner over the block's own 47
    commitments at the block's own ξ′ lands on `MinaWrapAggregationGate.COMBINED_GOLD`, which is
    **o1-labs' `PolyComm::multi_scalar_mul` over its own `combine_commitments` output**. The
    emitted round-robin sum does not, and neither does the same Horner at a moved ξ or a reversed
    list.
  * **`the_rebuilt_fold_closes_at_the_blocks_own_opening`** — `lhs` IS the block's `lhs`, and the
    block's own `(sg, b₀, z₁, z₂)` CLOSE `equal_g` under this assembly's own `bpCloses`. `G` can be
    the real accumulator: `SG_XY` is no longer refused.

## ⚑ THE ROWS ARE REWIRED (2026-08-09) — and this module gained the theorem that says so

`runIpa` emits §19d's fold now: `ipaLadderBase` / `ipaLadderCounter` / `ipaAddOperands` are the
wiring the docblock specified, and `qEndoInv` + `endoInvEqRows` are the fifteen witnessed
`endo_inv` points with their asserts. **`the_emitted_rows_are_the_rebuilt_fold`** is the leg that
was missing: driven at the BLOCK's own ξ′, the EMITTED assembly's own combine accumulator lands on
`COMBINED_GOLD` and its own `lhs` lands on `lhsRealOpening`. Before the rewiring it did neither, at
any ξ.

## ⚠ WHAT THIS IS STILL NOT — and it is now ONE thing, not two

**ξ is the BLOCK's, supplied — not the assembly's own `defc.pre 0`.** §8g chain 0 lifts the
STATEMENT word `vXiStmt`, and R8's `xi_correct` ties that word to the assembly's fr-sponge, which
runs over FIXTURE evaluations. So the assembly's OWN run (`tRealAdvice`) still does not close
`equal_g`, and **`G` STAYS `solveG`'s output**: publishing `SG_XY` over an `equal_g` the emitted
rows refuse would be a stapled slot, which is the shortcut §19b already declined and which the row
rewiring does NOT license. The residue is the **fr-sponge's instance** (segment B over the block's
own evaluations) plus the advice-cell split §19c(f) named. Both are smaller than the fold was and
neither is this one.
-/
import Dregg2.Circuit.Emit.KimchiStepMainPins19
import Dregg2.Circuit.Emit.MinaWrapXiEndoLift

namespace Dregg2.Circuit.Emit.KimchiStepMain

open Dregg2.Circuit.Emit.KimchiComposeStepFragment (jOf addA onCurveA)
open Dregg2.Bridge.MinaStepPrevCommitments (COMBINE_XY GAMMA_XY SG_XY DELTA_XY IPA_PRECHALS)
open Dregg2.Circuit.Emit.MinaWrapOpeningGate (CHAL CHAL_INV C_PRE CIP_SHIFTED U_BASE)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaCurve (scMulM)

set_option autoImplicit false
set_option maxRecDepth 100000

/-- The block's polyscale PRECHALLENGE ξ′, off the emitted Fq-sponge cone.
`MinaWrapXiEndoLift.the_polyscale_is_the_endo_lift_of_the_squeeze` is what says its `Fq` lift is
the ξ `MinaWrapAggregationGate` builds `COMBINED_GOLD` with — so the fold below and the aggregate
it is checked against are driven by ONE number, derived, not two that agree. -/
def XI_PRE : Nat := Dregg2.Circuit.Emit.MinaWrapXiEndoLift.V_CHAL

/-- o1-labs' own 47-term aggregate, affine. -/
def COMBINED_GOLD_A : Nat × Nat :=
  ((Dregg2.Circuit.Emit.MinaWrapAggregationGate.COMBINED_GOLD).1,
   (Dregg2.Circuit.Emit.MinaWrapAggregationGate.COMBINED_GOLD).2.1)

/-- The fifteen `bullet_reduce` prechallenges **as the assembly's own sponge squeezes them** at the
corrected advice pair. `…Pins19.the_transcript_half_closes_at_the_blocks_own_advice_pair` is what
says these are the block's `IPA_PRECHALS`; taking them off `tRealAdvice.sp` rather than off the
constant keeps every theorem below a statement about the ASSEMBLY. -/
def foldPres : List Nat :=
  (List.range 15).map (fun j => chalOf shapeStep tRealAdvice.sp (shapeStep.bulletChal j))

/-- …and the closing squeeze `c′`, likewise the assembly's own. -/
def foldCPre : Nat := chalOf shapeStep tRealAdvice.sp shapeStep.cChal

/-- ⚑ The keying the emitted shape used for the same thirty halves BEFORE 2026-08-09 —
`(msmTerms + r) % chals` at `r = 46 + 2j`, the round-robin cell. `StepShape.ipaChal` is DELETED;
the expression survives here, and only here, as defect (i)'s refutation pole. Pair `j`'s two halves
landed on their own squeeze by accident at two `j` and nowhere else. -/
def foldPresRoundRobin : List Nat :=
  (List.range 15).map (fun j =>
    chalOf shapeStep tRealAdvice.sp ((shapeStep.msmTerms + 46 + 2 * j) % shapeStep.chals))

/-- `uc = scale_fast2 u advice.combined_inner_product`, off §19's own `group_map` half at the
assembly's own squeeze and the block's advice. -/
def foldUc : Nat × Nat := (runUc (uSqueezeVal shapeStep tRealAdvice.sp) CIP_SHIFTED).res

/-- The rebuilt fold's `lhs`, at the assembly's own transcript. -/
def foldLhsReal : Nat × Nat :=
  foldLhs shapeStep COMBINE_XY GAMMA_XY XI_PRE foldPres foldUc DELTA_XY foldCPre

/-- ⚑⚑ **(g) THE LADDER IS MULTIPLICATION BY THE PALLAS LIFT — AND `endo_inv`'S ASSERT CLOSES.**

Without this leg the two theorems below would be facts about an arithmetic nobody had tied to
anything: `runEndo` could have been any endomorphism ladder and the Horner could have reproduced
`COMBINED_GOLD` for a reason having nothing to do with `Scalar_challenge.endo`.

⚑ **AND THE `Fp`/`Fq` LEG IS THE ONE THAT MATTERS.** `liftVal` is the SAME fold at
`ENDO_R = λ_Vesta` in `Fp` — §8g's deferred word, the C8 *scalar* fold's multiplier. If the two
were interchangeable a fold that read one for the other would be self-consistent and wrong; the
third conjunct refutes the interchange at the block's own first prechallenge. -/
theorem the_ladder_is_multiplication_by_the_pallas_lift :
    (-- one ladder IS scalar multiplication by the `Fq` lift, at the block's own prechallenge…
     (List.range 15).all (fun j =>
       let R := GAMMA_XY.getD (2 * j + 1) (0, 0)
       endoOutOf shapeStep R (IPA_PRECHALS.getD j 0)
         == jAffOf ((scMulM pN (endoScalarQ (IPA_PRECHALS.getD j 0) % qN) (jOf R)).getD (0, 0, 0)))
     -- …and that lift is the one `MinaWrapOpeningGate` derived from the same prechallenges…
     && (List.range 15).all (fun j => endoScalarQ (IPA_PRECHALS.getD j 0) == CHAL.getD j 0)
     -- …and `endo_inv`'s OWN assert closes: the ladder over the witnessed point IS the commitment…
     && (List.range 15).all (fun j =>
          let L := GAMMA_XY.getD (2 * j) (0, 0)
          endoOutOf shapeStep (endoInvOf L (IPA_PRECHALS.getD j 0)) (IPA_PRECHALS.getD j 0) == L)
     -- …its scalar is `CHAL_INV`, so the inverse is the one the opening gate proved is one…
     && (List.range 15).all (fun j =>
          qInv (endoScalarQ (IPA_PRECHALS.getD j 0)) == CHAL_INV.getD j 0)
     -- …and the `Fp`/`λ_Vesta` fold is a DIFFERENT scalar, so the two are not interchangeable.
     && (List.range 15).all (fun j =>
          liftVal shapeStep (IPA_PRECHALS.getD j 0) != endoScalarQ (IPA_PRECHALS.getD j 0)))
      = true := by
  native_decide

#assert_compiled the_ladder_is_multiplication_by_the_pallas_lift

/-- ⚑ **THE RETIRED FOLD, AS A VALUE.** `Σ_r Scalar_challenge.endo(C_{r+1}, roundRobin r)` chained
by `Ops.add_fast` from `sg_old[0]` — exactly what `runIpa` emitted until 2026-08-09, built here from
its own parts because the rows no longer produce it. Defect (i)'s refutation pole. -/
def roundRobinCombine : Nat × Nat :=
  (List.range 46).foldl
    (fun acc r => addA acc
      (endoOutOf shapeStep (COMBINE_XY.getD (r + 1) (0, 0))
        (chalOf shapeStep tRealAdvice.sp ((shapeStep.msmTerms + r) % shapeStep.chals))))
    (COMBINE_XY.getD 0 (0, 0))

/-- ⚑⚑ **(h) THE REBUILT COMBINE REPRODUCES O1-LABS' OWN AGGREGATE, AND THE EMITTED ONE DOES NOT.**

`COMBINED_GOLD` is `PolyComm::multi_scalar_mul` over o1-labs' own `combine_commitments` output for
this block — a number dumped from their code, not one this tree computed. The first conjunct says
`combine_split_commitments`, run on the assembly's own `EndoMul` ladder and `Ops.add_fast` over the
assembly's own 47 bases at the block's own ξ′, lands on it.

The refutation poles are what stop that being an accident of a fold that collapses:

  * a moved ξ misses it — so the ONE ξ is load-bearing;
  * the REVERSED commitment list misses it — so it is a Horner and not a sum, and
    `combine_split_commitments`' `List.rev` is read correctly;
  * ⚑ **the RETIRED round-robin fold misses it** — defect (i). ⚠ Since 2026-08-09 the rows no
    longer emit that value, so the pole is CONSTRUCTED here (`roundRobinCombine`) rather than read
    off `tRealAdvice`: a control that quietly becomes the same object it is refuting is a
    falsifier that stopped falsifying, and this one would have;
  * ⚑ **and the same Horner at the ASSEMBLY's own ξ misses it too** — which is the residue this
    module hands forward, now that the shape is right and only the instance is not. -/
theorem the_rebuilt_combine_reproduces_o1labs_own_aggregate :
    (-- the Horner IS o1-labs' aggregate…
     combineSplit shapeStep COMBINE_XY XI_PRE == COMBINED_GOLD_A
     -- …the list is the 47 `without_degree_bound` commitments…
     && COMBINE_XY.length == 47
     -- …one ξ, and it is load-bearing…
     && combineSplit shapeStep COMBINE_XY (XI_PRE + 1) != COMBINED_GOLD_A
     -- …it is a HORNER, not a sum: the reversed list is a different point…
     && combineSplit shapeStep COMBINE_XY.reverse XI_PRE != COMBINED_GOLD_A
     -- …and the RETIRED round-robin fold is NOT it, reconstructed as a value so the pole outlives
     -- the rows that used to emit it.
     && roundRobinCombine != COMBINED_GOLD_A
     -- …⚠ and neither is the same Horner at the ASSEMBLY's own ξ: that is the instance residue,
     -- and it is what `tRealAdvice.ipa.sums.getD 45` now carries.
     && combineSplit shapeStep COMBINE_XY (tRealAdvice.defc.pre.getD 0 0) != COMBINED_GOLD_A
     && (tRealAdvice.ipa.sums.getD 45 (0, 0)) != COMBINED_GOLD_A) = true := by
  native_decide

#assert_compiled the_rebuilt_combine_reproduces_o1labs_own_aggregate

/-- ⚑⚑⚑ **(i) THE REBUILT FOLD CLOSES `equal_g` AT THE BLOCK'S OWN `(sg, b₀, z₁, z₂)`.**

The whole of `check_bulletproof`, rebuilt: Horner combine, `+ uc`, `+ lr_prod` with `endo_inv` on
each L half, `Scalar_challenge.endo … c′`, `+ delta` — over the assembly's own bases, at the
assembly's OWN squeezes (`foldPres`, `foldCPre` read off `tRealAdvice.sp`, which §19c(d) showed
are the block's). Its `lhs` IS `lhsRealOpening`, the point `z₁·(sg + b₀·u) + z₂·H` lands on, and
`bpCloses` — the same predicate that has refused `SG_XY` since §19b — accepts.

**Each of §19c(f)'s three named defects is refuted separately**, so this is not one repair whose
parts are untested:

  * (i) the bullet halves keyed on the emitted ROUND-ROBIN cell instead of the pair's own
    prechallenge → a different `lhs`;
  * (ii) a forward `endo` on the L half instead of `endo_inv` → a different pair term;
  * (iii) a moved ξ → a different `lhs`.

⚠ **AND THE ONE THING THAT IS NOT THE ASSEMBLY'S OWN IS MEASURED, NOT ELIDED**: the last conjunct
says the assembly's own §8g ξ (`defc.pre 0`, the lift of the statement word `vXiStmt` that R8's
`xi_correct` ties to the fr-sponge over FIXTURE evaluations) is NOT the block's ξ′. That is the
residue this theorem hands forward, and it is the fr-sponge's INSTANCE, not the fold's shape. -/
theorem the_rebuilt_fold_closes_at_the_blocks_own_opening :
    (-- the assembly's own squeezes ARE the block's — §19c(d), restated on this subject…
     foldPres == IPA_PRECHALS && foldCPre == C_PRE
     -- …the rebuilt fold's `lhs` IS the block's own `lhs`…
     && foldLhsReal == lhsRealOpening
     -- …so the block's own `(sg, b₀, z₁, z₂)` CLOSE `equal_g` on this assembly's own predicate…
     && bpCloses U_BASE_A GENERATORS_H foldLhsReal (jOf SG_XY) B0_SHIFTED Z1_SHIFTED Z2_SHIFTED
     -- …and it still discriminates here: a moved `sg` is refused at the very same `lhs`…
     && bpCloses U_BASE_A GENERATORS_H foldLhsReal (jOf sgAlt)
          B0_SHIFTED Z1_SHIFTED Z2_SHIFTED == false
     -- …while the EMITTED fold's `lhs` is a different point, which is the contrast kept alive…
     && bpLhsOf tRealAdvice != foldLhsReal
     -- ── the three defects, each independently load-bearing ──
     -- (i) round-robin keying of the thirty halves…
     && foldLhs shapeStep COMBINE_XY GAMMA_XY XI_PRE foldPresRoundRobin foldUc DELTA_XY foldCPre
          != foldLhsReal
     && foldPresRoundRobin != foldPres
     -- (ii) a FORWARD `endo` on the L half where upstream takes `endo_inv`…
     && addA (endoOutOf shapeStep (GAMMA_XY.getD 0 (0, 0)) (IPA_PRECHALS.getD 0 0))
             (endoOutOf shapeStep (GAMMA_XY.getD 1 (0, 0)) (IPA_PRECHALS.getD 0 0))
          != bulletTerm shapeStep GAMMA_XY foldPres 0
     -- (iii) a moved ξ…
     && foldLhs shapeStep COMBINE_XY GAMMA_XY (XI_PRE + 1) foldPres foldUc DELTA_XY foldCPre
          != foldLhsReal
     -- ⚠ …and the residue this hands forward: the assembly's OWN §8g ξ is not the block's.
     && tRealAdvice.defc.pre.getD 0 0 != XI_PRE) = true := by
  native_decide

#assert_compiled the_rebuilt_fold_closes_at_the_blocks_own_opening

/-- ⚑ **THE EMITTED ROWS' OWN `IpaData`, at the two data the assembly does not yet derive.**

`runIpa` is the row emitter's value side — the very function `ipaRows`, `circuitEnv` and
`stepWitness` read — and this runs it on the committed shape over the block's own commitments and
the block's own transcript. ⚠ **TWO arguments are the BLOCK's rather than the assembly's, and both
are named rather than hidden:**

  * **ξ′** — §8g chain 0 lifts `vXiStmt`, which R8's `xi_correct` ties to a fr-sponge running over
    FIXTURE evaluations, so the assembly's own ξ is not the block's;
  * **`ft_comm`** — §6b's MSM runs at R6's own deferred scalars, so the assembly's round-2 base is
    not `COMBINE_XY[3]`.

Everything else — the 47 commitments, the thirty gammas, the fifteen prechallenges, `c′`, `delta`,
`uc` — is what the emitted assembly itself computes. The theorem below is therefore about the
fold's SHAPE and its `endo_inv` half; the two instances are the residue, and the last two conjuncts
measure each one on `tRealAdvice`. -/
def emittedAtBlockData : IpaData :=
  runIpa shapeStep (stepBases shapeStep) tRealAdvice.sp (COMBINE_XY.getD 3 (0, 0)) foldUc XI_PRE

def emittedLhs : Nat × Nat :=
  (emittedAtBlockData.lhsAdd.getD 4 0, emittedAtBlockData.lhsAdd.getD 5 0)

/-- ⚑⚑⚑ **(j) THE EMITTED ROWS ARE THE REBUILT FOLD — the leg §19d was missing.**

Theorems (g)–(i) are about `combineSplit` / `bulletTerm` / `foldLhs`, definitions §19d introduced.
This one is about **`runIpa`**, the function the row schedule and the witness environment both read.
It says the two are the same object, and it says it at the strongest available point: driven at the
block's ξ′ and `ft_comm`, the EMITTED fold's own 46-round accumulator IS `PolyComm::multi_scalar_mul`
over o1-labs' own `combine_commitments` output, its own `lhs` IS the block's opening point, and the
block's own `(sg, b₀, z₁, z₂)` CLOSE `equal_g` on it.

The wiring conjuncts are what make that a statement about the ROWS rather than a coincidence:

  * every combine ladder's base is the PREVIOUS step's add output, and step 0's is the LAST
    commitment — `combine_split_commitments`' `List.rev … init`;
  * `sg_old[0]` IS `COMBINE_XY[0]`, so the point the emitted chain closes on is the flat list's
    head and not a second copy of it;
  * each `endo_inv` witness is ON THE CURVE and its ladder's OUTPUT is the absorbed L commitment —
    which is what `endoInvEqRows` asserts, checked here at the value layer;
  * the fifteen witnesses are NOT the commitments they check (an identity carrier would satisfy
    every conjunct above and bind nothing).

⚠ **AND IT DOES NOT LICENSE PUBLISHING `SG_XY`.** The last two conjuncts are the assembly's own
run: its ξ is not the block's, its `ft_comm` is not the block's, and its `lhs` is therefore not
`lhsRealOpening`. `G` stays `solveG`'s output; `equal_g` on the emitted rows still refuses the real
accumulator, and stapling `SG_XY` over that refusal is the shortcut §19b declined. -/
theorem the_emitted_rows_are_the_rebuilt_fold :
    (-- the EMITTED fold's own combine accumulator IS o1-labs' aggregate…
     emittedAtBlockData.sums.getD 45 (0, 0) == COMBINED_GOLD_A
     -- …the EMITTED `lhs` is §19d's `foldLhs`, so rows and definitions are one object…
     && emittedLhs == foldLhsReal
     -- …and it is the block's own opening point…
     && emittedLhs == lhsRealOpening
     -- …so the block's own scalars CLOSE `equal_g` on the emitted rows' own `lhs`…
     && bpCloses U_BASE_A GENERATORS_H emittedLhs (jOf SG_XY)
          B0_SHIFTED Z1_SHIFTED Z2_SHIFTED
     -- ── the WIRING, read off the emitted data ──
     -- …every combine ladder runs on the previous step's add output…
     && (List.range 45).all (fun a =>
          emittedAtBlockData.ladderBases.getD (a + 1) (0, 0)
            == emittedAtBlockData.sums.getD a (0, 0))
     -- …and step 0's on the LAST commitment…
     && emittedAtBlockData.ladderBases.getD 0 (0, 0) == COMBINE_XY.getD 46 (0, 0)
     -- …`sg_old[0]` IS the flat list's head, so the chain closes on `COMBINE_XY[0]` itself…
     && Dregg2.Bridge.MinaStepPrevCommitments.SG_OLD0_XY == COMBINE_XY.getD 0 (0, 0)
     -- …the fifteen `endo_inv` witnesses exist, are on the curve…
     && emittedAtBlockData.invs.length == 15
     && emittedAtBlockData.invs.all onCurveA
     -- …their ladders' OUTPUTS are the absorbed L commitments (what `endoInvEqRows` asserts)…
     && (List.range 15).all (fun j =>
          (emittedAtBlockData.accs.getD (46 + 2 * j) []).getLastD (0, 0)
            == GAMMA_XY.getD (2 * j) (0, 0))
     -- …and they are NOT those commitments, so the binding is not an identity carrier…
     && (List.range 15).all (fun j =>
          emittedAtBlockData.invs.getD j (0, 0) != GAMMA_XY.getD (2 * j) (0, 0))
     -- ⚠ ── the residue, on the ASSEMBLY's OWN run ──
     && tRealAdvice.defc.pre.getD 0 0 != XI_PRE
     && tRealAdvice.ftc.out != COMBINE_XY.getD 3 (0, 0)
     && bpLhsOf tRealAdvice != lhsRealOpening) = true := by
  native_decide

#assert_compiled the_emitted_rows_are_the_rebuilt_fold

end Dregg2.Circuit.Emit.KimchiStepMain
