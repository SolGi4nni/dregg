/-
`KimchiStepMain` pins — §13 §14.

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

/-! ## §13 — R6: the COMPILED `ft_eval0` against dregg's own verified value layer.

The compiler of §8b is a compiler, not an oracle: every value it produces is pinned here against the
READ-ONLY `KimchiVerify` body it claims to compute, on the SAME inputs, and each pin carries a red
control that bites. The 67 gate constraints are compared **list by list**, so a slip in one body of
one gate cannot be absorbed by the sum. -/

-- ⚑ THE CONFIG IS REAL, not decorative. ω is a primitive `2^16`-th root of unity (so `ω^{n−1}` IS
-- the witnessed inverse the circuit derives), the three `EndomulScalar` quotients are the genuine
-- ones, and the endo coefficient is a cube root of unity distinct from 1.
#guard Dregg2.Bridge.MinaWrapFtEval0.powFast ((FT_OMEGA : Nat) : ZMod pN) FT_N == (1 : ZMod pN)
#guard Dregg2.Bridge.MinaWrapFtEval0.powFast ((FT_OMEGA : Nat) : ZMod pN) (FT_N / 2) != (1 : ZMod pN)
#guard fMul FT_OMEGA FT_OMEGA_INV == 1
#guard Dregg2.Circuit.Emit.KimchiVerify.endomulScalarConstsOk
        ((FT_QUOT.1 : Nat) : ZMod pN) ((FT_QUOT.2.1 : Nat) : ZMod pN)
        ((FT_QUOT.2.2 : Nat) : ZMod pN)
#guard ((FT_ENDO : Nat) : ZMod pN) ^ 3 == (1 : ZMod pN)
#guard ((FT_ENDO : Nat) : ZMod pN) != (1 : ZMod pN)
#guard FT_MDS9.length == 9

-- ⚑⚑ **THE SEVEN COSET SHIFTS ARE THE DERIVED TICK SHIFTS** (simplification #8, retired). The rung
-- runs `TickShifts.tickShiftsFp 16` — the `Shifts::new` Blake2b→field construction — and that list
-- is pinned BYTE-EXACT there against o1-labs' own `Shifts::new(Radix2EvaluationDomain::<Fp>::new
-- (2^16))` output (`tick_shifts_export`, a path that runs kimchi and touches no Lean). Restated
-- here so a swap back to a fixture is a red in THIS file, at the point of use.
#guard FT_SHIFTS == Dregg2.Bridge.TickShifts.TICK_SHIFTS_16_ORACLE
#guard FT_SHIFTS.length == 7
-- …the first shift is the identity coset (`shifts[0] = 1`, `permutation.rs:158`), the rest are not,
-- and all seven are distinct — the structure `Shifts::new` guarantees and a fixture cannot fake.
#guard FT_SHIFTS.headD 0 == 1
#guard (FT_SHIFTS.drop 1).all (fun x => x != 1 && x != 0)
#guard FT_SHIFTS.dedup.length == 7
-- …and the derivation really is a derivation: the six sampled shifts are quadratic NON-residues of
-- `Fp` outside the `2^16` domain, which is `Shifts::sample`'s own acceptance predicate.
#guard (FT_SHIFTS.drop 1).all (fun x =>
  Dregg2.Bridge.TickShifts.accept FT_N [] ((x : Nat) : ZMod pN))
-- ⚑ …and they are NOT the placeholders the rung used before (the red control lives in §13's
-- `ft_eval0` pins below, where the fixtures give a different value).
#guard (List.range 7).all (fun i => FT_SHIFTS.getD i 0 != FT_SHIFTS_WERE_FIXTURES.getD i 0)
-- ⚑ ALL SIX GATE SELECTORS FIRE. Without this every body but `generic` is multiplied by zero and
-- the six transcriptions rest on a source reading — the exact hazard `MinaWrapFtEval0Weld` §1b
-- named when it found the first fixture with a nonzero `emulSel`.
#guard (List.range 6).all (fun i => colZ (IDX_SEL + i) != 0)

-- ⚑ ω^{n−1}, ω^{n−2}, ω^{n−3} ARE the circuit's derived inverse powers — the reason the rung spends
-- ONE witnessed inverse instead of a 48-row exponentiation, and the reason `zkPoly` is exact.
#guard ((FT_OMEGA_INV : Nat) : ZMod pN)
        == Dregg2.Bridge.MinaWrapFtEval0.powFast ((FT_OMEGA : Nat) : ZMod pN) (FT_N - 1)
#guard ((ftVal ftS.fp.slots.omInv3 : Nat) : ZMod pN)
        == Dregg2.Bridge.MinaWrapFtEval0.powFast ((FT_OMEGA : Nat) : ZMod pN) (FT_N - 3)
-- …and `ζ^n` really is the `log2n`-fold squaring, and `zkPoly` the shipped one.
#guard ((ftVal ftS.fp.slots.zetaN : Nat) : ZMod pN)
        == Dregg2.Bridge.MinaWrapFtEval0.powFast ((zetaS : Nat) : ZMod pN) FT_N
#guard ((ftVal ftS.fp.slots.zkp : Nat) : ZMod pN)
        == Dregg2.Circuit.Emit.KimchiVerify.zkPolyR FT_N
             ((FT_OMEGA : Nat) : ZMod pN) ((zetaS : Nat) : ZMod pN)

-- ⚑ **THE LINEARIZATION CONSTANT TERM.** The compiled six-body sum IS `KimchiVerify.gateLinConst`
-- of the same `GateEvals` — the value `MinaWrapFtEval0Weld` reproduces byte-for-byte on devnet
-- block 539508's Step side (`lct_true = 20345…173047`) and on its Wrap side (`LCT`).
#guard ((ftVal ftS.fp.slots.linConst : Nat) : ZMod pN)
        == Dregg2.Circuit.Emit.KimchiVerify.gateLinConst gS
-- …and IT BITES: bend ONE input — the `endomul` selector — and the constant term moves.
#guard (((ftVal ftS.fp.slots.linConst : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.gateLinConst
              { gS with emulSel := gS.emulSel + 1 }) == false
-- …and the endo really is load-bearing (the `endoMulConstraints` reader; the cube-root conflation
-- `MinaWrapFtEval0Weld` closed would show HERE).
#guard (((ftVal ftS.fp.slots.linConst : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.gateLinConst
              { gS with endo := gS.endo + 1 }) == false

-- ⚑ **`ft_eval0`.** The compiled fold IS `KimchiVerify.ftEval0R` — the CommRing mirror that is the
-- shipped `ftEval0` for every field (`ftEval0R_eq`, `rfl`) — at the SAME domain, challenges,
-- columns, shifts and constant term, with the witnessed inverse the circuit checks.
#guard
  ((ftS.out : Nat) : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.ftEval0R FT_N
         ((FT_OMEGA : Nat) : ZMod pN) ((zetaS : Nat) : ZMod pN)
         ((betaS : Nat) : ZMod pN) ((gammaS : Nat) : ZMod pN)
         (((alphaS : Nat) : ZMod pN) ^ 21) (((alphaS : Nat) : ZMod pN) ^ 22)
         (((alphaS : Nat) : ZMod pN) ^ 23)
         wZ sZ (FT_SHIFTS.map (fun x => ((x : Nat) : ZMod pN)))
         (colZ IDX_Z) (colW IDX_Z) ((evVal 2 0 : Nat) : ZMod pN)
         (Dregg2.Circuit.Emit.KimchiVerify.gateLinConst gS)
         (((ftS.denomInv : Nat) : ZMod pN))
-- ⚑ …and the pin BITES at every leg that could silently drift. β for γ:
#guard
  (((ftS.out : Nat) : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.ftEval0R FT_N
         ((FT_OMEGA : Nat) : ZMod pN) ((zetaS : Nat) : ZMod pN)
         ((gammaS : Nat) : ZMod pN) ((gammaS : Nat) : ZMod pN)
         (((alphaS : Nat) : ZMod pN) ^ 21) (((alphaS : Nat) : ZMod pN) ^ 22)
         (((alphaS : Nat) : ZMod pN) ^ 23)
         wZ sZ (FT_SHIFTS.map (fun x => ((x : Nat) : ZMod pN)))
         (colZ IDX_Z) (colW IDX_Z) ((evVal 2 0 : Nat) : ZMod pN)
         (Dregg2.Circuit.Emit.KimchiVerify.gateLinConst gS)
         (((ftS.denomInv : Nat) : ZMod pN))) == false
-- ⚑ …a bent DERIVED coset shift (the leg `MinaWrapFtEval0Weld` §6b exhibits on the real block):
-- bend one of `tickShiftsFp 16`'s own outputs by one and `ft_eval0` moves.
#guard
  (((ftS.out : Nat) : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.ftEval0R FT_N
         ((FT_OMEGA : Nat) : ZMod pN) ((zetaS : Nat) : ZMod pN)
         ((betaS : Nat) : ZMod pN) ((gammaS : Nat) : ZMod pN)
         (((alphaS : Nat) : ZMod pN) ^ 21) (((alphaS : Nat) : ZMod pN) ^ 22)
         (((alphaS : Nat) : ZMod pN) ^ 23)
         wZ sZ ((FT_SHIFTS.map (fun x => ((x : Nat) : ZMod pN))).set 1
                  (((FT_SHIFTS.getD 1 0 : Nat) : ZMod pN) + 1))
         (colZ IDX_Z) (colW IDX_Z) ((evVal 2 0 : Nat) : ZMod pN)
         (Dregg2.Circuit.Emit.KimchiVerify.gateLinConst gS)
         (((ftS.denomInv : Nat) : ZMod pN))) == false
-- ⚑⚑ **DERIVED, NOT FIXED — the red control for simplification #8.** The seven placeholders the
-- rung ran until 2026-08-02 give a DIFFERENT `ft_eval0` at the same wire. So the value the circuit's
-- `Generic` rows compute is the one Mina's own `Shifts::new` cosets produce, and swapping the
-- derivation back out is a red rather than a silence.
#guard
  (((ftS.out : Nat) : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.ftEval0R FT_N
         ((FT_OMEGA : Nat) : ZMod pN) ((zetaS : Nat) : ZMod pN)
         ((betaS : Nat) : ZMod pN) ((gammaS : Nat) : ZMod pN)
         (((alphaS : Nat) : ZMod pN) ^ 21) (((alphaS : Nat) : ZMod pN) ^ 22)
         (((alphaS : Nat) : ZMod pN) ^ 23)
         wZ sZ (FT_SHIFTS_WERE_FIXTURES.map (fun x => ((x : Nat) : ZMod pN)))
         (colZ IDX_Z) (colW IDX_Z) ((evVal 2 0 : Nat) : ZMod pN)
         (Dregg2.Circuit.Emit.KimchiVerify.gateLinConst gS)
         (((ftS.denomInv : Nat) : ZMod pN))) == false
-- …and a constant term off by one (so the `gateLinConst` leg is not decoration inside the fold):
#guard
  (((ftS.out : Nat) : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.ftEval0R FT_N
         ((FT_OMEGA : Nat) : ZMod pN) ((zetaS : Nat) : ZMod pN)
         ((betaS : Nat) : ZMod pN) ((gammaS : Nat) : ZMod pN)
         (((alphaS : Nat) : ZMod pN) ^ 21) (((alphaS : Nat) : ZMod pN) ^ 22)
         (((alphaS : Nat) : ZMod pN) ^ 23)
         wZ sZ (FT_SHIFTS.map (fun x => ((x : Nat) : ZMod pN)))
         (colZ IDX_Z) (colW IDX_Z) ((evVal 2 0 : Nat) : ZMod pN)
         (Dregg2.Circuit.Emit.KimchiVerify.gateLinConst gS + 1)
         (((ftS.denomInv : Nat) : ZMod pN))) == false

-- ⚑ THE WITNESSED INVERSE IS THE GENUINE ONE — and the circuit checks it, so a prover who supplies
-- another value is refused by the `denom·denomInv = 1` row rather than believed.
#guard (((zetaS : Nat) : ZMod pN)
          - Dregg2.Bridge.MinaWrapFtEval0.powFast ((FT_OMEGA : Nat) : ZMod pN) (FT_N - 3))
        * (((zetaS : Nat) : ZMod pN) - 1) * ((ftS.denomInv : Nat) : ZMod pN) == (1 : ZMod pN)

-- ⚑ `Plonk_checks.checked` — `derive_plonk`'s `perm` scalar, compiled, against a direct fold of the
-- same six σ evaluations. `checked` asserts exactly this equality against the deferred word, and the
-- rung emits that assertion as a row.
#guard
  ((ftVal ftS.fp.slots.perm : Nat) : ZMod pN)
    == -((List.range 6).foldl
           (fun acc i => acc * (((gammaS : Nat) : ZMod pN)
             + ((betaS : Nat) : ZMod pN) * sZ.getD i 0 + wZ.getD i 0))
           (colW IDX_Z * ((betaS : Nat) : ZMod pN) * (((alphaS : Nat) : ZMod pN) ^ 21)
             * ((ftVal ftS.fp.slots.zkp : Nat) : ZMod pN)))
#guard (((ftVal ftS.fp.slots.perm : Nat) : ZMod pN) == 0) == false

-- ⚑ THE OUTPUT IS WIRED INTO R5's `combined_inner_product`: `ft_eval0` IS the `ft` column the C8
-- fold consumes (`combine ~ft:ft_eval0`, `step_verifier.ml:1078-1083`), so the two rungs share a
-- variable rather than agreeing by construction in Lean only.
#guard tS.df.ez.getD 3 0 == ftS.out
#guard evZOf ftS.out 3 == ftS.out
#guard evZOf ftS.out 3 != evVal 3 0

/-! ### §13a — the SIXTY-SEVEN CONSTRAINT BODIES, list by list.

The pins above check the SUM. These check each compiled body against the `KimchiVerify` list it
mirrors, elementwise, so a compensating pair of slips cannot pass. Each of the six is run through
`aEval` a second time in isolation (the same `ftLkS`), which is why the slot indices below are the
ones the isolated program returns. -/

#guard bodyVals bodyCompleteAdd
        == Dregg2.Circuit.Emit.KimchiVerify.completeAddConstraints wZ
#guard bodyVals bodyVarBaseMul
        == Dregg2.Circuit.Emit.KimchiVerify.varBaseMulConstraints wZ wW
#guard bodyVals (bodyEndoMul FT_ENDO)
        == (Dregg2.Circuit.Emit.KimchiVerify.endoMulConstraints
              ((FT_ENDO : Nat) : ZMod pN) wZ wW).take 11
#guard bodyVals bodyEmScalar
        == Dregg2.Circuit.Emit.KimchiVerify.endomulScalarConstraints
             ((FT_QUOT.1 : Nat) : ZMod pN) ((FT_QUOT.2.1 : Nat) : ZMod pN)
             ((FT_QUOT.2.2 : Nat) : ZMod pN) wZ
#guard bodyVals bodyPoseidon
        == Dregg2.Circuit.Emit.KimchiVerify.poseidonConstraints mdsS3 coeffZ wZ wW
-- …and the list-by-list pins BITE: a bent `endo` moves the `EndosclMul` list.
#guard (bodyVals (bodyEndoMul (FT_ENDO + 1))
         == (Dregg2.Circuit.Emit.KimchiVerify.endoMulConstraints
               ((FT_ENDO : Nat) : ZMod pN) wZ wW).take 11) == false
-- …and none of the five lists is all-zero (a body that vanished would match a wrong transcription).
#guard (Dregg2.Circuit.Emit.KimchiVerify.varBaseMulConstraints wZ wW).any (fun z => z != 0)
#guard (Dregg2.Circuit.Emit.KimchiVerify.poseidonConstraints mdsS3 coeffZ wZ wW).any (fun z => z != 0)

/-! ## §14 — R7: the EVALUATION ABSORPTION.

The three segments' arithmetic, against `PastaPoseidon.Ref.perm` — the same reference whose
`Ref.hash` reproduces the o1js `Poseidon.hash` gold KATs, and the same one R1's sponge answers to. -/

/-- ⚑ **SEGMENT B's WORD COUNT IS FIVE + 2×43 SINCE §22**, the five being the seed
(`step_main.ml:45`) and `finalize_other_proof`'s own four (`step_verifier.ml:962-965`). 91 is ODD, so
this segment — alone of the four — carries the rate-2 pad lane, and `nb` is one block larger than the
seedless shape's 45. -/
theorem segment_b_absorbs_ninety_one_words_and_is_the_only_padded_segment :
    (tS.specB.ws.length = SEG_B_PREFIX + 2 * (shapeSmoke.cipEvals - EV_PREFIX)
     ∧ tS.specB.ws.length = 91
     ∧ tS.specB.padded = true
     ∧ (tS.specA.padded, tS.specC.padded, tS.specD.padded) = (false, false, false)) := by
  native_decide
#assert_compiled segment_b_absorbs_ninety_one_words_and_is_the_only_padded_segment

#guard tS.specA.ws.length == 2 * shapeSmoke.bRounds
#guard tS.specC.ws.length == shapeSmoke.hmWords
#guard tS.specA.nb == nbA shapeSmoke
#guard tS.specB.nb == nbB shapeSmoke
#guard tS.specC.nb == nbC shapeSmoke

-- ⚑ EVERY SEGMENT IS THE REAL SPONGE: each block's output is `Ref.perm` of its absorbed input,
-- EXCEPT where the opt-sponge MASK discards it — and that exception is exactly the masked blocks.
#guard (List.range tS.specB.blocks).all (fun b =>
  let pre := tS.segB.states.getD b []
  let post := if b < tS.specB.nb then
      [ fAdd (pre.getD 0 0) ((tS.specB.ws.getD (2 * b) (xv 0, 0)).2)
      , fAdd (pre.getD 1 0) ((tS.specB.ws.getD (2 * b + 1) (xv 0, 0)).2), pre.getD 2 0 ]
    else pre
  tS.segB.states.getD (b + 1) [] == Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm post)
-- ⚑ Segment C is masked FROM BLOCK `N_HM_FIX/2` ON, so its own statement carries the exception:
-- a kept block is `Ref.perm` of the absorbed state, a dropped one is the state UNCHANGED. Both
-- legs occur (`MASK_BITS = [0,1]`), so neither half of the disjunction is idle.
#guard (List.range tS.specC.blocks).all (fun b =>
  let pre := tS.segC.states.getD b []
  let post := if b < tS.specC.nb then
      [ fAdd (pre.getD 0 0) ((tS.specC.ws.getD (2 * b) (xv 0, 0)).2)
      , fAdd (pre.getD 1 0) ((tS.specC.ws.getD (2 * b + 1) (xv 0, 0)).2), pre.getD 2 0 ]
    else pre
  if b < tS.specC.nb && tS.specC.maskedAt b && tS.specC.keepBit b == 0 then
    tS.segC.states.getD (b + 1) [] == pre
  else tS.segC.states.getD (b + 1) [] == Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm post)
-- …and BOTH legs really occur in segment C (a mask that dropped nothing would satisfy the above
-- with the `pre` branch dead).
#guard ((List.range tS.specC.nb).filter
          (fun b => tS.specC.maskedAt b && tS.specC.keepBit b == 0)).length > 0
#guard ((List.range tS.specC.nb).filter
          (fun b => tS.specC.maskedAt b && tS.specC.keepBit b == 1)).length > 0
#guard ((List.range tS.specC.nb).filter (fun b => !tS.specC.maskedAt b)).length == N_HM_FIX / 2

-- ⚑ THE MASK IS A MASK, BOTH WAYS. A `keep = 1` block advances to the permutation output; a
-- `keep = 0` block leaves the state EXACTLY where it was — `Field.if_` on all three lanes
-- (`step_verifier.ml:998-1003`). Both branches occur, so neither is untested.
#guard (List.range tS.specA.nb).all (fun b =>
  if tS.specA.keepBit b == 1
  then tS.segA.states.getD (b + 1) [] == tS.segA.afters.getD b []
  else tS.segA.states.getD (b + 1) [] == tS.segA.states.getD b [])
#guard (List.range tS.specA.nb).any (fun b => tS.specA.keepBit b == 1)
#guard (List.range tS.specA.nb).any (fun b => tS.specA.keepBit b == 0)
-- …and a masked-out block's DISCARDED permutation output is genuinely different from the state it
-- keeps, so the mux is deciding something.
#guard (List.range tS.specA.nb).all (fun b =>
  tS.specA.keepBit b == 1 || tS.segA.afters.getD b [] != tS.segA.states.getD b [])

end Dregg2.Circuit.Emit.KimchiStepMain
