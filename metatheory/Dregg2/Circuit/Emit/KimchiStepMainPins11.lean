/-
`KimchiStepMain` pins — §16.

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

/-! ## §16 — R8: `finalize_other_proof`'s tail, against the value layer.

Every scalar R8 emits is pinned against the READ-ONLY `KimchiVerify` object it claims to compute, on
the SAME inputs, each with a red control that BITES. A rung that proves but computes the wrong scalar
is the failure mode this section exists to catch. -/

-- ── (a) `to_field_checked`'s CLOSING LINE — the endo lift, retiring simplification #7 ──────────
-- ⚑ The `EndoMulScalar` chain's `a₈`/`b₈` cells, combined by R2's new row, ARE
-- `ScalarChallenge::to_field(endo_r)` of the squeeze — `KimchiVerify.endoMap`, the same map
-- `MinaRealBlockTranscript.derived_zeta` checks on a real block. So `plonk.zeta`/`plonk.alpha`, ξ, r
-- and every bulletproof challenge are now the LIFTED values upstream uses, not the prechallenges.
#guard (List.range shapeSmoke.chals).all (fun c =>
  ((liftOf shapeSmoke tS.sp c : Nat) : ZMod pN)
    == Dregg2.Circuit.Emit.KimchiVerify.endoMap ((ENDO_R : Nat) : ZMod pN)
         (chalOf shapeSmoke tS.sp c))
-- …and it BITES on the constant: the BASE endo `FT_ENDO` in place of the SCALAR endo `endo_r` — the
-- exact cube-root conflation `MinaWrapFtEval0Weld` closed — gives a different lift.
#guard (((liftOf shapeSmoke tS.sp 0 : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.endoMap ((FT_ENDO : Nat) : ZMod pN)
              (chalOf shapeSmoke tS.sp 0)) == false
#guard ENDO_R != FT_ENDO
-- …and on the challenge: challenge 1's lift is not challenge 0's.
#guard (((liftOf shapeSmoke tS.sp 0 : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.endoMap ((ENDO_R : Nat) : ZMod pN)
              (chalOf shapeSmoke tS.sp 1)) == false
-- …and the lift is NOT the identity on any challenge (a degenerate endo would make the pin vacuous).
#guard (List.range shapeSmoke.chals).all (fun c =>
  liftOf shapeSmoke tS.sp c != chalOf shapeSmoke tS.sp c)

-- ── (b) `b_correct` — BOTH legs (`step_verifier.ml:1124-1128`) ────────────────────────────────
-- ⚑ `b_actual = challenge_poly ζ + r · challenge_poly ζω`. `KimchiVerify.ipaB0` is exactly
-- `bEval ζ + evalscale · bEval ζω`; `bEvalSq` is its ladder form (`bEvalSq_eq_bEval`, a theorem for
-- every CommRing), which is what runs at `ZMod pN`. The `+ r·…` leg is the one the module header
-- named as ABSENT — it is here, and it is this value.
#guard ((finVal finS.fp.slots.bActual : Nat) : ZMod pN)
        == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) usS
           + ((rLS : Nat) : ZMod pN)
             * Dregg2.Circuit.Emit.KimchiVerify.bEvalSq
                 (((fMul FT_OMEGA zetaLS : Nat) : ZMod pN)) usS
-- …and the compiled slot IS the direct computation (the program is a compiler, not an oracle).
#guard finVal finS.fp.slots.bActual == finS.bActual
#guard finVal finS.fp.slots.zetaw == fMul FT_OMEGA zetaLS
-- ⚑ …and the SECOND leg is load-bearing: dropping it (i.e. `b(ζ)` alone) is a DIFFERENT value.
#guard (((finVal finS.fp.slots.bActual : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) usS) == false
-- ⚑ …and ζω really is ω·ζ, not ζ: evaluating the second polynomial at ζ moves the answer.
#guard (((finVal finS.fp.slots.bActual : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) usS
            + ((rLS : Nat) : ZMod pN)
              * Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) usS) == false
-- ⚑ …and the RAW prechallenges in place of the lifted ones move it (so (a) is load-bearing HERE).
#guard (((finVal finS.fp.slots.bActual : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN)
              ((List.range shapeSmoke.bRounds).map
                 (fun k => ((chalOf shapeSmoke tS.sp (shapeSmoke.uChal k) : Nat) : ZMod pN)))
            + ((rLS : Nat) : ZMod pN)
              * Dregg2.Circuit.Emit.KimchiVerify.bEvalSq
                  (((fMul FT_OMEGA zetaLS : Nat) : ZMod pN))
                  ((List.range shapeSmoke.bRounds).map
                     (fun k => ((chalOf shapeSmoke tS.sp (shapeSmoke.uChal k) : Nat) : ZMod pN)))) == false
-- ⚑ …and — since §8g — the `r` that weights the second leg is `endoMap` of the fr-sponge's SECOND
-- squeeze, so BENDING THAT SQUEEZE MOVES `b_actual` too. This is #10's red control on the
-- `b_correct` side: the value is derived from the sponge, not fixed by the transcript.
#guard (((finVal finS.fp.slots.bActual : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) usS
            + foldMulOf (sq2S + 1)
              * Dregg2.Circuit.Emit.KimchiVerify.bEvalSq
                  (((fMul FT_OMEGA zetaLS : Nat) : ZMod pN)) usS) == false
-- …and the RETIRED reading (the second-to-last transcript challenge) also moves it.
#guard (((finVal finS.fp.slots.bActual : Nat) : ZMod pN)
         == Dregg2.Circuit.Emit.KimchiVerify.bEvalSq ((zetaLS : Nat) : ZMod pN) usS
            + ((liftOf shapeSmoke tS.sp (shapeSmoke.chals - 2) : Nat) : ZMod pN)
              * Dregg2.Circuit.Emit.KimchiVerify.bEvalSq
                  (((fMul FT_OMEGA zetaLS : Nat) : ZMod pN)) usS) == false
-- …and neither b-polynomial is the trivial product.
#guard finS.bActual != 0 && bwOf shapeSmoke tS.sp != 1

-- ── (c) The THREE `Shifted_value.Type1.to_field` unshifts, and the FIELD KEY ───────────────────
-- ⚑ The shift constants are what `Shift.create (module Fp)` builds: `c = 2^255 + 1` and `½`.
#guard ((SHIFT_C : Nat) : ZMod pN) == (2 : ZMod pN) ^ 255 + 1
#guard 2 * SHIFT_INV2 % pN == 1
-- ⚑ Type1 ROUND-TRIPS, so the encoding is an encoding and not a digest.
#guard unshiftT1 (shiftT1 (finS.bActual)) == finS.bActual
#guard unshiftT1 (shiftT1 7) == 7 && unshiftT1 (shiftT1 (pN - 1)) == pN - 1
-- ⚑ **THE FIELD KEY IS LOAD-BEARING.** A Type2 reading (subtract-only, `x − 2^255`, the STEP
-- statement's own `fq` block, `impls.ml:135`) and the raw unshifted value BOTH diverge from the
-- Type1/`Fp` reading these three words wear. Getting this wrong misencodes SILENTLY.
#guard shiftT1 finS.bActual != shiftT2 finS.bActual
#guard shiftT1 finS.bActual != finS.bActual
#guard unshiftT1 (shiftT2 finS.bActual) != finS.bActual
-- ⚑ …and the circuit's own emitted unshift slots hit the three actual values.
#guard finVal finS.fp.slots.cipUsed == tS.df.ca.getLastD 0
#guard finVal finS.fp.slots.bUsed == finS.bActual
#guard finVal finS.fp.slots.permUsed == ftS.vals.getD ftS.fp.slots.perm 0
/-- …and `combined_inner_product` really is the value R5's Horner chain produced, which §12 already
pinned against `KimchiVerify.cipR`. So the unshift lands on `cipR`, not on a local name for it.
⚑ …over the SLOTS `combine` KEEPS, since 2026-08-02: §12l's mux drops prefix slot 0 and a dropped
slot consumes NO ξ power (`common.ml:271`), so the STATEMENT word R8 binds is the MASKED fold. Stated
against `cipRKept MASK_BITS` — §12l's own definition at the deployed mask — rather than a hand-copied
`.drop 1`, so the two sections cannot drift apart on what "kept" means. -/
theorem cipUsed_is_the_masked_fold :
    ((finVal finS.fp.slots.cipUsed : Nat) : ZMod pN) = cipRKept MASK_BITS := by native_decide
#assert_compiled cipUsed_is_the_masked_fold

/-- ⚑ …and the UNMASKED fold — which this pin carried until the mux landed — is a DIFFERENT field
element. Both directions, so the `.drop` is not decoration. -/
theorem cipUsed_is_not_the_unmasked_fold :
    (((finVal finS.fp.slots.cipUsed : Nat) : ZMod pN) == cipRFull) = false := by native_decide
#assert_compiled cipUsed_is_not_the_unmasked_fold

-- ── (d) `xi_correct` — the fr-sponge's own squeeze ────────────────────────────────────────────
-- ⚑ `xi_actual = lowest_128_bits (squeeze sponge)` (`step_verifier.ml:820-822,1102`), and the
-- squeeze is R7 segment B's — an assembly variable, not a fixture.
#guard finVal finS.fp.slots.xiActual == finS.xiStmt
#guard finS.xiStmt == Dregg2.Circuit.Emit.KimchiVerify.low128 (frSqueezeVal tS.segB tS.specB)
#guard finS.xiStmt < 2 ^ 128
-- …and the squeeze is NOT already 128 bits (so the decomposition is doing work).
#guard finS.xiHi != 0
-- …and it is NOT any R1 transcript squeeze: the two sponges are different objects, which is why the
-- check is a check.
#guard (List.range shapeSmoke.chals).all (fun c =>
  finS.xiStmt != chalOf shapeSmoke tS.sp c)
-- ⚑ **AND THIS WORD FEEDS THE FOLD** (simplification #10, retired). `xi_correct` ties the statement
-- ξ word to this squeeze, and §8g's chain 0 lifts THAT WORD into the multiplier `cipRows` Horners
-- over — upstream's `let xi_correct = … in let xi = scalar xi` (`step_verifier.ml:1010-1012`). So a
-- prover cannot move the fold's ξ without failing `xi_correct`, and cannot satisfy `xi_correct`
-- without the fold's ξ being `endoMap` of the fr-sponge's squeeze.
#guard ((xiFoldS : Nat) : ZMod pN)
        == Dregg2.Circuit.Emit.KimchiVerify.endoMap ((ENDO_R : Nat) : ZMod pN) finS.xiStmt
#guard tS.defc.pre.getD 0 0 == finS.xiStmt

-- ── (e) `Boolean.all` and the `should_verify` mux ─────────────────────────────────────────────
-- ⚑ ALL FOUR legs are 1 on the honest instance, the conjunction is 1, and the muxed output is 1 —
-- which is the value the rung's last row ASSERTS.
#guard [finVal finS.fp.slots.xc, finVal finS.fp.slots.bc, finVal finS.fp.slots.cc,
        finVal finS.fp.slots.pc, finVal finS.fp.slots.finalized, finVal finS.fp.slots.out]
        == [1, 1, 1, 1, 1, 1]

-- ⚑ **THE RED CONTROLS BITE, ONE PER DEFERRED WORD.** Bend the statement's `combined_inner_product`,
-- its `b`, its `plonk.perm` or its `xi` by ONE, give the equality gadget the witnesses an honest
-- prover would then have to give, and the assert `out = 1` FAILS. That is the whole point of the
-- rung: the deferred values BIND.
#guard (List.range 4).all (fun i => finOutBent i 1 != 1)
-- …and the UNBENT re-run through the same helper is 1, so the reds are about the bend.
#guard finVal finS.fp.slots.out == 1
-- ⚑ **BOTH BRANCHES OF THE `should_verify` MUX OCCUR.** With `should_verify = 0` the dummy path
-- accepts the very same bent statement — `verified && finalized ||| not should_verify`
-- (`step_main.ml:121`). A mux with one reachable branch is decoration.
#guard (List.range 4).all (fun i => finOutBent i 0 == 1)

-- ── (g) ⚑ `should_verify` IS A STATEMENT WORD, NOT A WITNESS ───────────────────────────────────
-- ⚑ THE HOLE THIS CLOSES, exhibited by the two lines above. `should_verify = 0` makes R8's assert
-- pass with ALL FOUR deferred legs false — so while it was an `AOp.wit` with no defining row, a
-- prover simply set it to 0 and `finalize_other_proof`'s tail bound NOTHING. That is not upstream:
-- `step_main.ml:36-37` asserts `unfinalized.should_finalize = should_verify`, and `should_finalize`
-- is in the Per_proof statement's `bool` list (`composition_types.ml:1219,1310`), i.e. PUBLIC.
-- It is now the assembly's tenth statement word and its FIFTH public word, so choosing the dummy
-- branch is a claim the consumer READS.
#guard (exposedVars shapeSmoke).getD 4 (xv 0) == vShouldVerify shapeSmoke
#guard (exposedVars shapeStep).getD 4 (xv 0) == vShouldVerify shapeStep
-- …its class is R8's five reads — the booleanity square (two cells), the `= sv` assert, the mux
-- multiply and the `1 − sv` — PLUS the closing public tie. Equality, so the tie's deletion (which
-- is the whole content of the fix) moves it: as a witness it was these five and no public cell.
#guard (classCells posS (vShouldVerify shapeSmoke)).length == 6
-- …and it is in `finInputEnv`, i.e. R8 reaches it as an `.inp` and not as a private cell.
#guard (finS.fp.prog.toList.filter (fun o => o == AOp.inp (vShouldVerify shapeSmoke))).length == 1
-- …and NO `.wit` slot of R8's program holds it any more. The witnesses that remain are exactly the
-- four `Field.equal` inverse/bit pairs, `lowest_128_bits`' high part (range-checked by §12c′'s
-- chain) and #11's `verified` bit — which is the honest census of what R8 still takes on trust.
#guard (finS.fp.prog.toList.filter (fun o =>
          match o with | .wit _ => true | _ => false)).length == 4 * 2 + 1 + 1

-- ── (f) NO FREE VARIABLE reaches the public vector ────────────────────────────────────────────
-- ⚑ Every exposed variable's copy class has a cell OUTSIDE its closing row, i.e. some row COMPUTES
-- it. This is the shape of the defect that hid `cipRows`: a public word tied to a variable no gate
-- writes passes every probe and every control while binding nothing.
#guard (exposedVars shapeSmoke).all (fun v => (classCells posS v).length ≥ 2)
-- …and the four STATEMENT words are among them, each reaching R8's rows.
#guard (classCells posS (vCipShift shapeSmoke)).length ≥ 2
#guard (classCells posS (vBShift shapeSmoke)).length ≥ 2
#guard (classCells posS (vPermShift shapeSmoke)).length ≥ 2
#guard (classCells posS (vXiStmt shapeSmoke)).length ≥ 2
-- …and every `.inp` source of R8's program is a variable the assembly's OTHER rows carry, so the
-- rung reads the assembly rather than a private island.
#guard (finS.fp.prog.toList.filterMap (fun o =>
          match o with | .inp v => some v | _ => none)).all
        (fun v => (classCells posS v).length ≥ 2)
#guard (finS.fp.prog.toList.filter (fun o =>
          match o with | .inp _ => true | _ => false)).length ≥ 10
-- …and R8's program is a real program, not a stub.
#guard finS.fp.prog.size ≥ 80

end Dregg2.Circuit.Emit.KimchiStepMain
