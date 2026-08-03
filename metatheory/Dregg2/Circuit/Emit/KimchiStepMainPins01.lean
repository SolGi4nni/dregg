/-
`KimchiStepMain` pins — §12.

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

/-! ## §12 — the in-CI pins, on the SMOKE instance (`#guard`, interpreter-reduced).

The committed step-scale instance is emitted and PROVED by the harness; these pins run in `lake
build` and cover every structural property the harness cannot see.

⚠ **MEASURED 2026-08-02, and it CORRECTS what this banner used to say** ("nullary `def`s so the
interpreter evaluates the chains ONCE"): a nullary `def` is **not** cached across `#guard` COMMANDS.
`#guard` compiles and interprets its term afresh every time, so `tS`/`placedS`/`witS` are rebuilt
once per pin — 77 pins here, ~1.4 s each. Sharing happens only WITHIN one command. That is why the
pins are split across thirteen PARALLEL modules rather than batched into fewer commands: batching
buys the same factor and costs each pin its own failure site. -/

-- ── Structure ────────────────────────────────────────────────────────────────────────────────
#guard shapeSmoke.blocks == shapeSmoke.absorbs + shapeSmoke.chals
#guard placedS.length == totalRowsS
#guard placedUS.length == totalRowsS
#guard (placedS.map (fun g => g.wires.length)).all (· == 7)
#guard witS.length == 15
#guard (witS.map (·.length)).all (· == totalRowsS)

-- ⚑ THE PLACEMENT DID NOT REFUSE. `placeChecked` is the fail-closed door: `auxOverlapsPublic`
-- cannot fire (AUX = 67 ≥ pubWords), `referenceInGap` cannot (every circuit id is ≥ AUX), and
-- `inertPublicWord` is the LIVE gate — it fires unless the closing rows read all `pubWords` words.
#guard refusalOf pubS gatesS == none
#guard inertPublicWords pubS gatesS == []
-- …and it CAN refuse: declare a wider public input than the closing rows read and word `pubWords`
-- is reported inert rather than silently pinned (the `PRIMARY_LEN` 67-vs-40 shape, in miniature).
#guard match refusalOf (pubS + 3) gatesS with
       | some (.inertPublicWord i) => i == pubS | _ => false

-- ⚑ SEVEN GATE TYPES in one circuit — the census. Eleven `Poseidon` rows per sponge block, which
-- is upstream's own run length (`sponge_inputs.ml:47-64` / `plonk_constraint_system.ml:1450-1530`,
-- and MEASURED in Mina's `step-zkapp-proved` blob: every `Poseidon` run there is exactly 11).
-- FIVE sponges now: R1's transcript sponge and R7's FOUR absorption segments — **plus the ONE
-- extra permutation §3c's `index_digest` is**, `Sponge.squeeze_field (Sponge.copy
-- sponge_after_index)`, which is why the `+ 1` is here and not hidden in a segment's block count.
#guard (placedS.filter (fun g => g.kind == KGateType.poseidon)).length
        == 11 * (shapeSmoke.blocks + tS.specA.blocks + tS.specB.blocks + tS.specC.blocks
                 + tS.specD.blocks + 1)
-- ⚑ `2·chals + 5` `to_field_checked` chains, 8 `EndoMulScalar` rows each — and the composition of
-- that number IS the ledger of two retirements. Per transcript challenge TWO chains: the challenge
-- itself and `lowest_128_bits`' `assert_128_bits hi` (#1). Plus §8g's ξ (one, no split) and its r
-- (two: the challenge and its high part). Plus R8's own `lowest_128_bits` of the fr-sponge's FIRST
-- squeeze — TWO, because `Opt_sponge.squeeze_challenge` passes `~constrain_low_bits:true` and
-- `util.ml:98-99` then asserts BOTH parts. Upstream's own arithmetic, `squeeze_challenge` +
-- `squeeze_scalar`.
#guard (placedS.filter (fun g => g.kind == KGateType.endoMulScalar)).length
        == (2 * shapeSmoke.chals + 5) * shapeSmoke.emsRows
-- …stated the other way, so a chain that vanished cannot hide inside the arithmetic: the range
-- chains are `chals + 3` of the total.
#guard ((List.range shapeSmoke.chals).flatMap
          (fun c => rangeRows shapeSmoke c (vHi shapeSmoke c) (hiOf shapeSmoke tS.sp c) true)).length
        == shapeSmoke.chals * (shapeSmoke.emsRows + 6)
#guard (rangeRows shapeSmoke (shapeSmoke.chals + 1) (vDHi shapeSmoke 1)
          (tS.defc.hi.getD 1 0) true).length == shapeSmoke.emsRows + 6
-- ⚑ …and R8's TWO, which is the third `lowest_128_bits` in the assembly. Stated as an EQUALITY on
-- the emitted sub-list: `finRows` is `aRows` + these two chains + three probes, so a deleted chain
-- moves this number rather than hiding behind another consumer of the same variable.
#guard (finRows shapeSmoke tS.ft tS.fin true).length
        == (aRows (baseFin shapeSmoke tS.ft) tS.fin.fp.prog).length
           + 2 * (shapeSmoke.emsRows + 6) + 3
#guard nRng shapeSmoke == shapeSmoke.chals + 4
#guard RNG_FIN_LO shapeSmoke == RNG_FIN_HI shapeSmoke + 1
-- ⚑ `VarBaseMul` is R3's `multiscale_known` AND §6b's `ft_comm` — the second MSM runs at
-- `FTC_CHUNKS = 51`, `step_verifier.ml:240-242`'s uniform 255 bits, not at `msmChunks`.
#guard (placedS.filter (fun g => g.kind == KGateType.varBaseMul)).length
        == shapeSmoke.msmTerms * shapeSmoke.msmChunks
           + ftcTerms shapeSmoke * FTC_CHUNKS
-- ⚑ `EndoMul` is `ipaRounds` fold ladders PLUS ONE — `check_bulletproof`'s `Scalar_challenge.endo q
-- c` (`:326`), the consumer that makes `delta` and the last squeeze mean something.
#guard (placedS.filter (fun g => g.kind == KGateType.endoMul)).length
        == (shapeSmoke.ipaRounds + 1) * shapeSmoke.ipaBlocks
-- …and `CompleteAdd` is the two summation chains, R3's OWN `add_fast base base` per term (§12f,
-- new 2026-08-02) and §6b's: per `scale_fast2` the initial `add_fast base base` and the odd-branch
-- `add_fast h (negate g)` (`plonk_curve_ops.ml:157,267`), then `common.ml`'s own `tCommN + 1` adds.
-- ⚑ The fold chain is `ipaRounds` adds and not `ipaRounds − 1` since the `~init` wiring (`:606`),
-- and the tail adds three: `endo`'s two seed `add_fast`s and the closing `cq + delta` (`:327`).
#guard (placedS.filter (fun g => g.kind == KGateType.completeAdd)).length
        == (shapeSmoke.msmTerms - 1) + shapeSmoke.msmTerms
           + shapeSmoke.ipaRounds + 2 * shapeSmoke.ipaRounds + 3
           + 2 * ftcTerms shapeSmoke + (tCommN shapeSmoke + 1)
-- ⚑ …and every `CompleteAdd` is still followed by a row of another kind, which is why the shape
-- diff's `CompleteAdd` family stays `1×n`: R3's seed row is preceded by a `Zero` probe (or the pin
-- block) and followed by its ladder's first `VarBaseMul`.
#guard ((List.range nRowsS).filter (fun i =>
          (rowsS.getD i default).kind == KGateType.completeAdd
          && (rowsS.getD (i + 1) default).kind == KGateType.completeAdd)) == []
-- Generic = the pubWords public rows `place` emits + the circuit's own generic rows.
#guard (placedS.filter (fun g => g.kind == KGateType.generic)).length ≥ pubS

-- The public rows ARE kimchi's `Pub` gates (`constraints.rs:420-423` errors `IncorrectPublic`
-- on anything else; `generic.rs:297-304` then reads the row as `w₀[r] − pᵣ = 0`).
#guard ((placedS.take pubS).map (fun g => (g.kind.ordinal, g.coeffs))).all
        (· == (1, ([1, 0, 0, 0, 0] : List Int)))

-- ── The copy-permutation, ON THE EMITTED OBJECT ───────────────────────────────────────────────
-- ⚑ σ IS A PERMUTATION of all `7 · totalRows` cells, WITH `pubSize > 0`.
#guard sortCells (allWires placedS) == sortCells (allCells totalRowsS)
#guard sortCells (allWires placedUS) == sortCells (allCells totalRowsS)

-- ⚑ THE COMPOSED GRID SATISFIES σ, against `place`'s ACTUAL permutation.
#guard pairsS.all (fun pr => gridAt witS pr.1 == gridAt witS pr.2)
#guard pairsUS.all (fun pr => gridAt witS pr.1 == gridAt witS pr.2)

-- ⚑ THE PUBLIC VECTOR IS witness column 0's prefix (`prover.rs:270`) — a fixture that got this
-- wrong would force the harness to re-derive the public input in Rust, i.e. author the witness.
#guard (witS.headD []).take pubS == stepPublic tS
#guard (stepPublic tS).length == pubS
#guard (exposedVars shapeSmoke).length == pubS
-- …and the exposed variables are DISTINCT, so 67 public words tie 67 different circuit values.
#guard ((exposedVars shapeSmoke).map varIx).dedup.length == pubS
-- ⚑ …AT THE COMMITTED SHAPE TOO. The smoke shape takes 12 of a 25-long list and so cannot see a
-- collision that only appears past word 12; this is the pin that does. (It found one: `vAcc bRounds`
-- and `vZ bRounds` were each exposed twice at `pubWords = 67`.)
#guard ((exposedVars shapeStep).map varIx).dedup.length == shapeStep.pubWords
#guard (exposedVars shapeStep).length == shapeStep.pubWords

-- ── The CROSS-SUB-CIRCUIT WIRES (the claim this file exists to make) ───────────────────────────
-- ⚑ ONE VARIABLE, THREE GATE TYPES. Challenge `c`'s value cell is in the `EndoMulScalar` chain
-- (col 1 of its last row), in the `Generic` decomposition row, and — for the terms/rounds that
-- consume it — in a `VarBaseMul` row (col 5) and an `EndoMul` tail `Zero` row (col 6). So the σ
-- class of `vN c emsRows` is genuinely cross-gate and cross-sub-circuit.
#guard (classCells posS (vN shapeSmoke 0 shapeSmoke.emsRows)).length ≥ 4
#guard (classCells posS (vN shapeSmoke 1 shapeSmoke.emsRows)).length ≥ 4
-- ⚑ THE SPONGE STATE CROSSES BLOCKS. Block b's output lane 0 is read by block b+1's absorb row
-- (or its permutation row 0) — a cross-row class no `KimchiRenderPoseidon` rung had.
#guard (classCells posS (vSt shapeSmoke 1 0)).length ≥ 2
#guard (classCells posS (vSt shapeSmoke 2 2)).length ≥ 2
-- ⚑ THE ENDO ROW-OVERLAP: a mid-chain endo accumulator is ONE cell (block e's `Next` col 4 IS
-- block e+1's `Curr` col 4), so σ self-wires it and two `EndoMul` gates read that one cell.
#guard (classCells posS (ipx shapeSmoke (qAcc shapeSmoke 0 3))).length == 1
-- Cross-ROW σ pairs — the cross-gate wiring count; removing the probes costs some of them.
#guard (pairsS.filter (fun pr => pr.1.row != pr.2.row)).length
        > (pairsUS.filter (fun pr => pr.1.row != pr.2.row)).length

-- ⚑ THE WIRED/UNWIRED DIFFERENCE IS EXACTLY THE PROBES: every probe cell is in a σ cycle in the
-- WIRED circuit and self-wired (in NO cycle) in the UNWIRED one.
#guard (rungProbeRows tS .opening).all (fun r => permLookup pairsS ⟨r, 0⟩ != (⟨r, 0⟩ : Cell))
#guard (rungProbeRows tS .opening).all (fun r => permLookup pairsS ⟨r, 1⟩ != (⟨r, 1⟩ : Cell))
#guard (rungProbeRows tS .opening).all (fun r => permLookup pairsUS ⟨r, 0⟩ == (⟨r, 0⟩ : Cell))
#guard (rungProbeRows tS .opening).all (fun r => permLookup pairsUS ⟨r, 1⟩ == (⟨r, 1⟩ : Cell))
#guard (rungProbeRows tS .opening).length ≥ 10

-- ⚑ IT CAN GO RED. Desync ONE mid-chain probe cell and the σ check FAILS, so the `= true` above
-- is a gate rather than a tautology. (`toGrid` is first-wins, so the prepended override lands.)
#guard
  (let probe := (rungProbeRows tS .opening).getD ((rungProbeRows tS .opening).length / 2) 0
   let ix := envIndex (stepEnv tS)
   let broken := Dregg2.Circuit.Emit.WitnessBuilder.toGrid 15 totalRowsS
     (((⟨probe, 0⟩ : Cell), (7 : Int))
      :: ((List.range pubS).map (fun i => ((⟨i, 0⟩ : Cell), envLookupAt ix (.external i))))
      ++ ((rowsS.zip (List.range nRowsS)).flatMap (fun ri =>
           gateVarWitnessAt ix (pubS + ri.2)
             { kind := ri.1.kind, permVars := ri.1.perm, coeffs := ri.1.coeffs }
           ++ ri.1.advice.map (fun cv => ((⟨pubS + ri.2, cv.1⟩ : Cell), cv.2)))))
   (pairsS.all (fun pr => gridAt broken pr.1 == gridAt broken pr.2)) == false)

-- ── The GATE constraints, evaluated ON THE ASSEMBLED GRID ─────────────────────────────────────
-- ⚑ NON-VACUITY IN LEAN, per gate type: every emitted row satisfies the SAME constraint bodies the
-- real proof uses (`KimchiVerify`, read-only), over `ZMod pN`, read out of the COMPOSED grid. A
-- placement bug that never reaches the grid cannot hide from these.

#guard ((List.range nRowsS).filter (fun i => (rowsS.getD i default).kind == KGateType.varBaseMul)).all
  (fun i => (varBaseMulConstraints (R := ZMod pN)
      ((gridRow witS (pubS + i)).map (fun n => (n : ZMod pN)))
      ((gridRow witS (pubS + i + 1)).map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0)))

#guard ((List.range nRowsS).filter (fun i => (rowsS.getD i default).kind == KGateType.completeAdd)).all
  (fun i => (completeAddConstraints (R := ZMod pN)
      ((gridRow witS (pubS + i)).map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0)))

#guard ((List.range nRowsS).filter (fun i => (rowsS.getD i default).kind == KGateType.endoMul)).all
  (fun i => (endoMulConstraints (R := ZMod pN) (KimchiRenderEndoMul.endo : ZMod pN)
      ((gridRow witS (pubS + i)).map (fun n => (n : ZMod pN)))
      ((gridRow witS (pubS + i + 1)).map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0)))

-- ── The SEMANTICS ─────────────────────────────────────────────────────────────────────────────
-- ⚑ THE SPONGE IS THE REAL SPONGE. Each block's output equals `PastaPoseidon.Ref.perm` of its
-- input — the same reference whose `Ref.hash` reproduces the o1js `Poseidon.hash` gold KATs.
#guard (List.range shapeSmoke.blocks).all (fun b =>
  let pre := tS.sp.states.getD b []
  let ms := tS.sp.msgs.getD b []
  let post := if (blockAbs shapeSmoke b).isSome then
      [ (pre.getD 0 0 + ms.getD 0 0) % pN, (pre.getD 1 0 + ms.getD 1 0) % pN, pre.getD 2 0 ]
    else pre
  tS.sp.states.getD (b + 1) [] == Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm post)

-- ⚑ THE CHALLENGE CHAIN RECONSTRUCTS ITS CHALLENGE: the `EndoMulScalar` folds' final `n₈` IS the
-- low-128-bit squeeze, and the decomposition row's identity `squeeze = n₈ + 2¹²⁸·hi` holds.
#guard (List.range shapeSmoke.chals).all (fun c =>
  ((emsAccs shapeSmoke (chalOf shapeSmoke tS.sp c)).getLastD (0,2,2)).1
    == chalOf shapeSmoke tS.sp c)
#guard (List.range shapeSmoke.chals).all (fun c =>
  (tS.sp.states.getD (sqBlock shapeSmoke c + 1) []).getD 0 0
    == chalOf shapeSmoke tS.sp c + 2 ^ shapeSmoke.chalBits * hiOf shapeSmoke tS.sp c)
-- ⚑ …and every emitted `EndoMulScalar` ROW satisfies the gate's own eleven constraints on the
-- ASSEMBLED grid (`endomulScalarConstraints`, read-only), with the three polynomial constants.
#guard
  (let cA : ZMod pN := (KimchiRenderEndoMulScalar.cA : ZMod pN)
   let cB : ZMod pN := (KimchiRenderEndoMulScalar.cB : ZMod pN)
   let cC : ZMod pN := (KimchiRenderEndoMulScalar.cC : ZMod pN)
   ((List.range nRowsS).filter
      (fun i => (rowsS.getD i default).kind == KGateType.endoMulScalar)).all
    (fun i => (endomulScalarConstraints (R := ZMod pN) cA cB cC
        ((gridRow witS (pubS + i)).map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0))))

-- ⚑ THE MSM SCALAR IS THE CHALLENGE. Term `i`'s var_base_mul counter chain closes on the value the
-- `EndoMulScalar` chain decoded — the σ wire, checked as an arithmetic identity too.
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  (tS.msm.terms.getD i default).ns.getLastD 0 == chalOf shapeSmoke tS.sp (shapeSmoke.msmChal i))
#guard (List.range shapeSmoke.ipaRounds).all (fun r =>
  (tS.ipa.ns.getD r []).getLastD 0 == chalOf shapeSmoke tS.sp (shapeSmoke.ipaChal r))

-- ⚑ EVERY var_base_mul BIT STEP is `accₖ₊₁ = [2]accₖ + (2bₖ−1)·T`, checked with `PastaCurve`'s
-- INDEPENDENT Jacobian double/add (a different formula family from the affine `stepVbm` that
-- produced the witness), compared without inversion by `jacEqM`.
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  let td := tS.msm.terms.getD i default
  let bits := tS.msm.bits.getD i []
  (List.range (5 * shapeSmoke.msmChunks)).all (fun k =>
    let a := td.accs.getD k (0, 0)
    let a' := td.accs.getD (k + 1) (0, 0)
    let q := if bits.getD k 0 == 1 then jOf td.T else jNeg (jOf td.T)
    jacEqM pN (jOf a') (jAdd (jDbl (jOf a)) q)))

-- ⚑ THE SCALAR CELL IS TIED TO THE POINT: with `acc₀ = [2]T` the chain closes to
-- `acc_final = [2^{5C} + 2n + 1]·T`, `n` the value in the last chunk's `n'` cell — checked against
-- `PastaCurve.scMulM`, an independent 255-bit double-and-add.
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  let td := tS.msm.terms.getD i default
  match scMulM pN (2 ^ (5 * shapeSmoke.msmChunks) + 2 * td.ns.getLastD 0 + 1) (jOf td.T) with
  | none => false
  | some R => jacEqM pN (jOf (td.accs.getLastD (0, 0))) R)

-- ⚑ EVERY endo_mul BLOCK is `accₑ₊₁ = [2]([2]accₑ + Q₁) + Q₂` with `Qₖ = ±φ^{b}(T)` — the
-- endomorphism selection included — same independent Jacobian oracle.
#guard (List.range shapeSmoke.ipaRounds).all (fun r =>
  let T := tS.ipa.bases.getD r (0, 0)
  (List.range shapeSmoke.ipaBlocks).all (fun e =>
    let b := (tS.ipa.blks.getD r []).getD e default
    let a := (tS.ipa.accs.getD r []).getD e (0, 0)
    let a' := (tS.ipa.accs.getD r []).getD (e + 1) (0, 0)
    let q1r : Nat × Nat := (KimchiRenderEndoMul.xqOf b.b1 T.1, T.2)
    let q2r : Nat × Nat := (KimchiRenderEndoMul.xqOf b.b3 T.1, T.2)
    let q1 := if b.b2 == 1 then jOf q1r else jNeg (jOf q1r)
    let q2 := if b.b4 == 1 then jOf q2r else jNeg (jOf q2r)
    jacEqM pN (jOf a') (jAdd (jDbl (jAdd (jDbl (jOf a)) q1)) q2)))

-- ⚑ THE ACCUMULATOR CHAINS REALLY SUM THE TERMS (Jacobian fold of all addends).
#guard
  (let pts := (List.range shapeSmoke.msmTerms).map (fun i =>
        (tS.msm.terms.getD i default).accs.getLastD (0, 0))
   let tot := (pts.drop 1).foldl (fun acc p => jAdd acc (jOf p)) (jOf (pts.getD 0 (0, 0)))
   jacEqM pN (jOf (tS.msm.sums.getLastD (0, 0))) tot)
-- ⚑ …and R4's fold starts at `sg_old[0]` (`~init`, `step_verifier.ml:606`), so the Jacobian oracle
-- is seeded there and not at round 0's output. `ipaRounds` adds, one per round.
#guard
  (let pts := (List.range shapeSmoke.ipaRounds).map (fun r =>
        (tS.ipa.accs.getD r []).getLastD (0, 0))
   let tot := pts.foldl (fun acc p => jAdd acc (jOf p))
                (jOf Dregg2.Bridge.MinaStepPrevCommitments.SG_OLD0_XY)
   jacEqM pN (jOf (tS.ipa.sums.getLastD (0, 0))) tot)
#guard tS.ipa.sums.length == shapeSmoke.ipaRounds
#guard tS.ipa.addCells.length == shapeSmoke.ipaRounds
-- ⚑ …and `check_bulletproof`'s tail really computes `endo q c + delta`: the ladder's own counter
-- closes on `c`'s challenge variable, its accumulator is `Scalar_challenge.endo`'s seed run, and the
-- closing `add_fast` is `cq + delta` over the block's own opening point.
#guard tS.ipa.lhsAccs.getD 0 (0, 0) == endoSeed (tS.ipa.sums.getLastD (0, 0))
#guard tS.ipa.lhsNs.getLastD 0 == chalOf shapeSmoke tS.sp shapeSmoke.cChal
#guard tS.ipa.lhsAccs.length == shapeSmoke.ipaBlocks + 1
#guard (List.range shapeSmoke.ipaBlocks).all (fun e =>
  let T := tS.ipa.sums.getLastD (0, 0)
  let b := tS.ipa.lhsBlks.getD e default
  let a := tS.ipa.lhsAccs.getD e (0, 0)
  let a' := tS.ipa.lhsAccs.getD (e + 1) (0, 0)
  let q1r : Nat × Nat := (KimchiRenderEndoMul.xqOf b.b1 T.1, T.2)
  let q2r : Nat × Nat := (KimchiRenderEndoMul.xqOf b.b3 T.1, T.2)
  let q1 := if b.b2 == 1 then jOf q1r else jNeg (jOf q1r)
  let q2 := if b.b4 == 1 then jOf q2r else jNeg (jOf q2r)
  jacEqM pN (jOf a') (jAdd (jDbl (jAdd (jDbl (jOf a)) q1)) q2))
#guard jacEqM pN (jOf (tS.ipa.lhsAdd.getD 4 0, tS.ipa.lhsAdd.getD 5 0))
         (jAdd (jOf (tS.ipa.lhsAccs.getLastD (0, 0)))
               (jOf Dregg2.Bridge.MinaStepPrevCommitments.DELTA_XY))
#guard onCurveA (tS.ipa.lhsAdd.getD 4 0, tS.ipa.lhsAdd.getD 5 0)

-- Every add is the distinct-x `add_fast` case (`inf = 0`, `same_x = 0`), so leaving col 6 unwired
-- at 0 is correct and no add silently lands on the point at infinity.
#guard tS.msm.addCells.all (fun c => c.getD 6 0 == 0 && c.getD 7 0 == 0)
#guard tS.ipa.addCells.all (fun c => c.getD 6 0 == 0 && c.getD 7 0 == 0)
-- Every point in every chain is on the Pallas curve.
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  ((tS.msm.terms.getD i default).accs).all onCurveA)
#guard tS.msm.sums.all onCurveA
#guard tS.ipa.sums.all onCurveA
#guard (List.range shapeSmoke.ipaRounds).all (fun r => (tS.ipa.accs.getD r []).all onCurveA)
-- The chains are non-degenerate: both bit values occur, so both slope signs / both endo branches
-- are exercised in every chain.
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  (tS.msm.bits.getD i []).contains 0 && (tS.msm.bits.getD i []).contains 1)

-- ⚑ THE DEFERRED `b(ζ)` IS THE CHALLENGE POLYNOMIAL: the assembled product equals the direct fold
-- `∏ (1 + u_k · ζ^{2^{bRounds−1−k}})`, and `ζ` IS challenge 0.
#guard tS.df.zs.getD 0 0 == liftOf shapeSmoke tS.sp shapeSmoke.zetaChal
#guard (List.range shapeSmoke.bRounds).all (fun k =>
  tS.df.zs.getD (k + 1) 0 == fMul (tS.df.zs.getD k 0) (tS.df.zs.getD k 0))
#guard tS.df.accs.getLastD 0
        == (List.range shapeSmoke.bRounds).foldl
             (fun acc k => fMul acc
               (fAdd 1 (fMul (liftOf shapeSmoke tS.sp (shapeSmoke.uChal k))
                             (tS.df.zs.getD (shapeSmoke.bRounds - 1 - k) 0)))) 1
-- …and it is NOT the trivial product (a degenerate `b` would make the rung vacuous).
#guard tS.df.accs.getLastD 0 != 1

end Dregg2.Circuit.Emit.KimchiStepMain
