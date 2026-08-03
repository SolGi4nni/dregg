/-
`KimchiStepMain` pins — §12e′ §12f §12g.

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

-- ── §12e′ — ⚠ ⚑ THE ζ-POWER COLLAPSE: NAMED AT FULL RESOLUTION, DELIBERATELY NOT HALF-FIXED ────
-- `plonk_checks.ml:496-497` computes TWO DIFFERENT values:
--     zeta_to_domain_size = env.zeta_to_n_minus_1 + F.one     -- ζ^{domain_size} of the PREVIOUS
--                                                                WRAP PROOF's own domain
--     zeta_to_srs_length  = pow2pow zeta env.srs_length_log2  -- ζ^{2^srs_length_log2}
-- and `step_verifier.ml:1053` passes `~srs_length_log2:Common.Max_degree.step_log2` = 16
-- (`common.ml:7-9`, `Backend.Tick.Rounds.n`). `Common.ft_comm` multiplies by the SECOND at every
-- Horner step and by the FIRST at the closing scale (`common.ml:251,256`), so upstream's ladder
-- reads TWO cells and this one reads ONE — `ftcScalOf` sends term `n` to the same scalar block as
-- terms `1..n−1`, because R6 is compiled at `log2n = FT_LOG2N = 16` and its `zetaN` slot therefore
-- plays both roles. The collapse is pinned as an EQUALITY here so it is a stated property of the
-- object and not a reader's inference.
#guard N_FTC_SCAL == 2
#guard ftcScalOf (tCommN shapeSmoke) == ftcScalOf 1
#guard ftcScalV tS.ftw (ftcScalOf (tCommN shapeSmoke)) == ftcScalV tS.ftw (ftcScalOf 1)
-- ⚠ …and it is WRONG AT EVERY REAL BLOCK, not fitted to one. The multi-block conformance lane
-- measures `zeta_to_srs_len` = ζ^{2^15} against `zeta_to_domain_size` = ζ^{2^14} on **5/5** devnet
-- blocks (539508 / 540890 / 540906 / 540922 / 540929). The two pins above this section already
-- REFUTE the collapse at 539508: the powers differ, and feeding `ZETA_SRS` where
-- `zeta_to_domain_size` belongs gives a point that is NOT `FT_COMM_GOLD`. So the values are
-- distinguishable and this assembly cannot distinguish them.
-- ⚑ **AND THE FIX IS NAMED PRECISELY, BECAUSE THE OBVIOUS ONE IS WRONG.** It is NOT "give `FtcWire`
-- a third slot": `srs_length_log2 = step_log2 = 16` is CORRECT here, so a `FT_SRS_LOG2` would be
-- `FT_LOG2N` again and the third slot would compute the same field element twice — a
-- partially-distinguished power that still reads one value, which LOOKS retired and is not. The
-- value that is wrong is **R6's DOMAIN**: `ftCfg`'s `log2n`, which this file sets to `FT_LOG2N = 16`
-- and a previous wrap proof sets to `2^14`. Separating the powers therefore means RE-DOMAINING R6
-- and re-welding §13's whole `ft_eval0` chain, `zkPolyR`, `omega` and `MinaWrapFtEval0` at the new
-- domain — a rung, not a hunk. Until that lands, `BRANCH_DOMAIN_LOG2 == FT_LOG2N` is the single
-- place the conflation is written down, and it is pinned.
#guard BRANCH_DOMAIN_LOG2 == FT_LOG2N
#guard FT_N == 2 ^ 16
#guard ftcSigma == ((Dregg2.Circuit.Emit.MinaWrapGroupGate.SIGMA6).1,
                    (Dregg2.Circuit.Emit.MinaWrapGroupGate.SIGMA6).2.1)

-- ⚑⚑ THE GRIND THAT WAS OPEN UNTIL THIS LANDED (§12d's shape, aimed at `t_comm`).

-- the block really is `t_comm`'s last, ζ really is the squeeze that follows it, and the helper
-- reproduces the assembly's OWN challenge on the honest word — so what follows measures the grind
-- and not a second sponge.
#guard tcOrd == oCip shapeSmoke - 1
#guard sqStBlock shapeSmoke shapeSmoke.zetaChal == tcBlk + 1
        && sqStLane shapeSmoke shapeSmoke.zetaChal == 0
#guard tCommBlock shapeSmoke tcOrd == some (tCommN shapeSmoke - 1)
#guard msgVar shapeSmoke tcOrd 1 == vTcY shapeSmoke (tCommN shapeSmoke - 1)
#guard tcChalAt tcHon == chalOf shapeSmoke tS.sp shapeSmoke.zetaChal

-- ⚑⚑ **THE GRIND SUCCEEDS.** The block's real quotient commitment MISSES the chosen target; the
-- prover finds a word that HITS it, by addition, in under 64 tries.
#guard chalOf shapeSmoke tS.sp shapeSmoke.zetaChal % GRIND_MOD != 0
#guard tcGrindT != 0
#guard tcChalAt tcGround % GRIND_MOD == 0
#guard tcGround != tcHon

-- ⚑⚑ **AND IT STEERS EVERY SQUEEZE.** One `t_comm` coordinate, chosen by the prover, and EVERY
-- transcript challenge moves — with them the x_hat MSM's scalars, the fold's weights and
-- `combined_inner_product`. That is Fiat–Shamir's INPUT becoming prover-chosen, and it is exactly
-- what absorbing `t_comm` WITHOUT consuming it would have left untouched.
-- ⚠ ⚑ …every squeeze taken AFTER the `t_comm` run, which since the R1 interleaving is ζ onwards and
-- not all of them: β, γ and α are squeezed BEFORE `receive without t_comm` (`:563-566` precede
-- `:567`), so upstream itself does not let a quotient chunk move them. Stated as the exact split
-- rather than as "every challenge", which was true only of the all-absorbs-first shape.
#guard ((List.range shapeSmoke.chals).drop shapeSmoke.zetaChal).all (fun c =>
  chalOf shapeSmoke spTc c != chalOf shapeSmoke tS.sp c)
#guard ((List.range shapeSmoke.chals).take shapeSmoke.zetaChal).all (fun c =>
  chalOf shapeSmoke spTc c == chalOf shapeSmoke tS.sp c)
#guard (spTc.states.getLastD []).getD 0 0 != (tS.sp.states.getLastD []).getD 0 0

-- ⚑ **THE HOLE, ON THE EMITTED OBJECT.** R1 itself never objects: with the ground word absorbed,
-- every sponge block is still exactly `Ref.perm` of its own absorbed state. A `Poseidon` gate
-- constrains the permutation and NOT what was fed to it, so before §6b nothing in the assembly
-- could refuse this.
#guard (List.range (tBlocks shapeSmoke)).all (fun b =>
  let pre := spTc.states.getD b []
  let ms := spTc.msgs.getD b []
  let post := [ (pre.getD 0 0 + ms.getD 0 0) % pN, (pre.getD 1 0 + ms.getD 1 0) % pN, pre.getD 2 0 ]
  spTc.states.getD (b + 1) [] == Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm post)

-- ⚑⚑ **AND THE ASSEMBLED VERSION REFUSES IT.** `t_comm` arrives through `Inner_curve.typ` now, so
-- §7b's `assert_on_curve` covers it: the row's own generic-gate body — `KimchiVerify.
-- genericGateConstraint`, read-only — is 0 on the block's real quotient commitment and NONZERO on
-- the ground one. ACCEPTED before §6b (no row read that word at all), REFUSED now.
#guard tcSqBody (ftcTc (tCommN shapeSmoke - 1)) == 0
#guard (tcSqBody ((ftcTc (tCommN shapeSmoke - 1)).1, tcGround) == 0) == false
#guard onCurveA ((ftcTc (tCommN shapeSmoke - 1)).1, tcGround) == false
-- …and the check is SATISFIABLE at every one of the seven chunks, not just the one the grind used.
#guard Dregg2.Bridge.MinaStepPrevCommitments.T_COMM_XY.all onCurveA
#guard (List.range N_TCOMM).all (fun i => tcSqBody (ftcTc i) == 0)
-- ⚑ …and §7b's rows really cover `t_comm`: the on-curve census is the fold's absorbed bases PLUS
-- the quotient chunks, and the last `tCommN` checked variables ARE `t_comm`'s.
#guard (List.range (tCommN shapeSmoke)).all (fun i =>
  onCVar shapeSmoke ((absRoundList shapeSmoke).length + i) == (vTcX shapeSmoke i, vTcY shapeSmoke i))

-- ── §12f — ⚑ R3's LADDER SEED WAS THE PROVER'S (`plonk_curve_ops.ml:157-158`, CLOSED) ──────────
-- §12b pinned R3's BASES to the SRS Lagrange constants and §12c/§12c′ closed the challenge
-- decompositions. Neither says a word about where the ladder STARTS. `scale_fast_unpack` opens with
-- TWO initialisers — `let acc = ref (add_fast base base)` (`:157`) and `let n_acc = ref Field.zero`
-- (`:158`) — and R3 emitted NEITHER, so `pAcc i 0` and `vSN i 0` were witnesses no row read. Both
-- are exhibited below on the assembly's OWN generators: the ladder's gate polynomial ACCEPTS each
-- forgery, and each of the two new rows refuses it.

-- the honest run IS the assembly's term 0, so what follows measures the forgery and not a second
-- copy of the ladder.
#guard (msmFrom msmSeedHon).accs == (tS.msm.terms.getD 0 default).accs
#guard (tS.msm.terms.getD 0 default).accs.getD 0 (0, 0) == msmSeedHon
#guard msmSeedForged != msmSeedHon
#guard onCurveA msmT0 && onCurveA msmSeedHon && onCurveA msmSeedForged
-- ⚑ the COUNTER CHAIN IS UNTOUCHED by a forged seed: the forged ladder's `n` cells are the honest
-- ones, so the σ class that closes `vSN 0 (msmChunksAt 0)` on the challenge variable — the only thing R3
-- constrained about this term — is satisfied by the forgery exactly as by the honest witness.
#guard msmForged.ns == (tS.msm.terms.getD 0 default).ns
-- ⚑⚑ **AND THE OUTPUT IS A DIFFERENT POINT.** `multiscale_known`'s result is `x_hat`: a PUBLIC word
-- (`exposedVars`) and a segment-C absorption. This is the prover choosing what the MSM returned.
#guard msmForged.accs.getLastD (0, 0) != (tS.msm.terms.getD 0 default).accs.getLastD (0, 0)

-- the cell helper reproduces the ASSEMBLY's own accepted rows on the honest term…
#guard (List.range (msmChunksAt 0)).all (fun j =>
  vbmOk (vbmChunkCells (tS.msm.terms.getD 0 default) (tS.msm.bits.getD 0 []) j))
-- ⚑⚑ **THE HOLE, ON THE EMITTED GATE POLYNOMIAL.** Every `VarBaseMul` row of the FORGED ladder
-- satisfies the same 21 constraints. A curve gate constrains the STEP and not the START, so before
-- this commit there was nothing in R3 that could refuse a chosen `acc₀`.
#guard (List.range (msmChunksAt 0)).all (fun j =>
  vbmOk (vbmChunkCells msmForged (tS.msm.bits.getD 0 []) j))

-- ⚑⚑ **AND THE ASSEMBLED VERSION REFUSES IT.** The seed row's own gate body is 0 on
-- `add_fast base base` and NONZERO on the prover's point. ACCEPTED this morning — no row read
-- `pAcc i 0` at all — REFUSED now.
#guard caOk (msmDblCellsAt msmSeedHon)
#guard caOk (msmDblCellsAt msmSeedForged) == false
-- …and the check is SATISFIABLE at every term, not just the one the exhibit used.
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  let T := (tS.msm.terms.getD i default).T
  caOk (completeAddWitness T.1 T.2 T.1 T.2))
-- …and the row is REALLY IN THE SCHEDULE, wired to the ladder's first accumulator cell: `pAcc i 0`
-- now has TWO cells (the seed row's output and chunk 0's `VarBaseMul` input) where it had one.
#guard (classCells posS (mpx shapeSmoke (pAcc shapeSmoke 0 0))).length == 2
#guard (classCells posS (mpy shapeSmoke (pAcc shapeSmoke 0 0))).length == 2
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  (classCells posS (mpx shapeSmoke (pAcc shapeSmoke i 0))).length == 2)

-- ── …AND THE SECOND WITNESS OF THE SAME TWO LINES: the counter seed (`:158`) ───────────────────

-- the trace helper reproduces the assembly's own counter chain from `n₀ = 0`…
#guard (nTraceFrom 0 (tS.msm.bits.getD 0 [])) == (tS.msm.terms.getD 0 default).ns
-- ⚑⚑ **THE FORGERY: DIFFERENT BITS, THE SAME CHALLENGE CELL.** The chain from the prover's seed
-- closes on exactly the value `vSN 0 (msmChunksAt 0)` is wired to, so `Field.Assert.equal !n_acc scalar`
-- (`:208`) — the wire R3 was relying on — is satisfied by a bit vector the prover chose.
#guard msmBitsForged != tS.msm.bits.getD 0 []
#guard msmN0Forged != 0
#guard (nTraceFrom msmN0Forged msmBitsForged).getLastD 0
        == (tS.msm.terms.getD 0 default).ns.getLastD 0
-- …and the ladder over those bits lands on a DIFFERENT point, which is the same theft as above
-- through the other cell.
#guard (runVbm msmT0 msmSeedHon msmBitsForged).accs.getLastD (0, 0)
        != (tS.msm.terms.getD 0 default).accs.getLastD (0, 0)

-- ⚑⚑ **AND `n_acc := ref Field.zero` REFUSES IT.** The pin row's own generic-gate body —
-- `KimchiVerify.genericGateConstraint`, read-only — is 0 at the constant upstream uses and NONZERO
-- at the prover's seed.
#guard msmNZeroRow0.coeffs == cConst 0 ++ cConst 0
#guard nZeroBody 0 == 0
#guard (nZeroBody msmN0Forged == 0) == false
-- …and `vSN i 0` is READ by that row for every term (two cells: the pin and chunk 0's `VarBaseMul`).
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  (classCells posS (vSN shapeSmoke i 0)).length == 2)

-- ⚑ **AND THE PIN IS WHAT FORCES THE TWO LEADING PAD BITS**, which is why `:158` is the load-bearing
-- half of the pair rather than tidiness. `chunks_needed ~num_bits:127 = 26` and `26·5 = 130`, so the
-- ladder carries TWO bits more than a challenge has. Nothing pins those two cells directly. The
-- ARGUMENT (an argument about the constraint system, not a machine-checked implication — the three
-- facts it rests on are pinned, the inference is prose): `VarBaseMul`'s own booleanity constraints
-- force every `bₖ ∈ {0,1}`; with `n₀ = 0` the counter chain gives `n_final = Σₖ bₖ·2^{129−k}`; the
-- `EndoMulScalar` chain reconstructs `n_final` from 8 rows × 8 crumbs × 2 bits with ITS OWN `n₀ = 0`
-- pin, so `n_final < 2¹²⁸`; and `2¹³⁰ < p`, so the field equation is an INTEGER one and `b₀ = b₁ = 0`
-- follows. Remove the `n₀` pin and every step of that collapses.
#guard 5 * msmChunksAt 5 == 130
#guard shapeSmoke.chalBits == 128 && shapeStep.chalBits == 128
#guard 2 ^ 130 < pN
#guard msmChunksAt 5 == (127 + 4) / 5
-- …and the endo ladder has NO pad: `4·ipaBlocks = 128` exactly, which is why §12g's leg is only
-- about the seed.
#guard 4 * shapeSmoke.ipaBlocks == shapeSmoke.chalBits
-- ⚑ …and the SAME pin now covers §6b's eight `ft_comm` ladders, which had `:157` and not `:158`:
-- `ftcN k 0` was free, so the closing `Field.Assert.equal !n_acc scalar` against R6's derived `perm`
-- / `ζ^n` cell was one equation in two unknowns and `ft_comm` was choosable the same way.
#guard (List.range (ftcTerms shapeSmoke)).all (fun k =>
  (tS.ftc.terms.getD k default).td.ns.headD 1 == 0)
#guard ((ftcNZeroRows shapeSmoke).headD default).coeffs == cConst 0 ++ cConst 0

-- ── §12g — ⚑ R4's SEED, THE THIRD REGION OF THE SAME FAMILY (`scalar_challenge.ml:230-235`) ────
-- `Scalar_challenge.endo` had BOTH free witnesses, and its point seed was also the WRONG POINT.
-- Upstream: `let p = G.( + ) t (seal (Field.scale xt Endo.base), yt) in ref G.(p + p)` and
-- `let n_acc = ref Field.zero`. `runIpa` seeded at `dblA T` — `2t`, not `2(t + φ(t))` — with
-- `qAcc r 0` and `vQN r 0` read by NO row. So the fold was self-consistent arithmetic that was not
-- `Scalar_challenge.endo`, over a starting point the prover could name.

-- ⚑ THE SEED IS THE ENDOMORPHISM'S, and it is a different point from what this file used to emit.
#guard Dregg2.Circuit.Emit.KimchiRenderEndoMul.endo != 1
#guard (endoQ (tS.ipa.bases.getD absR0 (0, 0))).1 != (tS.ipa.bases.getD absR0 (0, 0)).1
#guard (endoQ (tS.ipa.bases.getD absR0 (0, 0))).2 == (tS.ipa.bases.getD absR0 (0, 0)).2
#guard endoSeed (tS.ipa.bases.getD absR0 (0, 0)) != dblA (tS.ipa.bases.getD absR0 (0, 0))
-- …and `φ(t)` is on the curve, which is what makes `endo` the base-field endomorphism and not a
-- number: `a = 0` on Pallas, so `(ζx)³ + b = x³ + b` for a cube root of unity.
#guard (List.range shapeSmoke.ipaRounds).all (fun r =>
  onCurveA (endoQ (tS.ipa.bases.getD r (0, 0))) == onCurveA (tS.ipa.bases.getD r (0, 0)))
-- …the seed the assembly RUNS is the emitted rows' own output, round for round.
#guard (List.range shapeSmoke.ipaRounds).all (fun r =>
  (tS.ipa.accs.getD r []).getD 0 (0, 0) == endoSeed (tS.ipa.bases.getD r (0, 0)))

-- ⚑⚑ **THE SAME EXHIBIT AS §12f, ON THE ENDO LADDER.** A forged accumulator seed leaves the endo
-- gate's own eleven DEPLOYED constraints satisfied at every block — `endoMulConstraints`, read-only
-- — while the round's output moves. The counter chain is untouched, so the wire to the challenge
-- cell says nothing about it.

-- the helpers reproduce the assembly's OWN accepted rows on the honest seed…
#guard ipaAccsFrom (endoSeed ipaT0) == tS.ipa.accs.getD absR0 []
#guard (List.range shapeSmoke.ipaBlocks).all (fun e =>
  emOk (emCells (ipaBlocksFrom (endoSeed ipaT0)) (ipaAccsFrom (endoSeed ipaT0))
                (tS.ipa.ns.getD absR0 []) e))
-- ⚑⚑ …and the FORGED seed's rows are accepted just the same, with a different round output.
#guard ipaSeedForged != endoSeed ipaT0
#guard (List.range shapeSmoke.ipaBlocks).all (fun e =>
  emOk (emCells (ipaBlocksFrom ipaSeedForged) (ipaAccsFrom ipaSeedForged)
                (tS.ipa.ns.getD absR0 []) e))
#guard (ipaAccsFrom ipaSeedForged).getLastD (0, 0) != (ipaAccsFrom (endoSeed ipaT0)).getLastD (0, 0)

-- ⚑⚑ **AND THE TWO NEW `Ops.add_fast` ROWS REFUSE IT.** `acc₀ = p + p`'s own gate body is 0 at the
-- endomorphism seed and NONZERO at the prover's point.
#guard caOk (ipaDblCellsAt (endoSeed ipaT0))
#guard caOk (ipaDblCellsAt ipaSeedForged) == false
-- …and it is satisfiable at every round, both `add_fast`s.
#guard (List.range shapeSmoke.ipaRounds).all (fun r =>
  let T := tS.ipa.bases.getD r (0, 0)
  let q := endoQ T
  let p := endoP T
  caOk (completeAddWitness T.1 T.2 q.1 q.2) && caOk (completeAddWitness p.1 p.2 p.1 p.2))
-- ⚑ …and the cells that were in a ONE-cell class are not any more. `qAcc r 0`: the seed add's
-- output and block 0's `EndoMul` input. `vQN r 0`: the `Field.zero` pin and block 0's `n`.
#guard (List.range shapeSmoke.ipaRounds).all (fun r =>
  (classCells posS (ipx shapeSmoke (qAcc shapeSmoke r 0))).length == 2
  && (classCells posS (ipy shapeSmoke (qAcc shapeSmoke r 0))).length == 2
  && (classCells posS (vQN shapeSmoke r 0)).length == 2)
-- …and `φ(t)`'s x is read by its pin row and by the `p = t + φ(t)` add, nowhere else.
#guard (List.range shapeSmoke.ipaRounds).all (fun r =>
  (classCells posS (vQEndo shapeSmoke r)).length == 2)
-- ⚑ …so ALL THREE ladder regions now start where upstream starts them: R3's `multiscale_known`
-- (§12f), §6b's `ft_comm` (`:157` from the start, `:158` here) and R4's `Scalar_challenge.endo`.
#guard (List.range shapeSmoke.msmTerms).all (fun i =>
  (classCells posS (vSN shapeSmoke i 0)).length == 2)
#guard (List.range (ftcTerms shapeSmoke)).all (fun k =>
  (classCells posS (ftcN shapeSmoke k 0)).length == 2)
#guard (List.range shapeSmoke.ipaRounds).all (fun r =>
  (classCells posS (vQN shapeSmoke r 0)).length == 2)

end Dregg2.Circuit.Emit.KimchiStepMain
