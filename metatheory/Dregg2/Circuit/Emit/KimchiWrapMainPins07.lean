/-
# Dregg2.Circuit.Emit.KimchiWrapMainPins07 — §17b — W-FTCOMM

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

/-! ### §17b — ⚑ **W-FTCOMM'S PINS, AS NAMED THEOREMS.**

⚠ These are deliberately written so the KERNEL never reduces a ladder. A `scale_fast` ladder is 255
`stepVbmQ`s and each is three `qInv`s; the smoke shape runs five of them once `ftcResVal`'s recursion
is counted. `List.length` and a `kind`/`perm` filter reduce the list SPINE only — the accumulator and
slope values live in `advice` and stay unforced — so the row pins are cheap, and every pin that
needs a VALUE is stated over the scalars, which are plain `Nat`. No new `#guard`s. -/

/-- ⚑ **`scale_fast`'s CHUNK COUNT IS A DIVISION, NOT A ROUNDING — AND THE TWO AGREE ONLY HERE.**
`scale_fast_unpack` takes `num_bits / bits_per_chunk` under a `[%test_eq]` that the remainder is
zero (`plonk_curve_ops.ml:149-151`); `scale_fast2` takes `chunks_needed ~num_bits:(n−1)`, which
rounds UP (`:66-70,254-256`). At 255 both are 51, which is why the `408 = 8 × 51` census is
insensitive to the confusion §13 item 4 shipped. At 128 they are 25 and 26 — the pin names a width
where the two disagree, so it cannot be satisfied by a definition that quietly used the other one. -/
theorem ftc_chunks_is_exact_division_and_that_matters :
    FTC_CHUNKS = 51
    ∧ FTC_BITS % BITS_PER_CHUNK = 0
    ∧ FTC_CHUNKS = chunksNeededQ (FTC_BITS - 1)
    ∧ 128 / BITS_PER_CHUNK ≠ chunksNeededQ (128 - 1) := by
  refine ⟨rfl, rfl, rfl, by decide⟩

/-- ⚑ **THE LADDER CENSUS, AND THE `408` IT CLOSES.** `tComms + 1` ladders, `51` chunks each, two
rows per chunk. At the committed wrap shape that is `8 × 51 = 408` `VarBaseMul` rows — exactly
`wrap-transaction`'s `VarBaseMul 2417` minus W-XHAT's `1805` and W-BULLET's `204`. -/
theorem ftc_ladder_census :
    ftcLadders shapeWrap = 8
    ∧ ftcLadders shapeSmoke = 3
    ∧ ftcLadders shapeWrap * FTC_CHUNKS = 408
    ∧ 1805 + ftcLadders shapeWrap * FTC_CHUNKS + 204 = 2417 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- ⚑ **THREE SCALAR VARIABLES, EIGHT LADDERS.** `common.ml:247-251` scales by
`plonk.zeta_to_srs_length` on EVERY fold iteration, so `tComms − 1` ladders assert `n_acc` against
ONE variable. A layout that gave each ladder its own scalar cell would be a different circuit — six
independent witnesses where upstream has one. -/
theorem ftc_six_fold_ladders_share_one_scalar :
    ((List.range (ftcLadders shapeWrap)).map (ftcScalarIdx shapeWrap))
      = [0, 1, 1, 1, 1, 1, 1, 2]
    ∧ ((List.range (ftcLadders shapeSmoke)).map (ftcScalarIdx shapeSmoke)) = [0, 1, 2] := by
  refine ⟨rfl, rfl⟩

/-- ⚑ **DEFECT CLASS 2, EXHIBITED RATHER THAN DESCRIBED.** `scale_fast` ties its 255 free bit cells
to the scalar by `Field.Assert.equal !n_acc scalar` over `Fq` and by NOTHING else — there is no
top-bit-zero loop, because `scale_fast2`'s lives in `scale_fast2` (`plonk_curve_ops.ml:262-265`).
This exhibits the second admissible bit string for one of the three actual scalars: `v` and `v + q`
are DIFFERENT 255-bit strings, both recompose faithfully, both satisfy the only constraint the
circuit imposes, and the ladder multiplies by whichever the prover supplies. It is upstream's, it is
emitted unaltered, and adding a bound here would be a divergence from `wrap_main` rather than a fix
to it. -/
theorem ftc_scale_fast_admits_two_decompositions :
    ftcRecompose (ftcBitsOf (ftcSVal 1)) = ftcSVal 1
    ∧ ftcRecompose (ftcBitsOf (ftcSVal 1 + qN)) = ftcSVal 1 + qN
    ∧ ftcSVal 1 + qN < 2 ^ FTC_BITS
    ∧ (ftcSVal 1 + qN) % qN = ftcSVal 1
    ∧ ftcBitsOf (ftcSVal 1) ≠ ftcBitsOf (ftcSVal 1 + qN) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **EVERY LADDER SEED IS PINNED — BOTH OF THEM, PER LADDER.** `acc₀ = add_fast base base` is a
`CompleteAdd` row DEFINING the accumulator, and `n₀ = 0` is a `Generic` half; `plonk_curve_ops.ml:
157-158`. Read off the emitted row list: one `n₀` half per ladder, and the seed `CompleteAdd` count
is one per ladder plus the fold's `tComms − 1` adds plus the two closing adds. -/
theorem ftc_every_ladder_seed_is_pinned :
    ((List.range (ftcLadders shapeSmoke)).all (fun l =>
      hasHalf (ftcRows tKey true) [some (ftcCnt shapeSmoke tKey.sp l 0), none, none] (cConst 0)))
      = true
    ∧ ((ftcRows tKey true).filter (fun r => r.kind == KGateType.completeAdd)).length
        = ftcLadders shapeSmoke + (shapeSmoke.tComms - 1) + 2 := by
  refine ⟨rfl, rfl⟩

/-- The gate census of the sub-circuit: two rows per five-bit chunk, no sponge, no `EndoMul`. -/
theorem ftc_gate_census :
    ((ftcRows tKey true).filter (fun r => r.kind == KGateType.varBaseMul)).length
      = ftcLadders shapeSmoke * FTC_CHUNKS
    ∧ ((ftcRows tKey true).filter (fun r => r.kind == KGateType.poseidon)).length = 0
    ∧ ((ftcRows tKey true).filter (fun r => r.kind == KGateType.endoMul)).length = 0
    ∧ ((ftcRows tKey true).filter (fun r => r.probe)).length = ftcLadders shapeSmoke + 1 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- ⚑ **THE FIRST LADDER'S BASE IS W-KEY'S SEALED OUTPUT, NOT A CONSTANT.** `sigma_comm.(6)` is
index-sponge coordinates 12 and 13, so `ft_comm` reads the variables §14's one-hot fold produced.
This is the σ tie that makes W-FTCOMM depend on the branch selection rather than on a literal.

⚑ **AND ITS VALUE IS DREGG'S OWN STEP KEY'S SINCE 2026-08-06** — `mkWrapWith` selects
`KEY_CHAIN_BRANCH`, so the point `ft_comm`'s first ladder scales is `STEP_OWN_VK_XY`'s. The third
leg is what makes the second one a measurement of the SELECTION rather than of the table: Mina's
`step-transaction` key's coordinates 12/13 are a different point, and reading them here would red. -/
theorem ftc_first_base_is_the_chosen_keys_sigma_comm_last :
    ftcBaseVar tKey 0
      = ((keyVars shapeSmoke (baseKey shapeSmoke tKey.sp)).acc 12 (shapeSmoke.branches - 1),
         (keyVars shapeSmoke (baseKey shapeSmoke tKey.sp)).acc 13 (shapeSmoke.branches - 1))
    ∧ ftcSigmaLast tKey
        = (Dregg2.Circuit.Emit.KimchiStepWrapChainKey.STEP_OWN_VK_XY.getD 12 0,
           Dregg2.Circuit.Emit.KimchiStepWrapChainKey.STEP_OWN_VK_XY.getD 13 0)
    ∧ ftcSigmaLast tKey ≠ (STEP_VK_XY.getD 12 0, STEP_VK_XY.getD 13 0) := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- The `w8_ftcomm` rung is a strict superset of `w7_split`, and `placeChecked` accepts it with no
inert public word. -/
theorem ftcomm_rung_extends_split_and_places :
    (rungRows tKey .ftcomm true).length
      = (rungRows tKey .split true).length + (ftcRows tKey true).length
    ∧ (rungRows tKey .split true).length < (rungRows tKey .ftcomm true).length
    ∧ refusalOf shapeSmoke .ftcomm (rungPub shapeSmoke .ftcomm)
        (wrapGates (rungRows tKey .ftcomm true)) = none
    ∧ inertSlotsAt shapeSmoke .ftcomm (wrapGates (rungRows tKey .ftcomm true))
        = wrapInertOk shapeSmoke .ftcomm := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  decide

/-- ⚑ **`t_comm` DOES NOT LEAVE THE UNCONSUMED CENSUS.** The MSM is emitted and the seven points are
consumed into `ft_comm` — and `ft_comm` is read by W-COMBINE and W-BULLET, which are not assembled,
so nothing downstream refuses a substituted `t_comm`. The entry is REWRITTEN, exactly as `x_hat`'s
was at `w6_xhat`; the count stays 8. -/
theorem ftcomm_does_not_move_the_unconsumed_census :
    WRAP_UNCONSUMED.length = 8
    ∧ WRAP_UNCONSUMED_KEYS.getD 4 "" = "t_comm" := by
  refine ⟨rfl, ?_⟩
  decide

end Dregg2.Circuit.Emit.KimchiWrapMain
