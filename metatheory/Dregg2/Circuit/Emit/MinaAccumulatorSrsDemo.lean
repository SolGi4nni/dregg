/-
# `Dregg2.Circuit.Emit.MinaAccumulatorSrsDemo` — ⚑ the two inputs `-srs` is a FUNCTION of.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**No AIR is authored here.** `MinaAccumulatorAir` §10 authors every constraint and every theorem;
this module supplies the two arguments `accSrsDesc` takes and nothing else. It exists as a MODULE
rather than as lines in the emit script because two routes need the same term — `EmitByName.lean`'s
routing table and `EmitMinaAccumulator.lean`'s standalone printer — and
`reference-a-display-name-is-not-a-key` is what a second transcription of a manifest would cost.

## WHY THIS FILE IS SEPARATE FROM `MinaAccumulatorAir`

`MinaStepSrsG` is a 65 536-point decode whose `.olean` is ~289 MB. `MinaAccumulatorAir` must stay
clear of it: every theorem there is stated over an ARBITRARY generator list precisely so the AIR does
not carry the blob, and pulling the blob into the AIR module would push it into every consumer of the
accumulator cone. The blob enters here, at the emit boundary, once.

## ⚠ WHAT IS A PARAMETER CHOICE HERE, AND IT IS ALL OF IT

`demoChals` and the round count are CHOSEN. They are not a real block's `bulletproof_challenges`, and
`MinaAccumulatorAir` §10's docblock is where the cost of that is written down. What is NOT chosen is
the manifest: it is `srsScaledAddends`' image at these two inputs, and `circuit/tests/
mina_accumulator_srs_proves.rs` re-derives every entry natively from the **sha-pinned** blob.
-/
import Dregg2.Circuit.Emit.MinaAccumulatorAir
import Dregg2.Circuit.Emit.MinaStepSrsG

namespace Dregg2.Circuit.Emit.MinaAccumulatorSrsDemo

open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaCurveComplete (rcbAddM curveB3 Oproj)
open Dregg2.Circuit.Emit.MinaAccumulatorAir (srsScaledAddends smulV bPolyCoeff accSrsDesc)

set_option autoImplicit false

/-- Eight rows — a power of two, which the deployed prover requires of a base trace, and therefore
three challenges, since `2^3 = 8` coefficients tile eight rows the way sixteen tile the real `2^16`.
`2^rounds` generators of the REAL SRS at a REDUCED round count is `mina_accumulator_discharge.rs`'s
own `small_batch` idiom: the arithmetic is the real arithmetic and only the width is toy. -/
def DEMO_ROWS : Nat := 8

/-- ⚑ **THE DEMONSTRATION'S CHALLENGES** — read out of the PINNED blob (three coordinates of
generators `1024 / 2048 / 4096`, reduced at the Vesta SCALAR prime `pN`), so no reader has to trust a
magic constant.

⚠ The first draft derived them from `PastaCurve.Gv` and the FIRST challenge came out as **exactly
`1`** — the identity of the very operation `bPolyCoeff` performs, which would have made a derivation
that dropped that challenge entirely invisible. `the_demo_challenges_are_not_degenerate` in the Rust
tooth is the guard that catches it, and it is there because this happened. -/
def demoChals : List Nat :=
  [ (Dregg2.Circuit.Emit.MinaStepSrsG.SRS_G.getD 1024 (0, 0, 0)).1 % pN
  , (Dregg2.Circuit.Emit.MinaStepSrsG.SRS_G.getD 2048 (0, 0, 0)).2.1 % pN
  , (Dregg2.Circuit.Emit.MinaStepSrsG.SRS_G.getD 4096 (0, 0, 0)).1 % pN ]

/-- The eight declared addends, DERIVED: `A_r = −s_r · G_r` over the pinned blob. -/
def srsDemoAddends : List (Nat × Nat × Nat) :=
  srsScaledAddends Dregg2.Circuit.Emit.MinaStepSrsG.SRS_G demoChals DEMO_ROWS

/-- ⚑ **THE CLAIM THE CHAIN STARTS AT** — `C = Σ_{r<8} s_r · G_r`, by the same complete formula the
row computes. It is COMPUTED, not chosen: the chain vanishes because the relation holds, not because
the emitter wrote a zero. This is what `PI[0..95]` publishes. -/
def srsDemoClaim : Nat × Nat × Nat :=
  ((List.range DEMO_ROWS).map (fun r =>
      smulV (bPolyCoeff pN demoChals r)
        (Dregg2.Circuit.Emit.MinaStepSrsG.SRS_G.getD r (0, 0, 0)))).foldl
    (rcbAddM qN curveB3) Oproj

/-- The emitted SRS descriptor at the demonstration's two inputs — the checked-in artifact. -/
def accSrsDemoDesc : EffectVmDescriptor2 :=
  accSrsDesc Dregg2.Circuit.Emit.MinaStepSrsG.SRS_G demoChals DEMO_ROWS

/-- The certification inputs, one per line, so the Rust side READS them rather than transcribing
them: the three challenges, then the eight generator indices this manifest routes. -/
def srsParamsText : String :=
  String.intercalate "\n" (demoChals.map toString)
    ++ "\n" ++ String.intercalate " " ((List.range DEMO_ROWS).map toString) ++ "\n"

/-- The demonstration's manifest carries one declared addend per trace row, and the row count is a
power of two. Both are consumed by the deployed prover, and the first is what
`the_balance_forces_the_row_count` turns into a FORCED trace height. -/
theorem the_demonstration_is_eight_rows :
    srsDemoAddends.length = DEMO_ROWS
    ∧ DEMO_ROWS = 2 ^ 3
    ∧ demoChals.length = 3
    ∧ 2 ^ demoChals.length = DEMO_ROWS := by
  refine ⟨?_, by decide, by decide, by decide⟩
  simpa [srsDemoAddends] using
    Dregg2.Circuit.Emit.MinaAccumulatorAir.srsScaledAddends_length
      Dregg2.Circuit.Emit.MinaStepSrsG.SRS_G demoChals DEMO_ROWS

/-- ⚑ **THE ARTIFACT'S NAME IS THE SRS ONE**, so a router entry pointing at `accRoutedDemoDesc`
would be caught rather than silently serving the free-manifest descriptor under the derived name. -/
theorem the_demo_artifact_is_the_srs_descriptor :
    accSrsDemoDesc.name = "dregg-mina-accumulator-srs::v1"
    ∧ accSrsDemoDesc.name ≠ Dregg2.Circuit.Emit.MinaAccumulatorAir.accRoutedDemoDesc.name := by
  refine ⟨rfl, by decide⟩

#assert_axioms the_demonstration_is_eight_rows
#assert_axioms the_demo_artifact_is_the_srs_descriptor

end Dregg2.Circuit.Emit.MinaAccumulatorSrsDemo
