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

/-! ## ⚑⚑ THE HEAD THE DEMONSTRATION'S CLAIM IS DECLARED TO BELONG TO

⚠ **SAY WHAT IS REAL AND WHAT IS THE DEMONSTRATION'S, BECAUSE THEY ARE DIFFERENT HERE.**

* The head lanes are **REAL**: devnet block 539508's own protocol-state hash, the block whose Wrap
  proof o1-labs' `kimchi::verifier::verify` accepts. They are `LightClientMinaAir.DEVNET_TIP_LANES`
  and `honest_tip_lanes_decode_the_devnet_block` pins their recomposition against the decimal, so
  they are a GATE on a decode and not a transcription. They are re-stated here rather than imported
  because `MinaAccumulatorAir` must stay clear of the light-client cone;
  `mina_accumulator_head_proves.rs` asserts the two spellings agree.
* The **PAIRING is the demonstration's**, exactly as `demoChals` is. `srsDemoClaim` is `Σ s_r·G_r`
  at three CHOSEN challenges over the first eight SRS generators; it is **not** block 539508's
  `challenge_polynomial_commitment`. So `accHeadDemoDesc` declares a real head beside a synthetic
  claim, and the descriptor's own docblock (`MinaAccumulatorAir` §11) is where the standing of the
  binding is written down at full resolution. What the artifact demonstrates is the SEAM — that the
  pair is forced by a constraint — not that this particular pair is Mina's. -/

/-- The lanes of devnet block **539508**'s state hash. ⚑ One value, two spellings: this list and
`LightClientMinaAir.DEVNET_TIP_LANES`. A drift between them goes red in
`mina_accumulator_head_proves.rs::the_declared_head_is_the_light_clients_devnet_tip`. -/
def demoHeadLanes : List ℤ :=
  [148400356, 2288994, 332868807, 237767070, 530455789, 507531490, 336317945, 425818875, 3793778]

/-- ⚠ **THE HEAD IS NOT DEGENERATE AND IS NOT THE ANCHOR.** Nine lanes, none of them the whole
value, and distinct from the devnet GENESIS anchor's lanes — which is the head the refusal exhibit
substitutes, so if the two agreed the falsifier would move nothing. -/
theorem the_demo_head_is_nine_lanes_and_is_not_the_genesis_anchor :
    demoHeadLanes.length = 9
    ∧ demoHeadLanes ≠
        [317368465, 122552485, 518650043, 481937944, 112457995, 488503206, 390747624, 350427965,
         1320595] := by
  refine ⟨by decide, by decide⟩

/-- ⚑ **THE HEAD-BOUND DESCRIPTOR AT THE DEMONSTRATION'S INPUTS** — the checked-in artifact. -/
def accHeadDemoDesc : EffectVmDescriptor2 :=
  Dregg2.Circuit.Emit.MinaAccumulatorAir.accHeadDesc
    Dregg2.Circuit.Emit.MinaStepSrsG.SRS_G demoChals DEMO_ROWS demoHeadLanes srsDemoClaim

/-- ⚑ **THE ARTIFACT'S NAME IS THE HEAD ONE**, so a router entry pointing at `accSrsDemoDesc` would
be caught rather than silently serving the head-free descriptor under the head-bound name. -/
theorem the_head_artifact_is_the_head_descriptor :
    accHeadDemoDesc.name = "dregg-mina-accumulator-head::v1"
    ∧ accHeadDemoDesc.name ≠ accSrsDemoDesc.name := by
  refine ⟨rfl, by decide⟩

/-- ⚑⚑ **THE NEGATIVE CONTROL'S HEAD** — devnet GENESIS's state hash lanes
(`LightClientMinaAir.GENESIS_ANCHOR_LANES`), a DIFFERENT REAL Mina head. This is the head the
wrong-head forgery publishes. -/
def genesisHeadLanes : List ℤ :=
  [317368465, 122552485, 518650043, 481937944, 112457995, 488503206, 390747624, 350427965, 1320595]

/-- ⚑⚑ **THE NEGATIVE CONTROL.** The SAME algebra, the SAME manifest, the SAME claim — and the
GENESIS head declared instead of the block-539508 tip. Its only purpose is to make the refusal
exhibit ISOLATING: the wrong-head trace is refused under `accHeadDemoDesc` and PROVES here, so the
head half of the seam's `bound` is the only thing that separated them and no reader has to take
*"refused by the `proof_bind` and by nothing else"* on trust.

⚠ **EMITTED, NOT ASSEMBLED IN RUST.** A Rust test that edited a parsed descriptor's `bound` lanes
would be Rust authoring AIR (house law #1) — the same reason `mina-wrap-conjunction-unthreaded.json`
is an emitted artifact rather than a filtered constraint list. -/
def accHeadGenesisDesc : EffectVmDescriptor2 :=
  Dregg2.Circuit.Emit.MinaAccumulatorAir.accHeadDescNamed
    "dregg-mina-accumulator-head-genesis::v1"
    (Dregg2.Circuit.Emit.MinaAccumulatorAir.srsScaledAddends
      Dregg2.Circuit.Emit.MinaStepSrsG.SRS_G demoChals DEMO_ROWS)
    genesisHeadLanes srsDemoClaim

/-- ⚑ **THE CONTROL DIFFERS IN ITS NAME AND ITS DECLARED HEAD.** Same declared width and PI count;
the two heads are distinct REAL Mina state hashes, which is what makes the pair an exhibit rather
than two spellings of one descriptor.

⚠ The heavier halves — that the two carry the SAME constraint count and the SAME 105-lane seam
differing in exactly the nine head lanes — are measured on the EMITTED BYTES in
`circuit/tests/mina_accumulator_head_proves.rs::the_control_differs_from_the_artifact_in_nine_lanes`,
because `rfl` between two 4 843-constraint lists is a reduction this kernel should not be asked to
run twice for a fact the artifacts state directly. -/
theorem the_control_is_the_same_shape_under_a_different_name :
    accHeadGenesisDesc.name ≠ accHeadDemoDesc.name
    ∧ accHeadGenesisDesc.traceWidth = accHeadDemoDesc.traceWidth
    ∧ accHeadGenesisDesc.piCount = accHeadDemoDesc.piCount
    ∧ genesisHeadLanes ≠ demoHeadLanes := by
  refine ⟨by decide, rfl, rfl, by decide⟩

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
#assert_axioms the_demo_head_is_nine_lanes_and_is_not_the_genesis_anchor
#assert_axioms the_head_artifact_is_the_head_descriptor
#assert_axioms the_control_is_the_same_shape_under_a_different_name

end Dregg2.Circuit.Emit.MinaAccumulatorSrsDemo
