import Dregg2.Circuit.AlgoStarkSoundInstance
import Dregg2.Circuit.StarkSoundDischarge

/-!
# `StarkSound` for deployed transferV3, ASSEMBLED — no carrier anywhere

This composes the two carrier-free results into the apex soundness for the deployed `transferV3` slice,
through the *reduced* `verifyBatch`:

- `algoStarkSound_of_bricks_transferV3` (AlgoStarkSoundInstance) — `AlgoStarkSound` from a single
  explicit per-accept extraction hypothesis (an opened `VmTrace` whose `MainAirAcceptF` holds — produced
  by tonight's `ood_forces_mainAirAccept_field_of_residuals` (K′) — plus the LogUp/table legs, the
  aux-emptiness facts, and the published-commit link). NO carrier.
- `starkSound_of_algoStarkSound` (StarkSoundDischarge) — `StarkSound` from `AlgoStarkSound` alone, with
  `DeployedRefines` discharged because `verifyBatch` is now `verifyAlgo … (cfgView …)`.

Instantiated at the deployed config `cfg*`/`cfgView`, the composition gives `StarkSound hash
(fun _ => transferV3)` from the SINGLE extraction hypothesis `hextract` — with **no `verifyBatch`,
`AlgoStarkSound`, `StarkSound`, or `FriExtract` carrier**. The apex light-client soundness for the
transfer slice is now that one honest obligation (the FRI/AIR/decode extraction, which tonight's
proximity + decoder + K′ work discharges pointwise) plus the standing `cfgView`/`cfg*` KAT floor and
Poseidon2 CR.
-/

namespace Dregg2.Circuit.StarkSoundAssembled

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.FriVerifier
open Dregg2.Circuit.FriVerifierBridge
open Dregg2.Circuit.AlgoStarkSoundInstance
open Dregg2.Circuit.StarkSoundDischarge
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.AirChecksSatisfied

/-- **`StarkSound` for deployed transferV3, from one extraction hypothesis — carrier-free.** Composes
the carrier-free `AlgoStarkSound` assembly (at the deployed config `cfg*`/`cfgView`) with the
`DeployedRefines`-discharged bridge. The only input is `hextract`: on every `verifyAlgo`-accepting run
of the reduced `verifyBatch`, an opened `VmTrace t` with `MainAirAcceptF transferV3 t` (K′), the LogUp
arm, aux-emptiness, and `tracePublishedCommit t = pi.toPublished`. Nothing else assumed: no whole-verifier
carrier, no `verifyBatch` opacity, no `AlgoStarkSound`/`StarkSound`/`FriExtract` class instance. -/
theorem starkSound_of_extraction_transferV3 (hash : List Int → Int)
    (hextract : ∀ (pi : BatchPublicInputs) (π : BatchProof),
      verifyAlgo cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgChecks cfgInitState cfgLogN
          (cfgView pi π).1 (cfgView pi π).2 = true →
      ∃ (t : VmTrace),
        MainAirAcceptF Dregg2.Circuit.RotatedKernelRefinement.transferV3 t ∧
        (∀ i < t.rows.length, ∀ c ∈ Dregg2.Circuit.RotatedKernelRefinement.transferV3.constraints, ¬ isArith c →
            c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
        t.tf .memory = [] ∧ t.tf .mapOps = [] ∧
        tracePublishedCommit t = pi.toPublished) :
    StarkSound hash (fun _ => Dregg2.Circuit.RotatedKernelRefinement.transferV3) :=
  @starkSound_of_algoStarkSound hash (fun _ => Dregg2.Circuit.RotatedKernelRefinement.transferV3)
    (algoStarkSound_of_bricks_transferV3 hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgChecks
      cfgInitState cfgLogN cfgView hextract)

#assert_axioms starkSound_of_extraction_transferV3

end Dregg2.Circuit.StarkSoundAssembled
