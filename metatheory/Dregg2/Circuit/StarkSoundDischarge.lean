import Dregg2.Circuit.FriVerifierBridge

/-!
# `StarkSound` rests on ONE floor: `DeployedRefines` discharged for the reduced `verifyBatch`

`verifyBatch` (CircuitSoundness) is now a `def` — `FriVerifier.verifyAlgo` at the deployed config over
the byte-deserialization `cfgView` (commit *"verifyBatch REDUCED"*). `DeployedRefines` — "the verifier
computes the same accept Boolean as `verifyAlgo` on the mapped data" — is therefore a THEOREM here,
proved by unfolding the def: an `accept` can only occur when `verifyAlgo` itself returned `true`. The
deployment's faithfulness to the Rust wire is absorbed into the `cfgView`/`cfg*` KAT floor (the same
validation tier as Poseidon2 bit-exactness), not carried as a proof obligation.

`starkSound_of_verifyAlgo` rested on TWO named pieces — `AlgoStarkSound` (the FRI/AIR/decode math
floor) and `DeployedRefines` (the code-refines-spec residual). This file DISCHARGES the second, so the
apex `StarkSound hash R` now follows from `AlgoStarkSound` ALONE — the single irreducible math floor
the K′ bridge, the decoder (link D), and the proximity work (link A) exist to discharge.
-/

namespace Dregg2.Circuit.StarkSoundDischarge

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.FriVerifier
open Dregg2.Circuit.FriVerifierBridge

/-- **`DeployedRefines` DISCHARGED for the reduced `verifyBatch`.** `verifyBatch` acceptance FORCES
`verifyAlgo` acceptance on the mapped data — because `verifyBatch` IS
`verifyAlgoTB … (cfgView pi π) && cfgExtra …`, an `accept` occurs only when `verifyAlgoTB` returned
`true`, and `verifyAlgoTB` is a strengthening of `verifyAlgo`
(`FriTranscriptBind.verifyAlgoTB_imp_verifyAlgo`). Pure unfold + composition; no opaque appeal, no
carried hypothesis. -/
theorem deployedRefines_cfg (R : Registry) :
    DeployedRefines R cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgChecks cfgInitState cfgLogN cfgView := by
  intro pi π hacc
  unfold verifyBatch at hacc
  by_cases h :
      (Dregg2.Circuit.FriTranscriptBind.verifyAlgoTB cfgPerm cfgRATE cfgToNat cfgParams cfgVk
          cfgChecks cfgInitState cfgLogN (cfgView pi π).1 (cfgView pi π).2
        && cfgExtra (cfgView pi π).1 (cfgView pi π).2) = true
  · simp only [Bool.and_eq_true] at h
    exact Dregg2.Circuit.FriTranscriptBind.verifyAlgoTB_imp_verifyAlgo cfgPerm cfgRATE cfgToNat
      cfgParams cfgVk cfgChecks cfgInitState cfgLogN (cfgView pi π).1 (cfgView pi π).2 h.1
  · rw [if_neg h] at hacc
    exact absurd hacc (by decide)

/-- **`StarkSound` on ONE floor.** With `DeployedRefines` discharged, the apex `StarkSound hash R`
follows from `AlgoStarkSound` ALONE — the irreducible math floor (FRI proximity @ BabyBear + AIR
soundness + the trace decode + Poseidon2 collision-resistance). The two-floor
`starkSound_of_verifyAlgo` is now one-floor: `DeployedRefines` is a theorem, not an assumption. -/
theorem starkSound_of_algoStarkSound (hash : List Int → Int) (R : Registry)
    [carrier : AlgoStarkSound hash R cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgChecks
      cfgInitState cfgLogN cfgView] :
    StarkSound hash R :=
  starkSound_of_verifyAlgo hash R cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgChecks
    cfgInitState cfgLogN cfgView (deployedRefines_cfg R)

#assert_axioms deployedRefines_cfg
#assert_axioms starkSound_of_algoStarkSound

end Dregg2.Circuit.StarkSoundDischarge
