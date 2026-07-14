import Dregg2.Circuit.FriVerifierBridge

/-!
# `StarkSound` rests on ONE floor: `DeployedRefines` discharged for the reduced `verifyBatch`

`verifyBatch` (CircuitSoundness) is now a `def` — the quartic-extension faithful verifier at the
deployed config over `cfgView`/`cfgExtView`. `DeployedRefines` — "acceptance implies `verifyAlgo`
acceptance on the legacy mapped data" — remains a THEOREM with the same statement: extension-faithful
acceptance strengthens to the faithful scalar restriction, which strengthens to `verifyAlgo`. The
deployment's faithfulness to the Rust wire is absorbed into the reconstruction/config KAT floor (the same
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
`verifyAlgoUnifiedFaithfulExt … (cfgView pi π) (cfgExtView pi π) && cfgExtra …`, an `accept`
occurs only when the quartic-extension verifier returned `true`. Extension-faithful acceptance
first strengthens to the scalar faithful verifier, then to `verifyAlgoUnified`, then to
`verifyAlgo` (`verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnifiedFaithful`, followed by
`verifyAlgoUnifiedFaithful_imp_verifyAlgoUnified`, followed by
`verifyAlgoUnified_imp_verifyAlgo`). Pure unfold + composition; no opaque appeal, no carried hypothesis. -/
theorem deployedRefines_cfg (R : Registry) :
    DeployedRefines R cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgChecks cfgInitState cfgLogN cfgView := by
  intro pi π hacc
  unfold verifyBatch at hacc
  by_cases h :
      (Dregg2.Circuit.ExtFieldChallenge.verifyAlgoUnifiedFaithfulExt
          cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA cfgExtCore cfgExtA cfgExtW
          cfgInitState cfgLogN (cfgView pi π).1 (cfgView pi π).2 (cfgExtView pi π)
        && cfgExtra (cfgView pi π).1 (cfgView pi π).2) = true
  · simp only [Bool.and_eq_true] at h
    have hf := Dregg2.Circuit.ExtFieldChallenge.verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnifiedFaithful
      cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA cfgExtCore cfgExtA cfgExtW
      cfgInitState cfgLogN (cfgView pi π).1 (cfgView pi π).2 (cfgExtView pi π) h.1
    have hu := Dregg2.Circuit.FriChallengerUnified.verifyAlgoUnifiedFaithful_imp_verifyAlgoUnified
      cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA cfgInitState cfgLogN
      (cfgView pi π).1 (cfgView pi π).2 hf
    exact Dregg2.Circuit.FriChallengerUnified.verifyAlgoUnified_imp_verifyAlgo cfgPerm cfgRATE cfgToNat
      cfgParams cfgVk cfgCore cfgA cfgInitState cfgLogN (cfgView pi π).1 (cfgView pi π).2 hu
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
