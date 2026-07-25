import Dregg2.Circuit.FriColumnDecode
import Dregg2.Circuit.StarkSoundDischarge

/-!
# `StarkSound` for an ARBITRARY registry, through the reduced `verifyBatch` — general-effect capstone

The transferV3 capstones (`StarkSoundAssembled`, `StarkSoundFriLdt`) close the deployed transfer slice.
This closes the *general* registry: `starkSound_of_columnDecode_and_refines` (FriColumnDecode) derives
`StarkSound hash R` for ANY `R` from a `ColumnDecodeBridge` + the per-accept extraction `hood`
(proximity `decodeColumn ∈ C` ⟹ a satisfying `VmTrace`, whose commitment binding rests on the PROVED
`commitmentOpening_binds_of_poseidon2CR`) + `DeployedRefines`. Since `deployedRefines_cfg` discharges
`DeployedRefines` for the reduced `verifyBatch` at ANY `R`, the composition gives `StarkSound hash R`
through the reduced `verifyBatch` at the deployed config — no `verifyBatch`/`StarkSound` carrier, any effect.
-/

namespace Dregg2.Circuit.StarkSoundColumnCfg

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.FriVerifier
open Dregg2.Circuit.FriVerifierBridge
open Dregg2.Circuit.FriColumnDecode
open Dregg2.Circuit.StarkSoundDischarge
open Dregg2.Circuit.DescriptorIR2 (VmTrace envAt memLog mapLog opRow)
open Dregg2.Circuit.AirChecksSatisfied (isArith)
open Dregg2.Circuit.Emit.EffectVmEmit (siteHoldsAll)
open Dregg2.Circuit.FriFoldArity
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.DeployedTraceExtract
open Dregg2.Crypto

/-- **`StarkSound` for any registry `R`, at the deployed config.** Wires the general-registry
column-decode soundness to tonight's `DeployedRefines` discharge. The remaining inputs are the honest
structural/extraction floor: a `ColumnDecodeBridge` and the per-accept `hood` (proximity ⟹ satisfying
trace). No `verifyBatch` opacity — `DeployedRefines` is `deployedRefines_cfg`, a theorem. -/
theorem starkSound_of_columnDecode_cfg (hash : List Int → Int) (R : Registry)
    (B : ColumnDecodeBridge cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgChecks cfgInitState cfgLogN cfgView)
    (hood : ∀ (pi : BatchPublicInputs) (π : BatchProof),
      verifyAlgo cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgChecks cfgInitState cfgLogN
          (cfgView pi π).1 (cfgView pi π).2 = true →
      decodeColumn (B.column pi π) ∈ friSetupK8.C →
      ∃ (minit : Int → Int) (mfin : Int → Int × Nat) (maddrs : List Int) (t : VmTrace)
          (_ood : Dregg2.Circuit.OodInterpFieldExt.OodInterpFExt
            Dregg2.Circuit.OodInterpFieldExt.BB4 (R pi.effect) t),
        (∀ i < t.rows.length, ∀ c ∈ (R pi.effect).constraints, ¬ isArith c →
            c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
        (∀ i < t.rows.length, siteHoldsAll hash (envAt t i) (R pi.effect).hashSites) ∧
        (∀ i < t.rows.length, ∀ r ∈ (R pi.effect).ranges, r.holds (envAt t i)) ∧
        maddrs.Nodup ∧
        (∀ op ∈ memLog (R pi.effect) t, op.addr ∈ maddrs) ∧
        MemoryChecking.Disciplined (memLog (R pi.effect) t) ∧
        MemoryChecking.MemCheck minit mfin maddrs (memLog (R pi.effect) t) ∧
        t.tf .memory = (memLog (R pi.effect) t).map opRow ∧
        t.tf .mapOps = mapLog (R pi.effect) t ∧
        tracePublishedCommit t = pi.toPublished) :
    StarkSound hash R :=
  starkSound_of_columnDecode_and_refines hash R cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgChecks
    cfgInitState cfgLogN cfgView B hood (deployedRefines_cfg R)

#assert_axioms starkSound_of_columnDecode_cfg

end Dregg2.Circuit.StarkSoundColumnCfg
