import Dregg2.Circuit.StarkSoundColumnCfg
import Dregg2.Circuit.StarkSoundDischarge
import Dregg2.Circuit.DescriptorRefinesReduce

/-!
# The TOP theorem, deployed, for ANY registry — the NON-VACUOUS (reduction-form) apex, general R

The transferV3 R-twin (`StarkSoundReduce.lightclient_unfoolable_deployedR_transferV3`) ties the apex to
the honest floor for the deployed transfer slice, WITHOUT the injective `Poseidon2SpongeCR` premise
(proven false at real params). This ties it for an ARBITRARY registry `R`.

`lightclient_unfoolableR` (DescriptorRefinesReduce) takes `[StarkSound hash R]` and the reduction-form
refinement family `hrefinesR`, concluding `OrBreak (SpongeCollision hash) (…)` — no CR premise.
`starkSound_of_columnDecode_cfg` (StarkSoundColumnCfg) PRODUCES `[StarkSound hash R]` for any `R` through
the reduced `verifyBatch`, CR-free (`DeployedRefines` discharged by `deployedRefines_cfg`, the commitment
binding carried by the `hood` / the proved dichotomy). Composing them: the top-level unfoolability
statement for any effect is "state-pinned UNLESS a hash collision", valid at the real deployed hash — the
vacuous `hCR`-premised `lightclient_unfoolable_deployed_general` is deleted; this replaces it.
-/

namespace Dregg2.Circuit.LightClientDeployedGeneral

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.FriVerifier
open Dregg2.Circuit.FriVerifierBridge
open Dregg2.Circuit.FriColumnDecode
open Dregg2.Circuit.StarkSoundDischarge
open Dregg2.Circuit.StarkSoundColumnCfg
open Dregg2.Circuit.DescriptorRefinesReduce
open Dregg2.Circuit.CollisionReduce (OrBreak SpongeCollision)
open Dregg2.Circuit.DescriptorIR2 (VmTrace envAt memLog mapLog opRow)
open Dregg2.Circuit.AirChecksSatisfied (isArith)
open Dregg2.Circuit.Emit.EffectVmEmit (siteHoldsAll)
open Dregg2.Circuit.FriFoldArity
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.DeployedTraceExtract
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Crypto
open Dregg2.Exec

/-- **`lightclient_unfoolable` for an ARBITRARY registry, on the honest floor — reduction form.** A batch
the reduced `verifyBatch` accepts pins the pre/post kernel state for any effect `R`, UNLESS a collision in
the commitment hash. NO `Poseidon2SpongeCR` premise: `[StarkSound]` is discharged CR-free by
`starkSound_of_columnDecode_cfg`, and the AIR→kernel rung is the reduction-form `hrefinesR`. -/
theorem lightclient_unfoolable_deployedR_general
    (hash : List Int → Int) (S : CommitSurface) (R : Registry)
    (B : ColumnDecodeBridge cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgChecks cfgInitState cfgLogN cfgView)
    (hood : ∀ (pi : BatchPublicInputs) (π : BatchProof),
      verifyAlgo cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgChecks cfgInitState cfgLogN
          (cfgView pi π).1 (cfgView pi π).2 = true →
      decodeColumn (B.column pi π) ∈ friSetupK8.C →
      ∃ (minit : Int → Int) (mfin : Int → Int × Nat) (maddrs : List Int) (t : VmTrace)
          (_ood : Dregg2.Circuit.FieldIntegerLift.OodInterpF (R pi.effect) t),
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
        tracePublishedCommit t = pi.toPublished)
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefinesR : ∀ e, descriptorRefinesR S hash (R e) (kstep e))
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = Verdict.accept) :
    OrBreak (SpongeCollision hash)
      (∃ pre post : RecChainedState,
        StateDecode S pi.toPublished pre post ∧
        kstep pi.effect pre post ∧
        pi.pre = S.commit pre.kernel pi.turn ∧
        pi.post = S.commit post.kernel pi.turn) :=
  @lightclient_unfoolableR hash S R
    (starkSound_of_columnDecode_cfg hash R B hood) kstep hrefinesR pi π hwitdec hacc

/-- **Recovery: the unconditional general apex under no-collision.** If the commitment hash has no
collision, the general-R state-pinning holds outright — the exact conclusion the deleted vacuous
`hCR`-premised apex claimed, now from the strictly weaker `¬SpongeCollision`. -/
theorem lightclient_unfoolable_deployed_general_of_no_collision
    (hash : List Int → Int) (S : CommitSurface) (R : Registry)
    (B : ColumnDecodeBridge cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgChecks cfgInitState cfgLogN cfgView)
    (hood : ∀ (pi : BatchPublicInputs) (π : BatchProof),
      verifyAlgo cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgChecks cfgInitState cfgLogN
          (cfgView pi π).1 (cfgView pi π).2 = true →
      decodeColumn (B.column pi π) ∈ friSetupK8.C →
      ∃ (minit : Int → Int) (mfin : Int → Int × Nat) (maddrs : List Int) (t : VmTrace)
          (_ood : Dregg2.Circuit.FieldIntegerLift.OodInterpF (R pi.effect) t),
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
        tracePublishedCommit t = pi.toPublished)
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefinesR : ∀ e, descriptorRefinesR S hash (R e) (kstep e))
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = Verdict.accept)
    (hnc : ¬ SpongeCollision hash) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      kstep pi.effect pre post ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn :=
  OrBreak.resolve hnc
    (lightclient_unfoolable_deployedR_general hash S R B hood kstep hrefinesR pi π hwitdec hacc)

#assert_axioms lightclient_unfoolable_deployedR_general
#assert_axioms lightclient_unfoolable_deployed_general_of_no_collision

end Dregg2.Circuit.LightClientDeployedGeneral
