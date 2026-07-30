/-
# `Dregg2.Circuit.OpeningResidualCutoverCheck` — the BOTH-WAYS tooth of the 2026-07-30 opening-residual
cutover.

`ApexOodLaneRepair.FriLdtExtractCons`, `FriFsDecodedOodRepair.DecodedLdtLinkCons` and
`OodSingletonRepair.DecodedLdtLinkExtCons` gained one conjunct — the PER-RUN Merkle-opening residual
`¬ OpeningColl sponge idx topen.constraintEval vCommitted siblings`, stated at the witnesses each
bundle's own existential produces. That let every assembler and fan-out apex downstream of them
DELETE its `Poseidon2SpongeCR sponge` binder, which
`Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear` PROVES FALSE at deployed BabyBear
parameters and which therefore made every one of those statements vacuous at deployment.

## ⚑ WHY THIS FILE EXISTS, AND WHY HALF OF IT IS THE NEGATIVE HALF

A port measured only by what CLEARS cannot tell "the tree improved" from "the ruler moved". So this
module pins BOTH directions on every build, from the ELABORATED environment:

  * **§1 PORTED — 42 declarations that MUST NOT bind `Poseidon2SpongeCR` any more.** If one of
    them binds it again, someone re-introduced the refuted floor into a statement that had shed it,
    and the build goes red HERE rather than a reviewer noticing a binder.
  * **§2 RETAINED — 16 declarations that MUST STILL bind it.** These carry the OTHER instance,
    `Poseidon2SpongeCR hash`, which the map-op arm APPLIES (`memoryLegs_of_mapShape` →
    `mapOpsArm_of_modeler hash hCRh`). An applied floor is an ENDPOINT: it needs a hand-written
    extractor, not a mechanical re-point, and the sponge-side port cannot and does not retire it.
    **If these ever clear without the extractor landing, this file is the thing that says so.** A
    declaration that clears everything is a broken gate, not a fixed tree.

Both lists are checked FAIL-CLOSED: a name that no longer resolves is an error too, so the tooth
cannot quietly stop measuring by having its subjects renamed out from under it.

The check reads binder types WITHOUT unfolding, exactly as `Tools/ConePort` does, so a floor spelled
through its own name is seen and a `Function.Injective`-spelled one is not — that split is
`#floor_ratchet`'s business (`Verify/InjSpelling`), not this file's.
-/
import Lean
import Dregg2.Circuit.ApexOodLaneRepair
import Dregg2.Circuit.AlgoStarkSoundFanoutMemFree
import Dregg2.Circuit.AlgoStarkSoundFanoutMemory
import Dregg2.Circuit.AlgoStarkSoundFanoutSetField
import Dregg2.Circuit.AlgoStarkSoundKernel
import Dregg2.Circuit.AlgoStarkSoundKernelAvail
import Dregg2.Circuit.KernelConfigSoundness
import Dregg2.Circuit.KernelConfigSoundnessAvail
import Dregg2.Circuit.FriFsDecodedOodRepair
import Dregg2.Circuit.OodSingletonRepair

namespace Dregg2.Circuit.OpeningResidualCutoverCheck

open Lean Meta Elab Command

set_option autoImplicit false

/-- The floor this cutover is about. -/
def floorName : Name := `Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR

/-- Does `n`'s ELABORATED type bind `Poseidon2SpongeCR …` anywhere in its telescope? `none` when the
name does not resolve — a missing subject is a failure, never a pass. -/
def bindsFloor? (n : Name) : MetaM (Option Bool) := do
  let env ← getEnv
  match env.find? n with
  | none => return none
  | some info =>
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let ld ← x.fvarId!.getDecl
        if let .const h _ := ld.type.getAppFn then
          if h == floorName then return some true
      return some false

/-! ## §1 — PORTED: the floor binder is gone and must stay gone. -/

def portedOffTheFloor : List Name :=
  [ `Dregg2.Circuit.ApexOodLaneRepair.algoStarkSound_of_memoryLegs_cons
  , `Dregg2.Circuit.ApexOodLaneRepair.algoStarkSound_of_memoryFree_cons
  , `Dregg2.Circuit.ApexOodLaneRepair.algoStarkSound_transferV3_ofBusModels_cons
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_memFree_apply
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_mint
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_bridgeMint
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_supplyMint
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_burn
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_incrementNonce
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_emitEvent
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_exercise
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_pipelinedSend
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_delegate
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_delegateAtten
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_attenuate
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_grantCap
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_introduce
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_revokeCapability
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_revokeDelegation
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_refreshDelegation
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_makeSovereign
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_setPermissions
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_setVK
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_setProgram
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_cellSeal
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_cellUnseal
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_cellDestroy
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_receiptArchive
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_transferFee
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_setFieldStatic
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree.algoStarkSound_memFree_apply_noOodShape
  , `Dregg2.Circuit.AlgoStarkSoundFanoutSetField.algoStarkSound_of_memShape
  , `Dregg2.Circuit.AlgoStarkSoundFanoutSetField.algoStarkSound_setFieldDyn
  , `Dregg2.Circuit.AlgoStarkSoundFanoutSetField.algoStarkSound_setFieldDynForced
  , `Dregg2.Circuit.AlgoStarkSoundFanoutSetField.algoStarkSound_of_memShape_noOodShape
  , `Dregg2.Circuit.FriFsDecodedOodRepair.positiveRadiusTraceDecode_decoded_extCons
  , `Dregg2.Circuit.FriFsDecodedOodRepair.positiveRadiusTraceDecode_transferV3_extCons
  , `Dregg2.Circuit.FriFsDecodedOodRepair.positiveRadiusTraceDecode_decoded_extChallenges
  , `Dregg2.Circuit.FriFsDecodedOodRepair.positiveRadiusTraceDecode_transferV3_extChallenges
  , `Dregg2.Circuit.FriFsDecodedOodRepair.positiveRadiusTraceDecode_decoded_cons
  , `Dregg2.Circuit.FriFsDecodedOodRepair.positiveRadiusTraceDecode_transferV3_cons
  , `Dregg2.Circuit.OodSingletonRepair.mainAirAcceptF_of_decodedLdtLinkExtCons ]

/-! ## §2 — RETAINED: the APPLIED `Poseidon2SpongeCR hash` endpoint, deliberately unported. -/

def retainedEndpointCarriers : List Name :=
  [ `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.algoStarkSound_createCell
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.algoStarkSound_createCellFromFactory
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.algoStarkSound_heapWrite
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.algoStarkSound_noteCreate
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.algoStarkSound_noteSpend
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.algoStarkSound_of_mapShape
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.algoStarkSound_of_mapShape_noOodShape
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.algoStarkSound_refusal
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.algoStarkSound_spawn
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.algoStarkSound_spawnWrite
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.memoryLegs_of_mapShape
  , `Dregg2.Circuit.AlgoStarkSoundKernel.algoStarkSound_kernel
  , `Dregg2.Circuit.AlgoStarkSoundKernel.algoStarkSound_kernel_noOodShape
  , `Dregg2.Circuit.AlgoStarkSoundKernelAvail.algoStarkSound_kernelAvail
  , `Dregg2.Circuit.KernelConfigSoundness.kernelConfigSound
  , `Dregg2.Circuit.KernelConfigSoundnessAvail.kernelConfigSoundAvail ]

elab "#opening_residual_cutover_check" : command => do
  liftTermElabM do
    let mut bad : Array String := #[]
    for n in portedOffTheFloor do
      match ← bindsFloor? n with
      | none =>
        bad := bad.push s!"PORTED subject `{n}` DOES NOT RESOLVE — the tooth lost its subject; \
re-point it at the renamed declaration, never delete the line"
      | some true =>
        bad := bad.push s!"REGRESSION: `{n}` binds `Poseidon2SpongeCR` again. It shed that binder \
on 2026-07-30 when the corrected bundle took the per-run opening residual; a statement that takes \
the floor back is vacuous at deployed BabyBear parameters"
      | some false => pure ()
    for n in retainedEndpointCarriers do
      match ← bindsFloor? n with
      | none =>
        bad := bad.push s!"RETAINED subject `{n}` DOES NOT RESOLVE — the negative control cannot \
measure a name that is gone"
      | some false =>
        bad := bad.push s!"⚑ THE CONTROL CLEARED: `{n}` no longer binds `Poseidon2SpongeCR`. It \
carries the APPLIED `hash` instance, which is an ENDPOINT and was NOT ported. Either a hand-written \
extractor landed for the map-op arm — in which case move this name to §1 and say so in the commit — \
or the measurement moved rather than the tree"
      | some true => pure ()
    unless bad.isEmpty do
      for m in bad do logError m
      throwError "OpeningResidualCutoverCheck: the 2026-07-30 opening-residual cutover moved under \
its own tooth — read WHY before touching either list"
    logInfo m!"opening-residual cutover: {portedOffTheFloor.length} ported (floor binder absent), \
{retainedEndpointCarriers.length} retained (applied `hash` endpoint still carried)"

#opening_residual_cutover_check

end Dregg2.Circuit.OpeningResidualCutoverCheck
