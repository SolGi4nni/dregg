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

  * **§1 PORTED — 56 declarations that MUST NOT bind `Poseidon2SpongeCR` any more.** If one of
    them binds it again, someone re-introduced the refuted floor into a statement that had shed it,
    and the build goes red HERE rather than a reviewer noticing a binder.
  * **§2 RETAINED — the declarations that MUST STILL bind it.** A check that clears everything is a
    broken gate, not a fixed tree, so this list must never be empty while any endpoint genuinely
    carries the floor. Its current members are the WHOLE-TURN apex
    `ClosureForest.lightclient_unfoolable_circuit_sound_turn` and the base single-transition apex
    `CircuitSoundness.lightclient_unfoolable`: both consume `descriptorRefines`, whose refuted floor
    sits in the DEF BODY and must be paid at the application site. If either clears, the turn-level /
    base port landed — move it to §1 and say so in the commit.

  ⛑ 2026-07-31 (SITE 3): `KernelConfigSoundness.kernelConfigSound` and
    `KernelConfigSoundnessAvail.kernelConfigSoundAvail` LEFT §2 for §1, and this is the negative
    control firing as designed — it fired, and the reason is the one it named. The state-decode
    apex chain (`ClosureAll.lightclient_unfoolable_closed` →
    `ClosureFinal{,Avail}`/`ClosureFanout{,Genuine}` → these two) now routes through
    `ClosureAll.descriptorRefinesFree_of_closedLogExtract` → `ApexFloorFree.lightclient_unfoolable_free`,
    in which NO `Poseidon2SpongeCR` is introduced anywhere. The §2 prose above was WRONG about which
    binding was load-bearing: the apex's `hCR` was handed to `descriptorRefines`'s def-body antecedent
    and DISCARDED by `ClosureAll.effectDecodeBridge_of_closedLogExtract`'s `intro _hCR`; it never
    reached `rotV3_binds_published`. ⚠ AND SHEDDING IT DID NOT DE-VACUUM THOSE APEXES — they still
    quantify over `CommitSurface`, refuted at EVERY parameter by
    `Verify.ApexPremiseVacuity.apexCommitFloor_unsatisfiable`. Read the clearance as "one refuted
    hypothesis fewer", not as "the state-decode apex is now applicable".

  ⛑ 2026-07-31: fourteen names LEFT §2 for §1. The `2f72e093f` prose above once said the map-op arm
    APPLIES the floor via `mapOpsArm_of_modeler hash hCRh`. That became FALSE four hours later
    (`97a6520ce`, 2026-07-30 22:32): the denotation cutover retired `mapOp_holds_of_mapReconcile`
    and made `mapOpsArm_of_modeler` project the CARRIED, floor-free `MapDenotationFamily` modeler.
    The `Poseidon2SpongeCR hash` binder on `memoryLegs_of_mapShape` / `algoStarkSound_of_mapShape` /
    the map-shape fan-out apexes / `algoStarkSound_kernel{,Avail}` was therefore VESTIGIAL and is
    deleted. The real map obligation is `MapDenotationFamily`, inhabitable floor-free at deployed
    args by `MapDenotationCutoverCheck.deployed_opensTo_inhabited` — the tree improved, the ruler did
    not move.

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
import Dregg2.Circuit.ClosureForest
import Dregg2.Circuit.ClosureFanout
import Dregg2.Circuit.ApexFloorFree

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
  , `Dregg2.Circuit.OodSingletonRepair.mainAirAcceptF_of_decodedLdtLinkExtCons
  -- ⛑ 2026-07-31: the map-shape STARK layer sheds its VESTIGIAL `Poseidon2SpongeCR hash` binder
  -- (the map-op arm went floor-free at the `97a6520ce` denotation cutover; the binder never applied).
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.memoryLegs_of_mapShape
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.algoStarkSound_of_mapShape
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.algoStarkSound_of_mapShape_noOodShape
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.algoStarkSound_noteSpend
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.algoStarkSound_noteCreate
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.algoStarkSound_createCell
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.algoStarkSound_createCellFromFactory
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.algoStarkSound_spawn
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.algoStarkSound_spawnWrite
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.algoStarkSound_refusal
  , `Dregg2.Circuit.AlgoStarkSoundFanoutMemory.algoStarkSound_heapWrite
  , `Dregg2.Circuit.AlgoStarkSoundKernel.algoStarkSound_kernel
  , `Dregg2.Circuit.AlgoStarkSoundKernel.algoStarkSound_kernel_noOodShape
  , `Dregg2.Circuit.AlgoStarkSoundKernelAvail.algoStarkSound_kernelAvail
  -- ⛑ 2026-07-31 (SITE 3): the two state-decode apexes, moved here from §2.
  , `Dregg2.Circuit.KernelConfigSoundness.kernelConfigSound
  , `Dregg2.Circuit.KernelConfigSoundnessAvail.kernelConfigSoundAvail
  , `Dregg2.Circuit.ClosureAll.lightclient_unfoolable_closed
  , `Dregg2.Circuit.ClosureFanout.lightclient_unfoolable_closed_final
  , `Dregg2.Circuit.ClosureFanoutGenuine.lightclient_unfoolable_closed_final_genuine
  , `Dregg2.Circuit.ClosureFinal.lightclient_unfoolable_one
  , `Dregg2.Circuit.ClosureFinal.lightclient_unfoolable_circuit_sound
  , `Dregg2.Circuit.ClosureFinal.lightclient_unfoolable_circuit_sound_of_readouts
  , `Dregg2.Circuit.ClosureFinalAvail.lightclient_unfoolable_closed_final_avail
  , `Dregg2.Circuit.ApexFloorFree.lightclient_unfoolable_free ]

/-! ## §2 — RETAINED: the `Poseidon2SpongeCR hash` endpoints that are genuinely still unported.

The two kernel-config apexes left this list on 2026-07-31 (see the ⛑ note in the header). What remains
are the two apexes that still CONSUME `CircuitSoundness.descriptorRefines`, whose refuted antecedent
lives in the def BODY and therefore has to be paid by whoever applies the rung: the base
single-transition apex and the whole-turn forest apex. Porting them is the named remainder — the
single-transition one needs its ~15 `hrefines`-threading consumers retyped, the turn one needs
`stepsRefine_of_descriptorRefines` and `TurnDecodeChain` moved onto `ApexFloorFree.CommitMap`. -/

def retainedEndpointCarriers : List Name :=
  [ `Dregg2.Circuit.CircuitSoundness.lightclient_unfoolable
  , `Dregg2.Circuit.ClosureForest.lightclient_unfoolable_circuit_sound_turn ]

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
