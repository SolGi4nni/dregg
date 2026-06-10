/-
# Dregg2.Circuit.Emit.EmitGraduate — focused scratch emitter for the cutover-graduating descriptors.

Prints `<defName>\t<descriptor.name>\t<emitVmJson descriptor>` for ONLY the descriptors whose Lean
emit modules already tick the runtime nonce. Run:

  `lake env lean --run Dregg2/Circuit/Emit/EmitGraduate.lean`
-/
import Dregg2.Circuit.Emit.EffectVmEmit
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitBurn
import Dregg2.Circuit.Emit.EffectVmEmitNoteSpend
import Dregg2.Circuit.Emit.EffectVmEmitNoteCreate
import Dregg2.Circuit.Emit.EffectVmEmitBridgeMint
import Dregg2.Circuit.Emit.EffectVmEmitCreateSealPair
import Dregg2.Circuit.Emit.EffectVmEmitCellSeal
import Dregg2.Circuit.Emit.EffectVmEmitCellDestroy
import Dregg2.Circuit.Emit.EffectVmEmitRefusal
import Dregg2.Circuit.Emit.EffectVmEmitSetPermissions
import Dregg2.Circuit.Emit.EffectVmEmitSetVK
import Dregg2.Circuit.Emit.EffectVmEmitExercise
import Dregg2.Circuit.Emit.EffectVmEmitPipelinedSend
import Dregg2.Circuit.Emit.EffectVmEmitRefreshDelegation
import Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce
import Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation
import Dregg2.Circuit.Emit.EffectVmEmitIntroduce

open Dregg2.Circuit.Emit.EffectVmEmit (emitVmJson)

def main : IO Unit := do
  let emit (defName : String) (d : Dregg2.Circuit.Emit.EffectVmEmit.EffectVmDescriptor) : IO Unit :=
    IO.println s!"{defName}\t{d.name}\t{emitVmJson d}"
  emit "transferVmDescriptor" Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferVmDescriptor
  emit "burnVmDescriptor" Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptor
  emit "noteSpendVmDescriptor" Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.noteSpendVmDescriptor
  emit "noteCreateVmDescriptor" Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.noteCreateVmDescriptor
  emit "bridgeMintVmDescriptor" Dregg2.Circuit.Emit.EffectVmEmitBridgeMint.bridgeMintVmDescriptor
  emit "createSealPairVmDescriptor" Dregg2.Circuit.Emit.EffectVmEmitCreateSealPair.createSealPairVmDescriptor
  emit "cellSealVmDescriptor" Dregg2.Circuit.Emit.EffectVmEmitCellSeal.cellSealVmDescriptor
  emit "cellDestroyVmDescriptor" Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.cellDestroyVmDescriptor
  emit "refusalVmDescriptor" Dregg2.Circuit.Emit.EffectVmEmitRefusal.refusalVmDescriptor
  emit "setPermsVmDescriptor" Dregg2.Circuit.Emit.EffectVmEmitSetPermissions.setPermsVmDescriptor
  emit "setVKVmDescriptor" Dregg2.Circuit.Emit.EffectVmEmitSetVK.setVKVmDescriptor
  emit "exerciseVmDescriptor" Dregg2.Circuit.Emit.EffectVmEmitExercise.exerciseVmDescriptor
  emit "pipelinedSendVmDescriptor" Dregg2.Circuit.Emit.EffectVmEmitPipelinedSend.pipelinedSendVmDescriptor
  emit "refreshVmDescriptor" Dregg2.Circuit.Emit.EffectVmEmitRefreshDelegation.refreshVmDescriptor
  emit "incrementNonceVmDescriptor" Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce.incrementNonceVmDescriptor
  emit "revokeVmDescriptor" Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation.revokeVmDescriptor
  emit "introduceVmDescriptor" Dregg2.Circuit.Emit.EffectVmEmitIntroduce.introduceVmDescriptor
