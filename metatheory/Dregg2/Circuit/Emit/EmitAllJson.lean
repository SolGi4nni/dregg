/-
# Dregg2.Circuit.Emit.EmitAllJson — the EMIT-ALL executable (descriptor registry source).

Imports every effect's emit module and prints, for each emitted `EffectVmDescriptor`, a line

  `<LEAN_DEF_NAME>\t<descriptor.name>\t<emitVmJson descriptor>`

so the Rust descriptor registry (`circuit/src/effect_vm_descriptors.rs`) can be regenerated
byte-for-byte from the verified Lean emit. This is a SCRATCH executable (like `EmitCheck.lean`):
run it with `lake env lean --run Dregg2/Circuit/Emit/EmitAllJson.lean`.

The descriptor `name` is the canonical wire identity. NOTE: four selectors SHARE the attenuate
descriptor object (delegate / delegateAtten / revokeDelegation / introduce all `:= attenuateVmDescriptor`),
so the same JSON serves multiple effect selectors — the Rust registry maps selector → JSON, not
name → JSON, to capture this many-to-one fan-out.
-/
import Dregg2.Circuit.Emit.EffectVmEmit
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
import Dregg2.Circuit.Emit.EffectVmEmitBridgeCancel
import Dregg2.Circuit.Emit.EffectVmEmitBridgeFinalize
import Dregg2.Circuit.Emit.EffectVmEmitBridgeLockA
import Dregg2.Circuit.Emit.EffectVmEmitBridgeMint
import Dregg2.Circuit.Emit.EffectVmEmitBurn
import Dregg2.Circuit.Emit.EffectVmEmitCellDestroy
import Dregg2.Circuit.Emit.EffectVmEmitCellSeal
import Dregg2.Circuit.Emit.EffectVmEmitCreateCell
import Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactory
import Dregg2.Circuit.Emit.EffectVmEmitCreateCommittedEscrow
import Dregg2.Circuit.Emit.EffectVmEmitCreateEscrow
import Dregg2.Circuit.Emit.EffectVmEmitCreateSealPair
import Dregg2.Circuit.Emit.EffectVmEmitDelegate
import Dregg2.Circuit.Emit.EffectVmEmitDelegateAtten
import Dregg2.Circuit.Emit.EffectVmEmitDropRef
import Dregg2.Circuit.Emit.EffectVmEmitEmitEvent
import Dregg2.Circuit.Emit.EffectVmEmitEnliven
import Dregg2.Circuit.Emit.EffectVmEmitExercise
import Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce
import Dregg2.Circuit.Emit.EffectVmEmitIntroduce
import Dregg2.Circuit.Emit.EffectVmEmitMakeSovereign
import Dregg2.Circuit.Emit.EffectVmEmitMint
import Dregg2.Circuit.Emit.EffectVmEmitNoteCreate
import Dregg2.Circuit.Emit.EffectVmEmitNoteSpend
import Dregg2.Circuit.Emit.EffectVmEmitPipelinedSend
import Dregg2.Circuit.Emit.EffectVmEmitQueueAllocate
import Dregg2.Circuit.Emit.EffectVmEmitQueueAtomicTx
import Dregg2.Circuit.Emit.EffectVmEmitQueueDequeue
import Dregg2.Circuit.Emit.EffectVmEmitQueueEnqueue
import Dregg2.Circuit.Emit.EffectVmEmitQueuePipelineStep
import Dregg2.Circuit.Emit.EffectVmEmitQueueResize
import Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive
import Dregg2.Circuit.Emit.EffectVmEmitRefreshDelegation
import Dregg2.Circuit.Emit.EffectVmEmitRefundEscrow
import Dregg2.Circuit.Emit.EffectVmEmitRefusal
import Dregg2.Circuit.Emit.EffectVmEmitReleaseEscrow
import Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation
import Dregg2.Circuit.Emit.EffectVmEmitSeal
import Dregg2.Circuit.Emit.EffectVmEmitSetPermissions
import Dregg2.Circuit.Emit.EffectVmEmitSetVK
import Dregg2.Circuit.Emit.EffectVmEmitSpawn
import Dregg2.Circuit.Emit.EffectVmEmitSwissDrop
import Dregg2.Circuit.Emit.EffectVmEmitSwissExport
import Dregg2.Circuit.Emit.EffectVmEmitSwissHandoff
import Dregg2.Circuit.Emit.EffectVmEmitUnseal
import Dregg2.Circuit.Emit.EffectVmEmitValidateHandoff
import Dregg2.Circuit.Emit.EffectVmEmitRecordRoot

open Dregg2.Circuit.Emit.EffectVmEmit

/-- One registry entry: the Lean def name + its emitted descriptor. -/
structure Entry where
  defName : String
  desc    : EffectVmDescriptor

open Dregg2.Circuit.Emit in
/-- Every emitted descriptor, paired with its Lean def name. The fully-qualified opens
keep this readable; the `attenuateVmDescriptor` reuses (delegate/delegateAtten/revoke/introduce)
are listed explicitly so the line count equals the distinct (selector-bearing) emit modules. -/
def allEntries : List Entry :=
  [ ⟨"transferVmDescriptor",            EffectVmEmitTransfer.transferVmDescriptor⟩
  , ⟨"attenuateVmDescriptor",           EffectVmEmitAttenuateA.attenuateVmDescriptor⟩
  , ⟨"bridgeCancelVmDescriptor",        EffectVmEmitBridgeCancel.bridgeCancelVmDescriptor⟩
  , ⟨"bridgeFinalizeVmDescriptor",      EffectVmEmitBridgeFinalize.bridgeFinalizeVmDescriptor⟩
  , ⟨"bridgeLockVmDescriptor",          EffectVmEmitBridgeLockA.bridgeLockVmDescriptor⟩
  , ⟨"bridgeMintVmDescriptor",          EffectVmEmitBridgeMint.bridgeMintVmDescriptor⟩
  , ⟨"burnVmDescriptor",                EffectVmEmitBurn.burnVmDescriptor⟩
  , ⟨"cellDestroyVmDescriptor",         EffectVmEmitCellDestroy.cellDestroyVmDescriptor⟩
  , ⟨"cellSealVmDescriptor",            EffectVmEmitCellSeal.cellSealVmDescriptor⟩
  , ⟨"createCellVmDescriptor",          EffectVmEmitCreateCell.createCellVmDescriptor⟩
  , ⟨"factoryVmDescriptor",             EffectVmEmitCreateCellFromFactory.factoryVmDescriptor⟩
  , ⟨"escrowCreateVmDescriptor",        EffectVmEmitCreateCommittedEscrow.escrowCreateVmDescriptor⟩
  , ⟨"createEscrowVmDescriptor",        EffectVmEmitCreateEscrow.createEscrowVmDescriptor⟩
  , ⟨"createSealPairVmDescriptor",      EffectVmEmitCreateSealPair.createSealPairVmDescriptor⟩
  , ⟨"delegateVmDescriptor",            EffectVmEmitDelegate.delegateVmDescriptor⟩
  , ⟨"delegateAttenVmDescriptor",       EffectVmEmitDelegateAtten.delegateAttenVmDescriptor⟩
  , ⟨"dropRefVmDescriptor",             EffectVmEmitDropRef.dropRefVmDescriptor⟩
  , ⟨"emitEventVmDescriptor",           EffectVmEmitEmitEvent.emitEventVmDescriptor⟩
  , ⟨"enlivenVmDescriptor",             EffectVmEmitEnliven.enlivenVmDescriptor⟩
  , ⟨"exerciseVmDescriptor",            EffectVmEmitExercise.exerciseVmDescriptor⟩
  , ⟨"incrementNonceVmDescriptor",      EffectVmEmitIncrementNonce.incrementNonceVmDescriptor⟩
  , ⟨"introduceVmDescriptor",           EffectVmEmitIntroduce.introduceVmDescriptor⟩
  , ⟨"makeSovereignVmDescriptor",       EffectVmEmitMakeSovereign.makeSovereignVmDescriptor⟩
  , ⟨"mintVmDescriptor",                EffectVmEmitMint.mintVmDescriptor⟩
  , ⟨"noteCreateVmDescriptor",          EffectVmEmitNoteCreate.noteCreateVmDescriptor⟩
  , ⟨"noteSpendVmDescriptor",           EffectVmEmitNoteSpend.noteSpendVmDescriptor⟩
  , ⟨"pipelinedSendVmDescriptor",       EffectVmEmitPipelinedSend.pipelinedSendVmDescriptor⟩
    -- The four root-parameterized queue descriptors are functions of an OPAQUE side-table
    -- parameter (the `newRoot`/`emptyRoot`/`resizeCost` the row asserts but does NOT recompute —
    -- exactly the class-C queue gap in the assurance ledger). The emitted descriptor SHAPE is
    -- independent of that scalar (it enters only as one gate constant), so we serialize the
    -- canonical instance at `0`.
  , ⟨"queueAllocateVmDescriptor",       EffectVmEmitQueueAllocate.queueAllocateVmDescriptor 0⟩
  , ⟨"queueAtomicVmDescriptor",         EffectVmEmitQueueAtomicTx.queueAtomicVmDescriptor⟩
  , ⟨"queueDequeueVmDescriptor",        EffectVmEmitQueueDequeue.queueDequeueVmDescriptor 0⟩
  , ⟨"queueEnqueueVmDescriptor",        EffectVmEmitQueueEnqueue.queueEnqueueVmDescriptor 0⟩
  , ⟨"queuePipelineVmDescriptor",       EffectVmEmitQueuePipelineStep.queuePipelineVmDescriptor⟩
  , ⟨"queueResizeVmDescriptor",         EffectVmEmitQueueResize.queueResizeVmDescriptor 0⟩
  , ⟨"receiptArchiveVmDescriptor",      EffectVmEmitReceiptArchive.receiptArchiveVmDescriptor⟩
  , ⟨"refreshVmDescriptor",             EffectVmEmitRefreshDelegation.refreshVmDescriptor⟩
  , ⟨"refundEscrowVmDescriptor",        EffectVmEmitRefundEscrow.refundEscrowVmDescriptor⟩
  , ⟨"refusalVmDescriptor",             EffectVmEmitRefusal.refusalVmDescriptor⟩
  , ⟨"releaseEscrowVmDescriptor",       EffectVmEmitReleaseEscrow.releaseEscrowVmDescriptor⟩
  , ⟨"revokeVmDescriptor",              EffectVmEmitRevokeDelegation.revokeVmDescriptor⟩
  , ⟨"sealVmDescriptor",                EffectVmEmitSeal.sealVmDescriptor⟩
  , ⟨"setPermsVmDescriptor",            EffectVmEmitSetPermissions.setPermsVmDescriptor⟩
  , ⟨"setVKVmDescriptor",               EffectVmEmitSetVK.setVKVmDescriptor⟩
  , ⟨"spawnVmDescriptor",               EffectVmEmitSpawn.spawnVmDescriptor⟩
  , ⟨"swissDropVmDescriptor",           EffectVmEmitSwissDrop.swissDropVmDescriptor⟩
  , ⟨"swissExportVmDescriptor",         EffectVmEmitSwissExport.swissExportVmDescriptor⟩
  , ⟨"swissHandoffVmDescriptor",        EffectVmEmitSwissHandoff.swissHandoffVmDescriptor⟩
  , ⟨"unsealVmDescriptor",              EffectVmEmitUnseal.unsealVmDescriptor⟩
  , ⟨"validateHandoffVmDescriptor",     EffectVmEmitValidateHandoff.validateHandoffVmDescriptor⟩
    -- RECORD-LAYER STAGE 2: transfer descriptor + `fields_root`-absorbing GROUP-4 (site 3's
    -- spare 4th input now binds the user-field-map root cell into `state_commit`). Width-neutral
    -- (186): the carrier is the existing `state.FIELDS_ROOT` (= RESERVED, col 89) within the base
    -- layout, so the generic descriptor interpreter runs it with no width change.
  , ⟨"recordVmDescriptor",              EffectVmEmitRecordRoot.recordVmDescriptor⟩ ]

def main : IO Unit := do
  for e in allEntries do
    IO.println s!"{e.defName}\t{e.desc.name}\t{emitVmJson e.desc}"
