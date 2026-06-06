/-
# Dregg2.Circuit.EffectEmitRegistry — central AIR registry (Wave 2).
No `sorry`/`admit`/`axiom`.
-/
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.ActionDispatch
import Dregg2.Circuit.Transfer
import Dregg2.Circuit.SetFieldCommit
import Dregg2.Circuit.CoordinatedTurnEmit
import Dregg2.Circuit.Inst.attenuateA
import Dregg2.Circuit.Inst.balanceA
import Dregg2.Circuit.Inst.bridgeCancelA
import Dregg2.Circuit.Inst.bridgeFinalizeA
import Dregg2.Circuit.Inst.bridgeLockA
import Dregg2.Circuit.Inst.burnA
import Dregg2.Circuit.Inst.cellDestroyA
import Dregg2.Circuit.Inst.cellSealA
import Dregg2.Circuit.Inst.cellUnsealA
import Dregg2.Circuit.Inst.createCellA
import Dregg2.Circuit.Inst.createCellFromFactoryA
import Dregg2.Circuit.Inst.createCommittedEscrowA
import Dregg2.Circuit.Inst.createEscrowA
import Dregg2.Circuit.Inst.createSealPairA
import Dregg2.Circuit.Inst.delegate
import Dregg2.Circuit.Inst.delegateAttenA
import Dregg2.Circuit.Inst.dropRefA
import Dregg2.Circuit.Inst.emitEventA
import Dregg2.Circuit.Inst.enlivenRefA
import Dregg2.Circuit.Inst.exerciseA
import Dregg2.Circuit.Inst.incrementNonceA
import Dregg2.Circuit.Inst.introduceA
import Dregg2.Circuit.Inst.makeSovereignA
import Dregg2.Circuit.Inst.mintA
import Dregg2.Circuit.Inst.noteCreateA
import Dregg2.Circuit.Inst.noteSpendA
import Dregg2.Circuit.Inst.pipelinedSendA
import Dregg2.Circuit.Inst.queueAllocateA
import Dregg2.Circuit.Inst.queueAtomicTxA
import Dregg2.Circuit.Inst.queueDequeueA
import Dregg2.Circuit.Inst.queueEnqueueA
import Dregg2.Circuit.Inst.queuePipelineStepA
import Dregg2.Circuit.Inst.queueResizeA
import Dregg2.Circuit.Inst.receiptArchiveA
import Dregg2.Circuit.Inst.refreshDelegationA
import Dregg2.Circuit.Inst.refundEscrowA
import Dregg2.Circuit.Inst.refusalA
import Dregg2.Circuit.Inst.releaseEscrowA
import Dregg2.Circuit.Inst.revoke
import Dregg2.Circuit.Inst.revokeDelegationA
import Dregg2.Circuit.Inst.sealA
import Dregg2.Circuit.Inst.setPermissionsA
import Dregg2.Circuit.Inst.setVKA
import Dregg2.Circuit.Inst.spawnA
import Dregg2.Circuit.Inst.swissDropA
import Dregg2.Circuit.Inst.swissExportA
import Dregg2.Circuit.Inst.swissHandoffA
import Dregg2.Circuit.Inst.transfer
import Dregg2.Circuit.Inst.unsealA
import Dregg2.Circuit.Inst.validateHandoffA
import Dregg2.Circuit.Poseidon2Emit

namespace Dregg2.Circuit.EffectEmitRegistry

open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.Poseidon2Emit (poseidon2CompressAirName emittedPoseidon2Compress)
open Dregg2.Exec.TurnExecutorFull (FullActionA)

abbrev DescriptorLookup := String → Option EmittedDescriptor

/-- Gadget descriptors (column-indexed `merkle_hash` forms — PART II of `CircuitEmit`). -/
abbrev MerkleGadgetLookup := String → Option EmittedMerkleDescriptor

/-- Wave-4 gadget registry: Merkle membership + Poseidon2 sponge compress. -/
def gadgetEmitRegistry : MerkleGadgetLookup := fun name =>
  if name == merkleAirName then some emittedMerkle
  else if name == poseidon2CompressAirName then some emittedPoseidon2Compress
  else none

def gadgetRegistryCoverage : Nat := 2

/-- Explicit deferred AIR names (fail-closed: registry returns `none` for every `*-HOLE` name). -/
def createObligationAHoleName : String := "dregg-createObligationA-HOLE"
def releaseCommittedEscrowAHoleName : String := "dregg-releaseCommittedEscrowA-HOLE"
def refundCommittedEscrowAHoleName : String := "dregg-refundCommittedEscrowA-HOLE"

/-- All deferred HOLE names (registry must return `none` for each). -/
def holeAirNames : List String :=
  [createObligationAHoleName, releaseCommittedEscrowAHoleName, refundCommittedEscrowAHoleName]

/-- Map each `FullActionA` constructor to its Inst / commit AIR identity (53 mapped + 3 deferred). -/
def actionAirName : FullActionA → String
  | .balanceA _ _ => Dregg2.Circuit.Inst.BalanceA.balanceAAirName
  | .delegate _ _ _ => Dregg2.Circuit.Inst.Delegate.delegateAirName
  | .revoke _ _ => Dregg2.Circuit.Inst.Revoke.revokeAirName
  | .mintA _ _ _ _ => Dregg2.Circuit.Inst.MintA.mintAirName
  | .burnA _ _ _ _ => Dregg2.Circuit.Inst.BurnA.burnAirName
  | .setFieldA _ _ _ _ => Dregg2.Circuit.SetFieldCommit.setFieldAirName
  | .emitEventA _ _ _ _ => Dregg2.Circuit.Inst.EmitEventA.emitEventAAirName
  | .incrementNonceA _ _ _ => Dregg2.Circuit.Inst.IncrementNonceA.incrementNonceAAirName
  | .setPermissionsA _ _ _ => Dregg2.Circuit.Inst.SetPermissionsA.setPermissionsAAirName
  | .setVKA _ _ _ => Dregg2.Circuit.Inst.SetVKA.setVKAAirName
  | .introduceA _ _ _ => Dregg2.Circuit.Inst.IntroduceA.introduceAAirName
  | .delegateAttenA _ _ _ _ => Dregg2.Circuit.Inst.DelegateAttenA.delegateAttenAAirName
  | .attenuateA _ _ _ => Dregg2.Circuit.Inst.AttenuateA.attenuateAAirName
  | .dropRefA _ _ => Dregg2.Circuit.Inst.DropRefA.dropRefAAirName
  | .revokeDelegationA _ _ => Dregg2.Circuit.Inst.RevokeDelegationA.revokeDelegationAAirName
  | .validateHandoffA _ _ _ => Dregg2.Circuit.Inst.ValidateHandoffA.validateHandoffAAirName
  | .exerciseA _ _ _ => Dregg2.Circuit.Inst.ExerciseA.exerciseAAirName
  | .createCellA _ _ => Dregg2.Circuit.Inst.CreateCellA.createCellAAirName
  | .createCellFromFactoryA _ _ _ => Dregg2.Circuit.Inst.CreateCellFromFactoryA.createCellFromFactoryAAirName
  | .spawnA _ _ _ => Dregg2.Circuit.Inst.SpawnA.spawnAAirName
  | .bridgeMintA _ _ _ _ => Dregg2.Circuit.Inst.MintA.mintAirName
  | .createEscrowA _ _ _ _ _ _ => Dregg2.Circuit.Inst.CreateEscrowA.createEscrowAAirName
  | .releaseEscrowA _ _ => Dregg2.Circuit.Inst.ReleaseEscrowA.releaseEscrowAAirName
  | .refundEscrowA _ _ => Dregg2.Circuit.Inst.RefundEscrowA.refundEscrowAAirName
  | .createObligationA _ _ _ _ _ _ => createObligationAHoleName
  | .fulfillObligationA _ _ => Dregg2.Circuit.Inst.RefundEscrowA.refundEscrowAAirName
  | .slashObligationA _ _ => Dregg2.Circuit.Inst.ReleaseEscrowA.releaseEscrowAAirName
  | .noteSpendA _ _ => Dregg2.Circuit.Inst.NoteSpendA.noteSpendAAirName
  | .noteCreateA _ _ => Dregg2.Circuit.Inst.NoteCreateA.noteCreateAAirName
  | .createCommittedEscrowA _ _ _ _ _ _ _ => Dregg2.Circuit.Inst.CreateCommittedEscrowA.createCommittedEscrowAAirName
  | .releaseCommittedEscrowA _ _ => releaseCommittedEscrowAHoleName
  | .refundCommittedEscrowA _ _ => refundCommittedEscrowAHoleName
  | .bridgeLockA _ _ _ _ _ _ => Dregg2.Circuit.Inst.BridgeLockA.bridgeLockAAirName
  | .bridgeFinalizeA _ _ _ _ => Dregg2.Circuit.Inst.BridgeFinalizeA.bridgeFinalizeAAirName
  | .bridgeCancelA _ _ => Dregg2.Circuit.Inst.BridgeCancelA.bridgeCancelAAirName
  | .sealA _ _ _ => Dregg2.Circuit.Inst.SealA.sealAAirName
  | .unsealA _ _ _ => Dregg2.Circuit.Inst.UnsealA.unsealAAirName
  | .createSealPairA _ _ _ _ => Dregg2.Circuit.Inst.CreateSealPairA.createSealPairAAirName
  | .makeSovereignA _ _ => Dregg2.Circuit.Inst.MakeSovereignA.makeSovereignAAirName
  | .refusalA _ _ => Dregg2.Circuit.Inst.RefusalA.refusalAAirName
  | .receiptArchiveA _ _ => Dregg2.Circuit.Inst.ReceiptArchiveA.receiptArchiveAAirName
  | .queueAllocateA _ _ _ _ => Dregg2.Circuit.Inst.QueueAllocateA.queueAllocateAAirName
  | .queueEnqueueA _ _ _ _ _ _ _ => Dregg2.Circuit.Inst.QueueEnqueueA.queueEnqueueAAirName
  | .queueDequeueA _ _ _ _ _ => Dregg2.Circuit.Inst.QueueDequeueA.queueDequeueAAirName
  | .queueResizeA _ _ _ _ => Dregg2.Circuit.Inst.QueueResizeA.queueResizeAAirName
  | .queueAtomicTxA _ _ => Dregg2.Circuit.Inst.QueueAtomicTxA.queueAtomicTxAAirName
  | .queuePipelineStepA _ _ _ _ => Dregg2.Circuit.Inst.QueuePipelineStepA.queuePipelineStepAAirName
  | .pipelinedSendA _ => Dregg2.Circuit.Inst.PipelinedSendA.pipelinedSendAAirName
  | .exportSturdyRefA _ _ _ _ _ => Dregg2.Circuit.Inst.SwissExportA.swissExportAAirName
  | .enlivenRefA _ _ _ _ => Dregg2.Circuit.Inst.EnlivenRefA.enlivenRefAAirName
  | .swissHandoffA _ _ _ _ => Dregg2.Circuit.Inst.SwissHandoffA.swissHandoffAAirName
  | .swissDropA _ _ _ => Dregg2.Circuit.Inst.SwissDropA.swissDropAAirName
  | .cellSealA _ _ => Dregg2.Circuit.Inst.CellSealA.cellSealAAirName
  | .cellUnsealA _ _ => Dregg2.Circuit.Inst.CellUnsealA.cellUnsealAAirName
  | .cellDestroyA _ _ _ => Dregg2.Circuit.Inst.CellDestroyA.cellDestroyAAirName
  | .refreshDelegationA _ _ => Dregg2.Circuit.Inst.RefreshDelegationA.refreshDelegationAAirName

def actionAirNameCoverage : Nat := 56

def effectEmitRegistry : DescriptorLookup := fun name =>
  if name == Dregg2.Circuit.Transfer.transferAirName then some Dregg2.Circuit.Transfer.emittedTransfer else if name == Dregg2.Circuit.SetFieldCommit.setFieldAirName then some Dregg2.Circuit.SetFieldCommit.emittedSetField else if name == Dregg2.Circuit.CoordinatedTurnEmit.coordinatedTurnAirName then some Dregg2.Circuit.CoordinatedTurnEmit.emittedCoordinatedTurn else if name == Dregg2.Circuit.Inst.AttenuateA.attenuateAAirName then some Dregg2.Circuit.Inst.AttenuateA.attenuateAEmitted else if name == Dregg2.Circuit.Inst.BalanceA.balanceAAirName then some Dregg2.Circuit.Inst.BalanceA.balanceAEmitted else if name == Dregg2.Circuit.Inst.BridgeCancelA.bridgeCancelAAirName then some Dregg2.Circuit.Inst.BridgeCancelA.bridgeCancelAEmitted else if name == Dregg2.Circuit.Inst.BridgeFinalizeA.bridgeFinalizeAAirName then some Dregg2.Circuit.Inst.BridgeFinalizeA.bridgeFinalizeAEmitted else if name == Dregg2.Circuit.Inst.BridgeLockA.bridgeLockAAirName then some Dregg2.Circuit.Inst.BridgeLockA.bridgeLockAEmitted else if name == Dregg2.Circuit.Inst.BurnA.burnAirName then some Dregg2.Circuit.Inst.BurnA.burnEmitted else if name == Dregg2.Circuit.Inst.CellDestroyA.cellDestroyAAirName then some Dregg2.Circuit.Inst.CellDestroyA.cellDestroyAEmitted else if name == Dregg2.Circuit.Inst.CellSealA.cellSealAAirName then some Dregg2.Circuit.Inst.CellSealA.cellSealAEmitted else if name == Dregg2.Circuit.Inst.CellUnsealA.cellUnsealAAirName then some Dregg2.Circuit.Inst.CellUnsealA.cellUnsealAEmitted else if name == Dregg2.Circuit.Inst.CreateCellA.createCellAAirName then some Dregg2.Circuit.Inst.CreateCellA.createCellAEmitted else if name == Dregg2.Circuit.Inst.CreateCellFromFactoryA.createCellFromFactoryAAirName then some Dregg2.Circuit.Inst.CreateCellFromFactoryA.createCellFromFactoryAEmitted else if name == Dregg2.Circuit.Inst.CreateCommittedEscrowA.createCommittedEscrowAAirName then some Dregg2.Circuit.Inst.CreateCommittedEscrowA.createCommittedEscrowAEmitted else if name == Dregg2.Circuit.Inst.CreateEscrowA.createEscrowAAirName then some Dregg2.Circuit.Inst.CreateEscrowA.createEscrowAEmitted else if name == Dregg2.Circuit.Inst.CreateSealPairA.createSealPairAAirName then some Dregg2.Circuit.Inst.CreateSealPairA.createSealPairAEmitted else if name == Dregg2.Circuit.Inst.Delegate.delegateAirName then some Dregg2.Circuit.Inst.Delegate.delegateEmitted else if name == Dregg2.Circuit.Inst.DelegateAttenA.delegateAttenAAirName then some Dregg2.Circuit.Inst.DelegateAttenA.delegateAttenAEmitted else if name == Dregg2.Circuit.Inst.DropRefA.dropRefAAirName then some Dregg2.Circuit.Inst.DropRefA.dropRefAEmitted else if name == Dregg2.Circuit.Inst.EmitEventA.emitEventAAirName then some Dregg2.Circuit.Inst.EmitEventA.emitEventAEmitted else if name == Dregg2.Circuit.Inst.EnlivenRefA.enlivenRefAAirName then some Dregg2.Circuit.Inst.EnlivenRefA.enlivenRefAEmitted else if name == Dregg2.Circuit.Inst.ExerciseA.exerciseAAirName then some Dregg2.Circuit.Inst.ExerciseA.exerciseAEmitted else if name == Dregg2.Circuit.Inst.IncrementNonceA.incrementNonceAAirName then some Dregg2.Circuit.Inst.IncrementNonceA.incrementNonceAEmitted else if name == Dregg2.Circuit.Inst.IntroduceA.introduceAAirName then some Dregg2.Circuit.Inst.IntroduceA.introduceAEmitted else if name == Dregg2.Circuit.Inst.MakeSovereignA.makeSovereignAAirName then some Dregg2.Circuit.Inst.MakeSovereignA.makeSovereignAEmitted else if name == Dregg2.Circuit.Inst.MintA.mintAirName then some Dregg2.Circuit.Inst.MintA.mintEmitted else if name == Dregg2.Circuit.Inst.NoteCreateA.noteCreateAAirName then some Dregg2.Circuit.Inst.NoteCreateA.noteCreateAEmitted else if name == Dregg2.Circuit.Inst.NoteSpendA.noteSpendAAirName then some Dregg2.Circuit.Inst.NoteSpendA.noteSpendAEmitted else if name == Dregg2.Circuit.Inst.PipelinedSendA.pipelinedSendAAirName then some Dregg2.Circuit.Inst.PipelinedSendA.pipelinedSendAEmitted else if name == Dregg2.Circuit.Inst.QueueAllocateA.queueAllocateAAirName then some Dregg2.Circuit.Inst.QueueAllocateA.queueAllocateAEmitted else if name == Dregg2.Circuit.Inst.QueueAtomicTxA.queueAtomicTxAAirName then some Dregg2.Circuit.Inst.QueueAtomicTxA.queueAtomicTxAEmitted else if name == Dregg2.Circuit.Inst.QueueDequeueA.queueDequeueAAirName then some Dregg2.Circuit.Inst.QueueDequeueA.queueDequeueAEmitted else if name == Dregg2.Circuit.Inst.QueueEnqueueA.queueEnqueueAAirName then some Dregg2.Circuit.Inst.QueueEnqueueA.queueEnqueueAEmitted else if name == Dregg2.Circuit.Inst.QueuePipelineStepA.queuePipelineStepAAirName then some Dregg2.Circuit.Inst.QueuePipelineStepA.queuePipelineStepAEmitted else if name == Dregg2.Circuit.Inst.QueueResizeA.queueResizeAAirName then some Dregg2.Circuit.Inst.QueueResizeA.queueResizeAEmitted else if name == Dregg2.Circuit.Inst.ReceiptArchiveA.receiptArchiveAAirName then some Dregg2.Circuit.Inst.ReceiptArchiveA.receiptArchiveAEmitted else if name == Dregg2.Circuit.Inst.RefreshDelegationA.refreshDelegationAAirName then some Dregg2.Circuit.Inst.RefreshDelegationA.refreshDelegationAEmitted else if name == Dregg2.Circuit.Inst.RefundEscrowA.refundEscrowAAirName then some Dregg2.Circuit.Inst.RefundEscrowA.refundEscrowAEmitted else if name == Dregg2.Circuit.Inst.RefusalA.refusalAAirName then some Dregg2.Circuit.Inst.RefusalA.refusalAEmitted else if name == Dregg2.Circuit.Inst.ReleaseEscrowA.releaseEscrowAAirName then some Dregg2.Circuit.Inst.ReleaseEscrowA.releaseEscrowAEmitted else if name == Dregg2.Circuit.Inst.Revoke.revokeAirName then some Dregg2.Circuit.Inst.Revoke.revokeEmitted else if name == Dregg2.Circuit.Inst.RevokeDelegationA.revokeDelegationAAirName then some Dregg2.Circuit.Inst.RevokeDelegationA.revokeDelegationAEmitted else if name == Dregg2.Circuit.Inst.SealA.sealAAirName then some Dregg2.Circuit.Inst.SealA.sealAEmitted else if name == Dregg2.Circuit.Inst.SetPermissionsA.setPermissionsAAirName then some Dregg2.Circuit.Inst.SetPermissionsA.setPermissionsAEmitted else if name == Dregg2.Circuit.Inst.SetVKA.setVKAAirName then some Dregg2.Circuit.Inst.SetVKA.setVKAEmitted else if name == Dregg2.Circuit.Inst.SpawnA.spawnAAirName then some Dregg2.Circuit.Inst.SpawnA.spawnAEmitted else if name == Dregg2.Circuit.Inst.SwissDropA.swissDropAAirName then some Dregg2.Circuit.Inst.SwissDropA.swissDropAEmitted else if name == Dregg2.Circuit.Inst.SwissExportA.swissExportAAirName then some Dregg2.Circuit.Inst.SwissExportA.swissExportAEmitted else if name == Dregg2.Circuit.Inst.SwissHandoffA.swissHandoffAAirName then some Dregg2.Circuit.Inst.SwissHandoffA.swissHandoffAEmitted else if name == Dregg2.Circuit.Inst.Transfer.transferAirName then some Dregg2.Circuit.Inst.Transfer.transferEmitted else if name == Dregg2.Circuit.Inst.UnsealA.unsealAAirName then some Dregg2.Circuit.Inst.UnsealA.unsealAEmitted else if name == Dregg2.Circuit.Inst.ValidateHandoffA.validateHandoffAAirName then some Dregg2.Circuit.Inst.ValidateHandoffA.validateHandoffAEmitted else none

def registryCoverage : Nat := 53
#guard (effectEmitRegistry createObligationAHoleName == none)
#guard (effectEmitRegistry releaseCommittedEscrowAHoleName == none)
#guard (effectEmitRegistry refundCommittedEscrowAHoleName == none)
#guard (∀ name ∈ holeAirNames, effectEmitRegistry name == none)
#guard (effectEmitRegistry Dregg2.Circuit.Inst.MintA.mintAirName).isSome
#guard (effectEmitRegistry Dregg2.Circuit.Inst.Delegate.delegateAirName).isSome
#guard (gadgetEmitRegistry poseidon2CompressAirName).isSome
#guard (gadgetEmitRegistry merkleAirName).isSome
#guard emittedPoseidon2Compress.name == poseidon2CompressAirName

end Dregg2.Circuit.EffectEmitRegistry