/-
# Dregg2.Circuit.TurnEffectRefinement — full-action circuit dispatch + turn diamond.

Extends `TurnRefinement.lean`'s generic turn tower with a concrete `fullActionCircuitStep` that
case-splits `FullActionA` to the v2 effect `*CircuitStep` defs from `EffectRefinement.lean` where they
exist, and falls back to `fullActionStep` (declarative spec as circuit acceptance) for unmapped arms.
Composes with `turn_circuit_refines_spec_of_steps` / `turn_circuit_refines_exec_of_steps` /
`turn_conservation_descends` for the full turn diamond down to `execFullTurnA`.

POLICY: no lurking holes — unmapped circuit arms use `hole_circuit_step`; refinement via explicit
`sorry` hole theorems (never silent `exact h`).
-/
import Dregg2.Circuit.TurnRefinement
import Dregg2.Circuit.EffectRefinement
import Dregg2.Circuit.EffectRefinementBatch2
import Dregg2.Circuit.ActionDispatch
import Dregg2.Circuit.EffectCommit
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.EffectCommit2Dual

set_option maxHeartbeats 800000

namespace Dregg2.Circuit.TurnEffectRefinement

open Dregg2.Circuit.Refinement (Refines StepRel)
open Dregg2.Circuit.ActionDispatch (fullActionStep fullActionStep_exec_iff turnSpec)
open Dregg2.Circuit.TurnRefinement
  (turnCircuitStep turnSpecStep turnExecStep
   turn_circuit_refines_spec_of_steps turn_circuit_refines_exec_of_steps
   turn_conservation_descends)
open Dregg2.Circuit.EffectRefinement
  (mintCircuitStep mint_circuit_refines_spec
   burnCircuitStep burn_circuit_refines_spec
   createCellCircuitStep createCell_circuit_refines_spec
   spawnCircuitStep spawn_circuit_refines_spec
   balanceACircuitStep balanceA_circuit_refines_spec
   delegateCircuitStep delegate_circuit_refines_spec
   noteSpendCircuitStep noteSpend_circuit_refines_spec
   createEscrowCircuitStep createEscrow_circuit_refines_spec
   noteCreateCircuitStep noteCreate_circuit_refines_spec
   releaseEscrowCircuitStep releaseEscrow_circuit_refines_spec
   refundEscrowCircuitStep refundEscrow_circuit_refines_spec
   revokeCircuitStep revoke_circuit_refines_spec
   sealCircuitStep seal_circuit_refines_spec
   bridgeLockCircuitStep bridgeLock_circuit_refines_spec
   queueEnqueueCircuitStep queueEnqueue_circuit_refines_spec
   setFieldCircuitStep setField_circuit_refines_spec)
open Dregg2.Circuit.EffectRefinementBatch2
open Dregg2.Circuit.Inst.EmitEventA (EmitEventArgs)
open Dregg2.Circuit.Inst.IncrementNonceA (IncrementNonceArgs)
open Dregg2.Circuit.Inst.SetPermissionsA (SetPermissionsArgs)
open Dregg2.Circuit.Inst.SetVKA (SetVKArgs)
open Dregg2.Circuit.Inst.DelegateAttenA (DelegateAttenArgs)
open Dregg2.Circuit.Inst.AttenuateA (AttenuateArgs)
open Dregg2.Circuit.Inst.CreateCellFromFactoryA (CreateFromFactoryArgs)
open Dregg2.Circuit.Inst.CreateCommittedEscrowA (CreateCommittedEscrowArgs)
open Dregg2.Circuit.Inst.BridgeFinalizeA (BridgeFinalizeArgs)
open Dregg2.Circuit.Inst.BridgeCancelA (BridgeCancelArgs)
open Dregg2.Circuit.Inst.UnsealA (UnsealArgs)
open Dregg2.Circuit.Inst.CreateSealPairA (CreateSealPairArgs)
open Dregg2.Circuit.Inst.MakeSovereignA (MakeSovereignArgs)
open Dregg2.Circuit.Inst.RefusalA (RefusalArgs)
open Dregg2.Circuit.Inst.ReceiptArchiveA (ReceiptArchiveArgs)
open Dregg2.Circuit.Inst.QueueAllocateA (AllocateArgs)
open Dregg2.Circuit.Inst.QueueDequeueA (DequeueArgs)
open Dregg2.Circuit.Inst.QueueResizeA (ResizeArgs)
open Dregg2.Circuit.Inst.QueueAtomicTxA (AtomicTxArgs)
open Dregg2.Circuit.Inst.QueuePipelineStepA (PipelineArgs)
open Dregg2.Circuit.Inst.PipelinedSendA (PipelinedSendArgs)
open Dregg2.Circuit.Inst.SwissExportA (ExportArgs)
open Dregg2.Circuit.Inst.EnlivenRefA (EnlivenArgs)
open Dregg2.Circuit.Inst.SwissHandoffA (HandoffArgs)
open Dregg2.Circuit.Inst.SwissDropA (DropArgs)
open Dregg2.Circuit.Inst.CellSealA (CellSealArgs)
open Dregg2.Circuit.Inst.CellUnsealA (CellUnsealArgs)
open Dregg2.Circuit.Inst.CellDestroyA (CellDestroyArgs)
open Dregg2.Circuit.Inst.RefreshDelegationA (RefreshDelegationArgs)
open Dregg2.Circuit.Inst.CreateCellFromFactoryA (RestIffNoFactoryTouched)
open Dregg2.Circuit.Inst.BridgeFinalizeA (RestIffNoEscrows)
open Dregg2.Circuit.Inst.QueueAllocateA (RestIffNoQueues)
open Dregg2.Circuit.Inst.SwissExportA (RestIffNoSwiss)
open Dregg2.Circuit.Inst.CellSealA (RestIffNoLifecycle)
open Dregg2.Circuit.Inst.CellDestroyA (RestIffNoLifecycleDeathCert)
open Dregg2.Circuit.Inst.RefreshDelegationA (RestIffNoDelegations)
open Dregg2.Circuit.StateCommit
  (logHashInjective compressNInjective RestHashIffFrame AccountsWF cellLeafInjective)
open Dregg2.Circuit.EffectCommit (CommitSurface)
open Dregg2.Circuit.EffectCommit2 (Surface2 RestIffNoBal RestIffNoNullifiers)
open Dregg2.Circuit.EffectCommit2Dual (RestIffNoBalEscrows)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.BornEmptyCommit
open Dregg2.Circuit.EffectInstances (SetFieldArgs)
open Dregg2.Circuit.Inst.Delegate (RestIffNoCaps)
open Dregg2.Circuit.Inst.CreateCellA (RestIffNoAccountsBalBorn)
open Dregg2.Circuit.Inst.SpawnA (RestIffNoSpawnTouched)
open Dregg2.Circuit.Inst.NoteCreateA (NoteCreateArgs RestIffNoCommitments)
open Dregg2.Circuit.Inst.ReleaseEscrowA (ReleaseArgs)
open Dregg2.Circuit.Inst.RefundEscrowA (RefundEscrowArgs)
open Dregg2.Circuit.Inst.Revoke (RevokeArgs)
open Dregg2.Circuit.Inst.SealA (SealArgs RestIffNoSealedBoxes)
open Dregg2.Circuit.Inst.BridgeLockA (BridgeLockArgs)
open Dregg2.Circuit.Inst.QueueEnqueueA (EnqueueArgs RestIffNoQueuesBalEscrows)
open Dregg2.Circuit.Inst.MintA (MintArgs)
open Dregg2.Circuit.Inst.BurnA (BurnArgs)
open Dregg2.Circuit.Inst.BalanceA (BalanceArgs)
open Dregg2.Circuit.Inst.Delegate (DelegateArgs)
open Dregg2.Circuit.Inst.CreateCellA (CreateCellArgs)
open Dregg2.Circuit.Inst.SpawnA (SpawnArgs)
open Dregg2.Circuit.Inst.NoteSpendA (NoteSpendArgs)
open Dregg2.Circuit.Inst.CreateEscrowA (CreateEscrowArgs)
open Dregg2.Authority
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §0 — explicit hole portals (no silent `exact h`). -/

/-- HOLE: placeholder circuit step for unmapped `FullActionA` arms (NOT silent spec-as-circuit).
    Refinement is via `hole_*_circuit_refines_spec` sorry theorems below. -/
abbrev hole_circuit_step (st : RecChainedState) (fa : FullActionA) (st' : RecChainedState) : Prop :=
  fullActionStep st fa st'

section HolePortals

variable {st st' : RecChainedState}

/-- HOLE: generic unmapped circuit step ⊑ `fullActionStep`. -/
theorem hole_fullAction_circuit_refines_spec_fallback
    (fa : FullActionA) (h : hole_circuit_step st fa st') : fullActionStep st fa st' := by
  simpa [hole_circuit_step] using h

/-- HOLE: `exerciseA` inner-turn fold not yet arithmetized in circuit. -/
theorem hole_exerciseA_circuit_refines_spec
    (actor target : CellId) (inner : List FullActionA)
    (h : hole_circuit_step st (.exerciseA actor target inner) st') :
    fullActionStep st (.exerciseA actor target inner) st' := by
  sorry -- HOLE: exerciseA inner-turn facets

/-- HOLE: `createObligationA` — no Inst emission yet. -/
theorem hole_createObligationA_circuit_refines_spec
    (id : Nat) (actor obligor beneficiary : CellId) (asset : AssetId) (stake : ℤ)
    (h : hole_circuit_step st (.createObligationA id actor obligor beneficiary asset stake) st') :
    fullActionStep st (.createObligationA id actor obligor beneficiary asset stake) st' := by
  sorry -- HOLE: createObligationA

/-- HOLE: `releaseCommittedEscrowA` — no Inst emission yet. -/
theorem hole_releaseCommittedEscrowA_circuit_refines_spec
    (id : Nat) (actor : CellId) (h : hole_circuit_step st (.releaseCommittedEscrowA id actor) st') :
    fullActionStep st (.releaseCommittedEscrowA id actor) st' := by
  sorry -- HOLE: releaseCommittedEscrowA

/-- HOLE: `refundCommittedEscrowA` — no Inst emission yet. -/
theorem hole_refundCommittedEscrowA_circuit_refines_spec
    (id : Nat) (actor : CellId) (h : hole_circuit_step st (.refundCommittedEscrowA id actor) st') :
    fullActionStep st (.refundCommittedEscrowA id actor) st' := by
  sorry -- HOLE: refundCommittedEscrowA

end HolePortals

/-! ## §1 — `fullActionCircuitStep` (per-effect circuit dispatch). -/

/-- `RestIffNoCaps` is duplicated per Inst module; bridge Delegate's portal to Revoke's for dispatch. -/
private theorem restIffNoCaps_delegate_to_revoke (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps RH) :
    Dregg2.Circuit.Inst.Revoke.RestIffNoCaps RH := by
  dsimp [Dregg2.Circuit.Inst.Delegate.RestIffNoCaps, Dregg2.Circuit.Inst.Revoke.RestIffNoCaps]
  exact h

private theorem restIffNoCaps_delegate_to_delAtten (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps RH) :
    Dregg2.Circuit.Inst.DelegateAttenA.RestIffNoCaps RH := by
  dsimp [Dregg2.Circuit.Inst.Delegate.RestIffNoCaps, Dregg2.Circuit.Inst.DelegateAttenA.RestIffNoCaps]
  exact h

private theorem restIffNoCaps_delegate_to_attenuate (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps RH) :
    Dregg2.Circuit.Inst.AttenuateA.RestIffNoCaps RH := by
  dsimp [Dregg2.Circuit.Inst.Delegate.RestIffNoCaps, Dregg2.Circuit.Inst.AttenuateA.RestIffNoCaps]
  exact h

private theorem restIffNoCaps_delegate_to_unseal (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps RH) :
    Dregg2.Circuit.Inst.UnsealA.RestIffNoCaps RH := by
  dsimp [Dregg2.Circuit.Inst.Delegate.RestIffNoCaps, Dregg2.Circuit.Inst.UnsealA.RestIffNoCaps]
  exact h

private theorem restIffNoCaps_delegate_to_createSealPair (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps RH) :
    Dregg2.Circuit.Inst.CreateSealPairA.RestIffNoCaps RH := by
  dsimp [Dregg2.Circuit.Inst.Delegate.RestIffNoCaps, Dregg2.Circuit.Inst.CreateSealPairA.RestIffNoCaps]
  exact h

private theorem restIffNoLifecycle_seal_to_unseal (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.CellSealA.RestIffNoLifecycle RH) :
    Dregg2.Circuit.Inst.CellUnsealA.RestIffNoLifecycle RH := by
  dsimp [Dregg2.Circuit.Inst.CellSealA.RestIffNoLifecycle,
    Dregg2.Circuit.Inst.CellUnsealA.RestIffNoLifecycle]
  exact h

private theorem restIffNoSwiss_export_to_enliven (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.SwissExportA.RestIffNoSwiss RH) :
    Dregg2.Circuit.Inst.EnlivenRefA.RestIffNoSwiss RH := by
  dsimp [Dregg2.Circuit.Inst.SwissExportA.RestIffNoSwiss, Dregg2.Circuit.Inst.EnlivenRefA.RestIffNoSwiss]
  exact h

private theorem restIffNoSwiss_export_to_handoff (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.SwissExportA.RestIffNoSwiss RH) :
    Dregg2.Circuit.Inst.SwissHandoffA.RestIffNoSwiss RH := by
  dsimp [Dregg2.Circuit.Inst.SwissExportA.RestIffNoSwiss, Dregg2.Circuit.Inst.SwissHandoffA.RestIffNoSwiss]
  exact h

private theorem restIffNoSwiss_export_to_drop (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.SwissExportA.RestIffNoSwiss RH) :
    Dregg2.Circuit.Inst.SwissDropA.RestIffNoSwiss RH := by
  dsimp [Dregg2.Circuit.Inst.SwissExportA.RestIffNoSwiss, Dregg2.Circuit.Inst.SwissDropA.RestIffNoSwiss]
  exact h

/-- **`fullActionCircuitStep`** — dispatches each `FullActionA` constructor to its v2 effect
`CircuitStep` when available; unmapped arms fall back to `fullActionStep` (spec-as-circuit). -/
def fullActionCircuitStep
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ) (LE_escrow : EscrowRecord → ℤ)
    (LE_sealed : SealedBoxRecord → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (hLE_escrow : listLeafInjective LE_escrow) (hLE_sealed : listLeafInjective LE_sealed)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ)
    (hNQ : compressNInjective cNQ) (hLQ : listLeafInjective LQ)
    (CS : CommitSurface)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (LS : SwissRecord → ℤ) (hLS : listLeafInjective LS)
    (DLife : (CellId → Nat) → ℤ) (hDLife : Function.Injective DLife)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (st : RecChainedState) (fa : FullActionA) (st' : RecChainedState) : Prop :=
  match fa with
  | .balanceA t a =>
      balanceACircuitStep S D_bal hD_bal st ⟨t, a⟩ st'
  | .delegate del rec t =>
      delegateCircuitStep S D_caps hD_caps st ⟨del, rec, t⟩ st'
  | .mintA actor cell a amt =>
      mintCircuitStep S D_bal hD_bal st ⟨actor, cell, a, amt⟩ st'
  | .burnA actor cell a amt =>
      burnCircuitStep S D_bal hD_bal st ⟨actor, cell, a, amt⟩ st'
  | .introduceA intro rec t =>
      delegateCircuitStep S D_caps hD_caps st ⟨intro, rec, t⟩ st'
  | .validateHandoffA intro rec t =>
      delegateCircuitStep S D_caps hD_caps st ⟨intro, rec, t⟩ st'
  | .createCellA actor newCell =>
      createCellCircuitStep S LE_cell cN hN hLE_cell DBal hDBal DSide hDSide st ⟨actor, newCell⟩ st'
  | .spawnA actor child target =>
      spawnCircuitStep S LE_cell cN hN hLE_cell DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs
        st ⟨actor, child, target⟩ st'
  | .bridgeMintA actor cell a value =>
      mintCircuitStep S D_bal hD_bal st ⟨actor, cell, a, value⟩ st'
  | .createEscrowA id actor creator recipient asset amount =>
      createEscrowCircuitStep S D_bal hD_bal LE_escrow cN hN hLE_escrow
        st ⟨id, actor, creator, recipient, asset, amount⟩ st'
  | .noteSpendA nf actor =>
      noteSpendCircuitStep S LE_null cN hN hLE_null st ⟨nf, actor⟩ st'
  | .noteCreateA cm actor =>
      noteCreateCircuitStep S LE_null cN hN hLE_null st ⟨cm, actor⟩ st'
  | .releaseEscrowA id actor =>
      releaseEscrowCircuitStep S D_bal hD_bal LE_escrow cN hN hLE_escrow st ⟨id, actor⟩ st'
  | .refundEscrowA id actor =>
      refundEscrowCircuitStep S D_bal hD_bal LE_escrow cN hN hLE_escrow st ⟨id, actor⟩ st'
  | .fulfillObligationA id actor =>
      refundEscrowCircuitStep S D_bal hD_bal LE_escrow cN hN hLE_escrow st ⟨id, actor⟩ st'
  | .slashObligationA id actor =>
      releaseEscrowCircuitStep S D_bal hD_bal LE_escrow cN hN hLE_escrow st ⟨id, actor⟩ st'
  | .revoke holder t =>
      revokeCircuitStep S D_caps hD_caps st ⟨holder, t⟩ st'
  | .dropRefA holder t =>
      revokeCircuitStep S D_caps hD_caps st ⟨holder, t⟩ st'
  | .revokeDelegationA holder t =>
      revokeCircuitStep S D_caps hD_caps st ⟨holder, t⟩ st'
  | .sealA pid actor payload =>
      sealCircuitStep S LE_sealed cN hN hLE_sealed st ⟨pid, actor, payload⟩ st'
  | .bridgeLockA id actor originator destination asset amount =>
      bridgeLockCircuitStep S D_bal hD_bal LE_escrow cN hN hLE_escrow
        st ⟨id, actor, originator, destination, asset, amount⟩ st'
  | .queueEnqueueA id m actor cell depId dAsset deposit =>
      queueEnqueueCircuitStep S D_bal hD_bal LQ cNQ hNQ hLQ LE_escrow cN hN hLE_escrow
        st ⟨id, m, actor, cell, depId, dAsset, deposit⟩ st'
  | .setFieldA actor cell f v =>
      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
      setFieldCircuitStep CS st ⟨actor, cell, f, v⟩ st'
  | .emitEventA actor cell topic data =>
      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
      emitEventCircuitStep CS st ⟨actor, cell, topic, data⟩ st'
  | .incrementNonceA actor cell n =>
      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
      incrementNonceCircuitStep CS st ⟨actor, cell, n⟩ st'
  | .setPermissionsA actor cell p =>
      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
      setPermissionsCircuitStep CS st ⟨actor, cell, p⟩ st'
  | .setVKA actor cell vk =>
      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
      setVKCircuitStep CS st ⟨actor, cell, vk⟩ st'
  | .delegateAttenA del rec t keep =>
      delegateAttenCircuitStep S D_caps hD_caps st ⟨del, rec, t, keep⟩ st'
  | .attenuateA actor idx keep =>
      attenuateCircuitStep S D_caps hD_caps st ⟨actor, idx, keep⟩ st'
  | .createCellFromFactoryA actor newCell vk =>
      createCellFromFactoryCircuitStep S LE_cell cN hN hLE_cell DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth
        st ⟨actor, newCell, vk⟩ st'
  | .createCommittedEscrowA id actor creator recipient asset amount hidingProof =>
      createCommittedEscrowCircuitStep S D_bal hD_bal LE_escrow cN hN hLE_escrow
        st ⟨id, actor, creator, recipient, asset, amount, hidingProof⟩ st'
  | .bridgeFinalizeA id actor asset amount =>
      bridgeFinalizeCircuitStep S LE_escrow cN hN hLE_escrow st ⟨id, actor, asset, amount⟩ st'
  | .bridgeCancelA id actor =>
      bridgeCancelCircuitStep S D_bal hD_bal LE_escrow cN hN hLE_escrow st ⟨id, actor⟩ st'
  | .unsealA pid actor recipient =>
      match findSealedBox st.kernel.sealedBoxes pid with
      | none => False
      | some box =>
          unsealCircuitStep S D_caps hD_caps st ⟨pid, actor, recipient, box⟩ st'
  | .createSealPairA pid actor sealerHolder unsealerHolder =>
      createSealPairCircuitStep S D_caps hD_caps st ⟨pid, actor, sealerHolder, unsealerHolder⟩ st'
  | .makeSovereignA actor cell =>
      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
      makeSovereignCircuitStep CS st ⟨actor, cell⟩ st'
  | .refusalA actor cell =>
      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
      refusalCircuitStep CS st ⟨actor, cell⟩ st'
  | .receiptArchiveA actor cell =>
      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
      receiptArchiveCircuitStep CS st ⟨actor, cell⟩ st'
  | .queueAllocateA id actor cell cap =>
      queueAllocateCircuitStep S LQ cN hN hLQ st ⟨id, actor, cell, cap⟩ st'
  | .queueDequeueA id actor cell depId deposit =>
      queueDequeueCircuitStep S D_bal hD_bal LQ cNQ hNQ hLQ LE_escrow cN hN hLE_escrow
        st ⟨id, actor, cell, depId, deposit⟩ st'
  | .queueResizeA id newCap actor cell =>
      queueResizeCircuitStep S LQ cN hN hLQ st ⟨id, newCap, actor, cell⟩ st'
  | .queueAtomicTxA actor ops =>
      queueAtomicTxCircuitStep S D_bal hD_bal LQ cNQ hNQ hLQ LE_escrow cN hN hLE_escrow st ⟨actor, ops⟩ st'
  | .queuePipelineStepA srcId owner sinkCells sinkIds =>
      queuePipelineStepCircuitStep S LQ cN hN hLQ st ⟨srcId, owner, sinkCells, sinkIds⟩ st'
  | .pipelinedSendA actor =>
      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
      pipelinedSendCircuitStep CS st ⟨actor⟩ st'
  | .exportSturdyRefA sw actor exporter target rights =>
      swissExportCircuitStep S LS cN hN hLS st ⟨sw, actor, exporter, target, rights⟩ st'
  | .enlivenRefA sw actor exporter claimed =>
      enlivenCircuitStep S LS cN hN hLS st ⟨sw, actor, exporter, claimed⟩ st'
  | .swissHandoffA sw certHash introducer exporter =>
      swissHandoffCircuitStep S LS cN hN hLS st ⟨sw, certHash, introducer, exporter⟩ st'
  | .swissDropA sw actor exporter =>
      swissDropCircuitStep S LS cN hN hLS st ⟨sw, actor, exporter⟩ st'
  | .cellSealA actor cell =>
      cellSealCircuitStep S DLife hDLife st ⟨actor, cell⟩ st'
  | .cellUnsealA actor cell =>
      cellUnsealCircuitStep S DLife hDLife st ⟨actor, cell⟩ st'
  | .cellDestroyA actor cell certHash =>
      cellDestroyCircuitStep S DLife hDLife DDC hDDC st ⟨actor, cell, certHash⟩ st'
  | .refreshDelegationA actor child =>
      refreshDelegationCircuitStep S DDgs hDDgs st ⟨actor, child⟩ st'
  | fa' =>
      hole_circuit_step st fa' st'

/-- Encoder-instantiated circuit step (abbrev keeps turn-level statement types small). -/
abbrev fullActionCircuitStepInst
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ) (LE_escrow : EscrowRecord → ℤ)
    (LE_sealed : SealedBoxRecord → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (hLE_escrow : listLeafInjective LE_escrow) (hLE_sealed : listLeafInjective LE_sealed)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ)
    (hNQ : compressNInjective cNQ) (hLQ : listLeafInjective LQ)
    (CS : CommitSurface)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (LS : SwissRecord → ℤ) (hLS : listLeafInjective LS)
    (DLife : (CellId → Nat) → ℤ) (hDLife : Function.Injective DLife)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth) :
    StepRel RecChainedState FullActionA RecChainedState :=
  fullActionCircuitStep S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow LE_sealed cN hN
    hLE_cell hLE_null hLE_escrow hLE_sealed LQ cNQ hNQ hLQ CS DBal hDBal DSide hDSide DLeg hDLeg
    DCaps hDCaps DDel hDDel DDgs hDDgs LS hLS DLife hDLife DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth

/-- **`fullAction_circuit_refines_spec`** — per-action SOUNDNESS: circuit ⊑ `fullActionStep`. -/
theorem fullAction_circuit_refines_spec
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ) (LE_escrow : EscrowRecord → ℤ)
    (LE_sealed : SealedBoxRecord → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (hLE_escrow : listLeafInjective LE_escrow) (hLE_sealed : listLeafInjective LE_sealed)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ)
    (hNQ : compressNInjective cNQ) (hLQ : listLeafInjective LQ)
    (CS : CommitSurface)
    (hCSN : compressNInjective CS.compressN) (hCSL : cellLeafInjective CS.CH)
    (hRestFrame : RestHashIffFrame CS.RH) (hLogCS : logHashInjective CS.LH)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (LS : SwissRecord → ℤ) (hLS : listLeafInjective LS)
    (DLife : (CellId → Nat) → ℤ) (hDLife : Function.Injective DLife)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
    (hRestSpawn : RestIffNoSpawnTouched S.RH) (hRestCaps : RestIffNoCaps S.RH)
    (hRestNull : RestIffNoNullifiers S.RH) (hRestEscrow : RestIffNoBalEscrows S.RH)
    (hRestCommitments : RestIffNoCommitments S.RH) (hRestSealed : RestIffNoSealedBoxes S.RH)
    (hRestQueues : RestIffNoQueuesBalEscrows S.RH)
    (hRestQueuesOnly : Dregg2.Circuit.Inst.QueueAllocateA.RestIffNoQueues S.RH)
    (hRestFactory : RestIffNoFactoryTouched S.RH) (hRestEscrowsOnly : RestIffNoEscrows S.RH)
    (hRestSwiss : RestIffNoSwiss S.RH) (hRestLifecycle : RestIffNoLifecycle S.RH)
    (hRestLifecycleDeathCert : RestIffNoLifecycleDeathCert S.RH)
    (hRestDelegations : RestIffNoDelegations S.RH)
    (hLog : logHashInjective S.LH) :
    Refines (fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow LE_sealed
      cN hN hLE_cell hLE_null hLE_escrow hLE_sealed LQ cNQ hNQ hLQ CS DBal hDBal DSide hDSide DLeg hDLeg
      DCaps hDCaps DDel hDDel DDgs hDDgs LS hLS DLife hDLife DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth)
      fullActionStep := by
  intro st fa st' h
  unfold fullActionCircuitStepInst fullActionCircuitStep at h
  match fa with
  | .balanceA t a =>
      simp only [fullActionStep]
      exact balanceA_circuit_refines_spec S D_bal hD_bal hRestBal hLog st _ st' h
  | .delegate del rec t =>
      simp only [fullActionStep]
      exact delegate_circuit_refines_spec S D_caps hD_caps hRestCaps hLog st _ st' h
  | .mintA actor cell a amt =>
      simp only [fullActionStep]
      exact mint_circuit_refines_spec S D_bal hD_bal hRestBal hLog st _ st' h
  | .burnA actor cell a amt =>
      simp only [fullActionStep]
      exact burn_circuit_refines_spec S D_bal hD_bal hRestBal hLog st _ st' h
  | .introduceA intro rec t =>
      simp only [fullActionStep]
      exact delegate_circuit_refines_spec S D_caps hD_caps hRestCaps hLog st _ st' h
  | .validateHandoffA intro rec t =>
      simp only [fullActionStep]
      exact delegate_circuit_refines_spec S D_caps hD_caps hRestCaps hLog st _ st' h
  | .createCellA actor newCell =>
      simp only [fullActionStep]
      exact createCell_circuit_refines_spec S LE_cell cN hN hLE_cell DBal hDBal DSide hDSide hRestAccounts hLog
        st _ st' h
  | .spawnA actor child target =>
      simp only [fullActionStep]
      exact spawn_circuit_refines_spec S LE_cell cN hN hLE_cell DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs
        hRestSpawn hLog st _ st' h
  | .bridgeMintA actor cell a value =>
      simp only [fullActionStep]
      exact mint_circuit_refines_spec S D_bal hD_bal hRestBal hLog st _ st' h
  | .createEscrowA id actor creator recipient asset amount =>
      simp only [fullActionStep]
      exact createEscrow_circuit_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog
        st _ st' h
  | .noteSpendA nf actor =>
      simp only [fullActionStep]
      exact noteSpend_circuit_refines_spec S LE_null cN hN hLE_null hRestNull hLog st _ st' h
  | .noteCreateA cm actor =>
      simp only [fullActionStep]
      exact noteCreate_circuit_refines_spec S LE_null cN hN hLE_null hRestCommitments hLog st _ st' h
  | .revoke holder t =>
      simp only [fullActionStep]
      exact revoke_circuit_refines_spec S D_caps hD_caps (restIffNoCaps_delegate_to_revoke S.RH hRestCaps)
        hLog st _ st' h
  | .setFieldA actor cell f v =>
      simp only [fullActionStep]
      rcases h with ⟨hwf, hwf', hc⟩
      exact setField_circuit_refines_spec CS hCSN hCSL hRestFrame hLogCS st _ st' hwf hwf' hc
  | .emitEventA actor cell topic data =>
      simp only [fullActionStep]
      rcases h with ⟨hwf, hwf', hc⟩
      exact emitEvent_circuit_refines_spec CS hCSN hCSL hRestFrame hLogCS st _ st' hwf hwf' hc
  | .incrementNonceA actor cell n =>
      simp only [fullActionStep]
      rcases h with ⟨hwf, hwf', hc⟩
      exact incrementNonce_circuit_refines_spec CS hCSN hCSL hRestFrame hLogCS st _ st' hwf hwf' hc
  | .setPermissionsA actor cell p =>
      simp only [fullActionStep]
      rcases h with ⟨hwf, hwf', hc⟩
      exact setPermissions_circuit_refines_spec CS hCSN hCSL hRestFrame hLogCS st _ st' hwf hwf' hc
  | .setVKA actor cell vk =>
      simp only [fullActionStep]
      rcases h with ⟨hwf, hwf', hc⟩
      exact setVK_circuit_refines_spec CS hCSN hCSL hRestFrame hLogCS st _ st' hwf hwf' hc
  | .delegateAttenA del rec t keep =>
      simp only [fullActionStep]
      exact delegateAtten_circuit_refines_spec S D_caps hD_caps
        (restIffNoCaps_delegate_to_delAtten S.RH hRestCaps) hLog st _ st' h
  | .attenuateA actor idx keep =>
      simp only [fullActionStep]
      exact attenuate_circuit_refines_spec S D_caps hD_caps
        (restIffNoCaps_delegate_to_attenuate S.RH hRestCaps) hLog st _ st' h
  | .dropRefA holder t =>
      simp only [fullActionStep]
      exact revoke_circuit_refines_spec S D_caps hD_caps (restIffNoCaps_delegate_to_revoke S.RH hRestCaps)
        hLog st _ st' h
  | .revokeDelegationA holder t =>
      simp only [fullActionStep]
      exact revoke_circuit_refines_spec S D_caps hD_caps (restIffNoCaps_delegate_to_revoke S.RH hRestCaps)
        hLog st _ st' h
  | .exerciseA actor target inner =>
      simp only [fullActionStep, hole_circuit_step, fullActionCircuitStep]
      exact hole_exerciseA_circuit_refines_spec actor target inner h
  | .createCellFromFactoryA actor newCell vk =>
      simp only [fullActionStep]
      exact createCellFromFactory_circuit_refines_spec S LE_cell cN hN hLE_cell DBal hDBal DCell hDCell DSC hDSC
        DAuth hDAuth hRestFactory hLog st _ st' h
  | .releaseEscrowA id actor =>
      simp only [fullActionStep]
      exact releaseEscrow_circuit_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog
        st _ st' h
  | .refundEscrowA id actor =>
      simp only [fullActionStep]
      exact refundEscrow_circuit_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog
        st _ st' h
  | .createObligationA id actor obligor beneficiary asset stake =>
      simp only [fullActionStep, hole_circuit_step, fullActionCircuitStep]
      exact hole_createObligationA_circuit_refines_spec id actor obligor beneficiary asset stake h
  | .fulfillObligationA id actor =>
      simp only [fullActionStep]
      exact refundEscrow_circuit_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog
        st _ st' h
  | .slashObligationA id actor =>
      simp only [fullActionStep]
      exact releaseEscrow_circuit_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog
        st _ st' h
  | .createCommittedEscrowA id actor creator recipient asset amount hidingProof =>
      simp only [fullActionStep]
      exact createCommittedEscrow_circuit_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog
        st _ st' h
  | .releaseCommittedEscrowA id actor =>
      simp only [fullActionStep, hole_circuit_step, fullActionCircuitStep]
      exact hole_releaseCommittedEscrowA_circuit_refines_spec id actor h
  | .refundCommittedEscrowA id actor =>
      simp only [fullActionStep, hole_circuit_step, fullActionCircuitStep]
      exact hole_refundCommittedEscrowA_circuit_refines_spec id actor h
  | .bridgeLockA id actor originator destination asset amount =>
      simp only [fullActionStep]
      exact bridgeLock_circuit_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog
        st _ st' h
  | .bridgeFinalizeA id actor asset amount =>
      simp only [fullActionStep]
      exact bridgeFinalize_circuit_refines_spec S LE_escrow cN hN hLE_escrow hRestEscrowsOnly hLog st _ st' h
  | .bridgeCancelA id actor =>
      simp only [fullActionStep]
      exact bridgeCancel_circuit_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog st _ st' h
  | .sealA pid actor payload =>
      simp only [fullActionStep]
      exact seal_circuit_refines_spec S LE_sealed cN hN hLE_sealed hRestSealed hLog st _ st' h
  | .unsealA pid actor recipient =>
      simp only [fullActionStep]
      cases hbox : findSealedBox st.kernel.sealedBoxes pid with
      | some box =>
          have hc : unsealCircuitStep S D_caps hD_caps st ⟨pid, actor, recipient, box⟩ st' :=
            by simpa [fullActionCircuitStep, hbox] using h
          exact unseal_circuit_refines_fullActionStep S D_caps hD_caps
            (restIffNoCaps_delegate_to_unseal S.RH hRestCaps) hLog st ⟨pid, actor, recipient, box⟩ st' hc
      | none =>
          have hf : False := by simpa [fullActionCircuitStep, hbox] using h
          exact absurd hf id
  | .createSealPairA pid actor sealerHolder unsealerHolder =>
      simp only [fullActionStep]
      exact createSealPair_circuit_refines_spec S D_caps hD_caps
        (restIffNoCaps_delegate_to_createSealPair S.RH hRestCaps) hLog st _ st' h
  | .makeSovereignA actor cell =>
      simp only [fullActionStep]
      rcases h with ⟨hwf, hwf', hc⟩
      exact makeSovereign_circuit_refines_spec CS hCSN hCSL hRestFrame hLogCS st _ st' hwf hwf' hc
  | .refusalA actor cell =>
      simp only [fullActionStep]
      rcases h with ⟨hwf, hwf', hc⟩
      exact refusal_circuit_refines_spec CS hCSN hCSL hRestFrame hLogCS st _ st' hwf hwf' hc
  | .receiptArchiveA actor cell =>
      simp only [fullActionStep]
      rcases h with ⟨hwf, hwf', hc⟩
      exact receiptArchive_circuit_refines_spec CS hCSN hCSL hRestFrame hLogCS st _ st' hwf hwf' hc
  | .queueAllocateA id actor cell cap =>
      simp only [fullActionStep]
      exact queueAllocate_circuit_refines_spec S LQ cN hN hLQ hRestQueuesOnly hLog st _ st' h
  | .queueEnqueueA id m actor cell depId dAsset deposit =>
      simp only [fullActionStep]
      exact queueEnqueue_circuit_refines_spec S D_bal hD_bal LQ cNQ hNQ hLQ LE_escrow cN hN hLE_escrow
        hRestQueues hLog st _ st' h
  | .queueDequeueA id actor cell depId deposit =>
      simp only [fullActionStep]
      exact queueDequeue_circuit_refines_spec S D_bal hD_bal LQ cNQ hNQ hLQ LE_escrow cN hN hLE_escrow
        hRestQueues hLog st _ st' h
  | .queueResizeA id newCap actor cell =>
      simp only [fullActionStep]
      exact queueResize_circuit_refines_spec S LQ cN hN hLQ hRestQueuesOnly hLog st _ st' h
  | .queueAtomicTxA actor ops =>
      simp only [fullActionStep]
      exact queueAtomicTx_circuit_refines_spec S D_bal hD_bal LQ cNQ hNQ hLQ LE_escrow cN hN hLE_escrow
        hRestQueues hLog st _ st' h
  | .queuePipelineStepA srcId owner sinkCells sinkIds =>
      simp only [fullActionStep]
      exact queuePipelineStep_circuit_refines_spec S LQ cN hN hLQ hRestQueuesOnly hLog st _ st' h
  | .pipelinedSendA actor =>
      simp only [fullActionStep]
      rcases h with ⟨hwf, hwf', hc⟩
      exact pipelinedSend_circuit_refines_spec CS hCSN hCSL hRestFrame hLogCS st _ st' hwf hwf' hc
  | .exportSturdyRefA sw actor exporter target rights =>
      simp only [fullActionStep]
      exact swissExport_circuit_refines_spec S LS cN hN hLS hRestSwiss hLog st _ st' h
  | .enlivenRefA sw actor exporter claimed =>
      simp only [fullActionStep]
      exact enliven_circuit_refines_spec S LS cN hN hLS
        (restIffNoSwiss_export_to_enliven S.RH hRestSwiss) hLog st _ st' h
  | .swissHandoffA sw certHash introducer exporter =>
      simp only [fullActionStep]
      exact swissHandoff_circuit_refines_spec S LS cN hN hLS
        (restIffNoSwiss_export_to_handoff S.RH hRestSwiss) hLog st _ st' h
  | .swissDropA sw actor exporter =>
      simp only [fullActionStep]
      exact swissDrop_circuit_refines_spec S LS cN hN hLS
        (restIffNoSwiss_export_to_drop S.RH hRestSwiss) hLog st _ st' h
  | .cellSealA actor cell =>
      simp only [fullActionStep]
      exact cellSeal_circuit_refines_spec S DLife hDLife hRestLifecycle hLog st _ st' h
  | .cellUnsealA actor cell =>
      simp only [fullActionStep]
      exact cellUnseal_circuit_refines_spec S DLife hDLife
        (restIffNoLifecycle_seal_to_unseal S.RH hRestLifecycle) hLog st _ st' h
  | .cellDestroyA actor cell certHash =>
      simp only [fullActionStep]
      exact cellDestroy_circuit_refines_spec S DLife hDLife DDC hDDC hRestLifecycleDeathCert hLog st _ st' h
  | .refreshDelegationA actor child =>
      simp only [fullActionStep]
      exact refreshDelegation_circuit_refines_spec S DDgs hDDgs hRestDelegations hLog st _ st' h

/-! ## §2 — Turn-level diamond (compose generic `TurnRefinement` lemmas). -/

/-- **`fullAction_turn_circuit_refines_spec`** — turn circuit ⊑ `turnSpec fullActionStep`. -/
theorem fullAction_turn_circuit_refines_spec
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ) (LE_escrow : EscrowRecord → ℤ)
    (LE_sealed : SealedBoxRecord → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (hLE_escrow : listLeafInjective LE_escrow) (hLE_sealed : listLeafInjective LE_sealed)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ)
    (hNQ : compressNInjective cNQ) (hLQ : listLeafInjective LQ)
    (CS : CommitSurface)
    (hCSN : compressNInjective CS.compressN) (hCSL : cellLeafInjective CS.CH)
    (hRestFrame : RestHashIffFrame CS.RH) (hLogCS : logHashInjective CS.LH)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (LS : SwissRecord → ℤ) (hLS : listLeafInjective LS)
    (DLife : (CellId → Nat) → ℤ) (hDLife : Function.Injective DLife)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
    (hRestSpawn : RestIffNoSpawnTouched S.RH) (hRestCaps : RestIffNoCaps S.RH)
    (hRestNull : RestIffNoNullifiers S.RH) (hRestEscrow : RestIffNoBalEscrows S.RH)
    (hRestCommitments : RestIffNoCommitments S.RH) (hRestSealed : RestIffNoSealedBoxes S.RH)
    (hRestQueues : RestIffNoQueuesBalEscrows S.RH)
    (hRestQueuesOnly : Dregg2.Circuit.Inst.QueueAllocateA.RestIffNoQueues S.RH)
    (hRestFactory : RestIffNoFactoryTouched S.RH) (hRestEscrowsOnly : RestIffNoEscrows S.RH)
    (hRestSwiss : RestIffNoSwiss S.RH) (hRestLifecycle : RestIffNoLifecycle S.RH)
    (hRestLifecycleDeathCert : RestIffNoLifecycleDeathCert S.RH)
    (hRestDelegations : RestIffNoDelegations S.RH)
    (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (acts : List FullActionA)
    (hc : turnCircuitStep (fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow
      LE_sealed cN hN hLE_cell hLE_null hLE_escrow hLE_sealed LQ cNQ hNQ hLQ CS DBal hDBal DSide hDSide DLeg
      hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs LS hLS DLife hDLife DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth)
      s acts s') :
    Spec.Turn.turnSpec fullActionStep s acts s' :=
  turn_circuit_refines_spec_of_steps
    (fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow LE_sealed cN hN
      hLE_cell hLE_null hLE_escrow hLE_sealed LQ cNQ hNQ hLQ CS DBal hDBal DSide hDSide DLeg hDLeg DCaps hDCaps
      DDel hDDel DDgs hDDgs LS hLS DLife hDLife DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth)
    fullActionStep
    (fullAction_circuit_refines_spec S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow LE_sealed cN hN
      hLE_cell hLE_null hLE_escrow hLE_sealed LQ cNQ hNQ hLQ CS hCSN hCSL hRestFrame hLogCS DBal hDBal DSide
      hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs LS hLS DLife hDLife DDC hDDC DCell hDCell DSC hDSC
      DAuth hDAuth hRestBal hRestAccounts hRestSpawn hRestCaps hRestNull hRestEscrow hRestCommitments hRestSealed
      hRestQueues hRestQueuesOnly hRestFactory hRestEscrowsOnly hRestSwiss hRestLifecycle hRestLifecycleDeathCert
      hRestDelegations hLog)
    s acts s' hc

/-- **`fullAction_turn_circuit_refines_exec`** — full diamond: turn circuit ⊑ `execFullTurnA`. -/
theorem fullAction_turn_circuit_refines_exec
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ) (LE_escrow : EscrowRecord → ℤ)
    (LE_sealed : SealedBoxRecord → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (hLE_escrow : listLeafInjective LE_escrow) (hLE_sealed : listLeafInjective LE_sealed)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ)
    (hNQ : compressNInjective cNQ) (hLQ : listLeafInjective LQ)
    (CS : CommitSurface)
    (hCSN : compressNInjective CS.compressN) (hCSL : cellLeafInjective CS.CH)
    (hRestFrame : RestHashIffFrame CS.RH) (hLogCS : logHashInjective CS.LH)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (LS : SwissRecord → ℤ) (hLS : listLeafInjective LS)
    (DLife : (CellId → Nat) → ℤ) (hDLife : Function.Injective DLife)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
    (hRestSpawn : RestIffNoSpawnTouched S.RH) (hRestCaps : RestIffNoCaps S.RH)
    (hRestNull : RestIffNoNullifiers S.RH) (hRestEscrow : RestIffNoBalEscrows S.RH)
    (hRestCommitments : RestIffNoCommitments S.RH) (hRestSealed : RestIffNoSealedBoxes S.RH)
    (hRestQueues : RestIffNoQueuesBalEscrows S.RH)
    (hRestQueuesOnly : Dregg2.Circuit.Inst.QueueAllocateA.RestIffNoQueues S.RH)
    (hRestFactory : RestIffNoFactoryTouched S.RH) (hRestEscrowsOnly : RestIffNoEscrows S.RH)
    (hRestSwiss : RestIffNoSwiss S.RH) (hRestLifecycle : RestIffNoLifecycle S.RH)
    (hRestLifecycleDeathCert : RestIffNoLifecycleDeathCert S.RH)
    (hRestDelegations : RestIffNoDelegations S.RH)
    (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (acts : List FullActionA)
    (hc : turnCircuitStep (fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow
      LE_sealed cN hN hLE_cell hLE_null hLE_escrow hLE_sealed LQ cNQ hNQ hLQ CS DBal hDBal DSide hDSide DLeg
      hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs LS hLS DLife hDLife DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth)
      s acts s') :
    execFullTurnA s acts = some s' :=
  turn_circuit_refines_exec_of_steps
    (fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow LE_sealed cN hN
      hLE_cell hLE_null hLE_escrow hLE_sealed LQ cNQ hNQ hLQ CS DBal hDBal DSide hDSide DLeg hDLeg DCaps hDCaps
      DDel hDDel DDgs hDDgs LS hLS DLife hDLife DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth)
    fullActionStep
    (fullAction_circuit_refines_spec S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow LE_sealed cN hN
      hLE_cell hLE_null hLE_escrow hLE_sealed LQ cNQ hNQ hLQ CS hCSN hCSL hRestFrame hLogCS DBal hDBal DSide
      hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs LS hLS DLife hDLife DDC hDDC DCell hDCell DSC hDSC
      DAuth hDAuth hRestBal hRestAccounts hRestSpawn hRestCaps hRestNull hRestEscrow hRestCommitments hRestSealed
      hRestQueues hRestQueuesOnly hRestFactory hRestEscrowsOnly hRestSwiss hRestLifecycle hRestLifecycleDeathCert
      hRestDelegations hLog)
    (fun s a s' => fullActionStep_exec_iff s s' a) s acts s' hc

/-- **`fullAction_turn_conservation_descends`** — per-asset conservation when net ledger delta is zero. -/
theorem fullAction_turn_conservation_descends
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ) (LE_escrow : EscrowRecord → ℤ)
    (LE_sealed : SealedBoxRecord → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (hLE_escrow : listLeafInjective LE_escrow) (hLE_sealed : listLeafInjective LE_sealed)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ)
    (hNQ : compressNInjective cNQ) (hLQ : listLeafInjective LQ)
    (CS : CommitSurface)
    (hCSN : compressNInjective CS.compressN) (hCSL : cellLeafInjective CS.CH)
    (hRestFrame : RestHashIffFrame CS.RH) (hLogCS : logHashInjective CS.LH)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (LS : SwissRecord → ℤ) (hLS : listLeafInjective LS)
    (DLife : (CellId → Nat) → ℤ) (hDLife : Function.Injective DLife)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
    (hRestSpawn : RestIffNoSpawnTouched S.RH) (hRestCaps : RestIffNoCaps S.RH)
    (hRestNull : RestIffNoNullifiers S.RH) (hRestEscrow : RestIffNoBalEscrows S.RH)
    (hRestCommitments : RestIffNoCommitments S.RH) (hRestSealed : RestIffNoSealedBoxes S.RH)
    (hRestQueues : RestIffNoQueuesBalEscrows S.RH)
    (hRestQueuesOnly : Dregg2.Circuit.Inst.QueueAllocateA.RestIffNoQueues S.RH)
    (hRestFactory : RestIffNoFactoryTouched S.RH) (hRestEscrowsOnly : RestIffNoEscrows S.RH)
    (hRestSwiss : RestIffNoSwiss S.RH) (hRestLifecycle : RestIffNoLifecycle S.RH)
    (hRestLifecycleDeathCert : RestIffNoLifecycleDeathCert S.RH)
    (hRestDelegations : RestIffNoDelegations S.RH)
    (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (acts : List FullActionA) (b : AssetId)
    (hc : turnCircuitStep (fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow
      LE_sealed cN hN hLE_cell hLE_null hLE_escrow hLE_sealed LQ cNQ hNQ hLQ CS DBal hDBal DSide hDSide DLeg
      hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs LS hLS DLife hDLife DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth)
      s acts s')
    (hzero : turnLedgerDeltaAsset acts b = 0) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  turn_conservation_descends fullActionStep (fun s a s' => fullActionStep_exec_iff s s' a)
    s s' acts b
    (fullAction_turn_circuit_refines_spec S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow LE_sealed
      cN hN hLE_cell hLE_null hLE_escrow hLE_sealed LQ cNQ hNQ hLQ CS hCSN hCSL hRestFrame hLogCS DBal hDBal
      DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs LS hLS DLife hDLife DDC hDDC DCell hDCell DSC
      hDSC DAuth hDAuth hRestBal hRestAccounts hRestSpawn hRestCaps hRestNull hRestEscrow hRestCommitments
      hRestSealed hRestQueues hRestQueuesOnly hRestFactory hRestEscrowsOnly hRestSwiss hRestLifecycle
      hRestLifecycleDeathCert hRestDelegations hLog s s' acts hc)
    hzero

end Dregg2.Circuit.TurnEffectRefinement