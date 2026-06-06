/-
# Dregg2.Circuit.TurnEmit — turn-level witnesses linked to per-effect emitted AIRs.

Maps each `FullActionA` constructor to its Inst AIR name (`actionAirName`), checks per-step
`StepEmittedSat` against a descriptor lookup, and folds whole-turn satisfaction (`turnEmittedSat`)
through an abstract root-compress chain (reusing `TurnWitness.foldStepRoots`). Soundness composes
per-step emitted→spec refinement (EffectRefinement diamonds where available, or generic circuit step)
to `turnSpec`, then to `execFullTurnA` via `ActionDispatch.execFullTurnA_iff_turnSpec`.

POLICY: no lurking holes — unproved per-step arms use explicit `sorry` (never silent fallback).
-/
import Dregg2.Circuit.TurnWitness
import Dregg2.Circuit.ActionDispatch
import Dregg2.Circuit.TurnRefinement
import Dregg2.Circuit.EffectRefinement
import Dregg2.Circuit.EffectEmittedRefinement
import Dregg2.Circuit.EffectEmitRegistry
import Dregg2.Circuit.TurnEffectRefinement
import Dregg2.Circuit.Inst.mintA
import Dregg2.Circuit.Inst.burnA
import Dregg2.Circuit.Inst.attenuateA
import Dregg2.Circuit.Inst.emitEventA
import Dregg2.Circuit.Inst.incrementNonceA
import Dregg2.Circuit.Inst.setPermissionsA
import Dregg2.Circuit.Inst.setVKA
import Dregg2.Circuit.Inst.delegateAttenA
import Dregg2.Circuit.Inst.createCellFromFactoryA
import Dregg2.Circuit.Inst.createCommittedEscrowA
import Dregg2.Circuit.Inst.bridgeFinalizeA
import Dregg2.Circuit.Inst.bridgeCancelA
import Dregg2.Circuit.Inst.unsealA
import Dregg2.Circuit.Inst.createSealPairA
import Dregg2.Circuit.Inst.makeSovereignA
import Dregg2.Circuit.Inst.refusalA
import Dregg2.Circuit.Inst.receiptArchiveA
import Dregg2.Circuit.Inst.queueAllocateA
import Dregg2.Circuit.Inst.queueDequeueA
import Dregg2.Circuit.Inst.queueResizeA
import Dregg2.Circuit.Inst.queueAtomicTxA
import Dregg2.Circuit.Inst.queuePipelineStepA
import Dregg2.Circuit.Inst.pipelinedSendA
import Dregg2.Circuit.Inst.swissExportA
import Dregg2.Circuit.Inst.enlivenRefA
import Dregg2.Circuit.Inst.swissHandoffA
import Dregg2.Circuit.Inst.swissDropA
import Dregg2.Circuit.Inst.cellSealA
import Dregg2.Circuit.Inst.cellUnsealA
import Dregg2.Circuit.Inst.cellDestroyA
import Dregg2.Circuit.Inst.refreshDelegationA
import Dregg2.Exec.CircuitEmit
import Dregg2.Exec.RecordKernel

set_option maxHeartbeats 800000

namespace Dregg2.Circuit.TurnEmit

open Dregg2.Circuit
open Dregg2.Circuit.TurnWitness
  (StepWitness TurnWitness stepWitnessDigest foldStepRoots turnWitnessSatisfies)
open Dregg2.Circuit.ActionDispatch
  (actionTag fullActionStep turnSpec turnSpec_eq_spec execFullTurnA_iff_turnSpec)
open Dregg2.Circuit.TurnRefinement (turnSpec_of_turnStateChain)
open Dregg2.Circuit.EffectEmitRegistry
  (effectEmitRegistry actionAirName createObligationAHoleName releaseCommittedEscrowAHoleName
   refundCommittedEscrowAHoleName holeAirNames actionAirNameCoverage registryCoverage)
open Dregg2.Circuit.Inst.MintA (mintAirName mintEmitted mintDescriptorJson)
open Dregg2.Circuit.Inst.BurnA (burnAirName burnEmitted burnDescriptorJson)
open Dregg2.Authority
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.EffectCommit2 (encodeE2)
open Dregg2.Circuit.EffectCommit2Dual (encodeE2Dual)
open Dregg2.Circuit.EffectCommit3 (encodeE2Triple)
open Dregg2.Circuit.EffectCommit5 (encodeE2Quint)
open Dregg2.Circuit.EffectCommit (encodeE)
open Dregg2.Circuit.EffectInstances (setFieldE)
open Dregg2.Exec.CircuitEmit (EmittedDescriptor satisfiedEmitted emitDescriptorJson)
open Dregg2.Circuit.EffectEmittedRefinement
open Dregg2.Circuit.TurnEffectRefinement
  (fullActionCircuitStep fullActionCircuitStepInst fullAction_circuit_refines_spec hole_circuit_step)
open Dregg2.Circuit.Inst.SealA (SealArgs)
open Dregg2.Circuit.Inst.BridgeLockA (BridgeLockArgs)
open Dregg2.Circuit.Inst.QueueEnqueueA (EnqueueArgs)
open Dregg2.Circuit.Inst.CreateEscrowA (CreateEscrowArgs)
open Dregg2.Circuit.Inst.NoteSpendA (NoteSpendArgs)
open Dregg2.Circuit.Inst.NoteCreateA (NoteCreateArgs)
open Dregg2.Circuit.Inst.CreateCellA (CreateCellArgs)
open Dregg2.Circuit.Inst.SpawnA (SpawnArgs)
open Dregg2.Circuit.Inst.MintA (MintArgs)
open Dregg2.Circuit.Inst.BurnA (BurnArgs)
open Dregg2.Circuit.Inst.Delegate (DelegateArgs)
open Dregg2.Circuit.Inst.Revoke (RevokeArgs)
open Dregg2.Circuit.Inst.ReleaseEscrowA (ReleaseArgs)
open Dregg2.Circuit.Inst.RefundEscrowA (RefundEscrowArgs)
open Dregg2.Circuit.Inst.BalanceA (BalanceArgs balanceAE)
open Dregg2.Circuit.Inst.MintA (mintE)
open Dregg2.Circuit.Inst.BurnA (burnE)
open Dregg2.Circuit.Inst.Delegate (delegateE)
open Dregg2.Circuit.Inst.CreateCellA (createCellE)
open Dregg2.Circuit.Inst.SpawnA (spawnE)
open Dregg2.Circuit.Inst.CreateEscrowA (createEscrowE)
open Dregg2.Circuit.Inst.NoteSpendA (noteSpendE)
open Dregg2.Circuit.Inst.NoteCreateA (noteCreateE)
open Dregg2.Circuit.Inst.ReleaseEscrowA (releaseEscrowE)
open Dregg2.Circuit.Inst.RefundEscrowA (refundEscrowE)
open Dregg2.Circuit.Inst.Revoke (revokeE)
open Dregg2.Circuit.Inst.SealA (sealE)
open Dregg2.Circuit.Inst.BridgeLockA (bridgeLockE)
open Dregg2.Circuit.Inst.QueueEnqueueA (queueEnqueueE)
open Dregg2.Circuit.StateCommit
  (logHashInjective compressNInjective RestHashIffFrame AccountsWF cellLeafInjective)
open Dregg2.Circuit.EffectCommit (CommitSurface)
open Dregg2.Circuit.EffectCommit2 (Surface2 RestIffNoBal RestIffNoNullifiers)
open Dregg2.Circuit.EffectCommit2Dual (RestIffNoBalEscrows)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.BornEmptyCommit
open Dregg2.Circuit.Inst.Delegate (RestIffNoCaps)
open Dregg2.Circuit.Inst.CreateCellA (RestIffNoAccountsBalBorn)
open Dregg2.Circuit.Inst.SpawnA (RestIffNoSpawnTouched)
open Dregg2.Circuit.Inst.NoteCreateA (RestIffNoCommitments)
open Dregg2.Circuit.Inst.SealA (RestIffNoSealedBoxes)
open Dregg2.Circuit.Inst.QueueEnqueueA (RestIffNoQueuesBalEscrows)
open Dregg2.Circuit.Inst.AttenuateA (attenuateE AttenuateArgs)
open Dregg2.Circuit.Inst.EmitEventA (emitEventE EmitEventArgs)
open Dregg2.Circuit.Inst.IncrementNonceA (incrementNonceE incrementNonceAAirName IncrementNonceArgs)
open Dregg2.Circuit.Inst.SetPermissionsA (setPermissionsE setPermissionsAAirName SetPermissionsArgs)
open Dregg2.Circuit.Inst.SetVKA (setVKE setVKAAirName SetVKArgs)
open Dregg2.Circuit.Inst.DelegateAttenA (delegateAttenE DelegateAttenArgs)
open Dregg2.Circuit.Inst.CreateCellFromFactoryA
  (createFromFactoryE createCellFromFactoryAAirName CreateFromFactoryArgs RestIffNoFactoryTouched)
open Dregg2.Circuit.Inst.CreateCommittedEscrowA (createCommittedEscrowE CreateCommittedEscrowArgs)
open Dregg2.Circuit.Inst.BridgeFinalizeA (bridgeFinalizeE BridgeFinalizeArgs RestIffNoEscrows)
open Dregg2.Circuit.Inst.BridgeCancelA (bridgeCancelE BridgeCancelArgs)
open Dregg2.Circuit.Inst.UnsealA (unsealE UnsealArgs)
open Dregg2.Circuit.Inst.CreateSealPairA (createSealPairE CreateSealPairArgs)
open Dregg2.Circuit.Inst.MakeSovereignA (makeSovereignE makeSovereignAAirName MakeSovereignArgs)
open Dregg2.Circuit.Inst.RefusalA (refusalE refusalAAirName RefusalArgs)
open Dregg2.Circuit.Inst.ReceiptArchiveA (receiptArchiveE receiptArchiveAAirName ReceiptArchiveArgs)
open Dregg2.Circuit.Inst.QueueAllocateA (queueAllocateE AllocateArgs RestIffNoQueues)
open Dregg2.Circuit.Inst.QueueDequeueA (queueDequeueE DequeueArgs)
open Dregg2.Circuit.Inst.QueueResizeA (queueResizeE ResizeArgs)
open Dregg2.Circuit.Inst.QueueAtomicTxA (queueAtomicTxE AtomicTxArgs)
open Dregg2.Circuit.Inst.QueuePipelineStepA (queuePipelineStepE PipelineArgs)
open Dregg2.Circuit.Inst.PipelinedSendA (pipelinedSendE pipelinedSendAAirName PipelinedSendArgs)
open Dregg2.Circuit.Inst.SwissExportA (swissExportE ExportArgs RestIffNoSwiss)
open Dregg2.Circuit.Inst.EnlivenRefA (enlivenE EnlivenArgs)
open Dregg2.Circuit.Inst.SwissHandoffA (swissHandoffE)
open Dregg2.Circuit.Inst.SwissDropA (swissDropE DropArgs)
open Dregg2.Circuit.Inst.CellSealA (cellSealE CellSealArgs RestIffNoLifecycle)
open Dregg2.Circuit.Inst.CellUnsealA (cellUnsealE CellUnsealArgs)
open Dregg2.Circuit.Inst.CellDestroyA (cellDestroyE CellDestroyArgs RestIffNoLifecycleDeathCert)
open Dregg2.Circuit.Inst.RefreshDelegationA (refreshDelegationE RefreshDelegationArgs RestIffNoDelegations)
open Dregg2.Circuit.BornEmptyCommit (BornEmptyAuthorityTables)
open Dregg2.Exec (findSealedBox)

/-! ## §0 — decidability (for concrete `#guard`s / `#eval`s). -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — `actionAirName` + registry (re-exported from `EffectEmitRegistry`). -/

/-! ## §2 — Descriptor lookup + per-step emitted satisfaction. -/

/-- AIR-name registry lookup: the Rust `lean_descriptor_air` registry portal. -/
abbrev DescriptorLookup := String → Option EmittedDescriptor

/-- Decode abstract wire bytes (`List ℤ`) into a circuit `Assignment` (out-of-range wires = 0). -/
def assignmentOf (ws : List ℤ) : Assignment :=
  fun v => ws.getD v 0

/-- **`stepEmittedSat`** / **`StepEmittedSat`** — one step's emitted witness: tag matches the action,
and the looked-up descriptor is satisfied on the step's assignment bytes. -/
def stepEmittedSat (lookup : DescriptorLookup) (sw : StepWitness)
    (_st _st' : RecChainedState) (fa : FullActionA) : Prop :=
  sw.tag = actionTag fa ∧
  ∃ d, lookup (actionAirName fa) = some d ∧
    satisfiedEmitted d (assignmentOf sw.assignment)

/-- Alias matching the Wave-1 naming convention (`StepEmittedSat`). -/
abbrev StepEmittedSat := stepEmittedSat

/-- **`descriptorLookup_of_actionAirName`** — when the registry resolves `actionAirName fa`, per-step
emitted satisfaction reduces to tag match + `satisfiedEmitted` on the resolved descriptor. -/
theorem descriptorLookup_of_actionAirName (lookup : DescriptorLookup) (fa : FullActionA)
    (d : EmittedDescriptor) (hlookup : lookup (actionAirName fa) = some d) :
    ∀ sw (st st' : RecChainedState), stepEmittedSat lookup sw st st' fa ↔
      sw.tag = actionTag fa ∧ satisfiedEmitted d (assignmentOf sw.assignment) := by
  intro sw st st'
  dsimp [stepEmittedSat]
  constructor
  · rintro ⟨htag, d', hfind, hsat⟩
    have : d' = d := Option.some.inj (hfind.symm.trans hlookup)
    subst this
    exact ⟨htag, hsat⟩
  · rintro ⟨htag, hsat⟩
    exact ⟨htag, d, hlookup, hsat⟩

/-! ## §3 — Default registry (central `EffectEmitRegistry`). -/

/-- **`defaultDescriptorLookup`** — the Wave-2 central registry (53 Inst/commit AIRs + coordinated). -/
abbrev defaultDescriptorLookup : DescriptorLookup := effectEmitRegistry

/-- Mint+burn demo lookup (alias of the default registry). -/
abbrev demoMintBurnLookup : DescriptorLookup := defaultDescriptorLookup

/-! ## §4 — Whole-turn emitted satisfaction (root chain + state chain + per-step emitted). -/

/-- **`TurnEmittedChain`** — turn-level emitted witness: boundary roots fold under `compress`
(`TurnWitness.foldStepRoots`), states chain left-to-right, and every step satisfies its emitted AIR. -/
structure TurnEmittedChain (lookup : DescriptorLookup) (compress : ℤ → ℤ → ℤ)
    (stepRoot : StepWitness → ℤ) (s : RecChainedState) (acts : List FullActionA)
    (s' : RecChainedState) (w : TurnWitness) where
  steps_len : acts.length = w.steps.length
  root_chain : turnWitnessSatisfies compress stepRoot w
  chain : List RecChainedState
  chain_len : chain.length = acts.length + 1
  chain_head : chain[0]'(by rw [chain_len]; omega) = s
  chain_last : chain[acts.length]'(by rw [chain_len]; omega) = s'
  step_sat :
    ∀ (i : Fin acts.length),
      stepEmittedSat lookup (w.steps[i]) (chain[i.val]'(by rw [chain_len]; omega))
        (chain[i.val + 1]'(by rw [chain_len]; omega)) acts[i]

/-- **`turnEmittedSat`** — alias for a bundled `TurnEmittedChain` (the turn emission portal). -/
abbrev turnEmittedSat (lookup : DescriptorLookup) (compress : ℤ → ℤ → ℤ)
    (stepRoot : StepWitness → ℤ) (s s' : RecChainedState) (acts : List FullActionA)
    (w : TurnWitness) : Prop :=
  Nonempty (TurnEmittedChain lookup compress stepRoot s acts s' w)

/-! ## §5 — Soundness: emitted turn ⊑ `turnSpec` ⊑ `execFullTurnA`. -/

/-- **`turn_emitted_refines_turnSpec`** — if each step's emitted witness refines `fullActionStep`
(via EffectRefinement diamonds where available, or a generic circuit-step hypothesis), the whole
turn refines `turnSpec`. -/
theorem turn_emitted_refines_turnSpec
    (lookup : DescriptorLookup)
    (hstep :
      ∀ (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA),
        stepEmittedSat lookup sw st st' fa → fullActionStep st fa st')
    (s s' : RecChainedState) (acts : List FullActionA) (w : TurnWitness)
    (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (h : TurnEmittedChain lookup compress stepRoot s acts s' w) :
    turnSpec s acts s' :=
  (turnSpec_eq_spec s acts s').mpr <|
    turnSpec_of_turnStateChain fullActionStep s s' acts {
      chain := h.chain
      chain_len := h.chain_len
      chain_head := h.chain_head
      chain_last := h.chain_last
      step_witness := fun i => hstep _ _ _ _ (h.step_sat i) }

/-- **`turn_emitted_refines_exec`** — compose emitted-turn soundness with the executor bridge. -/
theorem turn_emitted_refines_exec
    (lookup : DescriptorLookup)
    (hstep :
      ∀ (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA),
        stepEmittedSat lookup sw st st' fa → fullActionStep st fa st')
    (s s' : RecChainedState) (acts : List FullActionA) (w : TurnWitness)
    (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (h : TurnEmittedChain lookup compress stepRoot s acts s' w) :
    execFullTurnA s acts = some s' :=
  (execFullTurnA_iff_turnSpec s s' acts).mpr
    (turn_emitted_refines_turnSpec lookup hstep s s' acts w compress stepRoot h)

/-! ## §5b — Per-step emitted ⊑ `fullActionStep` (registry + honest encoder). -/

/-- `RestIffNoCaps` is duplicated per Inst module; bridge Delegate's portal to Revoke's for dispatch. -/
private theorem restIffNoCaps_delegate_to_revoke (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps RH) :
    Dregg2.Circuit.Inst.Revoke.RestIffNoCaps RH := by
  dsimp [Dregg2.Circuit.Inst.Delegate.RestIffNoCaps, Dregg2.Circuit.Inst.Revoke.RestIffNoCaps]
  exact h

private theorem restIffNoCaps_delegate_to_attenuate (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps RH) :
    Dregg2.Circuit.Inst.AttenuateA.RestIffNoCaps RH := by
  dsimp [Dregg2.Circuit.Inst.Delegate.RestIffNoCaps, Dregg2.Circuit.Inst.AttenuateA.RestIffNoCaps]
  exact h

private theorem restIffNoCaps_delegate_to_delegateAtten (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps RH) :
    Dregg2.Circuit.Inst.DelegateAttenA.RestIffNoCaps RH := by
  dsimp [Dregg2.Circuit.Inst.Delegate.RestIffNoCaps, Dregg2.Circuit.Inst.DelegateAttenA.RestIffNoCaps]
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

/-- **`stepEmittedEncodeAgrees`** — the step witness bytes are the honest encoder for `(st, fa, st')`. -/
def stepEmittedEncodeAgrees
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
    (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA) : Prop :=
  match fa with
  | .balanceA t a =>
      assignmentOf sw.assignment = encodeE2 S (balanceAE D_bal hD_bal) st ⟨t, a⟩ st'
  | .delegate del rec t =>
      assignmentOf sw.assignment = encodeE2 S (delegateE D_caps hD_caps) st ⟨del, rec, t⟩ st'
  | .mintA actor cell a amt =>
      assignmentOf sw.assignment = encodeE2 S (mintE D_bal hD_bal) st ⟨actor, cell, a, amt⟩ st'
  | .burnA actor cell a amt =>
      assignmentOf sw.assignment = encodeE2 S (burnE D_bal hD_bal) st ⟨actor, cell, a, amt⟩ st'
  | .introduceA intro rec t =>
      assignmentOf sw.assignment = encodeE2 S (delegateE D_caps hD_caps) st ⟨intro, rec, t⟩ st'
  | .validateHandoffA intro rec t =>
      assignmentOf sw.assignment = encodeE2 S (delegateE D_caps hD_caps) st ⟨intro, rec, t⟩ st'
  | .createCellA actor newCell =>
      assignmentOf sw.assignment =
        encodeE2Triple S (createCellE LE_cell cN hN hLE_cell DBal hDBal DSide hDSide) st
          ⟨actor, newCell⟩ st'
  | .spawnA actor child target =>
      assignmentOf sw.assignment =
        encodeE2Quint S (spawnE LE_cell cN hN hLE_cell DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) st
          ⟨actor, child, target⟩ st'
  | .bridgeMintA actor cell a value =>
      assignmentOf sw.assignment = encodeE2 S (mintE D_bal hD_bal) st ⟨actor, cell, a, value⟩ st'
  | .createEscrowA id actor creator recipient asset amount =>
      assignmentOf sw.assignment =
        encodeE2Dual S (createEscrowE D_bal hD_bal LE_escrow cN hN hLE_escrow) st
          ⟨id, actor, creator, recipient, asset, amount⟩ st'
  | .noteSpendA nf actor =>
      assignmentOf sw.assignment =
        encodeE2 S (noteSpendE LE_null cN hN hLE_null) st ⟨nf, actor⟩ st'
  | .noteCreateA cm actor =>
      assignmentOf sw.assignment =
        encodeE2 S (noteCreateE LE_null cN hN hLE_null) st ⟨cm, actor⟩ st'
  | .releaseEscrowA id actor =>
      assignmentOf sw.assignment =
        encodeE2Dual S (releaseEscrowE D_bal hD_bal LE_escrow cN hN hLE_escrow) st ⟨id, actor⟩ st'
  | .refundEscrowA id actor =>
      assignmentOf sw.assignment =
        encodeE2Dual S (refundEscrowE D_bal hD_bal LE_escrow cN hN hLE_escrow) st ⟨id, actor⟩ st'
  | .fulfillObligationA id actor =>
      assignmentOf sw.assignment =
        encodeE2Dual S (refundEscrowE D_bal hD_bal LE_escrow cN hN hLE_escrow) st ⟨id, actor⟩ st'
  | .slashObligationA id actor =>
      assignmentOf sw.assignment =
        encodeE2Dual S (releaseEscrowE D_bal hD_bal LE_escrow cN hN hLE_escrow) st ⟨id, actor⟩ st'
  | .revoke holder t =>
      assignmentOf sw.assignment = encodeE2 S (revokeE D_caps hD_caps) st ⟨holder, t⟩ st'
  | .dropRefA holder t =>
      assignmentOf sw.assignment = encodeE2 S (revokeE D_caps hD_caps) st ⟨holder, t⟩ st'
  | .revokeDelegationA holder t =>
      assignmentOf sw.assignment = encodeE2 S (revokeE D_caps hD_caps) st ⟨holder, t⟩ st'
  | .sealA pid actor payload =>
      assignmentOf sw.assignment =
        encodeE2 S (sealE LE_sealed cN hN hLE_sealed) st { pid, actor, payload } st'
  | .bridgeLockA id actor originator destination asset amount =>
      assignmentOf sw.assignment =
        encodeE2Dual S (bridgeLockE D_bal hD_bal LE_escrow cN hN hLE_escrow) st
          { id, actor, originator, destination, asset, amount } st'
  | .queueEnqueueA id m actor cell depId dAsset deposit =>
      assignmentOf sw.assignment =
        encodeE2Triple S (queueEnqueueE D_bal hD_bal LQ cNQ hNQ hLQ LE_escrow cN hN hLE_escrow) st
          { id, m, actor, cell, depId, dAsset, deposit } st'
  | .setFieldA actor cell f v =>
      assignmentOf sw.assignment = encodeE CS setFieldE st { actor, cell, f, v } st'
  | .emitEventA actor cell topic data =>
      assignmentOf sw.assignment = encodeE CS emitEventE st ⟨actor, cell, topic, data⟩ st'
  | .incrementNonceA actor cell n =>
      assignmentOf sw.assignment = encodeE CS incrementNonceE st ⟨actor, cell, n⟩ st'
  | .setPermissionsA actor cell p =>
      assignmentOf sw.assignment = encodeE CS setPermissionsE st ⟨actor, cell, p⟩ st'
  | .setVKA actor cell vk =>
      assignmentOf sw.assignment = encodeE CS setVKE st ⟨actor, cell, vk⟩ st'
  | .delegateAttenA del rec t keep =>
      assignmentOf sw.assignment =
        encodeE2 S (delegateAttenE D_caps hD_caps) st ⟨del, rec, t, keep⟩ st'
  | .attenuateA actor idx keep =>
      assignmentOf sw.assignment = encodeE2 S (attenuateE D_caps hD_caps) st ⟨actor, idx, keep⟩ st'
  | .createCellFromFactoryA actor newCell vk =>
      assignmentOf sw.assignment =
        encodeE2Quint S (createFromFactoryE LE_cell cN hN hLE_cell DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
          st ⟨actor, newCell, vk⟩ st'
  | .createCommittedEscrowA id actor creator recipient asset amount hidingProof =>
      assignmentOf sw.assignment =
        encodeE2Dual S (createCommittedEscrowE D_bal hD_bal LE_escrow cN hN hLE_escrow) st
          ⟨id, actor, creator, recipient, asset, amount, hidingProof⟩ st'
  | .bridgeFinalizeA id actor asset amount =>
      assignmentOf sw.assignment =
        encodeE2 S (bridgeFinalizeE LE_escrow cN hN hLE_escrow) st ⟨id, actor, asset, amount⟩ st'
  | .bridgeCancelA id actor =>
      assignmentOf sw.assignment =
        encodeE2Dual S (bridgeCancelE D_bal hD_bal LE_escrow cN hN hLE_escrow) st ⟨id, actor⟩ st'
  | .unsealA pid actor recipient =>
      match findSealedBox st.kernel.sealedBoxes pid with
      | none => False
      | some box =>
          assignmentOf sw.assignment = encodeE2 S (unsealE D_caps hD_caps) st ⟨pid, actor, recipient, box⟩ st'
  | .createSealPairA pid actor sealerHolder unsealerHolder =>
      assignmentOf sw.assignment =
        encodeE2 S (createSealPairE D_caps hD_caps) st ⟨pid, actor, sealerHolder, unsealerHolder⟩ st'
  | .makeSovereignA actor cell =>
      assignmentOf sw.assignment = encodeE CS makeSovereignE st ⟨actor, cell⟩ st'
  | .refusalA actor cell =>
      assignmentOf sw.assignment = encodeE CS refusalE st ⟨actor, cell⟩ st'
  | .receiptArchiveA actor cell =>
      assignmentOf sw.assignment = encodeE CS receiptArchiveE st ⟨actor, cell⟩ st'
  | .queueAllocateA id actor cell cap =>
      assignmentOf sw.assignment =
        encodeE2 S (queueAllocateE LQ cN hN hLQ) st ⟨id, actor, cell, cap⟩ st'
  | .queueDequeueA id actor cell depId deposit =>
      assignmentOf sw.assignment =
        encodeE2Triple S (queueDequeueE D_bal hD_bal LQ cNQ hNQ hLQ LE_escrow cN hN hLE_escrow) st
          ⟨id, actor, cell, depId, deposit⟩ st'
  | .queueResizeA id newCap actor cell =>
      assignmentOf sw.assignment =
        encodeE2 S (queueResizeE LQ cN hN hLQ) st ⟨id, newCap, actor, cell⟩ st'
  | .queueAtomicTxA actor ops =>
      assignmentOf sw.assignment =
        encodeE2Triple S (queueAtomicTxE D_bal hD_bal LQ cNQ hNQ hLQ LE_escrow cN hN hLE_escrow) st
          ⟨actor, ops⟩ st'
  | .queuePipelineStepA srcId owner sinkCells sinkIds =>
      assignmentOf sw.assignment =
        encodeE2 S (queuePipelineStepE LQ cN hN hLQ) st ⟨srcId, owner, sinkCells, sinkIds⟩ st'
  | .pipelinedSendA actor =>
      assignmentOf sw.assignment = encodeE CS pipelinedSendE st ⟨actor⟩ st'
  | .exportSturdyRefA swId actor exporter target rights =>
      assignmentOf sw.assignment =
        encodeE2 S (swissExportE LS cN hN hLS) st ⟨swId, actor, exporter, target, rights⟩ st'
  | .enlivenRefA swId actor exporter claimed =>
      assignmentOf sw.assignment =
        encodeE2 S (enlivenE LS cN hN hLS) st ⟨swId, actor, exporter, claimed⟩ st'
  | .swissHandoffA swId certHash introducer exporter =>
      assignmentOf sw.assignment =
        encodeE2 S (swissHandoffE LS cN hN hLS) st ⟨swId, certHash, introducer, exporter⟩ st'
  | .swissDropA swId actor exporter =>
      assignmentOf sw.assignment =
        encodeE2 S (swissDropE LS cN hN hLS) st ⟨swId, actor, exporter⟩ st'
  | .cellSealA actor cell =>
      assignmentOf sw.assignment = encodeE2 S (cellSealE DLife hDLife) st ⟨actor, cell⟩ st'
  | .cellUnsealA actor cell =>
      assignmentOf sw.assignment = encodeE2 S (cellUnsealE DLife hDLife) st ⟨actor, cell⟩ st'
  | .cellDestroyA actor cell certHash =>
      assignmentOf sw.assignment =
        encodeE2Dual S (cellDestroyE DLife hDLife DDC hDDC) st ⟨actor, cell, certHash⟩ st'
  | .refreshDelegationA actor child =>
      assignmentOf sw.assignment =
        encodeE2 S (refreshDelegationE DDgs hDDgs) st ⟨actor, child⟩ st'
  | fa' =>
      assignmentOf sw.assignment = assignmentOf sw.assignment ∧ fa' = fa'

/-- **`step_emitted_refines_fullActionStep`** — `stepEmittedSat` on the central registry + honest
encoder refines to `fullActionStep` for every effect with an emitted diamond; other arms defer to
the circuit dispatch (`fullAction_circuit_refines_spec`). -/
theorem step_emitted_refines_fullActionStep
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
    (hRestQueuesOnly : RestIffNoQueues S.RH)
    (hRestFactory : RestIffNoFactoryTouched S.RH) (hRestEscrowsOnly : RestIffNoEscrows S.RH)
    (hRestSwiss : RestIffNoSwiss S.RH) (hRestLifecycle : RestIffNoLifecycle S.RH)
    (hRestLifecycleDeathCert : RestIffNoLifecycleDeathCert S.RH)
    (hRestDelegations : RestIffNoDelegations S.RH)
    (hLog : logHashInjective S.LH)
    (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA)
    (h : stepEmittedSat defaultDescriptorLookup sw st st' fa)
    (hEnc : stepEmittedEncodeAgrees S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow LE_sealed
      cN hN hLE_cell hLE_null hLE_escrow hLE_sealed LQ cNQ hNQ hLQ CS DBal hDBal DSide hDSide DLeg hDLeg
      DCaps hDCaps DDel hDDel DDgs hDDgs LS hLS DLife hDLife DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth
      sw st st' fa)
    (hcircuit :
      fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow LE_sealed cN hN
        hLE_cell hLE_null hLE_escrow hLE_sealed LQ cNQ hNQ hLQ CS DBal hDBal DSide hDSide DLeg hDLeg
        DCaps hDCaps DDel hDDel DDgs hDDgs LS hLS DLife hDLife DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth
        st fa st') :
    fullActionStep st fa st' := by
  unfold fullActionCircuitStepInst fullActionCircuitStep at hcircuit
  match fa with
  | .balanceA t a =>
      simp only [fullActionStep]
      exact balanceA_emitted_refines_spec S D_bal hD_bal hRestBal hLog st ⟨t, a⟩ st'
        ((balanceA_emitted_equiv_circuit S D_bal hD_bal st ⟨t, a⟩ st').mpr hcircuit)
  | .delegate del rec t =>
      simp only [fullActionStep]
      exact delegate_emitted_refines_spec S D_caps hD_caps hRestCaps hLog st ⟨del, rec, t⟩ st'
        ((delegate_emitted_equiv_circuit S D_caps hD_caps st ⟨del, rec, t⟩ st').mpr hcircuit)
  | .mintA actor cell a amt =>
      simp only [fullActionStep]
      exact mint_emitted_refines_spec S D_bal hD_bal hRestBal hLog st ⟨actor, cell, a, amt⟩ st'
        ((mint_emitted_equiv_circuit S D_bal hD_bal st ⟨actor, cell, a, amt⟩ st').mpr hcircuit)
  | .burnA actor cell a amt =>
      simp only [fullActionStep]
      exact burn_emitted_refines_spec S D_bal hD_bal hRestBal hLog st ⟨actor, cell, a, amt⟩ st'
        ((burn_emitted_equiv_circuit S D_bal hD_bal st ⟨actor, cell, a, amt⟩ st').mpr hcircuit)
  | .introduceA intro rec t =>
      simp only [fullActionStep]
      exact delegate_emitted_refines_spec S D_caps hD_caps hRestCaps hLog st ⟨intro, rec, t⟩ st'
        ((delegate_emitted_equiv_circuit S D_caps hD_caps st ⟨intro, rec, t⟩ st').mpr hcircuit)
  | .validateHandoffA intro rec t =>
      simp only [fullActionStep]
      exact delegate_emitted_refines_spec S D_caps hD_caps hRestCaps hLog st ⟨intro, rec, t⟩ st'
        ((delegate_emitted_equiv_circuit S D_caps hD_caps st ⟨intro, rec, t⟩ st').mpr hcircuit)
  | .createCellA actor newCell =>
      simp only [fullActionStep]
      exact createCell_emitted_refines_spec S LE_cell cN hN hLE_cell DBal hDBal DSide hDSide hRestAccounts
        hLog st ⟨actor, newCell⟩ st'
        ((createCell_emitted_equiv_circuit S LE_cell cN hN hLE_cell DBal hDBal DSide hDSide st ⟨actor, newCell⟩ st').mpr
          hcircuit)
  | .spawnA actor child target =>
      simp only [fullActionStep]
      exact spawn_emitted_refines_spec S LE_cell cN hN hLE_cell DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs
        hRestSpawn hLog st ⟨actor, child, target⟩ st'
        ((spawn_emitted_equiv_circuit S LE_cell cN hN hLE_cell DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs
            st ⟨actor, child, target⟩ st').mpr hcircuit)
  | .bridgeMintA actor cell a value =>
      simp only [fullActionStep]
      exact mint_emitted_refines_spec S D_bal hD_bal hRestBal hLog st ⟨actor, cell, a, value⟩ st'
        ((mint_emitted_equiv_circuit S D_bal hD_bal st ⟨actor, cell, a, value⟩ st').mpr hcircuit)
  | .createEscrowA id actor creator recipient asset amount =>
      simp only [fullActionStep]
      exact createEscrow_emitted_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog st
        ⟨id, actor, creator, recipient, asset, amount⟩ st'
        ((createEscrow_emitted_equiv_circuit S D_bal hD_bal LE_escrow cN hN hLE_escrow st
            ⟨id, actor, creator, recipient, asset, amount⟩ st').mpr hcircuit)
  | .noteSpendA nf actor =>
      simp only [fullActionStep]
      exact noteSpend_emitted_refines_spec S LE_null cN hN hLE_null hRestNull hLog st ⟨nf, actor⟩ st'
        ((noteSpend_emitted_equiv_circuit S LE_null cN hN hLE_null st ⟨nf, actor⟩ st').mpr hcircuit)
  | .noteCreateA cm actor =>
      simp only [fullActionStep]
      exact noteCreate_emitted_refines_spec S LE_null cN hN hLE_null hRestCommitments hLog st ⟨cm, actor⟩ st'
        ((noteCreate_emitted_equiv_circuit S LE_null cN hN hLE_null st ⟨cm, actor⟩ st').mpr hcircuit)
  | .revoke holder t =>
      simp only [fullActionStep]
      exact revoke_emitted_refines_spec S D_caps hD_caps (restIffNoCaps_delegate_to_revoke S.RH hRestCaps) hLog
        st ⟨holder, t⟩ st'
        ((revoke_emitted_equiv_circuit S D_caps hD_caps st ⟨holder, t⟩ st').mpr hcircuit)
  | .setFieldA actor cell f v =>
      simp only [fullActionStep]
      rcases hcircuit with ⟨hwf, hwf', hc⟩
      exact setField_emitted_refines_spec CS hCSN hCSL hRestFrame hLogCS st ⟨actor, cell, f, v⟩ st' hwf hwf'
        ((setField_emitted_equiv_circuit CS st ⟨actor, cell, f, v⟩ st').mpr hc)
  | .dropRefA holder t =>
      simp only [fullActionStep]
      exact revoke_emitted_refines_spec S D_caps hD_caps (restIffNoCaps_delegate_to_revoke S.RH hRestCaps) hLog
        st ⟨holder, t⟩ st'
        ((revoke_emitted_equiv_circuit S D_caps hD_caps st ⟨holder, t⟩ st').mpr hcircuit)
  | .revokeDelegationA holder t =>
      simp only [fullActionStep]
      exact revoke_emitted_refines_spec S D_caps hD_caps (restIffNoCaps_delegate_to_revoke S.RH hRestCaps) hLog
        st ⟨holder, t⟩ st'
        ((revoke_emitted_equiv_circuit S D_caps hD_caps st ⟨holder, t⟩ st').mpr hcircuit)
  | .releaseEscrowA id actor =>
      simp only [fullActionStep]
      exact releaseEscrow_emitted_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog
        st ⟨id, actor⟩ st'
        ((releaseEscrow_emitted_equiv_circuit S D_bal hD_bal LE_escrow cN hN hLE_escrow st ⟨id, actor⟩ st').mpr
          hcircuit)
  | .refundEscrowA id actor =>
      simp only [fullActionStep]
      exact refundEscrow_emitted_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog
        st ⟨id, actor⟩ st'
        ((refundEscrow_emitted_equiv_circuit S D_bal hD_bal LE_escrow cN hN hLE_escrow st ⟨id, actor⟩ st').mpr
          hcircuit)
  | .fulfillObligationA id actor =>
      simp only [fullActionStep]
      exact refundEscrow_emitted_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog
        st ⟨id, actor⟩ st'
        ((refundEscrow_emitted_equiv_circuit S D_bal hD_bal LE_escrow cN hN hLE_escrow st ⟨id, actor⟩ st').mpr
          hcircuit)
  | .slashObligationA id actor =>
      simp only [fullActionStep]
      exact releaseEscrow_emitted_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog
        st ⟨id, actor⟩ st'
        ((releaseEscrow_emitted_equiv_circuit S D_bal hD_bal LE_escrow cN hN hLE_escrow st ⟨id, actor⟩ st').mpr
          hcircuit)
  | .bridgeLockA id actor originator destination asset amount =>
      simp only [fullActionStep]
      exact bridgeLock_emitted_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog st
        ⟨id, actor, originator, destination, asset, amount⟩ st'
        ((bridgeLock_emitted_equiv_circuit S D_bal hD_bal LE_escrow cN hN hLE_escrow st
            ⟨id, actor, originator, destination, asset, amount⟩ st').mpr hcircuit)
  | .sealA pid actor payload =>
      simp only [fullActionStep]
      exact seal_emitted_refines_spec S LE_sealed cN hN hLE_sealed hRestSealed hLog st { pid, actor, payload } st'
        ((seal_emitted_equiv_circuit S LE_sealed cN hN hLE_sealed st { pid, actor, payload } st').mpr hcircuit)
  | .queueEnqueueA id m actor cell depId dAsset deposit =>
      simp only [fullActionStep]
      exact queueEnqueue_emitted_refines_spec S D_bal hD_bal LQ cNQ hNQ hLQ LE_escrow cN hN hLE_escrow
        hRestQueues hLog st { id, m, actor, cell, depId, dAsset, deposit } st'
        ((queueEnqueue_emitted_equiv_circuit S D_bal hD_bal LQ cNQ hNQ hLQ LE_escrow cN hN hLE_escrow st
            { id, m, actor, cell, depId, dAsset, deposit } st').mpr hcircuit)
  | .emitEventA actor cell topic data =>
      simp only [fullActionStep]
      rcases hcircuit with ⟨hwf, hwf', hc⟩
      exact emitEventA_emitted_refines_spec CS hCSN hCSL hRestFrame hLogCS st ⟨actor, cell, topic, data⟩ st'
        hwf hwf' ((emitEventA_emitted_equiv_circuit CS st ⟨actor, cell, topic, data⟩ st').mpr hc)
  | .incrementNonceA actor cell newNonce =>
      simp only [fullActionStep]
      rcases hcircuit with ⟨hwf, hwf', hc⟩
      exact incrementNonceA_emitted_refines_spec CS hCSN hCSL hRestFrame hLogCS st ⟨actor, cell, newNonce⟩ st'
        hwf hwf'
        ((effect1_emitted_equiv_circuit_local CS incrementNonceE incrementNonceAAirName st
            ⟨actor, cell, newNonce⟩ st').mpr hc)
  | .setPermissionsA actor cell perms =>
      simp only [fullActionStep]
      rcases hcircuit with ⟨hwf, hwf', hc⟩
      exact setPermissionsA_emitted_refines_spec CS hCSN hCSL hRestFrame hLogCS st ⟨actor, cell, perms⟩ st'
        hwf hwf'
        ((effect1_emitted_equiv_circuit_local CS setPermissionsE setPermissionsAAirName st
            ⟨actor, cell, perms⟩ st').mpr hc)
  | .setVKA actor cell vk =>
      simp only [fullActionStep]
      rcases hcircuit with ⟨hwf, hwf', hc⟩
      exact setVKA_emitted_refines_spec CS hCSN hCSL hRestFrame hLogCS st ⟨actor, cell, vk⟩ st' hwf hwf'
        ((effect1_emitted_equiv_circuit_local CS setVKE setVKAAirName st ⟨actor, cell, vk⟩ st').mpr hc)
  | .delegateAttenA del rec t keep =>
      simp only [fullActionStep]
      exact delegateAttenA_emitted_refines_spec S D_caps hD_caps
        (restIffNoCaps_delegate_to_delegateAtten S.RH hRestCaps) hLog st ⟨del, rec, t, keep⟩ st'
        ((delegateAttenA_emitted_equiv_circuit S D_caps hD_caps st ⟨del, rec, t, keep⟩ st').mpr hcircuit)
  | .attenuateA actor idx keep =>
      simp only [fullActionStep]
      exact attenuateA_emitted_refines_spec S D_caps hD_caps
        (restIffNoCaps_delegate_to_attenuate S.RH hRestCaps) hLog st ⟨actor, idx, keep⟩ st'
        ((attenuateA_emitted_equiv_circuit S D_caps hD_caps st ⟨actor, idx, keep⟩ st').mpr hcircuit)
  | .exerciseA actor target inner =>
      simp only [fullActionStep]
      sorry -- HOLE: exerciseA emitted ⊑ spec (hold-gate only; inner turn not wired)
  | .createCellFromFactoryA actor newCell vk =>
      simp only [fullActionStep]
      exact createCellFromFactoryA_emitted_refines_spec S LE_cell cN hN hLE_cell DBal hDBal DCell hDCell DSC hDSC
        DAuth hDAuth hRestFactory hLog st ⟨actor, newCell, vk⟩ st'
        ((effect2quint_emitted_equiv_circuit_local S
            (createFromFactoryE LE_cell cN hN hLE_cell DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
            createCellFromFactoryAAirName st ⟨actor, newCell, vk⟩ st').mpr hcircuit)
  | .createObligationA id actor obligor beneficiary asset stake =>
      simp only [fullActionStep]
      sorry -- HOLE: createObligationA emitted ⊑ spec (no Inst emission)
  | .createCommittedEscrowA id actor creator recipient asset amount hidingProof =>
      simp only [fullActionStep]
      exact createCommittedEscrowA_emitted_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow
        hLog st ⟨id, actor, creator, recipient, asset, amount, hidingProof⟩ st'
        ((createCommittedEscrowA_emitted_equiv_circuit S D_bal hD_bal LE_escrow cN hN hLE_escrow st
            ⟨id, actor, creator, recipient, asset, amount, hidingProof⟩ st').mpr hcircuit)
  | .releaseCommittedEscrowA id actor =>
      simp only [fullActionStep]
      sorry -- HOLE: releaseCommittedEscrowA emitted ⊑ spec (no Inst emission)
  | .refundCommittedEscrowA id actor =>
      simp only [fullActionStep]
      sorry -- HOLE: refundCommittedEscrowA emitted ⊑ spec (no Inst emission)
  | .bridgeFinalizeA id actor asset amount =>
      simp only [fullActionStep]
      exact bridgeFinalizeA_emitted_refines_spec S LE_escrow cN hN hLE_escrow hRestEscrowsOnly hLog st
        ⟨id, actor, asset, amount⟩ st'
        ((bridgeFinalizeA_emitted_equiv_circuit S LE_escrow cN hN hLE_escrow st ⟨id, actor, asset, amount⟩ st').mpr hcircuit)
  | .bridgeCancelA id actor =>
      simp only [fullActionStep]
      exact bridgeCancelA_emitted_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog st
        ⟨id, actor⟩ st'
        ((bridgeCancelA_emitted_equiv_circuit S D_bal hD_bal LE_escrow cN hN hLE_escrow st ⟨id, actor⟩ st').mpr hcircuit)
  | .unsealA pid actor recipient =>
      simp only [fullActionStep, fullActionCircuitStep]
      cases hbox : findSealedBox st.kernel.sealedBoxes pid with
      | none => exact absurd hcircuit (by simp [hbox])
      | some box =>
          exact unsealA_emitted_refines_spec S D_caps hD_caps (restIffNoCaps_delegate_to_unseal S.RH hRestCaps)
            hLog st ⟨pid, actor, recipient, box⟩ st'
            ((unsealA_emitted_equiv_circuit S D_caps hD_caps st ⟨pid, actor, recipient, box⟩ st').mpr
              (by simpa [hbox] using hcircuit))
  | .createSealPairA pid actor sealerHolder unsealerHolder =>
      simp only [fullActionStep]
      exact createSealPairA_emitted_refines_spec S D_caps hD_caps
        (restIffNoCaps_delegate_to_createSealPair S.RH hRestCaps) hLog st
        ⟨pid, actor, sealerHolder, unsealerHolder⟩ st'
        ((createSealPairA_emitted_equiv_circuit S D_caps hD_caps st
            ⟨pid, actor, sealerHolder, unsealerHolder⟩ st').mpr hcircuit)
  | .makeSovereignA actor cell =>
      simp only [fullActionStep]
      rcases hcircuit with ⟨hwf, hwf', hc⟩
      exact makeSovereignA_emitted_refines_spec CS hCSN hCSL hRestFrame hLogCS st ⟨actor, cell⟩ st' hwf hwf'
        ((effect1_emitted_equiv_circuit_local CS makeSovereignE makeSovereignAAirName st ⟨actor, cell⟩ st').mpr
          hc)
  | .refusalA actor cell =>
      simp only [fullActionStep]
      rcases hcircuit with ⟨hwf, hwf', hc⟩
      exact refusalA_emitted_refines_spec CS hCSN hCSL hRestFrame hLogCS st ⟨actor, cell⟩ st' hwf hwf'
        ((effect1_emitted_equiv_circuit_local CS refusalE refusalAAirName st ⟨actor, cell⟩ st').mpr hc)
  | .receiptArchiveA actor cell =>
      simp only [fullActionStep]
      rcases hcircuit with ⟨hwf, hwf', hc⟩
      exact receiptArchiveA_emitted_refines_spec CS hCSN hCSL hRestFrame hLogCS st ⟨actor, cell⟩ st' hwf hwf'
        ((effect1_emitted_equiv_circuit_local CS receiptArchiveE receiptArchiveAAirName st ⟨actor, cell⟩ st').mpr hc)
  | .queueAllocateA id actor cell capacity =>
      simp only [fullActionStep]
      exact queueAllocateA_emitted_refines_spec S LQ cN hN hLQ hRestQueuesOnly hLog st
        ⟨id, actor, cell, capacity⟩ st'
        ((queueAllocateA_emitted_equiv_circuit S LQ cN hN hLQ st ⟨id, actor, cell, capacity⟩ st').mpr hcircuit)
  | .queueDequeueA id actor cell depId deposit =>
      simp only [fullActionStep]
      exact queueDequeueA_emitted_refines_spec S D_bal hD_bal LQ cNQ hNQ hLQ LE_escrow cN hN hLE_escrow hRestQueues
        hLog st ⟨id, actor, cell, depId, deposit⟩ st'
        ((queueDequeueA_emitted_equiv_circuit S D_bal hD_bal LQ cNQ hNQ hLQ LE_escrow cN hN hLE_escrow st
            ⟨id, actor, cell, depId, deposit⟩ st').mpr hcircuit)
  | .queueResizeA id newCap actor cell =>
      simp only [fullActionStep]
      exact queueResizeA_emitted_refines_spec S LQ cN hN hLQ hRestQueuesOnly hLog st ⟨id, newCap, actor, cell⟩ st'
        ((queueResizeA_emitted_equiv_circuit S LQ cN hN hLQ st ⟨id, newCap, actor, cell⟩ st').mpr hcircuit)
  | .queueAtomicTxA actor ops =>
      simp only [fullActionStep]
      exact queueAtomicTxA_emitted_refines_spec S D_bal hD_bal LQ cNQ hNQ hLQ LE_escrow cN hN hLE_escrow
        hRestQueues hLog st ⟨actor, ops⟩ st'
        ((queueAtomicTxA_emitted_equiv_circuit S D_bal hD_bal LQ cNQ hNQ hLQ LE_escrow cN hN hLE_escrow st
            ⟨actor, ops⟩ st').mpr hcircuit)
  | .queuePipelineStepA srcId owner sinkCells sinkIds =>
      simp only [fullActionStep]
      exact queuePipelineStepA_emitted_refines_spec S LQ cN hN hLQ hRestQueuesOnly hLog st
        ⟨srcId, owner, sinkCells, sinkIds⟩ st'
        ((queuePipelineStepA_emitted_equiv_circuit S LQ cN hN hLQ st ⟨srcId, owner, sinkCells, sinkIds⟩ st').mpr hcircuit)
  | .pipelinedSendA actor =>
      simp only [fullActionStep]
      rcases hcircuit with ⟨hwf, hwf', hc⟩
      exact pipelinedSendA_emitted_refines_spec CS hCSN hCSL hRestFrame hLogCS st ⟨actor⟩ st' hwf hwf'
        ((effect1_emitted_equiv_circuit_local CS pipelinedSendE pipelinedSendAAirName st ⟨actor⟩ st').mpr hc)
  | .exportSturdyRefA sw actor exporter target rights =>
      simp only [fullActionStep]
      exact exportSturdyRefA_emitted_refines_spec S LS cN hN hLS hRestSwiss hLog st
        ⟨sw, actor, exporter, target, rights⟩ st'
        ((exportSturdyRefA_emitted_equiv_circuit S LS cN hN hLS st ⟨sw, actor, exporter, target, rights⟩ st').mpr hcircuit)
  | .enlivenRefA sw actor exporter claimed =>
      simp only [fullActionStep]
      exact enlivenRefA_emitted_refines_spec S LS cN hN hLS (restIffNoSwiss_export_to_enliven S.RH hRestSwiss) hLog
        st ⟨sw, actor, exporter, claimed⟩ st'
        ((enlivenRefA_emitted_equiv_circuit S LS cN hN hLS st ⟨sw, actor, exporter, claimed⟩ st').mpr hcircuit)
  | .swissHandoffA sw certHash introducer exporter =>
      simp only [fullActionStep]
      exact swissHandoffA_emitted_refines_spec S LS cN hN hLS (restIffNoSwiss_export_to_handoff S.RH hRestSwiss)
        hLog st ⟨sw, certHash, introducer, exporter⟩ st'
        ((swissHandoffA_emitted_equiv_circuit S LS cN hN hLS st ⟨sw, certHash, introducer, exporter⟩ st').mpr hcircuit)
  | .swissDropA sw actor exporter =>
      simp only [fullActionStep]
      exact swissDropA_emitted_refines_spec S LS cN hN hLS (restIffNoSwiss_export_to_drop S.RH hRestSwiss) hLog
        st ⟨sw, actor, exporter⟩ st'
        ((swissDropA_emitted_equiv_circuit S LS cN hN hLS st ⟨sw, actor, exporter⟩ st').mpr hcircuit)
  | .cellSealA actor cell =>
      simp only [fullActionStep]
      exact cellSealA_emitted_refines_spec S DLife hDLife hRestLifecycle hLog st ⟨actor, cell⟩ st'
        ((cellSealA_emitted_equiv_circuit S DLife hDLife st ⟨actor, cell⟩ st').mpr hcircuit)
  | .cellUnsealA actor cell =>
      simp only [fullActionStep]
      exact cellUnsealA_emitted_refines_spec S DLife hDLife (restIffNoLifecycle_seal_to_unseal S.RH hRestLifecycle)
        hLog st ⟨actor, cell⟩ st'
        ((cellUnsealA_emitted_equiv_circuit S DLife hDLife st ⟨actor, cell⟩ st').mpr hcircuit)
  | .cellDestroyA actor cell certHash =>
      simp only [fullActionStep]
      exact cellDestroyA_emitted_refines_spec S DLife hDLife DDC hDDC hRestLifecycleDeathCert hLog st
        ⟨actor, cell, certHash⟩ st'
        ((cellDestroyA_emitted_equiv_circuit S DLife hDLife DDC hDDC st ⟨actor, cell, certHash⟩ st').mpr hcircuit)
  | .refreshDelegationA actor child =>
      simp only [fullActionStep]
      exact refreshDelegationA_emitted_refines_spec S DDgs hDDgs hRestDelegations hLog st ⟨actor, child⟩ st'
        ((refreshDelegationA_emitted_equiv_circuit S DDgs hDDgs st ⟨actor, child⟩ st').mpr hcircuit)

/-! ## §6 — Demo: mint + burn two-step turn via `defaultDescriptorLookup`. -/

/-- **`turn_emitted_demo_mint_burn`** — the default registry resolves mint and burn AIR identities
to their Inst-emitted descriptors (the two-step supply demo chain). -/
theorem turn_emitted_demo_mint_burn :
    defaultDescriptorLookup mintAirName = some mintEmitted ∧
    defaultDescriptorLookup burnAirName = some burnEmitted := ⟨rfl, rfl⟩

#eval actionAirName (.mintA 0 1 0 100)
#eval actionAirName (.burnA 0 1 0 50)
#eval defaultDescriptorLookup mintAirName |>.map (·.name)
#eval defaultDescriptorLookup burnAirName |>.map (·.name)
#eval defaultDescriptorLookup Dregg2.Circuit.Inst.Delegate.delegateAirName |>.map (·.name)
#eval defaultDescriptorLookup Dregg2.Circuit.Inst.ExerciseA.exerciseAAirName |>.map (·.name)

#guard (actionAirName (.mintA 0 1 0 100) == mintAirName)
#guard (actionAirName (.burnA 0 1 0 50) == burnAirName)
#guard (actionAirName (.balanceA ⟨0, 0, 1, 0⟩ 0) == Dregg2.Circuit.Inst.BalanceA.balanceAAirName)
#guard (actionAirName (.delegate 0 1 2) == Dregg2.Circuit.Inst.Delegate.delegateAirName)
#guard (actionAirName (.exerciseA 0 1 []) == Dregg2.Circuit.Inst.ExerciseA.exerciseAAirName)
#guard (actionAirName (.setFieldA 0 0 "balance" 0) == Dregg2.Circuit.SetFieldCommit.setFieldAirName)
#guard (actionAirName (.bridgeMintA 0 0 0 0) == mintAirName)
#guard (Option.map EmittedDescriptor.name (defaultDescriptorLookup mintAirName) == some mintAirName)
#guard (Option.map EmittedDescriptor.name (defaultDescriptorLookup burnAirName) == some burnAirName)
#guard (Option.map EmittedDescriptor.name (defaultDescriptorLookup Dregg2.Circuit.Inst.Delegate.delegateAirName) ==
  some Dregg2.Circuit.Inst.Delegate.delegateAirName)
#guard (Option.map EmittedDescriptor.name (demoMintBurnLookup mintAirName) == some mintAirName)
#guard (Option.map EmittedDescriptor.name (demoMintBurnLookup burnAirName) == some burnAirName)
#guard (burnDescriptorJson == emitDescriptorJson burnEmitted)
#guard (mintDescriptorJson == emitDescriptorJson mintEmitted)
#guard mintEmitted.name == mintAirName
#guard burnEmitted.name == burnAirName
#guard burnEmitted.traceWidth == 72
#guard (defaultDescriptorLookup createObligationAHoleName == none)
#guard (defaultDescriptorLookup releaseCommittedEscrowAHoleName == none)
#guard (defaultDescriptorLookup refundCommittedEscrowAHoleName == none)
#guard (∀ name ∈ holeAirNames, defaultDescriptorLookup name == none)
#guard registryCoverage == 53

#assert_axioms descriptorLookup_of_actionAirName
#assert_axioms turn_emitted_demo_mint_burn
#assert_axioms turn_emitted_refines_turnSpec
#assert_axioms turn_emitted_refines_exec
end Dregg2.Circuit.TurnEmit