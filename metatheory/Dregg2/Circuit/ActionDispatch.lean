/-
# Dregg2.Circuit.ActionDispatch — the `FullActionA` apex dispatcher (Wave 1).

`fullActionStep` case-splits every `FullActionA` constructor to the existing per-family apex specs
(the 31 leaf `Circuit/Spec/*` modules). `fullActionStep_exec_iff` proves each arm ⟺ its
`execFullA_*_iff_spec` keystone — the spine `TurnWitness` and `Spec.exercise` build on.

## Executor shape (`TurnExecutorFull.lean:3665`)

    execFullA s (.exerciseA actor t inner) =
      match exerciseStepA s actor t with
      | some s' => execInnerA s' inner
      | none    => none

`exerciseStepA` (`:1602`) gates on `(s.kernel.caps actor).any (fun cap => confersEdgeTo target cap)`
and prepends `authReceipt actor` while leaving `kernel` UNCHANGED (exercising reads, never edits,
the c-list).

## Spec shape (executor-aligned Wave 1)

  * `exerciseGuard` — the hold-gate ONLY (no R4 facet-mask at this layer).
  * `fullActionStep` — dispatches each `FullActionA` constructor to the existing per-family apex
    specs (the 31 leaf modules' `*Spec` predicates).
  * `turnSpec` — declarative left-to-right fold: `∃ st₁, fullActionStep st a st₁ ∧ turnSpec st₁ rest st'`.
  * `ExerciseSpec` — `exerciseGuard` + `turnSpec (exerciseHoldState st actor) inner st'`.

## DEFER (documented, NOT in this module)

**R4 facet-mask** (`allowed_effects`): dregg1's `apply_exercise_via_capability` checks each inner
effect's facet against the held cap's mask (`Handlers/Exercise.lean`). The live `execFullA`/
`execInnerA` executor does NOT enforce R4 — only the hold-gate + inner fold. The handler algebra
(`exerciseH` / `exerciseAdmitB`) carries R4 at `Exec/Handlers/Exercise.lean`. Wave 1 matches the
executor; R4 is a later strengthening layer.

## What is proved

  * `fullActionStep_iff_execFullA` — each arm ⟺ its existing `execFullA_*_iff_spec` (or named twin).
  * `execInnerA_iff_turnSpec` / `execFullTurnA_iff_turnSpec` — inner fold ⟺ declarative `turnSpec`.
  * `execInnerA_eq_execFullTurnA` — the mutual/recursive twins coincide.
  * `execFullA_exerciseA_iff_spec` — exercise ⟺ `ExerciseSpec`.
  * `turnSpec_ledger_per_asset` / `exerciseSpec_ledger_per_asset` — conservation corollaries via
    `execInnerA_ledger_per_asset`.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.Spec.accountgrowth
import Dregg2.Circuit.Spec.authorityattenuation
import Dregg2.Circuit.Spec.authorityrevocation
import Dregg2.Circuit.Spec.authorityunattenuated
import Dregg2.Circuit.Spec.balancemovement
import Dregg2.Circuit.Spec.bridgeinboundmint
import Dregg2.Circuit.Spec.bridgeoutboundcancel
import Dregg2.Circuit.Spec.bridgeoutboundfinalize
import Dregg2.Circuit.Spec.bridgeoutboundlock
import Dregg2.Circuit.Spec.celllifecycle
import Dregg2.Circuit.Spec.cellstateaudit
import Dregg2.Circuit.Spec.cellstatefield
import Dregg2.Circuit.Spec.cellstatelog
import Dregg2.Circuit.Spec.cellstatemonotone
import Dregg2.Circuit.Spec.cellstatepermissions
import Dregg2.Circuit.Spec.cellstatevk
import Dregg2.Circuit.Spec.escrowcommitted
import Dregg2.Circuit.Spec.escrowholdingcreate
import Dregg2.Circuit.Spec.escrowholdingrefund
import Dregg2.Circuit.Spec.escrowholdingrelease
import Dregg2.Circuit.Spec.factorycreation
import Dregg2.Circuit.Spec.notecommitment
import Dregg2.Circuit.Spec.notenullifier
import Dregg2.Circuit.Spec.queueatomictx
import Dregg2.Circuit.Spec.queuefifocore
import Dregg2.Circuit.Spec.queuepipelinefanout
import Dregg2.Circuit.Spec.queuepipelinedsend
import Dregg2.Circuit.Spec.refreshdelegation
import Dregg2.Circuit.Spec.sealboxoperations
import Dregg2.Circuit.Spec.sealpaircreation
import Dregg2.Circuit.Spec.sovereigncommitment
import Dregg2.Circuit.Spec.supplycreation
import Dregg2.Circuit.Spec.supplydestruction
import Dregg2.Circuit.Spec.swissdrop
import Dregg2.Circuit.Spec.swissexport
import Dregg2.Circuit.Spec.swissenliven
import Dregg2.Circuit.Spec.swisshandoff
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.ActionDispatch

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Spec.BalanceMovement
open Dregg2.Circuit.Spec.SupplyCreation
open Dregg2.Circuit.Spec.SupplyDestruction
open Dregg2.Circuit.Spec.CellStateField
open Dregg2.Circuit.Spec.CellStateLog
open Dregg2.Circuit.Spec.CellStateMonotone
open Dregg2.Circuit.Spec.CellStatePermissions
open Dregg2.Circuit.Spec.CellStateVK
open Dregg2.Circuit.Spec.AuthorityUnattenuated
open Dregg2.Circuit.Spec.AuthorityAttenuation
open Dregg2.Circuit.Spec.AuthorityRevocation
open Dregg2.Circuit.Spec.AccountGrowth
open Dregg2.Circuit.Spec.FactoryCreation
open Dregg2.Circuit.Spec.NoteCommitment
open Dregg2.Circuit.Spec.NoteNullifier
open Dregg2.Circuit.Spec.EscrowHoldingCreate
open Dregg2.Circuit.Spec.EscrowHoldingRelease
open Dregg2.Circuit.Spec.EscrowHoldingRefund
open Dregg2.Circuit.Spec.EscrowCommitted
open Dregg2.Circuit.Spec.BridgeInboundMint
open Dregg2.Circuit.Spec.BridgeOutboundLock
open Dregg2.Circuit.Spec.BridgeOutboundFinalize
open Dregg2.Circuit.Spec.BridgeOutboundCancel
open Dregg2.Circuit.Spec.SealBoxOperations
open Dregg2.Circuit.Spec.SealPairCreation
open Dregg2.Circuit.Spec.SovereignCommitment
open Dregg2.Circuit.Spec.CellStateAudit
open Dregg2.Circuit.Spec.QueueFifoCore
open Dregg2.Circuit.Spec.QueueAtomicTx
open Dregg2.Circuit.Spec.QueuePipelineFanout
open Dregg2.Circuit.Spec.QueuePipelinedSend
open Dregg2.Circuit.Spec.SwissExport
open Dregg2.Circuit.Spec.SwissEnliven
open Dregg2.Circuit.Spec.SwissHandoff
open Dregg2.Circuit.Spec.SwissDrop
open Dregg2.Circuit.Spec.CellLifecycle
open Dregg2.Circuit.Spec.RefreshDelegation

/-! ## §1 — action tags (wire metadata for turn witnesses). -/

/-- **`actionTag`** — stable constructor index for `StepWitness.tag` (56/56 `FullActionA` arms). -/
def actionTag : FullActionA → Nat
  | .balanceA _ _ => 0
  | .delegate _ _ _ => 1
  | .revoke _ _ => 2
  | .mintA _ _ _ _ => 3
  | .burnA _ _ _ _ => 4
  | .setFieldA _ _ _ _ => 5
  | .emitEventA _ _ _ _ => 6
  | .incrementNonceA _ _ _ => 7
  | .setPermissionsA _ _ _ => 8
  | .setVKA _ _ _ => 9
  | .introduceA _ _ _ => 10
  | .delegateAttenA _ _ _ _ => 11
  | .attenuateA _ _ _ => 12
  | .dropRefA _ _ => 13
  | .revokeDelegationA _ _ => 14
  | .validateHandoffA _ _ _ => 15
  | .exerciseA _ _ _ => 16
  | .createCellA _ _ => 17
  | .createCellFromFactoryA _ _ _ => 18
  | .spawnA _ _ _ => 19
  | .bridgeMintA _ _ _ _ => 20
  | .createEscrowA _ _ _ _ _ _ => 21
  | .releaseEscrowA _ _ => 22
  | .refundEscrowA _ _ => 23
  | .createObligationA _ _ _ _ _ _ => 24
  | .fulfillObligationA _ _ => 25
  | .slashObligationA _ _ => 26
  | .noteSpendA _ _ => 27
  | .noteCreateA _ _ => 28
  | .createCommittedEscrowA _ _ _ _ _ _ _ => 29
  | .releaseCommittedEscrowA _ _ => 30
  | .refundCommittedEscrowA _ _ => 31
  | .bridgeLockA _ _ _ _ _ _ => 32
  | .bridgeFinalizeA _ _ _ _ => 33
  | .bridgeCancelA _ _ => 34
  | .sealA _ _ _ => 35
  | .unsealA _ _ _ => 36
  | .createSealPairA _ _ _ _ => 37
  | .makeSovereignA _ _ => 38
  | .refusalA _ _ => 39
  | .receiptArchiveA _ _ => 40
  | .queueAllocateA _ _ _ _ => 41
  | .queueEnqueueA _ _ _ _ _ _ _ => 42
  | .queueDequeueA _ _ _ _ _ => 43
  | .queueResizeA _ _ _ _ => 44
  | .queueAtomicTxA _ _ => 45
  | .queuePipelineStepA _ _ _ _ => 46
  | .pipelinedSendA _ => 47
  | .exportSturdyRefA _ _ _ _ _ => 48
  | .enlivenRefA _ _ _ _ => 49
  | .swissHandoffA _ _ _ _ => 50
  | .swissDropA _ _ _ => 51
  | .cellSealA _ _ => 52
  | .cellUnsealA _ _ => 53
  | .cellDestroyA _ _ _ => 54
  | .refreshDelegationA _ _ => 55

/-- Coverage count: every `FullActionA` constructor has a dispatch arm. -/
def actionDispatchCoverage : Nat := 56

/-! ## §2 — the hold-gate (for the `exerciseA` arm only; R4 facet-mask DEFERRED). -/

/-- **The hold-gate** `exerciseStepA` checks: the actor holds SOME cap conferring an edge to
`target` (`confersEdgeTo`). This is EXACTLY the executor gate — NOT the R4 facet-mask (DEFER). -/
def exerciseGuard (st : RecChainedState) (actor target : CellId) : Prop :=
  (st.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true

/-- The post-hold-gate chained state: kernel frozen, authority receipt prepended. -/
def exerciseHoldState (st : RecChainedState) (actor : CellId) : RecChainedState :=
  { st with log := authReceipt actor :: st.log }

@[simp] theorem exerciseHoldState_kernel (st : RecChainedState) (actor : CellId) :
    (exerciseHoldState st actor).kernel = st.kernel := rfl

@[simp] theorem exerciseHoldState_log (st : RecChainedState) (actor : CellId) :
    (exerciseHoldState st actor).log = authReceipt actor :: st.log := rfl

/-- **The hold-gate step spec** — the outer frame before the inner fold runs. -/
def ExerciseHoldSpec (st : RecChainedState) (actor target : CellId) (st' : RecChainedState) : Prop :=
  exerciseGuard st actor target ∧
  st' = exerciseHoldState st actor

/-! ## §2 — `fullActionStep` / `turnSpec` / `ExerciseSpec` (mutual declarative spine). -/

mutual
  /-- **Per-action declarative step** — case-splits `FullActionA` to the existing leaf apex specs. -/
  def fullActionStep (st : RecChainedState) (fa : FullActionA) (st' : RecChainedState) : Prop :=
    match fa with
    | .balanceA t a =>
        BalanceMovementSpec st t a st'
    | .delegate del rec t =>
        DelegateSpec st del rec t st'
    | .revoke holder t =>
        RevokeSpec st holder t st'
    | .mintA actor cell a amt =>
        MintASpec st actor cell a amt st'
    | .burnA actor cell a amt =>
        BurnSpec st actor cell a amt st'
    | .setFieldA actor cell f v =>
        SetFieldSpec st actor cell f v st'
    | .emitEventA actor cell topic data =>
        EmitEventSpec st actor cell topic data st'
    | .incrementNonceA actor cell n =>
        IncrementNonceSpec st actor cell n st'
    | .setPermissionsA actor cell p =>
        SetPermissionsSpec st actor cell p st'
    | .setVKA actor cell vk =>
        SetVKSpec st actor cell vk st'
    | .introduceA intro rec t =>
        DelegateSpec st intro rec t st'
    | .delegateAttenA del rec t keep =>
        DelegateAttenSpec st del rec t keep st'
    | .attenuateA actor idx keep =>
        AttenuateSpec st actor idx keep st'
    | .dropRefA holder t =>
        RevokeSpec st holder t st'
    | .revokeDelegationA holder t =>
        RevokeSpec st holder t st'
    | .validateHandoffA intro rec t =>
        DelegateSpec st intro rec t st'
    | .exerciseA actor target inner =>
        exerciseGuard st actor target ∧
        turnSpec (exerciseHoldState st actor) inner st'
    | .createCellA actor newCell =>
        CreateCellSpec st actor newCell st'
    | .createCellFromFactoryA actor newCell vk =>
        CreateFromFactorySpec st actor newCell vk st'
    | .spawnA actor child target =>
        SpawnSpec st actor child target st'
    | .bridgeMintA actor cell a value =>
        MintASpec st actor cell a value st'
    | .createEscrowA id actor creator recipient asset amount =>
        EscrowHoldingCreateSpec st id actor creator recipient asset amount st'
    | .releaseEscrowA id actor =>
        ReleaseEscrowSpec st id actor st'
    | .refundEscrowA id actor =>
        RefundEscrowSpec st id actor st'
    | .createObligationA id actor obligor beneficiary asset stake =>
        EscrowHoldingCreateSpec st id actor obligor beneficiary asset stake st'
    | .fulfillObligationA id actor =>
        RefundEscrowSpec st id actor st'
    | .slashObligationA id actor =>
        ReleaseEscrowSpec st id actor st'
    | .noteSpendA nf actor =>
        NoteSpendSpec st nf actor st'
    | .noteCreateA cm actor =>
        NoteCreateASpec st cm actor st'
    | .createCommittedEscrowA id actor creator recipient asset amount hidingProof =>
        CommittedEscrowCreateSpec st id actor creator recipient asset amount hidingProof st'
    | .releaseCommittedEscrowA id actor =>
        CommittedEscrowSettleSpec st id actor (fun r => r.recipient) releaseSettleAuthB st'
    | .refundCommittedEscrowA id actor =>
        CommittedEscrowSettleSpec st id actor (fun r => r.creator) refundSettleAuthB st'
    | .bridgeLockA id actor originator destination asset amount =>
        BridgeOutboundLockSpec st id actor originator destination asset amount st'
    | .bridgeFinalizeA id actor asset amount =>
        BridgeFinalizeSpec st id actor asset amount st'
    | .bridgeCancelA id actor =>
        BridgeOutboundCancelSpec st id actor st'
    | .sealA pid actor payload =>
        SealSpec st pid actor payload st'
    | .unsealA pid actor recipient =>
        match findSealedBox st.kernel.sealedBoxes pid with
        | none => False
        | some box => UnsealSpec st pid actor recipient box st'
    | .createSealPairA pid actor sealerHolder unsealerHolder =>
        CreateSealPairSpec st pid actor sealerHolder unsealerHolder st'
    | .makeSovereignA actor cell =>
        MakeSovereignSpec st actor cell st'
    | .refusalA actor cell =>
        RefusalSpec st actor cell st'
    | .receiptArchiveA actor cell =>
        ReceiptArchiveSpec st actor cell st'
    | .queueAllocateA id actor cell cap =>
        QueueAllocateSpec st id actor cell cap st'
    | .queueEnqueueA id m actor cell depId dAsset deposit =>
        QueueEnqueueSpec st id m actor cell depId dAsset deposit st'
    | .queueDequeueA id actor cell depId deposit =>
        QueueDequeueSpec st id actor cell depId deposit st'
    | .queueResizeA id newCap actor cell =>
        QueueResizeSpec st id newCap actor cell st'
    | .queueAtomicTxA actor ops =>
        QueueAtomicTxSpec st actor ops st'
    | .queuePipelineStepA srcId owner sinkCells sinkIds =>
        QueuePipelineFanoutSpec st srcId owner sinkCells sinkIds st'
    | .pipelinedSendA actor =>
        PipelinedSendSpec st actor st'
    | .exportSturdyRefA sw actor exporter target rights =>
        ExportSpec st sw actor exporter target rights st'
    | .enlivenRefA sw actor exporter claimed =>
        EnlivenSpec st sw actor exporter claimed st'
    | .swissHandoffA sw certHash introducer exporter =>
        HandoffSpec st sw certHash introducer exporter st'
    | .swissDropA sw actor exporter =>
        DropSpec st sw actor exporter st'
    | .cellSealA actor cell =>
        CellSealSpec st actor cell st'
    | .cellUnsealA actor cell =>
        CellUnsealSpec st actor cell st'
    | .cellDestroyA actor cell certHash =>
        CellDestroySpec st actor cell certHash st'
    | .refreshDelegationA actor child =>
        RefreshDelegationSpec st actor child st'

  /-- **Declarative inner-turn fold** — left-to-right, all-or-nothing, matching `execInnerA`. -/
  def turnSpec : RecChainedState → List FullActionA → RecChainedState → Prop
    | st, [], st' => st = st'
    | st, a :: rest, st' =>
        ∃ st1, fullActionStep st a st1 ∧ turnSpec st1 rest st'
end

/-- **The full-state declarative spec of a committed `exerciseA`.** Hold-gate + inner fold from
the hold post-state (auth receipt prepended, kernel frozen). Definitionally the `exerciseA` arm of
`fullActionStep`. -/
def ExerciseSpec (st : RecChainedState) (actor target : CellId) (inner : List FullActionA)
    (st' : RecChainedState) : Prop :=
  exerciseGuard st actor target ∧
  turnSpec (exerciseHoldState st actor) inner st'

/-! ## §3 — hold-gate ⟺ executor. -/

/-- **`exerciseStepA_iff_holdSpec` — the hold-gate step ⟺ `ExerciseHoldSpec`.** -/
theorem exerciseStepA_iff_holdSpec (st st' : RecChainedState) (actor target : CellId) :
    exerciseStepA st actor target = some st' ↔ ExerciseHoldSpec st actor target st' := by
  unfold ExerciseHoldSpec exerciseGuard exerciseHoldState exerciseStepA
  by_cases hg : (st.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hg, rfl⟩
    · rintro ⟨_, h⟩
      subst h
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-! ## §4 — `execInnerA` = `execFullTurnA`. -/

/-- **`execInnerA_eq_execFullTurnA` — PROVED.** The mutual inner fold and the named full-turn
executor coincide (same `execFullA` head + tail shape). -/
theorem execInnerA_eq_execFullTurnA (st : RecChainedState) (inner : List FullActionA) :
    execInnerA st inner = execFullTurnA st inner := by
  induction inner generalizing st with
  | nil => rfl
  | cons a rest ih =>
      simp only [execInnerA, execFullTurnA]
      cases h : execFullA st a with
      | none => rfl
      | some st1 => simp only [h]; exact ih st1

/-! ## §5–§7 — dispatcher bridge + inner fold + exercise. -/

mutual
  /-- **`execInnerA_iff_turnSpec` — the inner fold ⟺ declarative `turnSpec` (both directions).** -/
  theorem execInnerA_iff_turnSpec (st st' : RecChainedState) :
      ∀ inner, execInnerA st inner = some st' ↔ turnSpec st inner st'
    | [] => by simp [execInnerA, turnSpec]
    | a :: rest => by
        simp only [execInnerA, turnSpec]
        constructor
        · intro h
          cases hfa : execFullA st a with
          | none => simp [hfa] at h
          | some s₁ =>
              have hrest : execInnerA s₁ rest = some st' := by simpa [hfa] using h
              exact ⟨s₁, (fullActionStep_exec_iff st s₁ a).mp hfa, (execInnerA_iff_turnSpec s₁ st' rest).mp hrest⟩
        · intro h
          obtain ⟨s₁, hstep, htail⟩ := h
          cases hfa : execFullA st a with
          | none =>
              exact absurd ((fullActionStep_exec_iff st s₁ a).mpr hstep) (by simp [hfa])
          | some s₁' =>
              have hexec := (fullActionStep_exec_iff st s₁ a).mpr hstep
              have heq : s₁' = s₁ := Option.some.inj (hfa.symm.trans hexec)
              simpa [execInnerA, hfa, heq] using (execInnerA_iff_turnSpec s₁ st' rest).mpr htail
  termination_by inner => sizeOf inner

  /-- **`fullActionStep_exec_iff` — EVERY arm ⟺ its existing executor⟺spec keystone.** -/
  theorem fullActionStep_exec_iff (st st' : RecChainedState) :
      ∀ fa, execFullA st fa = some st' ↔ fullActionStep st fa st'
    | .balanceA t a => by
      simp only [fullActionStep, execFullA]
      exact execFullA_balanceA_iff_spec st t a st'
    | .delegate del rec t => by
      simp only [fullActionStep, execFullA]
      exact execFullA_delegate_iff_spec st del rec t st'
    | .revoke holder t => by
      simp only [fullActionStep, execFullA]
      exact execFullA_revoke_iff_spec st holder t st'
    | .mintA actor cell a amt => by
      simp only [fullActionStep, execFullA]
      exact execMintA_iff_spec st actor cell a amt st'
    | .burnA actor cell a amt => by
      simp only [fullActionStep, execFullA]
      exact execFullA_burnA_iff_spec st actor cell a amt st'
    | .setFieldA actor cell f v => by
      simp only [fullActionStep, execFullA]
      exact execFullA_setFieldA_iff_spec st actor cell f v st'
    | .emitEventA actor cell topic data => by
      simp only [fullActionStep, execFullA]
      exact execFullA_emitEvent_iff_spec st actor cell topic data st'
    | .incrementNonceA actor cell n => by
      simp only [fullActionStep, execFullA]
      exact execFullA_incrementNonce_iff_spec st actor cell n st'
    | .setPermissionsA actor cell p => by
      simp only [fullActionStep, execFullA]
      exact execFullA_setPermissions_iff_spec st actor cell p st'
    | .setVKA actor cell vk => by
      simp only [fullActionStep, execFullA]
      exact execFullA_setVK_iff_spec st actor cell vk st'
    | .introduceA intro rec t => by
      simp only [fullActionStep, execFullA]
      exact execFullA_introduceA_iff_spec st intro rec t st'
    | .delegateAttenA del rec t keep => by
      simp only [fullActionStep, execFullA]
      exact delegateAtten_iff_spec st del rec t keep st'
    | .attenuateA actor idx keep => by
      simp only [fullActionStep, execFullA]
      exact attenuate_iff_spec st actor idx keep st'
    | .dropRefA holder t => by
      simp only [fullActionStep, execFullA]
      exact execFullA_dropRef_iff_spec st holder t st'
    | .revokeDelegationA holder t => by
      simp only [fullActionStep, execFullA]
      exact execFullA_revokeDelegation_iff_spec st holder t st'
    | .validateHandoffA intro rec t => by
      simp only [fullActionStep, execFullA]
      exact execFullA_validateHandoff_iff_spec st intro rec t st'
    | .exerciseA actor target inner => by
      simp only [fullActionStep, ExerciseSpec, execFullA]
      constructor
      · intro h
        cases hg : exerciseStepA st actor target with
        | none =>
            rw [hg] at h
            exact absurd h (by simp)
        | some st1 =>
            obtain ⟨hguard, hst1⟩ := exerciseStepA_iff_holdSpec st st1 actor target |>.mp hg
            have hinner : execInnerA st1 inner = some st' := by simpa [hg] using h
            refine And.intro hguard ?_
            rw [← hst1]
            exact (execInnerA_iff_turnSpec st1 st' inner).mp hinner
      · intro h
        have hguard : exerciseGuard st actor target := h.1
        have hinner : turnSpec (exerciseHoldState st actor) inner st' := h.2
        have hg : exerciseStepA st actor target = some (exerciseHoldState st actor) :=
          (exerciseStepA_iff_holdSpec st (exerciseHoldState st actor) actor target).mpr
            ⟨hguard, rfl⟩
        simpa [hg, exerciseHoldState, Option.bind_eq_some_iff] using
          (execInnerA_iff_turnSpec (exerciseHoldState st actor) st' inner).mpr hinner
    | .createCellA actor newCell => by
      simp only [fullActionStep, execFullA]
      exact execCreateCellA_iff_spec st actor newCell st'
    | .createCellFromFactoryA actor newCell vk => by
      simp only [fullActionStep, execFullA]
      exact execCreateFromFactoryA_iff_spec st actor newCell vk st'
    | .spawnA actor child target => by
      simp only [fullActionStep, execFullA]
      exact execSpawnA_iff_spec st actor child target st'
    | .bridgeMintA actor cell a value => by
      simp only [fullActionStep, execFullA]
      exact Dregg2.Circuit.Spec.SupplyCreation.execBridgeMintA_iff_spec st actor cell a value st'
    | .createEscrowA id actor creator recipient asset amount => by
      simp only [fullActionStep, execFullA]
      exact execFullA_createEscrowA_iff_spec st id actor creator recipient asset amount st'
    | .releaseEscrowA id actor => by
      simp only [fullActionStep, execFullA]
      exact execFullA_releaseEscrow_iff_spec st id actor st'
    | .refundEscrowA id actor => by
      simp only [fullActionStep, execFullA]
      exact execFullA_refundEscrowA_iff_spec st id actor st'
    | .createObligationA id actor obligor beneficiary asset stake => by
      simp only [fullActionStep, execFullA]
      exact execFullA_createObligationA_iff_spec st id actor obligor beneficiary asset stake st'
    | .fulfillObligationA id actor => by
      simp only [fullActionStep, execFullA]
      exact execFullA_fulfillObligationA_iff_spec st id actor st'
    | .slashObligationA id actor => by
      simp only [fullActionStep, execFullA]
      exact execFullA_slashObligation_iff_spec st id actor st'
    | .noteSpendA nf actor => by
      simp only [fullActionStep, execFullA]
      exact execFullA_noteSpend_iff_spec st nf actor st'
    | .noteCreateA cm actor => by
      simp only [fullActionStep, execFullA]
      exact execNoteCreateA_iff_spec st cm actor st'
    | .createCommittedEscrowA id actor creator recipient asset amount hidingProof => by
      simp only [fullActionStep, execFullA]
      exact execFullA_createCommittedEscrowA_iff_spec st id actor creator recipient asset amount hidingProof st'
    | .releaseCommittedEscrowA id actor => by
      simp only [fullActionStep, execFullA]
      exact execFullA_releaseCommittedEscrowA_iff_spec st id actor st'
    | .refundCommittedEscrowA id actor => by
      simp only [fullActionStep, execFullA]
      exact execFullA_refundCommittedEscrowA_iff_spec st id actor st'
    | .bridgeLockA id actor originator destination asset amount => by
      simp only [fullActionStep, execFullA]
      exact execFullA_bridgeLockA_iff_spec st id actor originator destination asset amount st'
    | .bridgeFinalizeA id actor asset amount => by
      simp only [fullActionStep, execFullA]
      exact execFullA_bridgeFinalize_iff_spec st id actor asset amount st'
    | .bridgeCancelA id actor => by
      simp only [fullActionStep, execFullA]
      exact execFullA_bridgeCancelA_iff_spec st id actor st'
    | .sealA pid actor payload => by
      simp only [fullActionStep, execFullA]
      exact execFullA_seal_iff_spec st pid actor payload st'
    | .unsealA pid actor recipient => by
      cases hbox : findSealedBox st.kernel.sealedBoxes pid with
      | none =>
          simp only [fullActionStep, execFullA, hbox]
          constructor
          · intro h
            have hnone := unsealChainA_noBox_rejects st pid actor recipient hbox
            simpa [hnone] using h
          · intro h; cases h
      | some box =>
          simp only [fullActionStep, execFullA, hbox]
          exact execFullA_unseal_iff_spec st pid actor recipient box st' hbox
    | .createSealPairA pid actor sealerHolder unsealerHolder => by
      simp only [fullActionStep, execFullA]
      exact createSealPair_iff_spec st pid actor sealerHolder unsealerHolder st'
    | .makeSovereignA actor cell => by
      simp only [fullActionStep, execFullA]
      exact execFullA_makeSovereignA_iff_spec st actor cell st'
    | .refusalA actor cell => by
      simp only [fullActionStep, execFullA]
      exact execFullA_refusalA_iff_spec st actor cell st'
    | .receiptArchiveA actor cell => by
      simp only [fullActionStep, execFullA]
      exact execFullA_receiptArchiveA_iff_spec st actor cell st'
    | .queueAllocateA id actor cell cap => by
      simp only [fullActionStep, execFullA]
      exact execFullA_queueAllocateA_iff_spec st id actor cell cap st'
    | .queueEnqueueA id m actor cell depId dAsset deposit => by
      simp only [fullActionStep, execFullA]
      exact execFullA_queueEnqueueA_iff_spec st id m actor cell depId dAsset deposit st'
    | .queueDequeueA id actor cell depId deposit => by
      simp only [fullActionStep, execFullA]
      exact execFullA_queueDequeueA_iff_spec st id actor cell depId deposit st'
    | .queueResizeA id newCap actor cell => by
      simp only [fullActionStep, execFullA]
      exact execFullA_queueResizeA_iff_spec st id newCap actor cell st'
    | .queueAtomicTxA actor ops => by
      simp only [fullActionStep, execFullA]
      exact execFullA_queueAtomicTxA_iff_spec st actor ops st'
    | .queuePipelineStepA srcId owner sinkCells sinkIds => by
      simp only [fullActionStep, execFullA]
      exact execFullA_iff_spec st srcId owner sinkCells sinkIds st'
    | .pipelinedSendA actor => by
      simp only [fullActionStep, execFullA]
      exact execFullA_pipelinedSend_iff_spec st actor st'
    | .exportSturdyRefA sw actor exporter target rights => by
      simp only [fullActionStep, execFullA]
      exact export_iff_spec st sw actor exporter target rights st'
    | .enlivenRefA sw actor exporter claimed => by
      simp only [fullActionStep, execFullA]
      exact execFullA_enliven_iff_spec st sw actor exporter claimed st'
    | .swissHandoffA sw certHash introducer exporter => by
      simp only [fullActionStep, execFullA]
      exact execFullA_handoff_iff_spec st sw certHash introducer exporter st'
    | .swissDropA sw actor exporter => by
      simp only [fullActionStep, execFullA]
      exact execFullA_drop_iff_spec st sw actor exporter st'
    | .cellSealA actor cell => by
      simp only [fullActionStep, execFullA]
      exact cellSeal_iff_spec st actor cell st'
    | .cellUnsealA actor cell => by
      simp only [fullActionStep, execFullA]
      exact cellUnseal_iff_spec st actor cell st'
    | .cellDestroyA actor cell certHash => by
      simp only [fullActionStep, execFullA]
      exact cellDestroy_iff_spec st actor cell certHash st'
    | .refreshDelegationA actor child => by
      simp only [fullActionStep, execFullA]
      exact refreshDelegation_iff_spec st actor child st'
  termination_by fa => sizeOf fa
end

/-- **`execFullA_exerciseA_iff_spec` — exercise ⟺ independent `ExerciseSpec`.** -/
theorem execFullA_exerciseA_iff_spec (st st' : RecChainedState) (actor target : CellId)
    (inner : List FullActionA) :
    execFullA st (.exerciseA actor target inner) = some st'
      ↔ ExerciseSpec st actor target inner st' := by
  simp only [ExerciseSpec, execFullA]
  constructor
  · intro h
    cases hg : exerciseStepA st actor target with
    | none =>
        rw [hg] at h
        exact absurd h (by simp)
    | some st1 =>
        obtain ⟨hguard, hst1⟩ := exerciseStepA_iff_holdSpec st st1 actor target |>.mp hg
        have hinner : execInnerA st1 inner = some st' := by simpa [hg] using h
        refine And.intro hguard ?_
        rw [← hst1]
        exact (execInnerA_iff_turnSpec st1 st' inner).mp hinner
  · intro h
    have hguard : exerciseGuard st actor target := h.1
    have hinner : turnSpec (exerciseHoldState st actor) inner st' := h.2
    have hg : exerciseStepA st actor target = some (exerciseHoldState st actor) :=
      (exerciseStepA_iff_holdSpec st (exerciseHoldState st actor) actor target).mpr
        ⟨hguard, rfl⟩
    simpa [hg, exerciseHoldState, Option.bind_eq_some_iff] using
      (execInnerA_iff_turnSpec (exerciseHoldState st actor) st' inner).mpr hinner

/-- **`execFullTurnA_iff_turnSpec` — the named full-turn executor ⟺ `turnSpec`.** -/
theorem execFullTurnA_iff_turnSpec (st st' : RecChainedState) (inner : List FullActionA) :
    execFullTurnA st inner = some st' ↔ turnSpec st inner st' := by
  rw [← execInnerA_eq_execFullTurnA, execInnerA_iff_turnSpec]

/-! ## §8 — conservation corollaries (via `execInnerA_ledger_per_asset`). -/

/-- **`turnSpec_ledger_per_asset` — a committed `turnSpec` inner fold moves the combined per-asset
measure by exactly the net inner delta.** Reads off the proved `execInnerA_ledger_per_asset` through
the spec bridge. -/
theorem turnSpec_ledger_per_asset (st st' : RecChainedState) (inner : List FullActionA) (b : AssetId)
    (h : turnSpec st inner st') :
    recTotalAssetWithEscrow st'.kernel b = recTotalAssetWithEscrow st.kernel b + turnLedgerDeltaAsset inner b :=
  execInnerA_ledger_per_asset st st' inner b ((execInnerA_iff_turnSpec st st' inner).mpr h)

/-- **`exerciseSpec_ledger_per_asset` — exercise conservation: the hold-gate is kernel-neutral, so
the net move is the SUM of the inner per-action deltas.** -/
theorem exerciseSpec_ledger_per_asset (st st' : RecChainedState) (actor target : CellId)
    (inner : List FullActionA) (b : AssetId) (h : ExerciseSpec st actor target inner st') :
    recTotalAssetWithEscrow st'.kernel b =
      recTotalAssetWithEscrow st.kernel b + turnLedgerDeltaAsset inner b := by
  rcases h with ⟨_, hinner⟩
  have hledger :=
    turnSpec_ledger_per_asset (exerciseHoldState st actor) st' inner b hinner
  simpa [exerciseHoldState_kernel] using hledger

/-! ## §9 — axiom-hygiene tripwires. -/

#assert_axioms exerciseHoldState_kernel
#assert_axioms exerciseStepA_iff_holdSpec
#assert_axioms execInnerA_eq_execFullTurnA
#assert_axioms fullActionStep_exec_iff
#assert_axioms execInnerA_iff_turnSpec
#assert_axioms execFullTurnA_iff_turnSpec
#assert_axioms execFullA_exerciseA_iff_spec
#assert_axioms turnSpec_ledger_per_asset
#assert_axioms exerciseSpec_ledger_per_asset
end Dregg2.Circuit.ActionDispatch