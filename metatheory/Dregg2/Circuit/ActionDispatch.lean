/-
# Dregg2.Circuit.ActionDispatch — the `FullActionA` apex dispatcher (Wave 1).

`fullActionStep` case-splits every `FullActionA` constructor to the existing per-family apex specs
(the leaf `Circuit/Spec/*` modules). `fullActionStep_exec_iff` proves each arm ⟺ its
`execFullA_*_iff_spec` keystone — the spine `TurnWitness` and `Spec.exercise` build on.
dregg3 F1a: the escrow / obligation / bridge-Lock/Finalize/Cancel families lost their spec
modules (deleted; they re-land as verified factory cell-programs in `Dregg2/Apps/`); their
arms carry the executor equation verbatim until F1b removes the kernel constructors.
dregg3 F2a+F2b: the queue family (allocate/enqueue/dequeue/resize/atomicTx/pipelineStep) lost its
spec modules AND its `FullActionA` constructors (VerbRegistry: `.factory .queue`; behavior =
`Dregg2/Apps/QueueFactory` et al — the factory story).

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
-/
import Dregg2.Circuit.Spec.accountgrowth
import Dregg2.Circuit.Spec.authorityattenuation
import Dregg2.Circuit.Spec.authorityrevocation
import Dregg2.Circuit.Spec.authorityunattenuated
import Dregg2.Circuit.Spec.balancemovement
import Dregg2.Circuit.Spec.bridgeinboundmint
import Dregg2.Circuit.Spec.celllifecycle
import Dregg2.Circuit.Spec.cellstateaudit
import Dregg2.Circuit.Spec.cellstatefield
import Dregg2.Circuit.Spec.cellstatelog
import Dregg2.Circuit.Spec.cellstatemonotone
import Dregg2.Circuit.Spec.cellstatepermissions
import Dregg2.Circuit.Spec.cellstatevk
import Dregg2.Circuit.Spec.factorycreation
import Dregg2.Circuit.Spec.notecommitment
import Dregg2.Circuit.Spec.notenullifier
import Dregg2.Circuit.Spec.queuepipelinedsend
import Dregg2.Circuit.Spec.refreshdelegation
import Dregg2.Circuit.Spec.sovereigncommitment
import Dregg2.Circuit.Spec.supplycreation
import Dregg2.Circuit.Spec.supplydestruction
import Dregg2.Circuit.Spec.Turn
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
open Dregg2.Circuit.Spec.BridgeInboundMint
open Dregg2.Circuit.Spec.SovereignCommitment
open Dregg2.Circuit.Spec.CellStateAudit
open Dregg2.Circuit.Spec.QueuePipelinedSend
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
  | .revokeDelegationA _ _ => 14
  | .exerciseA _ _ _ => 16
  | .createCellA _ _ => 17
  | .createCellFromFactoryA _ _ _ => 18
  | .spawnA _ _ _ => 19
  | .bridgeMintA _ _ _ _ => 20
  | .noteSpendA _ _ _ => 27
  | .noteCreateA _ _ => 28
  | .makeSovereignA _ _ => 38
  | .refusalA _ _ => 39
  | .receiptArchiveA _ _ => 40
  | .pipelinedSendA _ => 47
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
    | .revokeDelegationA holder t =>
        RevokeSpec st holder t st'
    | .exerciseA actor target inner =>
        innerFacetsAdmittedA st actor target inner = true ∧
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
    | .noteSpendA nf actor spendProof =>
        NoteSpendSpec st nf actor spendProof st'
    | .noteCreateA cm actor =>
        NoteCreateASpec st cm actor st'
    | .makeSovereignA actor cell =>
        MakeSovereignSpec st actor cell st'
    | .refusalA actor cell =>
        RefusalSpec st actor cell st'
    | .receiptArchiveA actor cell =>
        ReceiptArchiveSpec st actor cell st'
    -- dregg3 F2b: the queue-family constructors are GONE (the behavior is the verified
    -- `Dregg2/Apps/QueueFactory` et al — the factory story).
    | .pipelinedSendA actor =>
        PipelinedSendSpec st actor st'
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

/-- **`turnSpec_eq_spec`** — the apex dispatcher's `turnSpec` is the generic `Spec.Turn.turnSpec`
instantiated at `fullActionStep`. -/
theorem turnSpec_eq_spec (st : RecChainedState) (acts : List FullActionA) (st' : RecChainedState) :
    turnSpec st acts st' ↔ Spec.Turn.turnSpec fullActionStep st acts st' := by
  induction acts generalizing st with
  | nil => simp [turnSpec, Spec.Turn.turnSpec]
  | cons a rest ih =>
      simp only [turnSpec, Spec.Turn.turnSpec]
      constructor
      · intro ⟨st1, hstep, htail⟩
        exact ⟨st1, hstep, (ih st1).mp htail⟩
      · intro ⟨st1, hstep, htail⟩
        exact ⟨st1, hstep, (ih st1).mpr htail⟩

/-- **The full-state declarative spec of a committed `exerciseA`.** Hold-gate + inner fold from
the hold post-state (auth receipt prepended, kernel frozen). Definitionally the `exerciseA` arm of
`fullActionStep`. -/
def ExerciseSpec (st : RecChainedState) (actor target : CellId) (inner : List FullActionA)
    (st' : RecChainedState) : Prop :=
  innerFacetsAdmittedA st actor target inner = true ∧
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

/-- **`execInnerA_eq_execFullTurnA`.** The mutual inner fold and the named full-turn
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
    | .revokeDelegationA holder t => by
      simp only [fullActionStep, execFullA]
      exact execFullA_revokeDelegation_iff_spec st holder t st'
    | .exerciseA actor target inner => by
      simp only [fullActionStep, ExerciseSpec, execFullA]
      constructor
      · intro h
        by_cases hf : innerFacetsAdmittedA st actor target inner = true
        · rw [if_pos hf] at h
          cases hg : exerciseStepA st actor target with
          | none =>
              rw [hg] at h
              exact absurd h (by simp)
          | some st1 =>
              obtain ⟨hguard, hst1⟩ := exerciseStepA_iff_holdSpec st st1 actor target |>.mp hg
              have hinner : execInnerA st1 inner = some st' := by simpa [hg] using h
              refine And.intro hf (And.intro hguard ?_)
              rw [← hst1]
              exact (execInnerA_iff_turnSpec st1 st' inner).mp hinner
        · rw [if_neg hf] at h; exact absurd h (by simp)
      · intro h
        have hf : innerFacetsAdmittedA st actor target inner = true := h.1
        have hguard : exerciseGuard st actor target := h.2.1
        have hinner : turnSpec (exerciseHoldState st actor) inner st' := h.2.2
        have hg : exerciseStepA st actor target = some (exerciseHoldState st actor) :=
          (exerciseStepA_iff_holdSpec st (exerciseHoldState st actor) actor target).mpr
            ⟨hguard, rfl⟩
        rw [if_pos hf]
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
    | .noteSpendA nf actor spendProof => by
      simp only [fullActionStep, execFullA]
      exact execFullA_noteSpend_iff_spec st nf actor spendProof st'
    | .noteCreateA cm actor => by
      simp only [fullActionStep, execFullA]
      exact execNoteCreateA_iff_spec st cm actor st'
    | .makeSovereignA actor cell => by
      simp only [fullActionStep, execFullA]
      exact execFullA_makeSovereignA_iff_spec st actor cell st'
    | .refusalA actor cell => by
      simp only [fullActionStep, execFullA]
      exact execFullA_refusalA_iff_spec st actor cell st'
    | .receiptArchiveA actor cell => by
      simp only [fullActionStep, execFullA]
      exact execFullA_receiptArchiveA_iff_spec st actor cell st'
    | .pipelinedSendA actor => by
      simp only [fullActionStep, execFullA]
      exact execFullA_pipelinedSend_iff_spec st actor st'
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
    by_cases hf : innerFacetsAdmittedA st actor target inner = true
    · rw [if_pos hf] at h
      cases hg : exerciseStepA st actor target with
      | none =>
          rw [hg] at h
          exact absurd h (by simp)
      | some st1 =>
          obtain ⟨hguard, hst1⟩ := exerciseStepA_iff_holdSpec st st1 actor target |>.mp hg
          have hinner : execInnerA st1 inner = some st' := by simpa [hg] using h
          refine And.intro hf (And.intro hguard ?_)
          rw [← hst1]
          exact (execInnerA_iff_turnSpec st1 st' inner).mp hinner
    · rw [if_neg hf] at h; exact absurd h (by simp)
  · intro h
    have hf : innerFacetsAdmittedA st actor target inner = true := h.1
    have hguard : exerciseGuard st actor target := h.2.1
    have hinner : turnSpec (exerciseHoldState st actor) inner st' := h.2.2
    have hg : exerciseStepA st actor target = some (exerciseHoldState st actor) :=
      (exerciseStepA_iff_holdSpec st (exerciseHoldState st actor) actor target).mpr
        ⟨hguard, rfl⟩
    rw [if_pos hf]
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
    recTotalAsset st'.kernel b = recTotalAsset st.kernel b + turnLedgerDeltaAsset inner b :=
  execInnerA_ledger_per_asset st st' inner b ((execInnerA_iff_turnSpec st st' inner).mpr h)

/-- **`exerciseSpec_ledger_per_asset` — exercise conservation: the hold-gate is kernel-neutral, so
the net move is the SUM of the inner per-action deltas.** -/
theorem exerciseSpec_ledger_per_asset (st st' : RecChainedState) (actor target : CellId)
    (inner : List FullActionA) (b : AssetId) (h : ExerciseSpec st actor target inner st') :
    recTotalAsset st'.kernel b =
      recTotalAsset st.kernel b + turnLedgerDeltaAsset inner b := by
  rcases h with ⟨_, _, hinner⟩
  have hledger :=
    turnSpec_ledger_per_asset (exerciseHoldState st actor) st' inner b hinner
  simpa [exerciseHoldState_kernel] using hledger

/-! ## §9 — axiom-hygiene tripwires. -/

#assert_axioms turnSpec_eq_spec
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