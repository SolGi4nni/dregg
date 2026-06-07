/-
# Dregg2.Exec.CellCommit — the COMMITMENT-PERSISTENCE crown: a published note commitment is never retracted.

`Exec/CellReal.lean` crowned the SHIPPED per-asset executor `execFullForestA` (the 46-effect, auth-gated
tree) with the coinductive **living cell** `livingCellA`, and `Exec/CellCarry.lean` distilled the
PARAMETRIC crown `livingCellA_carries`: ANY *state* predicate `Good` preserved by ONE living-cell step
holds along the ENTIRE unbounded adversarial trajectory `trajA`, under EVERY schedule. Conservation
(`livingCellA_obs_invariant'`) and the append-only audit log (`livingCellA_logMono`) are its first two
instances. This module adds the third headline of the **private-note layer**:

> **The note-commitment set is GROW-ONLY, FOREVER.** A commitment that has ever been published
> (`com0 ⊆ s.kernel.commitments`) is contained in `commitments` at EVERY index of the unbounded
> adversarial trajectory: it is never retracted, dropped, or rewritten. This is the **anti-equivocation /
> auditability** invariant of the off-ledger commitment tree — the grow-only DUAL of the nullifier set's
> no-double-spend (`META-FILL C`, closing `#121`) — now COINDUCTIVE on the real executor.

The proof is the same parametric shape as `livingCellA_logMono`, with the load-bearing per-step content
being a **registry frame lemma**: across ONE real `execFullA` step, `s.kernel.commitments` is *grown-only*
— `noteCreate` conses a fresh commitment onto it (`noteCreateCommitment`), and EVERY OTHER effect frames
it UNCHANGED (each kernel mutator is a `{ k with <non-commitments fields> := … }` structure update). So
`s.kernel.commitments ⊆ s'.kernel.commitments` for a committed `execFullA`, lifted to the forest and then
carried forever by `livingCellA_carries`.

Together with the nullifier-persistence crown this is the audit/anti-double-spend pair of the private-note
layer: the spent-set never loses a nullifier (no double-spend), the commitment-set never loses a
commitment (no equivocation) — both as `∀ n, Good (trajA …)` temporal νF invariants on the real machine.

Three theorems, ascending:
* **`execFullA_commitments_grow`** — the per-step registry frame: a committed `execFullA` step only GROWS
  `commitments` (`s.kernel.commitments ⊆ s'.kernel.commitments`), by case analysis on the 46-effect kind
  (noteCreate conses; all others frame). This is the executor-level content the crown stands on.
* **`execFullForestA_commitments_grow`** — the forest/turn lift: a committed full-FOREST only grows
  `commitments`, by induction on the lowered action list through the pre-order bridge.
* **`livingCellA_commitments_persist`** — THE CROWN: `com0 ⊆ s.kernel.commitments → ∀ n, com0 ⊆
  (trajA s sched n).kernel.commitments`. The grow-only set carried along the whole unbounded trajectory by
  `livingCellA_carries` with `Good := (com0 ⊆ ·.kernel.commitments)` — a genuinely NON-conservation safety,
  discharged from the registry frame on a commit + the stay-put self-loop on a reject.
-/
import Dregg2.Exec.CellCarry

namespace Dregg2.Exec

open Dregg2.Boundary
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState
open Dregg2.Authority
open Dregg2.Tactics

/-- **`subset_of_commitments_eq`** — a tiny bridge: when a step left the commitment set LITERALLY
unchanged (`k'.commitments = k.commitments`), the grow-only `⊆` holds by reflexivity. The uniform
closer the framing arms of `execFullA_commitments_grow` use (the non-`noteCreate` effects). -/
theorem subset_of_commitments_eq {k k' : RecordKernelState} (h : k'.commitments = k.commitments) :
    k.commitments ⊆ k'.commitments := by rw [h]; exact List.Subset.refl _

/-! ## Step 0 — per-mutator COMMITMENTS frames: each kernel mutator leaves `commitments` UNCHANGED.

Every `execFullA` arm's kernel mutator is a `{ k with <fields> := … }` structure update whose `<fields>`
NEVER includes `commitments` — except `noteCreateCommitment`, which conses onto it. We pin the "unchanged"
half here as tiny per-mutator frames (each: unfold, split the admissibility gate, `subst`, `rfl`), so the
master step lemma is a thin dispatch rather than 40 inline gate-peels. The `none` (rejected) branch is
discharged by the master lemma; these speak only to a committed `some k'`. -/

/-- Per-asset transfer leaves `commitments` unchanged (it edits only `bal`). -/
theorem recKExecAsset_commitments {k k' : RecordKernelState} {turn : Turn} {a : AssetId}
    (h : recKExecAsset k turn a = some k') : k'.commitments = k.commitments := by
  unfold recKExecAsset at h; split at h
  · obtain ⟨rfl⟩ := h; rfl
  · exact absurd h (by simp)

/-- Per-asset mint leaves `commitments` unchanged (edits only `bal`). -/
theorem recKMintAsset_commitments {k k' : RecordKernelState} {actor cell : CellId} {a : AssetId} {amt : ℤ}
    (h : recKMintAsset k actor cell a amt = some k') : k'.commitments = k.commitments := by
  unfold recKMintAsset at h; split at h
  · obtain ⟨rfl⟩ := h; rfl
  · exact absurd h (by simp)

/-- Per-asset burn leaves `commitments` unchanged (edits only `bal`). -/
theorem recKBurnAsset_commitments {k k' : RecordKernelState} {actor cell : CellId} {a : AssetId} {amt : ℤ}
    (h : recKBurnAsset k actor cell a amt = some k') : k'.commitments = k.commitments := by
  unfold recKBurnAsset at h; split at h
  · obtain ⟨rfl⟩ := h; rfl
  · exact absurd h (by simp)

/-- Delegate leaves `commitments` unchanged (edits only `caps`). -/
theorem recKDelegate_commitments {k k' : RecordKernelState} {del rec t : CellId}
    (h : recKDelegate k del rec t = some k') : k'.commitments = k.commitments := by
  unfold recKDelegate at h; split at h
  · obtain ⟨rfl⟩ := h; rfl
  · exact absurd h (by simp)

/-- Rights-carrying delegate leaves `commitments` unchanged (edits only `caps`). -/
theorem recKDelegateAtten_commitments {k k' : RecordKernelState} {del rec t : CellId} {keep : List Auth}
    (h : recKDelegateAtten k del rec t keep = some k') : k'.commitments = k.commitments := by
  unfold recKDelegateAtten at h; split at h
  · obtain ⟨rfl⟩ := h; rfl
  · exact absurd h (by simp)

/-- Target-revocation is total and leaves `commitments` unchanged (edits only `caps`). -/
theorem recKRevokeTarget_commitments (k : RecordKernelState) (holder t : CellId) :
    (recKRevokeTarget k holder t).commitments = k.commitments := rfl

/-- A field write leaves `commitments` unchanged (edits only `cell`). -/
theorem writeField_commitments (k : RecordKernelState) (f : FieldName) (target : CellId) (v : Value) :
    (writeField k f target v).commitments = k.commitments := rfl

/-- The make-sovereign rebind leaves `commitments` unchanged (edits only `cell`). -/
theorem makeSovereignKernel_commitments (k : RecordKernelState) (target : CellId) :
    (makeSovereignKernel k target).commitments = k.commitments := rfl

/-- A fresh-cell insert leaves `commitments` unchanged (edits only `accounts`/`bal`). -/
theorem createCellIntoAsset_commitments (k : RecordKernelState) (newCell : CellId) :
    (createCellIntoAsset k newCell).commitments = k.commitments := rfl

/-- Note-SPEND leaves `commitments` unchanged (grows `nullifiers`, the orthogonal set). -/
theorem noteSpendNullifier_commitments {k k' : RecordKernelState} {nf : Nat}
    (h : noteSpendNullifier k nf = some k') : k'.commitments = k.commitments := by
  unfold noteSpendNullifier at h; split at h
  · exact absurd h (by simp)
  · obtain ⟨rfl⟩ := h; rfl

/-- Escrow create leaves `commitments` unchanged (edits only `bal`/`escrows`). -/
theorem createEscrowKAsset_commitments {k k' : RecordKernelState} {id : Nat}
    {actor creator recipient : CellId} {asset : AssetId} {amount : ℤ}
    (h : createEscrowKAsset k id actor creator recipient asset amount = some k') :
    k'.commitments = k.commitments := by
  unfold createEscrowKAsset at h; split at h
  · obtain ⟨rfl⟩ := h; rfl
  · exact absurd h (by simp)

/-- Escrow release leaves `commitments` unchanged (edits only `bal`/`escrows`). -/
theorem releaseEscrowKAsset_commitments {k k' : RecordKernelState} {id : Nat}
    (h : releaseEscrowKAsset k id = some k') : k'.commitments = k.commitments := by
  unfold releaseEscrowKAsset at h; split at h
  · split at h
    · obtain ⟨rfl⟩ := h; rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Escrow refund leaves `commitments` unchanged (edits only `bal`/`escrows`). -/
theorem refundEscrowKAsset_commitments {k k' : RecordKernelState} {id : Nat}
    (h : refundEscrowKAsset k id = some k') : k'.commitments = k.commitments := by
  unfold refundEscrowKAsset at h; split at h
  · split at h
    · obtain ⟨rfl⟩ := h; rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Bridge lock leaves `commitments` unchanged (edits only `bal`/`escrows`). -/
theorem bridgeLockKAsset_commitments {k k' : RecordKernelState} {id : Nat}
    {actor originator destination : CellId} {asset : AssetId} {amount : ℤ}
    (h : bridgeLockKAsset k id actor originator destination asset amount = some k') :
    k'.commitments = k.commitments := by
  unfold bridgeLockKAsset at h; split at h
  · obtain ⟨rfl⟩ := h; rfl
  · exact absurd h (by simp)

/-- Bridge finalize leaves `commitments` unchanged (edits only `escrows`). -/
theorem bridgeFinalizeKAsset_commitments {k k' : RecordKernelState} {id : Nat} {asset : AssetId} {amount : ℤ}
    (h : bridgeFinalizeKAsset k id asset amount = some k') : k'.commitments = k.commitments := by
  unfold bridgeFinalizeKAsset at h; split at h
  · split at h
    · obtain ⟨rfl⟩ := h; rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Bridge cancel leaves `commitments` unchanged (edits only `bal`/`escrows`). -/
theorem bridgeCancelKAsset_commitments {k k' : RecordKernelState} {id : Nat}
    (h : bridgeCancelKAsset k id = some k') : k'.commitments = k.commitments := by
  unfold bridgeCancelKAsset at h; split at h
  · split at h
    · obtain ⟨rfl⟩ := h; rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Queue allocate leaves `commitments` unchanged (edits only `queues`). -/
theorem queueAllocateK_commitments {k k' : RecordKernelState} {id : Nat} {owner : CellId} {capacity : Nat}
    (h : queueAllocateK k id owner capacity = some k') : k'.commitments = k.commitments := by
  unfold queueAllocateK at h; split at h
  · exact absurd h (by simp)
  · obtain ⟨rfl⟩ := h; rfl

/-- The raw escrow-create body leaves `commitments` unchanged (edits only `bal`/`escrows`). -/
theorem createEscrowRawAsset_commitments (k : RecordKernelState) (id creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) :
    (createEscrowRawAsset k id creator recipient asset amount).commitments = k.commitments := rfl

/-- The raw escrow-settle body leaves `commitments` unchanged (edits only `bal`/`escrows`). -/
theorem settleEscrowRawAsset_commitments (k : RecordKernelState) (id target : CellId)
    (asset : AssetId) (amount : ℤ) :
    (settleEscrowRawAsset k id target asset amount).commitments = k.commitments := rfl

/-- Bare queue enqueue leaves `commitments` unchanged (edits only `queues`). -/
theorem queueEnqueueK_commitments {k k' : RecordKernelState} {id m : Nat}
    (h : queueEnqueueK k id m = some k') : k'.commitments = k.commitments := by
  unfold queueEnqueueK at h; split at h
  · exact absurd h (by simp)
  · split at h
    · obtain ⟨rfl⟩ := h; rfl
    · exact absurd h (by simp)

/-- Bare queue dequeue leaves `commitments` unchanged (edits only `queues`). -/
theorem queueDequeueK_commitments {k k' : RecordKernelState} {id : Nat} {actor : CellId} {mh : Nat}
    (h : queueDequeueK k id actor = some (k', mh)) : k'.commitments = k.commitments := by
  unfold queueDequeueK at h; split at h
  · exact absurd h (by simp)
  · split at h
    · split at h
      · exact absurd h (by simp)
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨he, _⟩ := h; subst he; rfl
    · exact absurd h (by simp)

/-- Queue enqueue (with deposit) leaves `commitments` unchanged: the FIFO append frames it
(`queueEnqueueK_commitments`) and the deposit PARK is a raw escrow-create (`createEscrowRawAsset`,
commitments-neutral by rfl). -/
theorem queueEnqueueDepositK_commitments {k k' : RecordKernelState} {id m : Nat}
    {sender owner : CellId} {depId : Nat} {dAsset : AssetId} {deposit : ℤ}
    (h : queueEnqueueDepositK k id m sender owner depId dAsset deposit = some k') :
    k'.commitments = k.commitments := by
  unfold queueEnqueueDepositK at h
  cases hq : queueEnqueueK k id m with
  | none => rw [hq] at h; exact absurd h (by simp)
  | some k₁ =>
      rw [hq] at h; simp only at h
      by_cases hg : 0 ≤ deposit ∧ deposit ≤ k₁.bal sender dAsset ∧ sender ∈ k₁.accounts
          ∧ ¬ (∃ r ∈ k₁.escrows, r.id = depId)
      · rw [if_pos hg, Option.some.injEq] at h; subst h
        rw [show (createEscrowRawAssetQueue k₁ depId sender owner dAsset deposit id m).commitments = k₁.commitments from rfl]
        exact queueEnqueueK_commitments hq
      · rw [if_neg hg] at h; exact absurd h (by simp)

/-- Queue dequeue (with refund) leaves `commitments` unchanged: the FIFO pop frames it
(`queueDequeueK_commitments`) and the deposit REFUND is a raw escrow-settle (`settleEscrowRawAsset`,
commitments-neutral by rfl). -/
theorem queueDequeueRefundK_commitments {k : RecordKernelState} {id : Nat} {actor : CellId} {depId : Nat}
    {k' : RecordKernelState} {mh : Nat}
    (h : queueDequeueRefundK k id actor depId = some (k', mh)) : k'.commitments = k.commitments := by
  unfold queueDequeueRefundK at h
  cases hq : queueDequeueK k id actor with
  | none => rw [hq] at h; exact absurd h (by simp)
  | some p =>
      obtain ⟨k₁, m1⟩ := p
      rw [hq] at h; simp only at h
      have hq1 : k₁.commitments = k.commitments := queueDequeueK_commitments hq
      by_cases hbind : dequeueMsgBindB k₁ actor depId id m1
      · rw [if_pos hbind] at h
        cases hfind : findUnresolvedDeposit k₁ depId with
        | none => simp only [hfind] at h; exact absurd h (by simp)
        | some r =>
            simp only [hfind] at h
            by_cases ha : actor ∈ k₁.accounts
            · rw [if_pos ha, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨he, _⟩ := h; subst he
              rw [settleEscrowRawAsset_commitments]; exact hq1
            · rw [if_neg ha] at h; exact absurd h (by simp)
      · rw [if_neg hbind] at h; exact absurd h (by simp)

/-- Queue resize leaves `commitments` unchanged (edits only `queues`). -/
theorem queueResizeK_commitments {k k' : RecordKernelState} {id newCap : Nat}
    (h : queueResizeK k id newCap = some k') : k'.commitments = k.commitments := by
  unfold queueResizeK at h; split at h
  · exact absurd h (by simp)
  · split at h
    · obtain ⟨rfl⟩ := h; rfl
    · exact absurd h (by simp)

/-- WAVE 4: one atomic-batch sub-op leaves `commitments` unchanged (the deposit-park frames it via the
escrow-create / settle bodies; the FIFO move via the queue bodies). -/
theorem queueTxOpStepA_commitments {s s' : RecChainedState} {op : QueueTxOpA}
    (h : queueTxOpStepA s op = some s') : s'.kernel.commitments = s.kernel.commitments := by
  cases op with
  | enqueue id m actor cell depId dAsset deposit =>
      simp only [queueTxOpStepA, queueEnqueueChainA] at h; split at h
      · cases hk : queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => commit_subst h hk; exact queueEnqueueDepositK_commitments hk
      · exact absurd h (by simp)
  | dequeue id actor cell depId =>
      simp only [queueTxOpStepA, queueDequeueChainA] at h; split at h
      · cases hk : queueDequeueRefundK s.kernel id actor depId with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some p => obtain ⟨k', mh⟩ := p
                    commit_subst h hk; exact queueDequeueRefundK_commitments hk
      · exact absurd h (by simp)

/-- WAVE 4: the ALL-OR-NOTHING atomic batch leaves `commitments` unchanged (induction over the sub-ops). -/
theorem queueAtomicTxChainA_commitments {s s' : RecChainedState} {ops : List QueueTxOpA}
    (h : queueAtomicTxChainA s ops = some s') : s'.kernel.commitments = s.kernel.commitments := by
  induction ops generalizing s with
  | nil => simp only [queueAtomicTxChainA, Option.some.injEq] at h; subst h; rfl
  | cons op rest ih =>
      simp only [queueAtomicTxChainA] at h
      cases hop : queueTxOpStepA s op with
      | none => rw [hop] at h; exact absurd h (by simp)
      | some s1 => rw [hop] at h; rw [ih h, queueTxOpStepA_commitments hop]

/-- WAVE 4: the pipeline fan-out enqueue fold leaves `commitments` unchanged (each `queueEnqueueK` frames it). -/
theorem pipelineFanoutK_commitments {k k' : RecordKernelState} {actor : CellId} {m : Nat}
    {sinks : List CellId} {sids : List Nat}
    (h : pipelineFanoutK k actor m sinks sids = some k') : k'.commitments = k.commitments := by
  induction sinks generalizing k sids with
  | nil => cases sids <;> (simp only [pipelineFanoutK, Option.some.injEq] at h; subst h; rfl)
  | cons sink rest ih =>
      cases sids with
      | nil => simp only [pipelineFanoutK] at h; exact absurd h (by simp)
      | cons sid sids' =>
          simp only [pipelineFanoutK] at h; split at h
          · cases hq : queueEnqueueK k sid m with
            | none => rw [hq] at h; exact absurd h (by simp)
            | some k1 => rw [hq] at h; rw [ih h, queueEnqueueK_commitments hq]
          · exact absurd h (by simp)

/-- Swiss export leaves `commitments` unchanged (edits only `swiss`). -/
theorem swissExportK_commitments {k k' : RecordKernelState} {sw : Nat} {exporter target : CellId}
    {rights : List Auth} (h : swissExportK k sw exporter target rights = some k') :
    k'.commitments = k.commitments := by
  unfold swissExportK at h; split at h
  · exact absurd h (by simp)
  · split at h
    · obtain ⟨rfl⟩ := h; rfl
    · exact absurd h (by simp)

/-- Swiss enliven leaves `commitments` unchanged (edits only `swiss`). -/
theorem swissEnlivenK_commitments {k k' : RecordKernelState} {sw : Nat} {claimed : List Auth}
    (h : swissEnlivenK k sw claimed = some k') : k'.commitments = k.commitments := by
  unfold swissEnlivenK at h; split at h
  · exact absurd h (by simp)
  · split at h
    · obtain ⟨rfl⟩ := h; rfl
    · exact absurd h (by simp)

/-- Swiss handoff leaves `commitments` unchanged (edits only `swiss`). -/
theorem swissHandoffK_commitments {k k' : RecordKernelState} {sw certHash : Nat}
    (h : swissHandoffK k sw certHash = some k') : k'.commitments = k.commitments := by
  unfold swissHandoffK at h; split at h
  · exact absurd h (by simp)
  · obtain ⟨rfl⟩ := h; rfl

/-- Swiss drop leaves `commitments` unchanged (edits only `swiss`). -/
theorem swissDropK_commitments {k k' : RecordKernelState} {sw : Nat}
    (h : swissDropK k sw = some k') : k'.commitments = k.commitments := by
  unfold swissDropK at h; split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · obtain ⟨rfl⟩ := h; rfl
      · obtain ⟨rfl⟩ := h; rfl

/-! ## Step 1 — `execFullA_commitments_grow`: the PER-STEP registry frame (grow-only across one step). -/

mutual
/-- **`execFullA_commitments_grow` (PROVED) — THE per-step registry frame.** A committed real `execFullA`
step only GROWS the note-commitment set: `s.kernel.commitments ⊆ s'.kernel.commitments`. By case analysis
on the effect kind — `noteCreate` conses a fresh commitment (`noteCreateCommitment`, so the old set is a
sublist hence subset), and EVERY OTHER effect leaves `commitments` literally UNCHANGED (each via its
per-mutator frame above; the chained `stateStep`/`emit`/`attenuate`/`exercise`/`spawn`/`createCell`
wrappers edit `cell`/`caps`/`accounts`/`bal`/`escrows`/`queues`/`swiss`, never `commitments`); `exerciseA`
RECURSES (mutual `execInnerA_commitments_grow`). This is the META-FILL-C grow-only DUAL of the nullifier
registry, on the SHIPPED executor — the load-bearing one-step content of the commitment-persistence crown. -/
theorem execFullA_commitments_grow (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s') : s.kernel.commitments ⊆ s'.kernel.commitments := by
  -- A uniform "the kernel mutator left `commitments` fixed" closer for the framing arms:
  -- expose `s' = { kernel := k', … }`, rewrite `commitments` by the per-mutator frame, `subset_refl`.
  -- `exerciseA` RECURSES — its inner fold can only GROW the set (mutual `execInnerA_commitments_grow`).
  cases fa with
  | balanceA t a =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := recCexecAsset_factors t a (by simpa only [execFullA] using h)
      subst h'; exact subset_of_commitments_eq (recKExecAsset_commitments hk)
  | delegate del rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel del rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => commit_subst h hk; exact subset_of_commitments_eq (recKDelegate_commitments hk)
  | revoke holder t =>
      simp only [execFullA, recCRevoke, Option.some.injEq] at h; subst h
      exact subset_of_commitments_eq (recKRevokeTarget_commitments _ _ _)
  | mintA actor cell a amt =>
      simp only [execFullA, recCMintAsset] at h
      cases hk : recKMintAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => commit_subst h hk; exact subset_of_commitments_eq (recKMintAsset_commitments hk)
  | burnA actor cell a amt =>
      simp only [execFullA, recCBurnAsset] at h
      cases hk : recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => commit_subst h hk; exact subset_of_commitments_eq (recKBurnAsset_commitments hk)
  | setFieldA actor cell f v =>
      -- §SLOT-CAVEAT: `setFieldA` runs the caveat-gated write; peel it to the `stateStep` post-state.
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := stateStep_factors (stateStepGuarded_eq h); subst hs'
      exact subset_of_commitments_eq (writeField_commitments _ _ _ _)
  | emitEventA actor cell topic data =>
      -- §EMIT-LIVE: `emitStep` is now live-cell guarded — peel the `cell ∈ accounts` gate, then the
      -- log-only post-state frames `commitments` (kernel unchanged).
      simp only [execFullA] at h
      by_cases hlive : cell ∈ s.kernel.accounts
      · rw [if_pos hlive] at h
        simp only [emitStep, Option.some.injEq] at h; subst h
        exact List.Subset.refl _
      · rw [if_neg hlive] at h; exact absurd h (by simp)
  | incrementNonceA actor cell n =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      exact subset_of_commitments_eq (writeField_commitments _ _ _ _)
  | setPermissionsA actor cell p =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      exact subset_of_commitments_eq (writeField_commitments _ _ _ _)
  | setVKA actor cell vk =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      exact subset_of_commitments_eq (writeField_commitments _ _ _ _)
  | introduceA intro rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel intro rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => commit_subst h hk; exact subset_of_commitments_eq (recKDelegate_commitments hk)
  | delegateAttenA del rec t keep =>
      simp only [execFullA, recCDelegateAtten] at h
      cases hk : recKDelegateAtten s.kernel del rec t keep with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => commit_subst h hk; exact subset_of_commitments_eq (recKDelegateAtten_commitments hk)
  | attenuateA actor idx keep =>
      simp only [execFullA, attenuateStepA, Option.some.injEq] at h; subst h
      exact List.Subset.refl _
  | dropRefA holder t =>
      simp only [execFullA, recCRevoke, Option.some.injEq] at h; subst h
      exact subset_of_commitments_eq (recKRevokeTarget_commitments _ _ _)
  | revokeDelegationA holder t =>
      simp only [execFullA, recCRevoke, Option.some.injEq] at h; subst h
      exact subset_of_commitments_eq (recKRevokeTarget_commitments _ _ _)
  | validateHandoffA intro rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel intro rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => commit_subst h hk; exact subset_of_commitments_eq (recKDelegate_commitments hk)
  | exerciseA actor t inner =>
      simp only [execFullA] at h
      by_cases hf : innerFacetsAdmittedA s actor t inner = true
      · rw [if_pos hf] at h
        cases hg : exerciseStepA s actor t with
        | none => rw [hg] at h; exact absurd h (by simp)
        | some s1 =>
            rw [hg] at h
            obtain ⟨_, hs1⟩ := exerciseStepA_factors hg
            have hk : s1.kernel.commitments = s.kernel.commitments := by rw [hs1]
            exact hk ▸ execInnerA_commitments_grow s1 s' inner h
      · rw [if_neg hf] at h; exact absurd h (by simp)
  | createCellA actor newCell =>
      simp only [execFullA] at h
      obtain ⟨_, _, hs'⟩ := createCellChainA_factors h; subst hs'
      exact subset_of_commitments_eq (createCellIntoAsset_commitments _ _)
  | createCellFromFactoryA actor newCell vk =>
      -- §MA-factory: the factory install leaves `commitments` UNTOUCHED (frame lemma).
      simp only [execFullA] at h
      exact subset_of_commitments_eq (createCellFromFactoryChainA_sideTables h).1
  | spawnA actor child target =>
      simp only [execFullA] at h
      -- §SPAWN-FACTOR: new 4-tuple shape — `⟨s1, ⟨held-edge, target∈accounts⟩, createCellChainA=…, s'=…⟩`.
      obtain ⟨s1, _, hc, hs'⟩ := spawnChainA_factors h; subst hs'
      obtain ⟨_, _, hc'⟩ := createCellChainA_factors hc; subst hc'
      -- post = `{ createCell-state with caps/delegate/delegations := … }`: every edit frames `commitments`.
      exact List.Subset.refl _
  | bridgeMintA actor cell a value =>
      simp only [execFullA, recCMintAsset] at h
      cases hk : recKMintAsset s.kernel actor cell a value with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => commit_subst h hk; exact subset_of_commitments_eq (recKMintAsset_commitments hk)
  | createEscrowA id actor creator recipient asset amount =>
      simp only [execFullA, createEscrowChainA] at h
      cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => commit_subst h hk; exact subset_of_commitments_eq (createEscrowKAsset_commitments hk)
  | releaseEscrowA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := releaseEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'; exact subset_of_commitments_eq (releaseEscrowKAsset_commitments hk)
  | refundEscrowA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := refundEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'; exact subset_of_commitments_eq (refundEscrowKAsset_commitments hk)
  | createObligationA id actor obligor beneficiary asset stake =>
      simp only [execFullA, createEscrowChainA] at h
      cases hk : createEscrowKAsset s.kernel id actor obligor beneficiary asset stake with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => commit_subst h hk; exact subset_of_commitments_eq (createEscrowKAsset_commitments hk)
  -- fulfill/slash route to refund/release (escrow SETTLE) — `commitments` literally unchanged.
  | fulfillObligationA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := refundEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'; exact subset_of_commitments_eq (refundEscrowKAsset_commitments hk)
  | slashObligationA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := releaseEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'; exact subset_of_commitments_eq (releaseEscrowKAsset_commitments hk)
  | noteSpendA nf actor =>
      simp only [execFullA, noteSpendChainA] at h
      cases hk : noteSpendNullifier s.kernel nf with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => commit_subst h hk; exact subset_of_commitments_eq (noteSpendNullifier_commitments hk)
  | noteCreateA cm actor =>
      -- THE grow arm: noteCreate conses `cm` onto `commitments` (`noteCreateCommitment`).
      simp only [execFullA, noteCreateChainA, Option.some.injEq] at h; subst h
      show s.kernel.commitments ⊆ (noteCreateCommitment s.kernel cm).commitments
      unfold noteCreateCommitment
      exact List.subset_cons_self cm s.kernel.commitments
  | createCommittedEscrowA id actor creator recipient asset amount hidingProof =>
      simp only [execFullA, createCommittedEscrowChainA, createEscrowChainA] at h; split at h
      · cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => commit_subst h hk; exact subset_of_commitments_eq (createEscrowKAsset_commitments hk)
      · exact absurd h (by simp)
  | releaseCommittedEscrowA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := releaseEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'; exact subset_of_commitments_eq (releaseEscrowKAsset_commitments hk)
  | refundCommittedEscrowA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := refundEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'; exact subset_of_commitments_eq (refundEscrowKAsset_commitments hk)
  | bridgeLockA id actor originator destination asset amount =>
      simp only [execFullA, bridgeLockChainA] at h
      cases hk : bridgeLockKAsset s.kernel id actor originator destination asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' => commit_subst h hk; exact subset_of_commitments_eq (bridgeLockKAsset_commitments hk)
  | bridgeFinalizeA id actor asset amount =>
      simp only [execFullA, bridgeFinalizeChainA] at h; split at h
      · cases hk : bridgeFinalizeKAsset s.kernel id asset amount with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => commit_subst h hk
                     exact subset_of_commitments_eq (bridgeFinalizeKAsset_commitments hk)
      · exact absurd h (by simp)
  | bridgeCancelA id actor =>
      simp only [execFullA, bridgeCancelChainA] at h; split at h
      · cases hk : bridgeCancelKAsset s.kernel id with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => commit_subst h hk
                     exact subset_of_commitments_eq (bridgeCancelKAsset_commitments hk)
      · exact absurd h (by simp)
  -- §seal (Wave-3 DE-SHADOW) — seal/unseal/createSealPair edit `caps`/`sealedBoxes`, never `commitments`
  -- (frame: `rfl`); makeSovereign/refusal/receiptArchive write the cell record.
  | sealA pid actor payload =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := sealChainA_factors h; subst hs'
      exact subset_of_commitments_eq rfl
  | unsealA pid actor recipient =>
      simp only [execFullA] at h; obtain ⟨_, _, _, hs'⟩ := unsealChainA_factors h; subst hs'
      exact subset_of_commitments_eq rfl
  | createSealPairA pid actor sealerHolder x =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := createSealPairChainA_factors h; subst hs'
      exact subset_of_commitments_eq rfl
  | makeSovereignA actor cell =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := makeSovereignStep_factors h; subst hs'
      exact subset_of_commitments_eq (makeSovereignKernel_commitments _ _)
  | refusalA actor cell =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      exact subset_of_commitments_eq (writeField_commitments _ _ _ _)
  | receiptArchiveA actor cell =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      exact subset_of_commitments_eq (writeField_commitments _ _ _ _)
  | queueAllocateA id actor cell cap =>
      simp only [execFullA, queueAllocateChainA] at h; split at h
      · cases hk : queueAllocateK s.kernel id actor cap with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => commit_subst h hk; exact subset_of_commitments_eq (queueAllocateK_commitments hk)
      · exact absurd h (by simp)
  | queueEnqueueA id m actor cell depId dAsset deposit =>
      simp only [execFullA, queueEnqueueChainA] at h; split at h
      · cases hk : queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => commit_subst h hk; exact subset_of_commitments_eq (queueEnqueueDepositK_commitments hk)
      · exact absurd h (by simp)
  | queueDequeueA id actor cell depId =>
      simp only [execFullA, queueDequeueChainA] at h; split at h
      · cases hk : queueDequeueRefundK s.kernel id actor depId with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some p => obtain ⟨k', mh⟩ := p
                    commit_subst h hk; exact subset_of_commitments_eq (queueDequeueRefundK_commitments hk)
      · exact absurd h (by simp)
  | queueResizeA id newCap actor cell =>
      simp only [execFullA, queueResizeChainA] at h; split at h
      · cases hk : queueResizeK s.kernel id newCap with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => commit_subst h hk; exact subset_of_commitments_eq (queueResizeK_commitments hk)
      · exact absurd h (by simp)
  -- §MA-queue-batch (WAVE 4): the atomic batch / pipeline step edit only `queues`/`escrows`/`bal` (the
  -- deposit park, the FIFO move), never `commitments` (the witness lemmas + frame helpers); pipelinedSend
  -- edits NOTHING.
  | queueAtomicTxA actor ops =>
      simp only [execFullA] at h
      obtain ⟨s1, hf, _, hk⟩ := queueAtomicTxA_atomic_witness h
      rw [show s'.kernel.commitments = s1.kernel.commitments from by rw [hk]]
      exact subset_of_commitments_eq (queueAtomicTxChainA_commitments hf)
  | queuePipelineStepA srcId owner sinkCells sinkIds =>
      simp only [execFullA] at h
      obtain ⟨k1, mh, hd, hfo⟩ := queuePipelineStepA_routing_witness h
      exact subset_of_commitments_eq
        ((pipelineFanoutK_commitments hfo).trans (queueDequeueK_commitments hd))
  | pipelinedSendA actor =>
      simp only [execFullA, Option.some.injEq] at h; subst h; exact subset_of_commitments_eq rfl
  | exportSturdyRefA sw actor exporter target rights =>
      simp only [execFullA, swissExportChainA] at h; split at h
      · cases hk : swissExportK s.kernel sw exporter target rights with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => commit_subst h hk; exact subset_of_commitments_eq (swissExportK_commitments hk)
      · exact absurd h (by simp)
  | enlivenRefA sw actor exporter claimed =>
      simp only [execFullA, swissEnlivenChainA] at h; split at h
      · cases hk : swissEnlivenK s.kernel sw claimed with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => commit_subst h hk; exact subset_of_commitments_eq (swissEnlivenK_commitments hk)
      · exact absurd h (by simp)
  | swissHandoffA sw certHash introducer exporter =>
      simp only [execFullA, swissHandoffChainA] at h; split at h
      · cases hk : swissHandoffK s.kernel sw certHash with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => commit_subst h hk; exact subset_of_commitments_eq (swissHandoffK_commitments hk)
      · exact absurd h (by simp)
  | swissDropA sw actor exporter =>
      simp only [execFullA, swissDropChainA] at h; split at h
      · cases hk : swissDropK s.kernel sw with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => commit_subst h hk; exact subset_of_commitments_eq (swissDropK_commitments hk)
      · exact absurd h (by simp)
  -- §lifecycle (Wave-3) — seal/unseal/destroy edit `lifecycle`/`deathCert`; refresh edits `delegations`
  -- — none touch `commitments` (frame: `rfl`).
  | cellSealA actor cell =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := cellSealChainA_factors h; subst hs'
      exact subset_of_commitments_eq rfl
  | cellUnsealA actor cell =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := cellUnsealChainA_factors h; subst hs'
      exact subset_of_commitments_eq rfl
  | cellDestroyA actor cell ch =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := cellDestroyChainA_factors h; subst hs'
      exact subset_of_commitments_eq rfl
  | refreshDelegationA actor child =>
      simp only [execFullA] at h; obtain ⟨_, hs'⟩ := refreshDelegationChainA_factors h; subst hs'
      exact subset_of_commitments_eq rfl

/-- **`execInnerA_commitments_grow`** — the inner-effect fold an `exerciseA` recurses through never
shrinks the commitment set. Mutual with `execFullA_commitments_grow`; chains `List.Subset.trans`. -/
theorem execInnerA_commitments_grow (s s' : RecChainedState) (inner : List FullActionA)
    (h : execInnerA s inner = some s') : s.kernel.commitments ⊆ s'.kernel.commitments := by
  cases inner with
  | nil => simp only [execInnerA, Option.some.injEq] at h; subst h; exact List.Subset.refl _
  | cons a rest =>
      simp only [execInnerA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          exact List.Subset.trans
            (execFullA_commitments_grow s s1 a ha)
            (execInnerA_commitments_grow s1 s' rest h)
end

/-! ## Step 2 — the turn/forest lift: a committed full-FOREST only grows `commitments`. -/

/-- **`execFullTurnA_commitments_grow` (PROVED).** A committed per-asset full-TURN (a list of
`FullActionA`) only grows `commitments`: `s.kernel.commitments ⊆ s'.kernel.commitments`. By induction on
the action list — each committed `execFullA` head step grows the set (`execFullA_commitments_grow`); the
empty turn is `subset_refl`; the inductive step chains by `List.Subset.trans`. -/
theorem execFullTurnA_commitments_grow :
    ∀ (s s' : RecChainedState) (tt : List FullActionA),
      execFullTurnA s tt = some s' → s.kernel.commitments ⊆ s'.kernel.commitments
  | s, s', [], h => by
      simp only [execFullTurnA, Option.some.injEq] at h; subst h; exact List.Subset.refl _
  | s, s', a :: rest, h => by
      simp only [execFullTurnA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          exact List.Subset.trans (execFullA_commitments_grow s s1 a ha)
            (execFullTurnA_commitments_grow s1 s' rest h)

/-- **`execFullForestA_commitments_grow` (PROVED).** A committed full-FOREST only grows `commitments`. Read
straight through the pre-order bridge `execFullForestA_eq_execFullTurnA` into `execFullTurnA_commitments_grow`.
This is the forest-level META-FILL-C grow-only registry fact — the one-step obligation of the crown. -/
theorem execFullForestA_commitments_grow (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') : s.kernel.commitments ⊆ s'.kernel.commitments := by
  rw [execFullForestA_eq_execFullTurnA] at h
  exact execFullTurnA_commitments_grow s s' (lowerForestA f) h

/-! ## Step 3 — THE CROWN: a published commitment persists along the whole unbounded trajectory. -/

/-- **`livingCellA_commitments_persist` (PROVED) — THE COMMITMENT-PERSISTENCE CROWN.** Fix any baseline set
`com0` of published note commitments contained in the initial state's commitment set. Then `com0` is
contained in `commitments` at EVERY index of the unbounded adversarial trajectory `trajA s sched`, under
EVERY schedule: a published commitment is NEVER retracted, dropped, or rewritten. This is the
anti-equivocation / auditability invariant of the off-ledger commitment tree — the **grow-only DUAL** of the
nullifier set's no-double-spend (`META-FILL C`), now COINDUCTIVE on the SHIPPED executor.

It is carried by `livingCellA_carries` with `Good := (com0 ⊆ ·.kernel.commitments)`, a genuinely
NON-conservation safety. Its one-step obligation is discharged from the registry frame on a COMMIT
(`execFullForestA_commitments_grow` grows the set, chained by `List.Subset.trans`) and the **stay-put
self-loop** on a REJECT (`cellNextA` leaves the state — and thus `commitments` — UNCHANGED). With
`livingCellA_logMono` (audit-log append-only) this completes the audit/anti-double-spend pair of the
private-note layer as temporal νF invariants on the real machine. -/
theorem livingCellA_commitments_persist (com0 : List Nat) (s : RecChainedState) (sched : SchedA)
    (hinit : com0 ⊆ s.kernel.commitments) :
    ∀ n, com0 ⊆ (trajA s sched n).kernel.commitments :=
  livingCellA_carries (fun s' => com0 ⊆ s'.kernel.commitments)
    (fun a cf h => by
      -- One-step preservation. `cellNextA a cf = (execFullForestA a cf.1).getD a`: on a COMMIT the forest
      -- registry-frame grows `commitments` (chain by `Subset.trans`); on a REJECT the state is the
      -- UNCHANGED `a`, so the `⊆` is preserved trivially.
      show com0 ⊆ (cellNextA a cf).kernel.commitments
      unfold cellNextA
      cases hc : execFullForestA a cf.1 with
      | some a' => simp only [Option.getD_some]
                   exact List.Subset.trans h (execFullForestA_commitments_grow a a' cf.1 hc)
      | none    => simp only [Option.getD_none]; exact h)
    s hinit sched

/-! ## It runs (`#eval`) — a real `noteCreate` GROWS the commitment set (non-vacuity).

The persistence invariant would be vacuous if no turn ever grew `commitments`. A `noteCreateA cm`
forest commits and conses `cm` onto the set: the length goes `0 → 1` and `cm` is present afterward. So
`livingCellA_commitments_persist` bounds a strictly-growing quantity (a baseline already-present
commitment stays present even as new ones are added), and the crown is exercised by a property that
genuinely moves. -/

/-- A real single-`noteCreateA` forest: actor 9 publishes commitment `42`. It commits (a fresh
commitment cannot conflict) and grows `commitments` by one. -/
def noteCreateFA : FullForestA := ⟨.noteCreateA 42 9, []⟩

#guard ((execFullForestA fma0 noteCreateFA).map (fun s' => s'.kernel.commitments)) == some [42]  --  some [42] (grew from [])
#guard (fma0.kernel.commitments.length) == 0  --  0   (BEFORE — strictly less)
#guard ((execFullForestA fma0 noteCreateFA).map (fun s' => decide (42 ∈ s'.kernel.commitments))) == some true  --  some true
-- The carried predicate at a published baseline `[42]` holds AFTER the create (and would FAIL on `∅`-state):
#guard ((execFullForestA fma0 noteCreateFA).map (fun s' => decide (([42] : List Nat) ⊆ s'.kernel.commitments))) == some true  --  some true

/-! ## Axiom hygiene — the persistence crown + the registry frame pinned to the kernel triple (NO `sorryAx`). -/

#assert_axioms execFullA_commitments_grow
#assert_axioms execFullTurnA_commitments_grow
#assert_axioms execFullForestA_commitments_grow
#assert_axioms livingCellA_commitments_persist

end Dregg2.Exec
