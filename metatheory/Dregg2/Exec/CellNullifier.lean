/-
# Dregg2.Exec.CellNullifier — the nullifier set is grow-only FOREVER (no double-spend).

The kernel's spent-note nullifier set (`s.kernel.nullifiers`) is grow-only: relative to any consumed
baseline `nul0`, every nullifier in `nul0` stays consumed at every index of the unbounded trajectory,
against every adversarial schedule. Combined with the per-step double-spend gate (`noteSpendNullifier`
rejects a repeat, `note_no_double_spend`), this is the formal "once spent, forever spent ⇒ no
double-spend" guarantee.

* **`execFullA_nullifiers_grow`** — the per-effect registry frame: a committed `FullActionA` never
  shrinks the nullifier set. `noteSpendA` grows it (`nf :: …`); the other 45 effects leave it unchanged.
* **`execFullTurnA_nullifiers_grow` / `execFullForestA_nullifiers_grow`** — turn- and forest-level lifts,
  by induction on the action list chained by `List.Subset.trans`.
* **`livingCellA_no_double_spend`** — `Good s := nul0 ⊆ s.kernel.nullifiers` carried by
  `livingCellA_carries`. A non-conservation safety (reads the registry, not the per-asset measure).
* **`livingCellA_spent_note_never_respent`** — if `nf` is spent in the initial state, it remains spent
  at every index of every trajectory, so a fresh `noteSpendNullifier … nf` always fails-closed.
-/
import Dregg2.Exec.CellCarry

namespace Dregg2.Exec

open Dregg2.Boundary
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Authority
open Dregg2.Exec.EffectsState (stateStep stateStep_factors stateStepGuarded_eq)
open Dregg2.Tactics

/-! ## Step 0 — nullifier-frame lemmas for the DEEPLY-NESTED kernel ops (queue-deposit + swiss).

Five kernel ops nest a `match … | some k₁ => if … then some (rawOp k₁ …)`-style body too deep to
`unfold`+`split` cleanly inline in the dispatch. Each touches ONLY `queues`/`swiss`/`bal`/`escrows`
(never `nullifiers`), so a committed step leaves `nullifiers` literally unchanged. We hoist those five
to named `private` frame lemmas (proven by the same nested `split` + `rfl`-projection) and reference
them from the dispatch, keeping every arm uniform. -/

/-- `queueEnqueueDepositK` commits via `queueEnqueueK` (queues-only) then `createEscrowRawAsset`
(bal/escrows-only) — `nullifiers` untouched. -/
private theorem queueEnqueueK_nullifiers (k : RecordKernelState) (id m : Nat) (k₁ : RecordKernelState)
    (hq : queueEnqueueK k id m = some k₁) : k₁.nullifiers = k.nullifiers := by
  unfold queueEnqueueK at hq; split at hq
  · exact absurd hq (by simp)
  · split at hq
    · injection hq with hq; subst hq; rfl
    · exact absurd hq (by simp)

private theorem queueEnqueueDepositK_nullifiers (k : RecordKernelState) (id m : Nat)
    (sender owner : CellId) (depId : Nat) (dAsset : AssetId) (deposit : ℤ) (k' : RecordKernelState)
    (h : queueEnqueueDepositK k id m sender owner depId dAsset deposit = some k') :
    k'.nullifiers = k.nullifiers := by
  -- queueEnqueueDepositK = `match queueEnqueueK | none => none | some k₁ => if … then some (rawk₁) else none`.
  unfold queueEnqueueDepositK at h
  split at h
  · exact absurd h (by simp)                                 -- queueEnqueueK = none
  · rename_i k₁ hq                                            -- queueEnqueueK = some k₁
    split at h
    · obtain ⟨rfl⟩ := h                               -- deposit gate true ⇒ k' = createEscrowRawAsset k₁ …
      show k₁.nullifiers = k.nullifiers
      exact queueEnqueueK_nullifiers k id m k₁ hq
    · exact absurd h (by simp)                               -- deposit gate false

/-- `queueDequeueRefundK` commits via `queueDequeueK` (queues-only) then `settleEscrowRawAsset`
(bal/escrows-only) — `nullifiers` untouched. -/
private theorem queueDequeueK_nullifiers (k : RecordKernelState) (id : Nat) (actor : CellId)
    (k₁ : RecordKernelState) (mh : Nat) (hq : queueDequeueK k id actor = some (k₁, mh)) :
    k₁.nullifiers = k.nullifiers := by
  unfold queueDequeueK at hq; split at hq
  · exact absurd hq (by simp)
  · split at hq
    · split at hq
      · exact absurd hq (by simp)
      · option_inj at hq; obtain ⟨hq, _⟩ := hq; subst hq; rfl
    · exact absurd hq (by simp)

private theorem queueDequeueRefundK_nullifiers (k : RecordKernelState) (id : Nat) (actor : CellId)
    (depId : Nat) (k' : RecordKernelState) (mh : Nat)
    (h : queueDequeueRefundK k id actor depId = some (k', mh)) :
    k'.nullifiers = k.nullifiers := by
  -- queueDequeueRefundK = `match queueDequeueK | none => none | some (k₁,_) =>
  --   match find? | some r => if actor∈accounts then some (settleEscrowRawAsset k₁ …, mh) else none | none => none`.
  unfold queueDequeueRefundK at h
  cases hq : queueDequeueK k id actor with
  | none => rw [hq] at h; exact absurd h (by simp)
  | some kp =>
      obtain ⟨k₁, mh₁⟩ := kp
      rw [hq] at h; simp only [] at h
      by_cases hbind : dequeueMsgBindB k₁ actor depId id mh₁
      · rw [if_pos hbind] at h
        cases hfind : findUnresolvedDeposit k₁ depId with
        | none => simp only [hfind] at h; exact absurd h (by simp)
        | some r =>
            simp only [hfind] at h
            by_cases ha : actor ∈ k₁.accounts
            · rw [if_pos ha, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨he, _⟩ := h; subst he
              exact queueDequeueK_nullifiers k id actor k₁ mh₁ hq
            · rw [if_neg ha] at h; exact absurd h (by simp)
      · rw [if_neg hbind] at h; exact absurd h (by simp)

/-- WAVE 4: one atomic-batch sub-op leaves `nullifiers` untouched (the deposit-park / FIFO frame). -/
private theorem queueTxOpStepA_nullifiers (s s' : RecChainedState) (op : QueueTxOpA)
    (h : queueTxOpStepA s op = some s') : s'.kernel.nullifiers = s.kernel.nullifiers := by
  cases op with
  | enqueue id m actor cell depId dAsset deposit =>
      simp only [queueTxOpStepA, queueEnqueueChainA] at h; split at h
      · cases hk : queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => commit_subst h hk
                     exact queueEnqueueDepositK_nullifiers s.kernel id m actor cell depId dAsset deposit k' hk
      · exact absurd h (by simp)
  | dequeue id actor cell depId =>
      simp only [queueTxOpStepA, queueDequeueChainA] at h; split at h
      · cases hk : queueDequeueRefundK s.kernel id actor depId with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some kp => obtain ⟨k', mhd⟩ := kp
                     commit_subst h hk
                     exact queueDequeueRefundK_nullifiers s.kernel id actor depId k' mhd hk
      · exact absurd h (by simp)

/-- WAVE 4: the ALL-OR-NOTHING atomic batch leaves `nullifiers` untouched (induction over the sub-ops). -/
private theorem queueAtomicTxChainA_nullifiers (s s' : RecChainedState) (ops : List QueueTxOpA)
    (h : queueAtomicTxChainA s ops = some s') : s'.kernel.nullifiers = s.kernel.nullifiers := by
  induction ops generalizing s with
  | nil => simp only [queueAtomicTxChainA, Option.some.injEq] at h; subst h; rfl
  | cons op rest ih =>
      simp only [queueAtomicTxChainA] at h
      cases hop : queueTxOpStepA s op with
      | none => rw [hop] at h; exact absurd h (by simp)
      | some s1 => simp only [hop] at h; rw [ih s1 h, queueTxOpStepA_nullifiers _ _ _ hop]

/-- WAVE 4: the pipeline fan-out enqueue fold leaves `nullifiers` untouched (each `queueEnqueueK` frames it). -/
private theorem pipelineFanoutK_nullifiers (k k' : RecordKernelState) (actor : CellId) (m : Nat)
    (sinks : List CellId) (sids : List Nat)
    (h : pipelineFanoutK k actor m sinks sids = some k') : k'.nullifiers = k.nullifiers := by
  induction sinks generalizing k sids with
  | nil => cases sids <;> (simp only [pipelineFanoutK, Option.some.injEq] at h; subst h; rfl)
  | cons sink rest ih =>
      cases sids with
      | nil => simp only [pipelineFanoutK] at h; exact absurd h (by simp)
      | cons sid sids' =>
          simp only [pipelineFanoutK] at h; split at h
          · cases hq : queueEnqueueK k sid m with
            | none => rw [hq] at h; exact absurd h (by simp)
            | some k1 => simp only [hq] at h; rw [ih k1 sids' h, queueEnqueueK_nullifiers k sid m k1 hq]
          · exact absurd h (by simp)

/-- `swissEnlivenK` commits to `{ k with swiss := … }` — `nullifiers` untouched. -/
private theorem swissEnlivenK_nullifiers (k : RecordKernelState) (sw : Nat) (claimed : List Auth)
    (k' : RecordKernelState) (h : swissEnlivenK k sw claimed = some k') :
    k'.nullifiers = k.nullifiers := by
  unfold swissEnlivenK at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · injection h with h; subst h; rfl
    · exact absurd h (by simp)

/-- `swissHandoffK` commits to `{ k with swiss := … }` — `nullifiers` untouched. -/
private theorem swissHandoffK_nullifiers (k : RecordKernelState) (sw certHash : Nat)
    (k' : RecordKernelState) (h : swissHandoffK k sw certHash = some k') :
    k'.nullifiers = k.nullifiers := by
  unfold swissHandoffK at h
  split at h
  · exact absurd h (by simp)
  · injection h with h; subst h; rfl

/-- `swissDropK` commits to `{ k with swiss := … }` (remove or decrement) — `nullifiers` untouched. -/
private theorem swissDropK_nullifiers (k : RecordKernelState) (sw : Nat)
    (k' : RecordKernelState) (h : swissDropK k sw = some k') :
    k'.nullifiers = k.nullifiers := by
  unfold swissDropK at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · injection h with h; subst h; rfl
      · injection h with h; subst h; rfl

/-! ## Step 1 — `execFullA_nullifiers_grow`: the per-effect REGISTRY FRAME (the 46-arm dispatch).

Mirrors `execFullA_ledger_per_asset`'s `cases fa with` walk. For the spent-set the bookkeeping is
SIMPLER than for the per-asset measure: only ONE arm (`noteSpendA`) moves `nullifiers` at all (it
GROWS it by one — `List.subset_cons_self`), and EVERY other arm leaves it literally unchanged
(`List.Subset.refl`), because every kernel transform is a record-update of a field OTHER than
`nullifiers`, so the `.nullifiers` projection reduces by `rfl`. -/

mutual
/-- **`execFullA_nullifiers_grow`** — a committed `FullActionA` never shrinks the spent-note
nullifier set: `s.kernel.nullifiers ⊆ s'.kernel.nullifiers`. `noteSpendA` conses a fresh nullifier;
the other effects touch other kernel fields only (frame: `nullifiers` literally unchanged); `exerciseA`
RECURSES — its inner fold can only GROW the set further (mutual `execInnerA_nullifiers_grow`). -/
theorem execFullA_nullifiers_grow (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s') : s.kernel.nullifiers ⊆ s'.kernel.nullifiers := by
  cases fa with
  -- §catalog / supply / authority — the chained `match kernelOp | some k' => some {kernel:=k',…}`
  -- wrappers. Read back the committed `k'`, then `k'.nullifiers = s.kernel.nullifiers` (the kernel op
  -- updates a NON-`nullifiers` field, so the projection is `rfl`).
  | balanceA t a =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := recCexecAsset_factors t a (by simpa only [execFullA] using h)
      subst h'
      show s.kernel.nullifiers ⊆ k'.nullifiers
      have hn : k'.nullifiers = s.kernel.nullifiers := by
        unfold recKExecAsset at hk; split at hk
        · injection hk with hk; subst hk; rfl
        · exact absurd hk (by simp)
      exact hn ▸ List.Subset.refl _
  | delegate del rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel del rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          show s.kernel.nullifiers ⊆ k'.nullifiers
          have hn : k'.nullifiers = s.kernel.nullifiers := by
            unfold recKDelegate at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          exact hn ▸ List.Subset.refl _
  | revoke holder t =>
      simp only [execFullA, recCRevoke] at h
      obtain ⟨rfl⟩ := h; exact List.Subset.refl _
  | mintA actor cell a amt =>
      simp only [execFullA, recCMintAsset] at h
      cases hk : recKMintAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          show s.kernel.nullifiers ⊆ k'.nullifiers
          have hn : k'.nullifiers = s.kernel.nullifiers := by
            unfold recKMintAsset at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          exact hn ▸ List.Subset.refl _
  | burnA actor cell a amt =>
      simp only [execFullA, recCBurnAsset] at h
      cases hk : recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          show s.kernel.nullifiers ⊆ k'.nullifiers
          have hn : k'.nullifiers = s.kernel.nullifiers := by
            unfold recKBurnAsset at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          exact hn ▸ List.Subset.refl _
  -- §pure-state — `stateStep` (field write); factors through `stateStep_factors` (kernel = writeField,
  -- a `cell`-only update). All nine share the proof.
  | setFieldA actor cell f v =>
      -- §SLOT-CAVEAT: peel the caveat gate to the `stateStep` post-state (a `cell`-only write).
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors (stateStepGuarded_eq h); subst hs'; exact List.Subset.refl _
  | emitEventA actor cell topic data =>
      -- §LIVE-CELL: the emit append is now gated on `cell ∈ accounts`; peel the gate, then the
      -- committed `emitStep` post-state shares `s.kernel` (frame: `nullifiers` literally unchanged).
      simp only [execFullA] at h
      split at h
      · simp only [emitStep] at h
        obtain ⟨rfl⟩ := h; exact List.Subset.refl _
      · exact absurd h (by simp)
  | incrementNonceA actor cell n =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; exact List.Subset.refl _
  | setPermissionsA actor cell p =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; exact List.Subset.refl _
  | setVKA actor cell vk =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; exact List.Subset.refl _
  -- §authority — introduce/validateHandoff route to recKDelegate; delegateAtten to recKDelegateAtten;
  -- attenuate is always-commit (`some (attenuateStepA …)`, a caps-only update); dropRef/revokeDelegation
  -- to recCRevoke; exercise factors (kernel UNCHANGED).
  | introduceA intro rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel intro rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          show s.kernel.nullifiers ⊆ k'.nullifiers
          have hn : k'.nullifiers = s.kernel.nullifiers := by
            unfold recKDelegate at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          exact hn ▸ List.Subset.refl _
  | delegateAttenA del rec t keep =>
      simp only [execFullA, recCDelegateAtten] at h
      cases hk : recKDelegateAtten s.kernel del rec t keep with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          show s.kernel.nullifiers ⊆ k'.nullifiers
          have hn : k'.nullifiers = s.kernel.nullifiers := by
            unfold recKDelegateAtten at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          exact hn ▸ List.Subset.refl _
  | attenuateA actor idx keep =>
      simp only [execFullA, attenuateStepA] at h
      obtain ⟨rfl⟩ := h; exact List.Subset.refl _
  | dropRefA holder t =>
      simp only [execFullA, recCRevoke] at h
      obtain ⟨rfl⟩ := h; exact List.Subset.refl _
  | revokeDelegationA holder t =>
      simp only [execFullA, recCRevoke] at h
      obtain ⟨rfl⟩ := h; exact List.Subset.refl _
  | validateHandoffA intro rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel intro rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          show s.kernel.nullifiers ⊆ k'.nullifiers
          have hn : k'.nullifiers = s.kernel.nullifiers := by
            unfold recKDelegate at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          exact hn ▸ List.Subset.refl _
  | exerciseA actor t inner =>
      simp only [execFullA] at h
      by_cases hf : innerFacetsAdmittedA s actor t inner = true
      · rw [if_pos hf] at h
        cases hg : exerciseStepA s actor t with
        | none => rw [hg] at h; exact absurd h (by simp)
        | some s1 =>
            rw [hg] at h
            -- the hold-gate leaves the kernel (hence `nullifiers`) UNCHANGED; the inner fold only GROWS it.
            obtain ⟨_, hs1⟩ := exerciseStepA_factors hg
            have hk : s1.kernel.nullifiers = s.kernel.nullifiers := by rw [hs1]
            exact hk ▸ execInnerA_nullifiers_grow s1 s' inner h
      · rw [if_neg hf] at h; exact absurd h (by simp)
  -- §supply-growth — createCell/spawn factor through their gates (kernel = createCellIntoAsset / + a
  -- caps grant — neither touches `nullifiers`); bridgeMint reuses recCMintAsset.
  | createCellA actor newCell =>
      obtain ⟨_, _, hs'⟩ := createCellChainA_factors (by simpa only [execFullA] using h)
      subst hs'; exact List.Subset.refl _
  | createCellFromFactoryA actor newCell vk =>
      -- §MA-factory: the factory install edits `cell`/`slotCaveats`/`accounts`/`bal`, never `nullifiers`.
      obtain ⟨_, s1, _, _, hc, hs'⟩ :=
        createCellFromFactoryChainA_factors (by simpa only [execFullA] using h)
      obtain ⟨_, _, hs1⟩ := createCellChainA_factors hc
      subst hs' hs1; exact List.Subset.refl _
  | spawnA actor child target =>
      -- §SPAWN: the new `spawnChainA_factors` exposes the live-held-edge gate as a SEPARATE conjunct
      -- (`_hg`), then the committed `createCellChainA` (into `s1`) and the held-cap copy post-state.
      -- The cap/delegation edit is `nullifiers`-orthogonal, and `createCellChainA` writes a fresh cell
      -- (frame: `nullifiers` literally unchanged).
      obtain ⟨s1, _hg, hc, hs'⟩ := spawnChainA_factors (by simpa only [execFullA] using h)
      subst hs'
      obtain ⟨_, _, hc'⟩ := createCellChainA_factors hc; subst hc'; exact List.Subset.refl _
  | bridgeMintA actor cell a value =>
      simp only [execFullA, recCMintAsset] at h
      cases hk : recKMintAsset s.kernel actor cell a value with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          show s.kernel.nullifiers ⊆ k'.nullifiers
          have hn : k'.nullifiers = s.kernel.nullifiers := by
            unfold recKMintAsset at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          exact hn ▸ List.Subset.refl _
  -- §escrow / obligation / committed — the chained holding-store steps (kernel updates bal/escrows,
  -- never `nullifiers`). create/obligation/committed-create share createEscrowKAsset; release/refund
  -- share releaseEscrowKAsset/refundEscrowKAsset.
  | createEscrowA id actor creator recipient asset amount =>
      simp only [execFullA, createEscrowChainA] at h
      cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          show s.kernel.nullifiers ⊆ k'.nullifiers
          have hn : k'.nullifiers = s.kernel.nullifiers := by
            unfold createEscrowKAsset createEscrowRawAsset at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          exact hn ▸ List.Subset.refl _
  | releaseEscrowA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := releaseEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'
      show s.kernel.nullifiers ⊆ k'.nullifiers
      have hn : k'.nullifiers = s.kernel.nullifiers := by
        unfold releaseEscrowKAsset settleEscrowRawAsset at hk
        split at hk
        · split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
        · exact absurd hk (by simp)
      exact hn ▸ List.Subset.refl _
  | refundEscrowA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := refundEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'
      show s.kernel.nullifiers ⊆ k'.nullifiers
      have hn : k'.nullifiers = s.kernel.nullifiers := by
        unfold refundEscrowKAsset settleEscrowRawAsset at hk
        split at hk
        · split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
        · exact absurd hk (by simp)
      exact hn ▸ List.Subset.refl _
  | createObligationA id actor obligor beneficiary asset stake =>
      simp only [execFullA, createEscrowChainA] at h
      cases hk : createEscrowKAsset s.kernel id actor obligor beneficiary asset stake with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          show s.kernel.nullifiers ⊆ k'.nullifiers
          have hn : k'.nullifiers = s.kernel.nullifiers := by
            unfold createEscrowKAsset createEscrowRawAsset at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          exact hn ▸ List.Subset.refl _
  -- fulfill/slash route to refund/release (escrow SETTLE) — `nullifiers` literally unchanged.
  | fulfillObligationA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := refundEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'
      show s.kernel.nullifiers ⊆ k'.nullifiers
      have hn : k'.nullifiers = s.kernel.nullifiers := by
        unfold refundEscrowKAsset settleEscrowRawAsset at hk
        split at hk
        · split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
        · exact absurd hk (by simp)
      exact hn ▸ List.Subset.refl _
  | slashObligationA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := releaseEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'
      show s.kernel.nullifiers ⊆ k'.nullifiers
      have hn : k'.nullifiers = s.kernel.nullifiers := by
        unfold releaseEscrowKAsset settleEscrowRawAsset at hk
        split at hk
        · split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
        · exact absurd hk (by simp)
      exact hn ▸ List.Subset.refl _
  -- §NOTE-SPEND — THE GROWER. `noteSpendNullifier` conses `nf` onto `nullifiers`, so the OLD set is a
  -- subset of the new (`List.subset_cons_self`). This is the ONE arm that moves the measured set.
  | noteSpendA nf actor spendProof =>
      simp only [execFullA, noteSpendChainA] at h
      by_cases hp : spendProof = true
      · rw [if_pos hp] at h
        cases hk : noteSpendNullifier s.kernel nf with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            show s.kernel.nullifiers ⊆ k'.nullifiers
            -- k' = { s.kernel with nullifiers := nf :: s.kernel.nullifiers } (the GROWER) ⇒ old ⊆ new.
            rw [show k' = { s.kernel with nullifiers := nf :: s.kernel.nullifiers } from by
                  unfold noteSpendNullifier at hk; split at hk
                  · exact absurd hk (by simp)
                  · injection hk with hk; exact hk.symm]
            exact List.subset_cons_self _ _
      · rw [if_neg hp] at h; exact absurd h (by simp)
  -- §NOTE-CREATE — grows `commitments` (a DIFFERENT set), `nullifiers` untouched (always-commit).
  | noteCreateA cm actor =>
      simp only [execFullA, noteCreateChainA] at h
      option_inj at h; subst h
      show s.kernel.nullifiers ⊆ (noteCreateCommitment s.kernel cm).nullifiers
      unfold noteCreateCommitment
      exact List.Subset.refl _
  | createCommittedEscrowA id actor creator recipient asset amount hidingProof =>
      simp only [execFullA, createCommittedEscrowChainA, createEscrowChainA] at h; split at h
      · cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            show s.kernel.nullifiers ⊆ k'.nullifiers
            have hn : k'.nullifiers = s.kernel.nullifiers := by
              unfold createEscrowKAsset createEscrowRawAsset at hk; split at hk
              · injection hk with hk; subst hk; rfl
              · exact absurd hk (by simp)
            exact hn ▸ List.Subset.refl _
      · exact absurd h (by simp)
  | releaseCommittedEscrowA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := releaseEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'
      show s.kernel.nullifiers ⊆ k'.nullifiers
      have hn : k'.nullifiers = s.kernel.nullifiers := by
        unfold releaseEscrowKAsset settleEscrowRawAsset at hk
        split at hk
        · split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
        · exact absurd hk (by simp)
      exact hn ▸ List.Subset.refl _
  | refundCommittedEscrowA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := refundEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'
      show s.kernel.nullifiers ⊆ k'.nullifiers
      have hn : k'.nullifiers = s.kernel.nullifiers := by
        unfold refundEscrowKAsset settleEscrowRawAsset at hk
        split at hk
        · split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
        · exact absurd hk (by simp)
      exact hn ▸ List.Subset.refl _
  -- §bridge — lock/finalize/cancel over the SHARED escrow holding-store (kernel updates bal/escrows).
  | bridgeLockA id actor originator destination asset amount =>
      simp only [execFullA, bridgeLockChainA] at h
      cases hk : bridgeLockKAsset s.kernel id actor originator destination asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          show s.kernel.nullifiers ⊆ k'.nullifiers
          have hn : k'.nullifiers = s.kernel.nullifiers := by
            unfold bridgeLockKAsset createBridgeRawAsset at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          exact hn ▸ List.Subset.refl _
  | bridgeFinalizeA id actor asset amount =>
      simp only [execFullA, bridgeFinalizeChainA] at h
      -- OUTER `if bridgeAuthOK` gate, THEN the kernel-op match.
      split at h
      · cases hk : bridgeFinalizeKAsset s.kernel id asset amount with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            show s.kernel.nullifiers ⊆ k'.nullifiers
            have hn : k'.nullifiers = s.kernel.nullifiers := by
              unfold bridgeFinalizeKAsset bridgeFinalizeRawAsset at hk
              split at hk
              · split at hk
                · injection hk with hk; subst hk; rfl
                · exact absurd hk (by simp)
              · exact absurd hk (by simp)
            exact hn ▸ List.Subset.refl _
      · exact absurd h (by simp)
  | bridgeCancelA id actor =>
      simp only [execFullA, bridgeCancelChainA] at h
      split at h
      · cases hk : bridgeCancelKAsset s.kernel id with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            show s.kernel.nullifiers ⊆ k'.nullifiers
            have hn : k'.nullifiers = s.kernel.nullifiers := by
              unfold bridgeCancelKAsset settleEscrowRawAsset at hk
              split at hk
              · split at hk
                · injection hk with hk; subst hk; rfl
                · exact absurd hk (by simp)
              · exact absurd hk (by simp)
            exact hn ▸ List.Subset.refl _
      · exact absurd h (by simp)
  -- §seal — the DE-SHADOWED seal/unseal/createSealPair move capabilities (edit `caps`/`sealedBoxes`),
  -- makeSovereign/refusal/receiptArchive write the cell record — none touch `nullifiers` (frame: `rfl`).
  | sealA pid actor payload =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := sealChainA_factors h; subst hs'; exact List.Subset.refl _
  | unsealA pid actor recipient =>
      simp only [execFullA] at h
      obtain ⟨_, _, _, hs'⟩ := unsealChainA_factors h; subst hs'; exact List.Subset.refl _
  | createSealPairA pid actor sealerHolder unsealerHolder =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := createSealPairChainA_factors h; subst hs'; exact List.Subset.refl _
  | makeSovereignA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := makeSovereignStep_factors h; subst hs'; exact List.Subset.refl _
  | refusalA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; exact List.Subset.refl _
  | receiptArchiveA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; exact List.Subset.refl _
  -- §lifecycle (Wave-3) — seal/unseal/destroy edit `lifecycle`/`deathCert`; refresh edits `delegations`
  -- — none touch `nullifiers` (frame: `rfl`).
  | cellSealA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := cellSealChainA_factors h; subst hs'; exact List.Subset.refl _
  | cellUnsealA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := cellUnsealChainA_factors h; subst hs'; exact List.Subset.refl _
  | cellDestroyA actor cell ch =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := cellDestroyChainA_factors h; subst hs'; exact List.Subset.refl _
  | refreshDelegationA actor child =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := refreshDelegationChainA_factors h; subst hs'; exact List.Subset.refl _
  -- §queue — four ring-buffer effects, each `if stateAuthB … then match queueK … | some k' => …`
  -- (kernel updates `queues`, never `nullifiers`). Gate-peel the outer `if`, then cases the kernel op.
  | queueAllocateA id actor cell cap =>
      simp only [execFullA, queueAllocateChainA] at h
      split at h
      · cases hk : queueAllocateK s.kernel id actor cap with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            show s.kernel.nullifiers ⊆ k'.nullifiers
            have hn : k'.nullifiers = s.kernel.nullifiers := by
              -- queueAllocateK = `match findQueue | some _ => none | none => some {k with queues:=…}`.
              unfold queueAllocateK at hk; split at hk
              · exact absurd hk (by simp)
              · injection hk with hk; subst hk; rfl
            exact hn ▸ List.Subset.refl _
      · exact absurd h (by simp)
  | queueEnqueueA id m actor cell depId dAsset deposit =>
      simp only [execFullA, queueEnqueueChainA] at h
      split at h
      · cases hk : queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            show s.kernel.nullifiers ⊆ k'.nullifiers
            -- queueEnqueueDepositK moves bal/queues/escrows only — read its frame on `nullifiers`.
            have hn : k'.nullifiers = s.kernel.nullifiers :=
              queueEnqueueDepositK_nullifiers s.kernel id m actor cell depId dAsset deposit k' hk
            exact hn ▸ List.Subset.refl _
      · exact absurd h (by simp)
  | queueDequeueA id actor cell depId =>
      simp only [execFullA, queueDequeueChainA] at h
      split at h
      · cases hk : queueDequeueRefundK s.kernel id actor depId with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some kp =>
            rw [hk] at h
            obtain ⟨k', mhd⟩ := kp
            obtain ⟨rfl⟩ := h
            show s.kernel.nullifiers ⊆ k'.nullifiers
            have hn : k'.nullifiers = s.kernel.nullifiers :=
              queueDequeueRefundK_nullifiers s.kernel id actor depId k' mhd hk
            exact hn ▸ List.Subset.refl _
      · exact absurd h (by simp)
  | queueResizeA id newCap actor cell =>
      simp only [execFullA, queueResizeChainA] at h
      split at h
      · cases hk : queueResizeK s.kernel id newCap with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            show s.kernel.nullifiers ⊆ k'.nullifiers
            have hn : k'.nullifiers = s.kernel.nullifiers := by
              -- queueResizeK = `match findQueue | none => none | some q => if … then some {…} else none`.
              unfold queueResizeK at hk
              split at hk
              · exact absurd hk (by simp)
              · split at hk
                · injection hk with hk; subst hk; rfl
                · exact absurd hk (by simp)
            exact hn ▸ List.Subset.refl _
      · exact absurd h (by simp)
  -- §MA-queue-batch (WAVE 4): the atomic batch / pipeline step edit `queues`/`escrows`/`bal`, never
  -- `nullifiers` (the witness lemmas + frame helpers); pipelinedSend edits NOTHING.
  | queueAtomicTxA actor ops =>
      simp only [execFullA] at h
      obtain ⟨s1, hf, _, hk⟩ := queueAtomicTxA_atomic_witness h
      show s.kernel.nullifiers ⊆ s'.kernel.nullifiers
      rw [show s'.kernel.nullifiers = s1.kernel.nullifiers from by rw [hk]]
      exact (queueAtomicTxChainA_nullifiers s s1 ops hf) ▸ List.Subset.refl _
  | queuePipelineStepA srcId owner sinkCells sinkIds =>
      simp only [execFullA] at h
      obtain ⟨k1, mh, hd, hfo⟩ := queuePipelineStepA_routing_witness h
      show s.kernel.nullifiers ⊆ s'.kernel.nullifiers
      have hn : s'.kernel.nullifiers = s.kernel.nullifiers :=
        (pipelineFanoutK_nullifiers k1 s'.kernel owner mh sinkCells sinkIds hfo).trans
          (queueDequeueK_nullifiers s.kernel srcId owner k1 mh hd)
      exact hn ▸ List.Subset.refl _
  | pipelinedSendA actor =>
      simp only [execFullA, Option.some.injEq] at h; subst h; exact List.Subset.refl _
  -- §swiss — four CapTP swiss-table effects, each `if stateAuthB … then match swissK … | some k' => …`
  -- (kernel updates `swiss`, never `nullifiers`). Gate-peel + cases, as the queue arms.
  | exportSturdyRefA sw actor exporter target rights =>
      simp only [execFullA, swissExportChainA] at h
      split at h
      · cases hk : swissExportK s.kernel sw exporter target rights with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            show s.kernel.nullifiers ⊆ k'.nullifiers
            have hn : k'.nullifiers = s.kernel.nullifiers := by
              unfold swissExportK at hk; split at hk
              · exact absurd hk (by simp)
              · split at hk
                · injection hk with hk; subst hk; rfl
                · exact absurd hk (by simp)
            exact hn ▸ List.Subset.refl _
      · exact absurd h (by simp)
  | enlivenRefA sw actor exporter claimed =>
      simp only [execFullA, swissEnlivenChainA] at h
      split at h
      · cases hk : swissEnlivenK s.kernel sw claimed with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            show s.kernel.nullifiers ⊆ k'.nullifiers
            have hn : k'.nullifiers = s.kernel.nullifiers :=
              swissEnlivenK_nullifiers s.kernel sw claimed k' hk
            exact hn ▸ List.Subset.refl _
      · exact absurd h (by simp)
  | swissHandoffA sw certHash introducer exporter =>
      simp only [execFullA, swissHandoffChainA] at h
      split at h
      · cases hk : swissHandoffK s.kernel sw certHash with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            show s.kernel.nullifiers ⊆ k'.nullifiers
            have hn : k'.nullifiers = s.kernel.nullifiers :=
              swissHandoffK_nullifiers s.kernel sw certHash k' hk
            exact hn ▸ List.Subset.refl _
      · exact absurd h (by simp)
  | swissDropA sw actor exporter =>
      simp only [execFullA, swissDropChainA] at h
      split at h
      · cases hk : swissDropK s.kernel sw with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            show s.kernel.nullifiers ⊆ k'.nullifiers
            have hn : k'.nullifiers = s.kernel.nullifiers :=
              swissDropK_nullifiers s.kernel sw k' hk
            exact hn ▸ List.Subset.refl _
      · exact absurd h (by simp)

/-- **`execInnerA_nullifiers_grow`** — the inner-effect fold an `exerciseA` recurses through never
shrinks the nullifier set. Mutual with `execFullA_nullifiers_grow`; chains `List.Subset.trans`. -/
theorem execInnerA_nullifiers_grow (s s' : RecChainedState) (inner : List FullActionA)
    (h : execInnerA s inner = some s') : s.kernel.nullifiers ⊆ s'.kernel.nullifiers := by
  cases inner with
  | nil => simp only [execInnerA, Option.some.injEq] at h; subst h; exact List.Subset.refl _
  | cons a rest =>
      simp only [execInnerA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          exact List.Subset.trans
            (execFullA_nullifiers_grow s s1 a ha)
            (execInnerA_nullifiers_grow s1 s' rest h)
end

/-! ## Step 2 — the turn- and forest-level lift (induction on the list + the pre-order bridge). -/

/-- **`execFullTurnA_nullifiers_grow`** — a committed full turn never shrinks the spent-note nullifier
set. By induction on the action list, chaining `execFullA_nullifiers_grow` by `List.Subset.trans`. -/
theorem execFullTurnA_nullifiers_grow :
    ∀ (s s' : RecChainedState) (tt : List FullActionA),
      execFullTurnA s tt = some s' → s.kernel.nullifiers ⊆ s'.kernel.nullifiers
  | s, s', [], h => by
      simp only [execFullTurnA, Option.some.injEq] at h; subst h; exact List.Subset.refl _
  | s, s', a :: rest, h => by
      simp only [execFullTurnA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          exact List.Subset.trans
            (execFullA_nullifiers_grow s s1 a ha)
            (execFullTurnA_nullifiers_grow s1 s' rest h)

/-- **`execFullForestA_nullifiers_grow`** — a committed full forest never shrinks the nullifier set.
Routes through the pre-order bridge `execFullForestA_eq_execFullTurnA` to the turn-level lemma. -/
theorem execFullForestA_nullifiers_grow (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') : s.kernel.nullifiers ⊆ s'.kernel.nullifiers := by
  rw [execFullForestA_eq_execFullTurnA] at h
  exact execFullTurnA_nullifiers_grow s s' (lowerForestA f) h

/-! ## Step 3 — `nul0 ⊆ s.kernel.nullifiers` carried forever by `livingCellA_carries`. -/

/-- **`livingCellA_no_double_spend`** — Fix any baseline of consumed nullifiers `nul0 ⊆ s.kernel.nullifiers`.
Along the entire unbounded adversarial trajectory `trajA s sched`, under every schedule, every nullifier
in `nul0` stays consumed: `nul0 ⊆ (trajA s sched n).kernel.nullifiers` at every index `n`. This is the
canonical ledger anti-replay safety ("once spent, forever spent") — a genuinely non-conservation property
carried by `livingCellA_carries`. The one-step obligation is: on a commit, `execFullForestA_nullifiers_grow`
(the set only grows); on a reject, the state is unchanged. -/
theorem livingCellA_no_double_spend (nul0 : List Nat) (s : RecChainedState)
    (hinit : nul0 ⊆ s.kernel.nullifiers) (sched : SchedA) :
    ∀ n, nul0 ⊆ (trajA s sched n).kernel.nullifiers :=
  livingCellA_carries (fun s' => nul0 ⊆ s'.kernel.nullifiers)
    (fun a cf h => by
      -- One-step preservation. `cellNextA a cf = (execFullForestA a cf.1).getD a`: on a COMMIT the
      -- forest registry frame only grows the nullifier set (chain by `List.Subset.trans`); on a REJECT
      -- the state is the UNCHANGED `a`, so the baseline `⊆` is preserved trivially.
      show nul0 ⊆ (cellNextA a cf).kernel.nullifiers
      unfold cellNextA
      cases hc : execFullForestA a cf.1 with
      | some a' => simp only [Option.getD_some]
                   exact List.Subset.trans h (execFullForestA_nullifiers_grow a a' cf.1 hc)
      | none    => simp only [Option.getD_none]; exact h)
    s hinit sched

/-- **`livingCellA_spent_note_never_respent`** — if a nullifier `nf` is consumed in the initial state,
then at every index of every trajectory `nf` is still consumed. So a fresh `noteSpendNullifier … nf`
at any reachable state fails-closed (`note_no_double_spend`) — the note cannot be spent twice, for all
time, against any adversarial schedule. The single-element instance of `livingCellA_no_double_spend`
(`nul0 := [nf]`). -/
theorem livingCellA_spent_note_never_respent (nf : Nat) (s : RecChainedState)
    (hinit : nf ∈ s.kernel.nullifiers) (sched : SchedA) :
    ∀ n, nf ∈ (trajA s sched n).kernel.nullifiers := by
  intro n
  have h := livingCellA_no_double_spend [nf] s (by
    intro x hx; rw [List.mem_singleton] at hx; subst hx; exact hinit) sched n
  exact h (List.mem_singleton.mpr rfl)

/-- **`livingCellA_respend_fails_closed`** — a previously-spent `nf` cannot be re-spent at any index
of any trajectory: `noteSpendNullifier` returns `none` (fail-closed). Composes the temporal
"still-spent" fact with the per-step double-spend gate (`note_no_double_spend`). -/
theorem livingCellA_respend_fails_closed (nf : Nat) (s : RecChainedState)
    (hinit : nf ∈ s.kernel.nullifiers) (sched : SchedA) :
    ∀ n, noteSpendNullifier (trajA s sched n).kernel nf = none :=
  fun n => note_no_double_spend _ nf (livingCellA_spent_note_never_respent nf s hinit sched n)

/-! ## It runs (`#eval`) — the spent set strictly grows on a committed noteSpend (non-vacuity).

A single committed `noteSpendA 77` appends `77` to the set (`[] → [77]`), demonstrating that the
grow-only invariant bounds a quantity that actually moves. -/

/-- A committed noteSpend turn: actor 0 spends nullifier 77 — the single `noteSpendA`, no children.
The kernel-side double-spend gate admits a fresh `77` and records it. -/
def spendCF : FullForestA := ⟨.noteSpendA 77 0 true, []⟩

#guard ((execFullForestA fma0 spendCF).map (fun s' => s'.kernel.nullifiers)) == some [77]  --  some [77] (grew from [])
#guard (fma0.kernel.nullifiers) == []  --  []   (BEFORE — strictly fewer)
#guard ((execFullForestA fma0 spendCF).map (fun s' => decide (([] : List Nat) ⊆ s'.kernel.nullifiers))) == some true  --  some true (the carried ⊆ from ∅)
#guard ((execFullForestA fma0 spendCF).map (fun s' => s'.kernel.nullifiers.contains 77)) == some true  --  some true (77 is now spent)
-- the anti-replay teeth: spending 77 AGAIN on the resulting state fails-closed (none)
#guard (((execFullForestA fma0 spendCF).bind (fun s' => noteSpendNullifier s'.kernel 77)).isNone)  --  true

/-! ## Axiom hygiene — no-double-spend pinned to the standard kernel triple. -/

#assert_axioms execFullA_nullifiers_grow
#assert_axioms execFullTurnA_nullifiers_grow
#assert_axioms execFullForestA_nullifiers_grow
#assert_axioms livingCellA_no_double_spend
#assert_axioms livingCellA_spent_note_never_respent
#assert_axioms livingCellA_respend_fails_closed

end Dregg2.Exec
