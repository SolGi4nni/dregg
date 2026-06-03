/-
# Dregg2.Apps.Identity — the identity app as a verified cell-program: revoked stays revoked, forever.

dregg1's identity / verifiable-credential app (`credentials/src/{issuance,revocation,verification}.rs`)
is a three-verb protocol: **issue** mints a credential with a stable id; **revoke** inserts that id into
a grow-only `RevocationRegistry` (`HashSet<[u8;32]>`, insert-only, never removes); **verify** admits a
credential only when a non-membership check passes (`verify_non_revocation` — on presence returns
`NonRevocationError::Revoked`). The verifier never trusts a self-asserted boolean; it checks genuine
absence against the committed set.

The headline safety: permanent revocation — once revoked, a credential can never be re-validated. The
registry is modelled as `s.kernel.revoked : List Nat` (`RecordKernel.lean`), with the verifier's
negative-discharge leg as `FullForestAuth.revocationGate` and per-step teeth `gateOK_revoked_fails`.
This module carries that one-step fact to the coinductive living cell, forever.

The current 46-effect executor has no arm that grows `revoked` (the authority `revoke`/`dropRef`
effects edit only `caps` via `recCRevoke`, not this credential-revocation side-table). So the frame
is the sharpest possible: per-step equality `s'.kernel.revoked = s.kernel.revoked`.

Five theorems, ascending:
* `execFullA_revoked_eq` — per-effect registry frame: a committed effect leaves the registry unchanged.
* `execFullTurnA_revoked_eq` / `execFullForestA_revoked_eq` — turn- and forest-level lift by induction.
* `livingCellA_revoked_grow` — the crown: `rev0 ⊆ s.kernel.revoked` carried forever by
  `livingCellA_carries` against every adversarial schedule.
* `livingCellA_identity_revoked_forever` — the headline: if `credNul` is revoked initially, it is in
  the registry at every trajectory index — so `gateOK` fail-closes at every reachable state.
-/
import Dregg2.Exec.CellNullifier
import Dregg2.Exec.FullForestAuth

namespace Dregg2.Apps.Identity

open Dregg2.Boundary
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Authority
open Dregg2.Exec.EffectsState (stateStep stateStep_factors)

/-! ## Step 0 — registry-frame lemmas for the deeply-nested kernel ops (queue-deposit + swiss).

These five kernel ops touch only `queues`/`swiss`/`bal`/`escrows` — never `revoked` — so a committed
step leaves `revoked` unchanged. Hoisted as `private` frame lemmas, the dual of `CellNullifier`'s
`_nullifiers` helpers. -/

/-- `queueEnqueueK` commits to `{ k with queues := … }` — `revoked` untouched. -/
private theorem queueEnqueueK_revoked (k : RecordKernelState) (id m : Nat) (k₁ : RecordKernelState)
    (hq : queueEnqueueK k id m = some k₁) : k₁.revoked = k.revoked := by
  unfold queueEnqueueK at hq; split at hq
  · exact absurd hq (by simp)
  · split at hq
    · injection hq with hq; subst hq; rfl
    · exact absurd hq (by simp)

private theorem queueEnqueueDepositK_revoked (k : RecordKernelState) (id m : Nat)
    (sender owner : CellId) (depId : Nat) (dAsset : AssetId) (deposit : ℤ) (k' : RecordKernelState)
    (h : queueEnqueueDepositK k id m sender owner depId dAsset deposit = some k') :
    k'.revoked = k.revoked := by
  unfold queueEnqueueDepositK at h
  split at h
  · exact absurd h (by simp)                                 -- queueEnqueueK = none
  · rename_i k₁ hq                                            -- queueEnqueueK = some k₁
    split at h
    · option_inj at h; subst h                               -- deposit gate true ⇒ k' = createEscrowRawAsset k₁ …
      show k₁.revoked = k.revoked
      exact queueEnqueueK_revoked k id m k₁ hq
    · exact absurd h (by simp)                               -- deposit gate false

/-- `queueDequeueK` commits to `{ k with queues := … }` — `revoked` untouched. -/
private theorem queueDequeueK_revoked (k : RecordKernelState) (id : Nat) (actor : CellId)
    (k₁ : RecordKernelState) (mh : Nat) (hq : queueDequeueK k id actor = some (k₁, mh)) :
    k₁.revoked = k.revoked := by
  unfold queueDequeueK at hq; split at hq
  · exact absurd hq (by simp)
  · split at hq
    · split at hq
      · exact absurd hq (by simp)
      · option_inj at hq; obtain ⟨hq, _⟩ := hq; subst hq; rfl
    · exact absurd hq (by simp)

private theorem queueDequeueRefundK_revoked (k : RecordKernelState) (id : Nat) (actor : CellId)
    (depId : Nat) (k' : RecordKernelState) (mh : Nat)
    (h : queueDequeueRefundK k id actor depId = some (k', mh)) :
    k'.revoked = k.revoked := by
  unfold queueDequeueRefundK at h
  cases hq : queueDequeueK k id actor with
  | none => rw [hq] at h; exact absurd h (by simp)
  | some kp =>
      obtain ⟨k₁, mh₁⟩ := kp
      rw [hq] at h; simp only [] at h
      split at h
      · split at h
        · option_inj at h; obtain ⟨h, _⟩ := h; subst h       -- record found ∧ live ⇒ settle
          show k₁.revoked = k.revoked
          exact queueDequeueK_revoked k id actor k₁ mh₁ hq
        · exact absurd h (by simp)                           -- target not a live account
      · exact absurd h (by simp)                             -- deposit record absent

/-- `swissEnlivenK` commits to `{ k with swiss := … }` — `revoked` untouched. -/
private theorem swissEnlivenK_revoked (k : RecordKernelState) (sw : Nat) (claimed : List Auth)
    (k' : RecordKernelState) (h : swissEnlivenK k sw claimed = some k') :
    k'.revoked = k.revoked := by
  unfold swissEnlivenK at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · injection h with h; subst h; rfl
    · exact absurd h (by simp)

/-- `swissHandoffK` commits to `{ k with swiss := … }` — `revoked` untouched. -/
private theorem swissHandoffK_revoked (k : RecordKernelState) (sw certHash : Nat)
    (k' : RecordKernelState) (h : swissHandoffK k sw certHash = some k') :
    k'.revoked = k.revoked := by
  unfold swissHandoffK at h
  split at h
  · exact absurd h (by simp)
  · injection h with h; subst h; rfl

/-- `swissDropK` commits to `{ k with swiss := … }` (remove or decrement) — `revoked` untouched. -/
private theorem swissDropK_revoked (k : RecordKernelState) (sw : Nat)
    (k' : RecordKernelState) (h : swissDropK k sw = some k') :
    k'.revoked = k.revoked := by
  unfold swissDropK at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · injection h with h; subst h; rfl
      · injection h with h; subst h; rfl

/-! ## Step 1 — `execFullA_revoked_eq`: the per-effect registry frame (46-arm dispatch).

Every arm leaves `revoked` unchanged: no current effect grows the credential-revocation registry
(`noteSpend` grows `nullifiers`; the authority `revoke`/`dropRef`/`revokeDelegation` effects edit `caps`
via `recKRevokeTarget`). Each arm reduces `k'.revoked = s.kernel.revoked` by `rfl`. -/

/-- **`execFullA_revoked_eq`** — a committed `FullActionA` leaves the credential revocation registry
unchanged: `s'.kernel.revoked = s.kernel.revoked`. No current effect grows it; every kernel transform
writes a different field. The sharpest dual of `execFullA_ledger_per_asset`. -/
theorem execFullA_revoked_eq (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s') : s'.kernel.revoked = s.kernel.revoked := by
  cases fa with
  -- §catalog / supply / authority — chained `match kernelOp | some k' => some {kernel:=k',…}` wrappers.
  | balanceA t a =>
      simp only [execFullA, recCexecAsset] at h
      cases hk : recKExecAsset s.kernel t a with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold recKExecAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | delegate del rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel del rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold recKDelegate at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | revoke holder t =>
      -- `recCRevoke`/`recKRevokeTarget` edit ONLY `caps` — the credential-revocation registry is a
      -- DISTINCT side-table, untouched (the projection through the `{caps := …}` update is `rfl`).
      simp only [execFullA, recCRevoke] at h
      option_inj at h; subst h; rfl
  | mintA actor cell a amt =>
      simp only [execFullA, recCMintAsset] at h
      cases hk : recKMintAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold recKMintAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | burnA actor cell a amt =>
      simp only [execFullA, recCBurnAsset] at h
      cases hk : recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold recKBurnAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  -- §pure-state — `stateStep` (field write); factors through `stateStep_factors` (kernel = writeField,
  -- a `cell`-only update, `revoked` untouched ⇒ `rfl`). All four share the proof.
  | setFieldA actor cell f v =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | emitEventA actor cell topic data =>
      simp only [execFullA, emitStep] at h
      option_inj at h; subst h; rfl
  | incrementNonceA actor cell n =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | setPermissionsA actor cell p =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | setVKA actor cell vk =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  -- §authority — introduce/validateHandoff route to recKDelegate; delegateAtten to recKDelegateAtten;
  -- attenuate is always-commit (caps-only); dropRef/revokeDelegation to recCRevoke (caps-only);
  -- exercise factors (kernel UNCHANGED). NONE touches the credential-revocation registry.
  | introduceA intro rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel intro rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold recKDelegate at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | delegateAttenA del rec t keep =>
      simp only [execFullA, recCDelegateAtten] at h
      cases hk : recKDelegateAtten s.kernel del rec t keep with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold recKDelegateAtten at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | attenuateA actor idx keep =>
      simp only [execFullA, attenuateStepA] at h
      option_inj at h; subst h; rfl
  | dropRefA holder t =>
      simp only [execFullA, recCRevoke] at h
      option_inj at h; subst h; rfl
  | revokeDelegationA holder t =>
      simp only [execFullA, recCRevoke] at h
      option_inj at h; subst h; rfl
  | validateHandoffA intro rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel intro rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold recKDelegate at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | exerciseA actor t =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := exerciseStepA_factors h; subst hs'; rfl
  -- §supply-growth — createCell/spawn factor through their gates (createCellIntoAsset / + a caps grant
  -- — neither touches `revoked`); bridgeMint reuses recCMintAsset.
  | createCellA actor newCell =>
      obtain ⟨_, _, hs'⟩ := createCellChainA_factors (by simpa only [execFullA] using h)
      subst hs'; rfl
  | spawnA actor child target =>
      obtain ⟨s1, hc, hs'⟩ := spawnChainA_factors (by simpa only [execFullA] using h)
      subst hs'
      obtain ⟨_, _, hc'⟩ := createCellChainA_factors hc; subst hc'; rfl
  | bridgeMintA actor cell a value =>
      simp only [execFullA, recCMintAsset] at h
      cases hk : recKMintAsset s.kernel actor cell a value with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold recKMintAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  -- §escrow / obligation / committed — chained holding-store steps (kernel updates bal/escrows, never
  -- `revoked`). create/obligation/committed-create share createEscrowKAsset; release/refund share
  -- releaseEscrowKAsset/refundEscrowKAsset.
  | createEscrowA id actor creator recipient asset amount =>
      simp only [execFullA, createEscrowChainA] at h
      cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold createEscrowKAsset createEscrowRawAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | releaseEscrowA id actor =>
      simp only [execFullA, releaseEscrowChainA] at h
      cases hk : releaseEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold releaseEscrowKAsset settleEscrowRawAsset at hk
          split at hk
          · split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          · exact absurd hk (by simp)
  | refundEscrowA id actor =>
      simp only [execFullA, refundEscrowChainA] at h
      cases hk : refundEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold refundEscrowKAsset settleEscrowRawAsset at hk
          split at hk
          · split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          · exact absurd hk (by simp)
  | createObligationA id actor obligor beneficiary asset stake =>
      simp only [execFullA, createEscrowChainA] at h
      cases hk : createEscrowKAsset s.kernel id actor obligor beneficiary asset stake with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold createEscrowKAsset createEscrowRawAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  -- §NOTE-SPEND — grows `nullifiers` (a DIFFERENT registry), `revoked` UNTOUCHED. This is the arm that
  -- moves the nullifier set in `CellNullifier`; here it frames the credential-revocation registry.
  | noteSpendA nf actor =>
      simp only [execFullA, noteSpendChainA] at h
      cases hk : noteSpendNullifier s.kernel nf with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold noteSpendNullifier at hk; split at hk
          · exact absurd hk (by simp)
          · injection hk with hk; subst hk; rfl
  -- §NOTE-CREATE — grows `commitments` (a DIFFERENT set), `revoked` untouched (always-commit).
  | noteCreateA cm actor =>
      simp only [execFullA, noteCreateChainA, noteCreateCommitment] at h
      option_inj at h; subst h; rfl
  | createCommittedEscrowA id actor creator recipient asset amount =>
      simp only [execFullA, createEscrowChainA] at h
      cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold createEscrowKAsset createEscrowRawAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | releaseCommittedEscrowA id actor =>
      simp only [execFullA, releaseEscrowChainA] at h
      cases hk : releaseEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold releaseEscrowKAsset settleEscrowRawAsset at hk
          split at hk
          · split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          · exact absurd hk (by simp)
  | refundCommittedEscrowA id actor =>
      simp only [execFullA, refundEscrowChainA] at h
      cases hk : refundEscrowKAsset s.kernel id with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold refundEscrowKAsset settleEscrowRawAsset at hk
          split at hk
          · split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          · exact absurd hk (by simp)
  -- §bridge — lock/finalize/cancel over the SHARED escrow holding-store (kernel updates bal/escrows).
  | bridgeLockA id actor originator destination asset amount =>
      simp only [execFullA, bridgeLockChainA] at h
      cases hk : bridgeLockKAsset s.kernel id actor originator destination asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; option_inj at h; subst h
          show k'.revoked = s.kernel.revoked
          unfold bridgeLockKAsset createBridgeRawAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | bridgeFinalizeA id actor asset amount =>
      simp only [execFullA, bridgeFinalizeChainA] at h
      split at h
      · cases hk : bridgeFinalizeKAsset s.kernel id asset amount with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; option_inj at h; subst h
            show k'.revoked = s.kernel.revoked
            unfold bridgeFinalizeKAsset bridgeFinalizeRawAsset at hk
            split at hk
            · split at hk
              · injection hk with hk; subst hk; rfl
              · exact absurd hk (by simp)
            · exact absurd hk (by simp)
      · exact absurd h (by simp)
  | bridgeCancelA id actor =>
      simp only [execFullA, bridgeCancelChainA] at h
      split at h
      · cases hk : bridgeCancelKAsset s.kernel id with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; option_inj at h; subst h
            show k'.revoked = s.kernel.revoked
            unfold bridgeCancelKAsset settleEscrowRawAsset at hk
            split at hk
            · split at hk
              · injection hk with hk; subst hk; rfl
              · exact absurd hk (by simp)
            · exact absurd hk (by simp)
      · exact absurd h (by simp)
  -- §seal — six bal-neutral field writes via stateStep / makeSovereignStep (cell-only update).
  | sealA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | unsealA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | createSealPairA actor sealerHolder unsealerHolder =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | makeSovereignA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := makeSovereignStep_factors h; subst hs'; rfl
  | refusalA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | receiptArchiveA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  -- §queue — four ring-buffer effects, each `if stateAuthB … then match queueK … | some k' => …`
  -- (kernel updates `queues`, never `revoked`). Gate-peel the outer `if`, then cases the kernel op.
  | queueAllocateA id actor cell cap =>
      simp only [execFullA, queueAllocateChainA] at h
      split at h
      · cases hk : queueAllocateK s.kernel id actor cap with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; option_inj at h; subst h
            show k'.revoked = s.kernel.revoked
            unfold queueAllocateK at hk; split at hk
            · exact absurd hk (by simp)
            · injection hk with hk; subst hk; rfl
      · exact absurd h (by simp)
  | queueEnqueueA id m actor cell depId dAsset deposit =>
      simp only [execFullA, queueEnqueueChainA] at h
      split at h
      · cases hk : queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; option_inj at h; subst h
            show k'.revoked = s.kernel.revoked
            exact queueEnqueueDepositK_revoked s.kernel id m actor cell depId dAsset deposit k' hk
      · exact absurd h (by simp)
  | queueDequeueA id actor cell depId deposit =>
      simp only [execFullA, queueDequeueChainA] at h
      split at h
      · cases hk : queueDequeueRefundK s.kernel id actor depId with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some kp =>
            rw [hk] at h
            obtain ⟨k', mhd⟩ := kp
            option_inj at h; subst h
            show k'.revoked = s.kernel.revoked
            exact queueDequeueRefundK_revoked s.kernel id actor depId k' mhd hk
      · exact absurd h (by simp)
  | queueResizeA id newCap actor cell =>
      simp only [execFullA, queueResizeChainA] at h
      split at h
      · cases hk : queueResizeK s.kernel id newCap with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; option_inj at h; subst h
            show k'.revoked = s.kernel.revoked
            unfold queueResizeK at hk
            split at hk
            · exact absurd hk (by simp)
            · split at hk
              · injection hk with hk; subst hk; rfl
              · exact absurd hk (by simp)
      · exact absurd h (by simp)
  -- §swiss — four CapTP swiss-table effects, each `if stateAuthB … then match swissK … | some k' => …`
  -- (kernel updates `swiss`, never `revoked`). Gate-peel + cases, as the queue arms.
  | exportSturdyRefA sw actor exporter target rights =>
      simp only [execFullA, swissExportChainA] at h
      split at h
      · cases hk : swissExportK s.kernel sw exporter target rights with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; option_inj at h; subst h
            show k'.revoked = s.kernel.revoked
            unfold swissExportK at hk; split at hk
            · exact absurd hk (by simp)
            · split at hk
              · injection hk with hk; subst hk; rfl
              · exact absurd hk (by simp)
      · exact absurd h (by simp)
  | enlivenRefA sw actor exporter claimed =>
      simp only [execFullA, swissEnlivenChainA] at h
      split at h
      · cases hk : swissEnlivenK s.kernel sw claimed with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; option_inj at h; subst h
            show k'.revoked = s.kernel.revoked
            exact swissEnlivenK_revoked s.kernel sw claimed k' hk
      · exact absurd h (by simp)
  | swissHandoffA sw certHash introducer exporter =>
      simp only [execFullA, swissHandoffChainA] at h
      split at h
      · cases hk : swissHandoffK s.kernel sw certHash with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; option_inj at h; subst h
            show k'.revoked = s.kernel.revoked
            exact swissHandoffK_revoked s.kernel sw certHash k' hk
      · exact absurd h (by simp)
  | swissDropA sw actor exporter =>
      simp only [execFullA, swissDropChainA] at h
      split at h
      · cases hk : swissDropK s.kernel sw with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; option_inj at h; subst h
            show k'.revoked = s.kernel.revoked
            exact swissDropK_revoked s.kernel sw k' hk
      · exact absurd h (by simp)

/-! ## Step 2 — the turn- and forest-level lift (induction on the list + the pre-order bridge). -/

/-- **`execFullTurnA_revoked_eq` (PROVED).** A committed per-asset full TURN leaves the credential
revocation registry UNCHANGED. By induction on the action list — each committed `execFullA` step frames
the registry (`execFullA_revoked_eq`), chained by `Eq.trans`; the empty turn is `rfl`. Mirrors
`CellNullifier.execFullTurnA_nullifiers_grow`'s structure (with `=` for `⊆`). -/
theorem execFullTurnA_revoked_eq :
    ∀ (s s' : RecChainedState) (tt : List FullActionA),
      execFullTurnA s tt = some s' → s'.kernel.revoked = s.kernel.revoked
  | s, s', [], h => by
      simp only [execFullTurnA, Option.some.injEq] at h; subst h; rfl
  | s, s', a :: rest, h => by
      simp only [execFullTurnA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          exact (execFullTurnA_revoked_eq s1 s' rest h).trans (execFullA_revoked_eq s s1 a ha)

/-- **`execFullForestA_revoked_eq` (PROVED).** A committed full FOREST leaves the credential revocation
registry UNCHANGED. Read straight through the pre-order bridge `execFullForestA_eq_execFullTurnA` into
the turn-level lemma — the route `CellNullifier.execFullForestA_nullifiers_grow` takes. -/
theorem execFullForestA_revoked_eq (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') : s'.kernel.revoked = s.kernel.revoked := by
  rw [execFullForestA_eq_execFullTurnA] at h
  exact execFullTurnA_revoked_eq s s' (lowerForestA f) h

/-- **`execFullForestA_revoked_grow` (PROVED) — the grow-only COROLLARY.** Read off the equality:
`s.kernel.revoked ⊆ s'.kernel.revoked` (the permanent-revocation frame as the dregg1
`RevocationRegistry`'s insert-only `HashSet` sees it). Stated as `⊆` so the carry below is forward-
compatible with a future explicit `cap_revoke` effect that GROWS the registry. -/
theorem execFullForestA_revoked_grow (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') : s.kernel.revoked ⊆ s'.kernel.revoked := by
  rw [execFullForestA_revoked_eq s s' f h]; exact List.Subset.refl _

/-! ## Step 3 — THE CROWN: `rev0 ⊆ s.kernel.revoked` carried FOREVER by `livingCellA_carries`. -/

/-- **`livingCellA_revoked_grow`** — the permanent-revocation crown: for any baseline `rev0 ⊆
s.kernel.revoked`, every id in `rev0` stays revoked at every index of every adversarial trajectory
`trajA s sched`. Carried by `livingCellA_carries` with `Good := (rev0 ⊆ ·.kernel.revoked)`, whose
one-step obligation is `execFullForestA_revoked_grow` on a commit and the stay-put self-loop on a reject.
A genuinely non-conservation safety: it reads the registry, never the per-asset measure. -/
theorem livingCellA_revoked_grow (rev0 : List Nat) (s : RecChainedState)
    (hinit : rev0 ⊆ s.kernel.revoked) (sched : SchedA) :
    ∀ n, rev0 ⊆ (trajA s sched n).kernel.revoked :=
  livingCellA_carries (fun s' => rev0 ⊆ s'.kernel.revoked)
    (fun a cf h => by
      -- One-step preservation. `cellNextA a cf = (execFullForestA a cf.1).getD a`: on a COMMIT the
      -- forest registry frame keeps (≥) the revocation registry (chain by `List.Subset.trans`); on a
      -- REJECT the state is the UNCHANGED `a`, so the baseline `⊆` is preserved trivially.
      show rev0 ⊆ (cellNextA a cf).kernel.revoked
      unfold cellNextA
      cases hc : execFullForestA a cf.1 with
      | some a' => simp only [Option.getD_some]
                   exact List.Subset.trans h (execFullForestA_revoked_grow a a' cf.1 hc)
      | none    => simp only [Option.getD_none]; exact h)
    s hinit sched

/-! ## Step 4 — THE HEADLINE: `identity_revoked_forever` — a revoked identity can NEVER be re-validated. -/

/-- **`livingCellA_identity_revoked_forever`** — if `credNul` is in the revocation registry initially,
it is in the registry at every index of every adversarial trajectory. The single-element instance of
the crown (`rev0 := [credNul]`). -/
theorem livingCellA_identity_revoked_forever (credNul : Nat) (s : RecChainedState)
    (hinit : credNul ∈ s.kernel.revoked) (sched : SchedA) :
    ∀ n, credNul ∈ (trajA s sched n).kernel.revoked := by
  intro n
  have h := livingCellA_revoked_grow [credNul] s (by
    intro x hx; rw [List.mem_singleton] at hx; subst hx; exact hinit) sched n
  exact h (List.mem_singleton.mpr rfl)

/-- **`identity_gate_revoked_forever`** — a revoked identity's auth gate fail-closes at every reachable
state of every trajectory: if `na.credNul` is revoked initially, then `gateOK na (trajA s sched n) =
false` for all `n`. Composes `livingCellA_identity_revoked_forever` with `gateOK_revoked_fails`.
The `NodeAuthC` type parameters `{Digest Proof … Tag}` are inferred from `na`; the proof reads only
`na.credNul` and the kernel registry. -/
theorem identity_gate_revoked_forever
    {Digest Proof Request Stmt Wit CellId Rights Ctx Gateway Bytes Tag : Type}
    [DecidableEq CellId] [SemilatticeInf Rights] [OrderTop Rights] [DecidableLE Rights]
    [Dregg2.Laws.Verifiable Stmt Wit]
    [DecidableEq Tag] [CaveatChain.MacKernel (CaveatChain.Key Tag) Bytes Tag]
    [FullForestAuth.AuthPortal (FullForestAuth.Authorization Digest Proof) Ctx]
    (na : FullForestAuth.NodeAuthC (Digest := Digest) (Proof := Proof) (Request := Request)
      (Stmt := Stmt) (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx)
      (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag))
    (s : RecChainedState) (hinit : na.credNul ∈ s.kernel.revoked) (sched : SchedA) :
    ∀ n, FullForestAuth.gateOK na (trajA s sched n) = false := by
  intro n
  refine FullForestAuth.gateOK_revoked_fails na (trajA s sched n) ?_
  -- `credNul ∈ revoked` (carried forever) ⇒ `revoked.contains credNul = true`.
  rw [List.contains_iff_mem]
  exact livingCellA_identity_revoked_forever na.credNul s hinit sched n

/-! ## It runs (`#eval`) — the registry is non-empty and stable across a real committed turn.

We exhibit a kernel with `credNul = 42` already revoked, run a real conserving transfer, and observe
`42` is still revoked afterward. This witnesses non-vacuity: the carried invariant bounds a genuinely
non-empty, genuinely stable registry. -/

/-- A real kernel state with credential id `42` ALREADY revoked: `fma0` with `revoked := [42]`. -/
def fmaRevoked : RecChainedState :=
  { fma0 with kernel := { fma0.kernel with revoked := [42] } }

#eval fmaRevoked.kernel.revoked                                                       -- [42] (42 is revoked)
#eval fmaRevoked.kernel.revoked.contains 42                                           -- true
-- run the real conserving transfer; the revocation registry is UNCHANGED (still [42]):
#eval (execFullForestA fmaRevoked transferCF.1).map (fun s' => s'.kernel.revoked)            -- some [42]
#eval (execFullForestA fmaRevoked transferCF.1).map (fun s' => s'.kernel.revoked.contains 42)  -- some true (STILL revoked)
#eval (execFullForestA fmaRevoked transferCF.1).map
        (fun s' => decide (([42] : List Nat) ⊆ s'.kernel.revoked))                    -- some true (the carried ⊆)
-- a credential id NOT revoked (`99`) is genuinely absent — the registry has teeth, not all-true:
#eval fmaRevoked.kernel.revoked.contains 99                                           -- false

/-! ## Axiom hygiene -/

#assert_axioms execFullA_revoked_eq
#assert_axioms execFullTurnA_revoked_eq
#assert_axioms execFullForestA_revoked_eq
#assert_axioms execFullForestA_revoked_grow
#assert_axioms livingCellA_revoked_grow
#assert_axioms livingCellA_identity_revoked_forever
#assert_axioms identity_gate_revoked_forever

end Dregg2.Apps.Identity
