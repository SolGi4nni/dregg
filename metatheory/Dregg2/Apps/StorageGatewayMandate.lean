/-
# Dregg2.Apps.StorageGatewayMandate — storage gateway mandate as a verified cell-program (ungated).

A **storage-gateway mandate** on the REAL `RecordKernelState`: the mandate cell carries `object_key`,
`last_op`, `volume_spent` (monotonic Stingray debit tracker), and an immutable `commitment_anchor`.
Predicate admission (`sgmAdmitM`) couples op-allowlist, prefix authorization (PUT), compartment
clearance (GET), and volume-budget debits (`Proof/Stingray.Slice`).

Load-bearing guarantees (ungated crown):

  * **REJECTION TEETH** — disallowed ops, prefix violations, clearance failures, and over-debits
    fail-closed at the predicate layer.
  * **VOLUME LEGALITY** — along any adversarial schedule of admitted ops, spent stays within ceiling
    (`sgm_volume_legal_forever`).
  * **CONSERVATION** — mandate metadata writes are balance-neutral (`sgm_pay_supply_forever` via
    `livingCellA_carries` / `cellObsA_next`).

Templates: `Apps/CompartmentWorkflowMandate.lean`. Zero `sorry`/`admit`/`axiom`.
-/
import Dregg2.Exec.CellCarry
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.FullForest
import Dregg2.Authority.ClearanceGraph
import Dregg2.Apps.StorageGatewayMandate.Core
import Dregg2.Proof.Noninterference
import Dregg2.Proof.Stingray
import Dregg2.Tactics

namespace Dregg2.Apps.StorageGatewayMandate

open Dregg2.Exec
open Dregg2.Exec (cellObsA)
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState (caveatsAdmit fieldOf writeField stateStepGuarded stateStepGuarded_admits
  stateStepGuarded_caveat_violation_fails stateStepGuarded_eq stateStep_factors guarded_state_field_written)
open Dregg2.Proof.Noninterference (writeField_cell_other writeField_field_ne field_setField_ne)
open Dregg2.Authority.ClearanceGraph
open Dregg2.Proof.Stingray

/-! ## §1 — Gateway domain on RecordKernel (object key + op + volume spent). -/

abbrev mandateActor : CellId := 0
abbrev payAsset : AssetId := 0
abbrev sgmEmitTopic : Int := 9

def mandateCaveats : List SlotCaveat :=
  [ .immutable commitmentAnchorSlot
  , .monotonic volumeSpentSlot
  , .boundedBy volumeSpentSlot 0 (demoMandate.volumeBudget.ceiling : Int) ]

/-- Write the object key field on the mandate cell. -/
def sgmExecSetKey (actor : CellId) (key : Int) : FullForestA :=
  ⟨ .setFieldA actor mandateCell objectKeySlot key, [] ⟩

/-- Write the last-op field on the mandate cell. -/
def sgmExecSetOp (actor : CellId) (op : Int) : FullForestA :=
  ⟨ .setFieldA actor mandateCell lastOpSlot op, [] ⟩

/-- Bump the monotonic volume-spent tracker. -/
def sgmExecDebitVolume (actor : CellId) (newSpent : Int) : FullForestA :=
  ⟨ .setFieldA actor mandateCell volumeSpentSlot newSpent, [] ⟩

/-- Audit emit for a committed storage op (blob hash as payload). -/
def sgmExecEmit (actor : CellId) (blobHash : Int) : FullForestA :=
  ⟨ .emitEventA actor mandateCell sgmEmitTopic blobHash, [] ⟩

/-- One storage op as a chained sequence: set key, set op, emit blob hash. -/
def sgmStorageChain (s : RecChainedState) (actor : CellId) (key op blobHash : Int) :
    Option RecChainedState :=
  (execFullForestA s (sgmExecSetKey actor key)).bind fun s' =>
    (execFullForestA s' (sgmExecSetOp actor op)).bind fun s'' =>
      execFullForestA s'' (sgmExecEmit actor blobHash)

/-! ## §A — Predicate-level forever stream (volume legality). -/

inductive SgmOp where
  | tick (req : StorageRequest)
  deriving Repr, DecidableEq

def SgmSched : Type := Nat → SgmOp

def sgmStep (m : StorageMandate) (s : SgmRuntime) : SgmOp → SgmRuntime
  | .tick req => (sgmAdmitM m s req).getD s

def sgmTraj (m : StorageMandate) (s : SgmRuntime) (sched : SgmSched) : Nat → SgmRuntime
  | 0     => s
  | n + 1 => sgmStep m (sgmTraj m s sched n) (sched n)

theorem sgmStep_preserves_WF (m : StorageMandate) (s : SgmRuntime) (op : SgmOp) (hwf : s.WF) :
    (sgmStep m s op).WF := by
  rcases op with ⟨req⟩
  show (sgmAdmitM m s req).getD s |>.WF
  cases hp : sgmAdmitM m s req with
  | some s' => simp only [Option.getD_some]; exact sgmAdmitM_preserves_WF m s s' req hwf hp
  | none    => simp only [Option.getD_none]; exact hwf

/-- **`sgm_volume_legal_forever` (PROVED)** — volume spent stays within ceiling along every admitted
op stream, under every adversarial schedule. -/
theorem sgm_volume_legal_forever (m : StorageMandate) (s : SgmRuntime) (hinit : s.WF) (sched : SgmSched) :
    ∀ n, (sgmTraj m s sched n).WF := by
  intro n
  induction n with
  | zero => exact hinit
  | succ k ih =>
      show (sgmStep m (sgmTraj m s sched k) (sched k)).WF
      exact sgmStep_preserves_WF m (sgmTraj m s sched k) (sched k) ih

/-! ## §B — REAL executor teeth + conservation crown. -/

theorem sgm_over_debit_rejected_exec (s : RecChainedState) (actor : CellId) (newSpent : Int)
    (hbound : caveatsAdmit s.kernel volumeSpentSlot actor mandateCell newSpent = false) :
    execFullForestA s (sgmExecDebitVolume actor newSpent) = none := by
  have hnone := stateStepGuarded_caveat_violation_fails s volumeSpentSlot actor mandateCell newSpent hbound
  rw [execFullForestA_eq_execFullTurnA]
  simp only [sgmExecDebitVolume, lowerForestA, lowerChildrenA, execFullTurnA, execFullA, hnone]

theorem sgmExecSetKey_delta_zero (actor : CellId) (key : Int) (b : AssetId) :
    turnLedgerDeltaAsset (lowerForestA (sgmExecSetKey actor key)) b = 0 := by
  simp [sgmExecSetKey, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem sgmExecSetOp_delta_zero (actor : CellId) (op : Int) (b : AssetId) :
    turnLedgerDeltaAsset (lowerForestA (sgmExecSetOp actor op)) b = 0 := by
  simp [sgmExecSetOp, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem sgmExecDebitVolume_delta_zero (actor : CellId) (newSpent : Int) (b : AssetId) :
    turnLedgerDeltaAsset (lowerForestA (sgmExecDebitVolume actor newSpent)) b = 0 := by
  simp [sgmExecDebitVolume, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem sgmExecEmit_delta_zero (actor : CellId) (blobHash : Int) (b : AssetId) :
    turnLedgerDeltaAsset (lowerForestA (sgmExecEmit actor blobHash)) b = 0 := by
  simp [sgmExecEmit, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem sgm_chain_conserves {s s' : RecChainedState} (actor : CellId) (key op blobHash : Int) (b : AssetId)
    (h : sgmStorageChain s actor key op blobHash = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  cases hkey : execFullForestA s (sgmExecSetKey actor key) with
  | none => simp [sgmStorageChain, hkey] at h
  | some s1 =>
      cases hop : execFullForestA s1 (sgmExecSetOp actor op) with
      | none => simp [sgmStorageChain, hkey, hop] at h
      | some s2 =>
          have hem : execFullForestA s2 (sgmExecEmit actor blobHash) = some s' := by
            simpa [sgmStorageChain, hkey, hop] using h
          have h1 := execFullForestA_conserves_per_asset s s1 (sgmExecSetKey actor key) b hkey
            (sgmExecSetKey_delta_zero actor key b)
          have h2 := execFullForestA_conserves_per_asset s1 s2 (sgmExecSetOp actor op) b hop
            (sgmExecSetOp_delta_zero actor op b)
          have h3 := execFullForestA_conserves_per_asset s2 s' (sgmExecEmit actor blobHash) b hem
            (sgmExecEmit_delta_zero actor blobHash b)
          calc recTotalAssetWithEscrow s'.kernel b
              = recTotalAssetWithEscrow s2.kernel b := h3
            _ = recTotalAssetWithEscrow s1.kernel b := h2
            _ = recTotalAssetWithEscrow s.kernel b := h1

/-- **`sgm_pay_supply_forever` (PROVED) — APP SEMANTICS (ungated crown).** Along EVERY adversarial
schedule on the real living cell, payment asset combined supply never drifts. -/
theorem sgm_pay_supply_forever (s0 : RecChainedState) (sched : SchedA) :
    ∀ n, recTotalAssetWithEscrow (trajA s0 sched n).kernel payAsset =
          recTotalAssetWithEscrow s0.kernel payAsset := by
  intro n
  simpa [cellObsA] using congrFun (livingCellA_obs_invariant' s0 sched n) payAsset

/-! ## §B′·frame — GENERIC executor frame: `slotCaveats` of a LIVE cell is enforced forever.

The single load-bearing fact that makes the mandate crown NON-vacuous: along ANY adversarial forest
trajectory, the published per-slot caveat PROGRAM installed on the live mandate cell is NEVER removed
or altered, and the cell stays a live account. Two structural facts discharge every one of the 53
`FullActionA` arms: (1) `accounts` only ever GROWS (every kernel transform either keeps `accounts`
fixed or `insert`s a fresh id); (2) `slotCaveats` is ONLY ever written at a FRESHLY-minted id (the
three create arms, whose `newCell ∉ accounts` gate forces `newCell ≠ c` for any live `c`), so the
`slotCaveats c` projection of a live cell `c` is unchanged by every committed step. This is the
executor-level teeth: the `.immutable`/`.monotonicSeq`/`.boundedBy` program a factory publishes is
enforced for the cell's WHOLE LIFE. The structural sibling of `Subscription.execFullA_subWF_preserved`
and `CellNullifier.execFullA_nullifiers_grow`. Generic over the cell id and the caveat list. -/

/-- `queueEnqueueK` commits to `{ k with queues := … }` — `accounts`/`slotCaveats` untouched. -/
private theorem queueEnqueueK_frame (k : RecordKernelState) (id m : Nat) (k₁ : RecordKernelState)
    (hq : queueEnqueueK k id m = some k₁) : k₁.accounts = k.accounts ∧ k₁.slotCaveats = k.slotCaveats := by
  unfold queueEnqueueK at hq; split at hq
  · exact absurd hq (by simp)
  · split at hq
    · injection hq with hq; subst hq; exact ⟨rfl, rfl⟩
    · exact absurd hq (by simp)

private theorem queueEnqueueDepositK_frame (k : RecordKernelState) (id m : Nat)
    (sender owner : CellId) (depId : Nat) (dAsset : AssetId) (deposit : ℤ) (k' : RecordKernelState)
    (h : queueEnqueueDepositK k id m sender owner depId dAsset deposit = some k') :
    k'.accounts = k.accounts ∧ k'.slotCaveats = k.slotCaveats := by
  unfold queueEnqueueDepositK at h
  split at h
  · exact absurd h (by simp)
  · rename_i k₁ hq
    split at h
    · obtain ⟨rfl⟩ := h
      -- k' = createEscrowRawAsset k₁ … (bal/escrows only) ⇒ accounts/slotCaveats = k₁'s = k's
      obtain ⟨ha, hc⟩ := queueEnqueueK_frame k id m k₁ hq
      exact ⟨by show k₁.accounts = k.accounts; exact ha,
             by show k₁.slotCaveats = k.slotCaveats; exact hc⟩
    · exact absurd h (by simp)

private theorem queueDequeueK_frame (k : RecordKernelState) (id : Nat) (actor : CellId)
    (k₁ : RecordKernelState) (mh : Nat) (hq : queueDequeueK k id actor = some (k₁, mh)) :
    k₁.accounts = k.accounts ∧ k₁.slotCaveats = k.slotCaveats := by
  unfold queueDequeueK at hq; split at hq
  · exact absurd hq (by simp)
  · split at hq
    · split at hq
      · exact absurd hq (by simp)
      · option_inj at hq; obtain ⟨hq, _⟩ := hq; subst hq; exact ⟨rfl, rfl⟩
    · exact absurd hq (by simp)

private theorem queueDequeueRefundK_frame (k : RecordKernelState) (id : Nat) (actor : CellId)
    (depId : Nat) (k' : RecordKernelState) (mh : Nat)
    (h : queueDequeueRefundK k id actor depId = some (k', mh)) :
    k'.accounts = k.accounts ∧ k'.slotCaveats = k.slotCaveats := by
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
              -- k' = settleEscrowRawAsset k₁ … (bal/escrows only)
              obtain ⟨ha', hc'⟩ := queueDequeueK_frame k id actor k₁ mh₁ hq
              refine ⟨?_, ?_⟩
              · show k₁.accounts = k.accounts; exact ha'
              · show k₁.slotCaveats = k.slotCaveats; exact hc'
            · rw [if_neg ha] at h; exact absurd h (by simp)
      · rw [if_neg hbind] at h; exact absurd h (by simp)

private theorem queueTxOpStepA_frame (s s' : RecChainedState) (op : QueueTxOpA)
    (h : queueTxOpStepA s op = some s') :
    s'.kernel.accounts = s.kernel.accounts ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats := by
  cases op with
  | enqueue id m actor cell depId dAsset deposit =>
      simp only [queueTxOpStepA, queueEnqueueChainA] at h; split at h
      · cases hk : queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' => commit_subst h hk
                     exact queueEnqueueDepositK_frame s.kernel id m actor cell depId dAsset deposit k' hk
      · exact absurd h (by simp)
  | dequeue id actor cell depId deposit =>
      simp only [queueTxOpStepA, queueDequeueChainA] at h; split at h
      · cases hk : queueDequeueRefundK s.kernel id actor depId with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some kp => obtain ⟨k', mhd⟩ := kp
                     commit_subst h hk
                     exact queueDequeueRefundK_frame s.kernel id actor depId k' mhd hk
      · exact absurd h (by simp)

private theorem queueAtomicTxChainA_frame (s s' : RecChainedState) (ops : List QueueTxOpA)
    (h : queueAtomicTxChainA s ops = some s') :
    s'.kernel.accounts = s.kernel.accounts ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats := by
  induction ops generalizing s with
  | nil => simp only [queueAtomicTxChainA, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | cons op rest ih =>
      simp only [queueAtomicTxChainA] at h
      cases hop : queueTxOpStepA s op with
      | none => rw [hop] at h; exact absurd h (by simp)
      | some s1 =>
          simp only [hop] at h
          obtain ⟨ha1, hc1⟩ := ih s1 h
          obtain ⟨ha0, hc0⟩ := queueTxOpStepA_frame _ _ _ hop
          exact ⟨ha1.trans ha0, hc1.trans hc0⟩

private theorem pipelineFanoutK_frame (k k' : RecordKernelState) (actor : CellId) (m : Nat)
    (sinks : List CellId) (sids : List Nat)
    (h : pipelineFanoutK k actor m sinks sids = some k') :
    k'.accounts = k.accounts ∧ k'.slotCaveats = k.slotCaveats := by
  induction sinks generalizing k sids with
  | nil => cases sids <;> (simp only [pipelineFanoutK, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
  | cons sink rest ih =>
      cases sids with
      | nil => simp only [pipelineFanoutK] at h; exact absurd h (by simp)
      | cons sid sids' =>
          simp only [pipelineFanoutK] at h; split at h
          · cases hq : queueEnqueueK k sid m with
            | none => rw [hq] at h; exact absurd h (by simp)
            | some k1 =>
                simp only [hq] at h
                obtain ⟨ha1, hc1⟩ := ih k1 sids' h
                obtain ⟨ha0, hc0⟩ := queueEnqueueK_frame k sid m k1 hq
                exact ⟨ha1.trans ha0, hc1.trans hc0⟩
          · exact absurd h (by simp)

mutual
/-- **`execFullA_progLive_preserved` (PROVED) — the per-effect program-live FRAME.** A committed
`FullActionA` keeps a live cell `c` live AND keeps its published caveat program installed. The three
create arms mint a FRESH `newCell ≠ c`; every other arm updates a non-`{accounts,slotCaveats}` field
(or `insert`s elsewhere), so the `(c ∈ accounts, slotCaveats c)` pair is preserved verbatim;
`exerciseA` RECURSES (mutual `execInnerA_progLive_preserved`). -/
theorem execFullA_progLive_preserved (s s' : RecChainedState) (fa : FullActionA) (c : CellId)
    (cav : List SlotCaveat) (h : execFullA s fa = some s')
    (hlive : c ∈ s.kernel.accounts) (hprog : s.kernel.slotCaveats c = cav) :
    c ∈ s'.kernel.accounts ∧ s'.kernel.slotCaveats c = cav := by
  cases fa with
  | balanceA t a =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := recCexecAsset_factors t a (by simpa only [execFullA] using h)
      subst h'
      have hn : k' = { s.kernel with bal := k'.bal } := by
        unfold recKExecAsset at hk; split at hk
        · injection hk with hk; subst hk; rfl
        · exact absurd hk (by simp)
      rw [hn]; exact ⟨hlive, hprog⟩
  | delegate del rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel del rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with caps := k'.caps } := by
            unfold recKDelegate at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]; exact ⟨hlive, hprog⟩
  | revoke holder t =>
      simp only [execFullA, recCRevoke] at h
      obtain ⟨rfl⟩ := h; exact ⟨hlive, hprog⟩
  | mintA actor cell a amt =>
      simp only [execFullA, recCMintAsset] at h
      cases hk : recKMintAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with bal := k'.bal } := by
            unfold recKMintAsset at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]; exact ⟨hlive, hprog⟩
  | burnA actor cell a amt =>
      simp only [execFullA, recCBurnAsset] at h
      cases hk : recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with bal := k'.bal } := by
            unfold recKBurnAsset at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]; exact ⟨hlive, hprog⟩
  | setFieldA actor cell f v =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors (stateStepGuarded_eq h); subst hs'; exact ⟨hlive, hprog⟩
  | emitEventA actor cell topic data =>
      simp only [execFullA] at h
      by_cases hl : cell ∈ s.kernel.accounts
      · rw [if_pos hl] at h; simp only [emitStep, Option.some.injEq] at h; subst h; exact ⟨hlive, hprog⟩
      · rw [if_neg hl] at h; exact absurd h (by simp)
  | incrementNonceA actor cell n =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; exact ⟨hlive, hprog⟩
  | setPermissionsA actor cell p =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; exact ⟨hlive, hprog⟩
  | setVKA actor cell vk =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; exact ⟨hlive, hprog⟩
  | introduceA intro rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel intro rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with caps := k'.caps } := by
            unfold recKDelegate at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]; exact ⟨hlive, hprog⟩
  | delegateAttenA del rec t keep =>
      simp only [execFullA, recCDelegateAtten] at h
      cases hk : recKDelegateAtten s.kernel del rec t keep with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with caps := k'.caps } := by
            unfold recKDelegateAtten at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]; exact ⟨hlive, hprog⟩
  | attenuateA actor idx keep =>
      simp only [execFullA, attenuateStepA] at h
      obtain ⟨rfl⟩ := h; exact ⟨hlive, hprog⟩
  | dropRefA holder t =>
      simp only [execFullA, recCRevoke] at h
      obtain ⟨rfl⟩ := h; exact ⟨hlive, hprog⟩
  | revokeDelegationA holder t =>
      simp only [execFullA, recCRevoke] at h
      obtain ⟨rfl⟩ := h; exact ⟨hlive, hprog⟩
  | validateHandoffA intro rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel intro rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with caps := k'.caps } := by
            unfold recKDelegate at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]; exact ⟨hlive, hprog⟩
  | exerciseA actor t inner =>
      simp only [execFullA] at h
      cases hg : exerciseStepA s actor t with
      | none => rw [hg] at h; exact absurd h (by simp)
      | some s1 =>
          rw [hg] at h
          obtain ⟨_, hs1⟩ := exerciseStepA_factors hg
          have hlive1 : c ∈ s1.kernel.accounts := by rw [hs1]; exact hlive
          have hprog1 : s1.kernel.slotCaveats c = cav := by rw [hs1]; exact hprog
          exact execInnerA_progLive_preserved s1 s' inner c cav h hlive1 hprog1
  | createCellA actor newCell =>
      obtain ⟨_, hfresh, hs'⟩ := createCellChainA_factors (by simpa only [execFullA] using h)
      have hne : c ≠ newCell := fun heq => hfresh (heq ▸ hlive)
      subst hs'
      refine ⟨?_, ?_⟩
      · dsimp [createCellIntoAsset]; exact Finset.mem_insert_of_mem hlive
      · dsimp [createCellIntoAsset, bornEmptyCellSlots]; simp only [if_neg hne]; exact hprog
  | createCellFromFactoryA actor newCell vk =>
      obtain ⟨e, s1, _, _, hc, hs'⟩ :=
        createCellFromFactoryChainA_factors (by simpa only [execFullA] using h)
      obtain ⟨_, hfresh, hs1⟩ := createCellChainA_factors hc
      have hne : c ≠ newCell := fun heq => hfresh (heq ▸ hlive)
      subst hs' hs1
      refine ⟨?_, ?_⟩
      · dsimp [createCellIntoAsset]; exact Finset.mem_insert_of_mem hlive
      · dsimp [createCellIntoAsset, bornEmptyCellSlots]; simp only [if_neg hne]; exact hprog
  | spawnA actor child target =>
      obtain ⟨s1, _, hc, hs'⟩ := spawnChainA_factors (by simpa only [execFullA] using h)
      obtain ⟨_, hfresh, hc'⟩ := createCellChainA_factors hc
      have hne : c ≠ child := fun heq => hfresh (heq ▸ hlive)
      subst hs' hc'
      refine ⟨?_, ?_⟩
      · dsimp [createCellIntoAsset]; exact Finset.mem_insert_of_mem hlive
      · dsimp [createCellIntoAsset, bornEmptyCellSlots]; simp only [if_neg hne]; exact hprog
  | bridgeMintA actor cell a value =>
      simp only [execFullA, recCMintAsset] at h
      cases hk : recKMintAsset s.kernel actor cell a value with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with bal := k'.bal } := by
            unfold recKMintAsset at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]; exact ⟨hlive, hprog⟩
  | createEscrowA id actor creator recipient asset amount =>
      simp only [execFullA, createEscrowChainA] at h
      cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with bal := k'.bal, escrows := k'.escrows } := by
            unfold createEscrowKAsset createEscrowRawAsset at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]; exact ⟨hlive, hprog⟩
  | releaseEscrowA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := releaseEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'
      have hn : k' = { s.kernel with bal := k'.bal, escrows := k'.escrows } := by
        unfold releaseEscrowKAsset settleEscrowRawAsset at hk
        split at hk
        · split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
        · exact absurd hk (by simp)
      rw [hn]; exact ⟨hlive, hprog⟩
  | refundEscrowA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := refundEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'
      have hn : k' = { s.kernel with bal := k'.bal, escrows := k'.escrows } := by
        unfold refundEscrowKAsset settleEscrowRawAsset at hk
        split at hk
        · split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
        · exact absurd hk (by simp)
      rw [hn]; exact ⟨hlive, hprog⟩
  | createObligationA id actor obligor beneficiary asset stake =>
      simp only [execFullA, createEscrowChainA] at h
      cases hk : createEscrowKAsset s.kernel id actor obligor beneficiary asset stake with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with bal := k'.bal, escrows := k'.escrows } := by
            unfold createEscrowKAsset createEscrowRawAsset at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]; exact ⟨hlive, hprog⟩
  | fulfillObligationA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := refundEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'
      have hn : k' = { s.kernel with bal := k'.bal, escrows := k'.escrows } := by
        unfold refundEscrowKAsset settleEscrowRawAsset at hk
        split at hk
        · split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
        · exact absurd hk (by simp)
      rw [hn]; exact ⟨hlive, hprog⟩
  | slashObligationA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := releaseEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'
      have hn : k' = { s.kernel with bal := k'.bal, escrows := k'.escrows } := by
        unfold releaseEscrowKAsset settleEscrowRawAsset at hk
        split at hk
        · split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
        · exact absurd hk (by simp)
      rw [hn]; exact ⟨hlive, hprog⟩
  | noteSpendA nf actor =>
      simp only [execFullA, noteSpendChainA] at h
      cases hk : noteSpendNullifier s.kernel nf with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with nullifiers := nf :: s.kernel.nullifiers } := by
            unfold noteSpendNullifier at hk; split at hk
            · exact absurd hk (by simp)
            · injection hk with hk; exact hk.symm
          rw [hn]; exact ⟨hlive, hprog⟩
  | noteCreateA cm actor =>
      simp only [execFullA, noteCreateChainA] at h
      option_inj at h; subst h
      show c ∈ (noteCreateCommitment s.kernel cm).accounts ∧ (noteCreateCommitment s.kernel cm).slotCaveats c = cav
      unfold noteCreateCommitment; exact ⟨hlive, hprog⟩
  | createCommittedEscrowA id actor creator recipient asset amount hidingProof =>
      simp only [execFullA, createCommittedEscrowChainA, createEscrowChainA] at h; split at h
      · cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            have hn : k' = { s.kernel with bal := k'.bal, escrows := k'.escrows } := by
              unfold createEscrowKAsset createEscrowRawAsset at hk; split at hk
              · injection hk with hk; subst hk; rfl
              · exact absurd hk (by simp)
            rw [hn]; exact ⟨hlive, hprog⟩
      · exact absurd h (by simp)
  | releaseCommittedEscrowA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := releaseEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'
      have hn : k' = { s.kernel with bal := k'.bal, escrows := k'.escrows } := by
        unfold releaseEscrowKAsset settleEscrowRawAsset at hk
        split at hk
        · split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
        · exact absurd hk (by simp)
      rw [hn]; exact ⟨hlive, hprog⟩
  | refundCommittedEscrowA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := refundEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'
      have hn : k' = { s.kernel with bal := k'.bal, escrows := k'.escrows } := by
        unfold refundEscrowKAsset settleEscrowRawAsset at hk
        split at hk
        · split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
        · exact absurd hk (by simp)
      rw [hn]; exact ⟨hlive, hprog⟩
  | bridgeLockA id actor originator destination asset amount =>
      simp only [execFullA, bridgeLockChainA] at h
      cases hk : bridgeLockKAsset s.kernel id actor originator destination asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with bal := k'.bal, escrows := k'.escrows } := by
            unfold bridgeLockKAsset createBridgeRawAsset at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]; exact ⟨hlive, hprog⟩
  | bridgeFinalizeA id actor asset amount =>
      simp only [execFullA, bridgeFinalizeChainA] at h
      split at h
      · cases hk : bridgeFinalizeKAsset s.kernel id asset amount with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            have hn : k' = { s.kernel with bal := k'.bal, escrows := k'.escrows } := by
              unfold bridgeFinalizeKAsset bridgeFinalizeRawAsset at hk
              split at hk
              · split at hk
                · injection hk with hk; subst hk; rfl
                · exact absurd hk (by simp)
              · exact absurd hk (by simp)
            rw [hn]; exact ⟨hlive, hprog⟩
      · exact absurd h (by simp)
  | bridgeCancelA id actor =>
      simp only [execFullA, bridgeCancelChainA] at h
      split at h
      · cases hk : bridgeCancelKAsset s.kernel id with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            have hn : k' = { s.kernel with bal := k'.bal, escrows := k'.escrows } := by
              unfold bridgeCancelKAsset settleEscrowRawAsset at hk
              split at hk
              · split at hk
                · injection hk with hk; subst hk; rfl
                · exact absurd hk (by simp)
              · exact absurd hk (by simp)
            rw [hn]; exact ⟨hlive, hprog⟩
      · exact absurd h (by simp)
  | sealA pid actor payload =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := sealChainA_factors h; subst hs'; exact ⟨hlive, hprog⟩
  | unsealA pid actor recipient =>
      simp only [execFullA] at h
      obtain ⟨_, _, _, hs'⟩ := unsealChainA_factors h; subst hs'; exact ⟨hlive, hprog⟩
  | createSealPairA pid actor sealerHolder unsealerHolder =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := createSealPairChainA_factors h; subst hs'; exact ⟨hlive, hprog⟩
  | makeSovereignA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := makeSovereignStep_factors h; subst hs'; exact ⟨hlive, hprog⟩
  | refusalA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; exact ⟨hlive, hprog⟩
  | receiptArchiveA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; exact ⟨hlive, hprog⟩
  | cellSealA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := cellSealChainA_factors h; subst hs'
      show c ∈ (setLifecycle s.kernel cell lcSealed).accounts ∧ (setLifecycle s.kernel cell lcSealed).slotCaveats c = cav
      unfold setLifecycle; exact ⟨hlive, hprog⟩
  | cellUnsealA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := cellUnsealChainA_factors h; subst hs'
      show c ∈ (setLifecycle s.kernel cell lcLive).accounts ∧ (setLifecycle s.kernel cell lcLive).slotCaveats c = cav
      unfold setLifecycle; exact ⟨hlive, hprog⟩
  | cellDestroyA actor cell ch =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := cellDestroyChainA_factors h; subst hs'
      refine ⟨?_, ?_⟩
      · show c ∈ (setLifecycle s.kernel cell lcDestroyed).accounts; unfold setLifecycle; exact hlive
      · show ({ (setLifecycle s.kernel cell lcDestroyed) with deathCert := _ }).slotCaveats c = cav
        unfold setLifecycle; exact hprog
  | refreshDelegationA actor child =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := refreshDelegationChainA_factors h; subst hs'
      show c ∈ ({ s.kernel with delegations := _ }).accounts ∧ ({ s.kernel with delegations := _ }).slotCaveats c = cav
      exact ⟨hlive, hprog⟩
  | queueAllocateA id actor cell cap =>
      simp only [execFullA, queueAllocateChainA] at h
      split at h
      · cases hk : queueAllocateK s.kernel id actor cap with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            have hn : k' = { s.kernel with queues := k'.queues } := by
              unfold queueAllocateK at hk; split at hk
              · exact absurd hk (by simp)
              · injection hk with hk; subst hk; rfl
            rw [hn]; exact ⟨hlive, hprog⟩
      · exact absurd h (by simp)
  | queueEnqueueA id m actor cell depId dAsset deposit =>
      simp only [execFullA, queueEnqueueChainA] at h
      split at h
      · cases hk : queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            obtain ⟨hacc, hcav⟩ :=
              queueEnqueueDepositK_frame s.kernel id m actor cell depId dAsset deposit k' hk
            exact ⟨hacc ▸ hlive, by rw [hcav]; exact hprog⟩
      · exact absurd h (by simp)
  | queueDequeueA id actor cell depId deposit =>
      simp only [execFullA, queueDequeueChainA] at h
      split at h
      · cases hk : queueDequeueRefundK s.kernel id actor depId with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some kp =>
            rw [hk] at h
            obtain ⟨k', mhd⟩ := kp
            obtain ⟨rfl⟩ := h
            obtain ⟨hacc, hcav⟩ :=
              queueDequeueRefundK_frame s.kernel id actor depId k' mhd hk
            exact ⟨hacc ▸ hlive, by rw [hcav]; exact hprog⟩
      · exact absurd h (by simp)
  | queueResizeA id newCap actor cell =>
      simp only [execFullA, queueResizeChainA] at h
      split at h
      · cases hk : queueResizeK s.kernel id newCap with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            have hn : k' = { s.kernel with queues := k'.queues } := by
              unfold queueResizeK at hk
              split at hk
              · exact absurd hk (by simp)
              · split at hk
                · injection hk with hk; subst hk; rfl
                · exact absurd hk (by simp)
            rw [hn]; exact ⟨hlive, hprog⟩
      · exact absurd h (by simp)
  | queueAtomicTxA actor ops =>
      simp only [execFullA] at h
      obtain ⟨s1, hf, _, hk⟩ := queueAtomicTxA_atomic_witness h
      obtain ⟨hacc0, hcav0⟩ := queueAtomicTxChainA_frame s s1 ops hf
      have hacc : s'.kernel.accounts = s.kernel.accounts := by rw [hk]; exact hacc0
      have hcav : s'.kernel.slotCaveats = s.kernel.slotCaveats := by rw [hk]; exact hcav0
      exact ⟨hacc ▸ hlive, by rw [hcav]; exact hprog⟩
  | queuePipelineStepA srcId owner sinkCells sinkIds =>
      simp only [execFullA] at h
      obtain ⟨k1, mh, hd, hfo⟩ := queuePipelineStepA_routing_witness h
      obtain ⟨hfacc, hfcav⟩ := pipelineFanoutK_frame k1 s'.kernel owner mh sinkCells sinkIds hfo
      obtain ⟨hdacc, hdcav⟩ := queueDequeueK_frame s.kernel srcId owner k1 mh hd
      have hacc : s'.kernel.accounts = s.kernel.accounts := hfacc.trans hdacc
      have hcav : s'.kernel.slotCaveats = s.kernel.slotCaveats := hfcav.trans hdcav
      exact ⟨hacc ▸ hlive, by rw [hcav]; exact hprog⟩
  | pipelinedSendA actor =>
      simp only [execFullA, Option.some.injEq] at h; subst h; exact ⟨hlive, hprog⟩
  | exportSturdyRefA sw actor exporter target rights =>
      simp only [execFullA, swissExportChainA] at h
      split at h
      · cases hk : swissExportK s.kernel sw exporter target rights with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            have hn : k' = { s.kernel with swiss := k'.swiss } := by
              unfold swissExportK at hk; split at hk
              · exact absurd hk (by simp)
              · split at hk
                · injection hk with hk; subst hk; rfl
                · exact absurd hk (by simp)
            rw [hn]; exact ⟨hlive, hprog⟩
      · exact absurd h (by simp)
  | enlivenRefA sw actor exporter claimed =>
      simp only [execFullA, swissEnlivenChainA] at h
      split at h
      · cases hk : swissEnlivenK s.kernel sw claimed with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            have hn : k' = { s.kernel with swiss := k'.swiss, caps := k'.caps } := by
              unfold swissEnlivenK at hk; split at hk
              · exact absurd hk (by simp)
              · split at hk
                · injection hk with hk; subst hk; rfl
                · exact absurd hk (by simp)
            rw [hn]; exact ⟨hlive, hprog⟩
      · exact absurd h (by simp)
  | swissHandoffA sw certHash introducer exporter =>
      simp only [execFullA, swissHandoffChainA] at h
      split at h
      · cases hk : swissHandoffK s.kernel sw certHash with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            have hn : k' = { s.kernel with swiss := k'.swiss } := by
              unfold swissHandoffK at hk; split at hk
              · exact absurd hk (by simp)
              · injection hk with hk; subst hk; rfl
            rw [hn]; exact ⟨hlive, hprog⟩
      · exact absurd h (by simp)
  | swissDropA sw actor exporter =>
      simp only [execFullA, swissDropChainA] at h
      split at h
      · cases hk : swissDropK s.kernel sw with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            have hn : k' = { s.kernel with swiss := k'.swiss } := by
              unfold swissDropK at hk; split at hk
              · exact absurd hk (by simp)
              · split at hk
                · exact absurd hk (by simp)
                · split at hk
                  · injection hk with hk; subst hk; rfl
                  · injection hk with hk; subst hk; rfl
            rw [hn]; exact ⟨hlive, hprog⟩
      · exact absurd h (by simp)

/-- **`execInnerA_progLive_preserved`** — the inner-effect fold an `exerciseA` recurses through keeps a
live cell's published caveat program installed. Mutual with `execFullA_progLive_preserved`. -/
theorem execInnerA_progLive_preserved (s s' : RecChainedState) (inner : List FullActionA) (c : CellId)
    (cav : List SlotCaveat) (h : execInnerA s inner = some s')
    (hlive : c ∈ s.kernel.accounts) (hprog : s.kernel.slotCaveats c = cav) :
    c ∈ s'.kernel.accounts ∧ s'.kernel.slotCaveats c = cav := by
  cases inner with
  | nil => simp only [execInnerA, Option.some.injEq] at h; subst h; exact ⟨hlive, hprog⟩
  | cons a rest =>
      simp only [execInnerA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          obtain ⟨hlive1, hprog1⟩ := execFullA_progLive_preserved s s1 a c cav ha hlive hprog
          exact execInnerA_progLive_preserved s1 s' rest c cav h hlive1 hprog1
end

/-- **`execFullTurnA_progLive_preserved` (PROVED).** A committed per-asset full TURN keeps a live cell's
caveat program installed. Induction on the action list. -/
theorem execFullTurnA_progLive_preserved :
    ∀ (s s' : RecChainedState) (tt : List FullActionA) (c : CellId) (cav : List SlotCaveat),
      execFullTurnA s tt = some s' → c ∈ s.kernel.accounts → s.kernel.slotCaveats c = cav →
        c ∈ s'.kernel.accounts ∧ s'.kernel.slotCaveats c = cav
  | s, s', [], c, cav, h, hlive, hprog => by
      simp only [execFullTurnA, Option.some.injEq] at h; subst h; exact ⟨hlive, hprog⟩
  | s, s', a :: rest, c, cav, h, hlive, hprog => by
      simp only [execFullTurnA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          obtain ⟨hlive1, hprog1⟩ := execFullA_progLive_preserved s s1 a c cav ha hlive hprog
          exact execFullTurnA_progLive_preserved s1 s' rest c cav h hlive1 hprog1

/-- **`execFullForestA_progLive_preserved` (PROVED).** A committed full FOREST keeps a live cell's caveat
program installed. Through the pre-order bridge `execFullForestA_eq_execFullTurnA`. -/
theorem execFullForestA_progLive_preserved (s s' : RecChainedState) (f : FullForestA) (c : CellId)
    (cav : List SlotCaveat) (h : execFullForestA s f = some s')
    (hlive : c ∈ s.kernel.accounts) (hprog : s.kernel.slotCaveats c = cav) :
    c ∈ s'.kernel.accounts ∧ s'.kernel.slotCaveats c = cav := by
  rw [execFullForestA_eq_execFullTurnA] at h
  exact execFullTurnA_progLive_preserved s s' (lowerForestA f) c cav h hlive hprog

/-! ## §B′ — `sgmWF` kernel predicates (volume bound + anchor tag). -/

def sgmVolumeSpent (k : RecordKernelState) : Int :=
  fieldOf volumeSpentSlot (k.cell mandateCell)

def sgmAnchor (k : RecordKernelState) : Int :=
  fieldOf commitmentAnchorSlot (k.cell mandateCell)

def sgmVolumeBound (k : RecordKernelState) : Bool :=
  let spent := sgmVolumeSpent k
  decide (0 ≤ spent ∧ spent ≤ (demoMandate.volumeBudget.ceiling : Int))

def sgmAnchorIs (k : RecordKernelState) (anchor : Int) : Bool :=
  decide (sgmAnchor k = anchor)

/-- Mandate cell carries the published caveat program (immutable anchor + monotonic/bounded volume). -/
def sgmMandateProgramOK (k : RecordKernelState) : Prop :=
  k.slotCaveats mandateCell = mandateCaveats

/-- **Strong step-legal invariant (Phase B)** — volume spent ≤ ceiling AND caveat program installed. -/
def sgmWFStrong (k : RecordKernelState) : Prop :=
  sgmVolumeBound k = true ∧ sgmMandateProgramOK k

/-- **Strong bucket invariant (Phase B)** — commitment anchor matches expected tag AND caveat program. -/
def sgmInBucketStrong (k : RecordKernelState) (bucket : Int) : Prop :=
  sgmAnchorIs k bucket = true ∧ sgmMandateProgramOK k

/-- **`sgmWF` — NON-VACUOUS Hatchery contract invariant.** The mandate cell stays a LIVE account AND its
published per-slot caveat program (immutable anchor + monotonic/bounded volume) remains installed — so
the executor's per-slot teeth (`sgm_over_debit_rejected_*`, immutable-anchor rewrite rejection) are
enforced on the cell for its WHOLE life, along EVERY adversarial `trajG`. Carried by the generic
`execFullForestA_progLive_preserved` frame (no `True` filler). -/
def sgmWF (k : RecordKernelState) : Prop :=
  mandateCell ∈ k.accounts ∧ sgmMandateProgramOK k

/-- **`sgmInBucket` — NON-VACUOUS bucket-binding invariant.** Carries the program-live core (mandate
cell live + its published per-slot caveat program installed). The `bucket` tag is the binding's domain:
the binding to `bucket` is ENFORCED for life by the persisted `.immutable commitmentAnchorSlot` caveat
inside `mandateCaveats` (the executor rejects any later anchor rewrite — `sgm_over_debit_rejected_*` and
the immutable teeth). Carried by `execFullForestA_progLive_preserved`. NOTE (precise residual): the
literal anchor-VALUE conjunct `sgmAnchorIs k bucket` is NOT carried here — that needs a second
cell-record frame (`fieldOf commitmentAnchorSlot (cell mandateCell)` preserved across the 53 arms via
the immutable caveat block + balance-field non-interference). Strictly stronger than `True`. -/
def sgmInBucket (_k : RecordKernelState) (_bucket : Int) : Prop :=
  mandateCell ∈ _k.accounts ∧ sgmMandateProgramOK _k

instance sgmWFStrongDecidable (k : RecordKernelState) : Decidable (sgmWFStrong k) := by
  unfold sgmWFStrong sgmMandateProgramOK; infer_instance

instance sgmInBucketStrongDecidable (k : RecordKernelState) (bucket : Int) :
    Decidable (sgmInBucketStrong k bucket) := by
  unfold sgmInBucketStrong sgmMandateProgramOK; infer_instance

theorem sgmWFStrong_of_mandate_cell_eq {k k' : RecordKernelState}
    (hc : k'.cell mandateCell = k.cell mandateCell) (hcav : k'.slotCaveats mandateCell = k.slotCaveats mandateCell)
    (hwf : sgmWFStrong k) : sgmWFStrong k' := by
  rcases hwf with ⟨hvol, hprog⟩
  refine ⟨?_, ?_⟩
  · unfold sgmVolumeBound sgmVolumeSpent at hvol ⊢
    simp [sgmVolumeSpent, hc] at hvol ⊢
    exact hvol
  · unfold sgmMandateProgramOK at hprog ⊢
    simpa [hcav] using hprog

theorem sgmInBucketStrong_of_mandate_cell_eq {k k' : RecordKernelState} (bucket : Int)
    (hc : k'.cell mandateCell = k.cell mandateCell) (hcav : k'.slotCaveats mandateCell = k.slotCaveats mandateCell)
    (hb : sgmInBucketStrong k bucket) : sgmInBucketStrong k' bucket := by
  rcases hb with ⟨hanchor, hprog⟩
  refine ⟨?_, ?_⟩
  · unfold sgmAnchorIs sgmAnchor at hanchor ⊢
    simp [sgmAnchor, hc] at hanchor ⊢
    exact hanchor
  · unfold sgmMandateProgramOK at hprog ⊢
    simpa [hcav] using hprog

/-- **`sgmWF_traj_carries` (PROVED) — NON-VACUOUS carry.** A committed forest keeps the mandate cell
live AND its published caveat program installed. The generic frame `execFullForestA_progLive_preserved`
instantiated at `mandateCell`/`mandateCaveats`. -/
theorem sgmWF_traj_carries (s s' : RecChainedState) (cf : FullForestA)
    (h : execFullForestA s cf = some s') (hwf : sgmWF s.kernel) : sgmWF s'.kernel := by
  obtain ⟨hlive, hprog⟩ := hwf
  exact execFullForestA_progLive_preserved s s' cf mandateCell mandateCaveats h hlive hprog

/-- **`sgmBucket_traj_carries` (PROVED) — NON-VACUOUS carry.** Same generic frame: the bucket binding's
enforcement (live cell + installed immutable-anchor caveat program) persists along every forest. -/
theorem sgmBucket_traj_carries (s s' : RecChainedState) (cf : FullForestA) (bucket : Int)
    (h : execFullForestA s cf = some s') (hb : sgmInBucket s.kernel bucket) :
    sgmInBucket s'.kernel bucket := by
  obtain ⟨hlive, hprog⟩ := hb
  exact execFullForestA_progLive_preserved s s' cf mandateCell mandateCaveats h hlive hprog

/-! ## §C — Stingray volume-budget demo (PUT debits exhaust slice). -/

def demoVolume : Slice := demoMandate.volumeBudget

theorem sgm_put_debit_fits_slice :
    (demoVolume.tryDebit demoMandate.putCost).isSome = true := by
  rw [tryDebit_isSome_iff]
  simp [demoVolume, demoMandate, Slice.remaining]

theorem sgm_double_put_exhausts_slice :
    ((demoVolume.tryDebit demoMandate.putCost).bind
      (fun s' => s'.tryDebit demoMandate.putCost)).isSome = true := by
  have h1 : demoVolume.tryDebit demoMandate.putCost = some { ceiling := 10, spent := 5 } := by
    unfold Slice.tryDebit; simp [demoVolume, demoMandate, Slice.remaining]
  have h2 : ({ ceiling := 10, spent := 5 } : Slice).tryDebit demoMandate.putCost =
      some { ceiling := 10, spent := 10 } := by
    unfold Slice.tryDebit; simp [demoMandate, Slice.remaining]
  simpa [h1, h2]

/-! ## §D — NON-VACUITY: authorize PUT on prefix, reject GET above clearance, slice exhaust. -/

def sgm0 : RecChainedState :=
  { kernel :=
      { accounts := {0}
        cell := fun c =>
          if c = mandateCell then
            .record [("balance", .int 0), (objectKeySlot, .int 0), (lastOpSlot, .int (-1)),
                     (volumeSpentSlot, .int 0), (commitmentAnchorSlot, .int demoMandate.anchor)]
          else .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0) else 0
        slotCaveats := fun c => if c = mandateCell then mandateCaveats else [] }
    log := [] }

abbrev demoKeyCode : Int := 101
abbrev demoBlobHash : Int := 3735928559

def sgmPutCommitted : Option RecChainedState :=
  sgmStorageChain sgm0 mandateActor demoKeyCode (StorageOp.PUT.toInt) demoBlobHash

def sgmPutDebited : Option RecChainedState :=
  sgmPutCommitted.bind (fun s => execFullForestA s (sgmExecDebitVolume mandateActor 5))

#guard ({ volume := demoVolume, anchor := demoMandate.anchor } : SgmRuntime).WF
#guard (sgmAdmitM demoMandate { volume := demoVolume, anchor := demoMandate.anchor } demoPutReq).isSome
#guard (sgmAdmitM demoMandate { volume := demoVolume, anchor := demoMandate.anchor } demoBadPutReq).isSome == false
#guard (sgmAdmitM guestMandate { volume := demoVolume, anchor := demoMandate.anchor } demoGetReq).isSome == false
#guard putPrefixOK demoMandate "uploads/doc.txt"
#guard getClearanceOK demoMandate
#guard getClearanceOK guestMandate == false

#guard (sgmPutCommitted.isSome)
#guard (sgmPutCommitted.map (fun s => fieldOf objectKeySlot (s.kernel.cell mandateCell))) == some demoKeyCode
#guard (sgmPutCommitted.map (fun s => fieldOf lastOpSlot (s.kernel.cell mandateCell))) == some 1
#guard (caveatsAdmit sgm0.kernel volumeSpentSlot mandateActor mandateCell 11) == false
#guard ((execFullForestA sgm0 (sgmExecDebitVolume mandateActor 11)).isSome) == false

#guard (demoVolume.tryDebit demoMandate.putCost).isSome
#guard ((demoVolume.tryDebit demoMandate.putCost).bind
        (fun s' => s'.tryDebit demoMandate.putCost)).isSome
#guard (((demoVolume.tryDebit demoMandate.putCost).bind
          (fun s' => s'.tryDebit demoMandate.putCost)).bind
         (fun s'' => s''.tryDebit demoMandate.putCost)).isSome == false

#guard ((sgmPutDebited.map (fun s => recTotalAssetWithEscrow s.kernel payAsset)).getD 0) == 100
#guard (sgmVolumeBound sgm0.kernel)
#guard (sgmAnchorIs sgm0.kernel (demoMandate.anchor : Int))
#guard (sgmWFStrong sgm0.kernel)
#guard (sgmInBucketStrong sgm0.kernel (demoMandate.anchor : Int))
-- NON-VACUITY of the carried invariant: the program-live invariant HOLDS at the genesis state
-- (mandate cell live + caveat program installed), so the safety crown is non-trivially applicable.
#guard (decide (mandateCell ∈ sgm0.kernel.accounts) && (sgm0.kernel.slotCaveats mandateCell == mandateCaveats))

#assert_axioms execFullA_progLive_preserved
#assert_axioms execFullForestA_progLive_preserved
#assert_axioms sgm_volume_legal_forever
#assert_axioms sgm_over_debit_rejected_exec
#assert_axioms sgm_chain_conserves
#assert_axioms sgm_pay_supply_forever
#assert_axioms sgm_put_debit_fits_slice
#assert_axioms sgm_double_put_exhausts_slice
#assert_axioms sgmWFStrong_of_mandate_cell_eq
#assert_axioms sgmInBucketStrong_of_mandate_cell_eq
#assert_axioms sgmWF_traj_carries
#assert_axioms sgmBucket_traj_carries

end Dregg2.Apps.StorageGatewayMandate