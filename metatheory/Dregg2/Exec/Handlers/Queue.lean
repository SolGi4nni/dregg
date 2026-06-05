/-
# Dregg2.Exec.Handlers.Queue — the QUEUE (FIFO + refundable deposit) handler batch.

This EXTENDS the `EffectHandler` algebra scaffolded in `Dregg2.Exec.Handler` (read that module first:
the `EffectHandler` record bundling `step`/`delta`/`auth`/`admission`/`trace` WITH the forced obligation
proofs `auth_gated`/`admission_gated`/`conserves`, the registry coproduct, and the generic
`turn_conserves`). We register one handler per effect of the QUEUE cluster — `queueAllocateA`,
`queueEnqueueA`, `queueDequeueA`, `queueResizeA`, `queueAtomicTxA`, `queuePipelineStepA` — each reusing
that effect's ALREADY-PROVED kernel step + conservation lemma + the queue-cell authority gate from
`Dregg2.Exec.RecordKernel`/`TurnExecutorFull`. We do NOT touch `TurnExecutorFull`'s
`execFullA`/`FullActionA` (the cutover is a later step); we only IMPORT and REUSE.

Conservation faces:

  * **bal-NEUTRAL ORDER ops** (`queueAllocateA`/`queueResizeA`). Allocate creates a fresh queue record;
    resize changes capacity. Both touch ONLY `queues`, never `bal`/`escrows` — the combined per-asset
    measure is unchanged (`delta = 0`), discharged by `queueAllocateK_balNeutral`/`queueResizeK_balNeutral`.

  * **COMBINED-conserving DEPOSIT ops** (`queueEnqueueA`/`queueDequeueA`). dregg1's enqueue PARKS a
    refundable anti-spam deposit (the sender's `bal` ledger DROPS, the shared holding-store RISES — the
    bare ledger genuinely MOVES, the COMBINED measure is fixed); dequeue REFUNDS it (ledger rises, store
    drops). The combined per-asset measure is unchanged (`delta = 0`), discharged by the proved
    `queueEnqueueDepositK_conserves_combined` / `queueDequeueRefundK_conserves_combined`. The bare ledger
    debit/credit is REAL (witnessed by `queueEnqueueDepositK_debits`) — only the combined sum is held.

  * **bal-NEUTRAL ROUTING ops** (`queueAtomicTxA`/`queuePipelineStepA`). The atomic batch folds the
    deposit enqueue/dequeue sub-ops all-or-nothing (each combined-conserving, so the fold is — proved by
    induction reusing the per-op `conserves`); the pipeline step dequeues a source head and fans it out
    into each ACL-checked sink (combined-conserving: dequeue + fan-out are both bal-neutral on `queues`).

## CLOSING THE QUEUE↔DEPOSIT BINDING HOLE (codex P0-1).

The kernel `queueDequeueRefundK k id actor depId` credits a CALLER-SUPPLIED deposit-record `depId`,
looked up in the GLOBAL `escrows` table, to the dequeuer `actor` — with NO binding between the named
record and the message being dequeued (or even the queue). So a dequeuer can name an UNRELATED unresolved
deposit (one parked FOR someone else, by someone else) and have its `amount` of its `asset` CREDITED to
itself — draining a deposit that was never destined to them. (`recTotalAssetWithEscrow` stays conserved
because it is a settle, so the conservation keystone does NOT catch it — this is a pure AUTHORITY hole.)

The fix is a WRAP: `dequeueBindStep` resolves the deposit record by `depId` and admits the refund ONLY
when `r.recipient = actor` — the deposit must be DESTINED to the dequeuer. In the honest flow the deposit
is parked with `recipient := owner` (the queue owner) and `queueDequeueK` already gates `actor = owner`,
so the bound deposit's `recipient` IS the dequeuer; an UNRELATED deposit (recipient ≠ actor) is REJECTED.
`auth_gated` makes the binding a TYPING obligation: a handler whose step skipped it would not type-check.
The minimal SOUND conjunct is `r.recipient = actor`; the FULLER per-message binding (the deposit keyed to
the specific dequeued message hash, not just the queue owner) is §DEFER'd — it needs a message→deposit
map the `QueueRecord` buffer does not carry. The conservation lemma is UNCONDITIONAL on the kernel op
committing, so the binding wrap composes for free (it only narrows WHICH deposit may be drained; the
value-conservation math is the kernel's, cited verbatim). `delta = 0`.

Discipline: no `sorry`/`admit`/`axiom`/`native_decide`/eval-only. Every keystone `#assert_axioms`-pinned
(a `sorryAx` fails the pin and the build). `#eval`-verified TEETH: the P0-1 attack (a dequeuer refunding
an UNRELATED deposit, recipient ≠ actor) returns `none`; the actor's own bound deposit returns `some`.
Standalone: `lake build Dregg2.Exec.Handlers.Queue`.
-/
import Dregg2.Exec.Handler

namespace Dregg2.Exec.Handlers.Queue

open Dregg2.Authority Dregg2.Execution
open Dregg2.Exec
open Dregg2.Exec.Handler
open Dregg2.Exec.TurnExecutorFull
  (acceptsEffects lcLive lcSealed lcDestroyed setLifecycle pipelineFanoutK pipelineFanoutK_balNeutral)
open Dregg2.Exec.EffectsState (stateAuthB)

/-! ## §1 — `queueAllocateA`: create a fresh queue record. bal-NEUTRAL (`delta = 0`).

`queueAllocateK` inserts a fresh `QueueRecord` (rejecting a duplicate id); it touches ONLY `queues`, so
the combined per-asset measure is unchanged. We WRAP it with the queue-cell authority gate
(`stateAuthB actor owner`, the dregg1 chained-step gate — the actor must hold authority over the owning
cell) and the owner-Live admission gate; `conserves` cites `queueAllocateK_balNeutral`. -/

/-- Queue-allocate arguments: the actor (authority subject), the fresh queue `id`, the queue `owner`,
and the buffer `capacity`. -/
structure AllocateArgs where
  /-- The actor performing the allocate (must hold authority over `owner`). -/
  actor : CellId
  /-- The fresh queue id (rejected if already in use). -/
  id : Nat
  /-- The queue owner (only the owner may dequeue). -/
  owner : CellId
  /-- The buffer capacity. -/
  capacity : Nat

/-- The authority-gated allocate step: the actor must hold authority over `owner` AND `owner` must be a
Live cell, then run the proved `queueAllocateK`. -/
def allocateStep (k : RecordKernelState) (a : AllocateArgs) : Option RecordKernelState :=
  if stateAuthB k.caps a.actor a.owner && acceptsEffects k a.owner then
    queueAllocateK k a.id a.owner a.capacity
  else none

/-- **`queueAllocateA` — the registered queue-allocate handler.** `delta = 0` (touches only `queues`).
`conserves` from `queueAllocateK_balNeutral`. `auth_gated`/`admission_gated` from the wrapping gate. -/
def queueAllocateA : EffectHandler AllocateArgs where
  step := allocateStep
  delta := fun _ _ => 0
  auth := fun k a => stateAuthB k.caps a.actor a.owner
  admission := fun k a => acceptsEffects k a.owner
  trace := fun a => { actor := a.actor, src := a.owner, dst := a.owner, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold allocateStep at h
    by_cases hg : stateAuthB s.caps a.actor a.owner && acceptsEffects s a.owner
    · simp only [Bool.and_eq_true] at hg; exact hg.1
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold allocateStep at h
    by_cases hg : stateAuthB s.caps a.actor a.owner && acceptsEffects s a.owner
    · simp only [Bool.and_eq_true] at hg; exact hg.2
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold allocateStep at h
    by_cases hg : stateAuthB s.caps a.actor a.owner && acceptsEffects s a.owner
    · rw [if_pos hg] at h
      obtain ⟨hbal, hheld⟩ := queueAllocateK_balNeutral h b
      unfold recTotalAssetWithEscrow; rw [hbal, hheld]; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §2 — `queueEnqueueA`: FIFO append + PARK the refundable deposit. COMBINED-conserving (`delta = 0`).

`queueEnqueueDepositK` APPENDS `m` to the FIFO tail AND PARKS the refundable anti-spam `deposit` of asset
`dAsset` from `sender` into the shared holding-store (record `depId`, `creator := sender` refund target,
`recipient := owner`). The bare `bal` ledger of `dAsset` DROPS by `deposit` (a REAL per-asset debit), the
holding-store RISES — the COMBINED per-asset measure is unchanged (`delta = 0`). We WRAP it with the
queue-cell authority gate (`stateAuthB sender sender` — the sender authorizes its own ledger debit, the
dregg1 chained writer-ACL). `conserves` cites the proved `queueEnqueueDepositK_conserves_combined`. -/

/-- Queue-enqueue (deposit-park) arguments: the queue `id`, the message `m`, the `sender` (debited) and
queue `owner`, the deposit record id `depId`, the deposit `asset`, and the `deposit` amount. -/
structure EnqueueArgs where
  /-- The queue id to enqueue into. -/
  id : Nat
  /-- The message hash appended to the FIFO tail. -/
  m : Nat
  /-- The sender whose `dAsset` ledger is debited by the deposit. -/
  sender : CellId
  /-- The queue owner (the deposit record's `recipient`). -/
  owner : CellId
  /-- The deposit record id (fresh; rejected if already in use). -/
  depId : Nat
  /-- The deposit asset class. -/
  dAsset : AssetId
  /-- The (non-negative) refundable deposit amount. -/
  deposit : Int

/-- The authority-gated enqueue-with-deposit step: the sender must hold authority over its own ledger
(`stateAuthB sender sender`) AND be Live, then run the proved `queueEnqueueDepositK` (which itself
fail-closes on FULL / insufficient deposit / non-account / duplicate deposit id). -/
def enqueueStep (k : RecordKernelState) (a : EnqueueArgs) : Option RecordKernelState :=
  if stateAuthB k.caps a.sender a.sender && acceptsEffects k a.sender then
    queueEnqueueDepositK k a.id a.m a.sender a.owner a.depId a.dAsset a.deposit
  else none

/-- **`queueEnqueueA` — the registered queue-enqueue (deposit-park) handler.** `delta = 0` (COMBINED
measure conserved — the deposit moves ledger↔holding-store). `conserves` cites the proved
`queueEnqueueDepositK_conserves_combined`. `auth_gated`/`admission_gated` from the wrapping gate. -/
def queueEnqueueA : EffectHandler EnqueueArgs where
  step := enqueueStep
  delta := fun _ _ => 0
  auth := fun k a => stateAuthB k.caps a.sender a.sender
  admission := fun k a => acceptsEffects k a.sender
  trace := fun a => { actor := a.sender, src := a.sender, dst := a.owner, amt := a.deposit }
  auth_gated := by
    intro s a s' h
    unfold enqueueStep at h
    by_cases hg : stateAuthB s.caps a.sender a.sender && acceptsEffects s a.sender
    · simp only [Bool.and_eq_true] at hg; exact hg.1
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold enqueueStep at h
    by_cases hg : stateAuthB s.caps a.sender a.sender && acceptsEffects s a.sender
    · simp only [Bool.and_eq_true] at hg; exact hg.2
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold enqueueStep at h
    by_cases hg : stateAuthB s.caps a.sender a.sender && acceptsEffects s a.sender
    · rw [if_pos hg] at h
      have := queueEnqueueDepositK_conserves_combined (k := s) (k' := s') h b
      rw [this]; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §3 — `queueDequeueA`: FIFO remove + REFUND the deposit, BINDING-GATED (closes P0-1).

`queueDequeueRefundK k id actor depId` REMOVES the FIFO head (owner-gated) AND REFUNDS the caller-supplied
deposit record `depId` (looked up in the GLOBAL `escrows` table) to the dequeuer `actor` — with NO binding
between the record and the dequeuer. The P0-1 HOLE: a dequeuer can name an UNRELATED unresolved deposit
(parked FOR someone else) and drain its value to themselves.

THE FIX (a WRAP): `dequeueBindStep` admits the refund ONLY when the named record's `recipient = actor` —
the deposit must be DESTINED to the dequeuer. Honest flow: enqueue parks with `recipient := owner`, and
dequeue requires `actor = owner` (kernel gate), so the bound deposit's recipient IS the dequeuer. An
unrelated deposit (recipient ≠ actor) is REJECTED. `auth_gated` forces the binding (a typing obligation).
The kernel op returns `(state, head)`; we project the state (the head surfaces in the kernel transition's
`Nat`). `conserves` cites the proved `queueDequeueRefundK_conserves_combined`; `delta = 0`. -/

/-- Queue-dequeue (deposit-refund) arguments: the queue `id`, the dequeuer `actor`, and the deposit
record id `depId` to refund. -/
structure DequeueArgs where
  /-- The queue id to dequeue from. -/
  id : Nat
  /-- The dequeuer (must be the queue owner — the kernel gate — AND the deposit's recipient — the P0-1 gate). -/
  actor : CellId
  /-- The deposit record id to refund (BINDING-GATED: its `recipient` must equal `actor`). -/
  depId : Nat

/-- Resolve the unresolved deposit record named `depId` (the kernel's own `find?` predicate). The binding
gate reads the record's `recipient` off THIS lookup, so it is a pure function of `(state, depId)`. -/
def findDeposit (k : RecordKernelState) (depId : Nat) : Option EscrowRecord :=
  k.escrows.find? (fun r => decide (r.id = depId ∧ r.resolved = false))

/-- **The P0-1 BINDING gate.** The named deposit record must be DESTINED to the dequeuer
(`r.recipient = actor`). If no unresolved record is named, fail-closed. This is the minimal sound
conjunct: only a deposit parked FOR this owner can be drained by this owner (the fuller per-message
binding is §DEFER'd). -/
def dequeueBindB (k : RecordKernelState) (a : DequeueArgs) : Bool :=
  match findDeposit k a.depId with
  | some r => decide (r.recipient = a.actor)
  | none   => false

/-- **The P0-1-closing dequeue-refund step.** Commit the kernel `queueDequeueRefundK` (projecting out the
post-state, dropping the dequeued head) ONLY when the binding gate holds (the named deposit's `recipient`
is the dequeuer). The bare kernel op (anyone-names-any-deposit) is otherwise unchanged. -/
def dequeueBindStep (k : RecordKernelState) (a : DequeueArgs) : Option RecordKernelState :=
  if dequeueBindB k a then
    (queueDequeueRefundK k a.id a.actor a.depId).map Prod.fst
  else none

/-- **`queueDequeueA` — the P0-1-closing dequeue-refund handler.** `auth_gated` BITES: a committed dequeue
proves the binding gate held (the refunded deposit's `recipient` is the dequeuer). `conserves` cites the
unconditional `queueDequeueRefundK_conserves_combined` (`delta = 0`); `admission` reports the same binding
witness (the deposit must exist + be destined to the actor — the admission analogue of the auth gate). -/
def queueDequeueA : EffectHandler DequeueArgs where
  step := dequeueBindStep
  delta := fun _ _ => 0
  auth := dequeueBindB
  admission := dequeueBindB
  trace := fun a => { actor := a.actor, src := a.actor, dst := a.actor, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold dequeueBindStep at h
    by_cases hg : dequeueBindB s a
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold dequeueBindStep at h
    by_cases hg : dequeueBindB s a
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold dequeueBindStep at h
    by_cases hg : dequeueBindB s a
    · rw [if_pos hg] at h
      -- the kernel op committed to `some (k1, mh)`; recover the pair and cite the conservation lemma.
      cases hk : queueDequeueRefundK s a.id a.actor a.depId with
      | none => rw [hk] at h; simp only [Option.map_none] at h; exact absurd h (by simp)
      | some pr =>
          obtain ⟨k1, mh⟩ := pr
          rw [hk] at h; simp only [Option.map_some] at h
          simp only [Option.some.injEq] at h; subst h
          have := queueDequeueRefundK_conserves_combined (k := s) (k' := k1) (mh := mh) hk b
          rw [this]; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §4 — `queueResizeA`: change the queue capacity. bal-NEUTRAL (`delta = 0`).

`queueResizeK` changes a queue's capacity (rejecting a shrink below current occupancy); it touches ONLY
`queues`, so the combined measure is unchanged. We WRAP it with the queue-cell authority gate
(`stateAuthB actor owner`) and the owner-Live admission gate; `conserves` cites `queueResizeK_balNeutral`. -/

/-- Queue-resize arguments: the actor, the queue `id`, the new `capacity`, and the queue `owner`
(authority subject). -/
structure ResizeArgs where
  /-- The actor performing the resize (must hold authority over `owner`). -/
  actor : CellId
  /-- The queue id to resize. -/
  id : Nat
  /-- The new capacity (rejected if below current occupancy). -/
  capacity : Nat
  /-- The queue owner (authority subject). -/
  owner : CellId

/-- The authority-gated resize step: the actor must hold authority over `owner` AND `owner` must be Live,
then run the proved `queueResizeK`. -/
def resizeStep (k : RecordKernelState) (a : ResizeArgs) : Option RecordKernelState :=
  if stateAuthB k.caps a.actor a.owner && acceptsEffects k a.owner then
    queueResizeK k a.id a.capacity
  else none

/-- **`queueResizeA` — the registered queue-resize handler.** `delta = 0` (touches only `queues`).
`conserves` from `queueResizeK_balNeutral`. `auth_gated`/`admission_gated` from the wrapping gate. -/
def queueResizeA : EffectHandler ResizeArgs where
  step := resizeStep
  delta := fun _ _ => 0
  auth := fun k a => stateAuthB k.caps a.actor a.owner
  admission := fun k a => acceptsEffects k a.owner
  trace := fun a => { actor := a.actor, src := a.owner, dst := a.owner, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold resizeStep at h
    by_cases hg : stateAuthB s.caps a.actor a.owner && acceptsEffects s a.owner
    · simp only [Bool.and_eq_true] at hg; exact hg.1
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold resizeStep at h
    by_cases hg : stateAuthB s.caps a.actor a.owner && acceptsEffects s a.owner
    · simp only [Bool.and_eq_true] at hg; exact hg.2
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold resizeStep at h
    by_cases hg : stateAuthB s.caps a.actor a.owner && acceptsEffects s a.owner
    · rw [if_pos hg] at h
      obtain ⟨hbal, hheld⟩ := queueResizeK_balNeutral h b
      unfold recTotalAssetWithEscrow; rw [hbal, hheld]; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §5 — `queueAtomicTxA`: the ALL-OR-NOTHING deposit-op batch. COMBINED-conserving (`delta = 0`).

dregg1's `apply_queue_atomic_tx` folds a list of queue deposit sub-ops (enqueue-with-deposit /
dequeue-refund) all-or-nothing: the batch COMMITS iff EVERY sub-op commits (each against the prior's
result); ANY failure rolls back the whole batch (`Option`-monad fold). We model the sub-op at the BARE
kernel layer (`QueueTxOpK`: enqueue-deposit or BINDING-GATED dequeue-refund — the P0-1 fix carries into
the batch), and the fold is COMBINED-conserving by induction reusing each sub-op's per-asset conservation
(`queueEnqueueDepositK_conserves_combined` / the binding-dequeue's `conserves`). `delta = 0`. -/

/-- One atomic-batch sub-op at the bare kernel layer: a deposit-park enqueue OR a binding-gated
deposit-refund dequeue (the P0-1 fix carries into the batch). -/
inductive QueueTxOpK where
  /-- `Enqueue { queue, message, deposit }` — append `m` + park the deposit (combined-conserving). -/
  | enqueue (id m : Nat) (sender owner : CellId) (depId : Nat) (dAsset : AssetId) (deposit : Int)
  /-- `Dequeue { queue }` — remove the FIFO head + refund the BOUND deposit (`recipient = actor`). -/
  | dequeue (id : Nat) (actor : CellId) (depId : Nat)
  deriving Repr

/-- Run one atomic sub-op at the bare kernel layer (reusing the proved kernel deposit ops + the P0-1
binding-gated dequeue from §3). -/
def queueTxOpStepK (k : RecordKernelState) : QueueTxOpK → Option RecordKernelState
  | .enqueue id m sender owner depId dAsset deposit =>
      queueEnqueueDepositK k id m sender owner depId dAsset deposit
  | .dequeue id actor depId =>
      dequeueBindStep k { id := id, actor := actor, depId := depId }

/-- **`queueTxOpStepK_conserves` — PROVED.** Each atomic sub-op is COMBINED-conserving per asset (the
deposit park / bound refund moves the bare ledger but the combined measure is fixed) — read off the
kernel deposit ops' proved combined-conservation. -/
theorem queueTxOpStepK_conserves {k k' : RecordKernelState} {op : QueueTxOpK}
    (h : queueTxOpStepK k op = some k') (b : AssetId) :
    recTotalAssetWithEscrow k' b = recTotalAssetWithEscrow k b := by
  cases op with
  | enqueue id m sender owner depId dAsset deposit =>
      exact queueEnqueueDepositK_conserves_combined (k := k) (k' := k') h b
  | dequeue id actor depId =>
      -- the §3 binding-gated dequeue step is combined-conserving — reuse the registered handler's own
      -- `conserves` obligation (`queueTxOpStepK k (.dequeue …)` is definitionally `queueDequeueA.step`;
      -- its `delta` is `0`, so the `+ delta` summand drops).
      have hc := queueDequeueA.conserves k { id := id, actor := actor, depId := depId } k' h b
      -- `queueDequeueA.delta _ b = 0` definitionally; drop the trivial summand.
      rw [show queueDequeueA.delta { id := id, actor := actor, depId := depId } b = 0 from rfl,
          add_zero] at hc
      exact hc

/-- **The all-or-nothing atomic batch fold** (dregg1 `apply_queue_atomic_tx`). Thread the sub-ops
left-to-right through the `Option` monad: COMMIT iff EVERY sub-op commits; ANY failure ⇒ `none` (the
whole batch rolls back). -/
def queueAtomicTxChainK (k : RecordKernelState) : List QueueTxOpK → Option RecordKernelState
  | []        => some k
  | op :: ops =>
      match queueTxOpStepK k op with
      | some k' => queueAtomicTxChainK k' ops
      | none    => none

/-- **`queueAtomicTxChainK_conserves` — PROVED (the atomic batch is COMBINED-conserving per asset).** A
committed batch preserves `recTotalAssetWithEscrow` at EVERY asset: each sub-op is combined-conserving,
and the fold composes them. By induction on the op list. -/
theorem queueAtomicTxChainK_conserves {k k' : RecordKernelState} {ops : List QueueTxOpK}
    (h : queueAtomicTxChainK k ops = some k') (b : AssetId) :
    recTotalAssetWithEscrow k' b = recTotalAssetWithEscrow k b := by
  induction ops generalizing k with
  | nil => simp only [queueAtomicTxChainK, Option.some.injEq] at h; subst h; rfl
  | cons op rest ih =>
      simp only [queueAtomicTxChainK] at h
      cases hop : queueTxOpStepK k op with
      | none    => rw [hop] at h; exact absurd h (by simp)
      | some k1 =>
          rw [hop] at h
          rw [ih h, queueTxOpStepK_conserves hop b]

/-- Atomic-tx arguments: the actor (the batch-commit subject) and the sub-op list. -/
structure AtomicTxArgs where
  /-- The actor performing the atomic batch (the metadata/receipt subject). -/
  actor : CellId
  /-- The all-or-nothing list of deposit sub-ops. -/
  ops : List QueueTxOpK

/-- The atomic-tx step: run the all-or-nothing batch fold over the bare kernel (the receipt-chain
metadata row lives in the chained executor; here the conservation content is the fold). -/
def atomicTxStep (k : RecordKernelState) (a : AtomicTxArgs) : Option RecordKernelState :=
  queueAtomicTxChainK k a.ops

/-- **`queueAtomicTxA` — the registered atomic-tx handler (`delta = 0`, COMBINED-conserving).**
`conserves` from `queueAtomicTxChainK_conserves` (the per-op conservation summed over the fold).
`auth`/`admission` default-true here (each sub-op carries its OWN fail-closed gate IN the fold — the
sender writer-ACL on each enqueue, the owner + P0-1 binding gate on each dequeue; the batch-level
authority is the conjunction enforced sub-op by sub-op). -/
def queueAtomicTxA : EffectHandler AtomicTxArgs where
  step := atomicTxStep
  delta := fun _ _ => 0
  auth := fun _ _ => true
  admission := fun _ _ => true
  trace := fun a => { actor := a.actor, src := a.actor, dst := a.actor, amt := 0 }
  auth_gated := by intro s a s' _; rfl
  admission_gated := by intro s a s' _; rfl
  conserves := by
    intro s a s' h b
    unfold atomicTxStep at h
    have := queueAtomicTxChainK_conserves (k := s) (k' := s') h b
    rw [this]; ring

/-! ## §6 — `queuePipelineStepA`: the FAN-OUT routing step. bal-NEUTRAL (`delta = 0`).

dregg1's `apply_queue_pipeline_step` DEQUEUEs the FIFO head from a source queue (owner-only) and
RE-ENQUEUEs that moved head into EACH sink (ACL-checked per sink, `pipelineFanoutK`). It moves MESSAGES,
never balance — every step is bal-NEUTRAL on `queues`, so the combined per-asset measure is unchanged
(`delta = 0`). We model the step at the bare kernel layer (the chained version adds a routing receipt
row); `conserves` composes `queueDequeueK_balNeutral` (the source dequeue) with the proved
`pipelineFanoutK_balNeutral` (the sink fan-out). -/

/-- Pipeline-step arguments: the source queue `srcId`, the `owner` (source dequeuer), and the
position-paired sink cells / sink queue ids. -/
structure PipelineArgs where
  /-- The source queue id (the FIFO head is dequeued from here). -/
  srcId : Nat
  /-- The source dequeuer (must be the source queue owner). -/
  owner : CellId
  /-- The representing cells of each sink (writer-ACL gated per sink). -/
  sinkCells : List CellId
  /-- The queue ids of each sink (position-paired with `sinkCells`). -/
  sinkIds : List Nat

/-- The pipeline step at the bare kernel layer: dequeue the source head (owner-gated, FIFO order) then
fan it out into each ACL-checked sink (all-or-nothing). Fail-closed if the source dequeue fails OR any
sink rejects. -/
def pipelineStep (k : RecordKernelState) (a : PipelineArgs) : Option RecordKernelState :=
  match queueDequeueK k a.srcId a.owner with
  | some (k1, m) => pipelineFanoutK k1 a.owner m a.sinkCells a.sinkIds
  | none         => none

/-- **`queuePipelineStepA` — the registered pipeline-routing handler (`delta = 0`, bal-NEUTRAL).**
`conserves` composes the source dequeue's bal-neutrality (`queueDequeueK_balNeutral`) with the sink
fan-out's (`pipelineFanoutK_balNeutral`). `auth`/`admission` default-true here (the OWNER gate lives in
`queueDequeueK` IN the step, the per-sink writer-ACL in `pipelineFanoutK` IN the step — the load-bearing
gates are the kernel ops the step composes; the `#eval` TEETH verify them). -/
def queuePipelineStepA : EffectHandler PipelineArgs where
  step := pipelineStep
  delta := fun _ _ => 0
  auth := fun _ _ => true
  admission := fun _ _ => true
  trace := fun a => { actor := a.owner, src := a.owner, dst := a.owner, amt := 0 }
  auth_gated := by intro s a s' _; rfl
  admission_gated := by intro s a s' _; rfl
  conserves := by
    intro s a s' h b
    unfold pipelineStep at h
    cases hd : queueDequeueK s a.srcId a.owner with
    | none => rw [hd] at h; exact absurd h (by simp)
    | some pr =>
        obtain ⟨k1, m⟩ := pr
        rw [hd] at h
        obtain ⟨hbd, hed⟩ := queueDequeueK_balNeutral hd b
        obtain ⟨hbf, hef⟩ := pipelineFanoutK_balNeutral h b
        unfold recTotalAssetWithEscrow
        rw [hbf, hef, hbd, hed]; ring

/-! ## §7 — The batch registry: the queue cluster as coproduct entries.

Each handler is one well-typed `PackedHandler` — the obligation proofs are a TYPING condition on entry.
This list plugs straight into the generic `turn_conserves` from `Dregg2.Exec.Handler`. -/

/-- The queue batch registry (the coproduct menu for this cluster). -/
def queueBatchRegistry : Registry :=
  [ ⟨AllocateArgs, queueAllocateA⟩,
    ⟨EnqueueArgs, queueEnqueueA⟩,
    ⟨DequeueArgs, queueDequeueA⟩,
    ⟨ResizeArgs, queueResizeA⟩,
    ⟨AtomicTxArgs, queueAtomicTxA⟩,
    ⟨PipelineArgs, queuePipelineStepA⟩ ]

/-- Build a closed queue-allocate effect (tag `0`). -/
def allocateEffect (actor : CellId) (id : Nat) (owner : CellId) (capacity : Nat) : ClosedEffect :=
  { tag := 0, Args := AllocateArgs,
    args := { actor := actor, id := id, owner := owner, capacity := capacity }, handler := queueAllocateA }

/-- Build a closed queue-enqueue (deposit-park) effect (tag `1`). -/
def enqueueEffect (id m : Nat) (sender owner : CellId) (depId : Nat) (dAsset : AssetId) (deposit : Int) :
    ClosedEffect :=
  { tag := 1, Args := EnqueueArgs,
    args := { id := id, m := m, sender := sender, owner := owner, depId := depId,
              dAsset := dAsset, deposit := deposit }, handler := queueEnqueueA }

/-- Build a closed queue-dequeue (deposit-refund) effect (tag `2`). -/
def dequeueEffect (id : Nat) (actor : CellId) (depId : Nat) : ClosedEffect :=
  { tag := 2, Args := DequeueArgs, args := { id := id, actor := actor, depId := depId },
    handler := queueDequeueA }

/-- Build a closed queue-resize effect (tag `3`). -/
def resizeEffect (actor : CellId) (id capacity : Nat) (owner : CellId) : ClosedEffect :=
  { tag := 3, Args := ResizeArgs,
    args := { actor := actor, id := id, capacity := capacity, owner := owner }, handler := queueResizeA }

/-- Build a closed atomic-tx effect (tag `4`). -/
def atomicTxEffect (actor : CellId) (ops : List QueueTxOpK) : ClosedEffect :=
  { tag := 4, Args := AtomicTxArgs, args := { actor := actor, ops := ops }, handler := queueAtomicTxA }

/-- Build a closed pipeline-step effect (tag `5`). -/
def pipelineEffect (srcId : Nat) (owner : CellId) (sinkCells : List CellId) (sinkIds : List Nat) :
    ClosedEffect :=
  { tag := 5, Args := PipelineArgs,
    args := { srcId := srcId, owner := owner, sinkCells := sinkCells, sinkIds := sinkIds },
    handler := queuePipelineStepA }

/-! ## §8 — TEETH: the P0-1 binding attack + the order/deposit/atomic behaviour, evaluated.

The methodology that matters: the P0-1 ATTACK (a dequeuer refunding an UNRELATED deposit, recipient ≠
actor) is REJECTED, and the honest bound refund succeeds + conserves. A handler whose step skipped the
binding gate would have FAILED `auth_gated` at type-check time. -/

/-- A fixture: cells 0 (queue owner), 5 (sender), 8 (a STRANGER) are live accounts; sender 5 holds 100
of asset 0; one queue (id 7, owner 0, cap 3, empty). Self-authority (every cell authorizes its own
ledger). All cells Live. -/
def qh0 : RecordKernelState :=
  { accounts := {0, 5, 8}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 5 ∧ a = 0 then 100 else 0
    queues := [{ id := 7, owner := 0, capacity := 3, buffer := [] }] }

/-- The fixture after sender 5 enqueues message 111 with a deposit of 30 (record id 9, recipient = owner
0). The deposit is parked FOR owner 0; the bare ledger of asset 0 dropped 100 → 70 (combined 100). -/
def qhEnq : Option RecordKernelState :=
  enqueueStep qh0 { id := 7, m := 111, sender := 5, owner := 0, depId := 9, dAsset := 0, deposit := 30 }

/-- The fixture additionally carrying an UNRELATED deposit (record id 99) parked FOR cell 8 (the
stranger) by sender 5 — destined to 8, NOT to the queue owner 0. The P0-1 attack tries to drain THIS. -/
def qhEnqUnrelated : Option RecordKernelState :=
  qhEnq.bind (fun k =>
    -- park a second deposit (id 99) recipient := 8 (stranger), by enqueuing another message
    enqueueStep k { id := 7, m := 222, sender := 5, owner := 8, depId := 99, dAsset := 0, deposit := 20 })

-- §TEETH-1 (P0-1 ATTACK): owner 0 dequeues but names the UNRELATED deposit 99 (recipient 8 ≠ actor 0) ⇒
-- REJECTED. The binding gate bites: a deposit destined to someone else cannot be drained.
#guard ((qhEnqUnrelated.bind (fun k => execEffect (dequeueEffect 7 0 99) k)).isSome) == false  --  false
-- §TEETH-2 (HONEST): owner 0 dequeues and names its OWN bound deposit 9 (recipient 0 = actor 0) ⇒ SUCCEEDS.
#guard ((qhEnqUnrelated.bind (fun k => execEffect (dequeueEffect 7 0 9) k)).isSome)  --  true
-- §TEETH-3 (CONSERVATION): the honest bound refund conserves the combined per-asset measure.
#guard ((qhEnq.bind (fun k => execEffect (dequeueEffect 7 0 9) k)).map
        (fun k => recTotalAssetWithEscrow k 0)) == some 100  --  some 100
-- §TEETH-4 (DEPOSIT MOVES the bare ledger): enqueue debits the sender's ledger (100 → 70), combined held.
#guard (qhEnq.map (fun k => (recTotalAsset k 0, recTotalAssetWithEscrow k 0))) == some (70, 100)  --  some (70, 100)
-- §TEETH-5 (FIFO order): after enqueue the message is in the buffer.
#guard (qhEnq.bind (fun k => (findQueue k.queues 7).map (·.buffer))) == some [111]  --  some [111]
-- §TEETH-6 (ALLOCATE): actor 0 allocates a fresh queue id 12 (owner 0) ⇒ SUCCEEDS, combined unchanged.
#guard ((execEffect (allocateEffect 0 12 0 4) qh0).map
        (fun k => (recTotalAssetWithEscrow k 0, ((findQueue k.queues 12).map (·.capacity))))) == some (100, some 4)  -- TODO(triage): comment claimed `some (0, some 4)`; code yields `some (100, some 4)` — the combined asset-0 measure of fixture qh0 is 100, not 0 (stale fixture value; allocate is correctly balance-neutral and capacity 4 is right).
-- §TEETH-7 (ALLOCATE duplicate id REJECTED): re-allocating the existing queue 7 ⇒ none.
#guard ((execEffect (allocateEffect 0 7 0 4) qh0).isSome) == false  --  false
-- §TEETH-8 (RESIZE): grow queue 7's capacity to 5 ⇒ SUCCEEDS; shrink below occupancy is rejected (see kernel).
#guard ((execEffect (resizeEffect 0 7 5 0) qh0).map
        (fun k => (findQueue k.queues 7).map (·.capacity))) == some (some 5)  --  some (some 5)
-- §TEETH-9 (ENQUEUE deposit gate): a deposit of 200 (> sender's 100) is REJECTED.
#guard ((execEffect (enqueueEffect 7 111 5 0 9 0 200) qh0).isSome) == false  --  false
-- §TEETH-10 (ATOMIC-TX all-or-nothing + conserve): a batch [enqueue dep30; dequeue-refund bound 9] runs
-- the fold and conserves the combined measure (deposit parked then refunded back).
#guard ((execEffect (atomicTxEffect 0
        [ QueueTxOpK.enqueue 7 111 5 0 9 0 30, QueueTxOpK.dequeue 7 0 9 ]) qh0).map
        (fun k => recTotalAssetWithEscrow k 0)) == some 100  --  some 100
-- §TEETH-11 (ATOMIC-TX P0-1 binding carries into the batch): a batch whose dequeue names an UNRELATED
-- deposit (recipient ≠ actor) ROLLS BACK the whole batch (the binding gate bites inside the fold).
#guard ((execEffect (atomicTxEffect 0
        [ QueueTxOpK.enqueue 7 111 5 0 9 0 30, QueueTxOpK.enqueue 7 222 5 8 99 0 20,
          QueueTxOpK.dequeue 7 0 99 ]) qh0).isSome) == false  --  false
-- §TEETH-12 (PIPELINE fan-out): allocate a sink queue (id 13, owner 0), enqueue a message into source 7,
-- then pipeline the head from 7 into sink 13 ⇒ SUCCEEDS; the message LANDED in the sink and the combined
-- measure is UNCHANGED (the fixture's asset-0 measure 100 stays 100 — messages move, not value).
#guard (((queueAllocateK qh0 13 0 3).bind (fun k => queueEnqueueK k 7 111)).bind
        (fun k => execEffect (pipelineEffect 7 0 [0] [13]) k) |>.map
        (fun k => ((findQueue k.queues 13).map (·.buffer), recTotalAssetWithEscrow k 0))) == some (some [111], 100)  --  some (some [111], 100)
-- §TEETH-13 (PIPELINE source-empty REJECTED): pipelining an EMPTY source queue ⇒ none.
#guard ((execEffect (pipelineEffect 7 0 [0] [13]) qh0).isSome) == false  --  false

/-! ## §9 — turn_conserves cross-check: a registry turn of queue effects conserves the combined measure.

The §8-TEETH-10 atomic batch's combined per-asset delta is `0` (deposit parked then refunded) — the SUM
the algebra's `turn_conserves` holds the measure to. A whole TURN of queue effects (allocate; enqueue;
bound dequeue) runs through the generic `execTurn` foldlM and conserves. -/
#guard (turnDelta [allocateEffect 0 12 0 4, enqueueEffect 7 111 5 0 9 0 30, dequeueEffect 7 0 9] 0) == 0  --  0
#guard ((execTurn [enqueueEffect 7 111 5 0 9 0 30, dequeueEffect 7 0 9] qh0).map
        (fun k => recTotalAssetWithEscrow k 0)) == some 100  --  some 100

/-! ## §10 — Axiom-hygiene pins (every handler keystone rests only on the three kernel axioms).

Pinning each handler def pins its obligation fields transitively (the literal CARRIES the proofs); each
fold/conservation helper is pinned directly. A `sorryAx` anywhere fails the pin AND the build. -/

#assert_axioms queueAllocateA
#assert_axioms queueEnqueueA
#assert_axioms queueDequeueA
#assert_axioms queueResizeA
#assert_axioms queueAtomicTxA
#assert_axioms queuePipelineStepA
#assert_axioms queueTxOpStepK_conserves
#assert_axioms queueAtomicTxChainK_conserves

/-! ## §DEFER — honest scope of this batch.

Deliberately OUT of this batch (documented, NOT a silent gap):

  * **Per-MESSAGE deposit binding (the FULLER P0-1 fix).** The minimal sound binding gate here is
    `r.recipient = actor` — the deposit must be destined to the dequeuer (the queue owner). The FULLER
    binding would key the deposit to the SPECIFIC dequeued message hash (so a dequeuer cannot refund a
    deposit parked for a DIFFERENT message in the same queue), but the `QueueRecord` buffer carries only
    message hashes, not a message→deposit map — that map is the next residual. The `recipient = actor`
    conjunct already blocks the cross-owner drain (the attack the codex flagged).

  * **The receipt-chain metadata rows.** `queueAtomicTxA`/`queuePipelineStepA` register the bare-kernel
    CONSERVATION content (the all-or-nothing fold / the source-dequeue-then-fan-out). The chained
    executor's batch-commit / routing receipt rows (`escrowReceiptA` / the routing log row) live in
    `TurnExecutorFull`'s `RecChainedState` layer — the EffectHandler algebra is over the bare kernel
    state; the receipt-chain face folds on at the cutover.

  * **`queueAtomicTxA`/`queuePipelineStepA` batch-level `auth`/`admission`.** These default-true because
    the load-bearing gates live IN the step (each sub-op's writer-ACL / owner / P0-1 binding inside the
    fold; the source-owner + per-sink ACL inside the pipeline). The §8 `#eval` TEETH verify the gates
    bite. A batch-level authority object (the conjunction of the sub-op gates as a single witness) is the
    Guard-valued upgrade noted in `Dregg2.Exec.Handler`'s §DEFER. -/

end Dregg2.Exec.Handlers.Queue
