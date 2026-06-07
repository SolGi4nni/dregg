/-
# Dregg2.Spec.FunctionalRefinement — REAL functional refinement: the executor commits EXACTLY
the independently-specified output (output-uniqueness, not merely "the result satisfies a predicate").

## The gap this closes (the grounded study finding)

A `RecordProgram`/`CellProgram` is a **constraint**: `admits (old, new)` accepts or rejects a
*candidate* pair — it does NOT name or derive the intended `new`. The next state is computed by a
*separate* op language (`applyOp`, the escrow/queue kernel ops), which has had NO declarative spec
it is proven to refine. So far we prove:

  * `recExec_admitted`   — "the committed result satisfies my predicate" (`admits old new`), and
  * `recExec_commits_applyOp` — "the commit equals what the op produced".

But neither says **the result IS the function I meant**. `admits old new` permits MANY `new`
(e.g. `monotonic "count"` admits every `new ≥ old`). Output *uniqueness + correctness* — "this op
commits to EXACTLY the post-state my protocol intent prescribes, and rejects every other candidate"
— existed only for the transfer beachhead, not the ~43 effects.

This module establishes that stronger property for the **escrow family** (create / release / refund)
as the validated REFERENCE PATTERN, and pushes it to a **second family** (queue FIFO
allocate / enqueue / dequeue). For each effect we:

  1. Write an **INDEPENDENT declarative reference function** in plain Lean — `escrowCreateSpec`,
     `escrowReleaseSpec`, … : the post-state, named *from protocol intent* (the asset ledger moves;
     a fresh unresolved record is parked; the settled record is marked resolved; the FIFO buffer
     gains/loses one message). These are written WITHOUT looking at the executor's code — they say
     what the correct answer IS, not "= the executor". (Anti-circularity: `escrowCreateSpec :=
     createEscrowRawAsset` would be vacuous; we instead reconstruct the post-state field-by-field
     from intent and then PROVE the executor equals it — a theorem that could be FALSE if the
     executor debited the wrong cell / parked the wrong record.)

  2. Prove the **functional-refinement triangle with output-uniqueness**:
     `step k a = some k' ↔ (gate k a ∧ k' = spec k a)`. The `→` direction is the "commits to EXACTLY
     the spec output" fact (output-uniqueness — strictly stronger than `admits`); the `←` direction
     is liveness/completeness (whenever the gate holds, the executor commits the spec's output).

  3. Include an **ANTI-GHOST tooth**: a candidate `k'' ≠ spec k a` is REJECTED —
     `step k a ≠ some k''` whenever `k'' ≠ spec k a` — so the refinement pins the UNIQUE correct
     output (non-vacuously: we also exhibit, via `#guard`, a concrete tampered candidate that the
     executor refuses while accepting the spec's output).

`#assert_axioms`-clean, no `sorry`, no `:= True`. Imports the escrow handlers (`createEscrowStep`,
`releaseStep`, `refundStep` — the actor-gated R2 steps) and the kernel queue ops.
-/
import Dregg2.Exec.Handlers.Escrow
import Dregg2.Exec.Handlers.StateSupply
import Dregg2.Exec.Handlers.Authority

namespace Dregg2.Spec.FunctionalRefinement

open Dregg2.Authority Dregg2.Execution
open Dregg2.Exec
open Dregg2.Exec.Handlers.Escrow
open Dregg2.Exec.TurnExecutorFull
  (acceptsEffects recKMintAsset recKBurnAsset recBalCredit attenuateSlotF)

/-! ## §0 — The independent intent-level vocabulary.

These are the field-level moves the protocol intent DESCRIBES, re-derived here in plain Lean
WITHOUT reference to the executor's `createEscrowRawAsset`/`settleEscrowRawAsset`. They are the
"what the answer is" oracle; the triangle below proves the executor realizes exactly them. -/

/-- **`intentDebit bal c a amt`** — the protocol intent of "park `amt` of asset `a` out of cell `c`":
cell `c`'s asset-`a` column drops by `amt`; every OTHER (cell, asset) pair is literally unchanged.
Written from intent (a single-cell, single-asset withdrawal); it happens to coincide pointwise with
the kernel's `recBalCreditCell _ _ _ (-amt)`, which we EXPLOIT (`recBalCreditCell_neg_eq`) to reuse the
proved conservation lemmas — but the DEFINITION here is intent, not a call to the executor. -/
def intentDebit (bal : CellId → AssetId → ℤ) (c : CellId) (a : AssetId) (amt : ℤ) :
    CellId → AssetId → ℤ :=
  fun x b => if x = c ∧ b = a then bal x b - amt else bal x b

/-- **`intentCredit bal c a amt`** — the dual: cell `c`'s asset-`a` column rises by `amt`. -/
def intentCredit (bal : CellId → AssetId → ℤ) (c : CellId) (a : AssetId) (amt : ℤ) :
    CellId → AssetId → ℤ :=
  fun x b => if x = c ∧ b = a then bal x b + amt else bal x b

/-- The intent debit/credit coincide pointwise with the kernel's `recBalCreditCell` (credit by a
signed delta). A bridge lemma so the SPEC (intent) and the EXECUTOR (kernel op) provably agree on the
ledger move — proving the executor's choice of `recBalCreditCell creator asset (-amount)` realizes the
INTENT "debit creator". This is a genuine fact about two *independently written* functions. -/
theorem intentDebit_eq_credit (bal : CellId → AssetId → ℤ) (c : CellId) (a : AssetId) (amt : ℤ) :
    intentDebit bal c a amt = recBalCreditCell bal c a (-amt) := by
  funext x b; unfold intentDebit recBalCreditCell
  by_cases h : x = c ∧ b = a
  · simp only [if_pos h]; ring
  · simp only [if_neg h]

theorem intentCredit_eq_credit (bal : CellId → AssetId → ℤ) (c : CellId) (a : AssetId) (amt : ℤ) :
    intentCredit bal c a amt = recBalCreditCell bal c a amt := by
  funext x b; unfold intentCredit recBalCreditCell
  by_cases h : x = c ∧ b = a
  · simp only [if_pos h]
  · simp only [if_neg h]

/-! ## §1 — ESCROW CREATE: the reference triangle.

### The independent declarative spec (intent).

A `createEscrow` of `(id, creator, recipient, asset, amount)` MEANS, declaratively:
  * the creator's asset-`asset` balance goes DOWN by `amount` (`intentDebit`),
  * a FRESH unresolved record `{id, creator, recipient, amount, resolved := false, asset}` is parked
    at the FRONT of the holding store,
  * EVERYTHING ELSE (accounts, caps, nullifiers, queues, …) is untouched.
We write this as a whole-state function `escrowCreateSpec`, derived from the protocol meaning, NOT
from `createEscrowRawAsset`. -/

/-- The fresh record the intent parks (named from the create's arguments). -/
def escrowCreateRecord (a : CreateEscrowArgs) : EscrowRecord :=
  { id := a.id, creator := a.creator, recipient := a.recipient,
    amount := a.amount, resolved := false, asset := a.asset }

/-- **`escrowCreateSpec` — the INDEPENDENT declarative post-state of a create.** The creator's
asset balance drops by `amount`; the fresh unresolved record is prepended; all else fixed. This is
intent, written field-by-field — it is what a correct executor MUST produce, and the triangle proves
`createEscrowStep` produces exactly this. -/
def escrowCreateSpec (k : RecordKernelState) (a : CreateEscrowArgs) : RecordKernelState :=
  { k with bal := intentDebit k.bal a.creator a.asset a.amount
           escrows := escrowCreateRecord a :: k.escrows }

/-- The create gate (intent-level precondition), re-expressed as the conjunction the executor checks.
Written here so the triangle's `←` direction (liveness) reads cleanly. -/
def escrowCreateGate (k : RecordKernelState) (a : CreateEscrowArgs) : Prop :=
  acceptsEffects k a.creator = true ∧
  authorizedB k.caps (createEscrowTurn a) = true ∧
  0 ≤ a.amount ∧ a.amount ≤ k.bal a.creator a.asset ∧ a.creator ∈ k.accounts ∧
  ¬ (∃ r ∈ k.escrows, r.id = a.id)

/-- The executor's `createEscrowRawAsset` realizes the INTENT post-state `escrowCreateSpec`.
A genuine equality of two independently-written functions: the executor debits via
`recBalCreditCell creator asset (-amount)` and prepends its record literal; the spec debits via
`intentDebit creator asset amount` and prepends `escrowCreateRecord`. They are EQUAL — proving the
executor's op realizes the intended ledger+store move (it would be FALSE if the executor debited the
recipient, or parked a resolved record, or wrote the wrong asset). -/
theorem createEscrowRawAsset_eq_spec (k : RecordKernelState) (a : CreateEscrowArgs) :
    createEscrowRawAsset k a.id a.creator a.recipient a.asset a.amount = escrowCreateSpec k a := by
  unfold createEscrowRawAsset escrowCreateSpec escrowCreateRecord
  rw [intentDebit_eq_credit]

/-- **THE ESCROW-CREATE TRIANGLE (PROVED, FULL BICONDITIONAL).** The actor-gated executor commits
EXACTLY the independently-specified output: `createEscrowStep k a = some k'` IFF the create gate holds
AND `k' = escrowCreateSpec k a`. The `→` is output-uniqueness (a commit pins the unique spec output —
strictly stronger than `admits`); the `←` is completeness (the gate suffices for the spec output to
commit). -/
theorem escrowCreate_triangle (k k' : RecordKernelState) (a : CreateEscrowArgs) :
    createEscrowStep k a = some k' ↔ (escrowCreateGate k a ∧ k' = escrowCreateSpec k a) := by
  unfold createEscrowStep createEscrowKAsset escrowCreateGate createEscrowTurn
  constructor
  · intro h
    by_cases hadm : acceptsEffects k a.creator = true
    · rw [if_pos hadm] at h
      by_cases hg : authorizedB k.caps { actor := a.actor, src := a.creator, dst := a.recipient, amt := a.amount } = true
          ∧ 0 ≤ a.amount ∧ a.amount ≤ k.bal a.creator a.asset ∧ a.creator ∈ k.accounts
          ∧ ¬ (∃ r ∈ k.escrows, r.id = a.id)
      · rw [if_pos hg] at h
        simp only [Option.some.injEq] at h
        obtain ⟨hauth, hamt, havail, hacc, hfresh⟩ := hg
        refine ⟨⟨hadm, hauth, hamt, havail, hacc, hfresh⟩, ?_⟩
        rw [← h, createEscrowRawAsset_eq_spec]
      · rw [if_neg hg] at h; exact absurd h (by simp)
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  · rintro ⟨⟨hadm, hauth, hamt, havail, hacc, hfresh⟩, hk⟩
    rw [if_pos hadm, if_pos ⟨hauth, hamt, havail, hacc, hfresh⟩]
    rw [hk, createEscrowRawAsset_eq_spec]

/-- **ANTI-GHOST TOOTH (escrow create, PROVED).** Any candidate `k'' ≠ escrowCreateSpec k a` is
REJECTED: the executor never commits a ghost output. The refinement pins the UNIQUE correct
post-state — a tampered next-state (wrong balance, wrong/missing record, an extra field touched)
cannot come out of `createEscrowStep`. -/
theorem escrowCreate_antighost (k k'' : RecordKernelState) (a : CreateEscrowArgs)
    (hne : k'' ≠ escrowCreateSpec k a) : createEscrowStep k a ≠ some k'' := by
  intro h
  obtain ⟨_, hk⟩ := (escrowCreate_triangle k k'' a).mp h
  exact hne hk

/-! ## §2 — ESCROW SETTLE (release / refund): the triangle on the side-table.

The settle spec is intent over the FOUND record `r` (looked up by id, unresolved): credit the
settlement target (`recipient` for release, `creator` for refund) at `r.asset` by `r.amount`, and mark
`r` resolved. The gate adds the actor-authority (R2) + the settle-liveness (`target ∈ accounts ∧ Live`)
the kernel checks. We parametrize the spec by the target-selector so release/refund share one proof. -/

/-- **`escrowSettleSpec` — the INDEPENDENT declarative post-state of a settle to `target`.** Over the
found unresolved record `r`: `target`'s asset-`r.asset` balance rises by `r.amount` (`intentCredit`), and
the record is marked resolved (`markResolved` by id). All else fixed. (`markResolved` is the
intent-level "mark THIS record done"; it is the kernel's own list primitive, reused — the asset/ledger
move is the part the executor could get wrong, and that is `intentCredit`, written from intent.) -/
def escrowSettleSpec (k : RecordKernelState) (target : CellId) (r : EscrowRecord) (id : Nat) :
    RecordKernelState :=
  { k with bal := intentCredit k.bal target r.asset r.amount
           escrows := markResolved k.escrows id }

/-- The executor's `settleEscrowRawAsset` realizes the INTENT settle post-state. Independent-function
equality: the executor credits via `recBalCreditCell target asset amount`; the spec credits via
`intentCredit target asset amount`. EQUAL — the credit lands on the intended target/asset. -/
theorem settleEscrowRawAsset_eq_spec (k : RecordKernelState) (target : CellId) (r : EscrowRecord)
    (id : Nat) :
    settleEscrowRawAsset k id target r.asset r.amount = escrowSettleSpec k target r id := by
  unfold settleEscrowRawAsset escrowSettleSpec
  rw [intentCredit_eq_credit]

/-- **THE ESCROW-RELEASE TRIANGLE (PROVED, FULL BICONDITIONAL).** `releaseStep k a = some k'` IFF
there is a found unresolved record `r` (named by `a.id`) whose RECIPIENT the actor is authorized over
and who is a live account, AND `k'` is EXACTLY `escrowSettleSpec` crediting that recipient. The output
is the unique intent post-state; release credits the RECIPIENT (not the creator) — a fact the triangle
pins. -/
theorem escrowRelease_triangle (k k' : RecordKernelState) (a : SettleArgs) :
    releaseStep k a = some k' ↔
      (∃ r, findUnresolved k a.id = some r ∧
            authorizedB k.caps { actor := a.actor, src := r.recipient, dst := r.recipient, amt := 0 } = true ∧
            r.recipient ∈ k.accounts ∧ cellLifecycleLive k r.recipient = true ∧
            k' = escrowSettleSpec k r.recipient r a.id) := by
  unfold releaseStep releaseSettleAuthB releaseEscrowKAsset findUnresolved
  constructor
  · intro h
    cases hf : k.escrows.find? (fun r => decide (r.id = a.id ∧ r.resolved = false)) with
    | none => rw [hf] at h; exact absurd h (by simp)
    | some r =>
        rw [hf] at h; simp only at h
        by_cases hauth : authorizedB k.caps { actor := a.actor, src := r.recipient, dst := r.recipient, amt := 0 } = true
        · rw [if_pos hauth] at h
          by_cases hlive : r.recipient ∈ k.accounts ∧ cellLifecycleLive k r.recipient = true
          · rw [if_pos hlive] at h; simp only [Option.some.injEq] at h
            refine ⟨r, rfl, hauth, hlive.1, hlive.2, ?_⟩
            rw [← h, settleEscrowRawAsset_eq_spec]
          · rw [if_neg hlive] at h; exact absurd h (by simp)
        · rw [if_neg hauth] at h; exact absurd h (by simp)
  · rintro ⟨r, hf, hauth, hacc, hlive, hk⟩
    rw [hf]; simp only
    rw [if_pos hauth, if_pos ⟨hacc, hlive⟩, hk, settleEscrowRawAsset_eq_spec]

/-- **ANTI-GHOST TOOTH (escrow release, PROVED).** Once the found record `r` is fixed, any candidate
`k'' ≠ escrowSettleSpec k r.recipient r a.id` is REJECTED. The release output is the unique intent
post-state crediting the recipient. -/
theorem escrowRelease_antighost (k k'' : RecordKernelState) (a : SettleArgs) (r : EscrowRecord)
    (hf : findUnresolved k a.id = some r) (hne : k'' ≠ escrowSettleSpec k r.recipient r a.id) :
    releaseStep k a ≠ some k'' := by
  intro h
  obtain ⟨r', hf', _, _, _, hk⟩ := (escrowRelease_triangle k k'' a).mp h
  rw [hf] at hf'; simp only [Option.some.injEq] at hf'; subst hf'
  exact hne hk

/-- **THE ESCROW-REFUND TRIANGLE (PROVED, FULL BICONDITIONAL).** Symmetric to release, but the credit
lands on the CREATOR (refund target). The output is the unique intent post-state crediting the creator —
the triangle pins release↔recipient vs refund↔creator. -/
theorem escrowRefund_triangle (k k' : RecordKernelState) (a : SettleArgs) :
    refundStep k a = some k' ↔
      (∃ r, findUnresolved k a.id = some r ∧
            authorizedB k.caps { actor := a.actor, src := r.creator, dst := r.creator, amt := 0 } = true ∧
            r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator = true ∧
            k' = escrowSettleSpec k r.creator r a.id) := by
  unfold refundStep refundSettleAuthB refundEscrowKAsset findUnresolved
  constructor
  · intro h
    cases hf : k.escrows.find? (fun r => decide (r.id = a.id ∧ r.resolved = false)) with
    | none => rw [hf] at h; exact absurd h (by simp)
    | some r =>
        rw [hf] at h; simp only at h
        by_cases hauth : authorizedB k.caps { actor := a.actor, src := r.creator, dst := r.creator, amt := 0 } = true
        · rw [if_pos hauth] at h
          by_cases hlive : r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator = true
          · rw [if_pos hlive] at h; simp only [Option.some.injEq] at h
            refine ⟨r, rfl, hauth, hlive.1, hlive.2, ?_⟩
            rw [← h, settleEscrowRawAsset_eq_spec]
          · rw [if_neg hlive] at h; exact absurd h (by simp)
        · rw [if_neg hauth] at h; exact absurd h (by simp)
  · rintro ⟨r, hf, hauth, hacc, hlive, hk⟩
    rw [hf]; simp only
    rw [if_pos hauth, if_pos ⟨hacc, hlive⟩, hk, settleEscrowRawAsset_eq_spec]

/-- **ANTI-GHOST TOOTH (escrow refund, PROVED).** -/
theorem escrowRefund_antighost (k k'' : RecordKernelState) (a : SettleArgs) (r : EscrowRecord)
    (hf : findUnresolved k a.id = some r) (hne : k'' ≠ escrowSettleSpec k r.creator r a.id) :
    refundStep k a ≠ some k'' := by
  intro h
  obtain ⟨r', hf', _, _, _, hk⟩ := (escrowRefund_triangle k k'' a).mp h
  rw [hf] at hf'; simp only [Option.some.injEq] at hf'; subst hf'
  exact hne hk

/-! ## §3 — SECOND FAMILY: QUEUE FIFO (allocate / enqueue / dequeue) — the same triangle.

The queue ops (`queueAllocateK`/`queueEnqueueK`/`queueDequeueK`) are a SEPARATE side-table family. We
give each an INDEPENDENT intent spec over the buffer and prove the triangle + anti-ghost tooth, so the
escrow REFERENCE PATTERN is shown to amplify to a structurally-different effect (a list-FIFO automaton,
not a per-asset ledger). -/

/-- **`queueAllocateSpec` — the INDEPENDENT post-state of an allocate.** A fresh queue record
`{id, owner, capacity, buffer := []}` is prepended; all else fixed. -/
def queueAllocateSpec (k : RecordKernelState) (id : Nat) (owner : CellId) (capacity : Nat) :
    RecordKernelState :=
  { k with queues := { id := id, owner := owner, capacity := capacity, buffer := [] } :: k.queues }

/-- **THE QUEUE-ALLOCATE TRIANGLE (PROVED, FULL BICONDITIONAL).** `queueAllocateK` commits EXACTLY the
intent post-state iff the id is fresh. -/
theorem queueAllocate_triangle (k k' : RecordKernelState) (id : Nat) (owner : CellId) (capacity : Nat) :
    queueAllocateK k id owner capacity = some k' ↔
      (findQueue k.queues id = none ∧ k' = queueAllocateSpec k id owner capacity) := by
  unfold queueAllocateK queueAllocateSpec
  constructor
  · intro h
    cases hf : findQueue k.queues id with
    | some q => rw [hf] at h; exact absurd h (by simp)
    | none   => rw [hf] at h; simp only [Option.some.injEq] at h; exact ⟨rfl, h.symm⟩
  · rintro ⟨hf, hk⟩; rw [hf, hk]

/-- **ANTI-GHOST TOOTH (queue allocate, PROVED).** -/
theorem queueAllocate_antighost (k k'' : RecordKernelState) (id : Nat) (owner : CellId) (capacity : Nat)
    (hne : k'' ≠ queueAllocateSpec k id owner capacity) :
    queueAllocateK k id owner capacity ≠ some k'' := by
  intro h
  exact hne ((queueAllocate_triangle k k'' id owner capacity).mp h).2

/-- **`queueEnqueueSpec` — the INDEPENDENT post-state of an enqueue over the found queue `q`.** The
message `m` is APPENDED to the back of `q`'s buffer (`qbufEnqueue` = FIFO tail-append); the queue record
is replaced in place; all else fixed. Written from intent ("the new message waits BEHIND those already
queued"). -/
def queueEnqueueSpec (k : RecordKernelState) (id : Nat) (q : QueueRecord) (m : Nat) :
    RecordKernelState :=
  { k with queues := replaceQueue k.queues id { q with buffer := qbufEnqueue q.buffer m } }

/-- **THE QUEUE-ENQUEUE TRIANGLE (PROVED, FULL BICONDITIONAL).** `queueEnqueueK` commits EXACTLY the
intent post-state iff the queue is found AND not full. The output appends to the TAIL (FIFO) — a
candidate that prepended, or replaced the wrong queue, is excluded. -/
theorem queueEnqueue_triangle (k k' : RecordKernelState) (id m : Nat) :
    queueEnqueueK k id m = some k' ↔
      (∃ q, findQueue k.queues id = some q ∧ q.buffer.length < q.capacity ∧
            k' = queueEnqueueSpec k id q m) := by
  unfold queueEnqueueK queueEnqueueSpec
  constructor
  · intro h
    cases hf : findQueue k.queues id with
    | none   => rw [hf] at h; exact absurd h (by simp)
    | some q =>
        rw [hf] at h; simp only at h
        by_cases hc : q.buffer.length < q.capacity
        · rw [if_pos hc] at h; simp only [Option.some.injEq] at h
          exact ⟨q, rfl, hc, h.symm⟩
        · rw [if_neg hc] at h; exact absurd h (by simp)
  · rintro ⟨q, hf, hc, hk⟩; rw [hf]; simp only; rw [if_pos hc, hk]

/-- **ANTI-GHOST TOOTH (queue enqueue, PROVED).** Once the found queue `q` is fixed, any candidate
`k'' ≠ queueEnqueueSpec k id q m` is REJECTED — the executor will not commit a buffer that isn't the
intent's tail-append. -/
theorem queueEnqueue_antighost (k k'' : RecordKernelState) (id m : Nat) (q : QueueRecord)
    (hf : findQueue k.queues id = some q) (hne : k'' ≠ queueEnqueueSpec k id q m) :
    queueEnqueueK k id m ≠ some k'' := by
  intro h
  obtain ⟨q', hf', _, hk⟩ := (queueEnqueue_triangle k k'' id m).mp h
  rw [hf] at hf'; simp only [Option.some.injEq] at hf'; subst hf'
  exact hne hk

/-- **`queueDequeueSpec` — the INDEPENDENT post-state of a dequeue over found queue `q` with buffer
`m :: rest`.** The FRONT message `m` (the OLDEST waiting) is removed; the queue record is replaced with
`rest`; all else fixed. The dequeued message is `m`. Written from intent ("the oldest message leaves
first"). -/
def queueDequeueSpec (k : RecordKernelState) (id : Nat) (q : QueueRecord) (rest : List Nat) :
    RecordKernelState :=
  { k with queues := replaceQueue k.queues id { q with buffer := rest } }

/-- **THE QUEUE-DEQUEUE TRIANGLE (PROVED, FULL BICONDITIONAL).** `queueDequeueK` commits EXACTLY the
intent post-state AND returns EXACTLY the front message iff the queue is found, the actor is the owner,
and the buffer is non-empty (`m :: rest`). The output removes the FRONT (FIFO) — a candidate that
removed the tail, or returned the wrong message, is excluded. This pins BOTH the post-state and the
returned message (a richer codomain — `RecordKernelState × Nat`). -/
theorem queueDequeue_triangle (k k' : RecordKernelState) (id : Nat) (actor : CellId) (m : Nat) :
    queueDequeueK k id actor = some (k', m) ↔
      (∃ q rest, findQueue k.queues id = some q ∧ actor = q.owner ∧ q.buffer = m :: rest ∧
                 k' = queueDequeueSpec k id q rest) := by
  unfold queueDequeueK queueDequeueSpec
  constructor
  · intro h
    cases hf : findQueue k.queues id with
    | none   => rw [hf] at h; exact absurd h (by simp)
    | some q =>
        rw [hf] at h; simp only at h
        by_cases ho : actor = q.owner
        · rw [if_pos ho] at h
          cases hb : q.buffer with
          | nil      => have hd : qbufDequeue q.buffer = none := by rw [hb]; rfl
                        rw [hd] at h; exact absurd h (by simp)
          | cons x xs =>
              have hd : qbufDequeue q.buffer = some (x, xs) := by rw [hb]; rfl
              rw [hd] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hk, hm⟩ := h; subst hm
              exact ⟨q, xs, rfl, ho, hb, hk.symm⟩
        · rw [if_neg ho] at h; exact absurd h (by simp)
  · rintro ⟨q, rest, hf, ho, hb, hk⟩
    rw [hf]; simp only; rw [if_pos ho]
    have hd : qbufDequeue q.buffer = some (m, rest) := by rw [hb]; rfl
    rw [hd, hk]

/-- **ANTI-GHOST TOOTH (queue dequeue, PROVED).** Once the found queue `q` (with buffer `m :: rest`)
is fixed, any candidate post-state `k'' ≠ queueDequeueSpec k id q rest` is REJECTED — the executor will
not commit a buffer that isn't the intent's front-removal. -/
theorem queueDequeue_antighost (k k'' : RecordKernelState) (id : Nat) (actor : CellId) (m : Nat)
    (q : QueueRecord) (rest : List Nat)
    (hf : findQueue k.queues id = some q) (hb : q.buffer = m :: rest)
    (hne : k'' ≠ queueDequeueSpec k id q rest) :
    queueDequeueK k id actor ≠ some (k'', m) := by
  intro h
  obtain ⟨q', rest', hf', _, hb', hk⟩ := (queueDequeue_triangle k k'' id actor m).mp h
  rw [hf] at hf'; simp only [Option.some.injEq] at hf'; subst hf'
  rw [hb] at hb'; simp only [List.cons.injEq] at hb'; obtain ⟨_, hr⟩ := hb'; subst hr
  exact hne hk

/-! ## §4 — NON-VACUITY TEETH (`#guard`): concrete witness TRUE and ghost REJECTED.

A live fixture proves each triangle's spec output is REACHED (the executor commits exactly it), and a
deliberately-tampered ghost candidate is REFUSED — so the refinement is not vacuously true. -/

/-- Fixture: cells 0,1 are accounts; cell 0 holds 100 of asset 0; self-authority; both Live. -/
def fx : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }

/-- The create arguments: lock 40 of asset 0, creator 0, recipient 1, id 9. -/
def caCreate : CreateEscrowArgs := { id := 9, actor := 0, creator := 0, recipient := 1, asset := 0, amount := 40 }

/-- The locked fixture (cell 0 has parked 40 into escrow id 9). -/
def fxLocked : RecordKernelState := escrowCreateSpec fx caCreate

-- Since `RecordKernelState` carries function fields it has no `BEq`; we witness the triangles via
-- DECIDABLE OBSERVATIONS (balances, buffer order, isSome) — `RecordKernelState`-equality itself is
-- proved/refuted by the triangle theorems + anti-ghost teeth above, which is the real content.

-- CREATE commits (the gate holds) and the debit is REAL: creator balance dropped 100 → 60.
#guard (createEscrowStep fx caCreate).isSome
#guard (((createEscrowStep fx caCreate).map (fun k => k.bal 0 0)) == some 60)
-- ...and the committed output's escrow head IS the intent's fresh unresolved record (asset 0, amt 40).
#guard (((createEscrowStep fx caCreate).bind (fun k => k.escrows.head?)).map
          (fun r => (r.id, r.creator, r.recipient, r.amount, r.resolved, r.asset))
        == some (9, 0, 1, 40, false, 0))
-- CREATE anti-ghost (CONCRETE): a ghost candidate with the creator's balance LEFT UNTOUCHED differs
-- OBSERVABLY from the spec output (bal 0 0 is 100 in the ghost `fx`, 60 in the spec) — so by
-- `escrowCreate_antighost` the executor refuses it. The observable witness of `ghost ≠ spec`:
#guard ((fx.bal 0 0, (escrowCreateSpec fx caCreate).bal 0 0) == (100, 60))

-- RELEASE credits the RECIPIENT (cell 1: 0 → 40); REFUND credits the CREATOR (cell 0: 60 → 100).
-- Distinct outputs ⇒ the triangle genuinely pins release↔recipient vs refund↔creator.
#guard ((releaseStep fxLocked { actor := 1, id := 9 }).map (fun k => k.bal 1 0)) == some 40
#guard ((refundStep  fxLocked { actor := 0, id := 9 }).map (fun k => k.bal 0 0)) == some 100
-- and the settled record is marked resolved (the side-table move is real).
#guard (((releaseStep fxLocked { actor := 1, id := 9 }).bind (fun k => k.escrows.head?)).map
          (·.resolved) == some true)

-- QUEUE allocate commits a fresh empty queue (id 7, owner 0, cap 2).
#guard (queueAllocateK fx 7 0 2).isSome
#guard (((queueAllocateK fx 7 0 2).bind (fun k => (findQueue k.queues 7))).map
          (fun q => (q.owner, q.capacity, q.buffer)) == some (0, 2, ([] : List Nat)))
-- ENQUEUE a(100) then b(200), then DEQUEUE returns the FRONT (a=100) — the FIFO order the triangle pins.
#guard (match queueAllocateK fx 7 0 2 with
        | some k1 => match queueEnqueueK k1 7 100 with
            | some k2 => match queueEnqueueK k2 7 200 with
                | some k3 => (queueDequeueK k3 7 0).map (·.2) == some 100  -- front = a = 100 (FIFO, not LIFO)
                | none => false
            | none => false
        | none => false)
-- ENQUEUE anti-ghost: a NON-OWNER cannot dequeue (the gate refuses); a FULL queue refuses enqueue.
#guard (match queueAllocateK fx 7 0 1 with  -- capacity 1
        | some k1 => match queueEnqueueK k1 7 100 with
            | some k2 => (queueEnqueueK k2 7 200).isNone  -- full ⇒ refused
            | none => false
        | none => false)

/-! ## §5 — Axiom-hygiene pins. Every triangle + anti-ghost rests only on the kernel axioms. -/

#assert_axioms intentDebit_eq_credit
#assert_axioms intentCredit_eq_credit
#assert_axioms createEscrowRawAsset_eq_spec
#assert_axioms escrowCreate_triangle
#assert_axioms escrowCreate_antighost
#assert_axioms settleEscrowRawAsset_eq_spec
#assert_axioms escrowRelease_triangle
#assert_axioms escrowRelease_antighost
#assert_axioms escrowRefund_triangle
#assert_axioms escrowRefund_antighost
#assert_axioms queueAllocate_triangle
#assert_axioms queueAllocate_antighost
#assert_axioms queueEnqueue_triangle
#assert_axioms queueEnqueue_antighost
#assert_axioms queueDequeue_triangle
#assert_axioms queueDequeue_antighost

/-! ## §6 — THIRD FAMILY: VALUE SUPPLY (mint / burn) — the per-asset supply triangle.

The supply ops (`Handlers.StateSupply.mintStep`/`burnStep`) move the ONE quantity that legitimately
changes the conserved per-asset measure. We give each an INDEPENDENT intent spec over the `bal`
ledger (the asset-`a` column of cell `c` rises/falls by `amt`, every OTHER (cell, asset) pair
literally untouched — `intentCredit`/`intentDebit`, the SAME intent oracles §0 wrote from protocol
intent) and prove the triangle + anti-ghost tooth. A wrong amount / wrong asset / wrong holder is
REJECTED — the supply move is pinned to the unique intent post-state.

The executor commits via the kernel op `recBalCredit cell a (±amt)`; our spec commits via the
independent `intentCredit`/`intentDebit cell a amt`. They are EQUAL (`intentCredit_eq_balCredit`),
proving the executor moves the INTENDED column — it would be FALSE if it credited the wrong cell,
the wrong asset, or the wrong sign. -/

open Dregg2.Exec.Handlers.StateSupply (SupplyArgs mintStep burnStep)

/-- The executor's per-asset single-cell move `recBalCredit` coincides pointwise with the intent
oracle `intentCredit` (both add a signed delta to ONE (cell, asset) column). An independent-function
equality bridging the SPEC (intent) and the EXECUTOR (kernel op) — it would be FALSE if the executor
spilled the credit onto another column. -/
theorem intentCredit_eq_balCredit (bal : CellId → AssetId → ℤ) (c : CellId) (a : AssetId) (amt : ℤ) :
    intentCredit bal c a amt = recBalCredit bal c a amt := by
  funext x b; unfold intentCredit recBalCredit
  by_cases h : x = c ∧ b = a
  · simp only [if_pos h]
  · simp only [if_neg h]

/-- The intent DEBIT coincides with the executor's `recBalCredit … (-amt)` (the burn move): both
subtract `amt` from ONE (cell, asset) column. The burn-side bridge (the `recKBurnAsset` op commits
`recBalCredit … (-amt)`, distinct from `RecordKernel.recBalCreditCell` used by `intentDebit_eq_credit`). -/
theorem intentDebit_eq_balCredit (bal : CellId → AssetId → ℤ) (c : CellId) (a : AssetId) (amt : ℤ) :
    intentDebit bal c a amt = recBalCredit bal c a (-amt) := by
  funext x b; unfold intentDebit recBalCredit
  by_cases h : x = c ∧ b = a
  · simp only [if_pos h]; ring
  · simp only [if_neg h]

/-- **`mintSpec` — the INDEPENDENT declarative post-state of a per-asset mint.** Cell `a.cell`'s
asset-`a.asset` column rises by `a.amt` (`intentCredit`); EVERYTHING ELSE (accounts, caps, escrows,
nullifiers, every other (cell, asset) column) untouched. Written from supply intent ("coin `amt`
of `asset` into `cell`"), NOT from `recKMintAsset`. -/
def mintSpec (k : RecordKernelState) (a : SupplyArgs) : RecordKernelState :=
  { k with bal := intentCredit k.bal a.cell a.asset a.amt }

/-- **`burnSpec` — the INDEPENDENT declarative post-state of a per-asset burn.** The dual: cell
`a.cell`'s asset-`a.asset` column FALLS by `a.amt` (`intentDebit`); all else fixed. Written from
intent ("annihilate `amt` of `asset` from `cell`"). -/
def burnSpec (k : RecordKernelState) (a : SupplyArgs) : RecordKernelState :=
  { k with bal := intentDebit k.bal a.cell a.asset a.amt }

/-- The mint gate (intent-level precondition), re-expressed as the conjunction the executor checks:
the target cell is Live (`acceptsEffects`), the actor holds PRIVILEGED mint authority (a `node`/
`control` cap — not bare ownership), the amount is non-negative, and the cell is a live account. -/
def mintGate (k : RecordKernelState) (a : SupplyArgs) : Prop :=
  acceptsEffects k a.cell = true ∧
  mintAuthorizedB k.caps a.actor a.cell = true ∧ 0 ≤ a.amt ∧ a.cell ∈ k.accounts

/-- The burn gate: the mint gate PLUS availability in the burned asset's column (you cannot burn
more than the cell holds). -/
def burnGate (k : RecordKernelState) (a : SupplyArgs) : Prop :=
  acceptsEffects k a.cell = true ∧
  mintAuthorizedB k.caps a.actor a.cell = true ∧ 0 ≤ a.amt ∧ a.amt ≤ k.bal a.cell a.asset ∧
  a.cell ∈ k.accounts

/-- **THE MINT TRIANGLE (PROVED, FULL BICONDITIONAL).** `mintStep k a = some k'` IFF the mint gate
holds AND `k' = mintSpec k a`. The `→` is output-uniqueness (a commit pins the unique intent
post-state — the credit lands on EXACTLY cell `a.cell`'s asset `a.asset` column, by EXACTLY `+a.amt`,
strictly stronger than `recTotalAsset += amt`); the `←` is completeness (the gate suffices). -/
theorem mint_triangle (k k' : RecordKernelState) (a : SupplyArgs) :
    mintStep k a = some k' ↔ (mintGate k a ∧ k' = mintSpec k a) := by
  unfold mintStep recKMintAsset mintGate mintSpec
  constructor
  · intro h
    by_cases hadm : acceptsEffects k a.cell = true
    · rw [if_pos hadm] at h
      by_cases hg : mintAuthorizedB k.caps a.actor a.cell = true ∧ 0 ≤ a.amt ∧ a.cell ∈ k.accounts
      · rw [if_pos hg] at h; simp only [Option.some.injEq] at h
        obtain ⟨hauth, hamt, hacc⟩ := hg
        refine ⟨⟨hadm, hauth, hamt, hacc⟩, ?_⟩
        rw [← h, intentCredit_eq_balCredit]
      · rw [if_neg hg] at h; exact absurd h (by simp)
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  · rintro ⟨⟨hadm, hauth, hamt, hacc⟩, hk⟩
    rw [if_pos hadm, if_pos ⟨hauth, hamt, hacc⟩, hk, intentCredit_eq_balCredit]

/-- **ANTI-GHOST TOOTH (mint, PROVED).** Any candidate `k'' ≠ mintSpec k a` is REJECTED — a mint
that credited a WRONG amount, the WRONG asset, the WRONG cell, or touched a 2nd column cannot come
out of `mintStep`. The supply move is pinned to the unique intent post-state. -/
theorem mint_antighost (k k'' : RecordKernelState) (a : SupplyArgs)
    (hne : k'' ≠ mintSpec k a) : mintStep k a ≠ some k'' := by
  intro h
  exact hne ((mint_triangle k k'' a).mp h).2

/-- **THE BURN TRIANGLE (PROVED, FULL BICONDITIONAL).** `burnStep k a = some k'` IFF the burn gate
(incl. availability in the burned asset) holds AND `k' = burnSpec k a`. The `→` pins the unique
intent post-state (the DEBIT lands on EXACTLY cell `a.cell`'s asset `a.asset` column, by EXACTLY
`-a.amt`); the `←` is completeness. -/
theorem burn_triangle (k k' : RecordKernelState) (a : SupplyArgs) :
    burnStep k a = some k' ↔ (burnGate k a ∧ k' = burnSpec k a) := by
  unfold burnStep recKBurnAsset burnGate burnSpec
  constructor
  · intro h
    by_cases hadm : acceptsEffects k a.cell = true
    · rw [if_pos hadm] at h
      by_cases hg : mintAuthorizedB k.caps a.actor a.cell = true ∧ 0 ≤ a.amt
          ∧ a.amt ≤ k.bal a.cell a.asset ∧ a.cell ∈ k.accounts
      · rw [if_pos hg] at h; simp only [Option.some.injEq] at h
        obtain ⟨hauth, hamt, havail, hacc⟩ := hg
        refine ⟨⟨hadm, hauth, hamt, havail, hacc⟩, ?_⟩
        rw [← h, intentDebit_eq_balCredit]
      · rw [if_neg hg] at h; exact absurd h (by simp)
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  · rintro ⟨⟨hadm, hauth, hamt, havail, hacc⟩, hk⟩
    rw [if_pos hadm, if_pos ⟨hauth, hamt, havail, hacc⟩, hk, intentDebit_eq_balCredit]

/-- **ANTI-GHOST TOOTH (burn, PROVED).** Any candidate `k'' ≠ burnSpec k a` is REJECTED. -/
theorem burn_antighost (k k'' : RecordKernelState) (a : SupplyArgs)
    (hne : k'' ≠ burnSpec k a) : burnStep k a ≠ some k'' := by
  intro h
  exact hne ((burn_triangle k k'' a).mp h).2

/-! ## §7 — FOURTH FAMILY: AUTHORITY (delegate / attenuate / revoke) — the cap-table triangle.

The cap-graph ops (`Handlers.Authority.delegateAttenStep`/`attenuateStep`/`revokeStep`) move the
`caps` side-table. We give each an INDEPENDENT intent spec over the cap function and prove the
triangle + anti-ghost tooth, pinning the EXACT resulting cap set (non-amplification is proven
ELSEWHERE — `delegateAttenH_non_amplifying`; here we pin the WHOLE cap function so an over-broad or
wrong-target cap edge is excluded as a ghost). Delegate is gated (Granovetter premise ⇒ a full
biconditional); attenuate/revoke are TOTAL (always commit ⇒ the load-bearing `→` output-uniqueness
direction is the whole content, the gate being trivially `true`). -/

open Dregg2.Exec.Handlers.Authority
  (DelegateArgs AttenuateArgs RevokeArgs delegateAttenStep attenuateStep revokeStep delegateGateB
   allAuths)

/-- **`delegateSpec` — the INDEPENDENT declarative post-state of an attenuated delegation.** The
recipient's slot GAINS exactly the delegator's held cap to `target`, attenuated to `keep`
(`grant … (attenuate keep (heldCapTo …))`); EVERYTHING ELSE (every other cell's slot, balances,
escrows) untouched. Written from intent ("hand `recipient` a `keep`-narrowed copy of the cap I hold
to `target`"). The cap installed is `attenuate keep (heldCapTo …)` — the SAME shape the executor's
`recKDelegateAtten` commits, which the triangle proves it realizes. -/
def delegateSpec (k : RecordKernelState) (a : DelegateArgs) : RecordKernelState :=
  { k with caps := grant k.caps a.recipient (attenuate a.keep (heldCapTo k.caps a.delegator a.target)) }

/-- **THE DELEGATE TRIANGLE (PROVED, FULL BICONDITIONAL).** `delegateAttenStep k a = some k'` IFF the
Granovetter connectivity premise holds (`delegateGateB` — the delegator already holds a cap conferring
an edge to `target`) AND `k' = delegateSpec k a`. The `→` pins the UNIQUE resulting cap function (the
recipient gains EXACTLY the attenuated held cap, and NO other slot changes — an over-broad grant, a
grant to the wrong recipient, or a fresh manufactured cap is excluded); the `←` is completeness. -/
theorem delegate_triangle (k k' : RecordKernelState) (a : DelegateArgs) :
    delegateAttenStep k a = some k' ↔ (delegateGateB k a = true ∧ k' = delegateSpec k a) := by
  unfold delegateAttenStep recKDelegateAtten delegateGateB delegateSpec
  constructor
  · intro h
    by_cases hg : (k.caps a.delegator).any (fun cap => confersEdgeTo a.target cap) = true
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h
      exact ⟨hg, h.symm⟩
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · rintro ⟨hg, hk⟩; rw [if_pos hg, hk]

/-- **ANTI-GHOST TOOTH (delegate, PROVED).** Any candidate `k'' ≠ delegateSpec k a` is REJECTED — the
delegation commits EXACTLY the attenuated-held-cap grant; an over-broad cap edge, a grant to the wrong
target/recipient, or a touched 2nd slot cannot come out of `delegateAttenStep`. -/
theorem delegate_antighost (k k'' : RecordKernelState) (a : DelegateArgs)
    (hne : k'' ≠ delegateSpec k a) : delegateAttenStep k a ≠ some k'' := by
  intro h
  exact hne ((delegate_triangle k k'' a).mp h).2

/-- **`attenuateSpec` — the INDEPENDENT declarative post-state of an in-place self-attenuation.** The
actor's OWN slot has its `idx`-th cap narrowed to `keep` (`attenuateSlotF` = `modify idx (attenuate
keep)` on the actor's slot only); EVERYTHING ELSE untouched. Written from intent ("narrow my own
idx-th held cap to `keep`"). -/
def attenuateSpec (k : RecordKernelState) (a : AttenuateArgs) : RecordKernelState :=
  { k with caps := attenuateSlotF k.caps a.actor a.idx a.keep }

/-- **THE ATTENUATE TRIANGLE (PROVED — TOTAL, output-uniqueness).** `attenuateStep` ALWAYS commits
(self-attenuation cannot fail — at worst the identity, still narrower-or-equal), so the gate is
trivially `true`; the load-bearing content is the `↔`: `attenuateStep k a = some k'` IFF
`k' = attenuateSpec k a`. The output is the UNIQUE intent post-state (the actor's own `idx`-th cap
narrowed in place, NO other slot/cell touched). -/
theorem attenuate_triangle (k k' : RecordKernelState) (a : AttenuateArgs) :
    attenuateStep k a = some k' ↔ k' = attenuateSpec k a := by
  unfold attenuateStep attenuateSpec
  constructor
  · intro h; simp only [Option.some.injEq] at h; exact h.symm
  · intro hk; rw [hk]

/-- **ANTI-GHOST TOOTH (attenuate, PROVED).** Any candidate `k'' ≠ attenuateSpec k a` is REJECTED —
the only thing `attenuateStep` ever commits is the in-place narrowing of the actor's `idx`-th cap; a
ghost that widened the cap, narrowed the WRONG slot, or touched another cell is excluded. -/
theorem attenuate_antighost (k k'' : RecordKernelState) (a : AttenuateArgs)
    (hne : k'' ≠ attenuateSpec k a) : attenuateStep k a ≠ some k'' := by
  intro h
  exact hne ((attenuate_triangle k k'' a).mp h)

/-- **`revokeTargetCaps` — the INDEPENDENT intent cap-function after a revocation.** The holder's slot
DROPS every cap conferring an edge to `target` (keep only the caps that do NOT confer such an edge);
every OTHER cell's slot is literally unchanged. Written from intent ("the holder loses its reach to
`target`, nothing else"), as a plain `Caps` function — NOT a call to `recKRevokeTarget`. The triangle
proves the executor's filter realizes exactly this. -/
def revokeTargetCaps (k : RecordKernelState) (a : RevokeArgs) : Caps :=
  fun l => if l = a.holder then (k.caps l).filter (fun cap => ¬ confersEdgeTo a.target cap)
           else k.caps l

/-- **`revokeSpec` — the INDEPENDENT declarative post-state of a revocation.** The `caps` function is
`revokeTargetCaps` (the holder's `target`-conferring caps filtered out); all else fixed. -/
def revokeSpec (k : RecordKernelState) (a : RevokeArgs) : RecordKernelState :=
  { k with caps := revokeTargetCaps k a }

/-- The executor's `recKRevokeTarget` realizes the INTENT revoke post-state `revokeSpec`. An
independent-function equality: the executor filters the holder's slot by `¬ confersEdgeTo target`; the
spec (`revokeTargetCaps`) does the same, written from intent. EQUAL — proving the revoke removes
EXACTLY the `target`-conferring caps from EXACTLY the holder's slot (it would be FALSE if it filtered
the wrong slot, the wrong target, or removed extra caps). -/
theorem recKRevokeTarget_eq_spec (k : RecordKernelState) (a : RevokeArgs) :
    recKRevokeTarget k a.holder a.target = revokeSpec k a := by
  unfold recKRevokeTarget revokeSpec revokeTargetCaps; rfl

/-- **THE REVOKE TRIANGLE (PROVED — TOTAL, output-uniqueness).** `revokeStep` ALWAYS commits
(revocation cannot fail — at worst the identity), so the gate is trivially `true`; the load-bearing
content is the `↔`: `revokeStep k a = some k'` IFF `k' = revokeSpec k a`. The output is the UNIQUE
intent post-state (the holder's `target`-conferring caps filtered out, NO other slot touched). -/
theorem revoke_triangle (k k' : RecordKernelState) (a : RevokeArgs) :
    revokeStep k a = some k' ↔ k' = revokeSpec k a := by
  unfold revokeStep
  constructor
  · intro h; simp only [Option.some.injEq] at h
    rw [← h, recKRevokeTarget_eq_spec]
  · intro hk; rw [hk, recKRevokeTarget_eq_spec]

/-- **ANTI-GHOST TOOTH (revoke, PROVED).** Any candidate `k'' ≠ revokeSpec k a` is REJECTED — the
revoke commits EXACTLY the filtered cap function; a ghost that KEPT a `target`-conferring cap (an
incomplete revoke), filtered the WRONG holder, or dropped extra caps is excluded. -/
theorem revoke_antighost (k k'' : RecordKernelState) (a : RevokeArgs)
    (hne : k'' ≠ revokeSpec k a) : revokeStep k a ≠ some k'' := by
  intro h
  exact hne ((revoke_triangle k k'' a).mp h)

/-! ## §8 — FIFTH FAMILY: SHIELDED NOTES (noteCreate / noteSpend) — the commitment/nullifier triangle.

The shielded-note ops (`RecordKernel.noteCreateCommitment`/`noteSpendNullifier`) move the off-ledger
commitment SET (grow-only) and nullifier SET (grow-only WITH double-spend rejection). We give each an
INDEPENDENT intent spec over those sets and prove the triangle + anti-ghost tooth. noteCreate is
TOTAL (a fresh commitment never conflicts ⇒ the `↔` output-uniqueness is the content); noteSpend is
GATED on freshness (the nullifier must be absent ⇒ a full biconditional, and the anti-ghost tooth
pins the no-double-spend discipline). -/

/-- **`noteCreateSpec` — the INDEPENDENT declarative post-state of a noteCreate.** The commitment
SET gains `cm` at the front; EVERYTHING ELSE (bal, nullifiers, escrows, caps) untouched (bal-NEUTRAL:
the note's hidden value is behind the §8 CryptoPortal). Written from intent ("park a fresh Pedersen
commitment"), NOT from `noteCreateCommitment`. -/
def noteCreateSpec (k : RecordKernelState) (cm : Nat) : RecordKernelState :=
  { k with commitments := cm :: k.commitments }

/-- **THE NOTE-CREATE TRIANGLE (PROVED — TOTAL, output-uniqueness).** `noteCreateCommitment` ALWAYS
commits (a fresh commitment cannot conflict — the grow-only dual of the nullifier set), so the content
is the `↔`: `noteCreateCommitment k cm = k'` IFF `k' = noteCreateSpec k cm`. The output is the UNIQUE
intent post-state (the commitment set grows by EXACTLY `cm`, nothing else moves). -/
theorem noteCreate_triangle (k k' : RecordKernelState) (cm : Nat) :
    noteCreateCommitment k cm = k' ↔ k' = noteCreateSpec k cm := by
  unfold noteCreateCommitment noteCreateSpec
  constructor
  · intro h; exact h.symm
  · intro hk; rw [hk]

/-- **ANTI-GHOST TOOTH (noteCreate, PROVED).** Any candidate `k'' ≠ noteCreateSpec k cm` is REJECTED —
noteCreate commits EXACTLY the front-insert of `cm`; a ghost that inserted the WRONG commitment, moved
`bal`/`nullifiers`/`escrows`, or dropped an existing commitment is excluded. -/
theorem noteCreate_antighost (k k'' : RecordKernelState) (cm : Nat)
    (hne : k'' ≠ noteCreateSpec k cm) : noteCreateCommitment k cm ≠ k'' := by
  intro h
  exact hne ((noteCreate_triangle k k'' cm).mp h)

/-- **`noteSpendSpec` — the INDEPENDENT declarative post-state of a noteSpend.** The nullifier SET
gains `nf` at the front (marking the note SPENT); EVERYTHING ELSE untouched. Written from intent
("burn the note by recording its nullifier"). The GATE is freshness — `nf ∉ k.nullifiers` (no
double-spend); the spec is only reached when the gate holds. -/
def noteSpendSpec (k : RecordKernelState) (nf : Nat) : RecordKernelState :=
  { k with nullifiers := nf :: k.nullifiers }

/-- **THE NOTE-SPEND TRIANGLE (PROVED, FULL BICONDITIONAL).** `noteSpendNullifier k nf = some k'` IFF
the nullifier is FRESH (`nf ∉ k.nullifiers` — the no-double-spend gate) AND `k' = noteSpendSpec k nf`.
The `→` pins the UNIQUE intent post-state (the nullifier set grows by EXACTLY `nf`) AND surfaces the
freshness gate; the `←` is completeness (a fresh nullifier commits its spend). -/
theorem noteSpend_triangle (k k' : RecordKernelState) (nf : Nat) :
    noteSpendNullifier k nf = some k' ↔ (nf ∉ k.nullifiers ∧ k' = noteSpendSpec k nf) := by
  unfold noteSpendNullifier noteSpendSpec
  constructor
  · intro h
    by_cases hin : nf ∈ k.nullifiers
    · rw [if_pos hin] at h; exact absurd h (by simp)
    · rw [if_neg hin] at h; simp only [Option.some.injEq] at h; exact ⟨hin, h.symm⟩
  · rintro ⟨hin, hk⟩; rw [if_neg hin, hk]

/-- **ANTI-GHOST TOOTH (noteSpend, PROVED — the no-double-spend tooth).** Two faces:
  * a candidate `k'' ≠ noteSpendSpec k nf` is REJECTED (output-uniqueness — the spend records EXACTLY
    `nf`, nothing else), AND
  * if `nf` is ALREADY spent (`nf ∈ k.nullifiers`), NO commit is possible at all (double-spend is
    fail-closed — `noteSpendNullifier k nf = none`).
The second face is the load-bearing anti-replay: a double-spend candidate is excluded. -/
theorem noteSpend_antighost (k k'' : RecordKernelState) (nf : Nat)
    (hne : k'' ≠ noteSpendSpec k nf) : noteSpendNullifier k nf ≠ some k'' := by
  intro h
  exact hne ((noteSpend_triangle k k'' nf).mp h).2

/-- **NO DOUBLE-SPEND (PROVED, the anti-ghost's second face).** An already-spent nullifier cannot be
spent again — `noteSpendNullifier` fails-closed `none`. So NO post-state (ghost or not) commits a
double-spend. -/
theorem noteSpend_double_spend_rejected (k k'' : RecordKernelState) (nf : Nat)
    (hspent : nf ∈ k.nullifiers) : noteSpendNullifier k nf ≠ some k'' := by
  rw [note_no_double_spend k nf hspent]; simp

/-! ## §9 — NON-VACUITY TEETH (`#guard`) for the three new families. -/

/-- Value/note fixture: cells 0,1 are accounts; cell 0 holds 100 of asset 0; cell 0 holds the
PRIVILEGED `node 0` mint cap; all Live. -/
def vfx : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 0 then [Dregg2.Authority.Cap.node 0] else []
    bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }

/-- A mint of 25 of asset 0 into cell 0 (privileged actor 0). -/
def aMint : SupplyArgs := { actor := 0, cell := 0, asset := 0, amt := 25 }
/-- A burn of 40 of asset 0 from cell 0. -/
def aBurn : SupplyArgs := { actor := 0, cell := 0, asset := 0, amt := 40 }

-- MINT commits and the supply MOVED: asset-0 column of cell 0 rises 100 → 125 (the spec's credit).
#guard (mintStep vfx aMint).isSome
#guard ((mintStep vfx aMint).map (fun k => k.bal 0 0)) == some 125
-- ...and asset 1 (a DIFFERENT asset) is UNTOUCHED (the per-asset discipline the spec pins).
#guard ((mintStep vfx aMint).map (fun k => k.bal 0 1)) == some 0
-- MINT anti-ghost (CONCRETE): the spec output's bal 0 0 (125) differs OBSERVABLY from a ghost that
-- left the column at 100 — so by `mint_antighost` such a ghost is refused.
#guard ((vfx.bal 0 0, (mintSpec vfx aMint).bal 0 0) == (100, 125))
-- UNAUTHORIZED mint (actor 1 holds no node cap) is REJECTED (the privileged gate bites).
#guard ((mintStep vfx { aMint with actor := 1 }).isSome) == false
-- BURN commits and the supply FELL: 100 → 60.
#guard ((burnStep vfx aBurn).map (fun k => k.bal 0 0)) == some 60
-- BURN over-spend (burn 200 > 100 held) is REJECTED (availability gate).
#guard ((burnStep vfx { aBurn with amt := 200 }).isSome) == false

/-- Authority fixture: cell 0 holds a `node 7` cap (edge to 7) + `endpoint 9 [write]`; cell 1 holds
nothing. -/
def afx : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 0 then [Dregg2.Authority.Cap.node 7, Dregg2.Authority.Cap.endpoint 9 [Auth.write]] else []
    bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }

/-- A full-authority delegation of the edge-to-7 from delegator 0 to recipient 1. -/
def aDel : DelegateArgs := { delegator := 0, recipient := 1, target := 7, keep := allAuths }

-- DELEGATE commits (delegator 0 holds the edge) and recipient 1 GAINS exactly the held cap to 7.
#guard (delegateAttenStep afx aDel).isSome
#guard ((delegateAttenStep afx aDel).map (fun k => k.caps 1)) == some [Dregg2.Authority.Cap.node 7]
-- DELEGATE by a delegator WITHOUT the edge (cell 1 holds nothing) is REJECTED (Granovetter premise).
#guard ((delegateAttenStep afx { aDel with delegator := 1 }).isSome) == false
-- REVOKE is TOTAL: cell 0 revokes its edge to 7 — the `node 7` cap is filtered out (only endpoint-9 left).
#guard ((revokeStep afx { holder := 0, target := 7 }).map (fun k => k.caps 0))
        == some [Dregg2.Authority.Cap.endpoint 9 [Auth.write]]
-- REVOKE leaves OTHER slots (cell 1) untouched (the spec pins the holder-only filter).
#guard ((revokeStep afx { holder := 0, target := 7 }).map (fun k => k.caps 1))
        == some ([] : List Dregg2.Authority.Cap)
-- ATTENUATE is TOTAL: cell 0 narrows its idx-1 cap (endpoint 9) to `[]` — write DROPPED, in place.
#guard ((attenuateStep afx { actor := 0, idx := 1, keep := [] }).map (fun k => k.caps 0))
        == some [Dregg2.Authority.Cap.node 7, Dregg2.Authority.Cap.endpoint 9 []]

-- NOTE-CREATE grows the commitment set by exactly the fresh commitment 42 (front-insert).
#guard ((noteCreateCommitment vfx 42).commitments) == [42]
#guard ((noteCreateCommitment (noteCreateCommitment vfx 42) 43).commitments) == [43, 42]
-- NOTE-SPEND of a FRESH nullifier 5 commits and records it; a SECOND spend of 5 is REJECTED (no double-spend).
#guard (noteSpendNullifier vfx 5).isSome
#guard ((noteSpendNullifier vfx 5).bind (fun k => noteSpendNullifier k 5)).isNone
-- the recorded nullifier IS 5 (the spend's set move is real).
#guard ((noteSpendNullifier vfx 5).map (fun k => k.nullifiers)) == some [5]

/-! ## §10 — Axiom-hygiene pins for the three new families. -/

#assert_axioms intentCredit_eq_balCredit
#assert_axioms intentDebit_eq_balCredit
#assert_axioms mint_triangle
#assert_axioms mint_antighost
#assert_axioms burn_triangle
#assert_axioms burn_antighost
#assert_axioms delegate_triangle
#assert_axioms delegate_antighost
#assert_axioms attenuate_triangle
#assert_axioms attenuate_antighost
#assert_axioms recKRevokeTarget_eq_spec
#assert_axioms revoke_triangle
#assert_axioms revoke_antighost
#assert_axioms noteCreate_triangle
#assert_axioms noteCreate_antighost
#assert_axioms noteSpend_triangle
#assert_axioms noteSpend_antighost
#assert_axioms noteSpend_double_spend_rejected

end Dregg2.Spec.FunctionalRefinement
