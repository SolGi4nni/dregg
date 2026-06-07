/-
# Dregg2.Apps.Subscription — dregg1's SUBSCRIPTION app as a verified cell-program (a carried-safety crown).

dregg1's `starbridge-apps/subscription/src/lib.rs` is a `CapInbox`-shaped publish/consume queue — the
subscription app's real load-bearing primitive (`STORAGE-AS-CELL-PROGRAMS.md` §3.1). Its 8-slot cell
layout pins three counters and the headline safety:

  | slot 0 | `seq_head` | producer cursor — a `publish` advances it `+1` (`MonotonicSequence`) |
  | slot 1 | `seq_tail` | consumer cursor — a `consume` advances it `+1` (`MonotonicSequence`) |
  | slot 2 | `capacity` | max in-flight messages — `Immutable`, set at creation |

and the `Always`-guarded **invariant** `state_constraints` bakes in (`lib.rs:272`, `:509`):

  > `StateConstraint::FieldLteField { left_index: SEQ_TAIL_SLOT, right_index: SEQ_HEAD_SLOT }`

i.e. **`seq_tail ≤ seq_head`** — *a consumer never reads past a producer*. The integration test
(`tests/integration_publish_consume.rs:239`) is its boundary teeth: *"consuming from an empty queue
(tail > head) must be rejected"*. Plus the capacity headline (`tests/program.rs:18` "write past
capacity → rejected"): the in-flight count `head − tail` never exceeds `capacity`.

This module models that CORE in Lean and proves + CARRIES the headline safety, in BOTH registers:

* **§A — the faithful self-contained automaton.** `SubState` carries dregg1's three slots
  (`head`/`tail`/`capacity`); `publish` advances `head` (gated `inFlight < capacity` — the capacity
  bound) and `consume` advances `tail` (gated `tail < head` — the non-empty / "no read past producer"
  gate). The invariant `WF s := s.tail ≤ s.head ∧ s.head − s.tail ≤ s.capacity` is preserved by EACH
  operation (`publish_preserves_WF` / `consume_preserves_WF`), and carried along ANY unbounded stream
  of publish/consume operations (`subscription_consumer_safe_forever`) by plain induction — the dregg1
  `seq_tail ≤ seq_head` headline, proved + forever, on the slot automaton. The decrement/overflow
  REJECTIONS have teeth (`consume_empty_rejected` / `publish_full_rejected`).

* **§B — the SAME safety on the REAL living cell.** dregg1's queue IS the `RecordKernel` `queues`
  side-table (a `QueueRecord` per subscription, `buffer.length` = in-flight count, `capacity` = the
  cap), driven by the SHIPPED executor `execFullForestA` via `queueEnqueueA` (publish) /
  `queueDequeueA` (consume) / `queueAllocateA` / `queueResizeA`. The subscription well-formedness
  `subWF k := ∀ q ∈ k.queues, q.buffer.length ≤ q.capacity` (NO queue ever over capacity — the
  in-flight bound on EVERY subscription) is preserved by a SINGLE committed `FullActionA`
  (`execFullA_subWF_preserved`, the 46-arm registry FRAME, mirroring `CellNullifier`'s nullifier
  frame) and therefore — by `CellCarry.livingCellA_carries` — holds along the ENTIRE unbounded
  adversarial trajectory under EVERY schedule: **`subscription_wellformed_forever`**. The capacity
  gate of `queueEnqueueK` (fail-closed at full) is exactly what makes the FRAME hold; a flag-only
  queue model could not even state it.

So the headline `subscription_consumer_safe_forever` (the dregg1 `tail ≤ head` relation, on the
faithful slot automaton) is matched by `subscription_wellformed_forever` (the SAME no-overflow safety,
carried by the REAL `execFullForestA` living cell, against any adversary, forever).

Templates: `Apps/RightOfWay.lean` (the self-contained automaton + teeth), `Exec/CellNullifier.lean`
(the per-effect kernel FRAME routed through `livingCellA_carries`). Reuses `Exec/CellCarry`'s crown +
`RecordKernel`'s queue transitions; edits nothing. Zero `sorry`/`admit`/`native_decide`/`axiom`; every
keystone `#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Exec.CellCarry

namespace Dregg2.Apps.Subscription

open Dregg2.Boundary
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Authority
open Dregg2.Exec.EffectsState (stateStep stateStep_factors stateStepGuarded_eq)
open Dregg2.Tactics

/-! ## §A — The faithful self-contained slot automaton: `seq_tail ≤ seq_head`, proved + carried forever.

dregg1's subscription cell is an 8-slot record; the three counters that carry the headline safety are
`seq_head` (slot 0), `seq_tail` (slot 1), `capacity` (slot 2). We model exactly those three and the
two cursor-advancing operations (publish / consume), with the dregg1 guards, as a self-contained
decidable automaton — the `RightOfWay.Scenario` shape. -/

/-- **A subscription cell's state** — dregg1's three load-bearing slots (`lib.rs:168-172`):
`head` (slot 0, the producer cursor), `tail` (slot 1, the consumer cursor), `capacity` (slot 2, the
max in-flight count, immutable). The other 5 slots (roots / owner / message_root / latest_payload)
are authority/data, orthogonal to the cursor safety; we model the cursors. -/
structure SubState where
  /-- `seq_head` (slot 0) — the producer cursor: # of messages ever published. A `publish` advances it. -/
  head     : Nat
  /-- `seq_tail` (slot 1) — the consumer cursor: # of messages ever consumed. A `consume` advances it. -/
  tail     : Nat
  /-- `capacity` (slot 2) — the immutable max in-flight count (`head − tail ≤ capacity`). -/
  capacity : Nat
  deriving Repr, DecidableEq

/-- **The in-flight count** `head − tail` (truncated `Nat` subtraction): the # of published-but-unconsumed
messages currently in the queue. dregg1's `MerkleQueue` occupancy; the capacity bound caps THIS. -/
def SubState.inFlight (s : SubState) : Nat := s.head - s.tail

/-- **`WF s` — the subscription well-formedness invariant.** Two conjuncts, exactly dregg1's baked-in
constraints: `tail ≤ head` (the `FieldLteField` invariant — *consumer never reads past producer*) AND
`head − tail ≤ capacity` (the in-flight count is within capacity — *no overflow*). This is the
predicate the living cell carries forever (in both §A and, transported, §B). -/
def SubState.WF (s : SubState) : Prop := s.tail ≤ s.head ∧ s.head - s.tail ≤ s.capacity

/-- `WF` is decidable (a conjunction of `Nat ≤`) — so the `#eval` non-vacuity checks can `decide` it. -/
instance (s : SubState) : Decidable s.WF := by unfold SubState.WF; infer_instance

/-- **`publish s` — advance the producer cursor (slot 0 `+1`), gated by the CAPACITY bound.** A publish
is admissible iff the queue is NOT full (`inFlight < capacity`, dregg1 `apply.rs:3348` — enqueue rejects
fail-closed at capacity); then `head := head + 1`. `none` when full (the fail-closed self-loop). The
`MonotonicSequence` head advance of the `publish` case (`lib.rs:288`). -/
def publish (s : SubState) : Option SubState :=
  if s.inFlight < s.capacity then some { s with head := s.head + 1 } else none

/-- **`consume s` — advance the consumer cursor (slot 1 `+1`), gated by NON-EMPTINESS.** A consume is
admissible iff the queue is NON-empty (`tail < head` — equivalently `inFlight > 0`; dregg1
`apply.rs:3444` — dequeue rejects fail-closed when empty; the test "consuming from an empty queue
(tail > head) must be rejected"); then `tail := tail + 1`. `none` when empty. The `MonotonicSequence`
tail advance of the `consume` case (`lib.rs:325`). -/
def consume (s : SubState) : Option SubState :=
  if s.tail < s.head then some { s with tail := s.tail + 1 } else none

/-- **`publish_preserves_WF` (PROVED).** A committed publish preserves `WF`: `head` rises by one, so
`tail ≤ head` is maintained (`tail ≤ head ≤ head+1`), and the in-flight count rises by one but the
publish gate `inFlight < capacity` guarantees the new `inFlight = (head+1) − tail ≤ capacity`. The
`Always`-invariant + the `publish`-case capacity discipline, in one step. -/
theorem publish_preserves_WF (s s' : SubState) (hwf : s.WF) (h : publish s = some s') : s'.WF := by
  unfold publish at h
  by_cases hc : s.inFlight < s.capacity
  · rw [if_pos hc] at h
    obtain ⟨rfl⟩ := h
    simp only [SubState.WF, SubState.inFlight] at hwf hc ⊢
    omega
  · rw [if_neg hc] at h; exact absurd h (by simp)

/-- **`consume_preserves_WF` (PROVED).** A committed consume preserves `WF`: `tail` rises by one but
the consume gate `tail < head` guarantees the new `tail ≤ head`, and the in-flight count `head − tail`
DROPS by one (so the capacity bound is maintained a fortiori). The `Always`-invariant + the
`consume`-case non-emptiness discipline, in one step. -/
theorem consume_preserves_WF (s s' : SubState) (hwf : s.WF) (h : consume s = some s') : s'.WF := by
  unfold consume at h
  by_cases hc : s.tail < s.head
  · rw [if_pos hc] at h
    obtain ⟨rfl⟩ := h
    simp only [SubState.WF] at hwf ⊢
    omega
  · rw [if_neg hc] at h; exact absurd h (by simp)

/-! ### §A.teeth — the rejections are REAL (the invariant is not vacuously preserved). -/

/-- **`consume_empty_rejected` (PROVED) — the empty-queue gate has teeth.** A consume on an EMPTY queue
(`tail = head`, so `inFlight = 0`) is REJECTED (`none`): the consumer cannot read past the producer.
This is dregg1's "consuming from an empty queue (tail > head) must be rejected" at its boundary
(`tail = head`). NON-VACUOUS: the `consume` gate genuinely fail-closes. -/
theorem consume_empty_rejected (s : SubState) (h : s.tail = s.head) : consume s = none := by
  unfold consume; rw [if_neg (by omega)]

/-- **`publish_full_rejected` (PROVED) — the capacity gate has teeth.** A publish into a FULL queue
(`inFlight = capacity`) is REJECTED (`none`): no overflow past `capacity`. dregg1's "write past
capacity → rejected". NON-VACUOUS: the `publish` gate genuinely fail-closes. -/
theorem publish_full_rejected (s : SubState) (h : s.inFlight = s.capacity) : publish s = none := by
  unfold publish; rw [if_neg (by omega)]

/-! ### §A.forever — the dregg1 `tail ≤ head` headline carried along ANY publish/consume stream.

An OPERATION is a publish or a consume; a SCHEDULE is an infinite stream of operations (the unbounded
adversarial driver, the `CellCarry.SchedA` shape for the abstract automaton). `subStep` runs one
operation, STAYING PUT on an inadmissible one (the Moore self-loop — `livingCellA`'s `cellNextA`
shape). The trajectory `subTraj` unfolds it. Then `WF` — the dregg1 `tail ≤ head` (+ capacity) —
holds at EVERY index, forever, by plain induction (the abstract face of `livingCellA_carries`). -/

/-- A subscription operation: publish (producer) or consume (consumer) — the two cursor-advancing
cell-program methods. -/
inductive SubOp where
  /-- a `publish` (producer advances `head`). -/
  | pub
  /-- a `consume` (consumer advances `tail`). -/
  | con
  deriving Repr, DecidableEq

/-- An infinite adversarial schedule of subscription operations (the abstract automaton's driver). -/
def SubSched : Type := Nat → SubOp

/-- **One subscription step, STAY-PUT on rejection** (the fail-closed self-loop — `livingCellA`'s
`cellNextA` shape lifted to the abstract automaton): run the operation; on `none` (full publish /
empty consume) keep the state unchanged. -/
def subStep (s : SubState) : SubOp → SubState
  | .pub => (publish s).getD s
  | .con => (consume s).getD s

/-- The unbounded **trajectory**: unfold `subStep` along the schedule (the abstract `trajA`). -/
def subTraj (s : SubState) (sched : SubSched) : Nat → SubState
  | 0     => s
  | n + 1 => subStep (subTraj s sched n) (sched n)

/-- **`subStep_preserves_WF` (PROVED) — one step keeps the subscription well-formed.** Whichever
operation fires, `WF` survives: publish via `publish_preserves_WF`, consume via `consume_preserves_WF`,
and the STAY-PUT self-loop on a rejected operation trivially preserves it (the state is unchanged). -/
theorem subStep_preserves_WF (s : SubState) (op : SubOp) (hwf : s.WF) : (subStep s op).WF := by
  cases op with
  | pub =>
      show (publish s).getD s |>.WF
      cases hp : publish s with
      | some s' => simp only [Option.getD_some]; exact publish_preserves_WF s s' hwf hp
      | none    => simp only [Option.getD_none]; exact hwf
  | con =>
      show (consume s).getD s |>.WF
      cases hp : consume s with
      | some s' => simp only [Option.getD_some]; exact consume_preserves_WF s s' hwf hp
      | none    => simp only [Option.getD_none]; exact hwf

/-- **`subscription_consumer_safe_forever` (PROVED) — THE HEADLINE on the slot automaton: a consumer
never reads past a producer, FOREVER.** From any well-formed start, along the ENTIRE unbounded stream
of publish/consume operations — under EVERY adversarial schedule — the subscription stays well-formed:
`(subTraj s sched n).WF` at EVERY index `n`, i.e. `seq_tail ≤ seq_head` AND `head − tail ≤ capacity`
hold for all time. The dregg1 `FieldLteField`/`Always` invariant (`lib.rs:272`), carried by plain
induction (`subStep_preserves_WF` at each step) — the abstract face of `livingCellA_carries`. -/
theorem subscription_consumer_safe_forever (s : SubState) (hinit : s.WF) (sched : SubSched) :
    ∀ n, (subTraj s sched n).WF := by
  intro n
  induction n with
  | zero => exact hinit
  | succ k ih =>
      show (subStep (subTraj s sched k) (sched k)).WF
      exact subStep_preserves_WF _ _ ih

/-! ## §B — The SAME safety on the REAL living cell: `subWF` carried by `livingCellA_carries`.

dregg1's subscription queue IS the `RecordKernel` `queues` side-table. A subscription is a
`QueueRecord` whose `buffer.length` is the in-flight count and `capacity` is the cap; `publish` is a
`queueEnqueueA` (append, fail-closed at `capacity`), `consume` is a `queueDequeueA` (remove-from-front,
fail-closed when empty), all driven by the SHIPPED `execFullForestA`. The §A in-flight bound, on this
real substrate, is `subWF`: NO queue is ever over capacity. We prove the REAL executor preserves it
per-step and carry it forever — the §B match of §A's headline. -/

/-- **`subWF k` — the subscription well-formedness on the REAL kernel.** EVERY queue record in the
`queues` side-table has its in-flight count within capacity: `q.buffer.length ≤ q.capacity`. This is
dregg1's "no subscription ever exceeds its capacity" — the in-flight bound (`head − tail ≤ capacity`)
realized on the executable queue (`buffer.length` IS `head − tail`). The predicate carried by
`livingCellA_carries`. -/
def subWF (k : RecordKernelState) : Prop := ∀ q ∈ k.queues, q.buffer.length ≤ q.capacity

/-! ### §B.0 — `queues`-frame helpers (the side-table bookkeeping shared by the 46-arm dispatch).

`subWF` is a `∀ q ∈ k.queues` bound. Two structural facts discharge every arm: (1) if a committed step
leaves `queues` UNCHANGED, `subWF` is preserved verbatim (the 42 non-queue arms + the bridge); (2) the
4 queue arms either CONS a within-capacity record (allocate: empty buffer, `0 ≤ cap`) or `replaceQueue`
the touched id with a within-capacity record (enqueue: gated `len < cap` ⇒ `len+1 ≤ cap`; dequeue:
buffer shrinks; resize: gated `len ≤ newCap`) — `replaceQueue_subWF` handles the replace shape. -/

/-- **`subWF_of_queues_eq` (PROVED).** If `k'.queues = k.queues`, then `subWF k → subWF k'`. The frame
the 42 non-queue effects ride (their kernel transform updates a field OTHER than `queues`, so the
projection is `rfl`). -/
theorem subWF_of_queues_eq {k k' : RecordKernelState} (hq : k'.queues = k.queues) (h : subWF k) :
    subWF k' := by
  intro q hqmem; rw [hq] at hqmem; exact h q hqmem

/-- **`subWF_cons` (PROVED).** Consing a within-capacity record onto a `subWF` queue list stays
`subWF`. The allocate shape: the fresh queue has an EMPTY buffer (`0 ≤ capacity`). -/
theorem subWF_cons {qs : List QueueRecord} (q0 : QueueRecord) (h0 : q0.buffer.length ≤ q0.capacity)
    (h : ∀ q ∈ qs, q.buffer.length ≤ q.capacity) :
    ∀ q ∈ q0 :: qs, q.buffer.length ≤ q.capacity := by
  intro q hq
  rcases List.mem_cons.mp hq with hq | hq
  · subst hq; exact h0
  · exact h q hq

/-- **`replaceQueue_subWF` (PROVED).** If every record of `qs` is within capacity AND the replacement
`q'` is within capacity, then every record of `replaceQueue qs id q'` is within capacity. The
enqueue/dequeue/resize shape: only the touched id's record changes (to a within-capacity one); every
other record is untouched (so its bound is inherited). -/
theorem replaceQueue_subWF {qs : List QueueRecord} {id : Nat} {q' : QueueRecord}
    (h : ∀ q ∈ qs, q.buffer.length ≤ q.capacity) (h' : q'.buffer.length ≤ q'.capacity) :
    ∀ q ∈ replaceQueue qs id q', q.buffer.length ≤ q.capacity := by
  intro q hq
  unfold replaceQueue at hq
  rw [List.mem_map] at hq
  obtain ⟨a, ha, hae⟩ := hq
  by_cases hc : (a.id == id) = true
  · rw [if_pos hc] at hae; subst hae; exact h'
  · rw [if_neg hc] at hae; subst hae; exact h a ha

/-! ### §B.1 — the deep kernel-op frames for the COMPOSED queue/escrow ops (enqueue-deposit / dequeue-refund).

`queueEnqueueDepositK` / `queueDequeueRefundK` compose the FIFO transition with an escrow PARK/SETTLE.
The escrow-raw ops (`createEscrowRawAsset`/`settleEscrowRawAsset`) update `bal`/`escrows` only — they
leave `queues` literally unchanged — so the COMPOSED op's `queues` is exactly the FIFO transition's
`queues`. We hoist the two composed frames (mirroring `CellNullifier`'s deep frames) to a clean
`subWF`-preservation, reusing the enqueue/dequeue `queues`-shape lemmas. -/

/-- `queueEnqueueK` preserves `subWF`: it `replaceQueue`s the touched id with a record whose buffer
grew by one but whose gate `len < capacity` ⇒ `len + 1 ≤ capacity` (within capacity). -/
private theorem queueEnqueueK_subWF {k k' : RecordKernelState} {id m : Nat}
    (hk : queueEnqueueK k id m = some k') (h : subWF k) : subWF k' := by
  unfold queueEnqueueK at hk
  cases hf : findQueue k.queues id with
  | none   => simp only [hf] at hk; exact absurd hk (by simp)
  | some q =>
      simp only [hf] at hk
      by_cases hc : q.buffer.length < q.capacity
      · rw [if_pos hc] at hk; simp only [Option.some.injEq] at hk; subst hk
        show ∀ qq ∈ replaceQueue k.queues id { q with buffer := qbufEnqueue q.buffer m }, _
        refine replaceQueue_subWF h ?_
        -- the replacement: buffer grew by one (`qbufEnqueue`), gate `len < cap` ⇒ `len + 1 ≤ cap`.
        show (qbufEnqueue q.buffer m).length ≤ q.capacity
        rw [qbuf_enqueue_length]; omega
      · rw [if_neg hc] at hk; exact absurd hk (by simp)

/-- `queueDequeueK` preserves `subWF`: it `replaceQueue`s the touched id with a record whose buffer
SHRANK (the tail of the old buffer), so its length only drops — still within capacity. -/
private theorem queueDequeueK_subWF {k k' : RecordKernelState} {id : Nat} {actor : CellId} {mh : Nat}
    (hk : queueDequeueK k id actor = some (k', mh)) (h : subWF k) : subWF k' := by
  unfold queueDequeueK at hk
  cases hf : findQueue k.queues id with
  | none   => simp only [hf] at hk; exact absurd hk (by simp)
  | some q =>
      simp only [hf] at hk
      by_cases ho : actor = q.owner
      · rw [if_pos ho] at hk
        cases hd : qbufDequeue q.buffer with
        | none        => rw [hd] at hk; exact absurd hk (by simp)
        | some hr =>
            obtain ⟨mm, rest⟩ := hr
            rw [hd] at hk; simp only [Option.some.injEq, Prod.mk.injEq] at hk
            obtain ⟨hkq, _⟩ := hk; subst hkq
            show ∀ qq ∈ replaceQueue k.queues id { q with buffer := rest }, _
            refine replaceQueue_subWF h ?_
            -- the replacement buffer `rest` is the dequeue tail: `q.buffer.length = rest.length + 1`,
            -- so `rest.length ≤ q.buffer.length ≤ q.capacity` (the old record was within capacity).
            show rest.length ≤ q.capacity
            have hlen : q.buffer.length = rest.length + 1 := qbuf_dequeue_length hd
            have hcap : q.buffer.length ≤ q.capacity := h q (List.mem_of_find?_eq_some hf)
            omega
      · rw [if_neg ho] at hk; exact absurd hk (by simp)

/-- `queueEnqueueDepositK` preserves `subWF`: it commits via `queueEnqueueK` (the `subWF`-mover) then
`createEscrowRawAsset` (a `bal`/`escrows`-only update — `queues` UNCHANGED). -/
private theorem queueEnqueueDepositK_subWF {k k' : RecordKernelState} {id m : Nat}
    {sender owner : CellId} {depId : Nat} {dAsset : AssetId} {deposit : ℤ}
    (hh : queueEnqueueDepositK k id m sender owner depId dAsset deposit = some k') (h : subWF k) :
    subWF k' := by
  unfold queueEnqueueDepositK at hh
  cases hq : queueEnqueueK k id m with
  | none    => simp only [hq] at hh; exact absurd hh (by simp)
  | some k₁ =>
      simp only [hq] at hh
      by_cases hg : 0 ≤ deposit ∧ deposit ≤ k₁.bal sender dAsset ∧ sender ∈ k₁.accounts
          ∧ ¬ (∃ r ∈ k₁.escrows, r.id = depId)
      · rw [if_pos hg] at hh; simp only [Option.some.injEq] at hh; subst hh
        -- `k' = createEscrowRawAsset k₁ … = { k₁ with bal := …, escrows := … }` ⇒ `queues` = `k₁.queues`.
        refine subWF_of_queues_eq (k := k₁) ?_ (queueEnqueueK_subWF hq h)
        rfl
      · rw [if_neg hg] at hh; exact absurd hh (by simp)

/-- `queueDequeueRefundK` preserves `subWF`: it commits via `queueDequeueK` (the `subWF`-mover) then
`settleEscrowRawAsset` (a `bal`/`escrows`-only update — `queues` UNCHANGED). -/
private theorem queueDequeueRefundK_subWF {k k' : RecordKernelState} {id : Nat} {actor : CellId}
    {depId : Nat} {mh : Nat}
    (hh : queueDequeueRefundK k id actor depId = some (k', mh)) (h : subWF k) : subWF k' := by
  unfold queueDequeueRefundK at hh
  cases hq : queueDequeueK k id actor with
  | none          => rw [hq] at hh; exact absurd hh (by simp)
  | some kp =>
      obtain ⟨k₁, mh₁⟩ := kp
      rw [hq] at hh; simp only [] at hh
      by_cases hbind : dequeueMsgBindB k₁ actor depId id mh₁
      · rw [if_pos hbind] at hh
        cases hfind : findUnresolvedDeposit k₁ depId with
        | none => simp only [hfind] at hh; exact absurd hh (by simp)
        | some r =>
            simp only [hfind] at hh
            by_cases ha : actor ∈ k₁.accounts
            · rw [if_pos ha, Option.some.injEq, Prod.mk.injEq] at hh
              obtain ⟨hhk, _⟩ := hh; subst hhk
              refine subWF_of_queues_eq (k := k₁) ?_ (queueDequeueK_subWF hq h)
              rfl
            · rw [if_neg ha] at hh; exact absurd hh (by simp)
      · rw [if_neg hbind] at hh; exact absurd hh (by simp)

/-- WAVE 4: one atomic-batch sub-op preserves `subWF` (the deposit-enqueue / refund-dequeue movers). -/
private theorem queueTxOpStepA_subWF {s s' : RecChainedState} {op : QueueTxOpA}
    (hh : queueTxOpStepA s op = some s') (h : subWF s.kernel) : subWF s'.kernel := by
  cases op with
  | enqueue id m actor cell depId dAsset deposit =>
      simp only [queueTxOpStepA, queueEnqueueChainA] at hh; split at hh
      · cases hk : queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit with
        | none => rw [hk] at hh; exact absurd hh (by simp)
        | some k' => rw [hk] at hh; simp only [Option.some.injEq] at hh; subst hh
                     exact queueEnqueueDepositK_subWF hk h
      · exact absurd hh (by simp)
  | dequeue id actor cell depId =>
      simp only [queueTxOpStepA, queueDequeueChainA] at hh; split at hh
      · cases hk : queueDequeueRefundK s.kernel id actor depId with
        | none => rw [hk] at hh; exact absurd hh (by simp)
        | some p => obtain ⟨k', mh⟩ := p
                    rw [hk] at hh; simp only [Option.some.injEq] at hh; subst hh
                    exact queueDequeueRefundK_subWF hk h
      · exact absurd hh (by simp)

/-- WAVE 4: the ALL-OR-NOTHING atomic batch preserves `subWF` (induction over the sub-ops). -/
private theorem queueAtomicTxChainA_subWF {s s' : RecChainedState} {ops : List QueueTxOpA}
    (hh : queueAtomicTxChainA s ops = some s') (h : subWF s.kernel) : subWF s'.kernel := by
  induction ops generalizing s with
  | nil => simp only [queueAtomicTxChainA, Option.some.injEq] at hh; subst hh; exact h
  | cons op rest ih =>
      simp only [queueAtomicTxChainA] at hh
      cases hop : queueTxOpStepA s op with
      | none => rw [hop] at hh; exact absurd hh (by simp)
      | some s1 => rw [hop] at hh; exact ih hh (queueTxOpStepA_subWF hop h)

/-- WAVE 4: the pipeline fan-out enqueue fold preserves `subWF` (each sink `queueEnqueueK` is within cap). -/
private theorem pipelineFanoutK_subWF {k k' : RecordKernelState} {actor : CellId} {m : Nat}
    {sinks : List CellId} {sids : List Nat}
    (hh : pipelineFanoutK k actor m sinks sids = some k') (h : subWF k) : subWF k' := by
  induction sinks generalizing k sids with
  | nil => cases sids <;> (simp only [pipelineFanoutK, Option.some.injEq] at hh; subst hh; exact h)
  | cons sink rest ih =>
      cases sids with
      | nil => simp only [pipelineFanoutK] at hh; exact absurd hh (by simp)
      | cons sid sids' =>
          simp only [pipelineFanoutK] at hh; split at hh
          · cases hq : queueEnqueueK k sid m with
            | none => rw [hq] at hh; exact absurd hh (by simp)
            | some k1 => rw [hq] at hh; exact ih hh (queueEnqueueK_subWF hq h)
          · exact absurd hh (by simp)

/-! ### §B.2 — `execFullA_subWF_preserved`: the per-effect FRAME (the 46-arm dispatch).

Mirrors `CellNullifier.execFullA_nullifiers_grow`'s walk. Only the FOUR queue arms touch `queues`
(each preserves the bound — allocate adds an empty buffer, enqueue's gate is `len < cap`, dequeue
shrinks, resize's gate is `len ≤ newCap`); the OTHER 42 arms leave `queues` literally unchanged, so
`subWF` is preserved via `subWF_of_queues_eq` (the `.queues` projection is `rfl` for a record-update of
another field). -/

mutual
/-- **`execFullA_subWF_preserved` (PROVED) — the per-effect subscription FRAME.** A committed
`FullActionA` preserves `subWF`: NO queue ends over capacity. The four queue effects move `queues` but
keep every record within capacity (the capacity gate of `queueEnqueueK` / the resize gate / the
allocate-empty / the dequeue-shrink); the other effects touch other kernel fields only (frame: `queues`
literally unchanged); `exerciseA` RECURSES (mutual `execInnerA_subWF_preserved`). The structural dual of
the conservation frame `execFullA_ledger_per_asset` and `CellNullifier`'s `execFullA_nullifiers_grow`. -/
theorem execFullA_subWF_preserved (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s') (hwf : subWF s.kernel) : subWF s'.kernel := by
  cases fa with
  -- §catalog/supply/authority — chained `match kernelOp | some k' => some {kernel:=k',…}` wrappers;
  -- the kernel op updates a NON-`queues` field, so `s'.kernel.queues = s.kernel.queues` (`rfl`).
  | balanceA t a =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := recCexecAsset_factors t a (by simpa only [execFullA] using h)
      subst h'
      refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
      unfold recKExecAsset at hk; split at hk
      · injection hk with hk; subst hk; rfl
      · exact absurd hk (by simp)
  | delegate del rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel del rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
          unfold recKDelegate at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | revoke holder t =>
      simp only [execFullA, recCRevoke] at h
      obtain ⟨rfl⟩ := h; exact hwf
  | mintA actor cell a amt =>
      simp only [execFullA, recCMintAsset] at h
      cases hk : recKMintAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
          unfold recKMintAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | burnA actor cell a amt =>
      simp only [execFullA, recCBurnAsset] at h
      cases hk : recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
          unfold recKBurnAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  -- §pure-state — `stateStep` / `emitStep` (field write / event), a `cell`-only update.
  | setFieldA actor cell f v =>
      -- §SLOT-CAVEAT: peel the caveat gate (`stateStepGuarded_eq`); the field write never edits `queues`.
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors (stateStepGuarded_eq h); subst hs'; exact hwf
  | emitEventA actor cell topic data =>
      -- §LIVE-CELL: `emitEventA` now gates the authority-free log append on `cell ∈ accounts`. Peel the
      -- live-cell `if`; a committed emit is exactly an `emitStep` (kernel UNCHANGED ⇒ `queues` frame).
      simp only [execFullA] at h
      by_cases hlive : cell ∈ s.kernel.accounts
      · rw [if_pos hlive] at h; simp only [emitStep, Option.some.injEq] at h; subst h; exact hwf
      · rw [if_neg hlive] at h; exact absurd h (by simp)
  | incrementNonceA actor cell n =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; exact hwf
  | setPermissionsA actor cell p =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; exact hwf
  | setVKA actor cell vk =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; exact hwf
  -- §authority — introduce/validateHandoff → recKDelegate; delegateAtten → recKDelegateAtten;
  -- attenuate always-commit (caps-only); dropRef/revokeDelegation → recCRevoke; exercise factors.
  | introduceA intro rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel intro rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
          unfold recKDelegate at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | delegateAttenA del rec t keep =>
      simp only [execFullA, recCDelegateAtten] at h
      cases hk : recKDelegateAtten s.kernel del rec t keep with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
          unfold recKDelegateAtten at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | attenuateA actor idx keep =>
      simp only [execFullA, attenuateStepA] at h
      obtain ⟨rfl⟩ := h; exact hwf
  | dropRefA holder t =>
      simp only [execFullA, recCRevoke] at h
      obtain ⟨rfl⟩ := h; exact hwf
  | revokeDelegationA holder t =>
      simp only [execFullA, recCRevoke] at h
      obtain ⟨rfl⟩ := h; exact hwf
  | validateHandoffA intro rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel intro rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
          unfold recKDelegate at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | exerciseA actor t inner =>
      simp only [execFullA] at h
      by_cases hf : innerFacetsAdmittedA s actor t inner = true
      · rw [if_pos hf] at h
        cases hg : exerciseStepA s actor t with
        | none => rw [hg] at h; exact absurd h (by simp)
        | some s1 =>
            rw [hg] at h
            obtain ⟨_, hs1⟩ := exerciseStepA_factors hg
            -- the hold-gate frames `queues`; the inner fold preserves `subWF` step-by-step.
            have hwf1 : subWF s1.kernel := subWF_of_queues_eq (k := s.kernel) (by rw [hs1]) hwf
            exact execInnerA_subWF_preserved s1 s' inner h hwf1
      · rw [if_neg hf] at h; exact absurd h (by simp)
  -- §supply-growth — createCell/spawn factor through their gates (createCellIntoAsset / + caps grant —
  -- neither touches `queues`); bridgeMint reuses recCMintAsset.
  | createCellA actor newCell =>
      obtain ⟨_, _, hs'⟩ := createCellChainA_factors (by simpa only [execFullA] using h)
      subst hs'; exact hwf
  | createCellFromFactoryA actor newCell vk =>
      -- §MA-factory: the factory install edits `cell`/`slotCaveats`/`accounts`/`bal`, never `queues`.
      obtain ⟨_, s1, _, _, hc, hs'⟩ :=
        createCellFromFactoryChainA_factors (by simpa only [execFullA] using h)
      obtain ⟨_, _, hs1⟩ := createCellChainA_factors hc
      subst hs' hs1; exact hwf
  | spawnA actor child target =>
      -- §SPAWN: `spawnChainA_factors` now yields a 3-part body (live-held gate ∧ `createCellChainA`-commit
      -- ∧ the held-cap-copy/delegation snapshot post-state). The post-state edits `caps`/`delegate`/
      -- `delegations` only — `queues` rides `s1.kernel.queues` = `createCellChainA`'s `queues` (frame).
      obtain ⟨s1, _, hc, hs'⟩ := spawnChainA_factors (by simpa only [execFullA] using h)
      subst hs'
      obtain ⟨_, _, hc'⟩ := createCellChainA_factors hc; subst hc'; exact hwf
  | bridgeMintA actor cell a value =>
      simp only [execFullA, recCMintAsset] at h
      cases hk : recKMintAsset s.kernel actor cell a value with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
          unfold recKMintAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  -- §escrow/obligation/committed — chained holding-store steps (kernel updates bal/escrows, never queues).
  | createEscrowA id actor creator recipient asset amount =>
      simp only [execFullA, createEscrowChainA] at h
      cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
          unfold createEscrowKAsset createEscrowRawAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | releaseEscrowA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := releaseEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'
      refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
      unfold releaseEscrowKAsset settleEscrowRawAsset at hk
      split at hk
      · split at hk
        · injection hk with hk; subst hk; rfl
        · exact absurd hk (by simp)
      · exact absurd hk (by simp)
  | refundEscrowA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := refundEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'
      refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
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
          commit_subst h hk
          refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
          unfold createEscrowKAsset createEscrowRawAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  -- fulfill/slash route to refund/release (escrow SETTLE) — `queues` literally unchanged (frame).
  | fulfillObligationA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := refundEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'
      refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
      unfold refundEscrowKAsset settleEscrowRawAsset at hk
      split at hk
      · split at hk
        · injection hk with hk; subst hk; rfl
        · exact absurd hk (by simp)
      · exact absurd hk (by simp)
  | slashObligationA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := releaseEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'
      refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
      unfold releaseEscrowKAsset settleEscrowRawAsset at hk
      split at hk
      · split at hk
        · injection hk with hk; subst hk; rfl
        · exact absurd hk (by simp)
      · exact absurd hk (by simp)
  -- §note — spend grows `nullifiers`, create grows `commitments` — `queues` untouched in both.
  | noteSpendA nf actor spendProof =>
      simp only [execFullA, noteSpendChainA] at h
      by_cases hp : spendProof = true
      · rw [if_pos hp] at h
        cases hk : noteSpendNullifier s.kernel nf with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
            unfold noteSpendNullifier at hk; split at hk
            · exact absurd hk (by simp)
            · injection hk with hk; subst hk; rfl
      · rw [if_neg hp] at h; exact absurd h (by simp)
  | noteCreateA cm actor =>
      simp only [execFullA, noteCreateChainA] at h
      option_inj at h; subst h
      exact hwf
  | createCommittedEscrowA id actor creator recipient asset amount hidingProof =>
      simp only [execFullA, createCommittedEscrowChainA, createEscrowChainA] at h; split at h
      · cases hk : createEscrowKAsset s.kernel id actor creator recipient asset amount with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
            unfold createEscrowKAsset createEscrowRawAsset at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
      · exact absurd h (by simp)
  | releaseCommittedEscrowA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := releaseEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'
      refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
      unfold releaseEscrowKAsset settleEscrowRawAsset at hk
      split at hk
      · split at hk
        · injection hk with hk; subst hk; rfl
        · exact absurd hk (by simp)
      · exact absurd hk (by simp)
  | refundCommittedEscrowA id actor =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := refundEscrowChainA_factors id actor (by simpa only [execFullA] using h)
      subst h'
      refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
      unfold refundEscrowKAsset settleEscrowRawAsset at hk
      split at hk
      · split at hk
        · injection hk with hk; subst hk; rfl
        · exact absurd hk (by simp)
      · exact absurd hk (by simp)
  -- §bridge — lock/finalize/cancel over the SHARED escrow holding-store (bal/escrows, never queues).
  | bridgeLockA id actor originator destination asset amount =>
      simp only [execFullA, bridgeLockChainA] at h
      cases hk : bridgeLockKAsset s.kernel id actor originator destination asset amount with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
          unfold bridgeLockKAsset createBridgeRawAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | bridgeFinalizeA id actor asset amount =>
      simp only [execFullA, bridgeFinalizeChainA] at h
      split at h
      · cases hk : bridgeFinalizeKAsset s.kernel id asset amount with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
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
            commit_subst h hk
            refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
            unfold bridgeCancelKAsset settleEscrowRawAsset at hk
            split at hk
            · split at hk
              · injection hk with hk; subst hk; rfl
              · exact absurd hk (by simp)
            · exact absurd hk (by simp)
      · exact absurd h (by simp)
  -- §seal — the DE-SHADOWED seal/unseal/createSealPair edit `caps`/`sealedBoxes`; makeSovereign/refusal/
  -- receiptArchive write the cell record — none touch `queues` (frame: `subWF` preserved).
  | sealA pid actor payload =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := sealChainA_factors h; subst hs'; exact hwf
  | unsealA pid actor recipient =>
      simp only [execFullA] at h
      obtain ⟨_, _, _, hs'⟩ := unsealChainA_factors h; subst hs'; exact hwf
  | createSealPairA pid actor sealerHolder unsealerHolder =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := createSealPairChainA_factors h; subst hs'; exact hwf
  | makeSovereignA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := makeSovereignStep_factors h; subst hs'; exact hwf
  | refusalA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; exact hwf
  | receiptArchiveA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; exact hwf
  -- §lifecycle (Wave-3) — seal/unseal/destroy edit `lifecycle`/`deathCert`; refresh edits `delegations`
  -- — none touch `queues` (frame: `subWF` preserved).
  | cellSealA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := cellSealChainA_factors h; subst hs'; exact hwf
  | cellUnsealA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := cellUnsealChainA_factors h; subst hs'; exact hwf
  | cellDestroyA actor cell ch =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := cellDestroyChainA_factors h; subst hs'; exact hwf
  | refreshDelegationA actor child =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := refreshDelegationChainA_factors h; subst hs'; exact hwf
  -- §QUEUE — THE FOUR MOVERS. Each `if stateAuthB … then match queueK … | some k' => …`; gate-peel the
  -- outer `if`, then the kernel op preserves the capacity bound (allocate empty / enqueue-gate /
  -- dequeue-shrink / resize-gate) via the §B.0/§B.1 lemmas.
  | queueAllocateA id actor cell cap =>
      simp only [execFullA, queueAllocateChainA] at h
      split at h
      · cases hk : queueAllocateK s.kernel id actor cap with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            -- queueAllocateK conses a FRESH queue with an EMPTY buffer (`0 ≤ cap`) onto `queues`.
            unfold queueAllocateK at hk
            split at hk
            · exact absurd hk (by simp)
            · injection hk with hk; subst hk
              show subWF { s.kernel with queues := _ :: s.kernel.queues }
              exact subWF_cons _ (by simp) hwf
      · exact absurd h (by simp)
  | queueEnqueueA id m actor cell depId dAsset deposit =>
      simp only [execFullA, queueEnqueueChainA] at h
      split at h
      · cases hk : queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            exact queueEnqueueDepositK_subWF hk hwf
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
            exact queueDequeueRefundK_subWF hk hwf
      · exact absurd h (by simp)
  | queueResizeA id newCap actor cell =>
      simp only [execFullA, queueResizeChainA] at h
      split at h
      · cases hk : queueResizeK s.kernel id newCap with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            -- queueResizeK gate is `len ≤ newCap`, so the resized record stays within (the NEW) capacity.
            unfold queueResizeK at hk
            cases hf : findQueue s.kernel.queues id with
            | none   => simp only [hf] at hk; exact absurd hk (by simp)
            | some q =>
                simp only [hf] at hk
                by_cases hc : q.buffer.length ≤ newCap
                · rw [if_pos hc] at hk; simp only [Option.some.injEq] at hk; subst hk
                  show ∀ qq ∈ replaceQueue s.kernel.queues id { q with capacity := newCap }, _
                  refine replaceQueue_subWF hwf ?_
                  show q.buffer.length ≤ newCap
                  exact hc
                · rw [if_neg hc] at hk; exact absurd hk (by simp)
      · exact absurd h (by simp)
  -- §MA-queue-batch (WAVE 4): the atomic batch / pipeline step PRESERVE the queue well-formedness
  -- `subWF` (each sub-op enqueue stays within capacity, each dequeue shrinks); pipelinedSend leaves
  -- `queues` UNCHANGED. The non-trivial faithful-mirror content: the batch/fan-out cannot overflow a queue.
  | queueAtomicTxA actor ops =>
      simp only [execFullA] at h
      obtain ⟨s1, hf, _, hk⟩ := queueAtomicTxA_atomic_witness h
      rw [show s'.kernel = s1.kernel from hk]
      exact queueAtomicTxChainA_subWF hf hwf
  | queuePipelineStepA srcId owner sinkCells sinkIds =>
      simp only [execFullA] at h
      obtain ⟨k1, mh, hd, hfo⟩ := queuePipelineStepA_routing_witness h
      exact pipelineFanoutK_subWF hfo (queueDequeueK_subWF hd hwf)
  | pipelinedSendA actor =>
      simp only [execFullA, Option.some.injEq] at h; subst h; exact hwf
  -- §swiss — four CapTP swiss-table effects (kernel updates `swiss`, never `queues`).
  | exportSturdyRefA sw actor exporter target rights =>
      simp only [execFullA, swissExportChainA] at h
      split at h
      · cases hk : swissExportK s.kernel sw exporter target rights with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
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
            commit_subst h hk
            refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
            unfold swissEnlivenK at hk; split at hk
            · exact absurd hk (by simp)
            · split at hk
              · injection hk with hk; subst hk; rfl
              · exact absurd hk (by simp)
      · exact absurd h (by simp)
  | swissHandoffA sw certHash introducer exporter =>
      simp only [execFullA, swissHandoffChainA] at h
      split at h
      · cases hk : swissHandoffK s.kernel sw certHash with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
            unfold swissHandoffK at hk; split at hk
            · exact absurd hk (by simp)
            · injection hk with hk; subst hk; rfl
      · exact absurd h (by simp)
  | swissDropA sw actor exporter =>
      simp only [execFullA, swissDropChainA] at h
      split at h
      · cases hk : swissDropK s.kernel sw with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            refine subWF_of_queues_eq (k := s.kernel) ?_ hwf
            unfold swissDropK at hk; split at hk
            · exact absurd hk (by simp)
            · split at hk
              · exact absurd hk (by simp)
              · split at hk
                · injection hk with hk; subst hk; rfl
                · injection hk with hk; subst hk; rfl
      · exact absurd h (by simp)

/-- **`execInnerA_subWF_preserved`** — the inner-effect fold an `exerciseA` recurses through preserves
queue well-formedness. Mutual with `execFullA_subWF_preserved`; induction on the inner list. -/
theorem execInnerA_subWF_preserved (s s' : RecChainedState) (inner : List FullActionA)
    (h : execInnerA s inner = some s') (hwf : subWF s.kernel) : subWF s'.kernel := by
  cases inner with
  | nil => simp only [execInnerA, Option.some.injEq] at h; subst h; exact hwf
  | cons a rest =>
      simp only [execInnerA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          exact execInnerA_subWF_preserved s1 s' rest h (execFullA_subWF_preserved s s1 a ha hwf)
end

/-! ### §B.3 — the turn- and forest-level lift (induction on the list + the pre-order bridge). -/

/-- **`execFullTurnA_subWF_preserved` (PROVED).** A committed per-asset full TURN preserves `subWF`. By
induction on the action list — each committed `execFullA` step preserves it (`execFullA_subWF_preserved`),
chained; the empty turn is trivial. Mirrors `CellNullifier.execFullTurnA_nullifiers_grow`. -/
theorem execFullTurnA_subWF_preserved :
    ∀ (s s' : RecChainedState) (tt : List FullActionA),
      execFullTurnA s tt = some s' → subWF s.kernel → subWF s'.kernel
  | s, s', [], h, hwf => by
      simp only [execFullTurnA, Option.some.injEq] at h; subst h; exact hwf
  | s, s', a :: rest, h, hwf => by
      simp only [execFullTurnA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          exact execFullTurnA_subWF_preserved s1 s' rest h (execFullA_subWF_preserved s s1 a ha hwf)

/-- **`execFullForestA_subWF_preserved` (PROVED).** A committed full FOREST preserves `subWF`. Read
straight through the pre-order bridge `execFullForestA_eq_execFullTurnA` into the turn-level lemma — the
same route `CellNullifier.execFullForestA_nullifiers_grow` takes. -/
theorem execFullForestA_subWF_preserved (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') (hwf : subWF s.kernel) : subWF s'.kernel := by
  rw [execFullForestA_eq_execFullTurnA] at h
  exact execFullTurnA_subWF_preserved s s' (lowerForestA f) h hwf

/-! ### §B.4 — THE CROWN: `subWF` carried forever by `livingCellA_carries`. -/

/-- **`subscription_wellformed_forever` (PROVED) — THE SUBSCRIPTION CROWN on the REAL machine: NO queue
is ever over capacity, FOREVER.** From any well-formed start (`subWF s.kernel` — every subscription's
in-flight count is within its capacity), along the ENTIRE unbounded adversarial trajectory `trajA s
sched`, under EVERY schedule, the subscription stays well-formed: `subWF (trajA s sched n).kernel` at
EVERY index `n`. This is dregg1's subscription headline (the in-flight bound / "write past capacity →
rejected", the executable face of `head − tail ≤ capacity`) carried by `CellCarry.livingCellA_carries`
with `Good := (subWF ·.kernel)`, whose one-step obligation is discharged from the executor's queue
FRAME (`execFullForestA_subWF_preserved` on a commit — the capacity gate keeps every record within
bounds) and the STAY-PUT self-loop on a reject (`cellNextA` leaves the state, hence `queues`,
UNCHANGED). The §B match of §A's `subscription_consumer_safe_forever` — the SAME no-overflow safety, on
the SHIPPED `execFullForestA`, against any adversary, for all time. -/
theorem subscription_wellformed_forever (s : RecChainedState) (hinit : subWF s.kernel)
    (sched : SchedA) :
    ∀ n, subWF (trajA s sched n).kernel :=
  livingCellA_carries (fun s' => subWF s'.kernel)
    (fun a cf h => by
      -- One-step preservation. `cellNextA a cf = (execFullForestA a cf.1).getD a`: on a COMMIT the
      -- forest FRAME keeps every queue within capacity; on a REJECT the state is the UNCHANGED `a`.
      show subWF (cellNextA a cf).kernel
      unfold cellNextA
      cases hc : execFullForestA a cf.1 with
      | some a' => simp only [Option.getD_some]
                   exact execFullForestA_subWF_preserved a a' cf.1 hc h
      | none    => simp only [Option.getD_none]; exact h)
    s hinit sched

/-! ## It runs (`#eval`) — both registers exercised on a REAL committed publish (non-vacuity).

The §A automaton: a publish on a non-full queue advances `head` and stays well-formed; a consume on a
non-empty queue advances `tail`; the boundary rejections fire. The §B kernel: a real
`queueAllocateA` + `queueEnqueueA` via `execFullForestA` lands a within-capacity queue, and `subWF`
holds on the post-state — the carried invariant bounds a queue that genuinely GREW. -/

/-! ### §A `#eval` — the slot automaton. -/

/-- A subscription with 2 published, 1 consumed, capacity 8 — well-formed (`1 ≤ 2`, in-flight `1 ≤ 8`). -/
def sub0 : SubState := { head := 2, tail := 1, capacity := 8 }

#guard decide sub0.WF                                         -- true  (well-formed start)
#guard (publish sub0).map (fun s => (s.head, s.tail, s.inFlight)) == some (3, 1, 2)  -- some (3, 1, 2)  (head advanced)
#guard (consume sub0).map (fun s => (s.head, s.tail, s.inFlight)) == some (2, 2, 0)  -- some (2, 2, 0)  (tail advanced)
#guard (publish sub0).map (fun s => decide s.WF) == some true  -- some true  (publish preserves WF)
#guard (consume sub0).map (fun s => decide s.WF) == some true  -- some true  (consume preserves WF)
-- the boundary teeth: a FULL queue rejects publish; an EMPTY queue rejects consume.
#guard (publish { head := 8, tail := 0, capacity := 8 }).isSome == false  -- false (full ⇒ rejected — capacity bound)
#guard (consume { head := 5, tail := 5, capacity := 8 }).isSome == false  -- false (empty ⇒ rejected — no read past producer)
-- consumer-safe forever along the alternating schedule (a few indices; the theorem covers ALL n):
#guard decide (subTraj sub0 (fun n => if n % 2 = 0 then SubOp.pub else SubOp.con) 4).WF  -- true

/-! ### §B `#eval` — the REAL living cell. -/

/-- A real subscription program: actor 0 ALLOCATES a queue (id 7, capacity 2, on cell 0), then
PUBLISHES (enqueues message hash 111, no deposit). A 2-node forest on `fma0` (actor 0 owns cell 0 by
ownership — empty caps). The post-state's queue holds `[111]`, within capacity 2. -/
def subForest : FullForestA :=
  ⟨ .queueAllocateA 7 0 0 2
  , [ { holder := 0, keep := [Auth.read], parentCap := .endpoint 0 [Auth.read, Auth.write]
      , sub := ⟨ .queueEnqueueA 7 111 0 0 9 0 0, [] ⟩ } ] ⟩

-- The subscription program COMMITS (allocate + publish run, gated handoff passes — cell 0 holds the cap):
#guard (execFullForestA fmaDeleg subForest).isSome                      -- true (the subscription commits)
-- The post-state's queue 7 holds the published message `[111]` (in-flight count 1, capacity 2):
#guard ((execFullForestA fmaDeleg subForest).bind
        (fun s => (findQueue s.kernel.queues 7).map (fun q => (q.buffer, q.capacity)))) == some ([111], 2)  -- some ([111], 2)
-- subWF HOLDS on the post-state — every queue (here the one we built) is within capacity:
#guard ((execFullForestA fmaDeleg subForest).map
        (fun s => s.kernel.queues.all (fun q => decide (q.buffer.length ≤ q.capacity)))) == some true  -- some true (the carried subWF)
-- the in-flight bound has teeth on the committed queue: 1 ≤ 2 (NOT over capacity):
#guard ((execFullForestA fmaDeleg subForest).bind
        (fun s => (findQueue s.kernel.queues 7).map (fun q => decide (q.buffer.length ≤ q.capacity)))) == some true  -- some true

/-! ## Axiom hygiene — every keystone pinned to the standard kernel triple (NO `sorryAx`). -/

-- §A — the faithful slot automaton.
#assert_axioms publish_preserves_WF
#assert_axioms consume_preserves_WF
#assert_axioms consume_empty_rejected
#assert_axioms publish_full_rejected
#assert_axioms subStep_preserves_WF
#assert_axioms subscription_consumer_safe_forever
-- §B — the REAL living-cell carry.
#assert_axioms replaceQueue_subWF
#assert_axioms execFullA_subWF_preserved
#assert_axioms execFullTurnA_subWF_preserved
#assert_axioms execFullForestA_subWF_preserved
#assert_axioms subscription_wellformed_forever

end Dregg2.Apps.Subscription
