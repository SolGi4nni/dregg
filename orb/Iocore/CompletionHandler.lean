import Iocore.Reactor

/-!
# Iocore.CompletionHandler — the inline completion-handler drain, verified

There are two ways to hand a batch of kernel completions to a consumer. The
**buffered** way materializes every completion into an array first — a
`List (Completion α ρ)` — and only then walks that array applying the consumer.
The **inline** way never builds the array at all: it *folds* the consumer over
the completions as they are drained, one at a time, applying the consumer to
each completion at the moment it is produced and letting the intermediate
storage evaporate. This file models the inline drain and proves it is
observationally the buffered drain — same observations, zero intermediate list.

The inline consumer is richer than a passive observer: during the callback for a
completion it may **re-submit** new I/O — issue a fresh operation straight back
into the pending slab — instead of parking a work item in a queue for a later
pass. This is the "re-submit during drain" discipline: the callback is handed a
submitter and the new op is enqueued into the slab immediately, in FIFO order,
with no lost work item.

## The model

`HState α ρ β` is the inline consumer's running state:

* `slab : Slab α` — the pending-operation slab (the reactor's, from `Reactor`);
* `log : List β` — the **observations**, newest first: what the consumer
  recorded for each completion it processed. This is the fold accumulator; there
  is deliberately **no** `List (Completion α ρ)` field — nothing is buffered;
* `submits : List α` — the operations re-submitted during callbacks, oldest
  first (FIFO): the work re-issued into the slab mid-drain.

A completion event is a `(Key × ρ)`: the correlator the kernel echoes and the
result it carries. The consumer is two pure callbacks:

* `obs : α → ρ → β` — what to record for a completed operation;
* `resub : α → ρ → Option α` — the op (if any) to re-submit during the callback.

`HState.step` processes **one** completion inline: look the correlator up in the
slab (a stale correlator does nothing — `Slab.remove` rejects it), record
`obs op res` directly into `log`, and if `resub` asks for a new op, insert it
into the slab and append it to `submits`. `HState.drain` is exactly
`evs.foldl HState.step` — a fold, never a collect.

## What is proven (0 sorries)

* `handler_inline_no_buffer` — the inline drain's observation log equals the
  buffered drain's: first materialize every completion into a list
  (`bufCollect`), then consume it. Same observations — but `HState` has no
  completion-list field, so the inline path materializes nothing. Buffer
  eliminated, result unchanged. (`drain_is_fold` states literally that the drain
  is a `List.foldl`, not a collect.)
* `handler_resubmit_ordered` — a submit issued during a completion callback is
  enqueued and processed: `submits` after the drain is exactly the prior submits
  followed by the re-submitted ops **in the order their callbacks fired**
  (`pendingSubmits`). None dropped, none reordered. The single-step
  `step_resubmit_live` shows the re-submitted op is retrievable from the slab
  the instant it is enqueued — no lost work item.
* `handler_refines_reactor` — the inline drain observably equals the ground-truth
  reactor's complete-then-consume: for an observer consumer, the inline log is
  exactly the map of `obs` over the completions the reactor's `RState.complete`
  emits into `done`. The fast inline path delivers the same observation sequence
  as registering each completion in the reactor and consuming its `done` log.

## Model-refines-Rust

This is the SPEC; the running Rust `poll_dispatch` is its realization. The
buffered path writes `CompletionEvent`s into a raw `events_out` array (the
`List (Completion α ρ)` here); the inline path drains the completion queue
straight through the handler trait, each callback holding a submitter it uses to
re-issue I/O — the executable form of `HState.step`'s `Slab.remove` /
`Slab.insert` / `log` fold, exactly as the buffer ring realizes
`Uring.RecycleOnce`. The inline drain realizes the running `uring.rs` / `kqueue.rs`
consumer; the Rust remains the running form, this model the spec it refines.
-/

namespace Iocore

variable {α ρ β : Type}

/-- The inline consumer's running state. `log` is the fold accumulator of
observations (newest first); `submits` is the FIFO of ops re-issued mid-drain.
There is deliberately no completion-list field — nothing is buffered. -/
structure HState (α ρ β : Type) where
  /-- The pending-operation slab (the reactor's). -/
  slab : Slab α
  /-- Observations recorded inline, newest first — the fold accumulator. -/
  log : List β
  /-- Ops re-submitted during callbacks, oldest first (FIFO). -/
  submits : List α

/-- Process **one** completion inline. A live correlator: record `obs op res`
straight into `log`, and if `resub` returns a new op, insert it into the slab and
append it to `submits` — the re-submit-during-callback. A stale correlator
(`Slab.remove` rejects it) is a no-op: no observation, no work. -/
def HState.step (obs : α → ρ → β) (resub : α → ρ → Option α)
    (h : HState α ρ β) (ev : Key × ρ) : HState α ρ β :=
  match h.slab.remove ev.1 with
  | some (op, sl) =>
      match resub op ev.2 with
      | some n =>
          { slab := (sl.insert n).2
            log := obs op ev.2 :: h.log
            submits := h.submits ++ [n] }
      | none =>
          { slab := sl
            log := obs op ev.2 :: h.log
            submits := h.submits }
  | none => h

/-- The inline drain: **fold** the consumer over the completion batch. This is
`List.foldl` of `HState.step` — one pass, no intermediate list. -/
def HState.drain (obs : α → ρ → β) (resub : α → ρ → Option α)
    (h : HState α ρ β) (evs : List (Key × ρ)) : HState α ρ β :=
  evs.foldl (HState.step obs resub) h

/-- **The drain is a fold, not a collect** — definitionally `List.foldl`. -/
theorem drain_is_fold (obs : α → ρ → β) (resub : α → ρ → Option α)
    (h : HState α ρ β) (evs : List (Key × ρ)) :
    HState.drain obs resub h evs = evs.foldl (HState.step obs resub) h := rfl

/-! ## No buffer: the fold equals collect-then-consume -/

/-- The **buffered** baseline: materialize every completion `(op, result)` into a
list (the eliminated `events_out` array / `Vec<Completion>`), threading the slab
exactly as the inline drain does (removes, and re-submit inserts). Oldest first. -/
def bufCollect (resub : α → ρ → Option α) (sl : Slab α) :
    List (Key × ρ) → List (α × ρ)
  | [] => []
  | ev :: rest =>
      match sl.remove ev.1 with
      | some (op, s2) =>
          let s3 := match resub op ev.2 with
            | some n => (s2.insert n).2
            | none => s2
          (op, ev.2) :: bufCollect resub s3 rest
      | none => bufCollect resub sl rest

/-- Consume a materialized completion list: fold `obs` over it, prepending
newest-last so the accumulator matches an inline left fold. -/
def consumeBuf (obs : α → ρ → β) (l0 : List β) (cs : List (α × ρ)) : List β :=
  cs.foldl (fun l p => obs p.1 p.2 :: l) l0

/-- **Inline ≡ buffered (no intermediate list).** The inline drain's observation
log is exactly what you get by first materializing every completion into a list
(`bufCollect`) and then consuming it (`consumeBuf`). The results are identical —
yet `HState` has no completion-list field, so the inline path never builds
`bufCollect`. The buffer is eliminated at no observable cost: a fold, not a
collect. -/
theorem handler_inline_no_buffer (obs : α → ρ → β) (resub : α → ρ → Option α)
    (h : HState α ρ β) (evs : List (Key × ρ)) :
    (HState.drain obs resub h evs).log
      = consumeBuf obs h.log (bufCollect resub h.slab evs) := by
  induction evs generalizing h with
  | nil => rfl
  | cons ev rest ih =>
      show (HState.drain obs resub (h.step obs resub ev) rest).log
        = consumeBuf obs h.log (bufCollect resub h.slab (ev :: rest))
      cases hrm : h.slab.remove ev.1 with
      | none =>
          have hs : h.step obs resub ev = h := by simp [HState.step, hrm]
          have hb : bufCollect resub h.slab (ev :: rest) = bufCollect resub h.slab rest := by
            simp [bufCollect, hrm]
          rw [hs, hb]; exact ih h
      | some p =>
          obtain ⟨op, sl⟩ := p
          cases hres : resub op ev.2 with
          | none =>
              have hs : h.step obs resub ev
                  = { slab := sl, log := obs op ev.2 :: h.log, submits := h.submits } := by
                simp [HState.step, hrm, hres]
              have hb : bufCollect resub h.slab (ev :: rest)
                  = (op, ev.2) :: bufCollect resub sl rest := by simp [bufCollect, hrm, hres]
              rw [hs, hb]; exact ih _
          | some n =>
              have hs : h.step obs resub ev
                  = { slab := (sl.insert n).2, log := obs op ev.2 :: h.log,
                      submits := h.submits ++ [n] } := by simp [HState.step, hrm, hres]
              have hb : bufCollect resub h.slab (ev :: rest)
                  = (op, ev.2) :: bufCollect resub (sl.insert n).2 rest := by
                simp [bufCollect, hrm, hres]
              rw [hs, hb]; exact ih _

/-! ## Re-submit during drain: enqueued, ordered, no lost work -/

/-- The re-submitted ops a drain produces, **in the order their callbacks fire**
(oldest first). Mirrors `HState.step`'s submit delta: one op per live completion
whose callback re-submits, none otherwise. -/
def pendingSubmits (obs : α → ρ → β) (resub : α → ρ → Option α)
    (h : HState α ρ β) : List (Key × ρ) → List α
  | [] => []
  | ev :: rest =>
      let d := match h.slab.remove ev.1 with
        | some (op, _) => (match resub op ev.2 with | some n => [n] | none => [])
        | none => []
      d ++ pendingSubmits obs resub (h.step obs resub ev) rest

/-- Single-step: `step` appends its re-submit delta to `submits` and nothing
else — the FIFO grows only at the end. -/
theorem step_submits (obs : α → ρ → β) (resub : α → ρ → Option α)
    (h : HState α ρ β) (ev : Key × ρ) :
    (h.step obs resub ev).submits
      = h.submits ++
        (match h.slab.remove ev.1 with
          | some (op, _) => (match resub op ev.2 with | some n => [n] | none => [])
          | none => []) := by
  unfold HState.step
  cases hrm : h.slab.remove ev.1 with
  | none => simp [hrm]
  | some p =>
      obtain ⟨op, sl⟩ := p
      cases hres : resub op ev.2 with
      | none => simp [hrm, hres]
      | some n => simp [hrm, hres]

/-- **Re-submit during a callback is enqueued and retrievable — no lost work.**
On a live completion whose callback re-submits `n`, the resulting slab holds `n`
live under a fresh correlator (`n` is retrievable the instant it is enqueued),
and `n` is appended to `submits`. -/
theorem step_resubmit_live (obs : α → ρ → β) (resub : α → ρ → Option α)
    (h : HState α ρ β) (ev : Key × ρ) (op : α) (sl : Slab α) (n : α)
    (hrm : h.slab.remove ev.1 = some (op, sl)) (hres : resub op ev.2 = some n) :
    (h.step obs resub ev).slab.get (sl.insert n).1 = some n
      ∧ (h.step obs resub ev).submits = h.submits ++ [n] := by
  have hs : h.step obs resub ev
      = { slab := (sl.insert n).2, log := obs op ev.2 :: h.log,
          submits := h.submits ++ [n] } := by simp [HState.step, hrm, hres]
  rw [hs]
  exact ⟨slab_insert_get sl n, rfl⟩

/-- **Re-submits are enqueued in order, none lost (the headline).** After the
inline drain, `submits` is exactly the prior submits followed by every
re-submitted op **in the order its callback fired** (`pendingSubmits`). Nothing
is dropped and nothing is reordered: a submit issued mid-drain lands, in FIFO
position, in the work queue. -/
theorem handler_resubmit_ordered (obs : α → ρ → β) (resub : α → ρ → Option α)
    (h : HState α ρ β) (evs : List (Key × ρ)) :
    (HState.drain obs resub h evs).submits
      = h.submits ++ pendingSubmits obs resub h evs := by
  induction evs generalizing h with
  | nil => simp [HState.drain, pendingSubmits]
  | cons ev rest ih =>
      show (HState.drain obs resub (h.step obs resub ev) rest).submits = _
      rw [ih (h.step obs resub ev)]
      rw [step_submits obs resub h ev]
      show h.submits ++ _ ++ pendingSubmits obs resub (h.step obs resub ev) rest = _
      rw [List.append_assoc]
      rfl

/-! ## Refinement: inline drain ≡ reactor complete-then-consume -/

/-- The ground-truth reactor's complete-then-collect: fold `RState.complete`
(from `Iocore.Reactor`) over the batch, building the `done` log (newest first). -/
def reactorCollect (st : RState α ρ) (evs : List (Key × ρ)) : RState α ρ :=
  evs.foldl (fun st ev => st.complete ev.1 ev.2) st

/-- **The inline drain observably refines the reactor.** For an *observer*
consumer (one that records but never re-submits), the inline observation log is
exactly `obs` mapped over the completions the ground-truth reactor emits into
`done`. The inline fast path delivers the identical observation sequence as
registering each completion in the reactor (`RState.complete`) and consuming its
`done` log — same slab evolution, same completions, same order. -/
theorem handler_refines_reactor (obs : α → ρ → β) (st : RState α ρ)
    (evs : List (Key × ρ)) :
    (HState.drain obs (fun _ _ => none)
        { slab := st.slab, log := st.done.map (fun c => obs c.op c.result), submits := [] }
        evs).log
      = (reactorCollect st evs).done.map (fun c => obs c.op c.result) := by
  induction evs generalizing st with
  | nil => rfl
  | cons ev rest ih =>
      show (HState.drain obs (fun _ _ => none)
        (HState.step obs (fun _ _ => none)
          { slab := st.slab, log := st.done.map (fun c => obs c.op c.result), submits := [] } ev)
        rest).log = (reactorCollect (st.complete ev.1 ev.2) rest).done.map (fun c => obs c.op c.result)
      cases hrm : st.slab.remove ev.1 with
      | none =>
          have hs : HState.step obs (fun _ _ => none)
              { slab := st.slab, log := st.done.map (fun c => obs c.op c.result), submits := [] } ev
              = { slab := st.slab, log := st.done.map (fun c => obs c.op c.result),
                  submits := [] } := by simp [HState.step, hrm]
          have hc : st.complete ev.1 ev.2 = st := by simp [RState.complete, hrm]
          rw [hs, hc]; exact ih st
      | some p =>
          obtain ⟨op, sl⟩ := p
          have hs : HState.step obs (fun _ _ => none)
              { slab := st.slab, log := st.done.map (fun c => obs c.op c.result), submits := [] } ev
              = { slab := sl, log := obs op ev.2 :: st.done.map (fun c => obs c.op c.result),
                  submits := [] } := by simp [HState.step, hrm]
          have hc : st.complete ev.1 ev.2
              = { slab := sl, done := ⟨ev.1, op, ev.2⟩ :: st.done } := by
            simp [RState.complete, hrm]
          rw [hs, hc]
          have := ih { slab := sl, done := ⟨ev.1, op, ev.2⟩ :: st.done }
          simpa using this

/-! ## Non-vacuity: concrete inline drains

Truth-table checks on concrete completion batches over a real `Slab Nat`. The
observer records the result value; the re-submitter re-issues a fixed op. -/

/-- A slab with two live ops, and their correlators. -/
private def s2 : Key × Key × Slab Nat :=
  let s0 := Slab.empty Nat 8
  let (k1, s1) := s0.insert 100
  let (k2, s2) := s1.insert 200
  (k1, k2, s2)

/-- Observer consumer: record the result. Re-submitter: none. -/
private def obsRes : Nat → Nat → Nat := fun _ r => r
private def noResub : Nat → Nat → Option Nat := fun _ _ => none

/-- Start state over `s2`'s slab, empty log and submits. -/
private def h0 : HState Nat Nat Nat :=
  { slab := s2.2.2, log := [], submits := [] }

-- Draining two live completions records both results, inline, newest first.
private def drainTwo : List Nat :=
  (HState.drain obsRes noResub h0 [(s2.1, 7), (s2.2.1, 9)]).log
#guard drainTwo == [9, 7]

-- No completion-buffer field exists; the inline log equals the buffered consume.
#guard drainTwo
  == consumeBuf obsRes h0.log (bufCollect noResub h0.slab [(s2.1, 7), (s2.2.1, 9)])

-- A stale correlator (already drained) is a no-op: it records nothing.
private def drainStale : List Nat :=
  let h1 := HState.drain obsRes noResub h0 [(s2.1, 7)]   -- s2.1 drained here
  (HState.drain obsRes noResub h1 [(s2.1, 99)]).log       -- re-delivery: no-op
#guard drainStale == [7]

-- A re-submitting callback: completing k1 re-issues op 555. It is enqueued
-- (appears in `submits`) and retrievable from the slab.
private def resub555 : Nat → Nat → Option Nat := fun _ _ => some 555
private def drainResub : List Nat × Bool :=
  let h1 := HState.drain obsRes resub555 h0 [(s2.1, 7)]
  -- the re-submitted op 555 is live under a fresh correlator, so it can complete
  let liveAgain := h1.slab.slots.any (fun sl => sl.payload == some 555)
  (h1.submits, liveAgain)
#guard drainResub.1 == [555]      -- enqueued, FIFO
#guard drainResub.2 == true       -- retrievable in the slab (no lost work)

-- Ordered re-submits: two completions each re-submit; FIFO order preserved.
private def resubOf : Nat → Nat → Option Nat := fun op _ => some (op + 1)
private def drainResubOrdered : List Nat :=
  (HState.drain obsRes resubOf h0 [(s2.1, 7), (s2.2.1, 9)]).submits
#guard drainResubOrdered == [101, 201]   -- op 100→101 then op 200→201, in order

-- The ordered-submits closed form matches `pendingSubmits`.
#guard drainResubOrdered == pendingSubmits obsRes resubOf h0 [(s2.1, 7), (s2.2.1, 9)]

-- Mutant: a consumer that *drops* the second completion's observation would
-- give [7] instead of [9,7]; the real inline fold keeps both. Non-vacuous.
#guard drainTwo != [7]

end Iocore
