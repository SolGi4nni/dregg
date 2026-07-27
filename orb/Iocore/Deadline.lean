import Iocore.Reactor

/-!
# Iocore.Deadline — the unified deadline min-heap with lazy deletion, verified

A completion reactor must wake *exactly* when the nearest of many pending
deadlines expires: connection idle timeouts, request body deadlines, handshake
and keepalive windows all funnel into a single queue that arms **one** kernel
timer for the earliest deadline and re-arms as deadlines come and go. The
running engines realize this with a `BinaryHeap` keyed by deadline plus a hash
map of the live keys; every safety property there lives in a property test.
Here it is a **theorem**.

## The model

A `DQ K` (deadline queue over correlator/connection keys `K`) holds three parts:

* `heap` — the min-heap, modeled by its *ordered projection*: the exact sequence
  a real binary min-heap yields on repeated pop, i.e. entries in nondecreasing
  deadline order. `Sorted` names that invariant, and `insert` preserves it
  (`insert_sorted`), so every reachable state satisfies it.
* `live` — the authoritative map from key to its **current** deadline. A heap
  entry `⟨d, k⟩` is *live* iff `live` still maps `k` to that exact `d`
  (`Live`); otherwise it is a **tombstone** (the key was removed, or its
  deadline was updated and this entry is the stale copy).
* `armed` — the single deadline the kernel timer is currently set for (`Option`:
  at most one armed timer, ever).

**Lazy deletion** is the point: `remove k` drops `k` from `live` and *leaves the
heap untouched* — no O(n) heap surgery. The stale entry is skipped when it
surfaces on pop. `insert`/`update` push a new entry and re-point `live`; the
superseded entry becomes a tombstone the same way.

## What is proven (0 sorries)

* `heap_min_correct` — **peek returns the earliest deadline**: the first live
  entry in the ordered heap has a deadline ≤ every live entry's, and is itself
  live. The queue's notion of "nearest" is the true minimum over live deadlines.
* `heap_lazy_delete` — **a cancelled timer is skipped on pop, not eagerly
  removed**: after `remove k` the heap is byte-for-byte unchanged, yet `k` is
  never emitted by a drain — its entry is passed over as a tombstone.
* `heap_arm_one` — **only the nearest deadline arms the kernel timer**: the
  deadline `arm` selects is a live deadline and is ≤ every live deadline; a queue
  carries at most one armed timer.
* `heap_pop_ordered` — **deadlines fire in order**: the sequence a drain emits is
  itself sorted by deadline (nondecreasing) — no timer fires before an earlier
  one.

## Composition with the reactor

The keys are the reactor's correlators (`Iocore.Key`) or connection handles: the
armed deadline is the timeout the reactor's `wake`/`complete` loop blocks on, and
a fired key drives a `complete` (idle-close, body-timeout) on the slab. The
lazy-tombstone discipline mirrors the slab's generation tags — a superseded
deadline is skipped exactly as a recycled correlator is rejected in
`Iocore.Slab`. This is the SPEC the running heap-plus-map queue refines.
-/

namespace Iocore

/-- A heap entry: a deadline (in kernel ticks) paired with the key it belongs to.
The kernel-facing `BinaryHeap<Reverse<HeapEntry>>` orders these by `deadline`. -/
structure Entry (K : Type) where
  /-- Absolute deadline in monotonic ticks. -/
  deadline : Nat
  /-- The correlator / connection key this deadline governs. -/
  key : K
deriving Repr, DecidableEq

/-- The deadline queue: the ordered heap projection, the authoritative live map,
and the single armed deadline. -/
structure DQ (K : Type) where
  /-- The min-heap as its ordered pop-sequence (nondecreasing deadline). -/
  heap : List (Entry K)
  /-- Authoritative key → current deadline map (association list). -/
  live : List (K × Nat)
  /-- The one deadline the kernel timer is armed for, if any. -/
  armed : Option Nat

/-! ## The live map (association list) -/

variable {K : Type} [DecidableEq K]

/-- Look up a key's current deadline in the live map (first match wins). -/
def lookupD (l : List (K × Nat)) (k : K) : Option Nat :=
  match l with
  | [] => none
  | (k', d) :: t => if k' = k then some d else lookupD t k

/-- Drop every binding for `k` from the live map. -/
def removeKey (k : K) : List (K × Nat) → List (K × Nat)
  | [] => []
  | (k', d) :: t => if k' = k then removeKey k t else (k', d) :: removeKey k t

/-- Set `k`'s deadline to `d` (drop any prior binding, then prepend). -/
def upsert (l : List (K × Nat)) (k : K) (d : Nat) : List (K × Nat) :=
  (k, d) :: removeKey k l

/-- **A heap entry is live** iff the live map still points its key at exactly its
deadline. Any other case (key removed, or deadline updated so this is a stale
copy) is a tombstone. -/
def Live (live : List (K × Nat)) (e : Entry K) : Prop :=
  lookupD live e.key = some e.deadline

/-- Decidable form of `Live`, used as the `find?`/drain predicate. -/
def isLive (live : List (K × Nat)) (e : Entry K) : Bool :=
  decide (lookupD live e.key = some e.deadline)

theorem isLive_iff (live : List (K × Nat)) (e : Entry K) :
    isLive live e = true ↔ Live live e := by
  simp [isLive, Live]

/-! ### Live-map lemmas -/

/-- After `removeKey k`, the key `k` is absent. -/
theorem lookupD_removeKey_self (l : List (K × Nat)) (k : K) :
    lookupD (removeKey k l) k = none := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k', d⟩ := p
    unfold removeKey
    by_cases h : k' = k
    · simp [h, ih]
    · simp only [h, if_false]
      unfold lookupD
      simp [h, ih]

/-- Removing *some other* key preserves an already-absent key. -/
theorem lookupD_removeKey_none {l : List (K × Nat)} {k k' : K}
    (h : lookupD l k = none) : lookupD (removeKey k' l) k = none := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a, d⟩ := p
    unfold lookupD at h
    by_cases ha : a = k
    · rw [if_pos ha] at h; exact absurd h (by simp)
    · rw [if_neg ha] at h
      unfold removeKey
      by_cases ha' : a = k'
      · rw [if_pos ha']; exact ih h
      · rw [if_neg ha']; unfold lookupD; rw [if_neg ha]; exact ih h

/-- `upsert` reads back the value just written. -/
theorem lookupD_upsert_self (l : List (K × Nat)) (k : K) (d : Nat) :
    lookupD (upsert l k d) k = some d := by
  unfold upsert lookupD; simp

/-! ## The pop sequence: drain expired, skipping tombstones -/

/-- **The pop sequence.** Walk the ordered heap front-to-back: stop at the first
entry whose deadline is still in the future (`now < deadline`); otherwise, if the
entry is live, emit it and remove its key from the live map (so a later duplicate
entry for the same key becomes a tombstone); if it is a tombstone, drop it and
continue. This is the exact key sequence `drain_expired` returns. -/
def fired : List (Entry K) → List (K × Nat) → Nat → List (Entry K)
  | [], _, _ => []
  | e :: rest, live, now =>
    if now < e.deadline then []
    else if isLive live e then e :: fired rest (removeKey e.key live) now
    else fired rest live now

/-- The full stateful drain: the fired entries, the surviving heap (future +
un-popped), and the compacted live map. `drainExpired.1 = fired` (`fired_eq`). -/
def drainExpired : List (Entry K) → List (K × Nat) → Nat → List (Entry K) × List (Entry K) × List (K × Nat)
  | [], live, _ => ([], [], live)
  | e :: rest, live, now =>
    if now < e.deadline then ([], e :: rest, live)
    else if isLive live e then
      let r := drainExpired rest (removeKey e.key live) now
      (e :: r.1, r.2.1, r.2.2)
    else drainExpired rest live now

/-- The stateful drain's fired projection is exactly `fired`. -/
theorem fired_eq (heap : List (Entry K)) (live : List (K × Nat)) (now : Nat) :
    (drainExpired heap live now).1 = fired heap live now := by
  induction heap generalizing live with
  | nil => rfl
  | cons e rest ih =>
    unfold drainExpired fired
    by_cases h1 : now < e.deadline
    · simp [h1]
    · by_cases h2 : isLive live e
      · simp [h1, h2, ih]
      · simp [h1, h2, ih]

/-! ## Peek / nearest / arm -/

/-- The first live entry in the ordered heap — a real min-heap's `peek` after it
skips tombstones off the top. -/
def firstLive (dq : DQ K) : Option (Entry K) :=
  dq.heap.find? (fun e => isLive dq.live e)

/-- The nearest live deadline: the deadline of the first live entry. -/
def nearest (dq : DQ K) : Option Nat :=
  (firstLive dq).map (·.deadline)

/-- **Arm** the kernel timer for the nearest live deadline (and only that one). -/
def arm (dq : DQ K) : DQ K :=
  { dq with armed := nearest dq }

/-! ## Insert / update / remove -/

/-- Insert `e` into the ordered heap, keeping nondecreasing deadline order. -/
def insertSorted (e : Entry K) : List (Entry K) → List (Entry K)
  | [] => [e]
  | h :: t => if e.deadline ≤ h.deadline then e :: h :: t else h :: insertSorted e t

/-- **Insert / update** a deadline: push a heap entry and re-point the live map,
then re-arm. `update` (sliding an idle window) is the same operation — the prior
entry for `k`, if any, is left in the heap as a tombstone. -/
def insert (dq : DQ K) (k : K) (d : Nat) : DQ K :=
  arm { dq with heap := insertSorted ⟨d, k⟩ dq.heap, live := upsert dq.live k d }

/-- **Remove** (lazy deletion): drop `k` from the live map only. The heap entry
stays, to be skipped when it surfaces on pop. -/
def remove (dq : DQ K) (k : K) : DQ K :=
  { dq with live := removeKey k dq.live }

/-! ## The sorted invariant -/

/-- The heap is ordered by nondecreasing deadline — a real min-heap's pop order. -/
def Sorted (h : List (Entry K)) : Prop :=
  h.Pairwise (fun a b => a.deadline ≤ b.deadline)

/-- Membership in `insertSorted` is membership in the list plus the new entry. -/
theorem mem_insertSorted {x e : Entry K} {l : List (Entry K)} :
    x ∈ insertSorted e l ↔ x = e ∨ x ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons h t ih =>
    unfold insertSorted
    by_cases hc : e.deadline ≤ h.deadline
    · rw [if_pos hc]; exact List.mem_cons
    · rw [if_neg hc]
      simp only [List.mem_cons, ih]
      exact or_left_comm

/-- **`insert` preserves the sorted invariant** — every reachable state is
sorted, so the peek/arm/pop theorems apply to real queues, not only ideal ones. -/
theorem insertSorted_sorted (e : Entry K) (l : List (Entry K)) (h : Sorted l) :
    Sorted (insertSorted e l) := by
  induction l with
  | nil => exact List.pairwise_singleton _ e
  | cons a t ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
    unfold insertSorted
    by_cases hc : e.deadline ≤ a.deadline
    · rw [if_pos hc]
      refine List.pairwise_cons.mpr ⟨?_, h⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hc
      · exact Nat.le_trans hc (ha x hx)
    · rw [if_neg hc]
      have hae : a.deadline ≤ e.deadline := Nat.le_of_not_le hc
      refine List.pairwise_cons.mpr ⟨?_, ih ht⟩
      intro x hx
      rcases mem_insertSorted.mp hx with rfl | hx
      · exact hae
      · exact ha x hx

/-- Empty heaps are sorted. -/
theorem sorted_nil : Sorted ([] : List (Entry K)) := List.Pairwise.nil

/-! ## Headline theorem 1 — peek returns the earliest deadline -/

/-- The core minimum lemma: in a sorted heap, the first live entry found has the
smallest deadline among all live entries. -/
theorem find_is_min (heap : List (Entry K)) (live : List (K × Nat)) (e : Entry K)
    (hs : Sorted heap) (hf : heap.find? (fun x => isLive live x) = some e) :
    ∀ e' ∈ heap, Live live e' → e.deadline ≤ e'.deadline := by
  induction heap with
  | nil => simp at hf
  | cons h t ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    cases hb : isLive live h with
    | true =>
      rw [List.find?_cons_of_pos hb] at hf
      injection hf with he
      intro e' he' _
      rw [← he]
      rcases List.mem_cons.mp he' with rfl | he'
      · exact Nat.le_refl _
      · exact hhead e' he'
    | false =>
      rw [List.find?_cons_of_neg (by rw [hb]; simp)] at hf
      intro e' he' hlive'
      rcases List.mem_cons.mp he' with rfl | he'
      · have h1 := (isLive_iff live e').mpr hlive'
        rw [hb] at h1; exact absurd h1 (by simp)
      · exact ih htail hf e' he' hlive'

/-- **`heap_min_correct` — peek returns the earliest deadline.** In a sorted
queue, the first live entry (`firstLive`, a real min-heap's post-tombstone-skip
peek) is itself live *and* has a deadline ≤ every live entry's. The queue's
"nearest" is the true minimum over live deadlines — no earlier deadline is ever
missed. -/
theorem heap_min_correct (dq : DQ K) (hs : Sorted dq.heap) (e : Entry K)
    (hf : firstLive dq = some e) :
    Live dq.live e ∧ ∀ e' ∈ dq.heap, Live dq.live e' → e.deadline ≤ e'.deadline := by
  refine ⟨?_, find_is_min dq.heap dq.live e hs hf⟩
  have := List.find?_some hf
  exact (isLive_iff dq.live e).mp this

/-! ## Headline theorem 2 — lazy deletion: a cancelled key is skipped on pop -/

/-- A key absent from the live map is never emitted by a drain: its entries are
all tombstones and are passed over. -/
theorem fired_absent (heap : List (Entry K)) (live : List (K × Nat)) (now : Nat)
    (k : K) (h : lookupD live k = none) :
    k ∉ (fired heap live now).map (·.key) := by
  induction heap generalizing live with
  | nil => simp [fired]
  | cons e rest ih =>
    unfold fired
    by_cases h1 : now < e.deadline
    · simp [h1]
    · rw [if_neg h1]
      by_cases h2 : isLive live e
      · rw [if_pos h2]
        have hek : e.key ≠ k := by
          intro heq
          have : lookupD live e.key = some e.deadline := (isLive_iff live e).mp h2
          rw [heq, h] at this; exact absurd this (by simp)
        simp only [List.map_cons, List.mem_cons, not_or]
        refine ⟨fun hc => hek hc.symm, ?_⟩
        exact ih (removeKey e.key live) (lookupD_removeKey_none h)
      · rw [if_neg h2]; exact ih live h

/-- **`heap_lazy_delete` — a cancelled timer is skipped on pop, not eagerly
removed.** After `remove dq k`, (1) the heap is *byte-for-byte unchanged* (lazy
deletion touches only the live map, no O(n) heap surgery), and (2) `k` is never
emitted by a drain at any `now` — its stale entry is passed over as a tombstone.
The two together are the exact meaning of lazy deletion. -/
theorem heap_lazy_delete (dq : DQ K) (k : K) (now : Nat) :
    (remove dq k).heap = dq.heap ∧
      k ∉ (fired (remove dq k).heap (remove dq k).live now).map (·.key) := by
  refine ⟨rfl, ?_⟩
  apply fired_absent
  exact lookupD_removeKey_self dq.live k

/-! ## Headline theorem 3 — only the nearest deadline arms the kernel timer -/

/-- **`heap_arm_one` — only the nearest deadline arms the kernel timer.** The
deadline `arm` installs (when it installs one) is a *live* deadline realized by
an actual heap entry, and it is ≤ every live entry's deadline. Combined with the
`armed : Option Nat` field (at most one armed timer at a time), the queue arms
exactly one timer, for exactly the earliest deadline. -/
theorem heap_arm_one (dq : DQ K) (hs : Sorted dq.heap) (d : Nat)
    (h : (arm dq).armed = some d) :
    (∃ e ∈ dq.heap, Live dq.live e ∧ e.deadline = d) ∧
      (∀ e' ∈ dq.heap, Live dq.live e' → d ≤ e'.deadline) := by
  have hn : nearest dq = some d := h
  unfold nearest at hn
  rw [Option.map_eq_some_iff] at hn
  obtain ⟨e, hfe, hde⟩ := hn
  obtain ⟨hlive, hmin⟩ := heap_min_correct dq hs e hfe
  refine ⟨⟨e, List.mem_of_find?_eq_some hfe, hlive, hde⟩, ?_⟩
  intro e' he' hlive'
  rw [← hde]; exact hmin e' he' hlive'

/-- At most one timer is armed at a time: the armed deadline is an `Option`, so a
queue can carry no more than a single kernel timeout — the single-arm discipline
is structural, not merely a proven side condition. -/
theorem armed_at_most_one (dq : DQ K) (d₁ d₂ : Nat)
    (h₁ : dq.armed = some d₁) (h₂ : dq.armed = some d₂) : d₁ = d₂ := by
  rw [h₁] at h₂; exact (Option.some.injEq _ _).mp h₂

/-! ## Headline theorem 4 — deadlines fire in order -/

/-- Every fired entry comes from the heap (the drain never invents an entry). -/
theorem fired_subset (heap : List (Entry K)) (live : List (K × Nat)) (now : Nat)
    (x : Entry K) (hx : x ∈ fired heap live now) : x ∈ heap := by
  induction heap generalizing live with
  | nil => simp [fired] at hx
  | cons e rest ih =>
    unfold fired at hx
    by_cases h1 : now < e.deadline
    · rw [if_pos h1] at hx; simp at hx
    · rw [if_neg h1] at hx
      by_cases h2 : isLive live e
      · rw [if_pos h2] at hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih (removeKey e.key live) hx)
      · rw [if_neg h2] at hx
        exact List.mem_cons_of_mem _ (ih live hx)

/-- **`heap_pop_ordered` — deadlines fire in order.** The sequence a drain emits
is itself sorted by nondecreasing deadline: no timer fires before one with an
earlier deadline. (Sortedness of the heap is preserved by `insert`, so this holds
for every reachable queue.) -/
theorem heap_pop_ordered (heap : List (Entry K)) (live : List (K × Nat)) (now : Nat)
    (hs : Sorted heap) : Sorted (fired heap live now) := by
  induction heap generalizing live with
  | nil => exact sorted_nil
  | cons e rest ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    unfold fired
    by_cases h1 : now < e.deadline
    · rw [if_pos h1]; exact sorted_nil
    · rw [if_neg h1]
      by_cases h2 : isLive live e
      · rw [if_pos h2]
        refine List.pairwise_cons.mpr ⟨?_, ih (removeKey e.key live) htail⟩
        intro x hx
        exact hhead x (fired_subset rest (removeKey e.key live) now x hx)
      · rw [if_neg h2]; exact ih live htail

/-! ## Non-vacuity: a concrete queue, evaluated

Real numbers, not schematic hypotheses. Three connection keys with staggered
deadlines; the queue is manifestly sorted; peek picks the minimum, a drain fires
in order, and a removed key is skipped. -/

/-- Sample: keys `10, 20, 30` with deadlines `3, 5, 8` (already sorted). -/
private def sampleDQ : DQ Nat :=
  { heap := [⟨3, 10⟩, ⟨5, 20⟩, ⟨8, 30⟩]
  , live := [(10, 3), (20, 5), (30, 8)]
  , armed := none }

/-- The sample heap is sorted (decidable check, not `native_decide`). -/
theorem sampleDQ_sorted : Sorted sampleDQ.heap := by unfold Sorted; decide

-- Peek returns the earliest deadline (key 10 at deadline 3).
#guard firstLive sampleDQ == some ⟨3, 10⟩
#guard nearest sampleDQ == some 3

-- Arm installs exactly the nearest deadline.
#guard (arm sampleDQ).armed == some 3

-- A full drain at now = 6 fires keys 10 then 20, in deadline order; 30 survives.
#guard (fired sampleDQ.heap sampleDQ.live 6).map (·.key) == [10, 20]

-- Lazy delete: remove key 20, heap is unchanged, and 20 is skipped on drain.
#guard (remove sampleDQ 20).heap == sampleDQ.heap
#guard (fired (remove sampleDQ 20).heap (remove sampleDQ 20).live 6).map (·.key) == [10]

-- Update (slide) key 10's deadline out to 9: the old entry becomes a tombstone,
-- so a drain at now = 6 no longer fires 10 (only 20).
#guard ((insert sampleDQ 10 9).heap).length == 4   -- old entry retained (tombstone)
#guard (fired (insert sampleDQ 10 9).heap (insert sampleDQ 10 9).live 6).map (·.key) == [20]

/-! ### Mutant witnesses (the contract bites)

A queue that armed the *second* entry rather than the nearest would report `5`,
not `3` — `heap_arm_one` rejects it. A drain that eagerly removed on `remove`
would drop the heap entry; `heap_lazy_delete`'s first conjunct (`heap` unchanged)
forbids that. These evaluate to the non-mutant answers, witnessing the theorems
constrain real behavior. -/

/-- The nearest is strictly below the runner-up: arming anything but the head is
observably wrong. -/
theorem sample_nearest_lt_second : nearest sampleDQ = some 3 ∧ (3 : Nat) < 5 := by
  refine ⟨rfl, by decide⟩

/-- Lazy (not eager) deletion is observable: after `remove`, the heap still has
all three entries — an eager implementation would have two. -/
theorem sample_remove_keeps_heap_len : (remove sampleDQ 20).heap.length = 3 := rfl

/-! ## Composition with the reactor correlators

The deadline keys are the reactor's own correlators. Instantiating `K :=
Iocore.Key` (the generation-tagged slab key, which is `DecidableEq`) shows the
deadline queue composes directly with `Iocore.Reactor`: a fired key is the
correlator whose slab slot the reactor will `complete` (idle-close / body
timeout), and the armed deadline is the timeout the reactor's wait loop blocks
on. -/

/-- A deadline queue keyed by reactor correlators — the composition instance. -/
private def reactorDQ : DQ Key :=
  { heap := [⟨100, ⟨1, 0⟩⟩, ⟨200, ⟨2, 0⟩⟩]
  , live := [(⟨1, 0⟩, 100), (⟨2, 0⟩, 200)]
  , armed := none }

theorem reactorDQ_sorted : Sorted reactorDQ.heap := by unfold Sorted; decide

-- The nearest correlator deadline arms; its key is a live slab correlator.
#guard nearest reactorDQ == some 100
#guard (fired reactorDQ.heap reactorDQ.live 150).map (·.key) == [(⟨1, 0⟩ : Key)]

end Iocore
