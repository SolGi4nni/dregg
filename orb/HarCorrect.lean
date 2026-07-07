/-
HarCorrect — a specification of a bounded FIFO recording ring, stated
independently of any implementation, and a refinement theorem showing the
deployed recorder (`Har.Recorder.record`) conforms to it.

The specification is the bounded first-in-first-out queue abstract data type
under the drop-oldest overflow policy — the discipline of a fixed-capacity
circular ("ring") buffer used to retain the most recent records of an unbounded
stream. Applied to a request/response recording log (the HAR 1.2 `log.entries`
array; W3C Web Performance WG, "HTTP Archive (HAR) format", §5.2 — the entries
list, ordered by arrival), a bounded recorder holds a capped, arrival-ordered
window of the stream. Reduced to its ring-buffer invariants the discipline says:

  * the retained window never exceeds the capacity;
  * while below capacity, a record is admitted without dropping anything; and
  * recording into a *full* window evicts exactly the OLDEST retained entry
    (first-in-first-out) and appends the new one at the newest end — so the
    window is always the most-recent `capacity` records, order preserved.

`push` below fixes those clauses as a single reference operator over an
ARBITRARY element type: append the new entry, and drop the head iff the result
overruns the capacity. Its properties (`push_length_le`, `push_not_full`,
`push_evicts_oldest`, `push_suffix`) are proved about `push` alone — nothing in
this section mentions the implementation.

`FifoContract` lifts the reference to a contract over an ABSTRACT ring system
(a state type, a capacity/contents observation, and a record operator). The
refinement (`har_refines_fifo`) instantiates the contract with the DEPLOYED
`Har.Recorder` — `HarRing.step` IS `Har.Recorder.record`, the operator
`Reactor.Recording.recordStep` threads on the served path — and discharges every
clause on all well-formed states. The precondition is discharged along the
deployed path itself (`init_wf` + `rec_preserves_wf`: a cold ring is well-formed
and recording preserves it), so the refinement holds unconditionally over every
reachable ring. Non-vacuity is witnessed by two mutants — one that overruns the
capacity (never evicts) and one that evicts the NEWEST (rejects the incoming
record when full) — each proved to VIOLATE the contract.
-/

import Har.Basic

namespace Har
namespace Correct

/-! ## The specification, stated independently of the implementation

The reference bounded-FIFO push: append the new entry to the retained window,
then drop the oldest (head) entry iff the window now overruns the capacity. This
is the drop-oldest overflow policy of a fixed-capacity ring buffer, written with
no reference to `Har.keepLast` or the deployed recorder. -/
def push {α : Type} (cap : Nat) (buf : List α) (e : α) : List α :=
  if cap < (buf ++ [e]).length then (buf ++ [e]).tail else buf ++ [e]

/-- `List.drop 1` is the tail (elementary, keeps `push` self-contained). -/
theorem drop_one_eq_tail {α : Type} (l : List α) : l.drop 1 = l.tail := by
  cases l <;> rfl

/-- Dropping the head of a nonempty list commutes with a right append. -/
theorem tail_append {α : Type} {buf : List α} (h : buf ≠ []) (l : List α) :
    (buf ++ l).tail = buf.tail ++ l := by
  cases buf with
  | nil => exact absurd rfl h
  | cons a bs => rfl

/-- **Capacity bound (spec).** From a window that fits the capacity, one `push`
still fits: the ring never overruns. -/
theorem push_length_le {α : Type} (cap : Nat) (buf : List α) (e : α)
    (h : buf.length ≤ cap) : (push cap buf e).length ≤ cap := by
  unfold push
  by_cases hc : cap < (buf ++ [e]).length
  · rw [if_pos hc, List.length_tail]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · rw [if_neg hc]; omega

/-- **No premature eviction (spec).** While strictly below capacity, `push`
admits the new entry and drops nothing. -/
theorem push_not_full {α : Type} (cap : Nat) (buf : List α) (e : α)
    (h : buf.length < cap) : push cap buf e = buf ++ [e] := by
  unfold push
  have hlen : (buf ++ [e]).length = buf.length + 1 := by
    simp [List.length_append]
  have hc : ¬ cap < (buf ++ [e]).length := by rw [hlen]; omega
  rw [if_neg hc]

/-- **FIFO eviction (spec).** Recording into a full window evicts exactly the
OLDEST entry (the head) and appends the new one at the newest end. -/
theorem push_evicts_oldest {α : Type} (cap : Nat) (buf : List α) (e : α)
    (hfull : buf.length = cap) (hpos : 0 < cap) :
    push cap buf e = buf.tail ++ [e] := by
  unfold push
  have hlen : (buf ++ [e]).length = cap + 1 := by
    simp [List.length_append, hfull]
  have hc : cap < (buf ++ [e]).length := by rw [hlen]; omega
  rw [if_pos hc]
  have hne : buf ≠ [] := by
    intro h; rw [h] at hfull; simp at hfull; omega
  exact tail_append hne [e]

/-- **Order preservation + retention (spec).** The window is always a suffix of
the arrival history-with-the-new-entry: nothing is reordered and the newest
entry is always kept (it is the last of `buf ++ [e]`, which the suffix retains). -/
theorem push_suffix {α : Type} (cap : Nat) (buf : List α) (e : α) :
    push cap buf e <:+ buf ++ [e] := by
  unfold push
  by_cases hc : cap < (buf ++ [e]).length
  · rw [if_pos hc, ← drop_one_eq_tail]; exact List.drop_suffix _ _
  · rw [if_neg hc]; exact List.suffix_refl _

/-! ## The contract over an abstract ring system

An abstract bounded recorder: an opaque state type, an observed capacity and
retained window (oldest first), and a record operator. The contract never
inspects the state type — it constrains only the observations. -/
structure RingSys (α : Type) where
  σ : Type
  cap : σ → Nat
  view : σ → List α
  step : σ → α → σ

/-- A ring state is well-formed when its retained window fits its capacity. -/
def RingSys.Wf {α : Type} (R : RingSys α) (s : R.σ) : Prop :=
  (R.view s).length ≤ R.cap s

/-- **The bounded-FIFO contract.** A ring system conforms when, for every state
and entry:

* `capStable` — recording never changes the capacity; and
* `refines` — from a well-formed state, recording produces exactly the reference
  bounded-FIFO push of the new entry into the retained window.

`refines` pins the observed behavior to the independent `push` pointwise, which
in turn carries the bound / no-premature-eviction / FIFO-eviction / order
clauses proved above. The definition mentions only `RingSys` and `push`; it does
not refer to the recorder implementation. -/
structure FifoContract {α : Type} (R : RingSys α) : Prop where
  capStable : ∀ s e, R.cap (R.step s e) = R.cap s
  refines : ∀ s e, R.Wf s → R.view (R.step s e) = push (R.cap s) (R.view s) e

/-! ## The deployed recorder as a ring system

`HarRing.step` is the DEPLOYED `Har.Recorder.record` — the same operator
`Reactor.Recording.recordStep` invokes for every served request on the deployed
path. `cap`/`view` are its real capacity/entries projections. -/
def HarRing : RingSys Har.Entry where
  σ := Har.Recorder
  cap := Har.Recorder.cap
  view := Har.Recorder.entries
  step := Har.Recorder.record

/-! ## The refinement: the deployed recorder equals the reference push -/

/-- The deployed `Har.Recorder.record`, on a well-formed ring, produces exactly
the independent bounded-FIFO `push`. This is the core refinement fact: the real
`keepLast cap`-based recorder and the reference append/drop-oldest operator agree
on every reachable window. -/
theorem record_eq_push (r : Har.Recorder) (e : Har.Entry)
    (hwf : r.entries.length ≤ r.cap) :
    (r.record e).entries = push r.cap r.entries e := by
  show Har.keepLast r.cap (r.entries ++ [e]) = push r.cap r.entries e
  have hlen : (r.entries ++ [e]).length = r.entries.length + 1 := by
    simp [List.length_append]
  simp only [Har.keepLast, push, hlen]
  by_cases hc : r.cap < r.entries.length + 1
  · rw [if_pos hc]
    have h1 : r.entries.length + 1 - r.cap = 1 := by omega
    rw [h1, drop_one_eq_tail]
  · rw [if_neg hc]
    have h0 : r.entries.length + 1 - r.cap = 0 := by omega
    rw [h0, List.drop_zero]

/-- **Refinement.** The deployed `Har.Recorder` satisfies the bounded-FIFO
contract: it never changes its capacity, and on every well-formed ring its
`record` produces exactly the reference push. This is the headline correctness
result — the deployed recorder *refines* the independent specification. -/
theorem har_refines_fifo : FifoContract HarRing where
  capStable := fun _ _ => rfl
  refines := fun s e hwf => record_eq_push s e hwf

/-! ## The precondition is discharged along the deployed path -/

/-- A cold ring (empty, any capacity) is well-formed. -/
theorem init_wf (cap : Nat) : HarRing.Wf { cap := cap, entries := [] } := by
  show ([] : List Har.Entry).length ≤ cap
  simp

/-- Recording preserves well-formedness — so every ring reachable from a cold
start satisfies the `refines` precondition, and the refinement holds
unconditionally over all reachable states. -/
theorem rec_preserves_wf (s : Har.Recorder) (e : Har.Entry) :
    HarRing.Wf (HarRing.step s e) :=
  Har.record_length_le_cap s e

/-! ## Spec-mandated behavior, inherited by the DEPLOYED record via the refinement -/

/-- **Capacity bound (deployed).** The deployed `Har.Recorder.record` never
overruns the capacity, on any well-formed ring. -/
theorem har_record_bounded (s : Har.Recorder) (e : Har.Entry)
    (hwf : s.entries.length ≤ s.cap) :
    (s.record e).entries.length ≤ s.cap := by
  rw [record_eq_push s e hwf]; exact push_length_le _ _ _ hwf

/-- **FIFO eviction (deployed).** On a full ring (positive capacity), the
deployed `Har.Recorder.record` evicts exactly the oldest entry and appends the
new one at the newest end. -/
theorem har_record_evicts_oldest (s : Har.Recorder) (e : Har.Entry)
    (hfull : s.entries.length = s.cap) (hpos : 0 < s.cap) :
    (s.record e).entries = s.entries.tail ++ [e] := by
  rw [record_eq_push s e (Nat.le_of_eq hfull)]
  exact push_evicts_oldest _ _ _ hfull hpos

/-- **Order preservation + retention (deployed).** The deployed record leaves the
window a suffix of the arrival history-with-the-new-entry — nothing reordered,
newest kept. -/
theorem har_record_most_recent (s : Har.Recorder) (e : Har.Entry)
    (hwf : s.entries.length ≤ s.cap) :
    (s.record e).entries <:+ s.entries ++ [e] := by
  rw [record_eq_push s e hwf]; exact push_suffix _ _ _

/-! ## Non-vacuity: broken recorders violate the specification -/

/-- Two distinct concrete records. -/
def e0 : Har.Entry := { method := "GET", path := "/a", status := 200 }
def e1 : Har.Entry := { method := "GET", path := "/b", status := 404 }

/-- A capacity-1 ring already holding one record — full. -/
def s0 : Har.Recorder := { cap := 1, entries := [e0] }

/-- Mutant 1 — the overrunning recorder: it appends unconditionally and never
evicts, so a full ring overruns its capacity. -/
def OverflowRing : RingSys Har.Entry where
  σ := Har.Recorder
  cap := Har.Recorder.cap
  view := Har.Recorder.entries
  step := fun s e => { s with entries := s.entries ++ [e] }

/-- Mutant 2 — the newest-evicting recorder: when full it drops the INCOMING
record and keeps the oldest, i.e. it evicts the newest instead of the oldest. -/
def RejectRing : RingSys Har.Entry where
  σ := Har.Recorder
  cap := Har.Recorder.cap
  view := Har.Recorder.entries
  step := fun s e =>
    if s.entries.length < s.cap then { s with entries := s.entries ++ [e] } else s

/-- **Non-vacuity, clause 1.** A recorder that overruns its capacity fails the
contract: from the full capacity-1 ring `s0`, the overflow mutant retains
`[e0, e1]` (length 2 > 1), while the spec `push` retains `[e1]`. -/
theorem overflow_violates : ¬ FifoContract OverflowRing := by
  intro h
  have hwf : OverflowRing.Wf s0 := by unfold RingSys.Wf; decide
  have heq := h.refines s0 e1 hwf
  exact absurd heq (by decide)

/-- **Non-vacuity, clause 2.** A recorder that evicts the NEWEST fails the
contract: from the full capacity-1 ring `s0`, the reject mutant keeps the oldest
`[e0]`, while the spec `push` evicts the oldest and keeps the newest `[e1]`. -/
theorem reject_violates : ¬ FifoContract RejectRing := by
  intro h
  have hwf : RejectRing.Wf s0 := by unfold RingSys.Wf; decide
  have heq := h.refines s0 e1 hwf
  exact absurd heq (by decide)

end Correct
end Har
