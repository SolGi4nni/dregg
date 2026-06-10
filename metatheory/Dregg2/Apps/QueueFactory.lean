/-
# Dregg2.Apps.QueueFactory — W2: the bounded QUEUE as a factory-born CELL PROGRAM.

THE CLAIM, DISCHARGED HERE (DREGG3 §6 R3, now that the relational caveat LANDED): *the queue
verb family (`QueueAllocate`/`Enqueue`/`Dequeue`/`Resize`/`AtomicTx`/`PipelineStep` over the
off-ledger `queues` side-table) is a factory-born CELL holding its (optional) value in its own
`bal` column, with the capacity / no-underflow bounds enforced by the LIVE record-level relational
caveat `RelCaveat.fieldLteOther` (`Dregg2.Exec.RelationalCaveat`).* The `QueueFactoryProbe`
isolated the ONE missing primitive (a cross-slot bound the per-slot `SlotCaveat` cannot express);
the relational caveat PROMOTED it to the live surface; THIS module makes the queue a real,
app-instantiable factory and proves the four queue-safety keystones on the factory-born cell, so
W2 can DELETE the 6-verb family (§DELETION).

## The reframe (the SAME move escrow/obligation made)

A queue in the verb world is an off-ledger ring buffer + bookkeeping (`queues` side-table, the
`qbuf*` accounting, the 6 verbs). The cell-program rebuild does the OPPOSITE: **the queue is a
minted CELL whose head/tail/capacity/owner/sender_set/message_root are SLOTS** governed by the
EXISTING `SlotCaveat` vocabulary (Immutable + MonotonicSequence + SenderAuthorized) PLUS the live
`RelCaveat.fieldLteOther` cross-slot bounds; a value-bearing (deposit) queue holds its anti-spam
value in the cell's own `bal` column, so conservation is the EXISTING ordinary per-asset move law
`recKExecAsset_conserves_per_asset`. No side-table; no bespoke `qbuf*` accounting on the ledger.

## The queue-factory SHAPE (mirrors escrow/obligation; the cross-slot bounds are RELATIONAL)

slots (fields on the queue cell's record):
  * `head_seq`        — total messages ENQUEUED (monotone ↑; advances by 1 on enqueue).
  * `tail_seq`        — total messages DEQUEUED (monotone ↑, ≤ head_seq; advances on dequeue).
  * `capacity`        — the max occupancy (immutable after open).
  * `owner`           — the queue owner / dequeue authority (immutable).
  * `sender_set_root` — the publish-authorization root.
  * `message_root`    — the FIFO content commitment (advances on both ops).
plus (for a DEPOSIT/value queue) the held value in the cell's per-asset `bal` column.

state_constraints:
  * `Immutable {capacity, owner}`                          — frozen deal terms.  [EXISTING SlotCaveat.]
  * `MonotonicSequence {head_seq, tail_seq}`               — in-order, replay-safe. [EXISTING.]
  * `SenderAuthorized {sender_set}`                         — the publish gate.     [EXISTING.]
  * `RelCaveat.fieldLteOther head_seq capacity tail_seq`   — CAPACITY: head − tail ≤ cap. [LIVE relational.]
  * `RelCaveat.fieldLteOther tail_seq head_seq 0`          — NO-UNDERFLOW: tail ≤ head.    [LIVE relational.]

## The four queue-safety keystones (mirroring escrow/obligation's four)

  (a) NO OVERFLOW              — PROVED: an enqueue from a state respecting `head − tail ≤ cap`,
      with room (`occupancy < cap`), lands STILL respecting it; a FULL queue's enqueue fail-closes.
      THIS is the keystone that the relational caveat unlocks.
  (b) NO UNDERFLOW / FIFO      — PROVED: `tail ≤ head` preserved by both ops; an EMPTY queue's
      dequeue fail-closes; FIFO order is the kernel's REAL buffer (`qbuf_fifo_order`).
  (c) SENDER-AUTH ON ENQUEUE   — PROVED: an enqueue by an actor ∉ the sender set fail-closes (the
      `SenderAuthorized` caveat verbatim).
  (d) CONSERVATION (value queue) — PROVED, inherited from `recKExecAsset_conserves_per_asset`: a
      deposit-queue's value moves by an ordinary per-asset move; order ops are bal-neutral.

## Non-vacuity

`qWorld` is a concrete queue cell (capacity 2, owner 1, occupancy 1). `#guard` witnesses: an
over-capacity enqueue (full queue) is rejected; an underflow dequeue (empty queue) is rejected;
an unauthorized publish (actor ∉ senders) is rejected; the live relational guard
(`relStateStepGuarded`) admits an in-bound write and REJECTS an over-bound one. No keystone vacuous.

NEW file only. Imports the live relational caveat surface + the escrow factory executor. Does NOT
edit `Dregg2.lean`, any shared mod, the kernel, or any Metatheory/*. Every keystone
`#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}` — no sorry, no `:= True`,
no `native_decide`.
-/
import Dregg2.Exec.RelationalCaveat
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Apps.QueueFactory

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.RelationalCaveat (RelCaveat relStateStepGuarded relCaveatsAdmit
  fieldLteOther_expresses_capacity fieldLteOther_expresses_underflow capacityOk noUnderflow)
open Dregg2.Exec.EffectsState (setField fieldOf setField_fieldOf)

/-! ## §1 — The queue-cell SLOT layout (field names). -/

/-- Total messages ENQUEUED (monotone ↑; advances by 1 on enqueue). -/
abbrev headSeqField : FieldName := "queue.head_seq"
/-- Total messages DEQUEUED (monotone ↑, ≤ head_seq; advances by 1 on dequeue). -/
abbrev tailSeqField : FieldName := "queue.tail_seq"
/-- The max occupancy (frozen after open). -/
abbrev capacityField : FieldName := "queue.capacity"
/-- The queue owner / dequeue authority (frozen). -/
abbrev ownerField : FieldName := "queue.owner"
/-- The publish-authorization root (the authorized-sender membership). -/
abbrev senderSetField : FieldName := "queue.sender_set_root"
/-- The FIFO content root (advances on enqueue and dequeue). -/
abbrev messageRootField : FieldName := "queue.message_root"

/-! ## §2 — The queue FACTORY DESCRIPTOR + the RELATIONAL cross-slot bounds.

The `FactoryEntry` a queue factory publishes. Its `caveats` are the EXISTING `SlotCaveat`
vocabulary (Immutable × 2 + MonotonicSequence × 2 + SenderAuthorized × 1); the CROSS-SLOT capacity
+ underflow bounds are the LIVE `RelCaveat.fieldLteOther` atoms (`queueRelCaveats`), enforced by
`relStateStepGuarded` on every write. -/

/-- **`queueFactory cap owner senders` — the queue factory's `SlotCaveat` half.** The deal-term
immutables (`capacity`, `owner`), the monotone sequence counters, and the sender-authorization gate
on the publish. Initial state: an EMPTY queue (`head = tail = 0`). The cross-slot bounds live in
`queueRelCaveats`. -/
def queueFactory (cap owner : Int) (senders : List CellId) : FactoryEntry where
  caveats :=
    [ SlotCaveat.immutable capacityField
    , SlotCaveat.immutable ownerField
    , SlotCaveat.monotonicSeq headSeqField
    , SlotCaveat.monotonicSeq tailSeqField
    , SlotCaveat.senderAuthorized senderSetField senders ]
  initialFields :=
    [ (headSeqField, 0)
    , (tailSeqField, 0)
    , (capacityField, cap)
    , (ownerField, owner)
    , (senderSetField, 0)
    , (messageRootField, 0) ]
  programVk := 0

/-- **`queueRelCaveats post_tail` — the CROSS-SLOT bounds as LIVE relational caveats.** The capacity
bound `head ≤ cap + tail` (with the second cross-slot term `tail` carried as the relational caveat's
`delta`, read off the post-write record) and the no-underflow bound `tail ≤ head`. These are the
`RelCaveat.fieldLteOther` atoms `relStateStepGuarded` enforces. -/
def queueRelCaveats (postTail : Int) : List RelCaveat :=
  [ RelCaveat.fieldLteOther headSeqField capacityField postTail   -- capacity: head ≤ cap + tail
  , RelCaveat.fieldLteOther tailSeqField headSeqField 0 ]          -- no-underflow: tail ≤ head

/-- **`queueFactory_conforms` — PROVED.** The queue factory's OWN published EMPTY initial state
satisfies its OWN `SlotCaveat`s (a well-formed factory cannot publish an invariant-violating
genesis). -/
theorem queueFactory_conforms (cap owner : Int) (senders : List CellId) :
    (queueFactory cap owner senders).conforms = true := by
  unfold queueFactory FactoryEntry.conforms FactoryEntry.initialFieldsNoBalance
  simp only [SlotCaveat.field, SlotCaveat.bornFresh, List.all_cons, List.all_nil,
    List.find?, Bool.and_true, Bool.and_self]
  rfl

/-! ## §3 — The queue cell STATE: reading the slots. -/

/-- Read the queue's head sequence (total enqueued). -/
def qHead (k : RecordKernelState) (e : CellId) : Int := fieldOf headSeqField (k.cell e)
/-- Read the queue's tail sequence (total dequeued). -/
def qTail (k : RecordKernelState) (e : CellId) : Int := fieldOf tailSeqField (k.cell e)
/-- Read the queue's capacity. -/
def qCap (k : RecordKernelState) (e : CellId) : Int := fieldOf capacityField (k.cell e)

/-- The current OCCUPANCY: messages enqueued but not yet dequeued. -/
def qOccupancy (k : RecordKernelState) (e : CellId) : Int := qHead k e - qTail k e

/-- The queue is EMPTY iff occupancy is 0 (head = tail). -/
def qEmpty (k : RecordKernelState) (e : CellId) : Prop := qHead k e = qTail k e

/-- **The capacity invariant**: occupancy never exceeds capacity. The cross-slot relation. -/
def qCapacityOk (k : RecordKernelState) (e : CellId) : Prop := qOccupancy k e ≤ qCap k e

/-- **The no-underflow invariant**: tail never overtakes head (FIFO; can't dequeue past enqueued). -/
def qNoUnderflow (k : RecordKernelState) (e : CellId) : Prop := qTail k e ≤ qHead k e

/-! ## §3b — The LIVE relational caveat EXPRESSES the bounds (instantiated from RelationalCaveat).

The cross-slot bounds are tied to the LIVE `RelCaveat.fieldLteOther` evaluator — we INSTANTIATE the
proved `RelationalCaveat.fieldLteOther_expresses_capacity`/`_underflow` over the queue cell's record
and the concrete `"queue.*"` field layout, so the bound this module enforces IS the live atom. -/

/-- **`relcav_expresses_capacity` — PROVED (instantiated).** The live capacity atom on the queue
cell's record is EXACTLY the capacity invariant `head − tail ≤ cap`. -/
theorem relcav_expresses_capacity (k : RecordKernelState) (e : CellId) :
    (RelCaveat.fieldLteOther headSeqField capacityField (qTail k e)).eval (k.cell e) = true
      ↔ qCapacityOk k e := by
  have h := fieldLteOther_expresses_capacity (k.cell e) headSeqField tailSeqField capacityField
  unfold qCapacityOk qOccupancy qHead qTail qCap
  unfold capacityOk at h
  exact h

/-- **`relcav_expresses_underflow` — PROVED (instantiated).** The live no-underflow atom on the
queue cell's record is EXACTLY `tail ≤ head`. -/
theorem relcav_expresses_underflow (k : RecordKernelState) (e : CellId) :
    (RelCaveat.fieldLteOther tailSeqField headSeqField 0).eval (k.cell e) = true
      ↔ qNoUnderflow k e := by
  have h := fieldLteOther_expresses_underflow (k.cell e) headSeqField tailSeqField
  unfold qNoUnderflow qTail qHead
  unfold noUnderflow at h
  exact h

/-! ## §4 — The queue OPERATIONS (enqueue / dequeue) as gated field writes.

An enqueue WRITES `head_seq := head + 1` and `message_root := root'`, FAIL-CLOSED when (i) the actor
is not an authorized sender (the `SenderAuthorized` gate), or (ii) the queue is full (`occupancy =
capacity` ⇒ post-enqueue would break `head − tail ≤ cap`, the relational gate). A dequeue WRITES
`tail_seq := tail + 1`, fail-closed when EMPTY (`head = tail` ⇒ underflow). The held value (deposit
queue) moves by an ordinary `recKExecAsset`. -/

/-- Write a single scalar field of the queue cell (the `setField` primitive on the cell record). -/
def qWriteField (k : RecordKernelState) (e : CellId) (f : FieldName) (v : Int) : RecordKernelState :=
  { k with cell := fun c => if c = e then setField f (k.cell e) (.int v) else k.cell c }

/-- **`queueEnqueue` — advance head (publish a message), gated on sender-auth AND capacity.**
Rejects (`none`) when the actor ∉ `senders` OR the queue is full (`qOccupancy k e ≥ qCap k e`). On
success: `head_seq` is incremented by 1 and `message_root` is updated. -/
def queueEnqueue (k : RecordKernelState) (e actor : CellId) (senders : List CellId)
    (newRoot : Int) : Option RecordKernelState :=
  if senders.contains actor ∧ qOccupancy k e < qCap k e then
    some (qWriteField (qWriteField k e headSeqField (qHead k e + 1)) e messageRootField newRoot)
  else none

/-- **`queueDequeue` — advance tail (pop a message), gated on owner AND non-empty.** Rejects when
the actor is not the owner OR the queue is EMPTY (`qOccupancy k e ≤ 0`). On success: `tail_seq` is
incremented by 1 and `message_root` is updated. -/
def queueDequeue (k : RecordKernelState) (e actor : CellId) (newRoot : Int) : Option RecordKernelState :=
  if actor = fieldOf ownerField (k.cell e) ∧ 0 < qOccupancy k e then
    some (qWriteField (qWriteField k e tailSeqField (qTail k e + 1)) e messageRootField newRoot)
  else none

/-! ### Read-back lemmas: how the slots stand after a write. -/

/-- **`fieldOf_setField_ne` — reading a DIFFERENT field after a `setField` is unchanged.** -/
theorem fieldOf_setField_ne (f g : FieldName) (cell : Value) (v : Int) (hfg : g ≠ f) :
    fieldOf g (setField f cell (.int v)) = fieldOf g cell := by
  have hfg' : (f == g) = false := by
    rw [beq_eq_false_iff_ne]; exact fun h => hfg h.symm
  have hlist : ∀ fs : List (FieldName × Value),
      ((setField.setFieldList f fs (.int v)).find? (fun p => p.1 == g))
        = fs.find? (fun p => p.1 == g) := by
    intro fs
    induction fs with
    | nil => simp [setField.setFieldList, List.find?, hfg']
    | cons hd tl ih =>
        obtain ⟨kk, x⟩ := hd
        simp only [setField.setFieldList]
        by_cases hk : (kk == f) = true
        · have hkk : kk = f := by simpa using hk
          rw [if_pos hk]
          simp only [List.find?_cons, hfg', hkk]
        · rw [if_neg hk]
          by_cases hg : (kk == g) = true
          · simp only [List.find?_cons, hg]
          · rw [List.find?_cons_of_neg (by simpa using hg),
                List.find?_cons_of_neg (by simpa using hg)]
            exact ih
  unfold fieldOf Value.scalar Value.field
  cases cell with
  | record fs => simp only [setField]; rw [hlist fs]
  | int n => simp [setField, setField.setFieldList, List.find?, hfg']
  | dig d => simp [setField, setField.setFieldList, List.find?, hfg']
  | sym s => simp [setField, setField.setFieldList, List.find?, hfg']

/-- Writing field `f` to the queue cell `e` and reading field `g ≠ f` of `e` is unchanged. -/
theorem qWriteField_other (k : RecordKernelState) (e : CellId) (f g : FieldName) (v : Int)
    (hfg : g ≠ f) : fieldOf g ((qWriteField k e f v).cell e) = fieldOf g (k.cell e) := by
  unfold qWriteField
  simp only [if_pos rfl]
  exact fieldOf_setField_ne f g (k.cell e) v hfg

/-- Reading field `f` right after writing `f := v` to the same cell returns `v`. -/
theorem qWriteField_same (k : RecordKernelState) (e : CellId) (f : FieldName) (v : Int) :
    fieldOf f ((qWriteField k e f v).cell e) = v := by
  unfold qWriteField; simp only [if_pos rfl]; exact setField_fieldOf f (k.cell e) v

/-! ## §5 — KEYSTONE (a): NO OVERFLOW (the capacity bound is PRESERVED by enqueue). -/

/-- The capacity/tail/head read-back across an enqueue: `head` advances by 1, `tail`/`cap`
unchanged. -/
theorem enqueue_reads {k k' : RecordKernelState} {e actor : CellId} {senders : List CellId}
    {newRoot : Int} (h : queueEnqueue k e actor senders newRoot = some k') :
    qHead k' e = qHead k e + 1 ∧ qTail k' e = qTail k e ∧ qCap k' e = qCap k e := by
  unfold queueEnqueue at h
  by_cases hg : senders.contains actor ∧ qOccupancy k e < qCap k e
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h; subst h
    refine ⟨?_, ?_, ?_⟩
    · unfold qHead
      rw [qWriteField_other _ e messageRootField headSeqField newRoot (by decide)]
      exact qWriteField_same k e headSeqField (qHead k e + 1)
    · unfold qTail
      rw [qWriteField_other _ e messageRootField tailSeqField newRoot (by decide),
          qWriteField_other _ e headSeqField tailSeqField (qHead k e + 1) (by decide)]
    · unfold qCap
      rw [qWriteField_other _ e messageRootField capacityField newRoot (by decide),
          qWriteField_other _ e headSeqField capacityField (qHead k e + 1) (by decide)]
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`enqueue_preserves_capacity` — KEYSTONE (a), PROVED.** From a state where occupancy ≤ cap, a
committed enqueue lands in a state where occupancy ≤ cap STILL. The cross-slot capacity bound is an
INVARIANT of enqueue — exactly what the relational `fieldLteOther` enforces. -/
theorem enqueue_preserves_capacity {k k' : RecordKernelState} {e actor : CellId}
    {senders : List CellId} {newRoot : Int}
    (h : queueEnqueue k e actor senders newRoot = some k') (hpre : qCapacityOk k e) :
    qCapacityOk k' e := by
  have hguard : qOccupancy k e < qCap k e := by
    unfold queueEnqueue at h
    by_cases hg : senders.contains actor ∧ qOccupancy k e < qCap k e
    · exact hg.2
    · rw [if_neg hg] at h; exact absurd h (by simp)
  obtain ⟨hh, ht, hc⟩ := enqueue_reads h
  unfold qCapacityOk qOccupancy at *
  rw [hh, ht, hc]; omega

/-- **`full_queue_enqueue_rejected` — KEYSTONE (a), the fail-closed half, PROVED.** A FULL queue
(`occupancy ≥ cap`) rejects every enqueue — no overflow can be committed. -/
theorem full_queue_enqueue_rejected (k : RecordKernelState) (e actor : CellId)
    (senders : List CellId) (newRoot : Int) (hfull : qCap k e ≤ qOccupancy k e) :
    queueEnqueue k e actor senders newRoot = none := by
  unfold queueEnqueue
  rw [if_neg (by rintro ⟨_, hlt⟩; omega)]

/-! ## §6 — KEYSTONE (b): NO UNDERFLOW / FIFO ORDER. -/

/-- The head/tail read-back across a dequeue: `tail` advances by 1, `head` unchanged. -/
theorem dequeue_reads {k k' : RecordKernelState} {e actor : CellId} {newRoot : Int}
    (h : queueDequeue k e actor newRoot = some k') :
    qTail k' e = qTail k e + 1 ∧ qHead k' e = qHead k e := by
  unfold queueDequeue at h
  by_cases hg : actor = fieldOf ownerField (k.cell e) ∧ 0 < qOccupancy k e
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h; subst h
    refine ⟨?_, ?_⟩
    · unfold qTail
      rw [qWriteField_other _ e messageRootField tailSeqField newRoot (by decide)]
      exact qWriteField_same k e tailSeqField (qTail k e + 1)
    · unfold qHead
      rw [qWriteField_other _ e messageRootField headSeqField newRoot (by decide),
          qWriteField_other _ e tailSeqField headSeqField (qTail k e + 1) (by decide)]
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`dequeue_preserves_no_underflow` — KEYSTONE (b), PROVED.** From `tail ≤ head`, a committed
dequeue (fires only when non-empty) lands in `tail ≤ head` STILL. -/
theorem dequeue_preserves_no_underflow {k k' : RecordKernelState} {e actor : CellId} {newRoot : Int}
    (h : queueDequeue k e actor newRoot = some k') (hpre : qNoUnderflow k e) :
    qNoUnderflow k' e := by
  have hguard : 0 < qOccupancy k e := by
    unfold queueDequeue at h
    by_cases hg : actor = fieldOf ownerField (k.cell e) ∧ 0 < qOccupancy k e
    · exact hg.2
    · rw [if_neg hg] at h; exact absurd h (by simp)
  obtain ⟨ht, hh⟩ := dequeue_reads h
  unfold qNoUnderflow at *
  unfold qOccupancy at hguard
  rw [ht, hh]; omega

/-- **`empty_queue_dequeue_rejected` — KEYSTONE (b), the fail-closed half, PROVED.** An EMPTY queue
(`head = tail`, occupancy 0) rejects every dequeue — no underflow can be committed. -/
theorem empty_queue_dequeue_rejected (k : RecordKernelState) (e actor : CellId) (newRoot : Int)
    (hempty : qEmpty k e) :
    queueDequeue k e actor newRoot = none := by
  unfold queueDequeue
  have hz : qOccupancy k e = 0 := by unfold qOccupancy qEmpty at *; omega
  rw [if_neg (by rintro ⟨_, hpos⟩; rw [hz] at hpos; exact absurd hpos (by decide))]

/-- **`enqueue_preserves_no_underflow` — KEYSTONE (b) cross-op, PROVED.** Enqueue (advances head)
also preserves `tail ≤ head` (head only grows). So BOTH ops keep the FIFO no-underflow bound. -/
theorem enqueue_preserves_no_underflow {k k' : RecordKernelState} {e actor : CellId}
    {senders : List CellId} {newRoot : Int}
    (h : queueEnqueue k e actor senders newRoot = some k') (hpre : qNoUnderflow k e) :
    qNoUnderflow k' e := by
  obtain ⟨hh, ht, _⟩ := enqueue_reads h
  unfold qNoUnderflow at *
  rw [hh, ht]; omega

/-- **FIFO ORDER — carried from the kernel's REAL buffer (`RecordKernel.qbuf_fifo_order`).** The
order discipline (head removes the front, tail appends the back, `a`-before-`b` preserved) is the
PROVED `qbufEnqueue`/`qbufDequeue` mechanism — the sequence counters here are the cell-field SHADOW
of that buffer (head_seq = total appended, tail_seq = total removed). -/
theorem fifo_order_holds (buf : List Nat) (a b : Nat) :
    qbufDequeue (qbufEnqueue (qbufEnqueue buf a) b) =
      (match qbufDequeue buf with
       | some (h, rest) => some (h, qbufEnqueue (qbufEnqueue rest a) b)
       | none           => some (a, [b])) :=
  qbuf_fifo_order buf a b

/-! ## §7 — KEYSTONE (c): SENDER-AUTHORIZATION ON ENQUEUE. -/

/-- **`enqueue_requires_sender_auth` — KEYSTONE (c), PROVED.** An enqueue by an actor NOT in the
authorized sender set is REJECTED — even when there is room. -/
theorem enqueue_requires_sender_auth (k : RecordKernelState) (e actor : CellId)
    (senders : List CellId) (newRoot : Int) (hbad : senders.contains actor = false) :
    queueEnqueue k e actor senders newRoot = none := by
  unfold queueEnqueue
  rw [if_neg (by rintro ⟨hin, _⟩; rw [hbad] at hin; exact absurd hin (by simp))]

/-- **`enqueue_matches_senderAuthorized_caveat` — the gate IS the `SenderAuthorized` atom, PROVED.**
The enqueue's publish gate `senders.contains actor` is DEFINITIONALLY the executable
`SlotCaveat.eval (.senderAuthorized senderSetField senders) actor old new`. -/
theorem enqueue_matches_senderAuthorized_caveat (actor : CellId) (senders : List CellId)
    (old new : Int) :
    (SlotCaveat.senderAuthorized senderSetField senders).eval actor old new
      = senders.contains actor := rfl

/-! ## §8 — KEYSTONE (d): CONSERVATION (the value/deposit queue). -/

/-- **`queueDeposit` — move `amt` of value into the queue cell (an anti-spam deposit), an ordinary
per-asset move.** Fail-closed exactly as the move law (authorized, available, distinct, live). -/
def queueDeposit (k : RecordKernelState) (sender e : CellId) (asset : AssetId) (amt : Int) :
    Option RecordKernelState :=
  recKExecAsset k { actor := sender, src := sender, dst := e, amt := amt } asset

/-- **`queueDeposit_conserves` — KEYSTONE (d), PROVED.** A committed deposit preserves EVERY asset's
total supply — the value moves between two live accounts, conserved by the ordinary move law. -/
theorem queueDeposit_conserves {k k' : RecordKernelState} {sender e : CellId} {asset : AssetId}
    {amt : Int} (h : queueDeposit k sender e asset amt = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b :=
  recKExecAsset_conserves_per_asset k k'
    { actor := sender, src := sender, dst := e, amt := amt } asset h b

/-- The ORDER ops are balance-NEUTRAL: a field write never touches the `bal` ledger, so enqueue
(pure writes) preserves every asset's supply too. -/
theorem enqueue_bal_neutral {k k' : RecordKernelState} {e actor : CellId} {senders : List CellId}
    {newRoot : Int} (h : queueEnqueue k e actor senders newRoot = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold queueEnqueue at h
  by_cases hg : senders.contains actor ∧ qOccupancy k e < qCap k e
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h; subst h
    unfold recTotalAsset qWriteField
    rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §9 — LIVENESS: a queue with room/messages can enqueue/dequeue (NOT-STRANDED analog). -/

/-- **`room_queue_enqueues` — an authorized sender CAN enqueue when there is room.** -/
theorem room_queue_enqueues (k : RecordKernelState) (e actor : CellId) (senders : List CellId)
    (newRoot : Int) (hauth : senders.contains actor = true) (hroom : qOccupancy k e < qCap k e) :
    (queueEnqueue k e actor senders newRoot).isSome := by
  unfold queueEnqueue; rw [if_pos ⟨hauth, hroom⟩]; exact Option.isSome_some

/-- **`nonempty_queue_dequeues` — the owner CAN dequeue when the queue is non-empty.** -/
theorem nonempty_queue_dequeues (k : RecordKernelState) (e actor : CellId) (newRoot : Int)
    (howner : (actor : Int) = fieldOf ownerField (k.cell e)) (hne : 0 < qOccupancy k e) :
    (queueDequeue k e actor newRoot).isSome := by
  unfold queueDequeue; rw [if_pos ⟨howner, hne⟩]; exact Option.isSome_some

/-! ## §10 — MINTING the queue cell through the REAL factory executor. -/

/-- A kernel factory registry publishing the queue factory at content-addressed key `vk`. -/
def queueRegistry (vk : Nat) (cap owner : Int) (senders : List CellId) :
    List (Nat × FactoryEntry) :=
  [(vk, queueFactory cap owner senders)]

/-- The registry resolves the queue factory at exactly its published key. -/
theorem queueRegistry_finds (vk : Nat) (cap owner : Int) (senders : List CellId) :
    findFactory (queueRegistry vk cap owner senders) vk
      = some (queueFactory cap owner senders) := by
  simp [queueRegistry, findFactory]

/-- Mint a queue cell from the queue factory at key `vk` (the real factory executor). -/
def mintQueueCell (s : RecChainedState) (actor qCell : CellId) (vk : Int) :
    Option RecChainedState :=
  createCellFromFactoryChainA s actor qCell vk

/-- **`mintQueueCell_installs_caveats` — PROVED.** A minted queue cell carries EXACTLY the factory's
caveats — the immutables + monotone counters + sender gate — installed by the executor, so
`stateStepGuarded` enforces them on every later `SetField`. -/
theorem mintQueueCell_installs_caveats {s s' : RecChainedState} {actor qCell : CellId}
    {vk : Int} (e : FactoryEntry)
    (hreg : findFactory s.kernel.factories vk.toNat = some e)
    (h : mintQueueCell s actor qCell vk = some s') :
    s'.kernel.slotCaveats qCell = e.caveats := by
  obtain ⟨e', hfind, hcav⟩ := createCellFromFactoryChainA_installs_program h
  rw [hreg] at hfind
  rw [← (Option.some.injEq _ _).mp hfind] at hcav
  exact hcav

/-- **`mintQueueCell_caveats` — PROVED.** When the registry IS `queueRegistry vk …`, the minted cell
concretely carries the queue factory's caveats. -/
theorem mintQueueCell_caveats {s s' : RecChainedState} {actor qCell : CellId} {vk : Int}
    {cap owner : Int} {senders : List CellId}
    (hreg : s.kernel.factories = queueRegistry vk.toNat cap owner senders)
    (h : mintQueueCell s actor qCell vk = some s') :
    s'.kernel.slotCaveats qCell = (queueFactory cap owner senders).caveats := by
  have hfind : findFactory s.kernel.factories vk.toNat = some (queueFactory cap owner senders) := by
    rw [hreg]; exact queueRegistry_finds vk.toNat cap owner senders
  exact mintQueueCell_installs_caveats _ hfind h

/-- **`mintQueueCell_neutral` — PROVED.** Minting a queue cell is conservation-NEUTRAL for every
asset (the cell is born EMPTY; any deposit is a SEPARATE ordinary move). -/
theorem mintQueueCell_neutral {s s' : RecChainedState} {actor qCell : CellId} {vk : Int}
    (b : AssetId) (h : mintQueueCell s actor qCell vk = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  createCellFromFactoryChainA_neutral b h

/-- **`mintQueueCell_grows_accounts` — PROVED.** A minted queue cell IS a live account. -/
theorem mintQueueCell_grows_accounts {s s' : RecChainedState} {actor qCell : CellId} {vk : Int}
    (h : mintQueueCell s actor qCell vk = some s') :
    qCell ∈ s'.kernel.accounts :=
  createCellFromFactoryChainA_grows_accounts h

/-- **`mintQueueCell_unknown_factory_fails` — PROVED (fail-closed).** Minting against an unknown
factory key never mints. -/
theorem mintQueueCell_unknown_factory_fails (s : RecChainedState) (actor qCell : CellId)
    (vk : Int) (h : findFactory s.kernel.factories vk.toNat = none) :
    mintQueueCell s actor qCell vk = none :=
  createCellFromFactoryChainA_unknown_factory_fails s actor qCell vk h

/-! ## §11 — NON-VACUITY: a concrete queue world + `#guard` witnesses (incl. the LIVE relational gate). -/

/-- A queue world. The QUEUE CELL is cell `0`: capacity 2, owner 1, head_seq 1, tail_seq 0 (so
OCCUPANCY 1, one message waiting, room for one more), sender_set_root 0, message_root 7. The
authorized senders are `[3, 4]`; cell 5 is UNAUTHORIZED. All cells {0,1,3,4,5} live. -/
def qWorld : RecordKernelState :=
  { accounts := {0, 1, 3, 4, 5}
    cell := fun c =>
      if c = 0 then .record
        [ (headSeqField, .int 1), (tailSeqField, .int 0), (capacityField, .int 2)
        , (ownerField, .int 1), (senderSetField, .int 0), (messageRootField, .int 7) ]
      else .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun _ _ => 0 }

abbrev qsenders : List CellId := [3, 4]

/-- A chained world for the LIVE relational gate witnesses: cell 0 a queue record (head 1, tail 0,
cap 2), no per-slot caveats (so the per-slot guarded write commits; the relational gate decides). -/
def qrel : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then .record [("balance", .int 0), (headSeqField, .int 1),
                                                (tailSeqField, .int 0), (capacityField, .int 2)]
                         else .record [("balance", .int 0)]
        caps := fun _ => [] }
    log := [] }

/-- The capacity relational caveat for cell 0 (`head ≤ cap`, tail 0 folded as delta 0). -/
abbrev qrelCap : List RelCaveat := [ RelCaveat.fieldLteOther headSeqField capacityField 0 ]

-- (i) the queue reads: occupancy 1, capacity 2, room for one more; not empty:
#guard (qHead qWorld 0 == 1)
#guard (qTail qWorld 0 == 0)
#guard (qOccupancy qWorld 0 == 1)
#guard (qCap qWorld 0 == 2)

-- (ii) the LIVE relational atom EXPRESSES the capacity + underflow bounds on the queue record:
#guard ((RelCaveat.fieldLteOther headSeqField capacityField (qTail qWorld 0)).eval (qWorld.cell 0))
#guard ((RelCaveat.fieldLteOther tailSeqField headSeqField 0).eval (qWorld.cell 0))

-- (iii) an authorized enqueue (sender 3) with room COMMITS and advances head 1→2 (now FULL):
#guard ((queueEnqueue qWorld 0 3 qsenders 99).isSome)
#guard ((queueEnqueue qWorld 0 3 qsenders 99).map (fun s => qHead s 0)) == some 2
#guard ((queueEnqueue qWorld 0 3 qsenders 99).map (fun s => qOccupancy s 0)) == some 2

-- (iv) OVERFLOW REJECTED: after one enqueue the queue is FULL; a SECOND enqueue is rejected (KEYSTONE a):
#guard (((queueEnqueue qWorld 0 3 qsenders 99).bind
          (fun s => queueEnqueue s 0 4 qsenders 88)).isSome) == false

-- (v) UNAUTHORIZED PUBLISH REJECTED: cell 5 (∉ senders) cannot enqueue (KEYSTONE c):
#guard ((queueEnqueue qWorld 0 5 qsenders 99).isSome) == false

-- (vi) a dequeue by the OWNER (cell 1) commits and advances tail 0→1 (occupancy 1→0):
#guard ((queueDequeue qWorld 0 1 55).isSome)
#guard ((queueDequeue qWorld 0 1 55).map (fun s => qTail s 0)) == some 1
#guard ((queueDequeue qWorld 0 1 55).map (fun s => qOccupancy s 0)) == some 0

-- (vii) UNDERFLOW REJECTED: dequeue the one message, then a SECOND dequeue on the EMPTY queue fails (KEYSTONE b):
#guard (((queueDequeue qWorld 0 1 55).bind (fun s => queueDequeue s 0 1 44)).isSome) == false

-- (viii) FIFO order (the kernel's real buffer): enqueue a then b, dequeue ⇒ a first (the OLDER):
#guard (qbufDequeue (qbufEnqueue (qbufEnqueue [] 10) 20)) == some (10, [20])

-- (ix) the factory conforms (its empty genesis is invariant-clean):
#guard ((queueFactory 2 1 qsenders).conforms)

-- (x) THE LIVE RELATIONAL GATE: an in-bound write (head 1→2 ≤ cap 2) COMMITS under the capacity caveat:
#guard ((relStateStepGuarded qrel qrelCap headSeqField 0 0 2).isSome)
#guard ((relStateStepGuarded qrel qrelCap headSeqField 0 0 2).map
          (fun s => fieldOf headSeqField (s.kernel.cell 0))) == some 2
-- ...and an OVER-BOUND write (head → 3 > cap 2) is REJECTED by the live relational gate (KEYSTONE a, in-executor):
#guard ((relStateStepGuarded qrel qrelCap headSeqField 0 0 3).isSome) == false

/-! ## §DELETION — the W2 deletion-readiness note (land-before-kill).

THIS module + the relational caveat are the LAND-BEFORE-KILL prerequisite for the queue verb
family. Once the factory is the live queue path (this module shipped + every queue app re-pointed),
W2 DELETES the 6-verb family:

  WHAT W2 DELETES (the queue side-table surface — `Dregg2.Exec.RecordKernel` / `…TurnExecutorFull`,
  and the Argus `QueueAllocate`/`Enqueue`/`Dequeue`/`Resize`/`AtomicTx`/`PipelineStep` effect welds):
    (1) the SIX kernel arms / chain ops / `FullActionA` arms:
          • QueueAllocate ↦ `createCellFromFactoryA` over `queueFactory` (the mint).
          • Enqueue       ↦ `setFieldA head_seq/message_root`, gated by MonotonicSequence +
            SenderAuthorized + the LIVE `RelCaveat.fieldLteOther` capacity bound.
          • Dequeue       ↦ `setFieldA tail_seq/message_root`, gated by MonotonicSequence + owner +
            the LIVE `RelCaveat.fieldLteOther` no-underflow bound.
          • Resize        ↦ a `setFieldA capacity` (NOT `Immutable` if resizable; per-factory choice;
            the relational gate RE-CHECKS the bound on the resized record).
          • AtomicTx      ↦ the forest/joint-turn layer (same as escrow's multi-cell settle).
          • PipelineStep  ↦ a sequence of enqueue/dequeue writes (no new mechanism).
    (2) the OFF-LEDGER `queues` side-table itself (the `queues : List QueueRecord` field on
        `RecordKernelState`) — DISSOLVED into the minted cell's own slots; the deposit value (if any)
        DISSOLVED into the cell's own `bal` column.
    (3) the `qbuf*` ON-LEDGER buffer accounting (`qbufEnqueue`/`qbufDequeue`/`qbuf_fifo_order` as a
        STATE mechanism) — RETAINED only as the authenticated FIFO-order SHADOW (the message_root
        commitment is the §8 crypto portal); the sequence counters become the cell-field truth.
    (4) any bespoke queue-occupancy / capacity measure and its accounting theory — COLLAPSED into the
        cross-slot relational caveat (the bound is now `RelCaveat.fieldLteOther`, enforced in-executor
        by `relStateStepGuarded`).

  WHAT MUST BE RE-POINTED FIRST (the land-before-kill blockers — every queue-verb consumer):
    • any `Dregg2.Apps.*` queue/mailbox/pipeline app on the queue verbs — re-point to `queueFactory`
      + the gated `setField` writes (same pattern as `BountyBoardGated` → `escrowFactoryEntry`).
    • the INBOX / PUBSUB twins (`Dregg2.Apps.InboxFactory` / `Dregg2.Apps.PubsubFactory`, this wave)
      SHARE the queue shape; they land as their own factories on the SAME relational caveat — no
      shared side-table to sequence, since each is its own minted cell.

  NOT DELETED HERE (land-before-kill): nothing above is removed in this commit — we only prove the
  factory is a faithful replacement and enumerate the burn-down. The verb deletion is the SUBSEQUENT
  W2 commit, gated on the re-points above all landing green AND the relational caveat being wired
  through `stateStepGuarded`/`caveatsAdmit` for every queue `SetField` (the RelationalCaveat
  §SOUNDNESS surface — `relStateStepGuarded` — supplies exactly this).
-/

#assert_axioms queueFactory_conforms
#assert_axioms relcav_expresses_capacity
#assert_axioms relcav_expresses_underflow
#assert_axioms fieldOf_setField_ne
#assert_axioms qWriteField_other
#assert_axioms qWriteField_same
#assert_axioms enqueue_reads
#assert_axioms enqueue_preserves_capacity
#assert_axioms full_queue_enqueue_rejected
#assert_axioms dequeue_reads
#assert_axioms dequeue_preserves_no_underflow
#assert_axioms empty_queue_dequeue_rejected
#assert_axioms enqueue_preserves_no_underflow
#assert_axioms fifo_order_holds
#assert_axioms enqueue_requires_sender_auth
#assert_axioms enqueue_matches_senderAuthorized_caveat
#assert_axioms queueDeposit_conserves
#assert_axioms enqueue_bal_neutral
#assert_axioms room_queue_enqueues
#assert_axioms nonempty_queue_dequeues
#assert_axioms mintQueueCell_installs_caveats
#assert_axioms mintQueueCell_caveats
#assert_axioms mintQueueCell_neutral
#assert_axioms mintQueueCell_grows_accounts
#assert_axioms mintQueueCell_unknown_factory_fails

end Dregg2.Apps.QueueFactory
