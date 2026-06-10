/-
# Dregg2.Apps.InboxFactory — W2: the value-less INBOX as a factory-born CELL PROGRAM.

THE CLAIM, DISCHARGED HERE (DREGG3 §6 R3 generalization, QueueFactoryProbe §VERDICT
"INBOX (CapInbox) = a queue whose messages are capability invocations; … no value ⇒ STRICTLY
EASIER (bal-neutral, no KEYSTONE d)"): *the inbox is the QUEUE shape MINUS the conservation
keystone — sequenced delivery (monotone head/tail), an owner-only dequeue, a sender-authorized
deposit, and the SAME cross-slot capacity / no-underflow bounds via the LIVE relational caveat
`RelCaveat.fieldLteOther` (`Dregg2.Exec.RelationalCaveat`).* Because an inbox carries NO value
(its messages are capability invocations / notifications, not asset moves), it never touches the
`bal` ledger — so it is the queue with KEYSTONE (d) DROPPED, the strictly-easier sibling the probe
predicted.

## The reframe (queue minus value)

An inbox in the verb world is an off-ledger mailbox + bookkeeping. The cell-program rebuild: the
inbox is a minted CELL whose head/tail/capacity/owner/sender_set/message_root are SLOTS governed by
the EXISTING `SlotCaveat` vocabulary (Immutable + MonotonicSequence + SenderAuthorized) PLUS the
LIVE `RelCaveat.fieldLteOther` cross-slot bounds. There is NO value column, NO deposit, NO
conservation keystone — every op is a pure field write, balance-NEUTRAL by construction.

## The inbox-factory SHAPE (the queue slots; NO value)

slots (fields on the inbox cell's record):
  * `head_seq`        — total messages DELIVERED (monotone ↑; advances by 1 on deliver).
  * `tail_seq`        — total messages CONSUMED (monotone ↑, ≤ head_seq; advances on consume).
  * `capacity`        — the max pending (immutable after open).
  * `owner`           — the inbox owner / consume authority (immutable).
  * `sender_set_root` — the deliver-authorization root.
  * `message_root`    — the ordered message commitment (advances on both ops).
(NO `bal` value: an inbox message is a capability invocation / notification, not an asset move.)

state_constraints:
  * `Immutable {capacity, owner}`                        — frozen.            [EXISTING SlotCaveat.]
  * `MonotonicSequence {head_seq, tail_seq}`             — sequenced delivery. [EXISTING.]
  * `SenderAuthorized {sender_set}`                       — the deliver gate.  [EXISTING.]
  * `RelCaveat.fieldLteOther head_seq capacity tail_seq` — CAPACITY: head − tail ≤ cap. [LIVE relational.]
  * `RelCaveat.fieldLteOther tail_seq head_seq 0`        — NO-UNDERFLOW: tail ≤ head.    [LIVE relational.]

## The three inbox-safety keystones (the queue's, MINUS conservation)

  (a) NO OVERFLOW — a deliver from a state respecting `head − tail ≤ cap`, with
      room, lands STILL respecting it; a FULL inbox's deliver fail-closes.
  (b) NO UNDERFLOW / SEQUENCED — `tail ≤ head` preserved; an EMPTY inbox's consume
      fail-closes; sequenced order is the factory FIFO shadow (`qbuf_fifo_order`).
  (c) SENDER-AUTH ON DELIVER — a deliver by an actor ∉ the sender set fail-closes;
      OWNER-ONLY CONSUME — a consume by a non-owner fail-closes.
  (NO KEYSTONE d: an inbox carries no value; `deliver_bal_neutral`/`consume_bal_neutral` witness
   that every op is balance-NEUTRAL — the strictly-easier sibling.)

## Non-vacuity

`inWorld` is a concrete inbox cell (capacity 2, owner 1, occupancy 1). `#guard` witnesses: an
over-capacity deliver (full inbox) is rejected; an underflow consume (empty inbox) is rejected; an
unauthorized deliver (actor ∉ senders) is rejected; a non-owner consume is rejected. No keystone
vacuous.

NEW file only. Imports the live relational caveat surface + the escrow factory executor. Does NOT
edit `Dregg2.lean`, any shared mod, the kernel, or any Metatheory/*. Every keystone
`#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}` — no sorry, no `:= True`,
no `native_decide`.
-/
import Dregg2.Exec.RelationalCaveat
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Apps.QueueFactory

namespace Dregg2.Apps.InboxFactory

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
-- F2b: the FIFO-order shadow lives with the queue-factory story (the kernel `qbuf*` is gone).
open Dregg2.Apps.QueueFactory (qbufEnqueue qbufDequeue qbuf_fifo_order)
open Dregg2.Exec.RelationalCaveat (RelCaveat relStateStepGuarded relCaveatsAdmit
  fieldLteOther_expresses_capacity fieldLteOther_expresses_underflow capacityOk noUnderflow)
open Dregg2.Exec.EffectsState (setField fieldOf setField_fieldOf)

/-! ## §1 — The inbox-cell SLOT layout (field names). -/

/-- Total messages DELIVERED (monotone ↑; advances by 1 on deliver). -/
abbrev headSeqField : FieldName := "inbox.head_seq"
/-- Total messages CONSUMED (monotone ↑, ≤ head_seq; advances by 1 on consume). -/
abbrev tailSeqField : FieldName := "inbox.tail_seq"
/-- The max pending (frozen after open). -/
abbrev capacityField : FieldName := "inbox.capacity"
/-- The inbox owner / consume authority (frozen). -/
abbrev ownerField : FieldName := "inbox.owner"
/-- The deliver-authorization root (the authorized-sender membership). -/
abbrev senderSetField : FieldName := "inbox.sender_set_root"
/-- The ordered message commitment (advances on deliver and consume). -/
abbrev messageRootField : FieldName := "inbox.message_root"

/-! ## §2 — The inbox FACTORY DESCRIPTOR + the RELATIONAL cross-slot bounds. -/

/-- **`inboxFactory cap owner senders` — the inbox factory's `SlotCaveat` half.** The deal-term
immutables (`capacity`, `owner`), the monotone sequence counters, and the sender-authorization gate
on the deliver. Initial state: an EMPTY inbox (`head = tail = 0`). The cross-slot bounds live in
`inboxRelCaveats`. NO value column. -/
def inboxFactory (cap owner : Int) (senders : List CellId) : FactoryEntry where
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

/-- **`inboxRelCaveats postTail` — the CROSS-SLOT bounds as LIVE relational caveats.** The capacity
bound `head ≤ cap + tail` and the no-underflow bound `tail ≤ head`. -/
def inboxRelCaveats (postTail : Int) : List RelCaveat :=
  [ RelCaveat.fieldLteOther headSeqField capacityField postTail
  , RelCaveat.fieldLteOther tailSeqField headSeqField 0 ]

/-- **`inboxFactory_conforms`.** The inbox factory's OWN published EMPTY initial state
satisfies its OWN `SlotCaveat`s. -/
theorem inboxFactory_conforms (cap owner : Int) (senders : List CellId) :
    (inboxFactory cap owner senders).conforms = true := by
  unfold inboxFactory FactoryEntry.conforms FactoryEntry.initialFieldsNoBalance
  simp only [SlotCaveat.field, SlotCaveat.bornFresh, List.all_cons, List.all_nil,
    List.find?, Bool.and_true, Bool.and_self]
  rfl

/-! ## §3 — The inbox cell STATE: reading the slots. -/

/-- Read the inbox's head sequence (total delivered). -/
def iHead (k : RecordKernelState) (e : CellId) : Int := fieldOf headSeqField (k.cell e)
/-- Read the inbox's tail sequence (total consumed). -/
def iTail (k : RecordKernelState) (e : CellId) : Int := fieldOf tailSeqField (k.cell e)
/-- Read the inbox's capacity. -/
def iCap (k : RecordKernelState) (e : CellId) : Int := fieldOf capacityField (k.cell e)

/-- The current PENDING count: messages delivered but not yet consumed. -/
def iPending (k : RecordKernelState) (e : CellId) : Int := iHead k e - iTail k e

/-- The inbox is EMPTY iff pending is 0 (head = tail). -/
def iEmpty (k : RecordKernelState) (e : CellId) : Prop := iHead k e = iTail k e

/-- **The capacity invariant**: pending never exceeds capacity. -/
def iCapacityOk (k : RecordKernelState) (e : CellId) : Prop := iPending k e ≤ iCap k e

/-- **The no-underflow invariant**: tail never overtakes head (sequenced; can't consume past delivered). -/
def iNoUnderflow (k : RecordKernelState) (e : CellId) : Prop := iTail k e ≤ iHead k e

/-! ## §3b — The LIVE relational caveat EXPRESSES the bounds (instantiated from RelationalCaveat). -/

/-- **`relcav_expresses_capacity` (instantiated).** The live capacity atom on the inbox
cell's record is EXACTLY the capacity invariant `head − tail ≤ cap`. -/
theorem relcav_expresses_capacity (k : RecordKernelState) (e : CellId) :
    (RelCaveat.fieldLteOther headSeqField capacityField (iTail k e)).eval (k.cell e) = true
      ↔ iCapacityOk k e := by
  have h := fieldLteOther_expresses_capacity (k.cell e) headSeqField tailSeqField capacityField
  unfold iCapacityOk iPending iHead iTail iCap
  unfold capacityOk at h
  exact h

/-- **`relcav_expresses_underflow` (instantiated).** The live no-underflow atom is EXACTLY
`tail ≤ head`. -/
theorem relcav_expresses_underflow (k : RecordKernelState) (e : CellId) :
    (RelCaveat.fieldLteOther tailSeqField headSeqField 0).eval (k.cell e) = true
      ↔ iNoUnderflow k e := by
  have h := fieldLteOther_expresses_underflow (k.cell e) headSeqField tailSeqField
  unfold iNoUnderflow iTail iHead
  unfold noUnderflow at h
  exact h

/-! ## §4 — The inbox OPERATIONS (deliver / consume) as gated field writes (NO value move). -/

/-- Write a single scalar field of the inbox cell. -/
def iWriteField (k : RecordKernelState) (e : CellId) (f : FieldName) (v : Int) : RecordKernelState :=
  { k with cell := fun c => if c = e then setField f (k.cell e) (.int v) else k.cell c }

/-- **`inboxDeliver` — advance head (deliver a message), gated on sender-auth AND capacity.**
Rejects when the actor ∉ `senders` OR the inbox is full (`iPending k e ≥ iCap k e`). On success:
`head_seq` is incremented by 1 and `message_root` is updated. NO value move (bal-neutral). -/
def inboxDeliver (k : RecordKernelState) (e actor : CellId) (senders : List CellId)
    (newRoot : Int) : Option RecordKernelState :=
  if senders.contains actor ∧ iPending k e < iCap k e then
    some (iWriteField (iWriteField k e headSeqField (iHead k e + 1)) e messageRootField newRoot)
  else none

/-- **`inboxConsume` — advance tail (consume a message), gated on OWNER AND non-empty.** Rejects
when the actor is not the owner OR the inbox is EMPTY. On success: `tail_seq` is incremented by 1
and `message_root` is updated. NO value move (bal-neutral). -/
def inboxConsume (k : RecordKernelState) (e actor : CellId) (newRoot : Int) : Option RecordKernelState :=
  if actor = fieldOf ownerField (k.cell e) ∧ 0 < iPending k e then
    some (iWriteField (iWriteField k e tailSeqField (iTail k e + 1)) e messageRootField newRoot)
  else none

/-! ### Read-back lemmas. -/

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
  | int n => simp [setField, List.find?, hfg']
  | dig d => simp [setField, List.find?, hfg']
  | sym s => simp [setField, List.find?, hfg']

/-- Writing field `f` to inbox cell `e` and reading field `g ≠ f` of `e` is unchanged. -/
theorem iWriteField_other (k : RecordKernelState) (e : CellId) (f g : FieldName) (v : Int)
    (hfg : g ≠ f) : fieldOf g ((iWriteField k e f v).cell e) = fieldOf g (k.cell e) := by
  unfold iWriteField
  simp only [if_pos rfl]
  exact fieldOf_setField_ne f g (k.cell e) v hfg

/-- Reading field `f` right after writing `f := v` to the same cell returns `v`. -/
theorem iWriteField_same (k : RecordKernelState) (e : CellId) (f : FieldName) (v : Int) :
    fieldOf f ((iWriteField k e f v).cell e) = v := by
  unfold iWriteField; simp only [if_pos rfl]; exact setField_fieldOf f (k.cell e) v

/-! ## §5 — KEYSTONE (a): NO OVERFLOW (the capacity bound is PRESERVED by deliver). -/

/-- The capacity/tail/head read-back across a deliver. -/
theorem deliver_reads {k k' : RecordKernelState} {e actor : CellId} {senders : List CellId}
    {newRoot : Int} (h : inboxDeliver k e actor senders newRoot = some k') :
    iHead k' e = iHead k e + 1 ∧ iTail k' e = iTail k e ∧ iCap k' e = iCap k e := by
  unfold inboxDeliver at h
  by_cases hg : senders.contains actor ∧ iPending k e < iCap k e
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h; subst h
    refine ⟨?_, ?_, ?_⟩
    · unfold iHead
      rw [iWriteField_other _ e messageRootField headSeqField newRoot (by decide)]
      exact iWriteField_same k e headSeqField (iHead k e + 1)
    · unfold iTail
      rw [iWriteField_other _ e messageRootField tailSeqField newRoot (by decide),
          iWriteField_other _ e headSeqField tailSeqField (iHead k e + 1) (by decide)]
    · unfold iCap
      rw [iWriteField_other _ e messageRootField capacityField newRoot (by decide),
          iWriteField_other _ e headSeqField capacityField (iHead k e + 1) (by decide)]
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`deliver_preserves_capacity` — KEYSTONE (a), PROVED.** From `pending ≤ cap`, a committed
deliver lands in `pending ≤ cap` STILL — the cross-slot capacity bound enforced by the relational
atom. -/
theorem deliver_preserves_capacity {k k' : RecordKernelState} {e actor : CellId}
    {senders : List CellId} {newRoot : Int}
    (h : inboxDeliver k e actor senders newRoot = some k') (hpre : iCapacityOk k e) :
    iCapacityOk k' e := by
  have hguard : iPending k e < iCap k e := by
    unfold inboxDeliver at h
    by_cases hg : senders.contains actor ∧ iPending k e < iCap k e
    · exact hg.2
    · rw [if_neg hg] at h; exact absurd h (by simp)
  obtain ⟨hh, ht, hc⟩ := deliver_reads h
  unfold iCapacityOk iPending at *
  rw [hh, ht, hc]; omega

/-- **`full_inbox_deliver_rejected` — KEYSTONE (a), the fail-closed half, PROVED.** A FULL inbox
(`pending ≥ cap`) rejects every deliver. -/
theorem full_inbox_deliver_rejected (k : RecordKernelState) (e actor : CellId)
    (senders : List CellId) (newRoot : Int) (hfull : iCap k e ≤ iPending k e) :
    inboxDeliver k e actor senders newRoot = none := by
  unfold inboxDeliver
  rw [if_neg (by rintro ⟨_, hlt⟩; omega)]

/-! ## §6 — KEYSTONE (b): NO UNDERFLOW / SEQUENCED DELIVERY. -/

/-- The head/tail read-back across a consume. -/
theorem consume_reads {k k' : RecordKernelState} {e actor : CellId} {newRoot : Int}
    (h : inboxConsume k e actor newRoot = some k') :
    iTail k' e = iTail k e + 1 ∧ iHead k' e = iHead k e := by
  unfold inboxConsume at h
  by_cases hg : actor = fieldOf ownerField (k.cell e) ∧ 0 < iPending k e
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h; subst h
    refine ⟨?_, ?_⟩
    · unfold iTail
      rw [iWriteField_other _ e messageRootField tailSeqField newRoot (by decide)]
      exact iWriteField_same k e tailSeqField (iTail k e + 1)
    · unfold iHead
      rw [iWriteField_other _ e messageRootField headSeqField newRoot (by decide),
          iWriteField_other _ e tailSeqField headSeqField (iTail k e + 1) (by decide)]
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`consume_preserves_no_underflow` — KEYSTONE (b), PROVED.** From `tail ≤ head`, a committed
consume (fires only when non-empty) lands in `tail ≤ head` STILL. -/
theorem consume_preserves_no_underflow {k k' : RecordKernelState} {e actor : CellId} {newRoot : Int}
    (h : inboxConsume k e actor newRoot = some k') (hpre : iNoUnderflow k e) :
    iNoUnderflow k' e := by
  have hguard : 0 < iPending k e := by
    unfold inboxConsume at h
    by_cases hg : actor = fieldOf ownerField (k.cell e) ∧ 0 < iPending k e
    · exact hg.2
    · rw [if_neg hg] at h; exact absurd h (by simp)
  obtain ⟨ht, hh⟩ := consume_reads h
  unfold iNoUnderflow at *
  unfold iPending at hguard
  rw [ht, hh]; omega

/-- **`empty_inbox_consume_rejected` — KEYSTONE (b), the fail-closed half, PROVED.** An EMPTY inbox
rejects every consume. -/
theorem empty_inbox_consume_rejected (k : RecordKernelState) (e actor : CellId) (newRoot : Int)
    (hempty : iEmpty k e) :
    inboxConsume k e actor newRoot = none := by
  unfold inboxConsume
  have hz : iPending k e = 0 := by unfold iPending iEmpty at *; omega
  rw [if_neg (by rintro ⟨_, hpos⟩; rw [hz] at hpos; exact absurd hpos (by decide))]

/-- **`deliver_preserves_no_underflow` — KEYSTONE (b) cross-op, PROVED.** Deliver (advances head)
also preserves `tail ≤ head`. -/
theorem deliver_preserves_no_underflow {k k' : RecordKernelState} {e actor : CellId}
    {senders : List CellId} {newRoot : Int}
    (h : inboxDeliver k e actor senders newRoot = some k') (hpre : iNoUnderflow k e) :
    iNoUnderflow k' e := by
  obtain ⟨hh, ht, _⟩ := deliver_reads h
  unfold iNoUnderflow at *
  rw [hh, ht]; omega

/-- **SEQUENCED ORDER — carried from the factory FIFO shadow (`Apps.QueueFactory.qbuf_fifo_order`;
F2b moved it there from the deleted kernel buffer).** -/
theorem sequenced_order_holds (buf : List Nat) (a b : Nat) :
    qbufDequeue (qbufEnqueue (qbufEnqueue buf a) b) =
      (match qbufDequeue buf with
       | some (h, rest) => some (h, qbufEnqueue (qbufEnqueue rest a) b)
       | none           => some (a, [b])) :=
  qbuf_fifo_order buf a b

/-! ## §7 — KEYSTONE (c): SENDER-AUTH ON DELIVER + OWNER-ONLY CONSUME. -/

/-- **`deliver_requires_sender_auth` — KEYSTONE (c), deliver side, PROVED.** A deliver by an actor
NOT in the authorized sender set is REJECTED. -/
theorem deliver_requires_sender_auth (k : RecordKernelState) (e actor : CellId)
    (senders : List CellId) (newRoot : Int) (hbad : senders.contains actor = false) :
    inboxDeliver k e actor senders newRoot = none := by
  unfold inboxDeliver
  rw [if_neg (by rintro ⟨hin, _⟩; rw [hbad] at hin; exact absurd hin (by simp))]

/-- **`deliver_matches_senderAuthorized_caveat` — the gate IS the `SenderAuthorized` atom, PROVED.** -/
theorem deliver_matches_senderAuthorized_caveat (actor : CellId) (senders : List CellId)
    (old new : Int) :
    (SlotCaveat.senderAuthorized senderSetField senders).eval actor old new
      = senders.contains actor := rfl

/-- **`consume_requires_owner` — KEYSTONE (c), consume side, PROVED.** A consume by an actor whose
cast ≠ the cell's frozen `owner` slot is REJECTED — only the owner can consume. -/
theorem consume_requires_owner (k : RecordKernelState) (e actor : CellId) (newRoot : Int)
    (hbad : (actor : Int) ≠ fieldOf ownerField (k.cell e)) :
    inboxConsume k e actor newRoot = none := by
  unfold inboxConsume
  rw [if_neg (by rintro ⟨ho, _⟩; exact hbad ho)]

/-! ## §8 — BALANCE-NEUTRALITY (the strictly-easier sibling: NO value move, NO KEYSTONE d). -/

/-- **`deliver_bal_neutral`.** An inbox deliver is a pure field write — every asset's total
supply is unchanged. (An inbox carries NO value; this is why it drops the queue's conservation
keystone.) -/
theorem deliver_bal_neutral {k k' : RecordKernelState} {e actor : CellId} {senders : List CellId}
    {newRoot : Int} (h : inboxDeliver k e actor senders newRoot = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold inboxDeliver at h
  by_cases hg : senders.contains actor ∧ iPending k e < iCap k e
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h; subst h
    unfold recTotalAsset iWriteField; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`consume_bal_neutral`.** An inbox consume is a pure field write — balance-NEUTRAL. -/
theorem consume_bal_neutral {k k' : RecordKernelState} {e actor : CellId} {newRoot : Int}
    (h : inboxConsume k e actor newRoot = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold inboxConsume at h
  by_cases hg : actor = fieldOf ownerField (k.cell e) ∧ 0 < iPending k e
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h; subst h
    unfold recTotalAsset iWriteField; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §9 — LIVENESS: an inbox with room/messages can deliver/consume. -/

/-- **`room_inbox_delivers` — an authorized sender CAN deliver when there is room.** -/
theorem room_inbox_delivers (k : RecordKernelState) (e actor : CellId) (senders : List CellId)
    (newRoot : Int) (hauth : senders.contains actor = true) (hroom : iPending k e < iCap k e) :
    (inboxDeliver k e actor senders newRoot).isSome := by
  unfold inboxDeliver; rw [if_pos ⟨hauth, hroom⟩]; exact Option.isSome_some

/-- **`nonempty_inbox_consumes` — the owner CAN consume when the inbox is non-empty.** -/
theorem nonempty_inbox_consumes (k : RecordKernelState) (e actor : CellId) (newRoot : Int)
    (howner : (actor : Int) = fieldOf ownerField (k.cell e)) (hne : 0 < iPending k e) :
    (inboxConsume k e actor newRoot).isSome := by
  unfold inboxConsume; rw [if_pos ⟨howner, hne⟩]; exact Option.isSome_some

/-! ## §10 — MINTING the inbox cell through the REAL factory executor. -/

/-- A kernel factory registry publishing the inbox factory at content-addressed key `vk`. -/
def inboxRegistry (vk : Nat) (cap owner : Int) (senders : List CellId) :
    List (Nat × FactoryEntry) :=
  [(vk, inboxFactory cap owner senders)]

/-- The registry resolves the inbox factory at exactly its published key. -/
theorem inboxRegistry_finds (vk : Nat) (cap owner : Int) (senders : List CellId) :
    findFactory (inboxRegistry vk cap owner senders) vk
      = some (inboxFactory cap owner senders) := by
  simp [inboxRegistry, findFactory]

/-- Mint an inbox cell from the inbox factory at key `vk` (the real factory executor). -/
def mintInboxCell (s : RecChainedState) (actor iCell : CellId) (vk : Int) :
    Option RecChainedState :=
  createCellFromFactoryChainA s actor iCell vk

/-- **`mintInboxCell_installs_caveats`.** A minted inbox cell carries EXACTLY the factory's
caveats, installed by the executor. -/
theorem mintInboxCell_installs_caveats {s s' : RecChainedState} {actor iCell : CellId}
    {vk : Int} (e : FactoryEntry)
    (hreg : findFactory s.kernel.factories vk.toNat = some e)
    (h : mintInboxCell s actor iCell vk = some s') :
    s'.kernel.slotCaveats iCell = e.caveats := by
  obtain ⟨e', hfind, hcav⟩ := createCellFromFactoryChainA_installs_program h
  rw [hreg] at hfind
  rw [← (Option.some.injEq _ _).mp hfind] at hcav
  exact hcav

/-- **`mintInboxCell_caveats`.** When the registry IS `inboxRegistry vk …`, the minted cell
concretely carries the inbox factory's caveats. -/
theorem mintInboxCell_caveats {s s' : RecChainedState} {actor iCell : CellId} {vk : Int}
    {cap owner : Int} {senders : List CellId}
    (hreg : s.kernel.factories = inboxRegistry vk.toNat cap owner senders)
    (h : mintInboxCell s actor iCell vk = some s') :
    s'.kernel.slotCaveats iCell = (inboxFactory cap owner senders).caveats := by
  have hfind : findFactory s.kernel.factories vk.toNat = some (inboxFactory cap owner senders) := by
    rw [hreg]; exact inboxRegistry_finds vk.toNat cap owner senders
  exact mintInboxCell_installs_caveats _ hfind h

/-- **`mintInboxCell_neutral`.** Minting an inbox cell is conservation-NEUTRAL for every
asset. -/
theorem mintInboxCell_neutral {s s' : RecChainedState} {actor iCell : CellId} {vk : Int}
    (b : AssetId) (h : mintInboxCell s actor iCell vk = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  createCellFromFactoryChainA_neutral b h

/-- **`mintInboxCell_grows_accounts`.** A minted inbox cell IS a live account. -/
theorem mintInboxCell_grows_accounts {s s' : RecChainedState} {actor iCell : CellId} {vk : Int}
    (h : mintInboxCell s actor iCell vk = some s') :
    iCell ∈ s'.kernel.accounts :=
  createCellFromFactoryChainA_grows_accounts h

/-- **`mintInboxCell_unknown_factory_fails` (fail-closed).** Minting against an unknown
factory key never mints. -/
theorem mintInboxCell_unknown_factory_fails (s : RecChainedState) (actor iCell : CellId)
    (vk : Int) (h : findFactory s.kernel.factories vk.toNat = none) :
    mintInboxCell s actor iCell vk = none :=
  createCellFromFactoryChainA_unknown_factory_fails s actor iCell vk h

/-! ## §11 — NON-VACUITY: a concrete inbox world + `#guard` witnesses (incl. the LIVE relational gate). -/

/-- An inbox world. The INBOX CELL is cell `0`: capacity 2, owner 1, head_seq 1, tail_seq 0 (so
PENDING 1, room for one more), sender_set_root 0, message_root 7. Authorized senders `[3, 4]`; cell
5 UNAUTHORIZED. All cells {0,1,3,4,5} live. NO value column. -/
def inWorld : RecordKernelState :=
  { accounts := {0, 1, 3, 4, 5}
    cell := fun c =>
      if c = 0 then .record
        [ (headSeqField, .int 1), (tailSeqField, .int 0), (capacityField, .int 2)
        , (ownerField, .int 1), (senderSetField, .int 0), (messageRootField, .int 7) ]
      else .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun _ _ => 0 }

abbrev isenders : List CellId := [3, 4]

/-- A chained world for the LIVE relational gate witnesses. -/
def inrel : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then .record [("balance", .int 0), (headSeqField, .int 1),
                                                (tailSeqField, .int 0), (capacityField, .int 2)]
                         else .record [("balance", .int 0)]
        caps := fun _ => [] }
    log := [] }

/-- The capacity relational caveat for cell 0 (`head ≤ cap`). -/
abbrev inrelCap : List RelCaveat := [ RelCaveat.fieldLteOther headSeqField capacityField 0 ]

-- (i) the inbox reads: pending 1, capacity 2, room for one more:
#guard (iHead inWorld 0 == 1)
#guard (iTail inWorld 0 == 0)
#guard (iPending inWorld 0 == 1)
#guard (iCap inWorld 0 == 2)

-- (ii) the LIVE relational atom EXPRESSES the capacity + underflow bounds:
#guard ((RelCaveat.fieldLteOther headSeqField capacityField (iTail inWorld 0)).eval (inWorld.cell 0))
#guard ((RelCaveat.fieldLteOther tailSeqField headSeqField 0).eval (inWorld.cell 0))

-- (iii) an authorized deliver (sender 3) with room COMMITS and advances head 1→2 (now FULL):
#guard ((inboxDeliver inWorld 0 3 isenders 99).isSome)
#guard ((inboxDeliver inWorld 0 3 isenders 99).map (fun s => iHead s 0)) == some 2
#guard ((inboxDeliver inWorld 0 3 isenders 99).map (fun s => iPending s 0)) == some 2

-- (iv) OVERFLOW REJECTED: a SECOND deliver on the now-FULL inbox fails (KEYSTONE a):
#guard (((inboxDeliver inWorld 0 3 isenders 99).bind
          (fun s => inboxDeliver s 0 4 isenders 88)).isSome) == false

-- (v) UNAUTHORIZED DELIVER REJECTED: cell 5 (∉ senders) cannot deliver (KEYSTONE c):
#guard ((inboxDeliver inWorld 0 5 isenders 99).isSome) == false

-- (vi) a consume by the OWNER (cell 1) commits and advances tail 0→1 (pending 1→0):
#guard ((inboxConsume inWorld 0 1 55).isSome)
#guard ((inboxConsume inWorld 0 1 55).map (fun s => iTail s 0)) == some 1
#guard ((inboxConsume inWorld 0 1 55).map (fun s => iPending s 0)) == some 0

-- (vii) NON-OWNER CONSUME REJECTED: cell 3 (≠ owner 1) cannot consume (KEYSTONE c, consume side):
#guard ((inboxConsume inWorld 0 3 55).isSome) == false

-- (viii) UNDERFLOW REJECTED: consume the one message, then a SECOND consume on the EMPTY inbox fails (KEYSTONE b):
#guard (((inboxConsume inWorld 0 1 55).bind (fun s => inboxConsume s 0 1 44)).isSome) == false

-- (ix) sequenced order (the factory FIFO shadow): deliver a then b, consume ⇒ a first (the OLDER):
#guard (qbufDequeue (qbufEnqueue (qbufEnqueue [] 10) 20)) == some (10, [20])

-- (x) the factory conforms (its empty genesis is invariant-clean):
#guard ((inboxFactory 2 1 isenders).conforms)

-- (xi) THE LIVE RELATIONAL GATE: an in-bound deliver write (head 1→2 ≤ cap 2) COMMITS:
#guard ((relStateStepGuarded inrel inrelCap headSeqField 0 0 2).isSome)
-- ...and an OVER-BOUND write (head → 3 > cap 2) is REJECTED by the live relational gate:
#guard ((relStateStepGuarded inrel inrelCap headSeqField 0 0 3).isSome) == false

/-! ## §DELETION — the W2 deletion-readiness note (land-before-kill).

THIS module + the relational caveat are the LAND-BEFORE-KILL prerequisite for the inbox/mailbox
verb family. Once the factory is the live inbox path (this module shipped + every inbox app
re-pointed), W2 DELETES:

  WHAT W2 DELETES (the inbox side-table surface — and the Argus inbox/mailbox effect welds):
    (1) the inbox/mailbox kernel arms / chain ops / `FullActionA` arms (deliver/consume/allocate):
          • InboxAllocate ↦ `createCellFromFactoryA` over `inboxFactory` (the mint).
          • Deliver       ↦ `setFieldA head_seq/message_root`, gated by MonotonicSequence +
            SenderAuthorized + the LIVE `RelCaveat.fieldLteOther` capacity bound.
          • Consume       ↦ `setFieldA tail_seq/message_root`, gated by MonotonicSequence + owner +
            the LIVE `RelCaveat.fieldLteOther` no-underflow bound.
    (2) the OFF-LEDGER inbox/mailbox side-table (the `inboxes`/`CapInbox` field on
        `RecordKernelState`) — DISSOLVED into the minted cell's own slots. (NO value column to
        dissolve — the inbox is bal-neutral by construction, the strictly-easier sibling.)
    (3) the inbox order accounting (`qbuf*` as a STATE mechanism) — RETAINED only as the
        authenticated SEQUENCED-order shadow (message_root = §8 crypto portal).

  WHAT MUST BE RE-POINTED FIRST (the land-before-kill blockers — every inbox-verb consumer):
    • any `Dregg2.Apps.*` mailbox / notification / cap-inbox app on the inbox verbs — re-point to
      `inboxFactory` + the gated `setField` writes (same pattern as `BountyBoardGated`).
    • shares NO side-table with queue/pubsub (each is its own minted cell), so there is no shared
      field to sequence — the deletions are independent per family.

  NOT DELETED HERE (land-before-kill): nothing above is removed in this commit. The verb deletion is
  the SUBSEQUENT W2 commit, gated on the re-points landing green AND the relational caveat wired
  through `stateStepGuarded`/`caveatsAdmit` for every inbox `SetField` (RelationalCaveat
  `relStateStepGuarded` supplies exactly this).
-/

#assert_axioms inboxFactory_conforms
#assert_axioms relcav_expresses_capacity
#assert_axioms relcav_expresses_underflow
#assert_axioms fieldOf_setField_ne
#assert_axioms iWriteField_other
#assert_axioms iWriteField_same
#assert_axioms deliver_reads
#assert_axioms deliver_preserves_capacity
#assert_axioms full_inbox_deliver_rejected
#assert_axioms consume_reads
#assert_axioms consume_preserves_no_underflow
#assert_axioms empty_inbox_consume_rejected
#assert_axioms deliver_preserves_no_underflow
#assert_axioms sequenced_order_holds
#assert_axioms deliver_requires_sender_auth
#assert_axioms deliver_matches_senderAuthorized_caveat
#assert_axioms consume_requires_owner
#assert_axioms deliver_bal_neutral
#assert_axioms consume_bal_neutral
#assert_axioms room_inbox_delivers
#assert_axioms nonempty_inbox_consumes
#assert_axioms mintInboxCell_installs_caveats
#assert_axioms mintInboxCell_caveats
#assert_axioms mintInboxCell_neutral
#assert_axioms mintInboxCell_grows_accounts
#assert_axioms mintInboxCell_unknown_factory_fails

end Dregg2.Apps.InboxFactory
