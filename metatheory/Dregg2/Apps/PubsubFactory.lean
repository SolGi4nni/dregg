/-
# Dregg2.Apps.PubsubFactory — W2: PUBSUB as a factory-born CELL PROGRAM (per-subscriber cursor).

THE CLAIM, DISCHARGED HERE (DREGG3 §6 R3 generalization, QueueFactoryProbe §VERDICT
"PUBSUB = a queue with MANY readers (each reader carries its OWN tail_seq slot vs a shared
head_seq); the `FieldLteOther` per-reader `reader_tail ≤ head` is the SAME cross-slot atom,
instantiated per subscriber"): *pubsub is the QUEUE shape with ONE shared `head_seq` (the publish
log) and a SEPARATE cursor slot per subscriber, each bounded `reader_cursor ≤ head` by the SAME
live relational caveat `RelCaveat.fieldLteOther` (`Dregg2.Exec.RelationalCaveat`), instantiated
per reader; publishing is publisher-authorized append.* The shared head replaces the queue's single
tail with N independent cursors — but each cursor's bound is the identical cross-slot atom the
relational caveat already supplies. No new primitive; just the same atom, per subscriber.

## The reframe (one shared log, N independent cursors)

A pubsub topic in the verb world is an off-ledger log + per-subscriber offset bookkeeping. The
cell-program rebuild: the topic is a minted CELL whose `head_seq` (the published count) is a single
shared monotone slot, and each subscriber `r` carries its OWN `reader_cursor[r]` slot. A PUBLISH
advances the shared `head_seq` (publisher-authorized append); a READ advances ONE subscriber's
cursor toward `head` (the subscriber-only advance). Each cursor is bounded `cursor[r] ≤ head` by the
LIVE `RelCaveat.fieldLteOther reader_cursor[r] head 0` — the SAME no-underflow atom, instantiated
per reader. Pubsub is bal-NEUTRAL (notifications, not value), like the inbox.

## The pubsub-factory SHAPE (shared head + per-reader cursors)

slots (fields on the topic cell's record):
  * `head_seq`              — total messages PUBLISHED (shared; monotone ↑; advances on publish).
  * `reader_cursor.<r>`     — subscriber `r`'s read offset (monotone ↑, ≤ head_seq; advances on read).
  * `publisher`             — the publish authority (immutable).
  * `message_root`          — the ordered log commitment (advances on publish).
(NO `bal` value: a pubsub message is a notification, not an asset move — bal-neutral like inbox.)

state_constraints:
  * `Immutable {publisher}`                              — frozen publish authority. [EXISTING SlotCaveat.]
  * `MonotonicSequence {head_seq}` + per reader `MonotonicSequence {reader_cursor.<r>}` — monotone. [EXISTING.]
  * per reader `RelCaveat.fieldLteOther reader_cursor.<r> head_seq 0` — `cursor[r] ≤ head`. [LIVE relational, per reader.]

## The three pubsub-safety keystones

  (a) NO READ-AHEAD — a read advances `cursor[r]` toward `head` only when
      `cursor[r] < head` (a message is available); from `cursor[r] ≤ head` it lands STILL
      `cursor[r] ≤ head`; a CAUGHT-UP reader (`cursor[r] = head`) fail-closes (cannot read past the
      published frontier). THIS is the per-reader instantiation of the relational `fieldLteOther`.
  (b) PUBLISHER-AUTHORIZED APPEND — a publish by a non-publisher fail-closes; the publisher
      append advances the shared `head_seq` by 1.
  (c) READER ISOLATION — advancing reader `r`'s cursor leaves `head_seq` AND every
      OTHER reader's cursor unchanged (one subscriber's progress never moves another's, nor the log).

## Non-vacuity

`psWorld` is a concrete topic (publisher 9, head_seq 2; reader 3 cursor 1, reader 4 cursor 2 =
caught up). `#guard` witnesses: an unauthorized publish (actor ≠ publisher) is rejected; a
caught-up reader's read (reader 4, cursor = head) is rejected (no read-ahead); reader 3's read
commits and advances ONLY reader 3's cursor (reader 4 + head untouched). No keystone vacuous.

NEW file only. Imports the live relational caveat surface + the escrow factory executor. Does NOT
edit `Dregg2.lean`, any shared mod, the kernel, or any Metatheory/*. Every keystone
`#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}` — no sorry, no `:= True`,
no `native_decide`.
-/
import Dregg2.Exec.RelationalCaveat
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Apps.PubsubFactory

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.RelationalCaveat (RelCaveat relStateStepGuarded relCaveatsAdmit
  fieldLteOther_expresses_underflow noUnderflow)
open Dregg2.Exec.EffectsState (setField fieldOf setField_fieldOf)

/-! ## §1 — The topic-cell SLOT layout (field names). The shared head + per-reader cursors. -/

/-- Total messages PUBLISHED (shared; monotone ↑; advances by 1 on publish). -/
abbrev headSeqField : FieldName := "pubsub.head_seq"
/-- The publish authority (frozen). -/
abbrev publisherField : FieldName := "pubsub.publisher"
/-- The ordered log commitment (advances on publish). -/
abbrev messageRootField : FieldName := "pubsub.message_root"

/-- **Subscriber `r`'s read-cursor field name** — `"pubsub.reader_cursor.<r>"`. Each subscriber
carries its OWN cursor slot, bounded `cursor[r] ≤ head` by the per-reader relational caveat. -/
def readerCursorField (r : CellId) : FieldName := "pubsub.reader_cursor." ++ toString (r : Nat)

/-! ## §2 — The pubsub FACTORY DESCRIPTOR + the per-reader RELATIONAL bounds. -/

/-- **`pubsubFactory publisher` — the pubsub topic factory's `SlotCaveat` half.** The frozen
publisher authority + the monotone shared `head_seq`. (Per-reader cursor monotone caveats are
installed per subscription — a reader's cursor slot is created on subscribe.) Initial state: an
EMPTY topic (`head = 0`). The per-reader cross-slot bounds live in `readerRelCaveat`. -/
def pubsubFactory (publisher : Int) : FactoryEntry where
  caveats :=
    [ SlotCaveat.immutable publisherField
    , SlotCaveat.monotonicSeq headSeqField ]
  initialFields :=
    [ (headSeqField, 0)
    , (publisherField, publisher)
    , (messageRootField, 0) ]
  programVk := 0

/-- **`readerRelCaveat r` — subscriber `r`'s cross-slot bound as a LIVE relational caveat.** The
no-read-ahead bound `cursor[r] ≤ head` — the SAME `RelCaveat.fieldLteOther` atom the queue's
no-underflow uses, instantiated for reader `r`. -/
def readerRelCaveat (r : CellId) : RelCaveat :=
  RelCaveat.fieldLteOther (readerCursorField r) headSeqField 0

/-- **`pubsubFactory_conforms`.** The topic factory's OWN published EMPTY initial state
satisfies its OWN `SlotCaveat`s. -/
theorem pubsubFactory_conforms (publisher : Int) :
    (pubsubFactory publisher).conforms = true := by
  unfold pubsubFactory FactoryEntry.conforms FactoryEntry.initialFieldsNoBalance
  simp only [SlotCaveat.field, SlotCaveat.bornFresh, List.all_cons, List.all_nil,
    List.find?, Bool.and_true, Bool.and_self]
  rfl

/-! ## §3 — The topic cell STATE: reading the shared head + per-reader cursors. -/

/-- Read the topic's shared head sequence (total published). -/
def psHead (k : RecordKernelState) (e : CellId) : Int := fieldOf headSeqField (k.cell e)

/-- Read subscriber `r`'s cursor on topic `e`. -/
def psCursor (k : RecordKernelState) (e r : CellId) : Int := fieldOf (readerCursorField r) (k.cell e)

/-- Read the topic's frozen publisher slot. -/
def psPublisher (k : RecordKernelState) (e : CellId) : Int := fieldOf publisherField (k.cell e)

/-- **The no-read-ahead invariant for reader `r`**: its cursor never overtakes the published head. -/
def psNoReadAhead (k : RecordKernelState) (e r : CellId) : Prop := psCursor k e r ≤ psHead k e

/-- Reader `r` is CAUGHT UP iff its cursor equals the published head (nothing left to read). -/
def psCaughtUp (k : RecordKernelState) (e r : CellId) : Prop := psCursor k e r = psHead k e

/-! ## §3b — The LIVE relational caveat EXPRESSES the per-reader bound (instantiated). -/

/-- **`readerRelCaveat_expresses_no_read_ahead` (instantiated, per reader).** Subscriber
`r`'s live caveat on the topic record is EXACTLY its no-read-ahead bound `cursor[r] ≤ head`. The
SAME `fieldLteOther` atom the queue uses, instantiated per subscriber. -/
theorem readerRelCaveat_expresses_no_read_ahead (k : RecordKernelState) (e r : CellId) :
    (readerRelCaveat r).eval (k.cell e) = true ↔ psNoReadAhead k e r := by
  unfold readerRelCaveat
  have h := fieldLteOther_expresses_underflow (k.cell e) headSeqField (readerCursorField r)
  unfold psNoReadAhead psCursor psHead
  unfold noUnderflow at h
  exact h

/-! ## §4 — The pubsub OPERATIONS (publish / read) as gated field writes (NO value move). -/

/-- Write a single scalar field of the topic cell. -/
def psWriteField (k : RecordKernelState) (e : CellId) (f : FieldName) (v : Int) : RecordKernelState :=
  { k with cell := fun c => if c = e then setField f (k.cell e) (.int v) else k.cell c }

/-- **`pubsubPublish` — advance the shared head (append a message), gated on the publisher.**
Rejects when the actor's cast ≠ the cell's frozen `publisher` slot. On success: `head_seq` is
incremented by 1 and `message_root` is updated. NO value move (bal-neutral). -/
def pubsubPublish (k : RecordKernelState) (e actor : CellId) (newRoot : Int) :
    Option RecordKernelState :=
  if (actor : Int) = psPublisher k e then
    some (psWriteField (psWriteField k e headSeqField (psHead k e + 1)) e messageRootField newRoot)
  else none

/-- **`pubsubRead` — advance subscriber `r`'s cursor (consume one message), gated on availability.**
Rejects when reader `r` is CAUGHT UP (`cursor[r] ≥ head` ⇒ no new message; reading would push the
cursor past the published frontier, breaking `cursor[r] ≤ head`). On success: `reader_cursor.<r>` is
incremented by 1. Only reader `r`'s cursor moves. NO value move (bal-neutral). -/
def pubsubRead (k : RecordKernelState) (e r : CellId) : Option RecordKernelState :=
  if psCursor k e r < psHead k e then
    some (psWriteField k e (readerCursorField r) (psCursor k e r + 1))
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

/-- Writing field `f` to topic cell `e` and reading field `g ≠ f` of `e` is unchanged. -/
theorem psWriteField_other (k : RecordKernelState) (e : CellId) (f g : FieldName) (v : Int)
    (hfg : g ≠ f) : fieldOf g ((psWriteField k e f v).cell e) = fieldOf g (k.cell e) := by
  unfold psWriteField
  simp only [if_pos rfl]
  exact fieldOf_setField_ne f g (k.cell e) v hfg

/-- Reading field `f` right after writing `f := v` to the same cell returns `v`. -/
theorem psWriteField_same (k : RecordKernelState) (e : CellId) (f : FieldName) (v : Int) :
    fieldOf f ((psWriteField k e f v).cell e) = v := by
  unfold psWriteField; simp only [if_pos rfl]; exact setField_fieldOf f (k.cell e) v

/-! ## §5 — KEYSTONE (a): NO READ-AHEAD (the per-reader cursor bound is PRESERVED by read).

The field names `reader_cursor.<r>` and `head_seq` are DISTINCT for every reader `r` (the cursor
prefix `"pubsub.reader_cursor."` never equals `"pubsub.head_seq"`), so a read of reader `r`'s cursor
leaves `head` unchanged and advances only that cursor. -/

/-- A reader-cursor field is never the head field (distinct lengths: the cursor field is the
21-char prefix `"pubsub.reader_cursor."` ++ a number, always ≥ 21 > 15 = `|"pubsub.head_seq"|`). -/
theorem readerCursor_ne_head (r : CellId) : readerCursorField r ≠ headSeqField := by
  intro h
  have hlen : (readerCursorField r).length = headSeqField.length := by rw [h]
  unfold readerCursorField headSeqField at hlen
  rw [String.length_append] at hlen
  have h1 : "pubsub.reader_cursor.".length = 21 := by decide
  have h2 : "pubsub.head_seq".length = 15 := by decide
  rw [h1, h2] at hlen
  omega

/-- The head/cursor read-back across a read by reader `r`: `cursor[r]` advances by 1, `head`
unchanged. -/
theorem read_reads {k k' : RecordKernelState} {e r : CellId}
    (h : pubsubRead k e r = some k') :
    psCursor k' e r = psCursor k e r + 1 ∧ psHead k' e = psHead k e := by
  unfold pubsubRead at h
  by_cases hg : psCursor k e r < psHead k e
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h; subst h
    refine ⟨?_, ?_⟩
    · unfold psCursor
      exact psWriteField_same k e (readerCursorField r) (psCursor k e r + 1)
    · unfold psHead
      rw [psWriteField_other _ e (readerCursorField r) headSeqField (psCursor k e r + 1)
            (readerCursor_ne_head r).symm]
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`read_preserves_no_read_ahead` — KEYSTONE (a), PROVED.** From `cursor[r] ≤ head`, a committed
read (fires only when `cursor[r] < head`) lands in `cursor[r] ≤ head` STILL — the per-reader
cross-slot bound enforced by the relational atom. -/
theorem read_preserves_no_read_ahead {k k' : RecordKernelState} {e r : CellId}
    (h : pubsubRead k e r = some k') (hpre : psNoReadAhead k e r) :
    psNoReadAhead k' e r := by
  have hguard : psCursor k e r < psHead k e := by
    unfold pubsubRead at h
    by_cases hg : psCursor k e r < psHead k e
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  obtain ⟨hc, hh⟩ := read_reads h
  unfold psNoReadAhead at *
  rw [hc, hh]; omega

/-- **`caught_up_reader_read_rejected` — KEYSTONE (a), the fail-closed half, PROVED.** A CAUGHT-UP
reader (`cursor[r] = head`, nothing new published) rejects every read — no read-ahead past the
published frontier. -/
theorem caught_up_reader_read_rejected (k : RecordKernelState) (e r : CellId)
    (hcaught : psCaughtUp k e r) :
    pubsubRead k e r = none := by
  unfold pubsubRead
  have : ¬ psCursor k e r < psHead k e := by unfold psCaughtUp at hcaught; omega
  rw [if_neg this]

/-! ## §6 — KEYSTONE (b): PUBLISHER-AUTHORIZED APPEND. -/

/-- The head read-back across a publish: `head` advances by 1. -/
theorem publish_reads {k k' : RecordKernelState} {e actor : CellId} {newRoot : Int}
    (h : pubsubPublish k e actor newRoot = some k') :
    psHead k' e = psHead k e + 1 := by
  unfold pubsubPublish at h
  by_cases hg : (actor : Int) = psPublisher k e
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h; subst h
    unfold psHead
    rw [psWriteField_other _ e messageRootField headSeqField newRoot (by decide)]
    exact psWriteField_same k e headSeqField (psHead k e + 1)
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`publish_requires_publisher` — KEYSTONE (b), PROVED.** A publish by an actor whose cast ≠ the
cell's frozen `publisher` slot is REJECTED — only the publisher can append. -/
theorem publish_requires_publisher (k : RecordKernelState) (e actor : CellId) (newRoot : Int)
    (hbad : (actor : Int) ≠ psPublisher k e) :
    pubsubPublish k e actor newRoot = none := by
  unfold pubsubPublish
  rw [if_neg hbad]

/-- **`publisher_can_publish` — KEYSTONE (b), liveness half, PROVED.** The genuine publisher CAN
append. -/
theorem publisher_can_publish (k : RecordKernelState) (e actor : CellId) (newRoot : Int)
    (hpub : (actor : Int) = psPublisher k e) :
    (pubsubPublish k e actor newRoot).isSome := by
  unfold pubsubPublish; rw [if_pos hpub]; exact Option.isSome_some

/-! ## §7 — KEYSTONE (c): READER ISOLATION (one subscriber's progress never moves another's). -/

/-- Two distinct readers have distinct cursor fields (their cast indices differ ⇒ the rendered field
names differ). -/
theorem readerCursor_ne_of_ne {r r' : CellId} (hrr : r ≠ r') :
    readerCursorField r' ≠ readerCursorField r := by
  intro h
  unfold readerCursorField at h
  have heq : toString (r' : Nat) = toString (r : Nat) := (String.append_right_inj _).mp h
  exact hrr (Nat.repr_inj.mp heq).symm

/-- **`read_isolates_other_readers` — KEYSTONE (c), PROVED.** A read by reader `r` leaves every
OTHER reader `r'`'s cursor unchanged — one subscriber's progress never moves another's. -/
theorem read_isolates_other_readers {k k' : RecordKernelState} {e r r' : CellId} (hrr : r ≠ r')
    (h : pubsubRead k e r = some k') :
    psCursor k' e r' = psCursor k e r' := by
  unfold pubsubRead at h
  by_cases hg : psCursor k e r < psHead k e
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h; subst h
    unfold psCursor
    exact psWriteField_other _ e (readerCursorField r) (readerCursorField r')
      (psCursor k e r + 1) (readerCursor_ne_of_ne hrr)
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`read_leaves_head` — KEYSTONE (c), the log half, PROVED.** A read by reader `r` leaves the
shared `head_seq` unchanged — a subscriber's progress never moves the published log. -/
theorem read_leaves_head {k k' : RecordKernelState} {e r : CellId}
    (h : pubsubRead k e r = some k') :
    psHead k' e = psHead k e :=
  (read_reads h).2

/-! ## §8 — BALANCE-NEUTRALITY (pubsub carries no value — bal-neutral like the inbox). -/

/-- **`publish_bal_neutral`.** A publish is a pure field write — every asset's total supply
is unchanged. -/
theorem publish_bal_neutral {k k' : RecordKernelState} {e actor : CellId} {newRoot : Int}
    (h : pubsubPublish k e actor newRoot = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold pubsubPublish at h
  by_cases hg : (actor : Int) = psPublisher k e
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h; subst h
    unfold recTotalAsset psWriteField; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`read_bal_neutral`.** A read is a pure field write — balance-NEUTRAL. -/
theorem read_bal_neutral {k k' : RecordKernelState} {e r : CellId}
    (h : pubsubRead k e r = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold pubsubRead at h
  by_cases hg : psCursor k e r < psHead k e
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h; subst h
    unfold recTotalAsset psWriteField; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §9 — LIVENESS: a behind reader can read; the publisher can publish. -/

/-- **`behind_reader_reads` — a reader strictly BEHIND the head CAN read.** -/
theorem behind_reader_reads (k : RecordKernelState) (e r : CellId)
    (hbehind : psCursor k e r < psHead k e) :
    (pubsubRead k e r).isSome := by
  unfold pubsubRead; rw [if_pos hbehind]; exact Option.isSome_some

/-! ## §10 — MINTING the topic cell through the REAL factory executor. -/

/-- A kernel factory registry publishing the pubsub topic factory at content-addressed key `vk`. -/
def pubsubRegistry (vk : Nat) (publisher : Int) : List (Nat × FactoryEntry) :=
  [(vk, pubsubFactory publisher)]

/-- The registry resolves the pubsub factory at exactly its published key. -/
theorem pubsubRegistry_finds (vk : Nat) (publisher : Int) :
    findFactory (pubsubRegistry vk publisher) vk = some (pubsubFactory publisher) := by
  simp [pubsubRegistry, findFactory]

/-- Mint a topic cell from the pubsub factory at key `vk` (the real factory executor). -/
def mintTopicCell (s : RecChainedState) (actor tCell : CellId) (vk : Int) :
    Option RecChainedState :=
  createCellFromFactoryChainA s actor tCell vk

/-- **`mintTopicCell_installs_caveats`.** A minted topic cell carries EXACTLY the factory's
caveats, installed by the executor. -/
theorem mintTopicCell_installs_caveats {s s' : RecChainedState} {actor tCell : CellId}
    {vk : Int} (e : FactoryEntry)
    (hreg : findFactory s.kernel.factories vk.toNat = some e)
    (h : mintTopicCell s actor tCell vk = some s') :
    s'.kernel.slotCaveats tCell = e.caveats := by
  obtain ⟨e', hfind, hcav⟩ := createCellFromFactoryChainA_installs_program h
  rw [hreg] at hfind
  rw [← (Option.some.injEq _ _).mp hfind] at hcav
  exact hcav

/-- **`mintTopicCell_caveats`.** When the registry IS `pubsubRegistry vk …`, the minted
cell concretely carries the topic factory's caveats. -/
theorem mintTopicCell_caveats {s s' : RecChainedState} {actor tCell : CellId} {vk : Int}
    {publisher : Int}
    (hreg : s.kernel.factories = pubsubRegistry vk.toNat publisher)
    (h : mintTopicCell s actor tCell vk = some s') :
    s'.kernel.slotCaveats tCell = (pubsubFactory publisher).caveats := by
  have hfind : findFactory s.kernel.factories vk.toNat = some (pubsubFactory publisher) := by
    rw [hreg]; exact pubsubRegistry_finds vk.toNat publisher
  exact mintTopicCell_installs_caveats _ hfind h

/-- **`mintTopicCell_neutral`.** Minting a topic cell is conservation-NEUTRAL. -/
theorem mintTopicCell_neutral {s s' : RecChainedState} {actor tCell : CellId} {vk : Int}
    (b : AssetId) (h : mintTopicCell s actor tCell vk = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  createCellFromFactoryChainA_neutral b h

/-- **`mintTopicCell_grows_accounts`.** A minted topic cell IS a live account. -/
theorem mintTopicCell_grows_accounts {s s' : RecChainedState} {actor tCell : CellId} {vk : Int}
    (h : mintTopicCell s actor tCell vk = some s') :
    tCell ∈ s'.kernel.accounts :=
  createCellFromFactoryChainA_grows_accounts h

/-- **`mintTopicCell_unknown_factory_fails` (fail-closed).** Minting against an unknown
factory key never mints. -/
theorem mintTopicCell_unknown_factory_fails (s : RecChainedState) (actor tCell : CellId)
    (vk : Int) (h : findFactory s.kernel.factories vk.toNat = none) :
    mintTopicCell s actor tCell vk = none :=
  createCellFromFactoryChainA_unknown_factory_fails s actor tCell vk h

/-! ## §11 — NON-VACUITY: a concrete topic world + `#guard` witnesses. -/

/-- A pubsub topic world. The TOPIC CELL is cell `0`: publisher 9, head_seq 2; reader 3's cursor 1
(one behind — has a message to read), reader 4's cursor 2 (CAUGHT UP — nothing new). All cells
{0,3,4,9} live. NO value column. -/
def psWorld : RecordKernelState :=
  { accounts := {0, 3, 4, 9}
    cell := fun c =>
      if c = 0 then .record
        [ (headSeqField, .int 2), (publisherField, .int 9), (messageRootField, .int 7)
        , (readerCursorField 3, .int 1), (readerCursorField 4, .int 2) ]
      else .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun _ _ => 0 }

-- (i) the topic reads: head 2; reader 3 behind (cursor 1), reader 4 caught up (cursor 2):
#guard (psHead psWorld 0 == 2)
#guard (psCursor psWorld 0 3 == 1)
#guard (psCursor psWorld 0 4 == 2)
#guard (psPublisher psWorld 0 == 9)

-- (ii) the LIVE per-reader relational atom EXPRESSES each reader's no-read-ahead bound:
#guard ((readerRelCaveat 3).eval (psWorld.cell 0))   -- cursor 1 ≤ head 2
#guard ((readerRelCaveat 4).eval (psWorld.cell 0))   -- cursor 2 ≤ head 2 (caught up, still ≤)

-- (iii) the PUBLISHER (cell 9) can publish and advances the shared head 2→3:
#guard ((pubsubPublish psWorld 0 9 88).isSome)
#guard ((pubsubPublish psWorld 0 9 88).map (fun s => psHead s 0)) == some 3

-- (iv) UNAUTHORIZED PUBLISH REJECTED: cell 3 (≠ publisher 9) cannot publish (KEYSTONE b):
#guard ((pubsubPublish psWorld 0 3 88).isSome) == false

-- (v) reader 3 (behind) READS and advances ONLY reader 3's cursor 1→2; reader 4 + head untouched:
#guard ((pubsubRead psWorld 0 3).isSome)
#guard ((pubsubRead psWorld 0 3).map (fun s => psCursor s 0 3)) == some 2
#guard ((pubsubRead psWorld 0 3).map (fun s => psCursor s 0 4)) == some 2   -- reader 4 ISOLATED
#guard ((pubsubRead psWorld 0 3).map (fun s => psHead s 0)) == some 2       -- log untouched

-- (vi) NO READ-AHEAD: reader 4 (caught up, cursor = head 2) cannot read (KEYSTONE a):
#guard ((pubsubRead psWorld 0 4).isSome) == false

-- (vii) after a publish (head → 3), reader 4 (cursor 2 < 3) CAN now read (liveness):
#guard ((pubsubPublish psWorld 0 9 88).bind (fun s => pubsubRead s 0 4) |>.isSome)

-- (viii) the factory conforms (its empty genesis is invariant-clean):
#guard ((pubsubFactory 9).conforms)

/-! ## §DELETION — the W2 deletion-readiness note (land-before-kill).

THIS module + the relational caveat are the LAND-BEFORE-KILL prerequisite for the pubsub/topic verb
family. Once the factory is the live pubsub path (this module shipped + every pubsub app
re-pointed), W2 DELETES:

  WHAT W2 DELETES (the pubsub side-table surface — and the Argus topic/subscribe effect welds):
    (1) the pubsub kernel arms / chain ops / `FullActionA` arms (create-topic/publish/subscribe/read):
          • CreateTopic ↦ `createCellFromFactoryA` over `pubsubFactory` (the mint).
          • Publish     ↦ `setFieldA head_seq/message_root`, gated by MonotonicSequence + the frozen
            `publisher` immutable.
          • Subscribe   ↦ create a `reader_cursor.<r>` slot (initial 0) + install its monotone +
            `RelCaveat.fieldLteOther reader_cursor.<r> head_seq 0` per-reader bound.
          • Read        ↦ `setFieldA reader_cursor.<r>`, gated by the per-reader LIVE relational
            no-read-ahead bound `cursor[r] ≤ head`.
    (2) the OFF-LEDGER topic side-table + per-subscriber offset bookkeeping (the `topics`/`subscribers`
        fields on `RecordKernelState`) — DISSOLVED into the minted cell's shared head + per-reader
        cursor slots. (NO value column — pubsub is bal-neutral, like the inbox.)
    (3) the per-subscriber offset accounting — COLLAPSED into the per-reader cross-slot relational
        caveat (each cursor's bound is now `RelCaveat.fieldLteOther`, instantiated per subscriber).

  WHAT MUST BE RE-POINTED FIRST (the land-before-kill blockers — every pubsub-verb consumer):
    • any `Dregg2.Apps.*` topic / event-stream / fan-out app on the pubsub verbs — re-point to
      `pubsubFactory` + the gated `setField` writes (same pattern as `BountyBoardGated`).
    • shares NO side-table with queue/inbox (each topic is its own minted cell); the per-reader
      cursor model means subscriptions are slot-additions, not a shared offset table — independent
      per family.

  NOT DELETED HERE (land-before-kill): nothing above is removed in this commit. The verb deletion is
  the SUBSEQUENT W2 commit, gated on the re-points landing green AND the per-reader relational
  caveat wired through `stateStepGuarded`/`caveatsAdmit` for every pubsub `SetField` (RelationalCaveat
  `relStateStepGuarded` supplies exactly this — the per-reader atom is the SAME `fieldLteOther`).
-/

#assert_axioms pubsubFactory_conforms
#assert_axioms readerRelCaveat_expresses_no_read_ahead
#assert_axioms fieldOf_setField_ne
#assert_axioms psWriteField_other
#assert_axioms psWriteField_same
#assert_axioms readerCursor_ne_head
#assert_axioms read_reads
#assert_axioms read_preserves_no_read_ahead
#assert_axioms caught_up_reader_read_rejected
#assert_axioms publish_reads
#assert_axioms publish_requires_publisher
#assert_axioms publisher_can_publish
#assert_axioms readerCursor_ne_of_ne
#assert_axioms read_isolates_other_readers
#assert_axioms read_leaves_head
#assert_axioms publish_bal_neutral
#assert_axioms read_bal_neutral
#assert_axioms behind_reader_reads
#assert_axioms mintTopicCell_installs_caveats
#assert_axioms mintTopicCell_caveats
#assert_axioms mintTopicCell_neutral
#assert_axioms mintTopicCell_grows_accounts
#assert_axioms mintTopicCell_unknown_factory_fails

end Dregg2.Apps.PubsubFactory
