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

* **§B — (F2b) the living-cell register moved to the FACTORY story.** The kernel queue
  side-table (`RecordKernelState.queues`) and the queue verb family are GONE — the living-cell
  subscription is now a FACTORY-BORN cell (`Apps/QueueFactory.lean` / `Apps/PubsubFactory.lean`):
  head/tail/capacity are SLOTS gated by `SlotCaveat` (MonotonicSequence + SenderAuthorized) plus
  the LIVE cross-slot relational caveat `RelCaveat.fieldLteOther` (capacity + no-underflow — the
  very `FieldLteField` constraint dregg1's `lib.rs:272` bakes in). The §A headline's living-cell
  match is `QueueFactory.enqueue_preserves_capacity` / `dequeue_preserves_no_underflow` and the
  in-executor relational gate (`relStateStepGuarded`), proved there.

Templates: `Apps/RightOfWay.lean` (the self-contained automaton + teeth), `Exec/CellNullifier.lean`
(the per-effect kernel FRAME routed through `livingCellA_carries`). Reuses `Exec/CellCarry`'s crown +
`RecordKernel`'s queue transitions; edits nothing.
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

/-! ## §B — (F2b) the living-cell register lives in the factory story now.

The `subWF` 46-arm dispatch FRAME (`execFullA_subWF_preserved` → `subscription_wellformed_forever`)
rode the kernel `queues` side-table and the queue verb family; both are GONE (REDUCTION F2). The
no-overflow / no-underflow safety on the REAL living cell is enforced by the LIVE relational caveat
on the factory-born queue cell — see `Apps/QueueFactory.lean` (keystones a/b + the
`relStateStepGuarded` teeth) and `Apps/PubsubFactory.lean` (the pubsub twin). -/

/-! ## It runs (`#eval`) — the §A automaton exercised (non-vacuity).

A publish on a non-full queue advances `head` and stays well-formed; a consume on a
non-empty queue advances `tail`; the boundary rejections fire.
-/

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

/-! ## Axiom hygiene — every keystone pinned to the standard kernel triple (NO `sorryAx`). -/

-- §A — the faithful slot automaton.
#assert_axioms publish_preserves_WF
#assert_axioms consume_preserves_WF
#assert_axioms consume_empty_rejected
#assert_axioms publish_full_rejected
#assert_axioms subStep_preserves_WF
#assert_axioms subscription_consumer_safe_forever
-- §B — (F2b) the living-cell carry lives in Apps/QueueFactory (relational-caveat keystones).

end Dregg2.Apps.Subscription
