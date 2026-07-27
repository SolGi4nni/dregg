/-!
# Iocore.Wake — verified coalesced might-block wakeup (Dekker, zero-syscall busy reactor)

Cross-thread wakeup is the one place a completion reactor *must* touch a shared
mutable cell: a producer on some other core has enqueued work and needs to nudge
the reactor, which may at that very instant be deciding to go to sleep in a
blocking kernel call. The naive design — "always ring the doorbell" — pays a
syscall (an `eventfd`/pipe write, or a `kevent` user-trigger) on *every* wakeup,
even when the reactor is wide awake and busy draining completions. The naive
*coalescing* design — "ring only on the first pending" — drops wakeups that race
the reactor's decision to block. Getting both right is a classic mutual-exclusion
problem, and the fix is **Dekker's algorithm** specialized to two flags:

* `pending`    — the producer's flag: "I have posted work / a wakeup".
* `mightBlock` — the reactor's flag: "I am about to block in the kernel".

**Producer (`notify`).** Publish `pending := true` (an atomic swap that also
tells the producer whether it *owns* the false→true transition, for coalescing).
Then read `mightBlock`. Signal the kernel doorbell **only if** the producer owns
the transition **and** the reactor announced it might block. Otherwise: silence —
either another wakeup is already in flight (coalesced) or the reactor is busy and
will observe `pending` on its next lap (zero syscalls).

**Reactor (pre-block).** Publish `mightBlock := true`. Then read `pending`. If
set, cancel the block and drain immediately. Otherwise block; the producer's
doorbell (if it fired) interrupts the blocking syscall.

The **Dekker invariant** is the crux: under sequentially-consistent ordering of
the two flags (production uses `SeqCst`, or the `swap(AcqRel);fence(SeqCst)`
decomposition), it is *impossible* for the producer to skip the doorbell (having
read `mightBlock = false`) **and** the reactor to block (having read
`pending = false`). Program order — producer writes `pending` *before* reading
`mightBlock`, reactor writes `mightBlock` *before* reading `pending` — forces at
least one thread to observe the other. In the running engines this lives in a
loom model and a `// SAFETY` comment. Here it is a **theorem**, quantified over
**every** interleaving of the four atomic memory operations.

## What is proven (0 sorries)

* `wake_no_lost` — for *every* sequentially-consistent interleaving of the
  producer/reactor atomic operations that respects program order, the wakeup is
  delivered: the producer wrote the doorbell **or** the reactor cancelled its
  block. No lost wakeup.
* `wake_busy_zero_syscall` — a wakeup posted while the reactor is busy
  (`mightBlock = false`, not about to block) issues **no** syscall.
* `wake_idempotent` — `notify` is idempotent: a second concurrent wakeup
  coalesces into the first, adding no further doorbell.

Non-vacuity is pinned by explicit witnesses (`no_lost_inhabited`) and by mutants
that violate the contract exactly where it is load-bearing
(`dekker_order_necessary`, `coalescing_guard_necessary`, `busy_guard_necessary`).
-/

namespace Iocore.Wake

/-- The shared wakeup cell of a completion reactor. `pending` is the producer's
Dekker flag (also the coalescing flag), `mightBlock` the reactor's, and
`syscalls` counts doorbell writes (the `eventfd`/`kevent` syscall we are trying
to avoid). -/
structure Cq where
  pending    : Bool
  mightBlock : Bool
  syscalls   : Nat
deriving DecidableEq, Repr

/-- Producer side: post a cross-thread wakeup.

`owner` is the value an atomic `swap(pending, true)` returns negated — it is
`true` exactly when *this* call performed the false→true transition, i.e. it is
the coalescing leader. The doorbell (`syscalls + 1`) fires only when this call
owns the transition **and** the reactor announced it might block. -/
def notify (c : Cq) : Cq :=
  let owner := !c.pending
  { pending    := true
    mightBlock := c.mightBlock
    syscalls   := if owner && c.mightBlock then c.syscalls + 1 else c.syscalls }

/-- Reactor side: after waking / draining, clear the pending flag. -/
def drain (c : Cq) : Cq := { c with pending := false }

/-! ## Coalescing and the busy reactor (sequential facts) -/

/-- **`wake_idempotent`** — a second wakeup racing the first coalesces into it:
`notify` is idempotent, so no second doorbell is issued. This is the coalescing
guarantee (at most one doorbell per batch of concurrent wakeups). -/
theorem wake_idempotent (c : Cq) : notify (notify c) = notify c := by
  rcases c with ⟨p, mb, s⟩
  cases p <;> cases mb <;> rfl

/-- Corollary in the currency that matters: the coalesced second wakeup adds no
syscall. -/
theorem wake_coalesce_no_extra_syscall (c : Cq) :
    (notify (notify c)).syscalls = (notify c).syscalls := by
  rw [wake_idempotent]

/-- **`wake_busy_zero_syscall`** — a wakeup posted to a *busy* reactor (one that
has not announced it might block: `mightBlock = false`) issues no syscall. -/
theorem wake_busy_zero_syscall (c : Cq) (h : c.mightBlock = false) :
    (notify c).syscalls = c.syscalls := by
  simp [notify, h]

/-! ## The Dekker no-lost-wakeup theorem (all interleavings)

We model the concurrent execution as an interleaving of the four load-bearing
atomic memory operations under sequentially-consistent ordering (the total
modification order production obtains from `SeqCst`). The *demonic* freedom —
which thread's operation the hardware schedules next — is exactly the set of
program-order-respecting interleavings, which we quantify over with an
interleaving relation. -/

/-- The four atomic memory operations of the protocol.
* `PW` — producer writes `pending := true`  (`swap`, records `owner`);
* `PR` — producer reads `mightBlock`;
* `RW` — reactor writes `mightBlock := true`;
* `RR` — reactor reads `pending`. -/
inductive Ev | PW | PR | RW | RR
deriving DecidableEq, Repr

/-- The observable state threaded through an execution: the two flags, plus what
each side *observed* (`owner` = producer's swap result; `prSawMB` = producer's
read of `mightBlock`; `rrSawPending` = reactor's read of `pending`). -/
structure Sim where
  pending      : Bool
  mightBlock   : Bool
  owner        : Bool
  prSawMB      : Bool
  rrSawPending : Bool
deriving Repr

/-- Both flags down, nothing observed. -/
def Sim.init : Sim := ⟨false, false, false, false, false⟩

/-- Sequentially-consistent single-step of one atomic operation. -/
def step (s : Sim) : Ev → Sim
  | .PW => { s with owner := !s.pending, pending := true }
  | .PR => { s with prSawMB := s.mightBlock }
  | .RW => { s with mightBlock := true }
  | .RR => { s with rrSawPending := s.pending }

/-- Run a whole schedule from the initial state. -/
def runSchedule (sch : List Ev) : Sim := sch.foldl step Sim.init

/-- The wakeup is *delivered* on a run iff the producer fired the doorbell
(it owned the transition and saw the reactor about to block) **or** the reactor
cancelled its block (it saw the pending flag). -/
def delivered (s : Sim) : Bool :=
  (s.owner && s.prSawMB) || s.rrSawPending

/-- Program-order-respecting interleaving of two per-thread operation sequences:
`IL prod react sched` holds when `sched` merges `prod` and `react` keeping each
thread's operations in order. This is the exact set of SC schedules the hardware
may pick. -/
inductive IL : List Ev → List Ev → List Ev → Prop
  | nil : IL [] [] []
  | left  {a as bs cs} : IL as bs cs → IL (a :: as) bs (a :: cs)
  | right {b as bs cs} : IL as bs cs → IL as (b :: bs) (b :: cs)

/-- **`wake_no_lost`** — the headline. For *every* interleaving of the producer
program `[PW, PR]` and the reactor program `[RW, RR]` (announce-then-check, the
Dekker order), the wakeup is delivered. No wakeup posted concurrently with the
reactor's decision to sleep is ever lost. -/
theorem wake_no_lost {s : List Ev}
    (h : IL [Ev.PW, Ev.PR] [Ev.RW, Ev.RR] s) :
    delivered (runSchedule s) = true := by
  cases h with
  | left h => cases h with
    | left h => cases h with
      | right h => cases h with
        | right h => cases h with
          | nil => decide
    | right h => cases h with
      | left h => cases h with
        | right h => cases h with
          | nil => decide
      | right h => cases h with
        | left h => cases h with
          | nil => decide
  | right h => cases h with
    | left h => cases h with
      | left h => cases h with
        | right h => cases h with
          | nil => decide
      | right h => cases h with
        | left h => cases h with
          | nil => decide
    | right h => cases h with
      | left h => cases h with
        | left h => cases h with
          | nil => decide

/-! ## Non-vacuity: witnesses and contract-tight mutants -/

/-- The hypothesis of `wake_no_lost` is inhabited — there really are such
interleavings (this exhibits the producer-then-reactor race). -/
theorem no_lost_inhabited :
    IL [Ev.PW, Ev.PR] [Ev.RW, Ev.RR] [Ev.PW, Ev.RW, Ev.PR, Ev.RR] :=
  IL.left (IL.right (IL.left (IL.right IL.nil)))

/-- Mutant: a reactor that **checks pending before announcing might_block**
(program `[RR, RW]` — the wrong order) admits a valid interleaving on which the
wakeup is *lost* (`delivered = false`). This is precisely why the Dekker order
(announce, *then* check) is load-bearing: swap the two reactor operations and
`wake_no_lost` becomes false. -/
theorem dekker_order_necessary :
    IL [Ev.PW, Ev.PR] [Ev.RR, Ev.RW] [Ev.RR, Ev.PW, Ev.PR, Ev.RW]
      ∧ delivered (runSchedule [Ev.RR, Ev.PW, Ev.PR, Ev.RW]) = false :=
  ⟨IL.right (IL.left (IL.left (IL.right IL.nil))), by decide⟩

/-- A doorbell that fires unconditionally (dropping both guards). -/
def notifyBroken (c : Cq) : Cq := { c with pending := true, syscalls := c.syscalls + 1 }

/-- Mutant: without the coalescing guard, `notify` is **not** idempotent — a
second wakeup issues a second doorbell. This shows the `owner` guard in `notify`
is what buys coalescing. -/
theorem coalescing_guard_necessary :
    ∃ c : Cq, (notifyBroken (notifyBroken c)).syscalls ≠ (notifyBroken c).syscalls :=
  ⟨⟨false, false, 0⟩, by decide⟩

/-- Mutant: without the `mightBlock` guard, a wakeup to a *busy* reactor incurs a
syscall — the very cost `wake_busy_zero_syscall` eliminates. -/
theorem busy_guard_necessary :
    ∃ c : Cq, c.mightBlock = false ∧ (notifyBroken c).syscalls ≠ c.syscalls :=
  ⟨⟨false, false, 0⟩, by decide, by decide⟩

/-! ## Executable sanity checks (the theorems, exercised on real inputs) -/

-- Busy reactor: two wakeups, reactor never announced a block → zero syscalls.
private def busyRun : Nat :=
  let c : Cq := ⟨false, false, 0⟩
  (notify (notify c)).syscalls
#guard busyRun == 0

-- Reactor about to block: first wakeup rings once, second coalesces → one syscall.
private def blockingRun : Nat :=
  let c : Cq := ⟨false, true, 0⟩          -- reactor announced mightBlock
  (notify (notify c)).syscalls
#guard blockingRun == 1

-- Every interleaving of the correct (Dekker) protocol delivers the wakeup.
#guard delivered (runSchedule [Ev.PW, Ev.PR, Ev.RW, Ev.RR]) == true
#guard delivered (runSchedule [Ev.PW, Ev.RW, Ev.PR, Ev.RR]) == true
#guard delivered (runSchedule [Ev.PW, Ev.RW, Ev.RR, Ev.PR]) == true
#guard delivered (runSchedule [Ev.RW, Ev.PW, Ev.PR, Ev.RR]) == true
#guard delivered (runSchedule [Ev.RW, Ev.PW, Ev.RR, Ev.PR]) == true
#guard delivered (runSchedule [Ev.RW, Ev.RR, Ev.PW, Ev.PR]) == true

-- The wrong (check-before-announce) reactor order loses this one.
#guard delivered (runSchedule [Ev.RR, Ev.PW, Ev.PR, Ev.RW]) == false

end Iocore.Wake
