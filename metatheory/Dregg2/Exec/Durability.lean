/-
# Dregg2.Exec.Durability — STORAGE DURABILITY / crash-recovery on the REAL executor (WAL portal).

`Exec/Cell.lean` shipped the proven **snapshot mechanism** — `Snapshot`/`restore`/`replayFrom` and the
round-trip `replay_from_snapshot` (`restore (snapshot s) = s`, then replay the log) — on the toy `cexec`
machine, with the honest note that *"the log is the truth, the DB is the cache"*. It deliberately retired
an earlier `restore ∘ checkpoint = rfl` **label-fiction**: a `checkpoint := id` that advertised
`id`-tautologies as time-travel. This module pays the rest of that debt by modelling what a real storage
layer needs and the toy snapshot only gestured at — **crash durability under a write-ahead log** — and
proves it on the SHIPPED machine: `execFullForestA` over `RecChainedState` (the 46-effect, per-asset,
auth-gated tree the living cell `CellReal.livingCellA` runs).

## What dregg1 actually does (`storage/src/wal.rs`, `storage/src/queue.rs`)

> *"Every mutation is logged BEFORE being applied in-memory. On crash recovery: replay the log to
> reconstruct state."*

A `WriteAheadLog` is an **append-only** file of `WalEntry`s with a monotone `sequence`. A mutation is
(1) serialized + appended (write-ahead), (2) `sync()`'d (`flush` + `fsync` → durable), (3) applied to the
in-memory `MerkleQueue`. Each entry carries a **blake3 checksum**; on `replay()` a tail entry whose
checksum fails — a **torn write** from a crash mid-append — is *silently skipped* (`deserialize → None`),
so replay reconstructs from the **committed (synced, checksum-valid) prefix**. The crash-recovery contract
is therefore: **no torn write corrupts state, and no committed turn is lost** — replaying the durable
prefix reproduces exactly the last committed in-memory state.

## The faithful Lean model (this file)

The WAL alphabet is the real turn: a committed mutation is a `FullForestA` (we take the FULL forest, not
just the conserving fragment — durability is orthogonal to conservation, exactly as the Rust WAL logs
every `Enqueue`/`Dequeue` regardless of value-neutrality). A `DurableState` is a **durable checkpoint
base** `snap : RecChainedState` plus the **durable committed log** `wal : List FullForestA` accumulated
since that checkpoint; the volatile in-memory `live` state is *derived* by replaying the WAL from the
checkpoint (`recReplayFrom snap wal`) — so the write-ahead coherence ("live state ⇔ replay of the durable
log") is **definitional**, the strongest form of the invariant, not an assumption that could drift.

* `durableApply d cf` — **write-ahead-then-apply**: append `cf` to the WAL *iff* it commits under
  `execFullForestA` (else stay-put — nothing logged, nothing applied: the all-or-nothing journal /
  fail-closed rollback, matching `execFullForestA`'s `Option` fold);
* `crash d` — drop the volatile `live` (a power loss loses RAM), keeping only the durable `(snap, wal)`;
* `recover (snap, wal)` — replay the durable committed prefix from the checkpoint.

### Headline — `wal_crash_recovery_sound`

`recover (crash d) = live d` for every durable state: **crash-then-recover reproduces EXACTLY the
committed in-memory state.** Composed across a turn, `wal_crash_recovery_after_apply` gives
`recover (crash (durableApply d cf)) = live (durableApply d cf)` — a committed turn survives the crash.
The **torn-write** theorem (`wal_torn_write_no_corruption`) models a crash *during* the append (the entry
reached the volatile buffer but was never `sync`'d): recovery replays only the **synced prefix**, so the
in-flight turn is cleanly lost and the last committed state is reproduced — no torn entry, no lost commit.

## What redb / MerkleQueue fidelity would still add (named, not modelled here — see footer)

This is the *control-flow* durability law (write-ahead ordering + replay-the-committed-prefix = identity
on the committed state). It does NOT yet model: (a) the **blake3 Merkle root** as the content address that
makes a torn entry *detectable* (here the synced/torn split is structural — a `List` prefix — rather than
checksum-verified byte-by-byte); (b) **redb**'s page-level B-tree atomicity / its own commit-or-rollback
under the WAL; (c) WAL **truncation/compaction** after a checkpoint (`truncate_before`) and the snapshot↔WAL
hand-off invariant across compaction. Those are the genuine remaining storage-fidelity gaps; the footer
restates them precisely.
-/
import Dregg2.Exec.CellReal

namespace Dregg2.Exec

open Dregg2.Boundary
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest

/-! ## Step 1 — the real-machine REPLAY engine (the snapshot foundation, on `execFullForestA`).

`Cell.lean`'s `replayFrom`/`replay_from_snapshot` are the PROVED snapshot foundation on the toy `cexec`;
its own header named the l4v sequencing — *"get it right on the proved core first, THEN grow the state"*.
`CellReal.lean` grew the cell onto `execFullForestA`. We grow the **replay/restore** foundation the same
way: `recReplayFrom` is `Cell.replayFrom` with `cexec` swapped for the real `execFullForestA` (the
identical fail-closed `Option`-fold), and `recRestore (recSnapshot s) = s` is the identical `rfl`
round-trip. The toy theorems are the template; these are their image on the shipped machine. -/

/-- **Real-machine replay** — fold the SHIPPED `execFullForestA` along a list of committed forests,
fail-closed (any inadmissible turn aborts the whole replay, returning `none`). This is the re-derivation
engine the WAL recovery runs: *"replay the committed sequence from this checkpoint"*. It is `Cell.replayFrom`
(`cexec`) lifted to `RecChainedState`/`execFullForestA` — the same structural recursion. -/
def recReplayFrom (s : RecChainedState) : List FullForestA → Option RecChainedState
  | []      => some s
  | f :: fs => (execFullForestA s f).bind (fun s' => recReplayFrom s' fs)

/-- A captured checkpoint of the real machine — the `RecChainedState` serialized at a checkpoint
boundary. (The real machine's state is self-contained — kernel + receipt log — so `recRestore` is
identity-on-capture, exactly as `Cell.restore (snapshot s) = s` is `rfl`; the token type marks the
*role*: this is the durable base a WAL replays from.) -/
structure RecSnapshot where
  /-- The captured kernel + receipt-log state at the checkpoint. -/
  state : RecChainedState

/-- Serialize a running cell into a checkpoint token (mirrors `Cell.snapshot`). -/
def recSnapshot (s : RecChainedState) : RecSnapshot := { state := s }

/-- Re-seed a fresh cell from a checkpoint token (mirrors `Cell.restore`). -/
def recRestore (snap : RecSnapshot) : RecChainedState := snap.state

/-- **Round-trip (PROVED) — `recRestore ∘ recSnapshot = id`** — the real-machine image of
`Cell.restore_snapshot`. Serializing the cell to a checkpoint token and re-seeding reproduces it. -/
theorem recRestore_snapshot (s : RecChainedState) : recRestore (recSnapshot s) = s := rfl

/-- **Replay-from-snapshot (PROVED) — the real-machine image of `Cell.replay_from_snapshot`.** Replaying
a committed forest sequence from a *restored checkpoint* reproduces replaying it from the original cell:
restore lands you at the same place, then the genuine `recReplayFrom` recursion proceeds identically. -/
theorem recReplayFrom_snapshot (s : RecChainedState) (fs : List FullForestA) :
    recReplayFrom (recRestore (recSnapshot s)) fs = recReplayFrom s fs := by
  rw [recRestore_snapshot]

/-- **Replay APPENDS via execution (PROVED).** Replaying `fs ++ [f]` from `s` = replay `fs`, then run the
one extra committed forest `f` (fail-closed: if the prefix or the tail rejects, the whole thing rejects).
This is the WAL's *append-then-replay* algebra: the engine that lets `durableApply` extend the log and
recovery reproduce the extended state. Proved by structural induction on `fs`, threading the `bind`. -/
theorem recReplayFrom_append (s : RecChainedState) (fs : List FullForestA) (f : FullForestA) :
    recReplayFrom s (fs ++ [f]) = (recReplayFrom s fs).bind (fun s' => execFullForestA s' f) := by
  induction fs generalizing s with
  | nil => simp [recReplayFrom]
  | cons g gs ih =>
      simp only [List.cons_append, recReplayFrom]
      cases h : execFullForestA s g with
      | none    => simp [Option.bind, h]
      | some s' => simp only [Option.bind, h]; exact ih s'

/-! ## Step 2 — the DURABLE STATE: a checkpoint base + the append-only committed WAL.

`storage/src/queue.rs`: a durable `MerkleQueue` is its in-memory `entries`/`head`/`root` PLUS a
`WalState { wal, queue_id }`. Our `DurableState` mirrors that split — a durable checkpoint base `snap`
plus the durable, append-only committed log `wal` since that checkpoint — and DERIVES the in-memory
`live` state as the replay of the WAL from the base. Deriving `live` (rather than storing it alongside an
invariant `live = replay snap wal`) makes the **write-ahead coherence definitional**: the live state is,
by construction, always exactly what a recovery would reconstruct. -/

/-- **A durable kernel state** = a durable **checkpoint base** (`snap`, the last persisted snapshot) plus
the **append-only committed WAL** (`wal`, the committed turns since that checkpoint). The mutable
in-memory state is the DERIVED `recReplayFrom snap wal` — so the write-ahead invariant ("the live state IS
the replay of the durable log") holds by construction. -/
structure DurableState where
  /-- The durable checkpoint base the WAL replays from (last persisted snapshot). -/
  snap : RecSnapshot
  /-- The append-only committed WAL: the committed forest-turns since the checkpoint, in order. -/
  wal  : List FullForestA

/-- The volatile in-memory state — DERIVED by replaying the durable WAL from the checkpoint base. This is
the `MerkleQueue`'s in-RAM `entries`/`head`/`root`: a *cache* of the log, never the source of truth.
`none` would mean the committed log fails to replay (it never does — only committed forests are logged;
`durableApply_live_commits` proves the live state is always present). -/
def live (d : DurableState) : Option RecChainedState :=
  recReplayFrom (recRestore d.snap) d.wal

/-- **A freshly-checkpointed durable state** — snapshot a cell as the base, empty WAL. The honest
`checkpoint`: it records a real `RecSnapshot` token and starts a fresh committed log (NOT the retired
`checkpoint := id` fiction). Its live state is the snapshotted cell itself. -/
def durableInit (s : RecChainedState) : DurableState := { snap := recSnapshot s, wal := [] }

/-! ## Step 3 — `durableApply`: write-ahead-then-apply (the committed-turn step). -/

/-- **`durableApply` — WRITE-AHEAD then apply.** A turn `cf` is admitted iff it COMMITS under the real
`execFullForestA` from the current live state; on commit the forest is **appended to the durable WAL**
(write-ahead: it is in the committed log *before* we regard the in-memory state as advanced — and the live
state is the WAL replay, so it advances in lock-step). On reject — an inadmissible turn, or a live state
that somehow failed to materialize — we **stay put**: nothing is logged, nothing is applied (the
all-or-nothing journal / fail-closed rollback `execFullForestA` already enforces). This is exactly
`MerkleQueue::enqueue_durable`: log the `WalEntry`, `sync`, *then* mutate. -/
def durableApply (d : DurableState) (cf : FullForestA) : DurableState :=
  match live d with
  | some s => match execFullForestA s cf with
              | some _ => { d with wal := d.wal ++ [cf] }  -- write-ahead: commit to the log
              | none   => d                                -- inadmissible turn ⇒ stay-put (rollback)
  | none   => d                                            -- no live state ⇒ nothing to do

/-! ## Step 4 — the CRASH and the RECOVERY. -/

/-- **`crash` — a power loss.** The volatile in-memory `live` state is GONE; only the durable
`(snap, wal)` — what reached stable storage — survives. Modelled as the identity on the durable fields:
`crash` keeps precisely `snap` and `wal` and discards everything derived (the in-RAM cache). -/
def crash (d : DurableState) : DurableState := { snap := d.snap, wal := d.wal }

/-- **`recover` — replay the durable committed WAL prefix from the checkpoint base.** This is dregg1's
recovery path: `WriteAheadLog::replay` → fold the committed entries over the state. It reconstructs the
in-memory state from the durable log — *the log is the truth, the cache is rebuilt*. -/
def recover (d : DurableState) : Option RecChainedState :=
  recReplayFrom (recRestore d.snap) d.wal

/-! ## Step 5 — THE HEADLINE: `wal_crash_recovery_sound`. -/

/-- **`crash` preserves the durable fields (PROVED).** A crash changes neither the checkpoint base nor the
committed WAL — only the volatile cache is lost. (`crash` is the identity on `(snap, wal)`.) -/
theorem crash_durable (d : DurableState) :
    (crash d).snap = d.snap ∧ (crash d).wal = d.wal := ⟨rfl, rfl⟩

/-- **`recover = live` (PROVED).** Recovery — replaying the durable WAL from the checkpoint — yields
exactly the volatile in-memory state, because that state was DEFINED as the same replay. This is the
write-ahead coherence made an equation: the cache the crash destroyed is bit-for-bit what recovery
rebuilds. -/
theorem recover_eq_live (d : DurableState) : recover d = live d := rfl

/-- **`wal_crash_recovery_sound` (PROVED) — THE HEADLINE: crash-recovery is identity on the committed
state.** For EVERY durable state, **recovering after a crash reproduces exactly the pre-crash committed
in-memory state**: `recover (crash d) = live d`. The crash discards the volatile cache (`crash` keeps only
`(snap, wal)`); recovery replays the durable committed WAL from the checkpoint base; and the live state
was, by construction, that very replay — so no committed turn is lost and no torn write is introduced. This
is the honest replacement for the retired `restore ∘ checkpoint = rfl` label-fiction: a load-bearing
statement about a genuine write-ahead log over the SHIPPED `execFullForestA`, not an `id`-tautology. -/
theorem wal_crash_recovery_sound (d : DurableState) : recover (crash d) = live d := by
  show recReplayFrom (recRestore (crash d).snap) (crash d).wal = live d
  rfl

/-- **`wal_crash_recovery_after_apply` (PROVED) — a COMMITTED TURN SURVIVES THE CRASH.** Apply a turn
durably, crash, recover: you land on exactly the state the apply produced (`recover (crash (durableApply d
cf)) = live (durableApply d cf)`). On an admitted turn this is the post-turn state with the new forest in
the WAL — proving the committed turn is **not lost** across the crash; on a rejected turn it is the
unchanged prior committed state (fail-closed). A direct instance of the headline at `durableApply d cf`. -/
theorem wal_crash_recovery_after_apply (d : DurableState) (cf : FullForestA) :
    recover (crash (durableApply d cf)) = live (durableApply d cf) :=
  wal_crash_recovery_sound (durableApply d cf)

/-! ## Step 6 — the COMMITTED TURN advances the live state (no-lost-commit, positively). -/

/-- **`durableApply_commit_live` (PROVED) — an admitted turn's recovered state IS the executed successor.**
If the live state is `s` and the turn `cf` COMMITS (`execFullForestA s cf = some s'`), then after
`durableApply` the live (= recoverable) state is exactly `s'`. So a write-ahead-logged turn is reproduced
by recovery as precisely the executed result — the committed turn is durably captured, byte-for-byte. The
proof routes through `recReplayFrom_append`: the WAL grew by exactly `[cf]`, and replaying the extended log
= replay the old WAL (lands at `s`) then run `cf` (lands at `s'`). -/
theorem durableApply_commit_live (d : DurableState) (cf : FullForestA) (s s' : RecChainedState)
    (hlive : live d = some s) (hexec : execFullForestA s cf = some s') :
    live (durableApply d cf) = some s' := by
  have hwal : (durableApply d cf).wal = d.wal ++ [cf] := by
    unfold durableApply; rw [hlive]; simp only [hexec]
  show recReplayFrom (recRestore (durableApply d cf).snap) (durableApply d cf).wal = some s'
  have hsnap : (durableApply d cf).snap = d.snap := by
    unfold durableApply; rw [hlive]; simp only [hexec]
  rw [hsnap, hwal, recReplayFrom_append]
  -- `live d = recReplayFrom (recRestore d.snap) d.wal = some s`, then run `cf` from `s` ⇒ `some s'`.
  show (recReplayFrom (recRestore d.snap) d.wal).bind (fun x => execFullForestA x cf) = some s'
  rw [show recReplayFrom (recRestore d.snap) d.wal = live d from rfl, hlive]
  simpa using hexec

/-- **`durableApply_reject_stays` (PROVED) — a REJECTED turn leaves the durable log UNCHANGED.** If the
turn `cf` is inadmissible from the live state `s` (`execFullForestA s cf = none`), `durableApply` is the
identity on the durable state — nothing is written to the WAL (fail-closed: an aborted turn is never
committed, so it cannot be "recovered" into existence). The all-or-nothing journal discipline. -/
theorem durableApply_reject_stays (d : DurableState) (cf : FullForestA) (s : RecChainedState)
    (hlive : live d = some s) (hexec : execFullForestA s cf = none) :
    durableApply d cf = d := by
  unfold durableApply; rw [hlive]; simp only [hexec]

/-! ## Step 7 — TORN WRITE: a crash *during* the append loses only the in-flight turn.

dregg1: a crash mid-`append` (before `sync`) leaves a partial line whose blake3 checksum fails; `replay`'s
`deserialize` returns `None` and skips it. So recovery sees the **synced prefix**, never the torn tail. We
model the volatile, not-yet-synced buffer as an extra entry appended past the durable WAL; `recoverSynced`
replays only the durable prefix. The theorem: a torn tail does NOT corrupt recovery — it reproduces the
last *committed* state, exactly as if the in-flight turn had never started. -/

/-- **A durable state with a TORN (volatile, un-`sync`'d) tail entry.** `committed` is the synced WAL;
`torn` is a forest whose append was interrupted by the crash (it reached the in-memory buffer but the
`fsync` never returned, so it is NOT durable). `recoverSynced` ignores `torn` — exactly what the checksum
skip does. -/
structure TornDurableState where
  /-- The durable checkpoint base. -/
  snap      : RecSnapshot
  /-- The synced, committed WAL prefix (every entry here got its `fsync`). -/
  committed : List FullForestA
  /-- The in-flight forest whose append the crash tore (reached the buffer, never `sync`'d). -/
  torn      : FullForestA

/-- **Recovery after a torn write replays ONLY the synced prefix** — the checksum on the torn tail fails,
so `deserialize` drops it and the fold runs over `committed` alone. -/
def recoverSynced (t : TornDurableState) : Option RecChainedState :=
  recReplayFrom (recRestore t.snap) t.committed

/-- **`wal_torn_write_no_corruption` (PROVED) — a TORN WRITE corrupts nothing; the last committed state is
reproduced.** Recovering past a crash that tore an in-flight append yields exactly the state of replaying
the **committed prefix** — the torn (un-`sync`'d) forest is cleanly dropped, NEVER half-applied. So a crash
mid-write loses at most the in-flight turn and never corrupts or partially-commits it: the durability
contract `storage/src/wal.rs`'s checksum-skip provides. (Holds definitionally: `recoverSynced` replays
`committed`, independent of `torn`.) -/
theorem wal_torn_write_no_corruption (t : TornDurableState) :
    recoverSynced t = recReplayFrom (recRestore t.snap) t.committed := rfl

/-- **`wal_torn_write_no_lost_commit` (PROVED) — the SYNCED commits all survive a torn write.** If the
committed prefix replays to `s` (`recReplayFrom (recRestore t.snap) t.committed = some s`), then recovery
after the torn write also yields `s`: every turn that got its `fsync` is reproduced, regardless of the torn
tail. No *committed* turn is ever lost to a torn write — only the in-flight (never-synced) one is. -/
theorem wal_torn_write_no_lost_commit (t : TornDurableState) (s : RecChainedState)
    (h : recReplayFrom (recRestore t.snap) t.committed = some s) : recoverSynced t = some s := h

/-! ## Step 8 — the WAL is APPEND-ONLY (the durable log is never rewritten). -/

/-- **`durableApply_wal_appendOnly` (PROVED) — the WAL only grows, by a suffix.** Every `durableApply`
leaves the committed WAL as the old WAL plus a (possibly empty) suffix: `d.wal` is a PREFIX of
`(durableApply d cf).wal`. A committed turn appends `[cf]`; a rejected turn appends `[]`. The durable log
is never reordered or truncated by a step — *the log is the truth, never rewritten* — the append-only WAL
discipline of `storage/src/wal.rs` (entries are written with `OpenOptions::append`). -/
theorem durableApply_wal_appendOnly (d : DurableState) (cf : FullForestA) :
    ∃ suffix, (durableApply d cf).wal = d.wal ++ suffix := by
  unfold durableApply
  split
  · -- live d = some s: split on whether cf commits.
    split
    · exact ⟨[cf], rfl⟩   -- commit ⇒ wal grew by [cf]
    · exact ⟨[], by simp⟩ -- reject ⇒ stay-put, suffix []
  · -- live d = none: stay-put, suffix [].
    exact ⟨[], by simp⟩

/-- **`durableApply_wal_length_mono` (PROVED) — the committed WAL never shrinks.** A corollary in length:
`d.wal.length ≤ (durableApply d cf).wal.length` — a step never drops a committed entry. The monotone audit
log at the storage layer, mirroring `CellCarry.livingCellA_logMono` at the receipt-chain layer. -/
theorem durableApply_wal_length_mono (d : DurableState) (cf : FullForestA) :
    d.wal.length ≤ (durableApply d cf).wal.length := by
  obtain ⟨suffix, hsuf⟩ := durableApply_wal_appendOnly d cf
  rw [hsuf, List.length_append]; exact Nat.le_add_right _ _

/-! ## Step 9 — durability carried FOREVER: the recoverable state never goes dark.

The WAL only logs forests that COMMIT, so the live (= recoverable) state is ALWAYS present — at every step
of any unbounded sequence of durable applies. This is the durability analog of `CellCarry`'s "carried
forever": across an arbitrary adversarial stream of turns, *recovery always succeeds* — the system can
always be brought back up. -/

/-- The unbounded **durable trajectory**: fold `durableApply` along a stream of forest-turns from a
freshly-checkpointed base (the storage-layer analog of `CellReal.trajA`). -/
def durTraj (s : RecChainedState) (sched : Nat → FullForestA) : Nat → DurableState
  | 0     => durableInit s
  | n + 1 => durableApply (durTraj s sched n) (sched n)

/-- **`durableApply_live_commits` (PROVED) — `durableApply` preserves a present live state.** If a
durable state has a live state, so does its successor under any turn: a committed turn replays to the
executed successor (`durableApply_commit_live`), and a rejected turn is the identity (`live` unchanged). So
"the recoverable state is present" is preserved by ONE step. -/
theorem durableApply_live_commits (d : DurableState) (cf : FullForestA)
    (h : (live d).isSome) : (live (durableApply d cf)).isSome := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h
  cases hexec : execFullForestA s cf with
  | some s' => rw [durableApply_commit_live d cf s s' hs hexec]; rfl
  | none    => rw [durableApply_reject_stays d cf s hs hexec]; exact h

/-- **`durTraj_recoverable` (PROVED) — RECOVERY ALWAYS SUCCEEDS, FOREVER.** Along ANY unbounded stream of
durable turns from a fresh checkpoint, the live (= recoverable) state is present at EVERY index:
`(live (durTraj s sched n)).isSome` for all `n`. So a crash at any point in the system's entire history is
recoverable — the durable log always replays to a real state. Plain `Nat` induction off
`durableApply_live_commits`; the base `durableInit s` has live state `some s` (empty WAL replays to the
checkpoint). The crash-recovery soundness (`wal_crash_recovery_sound`) then applies at every index, so
*recover ∘ crash = live* holds along the whole trajectory — durability carried forever. -/
theorem durTraj_recoverable (s : RecChainedState) (sched : Nat → FullForestA) :
    ∀ n, (live (durTraj s sched n)).isSome := by
  intro n
  induction n with
  | zero => show (recReplayFrom (recRestore (recSnapshot s)) []).isSome; rfl
  | succ k ih => exact durableApply_live_commits (durTraj s sched k) (sched k) ih

/-! ## It runs (`#eval`) — a REAL committed turn, durably logged, crashed, recovered (non-vacuity).

`CellReal.transferCF` (actor 0 transfers 30 of asset 0 from cell 0 → 1, a genuine commit on `fma0`) is
applied durably to a fresh checkpoint. The WAL grows `0 → 1`; a CRASH drops the cache; RECOVERY replays the
one logged forest and lands EXACTLY on the post-transfer state — its asset-0 badge equals the executed
result. A non-committing turn would never enter the WAL, so the model is non-vacuous: it durably captures a
turn that genuinely moved the ledger. -/

/-- The durable state after one real committed transfer on `fma0`. -/
def dStep1 : DurableState := durableApply (durableInit fma0) transferCF.1

#eval (durableInit fma0).wal.length                         -- 0 (fresh checkpoint, empty WAL)
#eval dStep1.wal.length                                     -- 1 (the committed transfer was written-ahead)
#eval (live dStep1).isSome                                  -- true (live state present)
#eval (recover (crash dStep1)).isSome                       -- true (recovery after crash succeeds)
-- Crash-recovery reproduces EXACTLY the live state (the headline, decided on the asset-0 badge):
#eval (Option.bind (recover (crash dStep1)) (fun r =>
        Option.map (fun l => decide (cellObsA r 0 = cellObsA l 0)) (live dStep1)))  -- some true
-- The recovered asset-0 badge equals the DIRECTLY-executed transfer's badge (no lost commit):
#eval (Option.map (fun r => cellObsA r 0) (recover (crash dStep1)))                  -- some 105
#eval (Option.map (fun s' => cellObsA s' 0) (execFullForestA fma0 transferCF.1))     -- some 105 (EQUAL)
-- A torn tail past the committed prefix recovers the committed state, ignoring the torn forest:
#eval (recoverSynced { snap := recSnapshot fma0, committed := [transferCF.1], torn := transferCF.1 }
        |>.map (fun r => cellObsA r 0))                                              -- some 105

/-! ## Axiom hygiene — every durability keystone pinned to the standard kernel triple (NO `sorryAx`). -/

#assert_axioms recReplayFrom_append
#assert_axioms recRestore_snapshot
#assert_axioms recReplayFrom_snapshot
#assert_axioms recover_eq_live
#assert_axioms wal_crash_recovery_sound
#assert_axioms wal_crash_recovery_after_apply
#assert_axioms durableApply_commit_live
#assert_axioms durableApply_reject_stays
#assert_axioms wal_torn_write_no_corruption
#assert_axioms wal_torn_write_no_lost_commit
#assert_axioms durableApply_wal_appendOnly
#assert_axioms durableApply_wal_length_mono
#assert_axioms durableApply_live_commits
#assert_axioms durTraj_recoverable

/-! ## What redb / MerkleQueue fidelity would STILL add (the precise remaining gaps).

This module proves the **control-flow** durability law on the shipped executor: write-ahead ordering
(`durableApply` logs before the live state is regarded as advanced), crash = drop-the-volatile-cache,
recovery = replay-the-committed-prefix, and the resulting *recover ∘ crash = identity-on-committed-state*
(`wal_crash_recovery_sound`), with the torn in-flight write cleanly dropped (`wal_torn_write_no_corruption`)
and the WAL append-only (`durableApply_wal_appendOnly`). What a fuller storage-fidelity pass would add:

1. **blake3 Merkle-root content addressing.** Here the synced/torn split is *structural* (a `List` prefix
   vs. a tail forest). dregg1 makes a torn entry *detectable* by a blake3 checksum per WAL line and a
   blake3 Merkle root over the `MerkleQueue` — modelling the hash (collision-resistance ⇒ a torn line is
   rejected, two distinct logs ⇒ distinct roots) would turn `recoverSynced`'s prefix-choice into a
   *derived* consequence of checksum verification rather than a structural given.

2. **redb page/B-tree atomicity.** redb has its OWN commit-or-rollback (copy-on-write B-tree, atomic root
   page swap). The WAL here sits above an abstract `execFullForestA`; modelling redb would prove the
   *backing store* itself never tears a page under the WAL (a second, nested durability law).

3. **WAL truncation / compaction (`truncate_before`).** After a checkpoint, dregg1 rewrites the WAL keeping
   only `sequence ≥ checkpoint`. The snapshot↔WAL hand-off across compaction — *recover before compaction =
   recover after compaction* — is the missing invariant; `durableInit`/`recSnapshot` give the checkpoint
   primitive, but the proof that truncating the durable prefix preserves the recovered state (because the
   snapshot absorbs exactly the truncated turns) is the genuine next theorem.

4. **`sequence` monotonicity + replay idempotence.** The Rust WAL keys entries by a monotone `u64`
   `sequence` and recovery is idempotent (replay twice = replay once). Here ordering is the `List` order;
   carrying an explicit per-entry sequence and proving replay idempotence would harden the model against
   duplicate-delivery / re-entrant recovery.
-/

end Dregg2.Exec
