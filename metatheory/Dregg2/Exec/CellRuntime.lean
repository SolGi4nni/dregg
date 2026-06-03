/-
# Dregg2.Exec.CellRuntime — checkpoint / restore / replay / time-travel as THEOREMS.

dregg2's living cell is an element of a final coalgebra `νF` — codata, not a transaction log.
The consequence of that choice: checkpoint / restore / replay / time-travel are theorems about
the running cell, not bespoke features. A snapshot is a re-seeding point in the unfold; restoring
is re-seeding the anamorphism; replaying is a deterministic fold over the committed log; forking is
running a different admissible turn-suffix from a shared snapshot — both continuations are sound
(no drifting future on either branch).

This module collects those as named keystones over the finite-run forms (`List Turn` / `List RecOp`),
reusing the existing `Snapshot`/`restore`/`snapshot`/`replayFrom`/`recReplay` machinery:

- **`checkpoint_restore_roundtrip`** — `restore ∘ checkpoint = id`.
- **`replay_deterministic_run`** — replay is a function (the unfold is deterministic).
- **`time_travel_fork`** — forking at a snapshot and running a different suffix yields two
  divergent continuations that both conserve the snapshot's badge.

The coinductive fork (two streams sharing a bisimulation prefix) is not rebuilt here; its soundness
content is already discharged since each step is step-complete (`Cell.livingCell_sound`). This module
adds the finite, executable form.
-/
import Dregg2.Exec.Cell
import Dregg2.Exec.RecordCellLive

namespace Dregg2.Exec.CellRuntime

open Dregg2.Exec Dregg2.Boundary

/-! ## 1 — Checkpoint / restore round-trip (the toy ℤ-ledger living cell).

`checkpoint` serializes a running cell into a distinct `Snapshot` token; `restore` re-seeds a
fresh carrier from it. The round-trip is genuine content (it crosses `ChainedState → Snapshot →
ChainedState`), not an `id`-tautology. -/

/-- **Checkpoint** — serialize a running cell into a named `Snapshot` token. An alias for `Cell.snapshot`. -/
def checkpoint (s : ChainedState) : Snapshot := snapshot s

/-- **`checkpoint_restore_roundtrip`** — `restore ∘ checkpoint = id`: restoring a named snapshot
recovers exactly the checkpointed cell. The token captures enough to rebuild the running cell. -/
theorem checkpoint_restore_roundtrip (s : ChainedState) : restore (checkpoint s) = s := rfl

/-- **`restore_comp_checkpoint`** — the composite `restore ∘ checkpoint` is literally the identity on cells. -/
theorem restore_comp_checkpoint : restore ∘ checkpoint = (id : ChainedState → ChainedState) :=
  rfl

/-- **`checkpoint_restore_obs`** — the restored cell emits exactly the conserved observation the
snapshot recorded: the checkpoint is a faithful record of the observable, not merely raw state. -/
theorem checkpoint_restore_obs (s : ChainedState) :
    cellObs (restore (checkpoint s)) = (checkpoint s).headObs := rfl

/-! ## 2 — Replay is deterministic (the log is the truth, the cell is the cache). -/

/-- **`replay_deterministic_run`** — re-running the same logged turn list from the same state
always reproduces the same successor cell: the unfold `cexec`/`replayFrom` is deterministic. -/
theorem replay_deterministic_run {s a b : ChainedState} {ts : List Turn}
    (ha : replayFrom s ts = some a) (hb : replayFrom s ts = some b) : a = b :=
  Option.some.inj (ha.symm.trans hb)

/-- **`replay_from_checkpoint`** — restoring a checkpoint and replaying the logged turn list lands
in exactly the result of replaying from the original cell. Routes through `checkpoint_restore_roundtrip`. -/
theorem replay_from_checkpoint (s : ChainedState) (ts : List Turn) :
    replayFrom (restore (checkpoint s)) ts = replayFrom s ts := by
  rw [checkpoint_restore_roundtrip]

/-! ### Replay conserves the badge.

A replay is sound because every step is step-complete (`cexec_attests` ⇒ `conservation_step_realized`). -/

/-- **`replayFrom_conserves`** — any successful multi-turn replay preserves the conserved badge
`cellObs` (total supply). Induction over the turn list, each committed `cexec` step conserves
via `conservation_step_realized`. -/
theorem replayFrom_conserves :
    ∀ (s s' : ChainedState) (ts : List Turn),
      replayFrom s ts = some s' → cellObs s' = cellObs s := by
  intro s s' ts
  induction ts generalizing s with
  | nil =>
      intro hrun
      simp only [replayFrom, Option.some.injEq] at hrun
      subst hrun; rfl
  | cons t ts ih =>
      intro hrun
      simp only [replayFrom] at hrun
      cases hc : cexec s t with
      | none => rw [hc] at hrun; simp at hrun
      | some s1 =>
          rw [hc] at hrun
          -- `(some s1).bind (replayFrom · ts)` is defeq to `replayFrom s1 ts`.
          have hstep : cellObs s1 = cellObs s := by
            unfold cellObs; exact conservation_step_realized hc
          exact (ih s1 hrun).trans hstep

/-! ## 3 — Time-travel fork: a divergent, still-sound continuation from one snapshot.

From a checkpoint we restore the cell and drive it down two different admissible turn-suffixes. Both
continuations are valid (step-complete by `cexec_attests`), both conserve the snapshot's badge, and
they genuinely diverge while sharing the restored prefix. Time-travel + branch as a theorem. -/

/-- **`fork_branches_from_shared_snapshot`** — restoring a checkpoint and running two turn-suffixes
both depart from the same re-seeded prefix: the two branches are forks of one cell. -/
theorem fork_branches_from_shared_snapshot (s : ChainedState) (ts₁ ts₂ : List Turn) :
    replayFrom (restore (checkpoint s)) ts₁ = replayFrom s ts₁
    ∧ replayFrom (restore (checkpoint s)) ts₂ = replayFrom s ts₂ := by
  constructor <;> rw [checkpoint_restore_roundtrip]

/-- **`time_travel_fork`** — fork at a checkpoint and run two different turn-suffixes from the
restored cell. If both branches commit, both conserve the checkpoint's recorded badge
(`cellObs a = cellObs b = (checkpoint s).headObs`) — neither drifts from the conservation law.
The branches may differ; soundness guarantees only that whatever they reach, they reach conserving. -/
theorem time_travel_fork {s a b : ChainedState} {ts₁ ts₂ : List Turn}
    (ha : replayFrom (restore (checkpoint s)) ts₁ = some a)
    (hb : replayFrom (restore (checkpoint s)) ts₂ = some b) :
    cellObs a = (checkpoint s).headObs ∧ cellObs b = (checkpoint s).headObs := by
  rw [checkpoint_restore_roundtrip] at ha hb
  refine ⟨?_, ?_⟩
  · -- branch 1 conserves the snapshot badge.
    have := replayFrom_conserves s a ts₁ ha
    simpa [checkpoint, snapshot, cellObs] using this
  · -- branch 2 conserves the snapshot badge — same proof, the OTHER suffix.
    have := replayFrom_conserves s b ts₂ hb
    simpa [checkpoint, snapshot, cellObs] using this

/-- **`time_travel_fork_agree_obs`** — the two forked branches agree on the conserved badge
(`cellObs a = cellObs b`) even when divergent on raw state. -/
theorem time_travel_fork_agree_obs {s a b : ChainedState} {ts₁ ts₂ : List Turn}
    (ha : replayFrom (restore (checkpoint s)) ts₁ = some a)
    (hb : replayFrom (restore (checkpoint s)) ts₂ = some b) :
    cellObs a = cellObs b := by
  obtain ⟨h1, h2⟩ := time_travel_fork ha hb
  rw [h1, h2]

/-- **`time_travel_fork_sound`** — each forked continuation is bisimilar to the conservation oracle
from its reached state (`Cell.livingCell_sound` holds at both `a` and `b`). Time-travel-and-branch
produces two genuinely sound cells. -/
theorem time_travel_fork_sound {s a b : ChainedState} {ts₁ ts₂ : List Turn}
    (_ha : replayFrom (restore (checkpoint s)) ts₁ = some a)
    (_hb : replayFrom (restore (checkpoint s)) ts₂ = some b) :
    Sound livingCell conservationOracle a ∧ Sound livingCell conservationOracle b :=
  ⟨livingCell_sound a, livingCell_sound b⟩

/-! ## 4 — The same runtime character over the name-keyed record cell (`RecordCellLive`).

Checkpoint/restore/replay/fork over `RecChained`, conserving the `sumEquals` invariant.
Reuses `RecordCellLive.recReplay` + `recReplay_preserves_sumEquals`. -/

open Dregg2.Exec.RecordCell

/-- **Record-cell snapshot token** — captures the live `Value`, its program/method, and the receipt
log. The record-cell analog of `Cell.Snapshot`. -/
structure RecSnapshot where
  /-- The chain height observed at the checkpoint (`recHeight`). -/
  headHeight : Nat
  /-- The captured record value. -/
  value      : Value
  /-- The captured (fixed) program. -/
  program    : RecordProgram
  /-- The captured dispatch method. -/
  method     : Nat
  /-- The captured receipt chain. -/
  log        : List RecOp

/-- **Checkpoint the record cell** — serialize a running `RecChained` into a distinct token. -/
def recCheckpoint (s : RecChained) : RecSnapshot :=
  { headHeight := recHeight s, value := s.value, program := s.program,
    method := s.method, log := s.log }

/-- **Restore the record cell** — re-seed a fresh `RecChained` from a token. -/
def recRestore (snap : RecSnapshot) : RecChained :=
  { value := snap.value, program := snap.program, method := snap.method, log := snap.log }

/-- **`recCheckpoint_restore_roundtrip`** — `recRestore ∘ recCheckpoint = id`: a named snapshot
re-seeds exactly the checkpointed record carrier. -/
theorem recCheckpoint_restore_roundtrip (s : RecChained) : recRestore (recCheckpoint s) = s := rfl

/-- **`recReplay_deterministic_run`** — record-cell replay is a function: re-running the same op list
from the same state reproduces the same successor. -/
theorem recReplay_deterministic_run {s a b : RecChained} {ops : List RecOp}
    (ha : recReplay s ops = some a) (hb : recReplay s ops = some b) : a = b :=
  Option.some.inj (ha.symm.trans hb)

/-- **`recReplay_from_checkpoint`** — restore a record checkpoint and replay the op list: same
result as replaying from the original. -/
theorem recReplay_from_checkpoint (s : RecChained) (ops : List RecOp) :
    recReplay (recRestore (recCheckpoint s)) ops = recReplay s ops := by
  rw [recCheckpoint_restore_roundtrip]

/-- **`recTimeTravel_fork`** — fork at a record checkpoint of a `sumEquals fields c`-enforcing cell,
run two different op-suffixes; if both branches commit, both conserve `Σ fields = c`. The record-cell
analog of `time_travel_fork`, routed through `recReplay_preserves_sumEquals`. -/
theorem recTimeTravel_fork {cs : List StateConstraint} {fields : List FieldName} {c : Int}
    (hmem : StateConstraint.sumEquals fields c ∈ cs)
    {s a b : RecChained} {ops₁ ops₂ : List RecOp}
    (hprog : s.program = .predicate cs)
    (h0 : sumScalars s.value fields = some c)
    (ha : recReplay (recRestore (recCheckpoint s)) ops₁ = some a)
    (hb : recReplay (recRestore (recCheckpoint s)) ops₂ = some b) :
    sumScalars a.value fields = some c ∧ sumScalars b.value fields = some c := by
  rw [recCheckpoint_restore_roundtrip] at ha hb
  exact ⟨recReplay_preserves_sumEquals hmem s a ops₁ hprog h0 ha,
         recReplay_preserves_sumEquals hmem s b ops₂ hprog h0 hb⟩

/-! ## 5 — Non-vacuity (`#eval` / `example`): checkpoint→mutate→restore; replay; a fork diverges.

A checkpoint survives a mutation and restores; replay reproduces; a fork down two different suffixes
lands in two different states (genuine divergence) while both conserve the badge. -/

/-- A second authorized turn (actor 1 owns src 1 after the first transfer credited it). -/
def turnBack : Turn := { actor := 1, src := 1, dst := 0, amt := 10 }

-- checkpoint → mutate → restore recovers the original cell.
example : restore (checkpoint cell0) = cell0 := rfl
#eval ((cexec (restore (checkpoint cell0)) turn0).map (fun s => cellObs s) ==
       (cexec cell0 turn0).map (fun s => cellObs s))   -- true (restore recovers, then steps identically)

-- replay reproduces: the logged single-turn list from cell0 vs from its restored checkpoint.
#eval (replayFrom (restore (checkpoint cell0)) [turn0]).map cellObs   -- some 105 (conserved)
example : replayFrom (restore (checkpoint cell0)) [turn0] = replayFrom cell0 [turn0] := rfl

-- a FORK diverges: from the restored snapshot, suffix [turn0] vs suffix [] reach DIFFERENT states
-- (different log length) yet agree on the conserved badge (105 on both).
#eval (replayFrom (restore (checkpoint cell0)) [turn0]).map (fun s => s.log.length)  -- some 1
#eval (replayFrom (restore (checkpoint cell0)) ([] : List Turn)).map (fun s => s.log.length)  -- some 0 (diverged)
#eval (replayFrom (restore (checkpoint cell0)) [turn0]).map cellObs                  -- some 105
#eval (replayFrom (restore (checkpoint cell0)) ([] : List Turn)).map cellObs         -- some 105 (badge agrees)

/-- The fork genuinely DIVERGES on state (the two branches differ) while AGREEING on the badge — the
non-vacuity witness for `time_travel_fork`: it is not the trivial case where both suffixes coincide. -/
example :
    (replayFrom (restore (checkpoint cell0)) [turn0]).map (fun s => s.log.length)
      ≠ (replayFrom (restore (checkpoint cell0)) ([] : List Turn)).map (fun s => s.log.length) := by
  decide

-- record-cell: checkpoint→restore roundtrip + a committing replay on the live counter.
example : recRestore (recCheckpoint conserveCell) = conserveCell := rfl
#eval (recReplay (recRestore (recCheckpoint liveCounter)) [Dregg2.Exec.RecordCell.RecOp.addScalar "count" 1]).map recHeight
                                                                     -- some 1 (committed; chain advanced)

/-! ## Axiom hygiene — every runtime-character keystone is kernel-axiom-clean. -/

#assert_axioms checkpoint_restore_roundtrip
#assert_axioms checkpoint_restore_obs
#assert_axioms replay_deterministic_run
#assert_axioms replayFrom_conserves
#assert_axioms time_travel_fork
#assert_axioms time_travel_fork_agree_obs
#assert_axioms time_travel_fork_sound
#assert_axioms recCheckpoint_restore_roundtrip
#assert_axioms recReplay_deterministic_run
#assert_axioms recTimeTravel_fork

end Dregg2.Exec.CellRuntime
