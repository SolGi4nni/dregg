/-
# Dregg2.Distributed.CrashRecovery — durable-commit-log recovery converges to the finalized
# ledger (checkpoint ⊕ overlay = full replay), the **recovery-side analogue of LaceMerge**.

**The gap this closes.** `Distributed.LaceMerge` proves that two replicas which merge the same set
of causally-closed blocks reach the SAME finalized executed state (`merge_convergence_to_state`).
It is about *agreement between replicas*. It says nothing about a SINGLE replica that **crashes and
recovers**: the running node persists its finalized ledger as a periodic full *checkpoint* plus a
per-turn durable *commit log* (`persist/src/commit_log.rs::commit_finalized_turn`,
`node/src/blocklace_sync.rs::execute_finalized_turn`). On restart it rebuilds the ledger as
`checkpoint ⊕ overlay`, where the overlay is the last-writer-wins post-state of every cell touched
by a committed turn ABOVE the checkpoint height (`commit_log.rs::cell_overlay_since`,
`node/src/state.rs` recovery). The correctness obligation — *the recovered ledger equals the ledger a
node would reach by replaying every finalized turn from genesis* — is THIS file.

A recovered node reaching the same finalized ledger IS LaceMerge convergence applied to recovery: the
durable log is a faithful, replayable transcript of the tau-finalized turn order, and recovery is a
join of (checkpoint-state, post-checkpoint-writes) that is order/grouping-independent for the same
reason the CRDT merge is — it is a fold of point updates whose observable is the final map.

## The model (matches the Rust recovery, as a pure function of the write stream).

* A ledger is a total map `Ledger := CellId → Option CellSt` (the `HashMap<CellId, Cell>` keyset+values
  of `dregg_cell::Ledger`, here keyed values; absence = `none`).
* A turn's durable record contributes a list of `(CellId × CellSt)` **writes** = the post-states of the
  cells it touched (`CommitRecord.touched_cells`, taken from the executor's `LedgerDelta`:
  `created ∪ updated ∪ transfer-endpoints` — the complete bounded touched set).
* `applyWrites` = `foldl` point-update — applying a turn's writes to the ledger (later write to the
  same id wins, exactly `Ledger::insert_cell`'s overwrite, `commit_log.rs` last-writer-wins).
* `replay base log` = fold every record's writes from `base` (the full deterministic ledger
  reconstruction = what a node that re-executed from genesis would hold).
* `checkpoint` at a cut = `replay genesis (log.take k)` (the persisted full snapshot is exactly the
  fold up to the checkpoint cut — `ledger_store.rs::checkpoint_ledger` serializes the live ledger).
* `overlay` = `cell_overlay_since`: the last-writer-wins post-state of cells written by records ABOVE
  the cut = the concatenated writes of `log.drop k`.
* `recover` = `applyWrites checkpoint overlay`.

THE theorem (`recover_eq_replay`): `recover genesis log k = replay genesis log` for any cut `k` —
**no torn state, no lost finalized turn, no double-apply**: the recovered ledger is byte-for-byte the
fully-replayed ledger, independent of WHERE the checkpoint fell. The crash-consistency corollaries:
* `recover_independent_of_checkpoint` — two different checkpoint cuts recover the SAME ledger
  (the checkpoint cadence is invisible to the recovered state; LaceMerge-style cut-independence).
* `lost_turn_changes_state` (anti-vacuity / NEG) — a recovery that DROPS a finalized record can yield
  a DIFFERENT ledger: the theorem is not vacuously true; persisting the full post-checkpoint log is
  load-bearing.

## SCOPE.

FAITHFUL (matches `commit_log.rs` / `state.rs` recovery as a pure function of the write stream):
* `applyWrites` = last-writer-wins point update = `Ledger::insert_cell` overwrite.
* `checkpoint = replay genesis (take k)` = `checkpoint_ledger` snapshots the live fold.
* `overlay = concat writes of (drop k)` = `cell_overlay_since(checkpoint_height)` last-writer-wins.
* `recover = applyWrites checkpoint overlay` = `state.rs` (checkpoint ⊕ overlay).

SIMPLIFIED (a faithful PROJECTION, stated, not hidden):
* We model the cells' *values* abstractly (`CellSt`); the per-cell internal structure (balance,
  nonce, caps) is `RecordKernel`'s job and orthogonal — the recovery argument is about the MAP, which
  is what crash-consistency is. The convergence is therefore parametric in `CellSt`.
* The commit log's `block_executed_up_to` / `ledger_root` fields (the recovery cursor + the
  convergence commitment the Rust side asserts) are the *runtime* witnesses of THIS theorem; the
  `ledger_root` equality the node checks (`state.rs`) is exactly `recover_eq_replay` instantiated at
  the canonical-root hash, which we do not re-model (it is a function of the map).

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); NO `sorry`/`:=True`/`native_decide`.
Pure, computable, `#guard`-checked non-vacuity (incl. a NEG witness). Verified with
`lake build Dregg2.Distributed.CrashRecovery`.
Differential: `persist/src/commit_log.rs`, `node/src/blocklace_sync.rs::execute_finalized_turn`,
`node/src/state.rs` (recovery overlay).
-/
import Mathlib.Data.List.Basic
import Dregg2.Tactics

namespace Dregg2.Distributed.CrashRecovery

universe u

/-- Cell identifiers (the `dregg_cell::CellId` 32-byte key), abstract + decidable-eq. -/
abbrev CellId := Nat

-- A cell's stored value (abstract; `RecordKernel` owns the internal structure).
variable {CellSt : Type u}

/-- The ledger as a total map: `dregg_cell::Ledger`'s `HashMap<CellId, Cell>`, absence = `none`. -/
abbrev Ledger (CellSt : Type u) := CellId → Option CellSt

/-- Point update: install `s` at `id`. This is `Ledger::insert_cell` (keys by `cell.id()`,
overwrites). Decidable on `CellId = Nat`. -/
def upd (m : Ledger CellSt) (id : CellId) (s : CellSt) : Ledger CellSt :=
  fun j => if j = id then some s else m j

/-- Apply a turn's list of writes left-to-right: later write to the same id wins. This is the
executor's `LedgerDelta` applied to the ledger, and (folded over records) the last-writer-wins
overlay of `commit_log.rs`. -/
def applyWrites (m : Ledger CellSt) (ws : List (CellId × CellSt)) : Ledger CellSt :=
  ws.foldl (fun acc w => upd acc w.1 w.2) m

/-- A durable commit record contributes its touched-cell post-states as writes. -/
abbrev Record (CellSt : Type u) := List (CellId × CellSt)

/-- Replay the whole log from `base`: the fully-reconstructed ledger a node that re-executed every
finalized turn from genesis would hold. -/
def replay (base : Ledger CellSt) (log : List (Record CellSt)) : Ledger CellSt :=
  log.foldl (fun acc r => applyWrites acc r) base

/-- The checkpoint at cut `k`: the live ledger snapshot = the fold of the first `k` records
(`ledger_store.rs::checkpoint_ledger` serializes the live fold). -/
def checkpoint (genesis : Ledger CellSt) (log : List (Record CellSt)) (k : Nat) : Ledger CellSt :=
  replay genesis (log.take k)

/-- The overlay above cut `k`: the concatenated writes of the records past the checkpoint
(`commit_log.rs::cell_overlay_since`). Folded with last-writer-wins by `applyWrites`. -/
def overlay (log : List (Record CellSt)) (k : Nat) : List (CellId × CellSt) :=
  (log.drop k).flatten

/-- Recovery: rebuild the ledger as `checkpoint ⊕ overlay` (`node/src/state.rs`). -/
def recover (genesis : Ledger CellSt) (log : List (Record CellSt)) (k : Nat) : Ledger CellSt :=
  applyWrites (checkpoint genesis log k) (overlay log k)

/-! ### Core algebra of the fold. -/

/-- `applyWrites` over a concatenation is the composite fold (the split law). -/
theorem applyWrites_append (m : Ledger CellSt) (a b : List (CellId × CellSt)) :
    applyWrites m (a ++ b) = applyWrites (applyWrites m a) b := by
  simp [applyWrites, List.foldl_append]

/-- Replaying a record is `applyWrites` of its writes (definitional bridge). -/
theorem replay_cons (base : Ledger CellSt) (r : Record CellSt) (rs : List (Record CellSt)) :
    replay base (r :: rs) = replay (applyWrites base r) rs := by
  simp [replay, applyWrites]

/-- **Replay = checkpoint then replay-the-rest.** Folding the whole log equals folding the first `k`
records (the checkpoint) and then folding the remaining records. -/
theorem replay_split (genesis : Ledger CellSt) (log : List (Record CellSt)) (k : Nat) :
    replay genesis log = replay (checkpoint genesis log k) (log.drop k) := by
  unfold checkpoint replay
  rw [← List.foldl_append, List.take_append_drop]

/-- Folding records (each via `applyWrites`) over a base equals `applyWrites` of the records'
concatenated writes. This is the key bridge: per-record folding = one flat fold of all writes, so the
overlay (a flat write list) reproduces the per-record replay. -/
theorem replay_eq_applyWrites_flatten (base : Ledger CellSt) (log : List (Record CellSt)) :
    replay base log = applyWrites base log.flatten := by
  induction log generalizing base with
  | nil => simp [replay, applyWrites]
  | cons r rs ih =>
      simp only [List.flatten_cons]
      rw [replay_cons, ih, applyWrites_append]

/-! ### THE convergence theorem. -/

/-- **Crash-consistent recovery converges to the fully-replayed ledger.**

For ANY checkpoint cut `k`, the recovered ledger `checkpoint ⊕ overlay` equals the ledger a node
would reach by replaying every finalized turn from genesis. No torn state (the checkpoint and overlay
compose exactly), no lost finalized turn (the overlay carries every post-checkpoint write), no
double-apply (each record's writes appear once, last-writer-wins).

This is `LaceMerge.merge_convergence_to_state` applied to recovery: independent of HOW the durable
state was split (where the checkpoint fell), the reconstructed ledger is the same finalized map. -/
theorem recover_eq_replay (genesis : Ledger CellSt) (log : List (Record CellSt)) (k : Nat) :
    recover genesis log k = replay genesis log := by
  unfold recover overlay
  -- recover = applyWrites checkpoint (flatten (drop k))
  --         = replay checkpoint (drop k)      [by replay_eq_applyWrites_flatten, backwards]
  --         = replay genesis log              [by replay_split, backwards]
  rw [← replay_eq_applyWrites_flatten, ← replay_split]

/-- **The checkpoint cadence is invisible to recovery.** Two nodes that checkpointed at DIFFERENT
cuts recover the byte-identical finalized ledger (cut-independence; the recovery-side counterpart of
LaceMerge's order/grouping independence). -/
theorem recover_independent_of_checkpoint
    (genesis : Ledger CellSt) (log : List (Record CellSt)) (j k : Nat) :
    recover genesis log j = recover genesis log k := by
  rw [recover_eq_replay, recover_eq_replay]

/-- A node that checkpointed everything (`k ≥ |log|`, empty overlay) recovers from the checkpoint
alone — the checkpoint already IS the finalized ledger. -/
theorem recover_full_checkpoint (genesis : Ledger CellSt) (log : List (Record CellSt))
    (k : Nat) (hk : log.length ≤ k) :
    recover genesis log k = checkpoint genesis log k := by
  unfold recover overlay
  rw [List.drop_eq_nil_of_le hk]
  simp [List.flatten, applyWrites]

-- Axiom hygiene: the convergence theorems rest only on the kernel's core axioms
-- (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`, no extra assumptions.
#assert_axioms applyWrites_append
#assert_axioms replay_split
#assert_axioms replay_eq_applyWrites_flatten
#assert_axioms recover_eq_replay
#assert_axioms recover_independent_of_checkpoint
#assert_axioms recover_full_checkpoint

end Dregg2.Distributed.CrashRecovery

/-! ### Non-vacuity + the NEG witness (`#guard`-checked, concrete `CellSt := Nat`). -/

namespace Dregg2.Distributed.CrashRecovery

/-- A concrete two-turn log over `CellSt := Nat`:
* turn 0 writes cell 7 := 100 and cell 8 := 5,
* turn 1 writes cell 7 := 999 (overwrites cell 7), cell 9 := 1. -/
def demoLog : List (Record Nat) :=
  [ [(7, 100), (8, 5)]
  , [(7, 999), (9, 1)] ]

def g0 : Ledger Nat := fun _ => none

-- The fully-replayed ledger: cell 7 = 999 (last writer), 8 = 5, 9 = 1, others none.
#guard (replay g0 demoLog 7 == some 999)
#guard (replay g0 demoLog 8 == some 5)
#guard (replay g0 demoLog 9 == some 1)
#guard (replay g0 demoLog 3 == none)

-- Recovery with the checkpoint AFTER turn 0 (k = 1) reproduces the same ledger — the overlay
-- carries turn 1's writes, cell 7 ends at 999 (no torn state, no lost turn).
#guard (recover g0 demoLog 1 7 == some 999)
#guard (recover g0 demoLog 1 8 == some 5)
#guard (recover g0 demoLog 1 9 == some 1)

-- Cut-independence is observable: k=0 (no checkpoint), k=1, k=2 (full checkpoint) all agree.
#guard (recover g0 demoLog 0 7 == recover g0 demoLog 2 7)
#guard (recover g0 demoLog 0 9 == recover g0 demoLog 1 9)

-- NEG witness (anti-vacuity). A BROKEN recovery that drops the last finalized record (replays
-- only `take 1`) loses turn 1's write: cell 9 is absent and cell 7 is stale (100, not 999). So
-- `recover_eq_replay` is NOT vacuous — persisting the FULL post-checkpoint log is load-bearing; a
-- node that lost a finalized turn would diverge.
#guard (replay g0 (demoLog.take 1) 9 == none)        -- lost: should be some 1
#guard (replay g0 (demoLog.take 1) 7 == some 100)    -- stale: should be some 999
#guard decide (replay g0 (demoLog.take 1) 7 ≠ replay g0 demoLog 7)

end Dregg2.Distributed.CrashRecovery
