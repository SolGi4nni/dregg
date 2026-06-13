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

## §B — RECORDS CARRY `(writes, burns)`: the forever-digest registry survives the crash cut.

The ledger model above covers the cell map. The node ALSO keeps **forever-digest registries**
(`persist/src/forever_digests.rs`): restart-surviving anti-replay carriers — a trustline draw
digest, a settle-unapplied compensation digest, a court resolved-evidence digest — burned exactly
once and refused for the rest of time. The Rust discipline is **durable-then-acknowledge**: the
digest is written in one committed redb transaction (fsync at the commit boundary) BEFORE the
in-memory insert is acknowledged, and the WHOLE set is reloaded at boot
(`load_forever_digests`). §B extends the record to `(writes, burns)` (`BRecord`), models the
durable registry as the append-only union of the log's burns (`registry`), and proves:

* `recoverB_eq_replayB` — the ledger convergence is untouched by the extension;
* `registry_cut_independent` — the registry reload sees no checkpoint cut (it is rebuilt from
  the WHOLE durable table, exactly `load_forever_digests`);
* **THE trustline forever-law lift** (`draw_replay_refused_across_crash`): a draw digest durably
  burned before the crash is REFUSED by the recovered trustline at ANY checkpoint cut — the Lean
  side of `forever_digests.rs`, composing `Trustline.draw_replay_refused` across recovery via
  `registry_burn_in_draws` (the reloaded registry is exactly the live carrier:
  `recovered_registry_faithful`, both inclusions).

### THE NAMED BOUNDARY (the post-commit/pre-ack window — read before trusting the theorem).

This model couples each turn's `writes` and `burns` in ONE durable record (the same-transaction
weld). The DEPLOYED node burns the digest in a SEPARATE redb transaction committed BEFORE the
in-memory ack: a crash between the digest commit and the turn's `CommitRecord` leaves the digest
durably burned while the turn is absent — the SAFE direction (the digest is refused after
recovery even though the draw never committed; no replay is ever ADMITTED). The CONVERSE — every
committed turn's digest is durably burned in the same transaction — is exactly the named node
closure "same-transaction burn weld" (docs/PERSISTENCE.md; HORIZONLOG `Node / runtime`). The
theorem's `hburn` hypothesis ranges over the durable registry, so it states exactly what
durable-then-acknowledge guarantees and no more.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); NO `sorry`/`:=True`/`native_decide`.
Pure, computable, `#guard`-checked non-vacuity (incl. a NEG witness). Verified with
`lake build Dregg2.Distributed.CrashRecovery`.
Differential: `persist/src/commit_log.rs`, `persist/src/forever_digests.rs`,
`node/src/blocklace_sync.rs::execute_finalized_turn`, `node/src/state.rs` (recovery overlay).
-/
import Mathlib.Data.List.Basic
import Dregg2.Apps.Trustline
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

/-! ## §B — records carry `(writes, burns)`: registry burns survive the crash cut.

See the header §B + THE NAMED BOUNDARY note. The forever-digest registry
(`persist/src/forever_digests.rs`) is append-only and reloaded WHOLESALE at boot — there is no
checkpoint/overlay split for it; the durable table IS the carrier. -/

namespace Dregg2.Distributed.CrashRecovery

universe v

/-- A forever digest (the 32-byte anti-replay digest, abstract; repo convention). -/
abbrev Digest := Nat

/-- **A durable commit record with its burns**: the touched-cell writes (the §A `Record`) PLUS the
forever digests this record's commit durably burned (durable-then-acknowledge: the burn commits
WITH the record — the same-transaction weld, the model's stated coupling). -/
abbrev BRecord (CellSt : Type u) := Record CellSt × List Digest

variable {CellSt : Type u}

/-- The ledger replay of a burn-carrying log: fold the WRITES (burns are ledger-neutral). -/
def replayB (base : Ledger CellSt) (log : List (BRecord CellSt)) : Ledger CellSt :=
  replay base (log.map Prod.fst)

/-- Recovery of the ledger from a burn-carrying log at checkpoint cut `k` (the §A
`checkpoint ⊕ overlay`, on the writes). -/
def recoverB (genesis : Ledger CellSt) (log : List (BRecord CellSt)) (k : Nat) : Ledger CellSt :=
  recover genesis (log.map Prod.fst) k

/-- **The §A convergence is untouched by the extension**: recovery of the burn-carrying log's
ledger equals its full replay, at any cut. -/
theorem recoverB_eq_replayB (genesis : Ledger CellSt) (log : List (BRecord CellSt)) (k : Nat) :
    recoverB genesis log k = replayB genesis log :=
  recover_eq_replay genesis (log.map Prod.fst) k

/-- **The durable forever-digest table** after the log: the append-only union of every record's
burns. This is what `load_forever_digests` reloads at boot — the WHOLE table, no cut. -/
def registry (log : List (BRecord CellSt)) : List Digest :=
  (log.map Prod.snd).flatten

/-- The registry is append-compatible: burning more records only appends digests. -/
theorem registry_append (l₁ l₂ : List (BRecord CellSt)) :
    registry (l₁ ++ l₂) = registry l₁ ++ registry l₂ := by
  simp [registry]

/-- **A burn survives the crash cut** — a digest burned anywhere in the durable log is in the
reloaded registry; in particular the ledger's checkpoint cadence is INVISIBLE to it
(`registry_cut_independent` below). Append-only: nothing is ever removed. -/
theorem registry_mono {log : List (BRecord CellSt)} {k : Nat} {d : Digest}
    (h : d ∈ registry (log.take k)) : d ∈ registry log := by
  have hsplit : registry log = registry (log.take k) ++ registry (log.drop k) := by
    rw [← registry_append, List.take_append_drop]
  rw [hsplit]
  exact List.mem_append_left _ h

/-- **The registry reload sees no checkpoint cut**: splitting the log at ANY `k` and re-uniting
reproduces the same table — the recovery-side statement that the forever table is rebuilt from
the WHOLE durable log, independent of where the ledger checkpoint fell. -/
theorem registry_cut_independent (log : List (BRecord CellSt)) (k : Nat) :
    registry (log.take k) ++ registry (log.drop k) = registry log := by
  rw [← registry_append, List.take_append_drop]

#assert_axioms recoverB_eq_replayB
#assert_axioms registry_mono
#assert_axioms registry_cut_independent

end Dregg2.Distributed.CrashRecovery

/-! ## §C — THE TRUSTLINE FOREVER-LAW LIFT: `draw_replay_refused_across_crash`.

`Apps/Trustline.lean` proves `draw_replay_refused_across_epochs`: a committed draw digest is
refused at every LATER STEP of the running trajectory. The node-side carrier of that law is the
durable forever-digest set (`forever_digests.rs`, namespace = trustline draws). Here we run the
trustline's adversarial schedule THROUGH the §B durable log — each step's record carries the
trustline cell's post-state as its write and the committed draw digest (if any) as its burn —
and prove the law ACROSS A CRASH: the reloaded registry is exactly the live draw carrier
(`recovered_registry_faithful`), the recovered cell is the pre-crash trustline
(`tlLog_recover`, any checkpoint cut), and a digest durably burned before the cut is refused by
the recovered line (`draw_replay_refused_across_crash`). -/

namespace Dregg2.Distributed.CrashRecovery

open Dregg2.Apps.Trustline

/-- The burns of one trustline step: a COMMITTED draw durably burns its digest
(durable-then-acknowledge — the burn is in the same durable record as the write, the §B stated
coupling); a refused draw and every other op burn nothing. -/
def tlStepBurns (s : SLine) : SOp → List Digest
  | .draw d a => if (drawS s d a).isSome then [d] else []
  | _ => []

/-- The trustline cell's id in the recovery ledger (a one-cell ledger suffices: the law is
per-cell). -/
def tlCell : CellId := 0

/-- The durable record of trustline step `i`: write = the post-state of the trustline cell,
burns = the step's committed draw digest (if any). -/
def tlRecord (s₀ : SLine) (sched : SSched) (i : Nat) : BRecord SLine :=
  ([(tlCell, trajS s₀ sched (i + 1))], tlStepBurns (trajS s₀ sched i) (sched i))

/-- The durable commit log of the first `n` trustline steps. -/
def tlLog (s₀ : SLine) (sched : SSched) (n : Nat) : List (BRecord SLine) :=
  (List.range n).map (tlRecord s₀ sched)

/-- One-step unfold of the trustline log (range-snoc). -/
theorem tlLog_succ (s₀ : SLine) (sched : SSched) (n : Nat) :
    tlLog s₀ sched (n + 1) = tlLog s₀ sched n ++ [tlRecord s₀ sched n] := by
  simp [tlLog, List.range_succ]

/-- A step's burned digest is in the post-step live carrier (the in-memory insert the durable
write precedes: durable-then-acknowledge). -/
theorem tlStepBurns_mem {s : SLine} {op : SOp} {d : Digest}
    (h : d ∈ tlStepBurns s op) : d ∈ (stepS s op).tl.draws := by
  cases op with
  | draw dg a =>
      simp only [tlStepBurns] at h
      cases hdr : drawS s dg a with
      | none => rw [hdr] at h; simp at h
      | some s' =>
          rw [hdr] at h
          simp only [Option.isSome_some, if_true, List.mem_singleton] at h
          subst h
          obtain ⟨tl', htl', hs'⟩ := drawS_spec hdr
          have hmem : d ∈ tl'.draws := (draw_records htl').2.2
          show d ∈ ((drawS s d a).getD s).tl.draws
          rw [hdr, Option.getD_some, hs']
          exact hmem
  | repay a => simp [tlStepBurns] at h
  | settle p => simp [tlStepBurns] at h

/-- A post-step live-carrier digest is either THIS step's burn or was already live (the converse
split: the carrier grows only by the step's burn). -/
theorem stepS_draws_split {s : SLine} {op : SOp} {d : Digest}
    (h : d ∈ (stepS s op).tl.draws) : d ∈ tlStepBurns s op ∨ d ∈ s.tl.draws := by
  cases op with
  | draw dg a =>
      revert h
      show d ∈ ((drawS s dg a).getD s).tl.draws → _
      cases hdr : drawS s dg a with
      | none => rw [Option.getD_none]; exact Or.inr
      | some s' =>
          rw [Option.getD_some]
          intro hd
          obtain ⟨tl', htl', hs'⟩ := drawS_spec hdr
          have hd' : d ∈ tl'.draws := by rw [hs'] at hd; exact hd
          obtain ⟨-, -, htl⟩ := draw_spec htl'
          rw [htl] at hd'
          rcases List.mem_cons.mp hd' with hd'' | hd''
          · subst hd''
            refine Or.inl ?_
            simp [tlStepBurns, hdr]
          · exact Or.inr hd''
  | repay a =>
      revert h
      show d ∈ ((repayS s a).getD s).tl.draws → _
      cases hrp : repayS s a with
      | none => rw [Option.getD_none]; exact Or.inr
      | some s' =>
          rw [Option.getD_some]
          intro hd
          obtain ⟨-, tl', htl', hs'⟩ := repayS_spec hrp
          have hd' : d ∈ tl'.draws := by rw [hs'] at hd; exact hd
          rw [repay_draws_fixed htl'] at hd'
          exact Or.inr hd'
  | settle p =>
      revert h
      show d ∈ ((settleS s p).getD s).tl.draws → _
      cases hst : settleS s p with
      | none => rw [Option.getD_none]; exact Or.inr
      | some s' =>
          rw [Option.getD_some]
          intro hd
          obtain ⟨-, hs'⟩ := settleS_spec hst
          rw [hs'] at hd
          exact Or.inr hd

/-- The last record's burns sit in the snoc'd registry (the membership bridge both inductions
use). -/
theorem registry_last_mem (s₀ : SLine) (sched : SSched) (k : Nat) {d : Digest}
    (h : d ∈ tlStepBurns (trajS s₀ sched k) (sched k)) :
    d ∈ registry (tlLog s₀ sched (k + 1)) := by
  rw [tlLog_succ, registry_append]
  refine List.mem_append_right _ ?_
  simpa [registry, tlRecord] using h

/-- **The reloaded registry only holds REAL burns**: a digest in the durable registry of the
first `n` steps is in the live carrier `(trajS s₀ sched n).tl.draws`. (The reload installs
nothing spurious.) -/
theorem registry_burn_in_draws (s₀ : SLine) (sched : SSched) :
    ∀ n {d : Digest}, d ∈ registry (tlLog s₀ sched n) → d ∈ (trajS s₀ sched n).tl.draws := by
  intro n
  induction n with
  | zero => intro d h; simp [tlLog, registry] at h
  | succ k ih =>
      intro d h
      rw [tlLog_succ, registry_append] at h
      rcases List.mem_append.mp h with h | h
      · exact stepS_draws_mono (trajS s₀ sched k) (sched k) (ih h)
      · -- the digest was burned AT step k: the in-memory insert follows the durable write.
        have hb : d ∈ tlStepBurns (trajS s₀ sched k) (sched k) := by
          simpa [registry, tlRecord] using h
        exact tlStepBurns_mem hb

/-- **The reload misses nothing**: a digest in the live carrier at step `n` was either durably
burned in the log or present at birth. With `registry_burn_in_draws` this gives
`recovered_registry_faithful`: the reloaded registry (∪ the birth registry) IS the live carrier,
membership-exactly — the boot rebuild loses no burn and invents none. -/
theorem draws_in_registry (s₀ : SLine) (sched : SSched) :
    ∀ n {d : Digest}, d ∈ (trajS s₀ sched n).tl.draws →
      d ∈ registry (tlLog s₀ sched n) ∨ d ∈ s₀.tl.draws := by
  intro n
  induction n with
  | zero => intro d h; exact Or.inr h
  | succ k ih =>
      intro d h
      have hreg : d ∈ registry (tlLog s₀ sched k) → d ∈ registry (tlLog s₀ sched (k + 1)) := by
        intro hm
        rw [tlLog_succ, registry_append]
        exact List.mem_append_left _ hm
      rcases stepS_draws_split h with hb | hold
      · exact Or.inl (registry_last_mem s₀ sched k hb)
      · rcases ih hold with h' | h'
        · exact Or.inl (hreg h')
        · exact Or.inr h'

/-- **`recovered_registry_faithful`** — the boot rebuild (reloaded registry ∪ birth registry)
has EXACTLY the membership of the live carrier at the crash point: no lost burn, no spurious
refusal. The Lean law of `load_forever_digests` + in-memory rebuild. -/
theorem recovered_registry_faithful (s₀ : SLine) (sched : SSched) (n : Nat) (d : Digest) :
    (d ∈ registry (tlLog s₀ sched n) ∨ d ∈ s₀.tl.draws)
      ↔ d ∈ (trajS s₀ sched n).tl.draws := by
  constructor
  · rintro (h | h)
    · exact registry_burn_in_draws s₀ sched n h
    · -- birth draws survive every step (registry monotone on the live side).
      induction n with
      | zero => exact h
      | succ k ih => exact stepS_draws_mono (trajS s₀ sched k) (sched k) ih
  · exact draws_in_registry s₀ sched n

/-- `replay` over an appended log is the composite fold (the snoc law the last-write read needs). -/
theorem replay_append (base : Ledger CellSt) (l₁ l₂ : List (Record CellSt)) :
    replay base (l₁ ++ l₂) = replay (replay base l₁) l₂ := by
  simp [replay, List.foldl_append]

/-- **The recovered trustline cell IS the pre-crash state** — for ANY checkpoint cut `k`, the
recovered ledger holds `trajS s₀ sched n` at the trustline cell (last-writer-wins over the
single-cell write stream; `n > 0` so at least one record wrote the cell). -/
theorem tlLog_recover (s₀ : SLine) (sched : SSched) (g : Ledger SLine) {n : Nat} (hn : 0 < n)
    (k : Nat) :
    recoverB g (tlLog s₀ sched n) k tlCell = some (trajS s₀ sched n) := by
  rw [recoverB_eq_replayB]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show replay g ((tlLog s₀ sched (m + 1)).map Prod.fst) tlCell = _
  rw [tlLog_succ, List.map_append, replay_append]
  -- the last record writes the trustline cell: the point update wins.
  simp [tlRecord, replay, applyWrites, upd, tlCell]

/-- **THE KEYSTONE — `draw_replay_refused_across_crash`.** A draw digest durably burned before
the crash (`hburn`: it is in the durable forever table the boot reload rebuilds from) is REFUSED
by the recovered trustline, for ANY checkpoint cut `k` and any amount: the recovered cell is the
pre-crash line (`tlLog_recover`), the reloaded registry is the live carrier
(`registry_burn_in_draws`), and `Trustline.draw_replay_refused` closes the gate. This is the Lean
side of `forever_digests.rs`'s durable-then-acknowledge contract — "forever" holds across a
process restart. (The post-commit/pre-ack window is the header's NAMED BOUNDARY: the model
couples burn and write in one record; the deployed separate-transaction burn is SAFE-direction
covered, and the converse weld is the named node closure.) -/
theorem draw_replay_refused_across_crash (s₀ : SLine) (sched : SSched) (n k : Nat)
    (g : Ledger SLine) {d : Digest}
    (hburn : d ∈ registry (tlLog s₀ sched n))
    {srec : SLine}
    (hrec : recoverB g (tlLog s₀ sched n) k tlCell = some srec)
    (amt : Nat) :
    drawS srec d amt = none := by
  -- the registry of the empty log is empty, so a burn forces n > 0.
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp [tlLog, registry] at hburn
    · exact h
  -- the recovered cell is the pre-crash trajectory state.
  have hsrec : srec = trajS s₀ sched n :=
    (Option.some.inj ((tlLog_recover s₀ sched g hn k).symm.trans hrec)).symm
  -- the burned digest is in the live carrier, so the draw refuses.
  have hd : d ∈ srec.tl.draws := hsrec ▸ registry_burn_in_draws s₀ sched n hburn
  unfold drawS
  rw [draw_replay_refused hd]
  rfl

#assert_axioms registry_burn_in_draws
#assert_axioms draws_in_registry
#assert_axioms recovered_registry_faithful
#assert_axioms tlLog_recover
#assert_axioms draw_replay_refused_across_crash

/-! ### §C non-vacuity (`#guard`-EXECUTED, both polarities).

A concrete schedule draws digest 5 (amount 3) at step 0 then settles 1; crash after 2 records.
The reloaded registry holds exactly the burn; recovery at every cut agrees; the burned digest is
REFUSED after recovery; a FRESH digest still draws (refusal is not fail-everything); and the NEG
witness — an AMNESIAC recovery that drops the registry (boot without `load_forever_digests`,
draws reset to `[]`) ADMITS the replay, so the durable table is load-bearing. -/

/-- Demo: a 10-line at birth. -/
def cDemoS0 : SLine := SLine.init 10

/-- Demo schedule: draw digest 5 amount 3 at step 0, then settle 1 forever after. -/
def cDemoSched : SSched := fun n => if n = 0 then .draw 5 3 else .settle 1

/-- Demo genesis ledger: empty. -/
def cDemoG : Ledger SLine := fun _ => none

-- the durable registry after 2 steps holds exactly the committed draw digest:
#guard registry (tlLog cDemoS0 cDemoSched 2) == [5]
-- recovery at every checkpoint cut (0 / 1 / 2) yields the same recovered cell:
#guard (recoverB cDemoG (tlLog cDemoS0 cDemoSched 2) 0 tlCell
        == recoverB cDemoG (tlLog cDemoS0 cDemoSched 2) 2 tlCell)
#guard (recoverB cDemoG (tlLog cDemoS0 cDemoSched 2) 1 tlCell
        == recoverB cDemoG (tlLog cDemoS0 cDemoSched 2) 2 tlCell)
-- the recovered cell is the pre-crash line (drawn 3, digest 5 burned, settled 1):
#guard ((recoverB cDemoG (tlLog cDemoS0 cDemoSched 2) 1 tlCell).map
          (fun s => (s.tl.drawn, s.tl.draws, s.settled))) == some (3, [5], 1)
-- THE LAW, executed: the burned digest is REFUSED after recovery (any amount):
#guard ((recoverB cDemoG (tlLog cDemoS0 cDemoSched 2) 1 tlCell).map
          (fun s => (drawS s 5 1).isNone)) == some true
-- POSITIVE companion: a FRESH digest still draws after recovery (refusal is targeted):
#guard ((recoverB cDemoG (tlLog cDemoS0 cDemoSched 2) 1 tlCell).map
          (fun s => (drawS s 6 2).isSome)) == some true
-- NEG witness: the AMNESIAC recovery (registry dropped, draws := []) ADMITS the replay —
-- the durable forever table is load-bearing, the theorem is not vacuous:
#guard ((recoverB cDemoG (tlLog cDemoS0 cDemoSched 2) 1 tlCell).map
          (fun s => (drawS { s with tl := { s.tl with draws := [] } } 5 1).isSome)) == some true

end Dregg2.Distributed.CrashRecovery
