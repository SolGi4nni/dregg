# WORLD-PERSISTENCE-PLAN

## Native World persistence — M4 of the reflexive migration

starbridge-v2 today boots a fresh demo image every launch (`main.rs` →
`demo_world()`/`demo_genesis()`) and `starbridge-v2/Cargo.toml` carries **no
`dregg-persist`/`redb` dependency**. The embedded `World` (`world.rs:71-123`) is
purely in-RAM: the engine ledger, the `receipts` provenance log, the `dynamics`
stream, and the replayable `History` all evaporate on close. This plan makes the
World a **durable image**: close it, reopen it, land exactly where you were — by
welding the already-built node durability spine (`dregg-persist`'s redb commit
log + the checkpoint⊕overlay boot-recovery, `node/src/state.rs:676-767`) onto the
single commit seam the World already has (`commit_turn`, `world.rs:571`).

The machinery is built and verified; what is missing is the wire. The recovery
semantics are the node's, proven by `CrashRecovery.lean::recover_eq_replay`
(`metatheory/Dregg2/Distributed/CrashRecovery.lean:193-216`,
`#assert_axioms`-clean) — the World **inherits** that proof by reusing the same
overlay semantics (last-writer-wins `upsert_cell` over a checkpoint), not by
re-proving anything.

**Scope split (independent of the stratified-fixpoint question):**

- **DOMAIN-cell persistence is fully independent of M3 (UI-as-cells).** A turn
  that moves value or sets a domain field already flows through `commit_turn`;
  persisting it needs nothing from the UI migration. **Plan it concretely now
  (A, C, D below).**
- **UI-subgraph persistence rides M3.** Once UI camera-aim state is cells
  (`REFLEXIVE-MIGRATION.md §3`), those cells flow through the *same* commit log
  and `replay_to` reconstructs them for free. This is stated as a **rider** (B);
  no separate persistence mechanism is built for it.

---

## (A) Wire `dregg-persist` (redb) into the World

### A.0 The dependency add (gated)

`dregg-persist` is a path crate (`../persist`) pulling redb + serde + postcard —
no networking, no Lean link, no async. Add it gated to the existing
`embedded-executor` feature set so the headless `cargo test` surface keeps it:

```toml
# starbridge-v2/Cargo.toml, [dependencies]
dregg-persist = { path = "../persist", optional = true }
```

and add `dep:dregg-persist` to the `embedded-executor` feature list
(`Cargo.toml:134`). redb is a pure-Rust embedded ACID store (WAL + fsync); it
adds no heavy native tree. The `canonical_ledger_root` helper currently lives in
`node/src/blocklace_sync.rs:5305` (`pub(crate)`) — see the SEAMS section for
where it must move so both the node and the World call ONE implementation.

### A.1 The persistent handle on `World`

Add an **optional** durable backing to the `World` struct (`world.rs:71`):

```rust
/// The durable commit log + checkpoint store. `None` for an ephemeral world
/// (the demo/test/fork path — `World::new`); `Some` for an opened image.
/// Every successful `commit_turn` dual-writes here when present.
store: Option<dregg_persist::PersistentStore>,
/// The durable commit ordinal we last wrote (the `expected_ordinal` the next
/// `commit_finalized_turn` must supply). Mirrors the store's `commit_cursor`;
/// the store remains the single source of truth (the torn-state guard inside
/// `commit_finalized_turn` re-checks it).
commit_cursor: u64,
```

`World::new`/`with_costs`/`fork` set `store: None` — they stay purely in-RAM
(fork MUST never persist: it is a what-if copy, `world.rs:332`). Only
`World::open(path)` (A.3) populates `store`.

### A.2 The dual-write at `commit_turn` — O(change)

`commit_turn` (`world.rs:585`) already, on `Ok(receipt)`:

- computes `touched` cells *before* the commit (`world.rs:577`) — the exact
  change-set,
- advances the engine chain head, records onto the replay `History`
  (`world.rs:594`), bumps `height`, emits dynamics, appends the receipt.

Insert the durable dual-write **immediately after `history.record_commit`**
(so the post-state ledger + recorded root tooth are settled), gated on
`self.store.is_some()`:

```rust
if let Some(store) = self.store.as_ref() {
    // The exact change-set, already in hand: post-state of every touched cell.
    let touched_cells: Vec<Cell> = touched
        .iter()
        .filter_map(|id| self.engine.ledger().get(id).cloned())
        .collect();
    let record = dregg_persist::CommitRecord {
        ordinal: 0,                       // assigned by the store at the cursor
        height: self.height,
        block_id: [0u8; 32],              // single-image: no consensus anchor
        block_executed_up_to: self.height,
        turn_hash: receipt.turn_hash,
        creator: *receipt.agent.as_bytes(),
        receipt_hash: receipt.receipt_hash(),
        ledger_root: canonical_ledger_root(self.engine.ledger()),  // SEAM §1
        touched_cells,
    };
    match store.commit_finalized_turn(self.commit_cursor, &record) {
        Ok(assigned) => { self.commit_cursor = assigned + 1; }
        Err(e) => { /* fail-closed: see §A.2.1 */ }
    }
}
```

This is **O(change)**, not O(ledger): `touched_cells` is bounded by the turn's
effect count, exactly like the node's commit path
(`blocklace_sync.rs:3204-3225`, which this mirrors field-for-field). The store's
`commit_finalized_turn` (`commit_log.rs:241`) writes the record + secondary
indices in **one redb transaction** (ACID, never torn), guards the
`expected_ordinal == durable cursor` torn-state invariant, and is idempotent on
replay of an already-committed turn.

`touched` does NOT include a cell *destroyed* this turn (it is gone from the
ledger post-commit, so `filter_map` drops it) — matching the node, whose comment
(`blocklace_sync.rs:3211`) notes the destroyed cell's removal is carried by the
next checkpoint, not the overlay. (A cell-destruction image therefore needs the
checkpoint cadence of (C) to durably reflect the removal; until the next
checkpoint, recovery's overlay simply never re-inserts it — correct, because the
overlay only adds, and the checkpoint is where deletions land.)

### A.2.1 Fail-closed on a durable-write error

A durable write that fails is a **torn-image hazard**: the in-RAM world advanced
but the disk did not. Per *Green Or Bust*, this must not be swallowed. Two
honest options, ember-decision:

- **(default) fail-closed:** turn the `CommitOutcome::Committed` into a hard
  error path — the World refuses to acknowledge a commit it could not durably
  record. This keeps RAM and disk in lock-step (the node's discipline).
- **degraded-readonly:** drop `store` to `None` and surface a loud banner
  ("image is no longer durable"), letting the live session continue unpersisted.

Recommend default-fail-closed for the image; degraded-readonly is the explicit
opt-out for "I know, keep going". Either way the choice is **named with its
banner**, never silent.

### A.3 `World::open(path)` — boot recovery (the EXACT node recovery)

Replace the `demo_world()`/`demo_genesis()` boot in `main.rs` with
`World::open(path)`. It runs the identical recovery `node/src/state.rs:676-767`
runs:

```rust
pub fn open(path: &Path, costs: ComputronCosts) -> Result<World, OpenError> {
    let store = dregg_persist::PersistentStore::open(path)?;

    // 1. Load the latest full ledger checkpoint (or empty if none yet).
    let (mut ledger, checkpoint_height) = match store.load_latest_ledger_checkpoint()? {
        Some((h, l)) => (l, h),
        None         => (Ledger::new(), 0),
    };

    // 2. Apply the durable commit-log overlay since the checkpoint, in ordinal
    //    order, LAST-WRITER-WINS (remove-then-insert), exactly node::upsert_cell.
    let overlay = store.cell_overlay_since(checkpoint_height)?;
    for cell in overlay { upsert_cell(&mut ledger, cell); }   // = state.rs:425

    // 3. Verify convergence FAIL-CLOSED: the reconstructed canonical root MUST
    //    equal the root the last committed turn durably recorded.
    if let Some(expected) = store.recovered_ledger_root()? {
        let got = canonical_ledger_root(&ledger);             // SEAM §1
        if got != expected {
            return Err(OpenError::Divergent { got, expected }); // refuse to open
        }
    }

    // 4. Rebuild the in-RAM World on top of the recovered ledger:
    //    - engine seeded WITH the recovered ledger (DreggEngine::with_ledger),
    //    - per-agent chain heads re-primed from the recovered cells' receipt
    //      heads (so the next turn threads previous_receipt_hash correctly),
    //    - History/receipts/dynamics rebuilt from the durable commit log
    //      (§A.4),
    //    - height = checkpoint_height + overlay-implied turns (= commit_cursor),
    //    - commit_cursor = store.commit_cursor(), store = Some(store).
    ...
}
```

- Step 1+2+3 are **`recover = checkpoint ⊕ overlay`** verbatim — the same calls,
  the same `upsert_cell` (last-writer-wins, NOT the strict first-writer-wins
  `Ledger::insert_cell`, `state.rs:414-428`), the same fail-closed convergence
  panic→Err (`state.rs:732-754`). Because the semantics are byte-identical, the
  World inherits `CrashRecovery.lean::recover_eq_replay`: the recovered ledger
  equals the genesis replay (`replay genesis log`), so `World::open` lands on the
  state `History::replay_to(head)` would land on.
- Step 4 rebuilds the *view spine*. The chain-head re-priming mirrors
  `World::fork`'s seeding loop (`world.rs:364-369`): for each recovered cell with
  a recorded receipt head, `engine.executor().set_last_receipt_hash`.

### A.4 Rebuilding `History` / `receipts` from the durable log

The durable `CommitRecord`s carry `turn_hash`/`receipt_hash`/`ledger_root` but
**not the input `Turn`** (the commit log stores post-state cells + teeth, not the
replayable input). Two faithful ways to restore the in-RAM `History` (which
`replay.rs` needs for time-travel) and the `receipts` log (which the provenance
browser reads):

1. **Reconstruct the receipt log directly** from the commit records' ordinal
   order: `receipts` is an append-only `Vec<TurnReceipt>` and the records give
   the receipt hashes + agents + action counts. This restores the provenance
   feed without replay.
2. **Restore `History` as a checkpoint-anchored tape.** Because the durable log
   does **not** carry input turns, full from-genesis replay is not reconstructible
   from disk alone unless input turns are *also* persisted. Two honest sub-options
   (ember-decision, cross-ref `replay.rs:266-278`):
   - **(recommended) Persist input turns too.** Extend the durable record (or a
     sibling table) with the postcard `Turn` so `History` can be rebuilt
     verbatim and `replay_to(k)` works from any k post-recovery. This is the only
     way the *rewindable* image survives a close (not just the *latest* image).
   - **Checkpoint-only history.** Treat the recovered ledger as a new genesis
     (`History::with_costs` seeded from the recovered cells); time-travel then
     reaches only back to the last opened-image boundary. Cheaper, but loses
     pre-restart scrubbing.

The recommended path persists the input `Turn` alongside the post-state record so
that **close→reopen→scrub-to-any-past-turn** holds. This is the durable analogue
of the in-RAM `History` and is what makes the image truly rewindable rather than
merely resumable. (Note: the durable-`Turn` table is the one piece of new schema;
everything else reuses existing persist tables.)

---

## (B) The UI-subgraph rider (rides M3)

**Stated as a rider, not built now.** Once UI camera-aim state is cells
(`REFLEXIVE-MIGRATION.md §3`: `WorkspaceCell`/`ViewCell`/`PanelCell`/`GadgetCell`,
the generalized `BufferCell` two-tier pattern), persistence of the UI subgraph is
**automatic and requires no new code**:

- A UI mutation that is *witnessed* (the occasional `SetField` commit, the
  `BufferCell.commit()` discipline, `REFLEXIVE-MIGRATION.md §3.5`) flows through
  the **same** `commit_turn` → the **same** (A.2) dual-write → the same durable
  commit log. The UI cell's post-state lands in `touched_cells` like any domain
  cell.
- `World::open` (A.3) recovers UI cells indiscriminately with domain cells
  (the overlay does not distinguish cell kinds).
- `History::replay_to(k)` reconstructs *any* past image **including** the UI
  subgraph — exactly what `ui_snapshot.rs` already does over the in-RAM
  `History`, just pointed at the durable one.

So the rewindable **desktop** = `replay_to(k)` + `Registry::present`, with UI
cells riding the commit log. The only thing that gates it is M3 landing; M4's
persistence machinery is **identical** whether a committed cell is domain or UI.

**Free-draft caveat:** the in-memory free-edit draft (the gpui-free
`BufferDoc`-style tier that does NOT ride the ledger per keystroke) is, by
design, NOT persisted between its commits. On reopen the image resumes at the
last **witnessed** UI commit, not at an uncommitted mid-edit. The commit cadence
(blur / Nth-interaction / explicit-save / snapshot — `REFLEXIVE-MIGRATION.md §7
Q4`) is therefore also the **durability granularity** of UI state. Name it; do
not silently lose the draft.

---

## (C) Cheap time-travel — periodic durable + in-RAM checkpoints

Today `History::replay_to(k)` re-executes from genesis (`replay.rs:247-264`);
`replay_to_via_checkpoint(k, cp)` (`replay.rs:278`) can start from a checkpoint
step but still **replays** from there because the only cached thing is the root
*tooth*, not the ledger snapshot. Two checkpoint surfaces, both already
half-built:

### C.1 Durable ledger checkpoints (`persist`)

`PersistentStore::checkpoint_ledger(ledger, height)` (`ledger_store.rs:72`)
serializes the **full ledger** to redb keyed by height, updates the
latest-checkpoint metadata, and **co-drives commit-log compaction**
(`compact_below`) so the WAL stays bounded (`ledger_store.rs:98`). Drive it from
the World on a cadence:

```rust
const LEDGER_CHECKPOINT_INTERVAL: u64 = 256; // turns; tune empirically
// in commit_turn, after a successful durable dual-write:
if self.height % LEDGER_CHECKPOINT_INTERVAL == 0 {
    if let Some(store) = self.store.as_ref() {
        let _ = store.checkpoint_ledger(self.engine.ledger(), self.height);
    }
}
```

Plus an **explicit checkpoint on graceful close** (`World::close`/`Drop`-time
flush) so the latest image is always covered and recovery's overlay is short.
This is exactly the node's cadence model (`ledger_store.rs:9-14`): periodic +
shutdown checkpoint, startup restores latest checkpoint then overlays the gap.

### C.2 In-RAM ledger-snapshot cache (cheap live scrubbing)

For *live* time-travel (the scrubber, the meta-debug frozen frames), cache the
reconstructed *ledger* (not just the root) at periodic step indices in `History`,
so `replay_to_via_checkpoint(k, cp)` starts from the **nearest cached ledger
snapshot** and re-executes only `cp..k` — **O(turns-since-checkpoint)** instead
of O(turns-from-genesis). The decomposition is already proven sound
(`replay.rs:266-277`, the `recover_eq_replay` identity asserted in tests); this
just *caches the checkpoint ledger* rather than recomputing it. Concretely: add a
`BTreeMap<usize, Ledger>` of cached snapshots to `History` populated every Nth
`record_commit`, and have `replay_to`/the scrubber pick the nearest entry ≤ k as
the `checkpoint_step`.

The two checkpoint surfaces compose: C.1 is the *durable* base (survives close);
C.2 is the *live* base (cheap scrubbing within a session). Both feed the same
checkpoint⊕overlay decomposition.

---

## THE SEAMS (honest)

### SEAM §1 — three roots: BLAKE3 view-tooth vs `Ledger::root()` vs `canonical_ledger_root`

There are **three distinct commitments** in play today, and the durable
convergence check (A.3 step 3) demands they line up:

| Root | Basis | Where | Role |
|---|---|---|---|
| `World::state_root()` | BLAKE3 over sorted postcard cells, **folded with `height` + receipt-chain head** | `world.rs:284-301` | a fast *view* tooth (the corner hash) — advances with history |
| `dregg_cell::Ledger::root()` | sorted Merkle tree over `hash_cell` leaves | `cell/ledger.rs:684`, `rebuild_tree` | the **`History`/replay** "root tooth" (`replay.rs` uses this) |
| `canonical_ledger_root()` | BLAKE3 over sorted postcard cells, **flat (no height/receipt fold)** | `node/blocklace_sync.rs:5305` | the durable `CommitRecord.ledger_root` + the recovery convergence check (`state.rs:719-723`) |

The recorded durable tooth is `canonical_ledger_root` (flat). `World::state_root`
folds in `height` + the receipt head, so it is **not** equal to the durable tooth
and must NOT be used for the convergence check. The decision:

**Adopt `canonical_ledger_root` as the durable convergence root (recommended),
keep BLAKE3 `state_root` only as a fast view tooth.** Rationale:

- The recorded teeth in the durable commit log MUST match what recovery
  reconstructs (`state.rs:719-723` compares `canonical_ledger_root(ledger)` to
  `recovered_ledger_root()`). The World's dual-write (A.2) must therefore record
  `canonical_ledger_root(post_state)`, and `World::open` (A.3) must verify with
  the same function. This is non-negotiable for fail-closed convergence to hold.
- `state_root`'s height+receipt fold is a *view* feature (the corner hash
  advances every commit even if cells are unchanged); it is the wrong commitment
  for a content convergence check and should stay a view-only tooth, memoized per
  the efficiency plan's `state_root` memo (cross-ref `REFLEXIVE-MIGRATION.md §2.2
  (A)` / M1 — cache `(height, receipt_head) → [u8;32]`). Do NOT conflate the two.
- **Mechanical move required:** `canonical_ledger_root` is `pub(crate)` in
  `node/src/blocklace_sync.rs`. It must be lifted to a **shared** location both
  the node and the World call (e.g. a `pub fn` in `dregg-persist` or `dregg-cell`)
  so there is exactly ONE implementation. A second copy in starbridge-v2 would be
  a silent divergence risk (the durable check would compare a re-expression, not
  the canonical one) — the kind of laundered insecurity the *Don't Launder a
  Load-Bearing Insecurity* scar warns against. Lift it once; both callers import
  it.
- (The longer-horizon "faithful 8-felt Poseidon2 commitment" is the *protocol*
  commitment floor — `docs/FAITHFUL-STATE-COMMITMENT.md`; it is a separate,
  deeper concern than this view/recovery root and is not in M4's path. Flag, do
  not block.)

The cross-ref to the efficiency plan's `state_root` memo means: M1 memoizes the
BLAKE3 view tooth; M4 records the canonical tooth durably. They are different
roots with different jobs — both kept, neither conflated.

### SEAM §2 — recorder double-ledger subsumption

The World runs **two** executions per turn today: the authoritative
`engine.execute_turn` (`world.rs:585`) AND the replay-tape
`history.record_commit` re-execution over `record_ledger`/`record_exec`
(`world.rs:594`). The durable commit log **already carries post-states** (the
`touched_cells`), so it overlaps the replay tape's job. The subsumption move:
**collapse the 2× execution** by having the durable log feed `History` rather
than re-executing. BUT:

- The **genesis path** (`install_genesis`, `genesis_grant_cap`,
  `set_cell_program`, `genesis_open_permissions`, `deploy_factory` —
  `world.rs:400-561`) **bypasses the executor** and is **hand-mirrored** into the
  `record_ledger` to keep the recorded roots in lock-step. These out-of-band
  installs produce no `commit_turn` and therefore **no durable `CommitRecord`**.
- Consequence: **each out-of-band genesis install needs its own durable genesis
  record** (a `Genesis { cell }` row in a durable genesis table, or a synthetic
  commit record) so `World::open` reconstructs the genesis cells, not only the
  post-genesis turns. Without this, an opened image is missing every
  genesis-installed cell that was never subsequently touched by a turn.
- Recommended sequencing: in M4, **persist genesis installs durably** (a small
  genesis table mirroring `History::record_genesis`, `replay.rs:198-206`) FIRST,
  then the per-turn dual-write. The double-ledger *collapse* is a **separate,
  later** efficiency move (it removes the in-RAM `record_ledger`/`record_exec`
  once the durable log + genesis table fully subsume the replay tape) — do NOT
  bundle it into the persistence weld, because the replay tape is currently the
  source of the `Ledger::root()` teeth `replay.rs` verifies against. Collapsing
  it is *Improve Don't Degrade* territory: stage it, do not rip it out under M4.

### SEAM §3 — the CrashRecovery burn-window named boundary

`CrashRecovery.lean::recover_eq_replay` is proven SAFE-direction-only over the
finalized log; the converse "same-transaction burn weld" (a turn that burns an
anti-replay digest landing its commit record AND its digest atomically) is a
**named node closure** (`commit_finalized_turn_with_burns`,
`commit_log.rs:260`). The single-image World does **not** today emit forever-digest
burns (trustline draws / court slashes are node-federation concerns), so M4 uses
the plain `commit_finalized_turn` (no burns) — but the boundary is **named here**:
if the desktop image ever grows anti-replay digests (e.g. a UI cell whose commit
burns a one-shot promise nullifier, `project-partial-turn-promises`), it must
switch to `commit_finalized_turn_with_burns` so the burn and the commit are
atomic across a crash. Until then: named boundary, not crossed.

---

## THE ORDERED TASK LIST

1. **Lift `canonical_ledger_root` to a shared `pub fn`** (SEAM §1) — one
   implementation, called by both node and World. *No behavior change; pure move.*
2. **Add the `dregg-persist` dep** (A.0), gated on `embedded-executor`.
3. **Add `store` + `commit_cursor` to `World`** (A.1); `None` for
   `new`/`with_costs`/`fork`.
4. **Durable genesis table + mirror every genesis install** (SEAM §2): each
   `install_genesis`/`genesis_grant_cap`/`set_cell_program`/
   `genesis_open_permissions`/`deploy_factory` writes a durable genesis record
   when `store.is_some()`.
5. **Dual-write at `commit_turn`** (A.2) recording `canonical_ledger_root`
   post-state + `touched_cells` (O(change)); fail-closed on durable-write error
   (A.2.1).
6. **Persist input `Turn`s** (A.4 recommended) so `History` is rebuildable for
   rewind.
7. **`World::open(path)`** (A.3): checkpoint-load → overlay via `upsert_cell` →
   fail-closed convergence check via the shared `canonical_ledger_root` → rebuild
   engine/History/receipts/dynamics/chain-heads.
8. **Periodic + on-close durable checkpoints** (C.1) driving `checkpoint_ledger`.
9. **In-RAM ledger-snapshot cache in `History`** (C.2) so
   `replay_to_via_checkpoint` starts from the nearest cached snapshot.
10. **Boot `main.rs` from `World::open(path)`** instead of `demo_world()`
    (first-run with no store → seed the demo genesis, then persist it).
11. *(later, separate)* **Collapse the recorder double-ledger** (SEAM §2) once the
    durable log + genesis table fully subsume the in-RAM replay tape.
12. *(rider, M3)* **UI-cell persistence** falls out automatically (B); no M4 code.

---

## VERIFICATION

- **Close-and-reopen restores the exact image.** Build a world, commit N turns
  (and some genesis installs), record `canonical_ledger_root(ledger)`, drop it,
  `World::open(path)`, assert the reopened ledger's `canonical_ledger_root`
  equals the recorded one **and** every cell (domain — and UI, post-M3) matches
  by id+content. This is the headline test.
- **Recovered root matches recorded tooth, fail-closed.** Assert `World::open`
  returns `Err(Divergent)` (refuses to open) when the durable
  `recovered_ledger_root` disagrees with the reconstructed
  `canonical_ledger_root` (corrupt-store fixture: hand-edit a checkpoint cell).
  Mirrors `state.rs:732-754`. A passing-when-corrupt open is a soundness failure.
- **Checkpoint-start works (durable).** Write a checkpoint at height `h`, commit
  more turns past `h`, drop, reopen: assert recovery loads the checkpoint at `h`
  and overlays only the `>h` records (`cell_overlay_since(h)`), landing on the
  same root as a from-genesis replay — the `recover_eq_replay` identity at the
  durable layer.
- **Checkpoint-start works (live).** Assert `replay_to_via_checkpoint(k, cp)`
  using the C.2 in-RAM cached snapshot lands on the same verified
  `Ledger::root()` tooth as `replay_to(k)` from genesis (the existing
  `replay.rs` test extended to use the cache), and re-executes only `cp..k`.
- **Genesis cells survive.** A genesis-installed cell never touched by a turn is
  present after reopen (catches the SEAM §2 hand-mirror gap).
- **Rewind survives a close** (A.4 recommended): after reopen, `replay_to(j)`
  for `j < head` reconstructs a verified past image (requires persisted input
  turns; the checkpoint-only variant would instead reach back only to the reopen
  boundary — assert whichever was chosen, do not leave it ambiguous).
- **Non-vacuity:** the convergence assertion must fire on a genuinely corrupt
  store (true) and pass on a genuine one (false) — prove both, per *Don't Launder
  Vacuity*.

---

*( ◕‿◕ ) a closing couplet, since the spine already knows how to come back:*
*the log remembers every cell the turn last wrote —*
*so close the lid; on reopen, the image floats.*
