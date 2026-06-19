# WHAT WE HAVE → HOW IT MOVES
## The migration + architecture analysis for a self-hosting, persistent, rewindable, functional-substrate-driven reflexive starbridge image

---

## 1. EXECUTIVE SUMMARY

starbridge-v2 today is a single gpui `Render` impl (`Cockpit`, `cockpit.rs:236`) holding a `world: Rc<RefCell<World>>` plus ~49 sibling plain-Rust fields, whose `render()` (`cockpit.rs:6217`) rebuilds the entire three-pane element tree from scratch on every `cx.notify()` — and gpui is pull-based, so the cost is per-interaction, not per-vsync, but each interaction pays a full from-scratch projection of the whole ledger. Underneath, the substrate is *already the right shape*: the executor is a pure journal-rollback transition (`turn/src/executor/execute.rs:152`, "no full ledger clone"), `World::commit_turn` is change-scoped (`world.rs:571`, snapshots only `touched_cells`), the dynamics log is a textbook append-only delta stream with a `since(cursor)` API (`dynamics.rs:136-179`), `Registry::present` is a pure per-target view function (`presentable.rs:881`), `ui_snapshot.rs` stores a tiny re-derivable `{focus,kind,WitnessCursor{height,receipt_head}}` (verified above, `ui_snapshot.rs:59-93`), and `replay.rs` gives root-verified time-travel (`replay_to`, `replay_to_via_checkpoint`, `fork_at`). The single biggest efficiency risk is that **every UI interaction re-projects O(whole-ledger + whole-receipt-log)** — concretely `state_root()` postcard-serializes + BLAKE3-hashes *every cell* just to draw a 12-char hash in the corner (`world.rs:284-301`, verified), `sorted_cells()` re-collects+re-sorts the `HashMap` ledger at 15+ independent call sites per frame, and `Registry::present`/`OcapGraph::build` rescan all cells×caps — with essentially **zero projection-layer memoization**. This is fine for a 4-year-old clicking a small image, but it is the wall the moment UI state *itself* becomes thousands of cells (the self-hosting endgame). The win is already designed-for and not yet wired: the dynamics `since(cursor)` delta and the `WitnessCursor` identity are exactly the dirty-set and the memo key an incremental projector needs, but the cockpit consumes neither (`grep since( cockpit.rs` → zero). The three highest-leverage first moves, in order: **(1)** memoize `state_root` and join `dynamics().since(cursor)` to render so the UI is a delta-fold not a re-projection (pure weld, the efficiency-proving milestone); **(2)** key a projection memo on `(FocusTarget, viewer, WitnessCursor)` so only dynamics-touched cells re-project, which *simultaneously* makes time-travel scrubbing cheap; **(3)** promote semantic UI state from Rust fields into dregg cells using the proven `BufferCell` two-tier pattern, which makes persistence and rewind fall out of the existing `History`/`replay` spine for free. Do the efficiency proof *first* — driving UI from cells without it merely makes the existing O(ledger)-per-frame disaster worse.

---

## 2. THE EFFICIENCY ARCHITECTURE (the central concern)

### 2.1 The current cost truth — what is O(ledger) per interaction today

gpui re-runs the *whole* `Cockpit::render` closure on any `cx.notify()`, and there are hundreds of notify sites (nearly every handler in `cockpit.rs:822-2033`). Per repaint, with **no memoization**:

| Hot path | Where | Cost |
|---|---|---|
| `state_root()` — postcard + BLAKE3 over **every cell**, run in `rail_header` to draw a 12-char hash | `world.rs:284-301` (verified: sorts all cells, hashes each), called `cockpit.rs:2069`, `:3858` | O(cells · cell_bytes) — the single most expensive recompute |
| `sorted_cells()` — full `HashMap` drain + sort, **15+ independent call sites** | `cockpit.rs:6293-6296`; callsites `517,780,…,3431` | O(n log n) × 15 per frame (HashMap → nondeterministic order forces re-sort) |
| `Registry::present` — clones the focused `Cell`, rebuilds the *entire* presentation set (reflect + `InspectAct` vocabulary + `cell_provenance` receipt scan) | `presentable.rs:863-888` — doc says "reads the live world fresh every call (never a cache)" | O(cell + receipt-log) per moldable frame |
| `OcapGraph::build` / `OrganSurvey::build` — rescan all cells × all cap edges | `cockpit.rs:4531,4617` | O(cells · caps) per visible tab |
| `ReplayPanelModel::build` — replay-to-cursor + two more full replays for the diff, **rebuilt every frame** | `replay.rs:711,733`; `cockpit.rs:4399` | ~O(history · ledger) per frame on the Replay tab |

**Net:** cost is O(whole ledger + whole receipt log) per interaction, *independent of how small the actual change was*. The only caches today are `self.cells` (a sorted vec refreshed on commit at `cockpit.rs:779-781` — but bypassed by most callers who re-sort fresh) and the live receipt feed's dedup-and-count gate.

### 2.2 The target reactive/incremental design — the FRP shape

The producer (`dynamics().since(cursor)`) and the consumer (gpui render) both exist; they are simply **not joined**. Each `WorldEvent` names its changed `CellId` (`CellBorn`, `BalanceFlowed`, `CapabilityGranted/Revoked`, `FieldSet`, `SurfaceDamaged{region_count}` — `dynamics.rs:19,66-75`). The design is a **delta-fold keyed on the witness identity that already exists**:

**(A) Memoize `state_root`.** Cache `(height, receipt_head) → [u8;32]` on the `World`, or fold per-touched-cell deltas at `commit_turn` (reuse the `touched_cells` set already computed at `world.rs:577-581`). `rail_header` then reads a cached root instead of re-serializing the ledger every frame. Pure reuse — the `receipt_head` is *already* the fold tooth (`world.rs:297-299`, verified) and *already* the `WitnessCursor` field (`ui_snapshot.rs:65-66`).

**(B) Promote `self.cells` to the sole sorted source and invalidate it off the stream.** Either back the ledger with a `BTreeMap` (kills the nondeterministic-order re-sort), or maintain `self.cells` incrementally: a `CellBorn`/`CellDestroyed` event from `since(cursor)` mutates the cached vec; everything else leaves it untouched. Kills the 15× re-sort.

**(C) Per-cell projection cache keyed on the dynamics dirty-set.** Give `Cockpit` a `dynamics_cursor: usize`. Each render:
```
for ev in world.dynamics().since(self.cursor) {
    // BalanceFlowed/FieldSet → invalidate just that cell's row+inspector
    // CellBorn/Destroyed     → insert/remove one rail entry
    // SurfaceDamaged         → repaint only region_count regions
}
self.cursor = world.dynamics().cursor();
```
Cache `(FocusTarget, viewer, WitnessCursor) → Vec<Presentation>` wrapping the **unchanged-pure** `Registry::present`. A presentation is a pure function of `(target, viewer, state)`, so it is valid exactly while `WitnessCursor::is_live_head` holds (`ui_snapshot.rs:89`, verified) — a new receipt advances the head, and only foci named by the delta invalidate. This turns per-frame O(ledger) into O(changed-cells).

**(D) The cache key *is* the time-travel coordinate.** Because the memo key is a `WitnessCursor`, rewinding = pointing the *same* memoized projector at a past cursor via `History::replay_to`, and every unchanged cell's cached projection is reused across a scrub. Efficiency and time-travel are one mechanism.

**What is reused unchanged:** the pure `reflect::*`/`Registry::present` projections (wrapped in a memo, never rewritten), the `since(cursor)` delta API, the `WitnessCursor`/`Liveness` identity, the live-feed notify gating. **What changes:** ledger backing (`HashMap`→`BTreeMap` or a sorted index), a memoized/incremental `state_root`, a per-cell projection cache, and splitting the one giant `Cockpit` Render into sub-view gpui Entities so a notify touching one cell repaints one pane.

### 2.3 The seams (efficiency)

1. **Notify granularity vs. projection.** Even with a per-cell cache, gpui re-runs the whole Render *closure* (the `div().child(...)` walk) on any notify unless the Cockpit is split into child Entities. This is real surgery on the "one uniform inspector renders everything" invariant.
2. **"Cell version" does not exist.** Invalidation derives entirely from the dynamics stream, so **cache soundness depends on the dynamics log being complete** — every `commit_turn` effect must emit a `WorldEvent` naming the cell. Auditing event-completeness is load-bearing; one un-emitting executor path = a stale projection that survives.
3. **`state_root` is not natively incremental** (BLAKE3 over sorted cells re-hashes the suffix). Cheapest correct move is *memoize-and-recompute-on-any-commit*, not true incrementality. (True incrementality wants the metatheory's sorted-Poseidon2 accumulator — but that is the protocol commitment, not this view-layer root.)
4. **Viewer-parametrized invalidation is non-local.** `InspectAct::build` projects cap badges *per viewer*, so a `CapabilityGranted/Revoked` *anywhere* can change another cell's affordance badges. The per-cell dirty-set is insufficient for the Affordances presentation — cap-graph deltas have non-local reach. Key on viewer *and* invalidate the affordance cache on any cap-edge event.
5. **The reflexive fixpoint (§5.2 deep open question):** when UI state is cells, the projector projects cells that include its own view state — needs a stratification so a UI-cell change doesn't infinitely re-invalidate its own projection.

---

## 3. THE REFLEXIVITY MIGRATION (cockpit → UI cells)

### 3.1 The exact field partition

The `Cockpit` struct (`cockpit.rs:236`, verified) holds ~50 fields in three classes:

**CELL-CANDIDATES (semantic "camera-aim" state — conserves nothing, names a position in the witnessed graph; the `{focus,kind,cursor}` shape `ui_snapshot` already proved re-derivable):**
- `selection` (`:241`, `Selection` enum `:69-73`)
- `tab` (`:247`, `Tab` enum `:78-173`, 24 variants)
- `moldable_focus` (`:467`) / `moldable_present_idx` (`:470`) / `moldable_query` (`:473`)
- `inspect_act_focus` (`:477`)
- `web_cells_opened` (`:376`) / `web_cells_viewer_rights` (`:383`)
- `links_here_focus` (`:404`) / `links_here_depth` (`:409`) / `links_here_viewer_rights` (`:419`)
- `powerbox_app` (`:427`) / `powerbox_confer_rights` (`:434`)
- `sim_target_idx` (`:452`) / `sim_effect_idx` (`:455`)
- `workspace_target_idx` (`:486`) / `lane_idx` (`:489`)
- `replay_cursor` (`:258`, verified) / `breakpoints` (`:254`, verified)

**gpui-LOCAL / engine-LOCAL (must NOT move into cells — they ARE the renderer or the live-image handle):**
- `world: Rc<RefCell<World>>` (`:237`, verified) — the substrate itself; cannot be a cell-in-the-ledger.
- `focus: FocusHandle` (`:352`) — a gpui keyboard-routing resource.
- `cells: Vec<CellId>` (`:240`, verified) — a derived sorted cache.
- `frame_seq` (`:287`); `live_node/live_stream/live_feed/live_snapshot` (`:359-370`) — OS sockets + background threads.
- `killer_demo: Option<HeadlineDemo>` (`:333`) — owns a *second* metered world.
- `pending_seed` (`:344`).

**MIDDLE class (already part-cell-backed — the seam to generalize):**
- `editor_buffer: BufferCell` (`:300`) + `editor_buffer_cap` (`:304`) — **the proof of concept** (below).
- `terminal: TerminalCell` (`:310`); `shell: Shell` (`:276`) + `surface_caps` (`:282`); `workspace: Workspace` (`:484`); `sim_draft: IntentDraft` (`:449`); `lane_*` (`:493-500`).

### 3.2 The proven pattern to generalize: `BufferCell`'s two-tier split

`BufferCell` is the existing demonstration that UI state can be cell-backed without paying ledger cost per keystroke (verified `buffer.rs:310-358`):
- Its visible `BufferDoc{text,cursor}` is gpui-free and **free / in-memory** (`doc_mut`, `buffer.rs:279`).
- Its authenticated **digest** rides a backing cell field `fields[BUFFER_DIGEST_SLOT]` (`stored_digest`, `buffer.rs:312-317`, verified), advanced only by `commit()` through a real cap-gated `Effect::SetField` turn (`buffer.rs:330-358`, verified).
- Its **revision = the cell's nonce** (`buffer.rs:322-328`, verified) — the receipt chain *is* the edit history.

This is exactly the **"free UI edits stream + occasional witnessed commit"** the vision wants.

### 3.3 The UI-cell kinds (thin newtypes over real cells)

- **`WorkspaceCell`** — `{active_tab, layout}` in cell fields. Absorbs `tab`, `workspace_target_idx`.
- **`ViewCell`** — `{focus, present_idx, viewer_rights}`. Absorbs the `moldable_*` + `inspect_act_focus` + `web_cells_*` + `links_here_*` triple.
- **`PanelCell`** — per-tab cursor/index. Absorbs `sim_target_idx`, `lane_idx`, `replay_cursor`, `breakpoints`.
- **`GadgetCell`** — an in-progress `IntentDraft`/`Composite`. Absorbs `sim_draft`, `lane_*`.

Each keeps a `BufferDoc`-style free in-memory draft and rides an authenticated slot in a backing cell. The `Cockpit` struct then *shrinks* to a handful of UI-cell handles + `world` Rc + `FocusHandle`.

### 3.4 `render()` becomes `present(workspace_subgraph)`

The cockpit's job becomes: read the `WorkspaceCell` for the active tab + the `ViewCell` for focus/lens, then call the **existing** `Registry::present(focus, viewer)` (`presentable.rs:881`) — which already *is* `render(cell)` (already cap-viewer-parametrized, already called per-frame in the Moldable tab at `cockpit.rs:2787,2810`). The 24-arm `Tab` match stays; only its *selector* moves from a Rust field to a cell read. Nothing in the projection layer changes.

### 3.5 The UI-mutation weight class

A tab-switch / focus-cycle **conserves nothing** — no balance moves. It is the `EmitEvent`/`SetField` weight class (`world.rs:772,800`), exactly as a buffer keystroke is. Free edits stay in-memory + `cx.notify()`; a witnessed **commit** (the thing that makes the image durable/rewindable) lands a `SetField` turn only occasionally — on blur, on snapshot, on explicit save — the `BufferCell.commit()` discipline generalized. UI stays fast; only the occasional checkpoint is O(turn).

---

## 4. THE FRACTAL META-DEBUG

### 4.1 What "suspend + insert a meta-level over it, recursively" maps to

**"Suspend"** maps to a **checkpoint cursor** (`WitnessCursor::at_head`, `ui_snapshot.rs:79`, verified), **not** a fork-clone. The live `World` keeps running; the meta-level captures the cursor at the moment of suspension and presents the *frozen* world at that cursor as an inspectable object. The frozen world is re-derived on demand via root-verified `History::replay_to` (`replay.rs:247`) — reusing the existing replay trust anchor — so "the paused world" is never a second mutable copy; it is a cursor the meta-level re-projects through.

The new object:
```
MetaDebugView { target_cursor: WitnessCursor, sub_cockpit_state, scrub_cursor }
```
It owns the existing time-travel scrubber (`replay_cursor` + `ReplayPanelModel`) bound to the *frozen* world rather than the live head, plus the existing per-turn debugger (`debug.rs:456`, `debug_turn` re-executing each effect-prefix on a fresh clone), `RefusalExplanation` (`debug.rs:173-393`), `inspect_witness` (`debug.rs:604`), and `simulate`/`fork_at` what-if branches off the suspended frame.

### 4.2 How it nests — the one-arm `Registry` extension

The keystone: make the meta-level **itself a `FocusTarget`**. Today `FocusTarget` has one variant `Cell(CellId)` (`presentable.rs:849`), with the doc explicitly noting "new object kinds add one arm." Add:
```
FocusTarget::DebugFrame(MetaLevelId)   // and FocusTarget::World / ::Cockpit
```
plus a `MetaDebugView impl Presentable`. Then **"debug the debugger" is literally focusing the inspector on the meta-level's own `MetaDebugView`** — recursion via the *same* `present()` dispatch, no new mechanism. Each meta-level carries its own `WitnessCursor` into the *same* durability log; the `History`/`replay_to` anchor is shared (**one tape, many cursors**), so meta-level N+1 scrubbing is just another cursor into the log meta-level N was suspended at.

The Cockpit's flat `Tab` sibling-panels (`cockpit.rs:78-173`) become a **`MetaStack: Vec<MetaDebugView>`** with push/pop semantics. The palette/keybindings that switch tabs gain push/pop instead.

### 4.3 How time-travel integrates

A meta-level's `scrub_cursor` *is* a `WitnessCursor`; scrubbing re-runs `replay_to` at the new height and re-projects. Because the suspended frame is itself pinned at a cursor, scrubbing the meta-level moves through the *same* log the live system writes — **a meta-debug session is itself rewindable**. The `Liveness` trichotomy (`ui_snapshot.rs:116-126`, verified) answers "am I looking at the live system or a frozen past one?" *by construction*: a meta-view honestly stamps `Live` / `ReplayedDeterministic` / `ReconstructedApproximate`. A what-if branch (`fork_at` off a frozen frame) produces a turn with a *different* hash — the debugger already flags this honesty (`debug.rs:30-35`) — so the meta-level's branch is provably a different timeline, surfaced via `Liveness`.

### 4.4 The design of the button

> **Suspend & inspect:** capture `WitnessCursor::at_head(world)`, construct a `MetaDebugView` focused on it, push it onto the `MetaStack` as the active `FocusTarget`. The recursive button *inside* that view captures the *meta-view's own* cursor and pushes another.

### 4.5 The seams (meta-debug)

1. **Efficiency is the load-bearing seam, NOT solved today.** Each meta-level naively triggers another O(history·ledger) replay per frame (`ReplayPanelModel::build` rebuilt at `cockpit.rs:4399`); N nested levels = N× that. The honest fix is the §2 memoization: pin a checkpoint ledger *once* via `replay_to_via_checkpoint` (`replay.rs:278`, the checkpoint⊕overlay decomposition is already proven sound) and overlay only the post-checkpoint delta; memoize projections keyed by `(focus, kind, WitnessCursor)`. Neither cache exists yet.
2. **The self-hosting knot (§3).** To "debug the debugger" as a *real witnessed object*, the cockpit's own state (`replay_cursor`, `breakpoints`, `sim_draft`) must become cells — raising conservation/authority questions (does a breakpoint cell conserve value? what authority mutates it? → §3.5: it is the `SetField` weight class, conserves nothing).
3. **"Suspend" semantics (ember-decision).** Checkpoint-cursor freezes a *past* world honestly; if the user wants the live system to literally *halt* (stop accepting turns) while inspected, that is a different primitive the live `World` does not have (`fork()` gives an isolated *divergent* copy, not the live system).
4. **Nesting termination + cost ceiling.** Each meta-level needs a stable `MetaLevelId`; the recursion needs a base case and a replay-storm cost ceiling.

---

## 5. PERSISTENCE

### 5.1 Native (the `dregg-persist` weld)

**The biggest gap is absence, not difficulty.** The embedded `World` is purely in-memory — `world.rs:71-123`, and `starbridge-v2/Cargo.toml` has **no `dregg-persist`/`redb` dep at all**. Every launch boots a fresh demo image (`main.rs:78/98/434` → `demo_world()`/`demo_genesis()`); close it and the image is gone. The only persistence-shaped thing in the World is the **in-process** `History` replay tape (`replay.rs:120-235`).

The durable machinery *all exists, wired to the node, not the desktop*: `dregg-persist` (redb, ACID/WAL/fsync) with `LedgerCheckpoint{height,cells,…}` (`persist/src/ledger_store.rs:38-136`), the `commit_log` recovery spine, the node's checkpoint⊕overlay boot-recovery with last-writer-wins `upsert_cell` + root-convergence panic (`node/src/state.rs:414-428,676-771`), and the verified `recover = replay` theorem (`CrashRecovery.lean:193-216`, `#assert_axioms`-clean).

**The moves (mostly weld):**
- **(A) Wire `dregg-persist` into the World.** Add the redb dep; on `commit_turn` (`world.rs:571`, the single commit seam) *also* call `commit_log.commit_finalized_turn` with the touched-cell delta already computed at `world.rs:577-619` — durable write is O(change). On boot, replace `demo_world()`/`demo_genesis()` with `World::open(path)` running the exact node recovery (load `LedgerCheckpoint`, apply `cell_overlay_since` via last-writer-wins `upsert_cell`, verify root convergence, rebuild in-RAM `History`/`receipts` from the durable log). `CrashRecovery.lean::recover_eq_replay` covers this — the World inherits the proof by using the same overlay semantics.
- **(B) Persist the UI-cell subgraph with it.** Once UI state IS cells (§3), persistence is *automatic*: the UI subgraph rides the same commit log + checkpoint, and `History::replay_to` already reconstructs any past image *including* the UI cells. The rewindable desktop is `replay_to(k)` + `Registry::present` — which `ui_snapshot.rs` already does over the in-RAM History; just point it at the durable one.
- **(C) Make time-travel cheap.** Add periodic in-RAM (and durable) ledger *checkpoints* to `History` so `replay_to_via_checkpoint` starts from the nearest cached ledger snapshot, not genesis — O(k) → O(turns-since-checkpoint). The decomposition machinery is all built; this caches the checkpoint *ledger* (not only its root tooth).
- **(D) Make `state_root` incremental** (= §2.2 (A)) so per-frame reads are O(1).

**The honest native seams:**
- The World uses BLAKE3 `state_root` (`world.rs:288`, verified) while persist/node use `canonical_ledger_root` (Poseidon2 note-tree). The World must adopt the canonical root so recorded teeth match the durable convergence check.
- The **recorder double-ledger** (`record_ledger`/`record_exec` re-executing every turn purely for replay teeth, `world.rs:91-94`) could be *subsumed* by the durable commit log (it already carries post-states), collapsing the 2× execution — but the genesis path (`install_genesis`, `genesis_grant_cap`) bypasses the executor and is hand-mirrored, so each out-of-band install needs a durable genesis record.
- **UI-as-cells is the unbuilt prerequisite** for the rewindable *desktop*: until window positions/inspector focus/open panels are real cells through `commit_turn`, persisting the World persists only domain cells, not the UI. The reflexive knot and the durable-rewindable desktop are the *same* unbuilt move.
- The `CrashRecovery.lean` named boundary (post-commit/pre-ack burn window) is SAFE-direction-only; the converse "same-transaction burn weld" is a named node closure that carries into the persist-PD.

### 5.2 The seL4 persist-PD gap

The seL4 spine is **real redb-over-block-cap durability + the HostingLease economy, host-green but not on-device** (`sel4/persist-hosttest/`, 21 tests green): `commit_store.rs` reuses `pg-dregg/mirror.rs` chain-verify + `persist commit_log CommitRecord` verbatim (no_std+alloc, rides inside the PD); `redb_store.rs` is real redb ACID over a `StorageBackend` whose 5 ops *are* a block cap (`commits_survive_drop_and_reopen` proves durability); `hosting.rs` is pay-coin-to-be-hosted with lapsed-fee eviction, modeled by `HostingLease.lean` (5 teeth, `#guard`).

**The one named wall:** `BlockCapBackend` — a single `redb::StorageBackend` impl routing the 5 ops (len/read/set_len/sync_data/write) through the seL4 virtio-blk block cap. It is a bounded device-driver trait impl, but it is real seL4/virtio plumbing on the macOS user-mode-qemu-aarch64 checkpoint, plus the `commit_out` shared-region framing + persist-PD ELF link. The durable store *above* it is unchanged and host-green. Once closed, the in-VM starbridge image persists to the persist-PD exactly as the host World persists to local redb — the same `CommitRecord` bytes, n=1 collapse.

---

## 6. THE MIGRATION PATH

An ordered, incremental sequence. **Efficiency-proving milestone FIRST** — driving UI from cells before the projector is incremental only deepens the existing O(ledger)-per-frame hole.

**Dependency arc:** M1→M2 are independent of cells and unlock everything (do first). M3 (UI-as-cells) depends on M2's memo for tolerable cost. M4 (persistence) and M5 (meta-debug) both depend on M3. M6 (seL4) depends on M4 and is independently sequenced.

- **M1 — Memoize `state_root` + the easy wins (pure weld, no API change).** Cache `(height,receipt_head)→root` on `World`; promote `self.cells` to the sole sorted source. *Verify:* `rail_header` no longer re-hashes the ledger; a microbench shows per-notify cost flat as cell count grows.
- **M2 — Close the delta loop (THE efficiency-proving milestone).** Add `Cockpit.dynamics_cursor`; fold `dynamics().since(cursor)` into per-slice invalidation; key a `(FocusTarget, viewer, WitnessCursor)` memo around the unchanged-pure `Registry::present`. *Verify:* `grep since( cockpit.rs` now nonzero; a profiling harness proves per-interaction cost is O(changed-cells), not O(ledger); replay-scrub reuses cached projections. **This is the make-or-break slice; gate everything after it on this number.**
- **M3 — Self-host UI state as cells.** Generalize the `BufferCell` two-tier pattern into `WorkspaceCell`/`ViewCell`/`PanelCell`/`GadgetCell`; move the §3.1 cell-candidate fields onto cell-backed slots (free in-memory draft + occasional `SetField` commit); make `render()` read its camera-aim from cells. *Verify:* a UI mutation emits a `WorldEvent` and repaints via the M2 delta-fold uniformly with any domain-cell change; the Cockpit struct shrinks.
- **M4 — Wire `dregg-persist` into the World + persist the UI subgraph.** Add the redb dep; dual-write at `commit_turn`; `World::open(path)` recovery; adopt `canonical_ledger_root`; add periodic checkpoints for cheap rewind. *Verify:* close-and-reopen restores the exact image *including* UI state; recovered root matches recorded tooth (fail-closed); `replay_to_via_checkpoint` starts from a cached ledger.
- **M5 — The fractal meta-debug.** Add `FocusTarget::DebugFrame` + `MetaDebugView impl Presentable`; replace the flat `Tab` with a `MetaStack`; wire the suspend-button (`WitnessCursor::at_head` → push). *Verify:* "debug the debugger" focuses the inspector on its own `MetaDebugView` recursively; each level honestly stamps `Liveness`; nesting has a base case + cost ceiling.
- **M6 — seL4 `BlockCapBackend` (independent track).** Implement the 5-op `redb::StorageBackend` over the virtio-blk cap + `commit_out` framing + persist-PD ELF link. *Verify:* the in-VM image persists across PD restart with the same `CommitRecord` bytes as the host.

**The honest seams to keep in mind:**
- **Cache soundness = dynamics completeness** (M2): audit that *every* `commit_turn` effect emits a `WorldEvent` naming its cell, or stale projections survive.
- **Viewer-non-local invalidation** (M2): cap-graph deltas invalidate affordance badges on *other* cells.
- **The reflexive fixpoint** (M3/M5, deepest open): the projector projects cells including its own view state — needs a stratification to break the self-invalidation cycle. Unaddressed in current code.
- **The gpui↔firmament mapping** — keep-in-mind-but-later: the firmament cap model already governs the UI itself (window IS a real `dregg_firmament::Capability` over `Target::Surface`, through the same `granted ⊆ held` gate and the same `TurnExecutor`; compositor T1/T2/T3 scene-authority teeth, `surface.rs:85`, `compositor.rs:1-44`). When UI state moves into cells (M3), surface *geometry/z/focus* (still engine-local shell structs at `surface.rs:193-212`) should become `SetField` effects on a compositor cell — the `SurfaceDamaged` event already treats the compositor cell's `present_digest` slot as on-ledger (`dynamics.rs:66-75`); extend that to geometry. This is the bridge to the real starbridge-v2 cockpit as a seL4-framebuffer Mode, but it sequences *after* the M1-M4 spine proves out. Flag it, don't block on it.

---

## 7. OPEN QUESTIONS FOR EMBER

1. **"Suspend" semantics (§4.5.3):** does the meta-debug button mean *freeze-and-inspect-a-past-cursor* (replay-deterministic, the live loop keeps running) or *halt-the-live-loop* (a pause/resume primitive the World does not have today)? This decides whether `MetaDebugView` pins a `WitnessCursor` or needs a new live-pause mechanism.
2. **UI-cell conservation & authority (§3.5):** UI cells conserve nothing and ride the `SetField` weight class — but *what authority* mutates a `WorkspaceCell`/`PanelCell`? Is it the desktop operator's own cap, ambient, or a dedicated UI-authority cell? (This also gates whether a window-move is cap-gated like a `BufferCell.commit()`.)
3. **The reflexive fixpoint stratification (§2.3.5):** when the inspector inspects its own UI cell, how do we break the self-invalidation cycle — a fixed stratification level, a generation counter, or a "UI-cells don't invalidate UI-cell projections of themselves" rule? This is the deepest unaddressed open question.
4. **Commit cadence for UI state (§3.5):** when does the free in-memory UI draft get *witnessed* — on blur, on every Nth interaction, on explicit save, on snapshot? This trades durability granularity against turn volume in the log.
5. **One root or two (§5.1):** does the desktop World adopt `canonical_ledger_root` (Poseidon2) wholesale to match the durable convergence check, keeping the BLAKE3 `state_root` only as a fast view-layer tooth — or unify on one?
6. **seL4 sequencing:** is `BlockCapBackend` (M6) on the critical path for this epoch, or does it stay the named-but-later wall while the host-native M1-M5 spine matures first?

---

*( ◕‿◕ ) a small closing couplet, since the substrate already breathes the right shape:*
*the ledger does not need re-reading whole each frame —*
*the stream already whispers every cell by name.*

Key evidence I re-verified against HEAD before writing: `world.rs:284-301` (state_root hashes every cell — confirmed), `dynamics.rs:136-179` (the `since(cursor)` delta API — confirmed), `ui_snapshot.rs:59-126` (`WitnessCursor` + `Liveness` trichotomy — confirmed), `cockpit.rs:236-258` (the monolithic struct + `replay_cursor`/`breakpoints` fields — confirmed), and `buffer.rs:310-358` (the two-tier digest-on-cell / free-draft pattern — confirmed). All five reports' load-bearing citations hold.