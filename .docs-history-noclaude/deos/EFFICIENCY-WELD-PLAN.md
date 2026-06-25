# THE EFFICIENCY WELD — M1 + M2 IMPLEMENTATION PLAN

The executable plan for the make-or-break efficiency milestone of the reflexive
migration (`REFLEXIVE-MIGRATION.md` §2, §6). Scope: **M1** (memoize `state_root`,
kill the 15× re-sort — pure weld, no API change) and **M2** (the delta loop — the
efficiency-proving milestone). This is **domain-cell projection only**. It is
**INDEPENDENT of the stratified-fixpoint question** (`REFLEXIVE-MIGRATION.md`
§2.3.5 / §3 / §7.3): the self-projection cycle — the projector projecting cells
that include its own view state — arrives only with **M3** (UI-as-cells). M1/M2
project *domain* cells through the unchanged-pure `Registry::present`; no cell is
ever both a projection input and the projection's own view-state, so no
stratification is needed here. Gate everything after M2 on the proof number in §3.

All citations verified against HEAD before writing (see the per-section
`file.rs:line` anchors).

---

## 0. THE COST TRUTH (what we are killing)

Per `cx.notify()` gpui re-runs the whole `Cockpit::render` closure
(`cockpit.rs:6217`). Today, with zero projection-layer memoization, each
interaction pays:

| Hot path | Where | Cost |
|---|---|---|
| `state_root()` postcard+BLAKE3 over **every cell**, to draw a 12-char hash | `world.rs:284-301`; called `cockpit.rs:2069` (`rail_header`), `:3858` | O(cells · cell_bytes) |
| `sorted_cells()` full `HashMap` drain+sort, **30+ call sites** | `cockpit.rs:6293-6296`; callsites at `517,986,1001,1021,1049,2350,2679,2871,2980,3084,3377,3388,3401,3425,3431,…` | O(n log n) × many per frame |
| `Registry::present` rebuilds the whole presentation set, "reads the live world fresh every call (never a cache)" | `presentable.rs:863-888`; called `cockpit.rs:2787,2810` | O(cell + receipt-log) per moldable frame |

The producer (`dynamics().since(cursor)`, `dynamics.rs:164`) and the consumer
(gpui render) both exist and are **not joined**: `grep -n "since(" cockpit.rs` →
**zero** today. Each `WorldEvent` already names its changed `CellId`
(`dynamics.rs:19-93`). M1/M2 join them.

---

## 1. M1 — MEMOIZE `state_root` + KILL THE RE-SORT (pure weld, no API change)

Two independent welds. Neither changes any public signature; both are verifiable
by `cargo check -p starbridge-v2` + one targeted unit test each.

### 1.1 Memoize `state_root` — cache `(height, receipt_head) → [u8;32]` on `World`

`state_root` (`world.rs:284-301`) folds `height` + every sorted cell's postcard +
the receipt-chain head (`world.rs:297-299`). The cache key is **exactly** the
`WitnessCursor` identity (`ui_snapshot.rs:69-75`): the root is a pure function of
`(height, receipt_head, ledger-contents)`, and the ledger only changes when the
height/receipt advances (genesis installs also bump via `install_genesis`). So:

**Chosen approach: a `RefCell` memo on `World` keyed on the witness tooth.** This
keeps `state_root(&self)` a `&self` method (no `&mut` ripple through the ~30
callers and the `Rc<RefCell<World>>` borrow discipline in cockpit).

Add to `World` (`world.rs:71-123`):

```rust
use std::cell::Cell as StdCell;   // alias: `Cell` is taken by dregg_cell::Cell

/// Memoized image root, valid while (height, receipt_head) is unchanged.
/// (height, receipt_head_or_zero, root)
state_root_memo: StdCell<Option<(u64, [u8; 32], [u8; 32])>>,
```

Initialize `state_root_memo: StdCell::new(None)` in **every** `World`
constructor: `with_costs_and_timestamp` (~`world.rs:165`) and the `fork`
struct-literal (`world.rs:370-384`). (`StdCell<Option<…>>` is `Copy`-friendly and
needs no `RefCell` borrow.)

Rewrite `state_root` (`world.rs:284`):

```rust
pub fn state_root(&self) -> [u8; 32] {
    let head = self.receipts.last().map(|r| r.receipt_hash()).unwrap_or([0u8; 32]);
    if let Some((h, rh, root)) = self.state_root_memo.get() {
        if h == self.height && rh == head {
            return root;
        }
    }
    let root = self.compute_state_root();      // the existing body, verbatim
    self.state_root_memo.set(Some((self.height, head, root)));
    root
}
```

Move the current `world.rs:285-300` body into a private `fn compute_state_root(&self) -> [u8;32]`.

**Soundness:** every mutation path advances `height` (`commit_turn` `world.rs:595`)
or the receipt head, OR is a genesis install which calls `install_genesis`
(`world.rs:400-416`) — genesis does **not** bump `height` or push a receipt, so it
must invalidate explicitly. Add one line at the end of `install_genesis` (after
`world.rs:414` emit): `self.state_root_memo.set(None);`. Likewise in
`set_cell_program` / `genesis_grant_cap` / `genesis_open_permissions` (`world.rs:475-543`)
which mutate the live ledger without a height bump — append `self.state_root_memo.set(None);`
to each. (These are the ONLY non-`commit_turn` ledger writers; confirm with
`grep -n "ledger_mut()" world.rs` — all are genesis-path.)

*Verify:* the existing `state_root_changes_when_state_changes` test
(`world.rs:1459-1467`) must still pass (it commits a turn between two reads — the
height bump busts the memo). Add `state_root_memoized_within_same_height`: read
twice with no commit between, assert the second is a cache hit (instrument with a
recompute-counter behind `#[cfg(test)]`, or just assert byte-equality — equality
is the contract). `rail_header` (`cockpit.rs:2067`) and `:3858` now read a cached
root.

### 1.2 Kill the 15×+ re-sort — `self.cells` as the sole sorted source

`sorted_cells(w)` (`cockpit.rs:6293`) re-collects + re-sorts the whole `HashMap`
ledger on every call; it is called at 30+ sites per frame. `Cockpit.cells`
(`cockpit.rs:240`) is **already** the sorted cache, refreshed by `refresh_cells`
(`cockpit.rs:779-781`) on every mutating handler — but most read sites bypass it
and call `sorted_cells` fresh.

**Chosen approach: route every read through `self.cells`, drop the free
`sorted_cells(&world)` callsites.** Do NOT change the `Ledger` backing
(`cell/src/ledger.rs:289`, `HashMap<CellId, Cell>`) — `Ledger` is in the shared
`cell` crate (also used by the node); a `HashMap→BTreeMap` swap is a cross-crate
change with its own root-ordering implications and is out of scope. Note: the
`Ledger` already carries `leaf_positions: BTreeMap<[u8;32], usize>`
(`ledger.rs:298`) — a sorted index — so a future `World::sorted_cell_ids()`
accessor could read it directly, but `self.cells` is the cheaper local weld now.

Mechanical change set in `cockpit.rs`:

1. **Render/read sites that already hold `&self`** (`986,1001,1021,1049,2350,2679,2871,2980,3084,3377,3388,3401,3425,3431,…`): replace `let cells = sorted_cells(&self.world.borrow());` with `let cells = &self.cells;` (or `self.cells.clone()` where a borrow conflicts with a later `self.world.borrow_mut()`). Each is a `&[CellId]` / `Vec<CellId>` of identical sort order — drop-in.

2. **Keep `self.cells` correct off the dynamics stream too** (not just `refresh_cells` on handlers): see M2 §2.2 — `CellBorn`/`CellDestroyed` from `since(cursor)` mutate `self.cells` incrementally. Until M2 lands, the existing `refresh_cells` calls (after every mutating handler, `cockpit.rs:816,836,854,…`) keep it correct; that is the current invariant and M1 preserves it.

3. The construction-time `sorted_cells(&world.borrow())` (`cockpit.rs:517`) stays — it seeds `self.cells` once.

4. `cells_of` (`cockpit.rs:6300`, an alias) → make it `&self.cells` at its single callsite (`cockpit.rs:3084`) and delete the free fn, OR leave `cells_of`/`sorted_cells` defined for the genesis/test paths but ensure no per-frame render path calls them. Acceptance: `grep -n "sorted_cells(&self.world\|sorted_cells(&w\|cells_of(&w" cockpit.rs` returns **only** non-render-hot sites (construction + handler bodies that already `refresh_cells`).

*Verify:* `cargo check -p starbridge-v2`; the rail order is unchanged (same sort
key `as_bytes().cmp`). A microbench (§3) shows per-notify cost flat as cell count
grows (no re-sort in the render closure).

---

## 2. M2 — THE DELTA LOOP (the efficiency-proving milestone)

Join `dynamics().since(cursor)` to render: fold the delta into per-slice
invalidation, and wrap the unchanged-pure `Registry::present` in a memo keyed on
the witness identity. **This is the make-or-break slice.**

### 2.1 `Cockpit.dynamics_cursor` + the per-render delta fold

Add to `Cockpit` (`cockpit.rs:236`):

```rust
/// Last dynamics cursor this view has folded. Each render folds
/// world.dynamics().since(self.dynamics_cursor) into per-slice invalidation,
/// then advances to world.dynamics().cursor().
dynamics_cursor: usize,
/// The per-(focus,viewer,cursor) projection memo (§2.3).
present_memo: PresentMemo,
```

Initialize `dynamics_cursor: 0` and `present_memo: PresentMemo::default()` in the
constructor (`cockpit.rs:~517`).

Add a fold helper, called at the **top** of `render` (`cockpit.rs:6218`, right
after `self.drain_live_stream(cx)` at `:6221`):

```rust
fn fold_dynamics(&mut self) {
    let new = {
        let w = self.world.borrow();
        let from = self.dynamics_cursor;
        // Clone the slice out so we drop the world borrow before mutating self.
        let slice = w.dynamics().since(from).to_vec();
        self.dynamics_cursor = w.dynamics().cursor();
        slice
    };
    for ev in &new {
        self.invalidate_for(ev);
    }
}
```

> Note: `drain_live_stream` (`cockpit.rs:6221`) is what pulls node receipts and
> commits turns onto the embedded World, so by the time `fold_dynamics` runs the
> dynamics log already carries this frame's new events. Local handler commits
> (e.g. via `commit_turn`) likewise emit before the next render. The cursor
> therefore strictly trails the log and `since` is well-defined.

### 2.2 `WorldEvent` variant → what it invalidates

`invalidate_for(&mut self, ev: &WorldEvent)` dispatches over the full variant set
(`dynamics.rs:19-93`). The mapping (the load-bearing table):

| `WorldEvent` | Names | Invalidates |
|---|---|---|
| `CellBorn{cell,…}` | a cell (or `CellId::ZERO` sentinel for `CreateCell`/`FromFactory`, `dynamics.rs:767,791`) | **`self.cells`** (insert sorted) + that cell's `present_memo` row. **ZERO sentinel ⇒ refresh `self.cells` from ledger** (id unknown — the only full-rescan case; bounded, fires once per cell-creating turn). |
| `CellDestroyed{cell}` | a cell | remove from `self.cells`; drop its `present_memo` entries |
| `BalanceFlowed{cell,…}` | a cell | that cell's row + inspector → `present_memo.invalidate_cell(cell)` |
| `FieldSet{cell,index}` | a cell | `present_memo.invalidate_cell(cell)` |
| `CellSealed/CellUnsealed{cell}` | a cell | `present_memo.invalidate_cell(cell)` (lifecycle badge) |
| `Burned{cell,…}` | a cell | `present_memo.invalidate_cell(cell)` |
| `CapabilityGranted{from,to}` / `CapabilityRevoked{cell,…}` | cap edge | `present_memo.invalidate_cell(from)`+`(to)` (or `cell`) **AND `present_memo.invalidate_affordances_all()`** — see §4 seam: affordance badges are viewer-non-local. |
| `SurfaceDamaged{cell,region_count,…}` | compositor cell | `present_memo.invalidate_cell(cell)`; later (M3) repaint `region_count` regions only |
| `EventEmitted{sender,cell,…}` | notify edge | `present_memo.invalidate_cell(cell)` (inbox badge) |
| `TurnCommitted{…}` | height tick | nothing cell-specific; the per-cell `BalanceFlowed`/`FieldSet`/… in the SAME `events` batch carry the actual invalidations (`commit_turn` emits `TurnCommitted` first, then the per-effect events, `world.rs:597-630`). `rail_header`'s root re-reads via the M1 memo (height bumped). |
| `TurnRejected{…}` | nothing changed | no invalidation (state didn't move; only the outcome banner, already a Rust field) |

This is the **dirty-set**: turning per-frame O(ledger) into O(changed-cells).

### 2.3 The projection memo around the UNCHANGED-pure `Registry::present`

`Registry::present(target, viewer)` (`presentable.rs:881`) is a pure function of
`(target, viewer, world-state)`. Wrap it — **do not rewrite it** — in a memo valid
exactly while `WitnessCursor::is_live_head` holds (`ui_snapshot.rs:89`).

New type (in a small new module `src/present_memo.rs`, or inline in `cockpit.rs`):

```rust
use std::collections::HashMap;
use crate::presentable::{FocusTarget, Presentation, Registry};
use crate::ui_snapshot::WitnessCursor;
use crate::world::World;
use dregg_cell::CellId;

#[derive(Default)]
pub struct PresentMemo {
    /// The cursor the cached entries were projected at. When the live head moves
    /// past this, entries NOT explicitly re-validated by the delta fold are stale;
    /// we lazily recompute on miss, and the fold proactively drops touched cells.
    cursor: Option<WitnessCursor>,
    /// (focus-cell, viewer) -> projected presentation set at `cursor`.
    entries: HashMap<(CellId, CellId), Vec<Presentation>>,
}

impl PresentMemo {
    /// The memoized projector. Valid while the live head is unchanged; on a head
    /// advance, entries the delta fold did NOT invalidate are reused (a cell the
    /// turn didn't touch projects identically). On a touched cell, the fold has
    /// already removed the entry, so this recomputes via the pure Registry.
    pub fn present(
        &mut self,
        world: &World,
        target: FocusTarget,
        viewer: CellId,
    ) -> Option<Vec<Presentation>> {
        let head = WitnessCursor::at_head(world);
        // If the cursor advanced, KEEP entries (the fold dropped the dirty ones)
        // but record the new head. (Time-travel: a non-live cursor never caches —
        // §2.4 — the caller passes a non-head world only via replay, handled there.)
        self.cursor = Some(head);
        let key = (target.cell(), viewer);
        if let Some(hit) = self.entries.get(&key) {
            return Some(hit.clone());
        }
        let set = Registry::new(world).present(target, viewer)?;
        self.entries.insert(key, set.clone());
        Some(set)
    }

    pub fn invalidate_cell(&mut self, cell: CellId) {
        self.entries.retain(|(c, _), _| *c != cell);
    }
    /// Cap-edge deltas reach OTHER cells' affordance badges (§4 seam): drop all.
    pub fn invalidate_affordances_all(&mut self) {
        self.entries.clear();
    }
}
```

Replace the moldable-tab call site (`cockpit.rs:2787,2810`):

```rust
// was: let reg = Registry::new(&w); … reg.present(FocusTarget::Cell(focus), focus)
let set = self.present_memo.present(&w, FocusTarget::Cell(focus), focus);
let Some(set) = set else { /* dangling focus, unchanged */ };
```

(borrow note: take `let w = self.world.borrow();` then call
`self.present_memo.present(&w, …)` — `present_memo` is a disjoint field of `self`,
so the borrow checker accepts the split; if it complains, fold the cursor first
and clone `focus`/`viewer` out of the world borrow.)

**Soundness:** a presentation is pure in `(target,viewer,state)`; it is valid
exactly while the cursor names the live head. A new receipt advances the head and
the fold (§2.2) drops every cell the delta named. A cell the turn did **not** touch
projects identically across the head advance, so its cached entry is correctly
reused. The ONLY way a stale entry survives is a state change with **no** naming
`WorldEvent` — that is the §4 cache-soundness = dynamics-completeness obligation.

### 2.4 Time-travel reuse (the same mechanism)

The memo key is the `WitnessCursor`. Replay (`History::replay_to`,
`replay.rs:247`) hands a reconstructed past `World`; project it with a **separate**
`PresentMemo` (or a per-cursor sub-map) and every cell unchanged between two scrub
steps reuses its cached projection. M2 only needs to NOT pollute the live memo with
non-head projections: the live `present_memo` is fed only the live-head world; the
replay panel keeps its own. (Replay-panel memoization is an M2-adjacent bonus, not
required for the proof; the proof is the live-head O(changed-cells) number.)

### 2.5 Splitting the giant Render into sub-view Entities

Even with the memo, gpui re-runs the whole `Cockpit::render` **closure** (the
`div().child(…)` walk, `cockpit.rs:6218-6288`) on any `cx.notify()` unless the
Cockpit is split into child `Entity`s so a notify touching one cell repaints one
pane. Minimum split that proves the principle:

- **`CellWorldView`** (`Entity<CellWorldView>`) — the left-rail cell world
  (`self.cell_world(cx)`, `cockpit.rs:6248`). Holds `world: Rc<RefCell<World>>` +
  its own `dynamics_cursor` + `present_memo`. Repaints on cell deltas only.
- **`RailHeaderView`** — `rail_header` (`cockpit.rs:2067`); repaints on
  `TurnCommitted` (height tick → M1-cached root).
- **`InspectorView`** — the right-pane moldable/inspector (`cockpit.rs:2787`
  region); holds the `present_memo`; repaints on the focused cell's deltas.

Each child `Entity` calls `cx.notify()` on **itself** only when its slice's
invalidation fires; the parent `Cockpit` stops calling `cx.notify()` for
per-cell changes. This is real surgery on the "one uniform inspector renders
everything" invariant (`REFLEXIVE-MIGRATION.md` §2.3.1) — do it incrementally:
the proof in §3 can be taken on `CellWorldView` ALONE (the rail is the cell-count-
scaling pane), with the rest of the Cockpit split following.

**Sequencing note:** §2.1–§2.4 (cursor + fold + memo) land FIRST and already
deliver the O(changed-cells) *projection* cost. The Entity split (§2.5) removes
the residual O(elements) closure-walk; it is the second half of M2 and is what the
"one notify repaints one pane" acceptance needs. Take the §3 proof after §2.1–§2.4
for the projection number, then again after §2.5 for the repaint-granularity
number.

---

## 3. THE PROOF (gate everything after on this number)

A microbench demonstrating **per-interaction cost is O(changed-cells), not
O(ledger)**, as cell-count grows. This is the make-or-break number.

### 3.1 The harness

A criterion-style bench (or a plain `#[test]` timing harness if criterion isn't
already a dev-dep — check `starbridge-v2/Cargo.toml`; a hand-rolled
`std::time::Instant` loop is acceptable and cargo-check-friendly) at
`starbridge-v2/benches/efficiency_weld.rs` (or `src/world.rs` `#[cfg(test)]`):

```text
for n in [16, 256, 4096, 65536] {
    let mut w = World::new();
    for _ in 0..n { w.genesis_cell(seed, 1); }   // build an n-cell ledger
    // ONE interaction = ONE single-cell turn (a SetField on one cell):
    let cell = /* one cell */;
    let t0 = Instant::now();
    for _ in 0..ITERS {
        w.commit_turn(w.turn(cell, vec![Effect::SetField{cell, index, value}]));
        // the projection cost under test:
        let _ = project_one_interaction(&w);   // M1: state_root + the memo'd present of the touched cell
    }
    record(n, t0.elapsed());
}
```

`project_one_interaction` exercises exactly the per-render hot path: call
`w.state_root()` (M1-memoized) + a `PresentMemo` fold of `dynamics().since` + the
memoized `present` of the touched cell.

### 3.2 The acceptance criteria

1. **Scaling:** plot/assert `time(n) / time(16)` stays ~**flat** (≈ constant
   factor, not linear) across `n ∈ {16,256,4096,65536}`. Before the weld it is
   ~linear in `n` (the `state_root` + `sorted_cells` re-scan). After: the touched-
   cell projection + the M1 cache hit are O(1) in `n`; only the one-time ledger
   build is O(n) and is OUTSIDE the timed loop. Concretely assert
   `time(65536) < K · time(16)` for a small constant `K` (e.g. `K ≤ 4`, slack for
   `HashMap` probe + allocation noise).
2. **`grep -n "since(" cockpit.rs` is now NONZERO** (the delta loop is wired).
   This is the structural acceptance check from `REFLEXIVE-MIGRATION.md` §6 M2.
3. **`state_root` is a cache hit within a height:** the §1.1 unit test
   (`state_root_memoized_within_same_height`) passes.
4. **Repaint granularity (after §2.5):** a notify naming one cell repaints one
   pane — assert via a render-count instrument on `CellWorldView` vs siblings, or
   at minimum confirm the closure-walk no longer re-runs the full three-pane tree
   on a single-cell notify.

**GATE:** M3 and beyond do not start until criterion (1)+(2) hold. Driving UI from
cells (M3) before this number deepens the O(ledger)-per-frame hole.

---

## 4. THE SEAMS (honest)

### 4.1 Cache soundness = dynamics completeness (load-bearing)

The memo (§2.3) and the incremental `self.cells` (§1.2) derive their invalidation
**entirely** from the dynamics stream. A stale projection survives iff some
`commit_turn` effect mutates a cell **without** emitting a `WorldEvent` naming it.
**Audit obligation — verify each effect's event:**

- The per-cell `BalanceFlowed` events are derived from the pre/post balance diff
  over `touched_cells(&turn)` (`world.rs:577-619`), so **any balance change** to a
  touched cell is named. But `touched_cells` (`world.rs:708-747`) only collects the
  cells in the effect arms it matches — verify the `_ => {}` arm
  (`world.rs:744`) does not silently drop an effect that writes a cell. List of
  effect kinds and their emitter:
  - `Transfer` → both `from`/`to` in `touched` ⇒ `BalanceFlowed` ✅
  - `SetField` → `touched` + `collect_effect_events` `FieldSet` (`world.rs:772`) ✅
  - `GrantCapability`/`RevokeCapability` → `CapabilityGranted/Revoked` (`world.rs:753-761`) ✅
  - `CellSeal/Unseal/Destroy`/`Burn` → named events (`world.rs:778-789`) ✅
  - `CreateCell`/`CreateCellFromFactory` → `CellBorn{cell: ZERO}` (`world.rs:762,790`) — **the id is unknown at emit**, so the dirty-set cannot name it; §2.2 handles this by refreshing `self.cells` from the ledger on any ZERO-sentinel `CellBorn` (the bounded full-rescan case). **Verify no inspector caches a child cell before its first real-id event.**
  - `IncrementNonce`, `MakeSovereign`, and any `_ => {}` effect → **emits NO `collect_effect_events` event** (only `touched`-based `BalanceFlowed`, and only if balance changed). A nonce bump or sovereign flip with no balance change ⇒ **NO event ⇒ a stale projection** if the inspector renders nonce/sovereign state. **This is the concrete completeness gap to close:** add `WorldEvent::FieldSet`-equivalent emissions (or a generic `CellMutated{cell}`) for `IncrementNonce`/`MakeSovereign` in `collect_effect_events` (`world.rs:750`), OR document that the inspector does not surface nonce/sovereign deltas (it does — nonce is the BufferCell revision, `buffer.rs:322`). **Recommendation: add `MakeSovereign`/`IncrementNonce` arms emitting a per-cell mutation event before relying on the memo for those slices.**

  How to verify: `grep -n "Effect::" turn/src/.../effect*.rs` for the full
  `Effect` enum, cross-check every variant against `collect_effect_events` +
  `collect_touched`; any variant in neither is a completeness hole. Add a test:
  for each `Effect` variant, commit a turn using it and assert
  `dynamics().since(before)` contains an event naming the written cell.

### 4.2 Viewer-non-local invalidation (cap-graph deltas)

`InspectAct`/affordance projection is **per-viewer**: a `CapabilityGranted/Revoked`
**anywhere** can change another cell's affordance badges (the viewer's reachable
cap set changed). The per-cell dirty-set is **insufficient** for the affordance
presentation. §2.2 handles this conservatively: any cap-edge event calls
`present_memo.invalidate_affordances_all()` (a full memo clear). This is correct
but coarse; a precise version keys the affordance sub-cache on `viewer` and
invalidates only entries for viewers whose reachable set changed — defer the
precise version until profiling shows cap-edge churn is hot (it is rare relative to
balance/field writes).

### 4.3 BLAKE3 vs canonical root

`World::state_root` is BLAKE3 over sorted cells (`world.rs:284-288`); the node /
persist layer use `canonical_ledger_root` (Poseidon2 note-tree) —
`REFLEXIVE-MIGRATION.md` §5.1. The M1 memo caches the BLAKE3 **view-layer** tooth;
it is NOT the protocol commitment. **Cross-ref the persistence plan (M4):** when
the World adopts `canonical_ledger_root` to match the durable convergence check,
the memo key (`height, receipt_head`) is unchanged — only `compute_state_root`'s
body swaps. The memo is forward-compatible with the root unification (§7.5 open
question). The `Ledger` already maintains an incremental Merkle `root()`
(`ledger.rs:303,326`) and a sorted `leaf_positions` index (`ledger.rs:298`), so the
canonical path is *already incremental* in the ledger — the World's view root can
eventually defer to it.

### 4.4 Fixpoint-INDEPENDENCE (explicit)

Everything above projects **domain** cells. No cell here is simultaneously a
projection input and the projection's own view-state, so the self-invalidation
cycle (`REFLEXIVE-MIGRATION.md` §2.3.5) **cannot arise**. The memo's
`invalidate_cell` touches only the named domain cell; there is no UI-cell whose
projection re-invalidates itself. The stratification question is **deferred whole
to M3** and is not a prerequisite for the M2 proof. (When M3 promotes UI state to
cells, a UI-cell's `FieldSet` event would invalidate the projection that *reads*
that UI-cell — that is the cycle, and it gets a generation-counter / "UI-cells
don't invalidate their own projection" rule THEN, §7.3.)

---

## 5. ORDERED TASK LIST (with per-step verification)

Each step is `cargo check -p starbridge-v2`-friendly; the heavy proof is the one
microbench (§3). Land in this order; commit per step.

**M1 (independent, pure weld):**

1. **`state_root` memo.** Add `state_root_memo` field + init in both constructors;
   split `compute_state_root`; rewrite `state_root` to check/fill the memo;
   invalidate (`set(None)`) in `install_genesis` + the three genesis-path ledger
   writers (`set_cell_program`, `genesis_grant_cap`, `genesis_open_permissions`).
   *Verify:* `cargo check`; `state_root_changes_when_state_changes` still green;
   new `state_root_memoized_within_same_height` green.
2. **Route reads through `self.cells`.** Replace the ~30 render-hot
   `sorted_cells(&self.world.borrow())` / `cells_of(&w)` callsites with
   `&self.cells` (clone where borrows conflict). Keep construction + handler seeds.
   *Verify:* `cargo check`; `grep -n "sorted_cells(&self.world\|cells_of(&w" cockpit.rs`
   returns only non-render sites; rail order visually unchanged.
3. **M1 microbench baseline.** Land the §3 harness; record pre-M2 numbers
   (state_root + sorted reads now flat in `n`).
   *Verify:* `time(n)/time(16)` flat for the M1 paths.

**M2 (the milestone — gated proof at the end):**

4. **`dynamics_cursor` + `fold_dynamics` + `invalidate_for`.** Add the two fields;
   call `fold_dynamics` at the top of `render` after `drain_live_stream`; implement
   the §2.2 variant→invalidation table (including the ZERO-sentinel `self.cells`
   refresh and the cap-edge `invalidate_affordances_all`).
   *Verify:* `cargo check`; `grep -n "since(" cockpit.rs` nonzero.
5. **`PresentMemo`.** Add the type (§2.3); wire `present_memo.present(&w, …)` at
   the moldable call site (`cockpit.rs:2787,2810`).
   *Verify:* `cargo check`; the moldable tab renders identically (same
   `Presentation` set, now cached).
6. **Dynamics-completeness audit + fixes (§4.1).** Enumerate every `Effect`
   variant; add per-cell mutation events for `IncrementNonce`/`MakeSovereign` (and
   any uncovered `_ =>` effect) in `collect_effect_events`. Add the
   per-effect "names its cell" test.
   *Verify:* the new completeness test green; no effect writes a cell without a
   naming event.
7. **The §3 proof (projection).** Run the microbench through the full M1+§2.1–§2.5
   path. **GATE:** assert `time(65536) < K·time(16)` (small `K`) + `grep since(`
   nonzero. Record the number.
8. **Sub-view Entity split (§2.5).** Extract `CellWorldView` (at least) into an
   `Entity`; move its `dynamics_cursor`/`present_memo` onto it; parent stops
   per-cell `cx.notify()`.
   *Verify:* `cargo check`; a single-cell notify repaints one pane (render-count
   instrument); re-run the §3 proof for the repaint-granularity number.

**GATE OUT OF THE WELD:** steps 7 (projection) + 8 (repaint) hold ⇒ the
efficiency milestone is proven; M3 (UI-as-cells) may begin.

---

*( ◕‿◕ ) the stream already whispers every cell by name —*
*we need only stop re-reading the whole ledger each frame,*
*and let the touched cell, alone, re-light its flame.*
