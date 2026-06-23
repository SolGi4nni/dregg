# Incremental commitment — make the per-turn state commitment O(changed), everywhere

## Why this exists

The verified executor's per-turn cost is dominated not by execution (the state
transition is cheap) but by **recomputing cryptographic commitments from scratch every
turn**. Three depth-16 sorted-Poseidon2 trees (cap, heap, fields-map) do a **full 2^16-leaf
rebuild** on every recompute — and the cap-tree rebuild is absorbed into the BLAKE3
`hash_cell` of *every dirty ledger leaf on every publishing turn*, even turns that never
touch capabilities. At the pre-`perf(field)` perm cost that was ~0.4s/turn; even after the
field fix it is tens of ms — the real "heavy boundary."

The existing `WitnessMode::Symbolic` bolt-on (a desktop-`World`-level buffer + replay-
`collapse`) is a **workaround for this slowness**: defer the commitment, replay later.
This document proposes the alternative that makes the workaround unnecessary: **make the
commitment cheap (O(changed)), intrinsically, in the ledger/cell — so every consumer
(node, desktop, MCP) pays µs per turn and nothing has to defer or replay.**

The principle, stated once: **the commitment is a pure function of state; the ledger
Merkle already proves you can keep it incrementally (dirty-track + update only changed
paths); extend that property down to every sub-commitment.**

## The two pipelines (both pay the bombs)

- **v8 BLAKE3 live path** — `Ledger::root()` → `hash_cell` → `compute_canonical_state_commitment`
  (`cell/src/commitment.rs:192`). Per dirty leaf, re-absorbs `cap_root` (full rebuild),
  `heap_root`, `fields_root`, `system_roots_digest`. Fires on every publishing turn.
- **v9 rotated witness/proof path** — `rotation_witness::produce` (`turn/src/rotation_witness.rs:342`).
  Adds the turn-level `cells_root`, `nullifier_root`, `commitments_root`, `iroot`. Fires on
  proof/light-client production.

## The complete inventory (ranked; verdict per tree)

| tree / root | compute fn | depth | full-rebuild today | empty short-cut | per-turn frequency | verdict |
|---|---|---|---|---|---|---|
| **cap-tree** `CanonicalCapTree` | `circuit/src/cap_root.rs` | 2^16 | **YES** | no (folds 65k zeros) | every turn, per dirty leaf | **incrementalize (template: ledger)** — #1 prize |
| **heap-tree** `CanonicalHeapTree` | `circuit/src/heap_root.rs`; `state.rs:374` | 2^16 | **YES** | no | per heap write | **incrementalize** |
| **fields-map tree** | `state.rs:345` (a `CanonicalHeapTree`) | 2^16 | **YES** | no | per extended-field write | **incrementalize** (shares heap fix) |
| nullifier_root `NullifierSet` | `cell/src/nullifier_set.rs:267` | BLAKE3 over set | YES (rebuild from sorted set) | yes | proof path; noteSpend admission | **cache levels + incremental append** (monotone grow → rightmost path only) |
| commitments_root | `rotation_witness.rs:374` | set accumulator | YES | yes | proof path (noteCreate) | **same as nullifier** |
| cells_root | `rotation_witness.rs:259` | 2^16 over present cells | YES | yes | per proven turn | **cache + incrementalize** (shares ledger's set state) |
| **ledger tree** `Ledger` | `cell/src/ledger.rs:868/826` | 2^⌈log N⌉ | **NO — already incremental** | n/a | every `root()` | **the TEMPLATE — do not touch** |
| system_roots_digest | `state.rs:249` | scalar (8-felt fold) | n/a | yes (const) | every `hash_cell` | **scalar — leave** |
| 8 system side-tables | `state.rs:46` | per-table felt | not wired (test-only `set_system_root`) | — | never (live) | **out of scope** (unwired; see house-capacities memory) |
| iroot (receipt MMR) | `rotation_witness.rs:282` | small fold | rebuild over tiny log | yes | proof path | **leave** (cheap) |

## The design

### The shape (copy the ledger's `Pending`)

`Ledger` already does it right: `enum Pending { Clean, Values(BTreeSet<CellId>), Structural }`,
`update_leaf` (O(log N) per changed leaf), `materialize` (only on `root()`), `leaf_positions`.
The fix is to give the same dirty-tracked, incrementally-materialized shape to the three
depth-16 trees, owned by `CellState`:

1. **`CellState` gains a `Pending`-style dirty-track** for each of its sub-commitments
   (cap-set, heap-map, fields-map). A mutation (`add`/`revoke` a cap, `set_heap`,
   `set_field_ext`) marks the touched leaf dirty instead of eagerly calling
   `compute_*_root` (today `state.rs:756/800/809` re-seal synchronously — that is the bug).
2. **The cached sub-tree** (a `CanonicalCapTree`/`CanonicalHeapTree` held on the cell) is
   updated by `update_leaf`/`update_witness`/`insert_witness` (these primitives already
   exist on both trees) along the changed leaf's path — ~depth Poseidon2, not 2^16.
3. **`*_root()` materializes lazily** (only when `hash_cell` actually needs it) and only the
   dirty paths.
4. **Empty / sparse → precomputed empty-subtree roots.** A cell with no caps returns the
   cached `empty_capability_root()` constant (a `OnceLock`) instead of folding 65k zeros;
   a sparse tree folds only real-leaf paths against the 16 precomputed empty-subtree roots.
   (This is the "sparse Merkle" half — it also drops the per-rebuild cost for non-empty
   small trees from 2^16 to ~depth·n_leaves.)

### Net per-turn cost

- transfer (2 cells, 0 cap/heap/field changes): the cells' sub-roots are clean → reused;
  only the ledger tree updates ~2 leaf paths. **≈ single-digit µs** (after `perf(field)`).
- delegate/revoke (1 cap change): one cap-tree leaf path updates (~16 Poseidon2). **µs.**
- heap/field write: one heap/fields leaf path. **µs.**

Computed **every turn, for every consumer**, with the chain staying bound to the real
state-root (no protocol change, light-clients unaffected).

### The invariant (non-negotiable)

The incremental root MUST be **byte-identical** to the full-rebuild root. The trees already
carry `prove_membership` / `position_of` / `*_witness` (the membership machinery that
*defines* a correct incremental update), so this is a known-correct operation, not new
crypto. Pin it with a **differential**: for a random corpus of mutation sequences,
`incremental_root == full_rebuild_root` for every step. (Same discipline as `perf(field)`'s
KAT byte-identity.)

## Relationship to the other work

- **`perf(field)` (DONE, `a340adf09`)** — kills the `%`-per-op so each Poseidon2 perm is
  ~25× cheaper. Multiplies into all of the above.
- **sparse empty-subtree roots** — the empty/sparse short-circuit; the foundation step of
  the incrementalization (and a standalone win for empty c-lists).
- **`WitnessMode::Symbolic` bolt-on** — once per-turn commitment is µs, this is **no longer
  load-bearing**. Demote it to an *optional* batch optimization (bulk sync/replay: defer
  even the µs work over thousands of turns, collapse once) or delete it. It stops being the
  thing the hot path "forgot to turn on."

## Staged plan

1. **Sparse empty-subtree roots** for `CanonicalCapTree`/`CanonicalHeapTree` (cache the 16
   empty-subtree roots + the empty-root constant; fold only real-leaf paths). Byte-identical;
   immediate win for empty/small trees. *Template-agnostic, lowest risk.*
2. **Cap-tree incrementalization** (the #1 prize, the template cut): `CellState` owns a
   dirty-tracked `CanonicalCapTree`; cap mutations `update_leaf`; `cap_root()` materializes
   dirty paths. Differential-pinned. This proves the pattern.
3. **Heap + fields-map** — the same `CellState` `Pending` wrapper covers both (fields-map IS
   a `CanonicalHeapTree`). One dirty-track, two roots.
4. **nullifier / commitments / cells_root** — cache tree levels + incremental append
   (monotone-grow is the easy case); `cells_root` can share the ledger's set state.
5. **Demote the symbolic bolt-on** to optional-batch (or remove), now that the hot path is
   intrinsically cheap.

## What "done" looks like

No consumer recomputes a commitment tree from scratch on a turn that didn't change it; a
turn's commitment costs O(its own changes); "why is it doing crypto per turn" is answered
with "it barely is, and only for what changed" — for the node and the desktop alike, with
no mode flag, no buffer, no replay, and the same byte-identical roots the circuit and light
clients verify against.
