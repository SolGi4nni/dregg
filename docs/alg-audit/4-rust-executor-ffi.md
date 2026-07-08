# Alg-complexity audit #4 — Rust executor + FFI + turn (read-only)

**Scope.** The Rust turn-execution path: `turn/src/executor/**`, the SWAP-inversion producer
(`exec-lean/src/lean_apply.rs`, `lean_shadow.rs`), the per-turn FFI (`dregg-lean-ffi/src/marshal.rs`,
`lean_direct.rs`), `build_pre_ledger`, and the single ingress gate `execute_via_producer`
(`node/src/executor_setup.rs`). Read-only recon — no source edited (the SWAP lane owns
`lean_shadow`/producer). Ranked by **complexity × frequency × what-grows**; the per-turn commit
path is the highest weight.

**Headline.** The scariest member is on the DEFAULT live commit path and is NOT in `lean_shadow`'s
turn-scoped marshalling (that path is clean, O(turn), refuted below) — it is the producer's
**full-ledger `template.clone()` per covered turn** in `wire_state_to_ledger`. Second is a genuine
**O(N_cells) linear scan of the whole ledger by public key** in bearer-cap authorization. `build_pre_ledger`,
`collect_id_map`, `ledger_to_wire_state`, and the FFI JSON wire are all **scoped to the turn**, not
the ledger — the rubric's biggest fear (per-turn re-walk of the whole ledger / cap-graph in the
shadow marshal) is REFUTED.

---

## Ranked table

| # | Name | file:line | complexity | hot path? | what grows | status | fix |
|---|------|-----------|-----------|-----------|-----------|--------|-----|
| 1 | Producer full-ledger clone per covered turn | `exec-lean/src/lean_apply.rs:1125` (template = full `pre_ledger`, `execute_via_lean` `:1440`) | O(N_cells + Merkle tree ~2N) alloc+copy | **YES — default producer commit path** (`execute_via_producer`, `node/src/executor_setup.rs:120`, DEFAULT ON) | **ledger** | **LIVE-DEFAULT** | return a touched-cell DELTA, apply in place; don't clone the whole `Ledger` per turn *(SWAP lane owns file)* |
| 2 | Ledger-wide scan by public key (bearer-cap auth) | `turn/src/executor/authorize.rs:1308` `ledger.iter().find(\|(_,cell)\| *cell.public_key()==*delegator_pk)` | O(N_cells) | **YES — authorization**, per bearer-cap (SignedDelegation) turn | **ledger** | **CONFIRMED** | add `HashMap<[u8;32] pubkey, CellId>` index to `Ledger` (maintain on insert/remove), O(1) lookup |
| 3 | Two full-ledger umem projections per committed turn | `turn/src/executor/execute.rs:1031` + `:1279` → `umem_snapshot` → `umem.rs:501` `for (_,cell) in ledger.iter()` | O(N_cells) × 2 | per committed turn **when `umem_witness_enabled`** (OFF by default) | **ledger** | **CONFIRMED, flag-gated** | project only the journal write-set (touched cells), not the whole ledger |
| 4 | Reject-path second full-ledger clone | `exec-lean/src/lean_apply.rs:1707` `Some(ledger.clone())` (verified-reject branch) | O(N_cells + tree) | producer path, per **rejected** covered turn (on top of #1) | **ledger** | **LIVE-DEFAULT (reject only)** | journal-scoped rollback of the cells Rust touched, not a whole-ledger snapshot *(SWAP lane owns file)* |
| 5 | Pipeline dep-hash linear `position` | `turn/src/executor/pipeline.rs:345` `turn_hashes.iter().position(\|h\| h==dep_hash)` in the per-turn `depends_on` loop | O(batch²) worst-case (dep-miss path) | batch-execution path only | pipeline **batch** (bounded per batch, not ledger) | **CONFIRMED, low** | build `HashMap<hash, idx>` once (`turn_hashes` already materialized `:318`), O(1) lookup |
| — | Strict-veto pre-state snapshot | `turn/src/executor/execute.rs:231` `Some(ledger.clone())` | O(N) | gated `strict_veto_enabled()` — OFF the hot path by comment/default | ledger | **CONDITIONAL** | same delta/journal-rollback lever as #4 if strict veto ever goes default |
| — | `build_pre_ledger` + closures | `exec-lean/src/lean_shadow.rs:1045` | O(turn) — `ledger.get()` is HashMap O(1); closures iterate only referenced cells | per turn | — | **REFUTED (turn-scoped)** | — |
| — | `ledger_to_wire_state` / `collect_id_map` / marshal wire | `lean_shadow.rs:1656` / `:962` / `marshal.rs` | O(turn·log turn) sort + linear push_str; `id_map` lookups HashMap O(1) | per turn | — | **REFUTED (turn-scoped, NOT O(ledger))** | — |
| — | `compute_state_hash` full-ledger hash | `turn/src/executor/finalize.rs:116` | O(N_cells) | — | ledger | **DEAD** (`#[allow(dead_code)]`) | — if ever revived, use the incremental Merkle `root()` |
| — | Refusal-vs-mutation conflict | `turn/src/executor/execute_tree.rs:581` | O(effects²) per action | per action | per-action effect count (bounded) | **BOUNDED** | — |

---

## 1. (Tier 1) Producer full-ledger clone per covered turn — the live-default exemplar

`node/src/executor_setup.rs:120` `execute_via_producer` is **THE one executor gate for every ingress**
(thin-HTTP, signed-envelope, blocklace-finalized) and `lean_producer_enabled` **defaults ON**
(`DREGG_LEAN_PRODUCER != 0`, `executor_setup.rs:109`). It calls `produce_via_lean`
→ `execute_via_lean` → `wire_state_to_ledger`, which reconstitutes the committed post-state by
**cloning the entire pre-state ledger**:

```rust
// exec-lean/src/lean_apply.rs:1125  (template == pre_ledger, passed at :1440)
let mut ledger = template.clone();
for (id, cell) in &out_cells { /* overwrite only the touched cells */ }
```

`template` here is the real, full `pre_ledger` (`execute_via_lean` passes `pre_ledger` as `template`,
`:1437-1444`). `Ledger::clone` copies `HashMap<CellId, Cell>` for **all** cells plus
`tree_levels: Vec<Vec<[u8;32]>>` (the whole materialized Merkle tree, ~2N nodes) — so every covered
turn pays an **O(N_cells + tree)** allocation and deep-copy even though only `out_cells` (the turn's
write-set) actually changed. As the ledger grows, per-turn latency grows linearly with total ledger
size, independent of turn size. This is the same "rebuild-from-scratch each turn where the input
grows" signature the finality gate had, now on the **execution** commit path.

The move-back (`produce_via_lean:1728` `*ledger = lean_ledger`) is cheap; the cost is entirely the
`template.clone()`. **Fix (SWAP lane owns the file — reported, not edited):** have
`wire_state_to_ledger` emit a **touched-cell delta** (`out_cells` + `cap`/`state` ops it already
computes) and apply it in place onto the caller's `&mut ledger`, so the producer pays O(write-set),
not O(ledger). The off-merkle side-tables it wants to preserve (`sovereign_commitments`, witness
sequences) already live in the caller's `ledger` — cloning them to preserve them is exactly the
work to remove.

## 2. (Tier 1) Ledger-wide scan by public key — bearer-cap authorization

```rust
// turn/src/executor/authorize.rs:1308
let delegator_cell = ledger
    .iter()
    .find(|(_, cell)| *cell.public_key() == *delegator_pk)   // O(N_cells) scan
    .map(|(_, cell)| cell);
```

On the `Authorization::SignedDelegation` bearer-cap path this scans **every cell in the ledger** to
find the delegator by public key. `CellId` is `derive(public_key, token_id)`, so the id is not
directly computable from the pk alone — but `Ledger` keeps **no `pubkey → CellId` index**
(`cell/src/ledger.rs:326`: `cells`, `sovereign_*`, `leaf_positions`, `migration_locks` — no pk map).
Every bearer-cap-authorized turn is O(N_cells); at scale this dominates authorization.
**Fix:** add a `HashMap<[u8;32], CellId>` (or `HashMap<[u8;32], SmallVec<CellId>>` if one pk can own
multiple token cells) to `Ledger`, maintained in `insert_cell` / removal, and replace the scan with
an O(1) lookup + the existing `has_access_including_delegation_at` check.

## 3. (Tier 2) Two full-ledger umem projections per committed turn (flag-gated)

When `umem_witness_enabled` is set, each committed turn snapshots the **whole** executor state twice
(pre at `execute.rs:1031`, post at `:1279`), each via `umem::project_executor_state` →
`umem.rs:501` `for (_, cell) in ledger.iter()` (+ sovereign commitments). That is O(N_cells) × 2 per
turn on the commit path. It is **off by default** (recursion-gated), so it is Tier 2, but if the
umem witness lane is turned on for a large ledger it re-projects the entire ledger every turn.
**Fix:** the journal already names the write-set; project only the touched cells (an incremental
`project_diff` over `journal.entries()`) rather than the full ledger pre/post.

## 4. (Tier 2) Reject-path second full-ledger clone

`produce_via_lean` takes the whole-ledger snapshot `Some(ledger.clone())` (`lean_apply.rs:1707`)
only on the verified-reject branch, to restore the pre-state after the demoted Rust reference
mutated `ledger`. Correct but O(N_cells + tree) per rejected covered turn, on top of #1's clone.
**Fix (SWAP lane owns):** roll back only the cells the Rust reference journaled, not a whole-ledger
snapshot.

## 5. (Tier 3) Pipeline dep-hash linear `position`

`turn/src/executor/pipeline.rs:345` does `turn_hashes.iter().position(|h| h == dep_hash)` inside the
per-turn `depends_on` loop inside the topo-order loop — O(batch²) worst-case, but only on the
dependency-miss branch and bounded by the pipeline **batch** (not the ledger/history). `turn_hashes`
is already materialized at `:318`; build a `HashMap<[u8;32], usize>` once and look up O(1).

---

## What is clean (refuted, with reason)

* **`build_pre_ledger` + delegation-parent / held-cap-target closures** (`lean_shadow.rs:1045`) —
  iterates only the turn's **referenced** cells; `Ledger::get` / `id_map.contains_key` are HashMap
  O(1). Bounded by turn size, NOT the ledger. REFUTED.
* **`collect_id_map`** (`lean_shadow.rs:962`) — walks only the call forest; O(turn). REFUTED.
* **`ledger_to_wire_state`** (`lean_shadow.rs:1656`) — iterates the turn-scoped `id_map`
  (`sort_by_key` O(k log k), k = turn cells); every cap-edge lookup is `id_map.get` HashMap O(1).
  Turn-scoped, NOT O(ledger). REFUTED.
* **Per-turn execution FFI wire** (`marshal.rs` `marshal_turn_hosted`, `serialize_*`) — a single
  linear `push_str` pass over the **turn-scoped** `WireState`/`WireTurn`; the `CString` payload is
  O(turn), not O(ledger) or O(history). This is the rubric's item-4 concern, and it is CLEAN —
  contrast the finality `build_wire` (`node/src/finality_gate.rs`) which reformats the whole lace per
  poll (known, out of this scope).
* **`compute_state_hash`** (`finalize.rs:116`) — O(N_cells) full-ledger hash, but `#[allow(dead_code)]`
  (the live receipt path uses the incremental Merkle `root()`). DEAD.
* **Strict-veto snapshot** (`execute.rs:231`) — O(N) `ledger.clone()`, but gated on
  `strict_veto_enabled()` (off the hot path by default). CONDITIONAL.
