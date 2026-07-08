# Alg-Complexity Audit 5 — Rust ordering + blocklace + net + storage

Read-only complexity audit. Scope: `blocklace/src/ordering.rs` (the Rust `tau` /
`PastCache` / `compute_rounds` / `build_ordering_blocklace`), `net/**`,
`storage/**`, `dregg-umem/**`. No source edits made.

Ranking axis = complexity × frequency (per-poll / per-op / per-message /
startup) × what-grows.

Symbol/path note: the prompt's `dregg_blocklace::ordering` lives at
`blocklace/src/ordering.rs`; `dregg-net` = `net/`; `dregg-storage` = `storage/`.

Confirmed hot-path fact: `ordering::tau` is invoked **per finality poll** over
the whole (growing) blocklace — `node/src/blocklace_sync.rs:1127`/`1137` ("the
Rust `ordering::tau` order for **THIS poll**"), and again in
`node/src/finality_gate.rs:317/518/661`. Everything below in §1–§4 pays its cost
on every poll.

---

## TOP 5

### 1. `tau` finality is ~O(waves · P · N³) per poll, rebuilt from scratch every call

The whole finalization pipeline is a stack of full-past scans nested inside each
other, and it is re-run on every poll against the growing DAG.

`blocklace/src/ordering.rs:284` (`ratifies`, the middle of the nest):

```rust
let approving_count = participants
    .iter()                                   // × P participants
    .filter(|&&participant| {
        past.iter().any(|&bid| {              // × N blocks in observer's past
            ... && approves(cache, blocklace, rounds, &bid, leader_id, leader_creator)
                                              //   approves → has_equivocation_in_past = O(N)
```

- **Nest:** `find_all_final_leaders` loops over waves (`R/wavelength`), each wave
  calls `is_super_ratified` (`ordering.rs:305`) which scans up to `N` wave-end
  blocks and calls `ratifies` on each; `ratifies` is `O(P · N)` calls to
  `approves`, and `approves` calls `has_equivocation_in_past` which is `O(N)`.
  Net `ratifies` ≈ `O(P·N²)`, `is_super_ratified` ≈ `O(P·N³)`,
  `find_all_final_leaders` ≈ `O(waves · P · N³)`. The `tau` coverage loop
  (`ordering.rs:520-537`) re-runs `ratifies` over all wave-end blocks a second
  time per final leader.
- **Complexity:** ~`O(waves · P · N³)`, `N` = blocks in blocklace.
- **Hot path?** YES — per finality poll (`blocklace_sync.rs:1127`).
- **What grows:** the blocklace DAG (`N`), and `waves` grows with rounds.
- **FIX:** (a) precompute the equivocator set once per `tau` (see §2) so
  `approves` is O(1); (b) memoize `ratifies(observer, leader)` and
  `approves(observer, leader)` per `(observer, leader)` in the same
  `PastCache`-style memo (they are recomputed identically in `is_super_ratified`
  and again in the coverage loop); (c) count "distinct approving participants"
  by iterating the observer's past ONCE and marking a `HashSet<creator>`, rather
  than `participants.iter()` × `past.iter().any()` — turns `O(P·N)` into `O(N)`.

### 2. `has_equivocation_in_past` — the innermost loop — rebuilds an O(N) group map on every `approves` call, unmemoized

`blocklace/src/ordering.rs:167-180`:

```rust
let past = causal_past_inclusive(cache, blocklace, observer);
let mut by_round: HashMap<u64, Vec<BlockId>> = HashMap::new();
for &bid in past.iter() {                     // O(N) EVERY call
    if let Some(block) = blocklace.get(&bid)
        && &block.creator == creator
        && let Some(&round) = rounds.get(&bid) { by_round.entry(round).or_default().push(bid); }
}
by_round.values().any(|blocks| blocks.len() > 1)
```

- Only the causal-past **set** is memoized (`PastCache`); this equivocation
  regrouping is NOT. It is called from `approves` (`ordering.rs:263`) — i.e.
  `O(P·N)` times per `ratifies` — and again in the `tau` new-blocks filter
  (`ordering.rs:547`). It re-scans the entire past and allocates a fresh
  `HashMap<u64, Vec<BlockId>>` each time.
- **Complexity:** `O(N)` time + allocation **per call**, called an ~`O(waves·P·N²)`
  number of times → dominant term of §1.
- **Hot path?** YES — the innermost body of the poll.
- **What grows:** `N` (blocks) × how often ratification runs.
- **FIX:** equivocation ("a creator has ≥2 blocks at the same round, visible
  from observer's past") is monotone in the past set. Compute the global
  equivocator set ONCE per `tau` from `(creator, round) → count` over all blocks
  (`compute_rounds` already has the rounds), then `has_equivocation_in_past` is a
  set-membership test filtered by "is this equivocator in the observer's past" —
  O(1)–O(#equivocators). Removes the per-call O(N) regroup entirely.

### 3. `BlindedQueue::commit` rebuilds the FULL dual Merkle tree (BLAKE3 + Poseidon2) on every single commit → O(n²)

`storage/src/blinded.rs:189-190` then `:331-339`:

```rust
self.commitments.push(commitment);
self.recompute_root();                         // full rebuild, per commit
...
fn recompute_root(&mut self) {
    let blake3_leaves: Vec<[u8;32]> = self.commitments.iter().map(|c| c.blake3).collect();
    let poseidon2_leaves: Vec<[BabyBear;4]> = self.commitments.iter().map(|c| c.poseidon2).collect();
    self.commitment_root = MerkleRoot::from_leaves(&blake3_leaves, &poseidon2_leaves);
}
```

- `from_leaves` → `poseidon2_binary_root` (`commitment.rs:602`) is `O(n)`
  Poseidon2 compressions (each parent = 6× `hash_4_to_1`, hundreds of field
  mults) rebuilt from the leaf layer every time. Adding `n` commitments to a
  queue is `Σ O(k) = O(n²)` Poseidon2 hashes.
- **Complexity:** `O(n)` (with a large Poseidon2 constant) per commit → `O(n²)`
  to fill a queue of `n`.
- **Hot path?** YES — issuer/dealer per-commit path.
- **What grows:** the blinded commitment set.
- **FIX:** keep an incremental/append-friendly accumulator. Either (a) an MMR
  (`bucket_commitment.rs` already has one — `MMR.mroot`) that appends in
  `O(log n)`, or (b) batch commits and reseal once, or (c) cache internal tree
  layers and only recompute the `O(log n)` path affected by the new rightmost
  leaf.

### 4. `MerkleQueue::recompute_root` rebuilds the whole pending-window root on every enqueue/dequeue → O(n²)

`storage/src/queue.rs:182` / `:213` / `:406-415`:

```rust
self.leaf_hashes.push(hash_entry(&entry));
self.entries.push(entry);
self.recompute_root();                         // per enqueue AND per dequeue
...
fn recompute_root(&mut self) {
    let pending = &self.leaf_hashes[self.head..];
    ...
    self.root = merkle_root(pending);          // full tree over ALL pending leaves
}
```

- Partially mitigated: `leaf_hashes` is cached so entry preimages are not
  re-hashed (comment at `:407`). But the **tree** is still rebuilt over the
  entire `head..tail` window on every op. Durable, WAL-backed; each
  `enqueue_durable`/`dequeue_durable` pays `O(pending)`.
- **Complexity:** `O(n)` per op → `O(n²)` over `n` enqueues.
- **Hot path?** YES — per queue op.
- **What grows:** the pending queue window.
- **FIX:** same as §3 — incremental root over the sliding `head..tail` window
  (cache internal layers; enqueue touches one rightmost path, dequeue advances
  `head` and invalidates one left path). Or an MMR/segment-tree so ops are
  `O(log n)`.

### 5. umem `lay` recomputes the whole-heap boundary root (and O(m)-scans the heap) on every write

`dregg-umem/src/lib.rs:167` + `:183`, resealing through
`cell/src/state.rs:898-900`:

```rust
state.heap_map.retain(|&(c, _), _| c != coll);   // O(m) scan of ENTIRE heap, per lay
...
state.reseal_heap_root();                         // → compute_heap_root(&heap_map)
// state.rs:899:  self.heap_root = compute_heap_root(&self.heap_map);  // O(m) over whole heap
```

- `compute_heap_root` (`state.rs:434`) walks the entire `BTreeMap` and folds a
  sorted-Poseidon2 root over **all** leaves of **all** collections — not just the
  collection being laid. Every `lay`/`lay_record` is `O(m)` (heap size) in both
  the `retain` scan and the reseal, with the large Poseidon2 constant.
- **Complexity:** `O(m)` per write, `m` = total heap leaves across all
  collections. `k` writes into a heap that grows to `m` → up to `O(k·m)`.
- **Hot path?** Per working-memory / registry write.
- **What grows:** the cell heap (all collections combined).
- **FIX:** the boundary root is a single sorted-Poseidon2 root by design, but it
  need not be recomputed per `lay`. Either (a) reseal lazily (mark dirty; reseal
  once before a boundary is read/passed), or (b) keep the leaves in a Merkle
  structure keyed by `heap_addr` so a `lay` updates only the `O(log m)` affected
  paths. The `retain` at `:167` should also index by collection to avoid the
  full-heap scan.

---

## SECONDARY (note, lower rank)

- **`is_cordial` recomputes ALL rounds (full Kahn) to read one block's round** —
  `blocklace/src/ordering.rs:570` `let (rounds, _) = compute_rounds(blocklace);`.
  `compute_rounds` is `O(V+E)` over the whole DAG; `is_cordial` uses it only to
  look up `rounds[block_id]` and the previous round's creators. If called per
  block admission this is `O(N)` per block → `O(N²)`. FIX: pass in a cached
  rounds map, or cache rounds incrementally as blocks are inserted.

- **Gossip anti-entropy scans the entire message cache (all topics) per request**
  — `net/src/gossip.rs:2417` `for (hash, cached) in s.message_cache.iter()`
  filters by `topic_id` inside the loop. `O(total_cache)` per `AntiEntropy`
  message, per peer, per interval; no per-topic index. Bounded by cache cap but
  scales with it. FIX: a `HashMap<TopicId, {hash}>` index so the scan is
  `O(#msgs in that topic)`.

- **`BoundedPendingIhaves::remove` is an O(n) `retain` on a hash-indexed deque**
  — `net/src/gossip.rs:478` `self.entries.retain(|(k, _)| k != key);` after an
  `index.remove`. Called on Graft resolution; bounded by `MAX_PENDING_IHAVES` but
  it is a linear scan of a structure that otherwise has an O(1) index. FIX:
  tombstone-on-`index`, lazily skip on eviction; or store the deque position in
  the index.

- **Erasure `encode` is quadratic in shard count** — `storage/src/erasure.rs:175`
  `let n_parity = n_data * (self.expansion_factor - 1);`. Parity count scales
  WITH `n_data`, so Reed–Solomon `encode` is `O(n_data² · chunk_size)`; for a
  large blob `n_data ≈ size/chunk`, i.e. `O(size²/chunk)`. This is inherent to a
  rate-proportional RS parity choice, but note it is quadratic in the number of
  shards, not linear. FIX (if large blobs matter): cap absolute parity count, or
  chunk into fixed-size RS groups (systematic RS per group) so encode is linear
  in blob size.

- **`PastCache` lifetime — item 3(a) answer:** it is created **fresh per `tau`
  call** (`ordering.rs:500` in `tau_with_config`, `:807` in `tau_unified`) and
  discarded when `tau` returns — see the doc comment at `ordering.rs:32-40`
  ("Created fresh per ordering call"). So, exactly like the Lean model, **nothing
  survives across polls**: every poll re-BFSes every block's causal past from
  scratch. Within a single `tau` it does correctly memoize the past-set; the
  cross-call recompute is the cost. FIX (larger): a persistent
  incremental-finality cache keyed on the blocklace frontier — new blocks extend
  the memo rather than invalidating it (the DAG is append-only), so a poll pays
  only for blocks added since the last poll.
