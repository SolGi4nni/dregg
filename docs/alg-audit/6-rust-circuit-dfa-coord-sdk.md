# Alg-Complexity Audit 6 — Rust circuit + dfa + coord + sdk + apps

Read-only sweep of `circuit/**`, `dfa/**` (the crate the prompt calls `dregg-dfa`),
`coord/**`, `sdk/**`, `collective-choice/**`, `dregg-governance/**`, spot-checking
`starbridge-apps/**`. No source edited. Scope root: `~/dev/breadstuffs`, HEAD at audit time.

Ranking axis = complexity × frequency (per-prove / per-op / rare) × what-grows
(circuit rows·constraints / DFA-states / debits / tree-leaves). "Hot?" = on a
per-prove or per-op path vs. a build-once / rare path.

---

## TOP 5

### 1. DSL Lookup constraint re-scans the whole lookup table **per trace row** — O(rows × table-size) per prove
`circuit/src/dsl/circuit.rs:493` and `:496`
```rust
if let Some(table) = lookup_tables.iter().find(|t| &t.id == table_id) {   // O(#tables)
    let query: Vec<u32> = query_columns.iter().map(|&c| local[c].0).collect();
    if table.entries.iter().any(|entry| entry == &query) {                 // O(#entries × width)
```
- **Complexity:** O(#tables + #entries·width) **per constraint evaluation**, and
  `eval_constraints` (`:653`) invokes each constraint's evaluator once **per trace
  row** (`local`/`next` are consecutive rows). Total per prove/verify:
  **O(rows × #entries)** for a single Lookup constraint. Range/byte tables can hold
  2^16 entries, so this is a genuine quadratic blow-up in circuit size.
- **Hot-path?** YES — production. `circuit/src/derivation_air.rs:390` wraps this in
  the per-row `constraint_prover::Constraint.eval` closure; `backends/plonky3.rs:608`
  drives `DslCircuit`. Runs for every row of every DSL-descriptor AIR.
- **What-grows:** trace rows × lookup-table entry count.
- **FIX:** Build once, before the row loop: a `HashMap<TableId, &LookupTable>` for the
  table lookup, and per table a `HashSet<SmallVec<u32>>` (or a sorted `Vec` +
  `binary_search`) of its entries. Per-row cost drops to O(width) hashing. The set
  can be memoized on the `CircuitDescriptor`/AIR so it is not rebuilt per row (note
  `tables.clone()` at `derivation_air.rs:386` already clones per constraint).

### 2. `debits: Vec` used as an anti-replay set — linear `contains` per debit → O(n²) per slice
`coord/src/budget.rs:90` (`pub debits: Vec<DebitDigest>`), scanned at `:140`, `:162`, `:460`
```rust
pub fn try_debit_fresh(&mut self, amount: u64, digest: DebitDigest) -> ... {
    if self.debits.contains(&digest) {              // :140  O(debits)
        return Err(BudgetError::DuplicateDebit { digest });
    }
    self.try_debit(amount, digest)                  // pushes onto the Vec
}
```
- **Complexity:** O(debits) per fresh-debit check; a slice that accumulates `n`
  debits costs **O(n²)** over its life. `restore_unapplied` (`:460`) and
  `unwind_debit` (`:162`, `iter().position`) share the linear scan.
- **Hot-path?** YES per-op — this is the trustline draw gate
  (`draw_fires_iff_tryDebit`); every metered draw hits `try_debit_fresh`.
- **What-grows:** debit digests retained per budget slice (grows across a session
  until a certificate/rebalance prunes it).
- **FIX:** Keep a `HashSet<DebitDigest>` beside the ordered `Vec` (the Vec is still
  needed for the spending certificate's order); freshness check becomes O(1),
  `unwind_debit` removes from both.

### 3. Linear `position` on an already-SORTED `sorted_leaves` — O(n) where O(log n) is free
`circuit/src/heap_root.rs:260,379,701,754`, `circuit/src/cap_root.rs:522`, `circuit/src/openable_fields_root.rs:231`
```rust
// heap_root: sorted_leaves is sort_by_key(addr) at construction (:new)
pub fn position_of(&self, key: BabyBear) -> Option<usize> {
    self.sorted_leaves.iter().position(|l| l.addr == key)     // O(n) on a sorted vec
}
let pos = self.sorted_leaves.iter().position(|l| l.addr > key)?;   // lower-bound, O(n)
```
- **Complexity:** O(n) per lookup; the vectors are provably sorted
  (`heap_root` by `addr.as_u32()`, `cap_root` by `slot_hash.as_u32()`,
  `openable_fields` by `key_hash.as_u32()`), so O(log n) is directly available.
- **Hot-path?** Per-op prover-side witness generation (membership / update / insert
  witnesses). Not per-row, but per proof.
- **What-grows:** Merkle-tree leaf count.
- **FIX:** `sorted_leaves.binary_search_by_key(&key.as_u32(), |l| l.addr.as_u32())`
  for exact match, and `partition_point(|l| l.addr.as_u32() <= key.as_u32())` for the
  `addr > key` insertion point.

### 4. `insert_witness` rebuilds the entire tree from scratch on every insert
`circuit/src/heap_root.rs:370-396` (and the twin `cap_root`/`openable_fields` inserts)
```rust
let pos = self.sorted_leaves.iter().position(|l| l.addr > key)?;   // O(n)  (see #3)
let new_real: Vec<HeapLeaf> = ... splice ...;
let new_tree = CanonicalHeapTree::new(new_real, self.depth);       // O(n·depth) full rebuild
let new_pos = new_tree.position_of(key)?;                          // O(n) again (see #3)
```
- **Complexity:** `CanonicalHeapTree::new` re-sorts, re-dedups, and re-folds **all**
  levels: O(n·depth) node hashes. Building a tree of `n` leaves by repeated
  `insert_witness` is **O(n²·depth)**.
- **Hot-path?** Rebuild is inherent to producing the post-insert root over a
  sorted-array-backed tree (an insert shifts every leaf right of `pos`), so this is
  a rubric-3 "rebuild-from-scratch as input grows" flag rather than an outright bug.
  No batch-insert loop caller found in-tree today, so the O(n²) is latent — it fires
  only if a caller loops single inserts to build a large tree.
- **What-grows:** tree size.
- **FIX:** Provide a batch constructor (build once from the full leaf set) for bulk
  loads; for incremental inserts, recompute only the affected sibling path plus the
  shifted suffix rather than re-folding every level. At minimum swap the two linear
  scans for the binary searches of #3.

### 5. `Re::from_dfa` state-elimination is O(states³) with cloning, growing regexes
`circuit/src/../dfa/src/derivative.rs:376-441`
```rust
for k in 0..n {                       // eliminate every state
    let loop_re = g[k][k].clone().star();
    for i in 0..total {               // O(n)
        for j in 0..total {           // O(n)  → O(n³) node visits
            let through = g[i][k].clone().then(loop_re.clone()).then(g[k][j].clone());
            g[i][j] = g[i][j].clone().or(through);   // Re trees can grow superpolynomially
        }
    }
}
```
- **Complexity:** O(states³) triple loop, and each step `.clone()`s and concatenates
  `Re` trees whose size can grow exponentially in the worst case (classic
  state-elimination regex blow-up).
- **Hot-path?** RARE — this is the documented compatibility shim so
  `FilterTree::add_filter(Dfa)` can re-enter the lazy-derivative `inter` fold. The
  preferred path adds filters as `Re`/`Pattern` directly and never calls this.
- **What-grows:** DFA state count of the recovered filter.
- **FIX:** Keep steering callers to add filters as patterns (already the documented
  preferred path); if `from_dfa` must stay, eliminate states in ascending
  degree/heuristic order and cap the recovered-regex size, or bypass recovery by
  intersecting the flat DFA via product (`compiler::dfa_intersection`) instead.

---

## Honorable mentions (real, lower rank)

- **`Re::derive` / `Re::matches` deep-clone subtrees each byte** —
  `dfa/src/derivative.rs:298-306`: `Cat` does `l.derive(b).then((**r).clone())`,
  `Star` does `r.derive(b).then(self.clone())`. Each derivative step is O(regex
  size) in clones rather than O(1). Bites `Re::compile` (build-time, per pattern) and
  the streaming `Re::matches`; the live router uses the **flat** `Dfa::matches`
  (O(input), cached table) so per-message dispatch is unaffected. FIX: share
  subtrees via `Rc<Re>`.

- **`compose_tagged_union` / `Nfa::determinize` product construction** —
  `dfa/src/router.rs:341` and `compiler.rs:296`: state maps keyed by `Vec<StateId>` /
  `BTreeSet<StateId>` incur O(n) key comparisons per BTreeMap probe, and
  `winning_component` (`router.rs:437`) is O(#routes) per composite accept state.
  Build-once at table-compile time and inherent to subset/product construction —
  acceptable, noted for completeness.

- **`GovernedRouter::update_routes` rebuilds `Router::new` on every swap** —
  `dfa/src/router.rs:763`. Governance-rate (rare), fine.

## Checked and found NOT quadratic (context, so the sweep is legible)

- **`descriptor_ir2.rs` trace/histogram passes** — the `for base_row { for k in
  &desc.constraints }` shape (`:3691`, `:3709`, etc.) is O(rows × constraints), the
  irreducible cost of evaluating each constraint at each row. `fact_hist` / `chip_hist`
  use `BTreeMap` (O(log) inserts), not linear scans. The `expected_num.iter().find`
  at `:746` is over a small fixed chip-param list, at parse time. No O(gates²) pass
  found.
- **`dregg-governance` tally + `collective-choice`** — `derive_tally`
  (`dregg-governance/src/lib.rs:406`) is a single O(blocks) pass (by-design
  from-scratch audit path, called once per verification, not per-append); `cast`
  dedups via `HashSet` (`:475`). `collective-choice` uses `BTreeSet`/`HashSet` for
  electorate + nullifiers. Clean.
- **`cipherclerk` receipt/caveat chains** — `caveat_chain_hash` is incrementally
  folded (`:770`), appends use `receipt_chain.last()` (O(1)); the O(chain)
  `verify_receipt_chain` is an explicit full-verify op, not per-append. `find_token`
  linear scans (`:1403/1408`) are test-only callers over a small wallet.
- **`coord/coord_diff` + `entangled_diff`** — the `Vec::contains` scans
  (`coord_diff.rs:153`, `entangled_diff.rs:52`) are over silo counts / a tiny
  proof-mirror `accounts` vec — bounded-small, not growing hot sets.

---

### Summary table

| # | Site | Complexity | Hot? | Grows with | Fix |
|---|------|-----------|------|-----------|-----|
| 1 | `dsl/circuit.rs:493,496` Lookup eval | O(rows × entries)/prove | per-prove | trace rows × table size | HashMap tables + HashSet entries |
| 2 | `coord/src/budget.rs:140,460,162` debits | O(n²)/slice | per-op | debits per slice | HashSet<DebitDigest> |
| 3 | `heap_root/cap_root/openable_fields` `position` | O(n) vs O(log n) | per-proof | tree leaves | binary_search / partition_point |
| 4 | `heap_root.rs:387` insert rebuild | O(n²·depth) if looped | latent | tree size | batch build / incremental path |
| 5 | `dfa/src/derivative.rs:376` from_dfa | O(states³)+expo | rare | DFA states | prefer Re-add path / bound |
