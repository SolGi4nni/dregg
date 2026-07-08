# ALG-COMPLEXITY AUDIT — master board (2026-07-08)

Systematic 6-lane sweep of the whole tree for the `tauOrderFast`-class derp:
**`List`/`Vec` linear-scan where a `HashMap`/`HashSet` belongs, or recompute where a cache belongs,
on an input that grows with the chain / ledger / history.** Per-lane detail: `docs/alg-audit/{1..6}-*.md`.

Verdict: the codebase was *architected* against the worst trap (per-turn work is scoped to the turn's
touched-cell set — `build_pre_ledger`, `execute_finalized_turn`, the exec FFI wire are all O(turn)),
but a cluster of **history-growing membership gates** and **per-turn full-ledger clones** slipped through.

## RANK (severity = complexity × frequency × what-grows)

### 🔴 Tier 1 — live commit path, grows unboundedly (fix first)
| # | derp | file:line | complexity | grows with | fix | class |
|---|------|-----------|-----------|-----------|-----|-------|
| 1 | Nullifier double-spend gate `nf ∈ k.nullifiers` | `RecordKernel.lean:935` | O(\|nullifiers\|)/spend | **all history** | `HashSet` twin in kernel state | needs-design (state-twin, seed) |
| 2 | Credential-revocation gate `revoked.contains` | `FullForestAuth.lean:481`(+500,648) | O(\|revoked\|)/action | **all history** | `HashSet` twin | needs-design (state-twin, seed) |
| 3 | Producer full-ledger `template.clone()` | `exec-lean/src/lean_apply.rs:1125` | O(N_cells)/turn | ledger | touched-cell delta | needs-care (in SWAP lane's file) |
| 4 | api full-ledger clone ×2 per submit/faucet | `node/src/api.rs:2994,3300,…` | O(N_cells)/turn | ledger | journal touched cells | **FIXING** (lane ab704ee) |

### 🟠 Tier 2 — hot path, quadratic-per-call (cheap wins, disjoint Rust)
| # | derp | file:line | complexity | grows | fix | class |
|---|------|-----------|-----------|-------|-----|-------|
| 5 | `has_equivocation_in_past` unmemoized (Rust `tau` dominant term) | `blocklace/src/ordering.rs:167` | O(waves·P·N²)/poll | DAG | precompute equivocator set once per `tau` | **cheap win** |
| 6 | Pubkey ledger scan in bearer-cap auth | `turn/src/executor/authorize.rs:1308` | O(N_cells)/bearer-turn | ledger | `HashMap<pubkey,CellId>` index | **cheap win** |
| 7 | DSL Lookup re-scans lookup table per trace row | `circuit/src/dsl/circuit.rs:493` | O(rows·entries)/prove (2^16) | table | `HashMap`+per-table `HashSet` built once | **cheap win** |
| 8 | coord budget `debits: Vec` as anti-replay set | `coord/src/budget.rs:140,460` | O(n²)/session | session debits | `HashSet<DebitDigest>` beside the Vec | **cheap win** |
| 9 | Catch-up `present_set(lace)` rebuilt per block | `node/src/catchup.rs:276` | O(B·N) sync | DAG | one `HashSet` seeded once, insert-on-accept | **cheap win** |
| 10 | Linear `position` on SORTED `sorted_leaves` | `heap_root.rs:260,379,…` `cap_root.rs:522` | O(n)→O(log n) | heap | `binary_search_by_key`/`partition_point` | **cheap win (trivial)** |
| 11 | `get_starbridge_receipts` full-chain scan | `node/src/api.rs:2350` | O(history)/request | receipts | raw-byte compare + agent/turn_hash index | cheap win |
| 12 | `poll_finalized_blocks` clones whole DAG 2–3×/poll | `node/src/blocklace_sync.rs:962,1101,1270` | O(N) alloc/poll | DAG | `Arc`-snapshot, move into spawn_blocking | cheap (in throughput lane's file) |

### 🟡 Tier 3 — storage Merkle full-recompute-per-op (route through incremental MMR)
| # | derp | file:line | fix |
|---|------|-----------|-----|
| 13 | `BlindedQueue::commit` dual-Merkle rebuild | `storage/src/blinded.rs:190` | incremental MMR (`bucket_commitment.rs` has one) |
| 14 | `MerkleQueue::recompute_root` per enq/deq | `storage/src/queue.rs:182` | incremental |
| 15 | umem `lay` whole-heap boundary root per write | `dregg-umem/src/lib.rs:167` | incremental |

### 🟢 Tier 4 — Lean model code (denotational; `@[implemented_by]` twins, off live path today)
StrandAdmission O(committee²) live-but-rare; distinctApprovers, HistoryAggregation.logRoot (MMR),
DirectoryLaws Dir, EpochReconfig, Polis Datalog `fire` (governance) — all `List`-model mirrors of
deployed Map/MMR structures. Fix the `tauOrderFast` way (`@[implemented_by]`, proofs untouched) when
they reach the live path or scale demands.

### CHECKED & CLEARED (sweep is legible)
per-turn exec (touched-scoped), execute_finalized_turn (actor-cell only), ExecutionCursor/finalization_votes
(HashSet), sync_receipt_index (incremental), cipherclerk (O(1) append), the `dregg-dfa` router (lazy
determinization + cached flat table), descriptor_ir2 trace (irreducible O(rows·constraints)), governance
tally (HashSet). Restart recovery = checkpoint + touched overlay (not full replay).

## PLAN
- **Cheap-wins blitz** (Tier 2, #5–11): disjoint Rust `HashSet`/`HashMap`/`binary_search` swaps, no seed
  rebuild, no proof impact — batch now.
- **Clone cluster** (#3,#4): journal/delta — #4 firing; #3 after the SWAP lane frees `lean_apply.rs`.
- **State-twins** (#1,#2): the scariest but need a carried-in-state HashSet twin + seed rebuild — considered batch.
- **Storage Merkle** (#13–15): route through the incremental MMR — medium.
