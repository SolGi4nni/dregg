# Light-Client × AAFI-IMT Impact Analysis

**Status:** scoping / impact analysis (read-only investigation, no code changed). Grounds the
ember decision on GAP #5 closure (`docs/reference/CARRIER-CENSUS.md` "GAP #5 CLOSURE OBSTRUCTION").
**Date:** 2026-07-12. **Question:** does the deployed architecture actually *depend* on the heap
root's input-order-independence (`heap_root.rs:1019`), or does it reconstruct state by *replaying*
the ordered history — making AAFI-IMT's insertion-order-dependent root tolerable (ember's lean) vs
load-bearing (reconsider sparse-by-addr)?

**Verdict up front: order-independence is NOT load-bearing on any trust path. The sync model is
REPLAY of the tau-finalized turn history — the node always has the canonical order. AAFI-IMT is
LOW-to-MEDIUM pain; ember's lean is confirmed. A split (AAFI on the append-only accumulators first)
minimizes it.**

---

## 1. The light-client / sync model: REPLAY, not snapshot

A dregg node reconstructs state by **re-executing the tau-finalized block sequence through the
TurnExecutor**, not by recomputing a root from a state snapshot. Ground truth:

- **`node/src/execution_cursor.rs:1-40`** — the cursor "executes exactly the finalized blocks not
  yet executed, in the CURRENT tau order — execution is a set difference, order is the current
  tau." State is a pure function of the ordered finalized history; a mid-prefix insertion "executes
  late, exactly once."
- **`node/src/committee_replay.rs:24-45`** — `derive_from_lace` "folds the finalized membership
  blocks over a fresh `ConstitutionManager`, **in the same order the executor served them**"
  (`ordering::tau`). The constitution is "a PURE VIEW of the chain," rebuilt by replay on every boot.
- **`node/src/catchup.rs:1-45`** — a joining/lagging node buffers orphan blocks and applies them in
  **causal order**, re-running full block verification; convergence is on the content-addressed
  keyset (`CatchupConverges.lean`).
- **`node/src/blocklace_sync.rs:1-18`** — "Running tau() ordering to produce the finalized total
  order" then "Processing finalized turns through the TurnExecutor."

The `chain/`, `eth-lightclient/`, `cosmos-lightclient/` light clients verify **FOREIGN** chains
(Ethereum beacon/MPT, Cosmos, Solana) — foreign schemes, irrelevant to the dregg heap. The EVM
**settlement** path (`chain/src/lib.rs:14-17`) is `settle(a,b,c, genesisRoot, finalRoot, numTurns,
chainDigest)` — a **whole-history wrapped SNARK** proving `genesisRoot → finalRoot` over the turn
sequence: it verifies a *fold-over-ordered-history proof*, it does **not** recompute a state root
from a snapshot map. **No dregg trust path snapshot-syncs its own state root from an (addr→value)
map.**

## 2. Where order-independence is actually consumed (and whether it's needed)

`root_is_input_order_independent` (`circuit/src/heap_root.rs:1020`, mirror `cap_root.rs:1129`) +
the "cell & executor compute byte-identical roots from the (addr→value) map" invariant
(`heap_root.rs:15-25`) have these consumers. **None require order-independence for correctness; each
has the canonical insertion order available (it IS the tau-finalized turn sequence, INV-6).**

| Consumer | File:line | Recomputes root from… | Needs order-indep? |
|---|---|---|---|
| Cell recompute | `cell/src/state.rs:519,977-1017` (`compute_heap_root`, `rebuild_heap_cache`, `set_heap`) | the `BTreeMap<(coll,key),value>` (sorts by addr) | **No** — but must gain a persisted `addr→slot`, or replay the cell's HeapWrite order |
| Executor↔cell parity (GENTIAN) | `heap_root.rs:15-18`, `circuit/tests/heap_root_cell_circuit_differential.rs` | both build a sorted `CanonicalHeapTree` | **No** — holds if both derive slots from the same canonical append order |
| Nullifier/commitment reconstruct-from-store (INV-2/3) | `cell/src/nullifier_set.rs:691-705`, `cell/src/commitment_set.rs:1-21,165`, `node/src/blocklace_sync.rs:4455-4459` (`load_all_nullifiers`) | the **flat persisted `(nf,value)` store**, rebuilt via `CanonicalHeapTree8::new` | **No** — append-only; canonical order = tau spend sequence; persist a seq column or replay |
| Cross-chain whole-cell root (producer) | `sandstorm-bridge/src/bridge.rs:1513-1533`, `bridge/src/midnight_inclusion.rs:15` | producer's `/var` map (`grain_cell_commitment` = `compute_heap_root(heap_leaves())`) | **No** for the verifier — external checks open a **leaf+path** (position-carrying); whole-root recompute is producer-side |
| Flat ledger / cells root | `node/src/api.rs:4271-4304` (`get_cell_proof`), `turn/src/rotation_witness.rs:293` (`cells_root`) | full leaf set, **separate BLAKE3-sorted-by-id flat root** (not the heap tree) | **N/A** — different scheme, not the AAFI target unless separately migrated |

The load-bearing proof that order-independence is a *convenience, not a necessity*:
`nullifier_set.rs:691-705` **explicitly reconstructs `S ∪ {spend}` "in a DIFFERENT insertion order"
and asserts the same root** ("INV-2 continuity, insertion-order-independent"). It exploits
order-independence to avoid tracking order — but the canonical order (the tau-finalized spend
sequence) *exists and is agreed* (INV-6, `NULLIFIER-ACCUMULATOR-UNIFICATION.md §2`), so it can be
persisted or replayed instead.

## 3. The PAIN list under AAFI-IMT (order-dependent root)

1. **Cell recompute (`cell/src/state.rs`)** — the cell holds `heap_map: BTreeMap` with **no slot
   info**. AAFI roots need each entry's append slot. **Fix:** persist an `addr→slot` map alongside
   `heap_map` (or replay the cell's HeapWrite order on load). *Bonus:* AAFI makes a fresh insert an
   **append at a free slot — no suffix shift**, retiring the current O(n) `rebuild_heap_cache` on
   every fresh address (`state.rs:994-1016`); value-updates stay O(log n). **Effort: medium** (add a
   persisted slot table + rewrite `set_heap`/`rebuild_heap_cache`; the rebuild gets *cheaper*).
2. **Executor↔cell parity** — still holds **iff** executor and cell derive slots from the *same*
   canonical order. **Fix:** share one slot-assignment routine (append = next free slot in tau-effect
   order). **Effort: low-medium** (shared code; the GENTIAN differential re-pins the new scheme).
3. **Nullifier/commitment/revoked reconstruct-from-store (INV-3)** — `load_all_nullifiers` →
   `CanonicalHeapTree8::new` currently ignores order. **Fix:** persist an insertion sequence (a `seq`
   column on the `(nf,value)` record) **or** reconstruct by replaying finalized spends in tau order.
   **Effort: low** — append-only, the order is canonical + already durable in block order.
4. **Cross-chain producer roots (sandstorm / midnight)** — the *producer* computes the whole-cell
   root; needs the slot map from #1. External **inclusion proofs already carry positions** (leaf +
   sibling path), so the *verifier* is unaffected. **Effort: low** (falls out of #1).
5. **State-equality / dedup by root** — none found on the trust path that compares two *independently
   built* maps by root; equality is either "reconstructed_root == committed_root" (same builder,
   fine) or SNARK-verified. **Effort: none.**
6. **VK + fixtures + differential tests** — every committed heap root changes ⇒ VK regen + all
   heap-root fixtures + differential rebuild. **Already owed by ANY redefinition** (census names it);
   the dominant mechanical cost, orthogonal to the sync question.

The AIR side (2nd shared-sibling path + `eval_lex_lt` range gate) is fixed-width-expressible and
**not** the blocker (census confirms). The blocker was the deployed compacted-array layout; AAFI's
stable positions remove it.

## 4. The split option — VIABLE and recommended

**Append-only (grow-only) sets:** nullifier set (`cell/src/nullifier_set.rs`), commitment set
(`cell/src/commitment_set.rs:12` "GROW-ONLY"), revoked-credential set (`turn/src/rotation_witness.rs:275`
"the registry is grow-only"). For these the canonical **insertion order = the tau-finalized
spend/create/revoke sequence** = INV-6 agreed across nodes. Order-dependence is a **non-issue**: the
order is canonical, deterministic, agreed, durable, and available (persist a seq or replay). **AAFI
is the natural form** — and GAP #5's double-spend lives *precisely* in these absence proofs
(nullifier/commitment/cell-creation), so AAFI here **directly closes the deployed gap**.

**Mutable maps:** the cell heap (`HeapWrite` value-updates + fresh inserts + removes) and the cells
existence set. AAFI handles updates fine (stable slot, in-place value change) and turns removes into
tombstones (never shift). The only added cost is the persisted `addr→slot` per cell (#1).

**Recommendation — STAGE:** migrate the **append-only accumulators to AAFI-IMT first** (highest
soundness payoff, lowest pain — order is free), then decide the mutable cell heap separately (AAFI +
slot-map, or keep sorted with producer-trust, or sparse-by-addr). This aligns with the
sorted-Merkle-accumulator unification direction the census already endorses
("IMT is its natural form").

## 5. Verdict

**AAFI-IMT's order-dependence is TOLERABLE. ember's lean is confirmed. Pain is LOW-to-MEDIUM and
is dominated by the mechanical redefinition (VK + fixtures + slot persistence) that *any* fix owes —
not by the sync model.**

- The architecture **reconstructs state by REPLAY** of the tau-finalized turn history; it always has
  the canonical order. **No snapshot-sync of dregg's own state depends on order-independence.**
- Order-independence is currently **exploited as a convenience** in the reconstruct-from-flat-store
  paths and the cell recompute — but the canonical insertion order *exists* (tau sequence) and can
  be persisted (a seq/slot column) or replayed. It is a nice-to-have, not load-bearing. The
  `nullifier_set.rs:691-705` test proves this by *choosing* a different order and getting the same
  root — a property the migration replaces with "the persisted/replayed canonical order."
- The one genuine friction: **the cell (and cross-chain producers) must persist an `addr→slot`
  map** (or replay per-cell HeapWrite order) — bounded, local work the census already names.
- **sparse-by-addr's advantage** (keeping order-independence, avoiding slot persistence) buys
  insurance the architecture doesn't need — it already replays — at ~2× path depth. Not worth it
  over AAFI on this evidence.
- **Recommended path:** AAFI-IMT, split — append-only accumulators first (near-zero conceptual pain,
  closes GAP #5's double-spend), mutable cell heap second.
