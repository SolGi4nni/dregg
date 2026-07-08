# Perf-bomb audit — the `tauOrderFast` O(n³) List-cache class

**Scope.** Hunt for the signature we just killed in `BlocklaceFinality.lean` (`mkPastCache`/
`cachedPast`/`roundLookup`, `List.find?`/`.dedup`/`.filter` over a growing DAG, rebuilt from scratch
every call → O(n²)/O(n³) that worsens as the chain runs). Fixed via `@[implemented_by]` HashMap/HashSet
twins in `02c4e1709`. This is **recon only** — no fixes applied, live mesh not disturbed (read curls +
faucet submits only).

**Method.** (A) static grep of the `@[export]`-reachable Lean + the Rust hot paths; (B) live profile —
submitted 35 faucet turns against hbox (`192.168.50.39:8420`, genesis `ed6c8ba1`) spaced ~4 s to grow
the DAG (finalized count climbed 12 → 312 over the window), watched `node0.log`.

**Headline.** Only ONE genuinely new same-class suspect turned up (`hbBool`, Tier 2). The scariest
member of the class — the per-poll finality recompute — is the ALREADY-KNOWN one and is **only
partially killed**: the `@[implemented_by]` twin fixed the *within-a-single-call* blow-up, but the whole
gate is still recomputed from scratch **every poll**, with no cross-poll incremental cache. Everything
else that pattern-matched the signature (per-turn executor, restart reconstruction, strand-admit,
decide-refines, catchup) is **bounded** — it does NOT grow with the ledger/DAG — and is refuted below
with the reason.

---

## Ranked table

| # | Name | file:line | what grows | hot path? | cadence | status | fix |
|---|------|-----------|-----------|-----------|---------|--------|-----|
| 1 | Verified finality gate, per-poll full recompute | `node/src/blocklace_sync.rs:935` `poll_finalized_blocks` → `node/src/finality_gate.rs:148` `compute_order` → Lean `BlocklaceFinality.tauOrderFast` (`metatheory/Dregg2/Distributed/BlocklaceFinality.lean:531`) | LACE / DAG size N | **YES — finality executor (serial), commit path** | per **poll** (every block produced/received, 150 ms debounce) | **LIVE-CONFIRMED**, PARTIALLY mitigated | cross-poll **incremental** cache / stateful Lean handle — `@[implemented_by]` alone does NOT make it incremental |
| 2 | `hbBool` / `hbReach` List-backed causal reachability | `metatheory/Dregg2/Exec/DistributedExports.lean:545` `directDepsOf` + `:565` `.dedup` + `:561` `hbReach` (export `dregg_coord_causal_order`, caller `coord/src/causal.rs:46`) | DAG (`d.turns`) | no — coord/2PC path, NOT faucet/finality | per coord causal-order query | **STATIC-SUSPECTED** (new) | `@[implemented_by]` HashMap adjacency for `directDepsOf` + HashSet frontier — the exact `tauOrderFast` recipe |
| 3 | `admittedLeaders` / `finalLeaderAtAdmitted` over waves | `metatheory/Dregg2/Distributed/StrandAdmission.lean:200` (`List.range waveCount` → per-wave `isSuperRatified`/`ratifies`, the un-cached finality primitives) | waves (DAG depth) | no — admission only | per strand admission (rare) | **STATIC-SUSPECTED, low** | thread the `PastCache`/`RoundCache` twins (as `tauOrderFast` does) if admission ever moves onto a hot path |
| — | Per-turn Lean executor cell resolver | `metatheory/Dregg2/Exec/FFI.lean:2685` `w.cells.find?` (+ `caps`/`bal`/`lifecycle`/`delegate` sibling resolvers) | — | per-turn commit path | per turn | **REFUTED** (bounded) | — |
| — | Restart ledger reconstruction | `node/src/state.rs:789` checkpoint + `cell_overlay_since` | — | reboot | per reboot | **REFUTED** (incremental) | — |
| — | Orphan buffer / catch-up | `node/src/catchup.rs` | — | per block received | per block | **CLEAN** (HashMap/HashSet) | — |
| — | `dregg_strand_admit` | `metatheory/Dregg2/Distributed/StrandAdmission.lean:469` | — | admission | per admission | **REFUTED** (bounded by committee) | — |
| — | `dregg_decide_refines` | `metatheory/Dregg2/Deos/FlowRefine.lean:428` | — | deploy gate | per deploy | **REFUTED** (bounded by descriptor) | — |
| — | `build_ordering_blocklace` per-poll rebuild | `node/src/blocklace_sync.rs:1657` | LACE | finality poll | per poll | HashMap-backed O(N log N); dominated by #1 | folded into #1's incremental fix |

---

## 1. (Tier 1) Verified finality gate — the class exemplar, only HALF killed

This is the same bomb as `tauOrderFast`; it is included because the fix (`02c4e1709`) closed only one
of its two exponents.

- **The per-poll path** (`node/src/blocklace_sync.rs`): `poll_finalized_blocks` (`:935`) clones the whole
  lace under the read lock (O(N)), `build_ordering_blocklace(&lace)` (`:1037`, body `:1657`) re-inserts
  every block recomputing ids (HashMap-backed, O(N log N)), then `spawn_blocking(compute_order)`
  (`finality_gate.rs:148`) formats the **entire lace** into a wire string and calls the Lean
  `dregg_tau_order` export. The finality executor (`spawn_finality_executor`, `:3660`) is a single serial
  task — the next poll cannot begin until this poll's FFI + execution finish.
- **What `02c4e1709` fixed:** inside one FFI call, `tauOrderFast`'s `mkPastCache`/`mkRoundCache`
  (`BlocklaceFinality.lean:312`/`:369`) were List-backed (`cachedPast` = `List.find?`, `:320`;
  `computeRounds` O(n²), `:97`). The `@[implemented_by tauOrderFastImpl]` twin backs them with
  `Std.HashMap`/`Std.HashSet` → the within-call O(n³) collapsed to ~O(n²).
- **What is STILL open (the residual bomb):** the memo lives *inside* the pure function and is thrown
  away at the end of every call. `BlocklaceHandle` (`:159`) has **no** cross-poll cache/fingerprint
  field. Every poll rebuilds the entire order from zero over the now-larger lace, so per-poll cost still
  climbs monotonically with the DAG. `docs/VERIFIED-GATE-PERF.md` measured 9.2 s @ 35 blocks; the serial
  executor falls behind block production and a round-2 client turn never enters the finalized prefix in
  the window. **The real fix is cross-poll incrementalization** (a persistent order cache, or a stateful
  Lean export that ingests only the new blocks) — `@[implemented_by]` cannot express that.
- **Live confirmation.** Under the 35-turn burst, faucet requests at turns 22–24 and 35 **returned empty
  (10 s curl timeouts)** while the DAG was largest — the commit/HTTP path stalling under sustained load
  as the lace grew, consistent with the documented per-poll O(history). (`ffi_ms`/`lace_size` from
  `7cf197230` is debug-level and NOT emitted at the mesh's info/warn, so the direct per-poll curve needs
  `RUST_LOG=debug`, which needs a node restart — NOT done, per the recon-only constraint. Instrumentation
  I would add read-only: promote the `finality_gate` cache-miss `ffi_ms`+`lace_size` line to info, or a
  one-shot `RUST_LOG=dregg_node::blocklace_sync=debug` node to capture `(lace_size, ffi_ms)` pairs and
  confirm the super-linear bend directly.)

**OWNED-LANE NOTE:** `blocklace_sync.rs` is the finality-throughput lane — this entry is recon; do not edit here.

## 2. (Tier 2) `hbBool` — the one genuinely NEW same-class suspect

`Dregg2/Exec/DistributedExports.lean:545`:
```
def directDepsOf (d : Dag) (b : Nat) : List Nat :=
  (d.turns.filter (fun e => e.hash == b)).foldr (fun e acc => e.deps ++ acc) []   -- O(|turns|) linear scan, PER frontier node
def hbReach (d : Dag) (fuel) (frontier) (a) : Bool :=
  let preds := (frontier.foldr (fun b acc => directDepsOf d b ++ acc) []).dedup   -- List.dedup = O(k²)
  ...
def hbBool (d : Dag) (a b : Nat) : Bool := hbReach d (d.turns.length + 1) [b] a
```
This is the identical "DAG re-walked as List" shape: `directDepsOf` linearly scans **all** `d.turns` for
every frontier node at every BFS layer, and the frontier is List-`dedup`ed. The author already added the
`.dedup` to kill the *exponential* diamond blow-up (`:552` comment), so it is polynomial —
O(depth · |nodes| · |turns|) with linear List scans and no HashMap adjacency — but it still grows with the
DAG and is rebuilt per query. It is the export `dregg_coord_causal_order` (Rust caller
`coord/src/causal.rs:46`), which is on the **coordination / 2PC** path, **not** the per-turn faucet or
finality poll — so it is lower urgency than #1, but it is the cleanest transplant target for the exact
`tauOrderFast` recipe: `@[implemented_by]` with a `HashMap<Nat, List Nat>` adjacency built once from
`d.turns` and a `HashSet` frontier.

## Refuted (bounded — do NOT grow with ledger/DAG)

- **Per-turn Lean executor** (prime suspect #1 in the brief). `stateOfWState` (`Exec/FFI.lean:2685`)
  resolves cells with `w.cells.find?` (linear), and `caps`/`bal`/`lifecycle`/`delegate` have the same
  `find?`-backed resolvers — BUT the node feeds only the turn's **touched** cells: `build_pre_ledger`
  (`exec-lean/src/lean_shadow.rs:1045`) inserts exactly `collect_id_map(turn)` plus the delegation-parent
  and cap-target closures. `w.cells` is O(turn), not O(ledger). Per-turn cost does not worsen as the
  ledger grows. **Not the class.**
- **Restart reconstruction** (prime suspect #2). `node/src/state.rs:789` restores from a ledger
  checkpoint and overlays only `cell_overlay_since(checkpoint_height)` (the touched-cell delta), replaying
  genesis exactly once — checkpoint+overlay, not an O(history) full-DAG re-execute. **Incremental.**
- **Orphan buffer / catch-up.** `node/src/catchup.rs` `OrphanBuffer` is entirely `HashMap`/`HashSet`
  (`orphans`/`waits`/`waiting_on`); `missing_predecessors` is `HashSet::contains`. **Already the fixed
  shape.**
- **`dregg_strand_admit`** (`StrandAdmission.lean:469`). The `admitted` predicate folds over
  `seeds`/`vouches`/`bonds` — federation membership, bounded by committee size, not the DAG. **Bounded.**
  (Caveat: the leader-coverage helpers `admittedLeaders`/`finalLeaderAtAdmitted` (`:200`) do iterate
  `List.range waveCount` × the un-cached finality primitives — Tier-3 suspect #3 above — but only at
  admission time.)
- **`dregg_decide_refines`** (`FlowRefine.lean:428`). Operates over the deploy-time `Proc` flow-algebra
  descriptor, bounded by descriptor size; no live per-turn/poll caller. **Bounded.**

---

*Recon performed 2026-07-07 against the live n4fed-v3 mesh (hbox), fresh genesis `ed6c8ba1`. No source
changed; live mesh not restarted. Faucet burst of 35 turns grew finalized 12→312.*
