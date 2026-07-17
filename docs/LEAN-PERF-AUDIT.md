# LEAN-PERF-AUDIT — the causalPast siblings, swept before production

**Date:** 2026-06-30 · **Scope:** the verified-Lean execution/hot paths in `metatheory/` and their
FFI callers (`node/`, `exec-lean/`, `dregg-lean-ffi/`). **Trigger:** the finality wedge — the verified
`BlocklaceFinality.causalPastAux` was un-memoized, so the nested
`ratifies`/`isSuperRatified`/`findAllFinalLeaders` loops re-traversed each block's causal past an
exponential number of times over the cross-linked n=5 DAG (99.3% in a `List.elem` scan). Fixed
proof-preserving in `24dcd0474` (`PastCache` + `tauOrderFast_eq`). This audit finds the **siblings**.

The recurring tell: **`Lace`/state is a `List`, lookups/membership are `List.find?`/`List.contains`
(O(n) linear scans), and whole-DAG / whole-state derived quantities (causal past, round map, state
root) are recomputed by full traversal — exactly where the Rust differential sibling uses a
`HashMap`/`HashSet`/`BTreeSet`/cached Merkle root.** None of the latent bombs bite at the current
`#guard`/test sizes (N ≤ 3, the 9-block `trace3`); all bite at scale (large lace, deep/wide DAG,
long history, n=5+). "Fine small, blows up at scale" is the causalPast signature.

---

## What was FIXED here (proof-preserving, `#assert_axioms`-clean, differential intact)

### FIX 1 — `roundOf`/`computeRounds` recompute (the PRIME sibling, same file, same live export)
`metatheory/Dregg2/Distributed/BlocklaceFinality.lean`

The `PastCache` fix memoized the causal past but **left a second un-memoized whole-lace recompute
untouched in the same fast path**: `roundOf B h := roundLookup (computeRounds B) h` re-folds
`computeRounds` over the WHOLE lace on EVERY call (itself O(n²·d) because `roundLookup` is a linear
`find?` over a growing accumulator and the lace is `List`-backed). And `roundOf` is called pervasively
on the fast path:
- `maxRound` (`B.map (roundOf …)`) — n calls;
- `blocksAtRound` (`B.filter (roundOf …)`) — n calls, per wave / per leader;
- `xsortBy` qsort comparator — `roundOf` twice per comparison, O(n log n) comparisons per segment;
- `hasEquivInPast` — nested `creatorBlocks.any (… creatorBlocks.any (… roundOf … == roundOf …))`,
  O(n²) `roundOf` calls per equivocation check, itself called per-past-block in `approves`/`ratifies`.

The `…C` cache twins memoized only the causal past, so each still called **bare `roundOf`**, re-deriving
`computeRounds B` thousands of times per finalization. Same `causalPast`-class bomb, on the live
`@[export] dregg_tau_order` / `dregg_blocklace_finalize` path (via `tauOrderFast`/`tauGoldenFast`).

**Fix:** a `RoundCache` = `computeRounds B` built ONCE (the Lean analogue of Rust's
`rounds: HashMap<BlockId,u64>`, `ordering.rs::compute_rounds`), threaded alongside the `PastCache`
through every `…C` twin. New `…R` primitives (`roundOfR`/`maxRoundR`/`blocksAtRoundR`/`xsortByR`/
`leaderCandidatesR`) look up the precomputed rounds; each is proved EQUAL to its pure original at
`rc = mkRoundCache B` **definitionally (`rfl`)** — `roundOfR (mkRoundCache B)` unfolds to exactly
`roundOf B`. The `…C_eq` theorems keep their statements (now also fixing `rc = mkRoundCache B`); the
pure rule, all safety theorems (`finalLeaders_one_per_wave`, `tauOrder_deterministic`, …) and `#guard`s
are untouched. `tauOrderFast_eq : tauOrderFast = tauOrder` still holds, so the gate exports keep their
verified-rule proof. **Result:** `computeRounds B` is folded ONCE per finalization instead of per
`roundOf` call; the high-order polynomial collapses by an n-factor. `#assert_axioms tauOrderFast_eq`
(transitively covering the round-cache chain) stays clean.

### FIX 2 — `hbReach` exponential frontier (the `dregg_coord_causal_order` export)
`metatheory/Dregg2/Exec/DistributedExports.lean:551`

`hbReach` (decidable happened-before, the body of `@[export] dregg_coord_causal_order`) walked the
dependency DAG with **no visited set and no frontier dedup**: `preds := frontier.foldr (directDepsOf
++) []`. On a RECONVERGENT DAG (diamonds), a node reachable by k paths appears k times in the frontier,
and stacked diamonds MULTIPLY the frontier each layer → **O(2^depth)** (the "DAG re-walked as a tree"
bomb; `fuel` bounds recursion depth, not the per-layer explosion).

**Fix:** `.dedup` the per-layer frontier (`(frontier.foldr …).dedup`). Result-preserving — dedup keeps
the SET of frontier nodes identical at every layer, so `preds.contains a` / `preds.isEmpty` and the
final `Bool` are UNCHANGED (the chain + diamond `#guard`s witness identical output), and fuel can only
be needed for FEWER layers. Caps every layer at ≤ |nodes| → polynomial. No theorem unfolds `hbReach`
(`coord_causal_order_eq` treats `hbBool` opaquely), so every proof is preserved.

---

## The n=5 SECOND finality-stall verdict (beyond the wedge)

**Verdict: NOT a Lean perf derp. The prime suspect is an inline verified-Lean *executor* FFI on the
async worker — the direct sibling the wedge fix MISSED — flagged below for the n5-debug lane.**

Reasoning:
1. The federation is **gate-off** (`DREGG_FINALITY_GATE=0`). Gate-off ⇒ `order_gate_armed = false`
   ⇒ the verified-Lean tau-order FFI is **never called** (`blocklace_sync.rs::poll_finalized_blocks`).
   So **the Lean ordering/finality path is entirely bypassed** — a Lean perf bomb on it cannot be the
   cause. (FIX 1/FIX 2 harden that path for when the gate is ON; they are not the n=5 cause.)
2. The ordering FFI (`VerifiedFinality::compute_order`) and the secondary gate FFI
   (`VerifiedFinality::compute`) ARE correctly `spawn_blocking`'d (`blocklace_sync.rs:1040`, `:1156`).
3. **The miss:** the per-turn *execution* FFI — `execute_finalized_turn` →
   `execute_via_producer` → `dregg_exec_full_forest_auth` — runs **INLINE on the async worker, no
   `spawn_blocking`, while holding `state.write().await`** (`node/src/blocklace_sync.rs:3951`, lock at
   `:3804`), once per finalized turn on the `spawn_finality_executor` consensus task. The wedge fix
   moved the *ordering* FFI off-worker but left the heavier *execution* FFI inline AND under the global
   state write lock. At n=5 more turns finalize per poll; each pins the worker on the synchronous Lean
   executor and holds the global state lock for its duration, which (a) blocks the finality task from
   advancing height / emitting votes / processing the next block, and (b) stalls every HTTP/gossip
   handler that needs the state lock — presenting exactly as a finality stall. This is independent of
   the gate flag (the executor FFI runs whenever a turn finalizes).

**This is a Rust fix in the n5-debug lane's domain (and an active-edit clobber risk), so it is FLAGGED
here, not touched.** Precise fix: compute on a state clone inside `spawn_blocking`, then apply under a
short-held lock — OR, minimally, `spawn_blocking` the FFI (note: a naive wrap still holds the write
guard across the `.await`; the clone-then-apply restructure is the real fix). Compounding sibling:
`submit_queue_drainer.rs:354` (`execute_submission`) has the identical inline-FFI-under-write-lock
shape under submission load. Also inline (lighter): `blocklace_sync.rs:966`
(`strand_admission_gate::admitted_participants`, the `dregg_strand_admit` FFI, inside the
otherwise-fixed `poll_finalized_blocks`, before the spawn_blocking blocks).

Secondary note (not the cause, but inline CPU): the Rust `tau()` differential sibling
(`blocklace_sync.rs:~1037`) is computed inline every poll even gate-off, but it carries the Rust
`PastCache` (HashMap) so it is polynomial, not the exponential the Lean lacked.

---

## RANKED inventory (latent-bomb severity)

### Tier A — LATENT BOMBS on a LIVE/deployed path (production-blow-up-at-scale)

| # | path (file:line) | complexity | trigger | status |
|---|---|---|---|---|
| A1 | **FFI starvation** — `node/src/blocklace_sync.rs:3951` `execute_finalized_turn` → `execute_via_producer` (`dregg_exec_full_forest_auth`) inline on async worker, holding `state.write()` | runtime starvation (per-turn) | turns finalized per poll, n≥5 | **FLAGGED for n5 lane** (Rust; n=5 stall suspect) |
| A2 | **`roundOf`/`computeRounds` recompute** — `BlocklaceFinality.lean` `roundOf`:100, `maxRound`:202, `blocksAtRound`:178, `xsortBy`:252, `hasEquivInPast`:159 | recompute O(n²·d) whole-lace fold, called O(n²–n³)× per finalization | lace size n, DAG depth/width | **FIXED (FIX 1)** |
| A3 | **closure-ledger turn executor** — `RecordKernel.lean` `recTransfer`:495 / `recTransferBal`:612; marshal `FFI.lean` `stateOfWState`:2683, `wstateOfState`:2752; reconstruct `balOfEntries`:1348, `capsOfEntries`:658 | O(N²) per turn (N nested `if`-closures, read through full chain) + O(C·(N+C)) / O(B·(N+B)) marshal | effects/turn N, cells C, balances B | **FLAGGED** (deep; deployed `dregg_exec_full_forest_auth`; not yet biting — FFI rebuilds per-turn so bounded by one turn) |
| A4 | **`hbReach` exponential frontier** — `DistributedExports.lean:551` (`dregg_coord_causal_order`) | O(2^depth) on reconvergent DAGs | DAG diamonds × depth | **FIXED (FIX 2)** |
| A5 | **nullifier/revoked List scans** — `FullForestAuth.lean:481` `revocationGate` (`revoked.contains`, per forest node → O(N·R)); `RecordKernel.lean:935` `noteSpendNullifier` (`∈ nullifiers`, per spend) | O(N·R) / O(spends·N) over history-growing grow-only `List`s; full sets shuttled on wire each turn | total revocations R, nullifiers, nodes N, history | **FLAGGED** (deployed gate; Rust uses `BTreeSet`/`HashSet` — `cell/src/nullifier_set.rs` already swapped Vec→BTreeSet for this) |

### Tier B — LATENT BOMBS on the commitment / witness / staged paths (not the live FFI executor)

| # | path (file:line) | complexity | trigger | status |
|---|---|---|---|---|
| B1 | **`frameDigest` re-sort + re-hash all accounts per commit** — `metatheory/Dregg2/Circuit/StateCommit.lean:173`, `encodeS`:293 | O(N log N) re-mergesort + re-hash every untouched leaf, un-shared across pre/post wires; O(T·N log N) aggregation | accounts N, turn count T | **FLAGGED** (circuit/light-client commitment model; Rust caches — `commit/src/merkle.rs:102` `cached_root`) |
| B2 | **`accountsSorted`/`accountsComponent` sort-on-every-call (twice)** — `metatheory/Dregg2/Circuit/AccountsCommit.lean:24,41` | O(N log N) per `digest` + re-sort for `expected` | account-growth (createCell/spawn) | **FLAGGED** (same family as B1) |
| B3 | **`Heap.root` full O(M) re-sponge per write** — `Substrate/Heap.lean:366`, via `HeapKernel.lean:204` `heapStepGuarded` | O(M) flat re-hash per write (advertised O(log M) Merkle openings); O(W·M) | heap entries M, writes W | **FLAGGED — STAGED + UNWIRED** (`execFullA` has no heap-write arm yet, `FullForestAuth.lean:592`; latent on activation; Rust caches `heap_root` per cell, `cell/src/state.rs:217`) |

### Tier C — secondary inline-FFI (n5 lane; lighter than A1)

`api.rs:2985`/`:3277` (`post_submit_turn`/`post_submit_signed_turn`, primary HTTP ingress),
`api.rs:6671`/`6703`/`5355` (`post_faucet`/`post_resolve_conditional`), `mcp/handlers_act.rs:216`
(`tool_submit_turn`), `api.rs:4234`/`4871` (`post_intent`/`post_fulfill_intent` → ring-settle
`dregg_record_kernel_step`), `api.rs:5738` (`post_atomic_vote` → `dregg_coord_2pc_decide`),
`equivocation_court_service.rs:720`/`775` — all run a verified-Lean FFI inline on an async fn (no
`spawn_blocking`). Same hardening as A1; **FLAGGED for the n5-debug lane**, not touched.

### Tier D — architectural multiplier (fix in tandem, not standalone bombs)
- `Lace = List Block`; `Lace.lookup`/`Lace.has` are `find?` = O(n) (`Authority/Blocklace.lean:73`).
- `roundLookup` = `find?` over a growing accumulator → each `computeRounds` is O(n²·d) not O(n·d)
  (`BlocklaceFinality.lean:82`).
- `causalPastIncl` per-call is O(n²–n³) (`acc.contains`/`.dedup`/`B.lookup` over `List`) — now built
  ONCE by the cache (bomb defused; the residual per-build cost is acknowledged in the fix docstring).
  Replacing `List` with a `Std.HashMap`-backed lace would drop A2/A3/A5/D from polynomial to
  near-linear, but is a larger structural change (the executor proofs are stated over `List`).

### Tier E — MINOR / benign / model-only (no live bite)
- `LaceMerge.lean:98`, `CatchupConverges.lean:82`, `CheckpointPrune.lean` — O(n²) recompute-in-loop
  (`laceIds` rebuild, `++`-fold), but **model/proof-only, no `@[export]`, off every live path** (the
  node's real catch-up/merge/prune is Rust).
- `StrandAdmission.lean:160,196` (`finalLeaderAtAdmitted`/`admittedFinalLeaders`) call the SLOW pure
  `finalLeaderAt`/`findAllFinalLeaders`, but appear only in theorems/`trace3` `#guard`s; the live
  `@[export] dregg_strand_admit` → `admitted` is pure registry Boolean (no DAG walk). MINOR.
  `distinctVouchersFor`:127 is O(V·(B+S)) + `.dedup` but small registries, one query — MINOR.
- `heapAtomsAdmit` (`HeapKernel.lean:158`), `Heap.get`/`set` (`Heap.lean:93,108`), `authorizedB` caps
  scan (`Kernel.lean:54`, Rust sibling `cell/src/capability.rs:478` is ALSO a linear `Vec.find` — not
  a Lean-specific divergence), `listDigest`/`Merkle.recompose` — single-pass O(n)/O(depth). BENIGN.
- No `.dedup`-on-hot-path or `++`-in-recursion (O(n²)) found on the live executor path.

---

## Verification

- `metatheory`: `lake build Dregg2.Distributed.BlocklaceFinality Dregg2.Distributed.FinalityGate
  Dregg2.Exec.DistributedExports` — green; `#assert_axioms tauOrderFast_eq`/`cachedPast_eq`/
  `tauGoldenFast_eq` ⊆ {propext, Classical.choice, Quot.sound}; the `#guard`s (the `tauGolden`/
  `tauOrderFast == tauOrder` differential teeth) recompute identically — fast == pure.
- The FFI starvation findings (A1, C) are reported for the n5-debug lane (Rust, active domain — not
  edited here to avoid clobbering concurrent work).
