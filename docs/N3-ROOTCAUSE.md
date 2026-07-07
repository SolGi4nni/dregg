# n=3 sustained-finality plateau — root cause

**Question.** Why does an n=3 committee fail to close later turns/waves even on a
perfect network (loopback finalizes only 2/3 turns in `sustained_finality.rs`; a
fast LAN plateaus)? Is n=3 a fundamental BFT degeneracy that n=4 correctly fixes,
or does n=4 *mask* a real bug?

**Verdict (one line).** It is **neither a produce/deliver/cite race nor a
fundamental n=3 degeneracy.** Consensus is healthy at n=3 — it builds a clean,
round-synchronous DAG and the ordering rule (`ordering::tau`) finalizes every turn.
The plateau is the **authoritative *verified-Lean* tau-order finality gate**
(`DREGG_FINALITY_GATE`, default ON): its O(history) `compute_order` FFI is too slow
to finish a poll on the grown DAG, and the single serial finality-executor blocks
awaiting it — so the committed prefix freezes at wave 2 even though the Lean and Rust
orders AGREE (no divergence) whenever a poll does complete. Flipping the authoritative
order Lean→Rust (`DREGG_FINALITY_GATE=0`) makes the same n=3 committee stream **3/3**
turns. The
"n=4 fixes it" story is a **confound**: the n=4 home-lab mesh ran gate-OFF, so it
streamed via Rust `tau`; the n=3 harness runs gate-ON by default. Node count is
secondary; the finality-gate *mode* is the real variable.

The failing step, in the a/b/c/d taxonomy, is **none of (a) PRODUCE, (b) DELIVER,
(c) CITE, (d) POLL** — those are all healthy. It is a *fifth* step the framing did
not enumerate: **(e) the verified-order GATE** that sits between `tau` and
execution.

---

## What was measured (instrumented, local, loopback)

Two throwaway probes drive the exact production types (committed, not pushed):

- `blocklace/tests/n3_delivery_gap_probe.rs` — pure `ordering::tau` over hand-built DAGs.
- `node/tests/n3_plateau_probe.rs` — three real `dregg-node` processes; watches the
  structural triple `(dag_height, block_count, latest_height)` through the turn-3
  plateau, then stops node-0, reopens its persisted `redb` store
  (`PersistentStore::load_all_blocks`), reconstructs the DAG, and runs `tau` on it.

### 1. Consensus is healthy at n=3 (NOT produce / deliver / cite)

At the turn-3 plateau, `dag_height` and `block_count` grow in **perfect lockstep on
all three nodes** while `latest_height` is frozen at 2:

```
[turn 2] committed  triples(dag,blk,latest) = (9, 27, 2) (9, 27, 2) (9, 27, 2)
[turn 3] t=3        (10,30,2) (10,30,2) (10,30,2)     cell_found=[false,false,false]
[turn 3] t=24       (17,49,2) (17,49,2) (17,49,2)     cell_found=[false,false,false]
```

The reopened DAG (49 blocks) is **clean and round-synchronous**:

```
49 blocks, 3 creators
  creator[1] 8f2d…  authored 16 blocks (3 turn-bearing)   <- the faucet node
  creator[0]/[2]    authored 17/16 blocks (0 turn-bearing)
  round 1/4/7/10/13/16  cohort=3  distinct_creators=3     [wave START/leader rounds]
  round 4/7/10 turns = [8f2d…]                             <- turns 1,2,3 carried
  in-lace pred counts at rounds 2,10,11,12,13 = [3,3,3]    <- full-cohort citation
  duplicate-same-round-block (leader-skip / equivocation) present = false
```

So: every round has all three creators (**DELIVER** complete), every non-genesis
block cites the whole previous cohort (**CITE** = the zero-slack rule is honoured),
no equivocation, no duplicate leader, and all three turns are carried as `Turn`
blocks at the wave-leader rounds 4/7/10 (**PRODUCE** complete). This refutes (a),
(b), (c). It also refutes the hypothesized timer-vs-quorum race: production is
supermajority-gated (`plan_round_block`, `node/src/blocklace_sync.rs:2994-3035` —
advances only when `cohort_creators.len() >= supermajority`), all n>1 cadence
actions route through the gated `produce_round_block`
(`blocklace_sync.rs:3450`; dispatch n>1 vs solo at `:3325`), and the naive
tip-linking `submit_heartbeat` is used *only* on the solo (n=1) path (`:3521-3536`).

### 2. `tau` on the live DAG DOES finalize turn 3

Running Rust `ordering::tau` on that exact 49-block DAG:

```
[dag] tau on the LIVE DAG finalizes 45 of 49 blocks;
      turn blocks finalized = [(8f2d, seq 4), (8f2d, seq 7), (8f2d, seq 10)]
```

All three turns — **including turn 3 (seq 10, round 10)** — are finalized. Only the
four frontier blocks (rounds 16–17) remain, as expected. So the ordering rule has
no 2-wave ceiling; confirmed independently by the pure-model tests:

- `n3_full_dag_finalizes_both_waves` — clean 6-round n=3 DAG → 18/18 (2 waves).
- `n3_four_clean_waves_all_finalize` — clean 12-round n=3 DAG → **36/36 (4 waves)**.
- (`blocklace` unit test `test_multiple_waves`, `ordering.rs:1294`, agrees.)

### 3. The gate is the locus (the decisive experiment)

`sustained_finality.rs`, same committee, same loopback, only `DREGG_FINALITY_GATE`
differs:

| authoritative order | result |
|---|---|
| **Lean tau-order gate (default ON)** | 2/3 turns; height plateaus at 2 |
| **Rust `tau` (`DREGG_FINALITY_GATE=0`)** | **3/3 turns; heights (1,1,1)→(2,2,2)→(3,3,3)** |

The live node treats the **verified-Lean** `dregg_tau_order` FFI as *authoritative*
and Rust `tau` as a differential sibling (`poll_finalized_blocks`,
`blocklace_sync.rs:1004-1119`; `ordered_from_lean = true`, the Lean order is what is
finalized over, `:1104-1105`). Because §2 proves Rust `tau` finalizes turn 3 and the
Rust-authoritative node streams, the verified-Lean gate is what withholds turn 3: the
live committed prefix freezes at wave 2, so `execute_finalized_turn` is never reached
for turn 3 (no `"finalized turn executed"` and no `"finalized turn rejected"` log
line for it; turns 1,2 log both, at rounds 4,7). The next section pins *why* the gate
withholds it.

**Which internal mechanism — confirmed: the slow Lean FFI stalls the serial
finality-executor (NOT an order divergence, NOT leader-assignment).** The gate-ON
run's node logs pin it:

- **No divergence, ever.** Every completed poll logs `"verified Lean dregg_tau_order
  is authoritative; Rust ordering::tau differential AGREES"` — never the
  `"DIFFERENTIAL DIVERGENCE"` warn (`blocklace_sync.rs:1078-1102`). The Lean and Rust
  orders agree on every poll that *finished*.
- **The finalized count sticks at 27.** The `AGREES finalized=N` lines climb 18→27
  and then stay at **27** for the rest of the run, while the DAG grows to 49 blocks
  (round 16). 27 = the whole DAG through wave 2 (round 9).
- **That pins it to a stalled poll, not a Lean shortfall.** `build_ordering_blocklace`
  (`blocklace_sync.rs:1523-1575`) is byte-identical to the faithful post-mortem
  projection, and post-mortem `tau` on the 49-block lace = 45. Inside
  `poll_finalized_blocks`, Rust `tau` is computed FIRST (fast, `:1025`) and the Lean
  `compute_order` FFI is awaited AFTER (`spawn_blocking`, `:1038-1061`); the
  AGREES/DIVERGENCE line is logged only once the Lean FFI returns (`:1078+`). So *if*
  a poll had completed on the grown lace, Rust would be 45 and — since Lean did not
  return 45 (it never logged >27) — it would have logged **DIVERGENCE**. It never
  did. Therefore the poll on the grown lace **never completed**: the single serial
  finality-executor task is blocked awaiting the O(history) Lean causal-past walk on
  the larger, cross-linked lace, so no poll after ~27 blocks ever finishes to surface
  turn 3. Removing the Lean FFI (`DREGG_FINALITY_GATE=0`) makes every poll complete in
  µs (memoized Rust `PastCache`) → turn 3 executes → 3/3 stream.
- **Order-insensitive** (rules out any leader-assignment interaction): running `tau`
  on the dumped DAG under all six participant permutations finalizes **45 blocks / 3
  turns every time** — the round-robin `participants[w % n]` leader choice does not
  affect the outcome.

This is exactly the O(history) Lean causal-past cost the prior-session `tauOrderFast`
memoization (`tauOrderFast_eq`) targets, and it compounds with the serial-executor
shape (one task awaits each poll before the next) — the same neighbourhood as the A1
execution-FFI-under-write-lock fix.

---

## The a/b/c/d/(e) answer

| step | status at n=3 | evidence |
|---|---|---|
| (a) PRODUCE | healthy | turns carried at rounds 4/7/10; producer supermajority-gated (`plan_round_block`) |
| (b) DELIVER | healthy | every round cohort=3 on all nodes; full-cohort predecessor citation (npreds=3) |
| (c) CITE | healthy | zero-slack rule honoured; no partial-cohort blocks; no equivocation/duplicate |
| (d) POLL | healthy | DAG grows in lockstep; O(history) Rust `tau` finalizes 45/49 in µs post-mortem |
| **(e) GATE** | **STALLS** | slow Lean `compute_order` FFI blocks the serial executor; commit prefix freezes at wave 2; gate-OFF streams 3/3 |

---

## Fundamental-vs-masked-bug verdict

**Real bug, not fundamental degeneracy — and n=4 does not "fix" it, it hides the
trigger.**

- The zero-slack property IS real and fundamental: `supermajority_threshold(n) =
  2n/3 + 1` gives **3 at n=3** (unanimity, f=0) vs **3-of-4 at n=4** (f=1)
  (`ordering.rs:236`). A single crash/drop halts an n=3 committee with no slack —
  demonstrated by `n3_one_missing_last_round_block_halts_finalization` (one missing
  wave-last block → 0 finalized) vs `n4_one_missing_last_round_block_still_finalizes`
  (same gap → 11 finalized). So n≥4 is the correct BFT *fault-tolerance* floor.
- BUT the observed plateau is **with all three nodes healthy on loopback**, where
  zero-slack does not bite (delivery is complete, §1). The plateau is entirely the
  verified-order gate (§3). n=4 in the home-lab avoided it only because that run set
  `DREGG_FINALITY_GATE=0`; an n=4 committee with the gate ON would hit the same
  Lean-order shortfall on a multi-wave DAG. The confound (node count changed *and*
  gate mode changed between the two live runs) is what produced the false
  "n=4-is-the-fix" conclusion.

## Fix design (do NOT fire — Lean/verification-owner's call)

The defect is **performance**, not correctness: the verified-Lean tau-order FFI
(`dregg_tau_order` / `VerifiedFinality::compute_order`, `node/src/finality_gate.rs`)
is too slow (O(history) Lean causal-past) to finish a poll on the grown
cross-linked DAG, and the single serial finality-executor blocks awaiting it. Rust
`ordering::tau` is already correct here (it finalizes the whole clean multi-wave DAG
in µs). Two independent levers, either of which restores gate-ON liveness:

1. **Make the verified order fast.** Route `compute_order` through the memoized Lean
   causal-past (`BlocklaceFinality.tauOrderFast` / `tauOrderFast_eq`, the parallel of
   the Rust `PastCache`) so the O(history) walk is not re-done from scratch each
   poll. This is the direct fix and connects to the prior-session memoization work.
2. **Un-stall the executor from the slow FFI.** The `poll_finalized_blocks` loop
   awaits each Lean `spawn_blocking` before the next poll, so one slow FFI freezes
   *all* finalization progress. Bounding it (timeout → fail-open to the already-
   computed Rust `tau` for that poll, or running the verified order off the critical
   path as a cross-check rather than as the awaited authority) keeps liveness while
   the Lean order remains verified-when-timely. This is the same neighbourhood as the
   A1 execution-FFI-under-write-lock fix (don't let an O(history) FFI gate the hot
   loop).

Add a **multi-wave n=3 perf/liveness guard** so a regression is caught: the existing
Lean `tauGolden` `#guard`s clearly do not exercise 3+ sustained waves under the live
poll cadence.

**Interim operational note (NOT a code change):** `DREGG_FINALITY_GATE=0` makes n=3
stream today — but it runs the *un-verified* Rust finality on the commit path, which
defeats the point of the verified gate. It is a diagnostic lever, not the fix; the
fix is to make the verified order keep up (levers 1–2 above).

---

## Reproduce

```
# consensus + ordering are correct at n=3 (pure model):
cargo test -p dregg-blocklace --test n3_delivery_gap_probe -- --nocapture

# the live plateau + DAG dump + post-mortem tau (gate ON, default) — stalls 2/3:
cargo test -p dregg-node --test n3_plateau_probe -- --nocapture

# the decisive flip — Rust tau authoritative — streams 3/3:
DREGG_FINALITY_GATE=0 DREGG_TEST_FINALITY_WAIT_S=25 \
  cargo test -p dregg-node --test sustained_finality -- --nocapture
```

*Scope: read + diagnose + throwaway local harnesses only. No consensus/kernel/Lean
change was made; the fix above is a design, not an edit.*
