# n=3 sustained-finality plateau — root cause

**Question.** Why does an n=3 committee fail to close later turns/waves even on a
perfect network (loopback finalizes only 2/3 turns in `sustained_finality.rs`; a
fast LAN plateaus)? Is n=3 a fundamental BFT degeneracy that n=4 correctly fixes,
or does n=4 *mask* a real bug?

**Verdict (one line).** It is **neither a produce/deliver/cite race nor a
fundamental n=3 degeneracy.** Consensus is healthy at n=3 — it builds a clean,
round-synchronous DAG and the ordering rule (`ordering::tau`) finalizes every turn.
The plateau is the **authoritative *verified-Lean* tau-order finality gate**
(`DREGG_FINALITY_GATE`, default ON) finalizing a strict *subset* of what Rust `tau`
finalizes on this DAG. Flipping the authoritative order Lean→Rust
(`DREGG_FINALITY_GATE=0`) makes the same n=3 committee stream **3/3** turns. The
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
finalized over, `:1104-1105`). Because §2 proves Rust `tau` finalizes turn 3 and §3
shows the Rust-authoritative node streams, the Lean order is finalizing **fewer**
blocks than Rust `tau` on this multi-wave DAG — it does not surface turn 3's wave
for execution, so `execute_finalized_turn` is never reached for turn 3 (no
`"finalized turn executed"` and no `"finalized turn rejected"` log line for it;
turns 1,2 log both times at rounds 4,7).

**Which internal mechanism (divergence vs slowness).** The evidence favours
*slowness*, not an order divergence. Across the gate-ON runs, node-0's log carries
**no `"consensus DIFFERENTIAL DIVERGENCE"` warn** — only the two
`"finalized turn executed"` lines for turns 1,2. If the Lean order that a poll
*completed on* disagreed with Rust `tau`, that warn would fire
(`blocklace_sync.rs:1078-1095`). Its absence, together with "gate-OFF streams" (so
`compute_order` is not simply returning `None` and falling back — that path also
streams), points at the Lean `compute_order` FFI being **too slow to complete a poll
on the grown, cross-linked DAG**: the verified order is O(history) over the Lean
causal-past, and each `poll_finalized_blocks` runs it on a fresh snapshot
(`blocklace_sync.rs:1038-1061`, on `spawn_blocking`). Every completed Lean poll was
computed on a snapshot from *before* turn 3 was finalizable (so it correctly, and
without divergence, excluded turn 3); by the time the lace is tall enough to
super-ratify turn 3's wave, the Lean walk no longer finishes inside the window — so
turn 3 is never surfaced and executed. This is the same O(history) Lean causal-past
cost the prior-session `tauOrderFast` memoization (`tauOrderFast_eq`) targets, and it
is why the Rust `tau` path (µs, memoized `PastCache`) keeps up where the Lean gate
does not. (Timing the FFI directly is the one confirmation not yet captured; the
classification step in the fix below pins it.)

---

## The a/b/c/d/(e) answer

| step | status at n=3 | evidence |
|---|---|---|
| (a) PRODUCE | healthy | turns carried at rounds 4/7/10; producer supermajority-gated (`plan_round_block`) |
| (b) DELIVER | healthy | every round cohort=3 on all nodes; full-cohort predecessor citation (npreds=3) |
| (c) CITE | healthy | zero-slack rule honoured; no partial-cohort blocks; no equivocation/duplicate |
| (d) POLL | healthy | DAG grows in lockstep; O(history) Rust `tau` finalizes 45/49 in µs post-mortem |
| **(e) GATE** | **STALLS** | Lean-authoritative order finalizes a subset; gate-OFF streams 3/3 |

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

The defect is in the **verified-Lean tau-order path**
(`dregg_tau_order` / `VerifiedFinality::compute_order`,
`node/src/finality_gate.rs`), not in consensus or in Rust `ordering::tau`. The
verified order must be brought into agreement with Rust `tau`, which is ground-truth
correct here (it finalizes the whole clean multi-wave DAG).

1. **Classify the shortfall.** Re-run the gate-ON committee and read node-0's log
   for the differential path (`blocklace_sync.rs:1078-1095`): either
   (i) `compute_order` returns a **shorter order** → a genuine Lean/Rust *order
   divergence* (the `"consensus DIFFERENTIAL DIVERGENCE"` warn should fire — and,
   contrary to its text, this is a **Lean-side** shortfall, since Rust `tau` is
   correct), or (ii) it returns `None`/times out on the O(history) causal-past walk
   → the `tauOrderFast` memoization (`tauOrderFast_eq`) is not covering this shape,
   and the poll silently falls back / stalls. The probe's log scan distinguishes
   these.
2. **Land a multi-wave golden.** The existing Lean `tauGolden` `#guard`s evidently
   do not cover **3+ sustained waves at n=3** (else this would have been caught).
   Add a golden that pins `dregg_tau_order` == `ordering::tau` on the exact
   round-synchronous 3-node / ≥4-wave DAG this investigation dumped.
3. **Fix `tauOrder`/`compute_order`** so the verified order equals `tau` on clean
   multi-wave DAGs (this is where it connects to the prior `tauOrderFast_eq`
   memoization and the A1 execution-FFI-under-write-lock work), then re-arm the gate
   by default.

**Interim operational note (NOT a code change):** `DREGG_FINALITY_GATE=0` makes n=3
stream today — but it runs the *un-verified* Rust finality on the commit path, which
defeats the point of the verified gate. It is a diagnostic lever, not the fix; the
fix is to make the verified order agree with `tau`.

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
