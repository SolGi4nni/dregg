# TEST-GAP AUDIT — the systematic blind spots that let a whole bug class hide (2026-07-07)

**Why this doc.** Two bug families each hid for the *entire* project, not by bad luck but
because the test suite was structurally incapable of seeing them:

- The `committed_height` / **THE SWAP authority-inversion** bug (the Lean/Rust producer commit
  different roots when the host stamps a non-zero block height). It hid because **every executor
  differential ran at `block_height = 0`**, where the `committed_height` stamp is a no-op
  (`apply_committed_height` only fires when `block_height != old_height`, so at height 0 both
  sides skip it and agree vacuously). The live 2-machine mesh was the first place a turn ever
  ran at height > 0 against the differential — `docs/CROSS-MACHINE-FINALITY-FINDING.md §1`.
- The `tauOrderFast` / api-clone / `has_equivocation_in_past` **perf bombs** (`docs/ALG-COMPLEXITY-AUDIT.md`,
  `docs/PERF-BOMB-AUDIT.md`, `docs/VERIFIED-GATE-PERF.md`). They hid because **nothing measured
  cost as N grows** — the finality/executor tests run at N≈9 blocks / 2–4 cells, where an O(n²)
  or per-poll-O(history) path is indistinguishable from O(1). The live n=4 federation (DAG →
  1500 blocks) was the first place the asymptotic showed.

Both are the *same meta-failure*: **the load-bearing checks were only ever exercised in the
regime where the bug is invisible.** This audit finds every other place that regime hole exists,
and designs the harness that closes the perf half.

Scope of the audit itself: **recon + design** (no tests were written by the audit). What has since
been built from it is in the status block below.

---

## STATUS AT HEAD (what this audit's asks became)

- **GAP-1 residual — CLOSED.** `exec-lean/tests/committed_height_effect_families.rs` is the
  height × effect-family matrix this doc designed: BOTH producers (Rust `TurnExecutor` ==
  verified-Lean `execute_via_lean`) at `block_height ∈ {0, 1, 7, 1_048_576}` across
  `SetField`/`Seal`/`Destroy`/`SetPermissions`/`SetVerificationKey`/`MakeSovereign`/cap-introduction,
  asserting post-state root agreement (the height-0 column is the non-vacuous control).
- **Part B, finality half — IMPLEMENTED.** `blocklace/tests/perf_growth.rs` is the gating `#[test]`
  (header: "Design + ground: docs/TEST-GAP-AUDIT.md §B") asserting the machine-independent
  `SLACK·(N_hi/N_lo)^EXPONENT` ratio bound in `cargo test`. **It refuted one design premise:** the
  fixed `tau` measures ~O(n²) (inherent to `xsort`'s per-block causal-past computation), NOT the
  near-linear baseline §B.2 assumed — so the shipped lever gates **sub-cubic**
  (`FINALITY_EXPONENT = 2.2`, one big-span ratio 100→900) rather than near-linear at 1.2. The O(n³)
  List-cache regression fails the bound; the present quadratic passes. §B.2's exponent guidance
  below stands for levers whose healthy baseline IS near-linear (the submit/ledger levers).
- **Part B, the other levers — IMPLEMENTED.** Three more gating `#[test]`s cite §B:
  `turn/tests/perf_growth.rs` (the per-turn submit/ledger FLAT lever over M ∈ {100, 1_000, 10_000}
  cells — bombs #5 pubkey-scan and #9 api-clone), `coord/tests/perf_growth.rs` (the budget
  anti-replay GROWTH lever, bomb #6, SLACK=4.0/EXPONENT=1.2), and `circuit/tests/perf_growth.rs`
  (bombs #7 sorted-leaf position scan and #8 lookup-table re-scan).
- **Still open:** GAP-2 (no seq≠topo lagging-creator lace test), GAP-4 (no live adversary against a
  running node's differential), and the node-side `finality_perf_growth.rs` (`compute_order`) lever of
  Part B, to land in `node/tests/` — the one Part-B lever not yet built.
- **GAP-5:** the matrix test's height-0 control closes the height-gated-vacuity instance; the
  mutation/non-vacuity pass over the other load-bearing differentials remains a standing
  discipline, not a shipped sweep.

---

# PART A — COVERAGE GAPS (ranked by the real bug class each hides)

Inventory (at HEAD): `node/tests` 24 `#[test]`, `blocklace/tests` 28, `blocklace/src` unit 218,
`exec-lean/tests` 76. The gate is `cargo test --workspace` (`.github/workflows/ci.yml:55`). The
`perf/` criterion benches are **not** in that gate and **not** in `bench.yml` either (which is
`workflow_dispatch`-only and lists 7 crates, none of them `dregg-perf`) — see Part B.

## GAP-1 (🔴 highest) — height = 0 only: the entire host-column / block-height dimension is untested off zero

**Bug class hidden: any host-stamped commitment limb that is a no-op at height 0** — exactly the
class the `committed_height`/SWAP bug lives in, and it is *not* the only limb stamped from the host
column.

Grounded evidence that height 0 was the universal regime:
- The named producer differentials run host-agnostic or at height 0. `rust_lean_divergence_finder.rs:557`
  hard-codes `let block_height = 0u64;` with the comment "block_height 0 ⇒ the marshaller omits the
  optional `block_height` wire field … the block_height>0 wire path is exercised separately by the
  FFI's own [tests]". So the *primary* divergence finder never crosses the stamp boundary.
- `faucet_fee_well_divergence.rs` is the ONLY exec-lean test that takes a `block_height` parameter
  (`run_faucet_at(amount, fee, block_height)`, `:154`; `executor.set_block_height`, `:173`). Its
  original bug-repro case (`:262`) pins `block_height: 0` and explicitly notes the commitment "limb
  … stays 0 on both sides and the FEE is the sole divergence." The height>0 goldens
  (`swap_inversion_committed_height_transfer_agrees` `:335`, `committed_height_family_agrees` `:349`)
  were **added by the fix** — they are the closure of GAP-1 for *Transfer*, not pre-existing coverage.
- Every other exec-lean differential (`lean_state_producer_widen.rs`, `_coverage.rs`,
  `_differential.rs`, `_denotational_census.rs`, `rust_lean_parity_gauntlet.rs`) constructs ledgers
  with `destroyed_at_height: 0`, `archive_start_height: 0`, `prefix_end_height: 0` and never calls
  `set_block_height` — i.e. runs at the implicit host height 0. At audit time `set_block_height`
  appeared in the *entire* `node/tests` + `exec-lean/tests` tree only inside
  `faucet_fee_well_divergence.rs`; at HEAD the closure matrix
  `committed_height_effect_families.rs` calls it too.

**The residual the closure had to cover (ranked within the gap; see STATUS for the matrix test that
covers it):** the SWAP fix added height>0 goldens
for the *Transfer* family. Every OTHER effect that touches a cell — and therefore gets the
`committed_height = block_height` stamp folded into its post-root — has **no height>0 differential**:
`SetField`, `Seal`/`Unseal` (note `lean_state_producer_widen.rs:365` runs `Cell::seal(reason,
block_height)` but the whole file is at height 0), `MakeSovereign`, `SetPermissions`,
`SetVerificationKey`, `RevokeDelegation`, cap introduction (`expires_at = block_height + …`,
`widen.rs:807`, tested only at height 0). If the covered-set characterization
(`lean_shadow::forest_is_root_agreeing`) has a residual hole for any of these under a non-zero stamp
— exactly the shape of the `4a8882bb`/`12d4e7e6` agents' turns in the cross-machine finding — the
suite cannot see it.

**Design to close:** parametrize the whole producer differential over `block_height ∈ {0, 1, 7,
2^20}` (a `for h in HEIGHTS` wrapper around the existing case generators in
`rust_lean_divergence_finder.rs` and `lean_state_producer_widen.rs`), asserting Lean-root == Rust-root
at every height for every effect family. The stamp is where SWAP inverted; height is the axis it
inverted on. This is the single highest-value gap because it is the *proven* one — it already shipped
a project-long bug. **Closed at HEAD**: `exec-lean/tests/committed_height_effect_families.rs` is
exactly this design (see STATUS).

## GAP-2 (🔴) — single-machine-only finality: the reorg / `PREFIX SHIFTED` / catch-up-churn path is untested

**Bug class hidden: everything that only appears when `seq`-order ≠ topological-order** — i.e. the
cross-machine catch-up case where a lagging creator's late block has a LOW `seq` but a HIGH DAG-depth
round. Per `docs/CROSS-MACHINE-FINALITY-FINDING.md §2`, single-machine on a clean round-synchronous
DAG `seq ≈ round ≈ topo`, no edges drop, and Rust `tau` == Lean "no divergence, ever"
(`docs/N3-ROOTCAUSE.md`). Three real defects live *only* in the regime the tests never build:

1. The Rust differential's `build_ordering_blocklace` re-inserts blocks sorted by `(seq, creator)`
   and drops predecessor edges to not-yet-inserted blocks (`ordering.rs`; finding §2), producing the
   `rust_len=0`-while-`lean_len=636` false alarm. **No unit test builds a lace where seq ≠ topo**, so
   this lossy rebuild reads as correct.
2. The `PREFIX SHIFTED` handling (`execution_cursor.rs` tracks executed blocks by *identity*, so a
   mid-prefix re-sort still executes once) is proven sound in Lean (`TauPrefixMonotone.lean` has the
   honest-catch-up counterexample) but is **exercised by no test** — `observe_order` shifts only
   happen live.
3. The finality integration tests are ALL single-machine: `sustained_finality.rs`,
   `three_node_ordering_rule.rs`, `payoff_client_turn.rs`, `n3_plateau_probe.rs` launch N nodes on
   **localhost ports** (`launch(...)` bind `127.0.0.1:port`), same clock, same wall, round-synchronous
   DAG. None injects lag/partition/catch-up, so none produces a seq≠topo lace.

`blocklace/tests/consensus_fault_sim.rs` and `multi_node_convergence.rs` DO model
partition→heal→equivocate — but they drive the pure `finality::Blocklace` / `ordering::tau` in-process
and assert only SAFETY/EXCLUSION/convergence; **they never assert Rust-tau == Lean-tau on the
resulting seq≠topo lace**, which is the exact differential that fired `rust_len=0` live.

**Design to close:** an in-process "lagging-creator" lace builder (creator C's block at `seq=k`
references round-`r` predecessors with `r ≫ k`) fed to BOTH `ordering::tau` and the verified Lean order
(`VerifiedFinality::compute_order`), asserting cohort-agreement — the `test_tau_differential_against_lean_model`
assertion, but on a topologically-adversarial lace instead of the fully-connected one. Plus a
`build_ordering_blocklace` unit test asserting it preserves the edge set on a seq≠topo lace (this is
the fix-3 in the cross-machine finding, currently unguarded).

## GAP-3 (🟠) — small-N-only: no finality/executor test runs at large DAG or large ledger

**Bug class hidden: every super-linear cost in Part B.** The perf bombs are *literally invisible*
below their crossover N:
- `test_tau_differential_against_lean_model` runs `build_full_blocklace(&participants, 3)` = **9
  blocks**. `has_equivocation_in_past` is O(waves·P·N²)/poll (`ordering.rs:167`); at N=9 that is ~9³
  ≈ instant. The `tauOrderFast` List-cache was O(n³) and STILL passed every unit test.
- The producer differentials build ledgers of 2 cells (`make_open_cell(1,100)` × a couple). The api
  full-ledger `template.clone()` / `pubkey ledger scan` are O(N_cells)/turn; at N_cells=2 they are
  free.
- `federation_gossip.rs` is the ONLY thing that sweeps N (`lace_sizes = [100, 1_000, 10_000]`), and
  it measures `insert`/`sign`/`verify`/`quorum_acks` — **not** `tau`, **not** `compute_order`, **not**
  `has_equivocation_in_past`. The one bench that scales N does not touch the functions that had the
  bombs. (grep confirms: no bench references `tau`, `compute_order`, `find_all_final_leaders`, or
  `has_equivocation`.)

**Design to close:** Part B. The correctness suite should also gain a *cheap* large-N smoke (tau over
a 2000-block synthetic lace completes and agrees with Lean) so a re-introduced O(n³) fails `cargo test`
by *timeout*, not just by a bench nobody runs.

## GAP-4 (🟠) — no equivocator / adversary in the LIVE differential path

**Bug class hidden: adversarial-input divergence between Rust and Lean.** The equivocator is covered
at the *pure* level (`test_tau_differential_equivocator_excluded` in `ordering.rs`, plus
`byzantine_finality_split.rs`, `consensus_fault_sim.rs`), and that coverage is good. But the LIVE
integration differentials — the node-level Rust↔Lean cross-checks in `poll_finalized_blocks`
(`blocklace_sync.rs:1163`) and the producer shadow (`executor_setup.rs:155`) — are only ever driven by
the **honest** faucet/transfer traffic that `sustained_finality`/`payoff_client_turn` generate. No
integration test submits an equivocating block, a double-spend, or a malformed attested turn to a
*running* node and asserts the live differential stays silent (or fires correctly). The SWAP inversion
surfaced live precisely because reorg re-executed covered turns repeatedly; an adversary that forces
re-execution is exactly what the honest tests never build.

**Design to close:** an integration test that submits a crafted equivocation / duplicate-carried turn
to a running 3-node localnet and asserts (a) the live producer differential does not silently diverge,
(b) the equivocator is excluded from the finalized order — porting the pure-level teeth onto the live
FFI path.

## GAP-5 (🟡) — vacuous / happy-path-only guards on load-bearing invariants

**Bug class hidden: a check that is true because its precondition is never met** — the `committed_height`
no-op is the archetype (the assertion `h == block_height` at `faucet_fee_well_divergence.rs:204` is
*skipped entirely* when `block_height == 0`, `:201`). Systematic instances:
- The fee-well `committed_height` guard (`:216`, "fee well must stay 0") only runs inside the
  `block_height != 0` branch — at height 0 the whole invariant is un-asserted.
- The n=1 solo path "trivially finalizes every block" — `three_node_ordering_rule.rs` exists *because*
  the deployed default was n=1 and "skips the ordering rule"; the ordering-rule differential was
  vacuous under n=1. This is documented (`three_node_ordering_rule.rs:3`) but is the template for the
  class: **any assertion gated behind a `participants > 1` / `height > 0` / `N > threshold` condition
  the default config never satisfies is vacuous in the default suite.**

**Design to close:** a mutation/vacuity pass over the load-bearing differentials (the project already
has this discipline — `minted-proof-integrity-discipline.md`): for each `assert_eq!(lean_root,
rust_root)`, confirm there exists a run where the two sides *would* differ absent the fix (non-vacuity),
and lift every `if height != 0 { assert }` to run at a height where the branch is taken.

---

# PART B — PERF-REGRESSION HARNESS DESIGN (four levers implemented: `blocklace/tests/perf_growth.rs`, `turn/tests/perf_growth.rs`, `coord/tests/perf_growth.rs`, `circuit/tests/perf_growth.rs`; the node-side lever is unbuilt)

**The core defect this closes.** Criterion benches *record* timings; they never *assert*. `bench.yml`
is `workflow_dispatch`-only, uploads artifacts, and does not even list `dregg-perf`. So today: (a) the
functions that had the bombs (`tau`, `compute_order`, `has_equivocation_in_past`, the api clone, the
pubkey scan) are benched by **nothing**, and (b) even a benched regression produces a number in an
artifact nobody diffs. The harness must turn "cost grows super-linearly" into a **`cargo test`
failure** — machine-independent, no hardcoded milliseconds.

## B.1 What to measure

| lever | function under test | N axis | site |
|---|---|---|---|
| finality order | `ordering::tau` + `has_equivocation_in_past` over a synthetic full lace | **N = {100, 500, 2000} blocks** | `blocklace/src/ordering.rs` |
| verified gate | `VerifiedFinality::compute_order` (build_wire + FFI) over the same laces | N = {100, 500, 2000} | `node/src/finality_gate.rs` |
| per-turn submit | executor `execute` + producer clone/pubkey-scan against a populated ledger | **M = {100, 1_000, 10_000} cells** | `perf/src/lib.rs::ledger_with_open_cells` already builds this |
| coord causal | `dregg_coord_causal_order` (`hbBool`/`hbReach`, PERF-BOMB #2) | N = {100, 500, 2000} turns | `coord/src/causal.rs` |

The lace builder already exists (`ordering.rs` unit helpers / `federation_gossip.rs::filled_lace`);
the cell-ledger builder exists (`perf/src/lib.rs:337 ledger_with_open_cells(n, balance)`). The harness
is mostly *wiring existing generators to the untested functions*, not new fixtures.

## B.2 The machine-independent growth assertion (the load-bearing idea)

Never assert absolute ms (machine-dependent, flaky). Assert a **ratio bound** — the measured cost at a
larger N divided by the cost at a smaller N must stay below what a chosen power law permits:

```
Let t(N) = median wall-time of the lever at input size N  (median over k iters, drop warmup).
For consecutive sizes N_lo < N_hi, REQUIRE:

    t(N_hi) / t(N_lo)  <  SLACK * (N_hi / N_lo) ^ EXPONENT

  where EXPONENT = just above the lever's HEALTHY baseline class
        SLACK    = 3.0    (absorbs constant-factor & scheduler noise at the small end)
```

Pick EXPONENT per lever, from the lever's MEASURED healthy baseline — not from hope. 1.2 (tolerates
near-linear + log factors; fails on quadratic) is right for levers whose fixed path is ~linear (the
submit/ledger levers). The shipped finality lever measured the fixed `tau` at ~O(n²) (inherent) and
gates sub-cubic with EXPONENT 2.2 — see the STATUS block. The worked example below uses the original
near-linear assumption; read it as the method, with the `tau` numbers superseded by measurement.

Worked: for `tau`, N_lo=500, N_hi=2000 (ratio 4): a linear/log path gives `t(2000)/t(500) ≈ 4^1.2 ≈
5.3`, times SLACK → threshold ≈ **16×**. The old O(n²) path gives `4^2 = 16×` → **fails** (16 ≮ 16,
and with the real n³ List-cache, 64× ≫ 16). The `has_equivocation_in_past` O(N²) bomb: 16× > 5.3×·… →
**fails cleanly**. A healthy HashSet-memoized path (≈ linear) sits at ~5×, comfortably under 16 →
**passes** on any machine. The assertion is on the *ratio of two timings measured on the same machine
in the same run*, so absolute CPU speed cancels — this is why it is CI-portable without a golden ms.

Robustness rules the harness must follow (or it self-flakes):
- **Two independent ratios** per lever (100→500 and 500→2000); require BOTH under bound (a single
  ratio can spike on a GC/scheduler hiccup at the small end).
- **Median of k≥7 iters**, discard the first 3 (warmup / cache fill), so a cold-start outlier at N_lo
  does not deflate the denominator and false-fail.
- **Guard the small end**: if `t(N_lo) < 50 µs` the ratio is dominated by timer granularity — bump
  N_lo until the baseline clears a floor, rather than dividing by noise.
- Print the measured ratios and the bound on failure (`t(2000)/t(500)=17.4 exceeds 16.0 — SUPER-LINEAR
  REGRESSION in tau`) so the failure names the bomb.

## B.3 Where it plugs in

**A `#[test]`, not a criterion bench** — because it must **fail `cargo test --workspace`** to gate CI,
which is the whole point (criterion can't fail a build and isn't in the gate). Concretely:
`blocklace/tests/perf_growth.rs` (finality), `turn/tests/perf_growth.rs` (submit/ledger),
`coord/tests/perf_growth.rs`, and `circuit/tests/perf_growth.rs` — all existing — plus
`finality_perf_growth.rs` in `node/tests/` (not yet built — the node-side `compute_order` lever),
each a `#[test]` that runs the ladder in-process and
asserts the ratio bound. Keep the sizes modest (N=2000, not 100k) so the
test adds seconds, not minutes, to the suite — the ratio catches the asymptotic without needing huge N.
Criterion benches stay for *tracking absolute numbers* over time (and `bench.yml` should be extended to
run `dregg-perf` and the ratio check made available as `cargo test -p dregg-perf-growth`), but the
**gate is the `#[test]` ratio assertion**.

## B.4 Which check would have caught each of the 9 just-fixed bombs

| # | bomb | file:line | grows with | the check that catches it |
|---|------|-----------|-----------|---------------------------|
| 1 | **throughput** — `poll_finalized_blocks` clones whole DAG 2–3×/poll | `blocklace_sync.rs:962,1101,1270` | DAG N | the unbuilt `finality_perf_growth.rs` in `node/tests/`: `compute_order` ratio over N={100,500,2000} — the per-poll O(N) clone shows as t(2000)/t(500) ≈ 4 ×(clone count); the fix must keep the *order* ratio flat, so a re-added full clone pushes the ratio over bound. |
| 2 | **SWAP** — committed_height inversion | `lean_apply.rs` producer / `finality_gate` | — (not perf) | **GAP-1** (Part A), NOT perf: the height-parametrized producer differential asserting `lean_root == rust_root` at `block_height ∈ {0,1,7,2^20}`. This is a *correctness* gate; the bomb was a divergence, not a slowdown. |
| 3 | **tau-equivocator** — `has_equivocation_in_past` unmemoized | `ordering.rs:167` | DAG N | `blocklace/tests/perf_growth.rs`: `tau` ratio over N={100,500,2000}. O(waves·P·N²) → t-ratio ≈ 16× ≫ 5.3× bound → **fails**. Also caught by the large-N *correctness* smoke (GAP-3): a 2000-block `tau` that was O(n²) times out. |
| 4 | **catch-up** — `present_set(lace)` rebuilt per block | `catchup.rs:276` | DAG N | A `catchup` ratio lever (sync B blocks into a lace of N): O(B·N) rebuild → super-linear in N per synced block → ratio bound fails. (Add `catchup` as a 5th lever in B.1.) |
| 5 | **pubkey-index** — pubkey ledger scan in bearer auth | `authorize.rs:1308` | ledger M cells | per-turn submit lever at M={100,1k,10k} cells with a bearer-cap turn: O(M)/turn scan → t(10k)/t(1k) ≈ 10× vs a HashMap index's ~1× → fails. |
| 6 | **coord-budget** — `debits: Vec` as anti-replay set | `budget.rs:140,460` | session debits | a coord-session lever that records D debits then checks: O(D²) → ratio over D={100,500,2000} fails. |
| 7 | **binary-search** — linear `position` on sorted leaves | `heap_root.rs:260`, `cap_root.rs:522` | heap size | a heap-op lever over heap sizes {100,500,2000}: O(n) position vs O(log n) → the linear scan's ratio ≈ 4× vs binary-search's ≈ log-ratio; with EXPONENT 1.2 the linear O(n) *inside a per-op loop that is itself O(n)* → O(n²) op → fails. (For a single O(n)→O(log n) the ratio gap is subtler; pair it with a correctness assertion that the result is found in `log2(n)` compares via an instrumented counter.) |
| 8 | **DSL-lookup** — re-scans lookup table per trace row | `circuit/src/dsl/circuit.rs:493` | table rows (2^16) | a prove-path lever over table sizes {2^10,2^12,2^14}: O(rows·entries) → the row×entry product makes t-ratio quadratic in the size step → fails. (Lives in `circuit`, so a `dsl_perf_growth.rs` under `circuit/tests/`.) |
| 9 | **api-clone** — full-ledger `template.clone()` ×2 per submit | `api.rs:2994,3300`, `lean_apply.rs:1125` | ledger M cells | per-turn submit lever at M={100,1k,10k} cells: O(M)/turn clone → t(10k)/t(1k) ≈ 10× vs the touched-cell-delta fix's ~1× → **fails**. This is the same lever as #5, different symptom — both surface as "per-turn cost scales with total ledger size, which it must not." |

**The unifying invariant the harness encodes:** *per-poll finality cost must not grow with total DAG
size, and per-turn execution cost must not grow with total ledger size.* Bombs 1,3,4 violate the
first; 5,9 violate the second; 6,7,8 are per-call super-linearities on their own growing input. Bomb 2
(SWAP) is the odd one out — a *correctness* divergence, closed by GAP-1's height-parametrized
differential, not by a timing ratio. Eight of nine perf/correctness bombs map to a concrete ratio (or
large-N timeout) assertion; the ninth (SWAP) maps to the Part-A height gap. That is the CI shape that
would have made this entire class impossible to hide.

---

## Summary — top gaps

1. **GAP-1 height=0-only** (🔴 proven — it shipped a project-long bug): **CLOSED** by the
   height × effect-family matrix, `exec-lean/tests/committed_height_effect_families.rs`.
2. **GAP-2 single-machine-only finality** (🔴 OPEN): the seq≠topo catch-up lace — where the
   `rust_len=0` divergence and `PREFIX SHIFTED` live — is built by no test. **Add a lagging-creator
   lace to the tau differential.**
3. **GAP-3 small-N-only** (🟠 partially closed): the finality lever runs `tau` at N up to 900 blocks
   under a gating ratio bound (`blocklace/tests/perf_growth.rs`) and the executor lever times
   `TurnExecutor::execute` against ledgers of 100/1_000/10_000 cells under a flat bound
   (`turn/tests/perf_growth.rs`); the `compute_order` (verified-gate) lever at large N remains
   unbuilt.
4. **GAP-4 no live adversary** (🟠 OPEN): equivocators are covered pure but never submitted to a
   *running* node's differential.
5. **GAP-5 vacuous guards** (🟡): assertions gated behind `height != 0` / `participants > 1` the
   default config never satisfies. The matrix test's height-0 control closes the height instance;
   the mutation/non-vacuity pass stays a standing discipline.

The perf harness: a `#[test]` (not a criterion bench, so it *gates* `cargo test`) asserting the
machine-independent ratio bound `t(N_hi)/t(N_lo) < SLACK·(N_hi/N_lo)^EXPONENT`, with EXPONENT set
just above each lever's measured healthy class. Four levers ship: `blocklace/tests/perf_growth.rs`
(finality — sub-cubic gate, EXPONENT 2.2 over the measured ~quadratic `tau`),
`turn/tests/perf_growth.rs` (submit — FLAT over the M-cell ladder, FLAT_SLACK=6),
`coord/tests/perf_growth.rs` (budget anti-replay), and `circuit/tests/perf_growth.rs` (sorted-leaf
scan + lookup-table re-scan); the node-side lever is designed here and not yet built. The 9th bomb
(SWAP) is a correctness divergence, closed by GAP-1's matrix.
