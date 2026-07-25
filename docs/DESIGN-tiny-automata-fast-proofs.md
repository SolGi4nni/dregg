# Making the composed automaton MEGAFAST to prove

**Status:** measured 2026-07-25 against `HEAD` on `fri-incidence-design`. Every number below is a
measurement on the real deployed IR-v2 prover (`circuit/src/descriptor_ir2.rs::prove_vm_descriptor2`,
production `ir2_config`: `log_blowup = 6`, `19` queries, `16` query-PoW bits, BabyBear with a
degree-4 challenge extension). The harness is
`circuit/tests/tiny_automata_prover_shape_measure.rs`; the soundness half of the recommendation is
proved in `metatheory/Dregg2/Circuit/Emit/DfaRoutingSubsetTableCost.lean`.

**Answer in one line:** composition IS nearly additive and the lookup argument DOES amortize —
**+1.05 KiB of wire and +13 ms of single-thread prover CPU per additional automaton, independent of
word length** — but the *currently emitted* carrier (`RowSemantics.exactPublicRows`) throws that
away by spending one whole batch STARK instance per declared table row, which makes composition
cost `Θ(k·n)` instances and caps the whole construction at `k·n ≤ 128`. The fix is a table-semantics
change in the emit path, and the refinement theorem survives it untouched (proved).

---

## 0. The two shapes measured

Both prove the SAME per-lane statement — a toggle DFA (`step(s,y) = s XOR y`) over an `n`-symbol
word, with the C2 continuity `window_gate` and the two boundary `pi_binding` pins, i.e. the
`DfaRoutingTableEmit.tableRoutingDesc` shape generalized to `k` lanes over one shared main trace
(`3k` columns: `(current, symbol, next)` per lane). They differ ONLY in how the transition tooth
reaches a table.

| | **Shape A — `exact_public_rows`** (what Lean emits today) | **Shape B — shared multiplicity table** (the byte/range mechanism, already deployed) |
|---|---|---|
| table realization | `Ir2Air::ExactPublicRow`, **one batch instance per declared row**, each `arity+1` wide × 2 rows, unit capacity | ONE table AIR, height `2^bits`, `LookupBus::table_entry(key, multiplicity)` |
| batch instances | `1 + k·n` | `2`, forever |
| capacity | each declared row consumed **exactly once** (`PublicLookupBalanced`) ⇒ manifest must be the exact query multiset ⇒ `#rows = k·n` | any number of queries per row (multiplicity column) |
| hard cap | `MAX_EXACT_PUBLIC_ROWS = 128` (`descriptor_ir2.rs:378`) ⇒ **`k·n ≤ 128`** | none |

Shape B in the harness uses a 4-bit range lookup on the symbol column as the stand-in for the
transition lookup: identical bus machinery, identical one-global-interaction-per-lookup accounting,
differing only in tuple arity (1 vs 3), which changes the `β`-combination but not the column count.
It is a faithful cost model of the amortizing shape, not a claim that a range check is a transition
check.

## 1. Where prover time actually goes — MEASURED

Timing method (this matters): the box is a shared co-tenant build machine (load average 50–120
throughout). Wall-clock prove timings inside one process spread 5x run-to-run and are worthless. So
every time below is **minimum user CPU seconds measured by the OS** across ≥3 process invocations,
`RAYON_NUM_THREADS=1`, ≥20 proofs per invocation, baseline (`REPS=0`) subtracted — user CPU is
charged only when the process actually runs, so a busy box inflates wall time, not this.

### 1a. The production FRI query proof-of-work is the dominant cost of a TINY automaton

Same descriptor, same witness (`B, k=1, n=16`), only `query_proof_of_work_bits` varied
(measurement-only configs; the production wire is `16` and unchanged):

| PoW bits | 0 | 8 | 12 | **16 (production)** | 18 | 20 |
|---|---|---|---|---|---|---|
| ms/proof | 1.75 | 2.00 | 2.00 | **6.75** | 9.50 | 145.25 |

The grind is witness-size-independent by construction and scales as `2^bits` (the 16→20 jump is
28x for an expected 16x — the grind is geometric per `(descriptor, witness)`, so a single grid
point is one exponential sample). **At `n = 16` the production grind is ~5 ms of a 6.75 ms proof:
74% of the entire prover cost of a tiny automaton is a fixed lottery that has nothing to do with
the automaton.** It is also what made the naive wall-clock sweep non-monotone. Every scaling law
below is therefore read off `pow = 0` and the grind is added back as a constant.

### 1b. The rest decomposes into a width-independent height term plus an additive lane term

Shape B, `pow = 0`, ms/proof:

| `n` \ `k` | 1 | 2 | 4 | 8 | 16 | 32 |
|---|---|---|---|---|---|---|
| **16** | 2.00 | 2.50 | 3.00 | 4.50 | 6.00 | 10.00 |
| **1024** | 110 | 115 | 142 | 207 | 324 | 514 |

| `n` (k=1) | 8 | 16 | 32 | 64 | 128 | 256 | 1024 | 4096 |
|---|---|---|---|---|---|---|---|---|
| ms/proof | 3.00 | 2.50 | 5.50 | 9.00 | 17.50 | 34.00 | 125 | 496 |

Fits (least-squares over the rows above):

```
T(n, k)  ≈  G  +  F·n  +  c·k·n
G ≈ 5 ms      the FRI query-PoW grind at 16 bits (fixed; §1a)
F ≈ 0.094 ms  per trace row, INDEPENDENT of width  (the k-intercept at n=1024 is 97 ms)
c ≈ 0.0127 ms per lane-row     (13.0 ms per lane at n=1024, 0.258 ms per lane at n=16)
```

The width-independence of `F` is not an accident and is the whole reason composition is cheap:
after the batch opening's random linear combination, the FRI **folding phase operates on a single
codeword** whose length is `max_height · 2^log_blowup`. Adding columns adds LDE + Merkle-leaf +
quotient work; it does not add FRI folding work.

**MEASURED CROSSOVER.** Lanes overtake the height term at `c·k·n = F·n`, i.e. `k ≈ F/c ≈ 7.4`,
confirmed independently at both word lengths: `k ≈ 7.5` at `n = 1024` (13.0k vs 97) and `k ≈ 6.8`
at `n = 16` (0.258k vs 1.75). **Below ~7 composed automata you are paying for the FRI layer, not
for the automata. The 8th automaton is where composition starts to be the thing you are buying.**

## 2. Does the lookup argument amortize across lanes? YES — and here is the mechanism

Read off `p3-lookup` (`~/.cargo/git/checkouts/plonky3-*/82cfad7/lookup/`):

* `Lookups::from_interactions` (`types.rs`) assigns **one auxiliary column per bus interaction**
  (`col += 1` per interaction), and `LogUpGadget::generate_permutation` (`logup.rs:380`) builds the
  permutation matrix at `width = lookups.len()` over `SC::Challenge`. So one lookup occurrence =
  **one extension-field column = 4 BabyBear columns** (`PROD_EXT_DEGREE = 4`), full trace height.
  There is no batching of several lookups into one running sum for global (cross-AIR) buses.
* The TABLE side is a *single* AIR that calls `LookupBus::table_entry(builder, key, multiplicity)`
  — a negative-multiplicity send. **k lanes' queries all land on one bus served by one table
  commitment**; the verifier's only global obligation is that each bus's cumulative sums total
  zero.

So the marginal cost of the `(k+1)`-th automaton, in the amortizing shape, is exactly:
**its main columns + ONE extension aux column. No new table, no new commitment, no new instance.**

The wire measurement confirms this to the byte. Shape B marginal wire per lane:

| `k` step (n=16) | 1→2 | 2→4 | 4→8 | 8→16 | 16→32 |
|---|---|---|---|---|---|
| bytes/lane | 1135 | 1048 | 1110 | 1061 | 1080 |

and at `n = 1024`: 1094 B/lane (k 1→8), 1076 B/lane (k 8→32). **The per-lane wire cost is
~1.05 KiB and does not depend on `n` at all** — because FRI queries open single rows, so extra
columns add opened leaf values, not Merkle path nodes.

Analytic check with the constants read off the Rust: a lane adds 3 main + 1 limb + 4 aux-base = 8
BabyBear columns; each query opens them on the `local` and `next` row windows; `19` queries ⇒
`8 · 4 B · 19 · 2 = 1216 B`. Measured 1076 B (88% of the bound) — the gap is postcard varint on a
0/1-valued witness; a full-felt witness would sit at the analytic bound.

## 3. What the DEPLOYED exact-public shape costs instead

Shape A, production config, measured (wire bytes are exact and load-independent):

| `k=1`, `n` | 8 | 16 | 32 | 64 | 128 |
|---|---|---|---|---|---|
| batch instances | 9 | 17 | 33 | 65 | 129 |
| wire (KiB) | 46.1 | 63.4 | 100.0 | 158.1 | **270.3** |
| ms/proof (pow=0) | 2.50 | 5.00 | 9.00 | 17.00 | 35.00 |

| `n=16`, `k` | 1 | 2 | 4 | 8 |
|---|---|---|---|---|
| batch instances | 17 | 33 | 65 | 129 |
| wire (KiB) | 63.4 | 90.9 | 146.8 | **259.8** |
| ms/proof (pow=0) | 4.00 | 7.00 | 12.50 | 21.00 |

Per **declared manifest row** (= per lane-row, since exact-multiset forces `#rows = k·n`):
**+1.76 KiB of wire and +0.15 ms of prover CPU.** Which gives, per additional automaton:

| | wire per extra automaton | prover CPU per extra automaton | cap |
|---|---|---|---|
| Shape A (deployed) | **+28.1 KiB at `n=16`**, +110 KiB at `n=64` — *linear in n* | +2.43 ms at `n=16` | `k·n ≤ 128` |
| Shape B (shared table) | **+1.05 KiB, independent of `n`** | +0.26 ms at `n=16`, +13.0 ms at `n=1024` | none |

**26x cheaper on the wire, 9x cheaper in prover CPU, and the ratio grows without bound in `n`
because shape A's per-lane cost is `Θ(n)` and shape B's is `Θ(1)`.** Head-to-head at identical
main traces: wire ratio A/B = 1.66x at `(k=1,n=16)`, 3.55x at `(k=4,n=16)`, **5.69x at
`(k=8,n=16)`** — and at `(k=8, n=1024)` shape A cannot be expressed at all (it would need an
8192-row manifest against a 128-row cap), where shape B proves in **207 ms for 80.5 KiB**.

### Why it is this expensive: read the assembly

`instance_airs` (`descriptor_ir2.rs:5860`) pushes one `Ir2Air::ExactPublicRow` **per declared row**;
each is a real batch instance with its own committed matrix (2 rows × `arity+1` columns), its own
aux column, its own quotient polynomial, and its own opened values + Merkle paths at all 19 queries.
The AIR itself (`descriptor_ir2.rs:3951`) pins each cell to a literal constant and gates the
multiplicity to exactly one. That unit capacity is the point of `exactPublicRows` — it is what makes
`PublicLookupBalanced` an *exact multiset equality* rather than a subset membership — but it is paid
for at ~1.76 KiB and ~0.15 ms **per symbol of the word, per automaton**.

## 4. The cheapest composition shape, and what has to change

### The shape

> **One main trace, `n` rows, `3k` columns (`current/symbol/next` per lane, or 2 columns per lane if
> `next` is read from the following row). One SHARED transition-table AIR of height
> `2^⌈log₂|T|⌉ ≥ 8` carrying the DEDUPLICATED distinct transitions plus a witnessed multiplicity
> column. `k` lookups per row on one bus. The `(k+1)`-th automaton costs one main column block and
> one extension aux column: ~1.05 KiB of wire and ~13 µs of prover CPU per row.**

For a 2-state/2-symbol DFA the table is **4 distinct rows** — not `k·n`. A 16-state/8-symbol
automaton is 128 distinct rows, i.e. the *entire* current cap spent on ONE automaton's alphabet, at
a table AIR of height 128 that all `k` lanes share for free.

### The emit-path changes (in dependency order)

1. **Lean, `DescriptorIR2.RowSemantics`** — add a sibling of `exactPublicRows`:
   `publicRows (rows : List (List Nat))`, with the SAME `TableDef.publicContentsFaithful` leg
   (contents committed by the descriptor bytes — the strong identity binding is retained) and
   **without** `PublicLookupBalanced` (drop the exact-multiset permutation leg). The acceptance
   predicate is `Satisfied2Subset` — already authored and green in
   `metatheory/Dregg2/Circuit/Emit/DfaRoutingSubsetTableCost.lean`.
2. **Lean, the refinement** — nothing to re-prove.
   `tableRouting_refines_classify_subset` derives the SAME conclusion
   (`final_state = classifyFrom d q0 word`) from the weaker `Satisfied2Subset`, and the deployed
   `tableRouting_refines_classify` falls out as a corollary
   (`tableRouting_refines_classify_of_public`). The existing proof never touched
   `publicLookupBalanced` — the exact-multiset leg is *witness-existence bookkeeping*, not
   soundness. Both tamper canaries (forbidden edge; forged `final_state`) still REFUSE under the
   weaker hypothesis, so this is a weakening, not a laundering.
3. **Wire** — `emitVmJson2` emits `"sem":"public_rows"` with the same `"rows"` array; the manifest
   is the DEDUPLICATED distinct transition set.
4. **Rust, `descriptor_ir2.rs`** — `TableSem::PublicRows { rows }`; `instance_airs` pushes ONE
   `Ir2Air::PublicTable { table_id, rows }` (not one per row); the table trace is
   `rows ++ padding` with a witnessed multiplicity column and `table_entry(key, multiplicity)` on
   `exact_public_bus_name(table_id)`; main-side `lookup_key(tuple, ONE)` is unchanged. The
   descriptor-carried row values are pinned exactly as `Ir2Air::ByteTable` pins its value column —
   the natural home is a **preprocessed (VK-time-committed) matrix** carrying the manifest, which
   the manifest already deserves: it is part of relation identity today
   (`effect_vm_descriptor2_semantic_fingerprint`).
5. **Producer preflight** — `build_traces`' exact-multiset equality check becomes a *subset* check
   plus multiplicity accumulation (the byte-histogram pattern at `descriptor_ir2.rs:4430` is the
   template).
6. **Caps** — `MAX_EXACT_PUBLIC_ROWS = 128` then bounds the *alphabet × state space*, not the word
   length or the fold count, which is the bound it should always have been.

### What this buys, at the composed-automaton sizes we actually want

| workload | deployed shape A | recommended shape |
|---|---|---|
| 1 automaton, 128-symbol word | 270.3 KiB, 129 instances (at the cap) | ~55 KiB, 2 instances |
| 8 automata, 16-symbol word | 259.8 KiB, 129 instances (at the cap) | ~46 KiB, 2 instances |
| 8 automata, 1024-symbol word | **inexpressible** (needs 8192 manifest rows) | 80.5 KiB, 207 ms |
| 32 automata, 1024-symbol word | **inexpressible** | 105.7 KiB, 514 ms |

## 5. Honest residuals

* **Shape B is a cost proxy, not a soundness artifact.** The 4-bit range lookup measured as
  "shared multiplicity table" is the same bus/aux/instance machinery a transition table would use,
  but it is a 1-tuple, not a 3-tuple. Tuple arity changes the `β`-combination inside one aux column
  and adds `(arity−1)` opened felts per query per lane — an analytic `+2 · 4 B · 19 · 2 = 304 B` per
  lane on top of the measured 1076 B. It does not change the instance count, the aux-column count,
  or the amortization argument. **The shipped-shape number would be ~1.35 KiB per automaton, not
  1.05.**
* **The timings are minimum-user-CPU on a contended box, single-threaded.** They are a faithful
  *relative* scaling law and a conservative *absolute* one (the production prover is
  rayon-parallel). Wall-clock production numbers are NOT derivable from this table.
* **The PoW grind is a per-witness exponential sample.** `G ≈ 5 ms` is one draw at one grid point,
  not an expectation; the spread across grid points measured 0.5 ms to 44 ms at 16 bits.
* **No claim past the model resolution.** `Satisfied2Public` / `Satisfied2Subset` are the Lean
  *model* of the deployed LogUp/AIR; a STARK proves the TRACE, not the witness generator, and the
  FRI floor is undischarged. Nothing here changes that.
* **Step 4 is unwritten.** The Lean half (steps 1–2) is proved and green; the Rust `PublicTable`
  AIR + preprocessed-manifest commitment is designed here and not implemented. The 26x/9x numbers
  are measured on the byte-table realization of that mechanism, not on a shipped `PublicTable`.

## 6. Artifacts

| file | what it is |
|---|---|
| `circuit/tests/tiny_automata_prover_shape_measure.rs` | the harness: shape A/B descriptor generators (emitted in the Lean `emitVmJson2` wire grammar), the `(n, k)` sweeps, and `one_point` — the single-grid-point CPU-time mode with `MEGAFAST_ONE` / `MEGAFAST_REPS` / `MEGAFAST_POW` |
| `metatheory/Dregg2/Circuit/Emit/DfaRoutingSubsetTableCost.lean` | `Satisfied2Subset`, `ofPublic`, `tableRouting_refines_classify_subset`, `tableRouting_refines_classify_of_public`, and both tamper canaries re-proved under the weaker hypothesis. `#assert_axioms`-clean; green in 20.2 s / 2.87 GB peak RSS; mutation-canary verified (flipping the witness classification turns it red and trips the axiom tripwire) |

Reproduce:

```
cargo test -p dregg-circuit --release --test tiny_automata_prover_shape_measure -- --nocapture
MEGAFAST_ONE=B:32:1024 MEGAFAST_REPS=5 MEGAFAST_POW=0 RAYON_NUM_THREADS=1 \
  /usr/bin/time -p ./target/release/deps/tiny_automata_prover_shape_measure-* one_point
cd metatheory && lake env lean Dregg2/Circuit/Emit/DfaRoutingSubsetTableCost.lean
```

---

# 7. THE ABSOLUTE NUMBERS, and the DECLARED-ROW axis isolated

Measured 2026-07-25, same `HEAD`, same production `ir2_config`. Two things §1–§4 did not have:
an **absolute** answer ("megafast" in milliseconds, not ratios), and the declared-row cost measured
**at a bit-identical main trace** instead of confounded with trace growth.

## 7.0 Timing method, and why the hedging in §1 can be dropped

`/usr/bin/time -p` user+sys CPU, `RAYON_NUM_THREADS=1`, min over 2 invocations, per-grid-point
`MEGAFAST_REPS=0` baseline subtracted, 20 reps (10 at `n = 1024`). Quantization is 0.5 ms/proof
(1 ms at 10 reps).

**The single-thread CPU number IS the end-to-end wall number here** — measured, not assumed. Re-run
at DEFAULT rayon threads on the same box:

| point | 1-thread CPU | default-threads wall | default-threads CPU |
|---|---|---|---|
| `B k=4 n=256` | 53.0 ms | **50.0 ms** | 47 ms |
| `B k=4 n=1024` | 175.0 ms | **183.0 ms** | 174 ms |
| `A k=4 n=16` | 47.5 ms | **50.0 ms** | 48 ms |

Wall ≈ CPU ≈ single-thread CPU: at these trace heights (2⁴–2¹⁰ rows) rayon finds nothing to
parallelize, so the prover is effectively single-threaded and §1's "conservative absolute" caveat is
retired. These are real wall-clock times for one composed automaton proof.

## 7.1 ⚑ HOW FAST IS A COMPOSED TINY-AUTOMATA PROOF? — 4 automata, one word

Production config (16-bit FRI query PoW **included**). Wire bytes are exact and load-independent.

| `k=4`, word `n` | **shape B (recommended: shared table)** | | | **shape A (deployed `exact_public_rows`)** | | |
|---|---|---|---|---|---|---|
| | prove | wire | inst | prove | wire | inst |
| 16 | **4.0 ms** | **41.34 KiB** | 2 | 47.5 ms | 146.80 KiB | 65 |
| 64 | **22.5 ms** | **54.12 KiB** | 2 | — INEXPRESSIBLE — | | |
| 256 | **53.0 ms** | **68.28 KiB** | 2 | — INEXPRESSIBLE — | | |
| 1024 | **175.0 ms** | **76.10 KiB** | 2 | — INEXPRESSIBLE — | | |

(`A k=4 n=32`: 30.0 ms / 266.63 KiB / 129 instances — the last point the cap admits. Past it the
prover refuses: `exact-public table dfa_transition_table has 256x3 cells; bounded tooth permits at
most 128 rows and 4096 cells`.)

**So: a 4-automaton composition over a 256-symbol word is 53 ms and 68 KiB.** Not 10 ms, not 1 s.
Over a 1024-symbol word, 175 ms and 76 KiB. In the shape that is deployed today, it is not provable
at any speed. Verification is 1.5–4 ms for shape B and ~13 ms for shape A at 129 instances
(single samples from the `--nocapture` run, load-contaminated).

`k=1` reference, same config: A 14.5 ms/63.36 KiB (`n=16`), 18.5/158.08 (`n=64`), 35.5/270.31
(`n=128`); B 8.5/38.19, 20.5/50.89, 47.0/64.98 (`n=256`), 132.0/73.00 (`n=1024`).

⚠ The PoW grind rides inside every production number as a **fixed but arbitrary per-`(descriptor,
witness)` draw**: across the 19 production points here the grind (production minus the `pow = 0`
re-run of the same point) ranged **0.5 ms to 37 ms**. `A k=4 n=16` is 47.5 ms in production but
10.5 ms at `pow = 0` — that 37 ms is a lottery ticket, not the automaton, and it is why
`A k=4 n=16` (47.5 ms) reads *slower* than `A k=4 n=32` (30.0 ms). `pow = 0` companions:
`A 4:16` 10.5, `A 4:32` 21.5, `B 4:16` 3.5, `B 4:64` 11.5, `B 4:256` 39.5, `B 4:1024` 163.0 ms.

## 7.2 ⚑ THE DECLARED-ROW COST, at a bit-identical main trace

§3 read the declared-row cost off sweeps that moved the trace at the same time. This isolates it:
`k = 1`, `n = 16`, 3 main columns, the same witness values — and `m` **identical** transition
lookups per row, which multiplies the declared manifest (exact-multiset LogUp forces
`#declared rows = #queries`, so `m` is the only handle that moves declared rows at a fixed trace).
Shape B at the same `(k, n, m)` is the control: same trace, same `m` bus interactions, hence the
same `m` LogUp extension aux columns, and **2 instances always** — so `A − B` is the pure
`ExactPublicRow`-instance cost.

| declared rows `D` | instances | A prove (pow=0) | B control | **A − B** | A wire | B wire |
|---|---|---|---|---|---|---|
| 16 | 17 | 4.50 ms | 2.50 ms | 2.00 ms | 64 878 B | 39 105 B |
| 32 | 33 | 7.00 ms | 2.50 ms | 4.50 ms | 93 483 B | 39 886 B |
| 64 | 65 | 11.50 ms | 3.50 ms | 8.00 ms | 149 271 B | 41 208 B |
| 128 | 129 | 20.50 ms | 4.00 ms | 16.50 ms | 264 230 B | 43 998 B |

```
per DECLARED ROW, at a fixed trace:   0.143 ms  and  1 780 B (1.74 KiB)
   of which the forced aux column:    0.013 ms  and     44 B
   ⇒ per ExactPublicRow INSTANCE:     0.130 ms  and  1 736 B (1.70 KiB)
```

`(A−B)/D` is 0.125, 0.141, 0.125, 0.129 ms across the four points — linear **through the origin**,
as it must be if the cost is one batch instance per declared row. Wire slope is 1788/1743/1796 B
across the three steps. The §3 estimates (0.15 ms, 1.76 KiB) were within 10% despite the confound.

**What this makes the discipline question, in milliseconds.** Every declared row costs 0.143 ms and
1.74 KiB *whatever the word length is*:

| discipline | declared rows `D` | declared-row bill, 4 automata over a 256-symbol word |
|---|---|---|
| RUN table (`exactPublicRows` today: the run's edges, with multiplicity) | `k·n` = 1024 | **+146 ms, +1.74 MiB** — and unreachable, `D ≤ 128` |
| WHOLE graph, DEDUPLICATED, shared across lanes (2-state/2-symbol DFA) | `|Q|·|Σ|` = 4 | **+0.6 ms, +7 KiB** |
| WHOLE graph, deduplicated (16-state/8-symbol automaton) | 128 | **+18 ms, +222 KiB** |

(The 1024-row row is the measured 0.143 ms/1.74 KiB law extrapolated past the cap — labelled
extrapolation, not a measurement.)

⚑ **This inverts §4b's framing.** The whole-graph discipline is *cheaper* in declared rows than the
run-table discipline for any word longer than `|Q|·|Σ|`, and it is `k`-independent when `k` lanes
share one table. The cost driver was never "whole graph vs run"; it is **UNIT CAPACITY** — under
`exactPublicRows` a deduplicated whole-graph table is not merely expensive, it is unsatisfiable
unless the word's run is an Eulerian path. Multiplicity is what buys both the dedup and the sharing.

## 7.3 The composition law, with the declared-row term

Independently reproduced on this grid (different points, different axis) and extended:

```
T(n, k, D)  ≈  G  +  F·n  +  c·k·n  +  d·D
   F ≈ 0.10  ms per trace row        (B k=4 pow=0: (163.0−3.5)/1008 = 0.158 = F + 4c)
   c ≈ 0.013 ms per lane-row         (B prod k=1→4 at n=1024: (175−132)/(3·1024) = 0.0140)
   d ≈ 0.143 ms per DECLARED row     (§7.2, at a fixed trace)
   G   = the 16-bit PoW grind, a per-(descriptor,witness) draw measured 0.5–37 ms
W(n, k, D)  ≈  W₀ + (≈6 KiB per FRI layer) + 1.05 KiB·k + 1.74 KiB·D
   (B k=1 wire 38.19 → 50.89 → 64.98 → 73.00 KiB at n = 16, 64, 256, 1024;
    B lane slope (41.34−38.19)/3 = 1.05 KiB — §2's number, reproduced exactly)
```

`d` is 11x `c` and 1.4x `F`: **one declared row costs more prover time than one trace row.** That
single inequality is the whole recommendation.

## 7.4 Recommendation, with the price tag attached

Ship the shape §4 designed — `RowSemantics.publicRows` / `Ir2Air::PublicTable`, one instance of
height `2^⌈log₂|T|⌉` carrying the DEDUPLICATED distinct transitions plus a witnessed multiplicity
column — and declare the **whole graph**, deduplicated, shared by all `k` lanes. Measured price of
that mechanism (shape B is the byte-table realization of exactly it): **4.0 ms / 41.3 KiB for 4
automata over a 16-symbol word, 53 ms / 68.3 KiB at 256, 175 ms / 76.1 KiB at 1024, two batch
instances at every size, verify 1.5–4 ms.** Price of not shipping it: `(k=4, n=256)` is
inexpressible, and merely lifting `MAX_EXACT_PUBLIC_ROWS` without adding multiplicity would still
cost +146 ms and +1.74 MiB over that (extrapolated law, §7.2).

Unchanged from §4: the emit-path change is steps 1–6 there; the Lean half is authored and green
(`DfaRoutingSubsetTableCost.lean`), the Rust `Ir2Air::PublicTable` is unwritten, and the refinement
theorem survives. Unchanged from §5: shape B is a **cost proxy** (1-tuple range lookup, not a
3-tuple transition lookup; add the analytic ~304 B/lane for arity), the FRI floor is undischarged,
and a STARK proves the trace, not the witness generator.

Reproduce §7:

```
cargo test -p dregg-circuit --release --test tiny_automata_prover_shape_measure --no-run
./target/release/deps/tiny_automata_prover_shape_measure-* absolute_wire_sizes  --exact --nocapture
./target/release/deps/tiny_automata_prover_shape_measure-* declared_row_axis_sizes --exact --nocapture
MEGAFAST_ONE=B:4:256 MEGAFAST_REPS=20 RAYON_NUM_THREADS=1 \
  /usr/bin/time -p ./target/release/deps/tiny_automata_prover_shape_measure-* one_point --exact
MEGAFAST_ONE=A:1:16:8 MEGAFAST_REPS=20 MEGAFAST_POW=0 RAYON_NUM_THREADS=1 \
  /usr/bin/time -p ./target/release/deps/tiny_automata_prover_shape_measure-* one_point --exact
```
