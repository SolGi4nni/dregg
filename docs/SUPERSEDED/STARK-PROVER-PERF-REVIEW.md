# STARK prover — mechanical-sympathy review (2026-07-06)

Triggered by an observed symptom: the DSL STARK prover "isn't even using a full core."
Confirmed, root-caused, and quantified. This is a **review + scoped plan**, not a landed
fix — the prover is deployed, soundness-critical, and `circuit/src/stark.rs` is a
shared file with a live concurrent lane. The rewrite is ember's call to schedule.

## The symptom, measured

`cargo run -p dregg-zkoracle-prove --example real_proof --release` (the injection-leg
STARK, one trace row per field byte), on a 12-core box:

| field | trace rows | prove | verify |
|---|---|---|---|
| 32 B | 32 | 15.6 ms | 6.0 ms |
| 256 B | 256 | 457 ms | 8.7 ms |
| 1024 B | 1024 | **20.3 s** | 14.5 ms |
| 64 KB | 65536 | (killed — did not finish) | — |

256 → 1024 rows is **4× the work for 44× the time**. That is between O(n²) and O(n³),
not the O(n log n) a STARK prover is supposed to be. `top` during the run: **99% of ONE
core**, the other 11 idle. So: not memory-bound — **single-threaded and
super-linear-compute-bound**. Verify stays cheap (correct: it is O(queries · log n)).

## Root cause — two textbook informatics mistakes, both in `circuit/src/stark.rs`

The prover builds its evaluation domains from **roots of unity**
(`get_root_of_unity`, `build_evaluation_domain`, up to 2^27 — the exact structure that
makes an NTT possible), and then **does not use the NTT**:

1. **`interpolate` (`stark.rs:276`) is naïve Lagrange — O(n²) at best.** For each of `n`
   trace points it multiplies out an `n`-term basis polynomial (a growing `Vec` per
   step), so the trace→coefficients step is O(n²) field ops per column (with the
   poly-grow it trends worse). Over a roots-of-unity domain this is exactly what an
   **inverse NTT does in O(n log n)**. Called per column at `stark.rs:916` and `:1033`.

2. **Multi-point evaluation is per-point Horner — O(n · domain_size).** `poly_eval`
   (`stark.rs:232`, Horner, O(n)) is called inside a `.map()` over **every** point of
   the blown-up eval domain (`stark.rs:920`, `:1041`), i.e. O(n · blowup·n) = O(n²·blowup)
   per column. A **forward (coset) NTT does the whole low-degree extension in
   O(domain_size log domain_size)**.

3. **Single-threaded.** No `rayon` in the crate; the per-column interpolate/eval loops
   (`for col in 0..num_cols`) and the domain-eval maps are sequential. The work is
   embarrassingly parallel across columns and across evaluation points — on this box
   that is 11/12 cores left on the floor even before the algorithmic fix.

Net: for an `n`-row trace the prover pays ~O(n²) single-threaded where the standard STARK
LDE pipeline is O(n log n) NTT, parallelized. The two compound — the quadratic term is
why 1 KB already takes 20 s.

## The fix (standard, and the domain is already NTT-ready)

- **Replace `interpolate` + per-point `poly_eval` with an NTT-based LDE:** inverse-NTT on
  the trace subgroup → coefficients; zero-extend; forward-NTT on the (coset) eval subgroup
  → the low-degree extension. Radix-2 Cooley–Tukey over BabyBear; the roots of unity are
  already computed by `get_root_of_unity`. O(n log n), same result (an equality test
  against the current `interpolate`/`poly_eval` on random traces pins correctness).
- **Parallelize across columns with `rayon`** (`trace.par_iter()` for the NTTs, and the
  Merkle-leaf hashing map at `stark.rs:1046`). Independent, no shared state.

Expected: the 1 KB injection proof drops from ~20 s to the millisecond range, and it
scales to the 64 KB+ traces that currently never finish. Verify is already fine.

## ⚠ Why this is a review and not a landed patch

- **Soundness-critical.** A wrong NTT silently produces wrong (or unsound) proofs. The
  swap must be gated by an exact equality test against the current path on random
  traces + the full existing STARK test suite, before it can be trusted — not a
  from-thin-context edit ([[feedback-be-thoughtful-not-trigger-happy]], never quick-fix).
- **Shared file, live lane.** `circuit/src/stark.rs` sits beside `circuit/src/*` files a
  concurrent session is editing right now. Landing an NTT rewrite needs the coordination
  window, not a mid-swarm edit ([[feedback-swarm-shared-tree-clobber-hazard]]).
- **It is a real, self-contained lane** (~a day: NTT + coset LDE + rayon + the equality
  gate + re-bench), worth scheduling — it makes every STARK in the tree (not just
  zkOracle) faster, and unblocks proving over large inputs at all.

## Note on the zkOracle injection leg specifically

Independent of the prover fix, the injection leg's trace is **one row per input byte**,
which is a poor encoding for large fields (a 256k-token context field would be a
256k-row trace). Two orthogonal improvements, both in `zkoracle-prove` (my lane), once
the prover is fast: pack multiple bytes per row, or run the DFA over the CFG token stream
(already O(tokens)) rather than raw bytes. Neither is the bottleneck today — the prover
is — but they compound the win.
