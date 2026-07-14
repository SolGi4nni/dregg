# FRI-PARAM-FRONTIER — the security-vs-cost map for the deployed FRI config

**What this is.** A parameterized model mapping FRI knobs
`(log_blowup, num_queries, max_log_arity, query_pow_bits)` to
`(proven-bits, conjectured-bits, proof-size, prover-cost, verifier-cost)`, using the
**actual** soundness formulas and the **measured** IR-v2 cost grid, plus a grid search for
the leanest config that still hits a 128-bit target. This is a READ-ONLY map — it changes
**nothing**. The deployed config is ember's to move. The runnable model is
[`fri_param_frontier.py`](./fri_param_frontier.py) (reproduces the measured grid to < 0.25 KiB).

Deployed IR-v2 config (`circuit/src/descriptor_ir2.rs:5382-5386`): `log_blowup=6`,
`log_final_poly_len=0`, `max_log_arity=3` (arity 8), `num_queries=19`, `query_pow_bits=16`.
Deployed v1 config (`circuit/src/plonky3_prover.rs:98-102`): `log_blowup=3`, `q=38`, `pow=16`
(security parity with IR-v2 on both ledgers).

---

## 1. The model

### 1a. Soundness ledgers (`circuit/tests/fri_params_soundness_budget.rs:45-53`)

```
conjectured (capacity)  = num_queries · log_blowup       + pow_bits
proven      (Johnson)   = num_queries · log_blowup / 2   + pow_bits     (integer floor)
```

- **Conjectured** = the FRI capacity / list-decoding-to-`(1-ρ)` conjecture: ~`log_blowup`
  soundness bits per query. This is the field-standard assumption every production STARK quotes
  (`:11-15`). The enforced floor is `CONJECTURED_FLOOR_BITS = 128` (`:42`).
- **Proven** = the Johnson bound (list-decoding to `√ρ`, BCIKS20): ~`log_blowup/2` bits per
  query. This is what is *proven* today (`:16-18`); reported, not floored.
- **Both are additionally capped** by `min(·, ~124)` — the degree-4 BabyBear challenge
  extension `2^124` (`circuit/src/plonky3_prover.rs:63`, `type EF = BinomialExtensionField<BabyBear,4>`;
  comment `:113`) — and by the Poseidon2 commitment hash. So the honest **system** headline is
  `min(ledger, 124)`.
- **`max_log_arity` and `log_final_poly_len` do NOT enter the soundness formula.** Arity is the
  FRI folding factor; `arity=8` (`max_log_arity=3`) is already measured-optimal (dropping to
  arity 2 costs **+9%** size — PROOF-ECONOMICS §1). `log_final_poly_len` is an early-stop knob
  (~-3% at 2⁴, marginal). Neither is a security lever; leave both pinned.

Deployed reads: conjectured `6·19+16 = 130`, proven `6·19//2+16 = 73`. Effective (field-capped)
= `min(130,124) = 124`.

### 1b. Cost model, anchored to the measured grid

The measured IR-v2 grid — the same real transfer proven at every size-parity `(lb, q)` point,
4-bit-nibble range table (`circuit/tests/effect_vm_ir2_size_measure.rs:355-403`):

| (lb, q) | proof | prove | verify | conj / proven |
|---|---:|---:|---:|---:|
| (3, 38) | 194.1 KiB | 29 ms | 6.9 ms | 130 / 73 |
| (4, 29) | 159.7 KiB | 20 ms | 6.2 ms | 132 / 74 |
| (5, 23) | 136.1 KiB | 32 ms | 4.9 ms | 131 / 73 |
| **(6, 19) = deployed** | **120.4 KiB** | 58 ms | 4.1 ms | 130 / 73 |
| (7, 17) | 114.0 KiB | 101 ms | 4.0 ms | 135 / 75 |
| (8, 15) | 106.5 KiB | 183 ms | 3.6 ms | 136 / 76 |

The proof is `fixed OOD opened_values (~20.0 KiB) + commitments (81 B) + the FRI opening`. The FRI
opening is `q` queries, each opening a row of every committed matrix **plus its Merkle path**; the
path length is `log₂(trace_height) + log_blowup`, so per-query bytes grow **linearly in
log_blowup**. Fitting the two extreme anchors:

```
proof_bytes(lb, q) ≈ 20_561 + q · (3971 + 239 · log_blowup)
```

This reproduces all six measured points to **< 0.25 KiB**. The cost shape, in one line:
**queries dominate the wire; blowup is nearly free to the prover** (tables are 2³–2⁸ rows, so the
high-blowup LDE costs milliseconds) — which is why IR-v2 trades blowup UP and queries DOWN vs v1.

- **Prover cost** is LDE-dominated: `~2^log_blowup · trace`, so prove time roughly **doubles per
  blowup step** (measured 20→32→58→101→183 ms for lb 4→8). Queries barely touch it. (Model
  numbers for non-measured points are `2^lb` extrapolations off the lb=6 anchor and run a little
  high — trust the measured column where present.)
- **Verifier cost** falls with query count (fewer openings): 6.9→3.6 ms across q 38→15.

---

## 2. The efficient frontier

### FRONTIER A — conjectured ledger, target 128 (the enforced floor), pow=16

`min q = ceil((128-16)/lb) = ceil(112/lb)` per blowup:

| lb | q | proof | prove | verify | conj / proven |
|---:|---:|---:|---:|---:|---:|
| 3 | 38 | 194.0 KiB | 29 ms | 6.9 ms | 130 / 73 |
| 4 | 28 | 154.8 KiB | ~14 ms | 5.7 ms | 128 / 72 |
| 5 | 23 | 136.1 KiB | 32 ms | 4.9 ms | 131 / 73 |
| **6 | 19 | 120.4 KiB | 58 ms | 4.1 ms | 130 / 73  ← deployed** |
| 7 | 16 | 108.3 KiB | ~116 ms | 3.9 ms | 128 / 72 |
| 8 | 14 | 100.5 KiB | ~232 ms | 3.6 ms | 128 / 72 |

The frontier is a clean **proof-size ↔ prover-time** trade, all at ~128-bit conjectured:
- **Cheapest prover:** `(4, 28)` — ~14 ms prove (LESS than deployed 58 ms) but 154.8 KiB (larger wire).
- **Deployed `(6, 19)`** sits ON the frontier — it is the size/prover **knee**.
- **Smallest proof at 128-conj:** `(8, 14)` — 100.5 KiB (~17% smaller than deployed) but ~4×
  the prover cost. `(7, 16)` = 108.3 KiB at ~2× prover is the intermediate.

### FRONTIER B — PROVEN (Johnson) ledger, target 128, pow=16

`min q = ceil(224/lb)` (needs `q·lb ≥ 224`, double the conjectured requirement):

| lb | q | proof | conj / proven |
|---:|---:|---:|---:|
| 6 | 38 | 220.7 KiB | 244 / 130 |
| 7 | 32 | 196.5 KiB | 240 / 128 |
| 8 | 28 | 180.9 KiB | 240 / 128 |
| 10 | 23 | 163.0 KiB | 246 / 131 |

Hitting **128 PROVEN roughly doubles proof size and prover cost** vs the conjectured target
(leanest ≈ 163 KiB at lb=10, with an exploding prover; ≈ 181 KiB at the practical lb=8). This is
the price of not leaning on the capacity conjecture.

---

## 3. Findings

### The leanest 128-bit config, and where the deployed config already sits

**On the conjectured ledger, `(6, 19)` is already minimal at its blowup.** Dropping one query to
`(6, 18)` gives `6·18+16 = 124` — **below the 128 floor**. The apparent "2 wasted bits" (130 vs
128) are *granularity slack*, not reclaimable at lb=6: a query is worth 6 bits there, so you
either sit at 130 or fall to 124. To trim below `(6,19)` you must move blowup (or PoW, below).
The deployed config is **not fat** — it is the size/prover knee of Frontier A.

The genuinely leaner 128-conj options are all blowup moves off the knee:
- want a **smaller wire**, accept a slower prover → `(7,16)` 108 KiB / ~2× or `(8,14)` 100 KiB / ~4×;
- want a **faster prover**, accept a bigger wire → `(4,28)` 155 KiB / ~0.25× prove.

### The 128-bit claim rests on the CONJECTURAL ledger

The deployed **proven** (Johnson) budget is **73 bits** — well under 128. The headline "128-bit"
security is the *conjectured* capacity bound (130). This is the field-standard posture (every
plonky3-ecosystem STARK quotes the same conjecture), and it is honestly labeled as such in the
budget gate — but it is worth stating plainly: **the deployed 128-bit claim is conjectural, not
proven.** The proven floor today is 73.

### The ~124-bit field cap is the real ceiling

Both ledgers are capped at `min(·, 124)` by the degree-4 challenge extension. So the deployed
conjectured 130 is *effectively 124*. Two consequences:
1. A true **128-bit** system is not reachable with this field regardless of FRI knobs — it would
   need a larger extension (degree-5 BabyBear ≈ `2^155`). The 128 in the budget gate is a floor on
   the **FRI-query term** (the knob-drift tooth), deliberately set above the 124 field cap for margin.
2. Against the *field cap* (124) rather than the *query-term floor* (128), `(6, 18)` suffices
   (conj 124, ~115 KiB) — **1 query / ~5 KiB leaner** than deployed. Taking it means declaring the
   target as "match the field cap" and dropping below the test's 128 floor: a deliberate,
   named decision, not this map's call.

### Levers, ranked

- **Query-PoW is the cheapest bits.** Each PoW bit adds directly to both ledgers for ~zero wire
  cost (one witness) and a one-time `2^pow`-hash prover grind. Raising `pow` 16→20 lets q drop
  19→18 at lb=6 (conj stays ≥128), shaving ~5 KiB for a `2^20`-hash grind (sub-second, one-time).
  Diminishing (each bit doubles the grind), but real and currently unused.
- **Blowup** is the main size lever (nearly free to the prover until the LDE dominates ~lb≥7).
- **Queries** dominate the wire but are the security workhorse; they *are* the knob you trim when
  a bound tightens.
- **Arity / final-poly** — pinned-optimal, not security levers. Leave them.

### What each bound-tightening buys in efficiency

The **list term is not the lever.** The list-decoding soundness error carries an additive `L/|F|`
term (list size over field), but with `|F| ≈ 2^124` and `L` polynomial, that is ~2^-116 of
headroom — it barely moves the budget. The recent tightenings (BCIKS20 list-decoding to `δ_J=1-√ρ`
fully proved; correlated-agreement off the boundary; the interior regime —
`docs/reference/STARK-SOUNDNESS-CENSUS.md`, `lean-circuit.md:82-92`) matter because they concern
the **decoding radius**, which sets the *per-query bit rate*:

- The gap between the **proven** ledger (`lb/2`, the `√ρ` Johnson rate) and the **conjectured**
  ledger (`lb`, the `1-ρ` capacity rate) IS the gap between the Johnson radius and the capacity
  radius. Every step the proven analysis moves from `√ρ` toward `1-ρ` (via proven up-to-capacity
  decoding, or by staying strictly **interior** to the list-decoding radius so per-query rejection
  approaches the capacity value) raises the proven per-query rate from `lb/2` toward `lb`.
- **If the proven ledger reached the full `lb` rate:** deployed `(6,19)` proven jumps
  **73 → 130** with NO config change — the 128 claim becomes *proven*, not conjectured.
- **Or, holding proven-128 as the target:** the leanest config collapses from Frontier B back onto
  Frontier A — **~163 KiB → ~95 KiB, ~42% smaller, at the same PROVEN security.** Equivalently, at
  the deployed proof size you would buy proven-128 instead of proven-73.

That is the payoff shape: **bound-tightening on the decoding radius is worth ~2× in query·blowup
— either ~40% off the wire at fixed proven security, or a 73→130 proven jump at fixed cost.** The
list-size term is not where the bits are.

---

*Model + grid search: [`fri_param_frontier.py`](./fri_param_frontier.py) — run
`python3 docs/reference/fri_param_frontier.py`. This document and the script change no deployed
parameter; they are the map for choosing a leaner config later.*
