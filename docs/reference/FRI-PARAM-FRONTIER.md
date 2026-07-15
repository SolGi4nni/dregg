# FRI-PARAM-FRONTIER — the security-vs-cost map for the deployed FRI config

**What this is.** A parameterized model mapping FRI knobs
`(log_blowup, num_queries, max_log_arity, query_pow_bits)` to
`(proven-bits, capacity-bits, proof-size, prover-cost, verifier-cost)`, using the
**actual** soundness formulas and the **measured** IR-v2 cost grid. This is a READ-ONLY map — it
changes **nothing**. The deployed config is ember's to move. The runnable model is
[`fri_param_frontier.py`](./fri_param_frontier.py) (reproduces the measured grid to < 0.25 KiB).

**Headline, up front.** The FRI **capacity** conjecture (per-query proximity to `1−ρ`) is
**REFUTED** — Kambiré (arXiv 2604.09724 + eprint 2025/2046) constructs counterexamples for coset
Reed–Solomon at `ρ ∈ (0, ½)`, covering our `ρ = 1/64`. So the "capacity-bits" column below is a
knob-drift *engineering* ledger, **not** an approachable security target. The **proven** floors are
what we stand behind: the general Johnson (`√ρ`) bound gives `73` bits at the deployed config, and —
for the deployed **dim-2 constant-fold recursion code specifically** — the field-independent counting
bound proves **~112.6 bits** (`wrap_perFold_soundness_capacity`,
`metatheory/Dregg2/Circuit/FriCorrelatedAgreementSharp.lean` §8, `03a6ee758`).

**⚑ CORRECTED (2026-07-15) — the ~112.6 is proved at an arity the deployed prover does NOT run.**
§8's model folds **2-to-1**; the deployed config folds at **arity 8** (`max_log_arity=3`). The
transfer was never mechanized. It is now derived and mechanized
(`metatheory/Dregg2/Circuit/FriArityTransfer.lean`, Lake-green, `sorry`-free): the same counting
method at the deployed arity 8 proves **~109.84 bits** (`14112 = 7·2016` good challenges over
`|F| ≈ 2^123.6`), exactly `log₂ 7 ≈ 2.807` bits below ~112.6, and **~112.6 provably does not hold
at arity 8** by this method (`arity8_error_not_lt_2e112`). The loss is the degree-7 moment curve
(§1a). **The standing per-fold posture at the DEPLOYED config is ~109.84 proven bits**, not ~112.6;
~112.6 remains correct as a statement about arity-2 folding (which only the gnark ETH-wrap runs).
Both figures sit far above the general Johnson floor (`73`). No query/PoW bump and no config change
are planned; re-pointing the posture number is ember's call.

Deployed IR-v2 config (`circuit/src/descriptor_ir2.rs:5382-5386`): `log_blowup=6`,
`log_final_poly_len=0`, `max_log_arity=3` (arity 8), `num_queries=19`, `query_pow_bits=16`.
Deployed v1 config (`circuit/src/plonky3_prover.rs:98-102`): `log_blowup=3`, `q=38`, `pow=16`
(security parity with IR-v2 on both ledgers).

---

## 1. The model

### 1a. Soundness ledgers (`circuit/tests/fri_params_soundness_budget.rs:45-53`)

```
capacity (REFUTED)      = num_queries · log_blowup       + pow_bits
proven   (Johnson)      = num_queries · log_blowup / 2   + pow_bits     (integer floor)
```

- **Capacity** = the FRI capacity / list-decoding-to-`(1-ρ)` conjecture: ~`log_blowup`
  soundness bits per query. **This conjecture is REFUTED** — Kambiré (arXiv 2604.09724, eprint
  2025/2046) exhibits coset-RS counterexamples at `ρ ∈ (0, ½)`, which cover our `ρ = 1/64`. It is
  therefore **not** a live/approachable security assumption; the column survives only as the
  historical field-standard *arithmetic* every plonky3-ecosystem STARK quoted, and as the
  knob-drift baseline the budget gate enforces `≥ 128` on as a conservative engineering margin
  (`fri_params_soundness_budget.rs`, honestly re-labeled).
- **Proven** = the Johnson bound (list-decoding to `√ρ`, BCIKS20): ~`log_blowup/2` bits per
  query. This is the general proven floor today (`:16-18`), `73` at the deployed config.
- **Proven, structure-specific (~112.6):** for the deployed **dim-2 constant-fold recursion code**
  the per-fold proximity error is the FIELD-INDEPENDENT counting bound `|Good| ≤ C(64,2) = 2016`
  over the deployed quartic-extension challenge field `F = BabyBear⁴` (`|F| ≈ 2^123.6`), giving
  `2016/|F| < 2⁻¹¹²` — i.e. **~112.6 proven bits** (`wrap_perFold_soundness_capacity`,
  `FriCorrelatedAgreementSharp.lean` §8). This is SOUND against Kambiré: his `n^C` blow-up needs
  `n → ∞`, `r > 2`; at our fixed dimension-`2` (`r = 2`) code his own construction caps at exactly
  `C(n,2)`, and no construction beats a valid counting bound.
- **All are additionally capped** by `min(·, ~124)` — the degree-4 BabyBear challenge
  extension `2^124` (`circuit/src/plonky3_prover.rs:63`, `type EF = BinomialExtensionField<BabyBear,4>`;
  comment `:113`) — and by the Poseidon2 commitment hash. The ~112.6 proven figure already lives
  under this cap (`123.6 − 11 = 112.6`).
- **⚑ CORRECTED (2026-07-15): `max_log_arity` IS a security lever — it costs `log₂ 7 ≈ 2.807`
  bits.** This bullet previously read "`max_log_arity` and `log_final_poly_len` do NOT enter the
  soundness formula … Neither is a security lever". That is **REFUTED** for `max_log_arity` by
  `metatheory/Dregg2/Circuit/FriArityTransfer.lean` (Lake-green, `sorry`-free). The ~112.6 figure
  is proved over a **2-to-1** fold (`FriCorrelatedAgreementSharp` §8,
  `Fold geom α f = E f + α·O f`, `Fin (2^7) → Fin (2^6)`), but the deployed prover folds at
  **arity 8**: the pinned plonky3 rev (`82cfad73`, `fri/src/two_adic_pcs.rs:109-131`) computes
  `lagrange_interpolate_at(xs, evals, beta)`, i.e. `Fold_β f (y) = Σ_{i<8} β^i · g_i(y)` — a
  degree-**7 moment curve**, not an affine line. §8's count rests on a `2×2` Vandermonde pinning
  PAIRWISE intersections to `≤ 1`; at arity 8 two challenges give only 2 equations in 8 unknowns,
  so that step does not survive. The arity-generic count
  (`good_card_le_of_phase_injective`: each pair `{y,z}` lies in `≤ m−1` agreement sets, since
  `H y − H z` is a nonzero degree-`≤ m−1` polynomial whose roots are exactly the good challenges
  folding both to the same constant) gives `|Good| · C(s,2) ≤ (m−1) · C(|κ|,2)`. It **recovers
  §8's `2016` exactly at `m = 2`** — and at the deployed `m = 8` gives `7 · 2016 = 14112`, i.e.
  **~109.84 proven bits** (`arity8_perFold_soundness`, `< 2⁻¹⁰⁹`), NOT ~112.6
  (`arity8_error_not_lt_2e112`). **The deployed per-fold posture is ~109.84 bits.** The ~112.6 is
  recovered at arity 8 only for the weaker inner radius `dIn ≤ 60` (`arity8_at_dIn60_clears_112`).
  Residual: the `M = 1` fiber bound is carried as the HYPOTHESIS `hΦ` (`Arity8FiberBound`) —
  discharging it needs the `|L| = 512`, dim-`8`, rate-`1/64` setup this tree does not build.
- **`log_final_poly_len` does NOT enter the soundness formula** and remains inert (an early-stop
  knob, ~-3% at 2⁴, marginal). Arity `8` remains measured-optimal on COST (dropping to arity 2
  costs **+9%** size — PROOF-ECONOMICS §1) — that trade is now priced at `2.807` bits, and moving
  it is ember's call, not this map's.

Deployed reads: capacity (refuted) `6·19+16 = 130`, proven-Johnson `6·19//2+16 = 73`,
**proven ~112.6** for the recursion fold. Effective field cap `~124`.

### 1b. Cost model, anchored to the measured grid

The measured IR-v2 grid — the same real transfer proven at every size-parity `(lb, q)` point,
4-bit-nibble range table (`circuit/tests/effect_vm_ir2_size_measure.rs:355-403`):

| (lb, q) | proof | prove | verify | capacity / proven |
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

### FRONTIER A — capacity ledger (refuted; engineering-margin floor 128), pow=16

`min q = ceil((128-16)/lb) = ceil(112/lb)` per blowup:

| lb | q | proof | prove | verify | capacity / proven |
|---:|---:|---:|---:|---:|---:|
| 3 | 38 | 194.0 KiB | 29 ms | 6.9 ms | 130 / 73 |
| 4 | 28 | 154.8 KiB | ~14 ms | 5.7 ms | 128 / 72 |
| 5 | 23 | 136.1 KiB | 32 ms | 4.9 ms | 131 / 73 |
| **6 | 19 | 120.4 KiB | 58 ms | 4.1 ms | 130 / 73  ← deployed** |
| 7 | 16 | 108.3 KiB | ~116 ms | 3.9 ms | 128 / 72 |
| 8 | 14 | 100.5 KiB | ~232 ms | 3.6 ms | 128 / 72 |

The frontier is a clean **proof-size ↔ prover-time** trade, all at the 128-bit capacity-margin (the
capacity number itself is refuted; the frontier is an engineering trade, not a security ranking):
- **Cheapest prover:** `(4, 28)` — ~14 ms prove (LESS than deployed 58 ms) but 154.8 KiB (larger wire).
- **Deployed `(6, 19)`** sits ON the frontier — it is the size/prover **knee**.
- **Smallest proof at the 128 margin:** `(8, 14)` — 100.5 KiB (~17% smaller than deployed) but ~4×
  the prover cost. `(7, 16)` = 108.3 KiB at ~2× prover is the intermediate.

### FRONTIER B — PROVEN (Johnson) ledger, target 128, pow=16

`min q = ceil(224/lb)` (needs `q·lb ≥ 224`, double the capacity-ledger requirement):

| lb | q | proof | capacity / proven-Johnson |
|---:|---:|---:|---:|
| 6 | 38 | 220.7 KiB | 244 / 130 |
| 7 | 32 | 196.5 KiB | 240 / 128 |
| 8 | 28 | 180.9 KiB | 240 / 128 |
| 10 | 23 | 163.0 KiB | 246 / 131 |

Hitting the **general Johnson `√ρ` proven bound at 128 roughly doubles proof size and prover cost**
(leanest ≈ 163 KiB at lb=10, with an exploding prover; ≈ 181 KiB at the practical lb=8). Note the
deployed config already carries a **~112.6 proven** bound for its recursion fold via the
structure-specific counting analysis (`FriCorrelatedAgreementSharp.lean` §8) — a stronger proven
number than the general Johnson `73`, at no cost. Frontier B is only relevant if one wants the
*general* Johnson bound (any code) pushed to 128.

---

## 3. Findings

### Where the deployed config sits, and the proven number we stand behind

**On the capacity ledger, `(6, 19)` is minimal at its blowup.** Dropping one query to `(6, 18)`
gives `6·18+16 = 124` — below the 128 engineering margin. The apparent "2 wasted bits" (130 vs
128) are *granularity slack*, not reclaimable at lb=6: a query is worth 6 bits there, so you
either sit at 130 or fall to 124. To trim below `(6,19)` you must move blowup (or PoW, below).
The deployed config is **not fat** — it is the size/prover knee of Frontier A.

The engineering-lean options are all blowup moves off the knee:
- want a **smaller wire**, accept a slower prover → `(7,16)` 108 KiB / ~2× or `(8,14)` 100 KiB / ~4×;
- want a **faster prover**, accept a bigger wire → `(4,28)` 155 KiB / ~0.25× prove.

### The security posture: ~112.6 PROVEN, and the capacity conjecture is REFUTED

The "capacity" ledger (130 at deployed) rests on the FRI capacity conjecture (per-query proximity to
`1−ρ`), and that conjecture is **REFUTED** for coset RS at our rate (Kambiré, arXiv 2604.09724 /
eprint 2025/2046) — so 130 is **not** a security number, only a knob-drift margin the budget gate
holds `≥ 128` on. What we stand behind is what is **proven**:
- the general Johnson (`√ρ`, BCIKS20) floor: **73** at the deployed config, for any code;
- the structure-specific counting floor for the deployed **dim-2 constant-fold recursion code**:
  **~112.6** (`wrap_perFold_soundness_capacity`, `FriCorrelatedAgreementSharp.lean` §8) — the
  field-independent `|Good| ≤ C(64,2) = 2016` over `|F| = babyBearP⁴ ≈ 2^123.6` gives
  `2016/|F| < 2⁻¹¹²`, i.e. `≥ 112` proven bits (exactly `≈ 2⁻¹¹²·⁶⁵`).

**~112.6 is the accepted standing posture (ember, 2026-07-13).** It is a strong, honest,
structure-specific theorem; there is no "gap to 120/128 to close" here — no query/PoW bump and no
config change are planned. The counting bound is sound against Kambiré precisely because his blow-up
needs `n → ∞`, `r > 2`, whereas at our fixed `r = 2`, `n = 64` his own construction caps at `C(64,2)`.

### The ~124-bit field cap

Both the capacity arithmetic and the ~112.6 proven bound sit under the `~124`-bit degree-4 challenge
extension (`|F| ≈ 2^123.6`). A larger extension (degree-5 BabyBear ≈ `2^155`) would be needed to lift
the field cap; the deployed choice is fixed. Against the field cap rather than the 128 knob-margin,
`(6, 18)` is arithmetically 1 query / ~5 KiB leaner — a deliberate, named decision, not this map's
call.

### Levers, ranked

- **Query-PoW is the cheapest bits.** Each PoW bit adds directly to both ledgers for ~zero wire
  cost (one witness) and a one-time `2^pow`-hash prover grind. Raising `pow` 16→20 lets q drop
  19→18 at lb=6 (capacity margin stays ≥128), shaving ~5 KiB for a `2^20`-hash grind (sub-second,
  one-time). Diminishing (each bit doubles the grind), but real and currently unused. (No bump is
  planned — ~112.6 proven is the accepted posture.)
- **Blowup** is the main size lever (nearly free to the prover until the LDE dominates ~lb≥7).
- **Queries** dominate the wire but are the security workhorse; they *are* the knob you trim when
  a bound tightens.
- **Arity / final-poly** — pinned-optimal, not security levers. Leave them.

### Where the proven bits come from (and where they do NOT)

The full capacity rate (`lb` bits/query, the `1−ρ` radius) is **not** an available target: the
capacity conjecture is refuted at our rate (Kambiré), so no general analysis reaches `lb`
bits/query, and the "73 → 130 proven jump" that an earlier draft of this section imagined is
foreclosed. What actually delivers the proven number is the **structure** of the deployed recursion
fold, not a sharper general radius:

- The general Johnson (`√ρ`) analysis gives `lb/2` bits/query — **73** at deployed, for any code.
- The deployed dim-2 constant-fold recursion code admits a **field-independent counting** bound
  (`|Good| ≤ C(64,2) = 2016`), which over the quartic extension gives **~112.6 proven bits** with no
  config change (`wrap_perFold_soundness_capacity`, `FriCorrelatedAgreementSharp.lean` §8). This is
  the number we stand behind; the recent proximity-gap work (interior radius `dIn = 52`, list `186`;
  boundary `dIn = 56`, list `292`; GS-ideal `128` BLOCKED — `STARK-SOUNDNESS-CENSUS.md`,
  `lean-circuit.md:84-92`) is what makes that counting analysis rigorous.
- **The list term is not the lever.** The list-decoding error carries an additive `L/|F|` term, but
  with `|F| ≈ 2^124` and `L` polynomial (`186`/`292`), that is ~`2^-116` of headroom — it barely
  moves the budget; the security lives in `|Good|/|F|`, not in `L`.

The payoff shape, honestly: **the proven ~112.6 for the recursion fold is already banked and
accepted; the general Johnson 73 is the floor for arbitrary codes.** There is no capacity-rate
upside to chase — that door is closed by the refutation.

---

*Model + grid search: [`fri_param_frontier.py`](./fri_param_frontier.py) — run
`python3 docs/reference/fri_param_frontier.py`. This document and the script change no deployed
parameter; they are the map for choosing a leaner config later.*
