# FRI-PARAM-FRONTIER — the security-vs-cost map for the deployed FRI config

**What this is.** A parameterized model mapping FRI knobs
`(log_blowup, num_queries, max_log_arity, query_pow_bits)` to
`(proven-bits, capacity-bits, proof-size, prover-cost, verifier-cost)`, using the
**actual** soundness formulas and the **measured** IR-v2 cost grid. This is a READ-ONLY map — it
changes **nothing**. The deployed config is ember's to move. The runnable model is
[`fri_param_frontier.py`](./fri_param_frontier.py) (reproduces the measured grid to < 0.25 KiB).

**Headline, up front.** The FRI **capacity** conjecture (per-query proximity to `1−ρ`) is
**REFUTED**. Two works, by different authors — the tree previously carried them as one, "Kambiré,
eprint 2025/2046", which is a mis-citation:

* **eprint 2025/2046 is Crites–Stewart** — Elizabeth Crites & Alistair Stewart (Web3 Foundation),
  *On Reed–Solomon Proximity Gaps Conjectures*, rec. 2025-11-05, rev. 2025-12-19. They prove FALSE
  the BCIKS up-to-capacity correlated-agreement conjecture and WHIR's mutual-correlated-agreement
  conjecture, and separately prove that correlated agreement with small enough error implies RS
  list-decoding.
* **Kambiré is arXiv 2604.09724** — Antonio Kambiré, *Proximity Gaps Conjecture Fails Near Capacity
  over Prime Fields*, 9 Apr 2026: a counterexample over prime fields.

⚑ **No counterexample instantiates at BabyBear, and that is NOT a defence.** Kambiré's Thm 1
quantifies the prime AFTER the block length (*"there exist infinitely many block lengths `n` … there
exists a prime `p < n^A` with `p ≡ 1 (mod n)`"*, via a quantitative Linnik theorem), so `p` must GROW
with `n`; dregg runs a FIXED 31-bit prime (`p = 2³¹ − 2²⁷ + 1`). His radius is
`δ = (1−ρ) − Ω(1/log n)` — vanishingly close to CAPACITY, far above the Johnson radius we run at.
Also refuting, none reaching us: **Diamond–Gruen** eprint 2025/2010 (rate → 0 only) and **BCHKS**
ECCC TR25-169 Thm 1.6 (constant rate — `ρ = 1/64` exactly at `τ = 4` — but characteristic 2 and a
random `F₂`-subspace domain, where ours is an odd-characteristic multiplicative coset). A conjecture
refuted in general is not a security basis for anyone, whatever the field-cardinality technicality.
So the "capacity-bits" column below is a knob-drift *engineering* ledger, **not** an approachable
security target.

**What the columns actually read.** Under **BCIKS20** (eprint 2020/654, Lemma 8.2 / Thm 8.3, printed
pp. 40–41) — the paper we name, and whose formula is now MECHANIZED in Lean
(`Dregg2.Circuit.FriLedger.friCommitLedger`) — the deployed wrap's **commit-phase column reads `71`**
at the `|D⁽⁰⁾| = 2^12` fixture, and the ethSTARK eq. (20) composite
`min{−log₂ ε_C, ζ − s·log₂ α} − 1` reads **~70** — not `73`. The `73` in the Johnson column is the
`m → ∞` idealisation that DROPS `ε_C`; it is the query ledger, never "the proven soundness". The
per-fold counting bound (`~112.6` at arity 2 / `109` at the deployed arity 8) is a separate column
and is a claim about **96.9%-far** words, not about the Johnson radius FRI operates at (§1c).

**⚑ CORRECTED (2026-07-15) — the ~112.6 is proved at an arity the deployed prover does NOT run.**
§8's model folds **2-to-1**; the deployed config folds at **arity 8** (`max_log_arity=3`). The
transfer was never mechanized. It is now derived and mechanized
(`metatheory/Dregg2/Circuit/FriArityTransfer.lean`, Lake-green, `sorry`-free): the same counting
method at the deployed arity 8 proves **~109.84 bits** (`14112 = 7·2016` good challenges over
`|F| ≈ 2^123.6`), exactly `log₂ 7 ≈ 2.807` bits below ~112.6, and **~112.6 provably does not hold
at arity 8** by this method (`arity8_error_not_lt_2e112`). The loss is the degree-7 moment curve
(§1a). **The standing per-fold posture at the DEPLOYED config is ~109.84 proven bits**, not ~112.6.

**⚑ CORRECTED AGAIN (2026-07-15, second pass) — "~112.6 is the arity-2 figure, which the gnark
ETH-wrap runs" was ALSO wrong, and there is no single per-fold number for this system.** That
sentence (and the same claim in the old `fri_params_soundness_budget.rs` header) attached a real
number to the wrong object: ~112.6 is a statement about `log_blowup = 6` (`|κ| = 2^6 = 64`, hence
`C(64,2) = 2016`), and the BN254 shrink the gnark circuit actually verifies (`create_outer_config`)
is `log_blowup = 3` — `|κ| = 8`, `|Good| ≤ C(8,2) = 28`, **118 bits**. Arity 2 alone does not pin the
number; `(arity, log_blowup, ext_deg)` does.

The ledger is now **parametric and EXPORTED**: `Dregg2.Circuit.FriLedger.friLedger : FriParams →
Ledger` is a computable Lean function, `@[export dregg_fri_ledger]`-ed, and
`circuit-prove/tests/fri_params_soundness_budget.rs` CALLS it for each of the **7** shipped configs
rather than re-deriving the arithmetic in Rust. One parametric theorem
(`FriLedgerSound.ledger_perFold_soundness`, instantiating `good_card_le_of_phase_injective` at each
config's `m = 2^maxLogArity` and `|κ| = 2^logBlowup`) justifies every row; ~112.6 and ~109.84 are two
of its instances, not a headline and an exception. **Per-fold, as shipped (all from Lean):**

| config | arity | `\|κ\|` | `\|Good\| ≤` | per-fold | Johnson | capacity |
|---|---|---|---|---|---|---|
| `ir2_config` (IR-v2 batch — **deployed wrap**) | 8 | 64 | 14112 | **109** | 73 | 130 |
| `ir2_leaf_wrap_config` (rotated leaf wrap) | 2 | 64 | 2016 | **112** | 73 | 130 |
| v1 `create_config` (production prover) | 8 | 8 | 196 | **116** | 73 | 130 |
| `create_zk_config` (shielded/hiding lane) | 8 | 8 | 196 | **116** | 73 | 130 |
| `create_outer_config` (**the config gnark verifies**) | 2 | 8 | 28 | **118** | 73 | 130 |
| `create_gpu_outer_config` (GPU twin) | 2 | 8 | 28 | **118** | 73 | 130 |
| `create_recursion_config` (recursion default) | 2 | 8 | 28 | **118** | **71** | **128** |

Reading the table honestly, three ways:

* **`ir2_leaf_wrap_config` — arity 2 at `log_blowup = 6` — is the ONE shipped config ~112.6
  describes.** Not the gnark wrap. ⚑ And note the NAME COLLISION: Lean's `FriVerifier.ir2LeafWrapConfig`
  models `dregg_circuit::descriptor_ir2::ir2_config` (arity 8), **not** the Rust fn named
  `ir2_leaf_wrap_config()` (arity 1, via `create_recursion_config_for_inner_fri`'s hardcoded PROBE).
  Two objects, one name, 109 vs 112. Modeled apart as `ir2LeafWrapConfig` / `ir2LeafWrapRotatedConfig`.
* **per-fold RISES as `log_blowup` FALLS (118/116 at 3 vs 112/109 at 6), and that is NOT an upgrade.**
  It is the per-fold proximity-gap factor ONLY: a smaller folded domain has fewer pairs, hence fewer
  good challenges. The rate is paid for in the QUERY ledger. The two columns are independent — a
  theorem, not a caveat (`FriLedgerSound.query_ledger_does_not_determine_perFold`: the wrap and v1
  share a Johnson ledger and differ on per-fold). Never multiply them into one figure.
* **`create_recursion_config` is the weakest shipped config on both query columns** (capacity exactly
  `128` — the drift margin with ZERO headroom; Johnson `71`), and the old gate — which judged 2 of the
  7 — never looked at it. Its `14` query-PoW bits (vs `16` everywhere else) are the whole difference.
  The gate's Johnson floor is now `71`, pinned to that config by name
  (`recursion_config_is_the_weakest_link`), so it cannot be quietly lowered without naming who forced it.

⚑ **The `M = 1` fiber bound is DISCHARGED at every shipped config** (2026-07-15,
`Dregg2/Circuit/FriArityFiberDischarge.lean`). Every per-fold number rests on it, carried as the
per-config hypothesis `hΦ` by the arity-generic count (correctly — that count mentions no setup).
It was discharged only at arity 2 / `log_blowup = 6` (§8's `far_fiber_card` + `wrap_fiber_le_one`)
and open at the deployed arity 8 and at every `log_blowup = 3` config, for want of the RS setups the
tree did not build. Those setups are now built parametrically (`friSetupK`: `|L| = 2^(k+b)`,
`|κ| = 2^b`, dimension `2^k`, rate `2^(−b)`), `far_fiber_card` is generalized to arity `n`
(`far_fiber_card_arity`: `n·|Φ⁻¹(a)| + dOut < |L|`), and `hΦ` is PROVED from farness at all six
configs — four `(k, b)` instances of one theorem (`phase_injective_of_far`):

| config | arity | `log_blowup` | `\|L\|` | `dOut` ⟹ `M = 1` | discharge |
|---|---|---|---|---|---|
| `ir2_leaf_wrap_config` (**deployed**) | 8 | 6 | 512 | `≥ 496` | `arity8_phase_injective` |
| rotated `ir2_leaf_wrap_config` | 2 | 6 | 128 | `≥ 124` | `arity2Lb6_phase_injective` |
| `create_outer_config` (**gnark verifies**) / `create_recursion_config` | 2 | 3 | 16 | `≥ 12` | `arity2Lb3_phase_injective` |
| v1 `create_config` / `create_zk_config` | 8 | 3 | 64 | `≥ 48` | `arity8Lb3_phase_injective` |

Non-vacuous: `phase_injective_fires` exhibits a concrete far word the discharge fires on at EVERY
`(k, b)` (at the deployed config, a `503`-far word against the `≥ 496` requirement).

⚠ **Found on the way — the obligation as it had been NAMED was FALSE, not open.** The `Prop`
`Arity8FiberBound` quantified over EVERY phase map `Φ` with no link to a far word, so the constant
map `Φ = 0` refutes it (`arity8FiberBoundNaive_false`). It had no consumers anywhere, so nothing was
contaminated — but it named no obligation, and it stood for a lane before anyone tried to refute it.
The farness link is the entire content of the claim.

`#assert_axioms` is blind to hypotheses — Lake-green is not hypothesis-free, and the discharge above
is a theorem, not something the axiom check could report.

Every figure sits far above the general Johnson floor (`71`). No query/PoW bump and no config change
are planned; re-pointing the posture number is ember's call.

Deployed IR-v2 config (`circuit/src/descriptor_ir2.rs:5382-5386`): `log_blowup=6`,
`log_final_poly_len=0`, `max_log_arity=3` (arity 8), `num_queries=19`, `query_pow_bits=16`.
Deployed v1 config (`circuit/src/plonky3_prover.rs:98-102`): `log_blowup=3`, `q=38`, `pow=16`
(security parity with IR-v2 on both ledgers).

---

## 1. The model

### 1a. Soundness ledgers (`circuit-prove/tests/fri_params_soundness_budget.rs:45-53`)

```
capacity (REFUTED)      = num_queries · log_blowup       + pow_bits
proven   (Johnson)      = num_queries · log_blowup / 2   + pow_bits     (integer floor)
```

- **Capacity** = the FRI capacity / list-decoding-to-`(1-ρ)` conjecture: ~`log_blowup`
  soundness bits per query. **This conjecture is REFUTED** — Crites–Stewart (eprint 2025/2046)
  disprove it by reduction; Kambiré (arXiv 2604.09724) exhibits a counterexample over prime
  fields. It is therefore **not** a live/approachable security assumption; the column survives
  only as the historical field-standard *arithmetic* every plonky3-ecosystem STARK quoted, and as
  the knob-drift baseline the budget gate enforces `≥ 128` on as a conservative engineering margin
  (`fri_params_soundness_budget.rs`, honestly re-labeled).
- **Johnson — the QUERY column** (list-decoding to `√ρ`): ~`log_blowup/2` bits per query, `73` at
  the deployed config (`:16-18`). ⚑ **This is not "the proven soundness", and BCIKS20 does not say
  it is.** `log_blowup/2` is `−log₂ α` in the `m → ∞` limit of BCIKS20's `α = √ρ·(1 + 1/2m)`; the
  paper's actual bound (eprint 2020/654, Lemma 8.2 / Thm 8.3, printed pp. 40–41) is

  ```
  ε_FRI = ε_C + α^s ,   α = √ρ·(1 + 1/2m) ,   m ≥ 3
  ε_C   = (m+½)⁷·|D⁽⁰⁾|² / (2ρ^{3/2}|F|)  +  (2m+1)(|D⁽⁰⁾|+1)/√ρ · (Σᵢ l⁽ⁱ⁾)/|F|
  ```

  The dropped commit-phase term `ε_C` is now MECHANIZED as
  `Dregg2.Circuit.FriLedger.friCommitLedger`, and at the deployed wrap **it binds** — see §1c.
- **Per-fold, structure-specific (~112.6 at arity 2, `109` at the deployed arity 8):** for the
  **dim-2 constant-fold recursion code** the per-fold proximity error is the FIELD-INDEPENDENT
  counting bound `|Good| ≤ C(64,2) = 2016` over the deployed quartic-extension challenge field
  `F = BabyBear⁴` (`|F| ≈ 2^123.6`), giving `2016/|F| < 2⁻¹¹²` — i.e. **~112.6 bits**
  (`wrap_perFold_soundness_capacity`, `FriCorrelatedAgreementSharp.lean` §8). Kambiré's
  construction does not reach it (his `n^C` blow-up needs `n → ∞`, `r > 2`; at our fixed
  dimension-`2` code it caps at exactly `C(n,2)`) — but the column stands on the counting
  argument, not on that escape. ⚑ **It is a claim about 96.9%-far words, not about the radius FRI
  operates at** — see §1c.
- **All are additionally capped** by `min(·, ~124)` — the degree-4 BabyBear challenge
  extension `2^124` (`circuit/src/plonky3_prover.rs:63`, `type EF = BinomialExtensionField<BabyBear,4>`;
  comment `:113`) — and by the Poseidon2 commitment hash. The ~112.6 per-fold figure already lives
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
  The `M = 1` fiber bound this count carries as the hypothesis `hΦ` is DISCHARGED at every shipped
  config (see the `FriArityFiberDischarge` table above) — but only at `96.9%` farness (§1c).
- **`log_final_poly_len` does NOT enter the soundness formula** and remains inert (an early-stop
  knob, ~-3% at 2⁴, marginal). Arity `8` remains measured-optimal on COST (dropping to arity 2
  costs **+9%** size — PROOF-ECONOMICS §1) — that trade is now priced at `2.807` bits, and moving
  it is ember's call, not this map's.

### 1c. The two things the columns above do not say

**(i) `ε_C` — the term the Johnson column drops, and the CEILING it imposes.** BCIKS20 Thm 8.3's
bound is `ε_FRI = ε_C + α^s`, and `num_queries·log_blowup/2` is only the `α^s` half at `m → ∞`.
`Dregg2.Circuit.FriLedger.friCommitLedger` now computes `ε_C` as a real parametric column:

| config | `\|D⁽⁰⁾\|` | `m` | `commitBits` (`−log₂ ε_C`) |
|---|---:|---:|---:|
| deployed wrap `(lb=6, q=19, pow=16, arity 8, extDeg 4)` | `2^12` | 7 | **71** |
| same config, larger trace | `2^20` | 7 | **55** |
| same config, at the `ε_C`-optimal `m` | `2^12` | 3 | **78** |
| **`q = 200`, `pow = 27`, otherwise deployed** | `2^12` | 7 | **71** — *unchanged* |

Three facts follow, and they are the shape of the whole section:

* **`ε_C` is NOT trace-invariant.** It falls ~2 bits per trace doubling, because `ε_C ∝ |D⁽⁰⁾|²/|F|`.
  The trace height is not an FRI knob at all. dregg's measured grid is a `2^6`-row trace
  (`|D⁽⁰⁾| = 2^12`), smaller than a production turn; nobody has measured the deployed trace-height
  distribution, so the honest number for a real turn is whatever `logD0` that turn has.
* **`ε_C` contains no `num_queries` and no `query_pow_bits`, so no query or query-PoW bump can pass
  it.** `q=200` and `pow=27` prove exactly what `q=19`/`pow=16` proves on this column. This is the
  ceiling, and it is now mechanized — ⚠ **but only at `commit_proof_of_work_bits = 0`.** plonky3
  carries a SECOND, commit-phase PoW knob (`fri/src/config.rs:18`, distinct from
  `query_proof_of_work_bits` at `:20`), ground per fold round immediately before the batching
  challenge `beta` (`fri/src/prover.rs:224`) and omitted from its own `conjectured_soundness_bits`
  (`config.rs:42-44`). It grinds against exactly the terms `ε_C` bounds. **Every dregg config sets
  it to `0`**, so the ceiling holds as stated for what ships — but it is not an absolute ceiling,
  and the knob is unpriced (`FRI-BOTH-WIN-LEVERS.md` §4.4 reports ~+5.5 bits at `lb=7`, unverified
  here).
* **Composing the columns as ethSTARK eq. (20) does** — `λ ≥ min{−log₂ ε_C, ζ − s·log₂ α} − 1` —
  the deployed wrap reads **~70**, not `73`. Maximized over `m ≥ 3` with `(q, pow)` unbounded, the
  ext-degree-4 ceiling is **~77.98** (attained at `m = 3`, where `ε_C` binds at `−log₂ ε_C ≈ 78.98`).

**The only lever that moves that ceiling is the extension degree**, worth exactly `log₂ p = 30.91`
bits per degree, because `ε_C ∝ 1/|F| = 1/p^extDeg`. See FRONTIER B below.

**(ii) The per-fold column is a claim about 96.9%-far words, not the operating radius.**
(`Dregg2/Circuit/FriJohnsonRadiusGap.lean`.) The `hΦ` discharge fires only for words
`dOut ≥ |L| − 2·arity`-far — `496` of `512` = **96.9%** at the deployed wrap. FRI's proven argument
runs at the **Johnson radius** `1 − √ρ` = **87.5%** (`dOut = 448`). `M = 1` is **FALSE** in the band
`[448, 496)`: `deployed_M1_false_at_johnson` exhibits a `448`-far word with a non-injective phase
map, and `deployed_discharge_threshold_tight` shows `496` cannot be weakened by even one. So the
`109` is TRUE and NON-VACUOUS about `96.9%`-far words and does **not** cover the operating regime.
At the Johnson radius the fiber bound is `M ≤ 7` and the honest count is
`arity8_johnson_good_card_le`'s `3528` ⟹ **~111 bits** — HIGHER only because it is a **WEAKER**
claim (it bounds the `dIn = 56` challenge family, not the far larger `dIn = 62` one). Different
objects; neither dominates. Wherever this document quotes `109` / `~112.6` / `118`, read it under
this caveat.

Deployed reads, each labeled with its column: capacity (refuted) `6·19+16 = 130`; Johnson QUERY
column `6·19//2+16 = 73`; commit-phase `ε_C` **`71`** at `|D⁽⁰⁾| = 2^12`; ethSTARK eq. (20)
composite of the two **~70**; per-fold **`109`** at the deployed arity 8 (the `~112.6` is arity 2),
at `96.9%` farness. Effective field cap `~124`, but `ε_C` binds first — the ext-degree-4 ceiling is
**~77.98**.

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

### FRONTIER B — WITHDRAWN at ext-degree 4; the ceiling is ~77.98, and the lever is the FIELD

**⚑ WITHDRAWN (2026-07-15).** This section carried a table — `(lb=7, q=32)` and `(lb=8, q=28)` at
"240 / 128" — headed *"FRONTIER B — PROVEN (Johnson) ledger, target 128"*, and the claim that
buying queries reaches a proven 128. **At the deployed ext-degree 4 that is FALSE at any `q`.**
Those rows are correct arithmetic for the **Johnson QUERY column** (`7·32/2 + 16 = 128`) and that
column is not the soundness. BCIKS20 Thm 8.3's bound is `ε_FRI = ε_C + α^s`, and `ε_C` contains
**no `num_queries` and no `query_pow_bits`** — so queries cannot pass it. Composing as ethSTARK
eq. (20) does, the ext-degree-4 ceiling over all `(q, pow)` and all `m ≥ 3` is **~77.98** at
`|D⁽⁰⁾| = 2^12` (§1c). `q = 200` proves what `q = 25` proves. The withdrawn table described a target
the configuration cannot reach. (⚠ The ceiling assumes `commit_proof_of_work_bits = 0`, where every
shipped config sits — §1c.)

**The real lever is the extension degree**, worth exactly `log₂ p = 30.91` bits per degree
(`ε_C ∝ 1/|F| = 1/p^extDeg`). (A second, unpriced lever exists: plonky3's commit-phase PoW, `0` in
every shipped config — §1c.) The eq. (20) ceiling, `(q, pow)` unbounded, `|D⁽⁰⁾| = 2^12`:

| extDeg | ceiling | plonky3 support (pinned rev `82cfad73`) |
|---:|---:|---|
| 4 (**deployed**) | **~77.98** | supported |
| 5 | **~108.88** | supported, but `EXT_TWO_ADICITY = 27` (vs `30` at degree 8) |
| 6 | ~139.79 | **PANICS** — `monty-31/src/extension.rs` `binomial_mul` matches `4 / 5 / 8` only |
| 8 | **~201.60** | supported, `EXT_TWO_ADICITY = 30` |

So: **degree 5 does not reach 128** (~108.88 is its ceiling at any `q`). Degree 6 would (~139.79)
but plonky3 panics on it. **Degree 8 reaches it** — and is preferable to 5 on two-adicity anyway.

⚑ **The field alone is not enough — both columns must move.** At the deployed `(6, 19, pow=16)`,
raising the extension degree moves eq. (20) only `70.11 → 71.95`, because the QUERY column then
binds. Reaching a composite 128 needs the bigger field **and** more queries. At **ext-degree 8,
pow=16, `|D⁽⁰⁾| = 2^12`** (each row the fewest queries whose eq. (20) composite clears 128):

| lb | q | proof | eq. (20) composite |
|---:|---:|---:|---:|
| 6 | 38 | 220.7 KiB | 128.89 |
| 7 | 33 | 202.0 KiB | 130.41 |
| 8 | 29 | 186.7 KiB | 130.92 |
| 10 | 23 | 163.0 KiB | 129.94 |

That is roughly **double the deployed proof size** (120.4 KiB), on top of a degree-8 extension whose
arithmetic cost this map has not measured. ⚠ And the whole table is pinned to the `2^12` fixture:
`ε_C` falls **~2 bits per trace doubling**, so a production-height trace moves every row. Nobody has
measured the deployed trace-height distribution.

**The unexploited path.** **BCHKS25** (ECCC Report TR25-169; Ben-Sasson, Carmon, Haböck, Kopparty,
Saraf, *On Proximity Gaps for Reed–Solomon Codes*, November 7, 2025) improves exactly the factor that
makes `ε_C` bind. Its abstract, verbatim: *"For proximity gaps up to the Johnson radius `J(δ)`, we
show that proximity loss `ε* = 0` can be achieved with only `O(n)` exceptional `z`'s (improving the
previous bound of `O(n²)` exceptions)."* That `O(n²) → O(n)` attacks the `|D⁽⁰⁾|²` in `ε_C`'s first
term. ⚠ **It backs no number quoted here.** BCHKS25 does not restate a full FRI soundness theorem —
it defers to the existing analyses — and nobody has instantiated it at our configs or computed the
ceiling it would give. It is a named, open lever, not a citation that rescues a figure. The numbers
in this document are BCIKS20's, mechanized in `Dregg2.Circuit.FriLedger`.

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

### The security posture, column by column

The "capacity" ledger (130 at deployed) rests on the FRI capacity conjecture (per-query proximity to
`1−ρ`), and that conjecture is **REFUTED** (Crites–Stewart eprint 2025/2046, by reduction; Kambiré
arXiv 2604.09724, a prime-field counterexample) — so 130 is **not** a security number, only a
knob-drift margin the budget gate holds `≥ 128` on. The columns that are not refuted:

- **the Johnson QUERY column: `73`** at the deployed config, for any code. It is the `m → ∞`
  idealisation of BCIKS20's `α` and DROPS `ε_C` (§1a). Not a soundness headline.
- **the commit-phase column `ε_C`: `71`** at the deployed wrap at `|D⁽⁰⁾| = 2^12`, mechanized as
  `FriLedger.friCommitLedger` from BCIKS20 Lemma 8.2 / Thm 8.3. It BINDS, it is not trace-invariant
  (~2 bits per trace doubling), and no `q` or `pow` bump moves it (§1c).
- **the composite** the two admit under ethSTARK eq. (20), `min{−log₂ ε_C, ζ − s·log₂ α} − 1`:
  **~70** at the deployed wrap and the `2^12` fixture.
- **the per-fold column: `109`** at the deployed arity 8 (`~112.6` is the arity-2 figure) — a claim
  about **96.9%-far** words, not about the Johnson radius FRI operates at (§1c). At the Johnson
  radius the honest count is `3528` ⟹ **~111**, higher only because it is a weaker claim. The
  columns are independent (`query_ledger_does_not_determine_perFold`); never multiply them.

⚑ The per-fold and query columns are **separate**. There is no single headline number for this
system, and assembling one would mean inventing it.

### The field cap, and what lifting it would buy

The degree-4 challenge extension (`|F| ≈ 2^123.6`) caps every column, but `ε_C` binds well below it:
the eq. (20) ceiling at degree 4 is **~77.98**, not ~124. The extension degree is the only knob that
moves that ceiling, at `log₂ p = 30.91` bits per degree — degree 5 reaches ~108.88 (still short of
128), degree 8 reaches ~201.60, and plonky3 PANICS on degree 6 (FRONTIER B). Against the field cap
rather than the 128 knob-margin, `(6, 18)` is arithmetically 1 query / ~5 KiB leaner — a deliberate,
named decision, not this map's call.

### Levers, ranked

- **Extension degree is the only lever on the CEILING** — `log₂ p = 30.91` bits per degree, because
  `ε_C ∝ 1/|F| = 1/p^extDeg`. It is also the only one that is not a trade against proof size. plonky3
  supports 4 / 5 / 8 and panics on 6; degree 8 is preferable to 5 (`EXT_TWO_ADICITY` 30 vs 27), and
  degree 5 does not reach 128 at any `q`. Cost unmeasured. (FRONTIER B.)
- **Query-PoW and queries buy the QUERY column only — they cannot pass `ε_C`.** Each query-PoW bit
  adds directly to both query ledgers for ~zero wire cost (one witness) and a one-time `2^pow`-hash
  prover grind. Raising `pow` 16→20 lets q drop 19→18 at lb=6 (capacity margin stays ≥128), shaving
  ~5 KiB. But `ε_C` contains neither knob: at ext-degree 4 the eq. (20) composite saturates at
  ~77.98 no matter how many queries are bought. (No bump is planned.)
- **Commit-phase PoW — a real knob this map does not price, `0` in every shipped config.** plonky3's
  `commit_proof_of_work_bits` (`fri/src/config.rs:18`) grinds per fold round against the terms `ε_C`
  bounds, and is the one knob that could move the ceiling without touching the field. Nobody has
  priced it here.
- **Blowup** is the main size lever (nearly free to the prover until the LDE dominates ~lb≥7).
- **Trace height is a lever nobody is pulling, in the wrong direction** — `ε_C ∝ |D⁽⁰⁾|²`, so the
  posture falls ~2 bits per trace doubling. It is not an FRI knob and it is unmeasured in
  production.
- **Arity / final-poly** — pinned-optimal on cost; arity IS a per-fold security lever worth
  `log₂ 7 ≈ 2.807` bits (§1a), final-poly enters no formula.

### Where the bits come from (and where they do NOT)

The full capacity rate (`lb` bits/query, the `1−ρ` radius) is **not** an available target: the
capacity conjecture is refuted (Crites–Stewart; Kambiré), so no general analysis reaches `lb`
bits/query, and the "73 → 130 proven jump" that an earlier draft of this section imagined is
foreclosed. Nor is a query-bought 128 available — `ε_C` caps the ext-degree-4 composite at ~77.98
regardless of `q` (FRONTIER B). Two different things carry the two columns:

- **The query column** comes from the general Johnson (`√ρ`) analysis: `lb/2` bits/query, **73** at
  deployed, for any code — minus `ε_C`, which the column drops and which binds at **71**, giving an
  eq. (20) composite of **~70** at the `2^12` fixture.
- **The per-fold column** comes from the **structure** of the recursion fold, not a sharper general
  radius: the dim-2 constant-fold code admits a **field-independent counting** bound
  (`|Good| ≤ C(64,2) = 2016`), which over the quartic extension gives **~112.6 bits** at arity 2 and
  **109** at the deployed arity 8, with no config change (`wrap_perFold_soundness_capacity`,
  `FriCorrelatedAgreementSharp.lean` §8; `FriArityTransfer.lean`). The proximity-gap work (interior
  radius `dIn = 52`, list `186`; boundary `dIn = 56`, list `292`; GS-ideal `128` BLOCKED —
  `STARK-SOUNDNESS-CENSUS.md`, `lean-circuit.md:84-92`) is what makes that counting analysis
  rigorous. ⚑ It is a statement about `96.9%`-far words (§1c).
- **The list term is not the lever.** The list-decoding error carries an additive `L/|F|` term, but
  with `|F| ≈ 2^124` and `L` polynomial (`186`/`292`), that is ~`2^-116` of headroom — it barely
  moves the budget; the security lives in `|Good|/|F|`, not in `L`.

The payoff shape, honestly: the per-fold and query columns describe **different objects at different
radii**, and there is no arithmetic that combines them into one figure. The capacity-rate door is
closed by the refutation; the query-bought-128 door is closed by `ε_C`. The one open lever on the
ceiling is the **extension degree** (FRONTIER B), and **BCHKS25** (ECCC TR25-169) is a real but
uninstantiated upgrade path to `ε_C` itself — named, not banked.

---

*Model + grid search: [`fri_param_frontier.py`](./fri_param_frontier.py) — run
`python3 docs/reference/fri_param_frontier.py`. This document and the script change no deployed
parameter; they are the map for choosing a leaner config later.*
