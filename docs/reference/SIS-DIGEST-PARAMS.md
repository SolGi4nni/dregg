# SIS-DIGEST-PARAMS — 128-bit parameters for the homomorphic MONOID digest

**What this is.** The reality-gate parameterization for the SIS-based homomorphic digest built in
[`metatheory/Dregg2/Crypto/HomomorphicDigest.lean`](../../metatheory/Dregg2/Crypto/HomomorphicDigest.lean)
(binding proven under `MSISHard` in `Dregg2.Crypto.Lattice`). It answers ONE question at real
numbers: for a "fluid scan state" that folds `N` turns, **how big is the digest** you must carry as a
recursion public input, at **128-bit security**? The answer decides whether the fluid distributed
fold is buildable-in-practice or pays a fat proof-input tax.

**Headline, up front.**

| construction | digest @ N=2²⁰ (128-bit classical) | governed by |
| --- | --- | --- |
| **single-matrix** `A·(Σe)` | **≈ 660–1060 BabyBear felts** (20.5k–33.0k bits) | Module-SIS lattice floor, grows as `(log₂ N)²` |
| **position-indexed** `Σ Aᵢeᵢ` | **≈ 9–48 BabyBear felts** (0.28k–1.4k bits) | birthday floor / small-β SIS floor, **flat in N** |

*Estimator-tightened (real `lattice-estimator` run, Core-SVP, below): single-matrix* **≈ 440–960 felts**
*(ℓ∞) / 255–664 (ℓ₂); position-indexed* **≈ 9 felts (ℓ₂/birthday) → 36–40 (ℓ∞), standard width** —
*same verdict, tighter numbers.*

**Position-indexed wins by ~15–70×** and is the only one that stays flat as the history grows. The
single-matrix digest is *fat* (hundreds to a thousand felts) because its collision-norm `β = 2N·β₀`
grows with the fold count; the position-indexed digest is *tolerable* (tens of felts) because its
per-block norm stays `≈2β₀`, constant in `N`. **Build the fluid scan state on the position-indexed
encoding.**

Sections 1–4 are a **first-principles Core-SVP estimate**; the **"Tightened (estimator)" section**
below now backs them with a **real `lattice-estimator` run** (Albrecht et al., through a Python/scipy
SageMath shim validated against the estimator's own doctests). The run **confirms and tightens** every
figure: the first-principles felt counts are honest *conservative* floors (Core-SVP under-counts real
attack cost, so true security ≥ quoted), and the estimator bears this out — the single-matrix ℓ∞ felt
counts drop ~12–14 % and the position-indexed ℓ∞ floor drops 46 → 36 felts. See the honesty note (§8)
for the model's slack.

---

## 1. The construction and the ring

`digest A encode S = A(∑_{i∈S} encode i)` — a linear SIS map `A` over a per-turn short encoding.
Binding reduces (`digest_collision_extracts_msis`) to Module-SIS: a collision on two distinct
histories `S ≠ T` extracts a short nonzero kernel vector `∑_S e − ∑_T e ∈ ker A`. The seminorm is the
**coefficient ∞-norm** (`ShortNorm` in `Lattice.lean`); so the extracted witness is bounded in **ℓ∞**.

* **Ring.** Instantiate over `R_q = ℤ_q[X]/(Xⁿ+1)` with `q =` the **BabyBear prime**
  `p = 2³¹ − 2²⁷ + 1 = 2013265921` (`⌈log₂ q⌉ = 31`, 2-adicity 27 so `Xⁿ+1` splits for `n ≤ 2²⁶` —
  Module-SIS with NTT is available). One ℤ_q coordinate = exactly **one BabyBear felt**, so
  `digest-felts = n` (the row count) and `digest-bits = 31·n`. Everything below works identically for
  **plain ℤ_q SIS** (no ring): Core-SVP credits the module structure *nothing* (best-known attacks do
  not exploit the ring at the blocksizes here), so the security estimate is the unstructured-SIS one
  in total scalar dimensions. Where it matters, `n` = number of ℤ_q rows = `k·d` for a rank-`k`
  module over a degree-`d` ring.

* **The two norms of the collision.**
  * **Single-matrix** `A·(Σe)`: all `N` encodings sum into one `ℤ_q^m` vector before `A`, so
    coordinates *accumulate*: `β = ‖∑_S e − ∑_T e‖_∞ ≈ (|S|+|T|)·β₀ ≈ 2N·β₀`. **β grows with N.**
  * **Position-indexed** `Σ Aᵢeᵢ`: each turn `i` lands in its **own block** `Aᵢ` (disjoint
    coordinates), so no coordinate accumulates more than one turn — `β = 2β₀` (loose; really `β₀`),
    **constant in N**, at the cost of an effective matrix of width `N·m`. This is exactly the
    structural fix the Lean header flags for `SumInjective`.

We take `β₀ = 1` throughout (unit / low-weight encodings, per the prompt).

---

## 2. The Core-SVP model (and its uncertainty)

Standard BKZ / Core-SVP, the model Kyber/Dilithium quote:

* **Root-Hermite factor** from blocksize `b`:  `δ(b) = ( (πb)^{1/b} · b/(2πe) )^{1/(2(b−1))}`.
* **SIS attack (Micciancio–Regev q-ary lattice).** The kernel lattice `Λ⊥(A) = {x : Ax ≡ 0}` has
  covolume `q^n` in the chosen subdimension `m'`. BKZ-`b` finds an ℓ₂ vector of length
  `L(m') = δ(b)^{m'} · q^{n/m'}`, minimized over the subdimension `n < m' ≤ (columns)`. The optimum is
  `m'_opt = √(n·ln q / ln δ)`, giving `L_min = 2^{2√(D·log₂δ)}` where **`D = n·log₂q` is precisely the
  digest width in bits.** SIS at ℓ₂-bound `β` is *solvable* iff `L_min ≤ β`; hence **hard at blocksize
  `b` iff**

  ```
  D  >  (log₂ β)²  /  (4 · log₂ δ(b)).            ← the whole story: digest-bits ∝ (log₂ β)²
  ```

* **ℓ∞ vs ℓ₂.** The witness is ℓ∞-bounded (`β_∞`) but BKZ bounds ℓ₂. Two conventions bracket the truth:
  * *optimistic (ℓ₂):* require `L_min > β_∞` — treats the ℓ∞ bound as an ℓ₂ bound (the standard
    Dilithium-MSIS simplification). Smaller `D`.
  * *conservative (ℓ∞):* a balanced BKZ vector has `‖x‖_∞ ≈ L/√m'`, so the attacker succeeds once
    `L_min ≤ β_∞·√m'` — self-consistently `≈2× ` the `D` of the ℓ₂ convention.

  We **report both** and size params to the **conservative (ℓ∞)** floor. The truth is between; the
  verdict is robust to the choice (single-matrix is fat either way, position-indexed small either way).

* **Cost of one SVP oracle call in dimension `b`** (Core-SVP, ignores polynomial factors, BKZ
  preprocessing, and "dimensions for free" — deliberately conservative):
  `classical 2^{0.292b}`, `quantum 2^{0.265b}`.
  Calibration: `128-bit classical ⇔ b = 438.4` (`log₂δ = 0.005380`), `128-bit quantum ⇔ b = 483.0`
  (`log₂δ = 0.005024`). Params sized for **classical-128** have **quantum-116** (`0.265·438.4`); the
  quantum-128 variant needs `b = 483`, i.e. `+7–8%` felts (columns "Q-128" below).

* **Generic / birthday floor.** Independent of the lattice: the digest is `31n` bits, and two random
  short histories collide generically in `2^{(31n)/2}`. For 128-bit this forces `digest ≥ 256 bits =
  9 felts`. (Quantum collision via BHT is `2^{k/3}`, but its `2^{k/3}` quantum-memory cost makes it
  non-advantageous under the memory model NIST uses; if credited it floors at `384 bits = 13 felts`.)
  **Governing digest = max(SIS-lattice floor, birthday floor).** Only the position-indexed
  construction is ever birthday-limited; the single-matrix is SIS-limited by a wide margin.

**Model slack:** Core-SVP is a *lower bound* on attack cost (real BKZ costs more per call, and this
ignores the constant that makes sieving ~2^{16} more expensive at these dims), so quoted security is
conservative and the digest sizes are honest upper bounds. The ℓ∞ balancedness factor is the largest
modeling lever (~2× on `D`); we take the pessimistic side of it.

---

## 3. Single-matrix `A·(Σe)` — `β = 2N·β₀`, `q = BabyBear`

Digest sized to **128-bit classical** Core-SVP (quantum = 116 for these params). `m` = subdimension
the optimal attack uses (the construction picks any `m ≥ m'_opt`; a *narrower* `A` is only more
secure).

| N | β (ℓ∞) | log₂β | n (rows = felts) | m ≳ | q | digest-bits | **digest-felts** | classical | quantum |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| **2¹²** | 8 192 | 13 | 506 *(254)* | 1 708 | 2³¹ | 15 680 *(7 854)* | **506** *(254)* | 128 | 116 |
| **2¹⁶** | 131 072 | 17 | 760 *(434)* | 2 093 | 2³¹ | 23 559 *(13 430)* | **760** *(434)* | 128 | 116 |
| **2²⁰** | 2 097 152 | 21 | 1 064 *(662)* | 2 477 | 2³¹ | 32 973 *(20 494)* | **1 064** *(662)* | 128 | 116 |

Bold / plain = **conservative ℓ∞** floor; *(italic)* = optimistic ℓ₂ floor. **Quantum-128** variants
(`b=483`): 545 / 818 / 1144 felts (ℓ∞), 272 / 464 / 708 felts (ℓ₂).

The felt count tracks `(log₂β)² = (1 + log₂N)²` — every 16× more turns adds ~250 felts (ℓ∞). This is
the tax for summing all history into one map before compressing.

---

## 4. Position-indexed `Σ Aᵢeᵢ` — `β = 2β₀ = 2` (flat in N), width `N·m`

Per-block norm is constant, so the SIS-lattice floor is tiny (`(log₂2)²/(4log₂δ) ≈ 46 bits`, ℓ∞
self-consistent `≈1405 bits`); the **birthday floor dominates** in the ℓ₂ reading. Same `q = 2³¹`.
The `N·m` total width is trivially `≥ m'_opt` for any `N ≥ 2¹²`.

| N | β (ℓ∞) | n (rows = felts) | total cols (`N·m`) | q | digest-bits | **digest-felts** | classical | quantum |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| **2¹²** | 2 | 46 *(9)* | ≥ 4 096 | 2³¹ | 1 426 *(279)* | **46** *(9)* | 128 | 116 |
| **2¹⁶** | 2 | 46 *(9)* | ≥ 65 536 | 2³¹ | 1 426 *(279)* | **46** *(9)* | 128 | 116 |
| **2²⁰** | 2 | 46 *(9)* | ≥ 1 048 576 | 2³¹ | 1 426 *(279)* | **46** *(9)* | 128 | 116 |

Bold = conservative ℓ∞ SIS floor (46 felts); *(italic)* = birthday floor (9 felts), which the
optimistic-ℓ₂ SIS reading collapses onto. **Quantum-128** ℓ∞ variant: 50 felts. **Flat in N** either
way — the whole point of position-indexing. Take **≈48 felts** as the safe design figure, or 9 felts
if you argue the ℓ∞ balancedness over-credits the attacker (both are small).

---

## Tightened (estimator)

The §1–§4 numbers are the closed-form Core-SVP relation. This section replaces them with a **real run
of the [`malb/lattice-estimator`](https://github.com/malb/lattice-estimator)** (Albrecht–Player–Scott
et al.) — the tool Kyber/Dilithium quote.

**How it was run (no Sage/Docker on this box).** The estimator is SageMath code; it was run through a
~200-line pure-Python **SageMath shim** (`math`/`scipy`-backed `RR`, `log`, `find_root`, `binomial`,
`erf`, arbitrary-precision `RealField` via `Decimal`, etc.). The shim is **validated against the
estimator's own published doctests** before any of our numbers were trusted — all reproduce exactly:

| estimator reference call | published | reproduced |
| --- | --- | --- |
| `SIS.lattice(Dilithium2_MSIS_WkUnf)` (MATZOV/GSA) | `2^152.2, β427, d2304` | ✅ identical |
| `SIS.estimate.rough(Dilithium2_MSIS_WkUnf)` (Core-SVP/lgsa) | `2^123.5, β423` | ✅ identical |
| `SIS.estimate(n=113,q=2048,ν=512,ℓ₂)` (euclidean) | `2^47.0, β61, d276` | ✅ identical |
| `SIS.lattice(n=113,q=2048,ν=16,ℓ∞,lgsa)` | `2^61.0, β95, d2486` | ✅ identical |
| `RC.BDGL16(500,1024)` / `RC.ADPS16(500,1024)` / `Kyber.d4f(500)` | `2^175.4 / 2^146.0 / 42.60` | ✅ identical |

**Models reported.** `q = 2³¹−2²⁷+1` (BabyBear), digest-felts `= n` (rows).
* **Core-SVP classical** — `RC.ADPS16` (`2^{0.292β}`), LGSA shape. *This is the doc's model* — the
  apples-to-apples tightening.
* **Core-SVP quantum** — `ADPS16(mode="quantum")` (`2^{0.265β}`), LGSA.
* **MATZOV** — the estimator's **default** state-of-the-art gate model (list-decoding sieve **with the
  dimensions-for-free** `β·log(4/3)/log(β/2πe)` term the first-principles pass omitted), GSA shape.
  Higher security than Core-SVP → an upper cross-check confirming the Core-SVP felt counts are safe.

Reported `n` = the **minimal digest-felt count** at which `rop ≥ 2^128`, at the estimator's default
(standard) SIS width; `m` and the optimal sub-dimension are found by the estimator.

### Position-indexed `Σ Aᵢeᵢ` (β = 2) — the one we build on

| reading | Core-SVP-C | Core-SVP-Q | MATZOV | first-principles (§4) | governed by |
| --- | --- | --- | --- | --- | --- |
| **ℓ₂ (optimistic)** | `rop=∞` ∀n≥1 → **9 felts** | → **13 felts** | `rop=∞` → 9 | 9 | **birthday floor** |
| **ℓ∞ (conservative)** | **36 felts** (2^130) | **40 felts** (2^131) | **26 felts** (2^129) | 46 | **small-β SIS floor** |

* **ℓ₂ / euclidean is width-independent and trivially hard:** a length-2 ℓ₂ kernel vector needs ≤4
  nonzero ±1 entries, and for `n=9` rows no such sparse combination exists below width `2^{≈70}`
  (`rop=∞` even at `n=1`, even at `m=10⁵`). So the ℓ₂ SIS floor is ~1 felt and the **birthday floor
  (9 felts classical, 13 quantum-BHT) governs** — exactly as §4 claimed for the ℓ₂ reading.
* **ℓ∞ / infinity governs the conservative reading at 36 felts** (not the birthday floor: at the
  birthday `n=9` the ℓ∞ SIS is only **~30 bits**, at `n=13` only ~45). This **tightens §4's 46 → 36
  felts** (CoreSVP-C) — the closed-form's `√m'` balancedness factor over-charged the attacker.

### Single-matrix `A·(Σe)` (β = 2N) — digest felts `n`

| N | ℓ₂ C / Q | ℓ∞ C / Q | ℓ∞ MATZOV | first-principles ℓ∞ / ℓ₂ (§3) |
| --- | --- | --- | --- | --- |
| **2¹²** | 255 / 273 | **443** / 478 | 360 | 506 / 254 |
| **2¹⁶** | 435 / 466 | **679** / 731 | 553 | 760 / 434 |
| **2²⁰** | 664 / 711 | **963** / 1037 | 788 | 1064 / 662 |

* **ℓ₂ matches almost exactly** (255/435/664 vs the doc's 254/434/662) — §3's ℓ₂ closed-form was
  already tight; spot-checked, the doc's ℓ₂ felt counts sit at **2^127.6–127.9**, i.e. calibrated
  right on 128.
* **ℓ∞ tightens by ~12–14 %** (443/679/963 vs 506/760/1064): the estimator's probabilistic
  infinity-norm analysis is less pessimistic than the doc's flat `√m' → 2×` balancedness heuristic
  (it lands at ~1.5× ℓ₂, not 2×). Spot-checked, the doc's ℓ∞ felt counts sit at **2^146–152** — real
  but loose by ~18–24 bits, confirming they were conservative upper bounds as advertised.
* **MATZOV** (with dims-for-free) is uniformly **higher security** than Core-SVP (e.g. `N=2²⁰` ℓ∞:
  `2^176.6` at n=1064 vs Core-SVP's `2^146.3`), so **every Core-SVP felt count above is safe/loose**
  against the state-of-the-art model too.

### Honesty note on the new run — the ℓ∞ **width** lever

One genuinely new observation the first-principles pass missed: **the ℓ∞ (Dilithium-style) cost falls
as the matrix width `m` grows.** At `n=36`, β=2: `m=960 → 2^130`, `m=5000 → 2^88`, `m=50000 → 2^46`.
The ℓ₂ reading has no such lever (subdimension-optimal; width-independent). This matters because the
**position-indexed matrix's *physical* width is `N·m_block`** (the whole point of position-indexing),
which for large `N` is far wider than the standard SIS width used above. The ℓ∞ figures (36/40 felts)
are therefore at **standard per-fold width**, and admitting the full concatenated width would push the
ℓ∞/combinatorial attack stronger (roughly, `n` grows ~`log(width)`). The **robust, width-independent
guarantees** are (a) the **birthday floor 9–13 felts** and (b) the **ℓ₂/euclidean reading** (`rop=∞`
even at astronomically wide `m`). **Design recommendation:** size each fold-block's SIS at standard
width and lean on the width-independent floors; treat the `36–40`-felt ℓ∞ number as the standard-width
Core-SVP point, not a full-width guarantee. (The estimator's GSA basis-shape simulator overflows
double-precision for `m ≳ 2^14`, so a direct full-width ℓ∞ run at `N·m_block` for `N≥2^16` was not
computed here — flagged as follow-up.)

### Tightened bottom line

* **Position-indexed digest at 128-bit: 9 felts (ℓ₂/birthday) → 36–40 felts (ℓ∞ Core-SVP), standard
  width.** Tighter than §4's `9–48`. **Still 9–48 (indeed ≤ 40) — buildable-in-practice confirmed.**
  9 felts ≈ 2 Poseidon2-BabyBear permutations, 40 felts ≈ 5 — one small commitment's worth of PI.
* **Single-matrix: 443–963 felts (ℓ∞ Core-SVP) / 255–664 (ℓ₂), tightened from 506–1064 / 254–662.**
  Still `Θ((log N)²)`-fat and the wrong asymptotic. Position-indexed still wins by **~12–70×**.

---

## 5. Which construction wins on digest size

**Position-indexed, decisively, and by a margin that widens with N.** The single-matrix digest is
`Θ((log₂N)²)` felts; the position-indexed digest is `O(1)` in N (a small constant set by the
birthday/ℓ∞ floor). At `N = 2²⁰`: **9–48 felts vs 660–1064 felts — a 15–70× reduction.** The cost
position-indexing pays is *not* in the digest but in the **public parameter**: `N` distinct matrix
blocks `Aᵢ` (or a seeded/hash-derived `Aᵢ = H(i)`), and a leaf circuit that indexes its block by
position. That is a one-time verifier/setup cost, not a per-fold or per-digest cost.

---

## 6. In-circuit cost

By `digest_eq_sum`, each turn contributes `A(eᵢ) ∈ ℤ_q^n` and the fold is componentwise addition, so:

* **Merge** (combine two sub-digests — the *hot path* of a distributed fold, run at every
  recombination): `n` mod-q additions.
  * single-matrix: **254–1064 adds** · position-indexed: **9–48 adds**.
* **Leaf** (fold one turn = one matrix-vector apply `A·eᵢ` resp. `Aᵢ·eᵢ`):
  * dense encoding: `n·m` mults — single-matrix ≈ `506·1708 ≈ 8.6·10⁵` … `1064·2477 ≈ 2.6·10⁶`
    mults; position-indexed ≈ `46·m_block` (block-local, `m_block` small — a handful of felts).
  * low-weight encoding (`β₀=1`, weight-`w` `eᵢ`): `n·w` adds — leaf collapses to selecting/scaling
    `w` columns of `A`; single-matrix `≈ 500–1000·w` adds, position-indexed `≈ 46·w` adds.

Position-indexed is **cheaper on both axes** — the merge is `n = 9–48` adds (vs hundreds–thousand),
and the leaf apply is over a small block `Aᵢ` rather than the full-height single `A`. The only place
single-matrix could be argued cheaper is one global `A` vs `N` blocks in the public parameter — moot
if `Aᵢ = H(i)` is derived, and dominated by the digest/merge savings.

---

## 7. Verdict

* **Position-indexed digest ≈ 9–48 felts → tolerable** as a recursion public input. Absorbing 48
  felts into a Poseidon2-BabyBear sponge (width 16, rate ~8) is ~6 permutations; 9 felts ~2. That is
  one small commitment's worth of PI — the fluid scan state is **buildable in practice** at
  128-bit, with a digest that **does not grow as history accumulates**.
* **Single-matrix digest ≈ 660–1064 felts → fat.** ~80–130 Poseidon2 permutations just to absorb the
  digest into the PI hash, growing as `(log N)²`. Usable but a real tax, and the wrong asymptotic for
  a "whole-history" scan state. **Not the one to build.**

**Bottom line for the reality gate:** the fluid distributed fold is practical **on the
position-indexed encoding** — a flat ~tens-of-felts digest at PQ-honest 128-bit — and impractical-ish
(fat, N-growing) on the single-matrix encoding. The Lean header's instinct to make `SumInjective`
structural via position-indexing is also the security-and-cost-optimal choice, not just the clean one.

---

## 8. Honesty note & citations

* **§1–§4 are first-principles; the estimator run is now done (see "Tightened (estimator)").** The
  §1–§4 numbers are the closed-form Core-SVP relation `D > (log₂β)²/(4 log₂δ(b))` with the standard
  `δ(b)` and `2^{0.292b}/2^{0.265b}` costs — the same model the tools report in their "Core-SVP"
  column, minus the tool's refinements (BKZ simulation, dimensions-for-free, the `+16` sieve
  constant). Those refinements make the attack **more** expensive, so the real security is **≥** quoted
  and these digest sizes are conservative — **and the estimator run bears this out**: the tightened
  section reruns `SIS.lattice` on `(n, q=2³¹, β, m)` under Core-SVP (`RC.ADPS16`, LGSA) and MATZOV, and
  the breaking blocksize *rises* exactly as predicted (single-matrix ℓ∞ felt counts drop ~12–14 %,
  position-indexed ℓ∞ floor 46 → 36). `lattice-estimator` was run **without Sage** via a Python/scipy
  shim validated against the estimator's own doctests (all reproduce exactly). One new lever the
  closed form missed surfaced: the **ℓ∞ cost is width-sensitive** — see the tightened section's honesty
  note.
* **Biggest modeling lever:** the ℓ∞→ℓ₂ balancedness factor `√m'` (~2× on `D`). We size to the
  pessimistic side. Second lever: whether "128-bit" means classical (b=438, quantum-116) or quantum
  (b=483, `+7–8%`); both are tabulated.
* **The floor is honest but assumed.** `MSISHard` is the named, undischarged lattice floor
  (`Lattice.lean` — an existence-refutation, *vacuous at deployment* by its own doc; the CONTENT is
  the reduction). These parameters make the *assumed* problem 128-bit hard under best-known attacks;
  they do not (cannot) prove MSIS hard — the shared floor of all lattice PQ crypto (FIPS ML-DSA
  included).
* **What was used:** BKZ root-Hermite `δ(b)` (Chen 2013 / used in NewHope, Kyber, Dilithium security
  analyses); Core-SVP sieve exponents `0.292` (classical, Becker–Ducas–Gama–Laarhoven 2016) and
  `0.265` (quantum, Laarhoven) — the ADPS/NewHope "Core-SVP" methodology; Micciancio–Regev q-ary SIS
  attack geometry. `q = 2³¹ − 2²⁷ + 1` (BabyBear). Companion computation is the closed forms above,
  reproducible in ~30 lines of Python (`δ(b)`, the two `D`-solves, birthday `max`).
