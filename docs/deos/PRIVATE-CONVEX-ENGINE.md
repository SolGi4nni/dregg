# The Private Convex Engine — an oblivious first-order solver as dregg's private-optimization factory

*Companion to `FHEGG-KERNEL.md`. That doc showed a uniform-price call auction is a **1-step**
homomorphic fold + one crossing. This doc generalizes: a whole suite of intricate financial
products are **convex programs**, and a convex program solved by a **first-order / operator-
splitting** method is exactly the fhEgg shape run **T times** — [a cheap homomorphic-linear step +
one small prox]. The claim under test: **oblivious first-order is the right private-convex engine**,
it is the private-friendliest solver family, and it turns dregg into a factory for private financial
products, not a pile of one-off circuits. SOTA survey (cited full-text + real numbers) · the engine
(stated precisely, mapped to dregg) · the products suite · the novel construction · the honest
frontier. What-is, present tense; every ambitious edge names its grade.*

---

## 0. Six-line summary

1. **Oblivious first-order is the right engine — and the optimization literature already named it.**
   Arjevani–Shamir (ICML'16, arXiv 1605.03529) define an *oblivious* first-order method as one whose
   **step schedule is fixed independent of the data** (only smoothness/strong-convexity side-info).
   That is *identically* the cryptographic obliviousness a private solver needs: **a fixed,
   data-independent number of iterations T, each a fixed-structure step.** The two notions of
   "oblivious" coincide — the private-friendly solvers are exactly the ones optimizers already call
   oblivious.
2. **The step shape is the fhEgg shape.** Every first-order/splitting iteration is `x ← prox( x − τ·(linear
   map with PUBLIC matrix A) )`: a **homomorphic-linear step** (matrix–vector product with a *public*
   A over *committed/encrypted* x — bootstrap-free, the cheap primitive) **+ one small prox/projection**
   (the single bounded nonlinearity — a clamp / soft-threshold / simplex projection = exactly one
   TFHE programmable-bootstrap-class LUT). fhEgg is **T=1** (one fold + one crossing); the convex
   engine is **T-step** (T folds + T crossings). Same algebra, same recursion apex, same "reveal only
   the result."
3. **It beats the alternatives on privacy, decisively.** Secure **simplex** has *data-dependent
   pivots* → must pad to worst-case iteration count → Dreier–Kerschbaum (ePrint 2011/108, full-text)
   estimate **Toft's secure simplex ≈ 7 years for a 282-variable LP**. Secure **interior-point** has an
   oblivious iteration count `O(√n·log 1/ε)` but each step is a **secure linear-system solve**
   (factorization + division — the expensive, comparison-heavy corner). **First-order needs no
   factorization and no division-heavy Newton step** — just matvec + prox — and its iteration count is
   fixed a priori.
4. **The killer certificate — optimality is a LINEAR check.** A convex optimum is certified by a
   **primal-dual pair with small duality gap**; the gap `⟨c,x⟩ − ⟨b,y⟩` (or the saddle gap) is a
   **homomorphic-linear, STARK-cheap functional**. So the engine never proves it *converged* — the T
   iterations are an **untrusted search**, and the **duality gap is the cheap checked certificate**.
   This is *translation validation for convex optimization* — dregg's "untrusted search, checked
   output" pattern (`project-verified-layout-optimizer`) applied to solving.
5. **Which method:** **PDHG / Chambolle–Pock** is the private-friendliest *general* engine — it is
   **matrix-free** (no factorization, only matvec with public A/Aᵀ + two proxes), inherently
   **primal-dual** (native gap certificate), fixed-iteration. **ADMM/OSQP** wins for QP (one *public*
   KKT factorization done in clear, then **division-free** matvec + box-prox). **Mirror descent** wins
   for simplex geometry (Fisher-market / welfare — the prox is an entropic softmax). fhEgg's crossing
   is the degenerate case of all three.
6. **Products + feasibility:** private uniform-price auction (T=1, **already-real**); private
   Markowitz/portfolio QP and Almgren–Chriss optimal execution (**near**, n≈10²); private CFMM optimal
   routing (**near**, small); welfare-max batch auction with concave utilities = a **Fisher-market
   convex program** (the true generalization of fhEgg, **research-medium**); convex lending/liquidation
   + options off the mark (**near**, ride the mark). The bill is **T batched-prox bootstrap-rounds**
   (SIMD-packed): at Zama's `<1 ms` GPU PBS, `T≈100–1000` is **1–1000 s** — minute-cadence-feasible to
   n≈few-thousand, frontier beyond. PQ-additive commitment layer is the same open residual as fhEgg.

**The single biggest insight:** *you never have to prove the solver converged.* Convex duality gives a
**self-certifying witness** — a primal-dual pair whose gap is a **linear functional** — so the private
engine runs a **fixed, oblivious, homomorphic-linear-plus-small-prox iteration** as an *untrusted
search*, and attests optimality with a **cheap linear duality-gap check** that stands entirely on its
own. The expensive, data-dependent, comparison-heavy machinery of exact solvers (simplex pivots,
interior-point Newton solves) — the part that made "private optimization" look impossible — is
**never entered**. Optimization collapses to *iterate-cheaply, certify-linearly*, which is the fhEgg
kernel with the crossing generalized to a prox and the single fold generalized to T folds.

---

## 1. SOTA survey — secure / private convex optimization (cited, with numbers)

### 1.1 The exact-solver line and why it is the wrong shape

The first instinct — "run a real LP/QP solver under MPC/FHE" — lands in the **comparison-and-branch**
corner, and the literature is blunt about the cost.

- **Secure simplex (Toft, FC'09; Li–Atallah; Catrina–de Hoogh, ESORICS'10).** Toft, *Solving Linear
  Programs Using Multiparty Computation* (FC'09) runs a **distributed secure simplex** over
  secret-shared data; Catrina–de Hoogh, *Secure Multiparty Linear Programming Using Fixed-Point
  Arithmetic* (ESORICS'10, LNCS 6345 pp. 134–150) sharpen it with a fixed-point-optimized simplex.
  **The structural problem is intrinsic:** simplex **pivots on a data-dependent rule** and terminates
  after a **data-dependent number of iterations**. Both the *pivot index* and the *iteration count*
  leak private information, so a secure implementation must (a) select the pivot with a full oblivious
  argmax over masked columns (an O(nm) secure-comparison sweep *per pivot*), and (b) **pad the number
  of pivots to the worst case** — which for simplex is *exponential* in the worst case and large in
  practice. The result is catastrophic: **Dreier–Kerschbaum (ePrint 2011/108, read full-text)**
  estimate that a prototype of **Toft's protocol needs ≈ 7 years to solve their 282-variable supply-
  chain LP**, and note supply-chain problems reach millions of variables. Their own fix is to *not*
  solve securely at all — a randomized problem *transformation* handed to a cleartext solver, trading
  quantified leakage for speed. **Verdict: secure simplex is the anti-pattern — data-dependent control
  flow forces worst-case padding, and the per-pivot oblivious argmax is comparison-dominated.**

- **Secure interior-point (IPM).** IPMs are *much* more oblivious in one crucial respect: the iteration
  count is `O(√n · log(1/ε))`, driven by **dimension and target precision — both public** — not by the
  data values. So the *round count* leaks nothing (this is the standard SOTA observation, confirmed
  across the secure-LP literature). **But each iteration is a Newton step = solve a linear system**
  `(AᵀDA)Δ = r` with a data-dependent diagonal `D`, plus a line search. Under MPC/FHE that is a
  **secure matrix factorization/inversion + secure division** — the most expensive dense-linear-algebra
  and the comparison-heavy line search, every iteration. IPM fixes the *leakage* of the round count but
  keeps the *cost* of dense secure linear solves and divisions. Good obliviousness, bad per-step cost.

- **Secure network flow (Aly–Van Vyve, ICISC'14, *Securely Solving Classical Network Flow Problems*).**
  First secure treatment of **shortest path, minimum-mean-cycle, and minimum-cost flow** in general
  MPC (min-cost circulation via minimum-mean-cycle-canceling). Existence proof that oblivious
  network-flow is **poly-time realizable** — the backbone of fhEgg's multilateral-ring frontier
  (`FHEGG-KERNEL.md §3.3`) — but again pays worst-case-padded combinatorial iteration counts.

### 1.2 The first-order line — where privacy gets cheap

The newer and much healthier line runs **first-order methods under encryption**, precisely because a
first-order step is oblivious-by-construction and linear-heavy.

- **Alexandru–Pappas, *Cloud-based Quadratic Optimization with Partially Homomorphic Encryption***
  (arXiv 1809.02267, IEEE TAC 66(5):2357–2364, 2021). Solves a private QP by **projected gradient
  ascent on the Lagrangian dual** under **Paillier** additive HE + light MPC. The gradient step is a
  **matrix–vector product** — Paillier's additive homomorphism does it directly on ciphertexts (the
  cheap primitive) — and the **projection onto the nonnegative orthant** (dual feasibility) is the
  *only* nonlinearity, handled by a small secure comparison. Proven **computationally private**. This
  is the fhEgg decomposition arriving from the optimization side: *linear step is homomorphic-free,
  one small projection is the whole nonlinearity.*
- **Encrypted MPC / control (Schulze Darup et al.; Alexandru et al.).** A large "encrypted model-
  predictive-control" literature reformulates **gradient-projection** solvers to be **comparison-free /
  branching-free**, precisely because conditional branches are the thing HE cannot do. The whole line
  is a working demonstration that *the way to compute optimization under encryption is to remove the
  data-dependent branches* — i.e. use fixed-iteration first-order methods with a small fixed prox.
- **HE gradient descent for QP** (arXiv 2309.01559, CDC). Benchmarks GD / accelerated-GD for QP under
  HE and concludes **CKKS is the only suitable scheme** (BFV/Paillier lack the approximate real
  arithmetic), that **step-size choice is decisive for convergence**, and quantifies the
  depth/accuracy trade-off — the honest feasibility envelope for encrypted iterative solvers.
- **Polynomial-penalty QCQP** (arXiv 2510.17294, CDC'25). Replaces projections/comparisons entirely
  with a **sequence of increasing-degree polynomial penalty functions** that get steep at the feasible
  boundary — so the *entire* solve is **additions and multiplications only**, HE-native, no PBS at all.
  This is the "minimize the nonlinearity" idea taken to its limit (§4): trade the prox's PBS for a
  higher-degree polynomial barrier, keeping everything in the cheap arithmetic layer.
- **Privacy-preserving distributed ADMM (secret-sharing line).** Because ADMM's subproblems are local
  and its coupling step is a **sum**, ADMM is the natural home for private distributed optimization:
  agents secret-share/aggregate local updates each round without revealing objectives. Iteration
  complexity stays at ADMM's `O(1/k)`; the privacy tax is per-round crypto overhead, *not* extra
  iterations (survey line: *Fully Privacy-Preserving Distributed Optimization Based on Secret Sharing*;
  event-triggered private ADMM, IEEE 2022).

### 1.3 The classical machinery — the old papers have the cleanest structure

The engine is built out of 40 years of convex-analysis machinery whose *structure* is exactly what the
homomorphic regime wants. Mine the originals:

| Method | Origin | Per-iteration shape | Rate | Private-friendly because |
|---|---|---|---|---|
| **Proximal point** | Rockafellar 1976 | `x ← prox_{τf}(x)` | — | the prox is the *only* op; everything else is the identity |
| **Douglas–Rachford / splitting** | Lions–Mercier 1979 | two proxes + a reflection | `O(1/k)` | splits a hard prox into two easy ones — each a small LUT |
| **ADMM** | Gabay–Mercier 1976; Boyd et al. 2011 monograph | linear solve (fixed KKT) + prox + dual add | `O(1/k)` | KKT matrix is **constant** (public A) → factor once, iterate division-free |
| **Mirror descent** | Nemirovski–Yudin 1983 | linear step + **Bregman prox** | `O(1/√k)` (nonsmooth) | on the simplex the prox is a **softmax** — one exp-LUT; natural for Fisher/welfare |
| **PDHG / Chambolle–Pock** | Chambolle–Pock 2011 | matvec `Kx`, `Kᵀy` + two proxes + extrapolation | ergodic `O(1/N)` | **matrix-free** — *no* solve, only matvec with public K; **primal-dual** (native gap) |
| **Nesterov acceleration / FISTA** | Nesterov 1983; Beck–Teboulle 2009 | grad/matvec + prox + momentum add | `O(1/√ε)` iters | momentum is a **linear combination** (free); cuts T quadratically |

Two facts jump out. (i) **Every one of these is `linear-map + prox`**, and the prox for the constraint
sets finance actually uses — box `[l,u]` (clamp), L1 (soft-threshold), nonneg orthant (ReLU), the
simplex (softmax/projection), a norm ball (scaling) — is **exactly a TFHE programmable-bootstrap LUT**
(§1.4). (ii) **The engineering realizations are already the private shape.** **OSQP** (Stellato et al.,
*OSQP: an operator splitting solver for QP*, MPC 2020) factors the KKT matrix **once** because it is
**constant across iterations**, then runs **division-free** iterations — a solver *designed* to avoid
per-iteration division and re-factorization, which is *precisely* the FHE constraint. **PDLP**
(Applegate et al., *Practical Large-Scale LP using PDHG*, NeurIPS'21) makes PDHG **matrix-free** and
**competitive with simplex/barrier at scale** on LPs with **millions of variables** — the existence
proof that first-order LP is not a toy, and its **diagonal preconditioning** is a *public* transform of
a *public* A, so under our regime it is **free**.

### 1.4 The homomorphic cost model — linear is free, the prox is the (small) bill

From `FHEGG-KERNEL.md §1.2` plus the FHE-optimization line (numbers current to 2025–26):

| Operation | Scheme | Concrete cost |
|---|---|---|
| Ciphertext **addition** / linear combination (the matvec workhorse) | CKKS / TFHE / Pedersen / Paillier | **linear, no bootstrap — µs** |
| **Matrix–vector** `Ax`, A **public**, x committed/encrypted | CKKS SIMD | packed rotations+adds; **cost = #rotations**, bootstrap-free; depth grows ~linearly in T → bootstrap every few iters |
| **Prox as a LUT** — clamp / ReLU / sign / soft-threshold / box-projection | TFHE PBS | **< 1 ms on GPU**; ~53 ms CPU-2021; cost **exponential in message-precision bits** (keep ≤ 6–8 bits) |
| Simplex/entropic prox (softmax) | TFHE PBS (exp-LUT) + normalize | one PBS-class op + a reciprocal |
| Bootstrap (refresh, needed to extend depth) | CKKS/TFHE | **≥ 50% of total time** in deep iterative work; **189k+ PBS/s on 8×H100** (Zama) |

The whole engine's economy: **the matvec (the O(T·n²) or O(T·nnz) work) is bootstrap-free and
SIMD-packed** (≈ free); **the prox is the only PBS-class work, and it is one bounded nonlinearity per
iteration**, SIMD-batchable across the coordinate vector into **≈ one bootstrap-round per iteration**.
So the bill is `≈ T bootstrap-rounds`, *not* `T·n` — the coordinate dimension rides inside one packed
prox. This is the numerical statement of "homomorphic-linear + small prox."

---

## 2. The private convex engine — stated precisely

> **A private convex solve is a fixed number of homomorphic-linear folds, each crossed by one small
> prox, producing a primal-dual pair whose duality gap — a linear functional — certifies the optimum;
> only the result opens, and a STARK over the fixed iteration trace attests the whole solve.**
>
> — the fhEgg kernel with the single fold generalized to T folds and the single crossing generalized to
> a prox. (fhEgg: "a clearing is the fold of order-increments into an aggregate curve, crossed once.")

### 2.1 The object — a public program over committed data

A **convex program** with **public structure, private data**:

```
   minimize   f(x)                     f convex  (public form: linear cᵀx, or quadratic ½xᵀPx+qᵀx, …)
   subject to A x ≤ b,   x ∈ C         A : PUBLIC matrix (who-can-do-what topology, tick grid, curve)
                                       x, b, (q, diag of P) : PRIVATE, committed/encrypted
```

The split is the load-bearing move and it is *realistic* for finance: **the matrix A is structural**
(the incidence/topology of a clearing ring, the price/tick grid, the linear constraints of a portfolio
mandate, the public curve of a CFMM) — it is **public, a constant**. The **amounts** (`x`, `b`,
objective weights) are **private**. Public A is exactly what makes the matvec a *linear combination of
ciphertexts with public scalars* — the bootstrap-free primitive, identical to fhEgg's fold of
order-increments (there A is the public unary step-encoding; here it is any public constraint matrix).

### 2.2 The operation — T oblivious `[linear + prox]` folds

Fix an accuracy target ε (public) and derive a **fixed** iteration budget `T = T(ε, condition number)`
— data-independent, hence **oblivious in both senses** (§0.1). Iterate the chosen splitting; in PDHG
form (the default, §2.5):

```
   for t = 1 … T   (FIXED, unrolled, straight-line — no data-dependent branch):
       ȳ  ←  y + σ·A x̄                       # homomorphic-linear: matvec with PUBLIC A  (cheap fold)
       y  ←  prox_{σ f*}( ȳ )                 # small prox on the DUAL   (one PBS-class LUT)
       x⁺ ←  x − τ·Aᵀ y                       # homomorphic-linear: matvec with PUBLIC Aᵀ (cheap fold)
       x  ←  prox_{τ g}( x⁺ )                 # small prox on the PRIMAL  (one PBS-class LUT: clamp/box)
       x̄  ←  2x − x_prev                      # extrapolation: a LINEAR combination            (free)
```

Every step is **either** a homomorphic-linear map with a public matrix (matvec + linear combine =
bootstrap-free, the cheap primitive, ⊕ of ciphertexts) **or** one bounded prox (a clamp / soft-
threshold / projection = one LUT, SIMD-batched across the vector = one bootstrap-round). There is **no
factorization, no division-heavy Newton solve, no data-dependent pivot, no branch**. The control flow
is a **constant** — the same T straight-line steps for every input. That is obliviousness *for free*,
by the shape of the method.

The **fold structure is literally fhEgg's**: `x ← ⊕ (public-scalar · committed-vector)` is the
commutative-monoid fold of §2 of `FHEGG-KERNEL.md`, run once per matvec; the prox is the monotone
crossing generalized from "first price where D≥S" (a threshold) to "clamp to the feasible box"
(a projection). fhEgg is this loop with `T=1` and the prox = the single crossing.

### 2.3 The certificate — optimality is a LINEAR check (the crux)

A first-order primal-dual method produces, at step T, a **pair `(x_T, y_T)`**. Convex duality gives a
**self-certifying witness**: for the primal `min cᵀx s.t. Ax≤b, x≥0` and its dual, the **duality gap**

```
   gap(x, y)  =  cᵀx − bᵀy        (with x, y feasible)      →   gap ≥ 0,  gap = 0 ⇔ optimal
```

is a **linear functional of the committed variables**. So the engine does **not** prove it converged.
It exhibits `(x_T, y_T)` and checks three things, **all homomorphic-linear / cheap**:

1. **primal feasibility** `A x_T ≤ b` — linear (matvec vs public A) + one sign-prox batch;
2. **dual feasibility** `Aᵀ y_T ≤ c` (or ≥, per sign) — linear + one sign-prox batch;
3. **small gap** `cᵀx_T − bᵀy_T ≤ ε` — a **single inner product**, a linear functional, `≤ ε` one
   comparison.

If the three hold, `(x_T, y_T)` is a **certified ε-optimal pair** — *regardless of how the iterations
found it*. The T iterations are an **untrusted search**; the gap-plus-feasibility triple is the
**checked certificate**. This is **translation validation for convex optimization** — dregg's
"untrusted search, checked output+refinement" pattern (`project-verified-layout-optimizer`,
`feedback-switch-to-better-approach`) applied to *solving a program*, not laying out a circuit. It is
also why the private engine sidesteps the hardest obligation: convergence proofs are replaced by a
**cheap linear witness check** that stands on its own. (For QP/SOCP the gap is the Wolfe/Lagrangian
dual gap — still a quadratic-then-linear functional, still cheap; the KKT residual `‖∇f + Aᵀy‖ + …`
is the alternative certificate and is equally linear-dominated.)

### 2.4 The proof + the privacy

- **Privacy — no viewer.** Same discipline as fhEgg: the matvecs are homomorphic over committed data
  (nothing decrypted mid-solve); conservation/feasibility is checked **on the commitments**
  (`Σ commit = commit Σ`, `created_value_conservation`). **Only the final `x*` (or only the market
  fact the product needs — a price, a fill vector) opens.** No decryption committee, no computing
  relayer.
- **Proof — a STARK over the fixed iteration trace + the certificate.** Because the solver is a
  **fixed-length, data-independent straight-line program** (T unrolled `[linear + prox]` steps), its
  execution trace is a **bounded, oblivious circuit** — the STARK-friendly shape. The prover shows, in
  one succinct proof: (i) the trace is the **faithful PDHG/ADMM recursion** on the committed inputs and
  public A (each row = one matvec + one prox, `aggregate_sound`-style faithfulness generalized from one
  fold to T); (ii) the emitted `(x_T, y_T)` satisfies the **certificate** of §2.3 (feasibility + gap
  ≤ ε — the cheap linear checks *in-circuit*); (iii) the result **conserves** where conservation applies
  (`exact_clears_iff` / `clearing_conserves_per_asset`). Crucially, **the STARK need not encode a
  convergence argument** — only that a valid certified pair was produced. It rides dregg's existing
  fold-recursion apex (`accumulator.rs`, `joint_turn_aggregation.rs`): T iterations fold into one proof
  exactly as T turns do. **Deterministic re-evaluation** (fhEgg's cheap verifiability, generalized): a
  re-executor re-runs the fixed T-step program on the committed inputs and re-checks the certificate —
  a bounded, oblivious re-computation, not a search.

### 2.5 Which method — PDHG default, ADMM for QP, mirror for the simplex

| Program | Engine | Why it is the private-friendliest here |
|---|---|---|
| **General LP / SOCP / saddle** | **PDHG / Chambolle–Pock** | **matrix-free** (no factorization at all — only matvec `Kx`, `Kᵀy` with public K); **primal-dual** so the gap certificate is native; fixed-iteration; each step *is* `[linear + prox]`. Backed at scale by **PDLP** (millions of vars). |
| **QP (portfolio, execution)** | **ADMM / OSQP** | KKT matrix is **constant** (P, A public-structure) → **factor once in the clear**, then **division-free** matvec + box-prox per iteration; OSQP is *designed* for exactly this no-division iterate. |
| **Simplex-geometry (Fisher market, welfare, allocation to a budget set)** | **Mirror descent (entropic)** | the Bregman prox on the probability simplex is a **softmax** — one exp-LUT + a normalize; the natural geometry for market-equilibrium/welfare problems, cheaper than Euclidean projection. |
| **Uniform-price call auction** | **fhEgg (T=1)** | the degenerate case: one fold, prox = the monotone crossing. Already-real. |

Nesterov/FISTA momentum layers onto any of these — momentum is a *linear combination* (free) and cuts
`T` from `O(1/ε)` to `O(1/√ε)`, i.e. it **reduces the number of bootstrap-rounds quadratically** for
the same accuracy, at zero homomorphic cost. Preconditioning (PDLP's diagonal scaling) is a **public**
transform of **public** A — free under our split — and it is what turns `O(1/ε)` into near-linear
convergence on well-conditioned finance problems.

### 2.6 Mapping to dregg's existing pieces

| Engine component | dregg primitive | file |
|---|---|---|
| homomorphic-linear step (matvec, public A over committed x) | `ValueCommitment` `impl Add/Sub/Neg`; `toBal_mul` (Σ distributes) | `cell-crypto/src/value_commitment.rs`; `metatheory/Market/Clearing.lean` |
| the fold (one matvec = one commutative-monoid fold) | `pool = foldr (·⊗·) 𝟙`; `Accumulator::accumulate` | `metatheory/Market/Clearing.lean`; `circuit-prove/src/accumulator.rs` |
| order-independence of the fold (CRDT) | `pool_as_perm` | `metatheory/Market/Aggregation.lean` |
| the prox / crossing (the bounded nonlinearity) | the monotone crossing `min{p : D(p) ≥ S(p)}` — generalize to clamp/soft-threshold/projection LUT | `metatheory/Market/Clearing.lean` (crossing); circuit prox = new gadget |
| the certificate (feasibility + duality gap, linear) | `exact_clears_iff` (Σ-balance = clearability) generalizes to KKT/gap residual ≤ ε | `metatheory/Market/Clearing.lean` |
| conserve-over-commitments, decrypt nothing | `created_value_conservation`; `shielded_ring_clears` | `Dregg2/Exec/ShieldedValue.lean`; `metatheory/Market/ShieldedClearing.lean` |
| STARK over the T-step trace (the apex) | `joint_turn_aggregation` / `Accumulator::finalize` — T iterations fold like T turns | `circuit-prove/src/joint_turn_aggregation.rs`, `.../accumulator.rs` |
| the T-leg ring solve (existing partial-fill trace) | N-leg variable-cycle + partial-fill-inequality AIR (12/12 teeth) | `circuit-prove/src/shielded_ring_clearing_nleg_air.rs` |
| shielded positions; conserving settlement | shielded pool + stealth; `settle_ring_verified` | `circuit-prove/src/shielded/pool.rs`; `intent/src/verified_settle.rs` |

**The engine is not a new build — it is fhEgg's decomposition, iterated.** `toBal_mul` is the matvec
homomorphism; the crossing is the prox at `T=1`; `exact_clears_iff` is the certificate at `T=1`
(Σ-balance = the duality gap of the exact clearing). The convex engine states that **these three, run
T times with a general prox and a general public A, are the whole of private convex optimization.**

---

## 3. The financial-products suite — convex program + private feasibility per product

Each product is *a convex program*; the engine handles it privately at the stated grade. "Real" =
already the fhEgg base case; "near" = engine applies at n≈10², minute cadence; "research-medium" =
needs the full T-step engine at scale or a richer prox; "frontier" = large-scale / PQ residual.

| Product | The convex program | Prox / nonlinearity | Private-feasibility grade |
|---|---|---|---|
| **Uniform-price call auction** (fhEgg) | `max V s.t. D(p)≥S(p)` — a 1-D crossing (linear-utility Fisher market) | one threshold crossing | **Real** — T=1, already largely proved (`FHEGG-KERNEL.md`). |
| **Portfolio / Markowitz mean-variance** | QP `min ½xᵀΣx − λμᵀx s.t. 𝟙ᵀx=1, x∈box` (Σ, μ private) | box-projection (clamp) + simplex/budget | **Near** — ADMM/OSQP, one public KKT factor, division-free; n≈10²–10³ assets. Matches the private-Markowitz line (Alexandru; hybrid HE+MPC). |
| **Optimal execution / order-splitting** (Almgren–Chriss) | QP `min Σ (impact·vₜ² + risk·xₜ²)` over a public time grid; schedule private | box/nonneg-projection on the schedule | **Near** — small QP over a public horizon; the schedule vector opens, sizes hidden. |
| **CFMM optimal routing / trade** | convex: `max` output `s.t.` public curve invariants (Angeris–Chitra convex-CFMM) over committed amounts | projection onto the (public) reachable set | **Near (small)** — public pool curves, private amounts; oblivious first-order over the convex trade set. |
| **Welfare-max batch auction, concave utilities** | **Fisher-market / Eisenberg–Gale** convex program `max Σ bᵢ log⟨uᵢ,xᵢ⟩ s.t. supply` | **entropic/simplex prox (softmax)** | **Research-medium** — the *true generalization of fhEgg*: uniform-price is the linear-utility special case; general concave utilities are the full convex program via **mirror descent**. Real algebra, scale is the frontier. |
| **Convex lending / liquidation** | convex risk program off the private mark (LTV, health-factor as convex constraints) | box/threshold prox | **Near** — mostly *rides the mark* (fhEgg oracle) + a small convex check; the manipulation-resistant private mark is the whole point (`Market/Lending.lean`). |
| **Options / perps / structured products** | payoff `max(0, mark−K)`, funding off `mark−index`, basket vs price-vector | comparison vs the mark (one prox) | **Near** — settle against the proof-carrying mark; a convex payoff, not a re-solve. (`CONDITIONAL-VAULT.md`, `DERIVATIVE-MATCHING-DESIGN.md`.) |
| **Multilateral ring, partial-fill volume-max** | max-volume **circulation LP** in `ker ∂` (public basis) | box-prox on edge flows | **Research (poly-time)** — now an **oblivious PDHG over the public cycle basis** (§3.3 of fhEgg), *not* secure simplex: fixed-T first-order replaces the padded-pivot LP. This is the engine's sharpest win over the SOTA. |

The unifying statement generalizes fhEgg's "one private mark unlocks a product surface": **one private
convex engine unlocks a product *factory*** — each product is a public program form + a prox + the
duality certificate, and the same oblivious T-step solver + STARK apex serves all of them. Adding a
product is *writing its convex program and its prox*, not building a bespoke private protocol.

---

## 4. The novel construction — verifiable oblivious first-order over PQ-additive commitments

The literature has the pieces separately; **no one has assembled the dregg-shaped whole.** The opening
is real and specific.

**What exists.** First-order under HE (Alexandru–Pappas: projected-dual-gradient under Paillier;
2309.01559: CKKS GD for QP), comparison-free reformulations (encrypted-MPC line; 2510.17294 polynomial-
penalty QCQP), matrix-free first-order LP at scale (PDLP), division-free ADMM QP (OSQP), the "oblivious
first-order" complexity theory (Arjevani–Shamir). Each is a piece.

**What is missing — the dregg construction (`dPDHG`):**

1. **A splitting tuned to the homomorphic budget.** Choose the splitting that **maximizes the
   homomorphic-linear fraction and collapses all proxes into ONE batched bootstrap-round per
   iteration** — i.e. a **single-prox-per-iteration** primal-dual method where the primal prox is a
   packable box/soft-threshold over the whole coordinate vector, and the dual prox is degenerate
   (indicator of a linear set → a matvec, no PBS). PDHG with `f*` an indicator (LP/box-constrained QP)
   already has this shape; the tuning is to *pick the constraint encoding so every prox is one packed
   LUT*. Where a prox would need high precision, swap it for the **polynomial-penalty barrier**
   (2510.17294) and keep it in the free arithmetic layer — a per-problem PBS-vs-degree trade-off.
2. **A fixed oblivious T from a public accuracy target**, with **momentum** (free) to make T small and
   **public preconditioning** (free, A public) to make the problem well-conditioned — so the whole
   solve is a genuinely small, fixed, data-independent circuit.
3. **PQ-lattice-additive commitments as the carrier.** The homomorphic layer is **lattice-additive**
   (CKKS/BGV/Regev-additive) — **already post-quantum**, unlike fhEgg's classical-DLog Pedersen. The
   matvec is a linear combination of lattice ciphertexts/commitments; this closes fhEgg's named PQ
   residual *for the compute layer* in the same stroke (the commitment-binding layer is the shared open
   residual, `PQ-SHIELDED-COMMITMENT.md`).
4. **The STARK-over-the-trace + duality-gap certificate — the genuinely novel part.** The entire
   encrypted-optimization line (Alexandru, control, CKKS-GD) is **semi-honest**: it *computes* under
   encryption but carries **no proof the computation was correct** — you trust the cloud. **dregg adds
   the succinct proof**: because the solve is a fixed straight-line circuit, a STARK attests the trace
   *and* the **linear duality-gap certificate** (§2.3). The result is **verifiable oblivious first-order
   convex optimization over committed inputs, revealing only the certified optimum** — which, as far as
   the surveyed literature shows, **does not yet exist**. The duality-gap certificate is what makes it
   cheap: proving *convergence* in-circuit would be brutal; proving *"here is a primal-dual pair, and
   its gap — a linear functional — is ≤ ε"* is a handful of matvecs and one comparison.

**This is dregg's edge, and it is defensible:** the crypto community has secure solvers (slow, no
proof) and the control community has encrypted first-order (fast-ish, no proof); dregg has the
**recursion/STARK apex and the commitment algebra already built** (fhEgg), so it is uniquely positioned
to ship the *proof-carrying* oblivious first-order engine. The novel object is the marriage:
*first-order's untrusted search + convex duality's linear certificate + dregg's fold-STARK.*

---

## 5. Honest feasibility envelope + the frontier

| Regime | Tractability | Basis |
|---|---|---|
| **Uniform-price auction (T=1)** | **Already-real.** | fhEgg; O(N·K) additions + one crossing. |
| **QP / LP, n≈10², minute cadence** | **Near.** Cost ≈ T batched-prox bootstrap-rounds + free matvec. | ADMM/OSQP or PDHG; T≈100 → ≈ 10²–10³ PBS-rounds; `<1 ms` GPU PBS (Zama) ⇒ **~0.1–1 s** of prox work + matvec. |
| **n≈10³, T≈10³** | **Feasible with SIMD-batched prox; frontier without.** | If the prox packs into one bootstrap-round/iter: **~1 s** (T=10³ × <1 ms). If it degrades to per-coordinate PBS (T·n ≈ 10⁶): **~10³ s** ⇒ too slow at minute cadence. **Packability of the prox is the swing factor.** |
| **Ill-conditioned problems** | **T blows up.** `O(1/ε)` → many bootstrap-rounds. | Mitigate with **public** diagonal preconditioning (free, A public) + momentum (free); well-conditioned finance QPs then converge near-linearly. Honest: pathological conditioning is a real wall. |
| **Exact-vertex optimum** (need the true LP vertex, not ε-close) | **Not the engine's job.** | First-order gives **ε-approximate** optima. Clearing to a **tick / basis point** is fine (fix ε to the tick); a use-case demanding an exact combinatorial vertex wants a different tool. Named plainly. |
| **CKKS depth / precision** | **Named cost.** | Depth ~ T ⇒ bootstrap every few iters (≥50% of time); PBS cost **exponential in precision bits** ⇒ keep ≤6–8-bit fixed-point; step-size choice is decisive (2309.01559). |
| **Multilateral partial-fill volume-max, at scale** | **Research (poly-time).** | Now an **oblivious PDHG over the public cycle basis** — replaces secure-simplex's padded pivots with fixed-T first-order. The engine's sharpest advance over the Toft/Catrina SOTA, but scale is unproven. |
| **PQ commitment binding** | **Shared open residual.** | The *compute* layer is lattice-additive (PQ) already; the *commitment-binding* is the same DLog→lattice cutover as fhEgg (`PQ-SHIELDED-COMMITMENT.md`). |

**Where it genuinely breaks (no spin):** (1) the prox must **SIMD-batch** into ≈ one bootstrap-round
per iteration, or the `T·n` PBS bill sinks minute cadence at n≈10³ — this is the single most important
engineering fact; (2) **ill-conditioning** inflates T past the budget (mitigated by free public
preconditioning, but not eliminated); (3) first-order is **ε-approximate**, wrong for exact-vertex
needs; (4) CKKS **depth/precision** caps how deep before bootstrap dominates; (5) the **PQ-binding**
residual persists. **What does NOT break:** the core claim — a private convex solve is a *fixed,
oblivious, data-independent* sequence of *homomorphic-linear folds + one small prox each*, certified by
a *linear duality-gap witness*, provable by a *STARK over the fixed trace*, revealing *only the
optimum* — with **no factorization, no data-dependent pivot, no worst-case-padded iteration count**, and
therefore **none of the 7-years-for-282-variables pathology of secure simplex.**

---

## 6. Verdict on the hypothesis

**Confirmed, and sharpened.** Oblivious first-order **is** the right private-convex engine:

1. **The two obliviousnesses coincide.** The optimizer's "oblivious first-order" (fixed data-
   independent step schedule, Arjevani–Shamir) *is* the cryptographer's obliviousness (fixed
   data-independent control flow). The private-friendly solvers are exactly the ones optimizers already
   call oblivious — you do not fight the algorithm to make it private; you pick the algorithm that is
   private by construction.
2. **The step is the fhEgg shape, generalized.** `linear-map-with-public-A (cheap homomorphic fold) +
   one small prox (bounded nonlinearity)` — T times. fhEgg is T=1; the engine is T-step; same fold
   algebra, same recursion apex, same reveal-only-the-result.
3. **The certificate makes it cheap and the proof clean.** Convex duality yields a **linear** optimality
   witness, so the solver is an *untrusted search* checked by a *cheap linear certificate* — translation
   validation for optimization — and the STARK attests a *fixed straight-line trace*, never a
   convergence argument.
4. **Which method:** **PDHG/Chambolle–Pock** general (matrix-free, primal-dual), **ADMM/OSQP** for QP
   (public one-time factor, division-free), **mirror descent** for simplex/welfare (softmax prox). All
   degenerate to fhEgg's crossing.

**Is there a better engine?** No cleaner one surfaced. Secure **simplex** is the anti-pattern (data-
dependent pivots → 7-years/282-vars). Secure **interior-point** fixes the round-count leak but keeps
per-iteration secure linear solves + division (expensive, comparison-heavy). General **FHE of an exact
solver** inherits the branch/comparison problem the whole first-order line exists to avoid. **Oblivious
first-order + duality-gap certificate + STARK-over-the-trace** is the decomposition that (a) puts the
work in the cheap half of the crypto (matvec free, one small prox), (b) shares dregg's fold-recursion
algebra so it composes into the existing apex and settlement layers, and (c) turns dregg into a
**factory** — a product is a convex program + a prox, not a bespoke protocol. **The novel opening:** the
*verifiable* oblivious first-order solve over *PQ-additive* commitments — encrypted-optimization has
the compute, dregg has the proof; nobody has yet shipped both. That is the private convex engine.

---

## 7. Sources

**IACR ePrint (read full-text from the local mirror):**
- Dreier & Kerschbaum, *Practical Secure and Efficient Multiparty Linear Programming Based on Problem
  Transformation*, ePrint **2011/108** — **estimate: Toft's secure simplex ≈ 7 years for a 282-variable
  LP**; surveys Toft, Li–Atallah, Catrina–de Hoogh secure-LP solvers; motivates transformation over
  secure solving.

**Optimization literature (classical machinery — the clean structure):**
- Rockafellar, *Monotone operators and the proximal point algorithm* (1976). Lions & Mercier,
  *Splitting algorithms* (Douglas–Rachford, 1979). Gabay–Mercier / Boyd et al., *Distributed
  Optimization and Statistical Learning via ADMM* (FnT ML, 2011) — ADMM `O(1/k)`.
- Nemirovski & Yudin, *Problem Complexity and Method Efficiency in Optimization* (1983, mirror descent).
  Nesterov (1983) / Beck–Teboulle FISTA (2009) — accelerated `O(1/√ε)`.
- Chambolle & Pock, *A first-order primal-dual algorithm for convex problems* (JMIV 2011) — PDHG,
  ergodic `O(1/N)`, matrix-free, primal-dual.
- Arjevani & Shamir, *On the Iteration Complexity of Oblivious First-Order Optimization Algorithms*
  (ICML'16, arXiv **1605.03529**) — defines *oblivious* = data-independent step schedule; `Ω(√L/ε)`.
- Stellato et al., *OSQP: An Operator Splitting Solver for Quadratic Programs* (Math. Prog. Comp. 2020)
  — constant KKT factored once, **division-free** iterations. Applegate et al., *Practical Large-Scale
  LP using PDHG* / **PDLP** (NeurIPS'21, Math. Prog. Comp. 2026) — matrix-free, restarts, competitive
  with simplex/barrier at **millions of variables**.

**Secure / encrypted optimization (the SOTA line):**
- Toft, *Solving Linear Programs Using Multiparty Computation* (FC'09) — secure simplex, padded pivots.
- Catrina & de Hoogh, *Secure Multiparty Linear Programming Using Fixed-Point Arithmetic* (ESORICS'10,
  LNCS 6345:134–150) — fixed-point secure simplex.
- Aly & Van Vyve, *Securely Solving Classical Network Flow Problems* (ICISC'14) — secure shortest-path /
  min-mean-cycle / min-cost flow.
- Alexandru & Pappas, *Cloud-based Quadratic Optimization with Partially Homomorphic Encryption*
  (arXiv **1809.02267**, IEEE TAC 66(5):2357–2364, 2021) — **projected-dual-gradient under Paillier**,
  one projection is the only nonlinearity, computationally private.
- *Homomorphically encrypted gradient descent algorithms for quadratic programming* (arXiv **2309.01559**,
  CDC) — CKKS is the only suitable scheme; step-size decisive; depth/accuracy trade-off.
- *A polynomial-based QCQP solver for encrypted optimization* (arXiv **2510.17294**, CDC'25) — replace
  projections with increasing-degree **polynomial penalty** functions; add/mult only, no PBS.
- Encrypted MPC / control (Schulze Darup et al.) — comparison-free / branching-free gradient projection.
- Privacy-preserving distributed ADMM (secret-sharing line): *Fully Privacy-Preserving Distributed
  Optimization Based on Secret Sharing*; *Privacy-Preserving Distributed ADMM with Event-Triggered
  Communication* (IEEE 2022).

**FHE cost model:**
- Zama TFHE / fhEVM: ciphertext addition ≈ µs (no bootstrap); **PBS < 1 ms on GPU**, ~53 ms CPU-2021;
  **189k+ PBS/s on 8×H100**; PBS cost exponential in message-precision bits (Zama TFHE deep-dive;
  *Improved Programmable Bootstrapping*, ePrint 2021/729). Bootstrap ≈ 50%+ of deep-iterative time.

**Products / convex-finance:**
- Angeris & Chitra et al. — convex analysis of CFMMs / optimal routing as a convex program.
- Almgren & Chriss — optimal execution QP. Markowitz — mean-variance QP. Eisenberg–Gale / Fisher-market
  convex program for welfare-max with concave utilities (uniform-price = linear-utility special case).

**dregg (this repo) — the engine is fhEgg's decomposition, iterated:**
- `docs/deos/FHEGG-KERNEL.md` — the T=1 base case (fold + crossing + certificate).
- `metatheory/Market/Clearing.lean` — `toBal_mul` (matvec homomorphism), the crossing (prox@T=1),
  `exact_clears_iff` (certificate@T=1). `metatheory/Market/Aggregation.lean` — `pool_as_perm`,
  `aggregate_sound`. `metatheory/Market/ShieldedClearing.lean` — `shielded_ring_clears`.
- `Dregg2/Exec/ShieldedValue.lean` — `created_value_conservation` (conserve on commitments).
- `cell-crypto/src/value_commitment.rs` — the homomorphic 𝔸. `circuit-prove/src/accumulator.rs`,
  `.../joint_turn_aggregation.rs` — the STARK-over-the-fold apex (T iterations fold like T turns).
- `circuit-prove/src/shielded_ring_clearing_nleg_air.rs` — N-leg partial-fill trace (the ring solve).
- `docs/deos/DREX-DESIGN.md`, `PQ-SHIELDED-COMMITMENT.md`, `project-verified-layout-optimizer` (memory)
  — the exchange, the PQ-binding residual, and the translation-validation pattern the certificate reuses.
