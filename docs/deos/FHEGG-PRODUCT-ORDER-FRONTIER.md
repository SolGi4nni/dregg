# fhEgg — The Product & Order-Type Frontier (Codex Round 2, Captured + Assessed)

*Second codex-exec round (GPT-5.6-sol), fed the mathematical brief + the round-1 insights and asked to
map the **derivatives, order-type, and product surface** the two-level fhEgg architecture unlocks —
under the design constraint "powerful enough for rich derivatives, yet extremely efficient (cheap
certificate, small fixed-`T` oblivious finder, few/no bootstraps, static memory, PQ)." Captured and
**honestly assessed** by R2.1–R2.4. Companion to `FHEGG-MATHEMATICAL-BRIEF.md` and
`FHEGG-CODEX-INSIGHTS.md`. Run: `codex exec --sandbox read-only`, codex-cli 0.144.1, 220,694 tokens;
full log `scratchpad/codex-round2.log` (answer block ~L6014–6878).*

**The architecture under test (codex's own round-1 crystallization):** a two-level system — (1) a
*replaceable, hidden* witness-finder (histogram/crossing for auctions; incidence-preconditioned
fixed-`T` PDHG for fractional circulation) + (2) a *small* primal–dual / Fenchel-gap **certificate**
that attests feasibility + fairness + conservation + optimality **without proving the solver's
iterations**, over PQ hash/STARK commitments with an optional lattice ingress.

---

## Headline (the single most valuable round-2 output)

**`fhIR` — a typed order/product language that is co-extensive with the cheap regime, plus a six-part
admissibility theorem: "admissible iff it compiles / passes the resource manifest."** Codex answered
the real prize question (R2.3) by *constructing the language*: three orthogonally-typed fragments
(`visibility ∈ {public, committed, opened-result}` × `curvature ∈ {affine, convex, concave,
discrete}` × `phase ∈ {payoff, price, clear, settle}`), an explicit grammar for
affine/convex/constraint/trigger/order/program, an **explicit reject-list** (private-matrix × secret
variable; secret × secret except certificate atoms; binary decision inside optimizer;
complementarity `x·y=0`; arbitrary disjunction; secret-indexed memory; unbounded trigger recursion;
large PSD / exp-cone without an approved prox), and a compiler
`compile(P) = (A, P, 𝒦, triggers, bounds, leakage-manifest)`. The admissibility theorem has six
parts: **(1) semantic preservation** (`Eval_fhIR(P,w)=o ⟺ ConicRel(compile(P),w,o)`); **(2)
certificate soundness** (verify primal-feas + dual-feas + gap ≤ ε ⇒ feasible, conserving, fair,
ε-optimal, *regardless of how found*); **(3) cost bound** — finder `O(T(nnz A + nnz P + n))` +
`T·Σ proxCost(K_j) + k·cmpCost`, **certificate `O(nnz A + nnz P + dim 𝒦)`, independent of `T`**; **(4)
conditional completeness** (given public radius/conditioning/error bounds and sufficient `T`, the
finder yields an acceptable certificate — but *soundness must not depend on this*: if the finder fails
the gap, the batch simply has no accepted result); **(5) exact-arithmetic/no-wrap** (static interval
analysis bounds every scaled intermediate; residue equality is not integer equality — range witnesses
mandatory); **(6) leakage refinement** (`View(P,w) ≈ Sim(Leak(P,w))` under named hiding/PCS-ZK floors,
the manifest listing only dimensions, public topology, `T`, precision, chosen result, deliberately-
public facts).

**Assessment — GOLD, and the deepest structural contribution of the two rounds.** This is exactly the
"single proof-carrying valuation/order LANGUAGE co-extensive with the cheap regime" the question
posed, delivered as an actual grammar + typed judgement + a theorem *shape* that decomposes cleanly
onto our existing floors (2 = the `Cert-F` soundness of round 1; 5 = our `VALUE_BITS`/`Bignum`
no-wrap keystones; 6 = the Component-3 reveal-nothing crux stated with a leakage functor). Two moves
make it more than a wish-list: **(i)** soundness is decoupled from completeness (a failed solve
produces *no result*, never an unsound one — this is the correct security posture and matches dregg's
verify-not-find DNA), and **(ii)** the honest refusal of a representation-independent maximal language
("equivalent convex functions can have radically different prox costs; maximality should be relative
to a declared `ProxLib` and cost budget"). That caveat is *correct and important* — it means the
"admissible iff compiles" theorem is **syntactic/resource-relative**, which is the only version that
can actually be proved. This is a directly buildable spec for a dregg DSL, and it is the natural
home for the `Market/*.lean` tower to grow into. **Build this.**

---

## R2.1 — Derivatives

**The unifying object codex proposed: `Price-Cert`, a state-price LP with superhedging dual.** Over a
public scenario grid/tree `Ω`, calibrated-instrument payoffs `H ∈ ℚ^{M×J}` with observed marks
`a ∈ ℚ^J`, and a new product's scenario payoff `h ∈ ℚ^M`, the no-arbitrage upper price is
`p̄ = max_{π≥0} hᵀπ s.t. Hᵀπ = a`, with superhedging dual `p̄ = min_y aᵀy s.t. Hy ≥ h`. The complete
certificate is `π≥0, Hᵀπ=a, Hy≥h, 0 ≤ aᵀy − hᵀπ ≤ ε`. State prices and hedges stay hidden; only a ZK
proof + the resulting bound (or interval) are public. Crucially, codex separates **three phases that
must not be conflated**: *settlement* (evaluate realized payoff — usually very cheap), *pricing*
(choose/bound a state-price measure — sometimes an LP, sometimes a hard oracle), *clearing* (balance
private buy/sell demand — the fhEgg histogram or a portfolio-coupled LP/QP). And the honest floor: *a
proof establishes correct pricing under a committed model; it cannot establish that the model/oracle
is economically correct.*

**Per-product grades (codex's table, condensed):**

| Product | Representation | Grade |
|---|---|---|
| European vanilla / basket / arithmetic Asian | state-price LP; one ReLU at settlement | **Core** |
| Barrier / digital / autocall | LP after finite-state expansion; bounded trigger circuit | **Core if horizon small** (else trigger-heavy) |
| **American / Bermudan** | **Snell-envelope LP** `min V_root s.t. V_n ≥ g_n, V_n ≥ d_n Σ P_nm V_m` + stopping-flow dual | **Polynomial, tree-size-sensitive** |
| Futures | balance LP `Σx_i=0, −c⁻≤x≤c⁺`; affine settlement | **Core** |
| Perps | auction mark + LP/CVaR margin or SOC-light norm margin | **Core / cone-light** |
| Variance swap | `RV = (A/H)Σ(r_t−r̄)²`; rotated-SOC epigraphs | **Core arithmetic** |
| Volatility swap | `√RV` — SOC-representable / bounded lookup | **Small nonlinear extension** |
| `S²` power perp (Squeeth) | one mult / SOC lift | **Cone-light** |
| higher/fractional power perp | exp/log/reciprocal oracle | **Frontier** |
| fixed structured note / tranche | `(L−A)₊−(L−D)₊` PWL waterfall + state-price LP | **Core for fixed templates** |
| endogenous tranche design | DC / MIP / SDP relaxation | **Outside core** |
| quadratic / PWL prediction AMM | QP/LP + Fenchel–Young certificate | **Core** |
| LMSR | `b·log Σ exp(q/b)` — exponential cone | **Extended** |
| plain rate / basis swap | affine cashflows in `(D, Z=DF)` + curve-fit QP | **Core QP** |
| swaptions / multi-curve | scenario/model layer | **Medium/frontier** |

**Assessment.**
- **`Price-Cert` is a genuinely strong unification — real and correctly grounded.** Reducing "price
  any derivative" to a state-price LP with a superhedging dual (cites Barratt–Tuck–Boyd convex
  risk-neutral pricing) is the right object: it is *one* certificate relation for the whole European /
  basket / Asian / barrier / tranche family, it produces an honest *arbitrage-free interval* (not a
  fake unique price), and its primal–dual gap is exactly the round-1 `Cert-F` shape. The three-phase
  settlement/pricing/clearing split is a **correct and clarifying** distinction our brief blurred, and
  the "proof certifies pricing-under-a-committed-model, not model-correctness" caveat is the honest
  floor a lot of ZK-finance hand-waves past.
- **American/Bermudan = Snell-envelope LP is the sharpest single result in R2.1** — and mildly
  counterintuitive (early exercise *feels* like it should be mixed-integer). On a finite tree it is an
  optimal-stopping LP with an occupation/stopping-flow dual, tied to the established Haugh–Kogan /
  Rogers martingale duals. The reframing "**American optionality is not the first expressiveness
  cliff; the scenario representation is**" is correct and strategically important — it says the cost is
  tree size (curse of dimensionality), not solver class. **Verify** the Snell-LP dual is exactly the
  martingale/occupation-measure dual (it is, modulo discounting bookkeeping) before relying on the
  certificate.
- **The barrier/path-dependence treatment is honest and right:** on an enumerated tree the barrier is
  a public state bit (still LP); on a *hidden path* you pay a running-max + `H` trigger comparisons.
  "Not solver-hard at fixed state size; state-size and comparison-budget hard." Correct.
- **The consistent honesty about the awkward nonlinearities** (Black–Scholes normal-CDF/exp/div "is
  not the natural private object"; log for variance/vol; exp/log for LMSR; fractional powers) is
  correct and prevents the classic overreach. The recommended dodges (finite-state LP instead of
  closed-form; committed fixed-point oracle log-returns with provenance; quadratic/PWL market maker
  instead of LMSR) are all sound.
- **Net:** R2.1 is **known convex-finance results (Snell duals, CVaR reformulation, convex risk-neutral
  pricing, cost-function prediction markets) assembled into one certificate discipline** — high
  correctness, high clarifying value, moderate novelty (the novelty is the *uniform certificate
  packaging* + the settlement/pricing/clearing phase separation, not the individual reductions).

---

## R2.2 — The order-type lattice

**Codex's factorization:** `Order = price-rule × fill-domain × activation × linkage × persistence`,
with the uniform shape `0 ≤ x_i ≤ a_i q_i`, `a_i ∈ {0,1}` the activation bit; continuous convex orders
differ only in how `q_i`, the price predicate, and linear link-constraints are formed; combinatorial
orders constrain the *fill itself* to a discrete set. The full classification table grades each type
Linear / Convex / Conditional / Integer with cost — highlights: limit/market/IOC/pegged(lagged)/TWAP/
proportional-link/shared-cap/GTT/GTC/reduce-only = **free**; stop / stop-limit / post-only / trailing-
stop = **one compare layer**; iceberg = **one clamp per refill (hidden full size otherwise free)**;
**AON / FOK / minimum-fill / OCO / if-then = integer, break the continuous regime.**

**The three cheap-regime-preserving encodings (the load-bearing part):**
1. **Lag all mark-dependent activation by one finalized epoch** — stops/post-only/pegs reference
   `p_{t−1}`, never the mark their own activation changes. Kills reflexive books; gives deterministic
   two-phase semantics.
2. **Compile linkage through receipts, not same-batch binaries** — an if-then child is minted only by
   the parent's fill receipt; a bracket entry mints a *guarded exit ticket*, and **both exits share
   one nullifier so only one can settle**. Uses the turn-kernel's sequential state instead of asking
   an LP to solve a disjunction.
3. **Fixed padded slots + cap-zero masking** — every order occupies a static slot; a private trigger
   produces `a_i`, then the finder uses `q_i' = a_i q_i`. No secret-indexed RAM, no branch-dependent
   access; linked topology public or a padded bounded-degree graph.

Plus a sharp honesty tooth: the convex OCO relaxation `x_i/q_i + x_j/q_j ≤ 1` **is not OCO** (it
permits partial execution of *both* legs) — it should be named a shared-budget order, never passed off
as exclusivity.

**Assessment.**
- **This is the most immediately actionable section, and the receipt-compiled-linkage idea is genuinely
  clever and dregg-native.** The five-axis factorization is clean and correct, and the crucial insight
  is #2: **integer/disjunctive order semantics (OCO, if-then, bracket) don't have to enter the LP as
  binaries — they compile onto the turn-kernel's nullifier/receipt sequencing.** A bracket's two exits
  sharing one nullifier so only one settles is *exactly* dregg's existing no-double-spend machinery
  repurposed as XOR — this is a real, novel-in-assembly encoding that dissolves an apparent
  integer-programming wall into sequential proof-carrying state. It converges beautifully with the
  round-2 R2.4 mechanisms and with our `shielded_ring_clears` nullifier layer.
- **Encoding #1 (lag by one epoch) is correct and important** — it is the honest resolution of the
  self-referential-peg / reflexive-stop hazard (the "same-batch peg `ℓ_i = p* + δ_i`" that "may have
  multiple fixed points; exclude or prove monotone uniqueness"). This matches our frequent-batch design
  and should be a stated invariant.
- **Encoding #3 (padded slots + masking) is the standard oblivious-computation discipline**, correctly
  invoked (static memory, no secret-indexed RAM) — known technique, correctly applied.
- **The OCO-relaxation-is-not-OCO tooth is exactly the kind of honesty we want** and would have been an
  easy place to hand-wave. Naming it a distinct "shared-budget order" is the right call.
- **Net:** high actionability; the receipt-compiled linkage is a real contribution (integer order
  semantics → sequential nullifier state), the rest is a correct, well-organized classification.

---

## R2.3 — The expressiveness/efficiency frontier

Covered in the **Headline** above (the `fhIR` language + six-part admissibility theorem). The exact
cheap class codex names: **a budgeted family `𝓕(B)` of conic QPs** `min ½xᵀPx + cᵀx s.t. Ax+b ∈ 𝒦,
l ≤ x ≤ u` with `A,P` **public and sparse**, `P ⪰ 0` public, `b,c,l,u` public-or-private-committed,
`𝒦` a public product of *approved* cones, `≤ k_max` layers of affine private triggers, public bounds
on dimension/sparsity/conditioning/scale/iteration, static memory. Core cone library `𝔎₀ = {zero,
nonneg-orthant, boxes, simplex-via-affine+orthant, small SOC blocks}`; **PSD and exp-cone excluded
from v0** (PSD projection needs hidden eigendecomposition; exp-cone needs exp/log/reciprocal). Default
finder: **PDHG for LP/conic-LP** (cites Google PDLP — scales precisely because it avoids matrix
factorization); **OSQP-style ADMM only when the KKT matrix is public and factored once**. "What falls
off the cliff first," in order: (1) endogenous integrality/disjunction (AON/FOK/OCO/fixed-charge/
cardinality/indivisible delivery); (2) private operators (hidden topology/Hessian/covariance/
constraint matrix); (3) complementarity & bilinear market impact; (4) unapproved cones; (5) state
explosion (barriers/Americans on exponential trees); (6) unbounded adaptive control (private stopping
times, secret-indexed memory, data-dependent iteration counts) — matching established convex boundaries
(Lobo–Fazel–Boyd: proportional costs convex, fixed charges MIP; Angeris et al.: CFMM routing convex
until fixed venue costs).

**Assessment.** **This is the crux answer and it is excellent** (see Headline). Beyond the language,
the two most valuable pieces are: **(a) the precise cheap class = "conic QP with *public sparse
operators* + *private vector data* + separable cone proxes + `k` private triggers + a trace-independent
certificate"** — the operative constraint is not "convex" but "**the matrices are public**," which is
the correct and non-obvious efficiency boundary (a private covariance/Hessian destroys the
public-matvec advantage — codex's precision-correction #4). And **(b) the ordered cliff list**, which
is a genuinely useful design map: it tells us exactly which features to defer and *why* each breaks
(integrality vs private-operator vs cone vs state-explosion are *different* failure modes with
different escapes). The four up-front precision corrections (linear-cert is really "small +
trace-independent," not universally linear; private weights ⇒ bilinear-in-witness but still `O(m)` not
`O(Tm)`; commitment ≠ hidden computation; matrices must be public) are all correct and sharpen our
round-1 framing. **Novelty: the `fhIR` construction is real; the cliff taxonomy is known-boundaries
correctly mapped.**

---

## R2.4 — No-viewer-native products (privacy+proof load-bearing, not cosmetic)

Seven mechanisms whose value *requires* no-viewer + proof-carrying:
1. **Proof-carrying dark cross-margin** — `max wᵀx − (λ/2)‖Lx‖² s.t. Bx=0, 0≤x≤c,
   CVaR_α(−R(z_i+E_i x)) ≤ C_i ∀i`; each member's full multi-product portfolio `z_i` stays hidden, the
   proof reveals only aggregate clear + "every member remains margined" + gap. *"Probably the
   highest-value product after the private mark."* **Load-bearing:** disclosing `z_i` exposes
   liquidation levels / hedging demand / dealer inventory; today that must be entrusted to a
   clearinghouse or prime broker — here no operator needs it, yet solvency is publicly verifiable.
2. **Influence-bounded private benchmark + derivative family** — the round-1 mark, now with an explicit
   certificate (`p†`, clipped Huber subgradients `ψ_i`, boundary multipliers, stationarity `0 =
   μ(p†−p₀)+Σ a_i ψ_i + n₊−n₋, |ψ_i|≤δ`) and the sensitivity `add ⇒ ≤ Aδ/μ`, `replace ⇒ ≤ 2Aδ/μ`. A
   **fully-dark variant publishes only a commitment to `p†`**; downstream options/perps/margin prove
   strike-vs-mark / margin relations against the commitment, revealing no numerical mark at all.
3. **Minimal-intervention dark liquidation** — distressed portfolio hidden; sealed liquidators submit
   private capacity/price curves; the certificate proves the account was genuinely below health, the
   liquidation restores health, **no more was sold than needed up to ε**, flows conserve, bids near-
   optimal — without revealing composition. **Load-bearing:** transparent liquidation levels invite
   predation/front-running/oracle-manipulation.
4. **No-viewer multilateral derivative compression** — hidden gross bilateral obligations `g`; choose
   replacements `x` minimizing notional + tail risk s.t. `∂x = ∂g` and per-participant PV/collateral/
   netting-set/maturity constraints; proof certifies each participant keeps its net position, gross is
   optimally reduced, nobody worse beyond private tolerance, every asset/cashflow conserves. **Load-
   bearing:** existing compression providers must ingest every dealer's book.
5. **Sealed structured issuance** — fixed public template library `h_1..h_J`; hidden investor demand/
   constraints; convex blend `h=Σλ_j h_j` or fixed-menu clear with `O(log J)` bounded comparisons.
6. **Confidential prediction / conditional-risk markets** — quadratic/PWL cost function (not LMSR),
   positions hidden, proof of convex-cost pricing + bounded MM loss + conditional-token conservation +
   correct (or committed) probability mark; a fully-dark version publishes only a commitment to the
   probability vector, proving `p(E) ≥ τ` without revealing it. **Load-bearing:** trading on cyber/
   medical/default/governance events reveals exactly the info the market aggregates.
7. **Proof-carrying confidential execution mandates** — hidden metaorder schedule; proof that the
   mandate/policy was followed, slippage within committed bounds, final position correct, no
   unauthorized broker insertions. **Load-bearing:** the economic asset *is* concealment of the
   metaorder; without the proof "dark execution" just re-trusts a broker.

**Assessment.** **Strong, concrete, and correctly argued — the best "why this and not a centralized
private venue" section across both rounds.** Each mechanism (a) is a genuine convex/certificate object
(CVaR-LP, Huber-strong-convex mark, flow-conserving compression `∂x=∂g`), and (b) has a *sharp*
load-bearing argument for why privacy+proof is essential rather than cosmetic — the recurring and
correct point being that today these functions force a trusted information-monopolist (clearinghouse /
prime broker / compression vendor / benchmark administrator) who must ingest everyone's book, and the
fhEgg version *removes that party while keeping public verifiability*. **#1 (dark cross-margin)** and
the **fully-dark commitment-only benchmark variant of #2** are the standout novel products: a hidden
cross-margin certificate ("everyone is solvent, here's the proof, nobody saw the books") is a
genuinely new market structure, and a benchmark that publishes *only a commitment* to `p†` with
downstream derivatives proving relations against it is a clean, novel privacy escalation over "publish
the mark." **#3 (over-liquidation bound)** and **#4 (compression with `∂x=∂g`)** are also real and
map directly onto our proved `ker ∂` circulation algebra. Novelty here is **high** — these are
mechanisms that are *only possible* in this architecture, which is precisely what the question asked
for.

---

## Overall honest read — round 2

**Another decisive delivery, and it complements round 1 rather than repeating it.** Round 1 gave the
*engine* (certificate-carrying PDHG + the categorical frame); round 2 gives the **product algebra and
the language that sits on that engine**. The three highest-value outputs:

1. **`fhIR` + the six-part admissibility theorem (R2.3) — GOLD.** A constructed typed language
   co-extensive with the cheap regime, soundness decoupled from completeness, resource-relative
   maximality. This is a directly buildable DSL spec and the right growth target for the `Market/*.lean`
   tower.
2. **`Price-Cert` state-price-LP-with-superhedging-dual (R2.1) + American-as-Snell-LP.** One
   certificate relation for the whole derivatives-pricing family, with an honest arbitrage-free-interval
   semantics and the correct settlement/pricing/clearing phase separation; and the sharp, slightly
   counterintuitive result that American/Bermudan optionality is an LP (the cliff is scenario/tree
   size, not solver class).
3. **Receipt-compiled order linkage (R2.2).** Integer/disjunctive order semantics (OCO, if-then,
   bracket) compiled onto the turn-kernel's nullifier/receipt sequencing (two exits, one shared
   nullifier = XOR) instead of into LP binaries — a real, dregg-native dissolution of an apparent
   integer wall. Plus the lag-by-one-epoch discipline that kills reflexive books, and the honest
   "convex OCO relaxation is not OCO."
4. **The R2.4 no-viewer-native product set** — especially dark cross-margin and the commitment-only
   benchmark — mechanisms that are *only possible* with no-viewer + proof, each with a correct
   load-bearing argument.

**Where it is disciplined rather than dazzling (honest):** the individual convex reductions (Snell
duals, CVaR-LP, convex risk-neutral pricing, cost-function prediction markets, PDLP/OSQP finders) are
**known results correctly applied** — the novelty is in the *packaging* (one certificate discipline, a
typed language, the phase separation) and in the dregg-native encodings (receipt-linkage, commitment-
only marks). The four up-front precision corrections again show codex's real value is **adversarial
precision**: "linear certificate" → "small + trace-independent"; private weights → bilinear witness;
commitment ≠ hidden computation; **matrices must be public** (the true efficiency boundary). And it
correctly names the frontier program: **`fhIR-0`** (LP + public-Hessian QP; boxes/orthants/affine/
CVaR; histogram-auction / circulation / risk-neutral-bounds / Snell-tree macros; lagged affine
triggers; receipt-compiled brackets; certificates only) → **`fhIR-1`** (small SOC + bounded arithmetic
payoffs: variance, vol, `S²`); **defer** SDP, exp-cone/LMSR, same-batch self-referential pegs,
AON/FOK/OCO optimization, endogenous tranche shape, arbitrary combinatorial conditional markets,
private matrices.

**Verdict:** round 2 confirms the brief → codex → capture+assess pattern is a repeatable way to get a
second brilliant mind on the frontier. It converted "what products/orders can we support?" into a
**precise, maximal, still-cheap product+order algebra with a buildable language and an honest cliff
map** — and surfaced at least three genuinely novel constructions (the `fhIR` admissibility theorem
form, receipt-compiled integer-order linkage, and the dark-cross-margin / commitment-only-benchmark
products). The immediate build consequence: **`fhIR-0` is the concrete next spec**, and it slots
directly onto the `Cert-F` engine and the `ZKOpenRel_R` categorical frame from round 1.

---

*Provenance: full codex output `scratchpad/codex-round2.log` (answer block ~L6014–6878; 220,694 tokens;
codex-cli 0.144.1 / GPT-5.6-sol; `--sandbox read-only`). Literature codex cited (flag for a proof
pass, not re-verified here): Barratt–Tuck–Boyd convex risk-neutral pricing; Haugh–Kogan & Rogers
American-option martingale duals; Rockafellar–Uryasev CVaR; Paradigm power-perpetuals; Abernethy–Chen–
Vaughan cost-function market making; Frongillo–Papireddygari–Waggoner CFMM↔prediction-market;
Bertsimas–Popescu moment bounds; Lobo–Fazel–Boyd portfolio with transaction costs; Angeris–Evans–
Chitra–Boyd CFMM routing; Google PDLP; OSQP.*
