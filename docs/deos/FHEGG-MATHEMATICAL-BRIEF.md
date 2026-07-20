# fhEgg — A Mathematical Research Brief on Private Market Clearing as an Aggregation-Monoid Fold

*Self-contained brief for a mathematical analyst. It assumes no access to the source repository.
It states (i) the structural through-line, (ii) the already-proved algebra, (iii) the cryptographic
floors, and (iv) — centrally — the open novel-construction questions. Written dense and precise, for
a mathematician/cryptographer. Notation is fixed in §0. The six open questions are §7.*

---

## 0. Notation and standing objects

- **𝔸** — a commutative monoid `(𝔸, ⊕, 𝟘)`, additionally the value group of a homomorphic
  *commitment* or *encryption*: there is a hiding, (additively) homomorphic map `commit : 𝕍 × ℛ → 𝔸`
  with `commit(v₁,r₁) ⊕ commit(v₂,r₂) = commit(v₁+v₂, r₁+r₂)`. Instantiations we care about:
  Pedersen over a prime-order group (classical, DLog-binding, perfectly hiding); exponential-ElGamal
  (Penumbra); a **Module-SIS / Ring-LWE additive lattice commitment** (post-quantum); or the in-AIR
  "commitment" that is simply *a field value carried in a STARK witness under a hiding polynomial
  commitment* (the value never leaves the witness; binding = STARK soundness = collision-resistance).
- **P = {p₁ < … < p_K}** — a public price grid; `K` the price resolution.
- **A limit order** `(side, q, ℓ)` — quantity `q ∈ 𝕍`, limit price `ℓ ∈ P`. Its **curve increment**
  `δ ∈ 𝔸^K` is the step vector: bid side adds `q` to every bucket `p ≤ ℓ`; ask side adds `q` to every
  bucket `p ≥ ℓ` (the Cryptobazaar unary encoding).
- **Aggregate curves** `D, S : P → 𝔸`, `D = ⊕_{bids} δ_i`, `S = ⊕_{asks} δ_j`. `D` non-increasing,
  `S` non-decreasing in `p`.
- **Clearing price** `p* = min{ p ∈ P : D(p) ≥ S(p) }` — the single monotone crossing.
- **Incidence / boundary** `∂ : ℝ^E → ℝ^V` of the directed trade graph `G=(V,E)` (nodes = traders×assets,
  edges = admissible swaps). **Cycle space** `Z = ker ∂` (graph homology `H₁`, `dim Z = |E|−|V|+c`).
  A **circulation** is `f ∈ Z` (conserves at every node). The cycle basis `B` (columns span `Z`) is
  **public** — topology (who *may* trade what) is structural; only the flow amounts `f` are private.
- **Turn-kernel** (dregg's base abstraction, stated for the analyst): *a turn is the exercise of an
  attenuable proof-carrying token over owned state, leaving a receipt.* Formally a turn is an element
  of a fold: state evolves by an **associative left-fold of proof-carrying increments**; a recursive
  STARK aggregates the fold into one succinct proof; attenuation (capability narrowing) is
  order-independent within a turn. The empirical claim under test in this brief is that **private
  market clearing is the same algebraic object** (an associative, commutative, homomorphic fold of
  order-increments, crossed once, proof-carrying), and that this identity is what makes it
  world-class-tractable and privacy-maximal.

---

## 1. The thesis in one paragraph

"Private matching" was mis-framed. *Matching* connotes sorting/pairing — the comparison-heavy,
bootstrap-dominated corner of FHE, `O(N log²N)` compare-swaps. But a **uniform-price batch call
auction never pairs orders**: it **aggregates** them into a price-indexed cumulative curve (a
commutative-monoid fold of unary increments) and **crosses that curve once** (a monotone threshold on
a chain, `O(K)`, independent of `N`). Aggregation is the *cheap* homomorphic primitive (ciphertext /
commitment addition — no bootstrap); the crossing is the only comparison and it does not scale in `N`.
Hence private single-pair clearing lives in the cheap half of the cryptography. The **multilateral
cross-asset ring**, which *looks* like NP-flavoured graph matching, is in fact a **circulation in the
linear cycle space `ker ∂`** over a **public** basis: netting is a coequalizer/quotient, the
conservation check is homomorphic linear algebra, and for **exact all-or-nothing intents it collapses
to a free homomorphic conservation check with no optimization at all**. Only **volume-maximizing
partial-fill** selection is a genuine optimization — a **poly-time oblivious flow-LP**, not a
combinatorial wall. This is the same shape as the turn-kernel (associative fold + recursive proof),
so it reuses the same recursion/settlement machinery and inherits the same "reveal only the receipt"
discipline — the receipt being the *clearing mark* `p*`.

---

## 2. The already-proved algebra (machine-checked in Lean; stated here as mathematics)

The following are theorems, mechanically checked. They are the load-bearing algebraic core; the brief
treats them as ground truth an analyst can build on. (`Bundle` = the free commutative monoid on assets;
`toBal : Bundle → AssetId → ℤ` = the per-asset ledger reading; `pool rs = foldr (⊗) 𝟙 rs`.)

**T1 — the additive homomorphism (`toBal_mul`).**
`toBal (b ⊗ b') a = toBal b a + toBal b' a` for every asset `a`. The per-asset ledger reading is a
monoid homomorphism `(Bundle, ⊗, 𝟙) → (ℤ, +, 0)`. Consequently `toBal (pool rs) a = Σᵢ toBal rsᵢ a`
(`pool_toBal`): *the reading of the aggregate is the sum of the readings.* This is the exact statement
that "the fold commutes with the measurement."

**T2 — order-independence / CRDT (`pool_as_perm`).**
If `rs ~ rs'` (permutation) then `(pool rs).as = (pool rs').as`. The aggregate is invariant under
reordering — the fold is over a *commutative* monoid, so arrival order is irrelevant (the
coordination-lite property). The aggregator is additionally proved *faithful* (`aggregate_sound`):
`mergeSort` by declared priority yields a book that is a permutation of the submissions (no drop, no
insert, multiset of nonces preserved) and is priority-sorted (no reorder) — with both polarities of
teeth (dropped/inserted/substituted books fail `faithful`; a reordered book fails `prioritized`).

**T3 — clearability *is* Σ-balance (`exact_clears_iff`).**
For an **exact book** (every order's predicate accepts exactly its `wanted`), a market clearing
*exists* **iff** the offered pool equals the wanted pool as bundles:
`Nonempty (MarketClearing book) ↔ (pool offers).as = (pool wants).as`.
Forward: fairness pins the whole allocation to the wanteds (`exact_alloc_eq`), and the discrete
`Converts` relation forces pool equality. Backward: allocate everyone their wanted; the pool equality
*is* the conversion witness. So for exact intents, **clearing is not an optimization — it is a
conservation equation.** Corollaries proved as teeth: a non-conserving book (`mintBook`, wants 8 gold
vs 7 offered) admits **no** clearing (`mint_refused`); a pool-balanced but misrouted allocation is
refused by fairness (`unfair_refused`) — conservation and fairness are independent teeth.

**T4 — conservation is checkable with nothing decrypted (`created_value_conservation`).**
`Σᵢ commit(vᵢ, rᵢ) = commit(Σᵢ vᵢ, Σᵢ rᵢ)`. Hence the homomorphic excess `Σ C_in − Σ C_out = 0`
certifies "the batch minted nothing" **over the commitments alone** — no value is ever opened.
Composed with T3, this gives `shielded_ring_value_conserves_hidden`: equal value-sums and equal
blinding-sums ⇒ equal commitment-sums, i.e. conservation while every amount stays hidden.

**T5 — the shielded ring clears conserving + fair + private (`shielded_ring_clears`).**
A shielded ring whose matched cycle is `CycleValid` and which settles through the verified executor is
simultaneously (a) **conserving** per asset on the real ledger, (b) **fair** — structurally
`RingBalanced` and every leg within its committed offer/want (`clearing_respects_limits`,
`cycle_individuallyRational`), and (c) **private + no-double-spend** — every leg spends a real
committed member note (hidden owner/value) whose nullifier is fresh and, once spent, never re-spendable.
The multilateral cross-asset ring — a 3-cycle in which *every* leg is bilaterally stuck
(`crossBid_needs_market`) and every proper sub-book fails to balance — clears. This is stated over the
**hidden commitments** (`MatchNode` columns are the pool's `commit_hidden_asset` values), so matching
happens over ciphertext, not cleartext. A **real-crypto** version (`shielded_ring_clears_real_crypto`)
re-grounds both hidden halves on real group-Pedersen (binding = DLog carrier) and a real Poseidon2
Merkle tree (root-binds-set = sponge collision-resistance), retiring the toy stand-ins.

**The upshot for the analyst.** The private uniform-price / ring clearing *reduces to* three proved
facts: **T1** (the fold commutes with measurement), **T3** (clearing = conservation for exact intents),
**T4** (conservation is a commitment identity, decrypt-nothing). fhEgg is the claim that these three,
folded, *are* the whole of exact private clearing — and the residual hard cores (partial-fill volume
maximization; the reveal-nothing theorem; a PQ homomorphic layer) are precisely the open questions §7.

---

## 3. The computational asymmetry (why "matching cost evaporates")

The cost model has one load-bearing asymmetry: in every homomorphic regime, **addition is ~free** and
**comparison (the bootstrap / LUT) is the cost unit**.

```
   naive private matching :  O(N log²N)  bootstraps         (comparison-dominated; oblivious sort)
   fhEgg kernel           :  O(N·K)      additions  +  O(K) comparisons
                               ╰─ bootstrap-free ─╯      ╰─ N-independent ─╯
```

Concrete anchors (published, current): TFHE ciphertext addition ≈ microseconds (no bootstrap); a
programmable bootstrap ≈ <1 ms on 8×H100, ~10–50 ms historical CPU; `FheUint16` equality ≈ 31 ms, min
≈ 96 ms on CPU. Penumbra runs additive aggregation per-block on mainnet; Cryptobazaar clears 128
bidders × 1024 price buckets in **< 0.5 s**; published FHE sorts land 128 real elements in ~22 s
(CKKS) / 64 in ~36 s (rank-sort). The `N`-dependent work in fhEgg (the fold) never touches a bootstrap;
the comparison work (the crossing) never depends on `N`; `K` (resolution) is a *chosen* constant. This
is the precise numerical content of "the expensive part of private matching evaporates."

**A cheap-verifiability corollary** worth stating for the analyst: because the aggregation+crossing
circuit is *deterministic* and the input ciphertexts are *public commitments*, correctness of the
*evaluation* is publicly re-checkable for free (re-run the public circuit, compare output ciphertext) —
no verifiable-FHE SNARK needed for the compute step. Only the final threshold **decryption of the
scalar `p*`** (in the FHE regime) or the aggregation-fold STARK (in the commitment regime) needs a
proof. This collapses "verifiable FHE" to "verifiable threshold decryption + public re-evaluation," or
in dregg's chosen regime to a STARK over the fold — decrypt nothing but the market fact `p*`.

---

## 4. The multilateral ring as homology (the de-fanging)

Pessimistic framing: cross-asset multilateral clearing (A→B→C→A top-trading-cycle) is graph matching,
hence combinatorial. **Correct framing:**

1. A clearing is a **circulation** `f ∈ Z = ker ∂` (conserves at every node). `Z` is a *linear
   subspace* (graph homology `H₁`), with an explicitly computable **public** cycle basis `B`.
2. **Netting is a coequalizer:** gross flow → net position is the quotient of the gross flow by the
   cycle relations (the boundaries `im ∂ᵀ` are exactly what collapses).
3. Because the topology is public and only the amounts `f` are private, computing net positions
   `net = ∂f` and verifying conservation `∂f = 0` are **homomorphic linear algebra over a public matrix
   and committed private amounts** — bootstrap-free, the same cheap primitive as the §2 fold (Penumbra's
   homomorphic scalar sum generalized to a *vector*). **Correction (`FHEGG-CODEX-INSIGHTS.md` Q3):** do
   this on the **incidence matrix `A = ∂` directly, not on an explicit cycle basis `B`** — `A` is sparse
   and well-conditioned, whereas a fundamental cycle basis can be dense/ill-conditioned and enlarges the
   fixed-point/modulus bounds of the oblivious solver; the traversal is public with `A` alone.
4. **For a GIVEN exact all-or-nothing book, verifying the clearing is free** (T3): clearing exists iff
   pools balance, and the allocation is pinned, so *checking a fixed proposed book* is a **free
   homomorphic conservation check** on the committed offers/wants (T4) — `shielded_ring_clears`, proved.
   **Correction (post-brief, `FHEGG-CODEX-INSIGHTS.md` Q3):** this is *verification*, not *selection*.
   Choosing the max-volume exact **subset** of all-or-nothing orders is
   `max Σᵢ wᵢ xᵢ s.t. Σᵢ xᵢ aᵢ = 0, xᵢ ∈ {0,1}`, a 0-1 balancing problem that encodes subset-sum /
   set-packing and is **NP-hard** — a public topology does not remove the integrality. The tractable
   engine is therefore the **`[0,1]` partial-fill relaxation** below, not exact-subset optimization.

**The residual hard core (named honestly):** when orders admit **partial fills** and the market
**maximizes total cleared volume** across many candidate cycles with binding box constraints
`0 ≤ f_e ≤ cap_e`, you have a genuine **max-volume circulation LP**, whose binding set and pivot path
are *data-dependent*. Doing that **obliviously** (control flow leaks nothing) is the frontier. Known
poly-time oblivious realizations exist — Aly–Van Vyve secure min-cost circulation via
minimum-mean-cycle-canceling; Toft's oblivious simplex (≈ `O(nm)` secure mults/pivot, pivot count
padded to worst-case or it leaks); interior-point (`O(√n·log 1/ε)` iterations, each a secure linear
solve). So the ring is a **poly-time oblivious LP**, not an exponential monster; the tax is worst-case
iteration padding.

---

## 5. The private-convex engine (thesis stated; not yet landed as a doc)

The natural generalization the brief poses — beyond auctions and rings — is a **private convex-program
factory**. Many DeFi primitives are convex programs: uniform-price clearing (an LP), volume-max
circulation (an LP), AMM curve trades and multi-hop routing (convex), portfolio/basket rebalancing
(QP), risk-constrained liquidation, optimal execution, collateral optimization. The thesis:

> **A convex optimization solved by an operator-splitting / first-order method decomposes each
> iteration into (i) a homomorphic-LINEAR step (matrix-vector products, gradient steps — cheap over an
> additive commitment) and (ii) a small, low-dimensional PROX / projection nonlinearity. If the prox
> is batched/minimized and the iteration count is a FIXED, data-independent budget `T`, the whole
> solve is an oblivious `T`-fold of "cheap linear + small prox" — the same aggregation-fold shape as
> fhEgg, generalized from a monoid sum to a fixed-length operator-splitting recursion.**

Under this thesis the private-convex engine is the fhEgg fold with the crossing replaced by a
fixed-`T` proximal-splitting fold, over the same PQ-additive commitments, carrying the same STARK. The
open question §7.1 is precisely: *what is the best such splitting method* — one that maximizes the
homomorphic-linear fraction, minimizes/batches the prox nonlinearity, runs a fixed oblivious budget,
and lives over lattice-additive commitments. This is the crux the analyst is asked to design.

---

## 6. The cryptographic floors (what the whole thing stands on)

- **STARK soundness floor:** Poseidon2 sponge **collision-resistance** (`HashCR`) +
  `Poseidon2ChipArithSound`, with the BCIKS20 list-decoding core proved for the deployed code. The
  deployed FRI query-soundness floor is **~31.5 bits** — a δ=7/16-far word survives the 38-query
  check with probability `(9/16)³⁸ < 2⁻³¹` (`FriArityForking.deployed_far_survival_lt`,
  `DeployedProximitySoundness`). The per-fold proximity-gap column reads **~109.84 bits** at the
  deployed arity-8 fold (`FriArityTransfer.arity8_perFold_soundness`, `< 2⁻¹⁰⁹`); the once-quoted
  ~112.6 is the arity-2 figure and provably fails at arity 8 (`arity8_error_not_lt_2e112`).
  Everything inherits this floor. All PQ (hash-based).
- **Privacy floor (already PQ):** Pedersen *hiding* is perfect/information-theoretic (quantum-safe
  unconditionally); the STARK privacy path is statistical zero-knowledge (`HidingFriPcs`, `ZK=true`).
  So confidentiality is quantum-safe today.
- **The one real PQ hole — value binding:** the shielded value-commitment is today a Pedersen
  commitment over Ristretto with a Schnorr excess and a Bulletproof range — all **discrete-log**.
  Pedersen *binding* is DLog and therefore **Shor-broken**: a quantum adversary recovers the generators'
  DLog relations, re-opens a commitment to a larger value, and forges a conservation-satisfying batch
  that **mints** while privacy hides the theft. This is *not* covered by dregg's PQ metatheory (whose
  floor uses DLog only as the classical leg of a *hybrid* signature with an MSIS fallback; the shielded
  binding has no lattice fallback). **The fix (Option A):** retire DLog onto a **Poseidon2
  hash-commitment + fully-in-AIR STARK conservation** — binding = `HashCR` (Grover-only, ~128-bit
  quantum at 256-bit output), conservation = an in-AIR field gate `Σ v_in − Σ v_out = 0` with an in-AIR
  range gadget preventing wraparound, hiding = the statistical-ZK PCS. Most of this is already built
  (`value_binding = hash(value, [randomness,…])` is already a public input; the in-AIR conservation
  gate and `VALUE_BITS` range gadget exist); the residual is a cutover + a 64-bit in-AIR range.
  **Option B (fallback):** a Module-SIS additive lattice commitment `Com(v;r)=A·r+v·g mod q` (binding =
  MSIS, additively homomorphic) — keeps the homomorphic-Σ elegance but pays kilobyte commitments + a
  second lattice proof system.
- **The reveal-nothing frontier (the crux theorem):** the clearing is private *by construction* (all
  plaintext stays in the witness; only `[nullifier, root, value_binding]` per leg is exposed), and an
  abstract perfect-ZK lemma exists (`view_indep_of_witness` from a perfect-ZK law), but **there is no
  theorem yet that the clearing transcript is independent of the trades** — no clearing-level
  simulator / indistinguishability, and no *named* statistical-ZK floor for the deployed hiding FRI.
  That theorem (statement + simulator + named floor) is the highest-value differentiator and does not
  exist today.

**The honest state table:**

| Property | Rests on | Status |
|---|---|---|
| Exact private clearing = Σ-balance | T1–T5, machine-checked | **PROVED (spec)** |
| Decrypt-nothing conservation | `created_value_conservation` (T4) | **PROVED** |
| 2-leg shielded ring-clearing AIR | in-AIR conservation + range + fusion; tested both poles | **BUILT** |
| N-leg variable cycle + partial-fill inequality in-AIR | — | **NEEDED (M)** |
| Reveal-nothing (transcript ⟂ trades) theorem | PerfectZK template + named FRI-ZK floor | **FRONTIER (RESEARCH)** |
| PQ value-binding (retire DLog) | Poseidon2 CR + in-AIR STARK conservation | **NEEDED (cutover, mostly built)** |
| Oblivious volume-max multilateral partial-fill at scale | oblivious flow-LP | **FRONTIER (poly-time)** |
| Private-convex engine (fixed-T splitting) | §5 thesis | **OPEN (design)** |

---

## 7. The open novel-construction questions (the crux — for the analyst)

These are posed precisely. (1) and (2) are the centre of gravity.

### Q1 — The novel homomorphic-native oblivious splitting method
Design a convex-optimization iteration that **maximizes the homomorphic-linear fraction**, **minimizes
/ batches the prox nonlinearity**, runs a **fixed, data-independent oblivious iteration budget `T`**,
and lives over **PQ lattice-additive commitments** (Module-SIS / Ring-LWE, `Com(v;r)=A·r+v·g`). Concretely:
which operator-splitting scheme is best here — ADMM, PDHG (Chambolle–Pock), Douglas–Rachford, a mirror-
descent / Bregman variant, Halpern iteration, or something new — for the two canonical programs
(uniform-price clearing as an LP; volume-max circulation over the public cycle basis as a box-constrained
LP)? What is the right way to make the prox oblivious and cheap (the prox for a box is a clamp; for an
LP it is a projection — can it be a single batched comparison per iteration, amortizing the one bootstrap
cost fhEgg already pays for the crossing)? Give a concrete construction, an iteration-complexity /
fixed-`T` convergence bound at target accuracy `ε`, and the per-iteration homomorphic cost (how many
ciphertext additions vs. bootstraps). Where must the commitment modulus `q` and the fixed-point scaling
be chosen to keep the linear algebra exact and no-wrap?

### Q2 — The categorical / algebraic unification
Is there a *single* structure that unifies **(i)** the turn-kernel (associative left-fold of
proof-carrying increments over owned state), **(ii)** the aggregation-monoid (commutative-monoid fold of
order-increments + a monotone crossing = a Tarski fixpoint on a chain), **(iii)** the circulation in
`ker ∂` (graph homology `H₁`; netting = coequalizer), and **(iv)** the private-convex engine
(fixed-`T` operator-splitting fold)? Candidate lenses to evaluate: a **chain complex / homological**
presentation (conservation = `∂`-closedness, netting = homology, mint = a non-closed chain); a
**traced / compact-closed monoidal category** (the fold = composition, the ring = the trace/feedback,
partial fills = a coend/optic); a **sheaf / topos** presentation (local orders glue to a global clearing
iff a cohomological obstruction vanishes — mint = a non-vanishing `H¹`); a **semiring / tropical
(min-plus)** presentation (the crossing and shortest-augmenting-cycle as min-plus matrix operations);
or a **lens / optic / comonad** presentation (a turn as a guarded comodel). The prize: a presentation
from which the whole DeFi surface (auction, ring, AMM, lending oracle, options mark, convex products)
falls out as instances of one "useful kernel that becomes private + coordination-lite easily," with the
privacy and the proof-carrying structure appearing as *functorial* properties (e.g. a monoidal functor
to a category of commitments that is faithful on conservation and trivial on values). State the object,
the morphisms, what conservation/mint/fairness/privacy each become, and what genuinely new mathematics
(if any) is required.

> **Post-analysis corrections + the recorded target (`FHEGG-CODEX-INSIGHTS.md` Q2; skeleton captured in
> `PRIVATE-CONVEX-ENGINE.md §4.1` as `ZKOpenRel_R`).** Two phrasings above are loose:
> (a) **the crossing is not automatically a Tarski fixpoint** — monotone *curves* are not a monotone
> *operator*; the fixpoint is of the explicit update `F(j) = j if D(pⱼ)≤S(pⱼ) else min(j+1,K)`, least
> fixed point *assuming a crossing exists*. (b) **A commitment functor cannot be both "faithful on
> conservation" AND "trivial on values"** — hiding *intentionally* identifies value-distinct worlds, so
> nothing is faithful on values while hiding them. Honest split: **computational binding reflects
> bounded-resource equalities**; **hiding makes same-leakage-class openings indistinguishable**; privacy
> is a simulator natural transformation `View ≈ Sim∘Q` over a leakage functor `Q`, not "transcript
> independent of values." The captured answer direction (**decorated cospans + guarded trace + resource
> grading + convex-cost-by-infimal-convolution + proof/privacy functors**, conservation = the zero-defect
> `d⁻¹(0)` subcategory) is a **well-posed research target, NOT a discharged proof** — the open theorem is
> compositionality/closure under feedback + adaptive composition.

### Q3 — The oblivious private-convex / LP frontier
The volume-max multilateral partial-fill is a poly-time oblivious LP over the *public* cycle basis
`B` (so the constraint matrix is public; only the objective data / caps are private). Is this the most
efficient private construction? Does the public-basis structure admit a *better-than-generic-LP*
oblivious algorithm — e.g. an oblivious min-mean-cycle-canceling whose cycle enumeration is public and
whose only private data are edge residuals, or a fixed-`T` first-order method (Q1) specialized to the
network-flow polytope (where prox = per-edge clamp, exact and batched)? Give the sharpest oblivious
iteration bound and the leakage profile (what padding is forced).

### Q4 — The PQ-lattice-additive homomorphic fold
Design the best lattice (Module-SIS additive) commitment for the price-curve aggregation `D = ⊕ δ_i`,
optimized to be **efficient to verify inside a hash-based STARK** (Poseidon2/FRI). Constraints: additive
homomorphism over `𝔸^K` (bucketwise), binding = MSIS, hiding, and — crucially — a commitment-opening /
conservation relation that is *cheap as an AIR* (few nonlinear gates; ideally the MSIS check is a small
number of field multiplications and range checks the Poseidon2 chip already supports). Is Option A
(hash-commitment + in-AIR field conservation, no homomorphism outside the AIR) strictly better than a
genuine lattice-homomorphic commitment once all legs are inside one clearing AIR? When does the
independent-aggregation property of a true homomorphism (summing commitments produced by *different*
provers without a shared circuit) actually earn its kilobyte cost?

### Q5 — Intricate private financial products (the gigabrain products)
Given the private-convex engine (Q1) and the fold/crossing kernel, what **novel private mechanisms** —
expressible as convex programs with the right oblivious structure — does it unlock, and what is their
mathematical structure? Prompts: a **private frequent-batch auction with a proven manipulation-resistant
mark** feeding options (strike-vs-mark), perps (funding off mark), lending (private liquidation oracle);
**private portfolio/basket rebalancing** as an oblivious QP; **private optimal execution / TWAP** over a
fixed horizon; **private risk-constrained clearing** (conservation + a convex risk budget); **private
multi-asset AMM routing** as a fixed-`T` convex solve; **combinatorial / batch-Walrasian equilibria** in
the linear regime. Which of these are genuinely new as *private* mechanisms, and what convex structure
makes each oblivious-tractable (or not)?

### Q6 — Efficiency gigabrain
Clever decompositions / factorings / algebraic methods for **world-class-efficient** private clearing +
convex optimization. Prompts: coarse→fine two-pass crossing to beat the `O(K)` resolution cost; SIMD /
CRT / RNS packing of the `𝔸^K` curve; exploiting the public cycle basis for a sparse / low-rank
homomorphic linear algebra; amortizing the single bootstrap fhEgg pays across many buckets; a
Newton-on-the-curve crossing; number-theoretic transforms for the fold; batching many independent
per-pair clearings into one recursive STARK; and any algebraic identity that turns a nonlinear step into
a linear one over the commitment. What are the sharpest asymptotic and constant-factor wins?

---

## 8. Pointers (for provenance; the analyst needs none of these to answer)

Machine-checked algebra: `metatheory/Market/{Clearing,Aggregation,ShieldedClearing}.lean`
(`toBal_mul`, `pool_toBal`, `pool_as_perm`, `aggregate_sound`, `exact_clears_iff`, `exact_alloc_eq`,
`clearing_conserves_per_asset`, `created_value_conservation`, `shielded_ring_clears`,
`shielded_ring_value_conserves_hidden`, `shielded_ring_clears_real_crypto`). Design/assurance:
`docs/deos/{FHEGG-KERNEL, SHIELDED-DREX-ASSURANCE-ROADMAP, PQ-SHIELDED-COMMITMENT,
DREX-NO-VIEWER-SURPASS}.md`. Prior art cited in those: BOREALIS (ePrint 2019/276), SEAL (2019/1332),
Cryptobazaar (2024/1410), Penumbra ZSwap flow-encryption, Renegade (MPC+zkSNARK), inner-product FE
(2015/017, 2015/608), Aly–Van Vyve secure network flow, Toft oblivious simplex (FC'09), Zama TFHE/TKMS,
Eisenberg–Noe / Tarski-fixpoint clearing (arXiv 2503.17836, 2602.16387).
