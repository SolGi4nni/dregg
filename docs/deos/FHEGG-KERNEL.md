# The fhEgg Kernel — the computational kernel that makes DrEX private clearing world-class-tractable

*Companion to `DREX-DESIGN.md` (the exchange) and the turn-kernel. This doc answers a
narrower, deeper question: is there an **elegant, composable computational kernel** for
private market clearing — the way "a turn = an attenuable proof-carrying token over owned
state, leaving a receipt" is the kernel that makes ZK + coordination fall out of dregg
naturally? SOTA survey (cited, with numbers) · the fhEgg kernel (precisely stated) · the
featureset it unlocks · the honest feasibility envelope. What-is, present tense; every
ambitious edge names its grade. No incremental ladder — this is the straight-at-it design.*

---

## 0. Six-line summary

1. **The hypothesis holds.** A batch uniform-price call auction is an **AGGREGATION, not a
   matching**: orders sum into a price-indexed supply/demand curve (a commutative-monoid
   fold of per-order increments), and clearing is a **single monotone crossing** of that
   curve. The expensive part of "private matching" (sort/compare, the bootstrap-heavy FHE
   regime) *evaporates* — it is replaced by **O(N) homomorphic additions + an O(K) crossing**
   over the aggregate, K = price resolution, cost independent of N.
2. **The aggregation-monoid IS the right kernel** — confirmed by economics (cumulative
   curves are folds), by cryptography (additive homomorphism is the cheap primitive across
   FHE / additive commitments / threshold-ElGamal / MPC-sum), and by **dregg's own proved
   Lean** (`exact_clears_iff`: clearability *is* Σ-balance; `toBal_mul`: the additive
   homomorphism; `created_value_conservation`: Σ commit = commit Σ, checkable with **nothing
   decrypted**).
3. **How rich a book:** a **full private limit-order-book call auction** — each limit order is
   one curve increment, the aggregate *is* the book, clearing is the crossing. Aggregation-
   tractable to N in the thousands today (Penumbra runs it per-block on mainnet; Cryptobazaar:
   128 bidders × 1024 prices in **< 0.5 s**).
4. **Which products:** the private-but-attested **clearing mark** is a manipulation-resistant
   fair oracle → options (strike vs mark), perps (funding off mark), lending (the private
   oracle), structured products — all over **shielded positions**, **proof-settled**.
5. **The multilateral cross-asset ring is *less hard than it looks*.** Multilateral clearing
   is a **circulation** (a flow in the cycle space = ker ∂, a linear subspace with a **public**
   basis); netting is a **coequalizer**/quotient. So the private part is **homomorphic linear
   algebra over a public matrix** (cheap); for **exact all-or-nothing intents it collapses to a
   pure homomorphic conservation check with no optimization at all** (`exact_clears_iff`). Only
   the **volume-maximizing partial-fill** selection is a genuine **oblivious flow-LP** — poly-
   time, real protocols exist (Aly–Van Vyve secure min-cost circulation; Toft secure simplex),
   but the scale frontier.
6. **Honest feasibility:** single-pair uniform-price private clearing is **real-soon / already-
   real** at N≈10³, K≈10²–10³. The frontier is (a) large price resolution K (linear cost),
   (b) marginal pro-rata rationing at the exact clearing price, (c) private volume-maximizing
   multilateral at scale (oblivious LP), (d) a PQ additive layer (today's Pedersen/ElGamal are
   classical-DLog). None of these is the exponential monster "private matching" was feared to be.

**The single biggest insight:** *"private matching" was mis-framed.* "Matching" evokes
sorting/pairing — the comparison-heavy, bootstrap-dominated corner of FHE. But a uniform-price
call auction **never pairs orders**; it **aggregates them into a price-indexed curve and
crosses it once**. Aggregation is the *cheap* homomorphic primitive (ciphertext addition, **no
bootstrap** — microseconds in TFHE); the crossing is O(price-buckets), independent of the
number of orders. Private clearing therefore lives in the **cheap half of FHE**, and dregg has
the algebra **already proved**. And the deeper turn of the same key: even the multilateral ring
— which *looks* like NP-flavoured graph-matching — is a **circulation in a linear cycle space
with a public basis**, so netting is homomorphic linear algebra and the residual hard core is a
*polynomial* oblivious LP, not a combinatorial explosion.

---

## 1. SOTA survey — private/verifiable market clearing (cited, with numbers)

### 1.1 The "auction as private aggregation / homomorphic tallying" line

The oldest and most robust idea in secure auctions is that **you do not need to match — you need
to tally**. The line runs voting → auctions:

- **Homomorphic threshold tallying (the ancestor).** Encrypt each contribution under a threshold
  key in an **additively homomorphic** scheme (Paillier, exponential-ElGamal), sum the
  ciphertexts publicly, threshold-decrypt **only the aggregate**. No individual input is ever
  revealed. This is the standard homomorphic e-voting tally and it ports directly to auctions:
  the "tally" becomes the **aggregate demand/supply at each price**.
- **BOREALIS** (Blass & Kerschbaum, ePrint **2019/276**, ASIA CCS'20): secure computation of the
  **k-th ranked** of n sealed integers using **additively homomorphic ECC-ElGamal** under
  *distinct* per-party keys + Groth–Sahai ZK, in **4 rounds — constant** in both bit-length ℓ and
  party count n. For **n = 200, ℓ = 32 bits**, all ZK proofs compute in **less than one Bitcoin
  block interval** (~10 min), and they explicitly note this *surpasses generic constant-round MPC
  including shared-key FHE*. This is the reference for the cost of the **crossing/comparison** half
  (rank/threshold), and it is already small.
- **SEAL** (Bag, Hao, Shahandashti, Ray, ePrint **2019/1332**): the first **auctioneer-free**
  sealed-bid protocol with **linear O(c)** computation/communication (c = bid bit-length), fully
  publicly verifiable, bidders jointly compute the max bid while losing bids stay secret;
  extends to Vickrey (reveal only winner + 2nd price).
- **Cryptobazaar** (Novakovic, Kavousi, Gurkan, Jovanovic, ePrint **2024/1410**, NDSS'25):
  *private sealed-bid auctions at scale* with a **single untrusted auctioneer** for coordination
  only. Core technique: **unary-encode each bid across the price range, then run a distributed
  logical-OR (an anonymous-veto aggregation)** over the unary vectors + succinct ZK gadgets.
  Handles first-, second-, and general **(p+1)-st-price** and sequential auctions. Concrete:
  **128 bidders × 1024-value price range terminates in < 0.5 s**. This is the cleanest published
  confirmation of the fhEgg decomposition — *unary-encoded orders are aggregated (OR/sum) across
  price buckets, then the outcome reads off a crossing*.
- **Functional encryption for inner products** (Abdalla–Bourse–De Caro–Pointcheval, ePrint
  **2015/017**; Agrawal–Libert–Stehlé, ePrint **2015/608**): efficient FE where a key for vector
  **k** reveals exactly ⟨k, x⟩ and nothing else. **Linear functionals only** — a weighted-sum
  clearing rule is expressible, but **comparison / threshold / max FE remains far less efficient
  than the additive path** (confirmed across the FE literature). Takeaway: use FE/additive-HE for
  the **aggregation** (linear), and *avoid* pushing the crossing into a general-comparison FE.

**Survey verdict on the line:** the field independently converged on *aggregate-then-open* —
additive homomorphism does the heavy lifting, and only a small ranked/threshold reveal remains.
That is the fhEgg kernel, arrived at from the auction side.

### 1.2 FHE-DeFi concrete numbers — is "aggregate cheap, cross small" borne out?

| Operation | Scheme | Concrete cost | Source |
|---|---|---|---|
| Ciphertext **addition** | TFHE (`tfhe-rs`) | **linear, no bootstrap — microseconds** | Zama docs; FHE folklore |
| Programmable bootstrap (PBS) — the unit of **comparison / LUT** | TFHE | **< 1 ms on 8×H100**; ~10–50 ms historical CPU | Zama (Messari/BlockEden reports) |
| Throughput | Zama fhEVM | **20+ TPS CPU**; **189,000+ bootstraps/s on 8×H100**; roadmap **500–1000 TPS** | Zama 2025–26 |
| Oblivious **sort** of N | any FHE (bitonic) | **O(N log²N) compare-swaps**, each ≈ a PBS | standard |
| Live **sealed-bid Dutch auction**, uniform clearing price computed homomorphically | Zama fhEVM (2025) | shipped on Ethereum; aggregates bids, reveals only clearing price | Zama token-auction announcement |

The asymmetry is the whole game. **Addition is ~free; the bootstrap (comparison/sort) is the
cost unit.** Naive "private matching" via oblivious sort of N orders is **O(N log²N) bootstraps**
— at even 1 ms/PBS that is seconds-to-minutes for N in the thousands, and it is the wrong shape.
The aggregation kernel does **O(N) additions (≈ free) into K price buckets + O(K) crossing**: the
N-dependent part never touches a bootstrap, and K (price resolution) is a *chosen* constant. This
is the numerical statement of "the matching cost evaporates."

### 1.3 The competitors — every one has a viewer or a committee, and all are classical

| System | Actual clearing mechanism | The viewer / committee | Class |
|---|---|---|---|
| **Penumbra ZSwap** | Additive **exponential-ElGamal** flow encryption: values split into **4×16-bit limbs**, encrypted to a validator DKG key, **homomorphically summed component-wise**, then **threshold-decrypt only the per-block aggregate**; recovery via **DLog lookup table over [0, 2²³)**; **640 bytes/value**. | A **t-of-n validator committee** threshold-decrypts; a colluding quorum can decrypt individual pre-aggregation contributions. Distributed, *not eliminated*. | classical DLog |
| **Renegade** | 2-party **MPC (SPDZ variant)** among relayers computes `VALID MATCH MPC` and emits a **collaborative zkSNARK**; orders matched on secret-shared inputs. | The **relayer pair holds the secret shares** and runs the match — a computing viewer. | classical |
| **Aztec** | Private notes, but the **sequencer orders/executes** the batch. | The **sequencer** sees ordering. | classical |
| **CoW Protocol** | Off-chain **solver competition** over batches, uniform directed clearing price. | **Every solver sees every signed order** before execution — *not private*. | classical |

**Penumbra is the closest relative and the sharpest contrast:** it *already does* the fhEgg
aggregation — additive homomorphic sum, decrypt only the aggregate — which is exactly why it has
the field's strongest privacy. But it **decrypts** (a committee holds the key), and it is
**classical DLog**. dregg's move (§2, §3.4) is to make the aggregate a **Pedersen/commitment fold
that never decrypts at all** — conservation is checked *on the commitments* (`Σ commit = commit
Σ`) — and to carry a **STARK proof** of the aggregation+crossing rather than trusting a committee.

### 1.4 The algebra that makes it fall out — clearing as a monotone operator on a lattice

The clean structures the research surfaces (and that the fhEgg kernel is built on):

- **Clearing as a Tarski / Knaster–Tarski fixpoint.** Market clearing is a **monotone operator on
  a complete lattice** (of price/allocation vectors); a fixed point *exists* and is reachable by
  monotone iteration — no smoothness or uniqueness needed. This is the standard treatment of
  **financial-network clearing** (Eisenberg–Noe; *Clearing Sections of Lattice Liability
  Networks*, arXiv 2503.17836; *Computing Tarski Fixed Points in Financial Networks*, arXiv
  2602.16387). For a **single-pair** uniform-price auction the lattice collapses to a chain (one
  price axis) and the fixpoint is the **single crossing** — a monotone threshold, the simplest
  possible case.
- **Curves as commutative-monoid folds / CRDTs.** The aggregate demand/supply curve is the fold
  of per-order increments under an **associative, commutative** ⊕; order-independent mergeable
  increments are exactly the **CRDT / commutative-monoid (G-Counter)** shape — merge does not
  depend on arrival order. This is what makes the aggregation **coordination-lite** (no consensus
  on order needed to compute the total) and **composable** (batches fold associatively).
- **Netting as a coequalizer; circulations as graph homology.** A multilateral net position is
  the **quotient of the gross flow by the cycle relations** — a coequalizer — and the space of
  conserving flows is the **cycle space = ker ∂** of the boundary map, a **linear subspace**
  (graph homology H₁). This is the structure that de-fangs the multilateral case (§3.3).

These are not decoration: each maps to a concrete dregg primitive that is **already proved**
(§2.4). The private clearing *falls out* of the algebra the way ZK + coordination fall out of the
turn-kernel — because in both cases the operation is an **associative fold of increments over
owned state** and the proof is a STARK over that fold.

---

## 2. The fhEgg kernel — stated precisely

> **A clearing is the fold of order-increments into an aggregate curve, crossed once, leaving a
> proof-carrying mark.**
>
> — the exact structural twin of the turn-kernel ("a turn is the exercise of an attenuable
> proof-carrying token over owned state, leaving a receipt").

### 2.1 The four parts

**(a) The object — an encrypted/committed aggregate curve.**
Fix a price grid `P = {p₁ < … < p_K}` (public; K is the chosen resolution). The market state is a
**price-indexed vector of aggregates**

```
   D : P → 𝔸        (cumulative demand)          S : P → 𝔸        (cumulative supply)
```

valued in a **commutative monoid 𝔸** that is *additively homomorphic under encryption/commitment*
— e.g. Pedersen commitments `𝔸 = 𝔾` (dregg's `ValueCommitment`), exponential-ElGamal (Penumbra),
a lattice-additive ciphertext (PQ), or an MPC additive share. The curve is the **aggregate**;
there is no per-order object to look at.

**(b) The operation — a commutative-monoid fold of order-increments.**
A limit order `(side, qty q, limit ℓ)` is one **curve increment**: on the bid side it adds `q` to
every bucket `p ≤ ℓ` (you'll trade any price at or below your limit); on the ask side it adds `q`
to every bucket `p ≥ ℓ`. Concretely it is a **unary/step increment vector** `δ ∈ 𝔸^K` (the
Cryptobazaar encoding). Aggregation is the fold

```
   D = ⊕_{i ∈ bids}  δ_i        S = ⊕_{i ∈ asks} δ_i        (⊕ = homomorphic add, bucketwise)
```

`⊕` is **associative and commutative** with identity `𝟘` — a commutative monoid. Hence the fold is
**order-independent** (CRDT-shaped: submit-order does not matter), **mergeable** (two sub-batches
fold associatively into one — `D = D_A ⊕ D_B`), and computable **without any decryption** (it is
ciphertext/commitment addition, the cheap primitive). Cost: **O(N·K) homomorphic additions**, all
bootstrap-free; with SIMD-packing or Pedersen scalars, effectively O(N) group ops.

**(c) The clearing — a single monotone crossing (a fixpoint on a chain).**
The uniform clearing price is the **crossing** of the two monotone curves:

```
   p* = the price where cumulative demand first meets cumulative supply
      = min { p ∈ P : D(p) ≥ S(p) }        (a monotone threshold / prefix-crossing)
```

Because D is non-increasing in p and S is non-decreasing, `D − S` is monotone and the crossing is
a **single threshold search over K buckets** — the Tarski fixpoint on the price *chain*. This is
the **only** place a comparison happens, and it is **O(K)**, *independent of N*. It reveals **only
p\*** (and, if desired, the cleared aggregate volume `V* = S(p*)`); the individual orders and the
rest of the curve stay sealed.

**(d) The proof + the privacy.**
- **Privacy — no viewer.** The fold is homomorphic, so the aggregate leaks nothing about any
  addend (additive-HE / commitment hiding). Conservation is checked **on the commitments**:
  `Σ commit(vᵢ, rᵢ) = commit(Σ vᵢ, Σ rᵢ)` (dregg's `created_value_conservation`) means a verifier
  confirms the batch minted nothing **without learning a single amount**. **Only p\* opens** —
  and p\* is a *market* fact, not anyone's private input. There is **no decryption committee**
  (contrast Penumbra) and **no computing relayer** (contrast Renegade).
- **Proof — a STARK over the fold + the crossing.** The prover shows, in one succinct proof:
  (i) the aggregate `D, S` is the **faithful fold** of the committed orders (no drop / no insert /
  no reorder — `aggregate_sound`); (ii) `p*` is the **correct crossing** of `D, S`; (iii) the
  cleared allocation **conserves** per asset (`exact_clears_iff` / `clearing_conserves_per_asset`)
  and is **within each order's limits** (`clearing_respects_limits`). WHO traded is the nullifier
  layer's job; **WHAT cleared correctly** is this STARK. The proof rides dregg's existing
  recursion/aggregation layer — the aggregation *is* a fold, so it proves like the turn-fold.

### 2.2 Why it is cheap — aggregation-cost, not matching-cost

The naive framing ("match N private orders") lands you in **oblivious sort**: O(N log²N)
compare-swaps, each a **bootstrap** — the expensive FHE corner. The fhEgg framing lands you in
**aggregation + one crossing**:

```
   naive private matching:   O(N log²N)  bootstraps           (comparison-dominated)
   fhEgg kernel:             O(N·K)      additions  +  O(K)  comparisons
                                ╰─ bootstrap-free ─╯     ╰─ N-independent ─╯
```

The N-dependent work never touches a comparison; the comparison work never depends on N. At Zama's
numbers (addition ≈ µs, PBS ≈ 1 ms) this is the difference between "free" and "the bill." This is
the precise sense in which **the expensive part of private matching evaporates**.

### 2.3 Why it is composable + coordination-lite — the turn-parallel, made concrete

| turn-kernel property | fhEgg-kernel mirror | why |
|---|---|---|
| a turn refines a kernel step, carries a receipt | a clearing folds order-increments, carries a mark | both are **increments over owned state leaving a proof** |
| turns compose **associatively** (the accumulator left-fold) | batches fold **associatively** (`D = D_A ⊕ D_B`) | ⊕ is a monoid — sub-batches merge into one aggregate |
| attenuation is **order-independent** within a turn | order-increments are **order-independent** (CRDT) | ⊕ is **commutative** — no consensus on arrival order |
| the STARK-fold aggregates turns into one proof | the STARK aggregates the fold+crossing into one proof | the aggregation **is** a fold — same recursion apex |
| coordination-lite: mergeable increments, no lock | coordination-lite: mergeable curves, no matching engine | commutativity kills the ordering authority |

The turn-kernel makes ZK + coordination natural because a turn is *an associative fold of
proof-carrying increments*. The fhEgg-kernel makes **private clearing** natural for the identical
reason: a clearing is *an associative, commutative, homomorphic fold of order-increments*, crossed
once. Same shape, same recursion layer, same "reveal only the receipt" discipline — the receipt is
just the **clearing mark** instead of a turn hash.

### 2.4 Mapping to dregg's existing pieces (all real, most PROVED)

| fhEgg component | dregg primitive | file |
|---|---|---|
| aggregate-curve object (homomorphic 𝔸) | `ValueCommitment` with `impl Add/Sub/Neg` (Pedersen) | `cell-crypto/src/value_commitment.rs` |
| commutative-monoid fold (the operation) | `pool = foldr (·⊗·) 𝟙` + the online left-fold `Accumulator::accumulate` | `metatheory/Market/Clearing.lean`; `circuit-prove/src/accumulator.rs` |
| order-independence (CRDT / commutativity) | `pool_as_perm` (reorder leaves the pool bundle unchanged) | `metatheory/Market/Aggregation.lean` |
| the additive homomorphism (Σ distributes) | `toBal_mul : toBal (b*b') a = toBal b a + toBal b' a` | `metatheory/Market/Clearing.lean` |
| **clearing = Σ-balance** (the crossing, as characterization) | `exact_clears_iff : clears ↔ pools balance`; `clearing_conserves_per_asset` | `metatheory/Market/Clearing.lean` |
| aggregation faithfulness (no drop/insert/reorder) | `aggregate_sound` (permutation + priority-sorted) | `metatheory/Market/Aggregation.lean` |
| **privacy: conserve over commitments, decrypt nothing** | `created_value_conservation : Σ commit(vᵢ,rᵢ) = commit(Σvᵢ,Σrᵢ)`; `shielded_ring_clears` | `Dregg2/Exec/ShieldedValue.lean`; `metatheory/Market/ShieldedClearing.lean` |
| STARK over the fold (the proof apex) | `joint_turn_aggregation` / `Accumulator::finalize` (recursion) | `circuit-prove/src/joint_turn_aggregation.rs`, `.../accumulator.rs` |
| shielded positions (hidden owner/value/asset) | shielded pool + stealth addresses | `circuit-prove/src/shielded/pool.rs`; `cell-crypto/src/stealth.rs` |
| settlement (the fold onto the ledger) | `settle_ring_verified` / `settleRing` (per-asset conserving, atomic) | `intent/src/verified_settle.rs`; `Dregg2/Intent/Ring.lean` |
| cross-chain proof-settle | Groth16/BN254 verifier contracts | `cosmos-settlement/`, `solana-settlement/` |

The striking fact: **the kernel is not a new build — it is the name of a decomposition dregg has
already proved.** `exact_clears_iff` says clearability *is* Σ-balance; `toBal_mul` is the additive
homomorphism; `ShieldedValue.created_value_conservation` is "conserve on commitments, decrypt
nothing." The fhEgg kernel is the statement that *these three, folded, are the whole of private
uniform-price clearing.*

---

## 3. The featureset

### 3.1 A full private limit-order-book call auction (aggregation-tractable ✓)

Each limit order is exactly **one curve increment** (§2.1b); the aggregate curve **is** the book;
clearing is the crossing. This is a *complete* LOB semantics for the **batch / call-auction**
mechanism:

- **Limit orders** — the step increment at the limit price. Native.
- **Market orders** — a limit at the extreme bucket (`ℓ = p_K` bid / `p₁` ask). Native.
- **Uniform clearing price** — the crossing p\* (`Market/Optimality.lean`: `uniform_price_optimal`,
  no-arbitrage / envy-free at p\*, PROVED at model scope).
- **Price-time / batch priority** — the aggregation is priority-faithful (`aggregate_sound`).
- **Partial fills at p\*** — the aggregate volume `V* = S(p*)` fills; the marginal bucket may
  over-subscribe → **pro-rata rationing** (the one honest extra step, §4).

**What it is *not*:** a *continuous* double-auction (CLOB with continuous-time matching, cancels,
price-time priority across a live book) is **inherently sequential/ordered** — it is *not* an
aggregation, because outcome depends on arrival order. The fhEgg kernel is a **frequent-batch
uniform-price call auction** (Budish–Cramton–Shim FBA). This is a **feature, not a limitation**:
FBA converts speed competition into price competition and kills mechanical latency-arb / sniping.
DrEX is a frequent-batch auction *by design*; state it plainly rather than pretend to be a CLOB.

### 3.2 The products the private-fair-clearing MARK unlocks

The clearing price p\* is a **private-but-attested fair oracle**: computed from sealed orders with
no viewer, carrying a STARK that it is the honest crossing, and **manipulation-resistant** because
there is no public book to spoof and no committee to bribe. That mark is the primitive the rest of
the exchange composes against — all over **shielded positions** (`shielded/pool.rs`), all
**proof-settled** (`verified_settle`):

- **Options** — settle intrinsic value = `max(0, mark − strike)` against the proof-carrying mark;
  strike-vs-mark is a comparison against p\*, not a re-run of the book. (`CONDITIONAL-VAULT.md`,
  `DERIVATIVE-MATCHING-DESIGN.md` are the existing dregg surfaces.)
- **Perps** — funding rate off `mark − index`; positions shielded, PnL proof-settled. The private
  mark is exactly the funding oracle a perp needs, without a manipulable public last-trade.
- **Lending** — the mark as the **private, manipulation-resistant liquidation oracle**
  (`Market/Lending.lean`). The dominant DeFi-lending exploit is oracle manipulation of a thin
  public pool; a sealed-batch mark with a correctness proof removes the surface.
- **Structured products / baskets** — a portfolio marks and settles against the vector of
  clearing prices; `Market/Liquidity.lean` (`pool_solvent_forever`) is the standing-pool floor.

The unifying statement: **one private-fair mark, proved once, is the settlement reference for a
whole product surface** — the fhEgg analogue of "one turn-receipt anchors a whole state
transition."

### 3.3 The multilateral cross-asset ring — folded IN, not walled off

The pessimistic framing: multilateral cross-asset clearing (A wants B, B wants C, C wants A — a
Top-Trading-Cycle) is **graph-matching**, and graph-matching *feels* NP / combinatorial, hence
"not aggregation, needs its own throwaway machinery." **That framing is wrong**, and the right
algebra brings the ring substantially into the fhEgg kernel.

**The structure.** A multilateral clearing is a **circulation**: a flow `f` on the trade graph
that **conserves at every node** (`∂f = 0`, in = out for every participant/asset). The space of
circulations is the **cycle space `Z = ker ∂`** — the kernel of the boundary/incidence map — a
**linear subspace** (graph homology H₁, dimension = |E| − |V| + #components). Netting is the
**coequalizer**: the quotient of the gross flow by the cycle relations (gross → net collapses
exactly the boundaries). Clearing = find a circulation in `Z ∩ box`, where `box` is the per-order
offer/want min–max constraints, **maximizing traded volume** — a **min-cost / max-volume flow LP**.
Flow LPs are **poly-time** (NOT NP-hard); network-flow is P.

**Why this is (mostly) FHE-cheap.** The load-bearing facts:

1. **The cycle basis is PUBLIC.** *Who can trade what* (the graph topology) is structural, not
   secret — only the **flow amounts** on edges are private. So the incidence matrix `∂` and a
   cycle basis `B` are public constants. Projecting onto `Z`, computing net positions
   (`net = ∂f`), and verifying conservation (`∂f = 0`) are **homomorphic linear algebra over a
   public matrix and private (committed) amounts** — i.e. **linear combinations of ciphertexts**,
   the *bootstrap-free* primitive. Cheap, exactly like the §2 fold. This is Penumbra's homomorphic
   sum generalized from a scalar to a **vector in the cycle space**.
2. **For EXACT all-or-nothing intents the optimization vanishes.** dregg's kernel models orders as
   exact intents (you get precisely your `wanted` or nothing — `ExactBook`). Then
   **`exact_clears_iff`** proves a clearing exists **iff the pools balance**, and **`exact_alloc_eq`**
   proves the allocation is **pinned** (everyone gets exactly their wanted). There is **no LP, no
   search, no optimization** — clearing is a **pure homomorphic conservation check** over the
   committed offers/wants (`Σ commit = commit Σ`, `= 0`). This is the ring **fully inside** the
   fhEgg kernel: `shielded_ring_clears` already states it — *the ring clears over shielded notes
   with nothing decrypted*. The current live path (`solver.rs`: Johnson cycles + Shapley–Scarf TTC)
   is the **cleartext** finder; the private version is the homomorphic conservation check on the
   found cycle's commitments.

**The residual hard core (named honestly).** When orders admit **partial fills** and the market
**maximizes total volume** across many candidate cycles with binding box constraints, you are back
to a genuine **optimization**: a max-volume circulation LP whose *binding set* and *pivot path* are
**data-dependent**. Doing that **obliviously** (so the control flow leaks nothing) is the real
frontier:

- **Aly & Van Vyve**, *Securely Solving Classical Network Flow Problems* — secure **minimum-cost
  circulation** via **MMCC (minimum-mean-cycle-canceling)** in MPC. Existence proof that oblivious
  network-flow is *poly-time realizable*.
- **Toft**, *Solving Linear Programs Using MPC* (FC'09) — **oblivious simplex**: masked pivoting,
  ≈ **O(nm) secure multiplications per pivot**; number of pivots must be **padded to worst-case**
  or it leaks.
- **Interior-point**: **O(√n · log(1/ε))** iterations, each a secure linear solve — smoother
  round-count, fixed-point arithmetic.

So the ring **is not hard the way it looked** — it is a poly-time flow LP whose *linear-algebra and
conservation core is homomorphically cheap over a public basis*, and which **collapses to a free
conservation check for exact intents**. The only genuinely-costly residue is **oblivious
volume-maximizing partial-fill selection**, which is poly-time with real protocols but is the
scale frontier (worst-case padding = the perf/leakage tax). **Verdict: the multilateral ring folds
into the fhEgg kernel for exact intents (PROVED, `shielded_ring_clears`); the partial-fill
volume-max case is a poly-time oblivious-LP frontier, not a combinatorial wall.**

---

## 4. Honest feasibility envelope

| Regime | Tractability | Basis |
|---|---|---|
| **Single-pair uniform-price call auction**, N ≈ 10³ orders, K ≈ 10²–10³ price buckets | **Real-soon / already-real.** Cost = O(N·K) bootstrap-free additions + O(K) crossing. | Penumbra runs additive aggregation **per block on mainnet**; Cryptobazaar **128×1024 < 0.5 s**; Zama shipped a live homomorphic clearing-price auction (2025). |
| **Fine price resolution** (large K) | **Linear cost wall.** K is the true cost driver, not N. | O(N·K) additions + O(K) crossing scale linearly in K; pick K to the asset's tick, use SIMD packing / a coarse→fine two-pass crossing. |
| **Marginal pro-rata rationing** at the exact clearing bucket | **One extra private step (NEAR).** | The crossing gives p\* and V\* cheaply; splitting the over-subscribed marginal bucket needs a small private division, or reveal only the *marginal-bucket* aggregate. Honest named seam. |
| **Multilateral ring, exact all-or-nothing intents** | **Tractable, PROVED at spec.** Pure homomorphic conservation check, no LP. | `exact_clears_iff` + `exact_alloc_eq` + `shielded_ring_clears`; conservation on commitments (`created_value_conservation`). |
| **Multilateral ring, partial-fill volume-max, private, at scale** | **RESEARCH frontier — poly-time, not exponential.** | Oblivious flow-LP (Aly–Van Vyve secure MCC; Toft secure simplex O(nm)/pivot; interior-point O(√n log 1/ε)); worst-case pivot padding is the tax. Small rings clear in clear today (`solver.rs`). |
| **Continuous CLOB** (live matching, cancels, price-time across a live book) | **Out of scope by construction.** | Inherently order-dependent → not an aggregation. DrEX is a **frequent-batch** auction by design (Budish FBA); this is a feature (kills latency-arb), stated plainly. |
| **Post-quantum aggregate layer** | **Named residual.** | Today's `ValueCommitment` (Pedersen) and Penumbra-style ElGamal are **classical DLog**. A PQ fold needs **lattice-additive** commitments/ciphertexts (BGV/Regev-additive). dregg's *signature* layer is already PQ-hybrid (ed25519 + ML-DSA-65); the *homomorphic* layer is the open PQ upgrade. |

**Where it genuinely breaks (no spin):** (1) fine-grained price resolution costs linearly — you
cannot have both N-independence *and* arbitrarily fine K for free; (2) exact-tie marginal rationing
needs a labeled extra step; (3) private, scaled, volume-maximizing multilateral partial-fill is a
real research problem (poly-time, but oblivious-LP overhead + worst-case padding); (4) the PQ
homomorphic layer is unbuilt. **What does NOT break:** the core claim — single-pair private
uniform-price clearing is dominated by cheap additive aggregation + a tiny crossing, is tractable
now at market-relevant sizes, requires **no decryption committee and no computing relayer**, and is
**already proved in dregg's Lean** modulo the circuit realization of the aggregation+crossing STARK
(the one MEDIUM→RESEARCH build named in `ShieldedClearing.lean §4b`).

---

## 5. The verdict on the hypothesis

**Confirmed, and sharpened.** The aggregation-monoid **is** the right kernel: a uniform-price call
auction is a commutative-monoid fold of order-increments crossed once, the expensive matching cost
evaporates into cheap additive aggregation, and the whole thing is composable (associative fold),
coordination-lite (commutative/CRDT increments), and STARK-provable (a proof over the fold+crossing
that reveals only the price). The sharpening the research forced:

1. **The aggregate is a price-indexed *curve* (vector), not a scalar net.** The pure "sum
   everything" reveals only net volume; a *clearing price* needs the cumulative curve. But the
   curve is still an additive fold (bucketwise), so the cheap-aggregation claim survives intact —
   this is exactly Cryptobazaar's unary-encoding + Penumbra's limb-vector, generalized.
2. **The privacy is stronger than "additive-HE + threshold-decrypt."** dregg's move is *decrypt
   nothing*: conserve on commitments (`Σ commit = commit Σ`), open only p\*. This removes the
   decryption committee that even Penumbra keeps — the field's best privacy, improved.
3. **The multilateral ring is not a different, harder kernel — it is the same kernel over the
   cycle space.** Circulation = ker ∂ (linear, public basis); netting = coequalizer; exact intents
   → free conservation check; only partial-fill volume-max is a poly-time oblivious-LP residue.

**Is there a better kernel?** No cleaner one surfaced. The alternatives are strictly worse or
narrower: general-comparison **FHE sorting** (the O(N log²N)-bootstrap trap the kernel exists to
avoid), **MPC matching** (Renegade — a computing viewer, no succinct proof), **FE for the whole
clearing rule** (inner-product FE is linear-only; comparison FE is inefficient), **TEE** (a hardware
viewer + side channels). The **aggregation-fold + monotone-crossing + homomorphic-conservation +
STARK-over-the-fold** decomposition is the one that (a) puts the work in the cheap half of the
crypto, (b) has the same algebra as dregg's turn-kernel so it composes into the existing recursion
and settlement layers, and (c) is **already largely proved**. That is the fhEgg kernel.

---

## 6. Sources

**IACR ePrint (read full-text from the local mirror):**
- BOREALIS — Blass & Kerschbaum, ePrint **2019/276** (ASIA CCS'20): additively-homomorphic ECC-
  ElGamal k-th-rank, **4 rounds constant**, n=200/ℓ=32 under one block interval.
- SEAL — Bag, Hao, Shahandashti, Ray, ePrint **2019/1332**: auctioneer-free, **O(c)** linear,
  publicly verifiable.
- FE for inner products — Abdalla–Bourse–De Caro–Pointcheval, ePrint **2015/017**; Agrawal–Libert–
  Stehlé, ePrint **2015/608** (linear functionals only).

**Web / Kagi:**
- Cryptobazaar — Novakovic, Kavousi, Gurkan, Jovanovic, ePrint **2024/1410** (NDSS'25): unary-
  encoded bids + distributed OR aggregation, **128 bidders × 1024 prices < 0.5 s**,
  single untrusted auctioneer, (p+1)-st price. <https://eprint.iacr.org/2024/1410>
- Penumbra homomorphic threshold encryption (ZSwap flow encryption): exponential-ElGamal, 4×16-bit
  limbs, aggregate-only threshold-decrypt, DLog LUT [0,2²³), 640 B/value.
  <https://protocol.penumbra.zone/main/crypto/flow-encryption/threshold-encryption.html> ·
  <https://protocol.penumbra.zone/main/concepts/batching_flows.html>
- Renegade — MPC (SPDZ) + collaborative zkSNARK `VALID MATCH MPC`.
  <https://help.renegade.fi/hc/en-us/articles/32529961385363> · <https://github.com/renegade-fi/renegade>
- CoW Protocol batch auctions / solver competition. <https://cow.fi/learn/understanding-batch-auctions>
- Zama fhEVM / TFHE numbers: 20+ TPS CPU, 189k+ bootstraps/s (8×H100), <1 ms PBS, live sealed-bid
  auction (2025). <https://www.zama.ai/products-and-services/fhevm> · Messari "Understanding Zama"
- Aly & Van Vyve, *Securely Solving Classical Network Flow Problems* (secure min-cost circulation via
  MMCC). Toft, *Solving Linear Programs Using MPC*, FC'09 (oblivious simplex, O(nm)/pivot).
  *Privacy Preserving Decentralized Netting*, FC'23 short paper.
- Clearing-as-Tarski-fixpoint / lattice liability networks: arXiv **2503.17836**, arXiv **2602.16387**;
  Knaster–Tarski. CRDT / commutative-monoid convergence (standard).

**dregg (this repo) — the kernel is already largely proved:**
- `metatheory/Market/Clearing.lean` — `pool` (the fold), `toBal_mul` (the additive homomorphism),
  `exact_clears_iff` (clearability = Σ-balance), `clearing_conserves_per_asset`.
- `metatheory/Market/Aggregation.lean` — `aggregate_sound`, `pool_as_perm` (CRDT / order-independence).
- `metatheory/Market/ShieldedClearing.lean` — `shielded_ring_clears` (decrypt nothing);
  `Dregg2/Exec/ShieldedValue.lean` — `created_value_conservation` (Σ commit = commit Σ).
- `cell-crypto/src/value_commitment.rs` — `ValueCommitment` (`impl Add/Sub/Neg`, the homomorphic 𝔸).
- `circuit-prove/src/accumulator.rs`, `.../joint_turn_aggregation.rs` — the STARK-over-the-fold apex.
- `intent/src/verified_settle.rs`, `Dregg2/Intent/Ring.lean` — conserving atomic settlement.
- `docs/deos/DREX-DESIGN.md` — the exchange this kernel sits inside (scholar survey §1, rung ladder).
