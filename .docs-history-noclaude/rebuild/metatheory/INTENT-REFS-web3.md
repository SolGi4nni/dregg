# INTENT-REFS — Intent-Centric web3, Solvers & MEV / Fair-Ordering (the state of the art we mean to surpass)

**Pillar:** *what already exists in the wild* for intent expression, matching/solving, and settlement — so we
know exactly what a formally-verified **intent-as-co-receipt + userspace-escrow + causal-time** stack would add.
**Companion to:** [`INTENT-AS-CO-RECEIPT.md`](./INTENT-AS-CO-RECEIPT.md) (the design spine; map onto its §N hooks).
**Siblings:** [`INTENT-REFS-resources.md`](./INTENT-REFS-resources.md) (the categorical resource/optics maths),
[`INTENT-REFS-optics.md`](./INTENT-REFS-optics.md).
**Research date:** 2026-06-03. Status: reference map, not a spec. READ-ONLY w.r.t. Lean.

Each entry: *what it is · URL · its intent/match/settle model · how it maps onto OR differs from our spine ·
**what WE add that it lacks.*** Where a claim of ours has a hard limit (the fair-ordering impossibilities), it is
called out honestly — `[LIMIT]`. Citations verified by fetching the abstract/spec; PDFs marked `[in library]`
are validated `%PDF` in `/Users/ember/dev/breadstuffs/pdfs/`.

> **One-line thesis of the comparison.** Every system below gets *one or two* of {intent expression, solver
> competition, MEV mitigation, conservation} as an **economic / operational** property enforced by a trusted
> operator, a token incentive, or a probabilistic ordering rule. **None of them makes any of these a
> machine-checked invariant of the settlement layer.** Our differentiator is not a new mechanism — most of these
> mechanisms are good — it is turning {conservation, no-frontrun, solver-soundness, escrow-release-correctness}
> from *things you trust the operator/validators to do* into *things the kernel proves*. The honest boundary is
> the fair-ordering impossibility cluster (refs 9–11): causal ordering **structurally excludes a definable class**
> of MEV but **cannot** deliver a perfectly-fair global total order — and we should claim exactly that, no more.

---

## TL;DR ranking

| # | Reference | What it is | Intent / match / settle model | What WE add it lacks | Spine hook |
|---|---|---|---|---|---|
| **1** | **Anoma** (whitepaper + Resource Machine) | full intent-centric "distributed OS"; the nearest neighbour to our entire thesis | intent = signed *partial* state transition · intent-gossip + permissionless solvers do counterparty-discovery · ARM resources (create-once/consume-once + resource-logic predicate + balance) · Typhon BFT + Ferveo threshold-decrypt batches | **machine-checked** conservation + solver-soundness; **causal/relativistic** time-typing (Anoma quantizes time via consensus — a global "now"); receipt⊣intent *adjunction* (Anoma has no dual-receipt) | §2,§3,§4,§5 |
| **2** | **CoW Protocol** (batch auctions) | intent-based DEX; the production reference for solver competition | signed order (intent) · ~5–30s **batch** · solvers compete, must find a CoW first then route residual · **uniform clearing price** per pair | provable conservation per settle; provable no-frontrun via causal order (CoW relies on *uniform price + trusted batch operator*, not a proof) | §3,§5 |
| **3** | **UniswapX** | off-chain signed orders + Dutch auction | signed order with decaying limit · fillers/"reactors" compete; optional RFQ pre-quote · on-chain settle | conservation as kernel invariant; *typed* deadline (Dutch decay is a wall-clock gas-race — exactly our `frame` vs `causal` confusion) | §2 face 4, §3, §5 |
| **4** | **1inch Fusion / Fusion+** | RFQ + Dutch auction "resolvers"; cross-chain | signed order, non-binding estimate · whitelisted **resolvers** auction-fill · escrow-based cross-chain (Fusion+ HTLC) | open permissionless solving with *proven* non-amplification; userspace-escrow with *proven* atomic release (Fusion+ HTLC ≈ our escrow but unverified) | §2 face 3, §3 |
| **5** | **ERC-4337** (account abstraction) | UserOperation + bundler + EntryPoint | `UserOperation` (a *transaction-shaped* intent) · bundlers batch · EntryPoint validates+executes | 4337 intents are still *imperative* (calldata), not a typed hole + predicate + escrow; no conservation law; no co-receipt | §1,§2,§6 |
| **6** | **ERC-7521** (generalized intents) | the *generalized*-intent EIP; same EntryPoint shape, pluggable "Intent Standards" | declarative intent w/ standards-defined satisfaction · solvers compete for "highest satisfaction" · EntryPoint orchestrates | 7521 is the closest EVM analogue of our pluggable matcher, but **satisfaction is unverified Solidity**; we make the predicate a `Prop` + the match a proof | §3,§6 |
| **7** | **SUAVE** (Flashbots) | decentralized sequencing / unified MEV mempool ("MEVM") | "preferences" (intents) · programmable builders/solvers as MEVM smart contracts · cross-domain block-building | SUAVE *organizes & auctions* MEV decentrally; we *structurally exclude a class of it* by causal ordering + conservation rather than re-selling it | §5 |
| **8** | **Penumbra / Osmosis+Ferveo** | shielded batch DEX / threshold-encrypted mempool | encrypt-then-batch · sealed-bid batch swap, only **net flow** revealed · threshold-decrypt after ordering | their no-frontrun is *cryptographic + economic* (DKG honesty, batch operator); ours is a *typed causal invariant* + verified conservation. Closest cousins to our sealed-bid auction (§5/§7) | §4,§5,§7 |
| **9** | **Order-Fairness / Aequitas** (Kelkar–Zhang–Goldfeder–Juels, CRYPTO'20) `[in library]` | the founding *formal* notion of order-fairness for BFT | γ-batch-order-fairness; receive-order-fairness | the source of our **honesty boundary**: defines what fair-ordering can mean and *proves* receive-order-fairness is unachievable (Condorcet) | §5 `[LIMIT]` |
| **10** | **Themis** (Kelkar et al. 2023) `[in library]` | fast, strong order-fairness; the practical Aequitas successor | γ-batch-order-fairness, O(n²), leader-based | the realizable target a fair-ordering layer would adopt *under* our causal model — and its limits bound our "no MEV" claim | §5 `[LIMIT]` |
| **11** | **Condorcet Attack** (Vafadar–Khabbazian 2023) `[in library]` | the sharpest *impossibility/attack* on batch-order-fairness | shows 2 honest txns suffice to weaponize Condorcet cycles | **the precise statement of what causal ordering CANNOT fix** — load-bearing for an honest "no-frontrun" claim | §5 `[LIMIT]` |
| 12 | **Quick Order Fairness** (Cachin et al.) · **SoK fair ordering** `[in library]` | differential order-fairness, optimal `n>3f`; survey | the cleaner realizability result + the map of the whole field | the realizable fair-ordering primitive + a literature anchor | §5 |

---

## 1. Anoma — intent-centric "distributed OS" + the Resource Machine — **the nearest neighbour, study hard**

- **What it is.** A full intent-centric architecture ("a unified architecture for full-stack decentralised
  applications"). This is the project closest to *our entire thesis*, and the resource model is **strikingly
  close to our resource-theory framing** (Coecke–Fritz convertibility, `INTENT-REFS-resources.md` #1).
- **URLs.** Whitepaper: <https://github.com/anoma/whitepaper> `[in library: anoma-whitepaper.md, pulled]`.
  Resource Machine: <https://anoma.net/research/rise-of-the-resource-machines>. Typhon/Heterogeneous-Paxos:
  cited in the whitepaper §Consensus; Ferveo: eprint 2022/898.
- **Intent / match / settle.**
  - **Intent** (whitepaper §Intents) = "a signed message that describes a **partial** state transition";
    "intents are partial and hence specific counterparties are not required." Anoma's own framing — *"intents
    as parts of transactions that require other direct or indirect parts as complements in order to form a final
    **balanced** transaction"* — **is our typed-hole-and-fill almost verbatim** (§1). Intents are opaque
    bytestrings at the architecture level; semantics fixed per-application.
  - **Match** = **intent gossip layer** (counterparty discovery) + **permissionless solvers** that "search the
    space of possible solutions … to find subsets of *combinable* intents to generate transactions." That
    "combine multiple partial intents into one balanced transaction" **is exactly our `∫^B` solver** (§3): the
    solver assembles a chain/bundle that closes the boundary.
  - **Settle.** Ferveo (DKG threshold) encryption of transactions → consensus orders ciphertexts → 2/3 decrypt
    → execute. **Data-availability domains** batch-decrypt "all at once after a time interval" → solvers compete
    "by a measurable criterion defined by the application" — i.e. their **anti-frontrun is threshold-encrypt +
    batch**, an economic/cryptographic device, not a typed causal fact.
  - **Anoma Resource Machine (ARM).** A resource is **immutable, created once, consumed once** (a state-change
    marker — *not* UTXO, *not* account); each carries a **resource logic** (predicate) that must evaluate true
    for create/consume; valid transactions **balance** (consumed vs created). This is **our intent's faces 1–2**
    (boundary + predicate) and the **conservation law** (§5) in their model — but ARM's balance is checked by the
    VM, not *proved* as a kernel invariant.
- **Map onto the spine.** Resource = our linear resource object; resource-logic = our `Predicate`; balanced
  transaction = our conserved fill; intent-as-partial-transition = our typed hole; solver = our coend matcher.
  Anoma is the *design* we are building the *proof* of.
- **What WE add that Anoma lacks.** (i) **Machine-checked** conservation + solver-soundness (Anoma's balance &
  solver correctness are VM/operator-trusted, not Lean-proved). (ii) The **receipt⊣intent adjunction** — Anoma has
  intents and transactions but **no dual receipt object**; our co-receipt unifies demand⊣supply. (iii) **Causal/
  relativistic time-typing** — Anoma *quantizes time via consensus* (a global "now" per concurrency domain) and
  its fairness is threshold-encryption; we refuse the global-now (§4) and make anti-frontrun a *lightcone fact*.
  (iv) **Userspace-escrow as a first-class proven object** (§2 face 3) — Anoma funds via resource balance, no
  escrow-release theorem.
- **Honest caveat.** Anoma is the most mature realization of this vision; our edge is *formal*, not conceptual.
  Read the whitepaper §Intents/§Solver/§Consensus and the ARM article before claiming novelty on the *model* —
  claim it on the *proof* and the *time-typing*.

## 2. CoW Protocol — batch auctions + solver competition — **the production solver benchmark**

- **What it is.** "Coincidence of Wants" — an intent-based DEX where users sign orders and a **batch auction**
  with **competing solvers** settles them. The reference implementation of solver competition in production.
- **URLs.** <https://docs.cow.fi/cow-protocol/concepts/how-it-works/coincidence-of-wants> ·
  <https://docs.cow.fi/cow-protocol/reference/core/auctions/competition-rules> · Fair Combinatorial Batch
  Auction: <https://docs.cow.fi/cow-protocol/concepts/introduction/fair-combinatorial-auction>.
- **Intent / match / settle.** Order = signed limit intent (give A, want ≥ C). Orders collected for a batch
  (~5–30s). **Solvers** (DEX aggregators, MMs, searchers) bid a *solution*: which orders clear, at what prices,
  through which liquidity. Winner = max surplus above limit prices. **Uniform clearing price** per token pair in a
  batch ⇒ *"transaction reordering is useless"* — the explicit anti-MEV device.
- **Map onto the spine.** A batch = a multilateral fill; "find a CoW first, then route residual through AMMs" is
  *exactly* the `∫^B` coend (§3): bilateral match (CoW) is the base case, AMM-routing is the through-`B` step.
  Uniform-price = a fairness tie-break over a *batch* (our "fair tie-break over the lace partial order", §5).
- **What WE add that CoW lacks.** CoW's conservation and "no internal reordering MEV" rest on a **trusted batch
  operator + the uniform-price rule**, not a proof: a solver *could* mis-price or extract, and CoW polices this
  by *competition + ex-post solver slashing/ranking*, not by a kernel invariant. We make (i) **conservation per
  settle** a kernel theorem (no value minted in the match), and (ii) **no-frontrun** a *causal* type rather than
  an emergent property of batching. CoW's batch is a *discrete-time* simultaneity surface (every order in the
  batch is "simultaneous"); ours is the causal partial order, which needs no synchronized batch window.

## 3. UniswapX — off-chain signed orders + Dutch auction — **the decaying-limit intent**

- **What it is.** Off-chain signed orders filled by competing "fillers"/reactors via an on-chain **Dutch
  auction** (limit decays over a 30–60s window), with an optional RFQ pre-quote phase on Ethereum.
- **URLs.** Whitepaper: <https://app.uniswap.org/whitepaper-uniswapx.pdf> · Auction types:
  <https://docs.uniswap.org/contracts/uniswapx/auctiontypes>.
- **Intent / match / settle.** Intent = signed order with a *decaying* acceptable output. Match = whichever
  filler executes first at the current decayed price (a gas race, optionally pre-empted by RFQ). Settle on-chain
  via the reactor contract; cross-chain variant escrows.
- **Map onto the spine.** The decaying limit is a **time-typed validity window** (§2 face 4) — but it is the
  *wrong* type: the Dutch decay presupposes a global wall-clock and resolves by a **gas race** (the filler who
  lands the tx first wins), which is *precisely the simultaneity-surface capture* we call MEV. UniswapX is the
  clearest illustration of **why §4's `causal` vs `frame` distinction matters**: a Dutch auction is a `frame`
  device used where the protocol *wishes* it had a `causal` ordering.
- **What WE add.** (i) Conservation as a kernel invariant. (ii) A *typed* deadline: `frame_within(F,T,±δ)` for the
  honest wall-clock part, `causal_after(reveal)` for anti-frontrun — so "who fills first" is a lightcone fact on
  the lace, not whoever bribes the builder. (iii) An exchange (multi-hop `∫^B`) instead of single-filler fills.

## 4. 1inch Fusion / Fusion+ — RFQ + resolver Dutch auction — **whitelisted solver + cross-chain escrow**

- **What it is.** Gasless signed orders filled by whitelisted **resolvers** in a Dutch auction; **Fusion+** adds
  cross-chain atomic swaps via HTLC-style escrow.
- **URLs.** 1inch Fusion docs (<https://docs.1inch.io>); comparison: <https://www.inferara.com/en/blog/pocket-exchange/>.
- **Intent / match / settle.** Order = signed, with a *non-binding* estimate; final price found during the
  auction (resolvers compete between start/reserve price). Settlement on-chain; Fusion+ escrows on both chains and
  releases on secret reveal (HTLC).
- **Map onto the spine.** Fusion+'s HTLC escrow is the closest production analogue of our **userspace-escrow**
  (§2 face 3): assets are held and released exactly on the discharging event. The resolver set is a *permissioned*
  solver pool.
- **What WE add.** (i) **Permissionless** solving with a *proven* **non-amplification** (no solver mints rights
  or value — we already have `granted ≤ held`, task #94/#112). (ii) Escrow **release-correctness as a theorem**
  (HTLC atomicity is assumed-correct Solidity; ours is the proven escrow inheritance, §7). (iii) The HTLC secret-
  reveal ordering is exactly a `causal_after(reveal)` fact in our model — provable, not socially-enforced.

## 5. ERC-4337 — account abstraction — **the imperative "intent" baseline**

- **What it is.** Account abstraction: a `UserOperation` (transaction-shaped object) validated/executed by an
  `EntryPoint` singleton, batched by **bundlers**, with `Paymaster`/`Aggregator` roles.
- **URLs.** <https://docs.erc4337.io> · EIP: <https://eips.ethereum.org/EIPS/eip-4337>.
- **Intent / match / settle.** A `UserOperation` is *not* a true intent: it carries **imperative calldata**
  (the exact execution), a separate mempool, bundler batching, EntryPoint dispatch. "Intent" here = "a tx my
  smart wallet authorizes," not "a typed hole + predicate + escrow."
- **Map onto the spine.** This is the **dregg1-`expiry`-baseline analogue** (§6): a flat, imperative request with
  a deadline and a funding bond (the Paymaster), missing the four Platonic faces.
- **What WE add.** Everything in §2/§6 of the spine: a *declarative* typed hole, a `Prop` predicate, first-class
  escrow, a typed causal/frame validity — versus 4337's "calldata + paymaster."

## 6. ERC-7521 — generalized intents — **the EVM's pluggable matcher (closest standard)**

- **What it is.** A **generalized-intent** standard reusing the EntryPoint pattern with pluggable **Intent
  Standards** (each defines its own satisfaction logic); solvers compete to maximize "user satisfaction."
- **URLs.** EIP: <https://eips.ethereum.org/EIPS/eip-7521> · <https://blog.essential.builders/introducing-erc-7521-generalized-intents/>
  · spec: <https://github.com/ethereum/ERCs/blob/master/ERCS/erc-7521.md>.
- **Intent / match / settle.** Declarative intent; satisfaction defined by an *Intent Standard* contract; the
  EntryPoint orchestrates; **solvers** (bundler-analogues) compete for the highest-satisfaction solution. This is
  the EVM construct *closest* to our pluggable, bounded, domain-specific matcher
  (`pdfs/LEARNINGS-intent-matching.md`: "matcher = a bounded pluggable DSL solver, never a general matcher").
- **Map onto the spine.** Intent Standard ≈ our per-application `Predicate` + match-fragment; solver competition ≈
  our coend assembly; EntryPoint ≈ the kernel discharge.
- **What WE add.** 7521's "satisfaction" is **unverified Solidity** evaluated at runtime — the predicate is code,
  not a `Prop`, and a buggy/adversarial Intent Standard can mis-settle. We make the **predicate a proposition**,
  the **match a proof of `A ⪰ C`**, and **conservation a kernel invariant** the Intent Standard cannot violate.
  7521 is the right *shape*; we add the *soundness*.

## 7. SUAVE (Flashbots) — decentralized sequencing / MEVM — **MEV organized vs MEV excluded**

- **What it is.** "Single Unifying Auction for Value Expression": a unified, decentralized mempool + block-builder
  network and a **decentralized sequencing layer**, with an **MEVM** that lets builders/solvers/relays be written
  as smart contracts.
- **URLs.** <https://writings.flashbots.net/the-future-of-mev-is-suave> ·
  <https://writings.flashbots.net/mevm-suave-centauri-and-beyond> · specs: <https://github.com/flashbots/suave-specs>.
- **Intent / match / settle.** Users express **preferences** (intents); programmable solvers/builders in the MEVM
  compute solutions; cross-domain block-building captures (and redistributes) MEV. SUAVE's premise is that MEV is
  *inevitable*, so the goal is to **decentralize its extraction and auction it transparently**.
- **Map onto the spine.** SUAVE is the *anti-thesis framing* worth citing: it accepts the simultaneity surface as
  a market and sells access to it fairly. Our claim (§5) is the dual — a **causal model has no global order to
  capture**, so a *definable class* of MEV is excluded rather than auctioned.
- **What WE add / honest contrast.** We do **not** claim to abolish all MEV (see refs 9–11). We claim: under
  causal ordering, **reorder-MEV within the lace's partial order is structurally impossible**, and **conservation
  excludes value-extraction-by-minting**; the *residual* MEV (Condorcet-trappable, cross-domain, statistical) is
  exactly what SUAVE-style auctions still address. SUAVE and a causal kernel are **complementary**: causal order
  shrinks the surface; an auction handles what remains.

## 8. Penumbra / Osmosis+Ferveo — shielded batch swaps + threshold-encrypted mempool — **our sealed-bid cousin**

- **What it is.** **Penumbra**: shielded DeFi with **sealed-bid batch swaps** (per block, only the *net flow* of a
  pair is revealed; positions created anonymously). **Osmosis/Ferveo**: a **threshold-encrypted mempool** (encrypt
  tx → order ciphertext → threshold-decrypt) for BFT chains.
- **URLs.** Penumbra protocol: <https://protocol.penumbra.zone> · Ferveo: <https://eprint.iacr.org/2022/898> ·
  mempool-privacy economics: <https://arxiv.org/abs/2307.10878>.
- **Intent / match / settle.** Encrypt-then-batch: trades are hidden until *after* ordering, then batch-cleared at
  one price (Penumbra) or decrypted post-order (Ferveo). Frontrunning is prevented because the adversary **cannot
  see the trade in time to react** and the batch erases intra-batch ordering.
- **Map onto the spine.** This is the **direct production analogue of our gallery sealed-bid auction** (§5/§7):
  commit (encrypted) → reveal-after-order → batch settle, with "only net flow revealed" ≈ our conservation-only-
  observable settle. Their *no-reveal-before-commit* is *cryptographic*; ours is *causal* (`causal_after(reveal)`
  on the lace) + sealed-bid privacy as a Lean property.
- **What WE add.** (i) The no-frontrun guarantee as a **typed causal invariant** + a **proof**, not "trust the DKG
  committee + the batch boundary." (ii) **Conservation across the settle** as a kernel theorem. (iii) Penumbra/
  Ferveo still order *ciphertexts* via consensus (a global-now batch); our causal model needs no synchronized
  global batch window — the partial order suffices. These two are the *best targets to benchmark our auction
  against*.

---

## 9–11. MEV & fair-ordering — **the honesty boundary: what "no MEV" can and cannot mean** `[LIMIT]`

This cluster is **load-bearing**: it tells us the *exact* limit of the §5 claim. Be precise — overclaiming "no
MEV" here would be dishonest, and the impossibility is a *theorem*, not a missing feature.

### 9. Kelkar, Zhang, Goldfeder, Juels — *Order-Fairness for Byzantine Consensus* (Aequitas), CRYPTO 2020

- **URLs.** eprint <https://eprint.iacr.org/2020/269> `[in library: aequitas-order-fairness-byzantine-consensus-2020-269.pdf, pulled]`
  · LNCS 12172 pp. 451–480, DOI 10.1007/978-3-030-56877-1_16.
- **What it proves.** Introduces a **third** consensus property beyond consistency+liveness: **transaction
  order-fairness**. Defines **receive-order-fairness** ("if every honest node received tx before tx′, tx is
  ordered before tx′") and shows it is **unachievable** in general — because honest receive-orders can form a
  **Condorcet cycle** (tx≺tx′, tx′≺tx″, tx″≺tx, a majority each way) with **no consistent total order**. The
  realizable relaxation is **γ-batch-order-fairness**: if a γ-fraction of nodes received tx before tx′, then tx is
  output in a batch *no later than* tx′ (cyclically-dependent txns share a batch). **Aequitas** is the protocol
  family achieving it.
- **Why it matters for us.** This is the precise statement of *what a causal/fair ordering layer can deliver*.
  Our `causal_after` lace order delivers something **stronger and cleaner** for the *anti-frontrun* case (a
  happens-before fact admits no cycle by acyclicity of the blocklace), **but** for *unordered concurrent* intents
  there is genuinely **no fair total order to impose** — the honest move is a *batch* + a *transparent tie-break*,
  exactly as §5 says ("respect the partial order + a fair tie-break"). We inherit the Condorcet limit on the
  *tie-break*, not on the happens-before part.

### 10. Kelkar et al. — *Themis: Fast, Strong Order-Fairness in Byzantine Consensus* (2023)

- **URLs.** eprint <https://eprint.iacr.org/2021/1465> `[in library: themis-order-fairness-byzantine-consensus-2021-1465.pdf]`.
- **What it is.** The practical successor to Aequitas: same **γ-batch-order-fairness**, but **O(n²)** comms
  (Aequitas was O(n³)), fixes Aequitas's liveness problem, via *batch unspooling / deferred ordering / stronger
  intra-batch guarantees*. The realizable fair-ordering primitive a deployed system would actually pick.
- **For us.** If/when a dregg fair-ordering layer is needed *on top of* the causal lace, Themis is the reference
  target — and its `γ` parameter bounds how strong our tie-break fairness can be claimed.

### 11. Vafadar, Khabbazian — *Condorcet Attack Against Fair Transaction Ordering* (2023)

- **URLs.** <https://arxiv.org/abs/2306.15743> `[in library: condorcet-attack-fair-transaction-ordering-2306.15743.pdf, pulled]`.
- **What it proves (the sharp result).** An adversary can **defeat batch-order-fairness** — "the strongest notion
  of fair ordering proposed to date" — using **only two legitimate transactions**, *even with all nodes honest*.
  Mechanism: the exception that lets Condorcet-cycle txns share a batch (where order-fairness does **not** apply)
  can be **deliberately weaponized** to trap target transactions — even ones submitted at very different times —
  into an "unorderable" batch, then reorder them at will.
- **Why it is the most important honesty anchor.** It says: **batch-order-fairness is not a no-MEV guarantee.**
  Any claim of ours of the form "fair ordering ⇒ no frontrun" must be scoped to the part that is a *happens-before
  fact on the lace* (which **is** immune — no cycle can form on an acyclic causal DAG), and must **not** extend to
  the tie-break over concurrent intents (which **is** Condorcet-attackable). The correct dregg claim:
  > Causal ordering makes **reorder-MEV of causally-ordered events** structurally impossible (a lightcone fact),
  > and conservation makes **mint-MEV** impossible; it does **not** and **cannot** make the tie-break over
  > *genuinely concurrent* intents perfectly fair — that is Condorcet-bounded, and we adopt a transparent,
  > attested tie-break (best realizable: γ-batch-order-fairness à la Themis) for that residue.

### 12. Adjacent (anchors, not re-analyzed)

- **Cachin, Mihajlović, Mikulić — *Quick Order Fairness*** (arXiv 2112.06615; impl 2312.13107): **differential
  order-fairness** with **optimal resilience `n > 3f`** — the cleanest realizability result; the primitive to
  reuse if we build a fair-ordering layer.
- **SoK: Consensus & Fair Message Ordering** (arXiv 2411.09981) `[in library: sok-consensus-fair-message-ordering-2411.09981.pdf]`:
  the survey that maps the whole field (receive-order / batch-order / differential / blind-order via encryption) —
  the literature anchor for §5.
- **Penumbra/Ferveo (ref 8)** are the *blind-order-fairness* (encryption-based) branch of this same SoK taxonomy:
  encrypt to defeat the adversary's information rather than to fix the order — *complementary* to causal ordering.

---

## DeFi primitives to target first — each with the specific property it would prove

Ordered by leverage (smallest honest theorem first); each is `intent + escrow + time + matching + conservation`
(spine §5) and validates one named guarantee. The **gallery sealed-bid auction** is the chosen first instance
(spine §7) because it exercises *all* faces at once.

| Order | Primitive | Intent-as-co-receipt shape | The specific property to PROVE | Why it's the right rung |
|---|---|---|---|---|
| **1** | **Limit order / swap** (bilateral) | intent(give A, want ≥C, price≥p) + escrow(A) + `causal` validity + bilateral match | **conservation across the fill** (`Σ_k` invariant, no value minted) **+** **no-frontrun = `causal_after(commit)`** (a lightcone fact, not a gas race) | the smallest honest "intent matches" theorem; needs *zero* coend (ref `INTENT-REFS-resources.md` Phase 0); directly beats UniswapX's Dutch gas-race |
| **2** | **Sealed-bid auction** (the gallery) ★ | sealed-bid intents + escrow(bid) + `causal` reveal-order + winner-`Predicate` | **conservation** + **sealed-bid privacy** + **provable no-reveal-before-commit** (`causal_after`) + **userspace-escrow ≥ kernel-escrow** | the spine's chosen first instance (§7); benchmarks directly against Penumbra/Ferveo but with a *proof* instead of a DKG-trust assumption |
| **3** | **AMM as a standing offer** | a *standing* Offer cell-program filling any swap on a pricing curve; multi-hop via `∫^B` | **curve invariant preserved** under every fill **+** **conservation** **+** **router soundness** (the coend assembly type-checks/conserves) | turns the matcher into an *exchange* (spine §3); the `∫^B` router is multi-hop by construction (beats CoW's "CoW-then-route" being operator-trusted) |
| **4** | **Lending** | intent(lend A, want A+interest by deadline) + escrow + **`frame`** deadline | **interest is honestly wall-clock** (attested `frame_within(F,T,±δ)`, δ carried) **+** **liquidation as a typed causal/frame condition** + conservation | the primitive that *forces* the `causal` vs `frame` distinction to do real work (§4); proves we model wall-clock honestly, not by pretending it's causal |

★ = chosen first instance. Build order rationale: rung 1 needs only the convertibility preorder (`a ⪰ c`) and
the conservation monotone — *pure mathlib reuse*; rung 2 adds escrow + the causal reveal-order (the keystone
proof that validates the whole stack, spine §7); rungs 3–4 add the coend solver and the `frame` time-authority.

---

## What we provably add — and the honest line we will not cross

**Add (machine-checked, none of the systems above has these as proofs):**
1. **Conservation per settle** — a kernel invariant `Σ_k` (no value minted in any match/fill). *vs* CoW/UniswapX/
   Anoma where balance is VM/operator-enforced, not proved.
2. **No-frontrun as a causal type** — `causal_after(reveal)` is a happens-before fact on the acyclic blocklace;
   no Condorcet cycle can form on a causal DAG, so reorder-MEV of *causally-ordered* events is structurally
   excluded. *vs* threshold-encryption (Penumbra/Ferveo) or batch-uniform-price (CoW) which are
   cryptographic/economic devices.
3. **Solver-soundness / non-amplification** — the coend match is proved to type-check and conserve; no solver
   mints rights or value (`granted ≤ held`, already proved). *vs* 7521/CoW solvers whose correctness is
   competition-policed Solidity.
4. **Escrow-release correctness** — userspace-escrow releases *exactly* on the discharging receipt, as a theorem.
   *vs* Fusion+ HTLC atomicity assumed-correct.
5. **Time-typing honesty** — `causal` vs `frame_within(F,T,±δ)` with δ explicit; every other system conflates
   wall-clock and ordering into a global "now" / a Dutch decay / a batch window.

**Will NOT cross (the impossibility boundary — refs 9–11):**
- We do **not** claim a perfectly-fair global total order over *concurrent* intents. The Condorcet result (ref 9)
  and the Condorcet *attack* (ref 11) prove receive-order-fairness and even batch-order-fairness are *not* a
  no-MEV guarantee. For the tie-break over genuinely-concurrent intents we adopt a **transparent, attested**
  ordering whose fairness is exactly **γ-batch-order-fairness** (best realizable, Themis/Quick-Order-Fairness) —
  and we *say so*. Our structural exclusion bites on the *causally-ordered* and *conservation* parts only.
- "MEV is the control of the simultaneity surface, structurally excluded by causal ordering" is true **for the
  reorder/sandwich class on causally-related events** and for **mint-extraction**; it is **false** as an absolute
  ("all MEV abolished"). Cross-domain MEV, statistical/timing MEV, and concurrent-tie-break MEV remain — exactly
  the residue SUAVE-style auctions (ref 7) address. The two approaches are complementary.

---

## PDFs / specs pulled this session (validated `%PDF` / markdown, in `/Users/ember/dev/breadstuffs/pdfs/`)

- `aequitas-order-fairness-byzantine-consensus-2020-269.pdf` — Kelkar–Zhang–Goldfeder–Juels, *Order-Fairness for
  Byzantine Consensus* / Aequitas, CRYPTO 2020 (ref 9). [509 KB, `%PDF`]
- `condorcet-attack-fair-transaction-ordering-2306.15743.pdf` — Vafadar–Khabbazian, *Condorcet Attack Against
  Fair Transaction Ordering*, 2023 (ref 11). [981 KB, `%PDF`]
- `anoma-whitepaper.md` — Anoma, *a unified architecture for full-stack decentralised applications* (ref 1).
  [67 KB markdown; the GitHub source whitepaper — note the full **Anoma Resource Machine** spec lives separately
  at anoma.net/research + the ARM specs repo, summarized here from *Rise of the Resource Machines*].

**Already present (cited, not re-pulled):**
- `themis-order-fairness-byzantine-consensus-2021-1465.pdf` — Themis (ref 10).
- `sok-consensus-fair-message-ordering-2411.09981.pdf` — SoK fair message ordering (ref 12).
- `LEARNINGS-intent-matching.md` (the verify/find decidability seam — the matcher must be bounded/pluggable;
  underwrites §3 and the 7521/CoW "solver" critique).
- `LEARNINGS-ordering-consensus.md` (Law-2 ordering over the blocklace; BEC I-confluence — underwrites the
  causal-order claims in §5 and the honesty boundary).

**Not pulled** (HTML-only / paywalled / non-PDF specs): CoW/UniswapX/1inch/4337/7521/SUAVE docs (living web specs,
URLs above); Penumbra protocol spec (web); Quick Order Fairness (arXiv 2112.06615 — available, not central enough
to pull). The full **Anoma Resource Machine** technical spec (commitments/nullifiers/balance-delta) is in the
Anoma specs repo + Juvix `anoma` package — worth a dedicated follow-up pull if we formalize the ARM↔resource-
theory correspondence (it is the single most direct external validation of `INTENT-REFS-resources.md` #1).
