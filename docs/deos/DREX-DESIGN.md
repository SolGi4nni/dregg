# DrEX — Dragon's EXchange: the definitive design

*What DrEX becomes, taken from "two proven rungs" to the fullest coherent exchange, grounded in
dregg's real primitives. Scholar survey of the field + the fullest DrEX (ranked, grounded) +
the full rung ladder (per-rung theorem + build + grade) + the recommended next rung. Present
tense, what-is. Every ambitious piece names its gap and its trust grade. This is a design doc to
build from, not a promise — the honest edges are §6 and are load-bearing.*

> One-line thesis: **every DEX in the field delegates the clearing/ordering step to a trusted
> solver, sequencer, or committee and ships no proof that it acted correctly. DrEX makes the
> clearing itself a machine-checked, proof-carrying executor turn — and (rung 3) makes it private
> without any party ever holding the plaintext or the ordering power.** That seam is the whole
> design.

---

## 0. Trust grades (the OCIP spine — carried on every claim)

| grade | means | you still trust |
|---|---|---|
| **PROVED** | a machine-checked Lean theorem about the deployed artifact | the proof checker + named crypto assumptions |
| **BUILT** | real code, tested both polarities, but not (yet) a Lean theorem | the test coverage + the code |
| **ATTESTED** | hardware-rooted (TEE) or zkTLS provenance that data came from a named origin | the HW vendor root + side-channel residual |
| **REPLAYABLE** | a pure function over public data; anyone re-derives with one command | nothing but your own machine + the public chain |
| **UNBUILT** | named, designed, not yet written | — (this is the honest frontier) |

Reachability tags on rungs: **NEAR** (a Lean-tower lift on substrate that mostly exists) ·
**MEDIUM** (a real circuit/protocol build, multi-week) · **RESEARCH** (a genuinely open design or
perf problem).

---

## 1. Scholar survey — the field, and where each is structurally stuck

Assessed on (1) matching/settlement, (2) privacy, (3) fairness/MEV, and — the load-bearing column
— (4) **the irreducible trusted party** each design cannot remove.

| System | Matching / settlement | Privacy | Fairness / MEV | **The stuck trust point** |
|---|---|---|---|---|
| **CoW Protocol** | Off-chain solver competition over discrete batches; **uniform directed clearing price** per pair-direction; Coincidences-of-Wants matched P2P, residual to AMMs | Weak — signed orders visible to all solvers before execution | Strong: UDCP + batch makes intra-batch ordering economically irrelevant; CoWs have nothing to front-run | **The permissioned solver.** Bonded/whitelisted; the winning solution carries **no validity/optimality proof** — trust is competition + slashing + after-the-fact detection, not verification |
| **Penumbra ZSwap** | Sealed-bid batch swaps; per-block **uniform clearing price** per pair; amounts verifiably encrypted to a validator threshold key, homomorphically summed | Strongest confidentiality — individual orders **never** revealed; only per-block **aggregate net flow** decrypts | Excellent: no individual order to see before it clears | **The validator threshold committee.** A colluding `t`-of-`n` quorum can decrypt individual pre-aggregation contributions; DKG must be honest. Distributed, not eliminated |
| **dYdX v4** | Cosmos appchain; each node runs an **off-chain in-memory CLOB**; the block **proposer** matches by price-time, only fills committed on-chain | None — orders gossiped in clear | Weakest structural story — proposer can reorder/insert/censor within its block | **The block proposer's off-chain matching.** Mitigation is a discrepancy dashboard + **social slashing** — retrospective, statistical, political. Matching is consensus-*ordered*, not verifiable |
| **Uniswap v4** | Constant-function AMM; singleton PoolManager + flash accounting; **hooks** customize pricing/fees | None — public mempool | Mixed, hook-dependent: vanilla pools have v3-grade sandwich/JIT exposure | **The hook (added trust) + base-chain builder.** Core math is trustless but each pool's hook is a new trusted contract; v4 exposes a socket where a trusted party can be installed |
| **Budish FBA** (academic) | Discretize time; clear each interval as a **uniform-price sealed-bid call auction** | Not confidential unless combined with encryption | Converts speed competition into price competition; kills mechanical latency-arb / sniping | **Out of scope by construction** — a market-design result; says nothing about *who runs* the auction. Also does not fix cross-batch info leakage or the interval tradeoff |
| **0x / UniswapX** | Signed off-chain intent on a **Dutch-auction decay curve** (± RFQ seed); permissionless **fillers** execute + pay gas | Limited — orders broadcast to fillers; RFQ quote private, fill public | Internalizes MEV as price improvement; failed fills cost the swapper nothing | **The filler / RFQ quoter + relay.** Permissionless in theory, professional-and-trusted in practice; **no best-execution proof**; RFQ last-look / quote-fade risk |
| **Hyperliquid** | Purpose-built L1; **fully on-chain CLOB**; deterministic price-time matching ordered by **HyperBFT**; matching is verifiable-by-re-execution *given the ordering* | None — transparent CLOB | Matching itself is not discretionary (deterministic re-execution) | **The BFT leader's ingestion ordering.** Trust moves from "matching" to "who sequences orders into the book" — a 1/3-honest committee, thin in practice (small/operator-concentrated set) |
| **Shutter** (mempool) | Threshold-encrypted mempool; txs included encrypted, **Keyper committee** releases shares after ordering is fixed | Blinds the ordering window only | Proposers order blind — no order-flow MEV in that window | **The Keyper threshold committee.** Can collude-to-decrypt-early or withhold-to-stall; metadata leaks; post-reveal backrunning survives |

### 1.1 Best-in-class per dimension

- **Matching quality** — Hyperliquid (on-chain CLOB, verifiable-by-re-execution, CEX-grade depth).
- **Privacy** — Penumbra (individual orders never revealed).
- **Fairness / MEV** — Penumbra (removes the info to exploit) and CoW (removes the ordering value to
  exploit) tie.
- **Liquidity** — Hyperliquid (professional MM depth) for active; Uniswap v4 for passive/permissionless.
- **Cross-margin** — Hyperliquid / dYdX v4 (purpose-built perp margin engines).
- **Settlement trust-minimization** — Uniswap v4 / vanilla AMMs (pure on-chain, no off-chain role in
  the settlement path — at the cost of privacy and MEV exposure).

### 1.2 The one trust point nobody has removed

**Every system retains a party that orders or clears the flow before it is verifiably settled — a
solver, a sequencer/proposer, or a committee — and none ships a proof that this party acted
correctly.** The trust only changes shape: CoW *distributes to competition + slashing*; Penumbra and
Shutter *distribute to a threshold committee*; dYdX *detects abuse after the fact*; UniswapX *makes it
professional-but-permissionless*; Hyperliquid *makes matching deterministic but leaves sequencing to a
BFT leader*. The field has decentralized *settlement* and, at best, made matching *deterministic given
an order* or made *ordering economically irrelevant* — but **the clearing computation itself carries no
succinct correctness proof.** That is the seam a verified-emit, proof-carrying settlement system is
uniquely positioned to weld shut. DrEX is the attempt to weld it.

---

## 2. Where DrEX stands today (rungs 1–2, PROVED)

DrEX is a Lean-first proof-carrying exchange: the exchange's *rules* are proven sound in Lean (the
`metatheory/Market/` tower), and each execution *instance* carries a proof it obeyed them (the circuit
+ FFI layer). Two rungs are done and axiom-clean (`#assert_all_clean` over all keystones).

> **Status update — rungs 4/5/6 have since LANDED at model scope.** The forward rung-ladder in §4/§5
> below is the original design framing (written when only rungs 1–2 existed). Since then, rung 5
> (`Market/Priced.lean` — priced/partial-fill/multi-pair, `priced_clearing_keystone`), rung 4
> (`Market/Optimality.lean` — uniform-price no-arbitrage / envy-freeness / `uniform_price_optimal`), and
> rung 6 (`Market/Liquidity.lean` — portfolio `pool_solvent_forever`) are all **PROVED, axiom-clean**.
> The load-bearing caveat: these three are proved over the **priced `Fill` / reserve model** (real ℚ
> prices, lifted off `DemoRes`), **NOT** yet ledger-realized through `settleRing`/`recKExec`. Only
> **rung 1** carries the executor tie (`cycleValid_fulfilled_respects_limits` over `settleRing`, via
> `RingFFI`). What remains genuinely open above the model rungs: **full k-coalition TTC-core** stability,
> the **on-ledger delta readback** for the priced layer (the `RecordKernelState.bal`-after-`settleRing`
> weld rung 5's design named), and the constant-function AMM curve above rung 6's solvency floor.

**Rung 1 — execution soundness + fairness** (`Market/Clearing.lean`, `Market/Fairness.lean`,
composing `Dregg2/Intent/Ring.lean`). PROVED:
- **Conservation** — a cleared book's per-asset Σ in = Σ out (`clearing_conserves_per_asset`), lifting
  the bilateral `settle_conserves` to the cleared *set* through the real ledger measure `toBal`; and
  the executable `settleRing_conserves` (per-asset supply preserved across the whole ring).
- **Atomicity** — any failing leg rolls back everything (`settleRing_atomic`).
- **Fairness, both sides** (`clearing_respects_limits`): every participant of a solver-admitted cycle
  is debited **only its offered asset, in amount ≤ its offer** (the new give-side half) AND credited
  **its wanted asset, in amount ≥ its declared minimum** (`cycle_individuallyRational`, the Shapley–
  Scarf receive-side). Enforced at cycle **formation**, not policed after: an over-debiting or
  wrong-asset cycle is **not `CycleValid`** (`overdebit_refused`, `wrongAsset_refused`), so it never
  reaches settlement.
- **Non-emptiness with teeth** — the 3-party ring containing the kernel's bilaterally-stuck `crossBid`
  *clears* (`ringClearing`), every 2-party sub-book *fails* (`ring_pairs_refused` — genuinely
  multilateral), a minting book is refused (`mint_refused`), and a pool-balanced-but-misrouted
  allocation is refused (`unfair_refused` — conservation and fairness are independent teeth).

**Rung 2 — order-book aggregation soundness** (`Market/Aggregation.lean`). PROVED: the aggregator
(`mergeSort` by priority) is **faithful** (a permutation of the submissions — no drop, no insert, nonce
multiset preserved) AND **prioritized** (sorted by declared price-time key — no reorder), with all four
teeth (`drop_refused`, `insert_refused`, `substitution_refused`, `reorder_refused`). Composes into
rung 1: `aggregated_clearing_conserves_submissions` — a clearing of the aggregated book conserves
exactly the *submitted* orders' per-asset totals, independent of arrival order. Reuses Dregg2's
`ChainBound` no-drop/no-insert/no-reorder discipline over the order stream.

**The real matcher underneath** (`intent/src/solver.rs`, `verified_settle.rs`) — and its honest limits,
which set the whole rung ladder:
- The solver is **top-trading-cycles** in spirit (Johnson circuits + Shapley–Scarf TTC), but in code a
  **bounded DFS** (`find_cycles(max_len)`, practical 3–5) with a **greedy** outer loop
  (`solve_greedy` takes the highest-participant-count ring first) — **not** full Johnson's and **not**
  welfare-optimal.
- **Exact-book, no partial fills.** `is_compatible` (`solver.rs:578`) requires `offer_asset ==
  want_asset` (asset-exact, no cross-asset routing) and settles the receiver's **full `want_min_amount`**
  or rejects the ring (`InsufficientAmount`). Overshoot is **wasted, not credited** (surplus stays with
  the offerer).
- **Prices are bound-checks only.** `min_rate`/`max_rate` are validated per-node; there is **no common
  numéraire, no price discovery, no uniform clearing price.**
- **But it settles through the verified kernel.** `verified_settle.rs` routes each leg through the Lean
  FFI export `@[export] dregg_record_kernel_step` over the **proved** `Exec.recKExec`, leg-by-leg
  all-or-nothing, cross-checking the executor's post-balances against the in-process transition
  (`FfiDivergence` fails closed). `RingFFI.ffi_export_realises_settleRing_leg` proves the export
  realises the leg. So "an intent fulfilled" *literally means* a verified, conserving, authorized
  executor turn executed — not a Rust mirror. (Honest sub-limits: `u8`-keyed ledger aliases cells
  sharing a low byte — `WideLeg` fixes it but refuses > 256 distinct cells; authorization is self-send
  only; on FFI-free builds the in-process transition stands alone, proved-equivalent but not actually
  invoking Lean.)

**Net:** DrEX today is a **provably-fair, provably-conserving, atomic multilateral clearing over an
exact two-asset/quantity book, settling through the proved kernel** — the matching *rules* are theorems
and the *settlement* is a proof-carrying executor turn. What it is **not** yet: priced, partial-fillable,
private, liquidity-pooled, cross-margined, or cross-chain-atomic. That is the ladder.

---

## 3. The fullest DrEX — ranked pieces, grounded, honest-gap each

Ranked by (structural distinctiveness × groundedness). Each piece names the dregg primitive it rests on,
why it beats the best-in-class, and its honest gap + grade.

### #1 — Private matching over hidden commitments (the marquee, the moat)
*The one thing no system in §1 can copy.* Matching happens **inside the proof over shielded notes** —
the ring solver clears over `circuit-prove/src/shielded/pool.rs` commitments (value + owner + **asset**
all hidden; homomorphic per-asset conservation via a Schnorr excess proof; per-output Bulletproof range
proofs close inflation; tested both polarities) rather than over the clear ledger.
- **Beats:** Penumbra (a `t`-of-`n` validator committee decrypts the aggregate — DrEX decrypts
  *nothing*); CoW (solvers see every order); Shutter (Keyper committee holds the key); dark pools
  (operator peeks). **There is no instant and no party that holds the plaintext or the ordering power.**
  Concretely it **deletes the `intent/src/trustless.rs` DECRYPT committee** — the residual trust that
  batch is candid about (`threshold_decrypt`, `t`-of-`n` Shamir shares) — because there is nothing to
  decrypt.
- **Rests on:** the shielded pool (BUILT, tested) + the proved ring (rung 1) + sealed-auction commit→
  reveal (`SealedAuction.lean`, CR over a real Blake3 kernel).
- **Gap (grade UNBUILT, MEDIUM→RESEARCH):** the shielded pool is *not woven into* `effect_vm`
  (`shielded/mod.rs:47`) — the weld is a custom private-matching circuit proving "this cleared
  allocation is the correct aggregation + execution of these *committed* orders under the book rules"
  without revealing them. Matching over hidden orders *fast enough for a book* is a perf frontier even
  with the wrap + GPU. This is DrEX rung 3.

### #2 — Proof-carrying clearing (the matching engine as a theorem + a verified turn)
The clearing *rules* are theorems (rung 1) and the clearing *instance* settles through the proved kernel
(`verified_settle.rs` → `Exec.recKExec`), so a counterparty **verifies the fill as a proof** instead of
trusting a solver.
- **Beats:** CoW's solver and dYdX's proposer, which ship **no proof** of correct clearing (competition/
  slashing/detection); Hyperliquid, whose matching is verifiable only *given* a trusted BFT sequencing.
  DrEX removes the trusted-solver residue **by proof**, not by distributing or detecting it: an
  over-debiting or minting clearing is *unconstructable* (`overdebit_refused`, `mint_refused`), and the
  settlement's conservation/atomicity are `settleRing_conserves`/`_atomic`.
- **Rests on:** rungs 1–2 + the FFI refinement (`RingFFI`).
- **Gap (grade PROVED for the rules + the ring's executor-refinement; UNBUILT for optimality):** the
  solver is greedy + bounded-DFS, so "fair and conserving" is PROVED but "*optimal* clearing" is not
  (rung 4). The `MarketRefinement` slash-leg alignment is the one open refinement instance.

### #3 — Priced, partial-fillable, multi-pair book (DrEX as a real exchange)
Lift the clearing from the two-asset exact `DemoRes` book to a **priced, continuous book with partial
fills across many pairs**. The quantity substrate half-exists: the `MatchNode`/`CycleValid` layer already
carries `offerAmount`/`wantMin` and settles a leg amount ≤ the offer — what's missing is prices
(a numéraire / rate), partial fills (fractional leg settlement), and lifting conservation off `DemoRes`.
- **Beats:** nothing yet — this is the piece that makes DrEX competitive at all as an exchange rather
  than an exact-swap demo. It is the substrate every richer piece needs.
- **Rests on:** rung 1 (conservation/fairness shape) + the priced columns already in `MatchNode`.
- **Gap (grade UNBUILT, NEAR):** the module's conservation + clearability theorems are over `DemoRes`
  (discrete two-asset, exact-book, all-or-nothing). This is a pure Lean lift — the tower's proven mode.
  This is DrEX rung 5, and it is **prerequisite substrate for rung 4 and rung 6** (see §4/§5).

### #4 — Uniform-price / envy-free clearing (the fairness apex)
All legs of a two-sided batch on one pair clear at **one price** (the Budish FBA discipline), and no
coalition can re-trade among themselves to strictly improve (Shapley–Scarf TTC-core stability).
- **Beats:** matches CoW's UDCP and Penumbra's per-block uniform price — but as a **machine-checked
  theorem** about the deployed clearing, not a solver constraint enforced by simulation.
- **Rests on:** the priced substrate (#3 / rung 5).
- **Gap (grade UNBUILT, MEDIUM — and BLOCKED on #3):** today's `clearing_respects_limits` is individual
  rationality (nobody worse than their declaration), which is strictly weaker than uniform-price
  optimality or core stability. Cannot be built before the priced substrate exists. This is DrEX rung 4.

### #5 — Liquidity: native multilateral CoWs + an optional proven-solvent pool
dregg's *native* liquidity mode is **multilateral P2P clearing** (the ring finds Coincidences of Wants
directly — `crossBid` clears with no AMM), so the base exchange needs **no LPs and no pricing curve**.
Above that, an **optional standing pool** whose solvency invariant is a `MarketClearing`-preserved
measure — a proven-solvent AMM-hybrid for residual/one-sided flow.
- **Beats:** CoW routes residual to external AMMs it doesn't prove; Uniswap pools carry no solvency
  theorem. A dregg pool would carry `stripe_reserve_solvent_forever`-style backing (`reserve ≥
  liabilities` over *every* schedule, a ∀-adversary object) as its invariant — a pool that
  *cannot lie about its book*.
- **Rests on:** the ring (native CoWs, PROVED) + `Verify/StripeReserve.lean` (∀-schedule solvency,
  PROVED single-channel) + the shielded pool's homomorphic conservation.
- **Gap (grade UNBUILT, MEDIUM):** solvency is proved per-channel over cleartext integers; a pool needs
  it lifted to a portfolio and (for a private pool) to the **hidden aggregate** — proving `reserve ≥
  liabilities` over Pedersen sums, a range/comparison argument over commitments. Also: an AMM pricing
  curve as a `MarketClearing`-preserving family is new. This is DrEX rung 6.

### #6 — Fees / incentives: bonded conduct, holder-compensating slashing
No trusted fee router: the OCIP discipline — a promoter/market-maker **posts a conduct bond**, slashed
on *mechanical on-chain misconduct predicates* (REPLAYABLE), and **slashes compensate holders, never the
platform**. Fee money-paths (splitter conservation, "exactly once" fee router) are PROVED.
- **Beats:** every venue's opaque fee + boosted-listing model; here promotion is bonded-not-boosted and
  the ranking is a REPLAYABLE pure function anyone re-derives.
- **Rests on:** OCIP money-paths (PROVED) + the bonded-conduct predicates (REPLAYABLE) + the solver
  bonding already in `trustless.rs` (`SolverSubmission.bond`).
- **Gap (grade PROVED for money-paths / REPLAYABLE for ranking; UNBUILT for the DrEX-specific weld):**
  solver/market-maker bonding is not yet wired to DrEX conduct predicates (e.g. "settled below the
  proven clearing price" → slash). Design, not new science.

### #7 — Cross-margin & derivatives via the capability mandate
A position is an **attenuable mandate** (`Dregg2/Agent/Mandate.lean`, `intent/src/agent_mandate.rs`):
non-amplifying (`subtree_rights_le_root`), budget-conserved (`subtree_budget_le_root`,
`children_no_oversubscribe`), revocable-at-tip (`revoke_kills_subtree`), and it **materializes into
committed executor effects** (`materialize_non_amplifying`/`materialize_grants` → real
`Effect::GrantCapability`/`RevokeDelegation` with a bitwise facet-mask attenuation). Derivatives =
guarded-holes / partial turns (forwards, conditional orders, structured products as promises).
- **Beats:** prime brokerage's counterparty-trust premise — a **mandate breach is unconstructable, not
  monitored** ("trade up to $X, assets/venues {…}, no withdrawals," checked by the settling venue). No
  Hyperliquid/dYdX margin engine offers cryptographically-scoped, provably-non-amplifying delegation.
- **Rests on:** the mandate (PROVED + materialized) + guarded-holes (largely built) + shielded positions
  (#1).
- **Gap (grade PROVED for delegation/budget/revocation; UNBUILT for per-trade admission + the
  derivative financialization):** the one open weld is **per-trade caveat-admission in-circuit** — the
  aggregate `caveatBit` (`Caveat.lean:59`) still *trusts the executor's decision*; reifying it as a real
  constraint turns "dregg can express this mandate" into "the venue verifies it as a proof." A cross-
  margin engine over shielded positions is new build. This is DrEX rung 7.

### #8 — Cross-chain settlement by proof (settle-anywhere)
A DrEX fill settles on any chain by proof: the EVM Groth16 wrap is **done end-to-end on real data** (a
real dregg apex shrinks BN254-native, a gnark gadget verifies FRI, settlement lands on-chain via
Foundry; `chain/gnark/`, `apex_shrink_real_fixture_test.go`). Collateral proven simultaneously across
Solana/EVM/Cosmos via light clients + `mpt_holding_leaf`.
- **Beats:** a bridge structurally cannot build this — a bridge's only verb is move-the-token, so it
  must converge assets onto one chain, and the convergence is the honeypot (Ronin *was* the vault).
  dregg proves a state transition that *references* holdings proofs; nothing converges.
- **Rests on:** `settleRing_atomic` + the field-parameterized wrap (`dregg_outer_config.rs`, EVM-verified)
  + the leaf-adapter fold fabric (12 adapters, `circuit-prove/src/*_leaf_adapter.rs`).
- **Gap (grade BUILT for the EVM rail end-to-end; UNBUILT for cross-chain atomicity):** a *single
  multilateral cycle whose legs settle on different chains atomically* needs a commit/abort protocol
  across verifiers — `settleRing_atomic` is single-machine. And the whole rail rides a **single-party dev
  ceremony** Groth16 (toxic-waste-known), not mainnet MPC. This is DrEX rung 8; cross-chain atomicity is
  the hardest coordination piece (RESEARCH).

### The uniquely-dregg composition (why the whole is more than the pieces)
Every economic fact above is a **recursion leaf**: `note_spend_leaf_adapter`, `mpt_holding_leaf`,
`deco_leaf_adapter`, `bridge_leaf_adapter`, … are composed by `joint_turn_recursive.rs`, and the apex
shrinks BN254-native end-to-end today. A DrEX **structured product** is one apex proof folding
{shielded note-spend ⊕ solvency ⊕ cross-chain holding ⊕ `clearing_respects_limits`} as leaves — verified
once, on any chain, and reusable as a leaf in a fund-of-funds above it. No other DEX stack can compose
proofs this way; it is the moat behind the moat. (Gap: the *financial* leaves — solvency-as-leaf,
clearing-as-leaf — are not yet written as adapters; the fold *machinery* works, this is build not
science.)

---

## 4. The rung ladder — per rung: theorem-to-prove · build · grade

Rungs 1–2 are PROVED (§2). The frontier:

| Rung | Name | Theorem to prove | Build | State / reach |
|---|---|---|---|---|
| **3** | **Private matching weld** (marquee) | *`private_clearing_sound`*: a published proof over shielded notes attests that a hidden allocation is the correct fair, conserving aggregation+clearing of committed orders under the book rules — without revealing owner/value/asset. Reflect rungs 1–2 in-circuit; nullifier layer proves *who* traded. | Weave `shielded/pool.rs` into the ring so clearing runs over shielded notes; a custom private-matching AIR atop the shielded-spend circuit; delete the `trustless.rs` DECRYPT committee. | UNBUILT · MEDIUM→RESEARCH |
| **4** | **Uniform-price / envy-free** (fairness apex) | *`uniform_price_optimal`*: all legs of a two-sided one-pair batch clear at ONE price; *`ttc_core_stable`*: no coalition re-trades to strictly improve (Shapley–Scarf core over `CycleValid`). | Weld the priced-book layer to the cycle model; a call-auction clearing rule. **Blocked on rung 5's substrate.** | UNBUILT · MEDIUM (blocked) |
| **5** | **Priced / partial-fill / multi-pair** (the substrate lift) | *`priced_clearing_conserves`* + *`partial_fill_respects_limits`*: lift `clearing_conserves_per_asset` and `clearing_respects_limits` off `DemoRes` to a priced continuous resource with fractional leg settlement across many pairs; on-ledger per-participant deltas read back off `RecordKernelState.bal` after `settleRing`. | Generalize `MarketClearing`/`pool`/`toBal` to a priced/continuous resource theory; connect to the `MatchNode` amount columns; partial-fill leg construction. | UNBUILT · **NEAR** |
| **6** | **Liquidity / proven-solvent pool** | *`pool_solvent_forever`*: a standing pool as a family of clearings whose `reserve ≥ liabilities` invariant is `MarketClearing`-preserved over every schedule; *`pool_solvent_hidden`*: the same over Pedersen sums (private pool). | Lift `stripe_reserve_solvent_forever` to a portfolio + to the hidden aggregate; an AMM curve as a clearing-preserving measure. | UNBUILT · MEDIUM |
| **7** | **Cross-margin / derivatives via mandate** | *`caveat_admits_in_circuit`*: the per-trade `caveatBit` is a real circuit constraint (mandate breach unconstructable at the venue); *`margin_position_sound`*: a shielded cross-margin position conserves + respects the mandate. | Reify `Caveat.lean:59` in-circuit; a cross-margin engine over shielded positions + guarded-holes for forwards/conditionals. | UNBUILT · MEDIUM |
| **8** | **Cross-chain atomic settlement** | *`cross_chain_ring_atomic`*: a multilateral cycle whose legs settle on different chains commits all-or-nothing, each leg checked by that chain's verifier via the wrap. | A commit/abort protocol across verifiers atop the (done) EVM wrap + light clients; production MPC ceremony (replaces the dev Groth16). | BUILT (EVM rail) · UNBUILT (atomicity) · RESEARCH |

---

## 5. The recommended next rung

**Build rung 5 — the priced / partial-fill / multi-pair substrate — next.**

Ranked by (value × reachability), rung 5 wins decisively, and the reason is a **dependency-inversion
finding worth stating plainly**: the prompt's natural ordering puts uniform-price (rung 4) before the
priced substrate (rung 5), but **rung 4 cannot be proved before rung 5 exists** — uniform-price
optimality and envy-freeness are theorems *about prices and partial allocations that the module does not
yet have*. Today's conservation/clearability/fairness theorems live over `DemoRes`: discrete, two-asset,
exact-book, all-or-nothing, no prices. Rung 5 is the substrate that unblocks rungs 4 **and** 6 **and**
meaningful derivatives (rung 7's margin math).

Why rung 5 specifically:
- **Reachability: NEAR.** It is a pure Lean-tower lift — the tower's proven mode of working (rungs 1–2
  went green and axiom-clean this way). No new circuit, no crypto assumption, no committee. The quantity
  columns already exist in `MatchNode` (`offerAmount`/`wantMin`); the leg amount is already `≤` the
  offer. The work is generalizing `MarketClearing`/`pool`/`toBal`/`clearing_respects_limits` from the
  discrete two-asset bundle to a priced continuous resource with fractional fills.
- **Value: HIGH.** It converts DrEX from "provably-fair *exact-swap demo*" into "provably-fair *real
  limit-order exchange with prices and partial fills across pairs*" — the single biggest jump in what
  DrEX *is*, and the thing the ambition doc explicitly flagged as the named `DemoRes → real-prices` lift.
- **It de-risks everything above it.** Once prices and partial fills are theorems, rung 4 (uniform-price)
  is a clearing-rule addition on real substrate, and rung 6 (pool solvency) has a priced measure to
  preserve.

**The marquee (rung 3, private matching) is the highest-*value* rung and the moat — run it as a parallel
circuit track**, not as the sequential next Lean rung, because (a) it is a MEDIUM→RESEARCH circuit build
on a different skill axis (weaving the shielded pool into `effect_vm`), and (b) building the private book
on today's exact-two-asset substrate would ship a private *toy*; the priced substrate makes the private
book a real exchange. The honest sequencing is: **rung 5 next on the Lean tower (unblocks the fairness
apex), rung 3 in parallel on the circuit side (the moat).** They converge when a priced private clearing
is one proof.

---

## 6. The honest edges (load-bearing — named once, plainly)

- **Exact-book / two-asset for the LEDGER-REALIZED rung.** Rung 1's ledger-tied conservation +
  clearability (`clearing_conserves_per_asset`, and `cycleValid_fulfilled_respects_limits` over
  `settleRing`) are over `DemoRes`/`MatchNode` (discrete, two-asset, exact, no prices/partial fills).
  Priced/optimal clearing IS now proved (rungs 4–5, `Market/{Priced,Optimality}.lean`) — but over the
  **`Fill` model**, off `DemoRes`, and **not** ledger-realized. So "DrEX clears fairly" is
  ledger-verified on an exact book (rung 1) and model-verified with prices (rungs 4–5) — say which.
- **The solver is greedy + bounded-DFS.** Fair and conserving are theorems; *welfare-optimal* is not —
  no max-weight-matching guarantee. Uniform-price no-arbitrage / envy-freeness are proved (rung 4,
  `Market/Optimality.lean`) at the single-participant / pairwise core; full **k-coalition TTC-core** is
  the open sub-rung.
- **The DECRYPT committee is still present.** `trustless.rs` front-running prevention rests on a `t`-of-`n`
  threshold-decryption committee (a real residual trust) *until* rung 3 deletes it. Today's private
  batch is committee-private, not proof-private.
- **STARK predicate verifiers are fail-closed, not fail-verified.** The trustless batch's strict registry
  installs `NotYetWiredVerifier` for most predicate kinds (they *reject*, not verify); only `NonMembership`
  ships a real verifier. Honest: proofs currently fail closed.
- **Shielding ≠ perfect anonymity.** Timing, anonymity-set size, and edge graph-analysis leak. The shielded
  pool discharges inflation with per-output Bulletproof range proofs (BUILT, tested both polarities) but
  the range-rib is still a *named obligation* of the Lean conservation law, not yet a Lean theorem — and
  the pool stands *beside* `effect_vm`, not inside it (the rung-3 weld).
- **Solvency: portfolio now proved (model), hidden-aggregate open.** `stripe_reserve_solvent_forever`
  is a real ∀-schedule theorem for one channel; the **portfolio** lift is now ALSO proved —
  `pool_solvent_forever` (`Market/Liquidity.lean`), a ∀-schedule fold over `Pool = AssetId → ℚ`, reusing
  the single-channel apex verbatim as the backing line. Both are over the reserve **model** (not welded
  to `settleRing`); hidden-aggregate solvency and the AMM curve remain rung-6+ open.
- **Mandate admission is expressiveness at the per-trade caveat.** Delegation/budget/revocation are PROVED
  + materialized into committed effects; only the per-trade `caveatBit` still trusts the executor's
  decision (rung 7 weld).
- **Trusted setup.** On-chain enforcement rides a Groth16 verifier on a **single-party dev ceremony**
  (toxic-waste-known), not mainnet MPC. A prerequisite, not a detail (rung 8).
- **Cross-chain is EVM-outbound end-to-end (real data), not yet atomic-multilateral.** The wrap is done;
  a cross-chain *atomic* ring (leg-fails-on-B rolls back leg-on-A) is an open distributed-commit design
  (rung 8, RESEARCH).

The precise claim, everywhere: **not "perfectly private, fair, solvent" — but "private, fair, and solvent
*without trusting any operator, committee, sequencer, bridge, or counterparty*, with the remaining trust
named, graded, and driven toward zero."** No system in §1 can make that claim; the machinery to back it
is, unusually, mostly already proven in the tree — and the next rung to build is the priced substrate that
turns the proven exact-book core into a real exchange.

---

## See also
`DREGGFI-VISION.md` · `DREGGFI-AMBITION.md` (the substrate frame + the moat) ·
`metatheory/Market/{Clearing,Fairness,Aggregation}.lean` (rungs 1–2, PROVED; rung 1 ledger-realized) ·
`metatheory/Market/{Priced,Optimality,Liquidity}.lean` (rungs 5/4/6, PROVED at model scope — priced `Fill`/reserve model, not yet `settleRing`-realized) ·
`metatheory/Dregg2/Intent/{Kernel,Ring,SealedAuction}.lean` · `metatheory/Dregg2/Agent/Mandate.lean` ·
`metatheory/Dregg2/Verify/StripeReserve.lean` ·
`intent/src/{solver,trustless,verified_settle,agent_mandate}.rs` ·
`circuit-prove/src/shielded/pool.rs` · `circuit-prove/src/*_leaf_adapter.rs` · `chain/gnark/`.
