# The dregg launchpad — the launchpad where fairness is a theorem

*A token launchpad that makes the dominant launchpad abuses **unconstructable** (a Lean theorem
forbids them), **disincentivizes** what remains with a bonded-conduct economic layer, and names
honestly the class of abuse mechanism design cannot fix (a bad token is still a bad token). Built by
composition on dregg's already-proven primitives — the sealed-bid commit→reveal auction, the DrEX
uniform-price multilateral clearing, the provably-solvent liquidity pool, the supply-authority
biconditional, the OCIP bonded-conduct pattern, and the networked-proofs cross-chain settlement.
Present-tense, what-is; every claim carries a trust grade; the honest edges are §5.*

**Grade of this document:** REPLAYABLE for the census (re-derivable by reading the cited code); the
mechanism is a **design over PROVED machinery** (the four proof towers below) with named welds. This
is a design doc, not a shipped product — §5 is the build path.

Trust grades (the OCIP spine, from `docs/deos/DREX-DESIGN.md` §0): **PROVED** = a machine-checked Lean
theorem about the artifact (you trust the checker + named crypto assumptions); **BUILT** = real code,
both polarities tested, not yet a theorem; **ATTESTED** = HW-rooted / zkTLS provenance; **REPLAYABLE**
= a pure function over public data anyone re-derives; **UNBUILT** = named, designed, not written.

---

## 1. The landscape — mechanisms, abuse vectors, anti-abuse SOTA (cited)

### 1.1 The bonding-curve baseline everyone abuses

The dominant model (pump.fun, LetsBONK, Meteora DBC, Virtuals) is a deterministic **constant-product
bonding curve**: no order book, price is a pure function of circulating supply, and a token
"graduates" when it fills the curve (~85 SOL on pump.fun) — at which point liquidity auto-migrates to a
DEX (Raydium) and is typically burned/locked. Standard supply is 1B tokens, ~800M seeded to the curve.
Only ~2–3% of tokens ever graduate; 97–98% decay toward zero. (Pump.fun Bonding Curve Explained,
https://j.tools/en/blog/pump-fun-bonding-curve-mechanics-explained; docs https://pump.fun/docs/bonding-curve)

The graduation LP-burn blocks the *classic LP-withdrawal rug at that one stage* — and nothing before
it. NOXA Fun's "hybrid V3" removes even the migration window (tokens are immediately tradable on
Uniswap V3 with liquidity permanently locked in the platform locker) (NOXA docs,
https://docs.noxa.fi/introduction/). Meteora's DBC lets projects define the curve/fee/graduation
threshold (`quoteReserve > migrationQuoteThreshold`) then graduates into a DAMM v2 pool
(https://docs.meteora.ag/core-products/dbc/what-is-dbc). LetsBONK is the same fair-launch/curve model
on Raydium LaunchLab, differentiated by ecosystem, not by eliminating the abuse class
(https://bingx.com/en/learn/article/letsbonk-fun-vs-pump-fun-which-solana-memecoin-launchpad-to-use).
Virtuals' "Genesis Launch" is a permissionless bonding curve paired with $VIRTUAL
(https://whitepaper.virtuals.io/builders-hub/agent-launch-mechanisms). (Note: the brief's "p0" and
"Believe" have no documented mechanic under those names in the sources surveyed; NOXA's "p0" is not a
documented NOXA term either — treated as unverified.)

### 1.2 The abuse-vector taxonomy (with $-scale)

The headline stat: a 2025 **Solidus Labs** report found ~**98.6%** of pump.fun tokens exhibited
rug-pull / scam / pump-and-dump characteristics (pump.fun disputed the framing) (BeInCrypto,
https://beincrypto.com/pump-fun-tokens-scams-solidus-labs-report/; CoinDesk,
https://www.coindesk.com/business/2025/05/07/98-of-tokens-on-pump-fun-have-been-rug-pulls-or-an-act-of-fraud-new-report-says).

| # | Vector | How it works | $-scale / example |
|---|---|---|---|
| A | **Dev-rug** | Collect funds, abandon or drain. "Zero-effort" deploy-then-abandon dominates and is hard to predict. | Median detected rug ≈ **$2,832**; largest ≈ **$1.9M** (Solidus). Academic: **$6.04M** from rug pulls (arXiv 2507.01963, https://arxiv.org/html/2507.01963v2; arXiv 2206.08202, https://arxiv.org/html/2206.08202v3) |
| B | **Snipe / bundle** | Bots watch RPC queues / bundle relays (Solana has no public mempool but txns are visible in-flight); use **Jito bundles** to buy the earliest, cheapest curve segment and flip to slower retail. | Retail eats **2.5–5%+** immediate loss; **1,012 persistent coordinated sniper cohorts** identified (arXiv 2607.02795, https://arxiv.org/pdf/2607.02795; Blockworks, https://blockworks.com/news/solana-cutting-mev-snipers) |
| C | **Insider / hidden allocation ("bundling")** | Pre-load fresh wallets, buy a large % of supply in the exact launch block at curve bottom, dump on retail. Even the *standard* "creator buys own token first" is insider allocation by design. | TRUMP-coin insider Hayden Davis (Bubblemaps) received large pre-public PUMP allocations (BeInCrypto, https://beincrypto.com/trump-coin-insider-hayden-davis-pumpfun-token-dump/) |
| D | **Curve manipulation** | Coordinated buys to fake curve progress/momentum, front-run/sandwich organic buyers within the curve. | "A tax paid by organic users to professional bots" (cryptogrowsnews, https://cryptogrowsnews.com/learn/memecoin-trading-solana-pumpfun-sniping-risks/) |
| E | **Wash trading** | Coordinated self-trading to fake volume/interest. Detected via wallet-cluster analysis, Benford's-Law anomaly tests, liquidity/spread analysis — hard because of instant pseudonymous addresses + native volatility "cover." | (cryptotracelabs, https://cryptotracelabs.com/blog/what-are-wash-trading-patterns-and-how-do-investigators-detect-them/; Nasdaq, https://www.nasdaq.com/articles/fintech/crypto-wash-trading-why-its-still-flying-under-the-radar-and-what-institutions-can-do-about-it) |
| F | **Pump-and-dump** | Coordinated hype pump then mass sell-off. | Academic: **$3.27M** realized (arXiv 2507.01963) |
| G | **Sybil** | One actor, many fake wallets, to defeat per-wallet caps / airdrop fairness / voting. | (sumsub, https://sumsub.com/blog/pump-dump-vs-rug-pull/) |

### 1.3 Anti-abuse SOTA — and where each FAILS (mitigation ≠ guarantee)

- **pump.fun creator-allocation lock** (Mar 2026): creators must lock ≥**50%** of initial allocation
  for ≥**72h** post-launch (Binance Square, https://www.binance.com/en/square/post/305605220874065).
  **Fails:** addresses dev-drains-own-allocation only, not sniping/insiders/manipulation; pump.fun
  *itself states* the guardrails do not eliminate market risk.
- **Sniper taxes** (linearly decaying early-sell fees) (Blockworks, as above). **Fails:** anti-snipe
  (rate limiters, wallet caps, fee schedulers) is "not a guarantee of fairness" — sophisticated
  operators circumvent simple limiters, and aggressive settings choke *genuine* early LPs (OpenLiquid,
  https://openliquid.io/learn/anti-snipe/).
- **Vesting / cliffs.** **Fails:** a big team/investor cliff unlock triggers a crash — without utility,
  unlocks are just *scheduled dumps* (defiprime, https://defiprime.com/token-vesting-guide).
- **"Fair launch" as a label.** **Fails:** a centralized/unaudited "fair launch" still permits insider
  manipulation; the label ≠ the property (capwolf, https://capwolf.com/why-cryptos-fair-launch-dream-falls-short/).

### 1.4 Fair-launch / auction mechanisms — and their limits

- **Frequent Batch Auctions (FBA)** — Budish, Cramton & Shim (QJE 2015): continuous limit order books
  create a wasteful HFT speed arms race and let the fastest front-run the slower. FBA batches in
  discrete time and clears at a **uniform price**, reducing any speed advantage smaller than the batch
  to zero — competition shifts from *who is fastest* to *who offers the best price*
  (https://academic.oup.com/qje/article/130/4/1547/1916146). **Limit:** with *privately informed*
  traders, LPs can still earn markups (SAFE WP 344,
  https://publikationen.ub.uni-frankfurt.de/opus4/frontdoor/deliver/index/docId/64572/file/SSRN-id4065547.pdf).
- **Gnosis batch auction (EasyAuction)** — bids sorted high→low, a single **uniform clearing price**
  where sell supply is fully matched by demand; kills gas-war time-priority (HackMD,
  https://hackmd.io/cA1xim1HTbmoU31HTof_Tg). **Limit:** *not truly sealed-bid* — bids are visible in
  the mempool absent timed-commitment/privacy tech (Riggs, https://eprint.iacr.org/2023/1336.pdf).
- **CoW Protocol** — batches settled at a **uniform clearing price (UCP)**, Coincidence-of-Wants
  matched P2P, solver competition off the public mempool (https://cow.fi/learn/understanding-batch-auctions).
  **Limit (per DREX-DESIGN §1):** the permissioned/bonded solver's winning solution carries **no
  validity/optimality proof** — trust is competition + slashing + after-the-fact detection.
- **Balancer LBP** — time-dependent dynamic weights make price *decay over time absent buying*,
  starting *high* so whales/bots are disincentivized (https://docs.balancer.fi/concepts/explore-available-balancer-pools/liquidity-bootstrapping-pool/liquidity-bootstrapping-pool.html).
  **Limit:** rests on high-start-price + **owner honesty** (owner sets/pauses the schedule).
- **Sealed-bid commit-reveal** — commit `H(bid, salt)`, later reveal; prevents observe-and-copy during
  bidding (a16z, https://a16zcrypto.com/posts/article/hidden-in-plain-sight-a-sneaky-solidity-implementation-of-a-sealed-bid-auction/).
  **Limits:** griefing/selective non-reveal (arXiv 2606.14939, https://arxiv.org/pdf/2606.14939),
  commit-tx metadata leakage, capital lock, lost-salt UX; the frontier fix is ZK/TEE sealed bids.

**Cross-cutting takeaway:** the dominant abuse is *not* the classic LP-drain (curves + LP-burn blunt
that) — it is **launch-block sniping/bundling by fresh coordinated wallets** and **insider
pre-allocation**, plus wash-traded fake volume, at industrial scale. And **every deployed anti-abuse
feature is explicitly a mitigation, not a guarantee.** The strongest structural defenses (batch
uniform-price → neutralize *speed*; LBP → neutralize *whale size*) each import a new trust surface. ZK
sealed bids + verified clearing are the frontier — which is exactly dregg's proven substrate.

---

## 2. The dregg mechanism — a launch is four verified turns

A dregg launch is not a bonding-curve contract you trust; it is a **composition of four proof towers**,
each already carrying a Lean keystone. A "launch" is: (1) a disclosed-supply **creation turn**, (2) a
**sealed-bid batch raise** cleared at a **uniform fair price**, (3) graduation into a **provably-solvent
pool**, (4) settlement of proceeds **non-custodially, cross-chain**. Each side-structure plugs into the
core effect-VM through the uniform `{proof, committed-claim, trust-grade, state-delta}` interface of
`docs/deos/EFFECTVM-SIDESTRUCTURE-ABI.md` — a forged committed-claim is UNSAT, so no root mints.

### 2.1 Creation — a disclosed-supply mint turn (no hidden supply is expressible)

Token creation is a privileged mint executed through the verified per-asset executor. The supply is
**disclosed by construction** because minting is governed by the supply-authority biconditional:
`Dregg2.Circuit.Spec.SupplyCreation.execMintA_iff_spec` — the executor commits a mint **iff** the
independent `MintASpec` is satisfied (a real post-state, frame and all), and it is non-vacuous
(`execMintA_iff_spec_satisfiable`, `metatheory/Dregg2/Verify/KeystoneAuditSupply.lean:83`). Two
consequences that are *theorems*, not policies:

- **Every mint is an authorized, disclosed executor turn.** A mint requires a **live issuer cell**
  (`recKMintAsset_requires_live_issuer_satisfiable`, `:105`) — asset 7's issuer not in `accounts` ⇒ the
  mint does not commit. There is no path to circulating supply that is not a recorded, conserving
  (`recKMintAsset_delta_satisfiable`, `:93`), issuer-authorized turn. **A supply the schedule does not
  disclose cannot enter circulation** — the ledger has no other mint door.
- **The launch descriptor commits the whole schedule.** Creation posts, in one turn's committed claim:
  total supply, the vesting schedule (as a monotone unlock predicate — a bounded `Pred` in the effect
  VM), the creator allocation and its lock, and the raise parameters. These are *public inputs of the
  proof*, so a launch page can display them and a re-executor can check them (REPLAYABLE).

The mint is the same `recKMintAsset` the `#keystone_audit` pins to the three kernel axioms
(`KeystoneAuditSupply.lean:145`). **Trust grade: PROVED** (the mint/burn biconditional + live-issuer
gate + conservation are machine-checked Lean).

### 2.2 The raise — a batch cleared at one uniform fair price (the robust anti-snipe lever), privacy-hardened by sealed bids

This is the heart. The anti-snipe guarantee has two layers, and the load-bearing one is **not** the
sealed-bid privacy — it is the **uniform-price batch clearing**. The privacy over the bids sits *on top*
of that lever in three honest grades (MVP floor → strong dregg-native upgrade).

**The robust lever — batch clearing at one uniform price.** The raise does not fill at bid-time
price-priority — it **clears the whole book at a single uniform price** through the DrEX tower. Clearing
at one price removes the *value of ordering*: there is no earliest block to win, no time-priority edge,
nothing an inclusion-order advantage can buy. **So the sniper edge dies regardless of the privacy layer
over the bids** — this is the robust, primitive-independent anti-snipe guarantee, and it is what the
launchpad contract already does today.

- Bids aggregate faithfully (`Market.aggregate` — a permutation-sorted book, **no drop / no insert**:
  `aggregate_faithful`, `no_drop`, `no_insert`, `Market/Aggregation.lean`). A hidden extra allocation
  cannot be inserted into the cleared book without failing `no_insert`.
- The book clears **multilaterally, conserving and fair**: `clearing_conserves_per_asset` (Σ-in = Σ-out
  through the real ledger measure `toBal`) and `clearing_respects_limits` (`Market/Fairness.lean:112`)
  — every participant stays within its declared bid; over-debit / wrong-asset clearings **never form**
  (`overdebit_refused`, `wrongAsset_refused`).
- The clearing is at a **single uniform price** with the marquee optimality guarantee:
  `uniform_price_no_arbitrage` (`Market/Optimality.lean:130`) — **every leg is value-neutral in the
  numéraire**, and `no_improving_deviation` — no feasible deviation at the uniform price strictly
  improves (the FBA optimality reading). `uniform_price_envy_free` — any two same-direction
  participants clear at the same rate. `uniform_price_optimal` composes it with rung-5 individual
  rationality: **sound *and* optimal as one theorem.**

This is the FBA/Gnosis/CoW fair-launch mechanism (§1.4) with the trust surface those designs *cannot
remove* — dregg's clearing carries a **validity + optimality proof**, where CoW's solver carries none
(DREX-DESIGN §1). Everyone who clears pays the **same** price; there is no order to front-run, no
earliest block to win. **Trust grade: PROVED** (uniform-price no-arb + conservation + limits, all
machine-checked); the one open weld is the `MarketRefinement` slash-leg alignment (§5).

**The privacy layer over the bids — three grades.** Batch clearing kills the *ordering* edge; a privacy
layer over the bids additionally denies a would-be sniper the *content* to react to (bid values, and the
mempool visibility batch designs like Gnosis/CoW cannot themselves remove, §1.4). dregg offers this in
three honest grades:

- **MVP floor — sealed commit→reveal.** Participants submit sealed bids into `Dregg2.Intent.SealedAuction`
  (`metatheory/Dregg2/Intent/SealedAuction.lean`). A `Bid` is `(bidder, value, nonce)`; its seal is
  `Blake3(bidder ‖ sign ‖ |value| ‖ nonce)` (`sealOf`, `:104`), resting on the *real* collision-resistant
  carrier `Blake3Kernel` — not `True`. The keystones do bite and are PROVED: `reveal_binds_committed`
  (`:248`) — **no late-switching** (a valid reveal opening a committed seal *is exactly* the bid that
  sealed it, non-vacuous, FALSE for a constant hash); `reveal_requires_reveal_phase` (`:216`) +
  `commit_noop_off_phase` (`:198`) — fail-closed phase ordering; `uncommitted_cannot_open` (`:260`) /
  `uncommitted_cannot_win` (`:415`) — a party whose seal was never committed can never win. **But
  commit→reveal is a weak privacy primitive**, and the design names its limits honestly rather than
  leaning on it as the marquee — it is the crude sealed-bid primitive `SealedAuction.lean` implements:
  1. **Selective non-reveal griefing** — a losing bidder can withhold the reveal, a stealth
     retraction/manipulation vector (arXiv 2606.14939, §1.4).
  2. **Metadata leak** — value is hidden, but the committing address, timing, and frequency are not, and
     are correlatable across launches.
  3. **The reveal round favors bots over humans** — a second timed transaction advantages exactly the
     automated actors the mechanism is meant to blunt (self-defeating for an anti-bot design).
  4. **Two-tx capital-lock UX** — commit then reveal, capital locked across the window.

  **MVP hardening (cheap, buildable now):** a **reveal-deposit/bond forfeited on non-reveal** makes
  withholding cost — it turns weakness (1) into an economic event — carried until shielded bids land.
  **Trust grade: PROVED** for the no-peek/no-switch theorems, but graded as the **MVP floor**, not the
  anti-snipe core.

- **Strong dregg-native upgrade — shielded / ZK-sealed bids (DrEX rung 3).** The frontier the research
  names ("ZK-sealed bids + MPC auctions") — and dregg sits in the **ZK-sealed-bid** category, not the
  threshold-encryption/committee one. `Market/ShieldedClearing.lean` (`shielded_ring_clears`,
  DrEX **rung 3, private matching**) is a **single-phase** clearing over *hidden commitments*: there is
  **no reveal round** (which deletes weaknesses 1, 3, and 4 outright), and it **deletes the committee**
  (no t-of-n threshold-decryption trust surface). The matcher reads only the committed claims
  (`clearing_respects_limits` over `MatchNode`), settles by spending **nullifiers** (`unshieldK`, never
  revealing owner or value), and conservation is checked over the Pedersen commitments alone
  (`shielded_ring_value_conserves_hidden` — homomorphic excess zero, no value revealed). **No party ever
  holds the plaintext or the ordering power.** *Honest grade — SPEC/MODEL:* rung 3 is a Lean spec with
  **toy commitment/Merkle stand-ins** (`MemberAtRoot`) and the **ring AIR unbuilt** — the value-commitments-in-AIR
  weld tying `MatchNode` offer/want to the hidden note is named as a **MEDIUM→RESEARCH AIR build**, and the
  *shielded-bid launchpad* weld (bidding through the shielded pool) is the named upgrade, **not built**
  (§5). It is graded exactly as the report grades it — spec/model, the named frontier, not a live claim.

So the story is: **batch uniform-price clearing is the robust anti-snipe lever (PROVED, live in the
contract, primitive-independent); commit→reveal is the honest MVP privacy floor (PROVED theorems, weak
primitive, non-reveal-forfeit hardening); shielded/ZK-sealed bids are the strong dregg-native privacy
upgrade (rung-3 SPEC/MODEL, the research-named frontier).**

### 2.3 Graduation — into the provably-solvent pool (the bonding curve, done right)

After the raise clears, the token graduates into a standing **liquidity pool** — the AMM — which is the
DrEX rung-6 `Market.Pool`. Its guarantee is the one no AMM ships: a **solvency theorem**.

- **`pool_solvent_forever` (`Market/Liquidity.lean:145`) — THE KEYSTONE.** Starting solvent, under
  **any** valid schedule of fills the pool's per-asset reserve is **never negative** — the clearing can
  never drive the pool insolvent. Each fill can only pay out what it holds (`PoolFillValid`); an
  overdraw is `¬ PoolFillValid` and provably drives a reserve below zero (both polarities).
- **`pool_fill_conserves` (`:82`) / `pool_absorbs_netFlow` (`:88`)** — every pool fill is zero-sum with
  the order it clears; the pool never mints or burns. `pool_backing_solvent_forever` (`:162`) — the
  pool's disclosed backing line is itself solvent forever (reused `stripe_reserve_solvent_forever`).
  **The pool is never insolvent AND never funded from thin air.**

Honest scope (from the file): this proves the **reserve-priced pool that is provably never negative** —
the core never-insolvent claim. The **constant-function `x·y=k` curve** as a `MarketClearing`-preserving
family (pricing the fill off the curve, proving `x·y` non-decreasing) is layered *on top* of this
solvency floor — **named, not yet built** (UNBUILT). A never-insolvent pool with a stated price is the
load-bearing guarantee; the curve is the pricing policy above it. Graduated LP is pool-owned and
solvency-bound — **there is no LP-withdrawal door for the creator to open** (contrast §1.1's
graduation-stage-only burn). **Trust grade: PROVED** (solvency + conservation); **UNBUILT** (the `x·y=k`
pricing curve above the floor).

### 2.4 Settlement — non-custodial, cross-chain, optionally shielded

- **Non-custodial proceeds.** The raise proceeds settle through the verified ring executor
  (`settleRing`, all-or-nothing, `settleRing_conserves` / `settleRing_atomic`, reused by the auction's
  `settle_atomic` `:366` and `settle_conserves` `:383`). Funds route through the **real Lean FFI
  executor** (`intent/src/verified_settle.rs` → `@[export] dregg_record_kernel_step` over proved
  `Exec.recKExec`) — "an intent fulfilled LITERALLY MEANS a verified, conserving, authorized executor
  turn executed" (`docs/deos/DREGGFI-AMBITION.md:32`). **BUILT/PROVED** (FFI-refined ring).
- **Cross-chain participation (networked proofs of holdings).** A participant on another chain proves
  their holdings — Solana accounts-inclusion under ≥2/3-stake supermajority (**REAL**, forgery closed),
  an EVM ERC-20 storage proof, a Cosmos bank-balance proof — and binds identity non-custodially (the
  Ed25519/secp256k1/bech32 binding trilogy), *without moving tokens into a bridge*
  (`docs/deos/INTERCHAIN-MODEL.md`). Outbound, a genuine Groth16 proof of the dregg raise **verifies
  on-chain** on EVM (Foundry, forgeries reject, four adversarial audits — on dev ceremony, not
  mainnet). **dregg networks *proofs*, not tokens** — no bridge validators to corrupt. **Trust grade:
  ATTESTED/REAL per-chain** (Solana inbound REAL; EVM outbound REAL; Cosmos/Mina in-progress/scoped —
  the honest per-chain table is INTERCHAIN-MODEL §"Per-chain maturity").
- **Optional private participation (shielded).** Two distinct privacy paths, at two distinct grades.
  *(a) Identity privacy — the shielded pool (BUILT).* A participant may settle through the multi-asset
  **shielded pool** (`circuit-prove/src/shielded/`, `docs/deos/SHIELDED-CELLS.md`), riding Plonky3's
  `HidingFriPcs` (statistically-ZK, salted leaves, zero AIR changes) with PI
  `[nullifier, merkle_root, value_binding]`. This makes participation private without a hidden-supply
  door (the *mint* is still the disclosed §2.1 turn; only the *participant identity* is shielded).
  *(b) Shielded bidding — the rung-3 ZK-sealed-bid clearing (SPEC/MODEL).* The **strong** privacy grade
  from §2.2: `Market/ShieldedClearing.lean` (`shielded_ring_clears`, DrEX rung 3) clears the *raise
  itself* over hidden commitments — single-phase, no reveal round, no committee — and is the dregg-native
  answer to the research's "ZK-sealed bids" frontier. Both sit **BESIDE** the core today (no
  leaf/expose/bind for the pool; toy Merkle/commitment stand-ins and an unbuilt ring AIR for the rung-3
  clearing), so weaving shielded *bidding* into the launchpad effect stream through the side-structure ABI
  is a **weld** (§5). **Trust grade: BUILT** (the ZK pool, identity privacy) + **SPEC/MODEL** (the rung-3
  shielded-bid clearing) + **UNBUILT** (the launchpad-effect binding for either).

---

## 3. The abuse → antidote table (graded PROVED / bonded / designed)

The honest headline: **three of the seven abuse vectors are UNCONSTRUCTABLE** — a theorem forbids the
mechanism, so the platform has no code path that produces them. **Two are DISINCENTIVIZED** by the
conduct bond (economic, not absolute). **Two dregg does NOT fully solve** — they live at the identity
layer or in human judgment, and §5 says so plainly.

| Vector (§1.2) | dregg antidote | Rests on (primitive) | Grade |
|---|---|---|---|
| **B — Snipe / bundle** | **UNCONSTRUCTABLE (ordering edge), privacy-hardened over the bids.** The robust lever is **batch uniform-price clearing**: one price removes the *value of ordering* — no earliest block to win, no time-priority — so the sniper edge dies *regardless of the privacy layer* (`uniform_price_no_arbitrage`). Over the bids, a privacy layer denies the sniper the *content* to react to: the **MVP floor** is sealed commit→reveal (`uncommitted_cannot_win`, but a weak primitive with named limits — §2.2), and the **strong** upgrade is shielded/ZK-sealed bids (rung-3, SPEC/MODEL). | DrEX `uniform_price_no_arbitrage` (`Optimality.lean:130`) **[lever]**; `SealedAuction.uncommitted_cannot_win` (`:415`), `reveal_binds_committed` (`:248`) **[MVP floor]**; `Market/ShieldedClearing.shielded_ring_clears` **[strong, spec/model]** | **PROVED** (batch lever + commit-reveal floor) / **SPEC** (shielded upgrade) |
| **C — Insider / hidden allocation** | **UNCONSTRUCTABLE (supply half).** No mint enters circulation except the disclosed, issuer-authorized creation turn — `execMintA_iff_spec`; no undisclosed supply door exists. No extra allocation can be inserted into the cleared raise book — `no_insert`. **(Buying half → bond, see F/D.)** | `KeystoneAuditSupply.execMintA_iff_spec_satisfiable` (`:83`), `requires_live_issuer` (`:105`); `Market/Aggregation.no_insert` | **PROVED** (that *hidden* supply is impossible); the creator openly buying at the same uniform price as everyone is **not** an edge (uniform price) — undisclosed pre-buy is bonded (§4) |
| **A — Dev-rug (LP drain / mint-drain)** | **UNCONSTRUCTABLE (two doors) + BONDED (schedule).** Graduated LP is pool-owned and `pool_solvent_forever` — no creator LP-withdrawal door. Mint-authority use after creation is an *authorized recorded turn* (`execMintA_iff_spec`), so a post-launch mint is publicly visible and a **conduct-bond slashing predicate** (§4). Dumping beyond the disclosed vesting schedule is the primary **bond predicate**. | `Market/Liquidity.pool_solvent_forever` (`:145`); `KeystoneAuditSupply`; §4 conduct bond | **PROVED** (no silent LP/mint door) + **BONDED** (schedule-violation dump) |
| **D — Curve manipulation** | **UNCONSTRUCTABLE (raise) + BONDED (pool).** In the raise there is no curve to manipulate — it is a batch uniform-price clearing (no per-tx price impact to game). In the graduated pool, uniform-price/CoW batching removes intra-batch reorder profit (`no_improving_deviation`); coordinated wash-pumps are a bond predicate + a detection matter (§5). | DrEX `uniform_price_no_arbitrage`, `no_improving_deviation` (`Optimality.lean`); §4 | **PROVED** (raise) + **BONDED/designed** (pool) |
| **F — Pump-and-dump** | **BONDED, not solved.** Mechanism design cannot forbid a holder choosing to sell; dregg forbids the *creator's* schedule-violating dump (bond predicate) and removes the snipe/insider *ammunition* (B, C). A community pump of a freely-held token is not a platform-constructable abuse. | §4 conduct bond (dump-beyond-schedule); B+C remove the pre-loaded ammunition | **BONDED** (creator) / **NOT SOLVED** (organic holders) |
| **E — Wash trading** | **DESIGNED, not solved by construction.** Uniform-price batch clearing makes *self-trading for price* pointless (you clear against yourself at one price, net zero, still paying the spread/fee). But volume-faking for *attention* remains; dregg's answer is the **REPLAYABLE** OCIP screener (wallet-cluster + Benford anomaly re-derivable over public state) + the bonded-not-boosted attention market — detection, not prevention. | OCIP screener/attention market (`DREGGFI-VISION.md:73`) — **UNBUILT** as product; DrEX uniform price removes *price*-motivated wash | **designed-not-built** |
| **G — Sybil** | **NOT SOLVED at the mechanism layer (honest).** One human with many wallets defeats per-wallet caps. dregg mitigates the *consequence* (uniform-price clearing makes many-wallet splitting yield no better price than one wallet — sybil buys nothing in the raise), but genuine identity-uniqueness is an **identity-layer** problem (proof-of-personhood, non-custodial binding raises cost but not to a proof). | Uniform price neutralizes sybil *advantage* in the raise; identity binding (INTERCHAIN trilogy) raises cost | **partial** — advantage neutralized in-raise (**PROVED**), uniqueness **NOT SOLVED** |

**Headline for the report:** UNCONSTRUCTABLE (a theorem forbids the mechanism) = **snipe/front-run (B),
hidden supply (C-supply), silent LP/mint-drain rug (A-doors), raise-time curve manipulation (D-raise)**.
DISINCENTIVIZED by bond (economic) = **schedule-violating creator dump (A/F-creator), post-launch
mint-authority use**. NOT fully solved = **wash-trading-for-attention (detection only), sybil uniqueness
(identity layer), and organic pump-and-dump of a freely-held bad token**.

---

## 4. The conduct bond — bonded-not-boosted, slashes compensate holders

The OCIP §9 / DREX-DESIGN §6 pattern (`docs/deos/DREX-DESIGN.md:210`): the creator **posts a conduct
bond** at creation, slashed on **mechanical on-chain misconduct predicates** that are **REPLAYABLE** (a
pure function over public state anyone re-derives), and **slashes compensate holders, never the
platform.** This is the economic layer over the constructable-abuse floor of §2–3 — it disincentivizes
what a theorem cannot forbid (a creator's discretionary conduct).

The primitive exists in adjacent form and is honestly not yet wired to launch predicates: a real
bond+slash with **conserving** restitution (`restitution + remainder == seized`,
`node/src/relay_dispute.rs`, `node/src/slash_treasury_mirror.rs`) is BUILT for relay operators; the
solver-bonding field `SolverSubmission.bond` exists in `trustless.rs`. Wiring these to launch conduct
predicates is **design, not new science** (DREGGFI-PREREQS 4.7 marks the *attention-market* framing
UNBUILT; the bond/slash *conservation* is PROVED).

**The misconduct predicates (all REPLAYABLE — re-derivable from public ledger state):**

1. **`dump_beyond_schedule`** — the creator's cumulative sells of its own allocation exceed the
   disclosed vesting unlock at the current epoch. The vesting schedule is a committed monotone `Pred`
   from the creation turn (§2.1); the predicate is `soldSoFar(creator) > unlocked(schedule, epoch)`.
   Slash proportional to the over-sell. **This is the primary anti-rug tooth** — it makes the
   §1.3-vesting failure ("unlocks are scheduled dumps") a *bonded* event.
2. **`unauthorized_mint_use`** — any post-creation mint of the token's asset that was not disclosed in
   the creation schedule. Because every mint is a recorded `execMintA` turn (§2.1), this predicate is
   `∃ mint turn t : t.asset = token ∧ t ∉ disclosedSchedule`. Slash the full bond (mint authority abuse
   is categorical). This closes the "hidden inflation after launch" door economically on top of the
   PROVED disclosure.
3. **`raise_proceeds_diversion`** — the settled raise proceeds route to a destination other than the
   disclosed treasury/LP-seeding path within the graduation turn. Checkable against the committed
   settlement claim (§2.4). Slash the diverted amount.
4. **`liquidity_pull_attempt`** — any turn attempting to remove graduated pool reserves outside the
   disclosed schedule. (Structurally near-impossible by `pool_solvent_forever` + pool ownership, but
   the predicate makes even an *attempt* — e.g. via a governance path — a slashing event.)
5. **`false_disclosure`** — the on-ledger realized supply/allocation diverges from the committed
   creation schedule. Since supply is PROVED-disclosed, this fires only on an off-ledger
   misrepresentation surfaced by the REPLAYABLE screener; slash the bond, compensate holders.

**Slash routing.** Every slash flows to a **holder-compensation pool** distributed pro-rata to current
token holders (never to the platform), through a conserving settleRing (the `restitution + remainder ==
seized` invariant, already PROVED for relay disputes). The platform earns fees on *volume and
creation*, never on slashing — removing the incentive to manufacture misconduct. **Trust grade:**
predicates REPLAYABLE; slash-conservation PROVED (relay-dispute primitive); the **launch-predicate
wiring + the `MarketRefinement` slash-leg refinement is the open weld** (§5) — the abstract predicate
binds the executor only through a `_refines_` theorem, and that alignment "is still open" (DREGGFI-VISION
`:86`).

---

## 5. Honest gaps + the build path

### 5.1 Buildable now (composes on proven pieces)

- **The sealed-bid raise + uniform-price clearing (§2.2)** — `SealedAuction` + DrEX rungs 1/4/5 are all
  PROVED and Lake-green *today*. The launchpad's anti-snipe core is a *composition*, not new science:
  wire `SealedAuction`'s revealed bids as the `Order` stream into `Market.aggregate` → clearing. This is
  a **NEAR** lift (a Lean-tower composition on substrate that exists).
- **The disclosed-supply creation turn (§2.1)** — `execMintA_iff_spec` + live-issuer gate are PROVED;
  the launch descriptor is a committed-claim over existing effect-VM `Pred` machinery.
- **The solvent pool graduation (§2.3, floor)** — `pool_solvent_forever` is PROVED; graduation routes
  raise proceeds into the pool's reserves.
- **Cross-chain inbound (Solana) + outbound (EVM)** — REAL today (INTERCHAIN-MODEL).

### 5.2 Needs a weld (real build, named)

- **The `x·y=k` pricing curve above the solvency floor** — UNBUILT (Liquidity.lean says so). The
  solvency *floor* is proved; the *pricing policy* on top is a `MarketClearing`-preserving family to
  build.
- **The shielded-participation binding (§2.4) + the rung-3 ZK-sealed-bid clearing (§2.2, strong grade)** —
  the ZK pool is BUILT for *identity* privacy but **BESIDE** the core (no leaf/expose/bind,
  EFFECTVM-SIDESTRUCTURE-ABI census #1); the rung-3 shielded-bid clearing
  (`Market/ShieldedClearing.shielded_ring_clears`) is a **SPEC/MODEL** with toy Merkle/commitment
  stand-ins and an **unbuilt ring AIR** (the value-commitments-in-AIR weld is a MEDIUM→RESEARCH build).
  Weaving shielded *bidding* into the launchpad effect stream is a side-structure-ABI conformance build
  on top of that AIR — the named strong-privacy upgrade over the commit→reveal MVP floor.
- **The conduct-bond launch predicates + slash-leg refinement (§4)** — the bond/slash *conservation* is
  PROVED for relay disputes; the *launch* predicates and the `MarketRefinement` slash-leg `_refines_`
  alignment are the open instance (DREX-DESIGN `:219`, DREGGFI-VISION `:86`). This is "design, not new
  science" but it is not yet written.
- **The OCIP screener / bonded attention market (§3-E)** — UNBUILT as product (DREGGFI-PREREQS 4.6/4.7,
  grep-empty); this is the wash-trading *detection* lane.
- **The live deploy** — a live dregg devnet/testnet with settlement contracts you can point a tx at is a
  prerequisite (DREGGFI-PREREQS Track "live devnet"); VK-epoch flip + re-genesis are ember-gated.

### 5.3 What dregg does NOT solve (no overclaim)

- **A bad token is still a bad token.** Mechanism design fixes the *rigged wheel*, not the *casino*. A
  fairly-launched, honestly-disclosed, un-rugged token can still be a worthless meme that goes to zero.
  dregg guarantees the *distribution and disclosure* are fair — it makes **no claim about the token's
  value or the creator's competence.** (This is exactly the §1.3 failure "hype-over-shipping": fair
  distribution is irrelevant once trust in the project collapses.)
- **Sybil uniqueness is an identity-layer problem.** dregg neutralizes the sybil *advantage* in the
  uniform-price raise (many wallets buy no better price than one) — PROVED — but cannot prove one human
  ≠ many wallets. Proof-of-personhood is out of scope; the non-custodial binding raises cost, not to a
  proof.
- **Wash-trading-for-attention is detection, not prevention.** Uniform-price clearing kills
  *price*-motivated wash trades; *volume-faking for attention* is caught by the REPLAYABLE screener
  (statistical, after-the-fact) — the same fundamental limit the whole industry faces (Nasdaq, §1.2-E).
- **Organic pump-and-dump of a freely-held token.** dregg forbids the *creator's* schedule-violating
  dump (bonded) and removes the *pre-loaded ammunition* (snipe/insider, PROVED) — but it cannot and does
  not forbid free holders from collectively buying then selling. That is a market, not an abuse the
  platform constructs.

---

## 6. The one-paragraph thesis

Every deployed launchpad's anti-abuse feature is, by the platforms' own admission, a *mitigation* —
pump.fun says its guardrails "do not eliminate market risk," anti-snipe is "not a guarantee of
fairness," and "fair launch" is a label unless the platform is decentralized and audited. dregg's
difference is that its three dominant abuses become **theorems you can't route around, not settings you
tune**: sniping and time-priority front-running are unconstructable (batch uniform-price clearing
removes the *value of ordering* — the robust lever — hardened by a privacy layer over the bids that runs
from a commit→reveal MVP floor up to shielded/ZK-sealed bids, PROVED), hidden supply is unconstructable
(the mint biconditional, PROVED), and the silent
LP/mint-drain rug has no door (pool solvency + disclosed mint, PROVED). What a theorem cannot forbid —
a creator's discretionary conduct — a **holder-compensating conduct bond** disincentivizes with
REPLAYABLE misconduct predicates. And what neither can fix — a bad token, sybil uniqueness, wash-trading
for attention — dregg names honestly rather than overclaiming. **The launchpad where fairness is a
theorem** is precise: fairness *of distribution and disclosure* is a theorem; the value of what you buy
is still, always, your own bet.

---

## Sources

**dregg primitives (read to confirm, cited by file:line):**
`metatheory/Dregg2/Intent/SealedAuction.lean` · `metatheory/Market/{Clearing,Fairness,Optimality,Priced,Aggregation,Liquidity}.lean`
· `metatheory/Dregg2/Verify/KeystoneAuditSupply.lean` · `docs/deos/{DREX-DESIGN,DREGGFI-VISION,DREGGFI-AMBITION,DREGGFI-PREREQS,INTERCHAIN-MODEL,SHIELDED-CELLS,EFFECTVM-SIDESTRUCTURE-ABI}.md`
· `intent/src/verified_settle.rs` · `node/src/{relay_dispute,slash_treasury_mirror}.rs` · `circuit-prove/src/shielded/`

**Landscape (Kagi FastGPT, 16 queries):** Solidus Labs / BeInCrypto (98.6% stat); arXiv 2507.01963,
2206.08202, 2607.02795 (abuse taxonomy + $-scale + 1,012 sniper cohorts); pump.fun docs + Binance Square
(creator lock); Blockworks + OpenLiquid (sniper tax / anti-snipe limits); j.tools + Meteora + NOXA +
Virtuals + BingX (curve models); Budish-Cramton-Shim QJE 2015 + SAFE WP 344 (FBA); Gnosis/HackMD + Riggs
eprint (batch auction + sealed-bid limit); cow.fi (UCP); Balancer docs (LBP); a16z + arXiv 2606.14939
(commit-reveal + griefing); capwolf + defiprime (fair-launch/vesting failures); cryptotracelabs + Nasdaq
(wash-trading detection). Full URLs inline in §1.
