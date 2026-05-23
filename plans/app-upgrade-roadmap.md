# App Upgrade Roadmap: Integrating New Platform Features

Generated: 2026-05-23

## Individual App Upgrades

### Stablecoin (CDP)

Current: Users lock collateral in escrow and mint PUSD. STARK proofs enforce collateral ratio >= 150%. Liquidators seize undercollateralized positions.

Upgrades:
- **Programmable queues**: Liquidation queue with priority ordering (lowest-health-factor-first). Validators enforce that enqueued liquidations are genuinely undercollateralized before processing. Prevents griefing/spam liquidation attempts.
- **Ring trade solver**: CDPs that want to swap collateral types (e.g., ETH->BTC backing) can participate in ring trades without going through a common denominator. User wanting to rotate collateral finds cycles: "I close ETH CDP, you close BTC CDP, I open BTC CDP, you open ETH CDP" -- all atomic.
- **Executor delegation**: Mobile CDP owners delegate ratio monitoring + emergency repayment to a cloud executor. Phone signs a scoped delegation: "if ratio < 160%, repay from my reserve." Executor batches proofs for multiple CDPs.
- **Multi-asset fees**: Mint fees and stability fees payable in any accepted token, not just the native computron. Accept PUSD itself for fees (self-referential but useful for UX).
- **KZG polynomial queues**: Oracle price feed as a KZG queue. O(1) proof that "the price I used was the official oracle price at position N." Eliminates the current attestation-per-mint pattern.
- **Store-and-forward inboxes**: Liquidation alerts delivered to CDP owners' inboxes even when offline. Owner comes back online, sees "your position was at 155%, action needed."
- **CapTP provable effects**: Mint/burn as provable capability operations. An agent holding a PUSD-mint capability can prove "I minted X PUSD with proof Y" to a third party without revealing their identity.

Priority: HIGH
Estimated effort: ~800 LOC, 4 agent-hours


### AMM (Constant-Product Market Maker)

Current: Liquidity pools with swap/add/remove operations. TurnComposer for atomic execution. Multi-hop router for A->B->C swaps.

Upgrades:
- **Ring trade solver**: THE killer upgrade. Instead of multi-hop (A->B->C with slippage at each hop), find ring trades: A->B, B->C, C->A settle atomically. No intermediate slippage. Solver finds optimal ring from live intent pool.
- **Programmable queues**: Swap intent queue with time-weighted batch execution. Queue collects swaps for 1 block, then executes them all at the same TWAP price. Eliminates MEV/sandwich attacks entirely.
- **Blinded queues**: Private LP withdrawal. LPs commit to withdrawal; nobody (including other LPs) knows who's withdrawing until execution. Prevents "exit stampede" front-running.
- **Executor delegation**: High-frequency arbitrageurs delegate swap execution to fast executors. Mobile LPs delegate rebalancing to a cloud service that monitors pool ratios.
- **Multi-asset fees**: Swap fees denominated in either pool token. LP rewards accumulate in the token the LP prefers.
- **KZG polynomial queues**: TWAP oracle as KZG queue. Each block's price is a point on the polynomial. Anyone can prove "average price over blocks N..M" with O(1) proof.
- **Dataflow pipelines**: Price oracle -> filter(staleness) -> route(by_pair) -> [pool_a_oracle, pool_b_oracle]. Automatic price propagation across pools.
- **Unified blocklace**: Pools spanning multiple reference groups. A pool exists across Group A and Group B; LPs from either group can provide liquidity visible to both.

Priority: HIGH
Estimated effort: ~1200 LOC, 6 agent-hours


### Orderbook (Verified Matching Engine)

Current: Commit-reveal order submission (anti-frontrunning), pre-trade escrow, STARK proofs of fair matching, Merkle state commitments, dark pool privacy mode.

Upgrades:
- **Ring trade solver**: Cross-pair atomic settlement. User has order on ETH/USDC book and another on BTC/ETH book -- solver finds a ring that fills both atomically. This is "cross-pair netting."
- **Blinded queues**: Fair order batch processing. Orders submitted to a blinded queue; nobody (including the matcher) sees the queue ordering until the batch window closes. Stronger than commit-reveal because even the queue operator cannot reorder.
- **KZG polynomial queues**: O(1) position proofs. "My order is at position 7 in the book" provable with a single G1 point instead of a Merkle path. Order-of-magnitude improvement for inclusion verification.
- **Programmable queues**: Settlement queue with constraints: "fill only if resulting spread <= X bps." Programmatic circuit validation on every fill before it enters the settlement pipeline.
- **Executor delegation**: Market makers delegate order management to fast executors. MM signs: "adjust my quotes within +/- 5bps of oracle." Executor batches proof updates for 100s of resting orders.
- **DFA routing**: Order routing by path. `/markets/eth-usdc/limit/buy` routes through access control DFA that enforces "only KYC'd cells can access this path." Multi-tier market access without separate order books.
- **Unified blocklace**: Cross-federation order books. A book spans multiple reference groups; orders from Federation A match against orders from Federation B. Requires cross-group state proofs.

Priority: HIGH
Estimated effort: ~1000 LOC, 5 agent-hours


### Lending (Utilization-Based)

Current: Multi-market lending pool with supply/borrow/liquidate. Interest accrual via TemporalPredicate. Health factor enforcement via STARK circuit. ConditionalTurn for liquidation triggers.

Upgrades:
- **Ring trade solver**: Debt recycling rings. Borrower A owes USDC collateralized by ETH; Borrower B owes ETH collateralized by BTC. Solver finds: A repays B's ETH debt, B repays A's USDC debt, net positions improve for both. No liquidations needed.
- **Programmable queues**: Interest accrual queue. Each block's interest update enters a validated queue; validators enforce that the rate model is correctly applied. Prevents rogue interest manipulation.
- **Executor delegation**: THE critical upgrade for lending. Borrowers delegate health monitoring to an executor: "if health < 1.1, repay from my reserve cell." Executor proves the repayment was necessary and correct. Prevents unnecessary liquidation for offline users.
- **Store-and-forward inboxes**: Liquidation warnings delivered to borrower's inbox. "Your health factor is 1.05, action within 50 blocks." Even if user is offline, the message waits.
- **Multi-asset fees**: Borrow fees payable in collateral token. "Pay interest in ETH instead of USDC." Reduces required transactions for borrowers.
- **Dataflow pipelines**: oracle_price -> interest_update -> health_check -> [liquidation_queue, alert_inbox]. Multi-stage pipeline from price feed to liquidation execution.
- **KZG polynomial queues**: Interest rate history as KZG queue. Prove "my average borrow rate over the last 100 blocks was X" for dispute resolution.
- **CapTP provable effects**: Flash loans as capability operations. Borrow + use + repay within one turn, proven via CapTP effect chain.

Priority: HIGH
Estimated effort: ~900 LOC, 5 agent-hours


### Compute Exchange (GPU Marketplace)

Current: Sealed-bid auctions for GPU compute. SLA-bonded providers. Optimistic settlement with dispute windows. STARK delivery proofs as optional evidence. Atomic escrow (payment + SLA bond).

Upgrades:
- **Executor delegation**: THE natural fit. GPU providers ARE executors. "Delegate my STARK proving to this H100 cluster." The compute exchange becomes a market for proof generation itself -- providers prove they proved your circuit.
- **Programmable queues**: Job queue with SLA validation. Queue accepts jobs only if SLA parameters match provider capabilities. Circuit-validated queue prevents overcommitment.
- **Blinded queues**: Fair GPU allocation during high demand. Jobs enter blinded queue; provider cannot cherry-pick profitable jobs. Withdrawal is random (no bias toward easy workloads).
- **Store-and-forward inboxes**: Result delivery to offline consumers. Job completes, result goes to consumer's inbox. Consumer comes back online, retrieves result + proof.
- **Multi-asset fees**: Pay for compute in any token. "I want 10 H100-hours, paying in ETH." Exchange rate oracle converts to computron equivalent.
- **Dataflow pipelines**: job_submission -> qualification_check -> matching -> execution -> delivery_proof -> settlement. Full pipeline from job to payment.
- **Ring trade solver**: Compute bartering. "I have spare A100 time, want H100 time." "I have H100 time, want storage." "I have storage, want A100 time." Ring trade settles all three atomically.
- **DFA routing**: /providers/h100/*, /providers/a100/* routing with access control. Tiered access: verified enterprise gets priority routing to premium GPUs.
- **Nameservice**: Providers register as `compute.h100.acme.pyana` for discovery. Consumers resolve names instead of tracking cell IDs.
- **Unified blocklace**: Cross-federation compute markets. Federation A's consumers access Federation B's GPU providers through unified order matching.

Priority: HIGH
Estimated effort: ~1100 LOC, 6 agent-hours


### Gallery (Privacy-Preserving Art Auctions)

Current: Artwork registration, commit-reveal Vickrey auctions, atomic settlement, provenance chain (ownership history), WebSocket live updates.

Upgrades:
- **Blinded queues**: TRUE Vickrey auctions. Currently bids are committed but the auction operator can see reveal order. With blinded queues: bids enter a blinded queue, withdrawal reveals winner without operator learning intermediate bids. STRICTLY stronger privacy than commit-reveal.
- **Programmable queues**: Bid validation queue. Queue only accepts bids that provably have sufficient escrow backing (circuit-validated). No "bid then fail to fund" scenario.
- **Store-and-forward inboxes**: Auction notifications for offline bidders. "You were outbid" or "You won! Claim within 50 blocks." Messages wait in inbox.
- **Nameservice**: Artists register as `gallery.artist-name.pyana`. Galleries register collections. Makes art discovery human-friendly.
- **Ring trade solver**: Art-for-art trades. "I have Piece A, want something from Collection X." "I have Piece X, want something from Collection Y." "I have Piece Y, want Piece A." Three-way trade settles atomically. Enables non-monetary art exchanges.
- **CapTP provable effects**: Provenance as capability chain. Each transfer is a CapTP delegation: artist -> collector1 -> collector2. The provenance chain IS the capability chain. Proof of authenticity = proof you hold the capability.
- **Multi-asset fees**: Auction fees payable in any accepted token. Commission in ETH, USDC, or the gallery's own token.
- **DFA routing**: /galleries/premium/*, /galleries/public/* with access-controlled viewing. VIP-only previews before public auction.
- **Unified blocklace**: Cross-federation art markets. A piece registered on Federation A can be auctioned on Federation B. Provenance spans federations.

Priority: MEDIUM
Estimated effort: ~900 LOC, 5 agent-hours


### Bounty Board (Federated Bounties with Escrow)

Current: Issuers post bounties with escrow. Workers prove qualifications privately (ring membership STARK, predicate proofs, standing proofs). Blinded worker identity. Conditional turn payment on delivery.

Upgrades:
- **Blinded queues**: Fair bounty claiming. Multiple workers compete; blinded queue ensures first-to-commit gets it without others learning timing. Prevents "snipe the bounty" races.
- **Executor delegation**: Workers delegate proof generation for qualification STARKs to compute providers. "Prove I have standing >= 5 without revealing my identity" is expensive; delegate to GPU executor.
- **Store-and-forward inboxes**: Delivery notifications for offline issuers. Worker completes, submits to issuer's inbox. Issuer reviews when available, approves, payment releases.
- **Programmable queues**: Submission review queue with deadline enforcement. Queue rejects submissions after deadline. Circuit-validated: late submissions cannot enter.
- **Nameservice**: Bounty boards register as `bounties.rust-dev.pyana` or `bounties.design.pyana`. Workers discover boards by category.
- **Multi-asset fees**: Bounties payable in any token. "500 USDC for a logo" or "0.1 ETH for a smart contract audit."
- **CapTP provable effects**: Work delivery as capability chain. Worker proves "I performed action X on cell Y at time T" via effect proof. Stronger than receipt chains -- the proof IS the delivery.
- **Dataflow pipelines**: bounty_creation -> qualification_filter -> worker_match -> submission -> review -> payment. Automated pipeline for simple bounties.
- **Ring trade solver**: Skill bartering. "I'll do your Rust work if you do my design." "I'll do your design if you do my copywriting." "I'll do your copywriting if you do my Rust work." Atomic skill exchange.

Priority: MEDIUM
Estimated effort: ~800 LOC, 4 agent-hours


### Identity (Verifiable Credentials)

Current: Full credential lifecycle (issue/hold/present/verify/revoke). Selective disclosure. Predicate proofs. Anonymous credentials (ring membership). Unlinkability across verifiers. Non-revocation proofs.

Upgrades:
- **Store-and-forward inboxes**: Credential delivery to offline holders. Issuer issues credential, it arrives in holder's inbox. Verification requests also arrive offline.
- **CapTP provable effects**: Credentials AS capabilities. A credential IS a capability token. "Holding credential X grants capability Y." The ZK presentation IS the capability invocation. Natural unification of identity and authorization.
- **DFA routing**: Credential-gated DFA routing. "Access to /services/premium/* requires credential with attribute premium=true." The DFA checks presentation proofs as route guards.
- **Nameservice**: Issuers register as `issuer.university.pyana`, `issuer.employer.pyana`. Verifiers can look up issuers by name instead of raw public key hashes.
- **Blinded queues**: Anonymous credential distribution. University issues 1000 alumni credentials to a blinded queue. Each alumnus withdraws one without the university knowing which credential maps to which student.
- **Executor delegation**: Delegated presentation generation. Mobile holder delegates to a cloud service: "generate presentations on my behalf for requests matching pattern X." The executor holds derived keys, not master keys.
- **Programmable queues**: Revocation queue with circuit validation. Revocations enter a validated queue; only the original issuer's signature can enqueue a revocation.
- **Unified blocklace**: Cross-federation credential verification. Credential issued on Federation A verified on Federation B via blocklace state proof.
- **KZG polynomial queues**: Revocation accumulator as KZG polynomial. "Credential C is NOT in the revocation set" provable with O(1) non-membership witness.

Priority: HIGH
Estimated effort: ~1000 LOC, 5 agent-hours


## Already-Upgraded Apps (Reference)

### Governed Namespace
Already uses: DFA routing, governance voting, capability security, content-addressed VFS.
Potential additions: Multi-asset fees for storage rental, KZG queue for governance proposal ordering.

### Nameservice
Already uses: Registration, resolution, delegation, rental, cross-federation lookups.
Potential additions: Programmable queue for dispute resolution ordering.

### Discord Bot
Already uses: CapTP, programmable queues, governance, nameservice integration.
Potential additions: Ring trade solver for in-Discord token swaps.


## Cross-App Upgrades

These upgrades benefit multiple apps simultaneously when implemented once:

### All DeFi Apps (Stablecoin + AMM + Orderbook + Lending)

| Feature | Benefit |
|---------|---------|
| Ring trade solver | Cross-protocol atomic settlement without common denominators |
| KZG polynomial queues | Shared oracle feed with O(1) price proofs |
| Multi-asset fees | Unified fee UX across all protocols |
| Executor delegation | Single executor manages positions across all DeFi apps |
| Programmable queues | MEV-resistant batch execution across protocols |
| Unified blocklace | Liquidity accessible from multiple reference groups |

Estimated cross-DeFi integration: ~600 LOC shared infrastructure + per-app wiring.

### All Marketplace Apps (Compute Exchange + Gallery + Bounty Board + Orderbook)

| Feature | Benefit |
|---------|---------|
| Blinded queues | Fair allocation/auction across all markets |
| Store-and-forward inboxes | Offline participation in any marketplace |
| Nameservice | Human-readable service discovery |
| Commit-reveal + blinded queue unification | Strictly stronger fairness than commit-reveal alone |

### All Apps (Universal)

| Feature | Benefit |
|---------|---------|
| Nameservice | Every app registers a discoverable service name |
| Multi-asset fees | Every app accepts flexible payment |
| Store-and-forward inboxes | Every app serves offline users |
| CapTP provable effects | Every operation is a provable capability invocation |


## New Cross-App Interactions

These upgrades create interactions between apps that didn't exist before:

1. **Stablecoin + Lending + AMM (DeFi Composability Ring)**
   - Borrow USDC on Lending -> LP into AMM -> Use LP token as collateral for CDP -> Mint PUSD
   - All linked via programmable queues: one queue's output feeds the next protocol's input
   - Ring trade solver finds optimal circular positions across all three

2. **Identity + All Apps (Credential-Gated Access)**
   - Identity credentials gate access to premium features in every other app
   - DFA routing checks credential presentations before granting access
   - "Only accredited investors can use Lending with leverage > 3x"
   - "Only verified artists can list on Gallery"

3. **Compute Exchange + Stablecoin/Lending/AMM (Proof-as-a-Service)**
   - DeFi apps delegate expensive STARK generation to Compute Exchange providers
   - Pay for proofs using DeFi tokens (multi-asset fees)
   - CDP proof, swap proof, liquidation proof -- all offloaded to GPU providers
   - Creates a circular economy: DeFi protocols pay for proving, provers earn DeFi yields

4. **Nameservice + All Apps (Unified Discovery)**
   - `swap.eth-usdc.amm.pyana` resolves to AMM pool endpoint
   - `lend.usdc.market.pyana` resolves to lending market
   - `gpu.h100.compute.pyana` resolves to compute provider
   - Human-readable URLs replace content-addressed cell IDs everywhere

5. **Bounty Board + Identity + Compute (Reputation Pipeline)**
   - Complete bounties -> earn credentials -> use credentials to access premium compute
   - Dataflow pipeline: bounty_completion -> credential_issuance -> qualification_proof
   - Standing proofs from bounty board feed directly into compute exchange qualification

6. **Gallery + AMM + Orderbook (NFT-DeFi Bridge)**
   - Fractionalized art pieces trade on the orderbook
   - Art fractions provide liquidity in AMM pools
   - Ring trades enable art-for-art swaps without going through money
   - Provenance chain integrates with CapTP delegation chain


## Entirely New Apps Enabled

The combination of new features enables apps that weren't possible before:

### 1. Prediction Market (Blinded Queues + Ring Solver + KZG Oracle)
- Outcomes committed to blinded queue (no one knows market sentiment until resolution)
- KZG oracle polynomial proves outcome with O(1) witness
- Ring trades enable "I bet on A, you bet on B, they bet on C" multi-outcome atomic settlement
- ~1500 LOC

### 2. DAO Treasury (Programmable Queues + Executor Delegation + Governance)
- Treasury spending proposals enter a programmable queue (circuit: "only proposals with quorum can dequeue")
- Execution delegated to a trusted executor (multi-sig -> single proof)
- Multi-asset portfolio managed via dataflow pipeline: rebalancing rules as queue programs
- ~1200 LOC

### 3. Privacy-Preserving Voting (Blinded Queues + Identity + KZG)
- Voters deposit vote-commitments into a blinded queue
- KZG polynomial over all votes enables O(1) tally proof
- Identity credentials prove eligibility without revealing identity
- Perfectly private, verifiably correct, O(1) verification
- ~800 LOC

### 4. Subscription Service (Temporal Predicates + Executor Delegation + Inboxes)
- Content creators deliver to subscriber inboxes (store-and-forward)
- Payment executor auto-debits subscribers each epoch (delegated execution)
- Credential-gated content tiers (identity integration)
- Programmable queue validates "only paid subscribers can dequeue content"
- ~1000 LOC

### 5. Cross-Federation DEX (Unified Blocklace + Ring Solver + Blinded Queues)
- Liquidity from Federation A and Federation B visible in single orderbook
- Ring trades settle across federation boundaries atomically
- Blinded queue prevents cross-federation front-running
- First truly decentralized cross-chain DEX without bridges
- ~2000 LOC


## Implementation Priority Matrix

| Priority | App | Key Upgrade | Impact | Effort |
|----------|-----|-------------|--------|--------|
| 1 | AMM | Ring trade solver | Eliminates multi-hop slippage | 6h |
| 2 | Lending | Executor delegation | Prevents unnecessary liquidations | 5h |
| 3 | Orderbook | Blinded queues + KZG position | Strongest fairness + O(1) proofs | 5h |
| 4 | Compute Exchange | Executor delegation + nameservice | GPU-as-a-prover market | 6h |
| 5 | Stablecoin | KZG oracle + programmable liquidation queue | Efficient oracle + fair liquidation | 4h |
| 6 | Identity | CapTP + DFA routing | Credentials become capabilities | 5h |
| 7 | Gallery | Blinded queue Vickrey + CapTP provenance | True privacy + provable authenticity | 5h |
| 8 | Bounty Board | Blinded queues + inboxes | Fair claiming + offline delivery | 4h |
| 9 | Cross-DeFi | Shared ring solver + KZG oracle | All DeFi apps interoperate | 4h |
| 10 | New: Prediction Market | Novel combination | Showcases unique capabilities | 8h |

**Total estimated effort: ~52 agent-hours for full upgrade of all apps.**

## What Makes This Unique

No other platform can do:
1. **Ring trades with ZK privacy** -- settle multi-party cycles where participants prove sufficiency without revealing amounts
2. **Circuit-validated queues** -- messages validated by STARK proof before entering queue (not just signature checks)
3. **Blinded queue auctions** -- operator CANNOT see bid ordering, not just "chooses not to"
4. **KZG oracle with queue semantics** -- O(1) price proofs with guaranteed ordering
5. **Credential-gated DFA routing** -- access control is a proven automaton, not a trusted middleware
6. **Cross-federation atomic settlement** -- ring trades span sovereign federations via blocklace proofs

These are architectural impossibilities on EVM/Solana/Cosmos -- they require the combination of STARK circuits, capability security, and structured queues that only this system provides.
