# $DREGG, computrons, and the units of the dregg economy

*Present-tense, what-is. The canonical statement of what the $DREGG token is, what it
does, what it deliberately does not do, and how it relates to the network's internal
metering unit — so the answer to "what's the tokenomics?" comes from the repo, not a
chat thread. Every claim carries a maturity label: **RUNS** (a test or demo exercises it
green), **BUILT** (real code, not exercised end-to-end live), **NAMED** (stub or doc
only), **VISION** (design doc). Sibling docs: `docs/deos/INTERCHAIN-MODEL.md` (how
proofs cross chains), `docs/deos/PROOF-OF-HOLDINGS.md` (governance weight),
`docs/deos/TOKEN-MIRROR-BRIDGE.md` (the vault).*

## The token in one paragraph

$DREGG is a fixed-supply SPL token native to Solana (~1B units, pump.fun launch). There
is no emission schedule, no inflation, no protocol mint. The architecture reinforces
this rather than hedging it: dregg **networks proofs, not tokens** — other chains verify
proofs *about* dregg state; $DREGG is never minted on another chain
(`docs/deos/INTERCHAIN-MODEL.md`, "What universal means here"). When $DREGG enters
dregg's own state it does so as a 1:1 mirror against tokens locked in a vault, and the
executor refuses any mint that would break `live_supply <= currently_locked`
(`turn/src/executor/bridge_ledger.rs`). Redeeming burns the mirror before release. The
repo deliberately pins **no** mainnet mint address in code; the binding is an operator
env decision (`dregg-pay/src/config.rs`, `DREGG_PAY_MINT`) — confirm the canonical
contract address out-of-band before citing one.

## The four roles of $DREGG (maturity-labeled)

**1. It buys services, never features.** The locked posture across the games and
service surfaces (`docs/GAME-STRATEGY.md`, decisions locked 2026-07-12): $DREGG buys
AI-narration run credits, hosting, cosmetics, entry — never power, never yield.
The payment rail is real code: `dregg-pay/` implements per-user Solana deposit
addresses, an idempotent credit ledger, and dual-asset treasury economics — USDC is
**fuel** (funds real inference, fails closed when empty), $DREGG is the **pile**
(accumulates in an illiquid operator treasury rather than being market-sold; an OTC leg
recycles pile for USDC at a 10% discount, governance-voted, operator-signed). A run
costs $0.10 by default and paying in $DREGG earns a ~20% discount over USDC via a
Jupiter price oracle (`dregg-pay/src/pricing.rs`, `dregg-pay/src/otc.rs`). **RUNS on
mock chains** (`cargo test -p dregg-pay` green end-to-end, Discord bot loop fully
wired); **the mainnet flip has not been made** — the deployed game surface is free to
play, sets no payment env, and the go-live runbook (`docs/ops/PAYMENTS-GO-LIVE.md`) is
written but unfired. No real $DREGG has yet been accepted for a service.

**2. It grants governance weight without staking.** A holder proves — cryptographically,
against a stake-weighted ≥2/3 Solana consensus supermajority anchored at a
governance-pinned checkpoint — that their own wallet held N units at a finalized
snapshot slot, and receives vote weight N. No lock, no transfer, no wrapped token, no
yield; custody preservation is a Lean theorem (`weight_backed_and_noncustodial`,
`metatheory/Dregg2/Bridge/ProofOfHoldings.lean`), and the weight verdict itself is
rendered by the extracted Lean core with no Rust fallback
(`dregg-governance/src/holding_weight.rs`). Snapshot semantics are deliberate: weight
is fixed per poll at a pinned slot with a consume-once nullifier per (poll, holder,
asset) — this is what defeats flash-loan weight and buy-vote-sell-revote, not a
fluidity bug. **RUNS in test** (13/13 bridge holdings polarities, 51/51 governance lib
tests, forged 1-key stake table rejected); **no live Solana feed has been ingested
yet**, so no real mainnet holding has been proven end-to-end, and holding-weighted
ballots still land in a host-side ballot box (a named residual in the code) rather than
the verified vote engine.

**3. It becomes spendable inside dregg through the vault.** To *spend* (rather than
reference) $DREGG inside dregg, you lock into the Solana vault program
(`solana-lock/`), and dregg mints mirror-$DREGG 1:1 against the observed lock —
consume-once nullifier, committed supply ledger, conservation-gated
(`turn/src/executor/bridge_ledger.rs::bridge_mint_against_lock`). This is real custody,
surrendered to a program that releases only on evidence — and the honest trust ladder
is: the production inbound slice is an M-of-N **oracle attestation** (BUILT/RUNS in
test); the **consensus-verified** inbound successor (bank-state-derived stake tables,
authorized-voter-bound tally, weak-subjectivity anchor) is built and green against
fixture clusters (`bridge/tests/solana_lock_trustless.rs`) but has never verified real
mainnet consensus; **release is oracle-custodial on every path** (there is no trustless
outbound yet). Three soundness suspects flagged 2026-07-15 (finality over-claim,
stake-set completeness, rotation signer binding) remain open — logged P1, "close
value-path holes before holding real value" (`HORIZONLOG.md`). Nothing in this leg is
deployed holding real value today.

**4. Collateral and bonds — mostly not $DREGG, and deliberately so.** The bonded
subsystems that exist are denominated in other units: relay operator bonds and slashing
run on internal computrons (`node/src/relay_dispute.rs`, RUNS in test), and the
launchpad's deployer bond example is ETH-denominated (`tools/deployer-gate/`). The
repo's own mechanism analysis argues **against** token-denominated conduct bonds: a
bond denominated in the token it polices loses value exactly when misconduct occurs, so
bonds should be quote-asset-denominated (`docs/deos/FHEGG-CODEX-ROUND4.md`). A $DREGG
bond/collateral sink via the ordinary Payable rail (bridged $DREGG is already an
ordinary asset to the service economy, `docs/guide/SERVICE-ECONOMY-SDK.md`) is
**NAMED** — a natural future sink, not built, and any design must price the
correlated-devaluation problem the codex analysis identifies.

## What deliberately does not exist

No staking yield. No burn mechanism (slash remainders are conserving transfers to a
treasury cell; supply is never destroyed by protocol action). No protocol fee capture
routed to the token — the launchpad's only fee is a 30bps pool swap fee that accrues to
the pool's own reserves, and launchpad slashes compensate holders, never the platform.
No play-to-earn: leaderboard reward is glory, not yield (locked decision,
`docs/GAME-STRATEGY.md`). Anyone reading dregg's tokenomics through the
staking/burn/P2E template will find the template empty; the design is a fixed-cap asset
whose demand comes from services, discounts, treasury-pile accumulation, and
non-custodial governance — with each leg's maturity labeled above.

## Computrons are not the token

Computrons are dregg's internal compute-metering unit — the gas, not the asset. A turn
declares a fee; the fee **is** the computron budget, and execution that would exceed it
is refused (`turn/src/executor/costs.rs`, `turn/src/executor/execute.rs`). The cost
table is explicitly a testing default, not a governed price list. Budget distribution
across execution silos is Byzantine-tolerant bounded counters (Stingray,
arXiv:2501.06531 — `coord/src/budget.rs`, RUNS). Fees are conserving moves, not burns:
50% proposer / 30% treasury / ≥20% fee-well, with unconfigured shares burned
(`turn/src/executor/mod.rs`). Computrons also denominate storage quotas, relay inbox
deposits, and operator bonds. Supply today is devnet-shaped: a rate-limited faucet
drains a pre-funded cell (`node/src/api.rs`); the Discord surface displays the unit as
"DEC", which is a display label with no code tie to the Solana token.

**There is no peg, oracle, purchase path, or exchange rate between computrons and
$DREGG anywhere in the code.** Claiming "$DREGG powers dregg compute" is unsupported at
HEAD. What exists are the docking points a purchase path would attach to: the relay
`FeePolicy.external_rate_micros` field (a per-external-asset units-per-computron rate,
designed for USDC/ETH deposit vouchers, disabled by default —
`node/src/relay_service.rs`), the Payable rail that treats any bridged asset as
spendable, and the fee-distribution engine that already routes every metered turn's
value to named cells. Because the bounded counter is generic over any fungible
resource, "computrons can be purchased in any asset at an operator- or market-set rate"
is an open **design decision**, not a kernel change — the natural verified venue for
market-set rates being DrEX ring clearing (`docs/deos/DREX-DESIGN.md`), which is
**VISION** for this purpose.

## Rules for talking about this

Present-tense claims track the maturity labels — say which. Do not use staking, burn,
or P2E vocabulary for mechanisms that do not exist. Do not cite a mint address from
memory; confirm out-of-band. The differentiating posture is that the maturity labels
are published by the project itself: lead with what runs, own every gap out loud.
