// =============================================================================
// Section 19: The units of the economy
// =============================================================================

#import "../defs.typ": lean
= The units of the economy <sec-economics>

The system has two economic units, and they are different objects. The
*computron* is the internal metering unit: it prices execution, storage, and
message delivery, and it is not a market asset. The *native token*, \$DREGG,
is an ordinary asset under the issuer discipline of the model --- the worked
instance of an asset whose issuer sits at the system's boundary. Neither unit
adds a kernel mechanism. Every flow described below is a conserving move under
the same value law that governs any other asset, and each role is stated with
its maturity: _runs_ (exercised green by a test or demo), _built_ (real code,
not exercised end-to-end live), _named_ (a stated design without code). The
canonical statement of record is `docs/TOKENOMICS.md`.

== Computrons

A turn declares a fee, and the fee is the computron budget. The executor
meters each action, effect, transfer, cell creation, proof verification,
signature verification, and byte processed against a cost table, and it
refuses a turn whose metered cost exceeds the declared fee
(`turn/src/executor/execute.rs`). Fee coverage is checked against the agent's
balance before execution begins. The cost table is a stated testing default,
not a governed price list (`turn/src/executor/costs.rs`).

Fees are moves, not burns. A committed fee splits into conserving credits:
half to the block proposer, three tenths to a federation treasury, and the
remainder --- at least one fifth, plus rounding dust and any share whose
recipient is unconfigured --- to a fee-well cell
(`turn/src/executor/mod.rs`). The books therefore close. On the Lean
executor, with mint and burn reshaped to issuer-moves, every state reachable
from a value-empty genesis has per-asset total exactly zero: the issuer wells
carry negative supply, and $Sigma delta = 0$ holds not merely per turn but
identically along the whole reachable trajectory
(#lean("ReachableConservation.reachable_total_zero")). A configuration
without a fee well burns the undelivered remainder; the deployed genesis
configures the well.

Budgets distribute across execution silos without per-operation consensus.
The mechanism is a Byzantine-tolerant bounded counter after Stingray
@stingray: an agent's balance splits into per-silo slices with ceiling
$b (f+1) \/ (2f+1)$ for balance $b$ and tolerated Byzantine silos $f$, silos
debit locally against their slice, and rebalancing requires Ed25519-signed
spending certificates with anti-replay debit digests, failing closed on a
missing or invalid signature (`coord/src/budget.rs`). The counter is generic
over any fungible resource; the computron carries no monetary semantics of
its own. The same unit denominates storage quotas, relay inbox deposits, and
relay-operator bonds. Supply today is devnet-shaped: a rate-limited faucet
drains a pre-funded cell --- a transfer, not a mint (`node/src/api.rs`).

== The native token

\$DREGG is a fixed-supply SPL token native to Solana, approximately $10^9$
units, with no emission schedule, no inflation, and no protocol mint. The
interchain posture reinforces the fixed supply rather than hedging it: dregg
networks proofs, not tokens --- other chains verify proofs _about_ dregg
state, and the token is never minted on another chain
(`docs/deos/INTERCHAIN-MODEL.md`). Inside dregg the token appears only as a
1:1 mirror against units locked in a Solana vault. The bridge mint consumes a
per-lock nullifier against the same committed nullifier set that note spends
ride, so racing relayers cannot double-mint against one lock, and the
executor refuses any mint that would take live mirror supply above the
committed locked amount (`turn/src/executor/bridge_ledger.rs`). Redemption
burns the mirror before release. The repository pins no mainnet mint address
in code; the binding is an operator environment decision.

== Four roles

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*role*], [*mechanism*], [*maturity*]),
    [services rail], [metered service runs paid in stablecoin or token,
      dual-asset treasury], [runs against mock chains; mainnet flip unfired],
    [governance weight], [non-custodial proof of holdings at a pinned slot],
      [runs in test; no live feed ingested],
    [vault mirror], [lock #sym.arrow mirror #sym.arrow burn #sym.arrow
      release], [built; release oracle-custodial on every path],
    [bond sink], [none], [deliberately absent],
  ),
  caption: [The token's four roles, at current maturity.],
)

*The services rail.* The payment backend sells metered service runs --- AI
narration on the deployed game surface --- for either a stablecoin or the
token: per-user derived deposit addresses, an idempotent per-payment credit
ledger, and a dual-asset treasury in which the stablecoin funds real
inference and fails closed when empty, while paid tokens accumulate in an
illiquid operator treasury rather than being market-sold (`dregg-pay/`).
Paying in the token earns a discount, set in basis points against an external
price oracle. The rail is exercised end-to-end against mock chains; the
mainnet go-live sequence is a written, unfired runbook
(`docs/ops/PAYMENTS-GO-LIVE.md`), and no real token has yet been accepted for
a service.

*Governance weight.* A holder proves that their own wallet held $N$ units at
a finalized snapshot slot, against a stake-weighted supermajority of Solana
consensus anchored at a governance-pinned checkpoint, and receives vote
weight $N$ --- no lock, no transfer, no wrapped token. A granted weight is
backed by a consensus-proven holding at a finalized slot, and the grant
leaves the on-chain state unchanged for every prior state
(#lean("ProofOfHoldings.weight_backed_and_noncustodial")); the weight verdict
is rendered by the extracted Lean core with no Rust fallback
(`dregg-governance/src/holding_weight.rs`). Weight is fixed per poll at the
pinned slot, with a consume-once nullifier per (poll, holder, asset); the
snapshot semantics are what defeat borrowed-balance weight and
vote-sell-revote. The path runs in test, including rejection of a forged
one-key stake table; no live Solana feed has been ingested, so no real
mainnet holding has been proven end to end, and holding-weighted ballots land
in a host-side ballot box rather than the verified vote engine.

*The vault mirror.* Spending the token inside dregg requires locking it into
the Solana vault program (`solana-lock/`) and minting mirror units 1:1
against the observed lock, under the conservation gate above. The trust
ladder is explicit. The production inbound slice is an M-of-N oracle
attestation. A consensus-verified inbound successor --- bank-state-derived
stake tables, an authorized-voter-bound tally, a weak-subjectivity anchor ---
is built and green against fixture clusters
(`bridge/tests/solana_lock_trustless.rs`) and has not verified real mainnet
consensus. Release is oracle-custodial on every path; there is no trustless
outbound. Three open soundness questions on the consensus-verified slice
(finality strength, stake-set completeness, rotation signer binding) are
logged in the horizon record, and the leg holds no real value today.

*The absent bond sink.* The bonded subsystems that exist are denominated in
other units: relay-operator bonds and slashing run on computrons
(`node/src/relay_dispute.rs`), and the launchpad's deployer-bond example is
ETH-denominated (`tools/deployer-gate/`). The absence is an argued position
rather than an omission: a conduct bond denominated in the token it polices
loses value exactly when misconduct occurs, so bonds should be denominated in
the quote asset (`docs/deos/FHEGG-CODEX-ROUND4.md`). A token-denominated
collateral sink through the ordinary payment rail is named and unbuilt; any
such design must price that correlated devaluation.

== What does not exist

There is no staking yield. There is no burn mechanism: a slash seizure splits
into a bounded restitution to the wronged party and a remainder moved to a
configured treasury cell, both conserving transfers out of the bonded cell.
No protocol fee routes to the token: the launchpad's only fee is a
30-basis-point pool swap fee that accrues to the pool's own reserves, and
launchpad slashes compensate holders, never the platform. There is no
play-to-earn; the deployed games' leaderboard reward carries no token
(`docs/GAME-STRATEGY.md`). A reader applying the staking / burn /
play-to-earn template will find each slot empty. The design is a fixed-supply
asset whose demand is services, discounts, treasury accumulation, and
governance weight, each at the maturity stated above.

== The open decision: purchasing computrons

No peg, oracle, purchase path, or exchange rate between computrons and the
token exists anywhere in the code; the token does not meter computation
today. What exists are the docking points a purchase path would attach to.
The relay fee policy carries a per-external-asset units-per-computron rate,
designed for stablecoin deposit vouchers and disabled by default
(`node/src/relay_service.rs`). The payment rail treats any bridged asset as
spendable. The fee-distribution engine already routes every metered turn's
value to named cells. Because the bounded counter is generic over any
fungible resource, letting computrons be purchased in any asset at an
operator- or market-set rate is a design decision above the kernel, not a
kernel change --- and it is deliberately open: the choice of which assets
buy computation, and at what rate, is the one economic question the units
leave unanswered. Until it is decided, the two units stay distinct: the
computron meters, the token pays for services, and any flow ever built
between them will be one more conserving move under the same value law.
