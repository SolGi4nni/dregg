// =============================================================================
// Section 7: Economic Model
// =============================================================================

= Economic Model

== Fee Model

=== Two-Phase Execution (Mina-Style)

Fees are processed in two phases: (1) the agent's balance is decremented by `turn.fee` and nonce incremented---this is never rolled back; (2) the call forest executes, with effects rolling back on failure but the fee retained. This ensures the federation is compensated for processing regardless of execution outcome.

=== Fee Distribution

Fees are split into three destinations on every committed turn:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, center, left),
    table.header([*Destination*], [*Share*], [*Rationale*]),
    [Block proposer], [50%], [Direct incentive to process turns],
    [Federation treasury], [30%], [Governance-directed spending],
    [Burned], [20%], [Mild deflation, aligns holder interests],
  ),
  caption: [Fee distribution split. Parameters are governance-adjustable via `FeePolicy` attested at epoch boundaries.],
)

The treasury is a distinguished cell whose spending requires a governance vote (quorum of current committee). This provides sustainable funding for development and operations without external revenue dependencies.

=== Fee Market (EIP-1559 Adaptation)

A base fee adjusts per-block to target 50% utilization:

$ "base_fee"_(n+1) = "base_fee"_n dot (1 + ("actual" - "target") / "target" dot 0.125) $

With parameters: target 1M computrons/block, max 2M, minimum base fee 1, maximum 1000. Users specify `max_fee` and `priority_fee`. They pay $min("max_fee", "base_fee" + "priority_fee")$. The base fee portion follows the standard split; the priority fee goes entirely to the block proposer.

== Validator Staking

=== Deposit-Based Committee Membership

Federation committees are small (3--20 nodes). Rather than heavy proof-of-stake machinery, Pyana uses deposit-based membership:

- Joining requires locking a deposit note with value $>=$ `MINIMUM_VALIDATOR_STAKE` (initially 100,000 computrons)
- The deposit is proven via a STARK range proof (value hidden, threshold satisfaction proven)
- Deposit is locked for the epoch duration + unbonding period (2 epochs)

=== Slash Conditions

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, center, left),
    table.header([*Condition*], [*Slash Amount*], [*Rationale*]),
    [Equivocation (double-vote)], [100%], [Always intentional],
    [Inactivity (>50% missed)], [5% per epoch], [Graceful for maintenance],
    [Invalid attestation], [50%], [Fraud proof required],
  ),
  caption: [Slash conditions. Slashed funds go to the federation treasury (not reporter) to prevent slash-for-profit griefing.],
)

=== Privacy-Compatible Staking

Note values are private (Poseidon2 commitments). Staking uses range proofs: "prove my stake >= X" without revealing the exact value. The `RangeProofAir` decomposes $"value" - "threshold"$ into BabyBear-width bit limbs, proving all are 0/1.

For slashing with private stakes: at deposit time, the validator provides a _slash commitment_ $= "Poseidon2"("note_commitment", "slash", "randomness")$. On slash, the protocol publishes this commitment to a "slashed set." The validator's note is encumbered---spending requires proving non-membership in the slashed set. Slashing is enforced at spend-time (like a lien), not at slash-time.

== Anti-Griefing

=== Conditional Turn Deposits

Conditional turns occupy space in the pending pool until timeout. A reservation deposit makes griefing expensive:

$ "deposit" = "base_deposit" + "per_block_rate" times ("timeout" - "submitted_at") $

With `base_deposit = 500` and `per_block_rate = 10`: a 1000-block conditional costs 10,500 computrons if it times out. On successful execution, the deposit is fully refunded. On timeout, 20% is burned and 80% goes to treasury.

=== Sybil Resistance

Each note commitment can be used as a stake proof $K$ times per epoch (governance parameter, initially $K = 5$). Epoch-scoped stake nullifiers prevent unlimited reuse:

$ "stake_nullifier" = "Poseidon2"("note_commitment", "epoch", "usage_counter") $

The federation maintains an append-only stake nullifier set per epoch. An entity with $N$ notes gets $N times K$ identities per epoch. Privacy is preserved: nullifiers do not reveal which note, and cross-epoch usage is unlinkable.

== Intent Marketplace Economics

=== Fulfiller Fees

When a fulfillment is accepted, the requester pays the fulfiller a `fulfillment_fee` negotiated off-protocol. This is a direct transfer between cells---not mediated by the federation.

=== Priority Tips

Intents can include a `priority_tip` (additional computrons locked with the intent). Higher-tip intents are propagated more eagerly by gossip relays. On fulfillment, the tip goes to the fulfiller. On expiry, the tip is returned minus a `gossip_rent` proportional to time-in-pool.

=== Proof Generation Costs

Proof generation is local (not metered by the network). The cost is borne by the prover in CPU time. Fulfillers factor this into their fulfillment fee. No on-chain "gas for proofs"---the market prices it.

== Incentive Analysis

=== Nash Equilibrium for Validators

With the proposed parameters, honest validation is the dominant strategy whenever annual fee income exceeds server cost plus opportunity cost of stake. Deviation strategies are strictly dominated:

- *Censor turns*: reduces fee income, risks inactivity slash
- *Include invalid turns*: other validators reject the block
- *Equivocate*: 100% stake slash---strictly dominated for any positive stake
- *Go offline*: 5% slash per epoch, lost income

=== Minimum Viable Economics

Federations are small and purpose-built. A 5-node federation serving a specific application domain (agent marketplace, credential issuance) is viable with modest throughput if operators have aligned interests (they are also users). No inflation needed---validators earn directly from fee distribution.

== Comparison

#figure(
  table(
    columns: (auto, auto, auto, auto),
    align: (left, left, left, left),
    table.header([*Property*], [*Pyana*], [*Cosmos*], [*Mina*]),
    [Committee size], [3--20], [100--175], [$tilde$1000],
    [Fee destination], [50/30/20 split], [Proposer+stakers], [Burned],
    [Staking model], [Deposit + range proof], [Delegated PoS], [Delegated PoS],
    [Privacy of stake], [ZK range proof], [Transparent], [Transparent],
    [Fee market], [EIP-1559 adapted], [First-price auction], [Fixed fees],
    [Inflation], [None], [Yes (5--20%)], [Yes],
    [Treasury], [30% of fees], [Community pool (2%)], [None],
  ),
  caption: [Economic model comparison. Pyana is non-inflationary; validators earn from fees.],
)

The key difference from Cosmos: Pyana does not need inflation because federations are small and operators have aligned interests. Cosmos needs inflation because validator sets are large and operators are pure infrastructure providers.
