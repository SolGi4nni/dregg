// =============================================================================
// Section: Interchain settlement and proof-of-holdings
// =============================================================================

#import "../defs.typ": lean
= Interchain settlement and proof-of-holdings <sec-interchain>

dregg networks proofs, not tokens. A bridge answers "did this happen on that
chain?" by trusting a validator set; dregg answers the same question with a
proof the asking side checks itself. The exchange runs in two directions.
Inbound, dregg acts as a light client of a foreign chain: a holder proves a
balance there and receives governance weight here, and nothing moves. Outbound,
a foreign chain acts as a light client of dregg: its on-chain verifier checks a
proof of a dregg state transition and settles. The outbound direction is the
light-client theorem exercised across a chain boundary
(#lean("RecursiveAggregation.light_client_verifies_whole_history")): the
aggregate a stranger can check with one verification is the same object whether
the stranger is a phone, an auditor, or a contract on another chain. The
inbound direction is the same discipline pointed the other way --- dregg admits
a foreign fact only against a verified consensus proof, never against an
attestation it cannot check.

== Inbound: proof of holdings

A holder proves that their own token account on a foreign chain held a balance
at a finalized point, and is granted vote weight equal to the proven balance.
Custody never moves: no lock, no escrow, no wrapped token. On Solana the
production verifier (`bridge/src/solana_holdings.rs`) checks, fail-closed:
token-program ownership and mint binding of the holder's account; a stake table
*derived* from proven bank-state accounts --- stake, vote, and the stake-history
sysvar with the warmup/cooldown effective-stake curve --- admitted only against
a governance-pinned weak-subjectivity anchor, never supplied by the caller; an
authorized-voter-bound, stake-weighted $gt.eq 2/3$ Ed25519 tally; recomputation
of the bank hash; a 16-ary accounts-hash inclusion proof of the holder's
account; and a bounded-anchor proof-of-history policy. The trust model is the
standard light-client one: trustless over a pinned anchor. With no anchor
configured the path refuses; there is no fallback to a caller-supplied table.

The holder's foreign key binds to a dregg voter identity by signature, not by
transfer: strict Ed25519 over a domain-separated message for Solana wallets,
EIP-191 `personal_sign` with secp256k1 recovery for EVM addresses, and
pubkey-carrying secp256k1 with the address-hash equality as the load-bearing
check for Cosmos addresses (`dregg-governance/src/holding_weight.rs`).
Chain-shape dispatch prevents a binding from one family being replayed into
another. Double counting is closed on two axes. Each poll pins one finalized
snapshot height per chain, so moving tokens between accounts and re-proving
fails against the pin. Each (poll, chain, holder, asset) tuple is a
consume-once nullifier, so re-presenting the same holding is refused; a refusal
never consumes the nullifier, and a weight too large for the ballot domain
refuses the cast rather than saturating. The same holder on two chains is two
nullifiers, and both count --- the holdings are distinct facts.

The weight verdict itself is a Lean function. The Rust pipeline performs the
pre-checks (consensus tier, owner binding, positive amount) and then calls the
exported core #lean("ProofOfHoldings.grantWeightCore") over FFI; a missing core
is an error, never a Rust reimplementation.
#lean("ProofOfHoldings.grantWeightCore_eq_grantsWeight") proves the exported
decision realizes the specification, and
#lean("ProofOfHoldings.weight_backed_and_noncustodial") is the guarantee: a
granted weight is backed by a consensus-proven holding of at least that weight
at a finalized slot, and the grant leaves the chain state definitionally
unchanged (#lean("ProofOfHoldings.grant_preserves_custody")). The model
generalizes past Solana: the chain-agnostic statement is
#lean("ProofOfHoldingsGeneric.weight_backed_and_noncustodial_generic"), and the
weighted *decision* is fold-compatible ---
#lean("HoldingWeightedTally.decision_backed") states that a passing outcome's
cleared weight is exactly the sum of consensus-proven, non-custodial holdings,
evaluable over independently verified ballot segments. The per-chain trust
dials collapse onto one fail-closed ordinal whose verdict is likewise the
proven object (#lean("InterchainAdapterDecision.reachedConsensusCore_correct")):
the lowest, uninitialized rung refuses --- the polarity whose inversion drained
the Nomad bridge.

The verifier has an adversarial history. Its predecessor accepted a
caller-supplied stake table, which is a weight forgery: a one-key attacker
table clears its own supermajority. An audit found this in 2026-07; the entry
is now compiled only under test gates, and the production tests drive both
polarities --- a supermajority over the holder's account verifies, while a
sub-supermajority tally, a wrong mint, an unauthorized voter, a tampered
accounts hash, and an attacker-supplied one-key table are each refused
(`bridge/tests/solana_holdings.rs`).

Three residuals bound the current resolution. Every consensus fixture to date
is test-constructed from the real constructors; no live Solana feed has been
ingested, so no mainnet holding has been proven end-to-end. The weighted
ballots land in a host-side ballot box whose one-vote and quorum gates are a
hash set and a comparison; the verified vote engine has no weighted cast yet,
so what is verified is the weight verdict, not the box it lands in. And the
consensus verification is off-circuit --- re-executing-verifier grade, not
folded into an AIR --- so a succinct attestation of the holding proof is future
work, not present fact.

== Custody has three modes

The holdings path above is one of three custody modes, and the distinctions
carry the security claims. *Native dregg assets* are self-custodied and trade
freely under the kernel's conservation law. *Holdings for governance* are
proved, not locked: a read-only weight that moves nothing. *Foreign assets for
trading* are different: to make an off-chain asset spendable inside dregg, the
holder locks it into a vault and dregg mints a 1:1 mirror; exit burns the
mirror and releases the lock. The lock is what prevents a double-spend, and it
is custody --- surrendered to a program that releases only on evidence, never
to a custodian or a validator set, but custody nonetheless. The trading mode is
proof-gated custody, not non-custodial, and the governance mode is the
participation front door; the vault exists for importing spendable value and
posting bonds.

== The vault

The Solana side is a native token program (`solana-lock/`): a lock transfers
into a program-derived vault and writes a lock record whose identifier is the
record's derived address. The dregg side mints against that lock through one
committed gate, `TurnExecutor::bridge_mint_against_lock`
(`turn/src/executor/bridge_ledger.rs`): evidence that is not consensus-verified
is refused before any state changes, a domain-separated lock nullifier is
consumed against the committed nullifier set so two relayers cannot mint twice
from one lock, and the mint draws against an independently recorded escrow leg
under the invariant that live mirror supply never exceeds the currently locked
amount. Given truthful lock evidence, an unbacked mint is structurally
impossible; the two-relayer race is refused in a committed-state test
(`bridge/tests/committed_double_mint.rs`).

Inbound lock evidence arrives at one of two labeled trust levels. The
trusted-oracle level --- a threshold attestation by a configured signer set ---
is the production slice. The trustless level
(`bridge/src/solana_trustless.rs`) verifies the lock with the same
consensus-anchored machinery as the holdings path: a derived stake table, an
authorized-voter-bound tally, bank-hash recomputation, and inclusion of the
vault account, with acceptance and five refusal polarities under test
(`bridge/tests/solana_lock_trustless.rs`). That leg has verified only
fixture-built clusters; it has never verified real mainnet consensus, and the
succinct in-circuit form of the statement is named, not built. Release is
narrower than lock verification on every path: unlocking on Solana always
requires an M-of-N Ed25519 oracle attestation, so the outbound leg of the
vault is oracle-custodial even where the inbound leg is trustless.

Three soundness suspects in the trustless leg are open, flagged by an external
review on 2026-07-15 and unfixed at the time of writing. The anchored verify
proves an exact-slot supermajority --- optimistic-confirmation grade --- while
the evidence structure's documentation says "finalized"; rooted finality is not
verified. The stake-table derivation proves each supplied account's membership
in the accounts hash but not the completeness of the set, so omitting stake
accounts shrinks the denominator in later epochs. And epoch rotation tallies
with the plain supermajority check rather than the authorized-voter-bound one,
an asymmetry the code itself documents
(`bridge/src/solana_provenance.rs`). Each is plausible at the code level and
none is confirmed exploitable; together they gate the vault from holding real
value.

== Outbound: settlement

A dregg proof settles on a foreign chain when that chain's verifier checks it
natively. The settlement layer is a field-parameterized shrink
(`circuit-prove/src/dregg_outer_config.rs`, generic over the STARK
configuration): the recursion apex is re-committed with a hash native to the
target chain's field, so the target's verifier hashes cheaply. The EVM is the
BN254 instantiation: the apex passes through a gnark wrap to a Groth16 proof
that a generated Solidity verifier checks on-chain, with forgeries rejected
(`chain/gnark`, `chain/contracts/DreggSettlement.sol`). This path is deployed:
a real proof of a dregg state transition verified on Base-Sepolia and advanced
the settlement contract's proven root and height (`chain/DEPLOYMENTS.md`). The
proof was a pre-generated fixture turn, and the Groth16 setup is a single-party
development ceremony whose toxic waste is known to the operator; a production
multi-party ceremony has not been run, and no mainnet deployment exists.

The Cosmos twin verifies the *same* BN254 proof --- the same pinned statement,
the same fixture --- natively in a CosmWasm runtime: an `ark-bn254` port
reproduces the two gnark pairing checks and advances the same
proven-root/height pair (`cosmos-settlement/`). It accepts the real proof and
rejects a forged root, proof point, or commitment under `cw-multi-test`, and it
compiles to a deployable contract; it is not deployed to a live Cosmos chain,
and the fuller IBC light-client path is named, not built. The Mina analogue ---
the Pasta instantiation of the same shrink --- is scoped, not built; the
earlier Kimchi relay was removed because it never verified the proof in-circuit.

== Per-chain maturity

#figure(
  table(
    columns: (auto, 1fr, 1fr),
    align: (left, left, left),
    table.header([*chain*], [*inbound (prove holdings, then govern)*],
      [*outbound (chain verifies a dregg proof)*]),
    [Solana],
      [consensus-anchored holdings verify with a derived stake table; accept
       plus refusal polarities under test; the Lean core renders the weight
       verdict; fixture evidence only, no live feed],
      [oracle-attested lock/mint runs; consensus-anchored lock verify built
       and fixture-tested, off-circuit; succinct wrapper named, not built;
       release oracle-custodial],
    [EVM],
      [ERC-20 storage-proof holding (EIP-1186) with secp256k1 binding, joined
       into governance],
      [Groth16 verify on-chain; deployed to Base-Sepolia with a fixture proof
       on a development ceremony],
    [Cosmos],
      [bank-balance holding with secp256k1/bech32 binding],
      [CosmWasm contract verifies the same BN254 proof in test; not deployed;
       IBC client named, not built],
    [Robinhood Chain \ (EVM L2, id 46630)],
      [tokenized-stock balance through the same EIP-1186 machinery against a
       supplied L2 root: structure-only, zero governance weight; the L1
       rollup-anchor upgrade is named, not built],
      [not demonstrated],
    [Mina],
      [---],
      [scoped, not built (Pasta instantiation of the same shrink)],
  ),
  caption: [Per-chain maturity of the two directions. Present-tense claims
    track this table: an entry says what verifies, under what evidence, and
    what remains named.],
)

The Robinhood row illustrates the trust grading the whole surface uses. The
proof machinery is identical to the Ethereum lane, but an Arbitrum-Orbit L2
carries no sync committee, so a holding verified against a supplied state root
enters as structure-only and grants zero weight
(`dregg-interchain-gov/tests/robinhood_inbound.rs`); the tier that grants
weight requires deriving the root from consensus, and the Lean gate makes the
distinction a theorem rather than a convention
(#lean("ProofOfHoldings.grantWeightCore_rpc_refuses")).

Nothing on this surface custodies real value today. The lock program has no
recorded deployment and its tests sit in a workspace-excluded crate outside CI;
the trustless verifies have accepted only synthetic fixtures; release is
oracle-custodial in both trust modes; and the three vault suspects are open.
The mechanism is built and adversarially tested; deployment behind a production
ceremony and an external audit is the remaining step, and it is stated here
once.
