//! `dregg-bridge`: Connects plaintext token crates to the ZK proof system.
//!
//! This crate bridges two worlds:
//! - **Plaintext tokens** (`token`, `macaroon`): MacaroonToken/BiscuitToken with HMAC
//!   verification, caveat-based authorization, and attenuation.
//! - **ZK proof system** (`dregg-commit`, `dregg-trace`, `dregg-circuit`): Merkle-committed
//!   fact sets, Datalog derivation traces, and STARK-based presentation proofs.
//!
//! The bridge performs four key transformations:
//! 1. **Token to FactSet**: Converts macaroon caveats into committed facts.
//! 2. **Attenuation to FoldDelta**: Maps plaintext attenuation steps to ZK fold deltas.
//! 3. **Request to AuthorizationTrace**: Evaluates authorization against committed state.
//! 4. **Full Presentation**: Assembles a ZK-ready proof from a token chain.
//!
//! # Architecture
//!
//! ```text
//! MacaroonToken                          PresentationProof
//!    │                                         ▲
//!    │ convert                                  │ prove
//!    ▼                                         │
//! FactSet + SymbolTable ──────────────────► PresentationBuilder
//!    │                                         ▲
//!    │ attenuate                                │ add_step
//!    ▼                                         │
//! FoldDelta ─────────────────────────────────┘
//!    │
//!    │ authorize
//!    ▼
//! AuthorizationTrace
//! ```

pub mod authorize;
pub mod convert;
pub mod delta;
pub mod ethereum;
/// The **live off-chain inbound relayer** for the EVM bridge: a real Ethereum
/// JSON-RPC client (`eth_getBlockByNumber("finalized")` / `eth_getLogs` /
/// `eth_getTransactionReceipt` / `eth_getProof`) that watches the bridge contract
/// for finalized `Deposit` logs, runs the off-chain verify (finality + the BR-2-B
/// escrow-to-contract binding + receipt inclusion), and produces the committed-mint
/// input. The Ethereum-direction twin of [`solana_relayer`]; the in-circuit witness
/// of EVM finality is the circuit swarm's VK-epoch (`dregg_circuit::bridge_action_air`).
pub mod ethereum_relayer;
pub mod midnight;
pub mod midnight_gateway;
pub mod midnight_inclusion;
pub mod midnight_observer;
pub mod midnight_verified;
pub mod mina;
/// The **live off-chain Mina observer** for the settlement loop: a real Mina
/// GraphQL client (`bestChain` for the finality depth + `account(publicKey)` for
/// the zkApp's settled `provenRoot`) that confirms an outbound dregg→Mina
/// settlement landed on a depth-finalized canonical block (and matches the settled
/// dregg root) instead of trusting a relayer ack. The Mina-direction twin of
/// [`midnight_observer`]; finalized-only, the verify, the injected transport.
pub mod mina_observer;
pub mod present;
/// Mirror a Solana/pump.fun SPL token (`$DREGG`) into dregg's value layer as a
/// conserved, `Payable` asset. See `docs/deos/TOKEN-MIRROR-BRIDGE.md`.
pub mod solana_holdings;
pub mod solana_mirror;

/// Mirror a verified **Stripe payment** (a signed `payment_intent.succeeded` /
/// `charge.succeeded` webhook) into dregg's value layer as a conserved, `Payable`
/// USD-credit asset — the `solana_mirror` pattern with Stripe as the trusted
/// payment oracle. An agent's Stripe payment funds its DreggNet execution-lease.
pub mod stripe_mirror;

/// The **PROVEN, DECO/zkTLS-verified** Stripe money-in — the trustless upgrade
/// from [`stripe_mirror`]'s trusted-HMAC-webhook oracle: mint only against a DECO
/// attestation (a zkTLS proof that a live Stripe TLS session disclosed a settled
/// payment), verified against the felt-commitment binding the deployed DECO leaf
/// (`circuit-prove::deco_leaf_adapter`) enforces in-AIR and `Deco.lean` proves. The
/// HMAC path stays as the explicitly-labeled fallback until the zkTLS PROVER lands.
pub mod stripe_deco;

/// The TRUSTLESS inbound proof-of-lock for the Solana mirror — the honest
/// upgrade from the trusted-oracle attestation: verify a `SolanaLockProof`
/// (consensus evidence + account inclusion) instead of trusting a signature.
/// See `docs/deos/TRUSTLESS-SOLANA-BRIDGE.md`.
pub mod solana_trustless;

/// The real Solana Tower-BFT consensus primitives the trustless bridge verifies:
/// the per-epoch stake table, real Ed25519 stake-weighted vote aggregation, the
/// bank-hash binding, the accounts-hash inclusion, and the PoH tick-chain check.
pub mod solana_consensus;

/// The mainnet **wire-format adapter** (pass 2): real Solana vote-transaction
/// ingestion (bincode `Transaction` + `VoteInstruction` → a signature-verified
/// [`solana_consensus::ValidatorVote`]) and the real 16-ary fan-out accounts-hash
/// Merkle over blake3 per-account hashes. See `docs/deos/TRUSTLESS-SOLANA-BRIDGE.md`.
pub mod solana_wire;

/// **Bank-state provenance** (pass 3): source the per-epoch stake table + the
/// authorized-voter binding from Solana's own bank state (verified against the
/// voted accounts hash), rotated across epochs from an irreducible
/// weak-subjectivity anchor. Replaces the trusted `EpochStakeTable` input with a
/// proven-from-the-bank-hash derivation. See `docs/deos/TRUSTLESS-SOLANA-BRIDGE.md`.
pub mod solana_provenance;

/// The **live off-chain relayer** (the watching service): a real Solana JSON-RPC
/// client that watches the bridge vault for finalized locks, runs the off-chain
/// verify (finality + the BR-2-B escrow-to-vault binding + structure/binding),
/// and produces the committed-mint input. Replaces the in-memory feed stand-in.
/// The in-circuit witness of the consensus path is the circuit swarm's G1
/// VK-epoch (`dregg_circuit::bridge_action_air`). See `solana_relayer` docs and
/// `docs/deos/TRUSTLESS-SOLANA-BRIDGE.md`.
pub mod solana_relayer;

/// Full-fidelity bridge-action binding: a thin re-export plus a wrapper for
/// the new sibling AIR `dregg_circuit::bridge_action_air` that pins
/// (nullifier, recipient, destination_federation, amount) at full byte/bit
/// fidelity (no 30-bit amount truncation, no Poseidon2 compression of 32-byte
/// values into a single felt). See module docs for the integration shape.
pub mod action_binding;

pub mod verifier;

/// ONE `InterchainAdapter` trait unifying the four per-chain trust dials
/// (`LockProofTrust` / `SnarkSystem` / `Verdict` / `FinalizedAttestation`) behind
/// a single fail-closed `TrustRung` that feeds the committed
/// `TurnExecutor::bridge_mint_against_lock` gate.
pub mod interchain_adapter;

#[cfg(test)]
mod tests;

// Re-export primary types for convenience.
pub use action_binding::{
    ActionBindingError, PortableActionBinding, create_action_binding, verify_action_binding,
};
pub use authorize::{AuthError, authorize_with_trace};
pub use convert::{grant_to_facts, macaroon_to_factset};
pub use delta::attenuation_to_delta;
pub use ethereum_relayer::{
    BlockTag, DEPOSIT_EVENT_SIGNATURE, ETH_DEPOSIT_NULLIFIER_DOMAIN, EthBridgeConfig, EthJsonRpc,
    EthLog, EthProof, EthReceipt, EthRelayer, EthRelayerError, EthRpc, EthStorageSlot,
    ObservedDeposit, deposit_event_topic0, encode_amount_word, eth_deposit_nullifier,
};
pub use interchain_adapter::{
    AdapterError, ChainAttestation, DialAdapter, InterchainAdapter, TrustDial, TrustRung,
};
pub use midnight_gateway::{
    AcceptedEnvelope, BridgeGateway, ClaimFraud, ClaimVerdict, GatewayError, Verdict, Watchtower,
    claim_hash,
};
pub use midnight_verified::{
    VerifiedBridgeError, VerifiedDreggToMidnight, commit_midnight_recipient,
};
pub use mina_observer::{
    MinaBlock, MinaGraphQlRpc, MinaObserver, MinaObserverConfig, MinaRpc, MinaZkappAccount,
    ObserveError, ObservedMinaSettlement, decode_root_from_fields, encode_root_to_fields,
};
pub use present::{
    BridgeCommittedThresholdProof, BridgePredicateProof, BridgePredicateProofInner,
    BridgePresentationBuilder, BridgePresentationProof, DEFAULT_MAX_PROOF_AGE_SECS,
    FederationRegistry, Predicate, ProgramProveError, UnsafeLocalOnlyMarker, VerifiedPresentation,
    VerifierConfig, VerifyError, WirePresentationProof, bb_from_bytes, bb_to_bytes,
    compute_revealed_facts_commitment, prove_committed_threshold, prove_predicate_for_fact,
    prove_predicate_program, prove_predicate_program_full, verify_committed_threshold_proof,
    verify_fold_chain, verify_predicate_program, verify_predicate_proof,
    verify_presentation_complete, verify_presentation_full, verify_proof_complete,
    verify_revealed_facts_commitment, verify_wire_fold_chain,
};
pub use solana_consensus::{
    BankHashComponents, EpochStakeTable, PohAnchorPolicy, PohError, PohSegment, ValidatorVote,
    VoteSetError, VoteTally, VoteTxWitness, account_leaf, merkle_node, tally_votes,
    verify_accounts_inclusion, verify_poh_anchored, verify_poh_segment, verify_supermajority,
    vote_message,
};
pub use solana_mirror::{
    MirrorConfig, MirrorError, MirrorMint, MirrorRedeem, MirrorState, SOLANA_LOCK_NULLIFIER_DOMAIN,
    SolanaLockAttestation, SolanaUnlockRequest, VerifiedLock, lock_nullifier,
};
pub use solana_provenance::{
    Delegation, DerivedStakeTable, ProvenAccount, ProvenanceError, RotationStep,
    STAKE_HISTORY_SYSVAR_ID, STAKE_PROGRAM_ID, SYSVAR_OWNER_ID, VerifiedStakeTable,
    WeakSubjectivityAnchor, active_stake, decode_authorized_voter, decode_stake_delegation,
    decode_stake_history, derive_stake_table, effective_stake, rotate, vote_program_id,
};
pub use solana_relayer::{
    AccountResponse, Commitment, JsonRpcTransport, ObservedLock, RelayerError, RpcAccount,
    RpcError, SolanaJsonRpc, SolanaRelayer, SolanaRpc, StdHttpTransport,
};
/// The LEGACY supplied-table consensus verify — TEST/INTERNAL ONLY (see its doc:
/// a caller-supplied stake table is forgeable; production uses
/// [`verify_lock_proof_consensus_anchored`]).
#[cfg(any(test, feature = "test-utils"))]
pub use solana_trustless::verify_lock_proof_consensus;
pub use solana_trustless::{
    AccountInclusionProof, ConsensusEvidence, LockProofError, LockProofTrust, ProofMintError,
    SolanaConsensusStatement, SolanaLockProof, StakeProvenance, verify_lock_proof,
    verify_lock_proof_consensus_anchored,
};
pub use solana_wire::{
    AccountsInclusionProof16, IngestedVote, MERKLE_FANOUT, MerkleLevel, WireError,
    accounts_merkle_node, compute_accounts_merkle_root, decode_lock_record, encode_lock_record,
    fold_account_inclusion_16ary, ingest_vote_transaction, parse_verified_vote_tx,
    solana_account_hash, verify_account_inclusion_16ary, witness_binds,
};
pub use stripe_deco::{DecoPaymentAttestation, MoneyIn};
pub use stripe_mirror::{
    DEFAULT_TOLERANCE_SECS, RECIPIENT_METADATA_KEY, STRIPE_PAYMENT_NULLIFIER_DOMAIN, StripeMint,
    StripeMirrorConfig, StripeMirrorError, StripeMirrorState, StripePaymentAttestation,
    StripeWebhookEvent, VerifiedPayment, payment_nullifier,
};
pub use verifier::{DslAwareProofVerifier, StarkProofVerifier};
