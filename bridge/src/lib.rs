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
pub mod midnight;
pub mod midnight_gateway;
pub mod midnight_inclusion;
pub mod midnight_observer;
pub mod midnight_verified;
pub mod mina;
pub mod present;
/// Mirror a Solana/pump.fun SPL token (`$DREGG`) into dregg's value layer as a
/// conserved, `Payable` asset. See `docs/deos/TOKEN-MIRROR-BRIDGE.md`.
pub mod solana_mirror;

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

/// Full-fidelity bridge-action binding: a thin re-export plus a wrapper for
/// the new sibling AIR `dregg_circuit::bridge_action_air` that pins
/// (nullifier, recipient, destination_federation, amount) at full byte/bit
/// fidelity (no 30-bit amount truncation, no Poseidon2 compression of 32-byte
/// values into a single felt). See module docs for the integration shape.
pub mod action_binding;

pub mod verifier;

#[cfg(test)]
mod tests;

// Re-export primary types for convenience.
pub use action_binding::{
    ActionBindingError, PortableActionBinding, create_action_binding, verify_action_binding,
};
pub use authorize::{AuthError, authorize_with_trace};
pub use convert::{grant_to_facts, macaroon_to_factset};
pub use delta::attenuation_to_delta;
pub use midnight_gateway::{
    AcceptedEnvelope, BridgeGateway, ClaimFraud, ClaimVerdict, GatewayError, Verdict, Watchtower,
    claim_hash,
};
pub use midnight_verified::{
    VerifiedBridgeError, VerifiedDreggToMidnight, commit_midnight_recipient,
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
    BankHashComponents, EpochStakeTable, PohError, PohSegment, ValidatorVote, VoteSetError,
    VoteTally, VoteTxWitness, account_leaf, merkle_node, tally_votes, verify_accounts_inclusion,
    verify_poh_segment, verify_supermajority, vote_message,
};
pub use solana_mirror::{
    MirrorConfig, MirrorError, MirrorMint, MirrorRedeem, MirrorState, SolanaLockAttestation,
    SolanaUnlockRequest,
};
pub use solana_trustless::{
    AccountInclusionProof, ConsensusEvidence, LockProofError, LockProofTrust, ProofMintError,
    SolanaLockProof, verify_lock_proof, verify_lock_proof_consensus,
};
pub use solana_wire::{
    AccountsInclusionProof16, IngestedVote, MERKLE_FANOUT, MerkleLevel, WireError,
    accounts_merkle_node, compute_accounts_merkle_root, decode_lock_record, encode_lock_record,
    fold_account_inclusion_16ary, ingest_vote_transaction, parse_verified_vote_tx,
    solana_account_hash, verify_account_inclusion_16ary, witness_binds,
};
pub use verifier::{DslAwareProofVerifier, StarkProofVerifier};
