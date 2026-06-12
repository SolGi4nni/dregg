//! # dregg-sdk
//!
//! # Which semantics does a deployed SDK run?
//!
//! The SDK builds and signs turns; the **federation node executes them**. Today
//! that execution runs on the LEGACY dregg1 Rust executor (`dregg-turn`), with
//! the VERIFIED Lean executor (`metatheory/Dregg2/`, via `dregg-lean-ffi`)
//! running as a SHADOW that compares its commit decision against the Rust path
//! (gated on `DREGG_LEAN_SHADOW=1`). The source of truth for the semantics is
//! the Lean — the Rust executor is the subject-under-test pending THE SWAP
//! (cutover to `dregg_exec_full_forest_auth` as the authoritative executor).
//!
//! Concretely, when you deploy this SDK today: turn-building, key management,
//! attenuation and proof generation are SDK-local Rust; the on-chain *effect
//! semantics* applied to those turns are the legacy Rust executor's, validated
//! turn-by-turn against the verified Lean (for every effect the shadow projector
//! covers — see `turn/src/lean_shadow.rs` and
//! `metatheory/docs/rebuild/_DREGG1-DREGG2-UNIFICATION-LEDGER.md`). After the
//! swap, the verified Lean semantics ARE what runs. Track the cutover in
//! `metatheory/docs/rebuild/SUCCESSOR-ROADMAP.md`.
//!
//! # Trust Model
//!
//! This crate operates at the **CLIENT-LOCAL** trust level.
//!
//! - **Soundness**: The SDK runs entirely on the user's device. It manages private keys,
//!   token chains, and proof generation locally. The user trusts their own device and
//!   the SDK's correct implementation. No other party can observe or interfere with
//!   SDK operations (assuming a secure device).
//! - **Assumptions**: The user's device is not compromised. Private keys remain in local
//!   memory/storage. The SDK correctly implements proof generation, token attenuation,
//!   and turn signing. Network interactions are authenticated (TLS to silos).
//! - **Verifiable by**: Only the user. The SDK's outputs (signed turns, proofs,
//!   presentations) are verified by the federation, but the SDK's internal state
//!   (held tokens, cipherclerk contents) is private to the user.
//!
//! ## Security Properties
//! - Key material never leaves the device (unless explicitly exported)
//! - Proof generation is local (witness data stays on-device)
//! - Token attenuation preserves the narrowing invariant (cannot escalate)
//! - Selective disclosure reveals only chosen facts
//!
//! ## What the SDK Does NOT Trust
//! - Remote silos (verified via TLS + receipt chains)
//! - Federation state (verified via attested roots + STARK proofs)
//! - Other agents (interactions mediated by capabilities)
//!
//! The unified agent SDK for the dregg federation protocol.
//!
//! This crate provides a single ergonomic entry point for agents that need to:
//! - Hold and manage authorization tokens (macaroon-backed)
//! - Attenuate and delegate tokens to sub-agents
//! - Sign and submit execution turns
//! - Generate zero-knowledge presentation proofs
//! - Interact with remote silos over the wire protocol
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────────┐
//! │                          AgentRuntime                                    │
//! │  ┌────────────────────┐  ┌──────────────┐  ┌──────────────────────┐    │
//! │  │ AgentCipherclerk   │  │   Ledger     │  │    SiloClient        │    │
//! │  │ (identity +        │  │   (local     │  │    (remote silo      │    │
//! │  │  tokens + keys)    │  │    state)    │  │     interaction)     │    │
//! │  └────────────────────┘  └──────────────┘  └──────────────────────┘    │
//! └─────────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! # The cipherclerk
//!
//! `AgentCipherclerk` (alias `AgentCClerk`, legacy alias `AgentCipherclerk`) is the
//! agent-side *cryptographic clerk*: it holds signing keys, authorization
//! tokens, the receipt chain, and presents credentials/proofs on behalf of a
//! Principal. The name borrows from Greg Egan's *Polis* (and its descendants),
//! where a citizen's "cipherclerk" is the autonomous component that manages
//! their cryptographic identity and capability handles. "Cipherclerk" was a poor
//! fit — cipherclerks connote value storage, but a dregg cipherclerk's authority
//! is mostly *capabilities*, not balances.
//!
//! # Quick Start
//!
//! ```no_run
//! use dregg_sdk::{AgentCipherclerk, AgentRuntime};
//! use dregg_token::Attenuation;
//!
//! // Create a cipherclerk with a fresh identity
//! let mut cclerk = AgentCipherclerk::new();
//!
//! // Mint a root token for our service
//! let root_token = cclerk.mint_token(b"my-secret-root-key-32-bytes!!!!!", "my-service");
//!
//! // Attenuate it for a specific task
//! let restricted = cclerk.attenuate(&root_token, &Attenuation {
//!     services: vec![("dns".into(), "r".into())],
//!     ..Default::default()
//! }).unwrap();
//! ```

// Modules that pull tokio / dregg-wire / dregg-captp are gated so the crate
// stays buildable on wasm32 (set `default-features = false`). Anything in
// the always-on group below is wasm-friendly.
#[cfg(feature = "captp")]
pub mod captp_client;
pub mod cipherclerk;
#[cfg(feature = "network")]
pub mod client;
pub mod committed_turn;
#[cfg(feature = "network")]
pub mod discharge;
#[cfg(feature = "network")]
pub mod discovery;
#[cfg(feature = "network")]
pub mod embed;
pub mod error;
#[cfg(all(feature = "federation-client", feature = "network"))]
pub mod events;
pub mod explain;
pub mod factories;
pub mod full_turn_proof;
pub mod identity;
#[cfg(feature = "captp")]
pub mod mailbox;
pub mod mnemonic;
#[cfg(feature = "captp")]
pub mod names;
pub mod polis;
pub mod privacy;
#[cfg(not(target_arch = "wasm32"))]
pub mod profiles;
pub mod program;
pub mod raw;
pub mod receipt;
pub mod runtime;
pub mod trustline;
pub mod turns;
pub mod verify;
pub mod witness_artifact;
pub mod wordlist;

/// Legacy module name for the cipherclerk surface.
///
/// During the rename window this re-exports `cipherclerk` plus an
/// `AgentCipherclerk` alias so downstream `use dregg_sdk::cipherclerk::...`
/// paths keep compiling. New code should reach for
/// `dregg_sdk::cipherclerk`.
#[doc(hidden)]
pub mod cclerk {
    pub use crate::cipherclerk::AgentCipherclerk;
    pub use crate::cipherclerk::*;
}

// ============================================================================
// THE PUBLIC SURFACE — two nouns, one authorized turn shape.
//
//   Identity (AgentCipherclerk / a named profile) → AgentRuntime::turn()
//     → typed verbs (.transfer/.write/.grant/…) → .sign() → .submit()
//     → Receipt
//
// and, for trusting a whole history at once, AttestedHistory (the
// light-client artifact). Everything below the "plumbing" line is the
// machinery these are made of — public modules, but not the headline.
// ============================================================================

/// **Noun 1**: proof-of-execution for one committed turn, with the composed
/// STARK lazily attached. See [`receipt`].
pub use receipt::{Receipt, TurnProof};

/// The receipt nervous system: subscribe to a node's committed receipts as
/// a `Stream` of [`Receipt`]. See [`events`].
#[cfg(all(feature = "federation-client", feature = "network"))]
pub use events::{NodeEvents, ReceiptFilter, ReceiptStream};

/// **Noun 2**: the light-client artifact — the verdict from verifying ONE
/// succinct whole-history aggregate (re-witnessing nothing), plus its
/// verifier entry points and trust-anchor type.
pub use dregg_lightclient::{
    AttestedHistory, FinalityCert, FinalizedAttestation, verify_finalized_history, verify_history,
};

/// The authorized turn flow: `runtime.turn()` opens a [`turns::TurnBuilder`];
/// `.sign()` yields a [`turns::AuthorizedTurn`]; `.submit()` a [`Receipt`].
pub use turns::{AuthorizedTurn, TurnBuilder};

// The identity, its runtime, and the effect vocabulary the verbs speak.
pub use cipherclerk::{AgentCipherclerk, SignedTurn};
pub use dregg_cell::{CellId, Ledger};
pub use dregg_turn::Effect;
pub use dregg_types::{PublicKey, Signature};
pub use error::SdkError;
pub use runtime::{AgentRuntime, SubAgent};

// Receipt-chain verification (the chain the Receipt noun links into).
pub use dregg_turn::{
    VerifyError, verify_receipt_chain, verify_receipt_chain_head, verify_receipt_extends,
};

/// Short alias for [`AgentCipherclerk`] — the "capability clerk" handle.
///
/// Use in tight scopes where the full name would dominate signatures.
pub use cipherclerk::AgentCipherclerk as AgentCClerk;

// ============================================================================
// PLUMBING RE-EXPORTS (compatibility surface).
//
// Kept at root because deployed consumers (node, wasm, app-framework,
// teasting, discord-bot) name them here. New code should prefer the module
// paths (`cipherclerk::`, `full_turn_proof::`, `verify::`, …). Raw
// `Action`/`Turn` construction — including the genesis-only
// `Authorization::Unchecked` — lives ONLY behind the sealed [`raw`] module.
// ============================================================================

pub use cipherclerk::{
    AuthorizationPresentation, ChainAppendError, DelegatedToken, DelegationAuthority,
    DisclosureSpec, FactDisclosure, FactIndex, HeldToken, LocalDelegation, OwnedStealthNote,
    VerificationMode,
};
#[cfg(feature = "network")]
pub use client::{PresentationResult, RevocationStatus, SiloClient};
pub use dregg_token::{Attenuation, AuthRequest, AuthToken};

// The factory/polis plan builders (authorized by construction: they emit
// effect lists that ride `runtime.turn().effects(..)` / the execute paths).
pub use factories::{
    ADOPT_TURN_FEE, SettlementCellPlan, bridge_lock_cell, cancel_bridge, create_escrow_cell,
    create_obligation_cell, finalize_bridge, fulfill_obligation, party_field, refund_escrow,
    release_escrow, slash_obligation,
};

// Mnemonic generation for identity backup.
pub use mnemonic::generate_mnemonic;

// The no-IO embed layer for service integration.
#[cfg(feature = "network")]
pub use embed::{DreggEngine, EmbedError, EngineConfig, WireCodec};

// Full-turn proof prove/verify entry points + witness types the node's
// proving pool names at root. The REST of the proof composition API is
// plumbing: reach it via [`full_turn_proof`]. (User code wants
// [`Receipt::proof`] / [`TurnProof`], not these.)
pub use full_turn_proof::{
    CapMembershipExpectation, CapMembershipWitness, FullTurnProof, FullTurnVerifyError,
    FullTurnWitness, NonRevocationWitness, prove_full_turn, prove_turn_self_sovereign,
    verify_full_turn, verify_full_turn_bound,
};

// Receipt-witness artifact codecs (app-framework re-exports these).
pub use witness_artifact::{
    WITNESSED_RECEIPT_ARTIFACT_FORMAT, decode_witnessed_receipt_artifact,
    decode_witnessed_receipt_artifact_hex, encode_witnessed_receipt_artifact,
};

// Discharge gateway client functions.
#[cfg(feature = "network")]
pub use discharge::{authorize_with_discharges, extract_third_party_tickets, obtain_discharge};

// Standalone credential verification the node/teasting name at root; the
// rest lives in [`verify`].
#[cfg(any(test, feature = "dev"))]
pub use verify::verify_any_tier;
pub use verify::{verify_authorization_proof, verify_committed_threshold};

// Name resolution types for the petname system.
#[cfg(feature = "captp")]
pub use names::{
    CipherclerkNames, EdgeNameEntry, NameError, NameProvenance, NameResolver, PetnameDb,
    PetnameEntry, ProposedNameEntry, ResolvedName, WhoisResult,
};

// CapTP client types for capability sharing and pipelining.
#[cfg(feature = "captp")]
pub use captp_client::{CapTpClient, CapTpConfig, EventualRef, LiveRef};

// The mailbox crank (ORGANS §2): drain a hosted inbox, execute sealed
// turn-intents through the owner's `.turn()` path, custody-receipted by the
// relay's existing dequeue proofs.
#[cfg(feature = "captp")]
pub use mailbox::{
    CrankDisposition, CrankOutcome, CrankReport, CustodyReceipt, DeliveredMessage, MailboxCrank,
    MailboxTransport, MailboxTurnIntent, RefusalReason, seal_intent,
};
#[cfg(all(feature = "captp", feature = "federation-client", feature = "network"))]
pub use mailbox::RelayHttpTransport;
#[cfg(feature = "captp")]
pub use dregg_captp::handoff::HandoffCertificate;
#[cfg(feature = "captp")]
pub use dregg_captp::pipeline::PipelinedAction;
#[cfg(feature = "captp")]
pub use dregg_captp::uri::DreggUri;
#[cfg(feature = "captp")]
pub use dregg_captp::{FederationId, GroupId};
