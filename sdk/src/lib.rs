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

// This crate is the OFFLINE CORE of the SDK: no tokio / reqwest / dregg-wire /
// dregg-captp / dregg-federation. It builds on wasm32. The networked layer
// (CapTP capability sharing, federation registration, the hosted-mailbox crank,
// receipt event streams, the PIR discovery client, and the wire codec) lives in
// the `dregg-sdk-net` crate, which depends on this one.
pub mod beacon_cell;
pub mod cipherclerk;
// The threshold-seal organ (DKG group-key hashed-ElGamal) and the
// sealed-bid/sealed-ballot orchestration that welds it with the beacon. These
// carry the UNLINKABLE sealed-ballot governance app (`council_seal` is the
// seal; `sealed_governance` is the auction/ballot ceremony over it). Wired here
// so they ship in the built image (the `_sealed_governance_typecheck` `#[path]`
// fixture is RETIRED by this real declaration).
pub mod committed_turn;
pub mod council_seal;
pub mod device_pairing;
pub mod guardian_rotation;
pub mod sealed_governance;
// `embed` houses the no-I/O `DreggEngine` (executor + ledger + token core,
// wire-free). It is unconditional in the offline core. The networked
// `WireCodec` over it lives in `dregg-sdk-net`.
pub mod embed;
pub mod error;
pub mod explain;
pub mod factories;
pub mod flashwell;
pub mod full_turn_proof;
pub mod hatchery_mint;
pub mod identity;
pub mod job_escrow;
// TEMP-DISABLED-FOR-DEVICE-PAIRING-VERIFY: sibling draft, Cargo deps not yet wired
pub mod hints_onboarding;
pub mod mnemonic;
pub mod polis;
pub mod privacy;
#[cfg(not(target_arch = "wasm32"))]
pub mod profiles;
pub mod program;
pub mod raw;
pub mod receipt;
// ORGAN 4 — THE GATEWAY: an inbound tool-call → a cap-gated, metered, receipted
// DELEGATED turn (admitted IFF the proven `delegAdmit` policy admits it) or an
// in-band refusal. Welds the verified `Dregg2/Apps/ToolAccessDelegation.lean`
// crown to the `AgentRuntime`/`SubAgent` cap-gated executor path. Usable by ANY
// external loop (a buildr/hermes agent) via `ToolGateway::invoke`.
pub mod runtime;
pub mod tool_gateway;
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

// ORGAN 4 — THE GATEWAY surface: the delegated tool-access seam for a live
// tool-calling agent loop (the proven `delegAdmit` mandate over the cap-gated
// executor).
pub use tool_gateway::{
    CALLS_MADE_SLOT, Charge, DeliveryReceipt, GatewayRefusal, RoutedHandle, RoutedResult,
    RoutedStatus, ToolCallError, ToolGateway, ToolGrant, ToolReceipt, deleg_admit, mandate_program,
};

// Receipt-chain verification (the chain the Receipt noun links into).
pub use dregg_turn::{
    VerifyError, verify_receipt_chain, verify_receipt_chain_head, verify_receipt_extends,
};

/// The theorem-backed reason the verified executor refused a turn at admission — the legible "why"
/// of a refusal (re-exported so SDK callers can match on the structured reason, not just its
/// `Display` string). Surfaced through [`SdkError::Turn`] →
/// [`TurnError::AdmissionRefused`](dregg_turn::TurnError::AdmissionRefused).
pub use dregg_turn::AdmissionReason;

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
pub use dregg_token::{Attenuation, AuthRequest, AuthToken};

// The factory/polis plan builders (authorized by construction: they emit
// effect lists that ride `runtime.turn().effects(..)` / the execute paths).
pub use factories::{
    ADOPT_TURN_FEE, SettlementCellPlan, bridge_lock_cell, cancel_bridge, create_escrow_cell,
    create_obligation_cell, finalize_bridge, fulfill_obligation, party_field, refund_escrow,
    release_escrow, slash_obligation,
};

// The flash-well ring builder (zero-duration credit; settlement is the same
// action — enforced by the well's installed program, not by the builder).
pub use flashwell::{FlashRing, FlashWell, FlashWellPlan, FlashWellStatus, plan_flash_well};

// Mnemonic generation for identity backup.
pub use mnemonic::generate_mnemonic;

// The sealed-governance surface: the threshold council seal (`council_seal`)
// and the sealed-bid auction / unlinkable sealed-ballot ceremonies built over
// it (`sealed_governance`). An eligible voter proves eligibility via an
// anonymous nullifier (no link to the vote), seals a ballot to a council that
// no sub-quorum can peek, and the quorum tallies at close — double-votes,
// early peeks, and ballot substitutions all fail-closed.
pub use council_seal::{Council, CouncilSealError, SealedPayload};
pub use sealed_governance::{
    AuctionOutcome, Ballot, BallotOutcome, Bid, GovernanceError, Phase, PolisElection,
    SealedAuction, SealedBallot, Submission, UnlinkableSubmission, eligibility_nullifier,
    seal_ballot, seal_bid, seal_unlinkable_ballot,
};

// The no-IO embed layer for service integration. (`WireCodec` is the networked
// face; it lives in `dregg-sdk-net`.)
pub use embed::{DreggEngine, EmbedError, EngineConfig};

// Full-turn proof prove/verify entry points + witness types the node's
// proving pool names at root. The REST of the proof composition API is
// plumbing: reach it via [`full_turn_proof`]. (User code wants
// [`Receipt::proof`] / [`TurnProof`], not these.)
pub use full_turn_proof::{
    CapMembershipExpectation, CapMembershipWitness, FullTurnProof, FullTurnVerifyError,
    FullTurnWitness, NonRevocationWitness, RotationTurnWitness, TurnIdentityFelts, UmemWeldWitness,
    prove_full_turn, prove_turn_self_sovereign, prove_turn_self_sovereign_rotated,
    verify_full_turn, verify_full_turn_bound,
};

// Receipt-witness artifact codecs (app-framework re-exports these).
pub use witness_artifact::{
    WITNESSED_RECEIPT_ARTIFACT_FORMAT, decode_witnessed_receipt_artifact,
    decode_witnessed_receipt_artifact_hex, encode_witnessed_receipt_artifact,
};

// Standalone credential verification the node/teasting name at root; the
// rest lives in [`verify`].
#[cfg(any(test, feature = "dev"))]
pub use verify::verify_any_tier;
pub use verify::{verify_authorization_proof, verify_committed_threshold};

// The networked surface — CapTP capability sharing + pipelining, petname
// resolution, the hosted-mailbox crank, the silo/discharge/discovery clients,
// the receipt event streams, and the wire codec — lives in the `dregg-sdk-net`
// crate, which depends on this offline core.
