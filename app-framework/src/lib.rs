//! # dregg-app-framework
//!
//! Production-grade application framework for dregg apps. Extracts and unifies
//! the shared patterns that every dregg HTTP service needs:
//!
//! - **Server infrastructure** (`server`): [`AppConfig`](server::AppConfig) for
//!   env-based configuration, [`AppServer`](server::AppServer) builder with health,
//!   CORS, and admin auth pre-wired.
//! - **Admin authentication** (`auth`): [`AdminAuth`](auth::AdminAuth) extractor
//!   for bearer-token-protected admin endpoints, with constant-time comparison.
//! - **Persistence** (`persistence`): [`JsonPersistence`](persistence::JsonPersistence)
//!   for atomic write-then-rename state snapshots.
//! - **Proof verification middleware** (`middleware`): Axum extractors for verifying
//!   dregg presentation proofs from HTTP headers.
//! - **Generic content store** (`store`): Thread-safe async CRUD store keyed by
//!   32-byte identifiers.
//! - (VERB-LOCKSTEP: the escrow lifecycle helpers dissolved with the kernel
//!   escrow verbs — settlement is the factory-cell story, `dregg_sdk::factories`.)
//! - **Hex utilities** (`hex`): Encode/decode 32-byte arrays to/from hex strings.
//!
//! # Quick Start
//!
//! ```ignore
//! use dregg_app_framework::server::{AppConfig, AppServer};
//! use dregg_app_framework::auth::{AdminAuth, AdminToken, HasAdminToken};
//! use dregg_app_framework::persistence::JsonPersistence;
//!
//! #[tokio::main]
//! async fn main() {
//!     let config = AppConfig::from_env();
//!     AppServer::new(config)
//!         .service_name("my-app")
//!         .with_health()
//!         .with_cors()
//!         .routes(my_routes(state))
//!         .serve()
//!         .await
//!         .unwrap();
//! }
//! ```
//!
//! # Re-exports
//!
//! Commonly needed types from sub-crates are re-exported so apps can import from
//! a single dependency instead of reaching into `dregg-intent`, `dregg-turn`, etc.

pub mod affordance;
pub mod affordance_endpoint;
pub mod auth;
pub mod authorizer;
pub mod batch_executor;
pub mod blinded_endpoint;
pub mod captp_server;
pub mod cipherclerk;
pub mod deos_app;
pub mod discovery;
pub mod dispute;
pub mod dreggverse_map;
pub mod fee_policy;
pub mod fields;
pub mod hex;
pub mod inbox_endpoint;
pub mod invoke;
pub mod middleware;
pub mod multi_group;
pub mod optimistic_fire;
pub mod persistence;
pub mod queue_endpoint;
pub mod reactor;
pub mod rehydration;
pub mod ring_trade;
pub mod scaffold;
pub mod server;
pub mod starbridge;
pub mod stark_rehydrate;
pub mod store;
pub mod transclude_affordance;
pub mod vk;
pub mod webgen;

/// Legacy module alias — `cipherclerk` was renamed to `cipherclerk`. This
/// alias keeps `dregg_app_framework::cipherclerk::...` callers compiling
/// during the migration. New code should reach for `cipherclerk`.
#[doc(hidden)]
pub mod cclerk {
    // Legacy module: forwards to `cipherclerk` and re-exports `AppCipherclerk` so
    // pre-rename callers keep building. New code should reach for `cipherclerk`.
    pub use crate::cipherclerk::AppCipherclerk;
    pub use crate::cipherclerk::*;
}

// =============================================================================
// Re-exports: types that apps commonly need from sub-crates
// =============================================================================

/// Fill constraints for partial intent fulfillment.
pub use dregg_intent::FillConstraints;

/// Predicate types for qualification proofs.
pub use dregg_circuit::PredicateType;

/// Commit-reveal fulfillment protocol types.
pub use dregg_intent::commit_reveal_fulfillment::{
    CommitRevealFulfiller, CommitRevealFulfillmentError, FulfillmentCommitment,
    FulfillmentRegistry, FulfillmentResult, compute_commitment_hash,
};

// Re-export the SDK engine for convenience.
pub use dregg_sdk::embed::{DreggEngine, EngineConfig};

// Re-export CellId since nearly all app code uses it.
pub use dregg_types::CellId;

// Re-export server and auth types at crate root for ergonomics.
pub use auth::{AdminAuth, AdminMode, AdminToken, HasAdminToken};
pub use authorizer::{
    AuthContext, AuthError, Authorizer, BearerAuthorizer, CapabilityAuthorizer,
    RejectingAuthorizer, SignedAuthorizer,
};
pub use cipherclerk::AppCipherclerk;
pub use persistence::JsonPersistence;
pub use server::{AppConfig, AppServer, ErrorResponse, api_error};

/// Short alias for [`AppCipherclerk`].
pub use cipherclerk::AppCipherclerk as AppCClerk;

// Legacy alias for `AppCipherclerk`, preserved while downstream apps migrate to
// the new name. New code should reach for `AppCipherclerk` (or the short `AppCClerk`).
// pub use cipherclerk::AppCipherclerk as AppCipherclerk; // already re-exported above

// Re-export common action / effect types so apps build effects through
// the framework rather than reaching into `dregg_turn` directly.
pub use dregg_cell::state::FieldElement;
pub use dregg_turn::action::{Action, Authorization, DelegationMode, Effect, Event, symbol};
pub use dregg_turn::{Turn, TurnReceipt, WitnessedReceipt};

// Re-export `CapabilityRef` so apps can build the `Effect::GrantCapability` an
// admin affordance fires without adding `dregg-cell` to their own Cargo.toml.
// (`AuthRequired` is already re-exported via the `dregg_cell::{…}` block below.)
pub use dregg_cell::CapabilityRef;

// The `invoke()` front door: cells-as-service-objects method dispatch at the
// userspace layer (no `Effect::Invoke`, no cell-commitment dependency — the
// interface is resolved in userspace and resolves to existing effects).
pub use invoke::{
    InterfaceRegistry, InvokeAuthority, InvokeRefused, invoke, invoke_with_descriptor,
    resolve_against, resolve_invocation,
};

// The reactive twin of `invoke()`: a service DECLARES what cells/ops it watches
// (a `ReceiptFilter`) + how it reacts (an observed on-chain op → a reaction
// turn), and the framework wires the match → cap-gate → build → sign. The
// on-chain agent-loop made first-class. No kernel `Effect::React` — a reaction
// desugars to ordinary effects, exactly as `invoke` desugars a command.
pub use reactor::{
    ObservedReceipt, ReactRefused, ReactionPlan, Reactor, ReceiptFilter, WatchCells, WatchMethods,
    plan_reaction, react, react_build, react_to_stream,
};

// Re-export the SDK cipherclerk at the framework root so applications
// that need to *construct* one (typically in `main`) don't have to add
// `dregg-sdk` to their Cargo.toml. App code outside `main` should
// reach for [`AppCipherclerk`] (the narrow handle), not
// [`AgentCipherclerk`].
pub use dregg_sdk::AgentCipherclerk;
pub use dregg_sdk::{
    WITNESSED_RECEIPT_ARTIFACT_FORMAT, decode_witnessed_receipt_artifact,
    decode_witnessed_receipt_artifact_hex, encode_witnessed_receipt_artifact,
};

// Legacy alias for `AgentCipherclerk`, re-exported from the SDK.
// pub use dregg_sdk::AgentCipherclerk as AgentCipherclerk; // already re-exported above

// Re-export dispute framework types for apps implementing optimistic settlement.
pub use dispute::BlindedDisputable;
pub use dispute::{
    ArbiterStrategy, ComputeMetrics, DeliveryClaim, Disputable, DisputeConfig, DisputeError,
    DisputeEvidence, DisputeResolution, OptimisticSettlement, SettlementState,
};
pub use dispute::{DisputeId, SettlementId as DisputeSettlementId};

// New-world module re-exports.
pub use batch_executor::{BatchExecution, BatchExecutor, ClientTurnRequest};
pub use captp_server::CapTpServer;
// `FederationId` (the web-of-cells group identity) — re-exported so a deos app can
// construct a `CapTpServer` / set its `DeosApp` federation without adding
// `dregg-types` to its own Cargo.toml.
pub use discovery::{DiscoveryError, NameRegistration, NameserviceClient};
pub use dregg_types::FederationId;
pub use fee_policy::{AcceptedAsset, FeePolicy};
pub use multi_group::MultiGroupConfig;
pub use ring_trade::{LegId, RingTradeParticipant};

// Starbridge mounting point. The canonical surface every
// starbridge-app receives via `register(ctx)`.
pub use starbridge::{
    AffordanceRegistry, FactoryRegistry, InspectorDescriptor, InspectorRegistry,
    StarbridgeAppContext,
};

// Cell affordances — the deos interaction model (DEOS-APPS.md §"the deos app
// model"): cap-gated verified-turn templates rendered as web surfaces, fired
// through the embedded executor (the closed dispatch seam), gated by the REAL
// `dregg_cell::is_attenuation`. Apps register surfaces via
// `StarbridgeAppContext::register_affordance_surface` and serve them via the
// `AffordanceEndpoint` router; `webgen` renders the anti-drift surface descriptor.
pub use affordance::{
    AffordanceElement, AffordanceIntent, AffordanceSurface, CellAffordance, EffectSummary,
    FireError, FireExecuteError, SurfaceDescriptor,
};
// The cap∧state conjunction (the Rust twin of `Dregg2.Deos.GatedAffordance`): a gated
// affordance pairs the REAL `is_attenuation` cap-gate with a REAL `CellProgram`
// live-state gate (`CellProgram::evaluate` — the executor's own predicate). A button
// lights IFF caps AND state both pass; `GatedSurface::project_gated_for` is the
// state-aware per-viewer frustum (the htmx reactivity). The state-tooth refusal is
// `FireError::StateConditionUnmet`, in-band, before any dispatch.
pub use affordance::{GatedAffordance, GatedSurface};
pub use affordance_endpoint::{
    AffordanceEndpoint, HELD_RIGHTS_HEADER, HeaderHeldRights, HeldRightsResolver,
};

// The deos-app COMPOSITION (DEOS-APPS.md §"the deos app model") — the six layers
// (cells×affordances + the sdk surface + web-of-cells distribution + rehydration +
// the web surface) wired into ONE shape. `DeosApp::builder(...).cell(...).build()` is
// the composed `register(ctx)`; `app.register(ctx)` folds every cell's surface into
// the host context; `app.mount()` yields the whole axum surface (manifest +
// `/surface.js` web component + per-cell cap-gated fires).
pub use deos_app::{DeosApp, DeosAppBuilder, DeosCell, PersistenceSeam};

// The deos-app TRANSCLUSION AFFORDANCE (the named consumer of the transclusion
// primitive, `starbridge_web_surface::transclusion`) — a `DeosCell` declares that it
// TRANSCLUDES another cell's finalized field the way it declares any other
// affordance, and the framework renders it WITH its provenance, per-viewer through
// the REAL membrane. Built ON the REAL `TranscludedField`/`Provenance`/`Backlinks` +
// the REAL framework `CellAffordance`/`AffordanceSurface`/`DeosCell` — names them,
// reinvents none. `TranscludeAffordance::resolve` is the verified finalized read;
// `project_for` is the cap-gate ∧ membrane per-viewer projection (a quote is a READ,
// never amplified); `record_into` populates the backlinks (the witness-graph the
// other way). The transclusion primitives themselves are re-exported from
// `starbridge_web_surface::transclusion`.
pub use transclude_affordance::{
    DeosCellTranscludeExt, ProjectedTransclusion, RenderedTransclusion, TranscludeAffordance,
    TranscludeProjectError, surface_declares,
};

// The frustum-snapshot + cap-membrane (DEOS.md §"the frustum-culled snapshot") — the
// dregg-only novelty, re-expressed over the framework's OWN `is_attenuation` lattice:
// snapshot an app surface, a peer rehydrates their attenuated, liveness-typed,
// per-viewer view.
pub use rehydration::{
    Interaction, InteractionLog, Membrane, RehydrateError, RehydratedSurface, Rehydration,
    Sturdyref, meet_authority,
};

// TIER B (DEOS-APPS.md §"the two tiers"): the SAME frustum-snapshot, but re-expansion is
// gated by a REAL STARK proof (the rotated `Ir2BatchProof` / the `WholeChainProof` ROOT)
// instead of a witness-replay over the receipt chain — opening the image VERIFIES the
// STARK (light-client style), so a tampered surface state / forged proof / wrong-root
// proof is rejected at rehydration, with NO receipt-chain walk.
pub use stark_rehydrate::{
    RotatedParticipantLeg, StarkRehydrateError, StarkSnapshot, TransferTurn, mint_stark_snapshot,
    mint_transfer_leg, verify_stark_leg, witness_replay_is_genuine,
};

// The interactive-tempo bridge (DEOS-APPS.md §"the interactive/real-time tempo gap";
// the #169 optimistic-local + verified-at-boundary dial) for affordance fires:
// predict locally NOW, settle the verified turn at the trust boundary, reconcile.
pub use optimistic_fire::{OptimisticFire, Settlement};

// The `dregg new deos-app` SCAFFOLD (DEOS-APPS.md §7) — a spec the builder writes
// (cells + affordances + rights + effects), turned into a live `DeosApp`
// (`AppSpec::into_app`) OR a full buildable crate + web surface (`Scaffold::render` /
// `write_to`) — the "useful deos app in an afternoon" one-command path.
pub use scaffold::{
    AffordanceEffect, AffordanceSpec, AppSpec, CellSpec, Scaffold, ScaffoldError, ScaffoldFiles,
};

// The web-component surface generator (DEOS.md §"htmx on crack") — render a DeosApp's
// `<dregg-affordance-surface>` custom element (the per-viewer, cap-gated affordance
// DOM the embedded servo web-surface mounts).
pub use webgen::render_surface_component;

// Re-export the embedded executor at the framework root for the
// common pattern: build a cipherclerk, build an executor, hand them
// to a StarbridgeAppContext.
pub use cipherclerk::{EmbeddedExecutor, ExecutorSubmitError};

// Anti-drift JS-constants generation: render an app's slot layout +
// event-topic vocabulary to a canonical `constants.generated.js` the web
// pages import, so the JS surface cannot drift from the Rust source of truth.
pub use webgen::{ConstantsModule, Slot};

// Re-export FactoryDescriptor from dregg-cell at the framework root
// so starbridge-apps only need dregg-app-framework in their Cargo.toml
// to construct factory descriptors.
pub use dregg_cell::{
    AuthRequired, CapGrant, CapTarget, CapTemplate, CellMode, CellProgram, ChildVkStrategy,
    FactoryDescriptor, FieldConstraint, ProvingSystemId, StateConstraint, VerifierFingerprint,
    VkComponents, canonical_vk_v2,
};
// Re-export the types needed to build non-trivial CellProgram::Cases — previously
// every app had to add dregg-cell to its own Cargo.toml just to get these.
pub use dregg_cell::predicate::{InputRef, WitnessedPredicate, WitnessedPredicateKind};
pub use dregg_cell::program::{AuthorizedSet, TransitionCase, TransitionGuard};
// The canonical clearance-graph commitment — the value a clearance-mandate cell
// pins in its `clearance_graph_root` slot so the executor's
// `StateConstraint::ClearanceDominates` (which recomputes it from the carried
// edges) binds the stored root. Re-exported so an app can compute the root it
// seeds without reaching into `dregg-cell` directly.
pub use dregg_cell::program::clearance_graph_root;

// Re-export the canonical field-element encoding helpers so apps can use them
// without duplicating these in every crate.
pub use fields::{field_from_bytes, field_from_u64, hex_encode_32};

// VK v2: re-export the layered VK encoders from `vk` module at the
// framework root. These *shadow* the cell crate's v1 `canonical_program_vk`
// / `canonical_predicate_vk` re-exports — apps that import from
// `dregg_app_framework` automatically pick up the v2 layered hashes,
// closing the "same spec, different AIR" gap that v1 left open.
// (`VK-AS-RE-EXECUTION-RECIPE.md` §v2.)
pub use vk::{
    DEFAULT_PROVING_SYSTEM, PLONKY3_PINNED_REV, canonical_predicate_vk,
    canonical_program_bytes_hash, canonical_program_vk, effect_vm_air_fingerprint,
    effect_vm_verifier_fingerprint, validate_child_vk_canonical,
};
