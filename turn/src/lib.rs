//! `dregg-turn`: Call-forest transaction model for atomic agent execution turns.
//!
//! # ⚠️ LEGACY dregg1 — pending the verified-Lean SWAP
//!
//! **This crate is the LEGACY dregg1 Rust executor. It is NOT the source of
//! truth for dregg's semantics.** The verified semantics live in Lean under
//! `metatheory/Dregg2/` (the `CellProgram`, `Authorization`, `Caveat`,
//! `Predicate`, effect-executor and circuit-descriptor definitions). This
//! Rust code is hand-written, UNVERIFIED, and is the thing dregg2 *replaces*.
//!
//! It remains here because the running devnet node (`dregg-node` →
//! `dregg-turn`) currently EXECUTES on this Rust executor. It is load-bearing
//! UNTIL THE SWAP (cutover to the verified Lean executor via the
//! `dregg-lean-ffi` bridge / `dregg_exec_full_forest_auth`), tracked in
//! `metatheory/docs/rebuild/SUCCESSOR-ROADMAP.md` and
//! `metatheory/Dregg2/Exec/FullForestAuth.lean`.
//!
//! While the swap is in flight, the `dregg-exec-lean` crate runs the verified
//! Lean executor as a *shadow* (gated on `DREGG_LEAN_SHADOW=1`) and compares its
//! commit decision against this Rust path — that comparison is the differential
//! harness validating the eventual cutover. This crate is FFI-free: it reaches
//! the shadow only through the [`shadow::ShadowObserver`] seam (a native node
//! injects `dregg_exec_lean::LeanShadowObserver`). The Lean side is the oracle;
//! this Rust side is the subject under test, never the reverse.
//!
//! Do NOT read this crate as "the dregg semantics". Read `metatheory/Dregg2/`.
//! See `metatheory/docs/rebuild/DREGG1-TO-DREGG2.md`.
//!
//! # Trust Model
//!
//! This crate spans TWO trust levels with a clear boundary:
//!
//! ## Executor-Trusted (classical path)
//! - Modules: [`executor`], [`forest`], [`action`], [`journal`]
//! - The executor walks the call forest, checks authorization, and applies effects.
//! - Soundness depends on honest federation execution (BFT replication).
//! - External parties trust the federation's attested state root.
//!
//! ## Trustless (proof-carrying path)
//! - Modules: [`verify`], sovereign cell proof verification in [`executor::verify_and_commit_proof`]
//! - Proof-carrying sovereign turns (Phase 3) are independently verifiable via STARK.
//! - The executor only checks the proof and updates a commitment -- no state interpretation.
//!
//! ## Trust Boundary
//! The boundary lives inside `executor.rs` at the `execution_proof` branch:
//! - If `turn.execution_proof` is `Some`: **TRUSTLESS** path (verify proof, update commitment)
//! - If `turn.execution_proof` is `None`: **EXECUTOR-TRUSTED** path (classical execution)
//!
//! A Turn is an atomic unit of agent execution, modeled after Mina's zkApp command structure.
//! It contains a *call forest* — a tree of actions that either all commit or all rollback.
//!
//! # Architecture
//!
//! ```text
//! ┌──────────────────────────────────────────────────────────────┐
//! │  Turn (atomic transaction)                                    │
//! │  ┌────────────────────────────────────────────────────────┐  │
//! │  │  CallForest                                             │  │
//! │  │  ┌──────────┐  ┌──────────┐  ┌──────────┐             │  │
//! │  │  │ CallTree │  │ CallTree │  │ CallTree │  ...         │  │
//! │  │  │ (root 1) │  │ (root 2) │  │ (root 3) │             │  │
//! │  │  │   │      │  │   │      │  │          │             │  │
//! │  │  │   ├─child│  │   └─child│  │          │             │  │
//! │  │  │   └─child│  │          │  │          │             │  │
//! │  │  │     └─gc │  │          │  │          │             │  │
//! │  │  └──────────┘  └──────────┘  └──────────┘             │  │
//! │  └────────────────────────────────────────────────────────┘  │
//! └──────────────────────────────────────────────────────────────┘
//! ```
//!
//! The key insight from Mina: the call forest IS the transaction. You don't prove
//! individual operations — you prove the entire tree. Authorization flows from
//! parent to child via capability delegation.
//!
//! # Modules
//!
//! - [`action`]: Action, Authorization, DelegationMode, Effect, Event
//! - [`forest`]: CallTree, CallForest
//! - [`turn`]: Turn, TurnReceipt, TurnResult
//! - [`executor`]: TurnExecutor, ComputronCosts, execution logic
//! - [`error`]: TurnError
//! - [`builder`]: TurnBuilder, ActionBuilder

pub mod action;
pub mod admission_reason;
pub mod bilateral_schedule;
pub mod binding_proof;
pub mod budget_gate;
pub mod builder;
pub mod collapse;
pub mod composer;
pub mod conditional;
pub mod conflict;
pub mod continuation;
pub mod continuation_resume;
pub mod cross_fed_cite;
pub mod dsl;
pub mod economics;
pub mod encrypted;
pub mod error;
pub mod eventual;
pub mod exact_fnsp_v4_consensus_envelope;
pub mod execution_path;
pub mod executor;
pub mod faithful_note_spend;
pub mod faithful_note_spend_exact_v3;
pub mod faithful_note_spend_exact_v3_acceptance;
pub mod faithful_note_spend_exact_v3_anchor;
pub mod faithful_note_spend_exact_v3_receipt_epoch;
pub mod fast_path;
pub mod finalized_receipt_core_v1;
pub mod forest;
pub(crate) mod journal;
pub mod pending;
pub mod pq;
pub mod presence_discharge;
pub mod reactive;
pub mod recursive_witness_producer;
pub mod reversible;
pub mod rotation_witness;
pub mod routing;
pub mod script;
pub mod shadow;
pub mod shielded_verifier;
pub mod state_commit;
pub mod turn;
pub mod umem;
pub mod verify;
pub mod witnessed_receipt;

#[cfg(test)]
mod tests;

// Re-export primary types at crate root.
pub use action::{
    Action, Authorization, BearerCapProof, CommitmentMode, DelegationMode, DelegationProofData,
    Effect, Event, TokenKeyRef, derive_cell_macaroon_secret,
};
pub use admission_reason::AdmissionReason;
pub use budget_gate::{BudgetGate, BudgetSlice};
pub use builder::{
    ActionBuilder, Authorized, Bearer, Breadstuff, NeedsAuth, Proved, Signed, TurnBuilder,
    UncheckedOptIn,
};
pub use collapse::{
    CollapseResult, DEFERRED_STATE_HASH, WitnessMode, collapse, collapse_with, is_deferred,
};
pub use composer::{ComposeError, ComposedTurn, SignedFragment, TurnComposer};
pub use conditional::{
    BASE_CONDITIONAL_DEPOSIT, ConditionProof, ConditionalResult, ConditionalTurn,
    DEFAULT_MAX_ROOT_AGE, MAX_CONDITIONAL_DEADLINE, PER_BLOCK_DEPOSIT, ProofCondition,
    ProvenReceipt, TrustedRoot, burn_conditional_deposit, compute_conditional_deposit,
    compute_proof_hash, refund_conditional_deposit, resolve_condition,
    validate_conditional_submission,
};
pub use conflict::{ConflictSet, build_conflict_set, extract_access_sets};
pub use economics::{EpochMinter, MintResult, MintingPolicy};
pub use encrypted::{
    ConflictBucket, EncryptedTurn, EncryptedTurnError, SubmitterAuth, TurnOrdering,
    TurnValidityProof, TurnValidityPublicInputs, order_encrypted_turns,
};
pub use error::{CustomBindingLeg, RefusalClass, TurnError};
pub use eventual::{
    CycleError, EventualRef, OutputRef, Pipeline, PipelineBuilder, PipelineError, PipelineResult,
    Target, TurnBatch, TurnOutput,
};
pub use exact_fnsp_v4_consensus_envelope::{
    EXACT_FNSP_V4_ACTIVATION_CORE_LEN, EXACT_FNSP_V4_FRAME_CORE_LEN, EXACT_RECEIPT_CORE_V4_LEN,
    ExactFnspV4ActivationCore, ExactFnspV4ActivationId, ExactFnspV4ConsensusError,
    ExactFnspV4FrameCore, ExactFnspV4FrameCoreFields, ExactFnspV4FrameId,
    ExactFnspV4FramePredecessor, ExactFnspV4ReceiptPredecessor, ExactReceiptCoreV4,
    ExactReceiptIdV4, HYBRID_LOCAL_EXACT_FNSP_V4_ENVELOPE_LEN, HybridExactFnspV4ValidatorIdentity,
    HybridExactFnspV4ValidatorSigner, HybridLocalExactFnspV4Envelope,
};
pub use execution_path::{ExecutionPath, compute_execution_path};
pub use executor::{
    AtomicProofEntry, AtomicSovereignTurn, AtomicTurnError, BridgeEscrowReceipt,
    BridgeEscrowRecord, BridgeMintError, BridgeMintReceipt, BridgeMintRequest,
    CellMigrationManager, ComputronCosts, MigrationCancelReason, MigrationError, MigrationState,
    MixedAtomicResult, MixedAtomicTurn, ProofVerifier, ResolutionTable, TurnExecutor,
    escrow_nullifier_for, execute_pipeline, execute_pipeline_result, new_mirror_ledger_cell,
    read_supply, resolve_eventual_ref,
};
pub use faithful_note_spend_exact_v3_acceptance::{
    AcceptedFaithfulNoteSpendExactV3, ExactFnspV3ProofAuthorityAlreadyInstalled,
    FaithfulNoteSpendExactV3AcceptanceBinding, FaithfulNoteSpendExactV3AcceptanceError,
    exact_fnsp_v3_proof_authority_installed, install_exact_fnsp_v3_proof_authority,
    verify_faithful_note_spend_exact_v3_acceptance,
};
pub use faithful_note_spend_exact_v3_anchor::{
    ExactFnspV3AnchorSide, ExactFnspV3DurableAnchor, ExactFnspV3DurableAnchorError,
    derive_exact_fnsp_v3_durable_anchor, derive_exact_fnsp_v3_durable_anchor_chain,
};
pub use faithful_note_spend_exact_v3_receipt_epoch::{
    ExactFnspV3OuterCommit, ExactFnspV3ReceiptEpoch, ExactFnspV3ReceiptEpochError,
    ExactFnspV3ReceiptEpochV1, ExactFnspV3ReceiptLinkV1, ExactFnspV3StatePoint,
    FullTurnReceiptStateCommit8, PreparedExactFnspV3ReceiptFrameV1,
    UntrustedExactFnspV3CommittedFrameHeadBindingV1, UntrustedExactFnspV3ReceiptFrameJoinV1,
};
pub use fast_path::{
    CellLockEntry, CellLockTable, FastPathConfig, FastPathError, TurnCertificate, TurnSign,
    assemble_certificate, clear_all_locks, execute_certified_turn, expire_stale_locks,
    is_fast_path_eligible, process_fast_path_lock, verify_turn_sign,
};
pub use finalized_receipt_core_v1::{
    FINALIZED_EXECUTION_CONTEXT_V1_LEN, FINALIZED_RECEIPT_CORE_V1_LEN, FinalizedExecutionContextV1,
    FinalizedReceiptCoreV1, FinalizedReceiptCoreV1Error, FinalizedReceiptIdV1,
    FinalizedReceiptPredecessorV1, HYBRID_LOCAL_FINALIZED_RECEIPT_ENVELOPE_V1_LEN,
    HybridFinalizedReceiptValidatorIdentityV1, HybridFinalizedReceiptValidatorSignerV1,
    HybridLocalFinalizedReceiptEnvelopeV1,
};
pub use forest::{CallForest, CallTree};
pub use pending::{
    BrokenReason, PendingEntry, PendingHandle, PendingReactError, PendingRegistryCodecError,
    PendingStatus, PendingSubmitError, PendingTurnRegistry, REACTIVE_NULLIFIER_DOMAIN_V1,
    ReactiveNullifierError, ReactiveNullifierSet, ResolutionCondition, ResolutionEvent,
    ResolutionOutcome,
};
pub use shielded_verifier::{ShieldedTransferVerifier, VerifiedShieldedTransfer};
// `Precondition` and friends collapsed into `dregg_cell::preconditions`
// per PREDICATE-INVENTORY §4.3 case 1. Re-export from cell for any
// callers that still reach for them through the turn crate root.
pub use dregg_cell::{Precondition, Preconditions, PreconditionsBuilder};
pub use presence_discharge::{
    PresenceCaveat as PresenceCapCaveat, PresenceClaimRequirement, PresenceDischarge,
    PresenceDischargeError, verify_presence_discharge,
};
pub use recursive_witness_producer::{
    RecursiveWitnessProducer, RecursiveWitnessProducerAlreadyInstalled,
    install_recursive_witness_producer, recursive_witness_producer,
    recursive_witness_producer_installed,
};
pub use reversible::{
    CommittedReason, Inversion, InvertError, ReversibleError, ReversibleHistory, ReversibleStep,
    changed_cells, ledgers_agree_modulo_nonce,
};
pub use routing::{IntroductionExport, RoutingDirective};
pub use shadow::{NoOpShadowObserver, ShadowHostCtx, ShadowObserver};
pub use turn::{
    ConsumedCapAuthPath, ConsumedCapWitness, CustomProgramProof, EmittedEvent, Finality,
    SovereignCellWitness, Turn, TurnReceipt, TurnResult, absorb_emitted_event,
};
pub use verify::{
    VerifyError, sign_receipt, verify_receipt_chain, verify_receipt_chain_head,
    verify_receipt_chain_strict, verify_receipt_chain_with_optional_keys, verify_receipt_extends,
    verify_receipt_signature_with_keys,
};
pub use witnessed_receipt::{
    AggregateMembership, RecursiveProofVariant, WitnessAvailability, WitnessBundle,
    WitnessedReceipt,
};
