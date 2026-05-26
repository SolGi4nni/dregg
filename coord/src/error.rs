//! Error types for the coordination layer.
//!
//! CoordError covers failures in both causal chaining (Layer 1)
//! and atomic multi-party turns (Layer 2).

use dregg_cell::{CellId, LedgerError};
use dregg_turn::TurnError;

/// All possible failure modes in the coordination layer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoordError {
    // ── Layer 1: Causal Chaining Errors ──────────────────────────────────
    /// A causal dependency is missing from the local DAG.
    MissingDependency {
        /// The turn that has a missing dep.
        turn_hash: [u8; 32],
        /// The missing dependency hash.
        dep_hash: [u8; 32],
    },

    /// A causal turn references a dependency cycle (should never happen with hashes).
    CausalCycle { turn_hash: [u8; 32] },

    /// Duplicate turn: a turn with this hash already exists in the DAG.
    DuplicateTurn { hash: [u8; 32] },

    /// The per-node sequence number is not monotonically increasing.
    SequenceGap {
        node_id: [u8; 32],
        expected: u64,
        got: u64,
    },

    /// Hash verification failed: recomputed hash does not match the claimed hash.
    HashMismatch {
        claimed: [u8; 32],
        computed: [u8; 32],
    },

    // ── Layer 2: Atomic Multi-Party Errors ───────────────────────────────
    /// The coordinator is not in the correct state for the requested operation.
    InvalidCoordinatorState {
        expected: &'static str,
        actual: &'static str,
    },

    /// A participant voted No, aborting the atomic turn.
    ParticipantRejected {
        participant: [u8; 32],
        reason: String,
    },

    /// Not enough participants voted Yes to reach the threshold.
    ThresholdNotMet { required: usize, received: usize },

    /// A participant is not listed in the atomic forest.
    UnknownParticipant { id: [u8; 32] },

    /// A participant voted more than once.
    DuplicateVote { participant: [u8; 32] },

    /// Precondition evaluation failed for a participant.
    PreconditionFailed {
        cell_id: CellId,
        description: String,
    },

    /// The atomic forest is empty (no actions).
    EmptyForest,

    /// The participant list is empty.
    NoParticipants,

    /// Threshold is invalid (zero or greater than participant count).
    InvalidThreshold {
        threshold: usize,
        participants: usize,
    },

    /// A vote's Ed25519 signature failed verification.
    InvalidVoteSignature { participant: [u8; 32] },

    /// The proposed forest's estimated cost exceeds the coordinator's max budget.
    BudgetExceeded { estimated: u64, max_budget: u64 },

    // ── Underlying errors ────────────────────────────────────────────────
    /// A turn execution error from the turn executor.
    TurnExecution(TurnError),

    /// A ledger error from applying a delta.
    Ledger(LedgerError),
}

impl core::fmt::Display for CoordError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            CoordError::MissingDependency {
                turn_hash,
                dep_hash,
            } => {
                write!(
                    f,
                    "missing causal dependency: turn {} needs dep {}",
                    hex4(turn_hash),
                    hex4(dep_hash)
                )
            }
            CoordError::CausalCycle { turn_hash } => {
                write!(f, "causal cycle detected at turn {}", hex4(turn_hash))
            }
            CoordError::DuplicateTurn { hash } => {
                write!(f, "duplicate turn: {}", hex4(hash))
            }
            CoordError::SequenceGap {
                node_id,
                expected,
                got,
            } => {
                write!(
                    f,
                    "sequence gap for node {}: expected {expected}, got {got}",
                    hex4(node_id)
                )
            }
            CoordError::HashMismatch { claimed, computed } => {
                write!(
                    f,
                    "hash mismatch: claimed {}, computed {}",
                    hex4(claimed),
                    hex4(computed)
                )
            }
            CoordError::InvalidCoordinatorState { expected, actual } => {
                write!(
                    f,
                    "invalid coordinator state: expected {expected}, in {actual}"
                )
            }
            CoordError::ParticipantRejected {
                participant,
                reason,
            } => {
                write!(f, "participant {} rejected: {reason}", hex4(participant))
            }
            CoordError::ThresholdNotMet { required, received } => {
                write!(f, "threshold not met: need {required}, got {received}")
            }
            CoordError::UnknownParticipant { id } => {
                write!(f, "unknown participant: {}", hex4(id))
            }
            CoordError::DuplicateVote { participant } => {
                write!(f, "duplicate vote from participant: {}", hex4(participant))
            }
            CoordError::PreconditionFailed {
                cell_id,
                description,
            } => {
                write!(f, "precondition failed for cell {cell_id}: {description}")
            }
            CoordError::EmptyForest => write!(f, "atomic forest is empty"),
            CoordError::NoParticipants => write!(f, "no participants in atomic turn"),
            CoordError::InvalidThreshold {
                threshold,
                participants,
            } => {
                write!(
                    f,
                    "invalid threshold: {threshold} with {participants} participants"
                )
            }
            CoordError::InvalidVoteSignature { participant } => {
                write!(
                    f,
                    "invalid vote signature from participant: {}",
                    hex4(participant)
                )
            }
            CoordError::BudgetExceeded {
                estimated,
                max_budget,
            } => {
                write!(
                    f,
                    "estimated cost {estimated} exceeds max budget {max_budget}"
                )
            }
            CoordError::TurnExecution(e) => write!(f, "turn execution error: {e}"),
            CoordError::Ledger(e) => write!(f, "ledger error: {e}"),
        }
    }
}

impl std::error::Error for CoordError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            CoordError::TurnExecution(e) => Some(e),
            CoordError::Ledger(e) => Some(e),
            _ => None,
        }
    }
}

impl From<TurnError> for CoordError {
    fn from(e: TurnError) -> Self {
        CoordError::TurnExecution(e)
    }
}

impl From<LedgerError> for CoordError {
    fn from(e: LedgerError) -> Self {
        CoordError::Ledger(e)
    }
}

/// Format the first 4 bytes of a hash as hex for display.
fn hex4(bytes: &[u8; 32]) -> String {
    format!(
        "{:02x}{:02x}{:02x}{:02x}...",
        bytes[0], bytes[1], bytes[2], bytes[3]
    )
}
