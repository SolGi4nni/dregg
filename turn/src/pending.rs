//! PendingTurnRegistry: async resolution, cross-federation EventualRefs, and
//! broken-promise propagation for distributed promise semantics.
//!
//! # Overview
//!
//! The pipeline system (eventual.rs) provides synchronous batched execution with
//! output forwarding. This module extends it with REAL distributed coordination:
//!
//! 1. A turn can be Pending (awaiting external resolution)
//! 2. EventualRefs can reference turns on OTHER federations
//! 3. When a promise breaks (turn rejected, timeout, federation offline),
//!    all dependents are notified via broken-promise propagation
//!
//! # Design
//!
//! ```text
//! ┌───────────────────────────────────────────────────────────────────┐
//! │ PendingTurnRegistry                                               │
//! │                                                                   │
//! │  pending: HashMap<[u8;32], PendingEntry>                         │
//! │     │                                                             │
//! │     ├─ turn_hash_A → PendingEntry { condition, dependents: [C] } │
//! │     ├─ turn_hash_B → PendingEntry { condition, dependents: [C] } │
//! │     └─ turn_hash_C → PendingEntry { condition: AwaitReceipt(A) } │
//! │                                                                   │
//! │  resolve(A, Resolved(receipt)) → cascading resolution of C       │
//! │  resolve(B, Broken(Timeout))   → cascading broken propagation    │
//! └───────────────────────────────────────────────────────────────────┘
//! ```

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use serde::{Deserialize, Serialize};

use crate::conditional::ProofCondition;
use crate::error::TurnError;
use crate::turn::{Turn, TurnReceipt};
use dregg_cell::Nullifier;

/// Wire prefix for one canonically encoded pending-turn registry snapshot.
///
/// The registry is durable consensus-side state.  Keeping an explicit prefix
/// outside postcard means a future schema change cannot be mistaken for this
/// version merely because its first fields happen to decode.
const PENDING_REGISTRY_MAGIC_V1: &[u8; 5] = b"DPRG1";

/// Version 2 adds an explicit durable release phase to every entry.  Postcard
/// encodes structs positionally, so this must be a real wire-version bump:
/// serde's skipped/default trailing-field pattern is not backwards-compatible
/// for a non-self-describing sequence format.
const PENDING_REGISTRY_MAGIC_V2: &[u8; 5] = b"DPRG2";

/// Hard admission ceiling for unresolved promises.
///
/// Without a bound, valid signed Promise turns can grow the durable registry
/// without limit.  The ceiling is deliberately generous for devnet while still
/// making the memory/disk obligation explicit and deterministic on every node.
pub const MAX_PENDING_TURNS: usize = 65_536;

/// Maximum canonical snapshot size accepted from durable storage.
pub const MAX_PENDING_REGISTRY_BYTES: usize = 64 * 1024 * 1024;

/// A pending entry could not be admitted without changing existing authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PendingSubmitError {
    /// The wake-turn hash already names a live promise.  Existing conditions,
    /// deadlines, and dependency edges are immutable until resolution.
    AlreadyPending { turn_hash: [u8; 32] },
    /// The durable registry reached its protocol capacity.
    RegistryFull { max: usize },
}

impl fmt::Display for PendingSubmitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AlreadyPending { turn_hash } => write!(
                f,
                "pending turn {} is already registered",
                hex::encode(turn_hash)
            ),
            Self::RegistryFull { max } => {
                write!(f, "pending-turn registry is full (maximum {max})")
            }
        }
    }
}

impl std::error::Error for PendingSubmitError {}

/// A durable pending-registry snapshot failed canonical validation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PendingRegistryCodecError {
    TooLarge {
        size: usize,
        max: usize,
    },
    InvalidMagic,
    Decode(String),
    NonCanonical,
    TooManyEntries {
        count: usize,
        max: usize,
    },
    TurnHashMismatch {
        stored: [u8; 32],
        canonical: [u8; 32],
    },
}

impl fmt::Display for PendingRegistryCodecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooLarge { size, max } => {
                write!(
                    f,
                    "pending registry snapshot is {size} bytes (maximum {max})"
                )
            }
            Self::InvalidMagic => {
                f.write_str("pending registry snapshot has invalid magic/version")
            }
            Self::Decode(error) => write!(f, "pending registry snapshot decode failed: {error}"),
            Self::NonCanonical => f.write_str("pending registry snapshot is not canonical"),
            Self::TooManyEntries { count, max } => {
                write!(f, "pending registry has {count} entries (maximum {max})")
            }
            Self::TurnHashMismatch { stored, canonical } => write!(
                f,
                "pending registry key {} does not match canonical wake hash {}",
                hex::encode(stored),
                hex::encode(canonical)
            ),
        }
    }
}

impl std::error::Error for PendingRegistryCodecError {}

/// A React effect did not match the live promise it attempted to discharge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PendingReactError {
    WakeHashMismatch,
    NotRegistered,
    ReactorMismatch {
        expected: dregg_cell::CellId,
        actual: dregg_cell::CellId,
    },
    ConditionIsNotProofDriven,
    ConditionMismatch,
    /// The proof condition was already discharged.  The exact wake remains in
    /// the registry until its real finalized receipt arrives, but it cannot be
    /// released or enqueued a second time.
    AlreadyReleased,
    Expired {
        timeout_height: u64,
        current_height: u64,
    },
}

impl fmt::Display for PendingReactError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WakeHashMismatch => f.write_str("React wake turn hash does not equal pending_id"),
            Self::NotRegistered => f.write_str("React pending_id is not registered"),
            Self::ReactorMismatch { expected, actual } => write!(
                f,
                "React actor {actual:?} does not own pending wake agent {expected:?}"
            ),
            Self::ConditionIsNotProofDriven => {
                f.write_str("React can discharge only a registered AwaitCondition promise")
            }
            Self::ConditionMismatch => {
                f.write_str("React proof condition differs from the registered promise condition")
            }
            Self::AlreadyReleased => {
                f.write_str("React pending wake was already released for execution")
            }
            Self::Expired {
                timeout_height,
                current_height,
            } => write!(
                f,
                "React promise expired at height {timeout_height} (current {current_height})"
            ),
        }
    }
}

impl std::error::Error for PendingReactError {}

/// Domain tag for the React replay gate.
///
/// React promise ids are not note spends and must never enter the faithful
/// FNSP nullifier sequence. This independent tag prevents a raw 32-byte value
/// from being silently substituted across those two semantic domains.
pub const REACTIVE_NULLIFIER_DOMAIN_V1: &str = "dregg-reactive-nullifiers-v1";

/// A canonical React-only one-shot set.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ReactiveNullifierSet {
    spent: BTreeSet<Nullifier>,
}

/// A React replay-set image or insertion was invalid.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReactiveNullifierError {
    AlreadyReacted { pending_id: Nullifier },
    NonCanonical,
}

impl fmt::Display for ReactiveNullifierError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AlreadyReacted { pending_id } => write!(
                f,
                "React pending_id {} was already consumed",
                hex::encode(pending_id.0)
            ),
            Self::NonCanonical => {
                f.write_str("reactive nullifier keys are not strictly sorted and unique")
            }
        }
    }
}

impl std::error::Error for ReactiveNullifierError {}

impl ReactiveNullifierSet {
    pub fn new() -> Self {
        Self::default()
    }

    /// Restore a strictly sorted, duplicate-free durable image.
    pub fn from_canonical_keys(keys: &[[u8; 32]]) -> Result<Self, ReactiveNullifierError> {
        if keys.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(ReactiveNullifierError::NonCanonical);
        }
        Ok(Self {
            spent: keys.iter().copied().map(Nullifier).collect(),
        })
    }

    pub fn canonical_keys(&self) -> Vec<[u8; 32]> {
        self.spent.iter().map(|nullifier| nullifier.0).collect()
    }

    pub fn contains(&self, pending_id: &Nullifier) -> bool {
        self.spent.contains(pending_id)
    }

    pub fn insert(&mut self, pending_id: Nullifier) -> Result<(), ReactiveNullifierError> {
        if self.spent.insert(pending_id) {
            Ok(())
        } else {
            Err(ReactiveNullifierError::AlreadyReacted { pending_id })
        }
    }

    pub fn remove(&mut self, pending_id: &Nullifier) -> bool {
        self.spent.remove(pending_id)
    }

    pub fn len(&self) -> usize {
        self.spent.len()
    }

    pub fn is_empty(&self) -> bool {
        self.spent.is_empty()
    }

    /// Domain-separated CAS digest over the canonical key image.
    pub fn commitment(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key(REACTIVE_NULLIFIER_DOMAIN_V1);
        hasher.update(&(self.spent.len() as u64).to_le_bytes());
        for nullifier in &self.spent {
            hasher.update(&nullifier.0);
        }
        *hasher.finalize().as_bytes()
    }
}

// ─── Core Types ─────────────────────────────────────────────────────────────

/// A pending turn entry awaiting resolution.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PendingEntry {
    /// The turn that will execute once its condition is met.
    pub turn: Turn,
    /// The condition that must be satisfied before execution.
    pub condition: ResolutionCondition,
    /// Hashes of turns that are waiting on THIS turn to resolve.
    pub dependents: Vec<[u8; 32]>,
    /// Block height at which this pending entry was submitted.
    pub submitted_at: u64,
    /// Block height at which this pending entry times out.
    pub timeout_height: u64,
    /// Durable release phase.  This is deliberately private: wire-authored
    /// Promise/Notify effects may create only `Waiting` entries.  A successful
    /// condition discharge advances the entry to `ReadyToPublish`; publishing
    /// the durable `ReadyToExecute` event advances it to `Published`.  Neither
    /// phase removes the exact wake -- only its real finalized receipt does.
    release_state: PendingReleaseState,
}

/// Durable lifecycle of a registered wake between condition discharge and its
/// real finalized execution.
///
/// Version 2 of the private canonical wire carries this phase explicitly; the
/// decoder migrates version-1 entries to `Waiting`.  The two non-default values
/// close the crash/replay seam: a release is retained across restart and a
/// published release is not emitted twice.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
enum PendingReleaseState {
    #[default]
    Waiting,
    ReadyToPublish,
    Published,
}

/// A condition that must be met before a pending turn can execute.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ResolutionCondition {
    /// Waiting for a specific turn receipt to arrive.
    /// If `federation_id` is Some, the receipt comes from a remote federation.
    AwaitReceipt {
        /// Hash of the turn whose receipt we are waiting for.
        turn_hash: [u8; 32],
        /// If Some, the receipt comes from a remote federation.
        federation_id: Option<[u8; 32]>,
    },
    /// Waiting for a ProofCondition to be satisfied (same as ConditionalTurn).
    AwaitCondition(ProofCondition),
    /// Waiting for a specific block height to be reached.
    AwaitHeight(u64),
}

/// The outcome of resolving a pending turn.
#[derive(Clone, Debug)]
pub enum ResolutionOutcome {
    /// The turn was executed successfully; here is its receipt.
    Resolved(TurnReceipt),
    /// The promise is broken; the turn will never execute.
    Broken(BrokenReason),
}

/// Why a promise was broken.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum BrokenReason {
    /// The turn was rejected during execution.
    TurnRejected(TurnError),
    /// The pending turn timed out (timeout_height exceeded).
    Timeout,
    /// The remote federation is unreachable.
    FederationUnreachable,
    /// An upstream dependency broke, causing this promise to break.
    DependencyBroken(Box<BrokenReason>),
}

impl std::fmt::Display for BrokenReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BrokenReason::TurnRejected(err) => write!(f, "turn rejected: {err}"),
            BrokenReason::Timeout => write!(f, "timeout"),
            BrokenReason::FederationUnreachable => write!(f, "federation unreachable"),
            BrokenReason::DependencyBroken(inner) => {
                write!(f, "dependency broken: {inner}")
            }
        }
    }
}

/// An event emitted by the registry during resolution or timeout checking.
#[derive(Clone, Debug)]
pub enum ResolutionEvent {
    /// A pending turn was resolved (executed successfully).
    Resolved {
        /// The hash of the turn that was resolved.
        turn_hash: [u8; 32],
        /// The receipt from executing the turn.
        receipt: TurnReceipt,
    },
    /// A dependent turn's condition has been met and it is ready to execute.
    /// The node must run TurnExecutor on it and then call `resolve()` with the
    /// real receipt (or Broken if execution fails).
    ReadyToExecute {
        /// The hash of the turn that is ready.
        turn_hash: [u8; 32],
        /// The turn that needs to be executed.
        turn: Turn,
    },
    /// A pending turn's promise was broken.
    Broken {
        /// The hash of the turn whose promise was broken.
        turn_hash: [u8; 32],
        /// Why the promise was broken.
        reason: BrokenReason,
    },
}

/// A handle returned when a pending turn is submitted.
#[derive(Clone, Debug)]
pub struct PendingHandle {
    /// The hash identifying the pending turn.
    pub turn_hash: [u8; 32],
    /// The current status of this pending turn.
    pub status: PendingStatus,
}

/// The current status of a pending turn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PendingStatus {
    /// Still waiting for its condition to be met.
    Pending,
    /// Successfully resolved with a receipt.
    Resolved,
    /// Promise broken.
    Broken,
}

// ─── Registry ───────────────────────────────────────────────────────────────

/// Registry tracking all unresolved pending turns and their dependency graph.
///
/// The registry provides:
/// - Submit: register a pending turn with a resolution condition
/// - Resolve: mark a turn as resolved or broken, cascading to dependents
/// - Timeout: check for expired pending turns and propagate broken promises
#[derive(Clone, Debug, Default)]
pub struct PendingTurnRegistry {
    /// Map from turn hash to pending entry.  `BTreeMap` is intentional: postcard
    /// serialization must be byte-identical regardless of insertion history so
    /// nodes can CAS and replay this state without HashMap iteration entropy.
    pending: BTreeMap<[u8; 32], PendingEntry>,
}

/// Private v1 wire. `Turn` contains a `HashMap` of sovereign witnesses, so
/// serializing `PendingEntry` directly would reintroduce randomized iteration
/// order inside an otherwise ordered registry. The base turn is serialized with
/// that map empty and the witnesses ride this sorted vector instead.
#[derive(Serialize, Deserialize)]
struct PendingRegistryWireV1 {
    entries: Vec<PendingEntryWireV1>,
}

#[derive(Serialize, Deserialize)]
struct PendingEntryWireV1 {
    turn_hash: [u8; 32],
    turn_without_sovereign_witnesses: Turn,
    sovereign_witnesses: Vec<(dregg_cell::CellId, crate::turn::SovereignCellWitness)>,
    condition: ResolutionCondition,
    dependents: Vec<[u8; 32]>,
    submitted_at: u64,
    timeout_height: u64,
}

#[derive(Serialize, Deserialize)]
struct PendingRegistryWireV2 {
    entries: Vec<PendingEntryWireV2>,
}

#[derive(Serialize, Deserialize)]
struct PendingEntryWireV2 {
    turn_hash: [u8; 32],
    turn_without_sovereign_witnesses: Turn,
    sovereign_witnesses: Vec<(dregg_cell::CellId, crate::turn::SovereignCellWitness)>,
    condition: ResolutionCondition,
    dependents: Vec<[u8; 32]>,
    submitted_at: u64,
    timeout_height: u64,
    release_state: PendingReleaseState,
}

impl PendingTurnRegistry {
    /// Create a new empty registry.
    pub fn new() -> Self {
        Self {
            pending: BTreeMap::new(),
        }
    }

    /// Canonical, versioned durable representation.
    pub fn to_canonical_bytes(&self) -> Result<Vec<u8>, PendingRegistryCodecError> {
        self.validate()?;
        let entries = self
            .pending
            .iter()
            .map(|(turn_hash, entry)| {
                let mut turn_without_sovereign_witnesses = entry.turn.clone();
                let mut sovereign_witnesses: Vec<_> = turn_without_sovereign_witnesses
                    .sovereign_witnesses
                    .drain()
                    .collect();
                sovereign_witnesses.sort_by_key(|(cell, _)| *cell.as_bytes());
                let mut dependents = entry.dependents.clone();
                dependents.sort_unstable();
                dependents.dedup();
                PendingEntryWireV2 {
                    turn_hash: *turn_hash,
                    turn_without_sovereign_witnesses,
                    sovereign_witnesses,
                    condition: entry.condition.clone(),
                    dependents,
                    submitted_at: entry.submitted_at,
                    timeout_height: entry.timeout_height,
                    release_state: entry.release_state,
                }
            })
            .collect();
        let wire = PendingRegistryWireV2 { entries };
        Self::encode_canonical_wire(PENDING_REGISTRY_MAGIC_V2, &wire)
    }

    /// Reconstruct the historical v1 image while validating a v1 snapshot.
    /// A v1 entry has no release phase, so only its migrated `Waiting` form can
    /// be represented here.
    fn to_canonical_bytes_v1(&self) -> Result<Vec<u8>, PendingRegistryCodecError> {
        self.validate()?;
        if self
            .pending
            .values()
            .any(|entry| entry.release_state != PendingReleaseState::Waiting)
        {
            return Err(PendingRegistryCodecError::NonCanonical);
        }
        let entries = self
            .pending
            .iter()
            .map(|(turn_hash, entry)| {
                let mut turn_without_sovereign_witnesses = entry.turn.clone();
                let mut sovereign_witnesses: Vec<_> = turn_without_sovereign_witnesses
                    .sovereign_witnesses
                    .drain()
                    .collect();
                sovereign_witnesses.sort_by_key(|(cell, _)| *cell.as_bytes());
                let mut dependents = entry.dependents.clone();
                dependents.sort_unstable();
                dependents.dedup();
                PendingEntryWireV1 {
                    turn_hash: *turn_hash,
                    turn_without_sovereign_witnesses,
                    sovereign_witnesses,
                    condition: entry.condition.clone(),
                    dependents,
                    submitted_at: entry.submitted_at,
                    timeout_height: entry.timeout_height,
                }
            })
            .collect();
        let wire = PendingRegistryWireV1 { entries };
        Self::encode_canonical_wire(PENDING_REGISTRY_MAGIC_V1, &wire)
    }

    fn encode_canonical_wire<T: Serialize>(
        magic: &[u8; 5],
        wire: &T,
    ) -> Result<Vec<u8>, PendingRegistryCodecError> {
        let payload = postcard::to_allocvec(&wire)
            .map_err(|error| PendingRegistryCodecError::Decode(error.to_string()))?;
        let size = magic.len().saturating_add(payload.len());
        if size > MAX_PENDING_REGISTRY_BYTES {
            return Err(PendingRegistryCodecError::TooLarge {
                size,
                max: MAX_PENDING_REGISTRY_BYTES,
            });
        }
        let mut encoded = Vec::with_capacity(size);
        encoded.extend_from_slice(magic);
        encoded.extend_from_slice(&payload);
        Ok(encoded)
    }

    /// Decode and revalidate one durable snapshot, rejecting alternate postcard
    /// encodings and any key that does not equal the contained wake turn's hash.
    pub fn from_canonical_bytes(bytes: &[u8]) -> Result<Self, PendingRegistryCodecError> {
        if bytes.len() > MAX_PENDING_REGISTRY_BYTES {
            return Err(PendingRegistryCodecError::TooLarge {
                size: bytes.len(),
                max: MAX_PENDING_REGISTRY_BYTES,
            });
        }
        let (wire_entries, is_v1) =
            if let Some(payload) = bytes.strip_prefix(PENDING_REGISTRY_MAGIC_V2) {
                let wire: PendingRegistryWireV2 = postcard::from_bytes(payload)
                    .map_err(|error| PendingRegistryCodecError::Decode(error.to_string()))?;
                (wire.entries, false)
            } else if let Some(payload) = bytes.strip_prefix(PENDING_REGISTRY_MAGIC_V1) {
                let wire: PendingRegistryWireV1 = postcard::from_bytes(payload)
                    .map_err(|error| PendingRegistryCodecError::Decode(error.to_string()))?;
                let entries = wire
                    .entries
                    .into_iter()
                    .map(|entry| PendingEntryWireV2 {
                        turn_hash: entry.turn_hash,
                        turn_without_sovereign_witnesses: entry.turn_without_sovereign_witnesses,
                        sovereign_witnesses: entry.sovereign_witnesses,
                        condition: entry.condition,
                        dependents: entry.dependents,
                        submitted_at: entry.submitted_at,
                        timeout_height: entry.timeout_height,
                        release_state: PendingReleaseState::Waiting,
                    })
                    .collect();
                (entries, true)
            } else {
                return Err(PendingRegistryCodecError::InvalidMagic);
            };
        if wire_entries.len() > MAX_PENDING_TURNS {
            return Err(PendingRegistryCodecError::TooManyEntries {
                count: wire_entries.len(),
                max: MAX_PENDING_TURNS,
            });
        }
        let mut pending = BTreeMap::new();
        for wire_entry in wire_entries {
            let PendingEntryWireV2 {
                turn_hash,
                mut turn_without_sovereign_witnesses,
                sovereign_witnesses,
                condition,
                dependents,
                submitted_at,
                timeout_height,
                release_state,
            } = wire_entry;
            if !turn_without_sovereign_witnesses
                .sovereign_witnesses
                .is_empty()
            {
                return Err(PendingRegistryCodecError::NonCanonical);
            }
            let mut previous = None;
            for (cell, witness) in sovereign_witnesses {
                if previous.is_some_and(|prior| prior >= *cell.as_bytes()) {
                    return Err(PendingRegistryCodecError::NonCanonical);
                }
                previous = Some(*cell.as_bytes());
                turn_without_sovereign_witnesses
                    .sovereign_witnesses
                    .insert(cell, witness);
            }
            if dependents.windows(2).any(|pair| pair[0] >= pair[1]) {
                return Err(PendingRegistryCodecError::NonCanonical);
            }
            let entry = PendingEntry {
                turn: turn_without_sovereign_witnesses,
                condition,
                dependents,
                submitted_at,
                timeout_height,
                release_state,
            };
            if pending.insert(turn_hash, entry).is_some() {
                return Err(PendingRegistryCodecError::NonCanonical);
            }
        }
        let decoded = Self { pending };
        decoded.validate()?;
        let canonical = if is_v1 {
            decoded.to_canonical_bytes_v1()?
        } else {
            decoded.to_canonical_bytes()?
        };
        if canonical.as_slice() != bytes {
            return Err(PendingRegistryCodecError::NonCanonical);
        }
        Ok(decoded)
    }

    /// Domain-separated digest used by durable compare-and-swap records.
    pub fn commitment(&self) -> Result<[u8; 32], PendingRegistryCodecError> {
        let encoded = self.to_canonical_bytes()?;
        let mut hasher = blake3::Hasher::new_derive_key("dregg-pending-registry-v1");
        hasher.update(&encoded);
        Ok(*hasher.finalize().as_bytes())
    }

    fn validate(&self) -> Result<(), PendingRegistryCodecError> {
        if self.pending.len() > MAX_PENDING_TURNS {
            return Err(PendingRegistryCodecError::TooManyEntries {
                count: self.pending.len(),
                max: MAX_PENDING_TURNS,
            });
        }
        for (stored, entry) in &self.pending {
            let canonical = entry.turn.hash();
            if *stored != canonical {
                return Err(PendingRegistryCodecError::TurnHashMismatch {
                    stored: *stored,
                    canonical,
                });
            }
        }
        Ok(())
    }

    /// Submit a new pending turn with a resolution condition and timeout.
    ///
    /// Returns the turn hash that identifies this pending entry.
    pub fn submit_pending(
        &mut self,
        turn: Turn,
        condition: ResolutionCondition,
        timeout_height: u64,
    ) -> [u8; 32] {
        self.submit_idempotent(turn, condition, timeout_height, 0)
    }

    /// Submit a new pending turn with a resolution condition, timeout, and submission height.
    ///
    /// Returns the turn hash that identifies this pending entry.
    pub fn submit_pending_at(
        &mut self,
        turn: Turn,
        condition: ResolutionCondition,
        timeout_height: u64,
        submitted_at: u64,
    ) -> [u8; 32] {
        self.submit_idempotent(turn, condition, timeout_height, submitted_at)
    }

    /// Strict admission used by the executor.  Unlike the compatibility
    /// `submit_pending*` helpers, a duplicate is an explicit refusal: a signed
    /// Promise/Notify turn must never overwrite another promise's condition,
    /// deadline, or dependency list under the same wake hash.
    pub fn try_submit_pending_at(
        &mut self,
        turn: Turn,
        condition: ResolutionCondition,
        timeout_height: u64,
        submitted_at: u64,
    ) -> Result<[u8; 32], PendingSubmitError> {
        let turn_hash = turn.hash();
        if self.pending.contains_key(&turn_hash) {
            return Err(PendingSubmitError::AlreadyPending { turn_hash });
        }
        if self.pending.len() >= MAX_PENDING_TURNS {
            return Err(PendingSubmitError::RegistryFull {
                max: MAX_PENDING_TURNS,
            });
        }
        let entry = PendingEntry {
            turn,
            condition,
            dependents: Vec::new(),
            submitted_at,
            timeout_height,
            release_state: PendingReleaseState::Waiting,
        };
        self.pending.insert(turn_hash, entry);
        Ok(turn_hash)
    }

    fn submit_idempotent(
        &mut self,
        turn: Turn,
        condition: ResolutionCondition,
        timeout_height: u64,
        submitted_at: u64,
    ) -> [u8; 32] {
        let turn_hash = turn.hash();
        self.pending.entry(turn_hash).or_insert(PendingEntry {
            turn,
            condition,
            dependents: Vec::new(),
            submitted_at,
            timeout_height,
            release_state: PendingReleaseState::Waiting,
        });
        turn_hash
    }

    /// Register a dependency: `dependent_hash` is waiting on `pending_hash`.
    ///
    /// When `pending_hash` resolves (or breaks), `dependent_hash` will be notified.
    pub fn register_dependent(&mut self, pending_hash: [u8; 32], dependent_hash: [u8; 32]) {
        if let Some(entry) = self.pending.get_mut(&pending_hash) {
            if !entry.dependents.contains(&dependent_hash) {
                entry.dependents.push(dependent_hash);
            }
        }
    }

    /// Resolve a pending turn with the given outcome.
    ///
    /// If `Resolved`: the turn executed successfully. Check all dependents to see
    /// if their conditions are now met (cascading resolution).
    ///
    /// If `Broken`: propagate `BrokenReason::DependencyBroken` to all dependents
    /// recursively.
    ///
    /// Returns a list of all resolution events that occurred (including cascading).
    pub fn resolve(
        &mut self,
        turn_hash: [u8; 32],
        outcome: ResolutionOutcome,
    ) -> Vec<ResolutionEvent> {
        let mut events = match outcome {
            ResolutionOutcome::Resolved(receipt) => {
                // A caller may not consume one registered wake by handing us a
                // receipt for another turn.  Finalization supplies this exact
                // equality; keeping it here makes the registry independently
                // fail closed and rules out synthetic/content-shaped receipts.
                if receipt.turn_hash != turn_hash {
                    Vec::new()
                } else if let Some(entry) = self.pending.remove(&turn_hash) {
                    let mut events = vec![ResolutionEvent::Resolved {
                        turn_hash,
                        receipt: receipt.clone(),
                    }];

                    // Cascade resolution to dependents whose conditions are now met.
                    self.cascade_resolved(turn_hash, &entry.dependents, &receipt, &mut events);
                    events
                } else {
                    Vec::new()
                }
            }
            ResolutionOutcome::Broken(reason) => {
                if let Some(entry) = self.pending.remove(&turn_hash) {
                    self.propagate_broken(turn_hash, &entry.dependents, reason)
                } else {
                    Vec::new()
                }
            }
        };

        // React discharges its condition while applying the carrier turn, but
        // the Ready event may become observable only if that carrier commits.
        // The finalized caller invokes `resolve` after successful execution;
        // draining here therefore welds Ready publication to the same durable
        // executor-state/outbox transaction.  `Published` survives restart and
        // prevents a duplicate release while the exact wake remains retained.
        events.extend(self.take_ready_events());
        events
    }

    /// Cascade to dependents whose conditions are met: emit ReadyToExecute events.
    ///
    /// Unlike the old approach that fabricated fake receipts, this keeps the entry
    /// in the registry and signals the caller (the node) to actually execute it.
    /// The node should then call `resolve()` with the real receipt, which will
    /// remove the entry and cascade to further dependents.
    fn cascade_resolved(
        &mut self,
        resolved_hash: [u8; 32],
        dependents: &[[u8; 32]],
        _trigger_receipt: &TurnReceipt,
        events: &mut Vec<ResolutionEvent>,
    ) {
        for &dep_hash in dependents {
            // Check condition without removing.
            let should_resolve = self
                .pending
                .get(&dep_hash)
                .map(|e| self.condition_met_by_receipt(&e.condition, &resolved_hash))
                .unwrap_or(false);

            if should_resolve {
                // The entry stays in the registry. Mark the release before
                // surfacing it; `take_ready_events` below advances it to the
                // durable Published phase and returns the exact stored wake.
                if let Some(entry) = self.pending.get_mut(&dep_hash) {
                    if entry.release_state == PendingReleaseState::Waiting {
                        entry.release_state = PendingReleaseState::ReadyToPublish;
                    }
                }
                // NOTE: We do NOT recursively cascade here. The node will execute the
                // turn, get a real receipt, and call resolve() again, which will cascade
                // to any further dependents at that point.
            }
        }

        events.extend(self.take_ready_events());
    }

    /// Check all pending turns for timeout at the given block height.
    ///
    /// Returns resolution events for all turns that have timed out.
    /// Timed-out turns are removed and their dependents get broken-promise propagation.
    pub fn check_timeouts(&mut self, current_height: u64) -> Vec<ResolutionEvent> {
        // Collect timed-out turn hashes first to avoid borrow conflicts.
        let timed_out: Vec<[u8; 32]> = self
            .pending
            .iter()
            .filter(|(_, entry)| {
                entry.release_state == PendingReleaseState::Waiting
                    && current_height > entry.timeout_height
            })
            .map(|(hash, _)| *hash)
            .collect();

        let mut events = Vec::new();
        for hash in timed_out {
            let sub_events = self.resolve(hash, ResolutionOutcome::Broken(BrokenReason::Timeout));
            events.extend(sub_events);
        }
        events
    }

    /// Look up a pending entry by its turn hash.
    pub fn get_pending(&self, hash: &[u8; 32]) -> Option<&PendingEntry> {
        self.pending.get(hash)
    }

    /// Bind a React attempt to the exact live promise authority before any
    /// nullifier or registry mutation occurs.
    ///
    /// The wake hash binds the object, `wake.agent` binds the only cell allowed
    /// to discharge it, and the stored `AwaitCondition` binds the exact proof
    /// statement.  Missing entries fail closed: there is no "out-of-band" React
    /// that can mint its own condition or infinite timeout.
    pub fn authorize_react(
        &self,
        pending_id: &[u8; 32],
        actor: &dregg_cell::CellId,
        condition: &ProofCondition,
        wake: &Turn,
        current_height: u64,
    ) -> Result<u64, PendingReactError> {
        if wake.hash() != *pending_id {
            return Err(PendingReactError::WakeHashMismatch);
        }
        let entry = self
            .pending
            .get(pending_id)
            .ok_or(PendingReactError::NotRegistered)?;
        // The key was validated on durable restore/submission, but repeat the
        // binding here at the authority boundary rather than trusting map shape.
        if entry.turn.hash() != *pending_id {
            return Err(PendingReactError::WakeHashMismatch);
        }
        let expected = entry.turn.agent;
        if wake.agent != expected || *actor != expected {
            return Err(PendingReactError::ReactorMismatch {
                expected,
                actual: *actor,
            });
        }
        let ResolutionCondition::AwaitCondition(expected_condition) = &entry.condition else {
            return Err(PendingReactError::ConditionIsNotProofDriven);
        };
        if expected_condition != condition {
            return Err(PendingReactError::ConditionMismatch);
        }
        if entry.release_state != PendingReleaseState::Waiting {
            return Err(PendingReactError::AlreadyReleased);
        }
        if current_height > entry.timeout_height {
            return Err(PendingReactError::Expired {
                timeout_height: entry.timeout_height,
                current_height,
            });
        }
        Ok(entry.timeout_height)
    }

    /// Advance an authenticated proof-driven wake to the durable release phase.
    ///
    /// This does not remove the pending entry and does not fabricate a receipt.
    /// The next successful finalized executor boundary drains exactly one
    /// [`ResolutionEvent::ReadyToExecute`]; only a later exact finalized receipt
    /// may call [`Self::resolve`] and remove the wake.
    pub fn mark_react_ready(
        &mut self,
        pending_id: &[u8; 32],
        actor: &dregg_cell::CellId,
        condition: &ProofCondition,
        wake: &Turn,
        current_height: u64,
    ) -> Result<(), PendingReactError> {
        self.authorize_react(pending_id, actor, condition, wake, current_height)?;
        let entry = self
            .pending
            .get_mut(pending_id)
            .ok_or(PendingReactError::NotRegistered)?;
        entry.release_state = PendingReleaseState::ReadyToPublish;
        Ok(())
    }

    /// Return whether a condition has been discharged and the wake is retained
    /// awaiting real finalized execution.
    pub fn is_released(&self, pending_id: &[u8; 32]) -> bool {
        self.pending
            .get(pending_id)
            .is_some_and(|entry| entry.release_state != PendingReleaseState::Waiting)
    }

    /// Publish each newly released wake at most once, in canonical hash order.
    ///
    /// The transition to `Published` and the returned events are committed by
    /// the node in the same finalized executor-state/outbox transaction.  If
    /// that transaction aborts, the isolated executor is discarded; retry from
    /// the durable `ReadyToPublish` predecessor emits the event again exactly as
    /// required.  After a successful commit, restart observes `Published` and
    /// emits nothing.
    pub(crate) fn take_ready_events(&mut self) -> Vec<ResolutionEvent> {
        let mut events = Vec::new();
        for (turn_hash, entry) in &mut self.pending {
            if entry.release_state == PendingReleaseState::ReadyToPublish {
                entry.release_state = PendingReleaseState::Published;
                events.push(ResolutionEvent::ReadyToExecute {
                    turn_hash: *turn_hash,
                    turn: entry.turn.clone(),
                });
            }
        }
        events
    }

    /// Returns the number of currently pending turns.
    pub fn len(&self) -> usize {
        self.pending.len()
    }

    /// Returns true if the registry has no pending turns.
    pub fn is_empty(&self) -> bool {
        self.pending.is_empty()
    }

    /// Check if a resolution condition is satisfied by a specific receipt arrival.
    fn condition_met_by_receipt(
        &self,
        condition: &ResolutionCondition,
        receipt_turn_hash: &[u8; 32],
    ) -> bool {
        match condition {
            ResolutionCondition::AwaitReceipt { turn_hash, .. } => turn_hash == receipt_turn_hash,
            ResolutionCondition::AwaitCondition(_) => {
                // ProofCondition requires explicit proof presentation, not just receipt arrival.
                false
            }
            ResolutionCondition::AwaitHeight(_) => {
                // Height-based conditions are checked by check_timeouts / check_heights.
                false
            }
        }
    }

    /// Propagate a broken promise to all dependents recursively.
    fn propagate_broken(
        &mut self,
        broken_hash: [u8; 32],
        dependents: &[[u8; 32]],
        reason: BrokenReason,
    ) -> Vec<ResolutionEvent> {
        let mut events = vec![ResolutionEvent::Broken {
            turn_hash: broken_hash,
            reason: reason.clone(),
        }];

        for &dep_hash in dependents {
            if let Some(dep_entry) = self.pending.remove(&dep_hash) {
                let dep_reason = BrokenReason::DependencyBroken(Box::new(reason.clone()));
                let sub_events = self.propagate_broken(dep_hash, &dep_entry.dependents, dep_reason);
                events.extend(sub_events);
            }
        }

        events
    }

    /// Check for pending turns whose AwaitHeight condition is now satisfied.
    ///
    /// Returns the turn hashes of entries whose height condition is met.
    /// The caller is responsible for actually executing these turns and calling
    /// `resolve()` with the outcome.
    pub fn check_height_conditions(&self, current_height: u64) -> Vec<[u8; 32]> {
        self.pending
            .iter()
            .filter(|(_, entry)| {
                entry.release_state == PendingReleaseState::Waiting
                    && matches!(
                        entry.condition,
                        ResolutionCondition::AwaitHeight(h) if current_height >= h
                    )
            })
            .map(|(hash, _)| *hash)
            .collect()
    }
}

impl crate::executor::TurnExecutor {
    /// Restore the dedicated React replay gate from a canonical durable image.
    pub fn set_reactive_nullifiers(&self, nullifiers: ReactiveNullifierSet) {
        *self
            .reactive_nullifiers
            .lock()
            .unwrap_or_else(|error| error.into_inner()) = nullifiers;
    }

    /// Canonical React replay-gate image for same-transaction persistence.
    pub fn reactive_nullifier_keys(&self) -> Vec<[u8; 32]> {
        self.reactive_nullifiers
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .canonical_keys()
    }

    /// Domain-separated pre-state digest for the React replay-gate CAS.
    pub fn reactive_nullifier_commitment(&self) -> [u8; 32] {
        self.reactive_nullifiers
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .commitment()
    }

    /// Canonical pre-state digest for the durable pending-registry CAS.
    ///
    /// A node captures this before executing an isolated finalized-turn
    /// candidate, then submits it beside the canonical successor bytes. The
    /// store compares it with its latest durable snapshot before publishing
    /// either the turn or the registry transition.
    pub fn reactive_registry_commitment(&self) -> Result<[u8; 32], PendingRegistryCodecError> {
        self.reactive_registry
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .commitment()
    }

    /// Canonical successor bytes for same-transaction durable publication.
    pub fn reactive_registry_canonical_bytes(&self) -> Result<Vec<u8>, PendingRegistryCodecError> {
        self.reactive_registry
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .to_canonical_bytes()
    }

    /// Resolve a finalized wake turn against this executor's candidate
    /// registry before its successor snapshot is captured.
    ///
    /// This deliberately mutates the isolated executor, not a second node-RAM
    /// registry. The returned cascade is observer work to publish only after
    /// the carrying finalized transaction commits.
    pub fn resolve_pending_receipt(
        &self,
        turn_hash: [u8; 32],
        receipt: TurnReceipt,
    ) -> Vec<ResolutionEvent> {
        self.reactive_registry
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .resolve(turn_hash, ResolutionOutcome::Resolved(receipt))
    }
}

// ─── Tests ──────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::action::{Action, Authorization, CommitmentMode, DelegationMode};
    use crate::forest::CallForest;
    use dregg_cell::{CellId, Preconditions};

    /// Helper: create a minimal turn for testing.
    fn make_turn(agent_byte: u8, nonce: u64) -> Turn {
        let agent = CellId::from_bytes([agent_byte; 32]);
        let action = Action {
            target: agent,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        };
        let mut forest = CallForest::new();
        forest.add_root(action);
        Turn {
            agent,
            nonce,
            call_forest: forest,
            fee: 1000,
            memo: None,
            valid_until: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            previous_receipt_hash: None,
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    /// Helper: create a dummy receipt for a turn.
    fn make_receipt(turn: &Turn) -> TurnReceipt {
        TurnReceipt {
            turn_hash: turn.hash(),
            forest_hash: turn.call_forest.compute_hash(),
            pre_state_hash: [0u8; 32],
            post_state_hash: [1u8; 32],
            timestamp: 1000,
            effects_hash: [0u8; 32],
            computrons_used: 100,
            action_count: 1,
            previous_receipt_hash: None,
            agent: turn.agent,
            federation_id: [0u8; 32],
            routing_directives: vec![],
            introduction_exports: vec![],
            derivation_records: vec![],
            emitted_events: vec![],
            executor_signature: None,
            finality: Default::default(),
            was_encrypted: false,
            was_burn: false,
            consumed_capabilities: vec![],
        }
    }

    // ─── Test 1: Submit pending → resolve with receipt → turn executes ────

    #[test]
    fn test_submit_and_resolve() {
        let mut registry = PendingTurnRegistry::new();

        let turn_a = make_turn(1, 0);
        let turn_a_hash = turn_a.hash();

        // Submit turn A as pending, awaiting receipt of some external turn.
        let external_hash = [0xAB; 32];
        let hash = registry.submit_pending(
            turn_a.clone(),
            ResolutionCondition::AwaitReceipt {
                turn_hash: external_hash,
                federation_id: None,
            },
            100,
        );
        assert_eq!(hash, turn_a_hash);
        assert_eq!(registry.len(), 1);

        // Resolve with a receipt.
        let receipt = make_receipt(&turn_a);
        let events = registry.resolve(turn_a_hash, ResolutionOutcome::Resolved(receipt.clone()));

        assert_eq!(events.len(), 1);
        assert!(matches!(
            &events[0],
            ResolutionEvent::Resolved { turn_hash, receipt: r }
            if *turn_hash == turn_a_hash && r.turn_hash == receipt.turn_hash
        ));
        assert_eq!(registry.len(), 0);
    }

    // ─── Test 2: Submit pending → timeout → broken propagated ─────────────

    #[test]
    fn test_timeout_propagates_broken() {
        let mut registry = PendingTurnRegistry::new();

        let turn_a = make_turn(1, 0);
        let turn_a_hash = turn_a.hash();

        registry.submit_pending_at(
            turn_a,
            ResolutionCondition::AwaitReceipt {
                turn_hash: [0xBB; 32],
                federation_id: None,
            },
            50, // timeout at height 50
            10, // submitted at height 10
        );

        // At height 40: no timeout yet.
        let events = registry.check_timeouts(40);
        assert!(events.is_empty());
        assert_eq!(registry.len(), 1);

        // At height 51: timeout triggered.
        let events = registry.check_timeouts(51);
        assert_eq!(events.len(), 1);
        assert!(matches!(
            &events[0],
            ResolutionEvent::Broken { turn_hash, reason }
            if *turn_hash == turn_a_hash && matches!(reason, BrokenReason::Timeout)
        ));
        assert_eq!(registry.len(), 0);
    }

    // ─── Test 3: Chain A → B → C: C resolves → B resolves → A resolves ───

    #[test]
    fn test_cascading_resolution() {
        let mut registry = PendingTurnRegistry::new();

        let turn_c = make_turn(3, 0);
        let turn_b = make_turn(2, 0);
        let turn_a = make_turn(1, 0);

        let hash_c = turn_c.hash();
        let hash_b = turn_b.hash();
        let hash_a = turn_a.hash();

        // C awaits an external receipt.
        registry.submit_pending(
            turn_c.clone(),
            ResolutionCondition::AwaitReceipt {
                turn_hash: [0xEE; 32],
                federation_id: None,
            },
            1000,
        );

        // B awaits C's receipt.
        registry.submit_pending(
            turn_b.clone(),
            ResolutionCondition::AwaitReceipt {
                turn_hash: hash_c,
                federation_id: None,
            },
            1000,
        );

        // A awaits B's receipt.
        registry.submit_pending(
            turn_a.clone(),
            ResolutionCondition::AwaitReceipt {
                turn_hash: hash_b,
                federation_id: None,
            },
            1000,
        );

        // Register dependencies: C's resolution triggers B, B's triggers A.
        registry.register_dependent(hash_c, hash_b);
        registry.register_dependent(hash_b, hash_a);

        assert_eq!(registry.len(), 3);

        // Resolve C → should emit Resolved for C + ReadyToExecute for B (immediate dependent).
        let receipt_c = make_receipt(&turn_c);
        let events = registry.resolve(hash_c, ResolutionOutcome::Resolved(receipt_c));

        // Should have 2 events: C resolved, B ready to execute.
        assert_eq!(events.len(), 2, "expected 2 events, got {}", events.len());
        assert!(
            matches!(&events[0], ResolutionEvent::Resolved { turn_hash, .. } if *turn_hash == hash_c),
            "first event should be Resolved for C"
        );
        assert!(
            matches!(&events[1], ResolutionEvent::ReadyToExecute { turn_hash, .. } if *turn_hash == hash_b),
            "second event should be ReadyToExecute for B"
        );

        // B and A are still in the registry (B awaiting real execution, A awaiting B).
        assert_eq!(registry.len(), 2);

        // Now simulate the node executing B and resolving it with a real receipt.
        let receipt_b = make_receipt(&turn_b);
        let events2 = registry.resolve(hash_b, ResolutionOutcome::Resolved(receipt_b));

        // Should have 2 events: B resolved, A ready to execute.
        assert_eq!(events2.len(), 2, "expected 2 events, got {}", events2.len());
        assert!(
            matches!(&events2[0], ResolutionEvent::Resolved { turn_hash, .. } if *turn_hash == hash_b),
            "first event should be Resolved for B"
        );
        assert!(
            matches!(&events2[1], ResolutionEvent::ReadyToExecute { turn_hash, .. } if *turn_hash == hash_a),
            "second event should be ReadyToExecute for A"
        );

        // A is still in registry (awaiting real execution).
        assert_eq!(registry.len(), 1);

        // Node executes A and resolves it.
        let receipt_a = make_receipt(&turn_a);
        let events3 = registry.resolve(hash_a, ResolutionOutcome::Resolved(receipt_a));

        // Just A resolved, no further dependents.
        assert_eq!(events3.len(), 1);
        assert!(
            matches!(&events3[0], ResolutionEvent::Resolved { turn_hash, .. } if *turn_hash == hash_a),
        );

        // Registry should be empty now.
        assert_eq!(registry.len(), 0);
    }

    // ─── Test 4: Chain A → B: B breaks → A immediately broken ─────────────

    #[test]
    fn test_broken_propagation() {
        let mut registry = PendingTurnRegistry::new();

        let turn_b = make_turn(2, 0);
        let turn_a = make_turn(1, 0);

        let hash_b = turn_b.hash();
        let hash_a = turn_a.hash();

        // B awaits external.
        registry.submit_pending(
            turn_b,
            ResolutionCondition::AwaitReceipt {
                turn_hash: [0xFF; 32],
                federation_id: None,
            },
            1000,
        );

        // A awaits B.
        registry.submit_pending(
            turn_a,
            ResolutionCondition::AwaitReceipt {
                turn_hash: hash_b,
                federation_id: None,
            },
            1000,
        );

        // Register A as dependent of B.
        registry.register_dependent(hash_b, hash_a);

        // B breaks.
        let events = registry.resolve(
            hash_b,
            ResolutionOutcome::Broken(BrokenReason::TurnRejected(TurnError::PreconditionFailed {
                description: "test failure".to_string(),
            })),
        );

        // Should have 2 events: B broken, A broken (dependency).
        assert_eq!(events.len(), 2);

        assert!(matches!(
            &events[0],
            ResolutionEvent::Broken { turn_hash, reason }
            if *turn_hash == hash_b && matches!(reason, BrokenReason::TurnRejected(_))
        ));

        assert!(matches!(
            &events[1],
            ResolutionEvent::Broken { turn_hash, reason }
            if *turn_hash == hash_a && matches!(reason, BrokenReason::DependencyBroken(_))
        ));

        assert_eq!(registry.len(), 0);
    }

    // ─── Test 5: Cross-fed EventualRef → receipt arrives → resolves ───────

    #[test]
    fn test_cross_federation_resolution() {
        let mut registry = PendingTurnRegistry::new();

        let remote_federation_id = [0x42; 32];
        let remote_turn_hash = [0xDE; 32];

        let local_turn = make_turn(1, 0);
        let local_hash = local_turn.hash();

        // Local turn depends on a remote federation's receipt.
        registry.submit_pending(
            local_turn.clone(),
            ResolutionCondition::AwaitReceipt {
                turn_hash: remote_turn_hash,
                federation_id: Some(remote_federation_id),
            },
            500,
        );

        assert_eq!(registry.len(), 1);
        let entry = registry.get_pending(&local_hash).unwrap();
        assert!(matches!(
            &entry.condition,
            ResolutionCondition::AwaitReceipt { federation_id: Some(fid), .. }
            if *fid == remote_federation_id
        ));

        // Remote receipt arrives → resolve.
        let receipt = make_receipt(&local_turn);
        let events = registry.resolve(local_hash, ResolutionOutcome::Resolved(receipt));

        assert_eq!(events.len(), 1);
        assert!(matches!(&events[0], ResolutionEvent::Resolved { .. }));
        assert_eq!(registry.len(), 0);
    }

    // ─── Test 6: Cross-fed remote offline → timeout → broken ──────────────

    #[test]
    fn test_cross_federation_timeout() {
        let mut registry = PendingTurnRegistry::new();

        let remote_federation_id = [0x42; 32];
        let remote_turn_hash = [0xDE; 32];

        let local_turn = make_turn(1, 0);
        let local_hash = local_turn.hash();

        registry.submit_pending_at(
            local_turn,
            ResolutionCondition::AwaitReceipt {
                turn_hash: remote_turn_hash,
                federation_id: Some(remote_federation_id),
            },
            100, // timeout at height 100
            50,  // submitted at height 50
        );

        // Height 99: not timed out yet.
        let events = registry.check_timeouts(99);
        assert!(events.is_empty());

        // Height 101: timed out.
        let events = registry.check_timeouts(101);
        assert_eq!(events.len(), 1);
        assert!(matches!(
            &events[0],
            ResolutionEvent::Broken { turn_hash, reason }
            if *turn_hash == local_hash && matches!(reason, BrokenReason::Timeout)
        ));
        assert_eq!(registry.len(), 0);
    }

    // ─── Test 7: AwaitHeight condition ────────────────────────────────────

    #[test]
    fn test_await_height_condition() {
        let mut registry = PendingTurnRegistry::new();

        let turn = make_turn(1, 0);
        let hash = turn.hash();

        registry.submit_pending(turn, ResolutionCondition::AwaitHeight(200), 1000);

        // At height 100: not ready.
        let ready = registry.check_height_conditions(100);
        assert!(ready.is_empty());

        // At height 200: ready.
        let ready = registry.check_height_conditions(200);
        assert_eq!(ready.len(), 1);
        assert_eq!(ready[0], hash);

        // At height 300: still ready (hasn't been resolved yet).
        let ready = registry.check_height_conditions(300);
        assert_eq!(ready.len(), 1);
    }

    // ─── Test 8: Duplicate dependent registration is idempotent ───────────

    #[test]
    fn test_duplicate_dependent_idempotent() {
        let mut registry = PendingTurnRegistry::new();

        let turn_a = make_turn(1, 0);
        let turn_b = make_turn(2, 0);
        let hash_a = turn_a.hash();
        let hash_b = turn_b.hash();

        registry.submit_pending(
            turn_a,
            ResolutionCondition::AwaitReceipt {
                turn_hash: [0xFF; 32],
                federation_id: None,
            },
            1000,
        );
        registry.submit_pending(
            turn_b,
            ResolutionCondition::AwaitReceipt {
                turn_hash: hash_a,
                federation_id: None,
            },
            1000,
        );

        // Register same dependent twice.
        registry.register_dependent(hash_a, hash_b);
        registry.register_dependent(hash_a, hash_b);

        let entry = registry.get_pending(&hash_a).unwrap();
        assert_eq!(entry.dependents.len(), 1, "should not duplicate");
    }

    // ─── Test 9: Resolving non-existent hash is a no-op ──────────────────

    #[test]
    fn test_resolve_nonexistent() {
        let mut registry = PendingTurnRegistry::new();
        let events = registry.resolve([0xFF; 32], ResolutionOutcome::Broken(BrokenReason::Timeout));
        assert!(events.is_empty());
    }

    // ─── Test 10: Deep chain propagation ──────────────────────────────────

    #[test]
    fn test_deep_chain_broken_propagation() {
        let mut registry = PendingTurnRegistry::new();

        // Create a chain of 5 turns: E → D → C → B → A (E is deepest dependency).
        let turns: Vec<Turn> = (0..5).map(|i| make_turn(i + 1, 0)).collect();
        let hashes: Vec<[u8; 32]> = turns.iter().map(|t| t.hash()).collect();

        // Submit all as pending.
        for (i, turn) in turns.into_iter().enumerate() {
            let condition = if i == 0 {
                // First turn awaits external.
                ResolutionCondition::AwaitReceipt {
                    turn_hash: [0xEE; 32],
                    federation_id: None,
                }
            } else {
                // Each subsequent turn awaits the previous.
                ResolutionCondition::AwaitReceipt {
                    turn_hash: hashes[i - 1],
                    federation_id: None,
                }
            };
            registry.submit_pending(turn, condition, 1000);
        }

        // Register chain: each turn is a dependent of the previous.
        for i in 0..4 {
            registry.register_dependent(hashes[i], hashes[i + 1]);
        }

        assert_eq!(registry.len(), 5);

        // Break the first turn in the chain. Broken propagation IS recursive
        // (unlike resolution which requires actual execution), so all dependents break.
        let events = registry.resolve(
            hashes[0],
            ResolutionOutcome::Broken(BrokenReason::FederationUnreachable),
        );

        // All 5 should be broken.
        assert_eq!(events.len(), 5);
        for event in &events {
            assert!(matches!(event, ResolutionEvent::Broken { .. }));
        }
        assert_eq!(registry.len(), 0);
    }

    #[test]
    fn duplicate_wake_cannot_replace_condition_or_timeout() {
        let mut registry = PendingTurnRegistry::new();
        let wake = make_turn(7, 3);
        let wake_hash = wake.hash();
        let original =
            ResolutionCondition::AwaitCondition(ProofCondition::HashPreimage { hash: [0x11; 32] });
        registry
            .try_submit_pending_at(wake.clone(), original.clone(), 500, 40)
            .expect("first registration");

        let replacement =
            ResolutionCondition::AwaitCondition(ProofCondition::HashPreimage { hash: [0x22; 32] });
        assert_eq!(
            registry.try_submit_pending_at(wake, replacement, u64::MAX, 0),
            Err(PendingSubmitError::AlreadyPending {
                turn_hash: wake_hash
            })
        );
        let retained = registry.get_pending(&wake_hash).expect("retained entry");
        assert_eq!(retained.condition, original);
        assert_eq!(retained.timeout_height, 500);
        assert_eq!(retained.submitted_at, 40);
    }

    #[test]
    fn react_authority_binds_registered_actor_condition_and_timeout() {
        let mut registry = PendingTurnRegistry::new();
        let wake = make_turn(9, 1);
        let wake_hash = wake.hash();
        let condition = ProofCondition::HashPreimage { hash: [0x33; 32] };
        registry
            .try_submit_pending_at(
                wake.clone(),
                ResolutionCondition::AwaitCondition(condition.clone()),
                80,
                10,
            )
            .expect("register");

        assert_eq!(
            registry.authorize_react(&wake_hash, &wake.agent, &condition, &wake, 80),
            Ok(80)
        );
        let attacker = CellId::from_bytes([0xAA; 32]);
        assert!(matches!(
            registry.authorize_react(&wake_hash, &attacker, &condition, &wake, 80),
            Err(PendingReactError::ReactorMismatch { .. })
        ));
        assert_eq!(
            registry.authorize_react(
                &wake_hash,
                &wake.agent,
                &ProofCondition::HashPreimage { hash: [0x44; 32] },
                &wake,
                80,
            ),
            Err(PendingReactError::ConditionMismatch)
        );
        assert_eq!(
            registry.authorize_react(&wake_hash, &wake.agent, &condition, &wake, 81),
            Err(PendingReactError::Expired {
                timeout_height: 80,
                current_height: 81,
            })
        );
        assert_eq!(
            PendingTurnRegistry::new().authorize_react(
                &wake_hash,
                &wake.agent,
                &condition,
                &wake,
                10,
            ),
            Err(PendingReactError::NotRegistered)
        );
    }

    #[test]
    fn released_wake_survives_restart_and_only_exact_receipt_resolves() {
        let mut registry = PendingTurnRegistry::new();
        let wake = make_turn(11, 4);
        let wake_hash = wake.hash();
        let condition = ProofCondition::HashPreimage { hash: [0x55; 32] };
        registry
            .try_submit_pending_at(
                wake.clone(),
                ResolutionCondition::AwaitCondition(condition.clone()),
                80,
                10,
            )
            .expect("register wake");

        registry
            .mark_react_ready(&wake_hash, &wake.agent, &condition, &wake, 50)
            .expect("condition discharge releases exact wake");
        assert!(registry.is_released(&wake_hash));
        assert_eq!(registry.len(), 1, "release must retain the wake");
        assert_eq!(
            registry.authorize_react(&wake_hash, &wake.agent, &condition, &wake, 50),
            Err(PendingReactError::AlreadyReleased),
            "released wake cannot produce another dispatch"
        );
        assert!(
            registry.check_timeouts(1_000).is_empty(),
            "a condition discharged before deadline cannot timeout while awaiting finalization"
        );

        // Crash/restart before publication: ReadyToPublish is canonical durable
        // state and emits exactly one Ready event after restore.
        let before_publish = registry.to_canonical_bytes().expect("encode released wake");
        let mut restarted =
            PendingTurnRegistry::from_canonical_bytes(&before_publish).expect("restart restore");
        assert!(restarted.is_released(&wake_hash));
        let ready = restarted.take_ready_events();
        assert!(matches!(
            ready.as_slice(),
            [ResolutionEvent::ReadyToExecute { turn_hash, turn }]
                if *turn_hash == wake_hash && turn.hash() == wake_hash
        ));
        assert!(
            ready
                .iter()
                .all(|event| !matches!(event, ResolutionEvent::Resolved { .. })),
            "condition discharge must never fabricate terminal resolution"
        );

        // Crash/restart after durable publication: Published emits no duplicate.
        let after_publish = restarted
            .to_canonical_bytes()
            .expect("encode published wake");
        let mut restarted_again =
            PendingTurnRegistry::from_canonical_bytes(&after_publish).expect("restore published");
        assert!(restarted_again.take_ready_events().is_empty());
        assert_eq!(restarted_again.len(), 1);

        // A receipt for any other turn cannot consume the retained wake.
        let other = make_turn(12, 4);
        assert!(
            restarted_again
                .resolve(wake_hash, ResolutionOutcome::Resolved(make_receipt(&other)))
                .is_empty()
        );
        assert!(restarted_again.get_pending(&wake_hash).is_some());

        // Only the exact wake's real receipt produces Resolved and removes it.
        let real = make_receipt(&wake);
        let resolved =
            restarted_again.resolve(wake_hash, ResolutionOutcome::Resolved(real.clone()));
        assert!(matches!(
            resolved.as_slice(),
            [ResolutionEvent::Resolved { turn_hash, receipt }]
                if *turn_hash == wake_hash && receipt.receipt_hash() == real.receipt_hash()
        ));
        assert!(restarted_again.is_empty());
    }

    #[test]
    fn canonical_snapshot_is_insertion_order_independent_and_restart_safe() {
        let a = make_turn(3, 1);
        let b = make_turn(4, 2);
        let condition_a =
            ResolutionCondition::AwaitCondition(ProofCondition::HashPreimage { hash: [0xA1; 32] });
        let condition_b =
            ResolutionCondition::AwaitCondition(ProofCondition::HashPreimage { hash: [0xB2; 32] });
        let mut left = PendingTurnRegistry::new();
        left.try_submit_pending_at(a.clone(), condition_a.clone(), 100, 1)
            .unwrap();
        left.try_submit_pending_at(b.clone(), condition_b.clone(), 200, 2)
            .unwrap();
        let mut right = PendingTurnRegistry::new();
        right
            .try_submit_pending_at(b.clone(), condition_b, 200, 2)
            .unwrap();
        right
            .try_submit_pending_at(a.clone(), condition_a, 100, 1)
            .unwrap();

        let encoded = left.to_canonical_bytes().expect("encode");
        assert_eq!(encoded, right.to_canonical_bytes().expect("encode"));
        assert_eq!(left.commitment().unwrap(), right.commitment().unwrap());
        let restored = PendingTurnRegistry::from_canonical_bytes(&encoded).expect("restore");
        assert_eq!(restored.to_canonical_bytes().unwrap(), encoded);
        assert!(restored.get_pending(&a.hash()).is_some());
        assert!(restored.get_pending(&b.hash()).is_some());

        // Historical v1 snapshots remain strictly decodable.  They migrate to
        // Waiting entries and are emitted as the explicit v2 schema on the
        // next durable write.
        let encoded_v1 = left.to_canonical_bytes_v1().expect("encode v1");
        assert!(encoded_v1.starts_with(PENDING_REGISTRY_MAGIC_V1));
        let migrated =
            PendingTurnRegistry::from_canonical_bytes(&encoded_v1).expect("restore historical v1");
        assert!(migrated.get_pending(&a.hash()).is_some());
        assert!(migrated.get_pending(&b.hash()).is_some());
        assert!(
            migrated
                .to_canonical_bytes()
                .expect("migrate to v2")
                .starts_with(PENDING_REGISTRY_MAGIC_V2)
        );

        let mut trailing = encoded;
        trailing.push(0);
        assert!(PendingTurnRegistry::from_canonical_bytes(&trailing).is_err());
    }
}
