//! Note bridge: cross-federation value transfer via proof-carrying notes.
//!
//! Notes are self-proving (the STARK proof carries all verification needed). A note
//! "burned" (nullifier published) in Federation A can be "minted" in Federation B by
//! presenting the spending proof. The proof IS the bridge — no light client needed.
//!
//! # Security Model
//!
//! The bridge relies on:
//! 1. **Nullifier uniqueness**: Since nullifiers are derived from note-intrinsic data
//!    (not tree position), the same note produces the same nullifier everywhere. A
//!    nullifier revealed in Fed A cannot be replayed in Fed B for a different note.
//! 2. **Trusted roots**: The destination federation maintains a set of trusted roots
//!    from source federations. Only proofs against these roots are accepted.
//! 3. **Bridged-nullifier tracking**: Each federation tracks which nullifiers have been
//!    bridged in, preventing double-bridge (same note minted twice).
//! 4. **STARK proof verification**: The spending proof proves knowledge of the spending
//!    key and Merkle membership without revealing the note contents.
//! 5. **Destination binding**: The proof is cryptographically bound to a specific target
//!    federation via `destination_federation` in the public inputs, preventing replay
//!    to other federations (cross-federation double-spend).

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use dregg_cell::note::{NoteCommitment, Nullifier};
use dregg_types::AttestedRoot;

// ============================================================================
// Bridge Destination (multi-chain routing)
// ============================================================================

/// The target chain for a cross-chain bridge operation.
///
/// Used when initiating a bridge to specify where the value should be delivered.
/// Each variant carries chain-specific addressing information.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BridgeDestination {
    /// Bridge to an EVM-compatible chain (Ethereum, Polygon, Arbitrum, etc.).
    Evm {
        /// EIP-155 chain ID (1 = mainnet, 137 = Polygon, etc.).
        chain_id: u64,
        /// The bridge contract address on the EVM chain (20 bytes).
        contract: [u8; 20],
    },
    /// Bridge to Mina Protocol (via Pickles/Kimchi proof composition).
    Mina {
        /// Mina network identifier ("mainnet", "devnet", "berkeley", etc.).
        network: String,
    },
    /// Bridge to Midnight Network (via observation-based federation attestation).
    Midnight {
        /// The Midnight bridge contract address (Substrate account ID, variable length).
        contract_address: Vec<u8>,
    },
}

/// A portable note proof that can be presented to another federation.
///
/// This is the "bridge message" — the thing Alice creates in Federation A
/// and presents to Federation B to mint equivalent value.
///
/// # Cross-federation replay prevention
///
/// The `destination_federation` field cryptographically binds this proof to a
/// single target federation. It is included in the STARK proof's public inputs,
/// so the same spending proof cannot be replayed against a different federation.
/// Without this, a note burned in Federation Source could be bridged to BOTH
/// Federation A and Federation B (inflation bug).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PortableNoteProof {
    /// The nullifier (proves the note was spent in the source federation).
    pub nullifier: [u8; 32],
    /// The destination federation's identity (e.g., genesis root hash or configured ID).
    ///
    /// This binds the proof to a specific target federation. The destination
    /// federation MUST verify that this matches its own identity before accepting
    /// the bridge mint. This prevents cross-federation double-spend: the same
    /// spending proof cannot be replayed against multiple federations because the
    /// destination is included in the STARK proof's public inputs.
    pub destination_federation: [u8; 32],
    /// The source federation's attested root at time of spend.
    pub source_root: AttestedRoot,
    /// The STARK proof of valid spending (NoteSpendingAir).
    /// Serialized via postcard from a StarkProof.
    pub spending_proof: Vec<u8>,
    /// The new note commitment for the destination (what gets minted).
    pub destination_commitment: NoteCommitment,
    /// Value being transferred.
    pub value: u64,
    /// Asset type.
    pub asset_type: u64,
}

/// Errors that can occur during bridge operations.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BridgeError {
    /// The source root is not in our trusted set.
    UntrustedRoot {
        /// Short hex of the untrusted root for diagnostics.
        root_hex: String,
    },
    /// The source root does not contain a note_tree_root (federation too old).
    MissingNoteTreeRoot,
    /// The STARK spending proof failed verification.
    InvalidSpendingProof { reason: String },
    /// The nullifier has already been bridged (double-bridge attempt).
    AlreadyBridged { nullifier: [u8; 32] },
    /// The nullifier in the proof does not match the public inputs.
    NullifierMismatch,
    /// Value or asset type inconsistency.
    ValueMismatch { expected: u64, got: u64 },
    /// The declared value is at or above the window the note-spend claim tuple's two value limbs
    /// bind INJECTIVELY (`dregg_circuit::dsl::note_spending::NOTE_SPEND_VALUE_BOUND` = `p · 2^30`).
    ///
    /// Above it, `hi = (value >> 30) as u32` truncates bits 62..64, so `value` and `value + 2^62`
    /// produce a byte-identical claim tuple and an identical `mint_hash` — one addition turns a
    /// legitimately-proved note into a mint of `value + 2^62`, which `finalize.rs` then counts as
    /// a conservation INPUT at full width. A value the proof cannot bind is refused, never encoded.
    ValueNotFaithfullyBound {
        /// The declared value.
        value: u64,
        /// The exclusive bound (`p · 2^30`).
        bound: u64,
    },
    /// The 32-byte nullifier is not the canonical encoding of a claim-tuple nullifier felt
    /// (`dregg_circuit::dsl::note_spending::note_spend_nullifier_is_canonical` — bytes `0..4` a
    /// little-endian `u32 < p`, bytes `4..32` zero; the image of `dregg_cell::felt_to_bytes32`,
    /// which is how `dregg_cell::Note::nullifier` builds every nullifier).
    ///
    /// THE DUPLICATE-BRIDGE-MINT REFUSAL. The note-spend claim tuple pins the nullifier through
    /// exactly ONE felt (`pi[0]`). The executor used to recover that felt from the bytes with
    /// `hash_many(bytes32_to_8_limbs(·))`, which reduces each 4-byte chunk mod `p` — so every
    /// chunk had ≥ 2 preimages and one legitimate nullifier had `3^7 · 2 = 4374` byte-siblings
    /// with an identical claim felt (`3^8 = 6561` when the felt lane is itself below `2^32 − 2p`).
    /// `BridgedNullifierSet` keys RAW BYTES, so each sibling was a FRESH replay key against the
    /// SAME proof: `2^12.1`–`2^12.7` free re-mints per note at `O(1)`, each counted again by
    /// `turn/src/executor/finalize.rs`'s per-asset conservation ledger.
    ///
    /// Refusing non-canonical bytes makes byte↔felt a BIJECTION on the admitted domain, so the
    /// replay set's keying and the proof's binding are the SAME keying. Reinterpreting instead of
    /// refusing is what created the alias.
    NullifierNotCanonical {
        /// The offending 32-byte nullifier.
        nullifier: [u8; 32],
    },
    /// The proof's destination_federation does not match the local federation identity.
    /// This indicates a cross-federation replay attempt.
    DestinationMismatch {
        /// The destination_federation in the proof.
        proof_destination: [u8; 32],
        /// The local federation's identity.
        local_federation: [u8; 32],
    },
    /// The note is already locked in a pending bridge (cannot double-lock).
    AlreadyLocked { nullifier: [u8; 32] },
    /// Attempted to cancel a bridge before the timeout height.
    TimeoutNotReached {
        current_height: u64,
        timeout_height: u64,
    },
    /// The bridge receipt's signature is invalid.
    InvalidReceipt { reason: String },
    /// The pending bridge was not found for the given nullifier.
    PendingBridgeNotFound { nullifier: [u8; 32] },
    /// The pending bridge is not in the expected state.
    InvalidBridgeState { nullifier: [u8; 32], reason: String },
}

impl core::fmt::Display for BridgeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            BridgeError::UntrustedRoot { root_hex } => {
                write!(f, "source root {root_hex}... is not in the trusted set")
            }
            BridgeError::MissingNoteTreeRoot => {
                write!(
                    f,
                    "source root does not contain a note_tree_root attestation"
                )
            }
            BridgeError::InvalidSpendingProof { reason } => {
                write!(f, "STARK spending proof verification failed: {reason}")
            }
            BridgeError::AlreadyBridged { nullifier } => {
                write!(
                    f,
                    "nullifier {:02x}{:02x}{:02x}{:02x}... already bridged",
                    nullifier[0], nullifier[1], nullifier[2], nullifier[3]
                )
            }
            BridgeError::NullifierMismatch => {
                write!(f, "nullifier does not match proof public inputs")
            }
            BridgeError::ValueMismatch { expected, got } => {
                write!(f, "value mismatch: expected {expected}, got {got}")
            }
            BridgeError::ValueNotFaithfullyBound { value, bound } => {
                write!(
                    f,
                    "bridge value {value} is at/above the faithfully-bound window {bound} \
                     (p·2^30): the note-spend claim tuple's two value limbs alias there"
                )
            }
            BridgeError::NullifierNotCanonical { nullifier } => {
                write!(
                    f,
                    "nullifier {:02x}{:02x}{:02x}{:02x}... is not the canonical encoding of a \
                     claim-tuple nullifier felt (bytes 0..4 little-endian < p, bytes 4..32 zero): \
                     a non-canonical string names a felt some other string also names, which is a \
                     fresh replay key against the same proof",
                    nullifier[0], nullifier[1], nullifier[2], nullifier[3]
                )
            }
            BridgeError::DestinationMismatch {
                proof_destination,
                local_federation,
            } => {
                write!(
                    f,
                    "destination federation mismatch: proof targets \
                     {:02x}{:02x}{:02x}{:02x}..., local federation is \
                     {:02x}{:02x}{:02x}{:02x}... (cross-federation replay rejected)",
                    proof_destination[0],
                    proof_destination[1],
                    proof_destination[2],
                    proof_destination[3],
                    local_federation[0],
                    local_federation[1],
                    local_federation[2],
                    local_federation[3]
                )
            }
            BridgeError::AlreadyLocked { nullifier } => {
                write!(
                    f,
                    "note {:02x}{:02x}{:02x}{:02x}... is already locked in a pending bridge",
                    nullifier[0], nullifier[1], nullifier[2], nullifier[3]
                )
            }
            BridgeError::TimeoutNotReached {
                current_height,
                timeout_height,
            } => {
                write!(
                    f,
                    "cannot cancel bridge: current height {current_height} < timeout {timeout_height}"
                )
            }
            BridgeError::InvalidReceipt { reason } => {
                write!(f, "invalid bridge receipt: {reason}")
            }
            BridgeError::PendingBridgeNotFound { nullifier } => {
                write!(
                    f,
                    "no pending bridge found for nullifier {:02x}{:02x}{:02x}{:02x}...",
                    nullifier[0], nullifier[1], nullifier[2], nullifier[3]
                )
            }
            BridgeError::InvalidBridgeState { nullifier, reason } => {
                write!(
                    f,
                    "bridge for nullifier {:02x}{:02x}{:02x}{:02x}... in invalid state: {reason}",
                    nullifier[0], nullifier[1], nullifier[2], nullifier[3]
                )
            }
        }
    }
}

impl std::error::Error for BridgeError {}

/// A set of nullifiers that have been bridged into this federation from others.
///
/// Prevents the same portable note proof from being accepted twice (double-bridge).
/// Separate from the local NullifierSet which tracks locally-spent notes.
#[derive(Clone, Debug, Default)]
pub struct BridgedNullifierSet {
    /// Sorted set of bridged nullifiers for O(log n) lookup.
    nullifiers: Vec<[u8; 32]>,
}

impl BridgedNullifierSet {
    /// Create an empty bridged nullifier set.
    pub fn new() -> Self {
        Self {
            nullifiers: Vec::new(),
        }
    }

    /// Check if a nullifier has already been bridged.
    pub fn contains(&self, nullifier: &[u8; 32]) -> bool {
        self.nullifiers.binary_search(nullifier).is_ok()
    }

    /// Insert a bridged nullifier. Returns error if already present.
    pub fn insert(&mut self, nullifier: [u8; 32]) -> Result<(), BridgeError> {
        match self.nullifiers.binary_search(&nullifier) {
            Ok(_) => Err(BridgeError::AlreadyBridged { nullifier }),
            Err(idx) => {
                self.nullifiers.insert(idx, nullifier);
                Ok(())
            }
        }
    }

    /// Iterate the bridged nullifiers in sorted order (the universal-memory
    /// projection walks the set).
    pub fn iter(&self) -> impl Iterator<Item = &[u8; 32]> {
        self.nullifiers.iter()
    }

    /// Number of bridged nullifiers.
    pub fn len(&self) -> usize {
        self.nullifiers.len()
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.nullifiers.is_empty()
    }

    /// Remove a nullifier from the set (used for rollback).
    /// Returns true if the nullifier was found and removed, false otherwise.
    pub fn remove(&mut self, nullifier: &[u8; 32]) -> bool {
        match self.nullifiers.binary_search(nullifier) {
            Ok(idx) => {
                self.nullifiers.remove(idx);
                true
            }
            Err(_) => false,
        }
    }
}

// ============================================================================
// Two-phase conditional locking bridge
// ============================================================================

/// The state of a pending bridge operation.
///
/// Instead of unconditionally burning a note, the two-phase bridge protocol
/// first LOCKS the note (conditionally committed to burn), then either
/// finalizes the burn upon receipt of a destination confirmation, or cancels
/// the lock after a timeout — returning value to the owner.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BridgeState {
    /// The note is locked: nullifier is committed-to but not yet revealed
    /// to the permanent nullifier set. Value is inaccessible until finalized or cancelled.
    Locked {
        timeout_height: u64,
        destination: [u8; 32],
    },
    /// The bridge completed: destination confirmed mint, nullifier is now permanent.
    Finalized,
    /// The bridge was cancelled (timeout expired without receipt). Note is unlocked.
    Cancelled,
}

/// A pending bridge record: tracks a note that is locked for cross-federation transfer.
///
/// Created during Phase 1 (lock) and resolved during Phase 3 (finalize) or
/// Phase 4 (timeout/cancel).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PendingBridge {
    /// The nullifier of the locked note (committed-to but not yet permanent).
    pub nullifier: [u8; 32],
    /// The destination federation this bridge targets.
    pub destination_federation: [u8; 32],
    /// The value being bridged.
    pub value: u64,
    /// The asset type being bridged.
    pub asset_type: u64,
    /// The block height at which this bridge times out (can be cancelled after).
    pub timeout_height: u64,
    /// The serialized portable proof bytes (for destination to claim).
    pub spending_proof: Vec<u8>,
    /// Current state of this bridge operation.
    pub state: BridgeState,
}

/// Serde helper for [u8; 64] since serde doesn't implement Serialize/Deserialize for arrays > 32.
mod sig_bytes {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(data: &[u8; 64], ser: S) -> Result<S::Ok, S::Error> {
        data.as_slice().serialize(ser)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(de: D) -> Result<[u8; 64], D::Error> {
        let v: Vec<u8> = Deserialize::deserialize(de)?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected 64 bytes for signature"))
    }
}

/// A signed receipt from a destination federation confirming that a bridge mint occurred.
///
/// Produced by the destination in Phase 2 after verifying and minting the bridged value.
/// Presented to the source in Phase 3 to finalize the burn.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BridgeReceipt {
    /// The nullifier that was bridged (matches PendingBridge.nullifier).
    pub nullifier: [u8; 32],
    /// The destination federation that minted the value.
    pub destination_federation: [u8; 32],
    /// The block height at which the mint occurred on the destination.
    pub mint_height: u64,
    /// Ed25519 signature from the destination federation over (nullifier || dest || mint_height).
    #[serde(with = "sig_bytes")]
    pub signature: [u8; 64],
}

impl BridgeReceipt {
    /// Compute the message that the destination federation signs.
    ///
    /// Uses domain-separated BLAKE3 to prevent cross-protocol signature confusion.
    /// The signed message is: BLAKE3_derive_key("dregg-bridge-receipt-v1", nullifier || destination_federation || mint_height_le_bytes).
    pub fn signing_message(
        nullifier: &[u8; 32],
        destination_federation: &[u8; 32],
        mint_height: u64,
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-bridge-receipt-v1");
        hasher.update(nullifier);
        hasher.update(destination_federation);
        hasher.update(&mint_height.to_le_bytes());
        *hasher.finalize().as_bytes()
    }
}

/// Tracks pending bridges by nullifier. Used by the source federation executor.
#[derive(Clone, Debug, Default)]
pub struct PendingBridgeSet {
    bridges: HashMap<[u8; 32], PendingBridge>,
}

impl PendingBridgeSet {
    /// Create an empty pending bridge set.
    pub fn new() -> Self {
        Self {
            bridges: HashMap::new(),
        }
    }

    /// Get a pending bridge by nullifier.
    pub fn get(&self, nullifier: &[u8; 32]) -> Option<&PendingBridge> {
        self.bridges.get(nullifier)
    }

    /// Get a mutable reference to a pending bridge by nullifier.
    pub fn get_mut(&mut self, nullifier: &[u8; 32]) -> Option<&mut PendingBridge> {
        self.bridges.get_mut(nullifier)
    }

    /// Check if a nullifier is already locked in a pending bridge.
    pub fn is_locked(&self, nullifier: &[u8; 32]) -> bool {
        self.bridges
            .get(nullifier)
            .is_some_and(|b| matches!(b.state, BridgeState::Locked { .. }))
    }

    /// Insert a new pending bridge. Returns error if the nullifier is already locked.
    pub fn insert(&mut self, bridge: PendingBridge) -> Result<(), BridgeError> {
        if self.is_locked(&bridge.nullifier) {
            return Err(BridgeError::AlreadyLocked {
                nullifier: bridge.nullifier,
            });
        }
        self.bridges.insert(bridge.nullifier, bridge);
        Ok(())
    }

    /// Number of pending bridges (all states).
    pub fn len(&self) -> usize {
        self.bridges.len()
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.bridges.is_empty()
    }

    /// Remove a bridge record (after finalization or cancellation cleanup).
    pub fn remove(&mut self, nullifier: &[u8; 32]) -> Option<PendingBridge> {
        self.bridges.remove(nullifier)
    }
}

// ============================================================================
// Stage 9 P3.D: Phased BridgeReceiptEnvelope (DESIGN-receipts.md §5)
// ============================================================================
//
// The single-shot `BridgeReceipt` above (the Phase 2 mint-ack) is preserved
// for backward compatibility. The types below give the full four-phase
// receipt protocol described in DESIGN-receipts.md §5: shared envelope
// (bridge_id, src/dst federation, sequence, previous-phase link) and
// per-phase payloads (Locked, Witnessed, Finalized, Refunded). A per-
// bridge `BridgePhaseLog` enforces monotone phase advancement and rejects
// replay attempts.
//
// The envelope is NOT a drop-in replacement for `BridgeReceipt` in
// `Effect::BridgeFinalize` (which would require touching the Effect enum —
// outside this lane's write surface). Instead, both coexist: the executor's
// finalize handler still consumes a `BridgeReceipt` (Phase-2 ack); the
// envelope is what federations exchange end-to-end and what
// `BridgePhaseLog` records.

/// The four phases of a cross-federation bridge.
///
/// `Locked` — source has locked the note (Phase 1).
/// `Witnessed` — destination has observed Phase 1 and minted; this is the
///   Phase-2 mint-ack receipt's phase tag. (The design doc calls this `Mint`.)
/// `Finalized` — source has consumed the witness and made the lock permanent.
/// `Refunded` — source has timed out without a witness and unlocked the note.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[repr(u8)]
pub enum BridgePhase {
    /// Phase 1: source locked the note.
    Locked = 1,
    /// Phase 2: destination witnessed the lock and minted.
    Witnessed = 2,
    /// Phase 3: source consumed the witness and finalized the burn.
    Finalized = 3,
    /// Phase 4: source timed out and refunded.
    Refunded = 4,
}

impl BridgePhase {
    /// The numeric tag baked into hashes (stable across schema migrations).
    pub fn tag(self) -> u8 {
        self as u8
    }

    /// The next phase that MAY legally follow `self`, or `None` if `self` is
    /// terminal. `Locked → {Witnessed, Refunded}`; `Witnessed → Finalized`;
    /// `Finalized` and `Refunded` are terminal.
    pub fn next_valid(self) -> &'static [BridgePhase] {
        match self {
            BridgePhase::Locked => &[BridgePhase::Witnessed, BridgePhase::Refunded],
            BridgePhase::Witnessed => &[BridgePhase::Finalized],
            BridgePhase::Finalized | BridgePhase::Refunded => &[],
        }
    }
}

/// Per-phase payload carried inside a [`BridgeReceiptEnvelope`].
///
/// Each variant carries only the fields meaningful to that phase. The shared
/// envelope fields (bridge_id, src/dst federation, sequence, etc.) live on
/// the envelope.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BridgePhasePayload {
    /// Phase 1 payload (source-side lock).
    Locked {
        /// Nullifier of the locked note.
        nullifier: [u8; 32],
        /// Asset type id (used for cross-fed asset registry).
        asset_type: u64,
        /// Value being bridged.
        value: u64,
        /// Source-side timeout after which Refund is allowed.
        timeout_height: u64,
        /// BLAKE3 of the portable spending proof bytes (binds the proof
        /// to this lock without inlining it).
        spending_proof_digest: [u8; 32],
    },
    /// Phase 2 payload (destination-side mint-ack).
    Witnessed {
        /// Mint height on the destination.
        mint_height: u64,
        /// Commitment to the minted note on the destination.
        mint_commitment: [u8; 32],
    },
    /// Phase 3 payload (source-side finalize).
    Finalized {
        /// Block height on the source when the finalize was applied.
        finalize_height: u64,
        /// Source's permanent-nullifier-set root after this finalize.
        post_nullifier_root: [u8; 32],
    },
    /// Phase 4 payload (source-side refund/timeout cancel).
    Refunded {
        /// Block height on the source when the refund was applied
        /// (must be `> timeout_height` of the corresponding Phase 1).
        refund_height: u64,
    },
}

impl BridgePhasePayload {
    /// The phase tag for this payload variant. Must match the envelope's
    /// `phase` field; the envelope-builders enforce this invariant.
    pub fn phase(&self) -> BridgePhase {
        match self {
            BridgePhasePayload::Locked { .. } => BridgePhase::Locked,
            BridgePhasePayload::Witnessed { .. } => BridgePhase::Witnessed,
            BridgePhasePayload::Finalized { .. } => BridgePhase::Finalized,
            BridgePhasePayload::Refunded { .. } => BridgePhase::Refunded,
        }
    }
}

/// Compute the deterministic `bridge_id` that identifies a bridge instance
/// across phases and federations.
///
/// `BLAKE3_derive_key("dregg-bridge-id-v1", lock_nullifier || src_fed ||
/// dst_fed || initiating_nonce_le)`. The Phase-1 lock nullifier (source-side)
/// ensures uniqueness — under the source's nullifier-uniqueness invariant
/// no two locks reuse the same nullifier — and `initiating_nonce` provides
/// per-source replay protection if the same (nullifier, src, dst) tuple
/// ever recurred (e.g. cross-version).
pub fn compute_bridge_id(
    lock_nullifier: &[u8; 32],
    src_fed: &[u8; 32],
    dst_fed: &[u8; 32],
    initiating_nonce: u64,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-bridge-id-v1");
    hasher.update(lock_nullifier);
    hasher.update(src_fed);
    hasher.update(dst_fed);
    hasher.update(&initiating_nonce.to_le_bytes());
    *hasher.finalize().as_bytes()
}

/// Phased bridge receipt envelope (Stage 9 / DESIGN-receipts.md §5).
///
/// Shared shape across all four phases. The `payload` discriminator's
/// phase tag must equal `phase`; constructors enforce this. The
/// `previous_phase_receipt_hash` chains phases together: Phase 1 has
/// `None`; Phase 2 binds Phase 1; Phase 3 binds Phase 2; Phase 4 binds
/// Phase 1. A [`BridgePhaseLog`] enforces this on entry.
///
/// The cross-federation QC (BLS or Ed25519 votes) lives on the next layer up
/// (`FederationReceipt` from `dregg-federation`). This envelope is the
/// *body* the QC commits to; serialize and pass through `body_hash` to
/// get the signing message.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BridgeReceiptEnvelope {
    /// Version tag: `1` corresponds to `dregg-bridge-envelope-v1`.
    pub version: u32,
    /// Which phase this receipt represents.
    pub phase: BridgePhase,
    /// Cross-phase join key (see [`compute_bridge_id`]).
    pub bridge_id: [u8; 32],
    /// Source federation id (always the federation that initiated).
    pub src_federation: [u8; 32],
    /// Destination federation id.
    pub dst_federation: [u8; 32],
    /// Block height on the issuing federation (source for L/F/R, dst for W).
    pub block_height: u64,
    /// Hash of the previous-phase envelope's `body_hash()`. `None` only
    /// for Phase 1 (the genesis lock).
    pub previous_phase_receipt_hash: Option<[u8; 32]>,
    /// Phase-specific payload.
    pub payload: BridgePhasePayload,
}

impl BridgeReceiptEnvelope {
    /// Current wire-format version.
    pub const VERSION: u32 = 1;

    /// Compute the canonical body hash — the message a federation's
    /// quorum certificate (BLS or Ed25519) signs over. Domain-separated
    /// via BLAKE3 derive_key; cannot collide with any other dregg hash.
    pub fn body_hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-bridge-envelope-v1");
        hasher.update(&self.version.to_le_bytes());
        hasher.update(&[self.phase.tag()]);
        hasher.update(&self.bridge_id);
        hasher.update(&self.src_federation);
        hasher.update(&self.dst_federation);
        hasher.update(&self.block_height.to_le_bytes());
        match self.previous_phase_receipt_hash {
            Some(h) => {
                hasher.update(&[1u8]);
                hasher.update(&h);
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        // Payload binding: each variant contributes a stable byte tag plus
        // its fields in declaration order.
        match &self.payload {
            BridgePhasePayload::Locked {
                nullifier,
                asset_type,
                value,
                timeout_height,
                spending_proof_digest,
            } => {
                hasher.update(&[0x01]);
                hasher.update(nullifier);
                hasher.update(&asset_type.to_le_bytes());
                hasher.update(&value.to_le_bytes());
                hasher.update(&timeout_height.to_le_bytes());
                hasher.update(spending_proof_digest);
            }
            BridgePhasePayload::Witnessed {
                mint_height,
                mint_commitment,
            } => {
                hasher.update(&[0x02]);
                hasher.update(&mint_height.to_le_bytes());
                hasher.update(mint_commitment);
            }
            BridgePhasePayload::Finalized {
                finalize_height,
                post_nullifier_root,
            } => {
                hasher.update(&[0x03]);
                hasher.update(&finalize_height.to_le_bytes());
                hasher.update(post_nullifier_root);
            }
            BridgePhasePayload::Refunded { refund_height } => {
                hasher.update(&[0x04]);
                hasher.update(&refund_height.to_le_bytes());
            }
        }
        *hasher.finalize().as_bytes()
    }

    /// Build a Phase-1 (Locked) envelope. `previous_phase_receipt_hash` is
    /// always `None` for Phase 1.
    pub fn new_locked(
        bridge_id: [u8; 32],
        src_federation: [u8; 32],
        dst_federation: [u8; 32],
        block_height: u64,
        nullifier: [u8; 32],
        asset_type: u64,
        value: u64,
        timeout_height: u64,
        spending_proof_digest: [u8; 32],
    ) -> Self {
        Self {
            version: Self::VERSION,
            phase: BridgePhase::Locked,
            bridge_id,
            src_federation,
            dst_federation,
            block_height,
            previous_phase_receipt_hash: None,
            payload: BridgePhasePayload::Locked {
                nullifier,
                asset_type,
                value,
                timeout_height,
                spending_proof_digest,
            },
        }
    }

    /// Build a Phase-2 (Witnessed) envelope. Must reference a Phase-1
    /// envelope's `body_hash` via `prior_lock_hash`.
    pub fn new_witnessed(
        bridge_id: [u8; 32],
        src_federation: [u8; 32],
        dst_federation: [u8; 32],
        block_height: u64,
        prior_lock_hash: [u8; 32],
        mint_height: u64,
        mint_commitment: [u8; 32],
    ) -> Self {
        Self {
            version: Self::VERSION,
            phase: BridgePhase::Witnessed,
            bridge_id,
            src_federation,
            dst_federation,
            block_height,
            previous_phase_receipt_hash: Some(prior_lock_hash),
            payload: BridgePhasePayload::Witnessed {
                mint_height,
                mint_commitment,
            },
        }
    }

    /// Build a Phase-3 (Finalized) envelope. References the Phase-2
    /// (Witnessed) envelope's body_hash.
    pub fn new_finalized(
        bridge_id: [u8; 32],
        src_federation: [u8; 32],
        dst_federation: [u8; 32],
        block_height: u64,
        prior_witness_hash: [u8; 32],
        finalize_height: u64,
        post_nullifier_root: [u8; 32],
    ) -> Self {
        Self {
            version: Self::VERSION,
            phase: BridgePhase::Finalized,
            bridge_id,
            src_federation,
            dst_federation,
            block_height,
            previous_phase_receipt_hash: Some(prior_witness_hash),
            payload: BridgePhasePayload::Finalized {
                finalize_height,
                post_nullifier_root,
            },
        }
    }

    /// Build a Phase-4 (Refunded) envelope. References the Phase-1
    /// (Locked) envelope's body_hash (NOT a Phase 2 — refund is the
    /// alternative branch).
    pub fn new_refunded(
        bridge_id: [u8; 32],
        src_federation: [u8; 32],
        dst_federation: [u8; 32],
        block_height: u64,
        prior_lock_hash: [u8; 32],
        refund_height: u64,
    ) -> Self {
        Self {
            version: Self::VERSION,
            phase: BridgePhase::Refunded,
            bridge_id,
            src_federation,
            dst_federation,
            block_height,
            previous_phase_receipt_hash: Some(prior_lock_hash),
            payload: BridgePhasePayload::Refunded { refund_height },
        }
    }
}

/// Errors specific to the phased bridge receipt protocol.
///
/// Distinct from `BridgeError` so callers can match on the structural
/// reasons (replay vs. non-monotone advancement vs. unknown bridge).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BridgePhaseError {
    /// A receipt for an unknown bridge_id was presented for a phase
    /// that requires a prior phase.
    UnknownBridge { bridge_id: [u8; 32] },
    /// Phase 1 was issued for a bridge_id that already has a Phase 1.
    DuplicateLock { bridge_id: [u8; 32] },
    /// The receipt's `phase` does not legally follow the bridge's last
    /// recorded phase (covers same-phase replay, out-of-order, and
    /// terminal-phase advancement).
    NonMonotoneAdvancement {
        bridge_id: [u8; 32],
        last_phase: BridgePhase,
        attempted_phase: BridgePhase,
    },
    /// The receipt's `previous_phase_receipt_hash` does not match the
    /// stored body_hash of the prior phase.
    PreviousPhaseHashMismatch {
        bridge_id: [u8; 32],
        expected: [u8; 32],
        actual: Option<[u8; 32]>,
    },
    /// The envelope's payload variant disagrees with its `phase` field.
    PayloadPhaseMismatch {
        envelope_phase: BridgePhase,
        payload_phase: BridgePhase,
    },
    /// The envelope's bridge_id does not match the expected value (e.g.
    /// Phase-2 envelope's bridge_id differs from Phase-1's).
    BridgeIdMismatch {
        expected: [u8; 32],
        actual: [u8; 32],
    },
    /// A later phase changed the source/destination federation pair that
    /// was established by the Phase-1 lock for this bridge_id.
    FederationPairMismatch {
        bridge_id: [u8; 32],
        expected_src: [u8; 32],
        expected_dst: [u8; 32],
        actual_src: [u8; 32],
        actual_dst: [u8; 32],
    },
}

impl core::fmt::Display for BridgePhaseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            BridgePhaseError::UnknownBridge { .. } => {
                write!(f, "no bridge_id recorded for this advancement")
            }
            BridgePhaseError::DuplicateLock { .. } => {
                write!(f, "bridge already has a Phase-1 lock recorded")
            }
            BridgePhaseError::NonMonotoneAdvancement {
                last_phase,
                attempted_phase,
                ..
            } => {
                write!(
                    f,
                    "non-monotone phase advancement: last={:?}, attempted={:?}",
                    last_phase, attempted_phase
                )
            }
            BridgePhaseError::PreviousPhaseHashMismatch { .. } => {
                write!(f, "previous_phase_receipt_hash mismatch")
            }
            BridgePhaseError::PayloadPhaseMismatch {
                envelope_phase,
                payload_phase,
            } => {
                write!(
                    f,
                    "envelope phase={:?} but payload is {:?}",
                    envelope_phase, payload_phase
                )
            }
            BridgePhaseError::BridgeIdMismatch { .. } => {
                write!(f, "bridge_id mismatch across phases")
            }
            BridgePhaseError::FederationPairMismatch { .. } => {
                write!(f, "federation pair mismatch across bridge phases")
            }
        }
    }
}

impl std::error::Error for BridgePhaseError {}

/// Per-bridge phase log enforcing monotone advancement and replay rejection.
///
/// Maps `bridge_id -> (last_phase, last_body_hash)`. On admission, an
/// envelope must:
///
/// 1. Carry a `payload.phase() == envelope.phase`.
/// 2. If `phase == Locked`, the bridge_id must not already be present.
/// 3. Otherwise, the bridge_id must be present, the new phase must be in
///    `last_phase.next_valid()`, and `previous_phase_receipt_hash` must
///    equal the stored `last_body_hash`.
///
/// This is the "race condition" defense (Phase 3 + Phase 4 cannot both
/// be recorded for the same bridge: once Refunded is logged, Finalized
/// fails monotone-check; once Finalized is logged, Refunded fails too).
#[derive(Clone, Debug, Default)]
pub struct BridgePhaseLog {
    entries: HashMap<[u8; 32], (BridgePhase, [u8; 32], [u8; 32], [u8; 32])>,
}

impl BridgePhaseLog {
    /// Create an empty phase log.
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of bridges tracked.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the log is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Look up the last recorded phase for a bridge.
    pub fn get(&self, bridge_id: &[u8; 32]) -> Option<(BridgePhase, [u8; 32])> {
        self.entries
            .get(bridge_id)
            .map(|(phase, body_hash, _, _)| (*phase, *body_hash))
    }

    /// Admit a phase envelope.
    ///
    /// On success, the log is updated to (envelope.phase, envelope.body_hash()).
    /// On failure, the log is unchanged.
    pub fn admit(&mut self, envelope: &BridgeReceiptEnvelope) -> Result<(), BridgePhaseError> {
        // 0. Envelope's payload phase tag must match its envelope phase.
        let payload_phase = envelope.payload.phase();
        if payload_phase != envelope.phase {
            return Err(BridgePhaseError::PayloadPhaseMismatch {
                envelope_phase: envelope.phase,
                payload_phase,
            });
        }

        let body_hash = envelope.body_hash();
        let bridge_id = envelope.bridge_id;

        match envelope.phase {
            BridgePhase::Locked => {
                // Phase 1 must be the first phase.
                if envelope.previous_phase_receipt_hash.is_some() {
                    return Err(BridgePhaseError::PreviousPhaseHashMismatch {
                        bridge_id,
                        expected: [0u8; 32],
                        actual: envelope.previous_phase_receipt_hash,
                    });
                }
                if self.entries.contains_key(&bridge_id) {
                    return Err(BridgePhaseError::DuplicateLock { bridge_id });
                }
                self.entries.insert(
                    bridge_id,
                    (
                        BridgePhase::Locked,
                        body_hash,
                        envelope.src_federation,
                        envelope.dst_federation,
                    ),
                );
                Ok(())
            }
            // Phases 2..4 require a prior entry and a monotone transition.
            phase => {
                let (last_phase, last_hash, src_federation, dst_federation) = self
                    .entries
                    .get(&bridge_id)
                    .copied()
                    .ok_or(BridgePhaseError::UnknownBridge { bridge_id })?;
                if envelope.src_federation != src_federation
                    || envelope.dst_federation != dst_federation
                {
                    return Err(BridgePhaseError::FederationPairMismatch {
                        bridge_id,
                        expected_src: src_federation,
                        expected_dst: dst_federation,
                        actual_src: envelope.src_federation,
                        actual_dst: envelope.dst_federation,
                    });
                }
                if !last_phase.next_valid().contains(&phase) {
                    return Err(BridgePhaseError::NonMonotoneAdvancement {
                        bridge_id,
                        last_phase,
                        attempted_phase: phase,
                    });
                }
                match envelope.previous_phase_receipt_hash {
                    Some(h) if h == last_hash => {}
                    other => {
                        return Err(BridgePhaseError::PreviousPhaseHashMismatch {
                            bridge_id,
                            expected: last_hash,
                            actual: other,
                        });
                    }
                }
                self.entries.insert(
                    bridge_id,
                    (phase, body_hash, src_federation, dst_federation),
                );
                Ok(())
            }
        }
    }
}

/// Initiate a bridge: lock the note for cross-federation transfer.
///
/// This is Phase 1 of the two-phase bridge protocol. The note is locked
/// (not yet burned) and a PendingBridge record is created. The note cannot
/// be spent or re-locked until the bridge is finalized or cancelled.
///
/// # Arguments
///
/// * `nullifier` - The nullifier of the note to lock.
/// * `destination_federation` - The target federation's identity.
/// * `value` - The value being bridged.
/// * `asset_type` - The asset type being bridged.
/// * `timeout_height` - Block height at which the lock expires.
/// * `spending_proof` - The serialized portable proof for destination claiming.
/// * `pending_set` - The set of pending bridges to register in.
pub fn initiate_bridge(
    nullifier: [u8; 32],
    destination_federation: [u8; 32],
    value: u64,
    asset_type: u64,
    timeout_height: u64,
    spending_proof: Vec<u8>,
    pending_set: &mut PendingBridgeSet,
) -> Result<PendingBridge, BridgeError> {
    let bridge = PendingBridge {
        nullifier,
        destination_federation,
        value,
        asset_type,
        timeout_height,
        spending_proof,
        state: BridgeState::Locked {
            timeout_height,
            destination: destination_federation,
        },
    };
    pending_set.insert(bridge.clone())?;
    Ok(bridge)
}

/// Finalize a bridge: confirm the burn after receiving a valid receipt from destination.
///
/// This is Phase 3 of the two-phase bridge protocol. The source verifies the
/// destination federation's receipt signature, then makes the nullifier permanent.
///
/// # Arguments
///
/// * `nullifier` - The nullifier of the pending bridge to finalize.
/// * `receipt` - The signed receipt from the destination federation.
/// * `destination_keys` - Map of destination federation id → its authorized
///   Ed25519 public key. The receipt must be signed by the key registered for
///   its OWN `destination_federation`; a trusted federation cannot sign a
///   receipt naming a destination it does not hold the key for.
/// * `pending_set` - The set of pending bridges.
/// * `permanent_nullifiers` - The permanent nullifier set to add the nullifier to.
pub fn finalize_bridge(
    nullifier: &[u8; 32],
    receipt: &BridgeReceipt,
    destination_keys: &HashMap<[u8; 32], [u8; 32]>,
    pending_set: &mut PendingBridgeSet,
    permanent_nullifiers: &mut BridgedNullifierSet,
) -> Result<(), BridgeError> {
    // Look up the pending bridge.
    let bridge = pending_set
        .get(nullifier)
        .ok_or(BridgeError::PendingBridgeNotFound {
            nullifier: *nullifier,
        })?;

    // Verify it's in Locked state.
    if !matches!(bridge.state, BridgeState::Locked { .. }) {
        return Err(BridgeError::InvalidBridgeState {
            nullifier: *nullifier,
            reason: "bridge is not in Locked state".to_string(),
        });
    }

    // Verify the receipt's nullifier matches.
    if receipt.nullifier != *nullifier {
        return Err(BridgeError::InvalidReceipt {
            reason: "receipt nullifier does not match pending bridge".to_string(),
        });
    }

    // Verify the receipt's destination matches the bridge's destination.
    if receipt.destination_federation != bridge.destination_federation {
        return Err(BridgeError::InvalidReceipt {
            reason: "receipt destination does not match bridge destination".to_string(),
        });
    }

    // Verify the receipt signature against the key registered for the receipt's
    // OWN destination federation (not merely "any trusted key").
    if !verify_bridge_receipt(receipt, destination_keys) {
        return Err(BridgeError::InvalidReceipt {
            reason: "receipt signature verification failed".to_string(),
        });
    }

    // Finalize: mark the bridge as finalized and add nullifier to permanent set.
    let bridge_mut = pending_set.get_mut(nullifier).unwrap();
    bridge_mut.state = BridgeState::Finalized;

    // The nullifier is now permanently spent.
    permanent_nullifiers.insert(*nullifier)?;

    Ok(())
}

/// Cancel a bridge: unlock the note after the timeout has expired.
///
/// This is Phase 4 of the two-phase bridge protocol. If the bridge was not
/// finalized before the timeout, the note is unlocked and returned to the owner.
///
/// # Arguments
///
/// * `nullifier` - The nullifier of the pending bridge to cancel.
/// * `current_height` - The current block height.
/// * `pending_set` - The set of pending bridges.
pub fn cancel_bridge(
    nullifier: &[u8; 32],
    current_height: u64,
    pending_set: &mut PendingBridgeSet,
) -> Result<(), BridgeError> {
    let bridge = pending_set
        .get(nullifier)
        .ok_or(BridgeError::PendingBridgeNotFound {
            nullifier: *nullifier,
        })?;

    // Verify it's in Locked state.
    let timeout_height = match bridge.state {
        BridgeState::Locked { timeout_height, .. } => timeout_height,
        _ => {
            return Err(BridgeError::InvalidBridgeState {
                nullifier: *nullifier,
                reason: "bridge is not in Locked state".to_string(),
            });
        }
    };

    // Verify the timeout has been reached.
    if current_height <= timeout_height {
        return Err(BridgeError::TimeoutNotReached {
            current_height,
            timeout_height,
        });
    }

    // Cancel: mark the bridge as cancelled (note is now unlocked).
    let bridge_mut = pending_set.get_mut(nullifier).unwrap();
    bridge_mut.state = BridgeState::Cancelled;

    Ok(())
}

/// Verify a bridge receipt's Ed25519 signature against the key registered for
/// the receipt's OWN destination federation.
///
/// `destination_keys` maps each destination federation id to its authorized
/// Ed25519 public key. The receipt is accepted ONLY if its signature verifies
/// under the key mapped to `receipt.destination_federation`.
///
/// Binding the signer to the destination is load-bearing: a trusted federation
/// A must not be able to sign a receipt naming a DIFFERENT destination B (whose
/// key it does not hold). Verifying against "any trusted key" would let A forge
/// B's mint-ack and drive `finalize_bridge` to burn the owner's note with no
/// B-side mint.
pub fn verify_bridge_receipt(
    receipt: &BridgeReceipt,
    destination_keys: &HashMap<[u8; 32], [u8; 32]>,
) -> bool {
    use ed25519_dalek::{Signature, VerifyingKey};

    // The only key that may sign this receipt is the one registered for the
    // receipt's own declared destination federation.
    let Some(key_bytes) = destination_keys.get(&receipt.destination_federation) else {
        return false;
    };

    let message = BridgeReceipt::signing_message(
        &receipt.nullifier,
        &receipt.destination_federation,
        receipt.mint_height,
    );

    let signature = Signature::from_bytes(&receipt.signature);

    VerifyingKey::from_bytes(key_bytes)
        .map(|vk| vk.verify_strict(&message, &signature).is_ok())
        .unwrap_or(false)
}

/// Verify a portable note proof from another federation.
///
/// This is the core verification that a destination federation performs before
/// minting a new note. It checks:
/// 1. The destination_federation in the proof matches our local federation identity.
/// 2. The source_root is in our trusted set (we accept proofs from that federation).
/// 3. The source_root has a note_tree_root (the source federation attests note trees).
/// 4. The STARK spending proof verifies against the source_root's note_tree_root,
///    with the destination_federation included in the public inputs (binding the
///    proof cryptographically to this specific target).
/// 5. The nullifier is consistent with the proof's public inputs.
/// 6. The value and asset_type claimed in the proof match commitments embedded in
///    the STARK proof's public inputs (prevents value inflation attacks).
///
/// On success, the caller should:
/// - Add the nullifier to the bridged-nullifier set (prevent double-bridge).
/// - Create a new note commitment in the local note tree.
///
/// # Arguments
///
/// * `proof` - The portable note proof to verify.
/// * `local_federation_id` - This federation's identity (genesis root or configured ID).
/// * `trusted_roots` - The set of attested roots we accept from other federations.
/// * `verify_stark` - A closure that verifies the STARK proof given
///   (nullifier_bytes, merkle_root_bytes, destination_federation_bytes, value, asset_type, proof_bytes).
///   The destination_federation, value, and asset_type are included in the public inputs
///   so the proof is cryptographically bound to one target and specific value/asset.
///   Returns Ok(()) if valid.
pub fn verify_portable_note<F>(
    proof: &PortableNoteProof,
    local_federation_id: &[u8; 32],
    trusted_roots: &[AttestedRoot],
    verify_stark: F,
) -> Result<(), BridgeError>
where
    F: FnOnce(&[u8; 32], &[u8; 32], &[u8; 32], u64, u64, &[u8]) -> Result<(), String>,
{
    // 1. Check destination_federation matches local identity.
    // This prevents cross-federation replay: a proof addressed to Federation A
    // cannot be accepted by Federation B.
    if proof.destination_federation != *local_federation_id {
        return Err(BridgeError::DestinationMismatch {
            proof_destination: proof.destination_federation,
            local_federation: *local_federation_id,
        });
    }

    // 2. Check source_root is in our trusted set.
    let is_trusted = trusted_roots.iter().any(|r| {
        r.merkle_root == proof.source_root.merkle_root
            && r.height == proof.source_root.height
            && r.note_tree_root == proof.source_root.note_tree_root
    });
    if !is_trusted {
        let root_hex = proof
            .source_root
            .merkle_root
            .iter()
            .take(4)
            .map(|b| format!("{b:02x}"))
            .collect::<String>();
        return Err(BridgeError::UntrustedRoot { root_hex });
    }

    // 3. Check the source root has a note_tree_root.
    let note_tree_root = proof
        .source_root
        .note_tree_root
        .ok_or(BridgeError::MissingNoteTreeRoot)?;

    // 3b. REFUSE A VALUE THE CLAIM TUPLE CANNOT BIND.
    //
    // The STARK below pins `value` through exactly two felts — `lo = value & (2^30 − 1)` and
    // `hi = BabyBear::new((value >> 30) as u32)`. `value >> 30` reaches 2^34, so the `as u32`
    // TRUNCATES bits 62..64: `value` and `value + 2^62` produce a byte-identical claim tuple, an
    // identical `bridge_mint_hash_felt`, and therefore the SAME proof verifies for both. Nothing
    // downstream re-checks the magnitude — `turn/src/executor/finalize.rs`'s per-asset
    // conservation ledger and `proof_verify.rs`'s `net` both add `proof.value` at FULL u64 width.
    // So a single legitimately-proved note could be presented as itself plus 2^62 units, in one
    // submission, at zero cost, and the receipt would carry the inflated figure as attested.
    //
    // The refusal is total inside the admitted domain: below `p · 2^30` the pair is injective, and
    // the deployed AIR's own balance range (`BAL_LIMB_BITS = 30`, two limbs → `[0, 2^60)`) is
    // strictly inside it, so nothing representable elsewhere in the system is turned away. It is
    // checked BEFORE `verify_stark` so no encoder ever runs on an unbindable value.
    if !dregg_circuit::dsl::note_spending::note_spend_value_is_faithfully_bound(proof.value) {
        return Err(BridgeError::ValueNotFaithfullyBound {
            value: proof.value,
            bound: dregg_circuit::dsl::note_spending::NOTE_SPEND_VALUE_BOUND,
        });
    }

    // 3c. REFUSE A NULLIFIER THE CLAIM TUPLE CANNOT NAME UNIQUELY — the duplicate-mint gate.
    //
    // TWO KEYINGS OF ONE THING, AT TWO FIDELITIES. The STARK pins the nullifier through exactly
    // ONE felt (`pi[0]`, welded by the emitted `note-spend-leaf` descriptor to the in-AIR two-step
    // `hash_fact` derivation). The anti-replay set — `BridgedNullifierSet`, a sorted `Vec<[u8;32]>`
    // binary-searched on RAW BYTES — keys the 32-byte string. The executor turned bytes into the
    // claim felt with `hash_many(bytes32_to_8_limbs(·))`, which reduces each 4-byte little-endian
    // chunk mod `p`. Since `r + p < 2p < 2^32` for EVERY residue, every chunk had ≥ 2 preimages
    // (3 when `r < 2^32 − 2p`), and the canonical encoding's 28 zero bytes are seven such chunks:
    // `3^7 · 2 = 4374` distinct byte strings shared one claim felt (`3^8 = 6561` when the felt
    // lane is itself below `2^32 − 2p`). Adding `p` to a chunk is one
    // addition, and it produced a value that was IDENTICAL to the proof and DIFFERENT to the
    // replay set — exactly backwards from what anti-replay needs. `finalize.rs`'s per-asset
    // conservation ledger then counted each admitted mint again at full u64 width.
    //
    // The refusal restores ONE keying: on the canonical domain, byte→felt (here) and felt→byte
    // (`dregg_cell::felt_to_bytes32`, what `Note::nullifier` actually emits) are mutual inverses,
    // so distinct admitted byte strings ⟺ distinct claim felts. Nothing is made lossy to reach
    // agreement — the replay set still keys the full 32 bytes.
    //
    // ⚠ It does NOT widen the nullifier: the claim tuple binds ~30.9 bits and still does, so two
    // DIFFERENT notes colliding on `hash_many` stays a `2^15.5` birthday / `2^31` second-preimage
    // grind. That is the separate nullifier-WIDTH wound, and it needs a PI widening in the
    // Lean-authored `note-spend-leaf::dregg-note-spending-dsl-v3` descriptor.
    //
    // Checked BEFORE `verify_stark` so no felt derivation ever runs on bytes that cannot name one.
    if !dregg_circuit::dsl::note_spending::note_spend_nullifier_is_canonical(&proof.nullifier) {
        return Err(BridgeError::NullifierNotCanonical {
            nullifier: proof.nullifier,
        });
    }

    // 4. Verify the STARK spending proof with destination_federation, value, and
    //    asset_type in public inputs. The verifier MUST check that the proof's
    //    public inputs commit to these exact values. This prevents:
    //    - Cross-federation replay (destination binding)
    //    - Value inflation (value binding)
    //    - Asset type confusion (asset_type binding)
    //
    // NOTE: The note_spending AIR embeds value and asset_type as public inputs
    // pi[2] and pi[3] respectively, with boundary constraints pinning them to
    // trace row 0 col::VALUE and col::ASSET_TYPE. The destination_federation is
    // pinned via pi[4] → col::DESTINATION_FEDERATION (boundary constraint). The
    // verify_stark closure receives the proof's declared values and the AIR
    // boundary constraints enforce they match what the prover committed to in
    // the trace; a mismatch fails the STARK verification. This is enforced in
    // note_spending_witness.rs::boundary_constraints().
    verify_stark(
        &proof.nullifier,
        &note_tree_root,
        &proof.destination_federation,
        proof.value,
        proof.asset_type,
        &proof.spending_proof,
    )
    .map_err(|reason| BridgeError::InvalidSpendingProof { reason })?;

    // 5. Verification passed. The nullifier corresponds to a valid note in the
    //    source federation's note tree at the attested root, the proof is
    //    cryptographically bound to this federation, and the value/asset_type
    //    are consistent with the STARK proof's public inputs.
    Ok(())
}

/// Create a portable note proof for cross-federation transfer.
///
/// This is called by the note owner in the source federation after spending
/// their note there. It packages the spending proof along with the federation's
/// attested root into a portable format that can be presented elsewhere.
///
/// # Arguments
///
/// * `nullifier` - The nullifier revealed when spending in the source federation.
/// * `spending_proof` - The serialized STARK proof from `prove_note_spend`.
///   MUST include `destination_federation` in its public inputs (the proof circuit
///   binds the spend to a specific target federation).
/// * `source_root` - The source federation's attested root at time of spend.
/// * `destination_federation` - The target federation's identity. This is included
///   in the STARK proof's public inputs to cryptographically bind the proof to one
///   target, preventing cross-federation replay.
/// * `destination_commitment` - The new note commitment for the destination federation.
/// * `value` - The value being transferred.
/// * `asset_type` - The asset type being transferred.
pub fn create_portable_note(
    nullifier: Nullifier,
    spending_proof: Vec<u8>,
    source_root: AttestedRoot,
    destination_federation: [u8; 32],
    destination_commitment: NoteCommitment,
    value: u64,
    asset_type: u64,
) -> PortableNoteProof {
    PortableNoteProof {
        nullifier: nullifier.0,
        destination_federation,
        source_root,
        spending_proof,
        destination_commitment,
        value,
        asset_type,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The test federation identity.
    const TEST_FEDERATION_ID: [u8; 32] = [0xFE; 32];

    fn make_attested_root(height: u64, note_root: Option<[u8; 32]>) -> AttestedRoot {
        AttestedRoot {
            merkle_root: [height as u8; 32],
            note_tree_root: note_root,
            nullifier_set_root: None,
            height,
            timestamp: 1000 + height as i64,
            blocklace_block_id: None,
            finality_round: None,
            quorum_signatures: vec![],
            threshold_qc: None,
            threshold: 0,
            federation_id: dregg_types::FederationId::PLACEHOLDER,
            receipt_stream_root: None,
            hybrid_quorum: Vec::new(),
        }
    }

    /// A **canonical** bridge nullifier: the `dregg_cell::felt_to_bytes32` encoding of a
    /// claim-tuple nullifier felt (four little-endian bytes, then twenty-eight zeros).
    ///
    /// This is the ONLY shape `dregg_cell::Note::nullifier` ever produces and, since the
    /// duplicate-mint close, the only shape `verify_portable_note` admits. The fixtures below
    /// used `[k; 32]`, which is a byte string no note can produce and which the old
    /// `hash_many(bytes32_to_8_limbs(·))` derivation shared with thousands of siblings.
    fn canonical_nullifier(felt: u32) -> [u8; 32] {
        dregg_cell::felt_to_bytes32(dregg_circuit::field::BabyBear::new(felt))
    }

    fn make_proof(nullifier: [u8; 32], value: u64, asset_type: u64) -> PortableNoteProof {
        let source_root = make_attested_root(42, Some([0xAA; 32]));
        PortableNoteProof {
            nullifier,
            destination_federation: TEST_FEDERATION_ID,
            source_root,
            spending_proof: vec![1, 2, 3, 4], // dummy proof bytes
            destination_commitment: NoteCommitment([0xBB; 32]),
            value,
            asset_type,
        }
    }

    /// A dummy verifier that always succeeds.
    fn verify_ok(
        _nullifier: &[u8; 32],
        _root: &[u8; 32],
        _dest_fed: &[u8; 32],
        _value: u64,
        _asset_type: u64,
        _proof: &[u8],
    ) -> Result<(), String> {
        Ok(())
    }

    /// A dummy verifier that always fails.
    fn verify_fail(
        _nullifier: &[u8; 32],
        _root: &[u8; 32],
        _dest_fed: &[u8; 32],
        _value: u64,
        _asset_type: u64,
        _proof: &[u8],
    ) -> Result<(), String> {
        Err("mock verification failure".to_string())
    }

    #[test]
    fn test_verify_portable_note_success() {
        let trusted = vec![make_attested_root(42, Some([0xAA; 32]))];
        let proof = make_proof(canonical_nullifier(1), 100, 1);
        let result = verify_portable_note(&proof, &TEST_FEDERATION_ID, &trusted, verify_ok);
        assert!(result.is_ok());
    }

    #[test]
    fn test_verify_portable_note_untrusted_root() {
        // Trusted set has height 99, but proof has height 42.
        let trusted = vec![make_attested_root(99, Some([0xCC; 32]))];
        let proof = make_proof(canonical_nullifier(1), 100, 1);
        let result = verify_portable_note(&proof, &TEST_FEDERATION_ID, &trusted, verify_ok);
        assert!(matches!(result, Err(BridgeError::UntrustedRoot { .. })));
    }

    #[test]
    fn test_verify_portable_note_missing_note_tree_root() {
        // Trusted root has no note_tree_root.
        let trusted = vec![make_attested_root(42, None)];
        let mut proof = make_proof(canonical_nullifier(1), 100, 1);
        proof.source_root.note_tree_root = None;
        let result = verify_portable_note(&proof, &TEST_FEDERATION_ID, &trusted, verify_ok);
        assert!(matches!(result, Err(BridgeError::MissingNoteTreeRoot)));
    }

    #[test]
    fn test_verify_portable_note_invalid_proof() {
        let trusted = vec![make_attested_root(42, Some([0xAA; 32]))];
        let proof = make_proof(canonical_nullifier(1), 100, 1);
        let result = verify_portable_note(&proof, &TEST_FEDERATION_ID, &trusted, verify_fail);
        assert!(matches!(
            result,
            Err(BridgeError::InvalidSpendingProof { .. })
        ));
    }

    #[test]
    fn test_verify_portable_note_destination_mismatch() {
        let trusted = vec![make_attested_root(42, Some([0xAA; 32]))];
        let proof = make_proof(canonical_nullifier(1), 100, 1);
        // Try to verify against a DIFFERENT federation identity.
        let wrong_federation = [0xAB; 32];
        let result = verify_portable_note(&proof, &wrong_federation, &trusted, verify_ok);
        assert!(matches!(
            result,
            Err(BridgeError::DestinationMismatch { .. })
        ));
    }

    #[test]
    fn test_bridged_nullifier_set_insert_and_contains() {
        let mut set = BridgedNullifierSet::new();
        let n = [42u8; 32];

        assert!(!set.contains(&n));
        set.insert(n).unwrap();
        assert!(set.contains(&n));
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_bridged_nullifier_set_double_bridge_rejected() {
        let mut set = BridgedNullifierSet::new();
        let n = [42u8; 32];

        set.insert(n).unwrap();
        let result = set.insert(n);
        assert!(matches!(result, Err(BridgeError::AlreadyBridged { .. })));
    }

    #[test]
    fn test_bridged_nullifier_set_multiple() {
        let mut set = BridgedNullifierSet::new();
        for i in 0..10u8 {
            let mut n = [0u8; 32];
            n[0] = i;
            set.insert(n).unwrap();
        }
        assert_eq!(set.len(), 10);

        for i in 0..10u8 {
            let mut n = [0u8; 32];
            n[0] = i;
            assert!(set.contains(&n));
        }
    }

    #[test]
    fn test_create_portable_note() {
        let nullifier = Nullifier([0x11; 32]);
        let source_root = make_attested_root(10, Some([0xAA; 32]));
        let dest_commitment = NoteCommitment([0xBB; 32]);

        let portable = create_portable_note(
            nullifier,
            vec![5, 6, 7, 8],
            source_root.clone(),
            TEST_FEDERATION_ID,
            dest_commitment,
            500,
            2,
        );

        assert_eq!(portable.nullifier, [0x11; 32]);
        assert_eq!(portable.destination_federation, TEST_FEDERATION_ID);
        assert_eq!(portable.value, 500);
        assert_eq!(portable.asset_type, 2);
        assert_eq!(portable.destination_commitment, dest_commitment);
        assert_eq!(portable.source_root.height, 10);
    }

    #[test]
    fn test_verify_then_bridge_flow() {
        // Simulate the full flow: verify then track in bridged set.
        let trusted = vec![make_attested_root(42, Some([0xAA; 32]))];
        let proof = make_proof(canonical_nullifier(0x99), 100, 1);
        let mut bridged_set = BridgedNullifierSet::new();

        // First bridge succeeds.
        verify_portable_note(&proof, &TEST_FEDERATION_ID, &trusted, verify_ok).unwrap();
        bridged_set.insert(proof.nullifier).unwrap();

        // Second bridge with same nullifier fails.
        let result = bridged_set.insert(proof.nullifier);
        assert!(matches!(result, Err(BridgeError::AlreadyBridged { .. })));
    }

    // ========================================================================
    // Adversarial tests: prove note bridge security properties
    // ========================================================================

    /// Adversarial test: Cross-federation double-spend (the bug this fix addresses).
    ///
    /// A proof addressed to Federation A cannot be accepted by Federation B.
    /// This is the core security property that prevents inflation via replay.
    #[test]
    fn adversarial_cross_federation_replay() {
        let trusted = vec![make_attested_root(42, Some([0xAA; 32]))];
        let proof = make_proof(canonical_nullifier(0xD0), 500, 1);

        // Verification succeeds at the intended destination.
        let result_a = verify_portable_note(&proof, &TEST_FEDERATION_ID, &trusted, verify_ok);
        assert!(
            result_a.is_ok(),
            "proof should pass at intended destination"
        );

        // Verification FAILS at a different federation (cross-federation replay).
        let federation_b = [0xBB; 32];
        let result_b = verify_portable_note(&proof, &federation_b, &trusted, verify_ok);
        assert!(
            matches!(result_b, Err(BridgeError::DestinationMismatch { .. })),
            "cross-federation replay must be rejected: got {:?}",
            result_b
        );
    }

    /// Adversarial test 8: Double-bridge attack.
    ///
    /// Bridge the same note (same nullifier) to the same federation twice.
    /// The second attempt MUST fail via BridgedNullifierSet.
    #[test]
    fn adversarial_double_bridge() {
        let trusted = vec![make_attested_root(42, Some([0xAA; 32]))];
        let nullifier = canonical_nullifier(0xD0);
        let proof = make_proof(nullifier, 500, 1);
        let mut bridged_set = BridgedNullifierSet::new();

        // First bridge: verify + insert.
        verify_portable_note(&proof, &TEST_FEDERATION_ID, &trusted, verify_ok).unwrap();
        bridged_set.insert(proof.nullifier).unwrap();

        // Attacker attempts to bridge the SAME note again.
        verify_portable_note(&proof, &TEST_FEDERATION_ID, &trusted, verify_ok).unwrap();
        let result = bridged_set.insert(proof.nullifier);
        assert!(
            matches!(result, Err(BridgeError::AlreadyBridged { nullifier: n }) if n == nullifier),
            "double-bridge must be rejected by BridgedNullifierSet"
        );
    }

    // ========================================================================
    // THE DUPLICATE-BRIDGE-MINT CLOSE — two keyings of one thing, at two fidelities
    // ========================================================================
    //
    // Four teeth. The first is the ALIAS POLE and MUST KEEP PASSING: it asserts that the map the
    // executor USED TO derive the claim felt with still collides, and that the replay set still
    // treats the colliding strings as distinct. That conjunction IS the wound; if either half
    // ever stops holding, the refusal below has gone vacuous and this test is the alarm.

    /// The 4-byte little-endian chunk decomposition the old derivation reduced mod `p`.
    fn chunks(b: &[u8; 32]) -> [u32; 8] {
        core::array::from_fn(|i| {
            u32::from_le_bytes([b[i * 4], b[i * 4 + 1], b[i * 4 + 2], b[i * 4 + 3]])
        })
    }

    /// The derivation `apply_bridge_mint`'s `verify_stark` closure USED to perform: Poseidon2 over
    /// the eight mod-`p`-reduced chunks. Transcribed here from its two named parts rather than
    /// called through the executor, so the tooth cannot go silent when that call site is edited.
    fn old_compress(b: &[u8; 32]) -> dregg_circuit::field::BabyBear {
        dregg_circuit::poseidon2::hash_many(&dregg_circuit::effect_vm::bytes32_to_8_limbs(b))
    }

    /// Every byte string the OLD derivation could not distinguish from `b`: each chunk `v`
    /// independently replaced by `v + k·p` for every `k` that stays inside `u32`. `b` itself is
    /// element 0.
    fn old_derivation_siblings(b: &[u8; 32]) -> Vec<[u8; 32]> {
        let p = dregg_circuit::field::BABYBEAR_P as u64;
        let mut out = vec![*b];
        for (i, v) in chunks(b).iter().enumerate() {
            let mut grown = Vec::new();
            for prefix in &out {
                for k in 1u64..4 {
                    let bumped = *v as u64 + k * p;
                    if bumped >= 1u64 << 32 {
                        break;
                    }
                    let mut sib = *prefix;
                    sib[i * 4..i * 4 + 4].copy_from_slice(&(bumped as u32).to_le_bytes());
                    grown.push(sib);
                }
            }
            out.extend(grown);
        }
        out
    }

    /// **ALIAS POLE — THE EXHIBIT.** One legitimate nullifier, thousands of byte strings the proof
    /// cannot tell apart, every one of them a FRESH key in the raw-byte-keyed replay set.
    ///
    /// This is the whole shape in one assertion block: acceptance was a function of a LOSSY
    /// projection of the nullifier, the anti-replay key was the RAW BYTES, and that is exactly
    /// backwards — a value that is the same to the proof must not be a different key to the set.
    #[test]
    fn the_old_derivation_aliases_while_the_replay_set_keys_raw_bytes() {
        let honest = canonical_nullifier(0xD0);
        let siblings = old_derivation_siblings(&honest);

        // The canonical encoding's twenty-eight zero bytes are seven chunks whose residue is 0,
        // and `0 + 2p < 2^32`, so each contributes THREE preimages. Lane 0 carries the felt.
        assert_eq!(
            siblings.len(),
            3usize.pow(7) * 3,
            "a canonical nullifier with a small felt has 3^8 = 6561 byte-siblings under the old \
             derivation (7 zero chunks × 3 preimages each, × 3 for the felt lane)"
        );
        assert!(
            (siblings.len() as f64).log2() > 12.0,
            "that is ~2^12.7 free re-mints per note, at O(1) — no grind"
        );

        // (1) THE PROOF CANNOT TELL THEM APART. Every sibling compresses to the same claim felt,
        //     so the SAME note-spend proof verified against every one of them.
        let honest_felt = old_compress(&honest);
        for sib in &siblings {
            assert_eq!(
                old_compress(sib),
                honest_felt,
                "the old derivation maps this sibling to the honest claim felt — the same proof \
                 verifies"
            );
        }

        // (2) THE REPLAY SET TELLS THEM APART. `BridgedNullifierSet` binary-searches raw bytes, so
        //     every sibling is a fresh key: N-1 free re-mints of ONE legitimately-proved note.
        let mut set = BridgedNullifierSet::new();
        for sib in &siblings {
            assert!(
                set.insert(*sib).is_ok(),
                "every byte-sibling is a FRESH key to the replay set — this is the duplicate mint"
            );
        }
        assert_eq!(
            set.len(),
            siblings.len(),
            "the anti-replay set holds one entry per sibling, all of them the same note"
        );

        // (3) …and the cheapest one is ONE ADDITION away: `p` added to chunk 0.
        let mut by_one_addition = honest;
        let bumped = chunks(&honest)[0] as u64 + dregg_circuit::field::BABYBEAR_P as u64;
        by_one_addition[0..4].copy_from_slice(&(bumped as u32).to_le_bytes());
        assert_ne!(by_one_addition, honest, "a different 32-byte string");
        assert_eq!(
            old_compress(&by_one_addition),
            honest_felt,
            "…and an identical claim felt"
        );
    }

    /// **CLOSED POLE, BY VARIANT.** The honest nullifier still verifies and is still consumed
    /// exactly once; the replay of the SAME bytes is refused as `AlreadyBridged`; every aliased
    /// sibling is refused as `NullifierNotCanonical` — and refused BEFORE the STARK closure runs,
    /// which the tooth asserts by watching whether the closure was reached at all.
    ///
    /// Never `is_err()`: `verify_ok` here always succeeds, so a bare error check would be
    /// satisfied by any incidental failure.
    #[test]
    fn an_aliased_bridge_nullifier_is_refused_by_variant() {
        use std::cell::Cell;

        let trusted = vec![make_attested_root(42, Some([0xAA; 32]))];
        let honest = canonical_nullifier(0xD0);
        let proof = make_proof(honest, 500, 1);
        let mut set = BridgedNullifierSet::new();

        let reached = Cell::new(0u32);
        let watched = |_n: &[u8; 32],
                       _r: &[u8; 32],
                       _d: &[u8; 32],
                       _v: u64,
                       _a: u64,
                       _p: &[u8]|
         -> Result<(), String> {
            reached.set(reached.get() + 1);
            Ok(())
        };

        // POLE 1 — the honest mint still verifies, reaches the STARK, and credits ONCE.
        verify_portable_note(&proof, &TEST_FEDERATION_ID, &trusted, &watched)
            .expect("an honest bridge mint must still be admitted");
        assert_eq!(
            reached.get(),
            1,
            "the honest mint reached the STARK verifier"
        );
        set.insert(proof.nullifier)
            .expect("the first mint consumes the nullifier");
        assert_eq!(proof.value, 500, "the admitted value round-trips unchanged");

        // POLE 2 — the SAME bytes again: the replay set itself rejects the second insertion.
        verify_portable_note(&proof, &TEST_FEDERATION_ID, &trusted, &watched)
            .expect("verification is stateless; the replay set is the authority");
        match set.insert(proof.nullifier) {
            Err(BridgeError::AlreadyBridged { nullifier: n }) => {
                assert_eq!(
                    n, honest,
                    "the refusal names the nullifier already consumed"
                )
            }
            other => panic!("a byte-identical replay must be AlreadyBridged, got {other:?}"),
        }

        // POLE 3 — every aliased sibling: refused BY VARIANT, before the STARK closure runs.
        let before = reached.get();
        let siblings = old_derivation_siblings(&honest);
        for sib in siblings.iter().skip(1) {
            let mut aliased = proof.clone();
            aliased.nullifier = *sib;
            match verify_portable_note(&aliased, &TEST_FEDERATION_ID, &trusted, &watched) {
                Err(BridgeError::NullifierNotCanonical { nullifier: n }) => {
                    assert_eq!(n, *sib, "the refusal names the offending byte string")
                }
                other => panic!(
                    "aliased nullifier {sib:02x?} must be refused as NullifierNotCanonical, got \
                     {other:?} — note that `watched` always succeeds, so a pass here IS the \
                     duplicate mint"
                ),
            }
            assert!(
                set.insert(*sib).is_ok(),
                "sanity: the replay set alone would still have taken it — the refusal upstream is \
                 what closes the hole, not the set"
            );
        }
        assert_eq!(
            reached.get(),
            before,
            "not one aliased sibling reached the STARK closure — the gate is upstream of every \
             felt derivation, so no encoder ever ran on bytes that cannot name one felt"
        );
    }

    /// **ANTI-VACUITY / ROUND-TRIP.** On the admitted domain the byte↔felt correspondence is a
    /// BIJECTION: `note_spend_nullifier_felt` is the exact inverse of `dregg_cell::felt_to_bytes32`
    /// — which is what `dregg_cell::Note::nullifier` actually emits, so nothing a real note
    /// produces is turned away. That is what makes the refusal a faithfulness gate and not a cap.
    #[test]
    fn the_bridge_nullifier_codec_is_the_felt_to_bytes32_inverse() {
        use dregg_circuit::dsl::note_spending::{
            note_spend_nullifier_felt, note_spend_nullifier_is_canonical,
        };
        use dregg_circuit::field::{BABYBEAR_P, BabyBear};

        // Round-trip across the whole field, including both ends.
        let mut samples: Vec<u32> = vec![0, 1, 2, 0xD0, 1 << 16, 1 << 28, BABYBEAR_P - 1];
        for k in 1..31 {
            samples.push(1u32 << k);
        }
        for f in samples {
            let felt = BabyBear::new(f);
            let bytes = dregg_cell::felt_to_bytes32(felt);
            assert!(
                note_spend_nullifier_is_canonical(&bytes),
                "felt_to_bytes32({f}) must land in the admitted domain"
            );
            assert_eq!(
                note_spend_nullifier_felt(&bytes),
                Some(felt),
                "the decode must recover the felt exactly — a bijection, not a hash"
            );
        }

        // A REAL note's nullifier is admitted, and decodes to the felt the AIR pins at pi[0].
        let note = dregg_cell::note::Note::with_randomness(
            [7u8; 32],
            [3u64, 250, 0, 0, 0, 0, 0, 0],
            [42u8; 32],
        );
        let real = note.nullifier(&[9u8; 32]);
        assert!(
            note_spend_nullifier_is_canonical(&real.0),
            "Note::nullifier builds felt_to_bytes32(hash_many(…)) — the honest producer must be \
             inside the admitted domain, or this gate would refuse every legitimate mint"
        );
        assert!(note_spend_nullifier_felt(&real.0).is_some());

        // NON-canonical in both independent ways, refused in both.
        let mut high_bytes = dregg_cell::felt_to_bytes32(BabyBear::new(0xD0));
        high_bytes[31] = 1;
        assert!(
            !note_spend_nullifier_is_canonical(&high_bytes),
            "a non-zero byte above the felt window is not canonical"
        );
        let mut over_p = [0u8; 32];
        over_p[0..4].copy_from_slice(&BABYBEAR_P.to_le_bytes());
        assert!(
            !note_spend_nullifier_is_canonical(&over_p),
            "`p` itself is not a canonical felt encoding — it is the alias of 0"
        );
        assert_eq!(note_spend_nullifier_felt(&over_p), None);
        let mut p_minus_1 = [0u8; 32];
        p_minus_1[0..4].copy_from_slice(&(BABYBEAR_P - 1).to_le_bytes());
        assert!(
            note_spend_nullifier_is_canonical(&p_minus_1),
            "`p − 1` is the largest admitted felt — a gate that also refused it would be a cap"
        );
    }

    /// **THE WIDTH RESIDUAL, SAID OUT LOUD.** The close above makes byte↔felt a bijection; it does
    /// NOT widen what the claim tuple binds. The nullifier is still ONE BabyBear, so two DIFFERENT
    /// notes can still be driven onto one claim felt — a `2^15.5` birthday pair, `2^31` against a
    /// chosen target. This tooth measures that ceiling rather than letting a later reader assume
    /// the bijection bought width it did not buy.
    #[test]
    fn the_admitted_domain_is_exactly_p_and_that_is_the_residual() {
        use dregg_circuit::field::BABYBEAR_P;
        let admitted = BABYBEAR_P as f64;
        assert!(
            (admitted.log2() - 30.907).abs() < 0.01,
            "the admitted nullifier domain is p ≈ 2^30.907 — the claim tuple's whole nullifier \
             binding. Closing the byte alias did not widen it; that needs a PI widening in the \
             Lean-authored note-spend-leaf descriptor."
        );
        // The birthday ceiling on DISTINCT notes colliding, stated so it cannot be mistaken for
        // the duplicate-mint bound the close above drives to zero.
        assert!(
            (admitted.sqrt().log2() - 15.45).abs() < 0.05,
            "distinct-note nullifier collision stays a ~2^15.5 birthday grind"
        );
    }

    // ---- THE 2^62 VALUE-TRUNCATION CLOSE ----
    //
    // Four teeth. The first is the ALIAS pole and MUST KEEP PASSING: it asserts the encoder still
    // collides, because that is the premise the refusal is about. If it ever fails, the refusal
    // below has gone vacuous and this test is the alarm.

    /// ALIAS POLE. The two value limbs the note-spend claim tuple carries are IDENTICAL for `v`
    /// and `v + 2^62`, and so is `bridge_mint_hash_felt` — the whole binding of the value to the
    /// proof. Computed here against an INDEPENDENT transcription of the limb split, not by calling
    /// the executor's copy, so the tooth does not go silent if that copy is edited.
    #[test]
    fn the_value_limbs_and_mint_hash_alias_at_2_62() {
        use dregg_circuit::field::BabyBear;
        let v: u64 = 500;
        let v_inflated: u64 = 500 + (1u64 << 62);

        let limbs = |x: u64| {
            (
                BabyBear::new((x & ((1u64 << 30) - 1)) as u32),
                BabyBear::new((x >> 30) as u32),
            )
        };
        assert_eq!(
            limbs(v),
            limbs(v_inflated),
            "`(v >> 30) as u32` truncates bit 62 — both limbs are identical"
        );

        // …and therefore the mint identity is identical, so the SAME proof binds both values.
        // `bridge_mint_hash_felt` debug-asserts the window, so exercise the alias through the
        // limb-level twin rather than through the guarded entry point.
        assert_eq!(
            dregg_circuit::dsl::note_spending::note_spend_mint_hash_felt(
                BabyBear::new(1),
                BabyBear::new(2),
                limbs(v).0,
                BabyBear::new(3),
                BabyBear::new(4),
                limbs(v).1,
            ),
            dregg_circuit::dsl::note_spending::note_spend_mint_hash_felt(
                BabyBear::new(1),
                BabyBear::new(2),
                limbs(v_inflated).0,
                BabyBear::new(3),
                BabyBear::new(4),
                limbs(v_inflated).1,
            ),
            "the mint identity cannot distinguish v from v + 2^62"
        );
    }

    /// CLOSED POLE, BY VARIANT. The inflated sibling is now refused at the boundary — and refused
    /// with the SPECIFIC variant, carrying the value and the bound, not merely `is_err()`. Asserted
    /// against three inflated values, including the one an attacker actually wants.
    #[test]
    fn an_unbindable_bridge_value_is_refused_by_variant() {
        let trusted = vec![make_attested_root(42, Some([0xAA; 32]))];
        let bound = dregg_circuit::dsl::note_spending::NOTE_SPEND_VALUE_BOUND;

        for v in [bound, bound + 1, 500 + (1u64 << 62), u64::MAX] {
            let proof = make_proof(canonical_nullifier(0xD1), v, 1);
            let result = verify_portable_note(&proof, &TEST_FEDERATION_ID, &trusted, verify_ok);
            match result {
                Err(BridgeError::ValueNotFaithfullyBound {
                    value,
                    bound: reported,
                }) => {
                    assert_eq!(value, v, "the refusal names the offending value");
                    assert_eq!(reported, bound, "the refusal names the exact window");
                }
                other => panic!(
                    "value {v} must be refused as ValueNotFaithfullyBound, got {other:?} — note \
                     that `verify_ok` always succeeds, so a pass here is the inflation itself"
                ),
            }
        }
    }

    /// THE STATED LIMIT, both sides. `bound - 1` is the largest faithfully-bound value and MUST be
    /// admitted; `bound` is the smallest unbindable one and must not be. A refusal that also turned
    /// away legitimate amounts would be a regression, not a fix.
    #[test]
    fn the_faithful_window_is_exactly_p_times_2_30() {
        let trusted = vec![make_attested_root(42, Some([0xAA; 32]))];
        let bound = dregg_circuit::dsl::note_spending::NOTE_SPEND_VALUE_BOUND;
        assert_eq!(
            bound,
            (dregg_circuit::field::BABYBEAR_P as u64) << 30,
            "the bound is p·2^30, transcribed independently"
        );

        // The deployed AIR's own balance range (BAL_LIMB_BITS = 30, two limbs) is [0, 2^60) —
        // strictly inside the window, so nothing representable elsewhere is turned away.
        assert!(
            (1u64 << 60) < bound,
            "the AIR's 2^60 balance range must fit inside the admitted domain"
        );

        for ok in [0u64, 1, 500, (1u64 << 60), bound - 1] {
            let proof = make_proof(canonical_nullifier(0xD2), ok, 1);
            assert!(
                verify_portable_note(&proof, &TEST_FEDERATION_ID, &trusted, verify_ok).is_ok(),
                "value {ok} is inside the faithful window and must be ADMITTED"
            );
        }

        let proof = make_proof(canonical_nullifier(0xD2), bound, 1);
        assert!(
            matches!(
                verify_portable_note(&proof, &TEST_FEDERATION_ID, &trusted, verify_ok),
                Err(BridgeError::ValueNotFaithfullyBound { .. })
            ),
            "the bound itself is the first refused value"
        );
    }

    /// ANTI-VACUITY / ROUND-TRIP. Inside the admitted domain the two limbs RECOVER the value
    /// exactly — that is what makes the refusal a faithfulness gate rather than a magnitude cap.
    /// Swept over the boundary values and the powers of two spanning the window.
    #[test]
    fn inside_the_window_the_value_limbs_round_trip() {
        let bound = dregg_circuit::dsl::note_spending::NOTE_SPEND_VALUE_BOUND;
        let mut samples = vec![0u64, 1, 500, (1u64 << 30) - 1, 1u64 << 30, bound - 1];
        for k in 31..61 {
            samples.push(1u64 << k);
            samples.push((1u64 << k) + 1);
        }
        for v in samples {
            assert!(
                dregg_circuit::dsl::note_spending::note_spend_value_is_faithfully_bound(v),
                "sample {v} must be inside the window"
            );
            let lo = (v & ((1u64 << 30) - 1)) as u32;
            let hi = (v >> 30) as u32;
            // Nothing reduces: both limbs are canonical BabyBear elements below p…
            assert!(
                (hi as u64) < dregg_circuit::field::BABYBEAR_P as u64,
                "the high limb of {v} must not reduce mod p"
            );
            // …so the pair RECOMPOSES to the original u64 exactly.
            assert_eq!(
                (lo as u64) | ((hi as u64) << 30),
                v,
                "the two limbs must recover {v} exactly"
            );
        }
    }

    /// Adversarial test 9: Untrusted root.
    #[test]
    fn adversarial_untrusted_root() {
        let trusted = vec![make_attested_root(99, Some([0xCC; 32]))];
        let proof = make_proof(canonical_nullifier(0xAA), 100, 1);
        assert_ne!(proof.source_root.merkle_root, trusted[0].merkle_root);

        let result = verify_portable_note(&proof, &TEST_FEDERATION_ID, &trusted, verify_ok);
        assert!(
            matches!(result, Err(BridgeError::UntrustedRoot { .. })),
            "untrusted root must be rejected: got {:?}",
            result
        );
    }

    /// Adversarial test 10: Tampered STARK proof.
    #[test]
    fn adversarial_tampered_stark_proof() {
        let trusted = vec![make_attested_root(42, Some([0xAA; 32]))];
        let mut proof = make_proof(canonical_nullifier(0xBB), 100, 1);

        proof.spending_proof[0] ^= 0xFF;

        let verify_checks_integrity = |_nullifier: &[u8; 32],
                                       _root: &[u8; 32],
                                       _dest_fed: &[u8; 32],
                                       _value: u64,
                                       _asset_type: u64,
                                       proof_bytes: &[u8]|
         -> Result<(), String> {
            if proof_bytes == [1, 2, 3, 4] {
                Ok(())
            } else {
                Err("STARK proof verification failed: commitment mismatch".to_string())
            }
        };

        let result = verify_portable_note(
            &proof,
            &TEST_FEDERATION_ID,
            &trusted,
            verify_checks_integrity,
        );
        assert!(
            matches!(result, Err(BridgeError::InvalidSpendingProof { ref reason }) if reason.contains("commitment mismatch")),
            "tampered proof must be rejected by verifier: got {:?}",
            result
        );
    }

    /// Adversarial test 11: Value mismatch — verifier now receives value/asset_type
    /// as explicit parameters and can reject inflated claims.
    #[test]
    fn adversarial_value_mismatch_rejected() {
        let trusted = vec![make_attested_root(42, Some([0xAA; 32]))];
        let mut proof = make_proof(canonical_nullifier(0xCC), 100, 1);
        // Attacker inflates the claimed value.
        proof.value = 1000;

        // A verifier that checks value against the proof's embedded public inputs.
        // The STARK proof was generated with value=100, but the PortableNoteProof claims 1000.
        let verify_with_value_check = |_nullifier: &[u8; 32],
                                       _root: &[u8; 32],
                                       _dest_fed: &[u8; 32],
                                       value: u64,
                                       _asset_type: u64,
                                       _proof_bytes: &[u8]|
         -> Result<(), String> {
            // The STARK proof internally commits to value=100.
            let proof_committed_value: u64 = 100;
            if value != proof_committed_value {
                Err(format!(
                    "public input mismatch: proof binds value={}, claimed {}",
                    proof_committed_value, value
                ))
            } else {
                Ok(())
            }
        };

        let result = verify_portable_note(
            &proof,
            &TEST_FEDERATION_ID,
            &trusted,
            verify_with_value_check,
        );
        assert!(
            matches!(result, Err(BridgeError::InvalidSpendingProof { ref reason }) if reason.contains("value=100")),
            "value-aware verifier must catch inflation: got {:?}",
            result
        );
    }

    /// Adversarial test: Asset type mismatch — verifier rejects wrong asset_type.
    #[test]
    fn adversarial_asset_type_mismatch_rejected() {
        let trusted = vec![make_attested_root(42, Some([0xAA; 32]))];
        let mut proof = make_proof(canonical_nullifier(0xCD), 100, 1);
        // Attacker changes asset_type to a more valuable asset.
        proof.asset_type = 99;

        let verify_with_asset_check = |_nullifier: &[u8; 32],
                                       _root: &[u8; 32],
                                       _dest_fed: &[u8; 32],
                                       _value: u64,
                                       asset_type: u64,
                                       _proof_bytes: &[u8]|
         -> Result<(), String> {
            let proof_committed_asset: u64 = 1;
            if asset_type != proof_committed_asset {
                Err(format!(
                    "public input mismatch: proof binds asset_type={}, claimed {}",
                    proof_committed_asset, asset_type
                ))
            } else {
                Ok(())
            }
        };

        let result = verify_portable_note(
            &proof,
            &TEST_FEDERATION_ID,
            &trusted,
            verify_with_asset_check,
        );
        assert!(
            matches!(result, Err(BridgeError::InvalidSpendingProof { ref reason }) if reason.contains("asset_type=1")),
            "asset-type-aware verifier must catch confusion: got {:?}",
            result
        );
    }

    /// Adversarial test 12: Nullifier from a different note.
    #[test]
    fn adversarial_nullifier_from_different_note() {
        let trusted = vec![make_attested_root(42, Some([0xAA; 32]))];
        let nullifier_a = canonical_nullifier(0xA0);
        let nullifier_b = canonical_nullifier(0xB0);
        let proof = make_proof(nullifier_a, 100, 1);

        let verify_nullifier_binding = |nullifier: &[u8; 32],
                                        _root: &[u8; 32],
                                        _dest_fed: &[u8; 32],
                                        _value: u64,
                                        _asset_type: u64,
                                        _proof_bytes: &[u8]|
         -> Result<(), String> {
            let expected_nullifier = nullifier_b;
            if nullifier != &expected_nullifier {
                Err(format!(
                    "nullifier binding failed: proof is for {:02x}{:02x}..., presented {:02x}{:02x}...",
                    expected_nullifier[0], expected_nullifier[1], nullifier[0], nullifier[1]
                ))
            } else {
                Ok(())
            }
        };

        let result = verify_portable_note(
            &proof,
            &TEST_FEDERATION_ID,
            &trusted,
            verify_nullifier_binding,
        );
        assert!(
            matches!(result, Err(BridgeError::InvalidSpendingProof { ref reason }) if reason.contains("nullifier binding failed")),
            "mismatched nullifier must be rejected: got {:?}",
            result
        );
    }

    /// Adversarial test 13: Expired source root.
    #[test]
    fn adversarial_expired_source_root() {
        let old_root = AttestedRoot {
            merkle_root: [0xDD; 32],
            note_tree_root: Some([0xEE; 32]),
            nullifier_set_root: None,
            height: 1,
            timestamp: 1000,
            blocklace_block_id: None,
            finality_round: None,
            quorum_signatures: vec![],
            threshold_qc: None,
            threshold: 0,
            federation_id: dregg_types::FederationId::PLACEHOLDER,
            receipt_stream_root: None,
            hybrid_quorum: Vec::new(),
        };

        let proof = PortableNoteProof {
            nullifier: canonical_nullifier(0xFF),
            destination_federation: TEST_FEDERATION_ID,
            source_root: old_root.clone(),
            spending_proof: vec![1, 2, 3, 4],
            destination_commitment: NoteCommitment([0x11; 32]),
            value: 100,
            asset_type: 1,
        };

        let trusted_with_old = vec![old_root.clone()];
        let result_with =
            verify_portable_note(&proof, &TEST_FEDERATION_ID, &trusted_with_old, verify_ok);
        assert!(
            result_with.is_ok(),
            "stale root still in trusted set is accepted (by design)"
        );

        let trusted_without_old: Vec<AttestedRoot> = vec![];
        let result_without =
            verify_portable_note(&proof, &TEST_FEDERATION_ID, &trusted_without_old, verify_ok);
        assert!(
            matches!(result_without, Err(BridgeError::UntrustedRoot { .. })),
            "pruned stale root must be rejected: got {:?}",
            result_without
        );
    }

    // ========================================================================
    // Two-phase conditional locking bridge tests
    // ========================================================================

    /// Helper: generate an Ed25519 keypair for testing receipt signatures.
    fn test_keypair() -> (ed25519_dalek::SigningKey, ed25519_dalek::VerifyingKey) {
        use ed25519_dalek::SigningKey;
        let sk = SigningKey::from_bytes(&[0x42u8; 32]);
        let vk = sk.verifying_key();
        (sk, vk)
    }

    /// Helper: sign a bridge receipt with a test key.
    fn sign_receipt(
        nullifier: &[u8; 32],
        destination: &[u8; 32],
        mint_height: u64,
        signing_key: &ed25519_dalek::SigningKey,
    ) -> [u8; 64] {
        use ed25519_dalek::Signer;
        let message = BridgeReceipt::signing_message(nullifier, destination, mint_height);
        let sig = signing_key.sign(&message);
        sig.to_bytes()
    }

    /// Helper: a destination→key trust map registering `vk` for `destination`.
    fn dest_keys(
        destination: [u8; 32],
        vk: &ed25519_dalek::VerifyingKey,
    ) -> HashMap<[u8; 32], [u8; 32]> {
        HashMap::from([(destination, vk.to_bytes())])
    }

    #[test]
    fn test_two_phase_happy_path() {
        // Full lifecycle: lock -> claim (destination side, not tested here) -> finalize
        let (sk, vk) = test_keypair();
        let destination = [0xDD; 32];
        let nullifier = [0xAA; 32];
        let mut pending_set = PendingBridgeSet::new();
        let mut permanent_nullifiers = BridgedNullifierSet::new();
        let trusted_keys = dest_keys(destination, &vk);

        // Phase 1: Lock
        let bridge = initiate_bridge(
            nullifier,
            destination,
            1000,
            1,
            100, // timeout at height 100
            vec![1, 2, 3, 4],
            &mut pending_set,
        )
        .unwrap();

        assert!(matches!(bridge.state, BridgeState::Locked { .. }));
        assert_eq!(pending_set.len(), 1);
        assert!(pending_set.is_locked(&nullifier));

        // Phase 3: Finalize with valid receipt
        let sig = sign_receipt(&nullifier, &destination, 50, &sk);
        let receipt = BridgeReceipt {
            nullifier,
            destination_federation: destination,
            mint_height: 50,
            signature: sig,
        };

        finalize_bridge(
            &nullifier,
            &receipt,
            &trusted_keys,
            &mut pending_set,
            &mut permanent_nullifiers,
        )
        .unwrap();

        // Verify the bridge is finalized.
        let finalized = pending_set.get(&nullifier).unwrap();
        assert_eq!(finalized.state, BridgeState::Finalized);
        // Nullifier is now permanently spent.
        assert!(permanent_nullifiers.contains(&nullifier));
    }

    #[test]
    fn test_verify_bridge_receipt_rejects_cross_federation_forgery() {
        // FALSIFIER for the cross-federation signer hole: a trusted federation A
        // must NOT be able to sign a receipt naming a DIFFERENT destination B.
        // Under the old "any trusted key" logic this returned true — A's sig over
        // (nullifier, B, height) verified because A was in the trusted set — so A
        // could forge B's mint-ack. With signer→destination binding, the receipt
        // is checked ONLY against B's registered key, so A's forgery is rejected.
        let key_a = ed25519_dalek::SigningKey::from_bytes(&[0xA1u8; 32]);
        let key_b = ed25519_dalek::SigningKey::from_bytes(&[0xB2u8; 32]);
        let fed_a = [0xAA; 32];
        let fed_b = [0xBB; 32];
        let nullifier = [0x77; 32];

        // Both federations are trusted, each registered to its OWN key.
        let mut destination_keys = HashMap::new();
        destination_keys.insert(fed_a, key_a.verifying_key().to_bytes());
        destination_keys.insert(fed_b, key_b.verifying_key().to_bytes());

        // A forges a receipt naming destination B, signing with A's own key.
        let forged_sig = sign_receipt(&nullifier, &fed_b, 50, &key_a);
        let forged_receipt = BridgeReceipt {
            nullifier,
            destination_federation: fed_b,
            mint_height: 50,
            signature: forged_sig,
        };
        assert!(
            !verify_bridge_receipt(&forged_receipt, &destination_keys),
            "federation A must not be able to sign a receipt for destination B"
        );

        // B's own signature over the same receipt is accepted.
        let honest_sig = sign_receipt(&nullifier, &fed_b, 50, &key_b);
        let honest_receipt = BridgeReceipt {
            nullifier,
            destination_federation: fed_b,
            mint_height: 50,
            signature: honest_sig,
        };
        assert!(
            verify_bridge_receipt(&honest_receipt, &destination_keys),
            "the receipt signed by B's registered key must verify"
        );
    }

    #[test]
    fn test_finalize_bridge_rejects_forged_destination_signer() {
        // FALSIFIER (end to end): a note is locked toward destination B. Trusted
        // federation A forges B's receipt. finalize_bridge must reject it and
        // leave the note locked — NOT burn the owner's note with no B-side mint.
        let key_a = ed25519_dalek::SigningKey::from_bytes(&[0xA1u8; 32]);
        let key_b = ed25519_dalek::SigningKey::from_bytes(&[0xB2u8; 32]);
        let fed_a = [0xAA; 32];
        let fed_b = [0xBB; 32];
        let nullifier = [0x88; 32];

        let mut pending_set = PendingBridgeSet::new();
        let mut permanent_nullifiers = BridgedNullifierSet::new();
        let mut destination_keys = HashMap::new();
        destination_keys.insert(fed_a, key_a.verifying_key().to_bytes());
        destination_keys.insert(fed_b, key_b.verifying_key().to_bytes());

        // Lock a note toward destination B.
        initiate_bridge(
            nullifier,
            fed_b,
            1000,
            1,
            100,
            vec![1, 2, 3, 4],
            &mut pending_set,
        )
        .unwrap();

        // A forges B's mint-ack (A's key over (nullifier, B, height)).
        let forged_sig = sign_receipt(&nullifier, &fed_b, 50, &key_a);
        let forged_receipt = BridgeReceipt {
            nullifier,
            destination_federation: fed_b,
            mint_height: 50,
            signature: forged_sig,
        };

        let result = finalize_bridge(
            &nullifier,
            &forged_receipt,
            &destination_keys,
            &mut pending_set,
            &mut permanent_nullifiers,
        );
        assert!(
            matches!(result, Err(BridgeError::InvalidReceipt { .. })),
            "a receipt forged by a non-destination federation must be rejected: got {:?}",
            result
        );
        // The owner's note stays locked; the nullifier is NOT permanently spent.
        assert!(pending_set.is_locked(&nullifier));
        assert!(!permanent_nullifiers.contains(&nullifier));
    }

    #[test]
    fn test_two_phase_timeout_cancel() {
        // Lifecycle: lock -> timeout reached -> cancel (value returned)
        let destination = [0xDD; 32];
        let nullifier = [0xBB; 32];
        let mut pending_set = PendingBridgeSet::new();

        // Phase 1: Lock with timeout at height 50
        initiate_bridge(
            nullifier,
            destination,
            500,
            2,
            50,
            vec![5, 6, 7],
            &mut pending_set,
        )
        .unwrap();

        assert!(pending_set.is_locked(&nullifier));

        // Phase 4: Cancel after timeout
        let result = cancel_bridge(&nullifier, 51, &mut pending_set);
        assert!(result.is_ok());

        let cancelled = pending_set.get(&nullifier).unwrap();
        assert_eq!(cancelled.state, BridgeState::Cancelled);
        // The note is now unlocked (not in permanent set).
    }

    #[test]
    fn test_two_phase_double_lock_prevented() {
        // Cannot lock the same note twice.
        let destination = [0xDD; 32];
        let nullifier = [0xCC; 32];
        let mut pending_set = PendingBridgeSet::new();

        // First lock succeeds.
        initiate_bridge(
            nullifier,
            destination,
            100,
            1,
            100,
            vec![1, 2, 3],
            &mut pending_set,
        )
        .unwrap();

        // Second lock on the same nullifier fails.
        let result = initiate_bridge(
            nullifier,
            destination,
            200,
            1,
            200,
            vec![4, 5, 6],
            &mut pending_set,
        );
        assert!(
            matches!(result, Err(BridgeError::AlreadyLocked { nullifier: n }) if n == nullifier),
            "double-lock must be prevented: got {:?}",
            result
        );
    }

    #[test]
    fn test_two_phase_early_cancel_prevented() {
        // Cannot cancel before the timeout height.
        let destination = [0xDD; 32];
        let nullifier = [0xEE; 32];
        let mut pending_set = PendingBridgeSet::new();

        initiate_bridge(
            nullifier,
            destination,
            100,
            1,
            100, // timeout at 100
            vec![1, 2],
            &mut pending_set,
        )
        .unwrap();

        // Try to cancel at height 50 (before timeout of 100).
        let result = cancel_bridge(&nullifier, 50, &mut pending_set);
        assert!(
            matches!(
                result,
                Err(BridgeError::TimeoutNotReached {
                    current_height: 50,
                    timeout_height: 100
                })
            ),
            "early cancel must be prevented: got {:?}",
            result
        );

        // Try exactly at timeout height (must also fail — need to be PAST timeout).
        let result = cancel_bridge(&nullifier, 100, &mut pending_set);
        assert!(
            matches!(result, Err(BridgeError::TimeoutNotReached { .. })),
            "cancel at exactly timeout must fail: got {:?}",
            result
        );

        // At height 101, cancel succeeds.
        let result = cancel_bridge(&nullifier, 101, &mut pending_set);
        assert!(result.is_ok());
    }

    #[test]
    fn test_two_phase_receipt_forgery_rejected() {
        // Invalid receipt signature must be rejected.
        let (sk, vk) = test_keypair();
        let destination = [0xDD; 32];
        let nullifier = [0xFF; 32];
        let mut pending_set = PendingBridgeSet::new();
        let mut permanent_nullifiers = BridgedNullifierSet::new();
        let trusted_keys = dest_keys(destination, &vk);

        initiate_bridge(
            nullifier,
            destination,
            1000,
            1,
            100,
            vec![1, 2, 3, 4],
            &mut pending_set,
        )
        .unwrap();

        // Create a receipt with a WRONG signature (signed over different data).
        let wrong_sig = sign_receipt(&nullifier, &destination, 999, &sk); // wrong mint_height
        let forged_receipt = BridgeReceipt {
            nullifier,
            destination_federation: destination,
            mint_height: 50, // claims height 50 but sig was over height 999
            signature: wrong_sig,
        };

        let result = finalize_bridge(
            &nullifier,
            &forged_receipt,
            &trusted_keys,
            &mut pending_set,
            &mut permanent_nullifiers,
        );
        assert!(
            matches!(result, Err(BridgeError::InvalidReceipt { .. })),
            "forged receipt must be rejected: got {:?}",
            result
        );

        // Also test with completely unknown key.
        let valid_sig = sign_receipt(&nullifier, &destination, 50, &sk);
        let receipt = BridgeReceipt {
            nullifier,
            destination_federation: destination,
            mint_height: 50,
            signature: valid_sig,
        };

        // Use an empty trust map — no federation is registered.
        let result = finalize_bridge(
            &nullifier,
            &receipt,
            &HashMap::new(), // no registered destination keys
            &mut pending_set,
            &mut permanent_nullifiers,
        );
        assert!(
            matches!(result, Err(BridgeError::InvalidReceipt { .. })),
            "receipt from untrusted key must be rejected: got {:?}",
            result
        );

        // Verify the bridge is still locked (not finalized).
        assert!(pending_set.is_locked(&nullifier));
        assert!(!permanent_nullifiers.contains(&nullifier));
    }

    #[test]
    fn test_two_phase_finalize_nonexistent_bridge() {
        // Finalizing a bridge that doesn't exist must fail.
        let (sk, vk) = test_keypair();
        let destination = [0xDD; 32];
        let nullifier = [0x11; 32];
        let mut pending_set = PendingBridgeSet::new();
        let mut permanent_nullifiers = BridgedNullifierSet::new();
        let trusted_keys = dest_keys(destination, &vk);

        let sig = sign_receipt(&nullifier, &destination, 50, &sk);
        let receipt = BridgeReceipt {
            nullifier,
            destination_federation: destination,
            mint_height: 50,
            signature: sig,
        };

        let result = finalize_bridge(
            &nullifier,
            &receipt,
            &trusted_keys,
            &mut pending_set,
            &mut permanent_nullifiers,
        );
        assert!(
            matches!(result, Err(BridgeError::PendingBridgeNotFound { .. })),
            "finalizing nonexistent bridge must fail: got {:?}",
            result
        );
    }

    #[test]
    fn test_two_phase_cancel_nonexistent_bridge() {
        // Cancelling a bridge that doesn't exist must fail.
        let nullifier = [0x22; 32];
        let mut pending_set = PendingBridgeSet::new();

        let result = cancel_bridge(&nullifier, 200, &mut pending_set);
        assert!(
            matches!(result, Err(BridgeError::PendingBridgeNotFound { .. })),
            "cancelling nonexistent bridge must fail: got {:?}",
            result
        );
    }

    #[test]
    fn test_verify_bridge_receipt_valid() {
        let (sk, vk) = test_keypair();
        let nullifier = [0x33; 32];
        let destination = [0x44; 32];
        let sig = sign_receipt(&nullifier, &destination, 100, &sk);

        let receipt = BridgeReceipt {
            nullifier,
            destination_federation: destination,
            mint_height: 100,
            signature: sig,
        };

        assert!(verify_bridge_receipt(
            &receipt,
            &dest_keys(destination, &vk)
        ));
    }

    #[test]
    fn test_verify_bridge_receipt_wrong_key() {
        let (sk, _vk) = test_keypair();
        let nullifier = [0x55; 32];
        let destination = [0x66; 32];
        let sig = sign_receipt(&nullifier, &destination, 100, &sk);

        let receipt = BridgeReceipt {
            nullifier,
            destination_federation: destination,
            mint_height: 100,
            signature: sig,
        };

        // Register a different key for the destination — the receipt's signer
        // is not the registered destination key, so verification must fail.
        let other_key = ed25519_dalek::SigningKey::from_bytes(&[0x99u8; 32]);
        let other_vk = other_key.verifying_key();
        assert!(!verify_bridge_receipt(
            &receipt,
            &dest_keys(destination, &other_vk)
        ));
    }

    // ========================================================================
    // Stage 9 P3.D: BridgeReceiptEnvelope phase chain tests
    // ========================================================================

    fn lock_envelope(bridge_id: [u8; 32]) -> BridgeReceiptEnvelope {
        BridgeReceiptEnvelope::new_locked(
            bridge_id, [0xAA; 32], // src
            [0xBB; 32], // dst
            10,         // block_height
            [0x01; 32], // nullifier
            7,          // asset_type
            500,        // value
            100,        // timeout_height
            [0x77; 32], // spending_proof_digest
        )
    }

    #[test]
    fn bridge_envelope_payload_phase_matches() {
        let lock = lock_envelope([0xC1; 32]);
        assert_eq!(lock.phase, BridgePhase::Locked);
        assert_eq!(lock.payload.phase(), BridgePhase::Locked);
    }

    #[test]
    fn bridge_envelope_body_hash_changes_with_phase() {
        let lock = lock_envelope([0xC1; 32]);
        let lock_hash = lock.body_hash();

        let witness = BridgeReceiptEnvelope::new_witnessed(
            lock.bridge_id,
            lock.src_federation,
            lock.dst_federation,
            12,
            lock_hash,
            13,
            [0x44; 32],
        );
        let witness_hash = witness.body_hash();
        assert_ne!(
            lock_hash, witness_hash,
            "phases must produce distinct body hashes"
        );

        // Same envelope re-built must hash identically.
        let lock2 = lock_envelope([0xC1; 32]);
        assert_eq!(
            lock_hash,
            lock2.body_hash(),
            "body_hash must be deterministic"
        );
    }

    #[test]
    fn bridge_phase_log_happy_path_lock_witness_finalize() {
        let bridge_id = compute_bridge_id(&[0x01; 32], &[0xAA; 32], &[0xBB; 32], 1);
        let mut log = BridgePhaseLog::new();

        let lock = lock_envelope(bridge_id);
        let lock_hash = lock.body_hash();
        log.admit(&lock).expect("lock admission");

        let witness = BridgeReceiptEnvelope::new_witnessed(
            bridge_id, [0xAA; 32], [0xBB; 32], 12, lock_hash, 13, [0x44; 32],
        );
        let witness_hash = witness.body_hash();
        log.admit(&witness).expect("witness admission after lock");

        let finalize = BridgeReceiptEnvelope::new_finalized(
            bridge_id,
            [0xAA; 32],
            [0xBB; 32],
            15,
            witness_hash,
            16,
            [0xEE; 32],
        );
        log.admit(&finalize)
            .expect("finalize admission after witness");

        let (last_phase, _) = log.get(&bridge_id).unwrap();
        assert_eq!(last_phase, BridgePhase::Finalized);
    }

    #[test]
    fn bridge_phase_log_happy_path_lock_refund() {
        let bridge_id = compute_bridge_id(&[0x02; 32], &[0xAA; 32], &[0xBB; 32], 2);
        let mut log = BridgePhaseLog::new();

        let lock = lock_envelope(bridge_id);
        let lock_hash = lock.body_hash();
        log.admit(&lock).expect("lock admission");

        let refund = BridgeReceiptEnvelope::new_refunded(
            bridge_id, [0xAA; 32], [0xBB; 32], 200, lock_hash, 201,
        );
        log.admit(&refund).expect("refund admission after lock");

        let (last_phase, _) = log.get(&bridge_id).unwrap();
        assert_eq!(last_phase, BridgePhase::Refunded);
    }

    /// Replay rejection: admitting the same phase twice must fail
    /// (DuplicateLock for Phase 1, NonMonotoneAdvancement for others).
    #[test]
    fn bridge_phase_log_rejects_replay_same_phase() {
        let bridge_id = compute_bridge_id(&[0x03; 32], &[0xAA; 32], &[0xBB; 32], 3);
        let mut log = BridgePhaseLog::new();

        let lock = lock_envelope(bridge_id);
        log.admit(&lock).expect("first lock admission");

        // Second Phase-1 lock for same bridge_id — must fail.
        let err = log.admit(&lock).expect_err("duplicate lock must fail");
        assert!(matches!(err, BridgePhaseError::DuplicateLock { .. }));

        // Advance to witness, then try to witness again.
        let lock_hash = lock.body_hash();
        let witness = BridgeReceiptEnvelope::new_witnessed(
            bridge_id, [0xAA; 32], [0xBB; 32], 12, lock_hash, 13, [0x44; 32],
        );
        log.admit(&witness).expect("first witness");
        // Replay witness — its previous_hash matches but the log is now at
        // Witnessed, which doesn't allow Witnessed as a next phase. So this
        // must surface as a NonMonotoneAdvancement error.
        let err = log.admit(&witness).expect_err("witness replay must fail");
        assert!(
            matches!(
                err,
                BridgePhaseError::NonMonotoneAdvancement {
                    last_phase: BridgePhase::Witnessed,
                    attempted_phase: BridgePhase::Witnessed,
                    ..
                }
            ),
            "expected NonMonotoneAdvancement, got {err:?}"
        );
    }

    /// Race-condition defense: Finalize and Refund cannot both be admitted.
    /// Whichever arrives first wins; the other is rejected as non-monotone.
    #[test]
    fn bridge_phase_log_finalize_refund_race_resolved_by_log() {
        // Variant A: refund first, then finalize must fail.
        let bridge_id_a = compute_bridge_id(&[0x04; 32], &[0xAA; 32], &[0xBB; 32], 4);
        let mut log_a = BridgePhaseLog::new();
        let lock_a = lock_envelope(bridge_id_a);
        let lock_hash_a = lock_a.body_hash();
        log_a.admit(&lock_a).unwrap();
        // Refund (legal after Locked).
        let refund_a = BridgeReceiptEnvelope::new_refunded(
            bridge_id_a,
            [0xAA; 32],
            [0xBB; 32],
            200,
            lock_hash_a,
            201,
        );
        log_a.admit(&refund_a).expect("refund after lock is legal");
        // Now a witness from a slow destination arrives — must be rejected
        // (Refunded is terminal; next_valid() is empty).
        let witness_a = BridgeReceiptEnvelope::new_witnessed(
            bridge_id_a,
            [0xAA; 32],
            [0xBB; 32],
            195,
            lock_hash_a,
            196,
            [0x55; 32],
        );
        let err = log_a
            .admit(&witness_a)
            .expect_err("witness after refund must fail");
        assert!(
            matches!(
                err,
                BridgePhaseError::NonMonotoneAdvancement {
                    last_phase: BridgePhase::Refunded,
                    attempted_phase: BridgePhase::Witnessed,
                    ..
                }
            ),
            "expected NonMonotoneAdvancement, got {err:?}"
        );

        // Variant B: witness+finalize first, then refund must fail.
        let bridge_id_b = compute_bridge_id(&[0x05; 32], &[0xAA; 32], &[0xBB; 32], 5);
        let mut log_b = BridgePhaseLog::new();
        let lock_b = lock_envelope(bridge_id_b);
        let lock_hash_b = lock_b.body_hash();
        log_b.admit(&lock_b).unwrap();
        let witness_b = BridgeReceiptEnvelope::new_witnessed(
            bridge_id_b,
            [0xAA; 32],
            [0xBB; 32],
            12,
            lock_hash_b,
            13,
            [0x44; 32],
        );
        let witness_hash_b = witness_b.body_hash();
        log_b.admit(&witness_b).unwrap();
        let finalize_b = BridgeReceiptEnvelope::new_finalized(
            bridge_id_b,
            [0xAA; 32],
            [0xBB; 32],
            15,
            witness_hash_b,
            16,
            [0xEE; 32],
        );
        log_b.admit(&finalize_b).expect("finalize after witness");
        // Late refund — must fail (Finalized is terminal).
        let refund_b = BridgeReceiptEnvelope::new_refunded(
            bridge_id_b,
            [0xAA; 32],
            [0xBB; 32],
            200,
            lock_hash_b,
            201,
        );
        let err = log_b
            .admit(&refund_b)
            .expect_err("refund after finalize must fail");
        assert!(
            matches!(
                err,
                BridgePhaseError::NonMonotoneAdvancement {
                    last_phase: BridgePhase::Finalized,
                    attempted_phase: BridgePhase::Refunded,
                    ..
                }
            ),
            "expected NonMonotoneAdvancement, got {err:?}"
        );
    }

    /// Witness with a corrupt `previous_phase_receipt_hash` must be
    /// rejected (chain-link forgery defense).
    #[test]
    fn bridge_phase_log_rejects_chain_link_forgery() {
        let bridge_id = compute_bridge_id(&[0x06; 32], &[0xAA; 32], &[0xBB; 32], 6);
        let mut log = BridgePhaseLog::new();
        let lock = lock_envelope(bridge_id);
        log.admit(&lock).unwrap();

        // Forged witness: claims a different prior hash.
        let mut witness = BridgeReceiptEnvelope::new_witnessed(
            bridge_id, [0xAA; 32], [0xBB; 32], 12, [0xDE; 32], 13, [0x44; 32],
        );
        let err = log.admit(&witness).expect_err("forged witness must fail");
        assert!(matches!(
            err,
            BridgePhaseError::PreviousPhaseHashMismatch { .. }
        ));

        // Same witness with `None` previous_phase_receipt_hash — also fails.
        witness.previous_phase_receipt_hash = None;
        let err = log
            .admit(&witness)
            .expect_err("missing prior hash must fail");
        assert!(matches!(
            err,
            BridgePhaseError::PreviousPhaseHashMismatch { .. }
        ));
    }

    /// Payload variant must match envelope.phase or admission fails.
    #[test]
    fn bridge_phase_log_rejects_payload_phase_mismatch() {
        let bridge_id = [0x07; 32];
        let mut log = BridgePhaseLog::new();

        // Hand-construct a Locked envelope carrying a Witnessed payload.
        let bogus = BridgeReceiptEnvelope {
            version: BridgeReceiptEnvelope::VERSION,
            phase: BridgePhase::Locked,
            bridge_id,
            src_federation: [0xAA; 32],
            dst_federation: [0xBB; 32],
            block_height: 10,
            previous_phase_receipt_hash: None,
            payload: BridgePhasePayload::Witnessed {
                mint_height: 13,
                mint_commitment: [0x44; 32],
            },
        };

        let err = log
            .admit(&bogus)
            .expect_err("payload/phase mismatch must fail");
        assert!(matches!(err, BridgePhaseError::PayloadPhaseMismatch { .. }));
    }

    /// Witnessing for an unknown bridge_id must fail.
    #[test]
    fn bridge_phase_log_rejects_witness_without_lock() {
        let bridge_id = compute_bridge_id(&[0x08; 32], &[0xAA; 32], &[0xBB; 32], 8);
        let mut log = BridgePhaseLog::new();

        let witness = BridgeReceiptEnvelope::new_witnessed(
            bridge_id, [0xAA; 32], [0xBB; 32], 12, [0xDE; 32], 13, [0x44; 32],
        );
        let err = log
            .admit(&witness)
            .expect_err("witness without lock must fail");
        assert!(matches!(err, BridgePhaseError::UnknownBridge { .. }));
    }

    /// Compute_bridge_id must be deterministic AND distinguishable across
    /// changes to any input.
    #[test]
    fn compute_bridge_id_distinguishes_inputs() {
        let id = compute_bridge_id(&[0x01; 32], &[0xAA; 32], &[0xBB; 32], 1);
        assert_eq!(
            id,
            compute_bridge_id(&[0x01; 32], &[0xAA; 32], &[0xBB; 32], 1),
            "deterministic"
        );
        assert_ne!(
            id,
            compute_bridge_id(&[0x02; 32], &[0xAA; 32], &[0xBB; 32], 1),
            "nullifier"
        );
        assert_ne!(
            id,
            compute_bridge_id(&[0x01; 32], &[0xCC; 32], &[0xBB; 32], 1),
            "src"
        );
        assert_ne!(
            id,
            compute_bridge_id(&[0x01; 32], &[0xAA; 32], &[0xDD; 32], 1),
            "dst"
        );
        assert_ne!(
            id,
            compute_bridge_id(&[0x01; 32], &[0xAA; 32], &[0xBB; 32], 2),
            "nonce"
        );
    }
}
