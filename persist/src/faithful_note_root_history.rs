//! Versioned, authenticated history for faithful-eight note-tree roots.
//!
//! `Dregg2.Circuit.CommitmentTreeWideHistory` is the semantic authority.  This
//! module is its strict Rust interpreter and durable carrier.  Every v1 record
//! binds one exact history edge:
//!
//! * session, federation, and committee epoch;
//! * predecessor and successor faithful-eight roots;
//! * predecessor and successor note counts;
//! * consecutive finalized heights and the carrying block id.
//!
//! The signed message is the record's fixed-width canonical `FNHR` encoding.
//! The production verifier is the enrolled-roster hybrid quorum verifier
//! (Ed25519 AND ML-DSA-65).  Structural validity is not called authentication.
//!
//! The finalized-turn store path can append one of these records in the same
//! redb transaction as the exact note leaves, receipt, attested root, and commit
//! cursor.  The existing scalar note-tree read APIs remain intact while their
//! wire consumers rotate.  Note-spend membership, nullifier, and conservation
//! authorization are separate cuts: this history authenticates the append-only
//! commitment frontier; it does not manufacture those proofs.

use redb::{ReadableTable, ReadableTableMetadata};
use serde::{Deserialize, Serialize};

use dregg_circuit::Faithful8;
use dregg_circuit::field::BABYBEAR_P;
use dregg_federation::frost::MlDsaPublicKey;
use dregg_types::{HybridQuorumSig, PublicKey};

use crate::{PersistentStore, Result as StoreResult, StoreError, tables};

const RECORD_MAGIC: [u8; 4] = *b"FNHR";
const ANCHOR_MAGIC: [u8; 4] = *b"FNHA";
const HEAD_MAGIC: [u8; 4] = *b"FNHH";
const VERSION_V1: u16 = 1;
const RESERVED_ZERO: u16 = 0;

/// `magic(4) || version(2) || reserved(2) || session(32) || federation(32) ||
/// epoch(8) || previous_height(8) || height(8) || previous_count(8) ||
/// count(8) || predecessor(32) || successor(32) || block_id(32)`.
pub const FAITHFUL_NOTE_ROOT_RECORD_V1_BYTES: usize = 208;
/// Fixed-width anchor encoding.
pub const FAITHFUL_NOTE_ROOT_ANCHOR_V1_BYTES: usize = 128;
/// Fixed-width persisted head seal: anchor bytes plus the exact record count.
pub const FAITHFUL_NOTE_ROOT_HEAD_V1_BYTES: usize = 136;

/// Bound hostile-allocation surface for a quorum envelope.  A normal hybrid
/// quorum is far below this, even with ML-DSA signatures.
const MAX_ENVELOPE_BYTES: usize = 4 * 1024 * 1024;
const MAX_QUORUM_SIGNERS: usize = 512;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FaithfulNoteRootHistoryError {
    Malformed(&'static str),
    NonCanonicalRoot { lane: usize, value: u32 },
    ContextMismatch(&'static str),
    NonConsecutiveHeight,
    CountRegression,
    RootDidNotTrackCount,
    Replay,
    Fork,
    DuplicateBlock,
    AuthenticationFailed,
    SnapshotMismatch(&'static str),
}

impl std::fmt::Display for FaithfulNoteRootHistoryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed(what) => write!(f, "malformed faithful note-root {what}"),
            Self::NonCanonicalRoot { lane, value } => {
                write!(f, "non-canonical faithful note-root lane {lane}: {value}")
            }
            Self::ContextMismatch(what) => write!(f, "faithful note-root {what} mismatch"),
            Self::NonConsecutiveHeight => {
                write!(f, "faithful note-root height is not the exact successor")
            }
            Self::CountRegression => write!(f, "faithful note-root note count regressed"),
            Self::RootDidNotTrackCount => {
                write!(f, "faithful note-root/count transition is inconsistent")
            }
            Self::Replay => write!(f, "faithful note-root record replay"),
            Self::Fork => write!(f, "faithful note-root history fork"),
            Self::DuplicateBlock => write!(f, "faithful note-root block replay"),
            Self::AuthenticationFailed => {
                write!(f, "faithful note-root hybrid authentication failed")
            }
            Self::SnapshotMismatch(what) => {
                write!(f, "faithful note-root snapshot {what} mismatch")
            }
        }
    }
}

impl std::error::Error for FaithfulNoteRootHistoryError {}

fn integrity(error: FaithfulNoteRootHistoryError) -> StoreError {
    StoreError::Integrity(error.to_string())
}

fn nonzero(bytes: &[u8; 32]) -> bool {
    bytes.iter().any(|byte| *byte != 0)
}

/// Canonical byte packing of a genuine eight-lane BabyBear root.
///
/// The private field prevents an arbitrary 32-byte string from being read as a
/// wide root.  Every 4-byte little-endian lane must be `< p`; malformed lanes
/// such as `p`, trailing bytes, or a short record refuse before authentication.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CanonicalFaithfulRoot([u8; 32]);

impl CanonicalFaithfulRoot {
    pub fn from_faithful(root: Faithful8) -> Self {
        Self(root.to_bytes32())
    }

    pub fn from_bytes(bytes: [u8; 32]) -> std::result::Result<Self, FaithfulNoteRootHistoryError> {
        for (lane, chunk) in bytes.chunks_exact(4).enumerate() {
            let value = u32::from_le_bytes(chunk.try_into().expect("four-byte lane"));
            if value >= BABYBEAR_P {
                return Err(FaithfulNoteRootHistoryError::NonCanonicalRoot { lane, value });
            }
        }
        Ok(Self(bytes))
    }

    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    pub fn to_bytes(self) -> [u8; 32] {
        self.0
    }

    pub fn to_faithful(self) -> Faithful8 {
        // Canonicality was checked on construction, so this roundtrip performs
        // no reduction and returns the exact eight lanes.
        Faithful8::from_bytes32(&self.0)
    }
}

/// Externally trusted start head for one root-history segment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaithfulNoteRootAnchorV1 {
    pub session_id: [u8; 32],
    pub federation_id: [u8; 32],
    pub committee_epoch: u64,
    pub height: u64,
    pub note_count: u64,
    pub root: CanonicalFaithfulRoot,
}

impl FaithfulNoteRootAnchorV1 {
    pub fn new(
        session_id: [u8; 32],
        federation_id: [u8; 32],
        committee_epoch: u64,
        height: u64,
        note_count: u64,
        root: CanonicalFaithfulRoot,
    ) -> std::result::Result<Self, FaithfulNoteRootHistoryError> {
        if !nonzero(&session_id) {
            return Err(FaithfulNoteRootHistoryError::Malformed("zero session id"));
        }
        if !nonzero(&federation_id) {
            return Err(FaithfulNoteRootHistoryError::Malformed(
                "zero federation id",
            ));
        }
        Ok(Self {
            session_id,
            federation_id,
            committee_epoch,
            height,
            note_count,
            root,
        })
    }

    pub fn to_bytes(&self) -> [u8; FAITHFUL_NOTE_ROOT_ANCHOR_V1_BYTES] {
        let mut out = [0u8; FAITHFUL_NOTE_ROOT_ANCHOR_V1_BYTES];
        out[0..4].copy_from_slice(&ANCHOR_MAGIC);
        out[4..6].copy_from_slice(&VERSION_V1.to_le_bytes());
        out[6..8].copy_from_slice(&RESERVED_ZERO.to_le_bytes());
        out[8..40].copy_from_slice(&self.session_id);
        out[40..72].copy_from_slice(&self.federation_id);
        out[72..80].copy_from_slice(&self.committee_epoch.to_le_bytes());
        out[80..88].copy_from_slice(&self.height.to_le_bytes());
        out[88..96].copy_from_slice(&self.note_count.to_le_bytes());
        out[96..128].copy_from_slice(self.root.as_bytes());
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> std::result::Result<Self, FaithfulNoteRootHistoryError> {
        if bytes.len() != FAITHFUL_NOTE_ROOT_ANCHOR_V1_BYTES {
            return Err(FaithfulNoteRootHistoryError::Malformed("anchor length"));
        }
        if bytes[0..4] != ANCHOR_MAGIC
            || u16::from_le_bytes(bytes[4..6].try_into().unwrap()) != VERSION_V1
            || u16::from_le_bytes(bytes[6..8].try_into().unwrap()) != RESERVED_ZERO
        {
            return Err(FaithfulNoteRootHistoryError::Malformed("anchor header"));
        }
        let session_id = bytes[8..40].try_into().unwrap();
        let federation_id = bytes[40..72].try_into().unwrap();
        let committee_epoch = u64::from_le_bytes(bytes[72..80].try_into().unwrap());
        let height = u64::from_le_bytes(bytes[80..88].try_into().unwrap());
        let note_count = u64::from_le_bytes(bytes[88..96].try_into().unwrap());
        let root = CanonicalFaithfulRoot::from_bytes(bytes[96..128].try_into().unwrap())?;
        Self::new(
            session_id,
            federation_id,
            committee_epoch,
            height,
            note_count,
            root,
        )
    }
}

/// Fixed-width v1 transition.  Construction is validation; a value of this
/// type is canonical and internally well-formed, but not yet authenticated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaithfulNoteRootRecordV1 {
    pub session_id: [u8; 32],
    pub federation_id: [u8; 32],
    pub committee_epoch: u64,
    pub previous_height: u64,
    pub height: u64,
    pub previous_note_count: u64,
    pub note_count: u64,
    pub predecessor: CanonicalFaithfulRoot,
    pub successor: CanonicalFaithfulRoot,
    pub block_id: [u8; 32],
}

impl FaithfulNoteRootRecordV1 {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        session_id: [u8; 32],
        federation_id: [u8; 32],
        committee_epoch: u64,
        previous_height: u64,
        height: u64,
        previous_note_count: u64,
        note_count: u64,
        predecessor: CanonicalFaithfulRoot,
        successor: CanonicalFaithfulRoot,
        block_id: [u8; 32],
    ) -> std::result::Result<Self, FaithfulNoteRootHistoryError> {
        if !nonzero(&session_id) {
            return Err(FaithfulNoteRootHistoryError::Malformed("zero session id"));
        }
        if !nonzero(&federation_id) {
            return Err(FaithfulNoteRootHistoryError::Malformed(
                "zero federation id",
            ));
        }
        if !nonzero(&block_id) {
            return Err(FaithfulNoteRootHistoryError::Malformed("zero block id"));
        }
        if previous_height.checked_add(1) != Some(height) {
            return Err(FaithfulNoteRootHistoryError::NonConsecutiveHeight);
        }
        if note_count < previous_note_count {
            return Err(FaithfulNoteRootHistoryError::CountRegression);
        }
        let count_changed = note_count > previous_note_count;
        let root_changed = successor != predecessor;
        if count_changed != root_changed {
            return Err(FaithfulNoteRootHistoryError::RootDidNotTrackCount);
        }
        Ok(Self {
            session_id,
            federation_id,
            committee_epoch,
            previous_height,
            height,
            previous_note_count,
            note_count,
            predecessor,
            successor,
            block_id,
        })
    }

    /// The exact bytes every quorum signer authenticates.
    pub fn signing_message(&self) -> [u8; FAITHFUL_NOTE_ROOT_RECORD_V1_BYTES] {
        let mut out = [0u8; FAITHFUL_NOTE_ROOT_RECORD_V1_BYTES];
        out[0..4].copy_from_slice(&RECORD_MAGIC);
        out[4..6].copy_from_slice(&VERSION_V1.to_le_bytes());
        out[6..8].copy_from_slice(&RESERVED_ZERO.to_le_bytes());
        out[8..40].copy_from_slice(&self.session_id);
        out[40..72].copy_from_slice(&self.federation_id);
        out[72..80].copy_from_slice(&self.committee_epoch.to_le_bytes());
        out[80..88].copy_from_slice(&self.previous_height.to_le_bytes());
        out[88..96].copy_from_slice(&self.height.to_le_bytes());
        out[96..104].copy_from_slice(&self.previous_note_count.to_le_bytes());
        out[104..112].copy_from_slice(&self.note_count.to_le_bytes());
        out[112..144].copy_from_slice(self.predecessor.as_bytes());
        out[144..176].copy_from_slice(self.successor.as_bytes());
        out[176..208].copy_from_slice(&self.block_id);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> std::result::Result<Self, FaithfulNoteRootHistoryError> {
        if bytes.len() != FAITHFUL_NOTE_ROOT_RECORD_V1_BYTES {
            return Err(FaithfulNoteRootHistoryError::Malformed("record length"));
        }
        if bytes[0..4] != RECORD_MAGIC
            || u16::from_le_bytes(bytes[4..6].try_into().unwrap()) != VERSION_V1
            || u16::from_le_bytes(bytes[6..8].try_into().unwrap()) != RESERVED_ZERO
        {
            return Err(FaithfulNoteRootHistoryError::Malformed("record header"));
        }
        Self::new(
            bytes[8..40].try_into().unwrap(),
            bytes[40..72].try_into().unwrap(),
            u64::from_le_bytes(bytes[72..80].try_into().unwrap()),
            u64::from_le_bytes(bytes[80..88].try_into().unwrap()),
            u64::from_le_bytes(bytes[88..96].try_into().unwrap()),
            u64::from_le_bytes(bytes[96..104].try_into().unwrap()),
            u64::from_le_bytes(bytes[104..112].try_into().unwrap()),
            CanonicalFaithfulRoot::from_bytes(bytes[112..144].try_into().unwrap())?,
            CanonicalFaithfulRoot::from_bytes(bytes[144..176].try_into().unwrap())?,
            bytes[176..208].try_into().unwrap(),
        )
    }

    pub fn to_anchor(&self) -> FaithfulNoteRootAnchorV1 {
        FaithfulNoteRootAnchorV1 {
            session_id: self.session_id,
            federation_id: self.federation_id,
            committee_epoch: self.committee_epoch,
            height: self.height,
            note_count: self.note_count,
            root: self.successor,
        }
    }

    pub fn validate_extension(
        &self,
        anchor: &FaithfulNoteRootAnchorV1,
    ) -> std::result::Result<(), FaithfulNoteRootHistoryError> {
        if self.session_id != anchor.session_id {
            return Err(FaithfulNoteRootHistoryError::ContextMismatch("session"));
        }
        if self.federation_id != anchor.federation_id {
            return Err(FaithfulNoteRootHistoryError::ContextMismatch("federation"));
        }
        if self.committee_epoch != anchor.committee_epoch {
            return Err(FaithfulNoteRootHistoryError::ContextMismatch(
                "committee epoch",
            ));
        }
        if self.previous_height != anchor.height
            || self.height
                != anchor
                    .height
                    .checked_add(1)
                    .ok_or(FaithfulNoteRootHistoryError::NonConsecutiveHeight)?
        {
            return Err(FaithfulNoteRootHistoryError::NonConsecutiveHeight);
        }
        if self.previous_note_count != anchor.note_count {
            return Err(FaithfulNoteRootHistoryError::ContextMismatch(
                "predecessor note count",
            ));
        }
        if self.predecessor != anchor.root {
            return Err(FaithfulNoteRootHistoryError::ContextMismatch(
                "predecessor root",
            ));
        }
        Ok(())
    }
}

#[derive(Serialize, Deserialize)]
struct EnvelopeWireV1 {
    version: u16,
    record: Vec<u8>,
    hybrid_quorum: Vec<HybridQuorumSig>,
}

/// An exact transition plus its enrolled-roster hybrid quorum.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaithfulNoteRootEnvelopeV1 {
    pub record: FaithfulNoteRootRecordV1,
    pub hybrid_quorum: Vec<HybridQuorumSig>,
}

impl FaithfulNoteRootEnvelopeV1 {
    pub fn verify_hybrid(
        &self,
        committee: &[PublicKey],
        ml_dsa_committee: &[MlDsaPublicKey],
        threshold: usize,
    ) -> bool {
        dregg_federation::receipt::verify_hybrid_quorum_sigs(
            &self.hybrid_quorum,
            &self.record.signing_message(),
            committee,
            ml_dsa_committee,
            threshold,
        )
    }

    pub(crate) fn to_bytes(&self) -> StoreResult<Vec<u8>> {
        if self.hybrid_quorum.len() > MAX_QUORUM_SIGNERS {
            return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                "quorum signer count",
            )));
        }
        let wire = EnvelopeWireV1 {
            version: VERSION_V1,
            record: self.record.signing_message().to_vec(),
            hybrid_quorum: self.hybrid_quorum.clone(),
        };
        let bytes = postcard::to_stdvec(&wire)?;
        if bytes.len() > MAX_ENVELOPE_BYTES {
            return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                "envelope size",
            )));
        }
        Ok(bytes)
    }

    fn from_bytes(bytes: &[u8]) -> StoreResult<Self> {
        if bytes.len() > MAX_ENVELOPE_BYTES {
            return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                "envelope size",
            )));
        }
        let (wire, remainder): (EnvelopeWireV1, &[u8]) = postcard::take_from_bytes(bytes)?;
        if !remainder.is_empty() || wire.version != VERSION_V1 {
            return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                "envelope framing",
            )));
        }
        if wire.hybrid_quorum.len() > MAX_QUORUM_SIGNERS {
            return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                "quorum signer count",
            )));
        }
        Ok(Self {
            record: FaithfulNoteRootRecordV1::from_bytes(&wire.record).map_err(integrity)?,
            hybrid_quorum: wire.hybrid_quorum,
        })
    }
}

/// External exact-head expectation.  A valid prefix is refused if it does not
/// match all four coordinates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FaithfulNoteRootExpectationV1 {
    pub records: u64,
    pub height: u64,
    pub note_count: u64,
    pub root: CanonicalFaithfulRoot,
}

#[derive(Clone, Debug)]
pub struct FaithfulNoteRootHistoryV1 {
    anchor: FaithfulNoteRootAnchorV1,
    envelopes: Vec<FaithfulNoteRootEnvelopeV1>,
}

impl FaithfulNoteRootHistoryV1 {
    pub fn new(anchor: FaithfulNoteRootAnchorV1) -> Self {
        Self {
            anchor,
            envelopes: Vec::new(),
        }
    }

    pub fn anchor(&self) -> &FaithfulNoteRootAnchorV1 {
        &self.anchor
    }

    pub fn envelopes(&self) -> &[FaithfulNoteRootEnvelopeV1] {
        &self.envelopes
    }

    pub fn head(&self) -> FaithfulNoteRootAnchorV1 {
        self.envelopes
            .last()
            .map(|envelope| envelope.record.to_anchor())
            .unwrap_or_else(|| self.anchor.clone())
    }

    fn append_structurally(
        &mut self,
        envelope: FaithfulNoteRootEnvelopeV1,
    ) -> std::result::Result<(), FaithfulNoteRootHistoryError> {
        let head = self.head();
        if let Some(existing) = self
            .envelopes
            .iter()
            .find(|existing| existing.record.height == envelope.record.height)
        {
            return Err(if existing == &envelope {
                FaithfulNoteRootHistoryError::Replay
            } else {
                FaithfulNoteRootHistoryError::Fork
            });
        }
        if self
            .envelopes
            .iter()
            .any(|existing| existing.record.block_id == envelope.record.block_id)
        {
            return Err(FaithfulNoteRootHistoryError::DuplicateBlock);
        }
        envelope.record.validate_extension(&head)?;
        self.envelopes.push(envelope);
        Ok(())
    }

    pub fn append_hybrid(
        &mut self,
        envelope: FaithfulNoteRootEnvelopeV1,
        committee: &[PublicKey],
        ml_dsa_committee: &[MlDsaPublicKey],
        threshold: usize,
    ) -> std::result::Result<(), FaithfulNoteRootHistoryError> {
        if !envelope.verify_hybrid(committee, ml_dsa_committee, threshold) {
            return Err(FaithfulNoteRootHistoryError::AuthenticationFailed);
        }
        self.append_structurally(envelope)
    }

    pub fn verify_exact_snapshot(
        &self,
        expected: FaithfulNoteRootExpectationV1,
    ) -> std::result::Result<(), FaithfulNoteRootHistoryError> {
        let head = self.head();
        let actual_records = u64::try_from(self.envelopes.len()).map_err(|_| {
            FaithfulNoteRootHistoryError::Malformed("record count does not fit u64")
        })?;
        if actual_records != expected.records {
            return Err(FaithfulNoteRootHistoryError::SnapshotMismatch(
                "record count",
            ));
        }
        if head.height != expected.height {
            return Err(FaithfulNoteRootHistoryError::SnapshotMismatch("height"));
        }
        if head.note_count != expected.note_count {
            return Err(FaithfulNoteRootHistoryError::SnapshotMismatch("note count"));
        }
        if head.root != expected.root {
            return Err(FaithfulNoteRootHistoryError::SnapshotMismatch("head root"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct HeadSealV1 {
    records: u64,
    head: FaithfulNoteRootAnchorV1,
}

impl HeadSealV1 {
    fn to_bytes(&self) -> [u8; FAITHFUL_NOTE_ROOT_HEAD_V1_BYTES] {
        let mut out = [0u8; FAITHFUL_NOTE_ROOT_HEAD_V1_BYTES];
        out[0..4].copy_from_slice(&HEAD_MAGIC);
        out[4..6].copy_from_slice(&VERSION_V1.to_le_bytes());
        out[6..8].copy_from_slice(&RESERVED_ZERO.to_le_bytes());
        out[8..16].copy_from_slice(&self.records.to_le_bytes());
        // The anchor's own header is redundant here; store only its payload.
        out[16..136].copy_from_slice(&self.head.to_bytes()[8..128]);
        out
    }

    fn from_bytes(bytes: &[u8]) -> std::result::Result<Self, FaithfulNoteRootHistoryError> {
        if bytes.len() != FAITHFUL_NOTE_ROOT_HEAD_V1_BYTES
            || bytes[0..4] != HEAD_MAGIC
            || u16::from_le_bytes(bytes[4..6].try_into().unwrap()) != VERSION_V1
            || u16::from_le_bytes(bytes[6..8].try_into().unwrap()) != RESERVED_ZERO
        {
            return Err(FaithfulNoteRootHistoryError::Malformed("head seal"));
        }
        let records = u64::from_le_bytes(bytes[8..16].try_into().unwrap());
        let mut anchor = [0u8; FAITHFUL_NOTE_ROOT_ANCHOR_V1_BYTES];
        anchor[0..4].copy_from_slice(&ANCHOR_MAGIC);
        anchor[4..6].copy_from_slice(&VERSION_V1.to_le_bytes());
        anchor[6..8].copy_from_slice(&RESERVED_ZERO.to_le_bytes());
        anchor[8..128].copy_from_slice(&bytes[16..136]);
        Ok(Self {
            records,
            head: FaithfulNoteRootAnchorV1::from_bytes(&anchor)?,
        })
    }
}

impl PersistentStore {
    /// Read the structurally sealed faithful history head.
    ///
    /// `None` means this store has not started a v1 segment.  A half-installed
    /// anchor/head or a record-count disagreement is an integrity error, never
    /// treated as an empty legacy store.  Authentication of the rows is checked
    /// by [`Self::load_faithful_note_root_history_hybrid`]; this narrow read is
    /// used only to plan the next locally-authenticated atomic append.
    pub fn faithful_note_root_head(&self) -> StoreResult<Option<FaithfulNoteRootAnchorV1>> {
        let read = self.db.begin_read()?;
        let table = read.open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)?;
        let metadata = read.open_table(tables::METADATA_BYTES)?;
        let anchor = metadata
            .get(tables::META_FAITHFUL_NOTE_ROOT_ANCHOR)?
            .map(|guard| guard.value().to_vec());
        let seal = metadata
            .get(tables::META_FAITHFUL_NOTE_ROOT_HEAD)?
            .map(|guard| guard.value().to_vec());
        match (anchor, seal) {
            (None, None) if table.is_empty()? => Ok(None),
            (Some(anchor), Some(seal)) => {
                let _ = FaithfulNoteRootAnchorV1::from_bytes(&anchor).map_err(integrity)?;
                let seal = HeadSealV1::from_bytes(&seal).map_err(integrity)?;
                if table.len()? != seal.records {
                    return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                        "persisted record count",
                    )));
                }
                Ok(Some(seal.head))
            }
            _ => Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                "partial anchor/head",
            ))),
        }
    }

    /// Exact externally-checkable seal coordinates for restart admission.
    pub fn faithful_note_root_expectation(
        &self,
    ) -> StoreResult<Option<FaithfulNoteRootExpectationV1>> {
        let read = self.db.begin_read()?;
        let table = read.open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)?;
        let metadata = read.open_table(tables::METADATA_BYTES)?;
        let anchor_present = metadata
            .get(tables::META_FAITHFUL_NOTE_ROOT_ANCHOR)?
            .is_some();
        let seal = metadata
            .get(tables::META_FAITHFUL_NOTE_ROOT_HEAD)?
            .map(|guard| guard.value().to_vec());
        match (anchor_present, seal) {
            (false, None) if table.is_empty()? => Ok(None),
            (true, Some(seal)) => {
                let seal = HeadSealV1::from_bytes(&seal).map_err(integrity)?;
                if table.len()? != seal.records {
                    return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                        "persisted record count",
                    )));
                }
                Ok(Some(FaithfulNoteRootExpectationV1 {
                    records: seal.records,
                    height: seal.head.height,
                    note_count: seal.head.note_count,
                    root: seal.head.root,
                }))
            }
            _ => Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                "partial anchor/head",
            ))),
        }
    }

    /// Install the external genesis/current anchor for the dedicated v1 table.
    /// Re-opening with the exact same anchor is idempotent; a different anchor
    /// refuses, so a caller cannot silently re-session existing history.
    pub fn initialize_faithful_note_root_history(
        &self,
        anchor: &FaithfulNoteRootAnchorV1,
    ) -> StoreResult<()> {
        let anchor_bytes = anchor.to_bytes();
        let head_bytes = HeadSealV1 {
            records: 0,
            head: anchor.clone(),
        }
        .to_bytes();
        let write = self.db.begin_write()?;
        {
            let table = write.open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)?;
            let mut metadata = write.open_table(tables::METADATA_BYTES)?;
            let existing_anchor = metadata
                .get(tables::META_FAITHFUL_NOTE_ROOT_ANCHOR)?
                .map(|guard| guard.value().to_vec());
            match existing_anchor {
                Some(existing) if existing.as_slice() != anchor_bytes.as_slice() => {
                    return Err(integrity(FaithfulNoteRootHistoryError::ContextMismatch(
                        "installed anchor",
                    )));
                }
                Some(_) => {}
                None => {
                    if !table.is_empty()? {
                        return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                            "records without anchor",
                        )));
                    }
                    metadata.insert(
                        tables::META_FAITHFUL_NOTE_ROOT_ANCHOR,
                        anchor_bytes.as_slice(),
                    )?;
                    metadata.insert(tables::META_FAITHFUL_NOTE_ROOT_HEAD, head_bytes.as_slice())?;
                }
            }
        }
        write.commit()?;
        Ok(())
    }

    /// Append only after the exact record passes the enrolled-roster hybrid
    /// quorum.  Structural validation and the table/head-seal mutation happen
    /// under one redb writer transaction.
    pub fn append_faithful_note_root_hybrid(
        &self,
        envelope: &FaithfulNoteRootEnvelopeV1,
        committee: &[PublicKey],
        ml_dsa_committee: &[MlDsaPublicKey],
        threshold: usize,
    ) -> StoreResult<()> {
        if !envelope.verify_hybrid(committee, ml_dsa_committee, threshold) {
            return Err(integrity(
                FaithfulNoteRootHistoryError::AuthenticationFailed,
            ));
        }
        self.append_faithful_note_root_verified(envelope)
    }

    fn append_faithful_note_root_verified(
        &self,
        envelope: &FaithfulNoteRootEnvelopeV1,
    ) -> StoreResult<()> {
        let write = self.db.begin_write()?;
        append_faithful_note_root_verified_in(&write, envelope, None, false)?;
        write.commit()?;
        Ok(())
    }

    /// Load, replay, and authenticate every record, then compare the exact
    /// externally expected head.  A truncated row, trailing bytes, a deleted
    /// tail with a surviving head seal, a fork, replay, or bad hybrid signature
    /// refuses.  Rollback of the database *and* the caller's expected head is,
    /// necessarily, an external checkpoint/finality problem.
    pub fn load_faithful_note_root_history_hybrid(
        &self,
        committee: &[PublicKey],
        ml_dsa_committee: &[MlDsaPublicKey],
        threshold: usize,
        expected: FaithfulNoteRootExpectationV1,
    ) -> StoreResult<FaithfulNoteRootHistoryV1> {
        self.load_faithful_note_root_history_with(expected, |envelope| {
            envelope.verify_hybrid(committee, ml_dsa_committee, threshold)
        })
    }

    fn load_faithful_note_root_history_with(
        &self,
        expected: FaithfulNoteRootExpectationV1,
        authenticate: impl Fn(&FaithfulNoteRootEnvelopeV1) -> bool,
    ) -> StoreResult<FaithfulNoteRootHistoryV1> {
        let read = self.db.begin_read()?;
        let table = read.open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)?;
        let metadata = read.open_table(tables::METADATA_BYTES)?;
        let anchor_guard = metadata
            .get(tables::META_FAITHFUL_NOTE_ROOT_ANCHOR)?
            .ok_or_else(|| integrity(FaithfulNoteRootHistoryError::Malformed("missing anchor")))?;
        let anchor =
            FaithfulNoteRootAnchorV1::from_bytes(anchor_guard.value()).map_err(integrity)?;
        let head_guard = metadata
            .get(tables::META_FAITHFUL_NOTE_ROOT_HEAD)?
            .ok_or_else(|| {
                integrity(FaithfulNoteRootHistoryError::Malformed("missing head seal"))
            })?;
        let seal = HeadSealV1::from_bytes(head_guard.value()).map_err(integrity)?;
        if table.len()? != seal.records {
            return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                "persisted record count",
            )));
        }

        let mut history = FaithfulNoteRootHistoryV1::new(anchor);
        for entry in table.iter()? {
            let (height, bytes) = entry?;
            let envelope = FaithfulNoteRootEnvelopeV1::from_bytes(bytes.value())?;
            if envelope.record.height != height.value() {
                return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                    "height key",
                )));
            }
            if !authenticate(&envelope) {
                return Err(integrity(
                    FaithfulNoteRootHistoryError::AuthenticationFailed,
                ));
            }
            history.append_structurally(envelope).map_err(integrity)?;
        }
        if history.head() != seal.head {
            return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                "persisted head seal",
            )));
        }
        history.verify_exact_snapshot(expected).map_err(integrity)?;
        Ok(history)
    }
}

/// Append or replay-check one faithful transition inside a caller-owned redb
/// transaction.  This is crate-private because only the finalized commit weld
/// may couple history mutation to note leaves and the commit cursor.
///
/// When the store has no segment yet, `initial_anchor` must be the exact
/// predecessor reconstructed from the durable note table.  `allow_replay` is
/// used only by the already-committed idempotence path and requires a
/// byte-identical existing envelope; it never patches a missing history row.
pub(crate) fn append_faithful_note_root_verified_in(
    write: &redb::WriteTransaction,
    envelope: &FaithfulNoteRootEnvelopeV1,
    initial_anchor: Option<&FaithfulNoteRootAnchorV1>,
    allow_replay: bool,
) -> StoreResult<()> {
    let envelope_bytes = envelope.to_bytes()?;
    let mut table = write.open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)?;
    let mut metadata = write.open_table(tables::METADATA_BYTES)?;

    let anchor_bytes = metadata
        .get(tables::META_FAITHFUL_NOTE_ROOT_ANCHOR)?
        .map(|guard| guard.value().to_vec());
    let seal_bytes = metadata
        .get(tables::META_FAITHFUL_NOTE_ROOT_HEAD)?
        .map(|guard| guard.value().to_vec());

    let seal = match (anchor_bytes, seal_bytes) {
        (Some(anchor_bytes), Some(seal_bytes)) => {
            let installed =
                FaithfulNoteRootAnchorV1::from_bytes(&anchor_bytes).map_err(integrity)?;
            if let Some(expected) = initial_anchor
                && installed != *expected
            {
                return Err(integrity(FaithfulNoteRootHistoryError::ContextMismatch(
                    "installed anchor",
                )));
            }
            HeadSealV1::from_bytes(&seal_bytes).map_err(integrity)?
        }
        (None, None) => {
            if !table.is_empty()? {
                return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                    "records without anchor",
                )));
            }
            let initial = initial_anchor.ok_or_else(|| {
                integrity(FaithfulNoteRootHistoryError::Malformed(
                    "missing initial anchor",
                ))
            })?;
            let anchor_bytes = initial.to_bytes();
            let seal = HeadSealV1 {
                records: 0,
                head: initial.clone(),
            };
            let seal_bytes = seal.to_bytes();
            metadata.insert(
                tables::META_FAITHFUL_NOTE_ROOT_ANCHOR,
                anchor_bytes.as_slice(),
            )?;
            metadata.insert(tables::META_FAITHFUL_NOTE_ROOT_HEAD, seal_bytes.as_slice())?;
            seal
        }
        _ => {
            return Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                "partial anchor/head",
            )));
        }
    };

    if table.len()? != seal.records {
        return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
            "persisted record count",
        )));
    }

    if let Some(existing) = table.get(envelope.record.height)? {
        let decoded = FaithfulNoteRootEnvelopeV1::from_bytes(existing.value())?;
        if allow_replay && decoded == *envelope && seal.head == envelope.record.to_anchor() {
            return Ok(());
        }
        return Err(integrity(if decoded == *envelope {
            FaithfulNoteRootHistoryError::Replay
        } else {
            FaithfulNoteRootHistoryError::Fork
        }));
    }

    if allow_replay {
        return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
            "missing replay record",
        )));
    }

    // A reused block id is replay even if an attacker changes height.
    for entry in table.iter()? {
        let (_, value) = entry?;
        let decoded = FaithfulNoteRootEnvelopeV1::from_bytes(value.value())?;
        if decoded.record.block_id == envelope.record.block_id {
            return Err(integrity(FaithfulNoteRootHistoryError::DuplicateBlock));
        }
    }

    envelope
        .record
        .validate_extension(&seal.head)
        .map_err(integrity)?;
    table.insert(envelope.record.height, envelope_bytes.as_slice())?;
    let next_seal = HeadSealV1 {
        records: seal.records.checked_add(1).ok_or_else(|| {
            integrity(FaithfulNoteRootHistoryError::Malformed(
                "record count overflow",
            ))
        })?,
        head: envelope.record.to_anchor(),
    }
    .to_bytes();
    metadata.insert(tables::META_FAITHFUL_NOTE_ROOT_HEAD, next_seal.as_slice())?;
    Ok(())
}

/// Build the exact next transition from the production faithful tree without
/// mutating the live tree.  This is the root-producer adapter the finalized
/// turn path can call once its authentication and atomic append weld land.
pub fn plan_faithful_note_root_transition_v1(
    tree: &crate::Poseidon2NoteTree,
    anchor: &FaithfulNoteRootAnchorV1,
    block_id: [u8; 32],
    new_commitments: &[[u8; 32]],
) -> std::result::Result<FaithfulNoteRootRecordV1, FaithfulNoteRootHistoryError> {
    let live_count = u64::try_from(tree.size())
        .map_err(|_| FaithfulNoteRootHistoryError::Malformed("live note count does not fit u64"))?;
    if live_count != anchor.note_count {
        return Err(FaithfulNoteRootHistoryError::ContextMismatch(
            "live note count",
        ));
    }
    let live_root = CanonicalFaithfulRoot::from_faithful(tree.faithful_root_immutable());
    if live_root != anchor.root {
        return Err(FaithfulNoteRootHistoryError::ContextMismatch(
            "live predecessor root",
        ));
    }
    let mut successor_tree = tree.clone();
    for commitment in new_commitments {
        successor_tree.append_blake3_commitment(commitment);
    }
    let added_count = u64::try_from(new_commitments.len())
        .map_err(|_| FaithfulNoteRootHistoryError::Malformed("append count does not fit u64"))?;
    let next_count = anchor.note_count.checked_add(added_count).ok_or(
        FaithfulNoteRootHistoryError::Malformed("note count overflow"),
    )?;
    FaithfulNoteRootRecordV1::new(
        anchor.session_id,
        anchor.federation_id,
        anchor.committee_epoch,
        anchor.height,
        anchor
            .height
            .checked_add(1)
            .ok_or(FaithfulNoteRootHistoryError::NonConsecutiveHeight)?,
        anchor.note_count,
        next_count,
        anchor.root,
        CanonicalFaithfulRoot::from_faithful(successor_tree.faithful_root_immutable()),
        block_id,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tag(byte: u8) -> [u8; 32] {
        let mut out = [0u8; 32];
        out[0] = byte;
        out
    }

    fn empty_anchor() -> (crate::Poseidon2NoteTree, FaithfulNoteRootAnchorV1) {
        let tree = crate::Poseidon2NoteTree::with_depth(4);
        let root = CanonicalFaithfulRoot::from_faithful(tree.faithful_root_immutable());
        let anchor = FaithfulNoteRootAnchorV1::new(tag(1), tag(2), 7, 40, 0, root).unwrap();
        (tree, anchor)
    }

    fn planned(
        tree: &crate::Poseidon2NoteTree,
        anchor: &FaithfulNoteRootAnchorV1,
        block: u8,
        commitments: &[[u8; 32]],
    ) -> FaithfulNoteRootEnvelopeV1 {
        FaithfulNoteRootEnvelopeV1 {
            record: plan_faithful_note_root_transition_v1(tree, anchor, tag(block), commitments)
                .unwrap(),
            hybrid_quorum: Vec::new(),
        }
    }

    #[test]
    fn canonical_record_is_exact_and_rejects_malformed_lanes_or_framing() {
        let (tree, anchor) = empty_anchor();
        let envelope = planned(&tree, &anchor, 3, &[[0x41; 32]]);
        let bytes = envelope.record.signing_message();
        assert_eq!(bytes.len(), FAITHFUL_NOTE_ROOT_RECORD_V1_BYTES);
        assert_eq!(&bytes[..8], b"FNHR\x01\x00\x00\x00");
        assert_eq!(bytes[8], 1, "Lean demo layout: session byte 0");
        assert_eq!(bytes[40], 2, "Lean demo layout: federation byte 0");
        assert_eq!(bytes[72], 7, "Lean demo layout: epoch LE");
        assert_eq!(bytes[80], 40, "Lean demo layout: predecessor height LE");
        assert_eq!(bytes[88], 41, "Lean demo layout: successor height LE");
        assert_eq!(bytes[96], 0, "this fixture starts at note count zero");
        assert_eq!(bytes[104], 1, "this fixture appends one note");
        assert_eq!(bytes[176], 3, "Lean demo layout: block id byte 0");
        assert_eq!(
            FaithfulNoteRootRecordV1::from_bytes(&bytes).unwrap(),
            envelope.record
        );
        assert!(FaithfulNoteRootRecordV1::from_bytes(&bytes[..bytes.len() - 1]).is_err());
        let mut trailing = bytes.to_vec();
        trailing.push(0);
        assert!(FaithfulNoteRootRecordV1::from_bytes(&trailing).is_err());
        let mut noncanonical = bytes;
        noncanonical[112..116].copy_from_slice(&BABYBEAR_P.to_le_bytes());
        assert!(matches!(
            FaithfulNoteRootRecordV1::from_bytes(&noncanonical),
            Err(FaithfulNoteRootHistoryError::NonCanonicalRoot { lane: 0, .. })
        ));
    }

    /// Rust correspondence for the Lean `demoAnchor`/`demoRecord` structural
    /// guards: the exact extension accepts, predecessor/session substitution,
    /// replay, and a sibling at the consumed height refuse.
    #[test]
    fn lean_demo_transition_matches_rust_interpreter() {
        let (tree, anchor) = empty_anchor();
        let first = planned(&tree, &anchor, 3, &[[0x11; 32], [0x12; 32]]);
        first.record.validate_extension(&anchor).unwrap();

        let mut history = FaithfulNoteRootHistoryV1::new(anchor.clone());
        history.append_structurally(first.clone()).unwrap();
        assert!(matches!(
            history.append_structurally(first.clone()),
            Err(FaithfulNoteRootHistoryError::Replay)
        ));

        let mut sibling = first.clone();
        sibling.record.block_id = tag(4);
        assert!(history.append_structurally(sibling).is_err());

        let mut wrong_session = first.record.clone();
        wrong_session.session_id = tag(99);
        assert!(matches!(
            wrong_session.validate_extension(&anchor),
            Err(FaithfulNoteRootHistoryError::ContextMismatch("session"))
        ));
    }

    #[test]
    fn planner_binds_exact_live_predecessor_and_multi_append_successor() {
        let (mut tree, anchor) = empty_anchor();
        let commitments = [[0x31; 32], [0x32; 32], [0x33; 32]];
        let record =
            plan_faithful_note_root_transition_v1(&tree, &anchor, tag(3), &commitments).unwrap();
        assert_eq!(record.previous_note_count, 0);
        assert_eq!(record.note_count, 3);
        for commitment in &commitments {
            tree.append_blake3_commitment(commitment);
        }
        assert_eq!(
            record.successor,
            CanonicalFaithfulRoot::from_faithful(tree.faithful_root())
        );

        let mut wrong = anchor;
        wrong.note_count = 1;
        assert!(matches!(
            plan_faithful_note_root_transition_v1(&tree, &wrong, tag(4), &[]),
            Err(FaithfulNoteRootHistoryError::ContextMismatch(
                "live note count"
            ))
        ));
    }

    #[test]
    fn hybrid_api_fails_closed_without_an_enrolled_roster() {
        let (tree, anchor) = empty_anchor();
        let envelope = planned(&tree, &anchor, 3, &[[0x51; 32]]);
        let mut history = FaithfulNoteRootHistoryV1::new(anchor);
        assert!(matches!(
            history.append_hybrid(envelope, &[], &[], 0),
            Err(FaithfulNoteRootHistoryError::AuthenticationFailed)
        ));
        assert!(history.envelopes().is_empty());
    }

    #[test]
    fn durable_history_rejects_replay_fork_and_tail_truncation() {
        let store = PersistentStore::open_in_memory().unwrap();
        let (tree, anchor) = empty_anchor();
        store
            .initialize_faithful_note_root_history(&anchor)
            .unwrap();
        let first = planned(&tree, &anchor, 3, &[[0x61; 32]]);
        store.append_faithful_note_root_verified(&first).unwrap();
        assert!(store.append_faithful_note_root_verified(&first).is_err());

        let expected = FaithfulNoteRootExpectationV1 {
            records: 1,
            height: first.record.height,
            note_count: first.record.note_count,
            root: first.record.successor,
        };
        let loaded = store
            .load_faithful_note_root_history_with(expected, |_| true)
            .unwrap();
        assert_eq!(loaded.envelopes().len(), 1);

        // Delete only the tail row while leaving the transactionally written
        // head seal.  Load must reject the apparently valid empty prefix.
        let write = store.db.begin_write().unwrap();
        {
            let mut table = write
                .open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)
                .unwrap();
            table.remove(first.record.height).unwrap();
        }
        write.commit().unwrap();
        assert!(
            store
                .load_faithful_note_root_history_with(expected, |_| true)
                .is_err()
        );
    }

    #[test]
    fn exact_expectation_rejects_a_valid_prefix() {
        let (tree, anchor) = empty_anchor();
        let first = planned(&tree, &anchor, 3, &[[0x71; 32]]);
        let mut history = FaithfulNoteRootHistoryV1::new(anchor.clone());
        history.append_structurally(first.clone()).unwrap();
        let full = FaithfulNoteRootExpectationV1 {
            records: 1,
            height: first.record.height,
            note_count: first.record.note_count,
            root: first.record.successor,
        };
        history.verify_exact_snapshot(full).unwrap();
        assert!(
            FaithfulNoteRootHistoryV1::new(anchor)
                .verify_exact_snapshot(full)
                .is_err()
        );
    }
}
