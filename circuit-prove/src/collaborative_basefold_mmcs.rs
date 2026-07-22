//! Commitment/opening seam for Dregg-native collaborative BaseFold rounds.
//!
//! This module connects [`crate::collaborative_basefold`] party rows to the
//! alternate packed/interleaved Merkle layout in
//! [`crate::packed_interleaved_merkle`].  A party-local fold through
//! [`verify_party_opening_then_fold`] is admitted only after the exact row has
//! opened at that party's canonical logical index under the published root.
//! The coordinator path additionally requires the complete ordered party set,
//! reconstructs the published all-row audit digest, differentially checks the
//! fold against the centralized coefficient-domain oracle, and recomputes the
//! exact next-round commitment.  The fold challenge is derived from the Merkle
//! root, not from the redundant audit digest: a publisher therefore cannot
//! grind challenges by choosing an inconsistent audit digest.
//!
//! The round manifest binds a canonical semantic-relation digest, session
//! digest, tensor geometry, round, packed layout, row-commitment root,
//! published state digest, and fold challenge.  `roster_digest` is deliberately
//! only an opaque public transcript input.  This module does not authenticate
//! it, its senders, or the bytes from which an application derived it.  In
//! particular, this seam does not treat Rust/Lean transport JSON as semantic
//! authority; callers must supply a digest of the canonical relation/statement
//! selected by the protocol.
//!
//! # Still open
//!
//! This is **not a complete PCS, FRI IOPP, or proof system**.  It does not prove
//! low degree, honest tensor encoding, query sampling/soundness, availability,
//! sender authentication, Byzantine broadcast, malicious-secure sharing,
//! zero knowledge, dropout recovery, accountability, or a canonical network
//! codec for these in-process reference types.  The implementation is a CPU
//! reference that materializes every row and the complete Merkle tree.
//! The base-field challenge remains subject to the soundness-ledger caveat in
//! [`crate::collaborative_basefold`].

use core::fmt;

use p3_matrix::dense::RowMajorMatrix;

use crate::collaborative_basefold::{
    CollaborativeBasefoldError, CollaborativeFoldTranscript, DistributedTensorCodeword,
    FoldChallenge, PartyEncodedRow, PartyIndex, TensorCodeShape, fold_party_row_local,
    fold_recombined_reference,
};
use crate::packed_interleaved_merkle::{
    PackedInterleavedCommitment, PackedInterleavedError, PackedInterleavedLayout,
    PackedInterleavedOpening, PackedInterleavedProverData, commit_packed_interleaved,
    verify_packed_interleaved_opening,
};

/// Binary protocol version for [`CollaborativeRoundManifest`].
pub const COLLABORATIVE_BASEFOLD_MMCS_MANIFEST_VERSION: u32 = 1;

/// Domain separating the manifest-to-fold-transcript context.
pub const COLLABORATIVE_BASEFOLD_MMCS_CONTEXT_DOMAIN_V1: &[u8] =
    b"dregg.native.collaborative-basefold-mmcs.context.v1\0";

/// Public identifiers that remain constant across a sequence of fold rounds.
///
/// These values are transcript inputs.  Construction of this type does not
/// attest a relation, authenticate a session, or validate a roster.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CollaborativeRoundContext {
    semantic_relation_digest: [u8; 32],
    session_digest: [u8; 32],
    roster_digest: [u8; 32],
}

impl CollaborativeRoundContext {
    /// Construct opaque public transcript inputs.
    pub const fn new(
        semantic_relation_digest: [u8; 32],
        session_digest: [u8; 32],
        roster_digest: [u8; 32],
    ) -> Self {
        Self {
            semantic_relation_digest,
            session_digest,
            roster_digest,
        }
    }

    /// Canonical semantic relation/statement identifier supplied by the caller.
    pub const fn semantic_relation_digest(self) -> [u8; 32] {
        self.semantic_relation_digest
    }

    /// Opaque public session identifier.
    pub const fn session_digest(self) -> [u8; 32] {
        self.session_digest
    }

    /// Opaque public roster binding; not an authentication proof.
    pub const fn roster_digest(self) -> [u8; 32] {
        self.roster_digest
    }
}

/// Versioned public description of one committed collaborative fold state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CollaborativeRoundManifest {
    version: u32,
    context: CollaborativeRoundContext,
    shape: TensorCodeShape,
    round: usize,
    columns: usize,
    packed_layout: PackedInterleavedLayout,
    row_commitment_root: [u8; 32],
    published_state_digest: [u8; 32],
    challenge: FoldChallenge,
}

impl CollaborativeRoundManifest {
    /// Manifest format version.
    pub const fn version(&self) -> u32 {
        self.version
    }

    /// Round-invariant semantic/session/roster transcript inputs.
    pub const fn context(&self) -> CollaborativeRoundContext {
        self.context
    }

    /// Original tensor-code geometry.
    pub const fn shape(&self) -> TensorCodeShape {
        self.shape
    }

    /// Number of folds already completed.
    pub const fn round(&self) -> usize {
        self.round
    }

    /// Current width of every party row.
    pub const fn columns(&self) -> usize {
        self.columns
    }

    /// Exact worker-interleaved physical layout bound into the root.
    pub const fn packed_layout(&self) -> &PackedInterleavedLayout {
        &self.packed_layout
    }

    /// Domain-separated packed/interleaved row commitment.
    pub const fn row_commitment_root(&self) -> &[u8; 32] {
        &self.row_commitment_root
    }

    /// Redundant all-row audit digest, checked by exact-set coordinator verification.
    ///
    /// A single party opening cannot establish this digest's consistency with
    /// every other row.  It therefore does not drive the challenge; the row
    /// commitment root does.
    pub const fn published_state_digest(&self) -> [u8; 32] {
        self.published_state_digest
    }

    /// Challenge derived from the semantic/session/roster/geometry context and
    /// the row commitment root.  The redundant all-row audit digest is checked
    /// separately by the exact-set coordinator.
    pub const fn challenge(&self) -> FoldChallenge {
        self.challenge
    }
}

/// Public commitment envelope for a round.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PublishedCollaborativeRound {
    manifest: CollaborativeRoundManifest,
    row_commitment: PackedInterleavedCommitment,
}

impl PublishedCollaborativeRound {
    /// Versioned round manifest.
    pub const fn manifest(&self) -> &CollaborativeRoundManifest {
        &self.manifest
    }

    /// Strongly typed alternate-layout row commitment.
    pub const fn row_commitment(&self) -> &PackedInterleavedCommitment {
        &self.row_commitment
    }
}

/// Publisher-side tree retained only for making row openings.
pub struct CollaborativeRoundProverData {
    published: PublishedCollaborativeRound,
    prover_data: PackedInterleavedProverData,
}

impl fmt::Debug for CollaborativeRoundProverData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CollaborativeRoundProverData")
            .field("published", &self.published)
            .field("prover_data", &"<packed/interleaved Merkle tree>")
            .finish()
    }
}

impl CollaborativeRoundProverData {
    /// In-process public envelope to hand to parties and verifiers.
    pub const fn published(&self) -> &PublishedCollaborativeRound {
        &self.published
    }

    /// Open one party's exact current row.
    ///
    /// This CPU helper sees the complete state/tree.  It models the wire object
    /// a future distributed worker-local subtree implementation must produce;
    /// it is not evidence of a no-viewer implementation.
    pub fn open_party_row(
        &self,
        state: &DistributedTensorCodeword,
        party: PartyIndex,
    ) -> Result<PartyRoundOpening, CollaborativeBasefoldMmcsError> {
        validate_state_matches_manifest(state, &self.published.manifest)?;
        let party_index = party.get();
        if party_index >= state.shape().party_count() {
            return Err(CollaborativeBasefoldMmcsError::PartyOutOfRange {
                party: party_index,
                party_count: state.shape().party_count(),
            });
        }
        let row = state.party_rows()[party_index].clone();
        if row.party() != party {
            return Err(CollaborativeBasefoldMmcsError::PartyOrderMismatch {
                position: party_index,
                actual: row.party().get(),
            });
        }
        Ok(PartyRoundOpening {
            party,
            row,
            opening: self.prover_data.open(party_index)?,
        })
    }
}

/// One party's claimed row plus its packed/interleaved Merkle authentication path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PartyRoundOpening {
    party: PartyIndex,
    row: PartyEncodedRow,
    opening: PackedInterleavedOpening,
}

impl PartyRoundOpening {
    /// Claimed canonical party index.
    pub const fn party(&self) -> PartyIndex {
        self.party
    }

    /// Claimed local BaseFold row.
    pub const fn row(&self) -> &PartyEncodedRow {
        &self.row
    }

    /// Physical authentication path for the canonical logical row index.
    pub const fn opening(&self) -> &PackedInterleavedOpening {
        &self.opening
    }
}

/// Verified result of one complete coordinator transition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedCollaborativeRoundTransition {
    next_state: DistributedTensorCodeword,
}

impl VerifiedCollaborativeRoundTransition {
    /// Reconstructed next state after all openings and the differential check.
    pub const fn next_state(&self) -> &DistributedTensorCodeword {
        &self.next_state
    }

    /// Consume the verification result.
    pub fn into_next_state(self) -> DistributedTensorCodeword {
        self.next_state
    }
}

/// Fail-closed errors at the new commitment/fold seam.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CollaborativeBasefoldMmcsError {
    /// Algebraic BaseFold shape or challenge failure.
    Basefold(CollaborativeBasefoldError),
    /// Packed/interleaved commitment or opening failure.
    PackedMerkle(PackedInterleavedError),
    /// The manifest uses an unsupported binary protocol version.
    UnsupportedManifestVersion { expected: u32, actual: u32 },
    /// Round and original geometry do not determine the declared row width.
    ManifestRoundGeometryMismatch {
        round: usize,
        expected_columns: usize,
        actual_columns: usize,
    },
    /// The committed tree layout is not the layout in the manifest.
    CommitmentLayoutMismatch,
    /// The typed commitment's alternate root is not the manifest root.
    CommitmentRootMismatch,
    /// Current row layout is not exactly one BaseFold row per logical party.
    RowLayoutMismatch,
    /// Re-deriving the transcript from the manifest changed the challenge.
    ManifestChallengeMismatch,
    /// A caller supplied a state from another round/shape/session publication.
    StateManifestMismatch(&'static str),
    /// Party label lies outside the tensor geometry.
    PartyOutOfRange { party: usize, party_count: usize },
    /// Coordinator did not receive exactly one opening for every party.
    WrongOpeningCount { expected: usize, actual: usize },
    /// Openings must arrive in exact canonical party order.
    PartyOrderMismatch { position: usize, actual: usize },
    /// Wrapper label and embedded BaseFold-row label disagree.
    EmbeddedPartyMismatch { wrapper: usize, embedded: usize },
    /// Merkle-opened field values differ from the row passed to the fold.
    OpenedRowMismatch { party: usize },
    /// Complete opened row set does not hash to the published state digest.
    PublishedStateDigestMismatch,
    /// Row-local fold and centralized coefficient-domain fold disagreed.
    CentralizedDifferentialMismatch,
    /// Claimed next public envelope differs from the deterministically rebuilt one.
    NextRoundCommitmentMismatch,
}

impl fmt::Display for CollaborativeBasefoldMmcsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Basefold(error) => write!(f, "collaborative BaseFold error: {error}"),
            Self::PackedMerkle(error) => write!(f, "packed Merkle error: {error}"),
            Self::UnsupportedManifestVersion { expected, actual } => write!(
                f,
                "unsupported collaborative round manifest version {actual}; expected {expected}"
            ),
            Self::ManifestRoundGeometryMismatch {
                round,
                expected_columns,
                actual_columns,
            } => write!(
                f,
                "round {round} requires {expected_columns} columns, manifest declares {actual_columns}"
            ),
            Self::CommitmentLayoutMismatch => {
                f.write_str("row commitment layout differs from the manifest")
            }
            Self::CommitmentRootMismatch => {
                f.write_str("row commitment root differs from the manifest")
            }
            Self::RowLayoutMismatch => f.write_str(
                "packed layout is not one BaseFold row source over the declared party set",
            ),
            Self::ManifestChallengeMismatch => {
                f.write_str("fold challenge is not derived from the exact round manifest")
            }
            Self::StateManifestMismatch(field) => {
                write!(f, "state differs from manifest field {field}")
            }
            Self::PartyOutOfRange { party, party_count } => {
                write!(f, "party {party} is outside range 0..{party_count}")
            }
            Self::WrongOpeningCount { expected, actual } => {
                write!(f, "received {actual} party openings, expected {expected}")
            }
            Self::PartyOrderMismatch { position, actual } => write!(
                f,
                "opening position {position} carries party {actual}, expected {position}"
            ),
            Self::EmbeddedPartyMismatch { wrapper, embedded } => write!(
                f,
                "opening wrapper carries party {wrapper}, embedded row carries {embedded}"
            ),
            Self::OpenedRowMismatch { party } => {
                write!(
                    f,
                    "Merkle-opened values differ from party {party}'s fold row"
                )
            }
            Self::PublishedStateDigestMismatch => {
                f.write_str("opened exact row set differs from the published state digest")
            }
            Self::CentralizedDifferentialMismatch => f.write_str(
                "party-local fold reconstruction differs from centralized coefficient oracle",
            ),
            Self::NextRoundCommitmentMismatch => {
                f.write_str("claimed next-round commitment/manifest was not rebuilt exactly")
            }
        }
    }
}

impl std::error::Error for CollaborativeBasefoldMmcsError {}

impl From<CollaborativeBasefoldError> for CollaborativeBasefoldMmcsError {
    fn from(value: CollaborativeBasefoldError) -> Self {
        Self::Basefold(value)
    }
}

impl From<PackedInterleavedError> for CollaborativeBasefoldMmcsError {
    fn from(value: PackedInterleavedError) -> Self {
        Self::PackedMerkle(value)
    }
}

/// Commit one complete BaseFold state and derive its versioned round manifest.
pub fn publish_collaborative_round(
    context: CollaborativeRoundContext,
    state: &DistributedTensorCodeword,
    worker_count: usize,
) -> Result<CollaborativeRoundProverData, CollaborativeBasefoldMmcsError> {
    let recombined = state.recombine()?;
    let source = RowMajorMatrix::new(recombined.values().to_vec(), state.columns());
    let (row_commitment, prover_data) = commit_packed_interleaved(&[source], worker_count)?;
    let manifest = build_manifest(context, state, row_commitment.clone())?;
    Ok(CollaborativeRoundProverData {
        published: PublishedCollaborativeRound {
            manifest,
            row_commitment,
        },
        prover_data,
    })
}

/// Verify inclusion of one exact local row, then and only then apply its fold.
pub fn verify_party_opening_then_fold(
    published: &PublishedCollaborativeRound,
    party_opening: &PartyRoundOpening,
) -> Result<PartyEncodedRow, CollaborativeBasefoldMmcsError> {
    validate_publication(published)?;
    let manifest = &published.manifest;
    // Security-critical order: authenticate inclusion and exact opened values
    // before accepting/producing a row-local fold result.
    authenticate_party_opening(published, party_opening)?;

    let transcript = transcript_for_manifest(manifest);
    Ok(fold_party_row_local(
        manifest.shape,
        manifest.round,
        manifest.columns,
        &party_opening.row,
        &transcript,
        manifest.row_commitment_root,
        &manifest.challenge,
    )?)
}

/// Verify a complete fold transition, including the exact next commitment.
///
/// The input vector position is part of the protocol; the coordinator never
/// sorts network inputs.  Every row is opened before its local fold, the complete
/// set is rehashed to the manifest state digest, and the next public envelope is
/// rebuilt byte-for-byte from the verified rows.
pub fn verify_collaborative_round_transition(
    current: &PublishedCollaborativeRound,
    openings: &[PartyRoundOpening],
    claimed_next: &PublishedCollaborativeRound,
) -> Result<VerifiedCollaborativeRoundTransition, CollaborativeBasefoldMmcsError> {
    validate_publication(current)?;
    let expected = current.manifest.shape.party_count();
    if openings.len() != expected {
        return Err(CollaborativeBasefoldMmcsError::WrongOpeningCount {
            expected,
            actual: openings.len(),
        });
    }

    let mut current_rows = Vec::with_capacity(expected);
    for (position, opening) in openings.iter().enumerate() {
        if opening.party.get() != position {
            return Err(CollaborativeBasefoldMmcsError::PartyOrderMismatch {
                position,
                actual: opening.party.get(),
            });
        }
        // Phase 1 authenticates the complete exact set.  No folding occurs
        // until every path and the redundant all-row digest have been checked.
        current_rows.push(authenticate_party_opening(current, opening)?);
    }

    let reconstructed_current = DistributedTensorCodeword::from_party_rows(
        current.manifest.shape,
        current.manifest.round,
        current.manifest.columns,
        current_rows,
    )?;
    if reconstructed_current.state_digest() != current.manifest.published_state_digest {
        return Err(CollaborativeBasefoldMmcsError::PublishedStateDigestMismatch);
    }

    // Phase 2 folds only the already authenticated complete row set.
    let transcript = transcript_for_manifest(&current.manifest);
    let next_rows = reconstructed_current
        .party_rows()
        .iter()
        .map(|row| {
            fold_party_row_local(
                current.manifest.shape,
                current.manifest.round,
                current.manifest.columns,
                row,
                &transcript,
                current.manifest.row_commitment_root,
                &current.manifest.challenge,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;

    let next_state = DistributedTensorCodeword::from_party_rows(
        current.manifest.shape,
        current.manifest.round + 1,
        current.manifest.columns / 2,
        next_rows,
    )?;

    let centralized = fold_recombined_reference(
        &reconstructed_current.recombine()?,
        &current.manifest.challenge,
    )?;
    if centralized != next_state.recombine()? {
        return Err(CollaborativeBasefoldMmcsError::CentralizedDifferentialMismatch);
    }

    let worker_count = current.manifest.packed_layout.worker_count();
    let expected_next =
        publish_collaborative_round(current.manifest.context, &next_state, worker_count)?;
    validate_publication(claimed_next)?;
    if expected_next.published != *claimed_next {
        return Err(CollaborativeBasefoldMmcsError::NextRoundCommitmentMismatch);
    }

    Ok(VerifiedCollaborativeRoundTransition { next_state })
}

fn build_manifest(
    context: CollaborativeRoundContext,
    state: &DistributedTensorCodeword,
    row_commitment: PackedInterleavedCommitment,
) -> Result<CollaborativeRoundManifest, CollaborativeBasefoldMmcsError> {
    let version = COLLABORATIVE_BASEFOLD_MMCS_MANIFEST_VERSION;
    let shape = state.shape();
    let round = state.round();
    let columns = state.columns();
    let packed_layout = row_commitment.layout().clone();
    let row_commitment_root = *row_commitment.alternate_root();
    let published_state_digest = state.state_digest();
    let challenge = transcript_for_parts(
        version,
        context,
        shape,
        round,
        columns,
        &packed_layout,
        row_commitment_root,
    )
    .challenge_for_published_digest(shape, round, columns, row_commitment_root)?;
    let manifest = CollaborativeRoundManifest {
        version,
        context,
        shape,
        round,
        columns,
        packed_layout,
        row_commitment_root,
        published_state_digest,
        challenge,
    };
    let published = PublishedCollaborativeRound {
        manifest: manifest.clone(),
        row_commitment,
    };
    validate_publication(&published)?;
    Ok(manifest)
}

fn validate_publication(
    published: &PublishedCollaborativeRound,
) -> Result<(), CollaborativeBasefoldMmcsError> {
    let manifest = &published.manifest;
    if manifest.version != COLLABORATIVE_BASEFOLD_MMCS_MANIFEST_VERSION {
        return Err(CollaborativeBasefoldMmcsError::UnsupportedManifestVersion {
            expected: COLLABORATIVE_BASEFOLD_MMCS_MANIFEST_VERSION,
            actual: manifest.version,
        });
    }
    let expected_columns = expected_columns(manifest.shape, manifest.round);
    if expected_columns != Some(manifest.columns) {
        return Err(
            CollaborativeBasefoldMmcsError::ManifestRoundGeometryMismatch {
                round: manifest.round,
                expected_columns: expected_columns.unwrap_or(0),
                actual_columns: manifest.columns,
            },
        );
    }
    if published.row_commitment.layout() != &manifest.packed_layout {
        return Err(CollaborativeBasefoldMmcsError::CommitmentLayoutMismatch);
    }
    if published.row_commitment.alternate_root() != &manifest.row_commitment_root {
        return Err(CollaborativeBasefoldMmcsError::CommitmentRootMismatch);
    }
    if manifest.packed_layout.logical_rows() != manifest.shape.party_count()
        || manifest.packed_layout.source_widths() != [manifest.columns]
    {
        return Err(CollaborativeBasefoldMmcsError::RowLayoutMismatch);
    }
    let expected_challenge = transcript_for_manifest(manifest).challenge_for_published_digest(
        manifest.shape,
        manifest.round,
        manifest.columns,
        manifest.row_commitment_root,
    )?;
    if expected_challenge != manifest.challenge {
        return Err(CollaborativeBasefoldMmcsError::ManifestChallengeMismatch);
    }
    Ok(())
}

fn validate_state_matches_manifest(
    state: &DistributedTensorCodeword,
    manifest: &CollaborativeRoundManifest,
) -> Result<(), CollaborativeBasefoldMmcsError> {
    if state.shape() != manifest.shape {
        return Err(CollaborativeBasefoldMmcsError::StateManifestMismatch(
            "shape",
        ));
    }
    if state.round() != manifest.round {
        return Err(CollaborativeBasefoldMmcsError::StateManifestMismatch(
            "round",
        ));
    }
    if state.columns() != manifest.columns {
        return Err(CollaborativeBasefoldMmcsError::StateManifestMismatch(
            "columns",
        ));
    }
    if state.state_digest() != manifest.published_state_digest {
        return Err(CollaborativeBasefoldMmcsError::StateManifestMismatch(
            "state digest",
        ));
    }
    Ok(())
}

fn authenticate_party_opening(
    published: &PublishedCollaborativeRound,
    party_opening: &PartyRoundOpening,
) -> Result<PartyEncodedRow, CollaborativeBasefoldMmcsError> {
    let party = party_opening.party.get();
    if party >= published.manifest.shape.party_count() {
        return Err(CollaborativeBasefoldMmcsError::PartyOutOfRange {
            party,
            party_count: published.manifest.shape.party_count(),
        });
    }
    if party_opening.row.party() != party_opening.party {
        return Err(CollaborativeBasefoldMmcsError::EmbeddedPartyMismatch {
            wrapper: party,
            embedded: party_opening.row.party().get(),
        });
    }
    let opened = verify_packed_interleaved_opening(
        &published.row_commitment,
        party,
        &party_opening.opening,
    )?;
    if opened.len() != 1 || opened[0].as_slice() != party_opening.row.values() {
        return Err(CollaborativeBasefoldMmcsError::OpenedRowMismatch { party });
    }
    Ok(party_opening.row.clone())
}

fn transcript_for_manifest(manifest: &CollaborativeRoundManifest) -> CollaborativeFoldTranscript {
    transcript_for_parts(
        manifest.version,
        manifest.context,
        manifest.shape,
        manifest.round,
        manifest.columns,
        &manifest.packed_layout,
        manifest.row_commitment_root,
    )
}

fn transcript_for_parts(
    version: u32,
    context_fields: CollaborativeRoundContext,
    shape: TensorCodeShape,
    round: usize,
    columns: usize,
    packed_layout: &PackedInterleavedLayout,
    row_commitment_root: [u8; 32],
) -> CollaborativeFoldTranscript {
    let mut context = Vec::with_capacity(256);
    context.extend_from_slice(COLLABORATIVE_BASEFOLD_MMCS_CONTEXT_DOMAIN_V1);
    context.extend_from_slice(&version.to_le_bytes());
    context.extend_from_slice(&context_fields.session_digest);
    context.extend_from_slice(&context_fields.roster_digest);
    context.extend_from_slice(&(shape.message_rows() as u64).to_le_bytes());
    context.extend_from_slice(&(shape.message_columns() as u64).to_le_bytes());
    context.extend_from_slice(&(shape.party_count() as u64).to_le_bytes());
    context.extend_from_slice(&(shape.encoded_columns() as u64).to_le_bytes());
    context.extend_from_slice(&(round as u64).to_le_bytes());
    context.extend_from_slice(&(columns as u64).to_le_bytes());
    context.extend_from_slice(&(packed_layout.logical_rows() as u64).to_le_bytes());
    context.extend_from_slice(&(packed_layout.worker_count() as u64).to_le_bytes());
    context.extend_from_slice(&(packed_layout.source_widths().len() as u64).to_le_bytes());
    for width in packed_layout.source_widths() {
        context.extend_from_slice(&(*width as u64).to_le_bytes());
    }
    context.extend_from_slice(&row_commitment_root);
    CollaborativeFoldTranscript::new(context_fields.semantic_relation_digest, &context)
}

fn expected_columns(shape: TensorCodeShape, round: usize) -> Option<usize> {
    let max_round = shape.encoded_columns().ilog2() as usize;
    (round <= max_round).then(|| shape.encoded_columns() >> round)
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;
    use p3_field::PrimeCharacteristicRing;

    use super::*;
    use crate::collaborative_basefold::{
        centralized_tensor_encode, collaborative_tensor_encode, column_encode_party_shares,
    };

    fn shape() -> TensorCodeShape {
        TensorCodeShape::new(2, 3, 4, 8).unwrap()
    }

    fn message() -> Vec<BabyBear> {
        (1..=6).map(BabyBear::from_u64).collect()
    }

    fn state() -> DistributedTensorCodeword {
        let shape = shape();
        let shares = column_encode_party_shares(shape, &message()).unwrap();
        collaborative_tensor_encode(shape, &shares).unwrap()
    }

    fn context() -> CollaborativeRoundContext {
        CollaborativeRoundContext::new([0x11; 32], [0x22; 32], [0x33; 32])
    }

    fn package(state: &DistributedTensorCodeword) -> CollaborativeRoundProverData {
        publish_collaborative_round(context(), state, 2).unwrap()
    }

    fn all_openings(
        package: &CollaborativeRoundProverData,
        state: &DistributedTensorCodeword,
    ) -> Vec<PartyRoundOpening> {
        (0..state.shape().party_count())
            .map(|party| {
                package
                    .open_party_row(state, PartyIndex::new(party))
                    .unwrap()
            })
            .collect()
    }

    fn honest_transition() -> (
        DistributedTensorCodeword,
        CollaborativeRoundProverData,
        Vec<PartyRoundOpening>,
        CollaborativeRoundProverData,
    ) {
        let current_state = state();
        let current = package(&current_state);
        let openings = all_openings(&current, &current_state);
        let next_rows = openings
            .iter()
            .map(|opening| verify_party_opening_then_fold(current.published(), opening).unwrap())
            .collect();
        let next_state =
            DistributedTensorCodeword::from_party_rows(shape(), 1, 4, next_rows).unwrap();
        let next = package(&next_state);
        (current_state, current, openings, next)
    }

    #[test]
    fn exact_openings_fold_and_commit_the_centralized_next_round() {
        let (current_state, current, openings, next) = honest_transition();
        let verified =
            verify_collaborative_round_transition(current.published(), &openings, next.published())
                .unwrap();

        let centralized_initial = centralized_tensor_encode(shape(), &message()).unwrap();
        assert_eq!(current_state.recombine().unwrap(), centralized_initial);
        let centralized_next = fold_recombined_reference(
            &centralized_initial,
            &current.published().manifest().challenge(),
        )
        .unwrap();
        assert_eq!(verified.next_state().recombine().unwrap(), centralized_next);
        assert_eq!(
            verified.next_state().state_digest(),
            next.published().manifest().published_state_digest()
        );
    }

    #[test]
    fn wrong_row_and_wrong_logical_index_are_rejected_before_fold() {
        let (_state, current, mut openings, _next) = honest_transition();
        openings[0].row = PartyEncodedRow::from_untrusted(PartyIndex::new(0), {
            let mut values = openings[0].row.values().to_vec();
            values[0] += BabyBear::ONE;
            values
        });
        assert_eq!(
            verify_party_opening_then_fold(current.published(), &openings[0]).unwrap_err(),
            CollaborativeBasefoldMmcsError::OpenedRowMismatch { party: 0 }
        );

        let (_state, current, mut openings, _next) = honest_transition();
        openings[0].opening = openings[1].opening.clone();
        assert!(matches!(
            verify_party_opening_then_fold(current.published(), &openings[0]),
            Err(CollaborativeBasefoldMmcsError::PackedMerkle(
                PackedInterleavedError::OpeningIndexMismatch { .. }
            ))
        ));
    }

    #[test]
    fn authentication_path_from_another_tree_is_rejected() {
        let (current_state, current, mut openings, _next) = honest_transition();
        let mut changed_rows = current_state.party_rows().to_vec();
        changed_rows[3] = PartyEncodedRow::from_untrusted(PartyIndex::new(3), {
            let mut values = changed_rows[3].values().to_vec();
            values[0] += BabyBear::ONE;
            values
        });
        let changed_state =
            DistributedTensorCodeword::from_party_rows(shape(), 0, 8, changed_rows).unwrap();
        let other_tree = package(&changed_state);
        let other_opening = other_tree
            .open_party_row(&changed_state, PartyIndex::new(0))
            .unwrap();
        // Party zero's leaf is unchanged, so only the path/root binding differs.
        assert_eq!(other_opening.row, openings[0].row);
        openings[0].opening = other_opening.opening;
        assert!(matches!(
            verify_party_opening_then_fold(current.published(), &openings[0]),
            Err(CollaborativeBasefoldMmcsError::PackedMerkle(
                PackedInterleavedError::PhysicalOpeningRejected(_)
            ))
        ));
    }

    #[test]
    fn layout_session_roster_round_and_challenge_are_bound() {
        let (_state, current, openings, _next) = honest_transition();

        let mut wrong_layout = current.published().clone();
        wrong_layout.manifest.packed_layout = PackedInterleavedLayout::new(4, 4, vec![8]).unwrap();
        assert_eq!(
            verify_party_opening_then_fold(&wrong_layout, &openings[0]).unwrap_err(),
            CollaborativeBasefoldMmcsError::CommitmentLayoutMismatch
        );

        let mut wrong_session = current.published().clone();
        wrong_session.manifest.context.session_digest = [0x44; 32];
        assert_eq!(
            verify_party_opening_then_fold(&wrong_session, &openings[0]).unwrap_err(),
            CollaborativeBasefoldMmcsError::ManifestChallengeMismatch
        );

        let mut wrong_relation = current.published().clone();
        wrong_relation.manifest.context.semantic_relation_digest = [0x45; 32];
        assert_eq!(
            verify_party_opening_then_fold(&wrong_relation, &openings[0]).unwrap_err(),
            CollaborativeBasefoldMmcsError::ManifestChallengeMismatch
        );

        let mut wrong_roster = current.published().clone();
        wrong_roster.manifest.context.roster_digest = [0x55; 32];
        assert_eq!(
            verify_party_opening_then_fold(&wrong_roster, &openings[0]).unwrap_err(),
            CollaborativeBasefoldMmcsError::ManifestChallengeMismatch
        );

        let mut wrong_round = current.published().clone();
        wrong_round.manifest.round = 1;
        assert!(matches!(
            verify_party_opening_then_fold(&wrong_round, &openings[0]),
            Err(CollaborativeBasefoldMmcsError::ManifestRoundGeometryMismatch { .. })
        ));

        let alternate = publish_collaborative_round(
            CollaborativeRoundContext::new([0x11; 32], [0xaa; 32], [0x33; 32]),
            &state(),
            2,
        )
        .unwrap();
        let mut wrong_challenge = current.published().clone();
        wrong_challenge.manifest.challenge = alternate.published().manifest().challenge();
        assert_eq!(
            verify_party_opening_then_fold(&wrong_challenge, &openings[0]).unwrap_err(),
            CollaborativeBasefoldMmcsError::ManifestChallengeMismatch
        );

        let mut wrong_root = current.published().clone();
        wrong_root.manifest.row_commitment_root[0] ^= 1;
        assert_eq!(
            verify_party_opening_then_fold(&wrong_root, &openings[0]).unwrap_err(),
            CollaborativeBasefoldMmcsError::CommitmentRootMismatch
        );
    }

    #[test]
    fn audit_digest_cannot_grind_challenge_and_exact_set_rejects_inconsistency() {
        let (_state, current, openings, next) = honest_transition();
        let honest_fold =
            verify_party_opening_then_fold(current.published(), &openings[0]).unwrap();
        let mut wrong_digest = current.published().clone();
        wrong_digest.manifest.published_state_digest = [0x5a; 32];
        wrong_digest.manifest.challenge = transcript_for_manifest(&wrong_digest.manifest)
            .challenge_for_published_digest(
                wrong_digest.manifest.shape,
                wrong_digest.manifest.round,
                wrong_digest.manifest.columns,
                wrong_digest.manifest.row_commitment_root,
            )
            .unwrap();

        // The redundant audit digest cannot change/grind the challenge.  A
        // local party can still check its committed row and obtains the exact
        // same fold; only exact-set verification can audit all-row consistency.
        assert_eq!(
            wrong_digest.manifest.challenge,
            current.published().manifest.challenge
        );
        assert_eq!(
            verify_party_opening_then_fold(&wrong_digest, &openings[0]).unwrap(),
            honest_fold
        );
        assert_eq!(
            verify_collaborative_round_transition(&wrong_digest, &openings, next.published(),)
                .unwrap_err(),
            CollaborativeBasefoldMmcsError::PublishedStateDigestMismatch
        );
    }

    #[test]
    fn omission_and_reordering_fail_exact_set_verification() {
        let (_state, current, mut openings, next) = honest_transition();
        let omitted = openings[..openings.len() - 1].to_vec();
        assert_eq!(
            verify_collaborative_round_transition(current.published(), &omitted, next.published(),)
                .unwrap_err(),
            CollaborativeBasefoldMmcsError::WrongOpeningCount {
                expected: 4,
                actual: 3,
            }
        );

        openings.swap(1, 2);
        assert_eq!(
            verify_collaborative_round_transition(
                current.published(),
                &openings,
                next.published(),
            )
            .unwrap_err(),
            CollaborativeBasefoldMmcsError::PartyOrderMismatch {
                position: 1,
                actual: 2,
            }
        );

        let (_state, current, mut duplicate, next) = honest_transition();
        duplicate[2] = duplicate[1].clone();
        assert_eq!(
            verify_collaborative_round_transition(
                current.published(),
                &duplicate,
                next.published(),
            )
            .unwrap_err(),
            CollaborativeBasefoldMmcsError::PartyOrderMismatch {
                position: 2,
                actual: 1,
            }
        );
    }

    #[test]
    fn changed_next_commitment_is_rejected() {
        let (_state, current, openings, next) = honest_transition();
        let mut wrong_next = next.published().clone();
        wrong_next.manifest.context.session_digest = [0x99; 32];
        // Keep it internally well-formed so the failure is specifically the
        // exact deterministic next-envelope comparison.
        wrong_next.manifest.challenge = transcript_for_manifest(&wrong_next.manifest)
            .challenge_for_published_digest(
                wrong_next.manifest.shape,
                wrong_next.manifest.round,
                wrong_next.manifest.columns,
                wrong_next.manifest.row_commitment_root,
            )
            .unwrap();
        assert_eq!(
            verify_collaborative_round_transition(current.published(), &openings, &wrong_next,)
                .unwrap_err(),
            CollaborativeBasefoldMmcsError::NextRoundCommitmentMismatch
        );
    }

    #[test]
    fn roster_digest_is_only_a_binding_not_an_authentication_claim() {
        let state = state();
        let caller_chosen = CollaborativeRoundContext::new([1; 32], [2; 32], [0xde; 32]);
        let publication = publish_collaborative_round(caller_chosen, &state, 2).unwrap();
        assert_eq!(
            publication.published().manifest().context().roster_digest(),
            [0xde; 32]
        );
        // Any caller can choose that value.  Its only executable property here
        // is transcript binding, tested above; no identity/authentication API exists.
    }
}
