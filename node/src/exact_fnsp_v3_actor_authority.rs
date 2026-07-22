//! Opaque durable actor/ledger authority for exact FNSP-v3 pre-execution.
//!
//! The cell-by-id index is only the post-checkpoint overlay.  Looking up an actor there therefore
//! falsely reports an untouched checkpoint cell as absent, and trusting a caller-carried `Cell`
//! merely moves the authority bug.  This module reconstructs the finalized ledger from the latest
//! full checkpoint plus the tombstone-aware commit overlay, welds it to both the live locked ledger
//! and the durable tail root, and only then releases an owned off-lock execution snapshot.
//!
//! Exact-v3 activation must install a canonical full-ledger checkpoint first.  Before the first
//! checkpoint, a commit overlay omits untouched genesis cells and can prove neither actor absence
//! nor the full ledger root; capture therefore fails with `CanonicalCheckpointUnavailable`.
//! When compaction has removed every commit row, the checkpoint root must additionally match a
//! committee-authenticated attested root at or above its height.  Checkpoint bytes do not become
//! consensus authority merely because the local database retained them.
//!
//! Capture must run while the caller holds the node-state read or write lock.  The store coordinates
//! are read on both sides of reconstruction as a second fence: a non-node writer racing the lock
//! makes capture fail instead of producing a cross-snapshot token.

use core::fmt;
use std::error::Error;

use dregg_cell::{Cell, CellId, Ledger};
use dregg_persist::{
    CellOverlayOp, ExactFnspV3StateHeadV1, PersistentStore, StoreError, StoredAttestedRoot,
    canonical_ledger_root,
};
use dregg_turn::TurnReceipt;

use crate::state::NodeStateInner;

/// Coordinates captured with the authenticated actor and full ledger image.
///
/// This value is deliberately obtainable only from the opaque authority's consuming method.  A
/// later exact preparation must require its CAS expected head, commit cursor, and receipt index to
/// agree before spending proof/executor work or publishing the resulting frame.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DurableExactFnspV3ActorCoordinates {
    actor_id: CellId,
    commit_cursor: u64,
    commit_compacted_floor: u64,
    checkpoint_height: u64,
    checkpoint_anchor_height: Option<u64>,
    checkpoint_anchor_root: Option<[u8; 32]>,
    checkpoint_anchor_seal: Option<[u8; 32]>,
    receipt_log_next_index: u64,
    receipt_log_tail_hash: Option<[u8; 32]>,
    exact_state_head: ExactFnspV3StateHeadV1,
    ledger_root: [u8; 32],
}

impl DurableExactFnspV3ActorCoordinates {
    pub(crate) const fn actor_id(self) -> CellId {
        self.actor_id
    }

    pub(crate) const fn commit_cursor(self) -> u64 {
        self.commit_cursor
    }

    pub(crate) const fn commit_compacted_floor(self) -> u64 {
        self.commit_compacted_floor
    }

    pub(crate) const fn checkpoint_height(self) -> u64 {
        self.checkpoint_height
    }

    pub(crate) const fn checkpoint_anchor_height(self) -> Option<u64> {
        self.checkpoint_anchor_height
    }

    pub(crate) const fn checkpoint_anchor_root(self) -> Option<[u8; 32]> {
        self.checkpoint_anchor_root
    }

    pub(crate) const fn receipt_log_next_index(self) -> u64 {
        self.receipt_log_next_index
    }

    pub(crate) const fn receipt_log_tail_hash(self) -> Option<[u8; 32]> {
        self.receipt_log_tail_hash
    }

    pub(crate) const fn exact_state_head(self) -> ExactFnspV3StateHeadV1 {
        self.exact_state_head
    }

    pub(crate) const fn ledger_root(self) -> [u8; 32] {
        self.ledger_root
    }

    /// Revalidate the complete coordinate key after off-lock proof/execution work.
    ///
    /// This is a read-side early refusal, not the durable writer CAS.  The finalizer must still
    /// consume the exact append/frame CAS in its one atomic transaction.
    pub(crate) fn revalidate_locked(
        self,
        locked: &NodeStateInner,
    ) -> Result<(), DurableExactFnspV3ActorAuthorityError> {
        revalidate_coordinates(&self, &locked.store, &locked.ledger)
    }
}

fn revalidate_coordinates(
    expected: &DurableExactFnspV3ActorCoordinates,
    store: &PersistentStore,
    live_ledger: &Ledger,
) -> Result<(), DurableExactFnspV3ActorAuthorityError> {
    let current = read_store_coordinates(store)?;
    if current.commit_cursor != expected.commit_cursor
        || current.commit_compacted_floor != expected.commit_compacted_floor
        || current.checkpoint_height != Some(expected.checkpoint_height)
        || current.checkpoint_anchor_height() != expected.checkpoint_anchor_height
        || current.checkpoint_anchor_root() != expected.checkpoint_anchor_root
        || current.checkpoint_anchor_seal != expected.checkpoint_anchor_seal
        || current.receipt_log_next_index != expected.receipt_log_next_index
        || current.receipt_log_tail_hash != expected.receipt_log_tail_hash
        || current.exact_state_head != expected.exact_state_head
        || canonical_ledger_root(live_ledger) != expected.ledger_root
    {
        return Err(DurableExactFnspV3ActorAuthorityError::SnapshotMoved);
    }
    Ok(())
}

/// Non-`Clone` authority for one actor in one complete finalized ledger snapshot.
///
/// There is no raw constructor.  The owned ledger may move off-lock for expensive proof/executor
/// work, while finalization remains a CAS against the captured coordinates.
pub(crate) struct DurableExactFnspV3ActorAuthority {
    actor: Cell,
    ledger: Ledger,
    coordinates: DurableExactFnspV3ActorCoordinates,
}

impl DurableExactFnspV3ActorAuthority {
    pub(crate) fn actor(&self) -> &Cell {
        &self.actor
    }

    pub(crate) fn ledger(&self) -> &Ledger {
        &self.ledger
    }

    pub(crate) const fn coordinates(&self) -> DurableExactFnspV3ActorCoordinates {
        self.coordinates
    }

    /// Consume the sole authority into the values the exact executor must retain through CAS.
    pub(crate) fn into_execution_parts(self) -> (Cell, Ledger, DurableExactFnspV3ActorCoordinates) {
        (self.actor, self.ledger, self.coordinates)
    }
}

/// Capture against a caller-held [`NodeStateInner`] lock.
///
/// Taking `&NodeStateInner` keeps this usable from both Tokio read and write guards.  Callers must
/// not retain an unguarded reference; the public `NodeState` surface exposes the inner value only
/// through those guards.
pub(crate) fn capture_durable_exact_fnsp_v3_actor(
    locked: &NodeStateInner,
    actor_id: CellId,
) -> Result<DurableExactFnspV3ActorAuthority, DurableExactFnspV3ActorAuthorityError> {
    capture_from_store_and_live_ledger(&locked.store, &locked.ledger, actor_id, |anchor| {
        checkpoint_anchor_is_authenticated(locked, anchor)
    })
}

/// Exact spends accept a checkpoint-only ledger only when the node can re-verify its root under a
/// known committee.  A structural QC, a foreign federation row, or a classical finalization vote
/// with no enrolled PQ twin is not silently promoted to authority here.
fn checkpoint_anchor_is_authenticated(
    locked: &NodeStateInner,
    anchor: &StoredAttestedRoot,
) -> bool {
    if !locked.federation_configured
        || anchor.threshold == 0
        || anchor.threshold_qc.is_some()
        || anchor.federation_id.0 != locked.federation_id
    {
        return false;
    }

    for (index, committee) in locked.derived_committee_history.iter().enumerate().rev() {
        if committee.is_empty() {
            continue;
        }
        let pq_committee = locked
            .derived_committee_ml_dsa_history
            .get(index)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        if checkpoint_anchor_is_authenticated_for_committee(anchor, committee, pq_committee) {
            return true;
        }
    }

    !locked.known_federation_keys.is_empty()
        && checkpoint_anchor_is_authenticated_for_committee(
            anchor,
            &locked.known_federation_keys,
            &locked.known_federation_ml_dsa_keys,
        )
}

fn checkpoint_anchor_is_authenticated_for_committee(
    anchor: &StoredAttestedRoot,
    committee: &[dregg_types::PublicKey],
    pq_committee: &[dregg_federation::frost::MlDsaPublicKey],
) -> bool {
    if anchor.threshold == 0 || committee.is_empty() {
        return false;
    }
    if anchor.verify_finalization_quorum(committee, pq_committee) {
        return true;
    }

    // Deliberate devnet/solo exception. `StoredAttestedRoot::verify_signatures` is classical;
    // even though the primitive now deduplicates signers, exact checkpoint authority never
    // promotes it into a multi-member substitute for the hybrid finalization quorum.
    committee.len() == 1
        && anchor.threshold == 1
        && anchor.quorum_signatures.len() == 1
        && anchor.quorum_signatures[0].0 == committee[0]
        && anchor.verify_signatures(committee)
}

fn capture_from_store_and_live_ledger(
    store: &PersistentStore,
    live_ledger: &Ledger,
    actor_id: CellId,
    checkpoint_anchor_is_authenticated: impl FnOnce(&StoredAttestedRoot) -> bool,
) -> Result<DurableExactFnspV3ActorAuthority, DurableExactFnspV3ActorAuthorityError> {
    let before = read_store_coordinates(store)?;

    let (checkpoint_height, durable_ledger) = reconstruct_durable_ledger(store)?;

    let durable_root = canonical_ledger_root(&durable_ledger);
    if before.commit_cursor > before.commit_compacted_floor {
        let tail_ordinal = before.commit_cursor - 1;
        let tail = store
            .commit_record_at(tail_ordinal)
            .map_err(DurableExactFnspV3ActorAuthorityError::Store)?
            .ok_or(DurableExactFnspV3ActorAuthorityError::CommitTailMissing {
                ordinal: tail_ordinal,
            })?;
        if tail.ledger_root != durable_root {
            return Err(
                DurableExactFnspV3ActorAuthorityError::RecoveredRootMismatch {
                    reconstructed: durable_root,
                    recorded: tail.ledger_root,
                },
            );
        }
    } else {
        let anchor = before.checkpoint_anchor.as_ref().ok_or(
            DurableExactFnspV3ActorAuthorityError::CheckpointAnchorMissing { checkpoint_height },
        )?;
        if anchor.height < checkpoint_height {
            return Err(
                DurableExactFnspV3ActorAuthorityError::CheckpointAnchorBehind {
                    checkpoint_height,
                    anchor_height: anchor.height,
                },
            );
        }
        if anchor.merkle_root != durable_root {
            return Err(
                DurableExactFnspV3ActorAuthorityError::CheckpointAnchorRootMismatch {
                    reconstructed: durable_root,
                    anchored: anchor.merkle_root,
                },
            );
        }
        if !checkpoint_anchor_is_authenticated(anchor) {
            return Err(
                DurableExactFnspV3ActorAuthorityError::CheckpointAnchorUnauthenticated {
                    anchor_height: anchor.height,
                },
            );
        }
    }

    let live_root = canonical_ledger_root(live_ledger);
    if live_root != durable_root {
        return Err(DurableExactFnspV3ActorAuthorityError::LiveRootMismatch {
            live: live_root,
            durable: durable_root,
        });
    }

    let durable_actor = durable_ledger.get(&actor_id).cloned().ok_or(
        DurableExactFnspV3ActorAuthorityError::DurableActorMissing(actor_id),
    )?;
    if live_ledger.get(&actor_id) != Some(&durable_actor) {
        return Err(DurableExactFnspV3ActorAuthorityError::LiveActorMismatch(
            actor_id,
        ));
    }

    let after = read_store_coordinates(store)?;
    if before != after || Some(checkpoint_height) != after.checkpoint_height {
        return Err(DurableExactFnspV3ActorAuthorityError::SnapshotMoved);
    }

    let coordinates = DurableExactFnspV3ActorCoordinates {
        actor_id,
        commit_cursor: after.commit_cursor,
        commit_compacted_floor: after.commit_compacted_floor,
        checkpoint_height,
        checkpoint_anchor_height: after.checkpoint_anchor_height(),
        checkpoint_anchor_root: after.checkpoint_anchor_root(),
        checkpoint_anchor_seal: after.checkpoint_anchor_seal,
        receipt_log_next_index: after.receipt_log_next_index,
        receipt_log_tail_hash: after.receipt_log_tail_hash,
        exact_state_head: after.exact_state_head,
        ledger_root: durable_root,
    };
    Ok(DurableExactFnspV3ActorAuthority {
        actor: durable_actor,
        ledger: durable_ledger,
        coordinates,
    })
}

/// Test-only mint for neighboring exact modules.  Production callers cannot bypass the
/// caller-held NodeState lock or committee authentication above.
#[cfg(test)]
pub(crate) fn capture_durable_exact_fnsp_v3_actor_for_test(
    store: &PersistentStore,
    live_ledger: &Ledger,
    actor_id: CellId,
) -> Result<DurableExactFnspV3ActorAuthority, DurableExactFnspV3ActorAuthorityError> {
    capture_from_store_and_live_ledger(store, live_ledger, actor_id, |_| true)
}

fn reconstruct_durable_ledger(
    store: &PersistentStore,
) -> Result<(u64, Ledger), DurableExactFnspV3ActorAuthorityError> {
    let (checkpoint_height, mut durable_ledger) = store
        .load_latest_ledger_checkpoint()
        .map_err(DurableExactFnspV3ActorAuthorityError::Store)?
        .ok_or(DurableExactFnspV3ActorAuthorityError::CanonicalCheckpointUnavailable)?;
    for operation in store
        .cell_overlay_since(checkpoint_height)
        .map_err(DurableExactFnspV3ActorAuthorityError::Store)?
    {
        apply_overlay(&mut durable_ledger, operation)?;
    }
    Ok((checkpoint_height, durable_ledger))
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct StoreCoordinates {
    commit_cursor: u64,
    commit_compacted_floor: u64,
    checkpoint_height: Option<u64>,
    checkpoint_anchor: Option<StoredAttestedRoot>,
    checkpoint_anchor_seal: Option<[u8; 32]>,
    receipt_log_next_index: u64,
    receipt_log_tail_hash: Option<[u8; 32]>,
    exact_state_head: ExactFnspV3StateHeadV1,
}

impl StoreCoordinates {
    fn checkpoint_anchor_height(&self) -> Option<u64> {
        self.checkpoint_anchor.as_ref().map(|anchor| anchor.height)
    }

    fn checkpoint_anchor_root(&self) -> Option<[u8; 32]> {
        self.checkpoint_anchor
            .as_ref()
            .map(|anchor| anchor.merkle_root)
    }
}

fn read_store_coordinates(
    store: &PersistentStore,
) -> Result<StoreCoordinates, DurableExactFnspV3ActorAuthorityError> {
    let commit_cursor = store
        .commit_cursor()
        .map_err(DurableExactFnspV3ActorAuthorityError::Store)?;
    let commit_compacted_floor = store
        .commit_compacted_floor()
        .map_err(DurableExactFnspV3ActorAuthorityError::Store)?;
    if commit_compacted_floor > commit_cursor {
        return Err(
            DurableExactFnspV3ActorAuthorityError::CompactionFloorAhead {
                floor: commit_compacted_floor,
                cursor: commit_cursor,
            },
        );
    }
    let checkpoint_height = Some(
        store
            .latest_ledger_checkpoint_height()
            .map_err(DurableExactFnspV3ActorAuthorityError::Store)?,
    );
    let (checkpoint_anchor, checkpoint_anchor_seal) = if commit_cursor == commit_compacted_floor {
        let anchor = store
            .latest_attested_root()
            .map_err(DurableExactFnspV3ActorAuthorityError::Store)?;
        let seal = anchor
            .as_ref()
            .map(|anchor| {
                postcard::to_stdvec(anchor)
                    .map(|wire| *blake3::hash(&wire).as_bytes())
                    .map_err(|error| {
                        DurableExactFnspV3ActorAuthorityError::CheckpointAnchorEncoding(
                            error.to_string(),
                        )
                    })
            })
            .transpose()?;
        (anchor, seal)
    } else {
        // The live commit tail is the authenticated canonical-root coordinate.  Attested-root
        // quorum backfill is allowed to advance independently without invalidating an off-lock
        // exact proof over the unchanged ledger/exact state.
        (None, None)
    };
    let (receipt_log_next_index, receipt_tail) = store
        .receipt_chain_head()
        .map_err(DurableExactFnspV3ActorAuthorityError::Store)?;
    let receipt_log_tail_hash = receipt_tail
        .as_deref()
        .map(|encoded| {
            postcard::from_bytes::<TurnReceipt>(encoded)
                .map(|receipt| receipt.receipt_hash())
                .map_err(|error| {
                    DurableExactFnspV3ActorAuthorityError::ReceiptDecode(error.to_string())
                })
        })
        .transpose()?;
    let exact_state_head = store
        .exact_fnsp_v3_state_head()
        .map_err(DurableExactFnspV3ActorAuthorityError::Store)?
        .ok_or(DurableExactFnspV3ActorAuthorityError::ExactStateMissing)?;
    Ok(StoreCoordinates {
        commit_cursor,
        commit_compacted_floor,
        checkpoint_height,
        checkpoint_anchor,
        checkpoint_anchor_seal,
        receipt_log_next_index,
        receipt_log_tail_hash,
        exact_state_head,
    })
}

fn apply_overlay(
    ledger: &mut Ledger,
    operation: CellOverlayOp,
) -> Result<(), DurableExactFnspV3ActorAuthorityError> {
    match operation {
        CellOverlayOp::Upsert(cell) => {
            let id = cell.id();
            let _ = ledger.remove(&id);
            ledger.insert_cell(cell).map_err(|error| {
                DurableExactFnspV3ActorAuthorityError::OverlayApply(error.to_string())
            })?;
        }
        CellOverlayOp::Remove(id) => {
            let _ = ledger.remove(&id);
        }
    }
    Ok(())
}

#[derive(Debug)]
pub(crate) enum DurableExactFnspV3ActorAuthorityError {
    Store(StoreError),
    CanonicalCheckpointUnavailable,
    CheckpointAnchorEncoding(String),
    CheckpointAnchorMissing {
        checkpoint_height: u64,
    },
    CheckpointAnchorBehind {
        checkpoint_height: u64,
        anchor_height: u64,
    },
    CheckpointAnchorRootMismatch {
        reconstructed: [u8; 32],
        anchored: [u8; 32],
    },
    CheckpointAnchorUnauthenticated {
        anchor_height: u64,
    },
    ExactStateMissing,
    ReceiptDecode(String),
    OverlayApply(String),
    CompactionFloorAhead {
        floor: u64,
        cursor: u64,
    },
    CommitTailMissing {
        ordinal: u64,
    },
    RecoveredRootMismatch {
        reconstructed: [u8; 32],
        recorded: [u8; 32],
    },
    LiveRootMismatch {
        live: [u8; 32],
        durable: [u8; 32],
    },
    DurableActorMissing(CellId),
    LiveActorMismatch(CellId),
    SnapshotMoved,
}

struct Hex32<'a>(&'a [u8; 32]);

impl fmt::Display for Hex32<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in self.0 {
            write!(f, "{byte:02x}")?;
        }
        Ok(())
    }
}

impl fmt::Display for DurableExactFnspV3ActorAuthorityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Store(error) => write!(f, "durable exact actor store read failed: {error}"),
            Self::CanonicalCheckpointUnavailable => f.write_str(
                "exact actor authority requires a canonical full-ledger checkpoint; overlay-only genesis is incomplete",
            ),
            Self::CheckpointAnchorEncoding(error) => write!(
                f,
                "exact actor checkpoint anchor failed canonical encoding: {error}"
            ),
            Self::CheckpointAnchorMissing { checkpoint_height } => write!(
                f,
                "fully compacted checkpoint at height {checkpoint_height} has no attested canonical ledger-root anchor",
            ),
            Self::CheckpointAnchorBehind {
                checkpoint_height,
                anchor_height,
            } => write!(
                f,
                "latest attested ledger-root anchor height {anchor_height} is behind checkpoint height {checkpoint_height}",
            ),
            Self::CheckpointAnchorRootMismatch {
                reconstructed,
                anchored,
            } => write!(
                f,
                "checkpoint root {} differs from attested canonical ledger root {}",
                Hex32(reconstructed),
                Hex32(anchored),
            ),
            Self::CheckpointAnchorUnauthenticated { anchor_height } => write!(
                f,
                "checkpoint-only ledger root at height {anchor_height} has no cryptographically verified committee anchor",
            ),
            Self::ExactStateMissing => f.write_str("exact FNSP-v3 durable state is not initialized"),
            Self::ReceiptDecode(error) => {
                write!(f, "durable receipt-log tail failed canonical decode: {error}")
            }
            Self::OverlayApply(error) => {
                write!(f, "durable ledger overlay could not be applied: {error}")
            }
            Self::CompactionFloorAhead { floor, cursor } => write!(
                f,
                "durable commit compaction floor {floor} exceeds cursor {cursor}",
            ),
            Self::CommitTailMissing { ordinal } => {
                write!(f, "durable commit tail row {ordinal} is missing")
            }
            Self::RecoveredRootMismatch {
                reconstructed,
                recorded,
            } => write!(
                f,
                "checkpoint plus overlay root {} differs from durable tail root {}",
                Hex32(reconstructed),
                Hex32(recorded),
            ),
            Self::LiveRootMismatch { live, durable } => write!(
                f,
                "locked live ledger root {} differs from durable reconstructed root {}",
                Hex32(live),
                Hex32(durable),
            ),
            Self::DurableActorMissing(actor) => {
                write!(f, "actor {actor} is absent from the durable finalized ledger")
            }
            Self::LiveActorMismatch(actor) => write!(
                f,
                "actor {actor} differs between locked live and durable finalized ledgers",
            ),
            Self::SnapshotMoved => {
                f.write_str("durable exact actor coordinates changed during capture")
            }
        }
    }
}

impl Error for DurableExactFnspV3ActorAuthorityError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Store(error) => Some(error),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_persist::CommitRecord;
    use tempfile::tempdir;

    fn actor(seed: u8, balance: u64) -> Cell {
        let mut cell = Cell::new([seed; 32], [seed.wrapping_add(1); 32]);
        cell.state.set_balance(balance);
        cell
    }

    fn ledger_with(cell: Cell) -> Ledger {
        let mut ledger = Ledger::new();
        ledger.insert_cell(cell).expect("insert actor");
        ledger
    }

    fn initialize_exact(store: &PersistentStore) {
        store
            .initialize_exact_fnsp_v3_state_from_faithful_nullifiers()
            .expect("initialize exact state");
    }

    /// The production entry independently verifies this row against the configured committee.
    /// Unit tests exercise the storage/root topology through the injected authentication verdict.
    fn store_checkpoint_anchor(store: &PersistentStore, height: u64, ledger: &Ledger) {
        store
            .store_attested_root(&StoredAttestedRoot {
                merkle_root: canonical_ledger_root(ledger),
                note_tree_root: None,
                nullifier_set_root: None,
                height,
                timestamp: 0,
                blocklace_block_id: Some([height as u8; 32]),
                finality_round: Some(height),
                quorum_signatures: Vec::new(),
                threshold_qc: None,
                threshold: 1,
                federation_id: dregg_types::FederationId([0xF3; 32]),
                receipt_stream_root: None,
                finalization_quorum: Vec::new(),
            })
            .expect("checkpoint root anchor");
    }

    fn signed_classical_anchor(
        signing_key: &dregg_types::SigningKey,
        threshold: usize,
    ) -> StoredAttestedRoot {
        let federation_id = dregg_types::FederationId([0xF3; 32]);
        let public_key = signing_key.public_key();
        let root = dregg_types::AttestedRoot {
            merkle_root: [0xA5; 32],
            note_tree_root: None,
            nullifier_set_root: None,
            height: 5,
            timestamp: 0,
            blocklace_block_id: Some([0xB5; 32]),
            finality_round: Some(5),
            quorum_signatures: Vec::new(),
            threshold_qc: None,
            threshold,
            federation_id,
            receipt_stream_root: None,
            hybrid_quorum: Vec::new(),
        };
        let signature = dregg_types::sign(signing_key, &root.signing_message());
        StoredAttestedRoot {
            merkle_root: root.merkle_root,
            note_tree_root: root.note_tree_root,
            nullifier_set_root: root.nullifier_set_root,
            height: root.height,
            timestamp: root.timestamp,
            blocklace_block_id: root.blocklace_block_id,
            finality_round: root.finality_round,
            quorum_signatures: vec![(public_key, signature)],
            threshold_qc: None,
            threshold,
            federation_id,
            receipt_stream_root: None,
            finalization_quorum: Vec::new(),
        }
    }

    #[test]
    fn duplicate_classical_signer_cannot_mint_checkpoint_authority() {
        let signer = dregg_types::SigningKey::from_bytes(&[0x11; 32]);
        let other = dregg_types::SigningKey::from_bytes(&[0x22; 32]);
        let mut anchor = signed_classical_anchor(&signer, 2);
        anchor.quorum_signatures.push(anchor.quorum_signatures[0]);
        let committee = [signer.public_key(), other.public_key()];

        assert!(
            !anchor.verify_signatures(&committee),
            "the persistence primitive must independently reject duplicate identities"
        );
        assert!(
            !checkpoint_anchor_is_authenticated_for_committee(&anchor, &committee, &[]),
            "exact checkpoint authority must not inherit duplicate classical counting"
        );
    }

    #[test]
    fn deliberate_solo_classical_anchor_remains_available() {
        let signer = dregg_types::SigningKey::from_bytes(&[0x33; 32]);
        let anchor = signed_classical_anchor(&signer, 1);
        assert!(checkpoint_anchor_is_authenticated_for_committee(
            &anchor,
            &[signer.public_key()],
            &[]
        ));
    }

    fn commit_record(
        store: &PersistentStore,
        height: u64,
        post: &Ledger,
        touched_cells: Vec<Cell>,
        removed: Vec<[u8; 32]>,
    ) {
        let ordinal = store.commit_cursor().expect("cursor");
        store
            .commit_finalized_turn(
                ordinal,
                &CommitRecord {
                    ordinal,
                    height,
                    block_id: [height as u8; 32],
                    block_executed_up_to: height,
                    turn_hash: [height.wrapping_add(1) as u8; 32],
                    creator: [height.wrapping_add(2) as u8; 32],
                    receipt_hash: [height.wrapping_add(3) as u8; 32],
                    ledger_root: canonical_ledger_root(post),
                    touched_cells,
                    removed,
                },
            )
            .expect("commit record");
    }

    #[test]
    fn checkpoint_actor_mints_owned_authority_with_exact_coordinates() {
        let store = PersistentStore::open_in_memory().expect("store");
        let cell = actor(1, 10);
        let ledger = ledger_with(cell.clone());
        store.checkpoint_ledger(&ledger, 0).expect("checkpoint");
        store_checkpoint_anchor(&store, 0, &ledger);
        initialize_exact(&store);

        let authority = capture_from_store_and_live_ledger(&store, &ledger, cell.id(), |_| true)
            .expect("durable actor authority");
        assert_eq!(authority.actor(), &cell);
        assert_eq!(authority.coordinates().actor_id(), cell.id());
        assert_eq!(authority.coordinates().commit_cursor(), 0);
        assert_eq!(authority.coordinates().receipt_log_next_index(), 0);
        assert_eq!(authority.coordinates().receipt_log_tail_hash(), None);
        assert_eq!(authority.coordinates().checkpoint_height(), 0);
        assert_eq!(
            authority.coordinates().ledger_root(),
            canonical_ledger_root(&ledger)
        );
    }

    #[test]
    fn overlay_only_genesis_refuses_without_full_checkpoint() {
        let store = PersistentStore::open_in_memory().expect("store");
        let cell = actor(9, 90);
        let ledger = ledger_with(cell.clone());
        initialize_exact(&store);

        assert!(matches!(
            capture_from_store_and_live_ledger(&store, &ledger, cell.id(), |_| true),
            Err(DurableExactFnspV3ActorAuthorityError::CanonicalCheckpointUnavailable)
        ));
    }

    #[test]
    fn checkpoint_only_state_refuses_without_attested_root_anchor() {
        let store = PersistentStore::open_in_memory().expect("store");
        let cell = actor(10, 100);
        let ledger = ledger_with(cell.clone());
        store.checkpoint_ledger(&ledger, 0).expect("checkpoint");
        initialize_exact(&store);

        assert!(matches!(
            capture_from_store_and_live_ledger(&store, &ledger, cell.id(), |_| true),
            Err(
                DurableExactFnspV3ActorAuthorityError::CheckpointAnchorMissing {
                    checkpoint_height: 0
                }
            )
        ));
    }

    #[test]
    fn fully_compacted_checkpoint_uses_matching_attested_root() {
        let store = PersistentStore::open_in_memory().expect("store");
        let cell = actor(11, 110);
        let ledger = ledger_with(cell.clone());
        store.checkpoint_ledger(&Ledger::new(), 0).expect("base");
        commit_record(&store, 1, &ledger, vec![cell.clone()], Vec::new());
        store
            .checkpoint_ledger(&ledger, 2)
            .expect("covering checkpoint");
        store_checkpoint_anchor(&store, 2, &ledger);
        initialize_exact(&store);

        assert_eq!(store.commit_cursor().expect("cursor"), 1);
        assert_eq!(store.commit_compacted_floor().expect("floor"), 1);
        assert!(store.commit_record_at(0).expect("tail read").is_none());

        let authority = capture_from_store_and_live_ledger(&store, &ledger, cell.id(), |_| true)
            .expect("attested compacted checkpoint authority");
        assert_eq!(authority.actor(), &cell);
        assert_eq!(authority.coordinates().checkpoint_height(), 2);
        assert_eq!(authority.coordinates().checkpoint_anchor_height(), Some(2));
        assert_eq!(
            authority.coordinates().checkpoint_anchor_root(),
            Some(canonical_ledger_root(&ledger))
        );
    }

    #[test]
    fn locked_live_store_drift_refuses() {
        let store = PersistentStore::open_in_memory().expect("store");
        let cell = actor(2, 20);
        let durable = ledger_with(cell.clone());
        store.checkpoint_ledger(&durable, 0).expect("checkpoint");
        store_checkpoint_anchor(&store, 0, &durable);
        initialize_exact(&store);

        let live = ledger_with(actor(2, 21));
        assert!(matches!(
            capture_from_store_and_live_ledger(&store, &live, cell.id(), |_| true),
            Err(DurableExactFnspV3ActorAuthorityError::LiveRootMismatch { .. })
        ));
    }

    #[test]
    fn missing_and_tombstoned_actor_refuse() {
        let store = PersistentStore::open_in_memory().expect("store");
        let cell = actor(3, 30);
        let before = ledger_with(cell.clone());
        store.checkpoint_ledger(&before, 0).expect("checkpoint");
        store_checkpoint_anchor(&store, 0, &before);
        initialize_exact(&store);

        let unknown = actor(4, 40).id();
        assert!(matches!(
            capture_from_store_and_live_ledger(&store, &before, unknown, |_| true),
            Err(DurableExactFnspV3ActorAuthorityError::DurableActorMissing(id)) if id == unknown
        ));

        let after = Ledger::new();
        commit_record(&store, 1, &after, Vec::new(), vec![cell.id().0]);
        assert!(matches!(
            capture_from_store_and_live_ledger(&store, &after, cell.id(), |_| true),
            Err(DurableExactFnspV3ActorAuthorityError::DurableActorMissing(id)) if id == cell.id()
        ));
    }

    #[test]
    fn restart_replays_checkpoint_plus_overlay_before_minting() {
        let dir = tempdir().expect("tempdir");
        let path = dir.path().join("actor-authority.redb");
        let before_cell = actor(5, 50);
        let before = ledger_with(before_cell.clone());
        let mut after_cell = before_cell.clone();
        after_cell.state.set_balance(55);
        let after = ledger_with(after_cell.clone());
        {
            let store = PersistentStore::open(&path).expect("store");
            store.checkpoint_ledger(&before, 0).expect("checkpoint");
            initialize_exact(&store);
            commit_record(&store, 1, &after, vec![after_cell.clone()], Vec::new());
        }

        let reopened = PersistentStore::open(&path).expect("reopen");
        let authority =
            capture_from_store_and_live_ledger(&reopened, &after, after_cell.id(), |_| true)
                .expect("restarted authority");
        assert_eq!(authority.actor(), &after_cell);
        assert_eq!(authority.coordinates().commit_cursor(), 1);
        assert_eq!(authority.coordinates().checkpoint_height(), 0);
        assert_eq!(authority.coordinates().exact_state_head().generation(), 0);
        store_checkpoint_anchor(&reopened, 1, &after);
        revalidate_coordinates(&authority.coordinates(), &reopened, &after)
            .expect("tail-backed coordinates ignore attested-root quorum backfill");
        let (owned_actor, owned_ledger, coordinates) = authority.into_execution_parts();
        assert_eq!(owned_actor, after_cell);
        assert_eq!(
            canonical_ledger_root(&owned_ledger),
            coordinates.ledger_root()
        );
    }
}
