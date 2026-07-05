//! Federation state persistent storage.
//!
//! Persists the revocation set (which token IDs have been revoked) and the
//! attested roots (consensus-signed Merkle roots at each block height).
//!
//! The revocation set is stored as individual key-value pairs for O(1) lookup.
//! Attested roots are stored indexed by height for ordered retrieval.

use redb::{ReadableTable, ReadableTableMetadata};
use serde::{Deserialize, Serialize};

use crate::tables;
use crate::{PersistentStore, Result, StoreError};

pub use dregg_types::{FederationId, PublicKey, Signature, ThresholdQC};

/// A stored attested root, capturing the federation's consensus state at a
/// particular block height.
///
/// Uses the canonical `dregg_types::PublicKey` (32 bytes) and
/// `dregg_types::Signature` (64 bytes) for correct Ed25519 representation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StoredAttestedRoot {
    /// The Merkle root of the revocation tree (cell state).
    pub merkle_root: [u8; 32],
    /// The note commitment tree root.
    #[serde(default)]
    pub note_tree_root: Option<[u8; 32]>,
    /// The nullifier set root.
    #[serde(default)]
    pub nullifier_set_root: Option<[u8; 32]>,
    /// The block height at which this root was agreed upon.
    pub height: u64,
    /// Unix timestamp (seconds) when finalized.
    pub timestamp: i64,
    /// The blocklace block id this attestation is anchored to.
    /// `None` for legacy roots; production roots from the live node carry it.
    #[serde(default)]
    pub blocklace_block_id: Option<[u8; 32]>,
    /// The Cordial Miners finality round at the anchoring block.
    #[serde(default)]
    pub finality_round: Option<u64>,
    /// Quorum signatures: Vec of (public_key, signature) with FULL 64-byte sigs.
    pub quorum_signatures: Vec<(PublicKey, Signature)>,
    /// Optional threshold aggregate QC (serialized BLS).
    pub threshold_qc: Option<ThresholdQC>,
    /// The number of signatures required for validity.
    pub threshold: usize,
    /// The federation id this attestation is produced by (v3 binding).
    /// `FederationId::PLACEHOLDER` for legacy roots produced before v3.
    #[serde(default)]
    pub federation_id: FederationId,
    /// v4 (#80): Merkle root over the canonical `receipt_hash()` of every
    /// receipt this attestation covers. `None` for legacy roots predating
    /// the receipt-stream binding. See `dregg_types::AttestedRoot`.
    #[serde(default)]
    pub receipt_stream_root: Option<[u8; 32]>,
    /// N3 committee-restart fix (Fix B): the assembled quorum of committee
    /// **finalization votes** over this root's `(blocklace_block_id,
    /// merkle_root)` — each pair a distinct committee member's Ed25519 signature
    /// over [`dregg_types::finalization_vote_signing_message`].
    ///
    /// This is the record that lets a FULL-MODE committee node restart cleanly.
    /// `quorum_signatures` carries the local node's signature over the full
    /// `signing_message()` preimage (the light-client attestation); a full-mode
    /// node only ever holds ONE such local signature synchronously, so on its
    /// own it is `1 < threshold` and cannot re-anchor. `finalization_quorum`
    /// instead accumulates the >=threshold cross-node vote signatures (which
    /// arrive async over gossip and are back-filled here as the quorum forms),
    /// verified on restart by [`Self::verify_finalization_quorum`]. Empty for
    /// legacy roots and for a freshly persisted head whose vote quorum has not
    /// yet assembled (the anchor recovers to the last quorum-carrying root).
    #[serde(default)]
    pub finalization_quorum: Vec<(PublicKey, Signature)>,
}

impl StoredAttestedRoot {
    /// Check structural completeness only (QC present, threshold count met).
    ///
    /// Does NOT verify signatures. For trusted verification, use
    /// [`verify_signatures`](Self::verify_signatures) with the committee keys.
    pub fn is_structurally_complete(&self) -> bool {
        if self.threshold_qc.is_some() {
            return true;
        }
        self.quorum_signatures.len() >= self.threshold
    }

    /// Deprecated alias for [`is_structurally_complete`](Self::is_structurally_complete).
    #[deprecated(
        note = "Use is_structurally_complete() (count-only) or verify_signatures() for cryptographic verification"
    )]
    pub fn is_valid(&self) -> bool {
        self.is_structurally_complete()
    }

    /// Verify signatures cryptographically against a set of known committee keys.
    ///
    /// Checks that the threshold count is met AND each signature verifies against
    /// the corresponding public key in `committee`.
    pub fn verify_signatures(&self, committee: &[PublicKey]) -> bool {
        if self.quorum_signatures.len() < self.threshold {
            return false;
        }
        let message = self.signing_message();
        for (pk, sig) in &self.quorum_signatures {
            if !committee.contains(pk) {
                return false;
            }
            if !pk.verify(&message, sig) {
                return false;
            }
        }
        true
    }

    /// Does this root carry a (non-empty) finalization-vote quorum record?
    ///
    /// Distinguishes a genuinely-unsigned/trailing head (empty — the vote
    /// quorum has not assembled yet, which the restart anchor treats as
    /// "not yet anchored", NOT as forgery) from a root that CLAIMS a quorum
    /// (non-empty — which must then verify or the root is rejected as forged).
    pub fn has_finalization_quorum(&self) -> bool {
        !self.finalization_quorum.is_empty()
    }

    /// Verify the assembled committee **finalization-vote** quorum
    /// (`finalization_quorum`) — the N3 committee-restart anchor (Fix B).
    ///
    /// Returns `true` only when ALL of:
    ///   * this root is anchored to a blocklace block (`blocklace_block_id` is
    ///     `Some` — the vote preimage binds it);
    ///   * every `(voter, sig)` is a committee member's valid Ed25519 signature
    ///     over [`dregg_types::finalization_vote_signing_message`] for THIS
    ///     root's `(blocklace_block_id, merkle_root)` — a signature over any
    ///     other root or block does not count;
    ///   * the number of **distinct** valid committee signers is `>= threshold`
    ///     (an equivocating/duplicated voter counts at most once, so a single
    ///     member cannot inflate the quorum).
    ///
    /// This never accepts a root without a genuine >=threshold committee quorum
    /// over the exact finalized state — it closes the liveness fail-close
    /// WITHOUT relaxing the soundness bar.
    pub fn verify_finalization_quorum(&self, committee: &[PublicKey]) -> bool {
        let Some(block_id) = self.blocklace_block_id else {
            return false;
        };
        if self.finalization_quorum.len() < self.threshold {
            return false;
        }
        let message = dregg_types::finalization_vote_signing_message(&block_id, &self.merkle_root);
        let mut distinct: std::collections::HashSet<[u8; 32]> = std::collections::HashSet::new();
        for (pk, sig) in &self.finalization_quorum {
            if !committee.contains(pk) {
                return false;
            }
            if !pk.verify(&message, sig) {
                return false;
            }
            distinct.insert(pk.0);
        }
        distinct.len() >= self.threshold
    }

    /// Does at least one committee-member signature validly bind THIS root's
    /// `merkle_root` — from EITHER the light-client `quorum_signatures` (over
    /// `signing_message`) OR the `finalization_quorum` (over the
    /// finalization-vote message)?
    ///
    /// This is weaker than a quorum (a single valid signature suffices) and is
    /// used ONLY for the restart tamper-check: even when a full committee quorum
    /// has not yet assembled for a trailing head, a ledger recovered to a root
    /// that does NOT match any self/committee-signed root must still be refused.
    /// It preserves the merkle_root-binding integrity the lone local signature
    /// provides, without treating that lone signature as a quorum anchor.
    pub fn has_any_valid_committee_signature(&self, committee: &[PublicKey]) -> bool {
        let full_msg = self.signing_message();
        for (pk, sig) in &self.quorum_signatures {
            if committee.contains(pk) && pk.verify(&full_msg, sig) {
                return true;
            }
        }
        if let Some(block_id) = self.blocklace_block_id {
            let vote_msg =
                dregg_types::finalization_vote_signing_message(&block_id, &self.merkle_root);
            for (pk, sig) in &self.finalization_quorum {
                if committee.contains(pk) && pk.verify(&vote_msg, sig) {
                    return true;
                }
            }
        }
        false
    }

    /// Compute the canonical message that was signed for this attested root.
    ///
    /// Mirrors [`dregg_types::AttestedRoot::signing_message`] (v3): includes
    /// `federation_id`, `note_tree_root`, `nullifier_set_root`,
    /// `blocklace_block_id`, and `finality_round` with `0x00 | 0x01 || value`
    /// framing for unambiguous `Option` encoding.
    ///
    /// `pub(crate)` so the recovery-anchor diagnosis test can reconstruct the
    /// exact bytes a genuine committee quorum must sign (see
    /// `tests::full_mode_single_sig_root_is_refused_genuine_quorum_accepted`).
    pub(crate) fn signing_message(&self) -> Vec<u8> {
        let mut msg = Vec::new();
        // v5 (N3 committee-restart fix): the wall-clock `timestamp` is DROPPED
        // from the signed preimage so the root's preimage is deterministic
        // across the committee. Mirrors `dregg_types::AttestedRoot::signing_message`.
        msg.extend_from_slice(b"dregg-attested-root-v5");
        msg.extend_from_slice(&self.federation_id.0);
        msg.extend_from_slice(&self.merkle_root);
        match self.note_tree_root {
            Some(ref r) => {
                msg.push(0x01);
                msg.extend_from_slice(r);
            }
            None => msg.push(0x00),
        }
        match self.nullifier_set_root {
            Some(ref r) => {
                msg.push(0x01);
                msg.extend_from_slice(r);
            }
            None => msg.push(0x00),
        }
        msg.extend_from_slice(&self.height.to_le_bytes());
        // NOTE (v5): `timestamp` is intentionally NOT mixed in (determinism).
        match self.blocklace_block_id {
            Some(ref id) => {
                msg.push(0x01);
                msg.extend_from_slice(id);
            }
            None => msg.push(0x00),
        }
        match self.finality_round {
            Some(round) => {
                msg.push(0x01);
                msg.extend_from_slice(&round.to_le_bytes());
            }
            None => msg.push(0x00),
        }
        // v4 (#80): receipt_stream_root with 0x00 / 0x01||32-byte framing.
        match self.receipt_stream_root {
            Some(ref r) => {
                msg.push(0x01);
                msg.extend_from_slice(r);
            }
            None => msg.push(0x00),
        }
        msg
    }

    /// Short hex of the Merkle root for display.
    pub fn root_hex(&self) -> String {
        self.merkle_root
            .iter()
            .take(4)
            .map(|b| format!("{b:02x}"))
            .collect()
    }
}

impl PersistentStore {
    // =========================================================================
    // Revocation Storage
    // =========================================================================

    /// Store a revocation for a token ID.
    ///
    /// Records the current time as the revocation timestamp.
    /// Idempotent: re-revoking an already-revoked token is a no-op.
    pub fn store_revocation(&self, token_id: &str) -> Result<()> {
        let timestamp = current_timestamp();
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::REVOCATIONS)?;
            // Only insert if not already present (idempotent).
            if table.get(token_id)?.is_none() {
                table.insert(token_id, timestamp)?;
            }
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Store a revocation with an explicit timestamp.
    pub fn store_revocation_at(&self, token_id: &str, timestamp: i64) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::REVOCATIONS)?;
            if table.get(token_id)?.is_none() {
                table.insert(token_id, timestamp)?;
            }
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Check whether a token ID has been revoked.
    pub fn is_revoked(&self, token_id: &str) -> Result<bool> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::REVOCATIONS)?;
        Ok(table.get(token_id)?.is_some())
    }

    /// Get the timestamp when a token was revoked, if it was.
    pub fn revocation_time(&self, token_id: &str) -> Result<Option<i64>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::REVOCATIONS)?;
        match table.get(token_id)? {
            Some(guard) => Ok(Some(guard.value())),
            None => Ok(None),
        }
    }

    /// Count the total number of revoked tokens.
    pub fn revocation_count(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::REVOCATIONS)?;
        Ok(table.len()?)
    }

    /// List all revoked token IDs.
    pub fn list_revocations(&self) -> Result<Vec<String>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::REVOCATIONS)?;

        let mut ids = Vec::new();
        let iter = table.iter()?;
        for entry in iter {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            ids.push(entry.0.value().to_string());
        }
        Ok(ids)
    }

    /// Batch-revoke multiple tokens in a single transaction.
    pub fn store_revocations_batch(&self, token_ids: &[&str]) -> Result<u64> {
        let timestamp = current_timestamp();
        let write_txn = self.db.begin_write()?;
        let mut count = 0u64;
        {
            let mut table = write_txn.open_table(tables::REVOCATIONS)?;
            for token_id in token_ids {
                if table.get(*token_id)?.is_none() {
                    table.insert(*token_id, timestamp)?;
                    count += 1;
                }
            }
        }
        write_txn.commit()?;
        Ok(count)
    }

    // =========================================================================
    // Attested Root Storage
    // =========================================================================

    /// Store an attested root at a given height.
    ///
    /// Also updates the metadata to track the latest height.
    pub fn store_attested_root(&self, root: &StoredAttestedRoot) -> Result<()> {
        let serialized = postcard::to_stdvec(root)?;

        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::ATTESTED_ROOTS)?;
            table.insert(root.height, serialized.as_slice())?;

            // Update latest height metadata.
            let mut meta = write_txn.open_table(tables::METADATA)?;
            let current_latest = meta
                .get(tables::META_LATEST_ROOT_HEIGHT)?
                .map(|g| g.value())
                .unwrap_or(0);
            if root.height >= current_latest {
                meta.insert(tables::META_LATEST_ROOT_HEIGHT, root.height)?;
            }
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Load the latest (highest-height) attested root.
    pub fn latest_attested_root(&self) -> Result<Option<StoredAttestedRoot>> {
        let read_txn = self.db.begin_read()?;
        let meta = read_txn.open_table(tables::METADATA)?;

        let height = match meta.get(tables::META_LATEST_ROOT_HEIGHT)? {
            Some(guard) => guard.value(),
            None => return Ok(None),
        };

        let table = read_txn.open_table(tables::ATTESTED_ROOTS)?;
        match table.get(height)? {
            Some(value) => {
                let root: StoredAttestedRoot = postcard::from_bytes(value.value())?;
                Ok(Some(root))
            }
            None => Ok(None),
        }
    }

    /// Load an attested root at a specific height.
    pub fn attested_root_at_height(&self, height: u64) -> Result<Option<StoredAttestedRoot>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::ATTESTED_ROOTS)?;

        match table.get(height)? {
            Some(value) => {
                let root: StoredAttestedRoot = postcard::from_bytes(value.value())?;
                Ok(Some(root))
            }
            None => Ok(None),
        }
    }

    /// Count the total number of stored attested roots.
    pub fn attested_root_count(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::ATTESTED_ROOTS)?;
        Ok(table.len()?)
    }

    /// Load all attested roots in height order.
    pub fn all_attested_roots(&self) -> Result<Vec<StoredAttestedRoot>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::ATTESTED_ROOTS)?;

        let mut roots = Vec::new();
        let iter = table.iter()?;
        for entry in iter {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let root: StoredAttestedRoot = postcard::from_bytes(entry.1.value())?;
            roots.push(root);
        }
        Ok(roots)
    }
}

/// Get the current unix timestamp in seconds.
fn current_timestamp() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}
