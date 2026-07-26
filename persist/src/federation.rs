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

pub use dregg_federation::frost::MlDsaPublicKey;

/// One committee member's HYBRID finalization-vote signature over an attested
/// root — BOTH halves (ed25519 ∧ ML-DSA-65), plus a REDUNDANT copy of the
/// voter's ML-DSA-65 public key carried ALONGSIDE the signature.
///
/// The `ml_dsa_pubkey` field is a wire convenience (a copy of the voter's key),
/// NOT a trust root. On re-verify, [`Self::verify_finalization_quorum`] PINS it
/// to the genesis-ENROLLED ML-DSA roster passed at restart: the self-carried key
/// must EQUAL `ml_dsa_committee[voter_index]` and the PQ half is checked under
/// that enrolled key. A restarting node therefore needs the enrolled ML-DSA
/// roster aligned with the committee it verifies against (the current committee's
/// via `known_federation_ml_dsa_keys`; historical committees carry an aligned
/// `derived_committee_ml_dsa_history`, which may be EMPTY for a purely on-chain
/// amended committee — in which case the hybrid re-verify REFUSES that root
/// rather than downgrade to ed25519-only).
///
/// This closes the quantum-forgery downgrade: without the pin, a quantum
/// adversary who breaks ed25519 for member `P` could attach its OWN fresh ML-DSA
/// keypair and a PQ signature valid under it, and BOTH halves would pass (the PQ
/// half was checked against the attacker's self-carried key). With the pin, the
/// PQ half must verify under `P`'s enrolled key, which the adversary does not
/// hold — so a quantum adversary who breaks ed25519 alone still cannot re-anchor
/// a forged root on restart.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuorumSignature {
    /// The voter's federation Ed25519 public key (the committee identity).
    pub voter: PublicKey,
    /// The ed25519 (CLASSICAL) signature over
    /// [`dregg_types::finalization_vote_signing_message`].
    pub signature: Signature,
    /// A REDUNDANT copy of the voter's ML-DSA-65 (FIPS 204) public key, as its
    /// 1952 serialized bytes (`Vec<u8>` because the 1952-byte array is beyond
    /// serde's array-derive ceiling). At verify time this is PINNED equal to the
    /// enrolled roster key for the voter's committee index — never trusted on its
    /// own.
    pub ml_dsa_pubkey: Vec<u8>,
    /// The ML-DSA-65 (POST-QUANTUM) signature over the SAME canonical bytes as
    /// `signature`, verified under the ENROLLED key. The quorum counts a signer
    /// only when BOTH halves verify (and the enrolled-key pin holds), so a
    /// quantum adversary who breaks ed25519 alone still cannot re-anchor a forged
    /// root on restart.
    pub pq_signature: Vec<u8>,
}

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
    ///
    /// HYBRID: each [`QuorumSignature`] carries BOTH the ed25519 and the ML-DSA-65
    /// half PLUS a redundant copy of the voter's ML-DSA public key, so the restart
    /// re-verifier re-checks the FULL hybrid quorum (classical ∧ pq) — with the PQ
    /// half PINNED to the genesis-enrolled ML-DSA roster the restart threads in
    /// (`verify_finalization_quorum`'s `ml_dsa_committee`), never the self-carried
    /// key. Widening this field changes the postcard wire
    /// shape of a `StoredAttestedRoot`: postcard is non-self-describing, so
    /// attested roots persisted before this change will NOT decode after upgrade.
    /// That is ACCEPTED (state wipe on upgrade, as prior schema additions were) —
    /// no versioned decode is provided by design; this is a mesh flag-day field.
    #[serde(default)]
    pub finalization_quorum: Vec<QuorumSignature>,
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
    /// the corresponding public key in `committee`.  Thresholds count distinct
    /// committee identities: duplicating one valid `(key, signature)` row never
    /// manufactures a quorum, and a zero threshold is not an authority.
    pub fn verify_signatures(&self, committee: &[PublicKey]) -> bool {
        if self.threshold == 0 || self.quorum_signatures.len() < self.threshold {
            return false;
        }
        let message = self.signing_message();
        let mut distinct = std::collections::HashSet::new();
        for (pk, sig) in &self.quorum_signatures {
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
    ///   * every signer is a committee member (at some index `i`) whose BOTH
    ///     signature halves — ed25519 AND ML-DSA-65 — verify over
    ///     [`dregg_types::finalization_vote_signing_message`] for THIS root's
    ///     `(blocklace_block_id, merkle_root)`, with the PQ half verified under
    ///     the ENROLLED key `ml_dsa_committee[i]` (the self-carried
    ///     `ml_dsa_pubkey` must EQUAL it). A signature over any other root or
    ///     block, a valid ed25519 half with a broken/missing PQ half, or a
    ///     self-carried PQ key that differs from the enrolled one, does not count
    ///     (fail-closed hybrid: `classical ∧ pq`, PQ key pinned to genesis);
    ///   * the number of **distinct** fully-valid committee signers is
    ///     `>= threshold` (an equivocating/duplicated voter counts at most once,
    ///     so a single member cannot inflate the quorum).
    ///
    /// `ml_dsa_committee` is the genesis-ENROLLED ML-DSA-65 roster, aligned
    /// index-for-index with `committee`. A misaligned/empty roster
    /// (`ml_dsa_committee.len() != committee.len()`) cannot pin any signer's PQ
    /// half, so the whole re-verify REFUSES — never a silent ed25519-only
    /// downgrade. This is what defeats a quantum adversary who breaks ed25519
    /// alone: the PQ half must verify under the enrolled key it does not hold,
    /// mirroring the FROST positional pin.
    ///
    /// This never accepts a root without a genuine >=threshold committee quorum
    /// over the exact finalized state — it closes the liveness fail-close
    /// WITHOUT relaxing the soundness bar.
    pub fn verify_finalization_quorum(
        &self,
        committee: &[PublicKey],
        ml_dsa_committee: &[MlDsaPublicKey],
    ) -> bool {
        // One of this crate's entries into `dregg-pq` (the enrolled ML-DSA half is checked below).
        // See `FaithfulNoteRootEnvelopeV1::verify_hybrid` for why the install is here.
        #[cfg(test)]
        dregg_pq_testkit::install_or_panic();
        let Some(block_id) = self.blocklace_block_id else {
            return false;
        };
        if self.finalization_quorum.len() < self.threshold {
            return false;
        }
        // The enrolled PQ roster MUST align index-for-index with the ed25519
        // committee, or there is no enrolled key to pin each signer against —
        // fail closed (an EMPTY roster is included here: no silent downgrade).
        if ml_dsa_committee.len() != committee.len() {
            return false;
        }
        let message = dregg_types::finalization_vote_signing_message(&block_id, &self.merkle_root);
        let mut distinct: std::collections::HashSet<[u8; 32]> = std::collections::HashSet::new();
        for qs in &self.finalization_quorum {
            // Membership — and the voter's ENROLLED index.
            let Some(idx) = committee.iter().position(|c| c == &qs.voter) else {
                return false;
            };
            // CLASSICAL half.
            if !qs.voter.verify(&message, &qs.signature) {
                return false;
            }
            // POST-QUANTUM half (ML-DSA-65) — PINNED to the enrolled roster. The
            // self-carried key must be a byte-identical copy of the enrolled key
            // (never trusted on its own), and the PQ signature is verified under
            // the ENROLLED key. A mismatch or a failing signature refuses the
            // whole quorum — never a silent ed25519-only downgrade.
            let enrolled = &ml_dsa_committee[idx];
            if qs.ml_dsa_pubkey.as_slice() != enrolled.0.as_slice() {
                return false;
            }
            if !enrolled.verify(&message, &qs.pq_signature) {
                return false;
            }
            distinct.insert(qs.voter.0);
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
    ///
    /// HYBRID BAR on the vote leg. A `finalization_quorum` entry counts here
    /// only when BOTH its halves — ed25519 AND ML-DSA-65 under the ENROLLED key
    /// `ml_dsa_committee[i]` — verify over the finalization-vote message
    /// (classical ∧ pq, PQ key pinned), the SAME bar
    /// [`verify_finalization_quorum`](Self::verify_finalization_quorum) sets
    /// per signer. Every genuinely emitted vote carries both halves
    /// (`FinalizationVote::sign` is hybrid), so requiring both loses nothing —
    /// while a valid ed25519 half riding with a forged/absent PQ half, or a
    /// self-carried PQ key that is not the enrolled one, is NOT a committee
    /// binding and must not be treated as one. When the enrolled roster is not
    /// aligned with `committee` (e.g. a purely on-chain amended committee with no
    /// recorded ML-DSA roster) the hybrid vote leg is skipped entirely — never a
    /// silent ed25519-only pass on that leg.
    ///
    /// The `quorum_signatures` leg (the node's OWN light-client signature over
    /// `signing_message()`) remains ed25519-only BY STRUCTURE: that field is
    /// `(PublicKey, Signature)` pairs with no PQ material on its wire. It is a
    /// lone local self-binding, never an anchor — anchoring always goes through
    /// the full hybrid `verify_finalization_quorum` — and a positive result
    /// from THIS check can only REFUSE a mismatched ledger, never accept one.
    pub fn has_any_valid_committee_signature(
        &self,
        committee: &[PublicKey],
        ml_dsa_committee: &[MlDsaPublicKey],
    ) -> bool {
        // The other entry into `dregg-pq` on this type — see `verify_finalization_quorum`.
        #[cfg(test)]
        dregg_pq_testkit::install_or_panic();
        let full_msg = self.signing_message();
        for (pk, sig) in &self.quorum_signatures {
            if committee.contains(pk) && pk.verify(&full_msg, sig) {
                return true;
            }
        }
        // The finalization-vote leg is HYBRID and PINNED — only consult it when
        // the enrolled roster aligns with the committee (otherwise there is no
        // enrolled key to pin each signer's PQ half against, and this leg must
        // NOT fall back to ed25519-only).
        if ml_dsa_committee.len() == committee.len()
            && let Some(block_id) = self.blocklace_block_id
        {
            let vote_msg =
                dregg_types::finalization_vote_signing_message(&block_id, &self.merkle_root);
            for qs in &self.finalization_quorum {
                // Membership — and the voter's enrolled index.
                let Some(idx) = committee.iter().position(|c| c == &qs.voter) else {
                    continue;
                };
                // CLASSICAL half.
                if !qs.voter.verify(&vote_msg, &qs.signature) {
                    continue;
                }
                // POST-QUANTUM half — PINNED to the enrolled roster. A
                // self-carried key differing from the enrolled one, or a failing
                // signature, means this entry is NOT a valid committee binding.
                let enrolled = &ml_dsa_committee[idx];
                if qs.ml_dsa_pubkey.as_slice() != enrolled.0.as_slice() {
                    continue;
                }
                if enrolled.verify(&vote_msg, &qs.pq_signature) {
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
        // across the committee. v6 (state anchor): `merkle_root` STAYS the BLAKE3
        // whole-image `canonical_ledger_root` — it is the restart anchor this very
        // function re-verifies — while the receipts under `receipt_stream_root` moved
        // to the AIR-bound chip 8-felt commitment (`dregg_turn::state_commit`).
        // Mirrors `dregg_types::AttestedRoot::signing_message` and MUST stay
        // byte-identical to it.
        msg.extend_from_slice(b"dregg-attested-root-v6");
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
        let write_txn = self.db.begin_write()?;
        store_attested_root_in(&write_txn, root, AttestedRootWrite::Replace)?;
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

/// Mutation policy for an attested-root write inside a larger transaction.
pub(crate) enum AttestedRootWrite {
    /// The ordinary backfill path may replace a root at the same height with
    /// the same state plus its newly assembled finalization quorum.
    Replace,
    /// A fresh finalized commit must not overwrite a competing attestation.
    Fresh,
    /// Crash replay requires the exact bytes already written by the original
    /// atomic commit and never repairs a missing row.
    ExactReplay,
}

/// Store one attested root inside a caller-owned redb transaction.
pub(crate) fn store_attested_root_in(
    write: &redb::WriteTransaction,
    root: &StoredAttestedRoot,
    policy: AttestedRootWrite,
) -> Result<()> {
    let serialized = postcard::to_stdvec(root)?;
    let mut table = write.open_table(tables::ATTESTED_ROOTS)?;
    if let Some(existing) = table.get(root.height)? {
        let existing_bytes = existing.value();
        match policy {
            AttestedRootWrite::Replace => {}
            AttestedRootWrite::Fresh => {
                return Err(StoreError::Integrity(format!(
                    "attested root height {} already exists; refusing finalized-root overwrite",
                    root.height
                )));
            }
            AttestedRootWrite::ExactReplay if existing_bytes == serialized.as_slice() => {
                return Ok(());
            }
            AttestedRootWrite::ExactReplay => {
                return Err(StoreError::Integrity(format!(
                    "attested root replay at height {} differs from durable root",
                    root.height
                )));
            }
        }
    } else if matches!(policy, AttestedRootWrite::ExactReplay) {
        return Err(StoreError::Integrity(format!(
            "attested root replay at height {} is missing from durable store",
            root.height
        )));
    }
    table.insert(root.height, serialized.as_slice())?;

    let mut meta = write.open_table(tables::METADATA)?;
    let current_latest = meta
        .get(tables::META_LATEST_ROOT_HEIGHT)?
        .map(|g| g.value())
        .unwrap_or(0);
    if root.height >= current_latest {
        meta.insert(tables::META_LATEST_ROOT_HEIGHT, root.height)?;
    }
    Ok(())
}

/// Get the current unix timestamp in seconds.
fn current_timestamp() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}
