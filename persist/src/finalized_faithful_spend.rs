//! Persist-minted public authority for a finalized faithful hidden-note spend.
//!
//! The authority contains only fields already public in FNSP-v2 plus the exact
//! finalized-turn coordinates that made the spend durable.  It deliberately
//! carries no note opening, Merkle path, spending key, randomness, or proof
//! bytes.  Its public type has private fields and does not implement
//! `Deserialize`: callers cannot manufacture an authority by decoding chosen
//! bytes.  Only the finalized-turn transaction writes the private wire and
//! [`PersistentStore`] wraps a validated durable row in the public type.
//!
//! This is a trusted-store custody boundary, not a standalone cryptographic
//! credential.  The BLAKE3 digests below are domain-separated corruption and
//! substitution checks; they are deliberately not described as a MAC or a
//! committee signature.  A hostile process able to rewrite the redb image can
//! recompute them.  Load therefore rejoins every row to its per-turn manifest,
//! durable historical-root record, exact nullifier prefix, carrying commit (or
//! checkpoint-compaction carrier), and attested-root row.  Independent hostile-
//! store authentication would additionally require retaining and verifying the
//! signed turn/receipt inclusion payload or signing the manifest under a key
//! outside the mutable database.

use redb::{ReadableTable, ReadableTableMetadata};
use serde::{Deserialize, Serialize};

use crate::commit_log::CommitRecord;
use crate::faithful_note_root_history::{
    CanonicalFaithfulRoot, FaithfulNoteRootAnchorV1, FaithfulNoteRootEnvelopeV1,
};
use crate::{PersistentStore, Result, StoreError, StoredAttestedRoot, tables};

const AUTHORITY_DOMAIN: &str = "dregg.finalized-faithful-spend.v1";
const TURN_MANIFEST_DOMAIN: &str = "dregg.finalized-faithful-spend-turn.v1";

/// Non-authoritative public claim supplied by the node's strict FNSP-v2
/// decoder to the atomic finalized-turn weld.
///
/// Persistence checks this claim against the ordered nullifier transition and
/// authenticated historical note-root table before minting an authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedFaithfulSpendInput {
    pub root_height: u64,
    pub historical_note_root: CanonicalFaithfulRoot,
    pub nullifier: [u8; 32],
    pub value: u64,
    pub asset_type: u64,
    pub successor_nullifier_root: CanonicalFaithfulRoot,
}

/// Private durable wire.  Keeping serde off the public wrapper is load-bearing:
/// an external crate that can deserialize the authority type could fabricate
/// the supposedly store-minted capability from arbitrary bytes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct StoredFinalizedFaithfulSpendV1 {
    authority_digest: [u8; 32],
    turn_hash: [u8; 32],
    turn_receipt_hash: [u8; 32],
    spend_agent: [u8; 32],
    spend_index: u32,
    spend_count: u32,
    nullifier_seq: u64,
    root_height: u64,
    historical_note_root: [u8; 32],
    nullifier: [u8; 32],
    value: u64,
    asset_type: u64,
    successor_nullifier_root: [u8; 32],
    finalized_height: u64,
    block_id: [u8; 32],
    federation_id: [u8; 32],
    finality_round: Option<u64>,
    attested_root_digest: [u8; 32],
}

/// Exact per-turn custody carrier.  Unlike the nullifier-keyed rows, this is
/// present for zero-spend turns as well.  It is deliberately retained when the
/// carrying [`CommitRecord`] is compacted under a checkpoint.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct StoredFinalizedFaithfulSpendTurnV1 {
    manifest_digest: [u8; 32],
    turn_hash: [u8; 32],
    turn_receipt_hash: [u8; 32],
    spend_agent: [u8; 32],
    spend_count: u32,
    first_nullifier_seq: u64,
    ordered_nullifiers: Vec<[u8; 32]>,
    ordered_authority_digests: Vec<[u8; 32]>,
    finalized_height: u64,
    block_id: [u8; 32],
    federation_id: [u8; 32],
    finality_round: Option<u64>,
    attested_root_digest: [u8; 32],
}

/// Public-only trusted-store authority for one exact faithful spend.
///
/// Construction is intentionally private.  A value can be obtained only by
/// loading a row that the atomic finalized-turn weld wrote and whose manifest,
/// root transitions, and finalization coordinates still agree with the durable
/// indices.  It is not a portable committee signature; see the module-level
/// threat model.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedFaithfulSpend {
    stored: StoredFinalizedFaithfulSpendV1,
}

impl FinalizedFaithfulSpend {
    pub fn authority_digest(&self) -> [u8; 32] {
        self.stored.authority_digest
    }

    pub fn turn_hash(&self) -> [u8; 32] {
        self.stored.turn_hash
    }

    pub fn turn_receipt_hash(&self) -> [u8; 32] {
        self.stored.turn_receipt_hash
    }

    pub fn spend_agent(&self) -> [u8; 32] {
        self.stored.spend_agent
    }

    pub fn spend_index(&self) -> u32 {
        self.stored.spend_index
    }

    pub fn spend_count(&self) -> u32 {
        self.stored.spend_count
    }

    /// Global append sequence in the durable faithful nullifier accumulator.
    pub fn nullifier_seq(&self) -> u64 {
        self.stored.nullifier_seq
    }

    pub fn root_height(&self) -> u64 {
        self.stored.root_height
    }

    pub fn historical_note_root8(&self) -> [u8; 32] {
        self.stored.historical_note_root
    }

    pub fn nullifier(&self) -> [u8; 32] {
        self.stored.nullifier
    }

    pub fn value(&self) -> u64 {
        self.stored.value
    }

    pub fn asset_type(&self) -> u64 {
        self.stored.asset_type
    }

    pub fn successor_nullifier_root8(&self) -> [u8; 32] {
        self.stored.successor_nullifier_root
    }

    pub fn finalized_height(&self) -> u64 {
        self.stored.finalized_height
    }

    pub fn block_id(&self) -> [u8; 32] {
        self.stored.block_id
    }

    pub fn federation_id(&self) -> [u8; 32] {
        self.stored.federation_id
    }

    pub fn finality_round(&self) -> Option<u64> {
        self.stored.finality_round
    }

    pub fn attested_root_digest(&self) -> [u8; 32] {
        self.stored.attested_root_digest
    }
}

fn nonzero(value: &[u8; 32]) -> bool {
    value.iter().any(|byte| *byte != 0)
}

fn push_option_u64(message: &mut Vec<u8>, value: Option<u64>) {
    match value {
        Some(value) => {
            message.push(1);
            message.extend_from_slice(&value.to_le_bytes());
        }
        None => message.push(0),
    }
}

fn authority_digest(value: &StoredFinalizedFaithfulSpendV1) -> [u8; 32] {
    let mut message = Vec::with_capacity(337);
    message.extend_from_slice(value.turn_hash.as_slice());
    message.extend_from_slice(value.turn_receipt_hash.as_slice());
    message.extend_from_slice(value.spend_agent.as_slice());
    message.extend_from_slice(&value.spend_index.to_le_bytes());
    message.extend_from_slice(&value.spend_count.to_le_bytes());
    message.extend_from_slice(&value.nullifier_seq.to_le_bytes());
    message.extend_from_slice(&value.root_height.to_le_bytes());
    message.extend_from_slice(value.historical_note_root.as_slice());
    message.extend_from_slice(value.nullifier.as_slice());
    message.extend_from_slice(&value.value.to_le_bytes());
    message.extend_from_slice(&value.asset_type.to_le_bytes());
    message.extend_from_slice(value.successor_nullifier_root.as_slice());
    message.extend_from_slice(&value.finalized_height.to_le_bytes());
    message.extend_from_slice(value.block_id.as_slice());
    message.extend_from_slice(value.federation_id.as_slice());
    push_option_u64(&mut message, value.finality_round);
    message.extend_from_slice(value.attested_root_digest.as_slice());
    *blake3::Hasher::new_derive_key(AUTHORITY_DOMAIN)
        .update(&message)
        .finalize()
        .as_bytes()
}

fn turn_manifest_digest(value: &StoredFinalizedFaithfulSpendTurnV1) -> [u8; 32] {
    let mut message = Vec::with_capacity(256 + 64 * value.ordered_authority_digests.len());
    message.extend_from_slice(value.turn_hash.as_slice());
    message.extend_from_slice(value.turn_receipt_hash.as_slice());
    message.extend_from_slice(value.spend_agent.as_slice());
    message.extend_from_slice(&value.spend_count.to_le_bytes());
    message.extend_from_slice(&value.first_nullifier_seq.to_le_bytes());
    for nullifier in &value.ordered_nullifiers {
        message.extend_from_slice(nullifier);
    }
    for digest in &value.ordered_authority_digests {
        message.extend_from_slice(digest);
    }
    message.extend_from_slice(&value.finalized_height.to_le_bytes());
    message.extend_from_slice(value.block_id.as_slice());
    message.extend_from_slice(value.federation_id.as_slice());
    push_option_u64(&mut message, value.finality_round);
    message.extend_from_slice(value.attested_root_digest.as_slice());
    *blake3::Hasher::new_derive_key(TURN_MANIFEST_DOMAIN)
        .update(&message)
        .finalize()
        .as_bytes()
}

fn decode_stored(bytes: &[u8]) -> Result<StoredFinalizedFaithfulSpendV1> {
    let stored: StoredFinalizedFaithfulSpendV1 = postcard::from_bytes(bytes)?;
    CanonicalFaithfulRoot::from_bytes(stored.historical_note_root)
        .map_err(|error| StoreError::Integrity(error.to_string()))?;
    CanonicalFaithfulRoot::from_bytes(stored.successor_nullifier_root)
        .map_err(|error| StoreError::Integrity(error.to_string()))?;
    if !nonzero(&stored.turn_hash)
        || !nonzero(&stored.turn_receipt_hash)
        || !nonzero(&stored.spend_agent)
        || !nonzero(&stored.nullifier)
        || !nonzero(&stored.block_id)
        || !nonzero(&stored.federation_id)
        || stored.root_height > stored.finalized_height
        || stored.spend_index >= stored.spend_count
        || stored.authority_digest != authority_digest(&stored)
    {
        return Err(StoreError::Integrity(
            "malformed finalized faithful-spend authority".to_string(),
        ));
    }
    Ok(stored)
}

fn decode_manifest(bytes: &[u8]) -> Result<StoredFinalizedFaithfulSpendTurnV1> {
    let manifest: StoredFinalizedFaithfulSpendTurnV1 = postcard::from_bytes(bytes)?;
    let count = usize::try_from(manifest.spend_count).map_err(|_| {
        StoreError::Integrity("faithful-spend manifest count does not fit usize".to_string())
    })?;
    if !nonzero(&manifest.turn_hash)
        || !nonzero(&manifest.turn_receipt_hash)
        || !nonzero(&manifest.spend_agent)
        || !nonzero(&manifest.block_id)
        || !nonzero(&manifest.federation_id)
        || manifest.ordered_nullifiers.len() != count
        || manifest.ordered_authority_digests.len() != count
        || manifest
            .first_nullifier_seq
            .checked_add(u64::from(manifest.spend_count))
            .is_none()
        || manifest
            .ordered_nullifiers
            .iter()
            .any(|value| !nonzero(value))
        || manifest
            .ordered_authority_digests
            .iter()
            .any(|value| !nonzero(value))
        || manifest.manifest_digest != turn_manifest_digest(&manifest)
    {
        return Err(StoreError::Integrity(
            "malformed finalized faithful-spend turn manifest".to_string(),
        ));
    }
    Ok(manifest)
}

fn attested_root_digest(root: &StoredAttestedRoot) -> [u8; 32] {
    *blake3::Hasher::new_derive_key("dregg.finalized-faithful-spend.attested-root.v1")
        .update(&root.signing_message())
        .finalize()
        .as_bytes()
}

fn historical_root_is_durable(
    write: &redb::WriteTransaction,
    height: u64,
    root: CanonicalFaithfulRoot,
) -> Result<bool> {
    let metadata = write.open_table(tables::METADATA_BYTES)?;
    if let Some(anchor_bytes) = metadata.get(tables::META_FAITHFUL_NOTE_ROOT_ANCHOR)? {
        let anchor = FaithfulNoteRootAnchorV1::from_bytes(anchor_bytes.value())
            .map_err(|error| StoreError::Integrity(error.to_string()))?;
        if anchor.height == height && anchor.root == root {
            return Ok(true);
        }
    }
    drop(metadata);

    let history = write.open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)?;
    let Some(envelope_bytes) = history.get(height)? else {
        return Ok(false);
    };
    let envelope = FaithfulNoteRootEnvelopeV1::from_bytes(envelope_bytes.value())
        .map_err(|error| StoreError::Integrity(error.to_string()))?;
    Ok(envelope.record.height == height && envelope.record.successor == root)
}

fn derive_stored(
    record: &CommitRecord,
    attested_root: &StoredAttestedRoot,
    input: FinalizedFaithfulSpendInput,
    spend_index: u32,
    spend_count: u32,
    nullifier_seq: u64,
) -> Result<StoredFinalizedFaithfulSpendV1> {
    if input.nullifier == [0; 32]
        || input.root_height > record.height
        || attested_root.height != record.height
        || attested_root.blocklace_block_id != Some(record.block_id)
        || attested_root.federation_id.0 == [0; 32]
    {
        return Err(StoreError::Integrity(
            "faithful-spend authority coordinates are malformed".to_string(),
        ));
    }
    let mut stored = StoredFinalizedFaithfulSpendV1 {
        authority_digest: [0; 32],
        turn_hash: record.turn_hash,
        turn_receipt_hash: record.receipt_hash,
        spend_agent: record.creator,
        spend_index,
        spend_count,
        nullifier_seq,
        root_height: input.root_height,
        historical_note_root: input.historical_note_root.to_bytes(),
        nullifier: input.nullifier,
        value: input.value,
        asset_type: input.asset_type,
        successor_nullifier_root: input.successor_nullifier_root.to_bytes(),
        finalized_height: record.height,
        block_id: record.block_id,
        federation_id: attested_root.federation_id.0,
        finality_round: attested_root.finality_round,
        attested_root_digest: attested_root_digest(attested_root),
    };
    stored.authority_digest = authority_digest(&stored);
    Ok(stored)
}

fn decode_nullifier_record(bytes: &[u8; 16]) -> (u64, u64) {
    let mut value = [0u8; 8];
    value.copy_from_slice(&bytes[..8]);
    let mut seq = [0u8; 8];
    seq.copy_from_slice(&bytes[8..]);
    (u64::from_le_bytes(value), u64::from_le_bytes(seq))
}

fn durable_input_sequences_in(
    write: &redb::WriteTransaction,
    inputs: &[FinalizedFaithfulSpendInput],
    replay_manifest: Option<&StoredFinalizedFaithfulSpendTurnV1>,
) -> Result<(u64, Vec<u64>)> {
    let presence = write.open_table(tables::NULLIFIERS)?;
    let records = write.open_table(tables::NULLIFIER_RECORDS_V1)?;
    if presence.len()? != records.len()? {
        return Err(StoreError::Integrity(
            "faithful-spend mint observed divergent nullifier tables".to_string(),
        ));
    }
    if inputs.is_empty() {
        // A replay can happen after later turns appended more nullifiers.  Its
        // original empty interval is therefore taken from the exact manifest,
        // never guessed from today's accumulator tail.
        let first = replay_manifest
            .map(|manifest| manifest.first_nullifier_seq)
            .unwrap_or(records.len()?);
        return Ok((first, Vec::new()));
    }

    let mut sequences = Vec::with_capacity(inputs.len());
    for input in inputs {
        if presence.get(&input.nullifier)?.is_none() {
            return Err(StoreError::Integrity(
                "faithful-spend authority has no durable spent-nullifier row".to_string(),
            ));
        }
        let encoded = records.get(&input.nullifier)?.ok_or_else(|| {
            StoreError::Integrity(
                "faithful-spend authority has no circuit-facing nullifier record".to_string(),
            )
        })?;
        let (value, seq) = decode_nullifier_record(encoded.value());
        if value != input.value {
            return Err(StoreError::Integrity(
                "faithful-spend authority value disagrees with durable nullifier record"
                    .to_string(),
            ));
        }
        sequences.push(seq);
    }
    let first = sequences[0];
    for (index, seq) in sequences.iter().copied().enumerate() {
        let expected = first
            .checked_add(u64::try_from(index).map_err(|_| {
                StoreError::Integrity("faithful-spend sequence index does not fit u64".to_string())
            })?)
            .ok_or_else(|| {
                StoreError::Integrity("faithful-spend nullifier sequence overflow".to_string())
            })?;
        if seq != expected {
            return Err(StoreError::Integrity(
                "faithful-spend nullifiers are not one exact durable append interval".to_string(),
            ));
        }
    }
    Ok((first, sequences))
}

fn derive_manifest(
    record: &CommitRecord,
    attested_root: &StoredAttestedRoot,
    first_nullifier_seq: u64,
    rows: &[StoredFinalizedFaithfulSpendV1],
) -> Result<StoredFinalizedFaithfulSpendTurnV1> {
    let spend_count = u32::try_from(rows.len())
        .map_err(|_| StoreError::Integrity("faithful-spend count does not fit u32".to_string()))?;
    let mut manifest = StoredFinalizedFaithfulSpendTurnV1 {
        manifest_digest: [0; 32],
        turn_hash: record.turn_hash,
        turn_receipt_hash: record.receipt_hash,
        spend_agent: record.creator,
        spend_count,
        first_nullifier_seq,
        ordered_nullifiers: rows.iter().map(|row| row.nullifier).collect(),
        ordered_authority_digests: rows.iter().map(|row| row.authority_digest).collect(),
        finalized_height: record.height,
        block_id: record.block_id,
        federation_id: attested_root.federation_id.0,
        finality_round: attested_root.finality_round,
        attested_root_digest: attested_root_digest(attested_root),
    };
    manifest.manifest_digest = turn_manifest_digest(&manifest);
    Ok(manifest)
}

fn validate_manifest_rows(
    manifest: &StoredFinalizedFaithfulSpendTurnV1,
    rows: &mut [StoredFinalizedFaithfulSpendV1],
) -> Result<()> {
    rows.sort_by_key(|row| row.spend_index);
    if rows.len() != usize::try_from(manifest.spend_count).unwrap_or(usize::MAX) {
        return Err(StoreError::Integrity(
            "finalized faithful-spend row count disagrees with turn manifest".to_string(),
        ));
    }
    for (index, row) in rows.iter().enumerate() {
        let index_u32 = u32::try_from(index).map_err(|_| {
            StoreError::Integrity("faithful-spend row index does not fit u32".to_string())
        })?;
        let expected_seq = manifest
            .first_nullifier_seq
            .checked_add(u64::try_from(index).map_err(|_| {
                StoreError::Integrity("faithful-spend row index does not fit u64".to_string())
            })?)
            .ok_or_else(|| {
                StoreError::Integrity("faithful-spend row sequence overflow".to_string())
            })?;
        if row.turn_hash != manifest.turn_hash
            || row.turn_receipt_hash != manifest.turn_receipt_hash
            || row.spend_agent != manifest.spend_agent
            || row.spend_index != index_u32
            || row.spend_count != manifest.spend_count
            || row.nullifier_seq != expected_seq
            || row.nullifier != manifest.ordered_nullifiers[index]
            || row.authority_digest != manifest.ordered_authority_digests[index]
            || row.finalized_height != manifest.finalized_height
            || row.block_id != manifest.block_id
            || row.federation_id != manifest.federation_id
            || row.finality_round != manifest.finality_round
            || row.attested_root_digest != manifest.attested_root_digest
        {
            return Err(StoreError::Integrity(
                "finalized faithful-spend row disagrees with turn manifest".to_string(),
            ));
        }
    }
    Ok(())
}

/// Write or exact-replay-check all authorities inside the caller's finalized
/// redb transaction.  `allow_insert` is false on an idempotent replay, so a
/// missing authority row is corruption rather than something replay repairs.
pub(crate) fn write_finalized_faithful_spends_in(
    write: &redb::WriteTransaction,
    record: &CommitRecord,
    attested_root: &StoredAttestedRoot,
    inputs: &[FinalizedFaithfulSpendInput],
    allow_insert: bool,
) -> Result<()> {
    let spend_count = u32::try_from(inputs.len())
        .map_err(|_| StoreError::Integrity("faithful-spend count does not fit u32".to_string()))?;
    for input in inputs {
        if !historical_root_is_durable(write, input.root_height, input.historical_note_root)? {
            return Err(StoreError::Integrity(
                "faithful-spend authority references an absent historical note root".to_string(),
            ));
        }
    }

    let existing_manifest = {
        let manifests = write.open_table(tables::FINALIZED_FAITHFUL_SPEND_TURNS)?;
        manifests
            .get(&record.turn_hash)?
            .map(|existing| decode_manifest(existing.value()))
            .transpose()?
    };
    let (first_nullifier_seq, sequences) =
        durable_input_sequences_in(write, inputs, existing_manifest.as_ref())?;
    let mut rows = Vec::with_capacity(inputs.len());
    for (index, input) in inputs.iter().copied().enumerate() {
        let index_u32 = u32::try_from(index).map_err(|_| {
            StoreError::Integrity("faithful-spend index does not fit u32".to_string())
        })?;
        let nullifier_seq = sequences[index];
        rows.push(derive_stored(
            record,
            attested_root,
            input,
            index_u32,
            spend_count,
            nullifier_seq,
        )?);
    }
    let manifest = derive_manifest(record, attested_root, first_nullifier_seq, &rows)?;

    match existing_manifest {
        Some(existing) if !allow_insert && existing == manifest => {}
        Some(_) => {
            return Err(StoreError::Integrity(
                "finalized faithful-spend turn manifest conflicts on replay".to_string(),
            ));
        }
        None if allow_insert => {
            let encoded = postcard::to_stdvec(&manifest)?;
            let mut manifests = write.open_table(tables::FINALIZED_FAITHFUL_SPEND_TURNS)?;
            manifests.insert(&record.turn_hash, encoded.as_slice())?;
        }
        None => {
            return Err(StoreError::Integrity(
                "idempotent faithful-spend replay is missing its turn manifest".to_string(),
            ));
        }
    }

    let mut table = write.open_table(tables::FINALIZED_FAITHFUL_SPENDS)?;
    let mut present_for_turn = Vec::new();
    for nullifier in &manifest.ordered_nullifiers {
        if let Some(entry) = table.get(nullifier)? {
            let stored = decode_stored(entry.value())?;
            if stored.nullifier != *nullifier {
                return Err(StoreError::Integrity(
                    "finalized faithful-spend table key disagrees with row nullifier".to_string(),
                ));
            }
            present_for_turn.push(stored);
        }
    }
    if allow_insert && !present_for_turn.is_empty() {
        return Err(StoreError::Integrity(
            "fresh faithful-spend mint found pre-existing rows for turn".to_string(),
        ));
    }
    if !allow_insert {
        validate_manifest_rows(&manifest, &mut present_for_turn)?;
    }

    for (input, stored) in inputs.iter().zip(rows) {
        let encoded = postcard::to_stdvec(&stored)?;
        let existing = table
            .get(&input.nullifier)?
            .map(|existing| existing.value().to_vec());
        match existing {
            Some(existing) if !allow_insert && existing == encoded => {}
            Some(_) => {
                return Err(StoreError::Integrity(
                    "finalized faithful-spend authority conflicts at nullifier".to_string(),
                ));
            }
            None if allow_insert => {
                table.insert(&input.nullifier, encoded.as_slice())?;
            }
            None => {
                return Err(StoreError::Integrity(
                    "idempotent faithful-spend replay is missing its durable authority".to_string(),
                ));
            }
        }
    }
    Ok(())
}

impl PersistentStore {
    fn load_faithful_spend_turn(
        &self,
        turn_hash: &[u8; 32],
    ) -> Result<
        Option<(
            StoredFinalizedFaithfulSpendTurnV1,
            Vec<StoredFinalizedFaithfulSpendV1>,
        )>,
    > {
        let read = self.db.begin_read()?;
        let manifests = read.open_table(tables::FINALIZED_FAITHFUL_SPEND_TURNS)?;
        let manifest = manifests
            .get(turn_hash)?
            .map(|value| decode_manifest(value.value()))
            .transpose()?;
        let Some(manifest) = manifest else {
            return Ok(None);
        };
        if manifest.turn_hash != *turn_hash {
            return Err(StoreError::Integrity(
                "faithful-spend manifest key disagrees with turn hash".to_string(),
            ));
        }

        let authorities = read.open_table(tables::FINALIZED_FAITHFUL_SPENDS)?;
        let mut rows = Vec::with_capacity(manifest.ordered_nullifiers.len());
        for nullifier in &manifest.ordered_nullifiers {
            let Some(entry) = authorities.get(nullifier)? else {
                return Err(StoreError::Integrity(
                    "finalized faithful-spend manifest names a missing authority row".to_string(),
                ));
            };
            let decoded = decode_stored(entry.value())?;
            if decoded.nullifier != *nullifier {
                return Err(StoreError::Integrity(
                    "finalized faithful-spend table key disagrees with row nullifier".to_string(),
                ));
            }
            rows.push(decoded);
        }
        validate_manifest_rows(&manifest, &mut rows)?;
        Ok(Some((manifest, rows)))
    }

    /// Load the store-minted authority for one public nullifier.
    pub fn finalized_faithful_spend(
        &self,
        nullifier: &[u8; 32],
    ) -> Result<Option<FinalizedFaithfulSpend>> {
        let stored = {
            let read = self.db.begin_read()?;
            let table = read.open_table(tables::FINALIZED_FAITHFUL_SPENDS)?;
            match table.get(nullifier)? {
                Some(value) => {
                    let stored = decode_stored(value.value())?;
                    if stored.nullifier != *nullifier {
                        return Err(StoreError::Integrity(
                            "finalized faithful-spend lookup key disagrees with row nullifier"
                                .to_string(),
                        ));
                    }
                    Some(stored)
                }
                None => None,
            }
        };
        let Some(stored) = stored else {
            return Ok(None);
        };
        let (manifest, rows) = self
            .load_faithful_spend_turn(&stored.turn_hash)?
            .ok_or_else(|| {
                StoreError::Integrity(
                    "finalized faithful-spend authority has no turn manifest".to_string(),
                )
            })?;
        self.verify_authority_coordinates(&manifest, &rows)?;
        let stored = rows
            .into_iter()
            .find(|row| row.nullifier == *nullifier)
            .ok_or_else(|| {
                StoreError::Integrity(
                    "finalized faithful-spend point row is absent from its manifest".to_string(),
                )
            })?;
        Ok(Some(FinalizedFaithfulSpend { stored }))
    }

    /// Load every finalized faithful spend minted by one turn, in exact DFS
    /// effect order.  The nullifier-keyed table makes each authority globally
    /// one-shot; the stored spend index restores within-turn order.
    pub fn finalized_faithful_spends_for_turn(
        &self,
        turn_hash: &[u8; 32],
    ) -> Result<Vec<FinalizedFaithfulSpend>> {
        let Some((manifest, stored)) = self.load_faithful_spend_turn(turn_hash)? else {
            return Ok(Vec::new());
        };
        self.verify_authority_coordinates(&manifest, &stored)?;
        Ok(stored
            .into_iter()
            .map(|stored| FinalizedFaithfulSpend { stored })
            .collect())
    }

    fn verify_authority_coordinates(
        &self,
        manifest: &StoredFinalizedFaithfulSpendTurnV1,
        authorities: &[StoredFinalizedFaithfulSpendV1],
    ) -> Result<()> {
        match self.lookup_turn(&manifest.turn_hash)? {
            Some(commit) => {
                if commit.receipt_hash != manifest.turn_receipt_hash
                    || commit.creator != manifest.spend_agent
                    || commit.height != manifest.finalized_height
                    || commit.block_id != manifest.block_id
                {
                    return Err(StoreError::Integrity(
                        "faithful-spend manifest disagrees with carrying commit".to_string(),
                    ));
                }
            }
            None => {
                // A normal checkpoint compaction intentionally removes the full
                // CommitRecord.  Its block-id carrier and the covering
                // checkpoint are the durable proof that this was deletion by
                // compaction rather than a torn/missing commit.
                let read = self.db.begin_read()?;
                let compacted = read.open_table(tables::COMMIT_COMPACTED_BLOCK_IDS)?;
                if compacted.get(&manifest.block_id)?.is_none()
                    || self.latest_ledger_checkpoint_height()? < manifest.finalized_height
                {
                    return Err(StoreError::Integrity(
                        "faithful-spend manifest has neither a live commit nor a covering compacted commit"
                            .to_string(),
                    ));
                }
            }
        }
        let attested = self
            .attested_root_at_height(manifest.finalized_height)?
            .ok_or_else(|| {
                StoreError::Integrity(
                    "faithful-spend manifest has no carrying attested root".to_string(),
                )
            })?;
        if attested.federation_id.0 != manifest.federation_id
            || attested.blocklace_block_id != Some(manifest.block_id)
            || attested.finality_round != manifest.finality_round
            || attested_root_digest(&attested) != manifest.attested_root_digest
        {
            return Err(StoreError::Integrity(
                "faithful-spend manifest disagrees with carrying attested root".to_string(),
            ));
        }

        for authority in authorities {
            let historical = CanonicalFaithfulRoot::from_bytes(authority.historical_note_root)
                .map_err(|error| StoreError::Integrity(error.to_string()))?;
            if !self.historical_faithful_root_is_durable(authority.root_height, historical)? {
                return Err(StoreError::Integrity(
                    "faithful-spend authority's historical note root is no longer durable"
                        .to_string(),
                ));
            }
        }

        let records = self.load_faithful_nullifier_records()?;
        let first = usize::try_from(manifest.first_nullifier_seq).map_err(|_| {
            StoreError::Integrity(
                "faithful-spend manifest first nullifier sequence does not fit usize".to_string(),
            )
        })?;
        let end = first.checked_add(authorities.len()).ok_or_else(|| {
            StoreError::Integrity("faithful-spend manifest nullifier interval overflow".to_string())
        })?;
        if end > records.len() {
            return Err(StoreError::Integrity(
                "faithful-spend manifest exceeds the durable nullifier accumulator".to_string(),
            ));
        }
        let mut set =
            dregg_cell::nullifier_set::NullifierSet::from_records(records[..first].iter().copied())
                .map_err(|error| {
                    StoreError::Integrity(format!(
                        "faithful-spend predecessor accumulator cannot be reconstructed: {error}"
                    ))
                })?;
        for (offset, authority) in authorities.iter().enumerate() {
            let (nullifier, value, seq) = records[first + offset];
            if nullifier.0 != authority.nullifier
                || value != authority.value
                || seq != authority.nullifier_seq
            {
                return Err(StoreError::Integrity(
                    "faithful-spend authority disagrees with its durable nullifier record"
                        .to_string(),
                ));
            }
            set.insert(nullifier, value).map_err(|_| {
                StoreError::Integrity(
                    "faithful-spend authority repeats a durable nullifier".to_string(),
                )
            })?;
            if set.faithful_root8_exact().to_bytes32() != authority.successor_nullifier_root {
                return Err(StoreError::Integrity(
                    "faithful-spend authority successor is not the exact durable prefix root"
                        .to_string(),
                ));
            }
        }
        if attested.nullifier_set_root != Some(set.faithful_root8_exact().to_bytes32()) {
            return Err(StoreError::Integrity(
                "faithful-spend turn interval does not end at its attested nullifier root"
                    .to_string(),
            ));
        }
        Ok(())
    }

    fn historical_faithful_root_is_durable(
        &self,
        height: u64,
        root: CanonicalFaithfulRoot,
    ) -> Result<bool> {
        let read = self.db.begin_read()?;
        let metadata = read.open_table(tables::METADATA_BYTES)?;
        if let Some(anchor_bytes) = metadata.get(tables::META_FAITHFUL_NOTE_ROOT_ANCHOR)? {
            let anchor = FaithfulNoteRootAnchorV1::from_bytes(anchor_bytes.value())
                .map_err(|error| StoreError::Integrity(error.to_string()))?;
            if anchor.height == height && anchor.root == root {
                return Ok(true);
            }
        }
        drop(metadata);
        let history = read.open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)?;
        let Some(envelope_bytes) = history.get(height)? else {
            return Ok(false);
        };
        let envelope = FaithfulNoteRootEnvelopeV1::from_bytes(envelope_bytes.value())
            .map_err(|error| StoreError::Integrity(error.to_string()))?;
        Ok(envelope.record.height == height && envelope.record.successor == root)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn encode_nullifier_record(value: u64, seq: u64) -> [u8; 16] {
        let mut out = [0u8; 16];
        out[..8].copy_from_slice(&value.to_le_bytes());
        out[8..].copy_from_slice(&seq.to_le_bytes());
        out
    }

    fn fixture_store_with_spends(
        store: PersistentStore,
        spends: &[([u8; 32], u64, u64)],
    ) -> (
        PersistentStore,
        CommitRecord,
        StoredAttestedRoot,
        Vec<FinalizedFaithfulSpendInput>,
    ) {
        let historical = CanonicalFaithfulRoot::from_bytes([1; 32]).unwrap();
        let anchor =
            FaithfulNoteRootAnchorV1::new([0x31; 32], [0x32; 32], 4, 7, 0, historical).unwrap();
        store
            .initialize_faithful_note_root_history(&anchor)
            .unwrap();

        let record = CommitRecord {
            ordinal: 0,
            height: 8,
            block_id: [0x41; 32],
            block_executed_up_to: 13,
            turn_hash: [0x42; 32],
            creator: [0x43; 32],
            receipt_hash: [0x44; 32],
            ledger_root: [0x45; 32],
            touched_cells: Vec::new(),
            removed: Vec::new(),
        };
        store.commit_finalized_turn(0, &record).unwrap();

        let mut nullifiers = dregg_cell::nullifier_set::NullifierSet::new();
        let mut inputs = Vec::new();
        for (nullifier, value, asset_type) in spends.iter().copied() {
            nullifiers
                .insert(dregg_cell::note::Nullifier(nullifier), value)
                .unwrap();
            inputs.push(FinalizedFaithfulSpendInput {
                root_height: anchor.height,
                historical_note_root: historical,
                nullifier,
                value,
                asset_type,
                successor_nullifier_root: CanonicalFaithfulRoot::from_bytes(
                    nullifiers.faithful_root8_exact().to_bytes32(),
                )
                .unwrap(),
            });
        }
        let final_nullifier_root = nullifiers.faithful_root8_exact().to_bytes32();

        let write = store.db.begin_write().unwrap();
        {
            let mut presence = write.open_table(tables::NULLIFIERS).unwrap();
            let mut records = write.open_table(tables::NULLIFIER_RECORDS_V1).unwrap();
            for (seq, (nullifier, value, _)) in spends.iter().copied().enumerate() {
                presence.insert(&nullifier, ()).unwrap();
                records
                    .insert(
                        &nullifier,
                        &encode_nullifier_record(value, u64::try_from(seq).unwrap()),
                    )
                    .unwrap();
            }
        }
        write.commit().unwrap();

        let attested = StoredAttestedRoot {
            merkle_root: record.ledger_root,
            note_tree_root: Some(historical.to_bytes()),
            nullifier_set_root: Some(final_nullifier_root),
            height: record.height,
            timestamp: 1_700_000_000,
            blocklace_block_id: Some(record.block_id),
            finality_round: Some(19),
            quorum_signatures: Vec::new(),
            threshold_qc: None,
            threshold: 1,
            federation_id: dregg_types::FederationId([0x32; 32]),
            receipt_stream_root: Some([0x46; 32]),
            finalization_quorum: Vec::new(),
        };
        store.store_attested_root(&attested).unwrap();
        (store, record, attested, inputs)
    }

    fn fixture_with_spends(
        spends: &[([u8; 32], u64, u64)],
    ) -> (
        PersistentStore,
        CommitRecord,
        StoredAttestedRoot,
        Vec<FinalizedFaithfulSpendInput>,
    ) {
        fixture_store_with_spends(PersistentStore::open_in_memory().unwrap(), spends)
    }

    fn fixture() -> (
        PersistentStore,
        CommitRecord,
        StoredAttestedRoot,
        FinalizedFaithfulSpendInput,
    ) {
        let (store, record, attested, mut inputs) = fixture_with_spends(&[([0x51; 32], 700, 9)]);
        (store, record, attested, inputs.remove(0))
    }

    #[test]
    fn persist_mints_exact_public_authority_and_replay_cannot_change_it() {
        let (store, record, attested, input) = fixture();
        let write = store.db.begin_write().unwrap();
        write_finalized_faithful_spends_in(
            &write,
            &record,
            &attested,
            std::slice::from_ref(&input),
            true,
        )
        .unwrap();
        write.commit().unwrap();

        let authority = store
            .finalized_faithful_spend(&input.nullifier)
            .unwrap()
            .unwrap();
        assert_eq!(authority.turn_hash(), record.turn_hash);
        assert_eq!(authority.turn_receipt_hash(), record.receipt_hash);
        assert_eq!(authority.spend_agent(), record.creator);
        assert_eq!(authority.spend_index(), 0);
        assert_eq!(authority.spend_count(), 1);
        assert_eq!(authority.nullifier_seq(), 0);
        assert_eq!(authority.root_height(), input.root_height);
        assert_eq!(
            authority.historical_note_root8(),
            input.historical_note_root.to_bytes()
        );
        assert_eq!(authority.nullifier(), input.nullifier);
        assert_eq!(authority.value(), input.value);
        assert_eq!(authority.asset_type(), input.asset_type);
        assert_eq!(
            authority.successor_nullifier_root8(),
            input.successor_nullifier_root.to_bytes()
        );
        assert_eq!(authority.finalized_height(), record.height);
        assert_eq!(authority.block_id(), record.block_id);
        assert_eq!(authority.federation_id(), attested.federation_id.0);
        assert_eq!(authority.finality_round(), attested.finality_round);
        assert_ne!(authority.authority_digest(), [0; 32]);
        assert_ne!(authority.attested_root_digest(), [0; 32]);

        let write = store.db.begin_write().unwrap();
        write_finalized_faithful_spends_in(
            &write,
            &record,
            &attested,
            std::slice::from_ref(&input),
            false,
        )
        .unwrap();
        write.commit().unwrap();

        let mut substituted = input;
        substituted.asset_type ^= 1;
        let write = store.db.begin_write().unwrap();
        assert!(
            write_finalized_faithful_spends_in(
                &write,
                &record,
                &attested,
                std::slice::from_ref(&substituted),
                false,
            )
            .is_err(),
            "idempotent replay must not change a public payment field"
        );
    }

    #[test]
    fn key_copy_truncation_and_empty_replay_are_refused() {
        let (store, record, attested, inputs) =
            fixture_with_spends(&[([0x51; 32], 700, 9), ([0x52; 32], 900, 10)]);
        let write = store.db.begin_write().unwrap();
        write_finalized_faithful_spends_in(&write, &record, &attested, &inputs, true).unwrap();
        write.commit().unwrap();

        let replay = store.db.begin_write().unwrap();
        assert!(
            write_finalized_faithful_spends_in(&replay, &record, &attested, &[], false).is_err(),
            "an empty exact replay must not erase the turn's durable spend cardinality"
        );
        drop(replay);

        let copied = {
            let read = store.db.begin_read().unwrap();
            let table = read.open_table(tables::FINALIZED_FAITHFUL_SPENDS).unwrap();
            table
                .get(&inputs[0].nullifier)
                .unwrap()
                .unwrap()
                .value()
                .to_vec()
        };
        let false_key = [0x77; 32];
        let write = store.db.begin_write().unwrap();
        {
            let mut table = write.open_table(tables::FINALIZED_FAITHFUL_SPENDS).unwrap();
            table.insert(&false_key, copied.as_slice()).unwrap();
        }
        write.commit().unwrap();
        assert!(
            store.finalized_faithful_spend(&false_key).is_err(),
            "a valid row copied under a different nullifier key must fail closed"
        );

        let write = store.db.begin_write().unwrap();
        {
            let mut table = write.open_table(tables::FINALIZED_FAITHFUL_SPENDS).unwrap();
            table.remove(&false_key).unwrap();
            table.remove(&inputs[1].nullifier).unwrap();
        }
        write.commit().unwrap();
        assert!(
            store
                .finalized_faithful_spends_for_turn(&record.turn_hash)
                .is_err(),
            "manifest cardinality must expose a truncated authority suffix"
        );
    }

    #[test]
    fn checkpoint_compaction_keeps_manifest_authority_loadable() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("faithful-spend.redb");
        let (store, record, attested, mut inputs) = fixture_store_with_spends(
            PersistentStore::open(&path).unwrap(),
            &[([0x51; 32], 700, 9)],
        );
        let input = inputs.remove(0);
        let write = store.db.begin_write().unwrap();
        write_finalized_faithful_spends_in(
            &write,
            &record,
            &attested,
            std::slice::from_ref(&input),
            true,
        )
        .unwrap();
        write.commit().unwrap();

        store
            .checkpoint_ledger(&dregg_cell::Ledger::new(), record.height + 1)
            .unwrap();
        assert!(store.lookup_turn(&record.turn_hash).unwrap().is_none());
        drop(store);

        let reopened = PersistentStore::open(&path).unwrap();
        let authority = reopened
            .finalized_faithful_spend(&input.nullifier)
            .unwrap()
            .expect("compacted authority survives restart through manifest custody");
        assert_eq!(authority.turn_hash(), record.turn_hash);
        assert_eq!(authority.nullifier(), input.nullifier);
        assert_eq!(
            authority.successor_nullifier_root8(),
            attested.nullifier_set_root.unwrap()
        );
    }
}
