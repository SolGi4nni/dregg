//! Atomic one-shot consumption of a Path of Angels holding capability.
//!
//! The Solana admission service issues a short-lived opaque receipt, but it is
//! not allowed to spend that receipt in an HTTP transaction.  A spend becomes
//! authoritative only here: beside the exact finalized Dregg turn, receipt,
//! and Lean-authored PoA event in the central redb transaction.  The reverse
//! index makes omission and invention on idempotent replay observable.

use redb::{ReadableTable, ReadableTableMetadata, TableDefinition, WriteTransaction};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

use crate::{CommitRecord, PersistentStore, Result, StoreError, tables};

pub(crate) const POA_HOLDING_CONSUMPTIONS_V1: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("poa_holding_consumptions_v1");
pub(crate) const POA_HOLDING_CONSUMPTION_BY_COMMIT_ORDINAL_V1: TableDefinition<u64, &[u8; 32]> =
    TableDefinition::new("poa_holding_consumption_by_commit_ordinal_v1");
pub(crate) const POA_HOLDING_CONSUMPTION_BY_EVENT_SCOPE_V1: TableDefinition<&[u8; 32], &[u8; 32]> =
    TableDefinition::new("poa_holding_consumption_by_event_scope_v1");

const WIRE_DOMAIN: &[u8] = b"dregg-poa-holding-consumption-v1\0";
const EVENT_SCOPE_DOMAIN: &[u8] = b"dregg-poa-holding-event-scope-v1\0";
const INTENT_EVENT_DOMAIN: &[u8] = b"dregg-poa-holding-intent-event-v1\0";
const MAX_WIRE_BYTES: usize = 4096;

/// Finalization input prepared only after the node has matched an active V2
/// capability to the validated SignedTurn signer and signer-derived agent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedPoaHoldingConsumptionV1 {
    capability_receipt_id: [u8; 32],
    holder_wallet: [u8; 32],
    player: [u8; 32],
    player_cell: [u8; 32],
    action_token: [u8; 32],
    beneficiary_player_id: [u8; 32],
    world_federation_id: [u8; 32],
    content_root: [u8; 32],
    activation_digest: [u8; 32],
    content_session: [u8; 32],
    content_epoch: u64,
    event_scope_nullifier: [u8; 32],
    intent_event_binding: [u8; 32],
    commit_ordinal: u64,
    turn_hash: [u8; 32],
    receipt_hash: [u8; 32],
    poa_batch_digest: [u8; 32],
    poa_event_index: u32,
    poa_stream_digest: [u8; 32],
    poa_event_sequence: u64,
    poa_event_digest: [u8; 32],
}

impl PreparedPoaHoldingConsumptionV1 {
    /// Crate-private raw construction is deliberate.  The public persistence
    /// API may consume this carrier but neither another crate nor serde can
    /// mint one from attacker-authored coordinates.  A production authority
    /// adapter must eventually move into this crate (or supply a sealed proof),
    /// so the currently unreachable sponsorship path stays fail-closed.
    pub(crate) fn new(
        capability_receipt_id: [u8; 32],
        holder_wallet: [u8; 32],
        player: [u8; 32],
        player_cell: [u8; 32],
        action_token: [u8; 32],
        beneficiary_player_id: [u8; 32],
        batch: &crate::PreparedPoaEventBatchV2,
        poa_event_index: u32,
    ) -> Result<Self> {
        let coordinate = batch.coordinate();
        let world = coordinate.world();
        let event = batch
            .events()
            .get(usize::try_from(poa_event_index).map_err(|_| {
                integrity("PoA holding event index does not fit the native platform")
            })?)
            .ok_or_else(|| integrity("PoA holding event index is absent from its batch"))?;
        if event.event_index() != poa_event_index {
            return Err(integrity("PoA holding event index is not canonical"));
        }
        let event_scope_nullifier = derive_poa_holding_event_scope_nullifier_v1(
            holder_wallet,
            world.federation_id(),
            world.content_root(),
            world.activation_digest(),
            world.content_session(),
            world.content_epoch(),
            batch.batch_digest(),
            event.event_index(),
            event.stream_digest(),
            event.sequence(),
            event.event_digest(),
        );
        let intent_event_binding = derive_poa_holding_intent_event_binding_v1(
            capability_receipt_id,
            holder_wallet,
            player,
            player_cell,
            action_token,
            beneficiary_player_id,
            world.federation_id(),
            world.content_root(),
            world.activation_digest(),
            world.content_session(),
            world.content_epoch(),
            batch.batch_digest(),
            event.event_index(),
            event.stream_digest(),
            event.sequence(),
            event.event_digest(),
        );
        let prepared = Self {
            capability_receipt_id,
            holder_wallet,
            player,
            player_cell,
            action_token,
            beneficiary_player_id,
            world_federation_id: world.federation_id(),
            content_root: world.content_root(),
            activation_digest: world.activation_digest(),
            content_session: world.content_session(),
            content_epoch: world.content_epoch(),
            event_scope_nullifier,
            intent_event_binding,
            commit_ordinal: coordinate.commit_ordinal(),
            turn_hash: coordinate.turn_hash(),
            receipt_hash: coordinate.receipt_hash(),
            poa_batch_digest: batch.batch_digest(),
            poa_event_index,
            poa_stream_digest: event.stream_digest(),
            poa_event_sequence: event.sequence(),
            poa_event_digest: event.event_digest(),
        };
        prepared.validate()?;
        Ok(prepared)
    }

    pub const fn capability_receipt_id(&self) -> [u8; 32] {
        self.capability_receipt_id
    }

    pub const fn player(&self) -> [u8; 32] {
        self.player
    }

    pub const fn player_cell(&self) -> [u8; 32] {
        self.player_cell
    }

    pub const fn holder_wallet(&self) -> [u8; 32] {
        self.holder_wallet
    }

    pub const fn action_token(&self) -> [u8; 32] {
        self.action_token
    }

    pub const fn beneficiary_player_id(&self) -> [u8; 32] {
        self.beneficiary_player_id
    }

    pub const fn event_scope_nullifier(&self) -> [u8; 32] {
        self.event_scope_nullifier
    }
    pub const fn intent_event_binding(&self) -> [u8; 32] {
        self.intent_event_binding
    }

    #[cfg(test)]
    pub(crate) fn new_for_legacy_event_test(
        capability_receipt_id: [u8; 32],
        player: [u8; 32],
        player_cell: [u8; 32],
        record: &CommitRecord,
        event: &crate::PreparedPoaEventEnvelopeV1,
        poa_stream_digest: [u8; 32],
    ) -> Result<Self> {
        let holder_wallet = [capability_receipt_id[0].wrapping_add(1); 32];
        let world_federation_id = [0xF1; 32];
        let content_root = [0xF2; 32];
        let activation_digest = [0xF3; 32];
        let content_session = [0xF4; 32];
        let content_epoch = 1;
        let event_scope_nullifier = derive_poa_holding_event_scope_nullifier_v1(
            holder_wallet,
            world_federation_id,
            content_root,
            activation_digest,
            content_session,
            content_epoch,
            event.event_digest(),
            0,
            poa_stream_digest,
            event.sequence(),
            event.event_digest(),
        );
        let prepared = Self {
            capability_receipt_id,
            holder_wallet,
            player,
            player_cell,
            action_token: [0xF5; 32],
            beneficiary_player_id: [0xF6; 32],
            world_federation_id,
            content_root,
            activation_digest,
            content_session,
            content_epoch,
            event_scope_nullifier,
            intent_event_binding: derive_poa_holding_intent_event_binding_v1(
                capability_receipt_id,
                holder_wallet,
                player,
                player_cell,
                [0xF5; 32],
                [0xF6; 32],
                world_federation_id,
                content_root,
                activation_digest,
                content_session,
                content_epoch,
                event.event_digest(),
                0,
                poa_stream_digest,
                event.sequence(),
                event.event_digest(),
            ),
            commit_ordinal: record.ordinal,
            turn_hash: record.turn_hash,
            receipt_hash: record.receipt_hash,
            poa_batch_digest: event.event_digest(),
            poa_event_index: 0,
            poa_stream_digest,
            poa_event_sequence: event.sequence(),
            poa_event_digest: event.event_digest(),
        };
        prepared.validate()?;
        Ok(prepared)
    }

    pub(crate) fn matches_poa_event(&self, event: &crate::PreparedPoaEventEnvelopeV1) -> bool {
        self.poa_batch_digest == event.event_digest()
            && self.poa_event_index == 0
            && self.poa_stream_digest == event.stream_digest()
            && self.poa_event_sequence == event.sequence()
            && self.poa_event_digest == event.event_digest()
    }

    pub(crate) fn matches_poa_batch(&self, batch: &crate::PreparedPoaEventBatchV2) -> bool {
        let world = batch.coordinate().world();
        let signer = batch.coordinate().signer();
        let signer_cell =
            dregg_cell::CellId::derive_raw(&signer, blake3::hash(b"default").as_bytes());
        if self.poa_batch_digest != batch.batch_digest()
            || self.player != signer
            || self.player_cell != signer_cell.0
            || self.world_federation_id != world.federation_id()
            || self.content_root != world.content_root()
            || self.activation_digest != world.activation_digest()
            || self.content_session != world.content_session()
            || self.content_epoch != world.content_epoch()
        {
            return false;
        }
        let mut matching = batch.events().iter().filter(|event| {
            self.poa_event_index == event.event_index()
                && self.poa_stream_digest == event.stream_digest()
                && self.poa_event_sequence == event.sequence()
                && self.poa_event_digest == event.event_digest()
        });
        let Some(event) = matching.next() else {
            return false;
        };
        matching.next().is_none()
            && self.event_scope_nullifier
                == derive_poa_holding_event_scope_nullifier_v1(
                    self.holder_wallet,
                    world.federation_id(),
                    world.content_root(),
                    world.activation_digest(),
                    world.content_session(),
                    world.content_epoch(),
                    batch.batch_digest(),
                    event.event_index(),
                    event.stream_digest(),
                    event.sequence(),
                    event.event_digest(),
                )
            && self.intent_event_binding
                == derive_poa_holding_intent_event_binding_v1(
                    self.capability_receipt_id,
                    self.holder_wallet,
                    self.player,
                    self.player_cell,
                    self.action_token,
                    self.beneficiary_player_id,
                    world.federation_id(),
                    world.content_root(),
                    world.activation_digest(),
                    world.content_session(),
                    world.content_epoch(),
                    batch.batch_digest(),
                    event.event_index(),
                    event.stream_digest(),
                    event.sequence(),
                    event.event_digest(),
                )
    }

    fn validate(&self) -> Result<()> {
        if self.capability_receipt_id == [0; 32]
            || self.holder_wallet == [0; 32]
            || self.player == [0; 32]
            || self.player_cell == [0; 32]
            || self.action_token == [0; 32]
            || self.beneficiary_player_id == [0; 32]
            || self.world_federation_id == [0; 32]
            || self.content_root == [0; 32]
            || self.activation_digest == [0; 32]
            || self.content_session == [0; 32]
            || self.content_epoch == 0
            || self.event_scope_nullifier == [0; 32]
            || self.intent_event_binding == [0; 32]
            || self.poa_batch_digest == [0; 32]
            || self.poa_stream_digest == [0; 32]
            || self.poa_event_sequence == 0
            || self.poa_event_digest == [0; 32]
        {
            return Err(integrity(
                "PoA holding consumption has a zero capability/player identity",
            ));
        }
        Ok(())
    }
}

/// Derive the one-per-wallet holder-service nullifier for one exact event in an
/// activated world.  Player, action token, beneficiary, and capability id are
/// deliberately excluded: changing any of those cannot multiply one wallet's
/// entitlement to the same event.  The exact batch/event coordinates are
/// included so using holder voice once does not permanently burn that wallet
/// for every later event on the same stream.
#[allow(clippy::too_many_arguments)]
pub fn derive_poa_holding_event_scope_nullifier_v1(
    holder_wallet: [u8; 32],
    federation_id: [u8; 32],
    content_root: [u8; 32],
    activation_digest: [u8; 32],
    content_session: [u8; 32],
    content_epoch: u64,
    batch_digest: [u8; 32],
    event_index: u32,
    poa_stream_digest: [u8; 32],
    event_sequence: u64,
    event_digest: [u8; 32],
) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(EVENT_SCOPE_DOMAIN);
    hasher.update(holder_wallet);
    hasher.update(federation_id);
    hasher.update(content_root);
    hasher.update(activation_digest);
    hasher.update(content_session);
    hasher.update(content_epoch.to_be_bytes());
    hasher.update(batch_digest);
    hasher.update(event_index.to_be_bytes());
    hasher.update(poa_stream_digest);
    hasher.update(event_sequence.to_be_bytes());
    hasher.update(event_digest);
    hasher.finalize().into()
}

/// Commit one authorized holder intent to one exact activated-world event.
/// This digest is not an authority substitute; it is the byte-exact join which
/// a Lean/game authority must reproduce before persistence can ever expose a
/// production constructor for the prepared carrier.
#[allow(clippy::too_many_arguments)]
pub fn derive_poa_holding_intent_event_binding_v1(
    capability_receipt_id: [u8; 32],
    holder_wallet: [u8; 32],
    player: [u8; 32],
    player_cell: [u8; 32],
    action_token: [u8; 32],
    beneficiary_player_id: [u8; 32],
    federation_id: [u8; 32],
    content_root: [u8; 32],
    activation_digest: [u8; 32],
    content_session: [u8; 32],
    content_epoch: u64,
    batch_digest: [u8; 32],
    event_index: u32,
    stream_digest: [u8; 32],
    event_sequence: u64,
    event_digest: [u8; 32],
) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(INTENT_EVENT_DOMAIN);
    hasher.update(capability_receipt_id);
    hasher.update(holder_wallet);
    hasher.update(player);
    hasher.update(player_cell);
    hasher.update(action_token);
    hasher.update(beneficiary_player_id);
    hasher.update(federation_id);
    hasher.update(content_root);
    hasher.update(activation_digest);
    hasher.update(content_session);
    hasher.update(content_epoch.to_be_bytes());
    hasher.update(batch_digest);
    hasher.update(event_index.to_be_bytes());
    hasher.update(stream_digest);
    hasher.update(event_sequence.to_be_bytes());
    hasher.update(event_digest);
    hasher.finalize().into()
}

/// Exact durable consumer of one otherwise unlinkable holding capability.
/// This record is node-internal and is never part of the public game status.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PoaHoldingConsumptionV1 {
    capability_receipt_id: [u8; 32],
    holder_wallet: [u8; 32],
    player: [u8; 32],
    player_cell: [u8; 32],
    action_token: [u8; 32],
    beneficiary_player_id: [u8; 32],
    world_federation_id: [u8; 32],
    content_root: [u8; 32],
    activation_digest: [u8; 32],
    content_session: [u8; 32],
    content_epoch: u64,
    event_scope_nullifier: [u8; 32],
    intent_event_binding: [u8; 32],
    commit_ordinal: u64,
    block_id: [u8; 32],
    turn_hash: [u8; 32],
    receipt_hash: [u8; 32],
    poa_batch_digest: [u8; 32],
    poa_event_index: u32,
    poa_stream_digest: [u8; 32],
    poa_event_sequence: u64,
    poa_event_digest: [u8; 32],
}

impl PoaHoldingConsumptionV1 {
    pub const fn capability_receipt_id(&self) -> [u8; 32] {
        self.capability_receipt_id
    }
    pub const fn commit_ordinal(&self) -> u64 {
        self.commit_ordinal
    }
    pub const fn turn_hash(&self) -> [u8; 32] {
        self.turn_hash
    }
    pub const fn receipt_hash(&self) -> [u8; 32] {
        self.receipt_hash
    }
    pub const fn holder_wallet(&self) -> [u8; 32] {
        self.holder_wallet
    }
    pub const fn action_token(&self) -> [u8; 32] {
        self.action_token
    }
    pub const fn beneficiary_player_id(&self) -> [u8; 32] {
        self.beneficiary_player_id
    }
    pub const fn event_scope_nullifier(&self) -> [u8; 32] {
        self.event_scope_nullifier
    }
    pub const fn intent_event_binding(&self) -> [u8; 32] {
        self.intent_event_binding
    }

    fn encode(&self) -> Result<Vec<u8>> {
        let payload = postcard::to_stdvec(self)
            .map_err(|error| StoreError::Serialization(error.to_string()))?;
        if payload.len() > MAX_WIRE_BYTES {
            return Err(integrity("PoA holding consumption wire exceeds its bound"));
        }
        let mut wire = payload;
        wire.extend_from_slice(&seal(&wire));
        Ok(wire)
    }

    fn decode(wire: &[u8]) -> Result<Self> {
        if wire.len() < 32 || wire.len() > MAX_WIRE_BYTES + 32 {
            return Err(integrity("PoA holding consumption wire length is invalid"));
        }
        let split = wire.len() - 32;
        let (payload, supplied_seal) = wire.split_at(split);
        if seal(payload).as_slice() != supplied_seal {
            return Err(integrity("PoA holding consumption seal mismatch"));
        }
        let decoded: Self = postcard::from_bytes(payload)
            .map_err(|error| StoreError::Serialization(error.to_string()))?;
        if decoded.capability_receipt_id == [0; 32]
            || decoded.holder_wallet == [0; 32]
            || decoded.player == [0; 32]
            || decoded.player_cell == [0; 32]
            || decoded.action_token == [0; 32]
            || decoded.beneficiary_player_id == [0; 32]
            || decoded.world_federation_id == [0; 32]
            || decoded.content_root == [0; 32]
            || decoded.activation_digest == [0; 32]
            || decoded.content_session == [0; 32]
            || decoded.content_epoch == 0
            || decoded.event_scope_nullifier == [0; 32]
            || decoded.intent_event_binding == [0; 32]
            || decoded.poa_batch_digest == [0; 32]
            || decoded.poa_stream_digest == [0; 32]
            || decoded.poa_event_sequence == 0
            || decoded.poa_event_digest == [0; 32]
        {
            return Err(integrity("PoA holding consumption identity is invalid"));
        }
        let expected_nullifier = derive_poa_holding_event_scope_nullifier_v1(
            decoded.holder_wallet,
            decoded.world_federation_id,
            decoded.content_root,
            decoded.activation_digest,
            decoded.content_session,
            decoded.content_epoch,
            decoded.poa_batch_digest,
            decoded.poa_event_index,
            decoded.poa_stream_digest,
            decoded.poa_event_sequence,
            decoded.poa_event_digest,
        );
        if decoded.event_scope_nullifier != expected_nullifier {
            return Err(integrity(
                "PoA holding consumption event-scope nullifier is not canonical",
            ));
        }
        let expected_binding = derive_poa_holding_intent_event_binding_v1(
            decoded.capability_receipt_id,
            decoded.holder_wallet,
            decoded.player,
            decoded.player_cell,
            decoded.action_token,
            decoded.beneficiary_player_id,
            decoded.world_federation_id,
            decoded.content_root,
            decoded.activation_digest,
            decoded.content_session,
            decoded.content_epoch,
            decoded.poa_batch_digest,
            decoded.poa_event_index,
            decoded.poa_stream_digest,
            decoded.poa_event_sequence,
            decoded.poa_event_digest,
        );
        if decoded.intent_event_binding != expected_binding {
            return Err(integrity(
                "PoA holding consumption intent/event binding is not canonical",
            ));
        }
        Ok(decoded)
    }
}

impl PersistentStore {
    pub fn load_poa_holding_consumption(
        &self,
        capability_receipt_id: &[u8; 32],
    ) -> Result<Option<PoaHoldingConsumptionV1>> {
        let read = self.db.begin_read()?;
        let rows = read.open_table(POA_HOLDING_CONSUMPTIONS_V1)?;
        let Some(wire) = rows.get(capability_receipt_id)? else {
            return Ok(None);
        };
        let decoded = PoaHoldingConsumptionV1::decode(wire.value())?;
        if decoded.capability_receipt_id != *capability_receipt_id {
            return Err(integrity("PoA holding consumption key/wire mismatch"));
        }
        Ok(Some(decoded))
    }

    pub fn audit_poa_holding_consumptions(&self) -> Result<()> {
        let read = self.db.begin_read()?;
        let rows = read.open_table(POA_HOLDING_CONSUMPTIONS_V1)?;
        let reverse = read.open_table(POA_HOLDING_CONSUMPTION_BY_COMMIT_ORDINAL_V1)?;
        let event_scopes = read.open_table(POA_HOLDING_CONSUMPTION_BY_EVENT_SCOPE_V1)?;
        let commits = read.open_table(tables::COMMIT_LOG)?;
        let metadata = read.open_table(tables::METADATA)?;
        let compacted_floor = metadata
            .get(tables::META_COMMIT_COMPACTED)?
            .map(|value| value.value())
            .unwrap_or(0);
        let compacted = crate::poa_compact_authority::load_audited_certificates_in_read(
            &read,
            compacted_floor,
        )?;
        let mut row_count = 0_u64;
        for entry in rows.iter()? {
            let (key, wire) = entry.map_err(db_error)?;
            let decoded = PoaHoldingConsumptionV1::decode(wire.value())?;
            if decoded.capability_receipt_id != *key.value() {
                return Err(integrity("PoA holding consumption key/wire mismatch"));
            }
            let reverse_id = reverse
                .get(decoded.commit_ordinal)?
                .ok_or_else(|| integrity("PoA holding consumption omitted reverse index"))?;
            if *reverse_id.value() != decoded.capability_receipt_id {
                return Err(integrity("PoA holding consumption reverse index mismatch"));
            }
            let scoped_id = event_scopes
                .get(&decoded.event_scope_nullifier)?
                .ok_or_else(|| integrity("PoA holding consumption omitted event-scope index"))?;
            if *scoped_id.value() != decoded.capability_receipt_id {
                return Err(integrity(
                    "PoA holding consumption event-scope index mismatch",
                ));
            }
            match commits.get(decoded.commit_ordinal)? {
                Some(commit) => {
                    let commit = crate::commit_log::decode_commit_record(commit.value())?;
                    if commit.block_id != decoded.block_id
                        || commit.turn_hash != decoded.turn_hash
                        || commit.receipt_hash != decoded.receipt_hash
                    {
                        return Err(integrity(
                            "PoA holding consumption disagrees with generic commit",
                        ));
                    }
                }
                None if decoded.commit_ordinal < compacted_floor => {
                    let certificate = compacted.get(&decoded.commit_ordinal).ok_or_else(|| {
                        integrity("PoA holding consumption has no compact authority certificate")
                    })?;
                    let identity =
                        crate::poa_compact_authority::holding_identity(key.value(), wire.value())?;
                    if !certificate.matches_block_carrier(
                        decoded.commit_ordinal,
                        decoded.block_id,
                        decoded.turn_hash,
                        decoded.receipt_hash,
                    ) || !certificate.has_sidecar(&identity)
                    {
                        return Err(integrity(
                            "compacted PoA holding consumption disagrees with its certified carrier",
                        ));
                    }
                }
                None => {
                    return Err(integrity(
                        "PoA holding consumption has no generic commit carrier",
                    ));
                }
            }
            row_count = row_count
                .checked_add(1)
                .ok_or_else(|| integrity("PoA holding consumption count overflow"))?;
        }
        if reverse.len()? != row_count {
            return Err(integrity(
                "PoA holding consumption reverse index has invention",
            ));
        }
        if event_scopes.len()? != row_count {
            return Err(integrity(
                "PoA holding consumption event-scope index has invention",
            ));
        }
        Ok(())
    }
}

pub(crate) fn initialize_poa_holding_consumption_tables_in(write: &WriteTransaction) -> Result<()> {
    let _ = write.open_table(POA_HOLDING_CONSUMPTIONS_V1)?;
    let _ = write.open_table(POA_HOLDING_CONSUMPTION_BY_COMMIT_ORDINAL_V1)?;
    let _ = write.open_table(POA_HOLDING_CONSUMPTION_BY_EVENT_SCOPE_V1)?;
    Ok(())
}

pub(crate) fn stage_fresh_poa_holding_consumption_in(
    write: &WriteTransaction,
    commit_ordinal: u64,
    record: &CommitRecord,
    prepared: &PreparedPoaHoldingConsumptionV1,
) -> Result<()> {
    prepared.validate()?;
    if record.ordinal != commit_ordinal
        || prepared.commit_ordinal != commit_ordinal
        || prepared.turn_hash != record.turn_hash
        || prepared.receipt_hash != record.receipt_hash
    {
        return Err(integrity(
            "PoA holding consumption disagrees with carrying commit coordinates",
        ));
    }
    let stored = plan(record, prepared);
    let wire = stored.encode()?;
    {
        let rows = write.open_table(POA_HOLDING_CONSUMPTIONS_V1)?;
        if rows.get(&prepared.capability_receipt_id)?.is_some() {
            return Err(integrity("PoA holding capability already has a consumer"));
        }
        let reverse = write.open_table(POA_HOLDING_CONSUMPTION_BY_COMMIT_ORDINAL_V1)?;
        if reverse.get(commit_ordinal)?.is_some() {
            return Err(integrity(
                "fresh commit ordinal already consumes a PoA holding capability",
            ));
        }
        let event_scopes = write.open_table(POA_HOLDING_CONSUMPTION_BY_EVENT_SCOPE_V1)?;
        if event_scopes.get(&prepared.event_scope_nullifier)?.is_some() {
            return Err(integrity(
                "PoA holder wallet already consumed this activated event scope",
            ));
        }
    }
    let mut rows = write.open_table(POA_HOLDING_CONSUMPTIONS_V1)?;
    rows.insert(&prepared.capability_receipt_id, wire.as_slice())?;
    let mut reverse = write.open_table(POA_HOLDING_CONSUMPTION_BY_COMMIT_ORDINAL_V1)?;
    reverse.insert(commit_ordinal, &prepared.capability_receipt_id)?;
    let mut event_scopes = write.open_table(POA_HOLDING_CONSUMPTION_BY_EVENT_SCOPE_V1)?;
    event_scopes.insert(
        &prepared.event_scope_nullifier,
        &prepared.capability_receipt_id,
    )?;
    Ok(())
}

pub(crate) fn verify_replayed_poa_holding_consumption_in(
    write: &WriteTransaction,
    commit_ordinal: u64,
    record: &CommitRecord,
    prepared: Option<&PreparedPoaHoldingConsumptionV1>,
) -> Result<()> {
    let indexed = {
        let reverse = write.open_table(POA_HOLDING_CONSUMPTION_BY_COMMIT_ORDINAL_V1)?;
        reverse.get(commit_ordinal)?.map(|entry| *entry.value())
    };
    let (Some(prepared), Some(indexed_id)) = (prepared, indexed) else {
        return match (prepared.is_some(), indexed.is_some()) {
            (false, false) => Ok(()),
            _ => Err(integrity(
                "replayed finalized turn omitted or invented its PoA holding consumption weld",
            )),
        };
    };
    if indexed_id != prepared.capability_receipt_id {
        return Err(integrity(
            "replayed PoA holding consumption names a different capability",
        ));
    }
    let scoped_id = {
        let event_scopes = write.open_table(POA_HOLDING_CONSUMPTION_BY_EVENT_SCOPE_V1)?;
        event_scopes
            .get(&prepared.event_scope_nullifier)?
            .map(|entry| *entry.value())
    };
    if scoped_id != Some(prepared.capability_receipt_id) {
        return Err(integrity(
            "replayed PoA holding consumption event-scope index disagrees",
        ));
    }
    let stored_wire = {
        let rows = write.open_table(POA_HOLDING_CONSUMPTIONS_V1)?;
        rows.get(&indexed_id)?
            .ok_or_else(|| integrity("PoA holding reverse index points to no row"))?
            .value()
            .to_vec()
    };
    let expected = plan(record, prepared).encode()?;
    if stored_wire != expected {
        return Err(integrity(
            "replayed PoA holding consumption is not byte-identical",
        ));
    }
    Ok(())
}

pub(crate) fn truncate_poa_holding_consumptions_in(
    write: &WriteTransaction,
    new_cursor: u64,
) -> Result<u64> {
    let doomed_ids: Vec<(u64, [u8; 32])> = {
        let reverse = write.open_table(POA_HOLDING_CONSUMPTION_BY_COMMIT_ORDINAL_V1)?;
        reverse
            .range(new_cursor..)?
            .map(|entry| {
                entry
                    .map(|(ordinal, id)| (ordinal.value(), *id.value()))
                    .map_err(db_error)
            })
            .collect::<Result<_>>()?
    };
    let doomed: Vec<(u64, [u8; 32], [u8; 32])> = {
        let rows = write.open_table(POA_HOLDING_CONSUMPTIONS_V1)?;
        doomed_ids
            .into_iter()
            .map(|(ordinal, id)| {
                let wire = rows
                    .get(&id)?
                    .ok_or_else(|| integrity("PoA holding rewind index points to no row"))?;
                let decoded = PoaHoldingConsumptionV1::decode(wire.value())?;
                Ok((ordinal, id, decoded.event_scope_nullifier))
            })
            .collect::<Result<_>>()?
    };
    let mut rows = write.open_table(POA_HOLDING_CONSUMPTIONS_V1)?;
    let mut reverse = write.open_table(POA_HOLDING_CONSUMPTION_BY_COMMIT_ORDINAL_V1)?;
    let mut event_scopes = write.open_table(POA_HOLDING_CONSUMPTION_BY_EVENT_SCOPE_V1)?;
    for (ordinal, id, event_scope_nullifier) in &doomed {
        rows.remove(id)?;
        reverse.remove(*ordinal)?;
        let removed = event_scopes.remove(event_scope_nullifier)?;
        if removed.as_ref().map(|entry| *entry.value()) != Some(*id) {
            return Err(integrity(
                "PoA holding rewind event-scope index disagrees with row",
            ));
        }
    }
    u64::try_from(doomed.len()).map_err(|_| integrity("PoA holding rewind count exceeds u64"))
}

fn plan(
    record: &CommitRecord,
    prepared: &PreparedPoaHoldingConsumptionV1,
) -> PoaHoldingConsumptionV1 {
    PoaHoldingConsumptionV1 {
        capability_receipt_id: prepared.capability_receipt_id,
        holder_wallet: prepared.holder_wallet,
        player: prepared.player,
        player_cell: prepared.player_cell,
        action_token: prepared.action_token,
        beneficiary_player_id: prepared.beneficiary_player_id,
        world_federation_id: prepared.world_federation_id,
        content_root: prepared.content_root,
        activation_digest: prepared.activation_digest,
        content_session: prepared.content_session,
        content_epoch: prepared.content_epoch,
        event_scope_nullifier: prepared.event_scope_nullifier,
        intent_event_binding: prepared.intent_event_binding,
        commit_ordinal: prepared.commit_ordinal,
        block_id: record.block_id,
        turn_hash: prepared.turn_hash,
        receipt_hash: prepared.receipt_hash,
        poa_batch_digest: prepared.poa_batch_digest,
        poa_event_index: prepared.poa_event_index,
        poa_stream_digest: prepared.poa_stream_digest,
        poa_event_sequence: prepared.poa_event_sequence,
        poa_event_digest: prepared.poa_event_digest,
    }
}

fn seal(payload: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(WIRE_DOMAIN);
    hasher.update(payload);
    hasher.finalize().into()
}

fn integrity(message: impl Into<String>) -> StoreError {
    StoreError::Integrity(message.into())
}

fn db_error(error: redb::StorageError) -> StoreError {
    StoreError::Database(error.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn record(ordinal: u64) -> CommitRecord {
        CommitRecord {
            ordinal,
            height: ordinal + 1,
            block_id: [ordinal as u8 + 1; 32],
            block_executed_up_to: ordinal,
            turn_hash: [ordinal as u8 + 2; 32],
            creator: [ordinal as u8 + 3; 32],
            receipt_hash: [ordinal as u8 + 4; 32],
            ledger_root: [ordinal as u8 + 5; 32],
            touched_cells: Vec::new(),
            removed: Vec::new(),
        }
    }

    fn prepared(
        capability: u8,
        wallet: [u8; 32],
        player: u8,
        action: u8,
        beneficiary: u8,
        record: &CommitRecord,
        event_ordinal: u64,
    ) -> PreparedPoaHoldingConsumptionV1 {
        let world_federation_id = [0x91; 32];
        let content_root = [0x92; 32];
        let activation_digest = [0x93; 32];
        let content_session = [0x94; 32];
        let content_epoch = 7;
        let poa_stream_digest = [0x95; 32];
        let poa_batch_digest = [0x96; 32];
        let poa_event_index = 0;
        let poa_event_sequence = event_ordinal + 1;
        let poa_event_digest = [ordinal_byte(event_ordinal, 0x97); 32];
        let player_id = [player; 32];
        let player_cell = [player.wrapping_add(1); 32];
        let action_token = [action; 32];
        let beneficiary_player_id = [beneficiary; 32];
        let event_scope_nullifier = derive_poa_holding_event_scope_nullifier_v1(
            wallet,
            world_federation_id,
            content_root,
            activation_digest,
            content_session,
            content_epoch,
            poa_batch_digest,
            poa_event_index,
            poa_stream_digest,
            poa_event_sequence,
            poa_event_digest,
        );
        let intent_event_binding = derive_poa_holding_intent_event_binding_v1(
            [capability; 32],
            wallet,
            player_id,
            player_cell,
            action_token,
            beneficiary_player_id,
            world_federation_id,
            content_root,
            activation_digest,
            content_session,
            content_epoch,
            poa_batch_digest,
            poa_event_index,
            poa_stream_digest,
            poa_event_sequence,
            poa_event_digest,
        );
        PreparedPoaHoldingConsumptionV1 {
            capability_receipt_id: [capability; 32],
            holder_wallet: wallet,
            player: player_id,
            player_cell,
            action_token,
            beneficiary_player_id,
            world_federation_id,
            content_root,
            activation_digest,
            content_session,
            content_epoch,
            event_scope_nullifier,
            intent_event_binding,
            commit_ordinal: record.ordinal,
            turn_hash: record.turn_hash,
            receipt_hash: record.receipt_hash,
            poa_batch_digest,
            poa_event_index,
            poa_stream_digest,
            poa_event_sequence,
            poa_event_digest,
        }
    }

    fn ordinal_byte(ordinal: u64, base: u8) -> u8 {
        base.wrapping_add(u8::try_from(ordinal).expect("small test ordinal"))
    }

    #[test]
    fn event_scope_nullifier_ignores_capability_actor_action_and_beneficiary() {
        let first = record(0);
        let second = record(1);
        let wallet = [0x41; 32];
        let a = prepared(0x51, wallet, 0x61, 0x71, 0x81, &first, 0);
        let redirected = prepared(0x52, wallet, 0x62, 0x72, 0x82, &second, 0);
        let later_event = prepared(0x53, wallet, 0x63, 0x73, 0x83, &second, 1);
        assert_eq!(a.event_scope_nullifier, redirected.event_scope_nullifier);
        assert_ne!(a.capability_receipt_id, redirected.capability_receipt_id);
        assert_ne!(a.player, redirected.player);
        assert_ne!(a.action_token, redirected.action_token);
        assert_ne!(a.beneficiary_player_id, redirected.beneficiary_player_id);
        assert_ne!(a.intent_event_binding, redirected.intent_event_binding);
        assert_ne!(a.event_scope_nullifier, later_event.event_scope_nullifier);
    }

    #[test]
    fn second_capability_for_same_wallet_and_event_scope_is_refused_atomically() {
        let store = PersistentStore::open_in_memory().expect("store");
        let first_record = record(0);
        let second_record = record(1);
        let wallet = [0x41; 32];
        let first = prepared(0x51, wallet, 0x61, 0x71, 0x81, &first_record, 0);
        let redirected = prepared(0x52, wallet, 0x62, 0x72, 0x82, &second_record, 0);

        let write = store.db.begin_write().expect("first writer");
        stage_fresh_poa_holding_consumption_in(&write, 0, &first_record, &first)
            .expect("first event-scoped holder use");
        write.commit().expect("commit first holder use");

        let write = store.db.begin_write().expect("second writer");
        let error = stage_fresh_poa_holding_consumption_in(&write, 1, &second_record, &redirected)
            .expect_err("same wallet may not multiply one event-scoped entitlement");
        assert!(error.to_string().contains("activated event scope"));
        drop(write);

        assert!(
            store
                .load_poa_holding_consumption(&redirected.capability_receipt_id)
                .expect("lookup")
                .is_none()
        );
    }
}
