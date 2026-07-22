//! Private, durable custody for already-signed dependent turns.
//!
//! Public promise-resolution rows deliberately contain no `Turn`.  This table
//! is the private half: an AEAD-sealed signed envelope is bound to the pending
//! turn hash and the stable `ReadyToExecute` expectation.  A release is an
//! atomic, destructive claim against a real durable resolution row.  The seal
//! is removed from redb before control returns to the caller, so a crash can
//! lose a claimed delivery but can never release it twice (at-most-once).

use redb::{ReadableTable, ReadableTableMetadata};
use serde::{Deserialize, Serialize};

use crate::{
    DurablePromiseResolutionV1, PersistentStore, PromiseResolutionCandidateV1,
    PromiseResolutionKindV1, Result, StoreError, tables,
};

const READY_DIGEST_DOMAIN_V1: &str = "dregg-private-dependent-ready-v1";
const INGRESS_RESERVATION_DOMAIN_V1: &str = "dregg-private-dependent-ingress-reservation-v1";
const CURSOR_META_KEY_V1: &str = "private_dependent_scheduler_cursor_v1";

pub const MAX_PRIVATE_DEPENDENT_TURNS: usize = 4_096;
pub const MAX_PRIVATE_DEPENDENT_SEAL_BYTES: usize = 256 * 1024 + 64;
pub const MAX_PRIVATE_DEPENDENT_ROW_BYTES: usize = MAX_PRIVATE_DEPENDENT_SEAL_BYTES + 4 * 1024;
pub const MAX_PRIVATE_DEPENDENT_TOTAL_BYTES: usize = 64 * 1024 * 1024;
pub const MAX_PRIVATE_DEPENDENT_REFUSAL_BYTES: usize = 4 * 1024;

/// Stable idempotency key for the consensus-ingress handoff created by one
/// exact Ready event.  It is intentionally signer/payload-byte independent:
/// the signed-turn hash already commits to the canonical signed transition,
/// while the Ready event identity prevents a different observer row from
/// claiming the same custody.
pub fn private_dependent_ingress_reservation_id_v1(
    promise_id: [u8; 32],
    signed_turn_hash: [u8; 32],
    ready_sequence: u64,
    event_id: [u8; 32],
) -> [u8; 32] {
    *blake3::Hasher::new_derive_key(INGRESS_RESERVATION_DOMAIN_V1)
        .update(&promise_id)
        .update(&signed_turn_hash)
        .update(&ready_sequence.to_le_bytes())
        .update(&event_id)
        .finalize()
        .as_bytes()
}

/// Stable expectation committed before the promise becomes ready.
pub fn private_dependent_ready_digest_v1(
    promise_id: [u8; 32],
    signed_turn_hash: [u8; 32],
) -> [u8; 32] {
    *blake3::Hasher::new_derive_key(READY_DIGEST_DOMAIN_V1)
        .update(&promise_id)
        .update(&signed_turn_hash)
        .update(b"ready_to_execute")
        .finalize()
        .as_bytes()
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrivateDependentTurnStatusV1 {
    Armed,
    Claimed {
        ready_sequence: u64,
        event_id: [u8; 32],
    },
    Submitted {
        ready_sequence: u64,
        event_id: [u8; 32],
        ingress_id: [u8; 32],
    },
    Refused {
        ready_sequence: u64,
        event_id: [u8; 32],
        reason: String,
    },
    Cancelled,
    Expired {
        ready_sequence: u64,
    },
}

impl PrivateDependentTurnStatusV1 {
    pub const fn is_terminal(&self) -> bool {
        matches!(
            self,
            Self::Submitted { .. } | Self::Refused { .. } | Self::Cancelled | Self::Expired { .. }
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateDependentTurnSnapshotV1 {
    pub promise_id: [u8; 32],
    pub signed_turn_hash: [u8; 32],
    pub expected_resolution_digest: [u8; 32],
    pub expires_at_sequence_exclusive: u64,
    pub status: PrivateDependentTurnStatusV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimedPrivateDependentTurnV1 {
    pub promise_id: [u8; 32],
    pub signed_turn_hash: [u8; 32],
    pub expected_resolution_digest: [u8; 32],
    pub ready_sequence: u64,
    pub event_id: [u8; 32],
    pub sealed_signed_turn: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateDependentTurnFinishV1 {
    Submitted { ingress_id: [u8; 32] },
    Refused { reason: String },
}

/// Durable state of the private handoff to consensus ingress. `Reserved`
/// retains the opaque AEAD seal, so the claim transaction cannot lose custody.
/// Moving to a terminal state destroys that seal in the same transaction that
/// marks the dependent turn Submitted/Refused.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrivateDependentIngressReservationStatusV1 {
    Reserved,
    Accepted { ingress_id: [u8; 32] },
    Refused { reason: String },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateDependentIngressReservationSnapshotV1 {
    pub reservation_id: [u8; 32],
    pub promise_id: [u8; 32],
    pub signed_turn_hash: [u8; 32],
    pub ready_sequence: u64,
    pub event_id: [u8; 32],
    pub status: PrivateDependentIngressReservationStatusV1,
    /// Opaque node-encrypted bytes. Present only while `Reserved`; this API is
    /// an internal persistence seam and is never wired to a public route.
    pub sealed_signed_turn: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct PrivateDependentIngressReservationRecordV1 {
    reservation_id: [u8; 32],
    promise_id: [u8; 32],
    signed_turn_hash: [u8; 32],
    ready_sequence: u64,
    event_id: [u8; 32],
    status: PrivateDependentIngressReservationStatusV1,
    sealed_signed_turn: Vec<u8>,
}

impl PrivateDependentIngressReservationRecordV1 {
    fn validate(&self, key: &[u8]) -> Result<()> {
        if key != self.reservation_id {
            return Err(StoreError::Integrity(
                "private dependent ingress key disagrees with reservation id".to_string(),
            ));
        }
        if self.promise_id != self.signed_turn_hash {
            return Err(StoreError::Integrity(
                "private dependent ingress is not bound to its promise id".to_string(),
            ));
        }
        if self.reservation_id
            != private_dependent_ingress_reservation_id_v1(
                self.promise_id,
                self.signed_turn_hash,
                self.ready_sequence,
                self.event_id,
            )
        {
            return Err(StoreError::Integrity(
                "private dependent ingress reservation id is not canonical".to_string(),
            ));
        }
        match &self.status {
            PrivateDependentIngressReservationStatusV1::Reserved => {
                if self.sealed_signed_turn.is_empty()
                    || self.sealed_signed_turn.len() > MAX_PRIVATE_DEPENDENT_SEAL_BYTES
                {
                    return Err(StoreError::Integrity(
                        "reserved private dependent ingress seal is empty or oversized".to_string(),
                    ));
                }
            }
            PrivateDependentIngressReservationStatusV1::Refused { reason } => {
                if reason.len() > MAX_PRIVATE_DEPENDENT_REFUSAL_BYTES {
                    return Err(StoreError::Integrity(
                        "private dependent ingress refusal text is oversized".to_string(),
                    ));
                }
                if !self.sealed_signed_turn.is_empty() {
                    return Err(StoreError::Integrity(
                        "terminal private dependent ingress retained its private seal".to_string(),
                    ));
                }
            }
            PrivateDependentIngressReservationStatusV1::Accepted { .. }
                if !self.sealed_signed_turn.is_empty() =>
            {
                return Err(StoreError::Integrity(
                    "accepted private dependent ingress retained its private seal".to_string(),
                ));
            }
            _ => {}
        }
        Ok(())
    }

    fn snapshot(&self) -> PrivateDependentIngressReservationSnapshotV1 {
        PrivateDependentIngressReservationSnapshotV1 {
            reservation_id: self.reservation_id,
            promise_id: self.promise_id,
            signed_turn_hash: self.signed_turn_hash,
            ready_sequence: self.ready_sequence,
            event_id: self.event_id,
            status: self.status.clone(),
            sealed_signed_turn: self.sealed_signed_turn.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct PrivateDependentTurnRecordV1 {
    promise_id: [u8; 32],
    signed_turn_hash: [u8; 32],
    expected_resolution_digest: [u8; 32],
    expires_at_sequence_exclusive: u64,
    status: PrivateDependentTurnStatusV1,
    /// Present only while Armed. A destructive claim clears it in the same
    /// transaction that records the unique durable Ready event.
    sealed_signed_turn: Vec<u8>,
}

impl PrivateDependentTurnRecordV1 {
    fn validate(&self, key: &[u8]) -> Result<()> {
        if key != self.promise_id {
            return Err(StoreError::Integrity(
                "private dependent-turn key disagrees with promise id".to_string(),
            ));
        }
        if self.promise_id != self.signed_turn_hash {
            return Err(StoreError::Integrity(
                "private dependent turn is not bound to its promise id".to_string(),
            ));
        }
        if self.expected_resolution_digest
            != private_dependent_ready_digest_v1(self.promise_id, self.signed_turn_hash)
        {
            return Err(StoreError::Integrity(
                "private dependent-turn resolution expectation is not canonical".to_string(),
            ));
        }
        match &self.status {
            PrivateDependentTurnStatusV1::Armed => {
                if self.sealed_signed_turn.is_empty()
                    || self.sealed_signed_turn.len() > MAX_PRIVATE_DEPENDENT_SEAL_BYTES
                {
                    return Err(StoreError::Integrity(
                        "private dependent-turn armed seal is empty or oversized".to_string(),
                    ));
                }
            }
            PrivateDependentTurnStatusV1::Refused { reason, .. } => {
                if reason.len() > MAX_PRIVATE_DEPENDENT_REFUSAL_BYTES {
                    return Err(StoreError::Integrity(
                        "private dependent-turn refusal text is oversized".to_string(),
                    ));
                }
                if !self.sealed_signed_turn.is_empty() {
                    return Err(StoreError::Integrity(
                        "terminal private dependent turn retained its private seal".to_string(),
                    ));
                }
            }
            _ if !self.sealed_signed_turn.is_empty() => {
                return Err(StoreError::Integrity(
                    "non-armed private dependent turn retained its private seal".to_string(),
                ));
            }
            _ => {}
        }
        Ok(())
    }

    fn snapshot(&self) -> PrivateDependentTurnSnapshotV1 {
        PrivateDependentTurnSnapshotV1 {
            promise_id: self.promise_id,
            signed_turn_hash: self.signed_turn_hash,
            expected_resolution_digest: self.expected_resolution_digest,
            expires_at_sequence_exclusive: self.expires_at_sequence_exclusive,
            status: self.status.clone(),
        }
    }
}

fn canonical_bytes<T: Serialize>(value: &T) -> Result<Vec<u8>> {
    postcard::to_stdvec(value).map_err(|error| StoreError::Serialization(error.to_string()))
}

fn decode_record(bytes: &[u8], key: &[u8]) -> Result<PrivateDependentTurnRecordV1> {
    if bytes.len() > MAX_PRIVATE_DEPENDENT_ROW_BYTES {
        return Err(StoreError::Integrity(format!(
            "private dependent-turn row is {} bytes (maximum {})",
            bytes.len(),
            MAX_PRIVATE_DEPENDENT_ROW_BYTES
        )));
    }
    let record: PrivateDependentTurnRecordV1 = postcard::from_bytes(bytes).map_err(|error| {
        StoreError::Integrity(format!("private dependent-turn row decode failed: {error}"))
    })?;
    record.validate(key)?;
    if canonical_bytes(&record)?.as_slice() != bytes {
        return Err(StoreError::Integrity(
            "private dependent-turn row is non-canonical".to_string(),
        ));
    }
    Ok(record)
}

fn decode_ingress_reservation(
    bytes: &[u8],
    key: &[u8],
) -> Result<PrivateDependentIngressReservationRecordV1> {
    if bytes.len() > MAX_PRIVATE_DEPENDENT_ROW_BYTES {
        return Err(StoreError::Integrity(format!(
            "private dependent ingress row is {} bytes (maximum {})",
            bytes.len(),
            MAX_PRIVATE_DEPENDENT_ROW_BYTES
        )));
    }
    let record: PrivateDependentIngressReservationRecordV1 =
        postcard::from_bytes(bytes).map_err(|error| {
            StoreError::Integrity(format!(
                "private dependent ingress row decode failed: {error}"
            ))
        })?;
    record.validate(key)?;
    if canonical_bytes(&record)?.as_slice() != bytes {
        return Err(StoreError::Integrity(
            "private dependent ingress row is non-canonical".to_string(),
        ));
    }
    Ok(record)
}

fn decode_resolution(bytes: &[u8], sequence: u64) -> Result<DurablePromiseResolutionV1> {
    if bytes.len() > crate::promise_resolutions::MAX_PROMISE_RESOLUTION_ROW_BYTES {
        return Err(StoreError::Integrity(
            "private dependent-turn release found an oversized resolution row".to_string(),
        ));
    }
    let row: DurablePromiseResolutionV1 = postcard::from_bytes(bytes).map_err(|error| {
        StoreError::Integrity(format!(
            "private dependent-turn resolution decode failed: {error}"
        ))
    })?;
    if canonical_bytes(&row)?.as_slice() != bytes || row.sequence != sequence {
        return Err(StoreError::Integrity(
            "private dependent-turn release found a non-canonical resolution row".to_string(),
        ));
    }
    let candidate = PromiseResolutionCandidateV1 {
        source_commit_ordinal: row.source_commit_ordinal,
        source_receipt_hash: row.source_receipt_hash,
        event_index: row.event_index,
        pending_id: row.pending_id,
        outcome: row.outcome.clone(),
    };
    if row.event_id != candidate.event_id() {
        return Err(StoreError::Integrity(
            "private dependent-turn release found a forged resolution event id".to_string(),
        ));
    }
    Ok(row)
}

impl PersistentStore {
    /// Store one already-AEAD-sealed signed turn. Exact repeats are idempotent;
    /// a same-promise substitution is refused.
    pub fn arm_private_dependent_turn_v1(
        &self,
        promise_id: [u8; 32],
        signed_turn_hash: [u8; 32],
        sealed_signed_turn: Vec<u8>,
        expires_at_sequence_exclusive: u64,
    ) -> Result<bool> {
        let record = PrivateDependentTurnRecordV1 {
            promise_id,
            signed_turn_hash,
            expected_resolution_digest: private_dependent_ready_digest_v1(
                promise_id,
                signed_turn_hash,
            ),
            expires_at_sequence_exclusive,
            status: PrivateDependentTurnStatusV1::Armed,
            sealed_signed_turn,
        };
        record.validate(&promise_id)?;
        let bytes = canonical_bytes(&record)?;
        if bytes.len() > MAX_PRIVATE_DEPENDENT_ROW_BYTES {
            return Err(StoreError::Integrity(
                "private dependent-turn custody row exceeds its durable bound".to_string(),
            ));
        }

        let write = self.db.begin_write()?;
        {
            let mut table = write.open_table(tables::PRIVATE_DEPENDENT_TURNS_V1)?;
            if let Some(existing) = table.get(&promise_id)? {
                let existing_bytes = existing.value();
                let _ = decode_record(existing_bytes, &promise_id)?;
                if existing_bytes == bytes.as_slice() {
                    return Ok(false);
                }
                return Err(StoreError::Integrity(
                    "private dependent-turn promise id already has different custody".to_string(),
                ));
            }
            if table.len()? as usize >= MAX_PRIVATE_DEPENDENT_TURNS {
                return Err(StoreError::Integrity(format!(
                    "private dependent-turn table is full (maximum {MAX_PRIVATE_DEPENDENT_TURNS})"
                )));
            }
            let mut total = 0usize;
            for entry in table.iter()? {
                let (key, value) = entry?;
                let _ = decode_record(value.value(), key.value())?;
                total = total.checked_add(value.value().len()).ok_or_else(|| {
                    StoreError::Integrity(
                        "private dependent-turn storage accounting overflow".to_string(),
                    )
                })?;
            }
            if total.saturating_add(bytes.len()) > MAX_PRIVATE_DEPENDENT_TOTAL_BYTES {
                return Err(StoreError::Integrity(format!(
                    "private dependent-turn custody exceeds {} byte total bound",
                    MAX_PRIVATE_DEPENDENT_TOTAL_BYTES
                )));
            }
            table.insert(&promise_id, bytes.as_slice())?;
        }
        write.commit()?;
        Ok(true)
    }

    /// Atomically and destructively release the private seal only when the
    /// named durable observer row is the canonical Ready event for this promise.
    pub fn claim_private_dependent_turn_v1(
        &self,
        promise_id: [u8; 32],
        ready_sequence: u64,
    ) -> Result<Option<ClaimedPrivateDependentTurnV1>> {
        let write = self.db.begin_write()?;
        let claimed = {
            let resolutions = write.open_table(tables::PROMISE_RESOLUTION_RECORDS_V1)?;
            let resolution_bytes = resolutions.get(ready_sequence)?.ok_or_else(|| {
                StoreError::Integrity(
                    "private dependent-turn release requires a durable resolution row".to_string(),
                )
            })?;
            let resolution = decode_resolution(resolution_bytes.value(), ready_sequence)?;
            if resolution.pending_id != promise_id
                || resolution.outcome != PromiseResolutionKindV1::ReadyToExecute
            {
                return Err(StoreError::Integrity(
                    "private dependent-turn release row is not its promised ReadyToExecute"
                        .to_string(),
                ));
            }

            let mut table = write.open_table(tables::PRIVATE_DEPENDENT_TURNS_V1)?;
            let Some(current) = table.get(&promise_id)? else {
                return Ok(None);
            };
            let mut record = decode_record(current.value(), &promise_id)?;
            drop(current);
            if record.status != PrivateDependentTurnStatusV1::Armed {
                return Ok(None);
            }
            if ready_sequence >= record.expires_at_sequence_exclusive {
                record.status = PrivateDependentTurnStatusV1::Expired { ready_sequence };
                record.sealed_signed_turn.clear();
                let bytes = canonical_bytes(&record)?;
                table.insert(&promise_id, bytes.as_slice())?;
                None
            } else {
                let expected = private_dependent_ready_digest_v1(
                    resolution.pending_id,
                    record.signed_turn_hash,
                );
                if expected != record.expected_resolution_digest {
                    return Err(StoreError::Integrity(
                        "private dependent-turn Ready digest disagrees with custody".to_string(),
                    ));
                }
                let seal = core::mem::take(&mut record.sealed_signed_turn);
                let reservation_id = private_dependent_ingress_reservation_id_v1(
                    promise_id,
                    record.signed_turn_hash,
                    ready_sequence,
                    resolution.event_id,
                );
                let reservation = PrivateDependentIngressReservationRecordV1 {
                    reservation_id,
                    promise_id,
                    signed_turn_hash: record.signed_turn_hash,
                    ready_sequence,
                    event_id: resolution.event_id,
                    status: PrivateDependentIngressReservationStatusV1::Reserved,
                    sealed_signed_turn: seal.clone(),
                };
                reservation.validate(&reservation_id)?;
                let reservation_bytes = canonical_bytes(&reservation)?;
                if reservation_bytes.len() > MAX_PRIVATE_DEPENDENT_ROW_BYTES {
                    return Err(StoreError::Integrity(
                        "private dependent ingress reservation exceeds its durable bound"
                            .to_string(),
                    ));
                }
                {
                    let mut reservations =
                        write.open_table(tables::PRIVATE_DEPENDENT_INGRESS_RESERVATIONS_V1)?;
                    if reservations.get(&reservation_id)?.is_some() {
                        return Err(StoreError::Integrity(
                            "private dependent Ready claim found a pre-existing ingress reservation"
                                .to_string(),
                        ));
                    }
                    if reservations.len()? as usize >= MAX_PRIVATE_DEPENDENT_TURNS {
                        return Err(StoreError::Integrity(format!(
                            "private dependent ingress reservation table is full (maximum {MAX_PRIVATE_DEPENDENT_TURNS})"
                        )));
                    }
                    reservations.insert(&reservation_id, reservation_bytes.as_slice())?;
                }
                record.status = PrivateDependentTurnStatusV1::Claimed {
                    ready_sequence,
                    event_id: resolution.event_id,
                };
                let bytes = canonical_bytes(&record)?;
                table.insert(&promise_id, bytes.as_slice())?;
                Some(ClaimedPrivateDependentTurnV1 {
                    promise_id,
                    signed_turn_hash: record.signed_turn_hash,
                    expected_resolution_digest: record.expected_resolution_digest,
                    ready_sequence,
                    event_id: resolution.event_id,
                    sealed_signed_turn: seal,
                })
            }
        };
        write.commit()?;
        Ok(claimed)
    }

    pub fn finish_private_dependent_turn_v1(
        &self,
        promise_id: [u8; 32],
        ready_sequence: u64,
        event_id: [u8; 32],
        outcome: PrivateDependentTurnFinishV1,
    ) -> Result<()> {
        let (turn_status, reservation_status) = match outcome {
            PrivateDependentTurnFinishV1::Submitted { ingress_id } => (
                PrivateDependentTurnStatusV1::Submitted {
                    ready_sequence,
                    event_id,
                    ingress_id,
                },
                PrivateDependentIngressReservationStatusV1::Accepted { ingress_id },
            ),
            PrivateDependentTurnFinishV1::Refused { reason } => {
                if reason.len() > MAX_PRIVATE_DEPENDENT_REFUSAL_BYTES {
                    return Err(StoreError::Integrity(
                        "private dependent-turn refusal text exceeds bound".to_string(),
                    ));
                }
                (
                    PrivateDependentTurnStatusV1::Refused {
                        ready_sequence,
                        event_id,
                        reason: reason.clone(),
                    },
                    PrivateDependentIngressReservationStatusV1::Refused { reason },
                )
            }
        };
        let reservation_id = private_dependent_ingress_reservation_id_v1(
            promise_id,
            promise_id,
            ready_sequence,
            event_id,
        );
        let write = self.db.begin_write()?;
        {
            let mut table = write.open_table(tables::PRIVATE_DEPENDENT_TURNS_V1)?;
            let current = table.get(&promise_id)?.ok_or_else(|| {
                StoreError::Integrity("claimed private dependent turn is missing".to_string())
            })?;
            let mut record = decode_record(current.value(), &promise_id)?;
            drop(current);
            let exact_replay = record.status == turn_status;
            if !exact_replay
                && record.status
                    != (PrivateDependentTurnStatusV1::Claimed {
                        ready_sequence,
                        event_id,
                    })
            {
                return Err(StoreError::Integrity(
                    "private dependent-turn finish does not match its durable claim".to_string(),
                ));
            }
            let mut reservations =
                write.open_table(tables::PRIVATE_DEPENDENT_INGRESS_RESERVATIONS_V1)?;
            let current_reservation = reservations.get(&reservation_id)?.ok_or_else(|| {
                StoreError::Integrity(
                    "claimed private dependent turn is missing its ingress reservation".to_string(),
                )
            })?;
            let mut reservation =
                decode_ingress_reservation(current_reservation.value(), &reservation_id)?;
            drop(current_reservation);
            if reservation.promise_id != promise_id
                || reservation.signed_turn_hash != record.signed_turn_hash
                || reservation.ready_sequence != ready_sequence
                || reservation.event_id != event_id
            {
                return Err(StoreError::Integrity(
                    "private dependent ingress reservation disagrees with its claim".to_string(),
                ));
            }
            if exact_replay {
                if reservation.status != reservation_status
                    || !reservation.sealed_signed_turn.is_empty()
                {
                    return Err(StoreError::Integrity(
                        "private dependent finish replay disagrees with ingress reservation"
                            .to_string(),
                    ));
                }
                return Ok(());
            }
            if reservation.status != PrivateDependentIngressReservationStatusV1::Reserved {
                return Err(StoreError::Integrity(
                    "private dependent ingress reservation was already consumed differently"
                        .to_string(),
                ));
            }
            record.status = turn_status;
            reservation.status = reservation_status;
            reservation.sealed_signed_turn.clear();
            reservation.validate(&reservation_id)?;
            let bytes = canonical_bytes(&record)?;
            let reservation_bytes = canonical_bytes(&reservation)?;
            table.insert(&promise_id, bytes.as_slice())?;
            reservations.insert(&reservation_id, reservation_bytes.as_slice())?;
        }
        write.commit()?;
        Ok(())
    }

    /// Atomically persist one already-admitted turn-bearing block and consume
    /// its private ingress reservation.
    ///
    /// The blocklace producer must construct the block on an isolated clone,
    /// call this method, and only then install/broadcast that clone. A crash
    /// before this transaction leaves the reservation `Reserved`; a crash
    /// after it leaves both the exact block bytes and `Submitted(block_id)`.
    /// Exact retries are idempotent and a different block is refused.
    ///
    /// This persistence seam deliberately does not replace SignedTurn
    /// admission: the caller must run the canonical node validator before
    /// constructing `block`. It does, however, refuse non-turn carriers and
    /// oversized/empty signed payloads before any durable mutation.
    pub fn accept_private_dependent_ingress_block_v1(
        &self,
        reservation_id: [u8; 32],
        block: &dregg_blocklace::finality::Block,
    ) -> Result<[u8; 32]> {
        use dregg_blocklace::finality::Payload;

        let signed_turn = match &block.payload {
            Payload::Turn(bytes) => bytes.as_slice(),
            Payload::TurnBundle(bundle) => bundle.signed_turn.as_slice(),
            Payload::ConsensusTimedTurnV1(timed) => timed.signed_turn(),
            Payload::Ack
            | Payload::Checkpoint { .. }
            | Payload::MembershipVote { .. }
            | Payload::Data(_) => {
                return Err(StoreError::Integrity(
                    "private dependent ingress block is not turn-bearing".to_string(),
                ));
            }
        };
        if signed_turn.is_empty() || signed_turn.len() > MAX_PRIVATE_DEPENDENT_SEAL_BYTES {
            return Err(StoreError::Integrity(
                "private dependent ingress block has an empty or oversized signed turn".to_string(),
            ));
        }

        let ingress_id = block.id().0;
        let block_bytes = block.to_bytes();
        let write = self.db.begin_write()?;
        {
            let mut reservations =
                write.open_table(tables::PRIVATE_DEPENDENT_INGRESS_RESERVATIONS_V1)?;
            let current = reservations.get(&reservation_id)?.ok_or_else(|| {
                StoreError::Integrity(
                    "private dependent ingress reservation is missing".to_string(),
                )
            })?;
            let mut reservation = decode_ingress_reservation(current.value(), &reservation_id)?;
            drop(current);

            let mut turns = write.open_table(tables::PRIVATE_DEPENDENT_TURNS_V1)?;
            let current_turn = turns.get(&reservation.promise_id)?.ok_or_else(|| {
                StoreError::Integrity(
                    "private dependent ingress lost its primary custody row".to_string(),
                )
            })?;
            let mut turn = decode_record(current_turn.value(), &reservation.promise_id)?;
            drop(current_turn);
            if turn.signed_turn_hash != reservation.signed_turn_hash {
                return Err(StoreError::Integrity(
                    "private dependent ingress signed-turn hash disagrees with custody".to_string(),
                ));
            }

            let claimed = PrivateDependentTurnStatusV1::Claimed {
                ready_sequence: reservation.ready_sequence,
                event_id: reservation.event_id,
            };
            let submitted = PrivateDependentTurnStatusV1::Submitted {
                ready_sequence: reservation.ready_sequence,
                event_id: reservation.event_id,
                ingress_id,
            };
            let accepted = PrivateDependentIngressReservationStatusV1::Accepted { ingress_id };

            let exact_replay = reservation.status == accepted && turn.status == submitted;
            if !exact_replay
                && (reservation.status != PrivateDependentIngressReservationStatusV1::Reserved
                    || turn.status != claimed)
            {
                return Err(StoreError::Integrity(
                    "private dependent ingress block does not match a live reservation".to_string(),
                ));
            }

            let mut blocks = write.open_table(tables::BLOCKLACE_BLOCKS)?;
            if let Some(existing) = blocks.get(&ingress_id)? {
                if existing.value() != block_bytes.as_slice() {
                    return Err(StoreError::Integrity(
                        "private dependent ingress block id has different durable bytes"
                            .to_string(),
                    ));
                }
            } else if exact_replay {
                return Err(StoreError::Integrity(
                    "accepted private dependent ingress is missing its durable block".to_string(),
                ));
            } else {
                blocks.insert(&ingress_id, block_bytes.as_slice())?;
            }

            if !exact_replay {
                turn.status = submitted;
                reservation.status = accepted;
                reservation.sealed_signed_turn.clear();
                reservation.validate(&reservation_id)?;
                let turn_bytes = canonical_bytes(&turn)?;
                let reservation_bytes = canonical_bytes(&reservation)?;
                turns.insert(&reservation.promise_id, turn_bytes.as_slice())?;
                reservations.insert(&reservation_id, reservation_bytes.as_slice())?;
            }
        }
        write.commit()?;
        Ok(ingress_id)
    }

    /// Cancel only an unclaimed custody item. Once claimed, at-most-once release
    /// has begun and cancellation cannot race it back to Armed.
    pub fn cancel_private_dependent_turn_v1(&self, promise_id: [u8; 32]) -> Result<bool> {
        let write = self.db.begin_write()?;
        let cancelled = {
            let mut table = write.open_table(tables::PRIVATE_DEPENDENT_TURNS_V1)?;
            let Some(current) = table.get(&promise_id)? else {
                return Ok(false);
            };
            let mut record = decode_record(current.value(), &promise_id)?;
            drop(current);
            if record.status != PrivateDependentTurnStatusV1::Armed {
                false
            } else {
                record.status = PrivateDependentTurnStatusV1::Cancelled;
                record.sealed_signed_turn.clear();
                let bytes = canonical_bytes(&record)?;
                table.insert(&promise_id, bytes.as_slice())?;
                true
            }
        };
        write.commit()?;
        Ok(cancelled)
    }

    pub fn private_dependent_turn_status_v1(
        &self,
        promise_id: [u8; 32],
    ) -> Result<Option<PrivateDependentTurnSnapshotV1>> {
        let read = self.db.begin_read()?;
        let table = read.open_table(tables::PRIVATE_DEPENDENT_TURNS_V1)?;
        let Some(value) = table.get(&promise_id)? else {
            return Ok(None);
        };
        Ok(Some(decode_record(value.value(), &promise_id)?.snapshot()))
    }

    /// Bounded restart reconciliation surface. It exposes no sealed bytes.
    pub fn claimed_private_dependent_turns_v1(
        &self,
    ) -> Result<Vec<PrivateDependentTurnSnapshotV1>> {
        let read = self.db.begin_read()?;
        let table = read.open_table(tables::PRIVATE_DEPENDENT_TURNS_V1)?;
        let mut claimed = Vec::new();
        for entry in table.iter()? {
            let (key, value) = entry?;
            let record = decode_record(value.value(), key.value())?;
            if matches!(record.status, PrivateDependentTurnStatusV1::Claimed { .. }) {
                claimed.push(record.snapshot());
            }
        }
        Ok(claimed)
    }

    /// Read one private ingress reservation by its stable idempotency key.
    /// This is an internal custody surface: it returns the opaque AEAD seal
    /// while Reserved and must never be connected to a public observer API.
    pub fn private_dependent_ingress_reservation_v1(
        &self,
        reservation_id: [u8; 32],
    ) -> Result<Option<PrivateDependentIngressReservationSnapshotV1>> {
        let read = self.db.begin_read()?;
        let table = read.open_table(tables::PRIVATE_DEPENDENT_INGRESS_RESERVATIONS_V1)?;
        let Some(value) = table.get(&reservation_id)? else {
            return Ok(None);
        };
        Ok(Some(
            decode_ingress_reservation(value.value(), &reservation_id)?.snapshot(),
        ))
    }

    /// Explicit bounded-storage cleanup. Armed/Claimed records can never be
    /// forgotten through this API.
    pub fn forget_terminal_private_dependent_turn_v1(&self, promise_id: [u8; 32]) -> Result<bool> {
        let write = self.db.begin_write()?;
        let removed = {
            let mut table = write.open_table(tables::PRIVATE_DEPENDENT_TURNS_V1)?;
            let Some(value) = table.get(&promise_id)? else {
                return Ok(false);
            };
            let record = decode_record(value.value(), &promise_id)?;
            drop(value);
            if !record.status.is_terminal() {
                false
            } else {
                let reservation_terminal = match &record.status {
                    PrivateDependentTurnStatusV1::Submitted {
                        ready_sequence,
                        event_id,
                        ingress_id,
                    } => Some((
                        *ready_sequence,
                        *event_id,
                        PrivateDependentIngressReservationStatusV1::Accepted {
                            ingress_id: *ingress_id,
                        },
                    )),
                    PrivateDependentTurnStatusV1::Refused {
                        ready_sequence,
                        event_id,
                        reason,
                    } => Some((
                        *ready_sequence,
                        *event_id,
                        PrivateDependentIngressReservationStatusV1::Refused {
                            reason: reason.clone(),
                        },
                    )),
                    PrivateDependentTurnStatusV1::Cancelled
                    | PrivateDependentTurnStatusV1::Expired { .. } => None,
                    PrivateDependentTurnStatusV1::Armed
                    | PrivateDependentTurnStatusV1::Claimed { .. } => unreachable!(),
                };
                if let Some((ready_sequence, event_id, expected_status)) = reservation_terminal {
                    let reservation_id = private_dependent_ingress_reservation_id_v1(
                        promise_id,
                        record.signed_turn_hash,
                        ready_sequence,
                        event_id,
                    );
                    let mut reservations =
                        write.open_table(tables::PRIVATE_DEPENDENT_INGRESS_RESERVATIONS_V1)?;
                    let reservation_value =
                        reservations.get(&reservation_id)?.ok_or_else(|| {
                            StoreError::Integrity(
                                "terminal private dependent turn is missing its ingress reservation"
                                    .to_string(),
                            )
                        })?;
                    let reservation =
                        decode_ingress_reservation(reservation_value.value(), &reservation_id)?;
                    drop(reservation_value);
                    if reservation.status != expected_status
                        || !reservation.sealed_signed_turn.is_empty()
                    {
                        return Err(StoreError::Integrity(
                            "terminal private dependent turn disagrees with its ingress reservation"
                                .to_string(),
                        ));
                    }
                    reservations.remove(&reservation_id)?;
                }
                table.remove(&promise_id)?.is_some()
            }
        };
        write.commit()?;
        Ok(removed)
    }

    pub fn private_dependent_scheduler_cursor_v1(&self) -> Result<Option<u64>> {
        let read = self.db.begin_read()?;
        let table = read.open_table(tables::METADATA)?;
        Ok(table.get(CURSOR_META_KEY_V1)?.map(|value| value.value()))
    }

    pub fn advance_private_dependent_scheduler_cursor_v1(&self, sequence: u64) -> Result<()> {
        let write = self.db.begin_write()?;
        {
            let mut table = write.open_table(tables::METADATA)?;
            if table
                .get(CURSOR_META_KEY_V1)?
                .is_some_and(|current| current.value() >= sequence)
            {
                return Ok(());
            }
            table.insert(CURSOR_META_KEY_V1, sequence)?;
        }
        write.commit()?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    fn store() -> (TempDir, PersistentStore) {
        let dir = TempDir::new().unwrap();
        let store = PersistentStore::open(&dir.path().join("store.redb")).unwrap();
        (dir, store)
    }

    fn source(ordinal: u64, receipt_hash: [u8; 32]) -> crate::CommitRecord {
        crate::CommitRecord {
            ordinal,
            height: ordinal + 1,
            block_id: [ordinal as u8; 32],
            block_executed_up_to: ordinal,
            turn_hash: [0x41; 32],
            creator: [0x51; 32],
            receipt_hash,
            ledger_root: [0x61; 32],
            touched_cells: Vec::new(),
            removed: Vec::new(),
        }
    }

    fn commit_ready(store: &PersistentStore, promise_id: [u8; 32]) {
        let receipt_hash = [0x11; 32];
        let mut state = crate::FinalizedExecutorConsensusState::default();
        state.promise_resolutions = vec![PromiseResolutionCandidateV1 {
            source_commit_ordinal: 0,
            source_receipt_hash: receipt_hash,
            event_index: 0,
            pending_id: promise_id,
            outcome: PromiseResolutionKindV1::ReadyToExecute,
        }];
        store
            .commit_finalized_turn_with_executor_state(0, &source(0, receipt_hash), &[], &state)
            .unwrap();
    }

    fn reservation_id(claim: &ClaimedPrivateDependentTurnV1) -> [u8; 32] {
        private_dependent_ingress_reservation_id_v1(
            claim.promise_id,
            claim.signed_turn_hash,
            claim.ready_sequence,
            claim.event_id,
        )
    }

    fn block(payload: dregg_blocklace::finality::Payload) -> dregg_blocklace::finality::Block {
        // Persistence validates the carrier shape and byte identity, while the
        // node's canonical ingress validates hybrid signatures before calling
        // it. A hand-built carrier keeps this persistence-only test from
        // invoking unaudited fallback PQ key generation.
        dregg_blocklace::finality::Block {
            creator: [0x35; 32],
            ed25519: [0x36; 32],
            seq: 1,
            payload,
            predecessors: Vec::new(),
            signature: [0; 64],
            pq_signature: Vec::new(),
        }
    }

    #[test]
    fn durable_ready_destructively_claims_exactly_once() {
        let (_dir, store) = store();
        let promise = [7; 32];
        store
            .arm_private_dependent_turn_v1(promise, promise, vec![9; 80], 10)
            .unwrap();
        commit_ready(&store, promise);
        let first = store
            .claim_private_dependent_turn_v1(promise, 0)
            .unwrap()
            .unwrap();
        assert_eq!(first.sealed_signed_turn, vec![9; 80]);
        let reservation = store
            .private_dependent_ingress_reservation_v1(reservation_id(&first))
            .unwrap()
            .unwrap();
        assert_eq!(
            reservation.status,
            PrivateDependentIngressReservationStatusV1::Reserved
        );
        assert_eq!(reservation.sealed_signed_turn, vec![9; 80]);
        assert!(
            store
                .claim_private_dependent_turn_v1(promise, 0)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn crash_after_claim_never_releases_again() {
        let (dir, store) = store();
        let promise = [8; 32];
        store
            .arm_private_dependent_turn_v1(promise, promise, vec![3; 80], 10)
            .unwrap();
        commit_ready(&store, promise);
        let claim = store
            .claim_private_dependent_turn_v1(promise, 0)
            .unwrap()
            .unwrap();
        let reservation_id = reservation_id(&claim);
        drop(store);
        let reopened = PersistentStore::open(&dir.path().join("store.redb")).unwrap();
        assert!(
            reopened
                .claim_private_dependent_turn_v1(promise, 0)
                .unwrap()
                .is_none()
        );
        assert!(matches!(
            reopened
                .private_dependent_turn_status_v1(promise)
                .unwrap()
                .unwrap()
                .status,
            PrivateDependentTurnStatusV1::Claimed { .. }
        ));
        let reservation = reopened
            .private_dependent_ingress_reservation_v1(reservation_id)
            .unwrap()
            .unwrap();
        assert_eq!(
            reservation.status,
            PrivateDependentIngressReservationStatusV1::Reserved
        );
        assert_eq!(reservation.sealed_signed_turn, vec![3; 80]);
    }

    #[test]
    fn wrong_promise_substitution_and_non_ready_release_fail_closed() {
        let (_dir, store) = store();
        let promise = [4; 32];
        let attacker = [5; 32];
        assert!(
            store
                .arm_private_dependent_turn_v1(promise, attacker, vec![1; 80], 10)
                .is_err()
        );
        store
            .arm_private_dependent_turn_v1(promise, promise, vec![1; 80], 10)
            .unwrap();
        commit_ready(&store, attacker);
        assert!(store.claim_private_dependent_turn_v1(promise, 0).is_err());
        assert!(matches!(
            store
                .private_dependent_turn_status_v1(promise)
                .unwrap()
                .unwrap()
                .status,
            PrivateDependentTurnStatusV1::Armed
        ));
    }

    #[test]
    fn cancellation_and_sequence_expiry_destroy_private_seal() {
        let (_dir, store) = store();
        let cancelled = [2; 32];
        store
            .arm_private_dependent_turn_v1(cancelled, cancelled, vec![1; 80], 10)
            .unwrap();
        assert!(store.cancel_private_dependent_turn_v1(cancelled).unwrap());
        assert!(
            store
                .forget_terminal_private_dependent_turn_v1(cancelled)
                .unwrap()
        );

        let expired = [3; 32];
        store
            .arm_private_dependent_turn_v1(expired, expired, vec![1; 80], 0)
            .unwrap();
        commit_ready(&store, expired);
        assert!(
            store
                .claim_private_dependent_turn_v1(expired, 0)
                .unwrap()
                .is_none()
        );
        assert!(matches!(
            store
                .private_dependent_turn_status_v1(expired)
                .unwrap()
                .unwrap()
                .status,
            PrivateDependentTurnStatusV1::Expired { ready_sequence: 0 }
        ));
    }

    #[test]
    fn finish_is_atomic_exact_idempotent_and_destroys_reserved_seal() {
        let (_dir, store) = store();
        let promise = [6; 32];
        assert!(
            store
                .arm_private_dependent_turn_v1(
                    promise,
                    promise,
                    vec![0; MAX_PRIVATE_DEPENDENT_SEAL_BYTES + 1],
                    10,
                )
                .is_err()
        );
        store
            .arm_private_dependent_turn_v1(promise, promise, vec![7; 80], 10)
            .unwrap();
        commit_ready(&store, promise);
        let claim = store
            .claim_private_dependent_turn_v1(promise, 0)
            .unwrap()
            .unwrap();
        assert!(
            store
                .finish_private_dependent_turn_v1(
                    promise,
                    claim.ready_sequence,
                    [0xff; 32],
                    PrivateDependentTurnFinishV1::Submitted {
                        ingress_id: [1; 32],
                    },
                )
                .is_err()
        );
        let reservation_id = reservation_id(&claim);
        let accepted = PrivateDependentTurnFinishV1::Submitted {
            ingress_id: [1; 32],
        };
        store
            .finish_private_dependent_turn_v1(
                promise,
                claim.ready_sequence,
                claim.event_id,
                accepted.clone(),
            )
            .unwrap();
        // A crash after commit but before return may replay the exact finish.
        store
            .finish_private_dependent_turn_v1(
                promise,
                claim.ready_sequence,
                claim.event_id,
                accepted,
            )
            .unwrap();
        assert!(
            store
                .finish_private_dependent_turn_v1(
                    promise,
                    claim.ready_sequence,
                    claim.event_id,
                    PrivateDependentTurnFinishV1::Submitted {
                        ingress_id: [2; 32],
                    },
                )
                .is_err()
        );
        let reservation = store
            .private_dependent_ingress_reservation_v1(reservation_id)
            .unwrap()
            .unwrap();
        assert_eq!(
            reservation.status,
            PrivateDependentIngressReservationStatusV1::Accepted {
                ingress_id: [1; 32]
            }
        );
        assert!(reservation.sealed_signed_turn.is_empty());
        assert!(
            store
                .forget_terminal_private_dependent_turn_v1(promise)
                .unwrap()
        );
        assert!(
            store
                .private_dependent_ingress_reservation_v1(reservation_id)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn accepted_block_and_reservation_commit_atomically_and_replay_exactly() {
        let (dir, store) = store();
        let promise = [0x68; 32];
        store
            .arm_private_dependent_turn_v1(promise, promise, vec![0x91; 80], 10)
            .unwrap();
        commit_ready(&store, promise);
        let claim = store
            .claim_private_dependent_turn_v1(promise, 0)
            .unwrap()
            .unwrap();
        let reservation_id = reservation_id(&claim);
        let accepted_block = block(dregg_blocklace::finality::Payload::Turn(vec![0x92; 96]));
        let ingress_id = accepted_block.id().0;
        assert_eq!(
            store
                .accept_private_dependent_ingress_block_v1(reservation_id, &accepted_block)
                .unwrap(),
            ingress_id
        );
        // Exact replay, including after process death, is a no-op success.
        assert_eq!(
            store
                .accept_private_dependent_ingress_block_v1(reservation_id, &accepted_block)
                .unwrap(),
            ingress_id
        );
        drop(store);
        let reopened = PersistentStore::open(&dir.path().join("store.redb")).unwrap();
        assert_eq!(
            reopened
                .accept_private_dependent_ingress_block_v1(reservation_id, &accepted_block)
                .unwrap(),
            ingress_id
        );
        let reservation = reopened
            .private_dependent_ingress_reservation_v1(reservation_id)
            .unwrap()
            .unwrap();
        assert_eq!(
            reservation.status,
            PrivateDependentIngressReservationStatusV1::Accepted { ingress_id }
        );
        assert!(reservation.sealed_signed_turn.is_empty());
        assert!(matches!(
            reopened
                .private_dependent_turn_status_v1(promise)
                .unwrap()
                .unwrap()
                .status,
            PrivateDependentTurnStatusV1::Submitted {
                ingress_id: stored,
                ..
            } if stored == ingress_id
        ));
        assert!(
            reopened
                .load_all_blocks()
                .unwrap()
                .iter()
                .any(|stored| stored.id().0 == ingress_id && stored == &accepted_block)
        );

        let substituted = block(dregg_blocklace::finality::Payload::Turn(vec![0x93; 96]));
        assert!(
            reopened
                .accept_private_dependent_ingress_block_v1(reservation_id, &substituted)
                .is_err()
        );
    }

    #[test]
    fn non_turn_block_cannot_consume_private_ingress_reservation() {
        let (_dir, store) = store();
        let promise = [0x69; 32];
        store
            .arm_private_dependent_turn_v1(promise, promise, vec![0x94; 80], 10)
            .unwrap();
        commit_ready(&store, promise);
        let claim = store
            .claim_private_dependent_turn_v1(promise, 0)
            .unwrap()
            .unwrap();
        let reservation_id = reservation_id(&claim);
        let inert = block(dregg_blocklace::finality::Payload::Ack);
        assert!(
            store
                .accept_private_dependent_ingress_block_v1(reservation_id, &inert)
                .is_err()
        );
        let reservation = store
            .private_dependent_ingress_reservation_v1(reservation_id)
            .unwrap()
            .unwrap();
        assert_eq!(
            reservation.status,
            PrivateDependentIngressReservationStatusV1::Reserved
        );
        assert_eq!(reservation.sealed_signed_turn, vec![0x94; 80]);
    }

    #[test]
    fn exact_arm_is_idempotent_but_seal_substitution_is_refused() {
        let (_dir, store) = store();
        let promise = [0x72; 32];
        assert!(
            store
                .arm_private_dependent_turn_v1(promise, promise, vec![1; 80], 10)
                .unwrap()
        );
        assert!(
            !store
                .arm_private_dependent_turn_v1(promise, promise, vec![1; 80], 10)
                .unwrap()
        );
        assert!(
            store
                .arm_private_dependent_turn_v1(promise, promise, vec![2; 80], 10)
                .is_err()
        );
    }

    #[test]
    fn oversized_private_row_is_rejected_before_decode() {
        let (_dir, store) = store();
        let promise = [0x73; 32];
        let oversized = vec![0u8; MAX_PRIVATE_DEPENDENT_ROW_BYTES + 1];
        let write = store.db.begin_write().unwrap();
        {
            let mut table = write
                .open_table(tables::PRIVATE_DEPENDENT_TURNS_V1)
                .unwrap();
            table.insert(&promise, oversized.as_slice()).unwrap();
        }
        write.commit().unwrap();
        let error = store.private_dependent_turn_status_v1(promise).unwrap_err();
        assert!(error.to_string().contains("maximum"));
    }

    #[test]
    fn oversized_ingress_reservation_is_rejected_before_decode() {
        let (_dir, store) = store();
        let reservation_id = [0x74; 32];
        let oversized = vec![0u8; MAX_PRIVATE_DEPENDENT_ROW_BYTES + 1];
        let write = store.db.begin_write().unwrap();
        {
            let mut table = write
                .open_table(tables::PRIVATE_DEPENDENT_INGRESS_RESERVATIONS_V1)
                .unwrap();
            table.insert(&reservation_id, oversized.as_slice()).unwrap();
        }
        write.commit().unwrap();
        let error = store
            .private_dependent_ingress_reservation_v1(reservation_id)
            .unwrap_err();
        assert!(error.to_string().contains("maximum"));
    }
}
