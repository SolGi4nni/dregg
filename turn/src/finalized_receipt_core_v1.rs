//! Deterministic finalized-execution context and signer-independent receipt identity.
//!
//! A [`TurnReceipt`] is useful executor output, but its legacy identity was minted before the
//! finalized block coordinate existed.  This module projects a *final* receipt into one strict,
//! fixed-width consensus core.  Local executor keys, signatures, receipt serialization, and wall
//! clocks are deliberately absent.  Variable-length receipt disclosures are independently
//! canonicalized into count+digest pairs so the outer wire remains fixed-width without dropping
//! any field currently bound by `TurnReceipt::receipt_hash`.

use core::fmt;

use crate::{Finality, TurnReceipt};

const CONTEXT_MAGIC: [u8; 4] = *b"FEC1";
const CORE_MAGIC: [u8; 4] = *b"FRC1";
const WIRE_VERSION: u16 = 1;
const PREFIX_LEN: usize = 8;
const CORE_ID_DOMAIN: &str = "dregg-finalized-receipt-core-v1";

/// Exact canonical width of [`FinalizedExecutionContextV1`].
pub const FINALIZED_EXECUTION_CONTEXT_V1_LEN: usize = 64;
/// Exact canonical width of [`FinalizedReceiptCoreV1`].
pub const FINALIZED_RECEIPT_CORE_V1_LEN: usize = 560;

/// Consensus input required by finalized execution.
///
/// None of these fields may be reconstructed from local process time or scheduling state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalizedExecutionContextV1 {
    block_id: [u8; 32],
    tau_round: u64,
    finalized_ordinal: u64,
    consensus_unix_seconds: i64,
}

impl FinalizedExecutionContextV1 {
    pub const fn new(
        block_id: [u8; 32],
        tau_round: u64,
        finalized_ordinal: u64,
        consensus_unix_seconds: i64,
    ) -> Self {
        Self {
            block_id,
            tau_round,
            finalized_ordinal,
            consensus_unix_seconds,
        }
    }

    pub const fn block_id(self) -> [u8; 32] {
        self.block_id
    }

    pub const fn tau_round(self) -> u64 {
        self.tau_round
    }

    pub const fn finalized_ordinal(self) -> u64 {
        self.finalized_ordinal
    }

    pub const fn consensus_unix_seconds(self) -> i64 {
        self.consensus_unix_seconds
    }

    pub fn to_canonical_bytes(self) -> [u8; FINALIZED_EXECUTION_CONTEXT_V1_LEN] {
        let mut out = [0u8; FINALIZED_EXECUTION_CONTEXT_V1_LEN];
        write_prefix(&mut out, CONTEXT_MAGIC);
        let mut cursor = PREFIX_LEN;
        write_32(&mut out, &mut cursor, self.block_id);
        write_u64(&mut out, &mut cursor, self.tau_round);
        write_u64(&mut out, &mut cursor, self.finalized_ordinal);
        write_i64(&mut out, &mut cursor, self.consensus_unix_seconds);
        debug_assert_eq!(cursor, FINALIZED_EXECUTION_CONTEXT_V1_LEN);
        out
    }

    pub fn decode_canonical(bytes: &[u8]) -> Result<Self, FinalizedReceiptCoreV1Error> {
        require_wire(bytes, FINALIZED_EXECUTION_CONTEXT_V1_LEN, CONTEXT_MAGIC)?;
        let mut cursor = PREFIX_LEN;
        let context = Self::new(
            read_32(bytes, &mut cursor),
            read_u64(bytes, &mut cursor),
            read_u64(bytes, &mut cursor),
            read_i64(bytes, &mut cursor),
        );
        debug_assert_eq!(cursor, FINALIZED_EXECUTION_CONTEXT_V1_LEN);
        Ok(context)
    }
}

/// Typed signer-independent finalized receipt identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FinalizedReceiptIdV1([u8; 32]);

impl FinalizedReceiptIdV1 {
    pub const fn from_bytes(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }

    pub const fn bytes(self) -> [u8; 32] {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct DisclosureCommitment {
    count: u64,
    digest: [u8; 32],
}

/// Fixed-width deterministic projection of one finalized [`TurnReceipt`].
///
/// The five count+digest fields commit the complete canonical contents of routing directives,
/// introduction exports, derivation records, emitted events, and consumed-capability witnesses.
/// `executor_signature` is intentionally excluded; it belongs in a local envelope over [`Self::id`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedReceiptCoreV1 {
    context: FinalizedExecutionContextV1,
    committee_epoch: u64,
    turn_hash: [u8; 32],
    forest_hash: [u8; 32],
    pre_state_hash: [u8; 32],
    post_state_hash: [u8; 32],
    effects_hash: [u8; 32],
    computrons_used: u64,
    action_count: u64,
    previous_receipt_id: Option<FinalizedReceiptIdV1>,
    agent: [u8; 32],
    federation_id: [u8; 32],
    routing: DisclosureCommitment,
    introduction_exports: DisclosureCommitment,
    derivations: DisclosureCommitment,
    events: DisclosureCommitment,
    consumed_capabilities: DisclosureCommitment,
    was_encrypted: bool,
    was_burn: bool,
}

impl FinalizedReceiptCoreV1 {
    /// Project a final executor receipt under an authenticated finalization context.
    ///
    /// The receipt timestamp must equal the context time.  This fail-closed equality is the seam
    /// that prevents a locally seeded executor clock from being laundered into consensus identity.
    pub fn from_receipt(
        context: FinalizedExecutionContextV1,
        committee_epoch: u64,
        receipt: &TurnReceipt,
    ) -> Result<Self, FinalizedReceiptCoreV1Error> {
        if receipt.finality != Finality::Final {
            return Err(FinalizedReceiptCoreV1Error::ReceiptNotFinal);
        }
        if receipt.timestamp != context.consensus_unix_seconds {
            return Err(FinalizedReceiptCoreV1Error::ReceiptTimestampMismatch {
                expected: context.consensus_unix_seconds,
                actual: receipt.timestamp,
            });
        }
        let action_count = u64::try_from(receipt.action_count)
            .map_err(|_| FinalizedReceiptCoreV1Error::CountOverflow("actions"))?;
        Ok(Self {
            context,
            committee_epoch,
            turn_hash: receipt.turn_hash,
            forest_hash: receipt.forest_hash,
            pre_state_hash: receipt.pre_state_hash,
            post_state_hash: receipt.post_state_hash,
            effects_hash: receipt.effects_hash,
            computrons_used: receipt.computrons_used,
            action_count,
            previous_receipt_id: receipt
                .previous_receipt_hash
                .map(FinalizedReceiptIdV1::from_bytes),
            agent: *receipt.agent.as_bytes(),
            federation_id: receipt.federation_id,
            routing: routing_commitment(receipt)?,
            introduction_exports: introduction_export_commitment(receipt)?,
            derivations: derivation_commitment(receipt)?,
            events: event_commitment(receipt)?,
            consumed_capabilities: consumed_capability_commitment(receipt)?,
            was_encrypted: receipt.was_encrypted,
            was_burn: receipt.was_burn,
        })
    }

    pub const fn context(&self) -> FinalizedExecutionContextV1 {
        self.context
    }

    pub const fn committee_epoch(&self) -> u64 {
        self.committee_epoch
    }

    pub const fn previous_receipt_id(&self) -> Option<FinalizedReceiptIdV1> {
        self.previous_receipt_id
    }

    pub fn id(&self) -> FinalizedReceiptIdV1 {
        let mut hasher = blake3::Hasher::new_derive_key(CORE_ID_DOMAIN);
        hasher.update(&self.to_canonical_bytes());
        FinalizedReceiptIdV1(*hasher.finalize().as_bytes())
    }

    pub fn to_canonical_bytes(&self) -> [u8; FINALIZED_RECEIPT_CORE_V1_LEN] {
        let mut out = [0u8; FINALIZED_RECEIPT_CORE_V1_LEN];
        write_prefix(&mut out, CORE_MAGIC);
        let mut cursor = PREFIX_LEN;
        let context = self.context.to_canonical_bytes();
        out[cursor..cursor + context.len()].copy_from_slice(&context);
        cursor += context.len();
        write_u64(&mut out, &mut cursor, self.committee_epoch);
        for value in [
            self.turn_hash,
            self.forest_hash,
            self.pre_state_hash,
            self.post_state_hash,
            self.effects_hash,
        ] {
            write_32(&mut out, &mut cursor, value);
        }
        write_u64(&mut out, &mut cursor, self.computrons_used);
        write_u64(&mut out, &mut cursor, self.action_count);
        match self.previous_receipt_id {
            Some(id) => {
                out[cursor] = 1;
                cursor += 1;
                write_32(&mut out, &mut cursor, id.bytes());
            }
            None => {
                out[cursor] = 0;
                cursor += 1;
                write_32(&mut out, &mut cursor, [0; 32]);
            }
        }
        write_32(&mut out, &mut cursor, self.agent);
        write_32(&mut out, &mut cursor, self.federation_id);
        for disclosure in [
            self.routing,
            self.introduction_exports,
            self.derivations,
            self.events,
            self.consumed_capabilities,
        ] {
            write_u64(&mut out, &mut cursor, disclosure.count);
            write_32(&mut out, &mut cursor, disclosure.digest);
        }
        out[cursor] = u8::from(self.was_encrypted) | (u8::from(self.was_burn) << 1);
        cursor += 1;
        // Six zero reserved bytes complete the fixed-width record.
        cursor += 6;
        debug_assert_eq!(cursor, FINALIZED_RECEIPT_CORE_V1_LEN);
        out
    }

    pub fn decode_canonical(bytes: &[u8]) -> Result<Self, FinalizedReceiptCoreV1Error> {
        require_wire(bytes, FINALIZED_RECEIPT_CORE_V1_LEN, CORE_MAGIC)?;
        let mut cursor = PREFIX_LEN;
        let context = FinalizedExecutionContextV1::decode_canonical(
            &bytes[cursor..cursor + FINALIZED_EXECUTION_CONTEXT_V1_LEN],
        )?;
        cursor += FINALIZED_EXECUTION_CONTEXT_V1_LEN;
        let committee_epoch = read_u64(bytes, &mut cursor);
        let turn_hash = read_32(bytes, &mut cursor);
        let forest_hash = read_32(bytes, &mut cursor);
        let pre_state_hash = read_32(bytes, &mut cursor);
        let post_state_hash = read_32(bytes, &mut cursor);
        let effects_hash = read_32(bytes, &mut cursor);
        let computrons_used = read_u64(bytes, &mut cursor);
        let action_count = read_u64(bytes, &mut cursor);
        let previous_tag = bytes[cursor];
        cursor += 1;
        let previous_bytes = read_32(bytes, &mut cursor);
        let previous_receipt_id = match previous_tag {
            0 if previous_bytes == [0; 32] => None,
            0 => return Err(FinalizedReceiptCoreV1Error::NonCanonicalAbsentPredecessor),
            1 => Some(FinalizedReceiptIdV1::from_bytes(previous_bytes)),
            tag => return Err(FinalizedReceiptCoreV1Error::BadOptionalTag(tag)),
        };
        let agent = read_32(bytes, &mut cursor);
        let federation_id = read_32(bytes, &mut cursor);
        let mut read_disclosure = || {
            let count = read_u64(bytes, &mut cursor);
            let digest = read_32(bytes, &mut cursor);
            DisclosureCommitment { count, digest }
        };
        let routing = read_disclosure();
        let introduction_exports = read_disclosure();
        let derivations = read_disclosure();
        let events = read_disclosure();
        let consumed_capabilities = read_disclosure();
        let flags = bytes[cursor];
        cursor += 1;
        if flags & !0b11 != 0 {
            return Err(FinalizedReceiptCoreV1Error::UnknownFlags(flags));
        }
        if bytes[cursor..cursor + 6] != [0; 6] {
            return Err(FinalizedReceiptCoreV1Error::NonZeroReserved);
        }
        cursor += 6;
        debug_assert_eq!(cursor, FINALIZED_RECEIPT_CORE_V1_LEN);
        Ok(Self {
            context,
            committee_epoch,
            turn_hash,
            forest_hash,
            pre_state_hash,
            post_state_hash,
            effects_hash,
            computrons_used,
            action_count,
            previous_receipt_id,
            agent,
            federation_id,
            routing,
            introduction_exports,
            derivations,
            events,
            consumed_capabilities,
            was_encrypted: flags & 1 != 0,
            was_burn: flags & 2 != 0,
        })
    }
}

fn routing_commitment(
    receipt: &TurnReceipt,
) -> Result<DisclosureCommitment, FinalizedReceiptCoreV1Error> {
    let count = checked_count(receipt.routing_directives.len(), "routing directives")?;
    let mut hasher = blake3::Hasher::new_derive_key("dregg-finalized-routing-v1");
    hasher.update(&count.to_le_bytes());
    for directive in &receipt.routing_directives {
        hasher.update(directive.sender.as_bytes());
        hasher.update(directive.target.as_bytes());
        hasher.update(&directive.authorizing_turn);
        hash_optional_u64(&mut hasher, directive.expires);
    }
    Ok(DisclosureCommitment {
        count,
        digest: *hasher.finalize().as_bytes(),
    })
}

fn introduction_export_commitment(
    receipt: &TurnReceipt,
) -> Result<DisclosureCommitment, FinalizedReceiptCoreV1Error> {
    let count = checked_count(receipt.introduction_exports.len(), "introduction exports")?;
    let mut hasher = blake3::Hasher::new_derive_key("dregg-finalized-introduction-exports-v1");
    hasher.update(&count.to_le_bytes());
    for export in &receipt.introduction_exports {
        hasher.update(export.target.as_bytes());
        hasher.update(export.recipient.as_bytes());
        hasher.update(&export.authorizing_turn);
        hash_optional_u64(&mut hasher, export.expires);
    }
    Ok(DisclosureCommitment {
        count,
        digest: *hasher.finalize().as_bytes(),
    })
}

fn derivation_commitment(
    receipt: &TurnReceipt,
) -> Result<DisclosureCommitment, FinalizedReceiptCoreV1Error> {
    let count = checked_count(receipt.derivation_records.len(), "derivation records")?;
    let mut hasher = blake3::Hasher::new_derive_key("dregg-finalized-derivations-v1");
    hasher.update(&count.to_le_bytes());
    for record in &receipt.derivation_records {
        hasher.update(&record.hash());
    }
    Ok(DisclosureCommitment {
        count,
        digest: *hasher.finalize().as_bytes(),
    })
}

fn event_commitment(
    receipt: &TurnReceipt,
) -> Result<DisclosureCommitment, FinalizedReceiptCoreV1Error> {
    let count = checked_count(receipt.emitted_events.len(), "events")?;
    let mut hasher = blake3::Hasher::new_derive_key("dregg-finalized-events-v1");
    hasher.update(&count.to_le_bytes());
    for event in &receipt.emitted_events {
        hasher.update(event.cell.as_bytes());
        hasher.update(&event.topic);
        let data_count = checked_count(event.data.len(), "event data")?;
        hasher.update(&data_count.to_le_bytes());
        for field in &event.data {
            hasher.update(field);
        }
    }
    Ok(DisclosureCommitment {
        count,
        digest: *hasher.finalize().as_bytes(),
    })
}

fn consumed_capability_commitment(
    receipt: &TurnReceipt,
) -> Result<DisclosureCommitment, FinalizedReceiptCoreV1Error> {
    let count = checked_count(receipt.consumed_capabilities.len(), "consumed capabilities")?;
    let mut hasher = blake3::Hasher::new_derive_key("dregg-finalized-consumed-capabilities-v1");
    hasher.update(&count.to_le_bytes());
    for witness in &receipt.consumed_capabilities {
        hasher.update(&witness.hash());
    }
    Ok(DisclosureCommitment {
        count,
        digest: *hasher.finalize().as_bytes(),
    })
}

fn checked_count(len: usize, field: &'static str) -> Result<u64, FinalizedReceiptCoreV1Error> {
    u64::try_from(len).map_err(|_| FinalizedReceiptCoreV1Error::CountOverflow(field))
}

fn hash_optional_u64(hasher: &mut blake3::Hasher, value: Option<u64>) {
    match value {
        Some(value) => {
            hasher.update(&[1]);
            hasher.update(&value.to_le_bytes());
        }
        None => {
            hasher.update(&[0]);
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FinalizedReceiptCoreV1Error {
    WrongWireLength { expected: usize, actual: usize },
    WrongMagic,
    UnsupportedVersion(u16),
    NonZeroReserved,
    BadOptionalTag(u8),
    NonCanonicalAbsentPredecessor,
    UnknownFlags(u8),
    ReceiptNotFinal,
    ReceiptTimestampMismatch { expected: i64, actual: i64 },
    CountOverflow(&'static str),
}

impl fmt::Display for FinalizedReceiptCoreV1Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrongWireLength { expected, actual } => {
                write!(
                    f,
                    "wrong finalized receipt wire length: expected {expected}, got {actual}"
                )
            }
            Self::WrongMagic => f.write_str("wrong finalized receipt wire magic"),
            Self::UnsupportedVersion(version) => {
                write!(f, "unsupported finalized receipt wire version {version}")
            }
            Self::NonZeroReserved => f.write_str("nonzero finalized receipt reserved bytes"),
            Self::BadOptionalTag(tag) => write!(f, "bad finalized receipt optional tag {tag}"),
            Self::NonCanonicalAbsentPredecessor => {
                f.write_str("absent finalized receipt predecessor has nonzero payload")
            }
            Self::UnknownFlags(flags) => write!(f, "unknown finalized receipt flags {flags:#x}"),
            Self::ReceiptNotFinal => f.write_str("tentative receipt cannot mint a finalized core"),
            Self::ReceiptTimestampMismatch { expected, actual } => write!(
                f,
                "receipt timestamp {actual} differs from authenticated consensus time {expected}"
            ),
            Self::CountOverflow(field) => write!(f, "finalized receipt {field} count exceeds u64"),
        }
    }
}

impl std::error::Error for FinalizedReceiptCoreV1Error {}

fn write_prefix(out: &mut [u8], magic: [u8; 4]) {
    out[..4].copy_from_slice(&magic);
    out[4..6].copy_from_slice(&WIRE_VERSION.to_le_bytes());
    // out[6..8] are reserved zero.
}

fn require_wire(
    bytes: &[u8],
    expected_len: usize,
    expected_magic: [u8; 4],
) -> Result<(), FinalizedReceiptCoreV1Error> {
    if bytes.len() != expected_len {
        return Err(FinalizedReceiptCoreV1Error::WrongWireLength {
            expected: expected_len,
            actual: bytes.len(),
        });
    }
    if bytes[..4] != expected_magic {
        return Err(FinalizedReceiptCoreV1Error::WrongMagic);
    }
    let version = u16::from_le_bytes(bytes[4..6].try_into().expect("two bytes"));
    if version != WIRE_VERSION {
        return Err(FinalizedReceiptCoreV1Error::UnsupportedVersion(version));
    }
    if bytes[6..8] != [0; 2] {
        return Err(FinalizedReceiptCoreV1Error::NonZeroReserved);
    }
    Ok(())
}

fn write_32(out: &mut [u8], cursor: &mut usize, value: [u8; 32]) {
    out[*cursor..*cursor + 32].copy_from_slice(&value);
    *cursor += 32;
}

fn write_u64(out: &mut [u8], cursor: &mut usize, value: u64) {
    out[*cursor..*cursor + 8].copy_from_slice(&value.to_le_bytes());
    *cursor += 8;
}

fn write_i64(out: &mut [u8], cursor: &mut usize, value: i64) {
    out[*cursor..*cursor + 8].copy_from_slice(&value.to_le_bytes());
    *cursor += 8;
}

fn read_32(bytes: &[u8], cursor: &mut usize) -> [u8; 32] {
    let value = bytes[*cursor..*cursor + 32]
        .try_into()
        .expect("wire length checked");
    *cursor += 32;
    value
}

fn read_u64(bytes: &[u8], cursor: &mut usize) -> u64 {
    let value = u64::from_le_bytes(
        bytes[*cursor..*cursor + 8]
            .try_into()
            .expect("wire length checked"),
    );
    *cursor += 8;
    value
}

fn read_i64(bytes: &[u8], cursor: &mut usize) -> i64 {
    let value = i64::from_le_bytes(
        bytes[*cursor..*cursor + 8]
            .try_into()
            .expect("wire length checked"),
    );
    *cursor += 8;
    value
}

#[cfg(test)]
mod tests {
    use super::*;

    fn receipt_at(timestamp: i64) -> TurnReceipt {
        TurnReceipt {
            turn_hash: [1; 32],
            forest_hash: [2; 32],
            pre_state_hash: [3; 32],
            post_state_hash: [4; 32],
            timestamp,
            effects_hash: [5; 32],
            computrons_used: 123,
            action_count: 7,
            federation_id: [6; 32],
            previous_receipt_hash: Some([7; 32]),
            ..TurnReceipt::default()
        }
    }

    #[test]
    fn context_wire_is_fixed_strict_and_roundtrips() {
        let context = FinalizedExecutionContextV1::new([9; 32], 11, 13, -17);
        let bytes = context.to_canonical_bytes();
        assert_eq!(bytes.len(), FINALIZED_EXECUTION_CONTEXT_V1_LEN);
        assert_eq!(
            FinalizedExecutionContextV1::decode_canonical(&bytes),
            Ok(context)
        );
        assert!(matches!(
            FinalizedExecutionContextV1::decode_canonical(&bytes[..63]),
            Err(FinalizedReceiptCoreV1Error::WrongWireLength { .. })
        ));
        let mut reserved = bytes;
        reserved[7] = 1;
        assert_eq!(
            FinalizedExecutionContextV1::decode_canonical(&reserved),
            Err(FinalizedReceiptCoreV1Error::NonZeroReserved)
        );
    }

    #[test]
    fn finalized_id_ignores_local_clock_and_executor_signature() {
        let consensus_time = 1_700_000_000;
        let context = FinalizedExecutionContextV1::new([8; 32], 21, 34, consensus_time);
        let unrelated_local_clock_a = consensus_time - 10_000;
        let unrelated_local_clock_b = consensus_time + 10_000;
        assert_ne!(unrelated_local_clock_a, unrelated_local_clock_b);

        let mut receipt_a = receipt_at(consensus_time);
        receipt_a.executor_signature = Some(vec![0xAA; 64]);
        let mut receipt_b = receipt_a.clone();
        receipt_b.executor_signature = Some(vec![0xBB; 64]);

        let a = FinalizedReceiptCoreV1::from_receipt(context, 5, &receipt_a).unwrap();
        let b = FinalizedReceiptCoreV1::from_receipt(context, 5, &receipt_b).unwrap();
        assert_eq!(a, b);
        assert_eq!(a.id(), b.id());
        assert_eq!(
            FinalizedReceiptCoreV1::decode_canonical(&a.to_canonical_bytes()),
            Ok(a)
        );
    }

    #[test]
    fn consensus_time_and_deterministic_disclosures_change_finalized_id() {
        let time = 1_700_000_000;
        let base_context = FinalizedExecutionContextV1::new([8; 32], 21, 34, time);
        let receipt = receipt_at(time);
        let base = FinalizedReceiptCoreV1::from_receipt(base_context, 5, &receipt).unwrap();

        let later_context = FinalizedExecutionContextV1::new([8; 32], 21, 34, time + 1);
        let later =
            FinalizedReceiptCoreV1::from_receipt(later_context, 5, &receipt_at(time + 1)).unwrap();
        assert_ne!(base.id(), later.id());

        let mut disclosed = receipt;
        disclosed.was_burn = true;
        let disclosed = FinalizedReceiptCoreV1::from_receipt(base_context, 5, &disclosed).unwrap();
        assert_ne!(base.id(), disclosed.id());
    }

    #[test]
    fn local_timestamp_or_tentative_receipt_cannot_mint_finalized_core() {
        let context = FinalizedExecutionContextV1::new([8; 32], 21, 34, 100);
        assert_eq!(
            FinalizedReceiptCoreV1::from_receipt(context, 5, &receipt_at(99)),
            Err(FinalizedReceiptCoreV1Error::ReceiptTimestampMismatch {
                expected: 100,
                actual: 99,
            })
        );
        let mut tentative = receipt_at(100);
        tentative.finality = Finality::Tentative;
        assert_eq!(
            FinalizedReceiptCoreV1::from_receipt(context, 5, &tentative),
            Err(FinalizedReceiptCoreV1Error::ReceiptNotFinal)
        );
    }

    #[test]
    fn core_decoder_refuses_trailing_and_noncanonical_absent_predecessor() {
        let context = FinalizedExecutionContextV1::new([8; 32], 21, 34, 100);
        let mut receipt = receipt_at(100);
        receipt.previous_receipt_hash = None;
        let core = FinalizedReceiptCoreV1::from_receipt(context, 5, &receipt).unwrap();
        let bytes = core.to_canonical_bytes();
        let mut trailing = bytes.to_vec();
        trailing.push(0);
        assert!(matches!(
            FinalizedReceiptCoreV1::decode_canonical(&trailing),
            Err(FinalizedReceiptCoreV1Error::WrongWireLength { .. })
        ));

        // Header + nested context + epoch + five commitments + two counters + option tag.
        const PREDECESSOR_PAYLOAD_OFFSET: usize = 8 + 64 + 8 + 5 * 32 + 2 * 8 + 1;
        let mut noncanonical = bytes;
        noncanonical[PREDECESSOR_PAYLOAD_OFFSET] = 1;
        assert_eq!(
            FinalizedReceiptCoreV1::decode_canonical(&noncanonical),
            Err(FinalizedReceiptCoreV1Error::NonCanonicalAbsentPredecessor)
        );
    }
}
