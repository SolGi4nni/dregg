//! O(1) live induction boundary between the faithful nullifier image and exact FNSP-v3.
//!
//! A full store-open/bootstrap audit compares both complete append histories.  Its result is
//! summarized by this domain-separated rolling seal.  Thereafter the only production mutation is
//! [`stage_matching_append_in`], which accepts the same append record from both authorities and
//! advances the seal in their shared redb writer.  Live admission therefore checks one sealed
//! head plus the two authority counts instead of replaying and comparing both histories per turn.
//!
//! The seal is not a substitute for the boot audit: it is the durable induction hypothesis that
//! the boot audit establishes and every atomic paired append preserves.

use dregg_circuit::exact_nullifier_aafi::ExactAppendRecord;
use redb::{
    ReadTransaction, ReadableTable, ReadableTableMetadata, TableDefinition, WriteTransaction,
};

use crate::{Result, StoreError, exact_fnsp_v3_state, tables};

pub(crate) const EXACT_FNSP_V3_FAITHFUL_BRIDGE: TableDefinition<u8, &[u8]> =
    TableDefinition::new("exact_fnsp_v3_faithful_bridge_v1");

const SINGLETON_KEY: u8 = 0;
const MAGIC: [u8; 4] = *b"FEB3";
const VERSION: u8 = 1;
const RESERVED_OFFSET: usize = 5;
const COUNT_OFFSET: usize = 8;
const ROLLING_SEAL_OFFSET: usize = 16;
const WIRE_SEAL_OFFSET: usize = 48;
const WIRE_LEN: usize = 80;
const ROLLING_DOMAIN: &str = "dregg-exact-fnsp-v3-faithful-bridge-rolling-v1";
const WIRE_DOMAIN: &str = "dregg-exact-fnsp-v3-faithful-bridge-wire-v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct BridgeHeadV1 {
    count: u64,
    rolling_seal: [u8; 32],
}

impl BridgeHeadV1 {
    fn genesis() -> Self {
        let mut hasher = blake3::Hasher::new_derive_key(ROLLING_DOMAIN);
        hasher.update(b"genesis");
        Self {
            count: 0,
            rolling_seal: *hasher.finalize().as_bytes(),
        }
    }

    fn from_records(records: &[ExactAppendRecord]) -> Result<Self> {
        let mut head = Self::genesis();
        for record in records {
            head = head.append(*record)?;
        }
        Ok(head)
    }

    fn append(self, record: ExactAppendRecord) -> Result<Self> {
        if record.seq != self.count {
            return Err(StoreError::Integrity(format!(
                "faithful/exact bridge append sequence {} differs from sealed count {}",
                record.seq, self.count
            )));
        }
        let count = self.count.checked_add(1).ok_or_else(|| {
            StoreError::Integrity("faithful/exact bridge count overflow".to_string())
        })?;
        let mut hasher = blake3::Hasher::new_derive_key(ROLLING_DOMAIN);
        hasher.update(b"append");
        hasher.update(&self.count.to_le_bytes());
        hasher.update(&self.rolling_seal);
        hasher.update(&record.seq.to_le_bytes());
        hasher.update(&record.raw);
        hasher.update(&record.value.to_le_bytes());
        Ok(Self {
            count,
            rolling_seal: *hasher.finalize().as_bytes(),
        })
    }

    fn encode(self) -> [u8; WIRE_LEN] {
        let mut out = [0u8; WIRE_LEN];
        out[..4].copy_from_slice(&MAGIC);
        out[4] = VERSION;
        out[COUNT_OFFSET..ROLLING_SEAL_OFFSET].copy_from_slice(&self.count.to_le_bytes());
        out[ROLLING_SEAL_OFFSET..WIRE_SEAL_OFFSET].copy_from_slice(&self.rolling_seal);
        let mut wire_hasher = blake3::Hasher::new_derive_key(WIRE_DOMAIN);
        wire_hasher.update(&out[..WIRE_SEAL_OFFSET]);
        let wire_seal = wire_hasher.finalize();
        out[WIRE_SEAL_OFFSET..].copy_from_slice(wire_seal.as_bytes());
        out
    }

    fn decode(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != WIRE_LEN {
            return Err(StoreError::Integrity(format!(
                "faithful/exact bridge wire length {}, expected {WIRE_LEN}",
                bytes.len()
            )));
        }
        if bytes[..4] != MAGIC {
            return Err(StoreError::Integrity(
                "faithful/exact bridge wire has wrong magic".to_string(),
            ));
        }
        if bytes[4] != VERSION {
            return Err(StoreError::Integrity(format!(
                "unsupported faithful/exact bridge version {}",
                bytes[4]
            )));
        }
        if bytes[RESERVED_OFFSET..COUNT_OFFSET]
            .iter()
            .any(|byte| *byte != 0)
        {
            return Err(StoreError::Integrity(
                "faithful/exact bridge reserved bytes are nonzero".to_string(),
            ));
        }
        let mut wire_hasher = blake3::Hasher::new_derive_key(WIRE_DOMAIN);
        wire_hasher.update(&bytes[..WIRE_SEAL_OFFSET]);
        let expected = wire_hasher.finalize();
        if bytes[WIRE_SEAL_OFFSET..] != expected.as_bytes()[..] {
            return Err(StoreError::Integrity(
                "faithful/exact bridge wire seal mismatch".to_string(),
            ));
        }
        let mut count = [0u8; 8];
        count.copy_from_slice(&bytes[COUNT_OFFSET..ROLLING_SEAL_OFFSET]);
        let mut rolling_seal = [0u8; 32];
        rolling_seal.copy_from_slice(&bytes[ROLLING_SEAL_OFFSET..WIRE_SEAL_OFFSET]);
        Ok(Self {
            count: u64::from_le_bytes(count),
            rolling_seal,
        })
    }
}

fn load_head(table: &impl ReadableTable<u8, &'static [u8]>) -> Result<Option<BridgeHeadV1>> {
    let len = table.len()?;
    if len == 0 {
        return Ok(None);
    }
    if len != 1 {
        return Err(StoreError::Integrity(format!(
            "faithful/exact bridge table contains {len} rows instead of one"
        )));
    }
    let bytes = table.get(SINGLETON_KEY)?.ok_or_else(|| {
        StoreError::Integrity("faithful/exact bridge singleton key is missing".to_string())
    })?;
    BridgeHeadV1::decode(bytes.value()).map(Some)
}

fn faithful_count_from_read(read: &ReadTransaction) -> Result<u64> {
    let presence = read.open_table(tables::NULLIFIERS)?;
    let records = read.open_table(tables::NULLIFIER_RECORDS_V1)?;
    let presence_len = presence.len()?;
    let records_len = records.len()?;
    if presence_len != records_len {
        return Err(StoreError::Integrity(format!(
            "nullifier presence/record table lengths disagree ({presence_len} != {records_len})"
        )));
    }
    Ok(records_len)
}

fn faithful_count_from_write(write: &WriteTransaction) -> Result<u64> {
    let presence = write.open_table(tables::NULLIFIERS)?;
    let records = write.open_table(tables::NULLIFIER_RECORDS_V1)?;
    let presence_len = presence.len()?;
    let records_len = records.len()?;
    if presence_len != records_len {
        return Err(StoreError::Integrity(format!(
            "nullifier presence/record table lengths disagree ({presence_len} != {records_len})"
        )));
    }
    Ok(records_len)
}

fn validate_counts(head: BridgeHeadV1, faithful_count: u64, exact_count: u64) -> Result<()> {
    if head.count != faithful_count || head.count != exact_count {
        return Err(StoreError::Integrity(format!(
            "faithful/exact bridge count {} disagrees with faithful {faithful_count} / exact {exact_count}",
            head.count
        )));
    }
    Ok(())
}

/// O(1) live admission gate after store-open established the full-history induction base.
pub(crate) fn validate_live_from_read(read: &ReadTransaction) -> Result<()> {
    let exact = exact_fnsp_v3_state::load_live_state_head_from_read(read)?.ok_or_else(|| {
        StoreError::Integrity("exact FNSP-v3 authority is uninitialized".to_string())
    })?;
    let bridge = load_head(&read.open_table(EXACT_FNSP_V3_FAITHFUL_BRIDGE)?)?.ok_or_else(|| {
        StoreError::Integrity("faithful/exact bridge is uninitialized".to_string())
    })?;
    validate_counts(bridge, faithful_count_from_read(read)?, exact.generation())
}

/// Writer-snapshot form of the O(1) live predecessor gate.
pub(crate) fn validate_live_from_write(write: &WriteTransaction) -> Result<()> {
    let exact = exact_fnsp_v3_state::exact_fnsp_v3_state_head_in(write)?;
    let bridge =
        load_head(&write.open_table(EXACT_FNSP_V3_FAITHFUL_BRIDGE)?)?.ok_or_else(|| {
            StoreError::Integrity("faithful/exact bridge is uninitialized".to_string())
        })?;
    validate_counts(
        bridge,
        faithful_count_from_write(write)?,
        exact.generation(),
    )
}

/// Establish or verify the induction base after a complete faithful/exact equality audit.
pub(crate) fn install_after_full_audit_in(
    write: &WriteTransaction,
    records: &[ExactAppendRecord],
) -> Result<()> {
    let expected = BridgeHeadV1::from_records(records)?;
    let mut table = write.open_table(EXACT_FNSP_V3_FAITHFUL_BRIDGE)?;
    match load_head(&table)? {
        Some(existing) if existing != expected => Err(StoreError::Integrity(
            "faithful/exact bridge disagrees with the fully audited append history".to_string(),
        )),
        Some(_) => Ok(()),
        None => {
            let encoded = expected.encode();
            table.insert(SINGLETON_KEY, encoded.as_slice())?;
            Ok(())
        }
    }
}

/// Require no bridge induction claim when the exact authority itself is absent.
pub(crate) fn require_absent_in(write: &WriteTransaction) -> Result<()> {
    if load_head(&write.open_table(EXACT_FNSP_V3_FAITHFUL_BRIDGE)?)?.is_some() {
        return Err(StoreError::Integrity(
            "faithful/exact bridge exists without an exact FNSP-v3 authority".to_string(),
        ));
    }
    Ok(())
}

/// Whether the full-audit induction boundary has been installed in this writer snapshot.
pub(crate) fn installed_in(write: &WriteTransaction) -> Result<bool> {
    Ok(load_head(&write.open_table(EXACT_FNSP_V3_FAITHFUL_BRIDGE)?)?.is_some())
}

/// Advance the induction boundary after both matching history rows were staged.
///
/// The caller passes the independently derived faithful row and exact CAS row.  Equality, prior
/// sealed count, and both durable successor counts are checked before the singleton is replaced.
pub(crate) fn stage_matching_append_in(
    write: &WriteTransaction,
    faithful: ExactAppendRecord,
    exact: ExactAppendRecord,
) -> Result<()> {
    if faithful != exact {
        return Err(StoreError::Integrity(
            "faithful/exact bridge cannot advance over different append records".to_string(),
        ));
    }
    let mut table = write.open_table(EXACT_FNSP_V3_FAITHFUL_BRIDGE)?;
    let predecessor = load_head(&table)?.ok_or_else(|| {
        StoreError::Integrity("faithful/exact bridge is uninitialized".to_string())
    })?;
    let successor = predecessor.append(exact)?;
    let exact_head = exact_fnsp_v3_state::exact_fnsp_v3_state_head_in(write)?;
    validate_counts(
        successor,
        faithful_count_from_write(write)?,
        exact_head.generation(),
    )?;
    let encoded = successor.encode();
    table.insert(SINGLETON_KEY, encoded.as_slice())?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PersistentStore;

    fn install_faithful_records(store: &PersistentStore, records: &[ExactAppendRecord]) {
        let write = store.db.begin_write().unwrap();
        {
            let mut presence = write.open_table(tables::NULLIFIERS).unwrap();
            let mut rows = write.open_table(tables::NULLIFIER_RECORDS_V1).unwrap();
            for record in records {
                let mut encoded = [0u8; 16];
                encoded[..8].copy_from_slice(&record.value.to_le_bytes());
                encoded[8..].copy_from_slice(&record.seq.to_le_bytes());
                presence.insert(&record.raw, ()).unwrap();
                rows.insert(&record.raw, &encoded).unwrap();
            }
        }
        write.commit().unwrap();
    }

    fn nonempty_prefix() -> [ExactAppendRecord; 3] {
        [
            ExactAppendRecord {
                seq: 0,
                raw: [0x21; 32],
                value: 21,
            },
            ExactAppendRecord {
                seq: 1,
                raw: [0x22; 32],
                value: 22,
            },
            ExactAppendRecord {
                seq: 2,
                raw: [0x23; 32],
                value: 23,
            },
        ]
    }

    #[test]
    fn rolling_bridge_wire_and_append_are_byte_stable() {
        let genesis = BridgeHeadV1::genesis();
        assert_eq!(BridgeHeadV1::decode(&genesis.encode()).unwrap(), genesis);
        let record = ExactAppendRecord {
            seq: 0,
            raw: [0x42; 32],
            value: 73,
        };
        let successor = genesis.append(record).unwrap();
        assert_eq!(
            BridgeHeadV1::decode(&successor.encode()).unwrap(),
            successor
        );
        assert_eq!(successor, BridgeHeadV1::from_records(&[record]).unwrap());
        assert_ne!(successor.rolling_seal, genesis.rolling_seal);
    }

    #[test]
    fn rolling_bridge_refuses_wrong_sequence_and_corrupt_wire() {
        let genesis = BridgeHeadV1::genesis();
        assert!(
            genesis
                .append(ExactAppendRecord {
                    seq: 1,
                    raw: [0x11; 32],
                    value: 1,
                })
                .is_err()
        );
        let mut corrupt = genesis.encode();
        corrupt[ROLLING_SEAL_OFFSET] ^= 1;
        assert!(BridgeHeadV1::decode(&corrupt).is_err());
    }

    #[test]
    fn production_bootstrap_installs_live_boundary_before_activation() {
        let store = PersistentStore::open_in_memory().unwrap();
        store
            .initialize_exact_fnsp_v3_state_from_faithful_nullifiers()
            .unwrap();
        assert!(store.exact_fnsp_v3_activation().unwrap().is_none());
        let write = store.db.begin_write().unwrap();
        assert!(installed_in(&write).unwrap());
        write.abort().unwrap();
        store.validate_live_exact_fnsp_v3_faithful_bridge().unwrap();
    }

    #[test]
    fn nonempty_missing_bridge_is_migrated_once_on_full_reopen_audit() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("bridge-migration.redb");
        {
            let store = PersistentStore::open(&path).unwrap();
            let records = nonempty_prefix();
            install_faithful_records(&store, &records);
            store
                .initialize_exact_fnsp_v3_state_from_faithful_nullifiers()
                .unwrap();
            store.validate_live_exact_fnsp_v3_faithful_bridge().unwrap();

            // Model an exact-v3 image written before the additive bridge existed.
            let write = store.db.begin_write().unwrap();
            write
                .open_table(EXACT_FNSP_V3_FAITHFUL_BRIDGE)
                .unwrap()
                .remove(SINGLETON_KEY)
                .unwrap();
            write.commit().unwrap();
        }

        let reopened = PersistentStore::open(&path).expect("full audit installs migration seal");
        reopened
            .validate_live_exact_fnsp_v3_faithful_bridge()
            .expect("migrated boundary is live");
    }

    #[test]
    fn hostile_interior_faithful_row_corruption_fails_full_reopen_audit() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("bridge-interior-corruption.redb");
        {
            let store = PersistentStore::open(&path).unwrap();
            let records = nonempty_prefix();
            install_faithful_records(&store, &records);
            store
                .initialize_exact_fnsp_v3_state_from_faithful_nullifiers()
                .unwrap();
            store.validate_live_exact_fnsp_v3_faithful_bridge().unwrap();

            // Keep cardinality, key, and dense sequence unchanged; alter only an interior value.
            // A count/last-row shortcut would accept this.  Reopen must replay both full histories
            // and refuse before the rolling seal can be trusted for live O(1) admission.
            let write = store.db.begin_write().unwrap();
            {
                let mut rows = write.open_table(tables::NULLIFIER_RECORDS_V1).unwrap();
                let mut corrupt = [0u8; 16];
                corrupt[..8].copy_from_slice(&999u64.to_le_bytes());
                corrupt[8..].copy_from_slice(&1u64.to_le_bytes());
                rows.insert(&records[1].raw, &corrupt).unwrap();
            }
            write.commit().unwrap();
        }

        assert!(
            PersistentStore::open(&path).is_err(),
            "interior faithful/exact divergence must fail the full boot audit"
        );
    }
}
