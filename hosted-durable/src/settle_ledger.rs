//! `settle_ledger` — a **durable**, restart-surviving record of settled
//! `(lease, period)` keys, so a production settlement rail (e.g.
//! [`crate::payable::PayableSettlement`] over a node-API submitter) is
//! exactly-once across a process restart (or a second settler instance sharing
//! the path), not merely exactly-once in-memory.
//!
//! ## Why this exists (red-team LEASE-3, ported from the operated layer)
//!
//! [`crate::payable::PayableSettlement`]'s dedup is an in-memory
//! `Mutex<HashMap<(lease,period), …>>` — its own doc names cross-restart
//! exactly-once as "the submitter side's concern (the node-API rail's durable
//! write-ahead ledger)". THIS is that ledger, ported from the operated layer
//! (`the prior operated layer control/src/settle_ledger.rs`) where the property was red-teamed:
//! a settler restart (a crash, a redeploy, a second instance) starts with an
//! EMPTY map, so it re-settles every `(lease, period)` it is handed again —
//! each as a fresh **real on-chain `Transfer`**, double-charging the lessee.
//!
//! This ledger closes that: it persists each settled key to disk and is
//! consulted **before** a transfer is submitted. A reservation is written
//! **write-ahead** (before the on-chain submit), so the property the rail
//! upholds is **at-most-once on-chain submission per `(lease, period)` across
//! any number of restarts**:
//!
//! - a key already present (this process OR a prior process's persisted file)
//!   is **replayed** — no second transfer is submitted;
//! - a fresh key is persisted+fsync'd before the submit, so a crash anywhere
//!   after the reservation leaves the key marked and a restart will NOT
//!   resubmit.
//!
//! The safe direction is deliberate: a settlement that crashed between the
//! write-ahead reservation and the on-chain commit is treated as
//! already-settled (it may be an operator-reconciliation item — under-charge,
//! never double-charge). The strongest cross-live-instance form is a database
//! unique constraint on `(lease, period)`; this file-backed ledger is the
//! dependency-light form that makes a **restart** provably non-double-charging.
//! (The kernel-native endgame is stronger still: a settlement as a turn whose
//! exactly-once is the nullifier discipline — this ledger is the honest rail
//! until settlements ride turns end-to-end.)
//!
//! ## Format
//!
//! Append-only JSON lines, one [`SettleRecord`] per line. A reservation appends
//! a record with `turn_hash: null`; a confirmation appends the same key with
//! the on-chain turn hash + post-transfer balances. On load, the **last**
//! record for a key wins, so a confirmed record supersedes its reservation.
//!
//! ## Wiring (deliberately unwired at port time)
//!
//! This file was ported as a NEW file only. To activate:
//! 1. `hosted-durable/src/lib.rs`: add `pub mod settle_ledger;`
//! 2. `hosted-durable/Cargo.toml`: add `serde_json = { workspace = true }`
//! 3. Consult it from the submitter side around `PayableSettlement::settle`
//!    (reserve_or_replay → submit → confirm).

use std::collections::HashMap;
use std::fs::{File, OpenOptions};
use std::io::{self, BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use serde::{Deserialize, Serialize};

use crate::settle::{LeaseCharge, SettleError, SettleReceipt};

/// One durable settlement record — the persisted half of the exactly-once key.
///
/// `turn_hash` is `None` for a write-ahead reservation (persisted before the
/// on-chain submit) and `Some` once the conserving `Transfer` was accepted.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SettleRecord {
    pub lease_id: String,
    pub period: i64,
    pub asset: String,
    pub amount: i64,
    /// The payer's balance after the transfer (`0` until confirmed).
    #[serde(default)]
    pub payer_balance: i64,
    /// The beneficiary's balance after the transfer (`0` until confirmed).
    #[serde(default)]
    pub beneficiary_balance: i64,
    /// The on-chain turn hash of the settling `Transfer`, once accepted.
    #[serde(default)]
    pub turn_hash: Option<String>,
}

impl SettleRecord {
    /// The exactly-once key `(lease_id, period)`.
    fn key(&self) -> (String, i64) {
        (self.lease_id.clone(), self.period)
    }

    /// The replay receipt this persisted record reconstructs (always `replayed`).
    fn replay_receipt(&self) -> SettleReceipt {
        SettleReceipt {
            lease_id: self.lease_id.clone(),
            period: self.period,
            asset: self.asset.clone(),
            amount: self.amount,
            payer_balance: self.payer_balance,
            beneficiary_balance: self.beneficiary_balance,
            replayed: true,
        }
    }
}

/// The outcome of [`DurableSettleLedger::reserve_or_replay`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Reserved {
    /// The `(lease, period)` was not settled before — the reservation is
    /// persisted (write-ahead) and the caller may submit the conserving
    /// `Transfer`.
    Fresh,
    /// The `(lease, period)` was already settled (this process or a prior one):
    /// the recorded receipt is returned and NO transfer is submitted.
    Replay(SettleReceipt),
}

struct Inner {
    /// `(lease_id, period)` → the record persisted for it.
    map: HashMap<(String, i64), SettleRecord>,
    /// The append-only backing file (append mode), fsync'd per write.
    file: File,
}

/// A durable, restart-surviving `(lease, period)` settlement ledger.
pub struct DurableSettleLedger {
    path: PathBuf,
    inner: Mutex<Inner>,
}

impl DurableSettleLedger {
    /// Open (or create) the ledger at `path`, loading every already-settled key
    /// so a restart sees prior settlements and refuses to double-charge.
    pub fn open(path: impl AsRef<Path>) -> io::Result<DurableSettleLedger> {
        let path = path.as_ref().to_path_buf();
        let map = load_records(&path)?;
        let file = OpenOptions::new().create(true).append(true).open(&path)?;
        Ok(DurableSettleLedger {
            path,
            inner: Mutex::new(Inner { map, file }),
        })
    }

    /// The path this ledger persists to.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// How many distinct `(lease, period)` keys have been settled (across
    /// restarts).
    pub fn len(&self) -> usize {
        self.inner.lock().expect("settle ledger poisoned").map.len()
    }

    /// Whether the ledger holds no settled keys.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Reserve `(lease, period)` for settlement, or replay it if already
    /// settled.
    ///
    /// On [`Reserved::Fresh`] the reservation is durably persisted (write-ahead,
    /// fsync'd) **before** this returns, so the caller can safely submit the
    /// transfer knowing a crash afterward will not cause a resubmit. A
    /// re-reserve of an already-settled key returns [`Reserved::Replay`] (no
    /// transfer). A key already settled with *different* terms is a
    /// [`SettleError::Conflict`].
    pub fn reserve_or_replay(&self, charge: &LeaseCharge) -> Result<Reserved, SettleError> {
        let key = (charge.lease_id.clone(), charge.period);
        let mut inner = self.inner.lock().expect("settle ledger poisoned");
        if let Some(prior) = inner.map.get(&key) {
            if prior.amount != charge.amount || prior.asset != charge.asset {
                return Err(SettleError::Conflict {
                    lease_id: charge.lease_id.clone(),
                    period: charge.period,
                });
            }
            return Ok(Reserved::Replay(prior.replay_receipt()));
        }
        let record = SettleRecord {
            lease_id: charge.lease_id.clone(),
            period: charge.period,
            asset: charge.asset.clone(),
            amount: charge.amount,
            payer_balance: 0,
            beneficiary_balance: 0,
            turn_hash: None,
        };
        append_record(&mut inner.file, &record)
            .map_err(|e| SettleError::Backend(format!("persist settlement reservation: {e}")))?;
        inner.map.insert(key, record);
        Ok(Reserved::Fresh)
    }

    /// Confirm a reserved `(lease, period)` with the on-chain turn hash + the
    /// post-transfer balances — persisted so the confirmed receipt survives a
    /// restart. Idempotent: re-confirming overwrites the in-memory record and
    /// appends an updated line.
    pub fn confirm(
        &self,
        charge: &LeaseCharge,
        payer_balance: i64,
        beneficiary_balance: i64,
        turn_hash: Option<String>,
    ) -> Result<SettleReceipt, SettleError> {
        let key = (charge.lease_id.clone(), charge.period);
        let record = SettleRecord {
            lease_id: charge.lease_id.clone(),
            period: charge.period,
            asset: charge.asset.clone(),
            amount: charge.amount,
            payer_balance,
            beneficiary_balance,
            turn_hash,
        };
        let mut inner = self.inner.lock().expect("settle ledger poisoned");
        append_record(&mut inner.file, &record)
            .map_err(|e| SettleError::Backend(format!("persist settlement confirmation: {e}")))?;
        inner.map.insert(key, record);
        Ok(SettleReceipt {
            lease_id: charge.lease_id.clone(),
            period: charge.period,
            asset: charge.asset.clone(),
            amount: charge.amount,
            payer_balance,
            beneficiary_balance,
            replayed: false,
        })
    }

    /// The on-chain turn-receipt hash (64-hex) persisted for `(lease_id,
    /// period)`, if that period settled and the node reported a hash. `None`
    /// for an unsettled period or a write-ahead reservation not yet confirmed.
    pub fn confirmed_turn_hash(&self, lease_id: &str, period: i64) -> Option<String> {
        self.inner
            .lock()
            .expect("settle ledger poisoned")
            .map
            .get(&(lease_id.to_string(), period))
            .and_then(|r| r.turn_hash.clone())
    }

    /// The total amount settled for `lease_id` across all its persisted periods.
    pub fn settled_total(&self, lease_id: &str) -> i64 {
        self.inner
            .lock()
            .expect("settle ledger poisoned")
            .map
            .iter()
            .filter(|((l, _), _)| l == lease_id)
            .map(|(_, r)| r.amount)
            .sum()
    }
}

/// Load every persisted record from `path` (last line per key wins). A missing
/// file is an empty ledger; a malformed line is skipped (the file is
/// append-only, so a torn tail line never corrupts earlier records).
fn load_records(path: &Path) -> io::Result<HashMap<(String, i64), SettleRecord>> {
    let mut map = HashMap::new();
    let file = match File::open(path) {
        Ok(f) => f,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(map),
        Err(e) => return Err(e),
    };
    for line in BufReader::new(file).lines() {
        let line = line?;
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        if let Ok(rec) = serde_json::from_str::<SettleRecord>(line) {
            map.insert(rec.key(), rec);
        }
    }
    Ok(map)
}

/// Append one record as a JSON line and fsync, so the durable mark is on disk
/// before the call returns.
fn append_record(file: &mut File, record: &SettleRecord) -> io::Result<()> {
    let mut line =
        serde_json::to_string(record).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
    line.push('\n');
    file.write_all(line.as_bytes())?;
    file.flush()?;
    file.sync_all()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn charge(lease: &str, period: i64, amount: i64) -> LeaseCharge {
        LeaseCharge::new("lessee", "provider", "USD", lease, period, amount)
    }

    fn temp_path(tag: &str) -> PathBuf {
        let mut p = std::env::temp_dir();
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        p.push(format!("dregg-settle-ledger-{tag}-{nanos}.jsonl"));
        p
    }

    #[test]
    fn reserve_then_replay_in_one_process() {
        let path = temp_path("one-proc");
        let ledger = DurableSettleLedger::open(&path).unwrap();
        assert!(matches!(
            ledger.reserve_or_replay(&charge("L", 1, 10)).unwrap(),
            Reserved::Fresh
        ));
        ledger
            .confirm(&charge("L", 1, 10), 90, 10, Some("h1".into()))
            .unwrap();
        // Re-reserving the same key replays — never Fresh, so never resubmitted.
        match ledger.reserve_or_replay(&charge("L", 1, 10)).unwrap() {
            Reserved::Replay(r) => {
                assert!(r.replayed);
                assert_eq!(r.amount, 10);
                assert_eq!(r.payer_balance, 90);
            }
            Reserved::Fresh => panic!("a settled key must replay, not reserve"),
        }
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn survives_a_restart() {
        let path = temp_path("restart");
        {
            let ledger = DurableSettleLedger::open(&path).unwrap();
            assert!(matches!(
                ledger.reserve_or_replay(&charge("L", 1, 5)).unwrap(),
                Reserved::Fresh
            ));
            ledger
                .confirm(&charge("L", 1, 5), 95, 5, Some("h".into()))
                .unwrap();
        }
        // A brand-new ledger over the same path (a "restart"): the prior
        // settlement is loaded, so the same key replays rather than reserving
        // afresh.
        let restarted = DurableSettleLedger::open(&path).unwrap();
        assert_eq!(restarted.len(), 1);
        assert!(matches!(
            restarted.reserve_or_replay(&charge("L", 1, 5)).unwrap(),
            Reserved::Replay(_)
        ));
        // A NEW period is still fresh.
        assert!(matches!(
            restarted.reserve_or_replay(&charge("L", 2, 5)).unwrap(),
            Reserved::Fresh
        ));
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn reservation_alone_blocks_a_resubmit() {
        // A crash AFTER the write-ahead reservation but BEFORE confirm: the key
        // is still persisted, so a restart replays it (at-most-once on-chain
        // submit).
        let path = temp_path("wal");
        {
            let ledger = DurableSettleLedger::open(&path).unwrap();
            assert!(matches!(
                ledger.reserve_or_replay(&charge("L", 7, 3)).unwrap(),
                Reserved::Fresh
            ));
            // no confirm — simulate a crash between reserve and confirm.
        }
        let restarted = DurableSettleLedger::open(&path).unwrap();
        assert!(matches!(
            restarted.reserve_or_replay(&charge("L", 7, 3)).unwrap(),
            Reserved::Replay(_),
        ));
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn different_terms_same_key_is_a_conflict() {
        let path = temp_path("conflict");
        let ledger = DurableSettleLedger::open(&path).unwrap();
        ledger.reserve_or_replay(&charge("L", 1, 5)).unwrap();
        assert!(matches!(
            ledger.reserve_or_replay(&charge("L", 1, 9)),
            Err(SettleError::Conflict { .. })
        ));
        std::fs::remove_file(&path).ok();
    }
}
