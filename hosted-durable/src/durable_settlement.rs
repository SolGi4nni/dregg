//! `durable_settlement` — the **restart-surviving production settlement
//! rail**: the write-ahead [`crate::settle_ledger::DurableSettleLedger`]
//! composed with the crate's own [`PaySubmitter`](crate::payable::PaySubmitter)
//! wire seam, so cross-restart exactly-once stops being a "submitter side's
//! concern" note on [`crate::payable::PayableSettlement`] and becomes a rail
//! this crate ships.
//!
//! Ported semantics: the operated layer's node-API settlement (the prior operated layer), re-expressed over the native [`PaySubmitter`] seam so no
//! HTTP client is linked here. The settle flow per `(lease, period)`:
//!
//! 1. **validate identities** (64-hex cell ids + asset alias) BEFORE any
//!    reservation is written — a bad payer/beneficiary/asset must fail without
//!    persisting a reservation, otherwise the period is burned (a later retry
//!    of the same charge replays the reservation and returns "settled" without
//!    ever moving value);
//! 2. **reserve_or_replay** — an already-settled key (this process or a prior
//!    process's persisted file) replays its recorded receipt: no second
//!    transfer, across restarts;
//! 3. **submit** the conserving `Transfer` over the injected wire;
//! 4. **confirm** with the on-chain turn hash + post-balances (persisted, so
//!    [`Settlement::settled_turn_hash`] survives a restart — the value a sealed
//!    product receipt threads into its `turn_receipt_hash` view link).
//!
//! A crash between 2 and 4 leaves the key reserved: the restart replays it —
//! at-most-once on-chain, under-charge-never-double-charge (the deliberate safe
//! direction; a reserved-but-unconfirmed key is an operator-reconciliation
//! item). The ledger's own lock makes reserve → submit → confirm effectively
//! exactly-once per key even under concurrent settles of the same period.
//!
//! ## Wiring (applied)
//!
//! `pub mod durable_settlement;` is in `hosted-durable/src/lib.rs` (after
//! `pub mod settle_ledger;`, which this module depends on) and `serde_json` is
//! a crate dependency. This rail is the injectable production [`Settlement`];
//! callers choose it where they would otherwise inject a bare
//! [`crate::payable::PayableSettlement`].

use std::collections::HashMap;
use std::io;
use std::path::Path;

use crate::payable::{PaySubmitter, PayTerms};
use crate::settle::{LeaseCharge, SettleError, SettleReceipt, Settlement};
use crate::settle_ledger::{DurableSettleLedger, Reserved};

/// Parse a 64-hex-char string into 32 bytes, or `None` if malformed. Private
/// twin of the validator vendored in [`crate::payable`] (kept private there
/// too — a trivial helper, duplicated rather than editing the shared file).
fn hex32(hex: &str) -> Option<[u8; 32]> {
    let bytes = hex.as_bytes();
    if bytes.len() != 64 {
        return None;
    }
    let nibble = |b: u8| -> Option<u8> {
        match b {
            b'0'..=b'9' => Some(b - b'0'),
            b'a'..=b'f' => Some(b - b'a' + 10),
            b'A'..=b'F' => Some(b - b'A' + 10),
            _ => None,
        }
    };
    let mut out = [0u8; 32];
    for (i, pair) in bytes.chunks(2).enumerate() {
        out[i] = (nibble(pair[0])? << 4) | nibble(pair[1])?;
    }
    Some(out)
}

/// Require `hex` to be a 64-hex cell id, naming `role` in the refusal.
fn require_cell_id(role: &str, hex: &str) -> Result<(), SettleError> {
    if hex32(hex).is_none() {
        return Err(SettleError::Backend(format!(
            "{role} `{hex}` is not a 64-hex cell id"
        )));
    }
    Ok(())
}

/// The restart-surviving production [`Settlement`]: each charge is one
/// conserving transfer turn submitted over an injected [`PaySubmitter`], with
/// the exactly-once `(lease, period)` keys persisted write-ahead in a
/// [`DurableSettleLedger`] (see the module docs for the flow and the crash
/// semantics).
pub struct DurableSettlement<S: PaySubmitter> {
    submitter: S,
    ledger: DurableSettleLedger,
    /// Optional `asset label -> issuer-cell id (64-hex)` aliases, mirroring
    /// [`crate::payable::PayableSettlement::with_asset`].
    asset_aliases: HashMap<String, String>,
}

impl<S: PaySubmitter> DurableSettlement<S> {
    /// A restart-surviving rail submitting through `submitter`, persisting the
    /// exactly-once keys at `ledger_path` (created if absent; prior settlements
    /// are loaded so a restart refuses to double-charge).
    pub fn open(submitter: S, ledger_path: impl AsRef<Path>) -> io::Result<DurableSettlement<S>> {
        Ok(DurableSettlement {
            submitter,
            ledger: DurableSettleLedger::open(ledger_path)?,
            asset_aliases: HashMap::new(),
        })
    }

    /// Register an asset alias: charges denominated in `label` resolve to the
    /// issuer-cell `asset_hex` (64-hex). A charge whose `asset` is already a
    /// 64-hex id needs no alias.
    pub fn with_asset(mut self, label: impl Into<String>, asset_hex: impl Into<String>) -> Self {
        self.asset_aliases.insert(label.into(), asset_hex.into());
        self
    }

    /// The underlying write-ahead ledger (for audit / reconciliation reads).
    pub fn ledger(&self) -> &DurableSettleLedger {
        &self.ledger
    }

    /// Borrow the wire (test observability; mirrors `PayableSettlement`'s
    /// field access pattern).
    pub fn submitter(&self) -> &S {
        &self.submitter
    }

    /// Resolve a charge's `asset` string to the issuer-cell id (64-hex): a
    /// registered alias, or already a 64-hex id. Malformed ⇒ refused.
    fn asset_hex(&self, asset: &str) -> Result<String, SettleError> {
        let candidate = self
            .asset_aliases
            .get(asset)
            .map(String::as_str)
            .unwrap_or(asset);
        if hex32(candidate).is_none() {
            return Err(SettleError::Backend(format!(
                "asset `{asset}` is neither a registered alias nor a 64-hex issuer-cell id"
            )));
        }
        Ok(candidate.to_string())
    }
}

impl<S: PaySubmitter> Settlement for DurableSettlement<S> {
    fn settle(&self, charge: &LeaseCharge) -> Result<SettleReceipt, SettleError> {
        if charge.amount <= 0 {
            return Err(SettleError::NonPositiveAmount(charge.amount));
        }
        let amount = u64::try_from(charge.amount)
            .map_err(|_| SettleError::NonPositiveAmount(charge.amount))?;

        // Identities validated BEFORE the reservation (a bad identity must not
        // burn the period — see the module docs).
        require_cell_id("payer", &charge.payer)?;
        require_cell_id("beneficiary", &charge.beneficiary)?;
        let asset_hex = self.asset_hex(&charge.asset)?;

        // Write-ahead: persist the reservation (or replay the recorded
        // receipt — no second transfer, across restarts).
        if let Reserved::Replay(receipt) = self.ledger.reserve_or_replay(charge)? {
            return Ok(receipt);
        }

        let terms = PayTerms {
            from_hex: charge.payer.clone(),
            to_hex: charge.beneficiary.clone(),
            asset_hex,
            amount,
            memo: format!("settle:{}:{}", charge.lease_id, charge.period),
        };
        let submitted = self.submitter.submit_pay(&terms)?;
        self.ledger.confirm(
            charge,
            submitted.payer_balance,
            submitted.beneficiary_balance,
            submitted.turn_hash_hex,
        )
    }

    fn settled_total(&self, lease_id: &str) -> i64 {
        self.ledger.settled_total(lease_id)
    }

    /// The real on-chain reserve `holder` (a 64-hex cell id) holds, read
    /// through the submitter. Fail-closed: a non-cell-id holder is `0`
    /// (refuse admission).
    fn funded_balance(&self, _asset: &str, holder: &str) -> i64 {
        if hex32(holder).is_none() {
            return 0;
        }
        self.submitter.funded_balance(holder)
    }

    /// The recorded on-chain turn hash for a settled `(lease_id, period)` —
    /// the `turn_receipt_hash` view-link value. Survives a restart (read from
    /// the persisted ledger).
    fn settled_turn_hash(&self, lease_id: &str, period: i64) -> Option<[u8; 32]> {
        self.ledger
            .confirmed_turn_hash(lease_id, period)
            .as_deref()
            .and_then(hex32)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::payable::SubmittedPay;
    use std::path::PathBuf;
    use std::sync::atomic::{AtomicUsize, Ordering};

    const PAYER: &str = "1111111111111111111111111111111111111111111111111111111111111111";
    const BENEF: &str = "2222222222222222222222222222222222222222222222222222222222222222";
    const ASSET: &str = "3333333333333333333333333333333333333333333333333333333333333333";
    const TURN: &str = "00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff";

    struct MockWire {
        submits: AtomicUsize,
    }

    impl MockWire {
        fn new() -> MockWire {
            MockWire {
                submits: AtomicUsize::new(0),
            }
        }
    }

    impl PaySubmitter for MockWire {
        fn submit_pay(&self, _terms: &PayTerms) -> Result<SubmittedPay, SettleError> {
            self.submits.fetch_add(1, Ordering::SeqCst);
            Ok(SubmittedPay {
                turn_hash_hex: Some(TURN.to_string()),
                payer_balance: 93,
                beneficiary_balance: 7,
            })
        }
        fn funded_balance(&self, _holder_hex: &str) -> i64 {
            100
        }
    }

    fn charge(lease: &str, period: i64, amount: i64) -> LeaseCharge {
        LeaseCharge::new(PAYER, BENEF, ASSET, lease, period, amount)
    }

    fn temp_path(tag: &str) -> PathBuf {
        let mut p = std::env::temp_dir();
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        p.push(format!("hosted-durable-settlement-{tag}-{nanos}.jsonl"));
        p
    }

    #[test]
    fn exactly_once_across_a_restart() {
        let path = temp_path("restart");
        {
            let rail = DurableSettlement::open(MockWire::new(), &path).unwrap();
            let r = rail.settle(&charge("lease-1", 1, 7)).unwrap();
            assert!(!r.replayed);
            assert_eq!(rail.submitter().submits.load(Ordering::SeqCst), 1);
            // The turn hash is recorded — the receipt-contract thread-through.
            assert_eq!(rail.settled_turn_hash("lease-1", 1), hex32(TURN));
        }
        // A fresh rail over the same ledger path (a restart): the same period
        // replays without a second on-chain submit — LEASE-3 stays closed
        // across the restart, which the in-memory PayableSettlement cannot do.
        let rail = DurableSettlement::open(MockWire::new(), &path).unwrap();
        let again = rail.settle(&charge("lease-1", 1, 7)).unwrap();
        assert!(again.replayed);
        assert_eq!(
            rail.submitter().submits.load(Ordering::SeqCst),
            0,
            "a restarted settler must not resubmit a settled period"
        );
        // The confirmed turn hash also survives the restart.
        assert_eq!(rail.settled_turn_hash("lease-1", 1), hex32(TURN));
        assert_eq!(rail.settled_total("lease-1"), 7);
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn distinct_periods_accumulate() {
        let path = temp_path("periods");
        let rail = DurableSettlement::open(MockWire::new(), &path).unwrap();
        rail.settle(&charge("lease-1", 1, 3)).unwrap();
        rail.settle(&charge("lease-1", 2, 4)).unwrap();
        assert_eq!(rail.settled_total("lease-1"), 7);
        assert_eq!(rail.submitter().submits.load(Ordering::SeqCst), 2);
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn same_key_different_terms_is_a_conflict() {
        let path = temp_path("conflict");
        let rail = DurableSettlement::open(MockWire::new(), &path).unwrap();
        rail.settle(&charge("lease-1", 1, 5)).unwrap();
        assert!(matches!(
            rail.settle(&charge("lease-1", 1, 9)),
            Err(SettleError::Conflict { .. })
        ));
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn bad_identities_fail_before_any_reservation() {
        let path = temp_path("ident");
        let rail = DurableSettlement::open(MockWire::new(), &path).unwrap();
        let bad = LeaseCharge::new("not-a-cell", BENEF, ASSET, "lease-1", 1, 5);
        assert!(matches!(rail.settle(&bad), Err(SettleError::Backend(_))));
        let bad_asset = LeaseCharge::new(PAYER, BENEF, "DREGG", "lease-1", 1, 5);
        assert!(matches!(
            rail.settle(&bad_asset),
            Err(SettleError::Backend(_))
        ));
        // No reservation was burned: a corrected retry of the same
        // (lease, period) can still settle for real.
        assert!(rail.ledger().is_empty());
        assert_eq!(rail.submitter().submits.load(Ordering::SeqCst), 0);
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn asset_aliases_resolve_before_the_reservation() {
        let path = temp_path("alias");
        let rail = DurableSettlement::open(MockWire::new(), &path)
            .unwrap()
            .with_asset("DREGG", ASSET);
        let c = LeaseCharge::new(PAYER, BENEF, "DREGG", "lease-1", 1, 5);
        rail.settle(&c).expect("aliased asset settles");
        assert_eq!(rail.settled_total("lease-1"), 5);
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn a_wire_refusal_leaves_the_reservation_for_reconciliation() {
        struct RefusingWire;
        impl PaySubmitter for RefusingWire {
            fn submit_pay(&self, _t: &PayTerms) -> Result<SubmittedPay, SettleError> {
                Err(SettleError::Backend("node said no".into()))
            }
        }
        let path = temp_path("refuse");
        let rail = DurableSettlement::open(RefusingWire, &path).unwrap();
        assert!(matches!(
            rail.settle(&charge("lease-1", 1, 5)),
            Err(SettleError::Backend(_))
        ));
        // The write-ahead reservation IS persisted — the safe under-charge
        // direction: a retry replays instead of risking a double-submit whose
        // first attempt may have landed on-chain before the error.
        assert_eq!(rail.ledger().len(), 1);
        let replay = rail.settle(&charge("lease-1", 1, 5)).unwrap();
        assert!(replay.replayed);
        assert_eq!(rail.settled_turn_hash("lease-1", 1), None);
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn funded_balance_is_fail_closed() {
        let path = temp_path("funded");
        let rail = DurableSettlement::open(MockWire::new(), &path).unwrap();
        assert_eq!(rail.funded_balance("DREGG", PAYER), 100);
        assert_eq!(rail.funded_balance("DREGG", "not-a-cell"), 0);
        std::fs::remove_file(&path).ok();
    }
}
