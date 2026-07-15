//! The funding gate — a publish is admitted only against a resident, non-lapsed
//! hosting lease, AND it is CHARGED for on admission.
//!
//! This is the IMPROVEMENT over a bare "does the chain fund this?" shim: the gate is
//! backed by the resident [`hosted_lease::HostedLease`] — a real durable-execution
//! lease whose rent is metered by a [`StandingObligation`](dregg_cell) (or the fused
//! prepaid meter) and which LAPSES on non-payment.
//!
//! Two teeth bite on EVERY publish, not just the refusal branch:
//!
//! 1. **Clock-driven lapse.** The gate runs [`HostedLease::lapse_if_behind`] with the
//!    handler's own `now` at publish time — so a lease that should have lapsed by
//!    wall-clock IS lapsed before it is trusted, never left "Covered" on stale cached
//!    state until some external caller happens to run the meter.
//! 2. **The accept path is metered.** A covered publish DEBITS a bounded publish
//!    allowance the lease funds ([`PUBLISH_TOPUP_UNITS`] per publish). When the
//!    allowance is spent the gate fails closed with a `402` [`TopupReason::Exhausted`]
//!    hint — a single non-lapsed lease no longer funds unlimited free publishes.
//!
//! A refusal (unfunded / lapsed / exhausted) carries an **x402-style topup hint**
//! ([`TopupHint`]) naming the lease, the rent asset, a suggested amount, and the retry
//! endpoint, so an agent client can auto-fund and re-POST. No free hosting; a
//! self-healing pay loop.

use std::collections::BTreeMap;
use std::sync::Mutex;

use hosted_lease::HostedLease;
use serde::{Deserialize, Serialize};

use crate::lock::lock_recover;

/// The publish-allowance units a single publish consumes — a small fixed
/// control-plane cost (write the content cell + seal the receipt), not a per-byte
/// charge (serving bandwidth is metered on the read path).
pub const PUBLISH_TOPUP_UNITS: u64 = 1;

/// Why the funding gate refused — the x402 topup shapes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TopupReason {
    /// A hosting lease exists for the owner but has LAPSED (rent unpaid) — top it up
    /// to reinstate and retry.
    Lapsed,
    /// No hosting lease covers the owner — open/fund one and retry.
    Unfunded,
    /// The lease is live but its publish allowance is SPENT — top up to extend the
    /// allowance and retry (no free unlimited publishing).
    Exhausted,
}

/// An x402-style payment requirement returned on a `402`: everything an agent client
/// needs to auto-fund the owner's hosting lease and retry the publish.
///
/// Rendered into the `402` response as a JSON body plus an `X-Payment-Required`
/// header, so a machine client reads the requirement, tops up, and re-POSTs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TopupHint {
    /// The payment scheme identifier (`site-host-lease-topup`).
    pub scheme: String,
    /// Why funding was refused.
    pub reason: TopupReason,
    /// The lease cell to top up (hex), when a lease exists for the owner.
    pub lease: Option<String>,
    /// The rent asset the top-up is denominated in (hex), when known.
    pub asset: Option<String>,
    /// A suggested top-up amount (>= one rent period) in the rent asset.
    pub amount: u64,
    /// Where a client funds the lease (a hint the host advertises).
    pub topup_endpoint: String,
    /// The publish endpoint to retry once funded.
    pub retry: String,
    /// A human-readable explanation.
    pub detail: String,
}

impl TopupHint {
    /// The scheme identifier used by this crate's topup hints.
    pub const SCHEME: &'static str = "site-host-lease-topup";
}

/// The funding gate's decision for a publish.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FundingDecision {
    /// A resident, non-lapsed lease covers the publish — admit it.
    Covered,
    /// Refused; carries the x402 topup hint the `402` returns.
    Denied(TopupHint),
}

/// The funding gate a [`crate::publish::SitePublishHandler`] consults: given the
/// authenticated owner subject and the publish-time clock, decide (and CHARGE for)
/// whether a publish is funded.
///
/// The `retry` and `topup_endpoint` are passed in by the handler (it knows the
/// concrete request path + the host's funding endpoint) so an implementation stays
/// decoupled from routing.
pub trait PublishFunding: Send + Sync {
    /// Decide whether `owner`'s publish is funded at `now`, DEBITING the allowance on
    /// admission. `now` drives the lease lapse check; `retry` is the publish path to
    /// echo into a topup hint; `topup_endpoint` is where the client funds a lease.
    fn authorize_publish(
        &self,
        owner: &str,
        now: u64,
        retry: &str,
        topup_endpoint: &str,
    ) -> FundingDecision;
}

/// One owner's funded account: their hosting lease plus the publish allowance the
/// lease funds and how much of it has been consumed.
struct LeaseAccount {
    lease: HostedLease,
    /// Total publish allowance (in publish-units) this lease grants.
    budget: u64,
    /// Publish-units consumed by admitted publishes so far.
    consumed: u64,
}

/// The resident lease-backed funding gate: a book of hosting leases keyed by owner
/// subject, each a real [`hosted_lease::HostedLease`] with a bounded publish
/// allowance. A publish is covered iff the owner has a lease that is not lapsed (at
/// the publish clock) AND has allowance remaining; admission DEBITS the allowance.
#[derive(Default)]
pub struct LeaseBook {
    accounts: Mutex<BTreeMap<String, LeaseAccount>>,
}

impl LeaseBook {
    /// An empty book (every owner is unfunded until a lease is bound).
    pub fn new() -> LeaseBook {
        LeaseBook::default()
    }

    /// Bind `owner`'s hosting lease into the book with an allowance derived from the
    /// lease's rent (one period of rent funds one period's worth of publishes).
    pub fn bind(&self, owner: impl Into<String>, lease: HostedLease) {
        let budget = lease.terms().rent_per_period.max(PUBLISH_TOPUP_UNITS);
        self.bind_with_budget(owner, lease, budget);
    }

    /// Bind `owner`'s lease with an explicit publish allowance (in publish-units).
    pub fn bind_with_budget(&self, owner: impl Into<String>, lease: HostedLease, budget: u64) {
        lock_recover(&self.accounts).insert(
            owner.into(),
            LeaseAccount {
                lease,
                budget: budget.max(PUBLISH_TOPUP_UNITS),
                consumed: 0,
            },
        );
    }

    /// Extend `owner`'s publish allowance by `units` (what a successful top-up does —
    /// the x402 loop's other half). No-op for an unbound owner.
    pub fn credit(&self, owner: &str, units: u64) {
        if let Some(acct) = lock_recover(&self.accounts).get_mut(owner) {
            acct.budget = acct.budget.saturating_add(units);
        }
    }

    /// Whether `owner` has a bound lease (lapsed or not).
    pub fn has_lease(&self, owner: &str) -> bool {
        lock_recover(&self.accounts).contains_key(owner)
    }

    /// The remaining publish allowance for `owner` (`0` if unbound).
    pub fn remaining(&self, owner: &str) -> u64 {
        lock_recover(&self.accounts)
            .get(owner)
            .map(|a| a.budget.saturating_sub(a.consumed))
            .unwrap_or(0)
    }

    /// Whether `owner`'s bound lease has lapsed (`false` if no lease / not lapsed).
    /// Read-only (does not run the clock).
    pub fn is_lapsed(&self, owner: &str) -> bool {
        lock_recover(&self.accounts)
            .get(owner)
            .map(|a| a.lease.is_lapsed())
            .unwrap_or(false)
    }

    fn deny(
        reason: TopupReason,
        lease: Option<&HostedLease>,
        amount: u64,
        retry: &str,
        topup: &str,
        detail: String,
    ) -> FundingDecision {
        let (lease_hex, asset_hex) = match lease {
            Some(l) => {
                let t = l.terms();
                (
                    Some(hex32(t.lease.as_bytes())),
                    Some(hex32(t.asset.as_bytes())),
                )
            }
            None => (None, None),
        };
        FundingDecision::Denied(TopupHint {
            scheme: TopupHint::SCHEME.to_string(),
            reason,
            lease: lease_hex,
            asset: asset_hex,
            amount,
            topup_endpoint: topup.to_string(),
            retry: retry.to_string(),
            detail,
        })
    }
}

impl PublishFunding for LeaseBook {
    fn authorize_publish(
        &self,
        owner: &str,
        now: u64,
        retry: &str,
        topup_endpoint: &str,
    ) -> FundingDecision {
        let mut book = lock_recover(&self.accounts);
        let Some(acct) = book.get_mut(owner) else {
            return LeaseBook::deny(
                TopupReason::Unfunded,
                None,
                PUBLISH_TOPUP_UNITS,
                retry,
                topup_endpoint,
                format!("no hosting lease covers `{owner}`: open and fund one, then retry"),
            );
        };

        // (1) Clock-driven lapse: run the lease's own lapse check at the publish
        //     clock, so a lease behind on rent is lapsed BEFORE it is trusted — never
        //     "Covered" on stale cached state.
        let _ = acct.lease.lapse_if_behind(now as i64);
        if acct.lease.is_lapsed() {
            let rent = acct.lease.terms().rent_per_period.max(PUBLISH_TOPUP_UNITS);
            return LeaseBook::deny(
                TopupReason::Lapsed,
                Some(&acct.lease),
                rent,
                retry,
                topup_endpoint,
                format!(
                    "the hosting lease for `{owner}` has lapsed (rent unpaid): top up ~{rent} and retry"
                ),
            );
        }

        // (2) Meter the accept path: a covered publish DEBITS the allowance. When it
        //     is spent, fail closed — no free unlimited publishing.
        if acct.consumed.saturating_add(PUBLISH_TOPUP_UNITS) > acct.budget {
            let rent = acct.lease.terms().rent_per_period.max(PUBLISH_TOPUP_UNITS);
            return LeaseBook::deny(
                TopupReason::Exhausted,
                Some(&acct.lease),
                rent,
                retry,
                topup_endpoint,
                format!(
                    "the publish allowance for `{owner}` is spent ({}/{}): top up ~{rent} and retry",
                    acct.consumed, acct.budget
                ),
            );
        }
        acct.consumed = acct.consumed.saturating_add(PUBLISH_TOPUP_UNITS);
        FundingDecision::Covered
    }
}

/// Lower-hex a 32-byte id.
fn hex32(b: &[u8; 32]) -> String {
    use std::fmt::Write as _;
    let mut s = String::with_capacity(64);
    for x in b {
        let _ = write!(s, "{x:02x}");
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::Cell;
    use dregg_types::CellId;
    use hosted_lease::{LeaseTerms, field_from_u64};

    const NOW: u64 = 1_000;

    fn cid(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }

    fn lease_cell() -> Cell {
        Cell::with_balance([7u8; 32], [9u8; 32], 10_000)
    }

    // provider=2, lease=7, asset=9; rent 100 every 50 blocks from block 1000.
    fn terms() -> LeaseTerms {
        LeaseTerms::new(cid(2), cid(7), cid(9), 100, 50, 1000, 0)
    }

    /// A lease that is rent-current at block 1000: period 0 metered (paid), so a
    /// clock-driven lapse check at 1000 leaves it live.
    fn current_lease() -> HostedLease {
        let mut lease = HostedLease::open(lease_cell(), terms(), field_from_u64(0)).unwrap();
        lease.meter(0, 1000).unwrap();
        lease
    }

    #[test]
    fn a_bound_current_lease_covers_and_charges_the_publish() {
        let book = LeaseBook::new();
        book.bind("agent:alice", current_lease());
        assert_eq!(book.remaining("agent:alice"), 100, "rent-derived allowance");
        assert_eq!(
            book.authorize_publish("agent:alice", NOW, "/v1/sites/blog/publish", "/v1/fund"),
            FundingDecision::Covered
        );
        // The accept path DEBITED the allowance (the fix: it used to be free).
        assert_eq!(book.remaining("agent:alice"), 99, "publish was charged");
    }

    #[test]
    fn allowance_exhausts_and_fails_closed() {
        let book = LeaseBook::new();
        book.bind_with_budget("agent:alice", current_lease(), 2);
        assert!(matches!(
            book.authorize_publish("agent:alice", NOW, "/r", "/f"),
            FundingDecision::Covered
        ));
        assert!(matches!(
            book.authorize_publish("agent:alice", NOW, "/r", "/f"),
            FundingDecision::Covered
        ));
        // Third publish: allowance spent -> 402 Exhausted.
        match book.authorize_publish("agent:alice", NOW, "/r", "/f") {
            FundingDecision::Denied(h) => assert_eq!(h.reason, TopupReason::Exhausted),
            other => panic!("expected Exhausted, got {other:?}"),
        }
        // A top-up extends the allowance and the loop heals.
        book.credit("agent:alice", 5);
        assert!(matches!(
            book.authorize_publish("agent:alice", NOW, "/r", "/f"),
            FundingDecision::Covered
        ));
    }

    #[test]
    fn an_unfunded_owner_gets_an_unfunded_topup_hint() {
        let book = LeaseBook::new();
        let d = book.authorize_publish("agent:nobody", NOW, "/v1/sites/blog/publish", "/v1/fund");
        match d {
            FundingDecision::Denied(hint) => {
                assert_eq!(hint.reason, TopupReason::Unfunded);
                assert!(hint.lease.is_none());
                assert_eq!(hint.retry, "/v1/sites/blog/publish");
                assert_eq!(hint.topup_endpoint, "/v1/fund");
                assert_eq!(hint.scheme, TopupHint::SCHEME);
            }
            other => panic!("expected Denied, got {other:?}"),
        }
    }

    #[test]
    fn a_lapsed_lease_gets_a_lapsed_topup_hint_naming_the_lease() {
        let book = LeaseBook::new();
        let mut lease = HostedLease::open(lease_cell(), terms(), field_from_u64(0)).unwrap();
        // Run the clock past the next due block with no payment -> lapse.
        assert!(lease.lapse_if_behind(1100).unwrap());
        assert!(lease.is_lapsed());
        book.bind("agent:alice", lease);

        let d = book.authorize_publish("agent:alice", 1100, "/v1/sites/blog/publish", "/v1/fund");
        match d {
            FundingDecision::Denied(hint) => {
                assert_eq!(hint.reason, TopupReason::Lapsed);
                assert_eq!(hint.lease.as_deref(), Some(&*hex32(&[7u8; 32])));
                assert_eq!(hint.asset.as_deref(), Some(&*hex32(&[9u8; 32])));
                assert_eq!(hint.amount, 100, "the lease's own rent");
            }
            other => panic!("expected Denied, got {other:?}"),
        }
    }

    #[test]
    fn lapse_is_clock_driven_not_cached() {
        // A lease that is live at 1000 but goes behind by 1100: the gate lapses it at
        // the PUBLISH clock, without any external caller having run the meter.
        let book = LeaseBook::new();
        book.bind("agent:alice", current_lease());
        assert!(matches!(
            book.authorize_publish("agent:alice", 1000, "/r", "/f"),
            FundingDecision::Covered
        ));
        // Now publish at a clock where rent is overdue -> clock-driven lapse.
        match book.authorize_publish("agent:alice", 1200, "/r", "/f") {
            FundingDecision::Denied(h) => assert_eq!(h.reason, TopupReason::Lapsed),
            other => panic!("expected Lapsed by clock, got {other:?}"),
        }
    }
}
