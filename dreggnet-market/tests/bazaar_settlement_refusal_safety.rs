//! Bazaar settlement authorization and refusal atomicity.
//!
//! These are regression teeth for two griefing paths: a non-seller trying to
//! close another actor's auction, and a below-reserve clear closing COMMIT even
//! though the offering reports `Refused`.

/// The verified settlement gate this binary installs before every test — see
/// `tests/support/mod.rs`. Without it `settle_ring_verified` refuses every award as
/// NEVER JUDGED, which is a host-wiring fact about this binary and not a market verdict.
mod support;

use dreggnet_market::{DarkBazaarOffering, TURN_BID, TURN_LIST, TURN_SETTLE};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};
use starbridge_sealed_auction::Phase;

const SELLER: &str = "seller";

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

fn advance(
    offering: &DarkBazaarOffering,
    session: &mut dreggnet_market::DarkBazaarSession,
    turn: &str,
    arg: i64,
    who: &str,
) -> Outcome {
    offering.advance(session, Action::new(turn, turn, arg, true), actor(who))
}

fn assert_commit_state_is_unchanged(
    session: &dreggnet_market::DarkBazaarSession,
    receipts_before: usize,
) {
    assert_eq!(session.market().phase(), Some(Phase::Commit));
    assert_eq!(session.market().onledger_phase(), Some(0));
    assert_eq!(session.market().receipts_len(), receipts_before);
    assert!(!session.is_settled());
    assert!(session.clearing().is_none());
}

#[test]
fn a_non_seller_cannot_settle_or_close_someone_elses_bazaar() {
    support::install_verified_settlement_gate();
    let offering = DarkBazaarOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(0xA11CE))
        .expect("Bazaar opens");
    assert!(advance(&offering, &mut session, TURN_LIST, 25, SELLER).landed());
    assert!(advance(&offering, &mut session, TURN_BID, 50, "bidder").landed());
    let receipts_before = session.market().receipts_len();

    let refused = advance(&offering, &mut session, TURN_SETTLE, 0, "seller ");
    assert!(
        matches!(&refused, Outcome::Refused(reason) if reason.contains("listing seller")),
        "a non-seller SETTLE must be refused explicitly: {refused:?}"
    );
    assert_commit_state_is_unchanged(&session, receipts_before);

    let seller_settle = advance(&offering, &mut session, TURN_SETTLE, 0, SELLER);
    let Outcome::Landed { receipt, .. } = seller_settle else {
        panic!("the attack must not prevent the seller from settling later: {seller_settle:?}");
    };
    assert_eq!(
        receipt.action_count, 3,
        "close + one reveal + resolve commit as one atomic turn"
    );
    assert!(session.is_settled());

    let settled_receipts = session.market().receipts_len();
    let replay = advance(&offering, &mut session, TURN_SETTLE, 0, SELLER);
    assert!(
        matches!(&replay, Outcome::Refused(reason) if reason.contains("already settled")),
        "an exact seller replay must refuse: {replay:?}"
    );
    assert_eq!(session.market().phase(), Some(Phase::Settled));
    assert_eq!(session.market().onledger_phase(), Some(2));
    assert_eq!(session.market().receipts_len(), settled_receipts);
}

#[test]
fn below_reserve_refusal_keeps_commit_open_and_appends_no_receipts() {
    support::install_verified_settlement_gate();
    let offering = DarkBazaarOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(0xB310_0E5E))
        .expect("Bazaar opens");
    assert!(advance(&offering, &mut session, TURN_LIST, 100, SELLER).landed());
    assert!(advance(&offering, &mut session, TURN_BID, 60, "early").landed());
    let receipts_before = session.market().receipts_len();

    let refused = advance(&offering, &mut session, TURN_SETTLE, 0, SELLER);
    assert!(
        matches!(&refused, Outcome::Refused(reason) if reason.contains("below the reserve")),
        "a below-reserve SETTLE must refuse: {refused:?}"
    );
    assert_commit_state_is_unchanged(&session, receipts_before);

    assert!(
        advance(&offering, &mut session, TURN_BID, 120, "later").landed(),
        "a refused no-sale must not close the commit phase"
    );
    let seller_settle = advance(&offering, &mut session, TURN_SETTLE, 0, SELLER);
    let Outcome::Landed { receipt, .. } = seller_settle else {
        panic!("the later qualifying book must settle: {seller_settle:?}");
    };
    assert_eq!(
        receipt.action_count, 4,
        "close + two reveals + resolve commit as one atomic turn"
    );
    assert_eq!(session.clearing().expect("seller clears").price(), 120);
}
