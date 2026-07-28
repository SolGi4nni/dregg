//! **THE CANARY for `tests/support/mod.rs`.** Delete the
//! `support::install_verified_settlement_gate()` call from this file — or from
//! `dreggnet_market`'s test harness generally — and this test goes red, naming the omission.
//!
//! The finding it exists to keep detected: `dreggnet-market` drove every SETTLE through
//! `dregg_intent::verified_settle::settle_ring_verified`, which is FAIL-CLOSED without a registered
//! `IntentVerifiedGate`, and **no test binary in this crate ever registered one**. Measured at HEAD
//! on 2026-07-28: 23 of 52 red, 22 of them this. The refusal text says so in as many words
//! ("WIRING BUG in this host … the award was NEVER JUDGED — it was not rejected"), and it went
//! unread for three days because the reds were on a standing "known pre-existing, not yours" list.
//!
//! # Both poles, in one process, and only one thing between them
//!
//! `register_intent_verified_gate` is a process-wide `OnceLock`: once installed it cannot be
//! removed. So the two poles are ordered rather than parameterised, and that ordering is what makes
//! this a real tooth instead of a green that could be true for free —
//!
//!   * BEFORE the install, an award that is conserved, above reserve, and correctly sealed is
//!     REFUSED, and the refusal cites the absent gate. If that refusal ever stops happening, the
//!     gate is being installed by something else and this file should say who.
//!   * AFTER the install — the ONLY thing that changed — the identical award CLEARS to the top
//!     sealed bid, conservation-checked.
//!
//! A permissive stand-in gate would satisfy the second half and is exactly what this must not be:
//! `install_verified_settlement_gate` installs `dregg-exec-lean`'s Lean-backed implementation over
//! the linked archive, and refuses to run at all (`dregg_lean_ffi::demand_lean`) when the archive
//! does not export it.

mod support;

use dreggnet_market::{MarketOffering, TURN_BID, TURN_LIST, TURN_SETTLE};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};

fn seller() -> DreggIdentity {
    DreggIdentity("seller-alice".to_string())
}

/// Drive list → three sealed bids on a fresh market, leaving it one SETTLE from clearing.
fn listed_with_bids(off: &MarketOffering, seed: u64) -> dreggnet_market::MarketSession {
    let mut s = off
        .open(SessionConfig::with_seed(seed))
        .expect("market opens");
    assert!(
        off.advance(&mut s, Action::new("list", TURN_LIST, 25, true), seller())
            .landed(),
        "LIST is a real factory birth turn and does not touch the ring"
    );
    for (who, value) in [("alice", 30), ("bob", 50), ("carol", 40)] {
        let bidder = DreggIdentity(format!("bidder-{who}"));
        assert!(
            off.advance(&mut s, Action::new("bid", TURN_BID, value, true), bidder)
                .landed(),
            "a sealed BID is a WriteOnce commit turn and does not touch the ring"
        );
    }
    s
}

fn settle(off: &MarketOffering, s: &mut dreggnet_market::MarketSession) -> Outcome {
    off.advance(s, Action::new("settle", TURN_SETTLE, 0, true), seller())
}

#[test]
fn the_settlement_gate_is_what_decides_an_award_and_this_harness_installs_it() {
    let off = MarketOffering::new();

    // POLE 1 — no gate registered yet. An honest, conserved, above-reserve award is REFUSED, and
    // the refusal names the missing host wiring rather than blaming the auction.
    let mut ungated = listed_with_bids(&off, 0xCA9A_121);
    let refused = settle(&off, &mut ungated);
    let Outcome::Refused(reason) = &refused else {
        panic!(
            "with NO verified gate registered the award must be refused, not judged — got \
             {refused:?}. If something else in this binary's graph now installs the gate, say what \
             and delete this pole; do not leave a tooth that cannot bite."
        )
    };
    assert!(
        reason.contains("no verified executor gate is installed")
            && reason.contains("NEVER JUDGED"),
        "the gate-absent refusal must say the award was never judged, not that it was rejected: \
         {reason}"
    );
    assert!(
        ungated.clearing().is_none(),
        "an award nothing judged must not have cleared"
    );

    // THE ONLY THING THAT CHANGES between the poles.
    assert!(
        support::install_verified_settlement_gate(),
        "the linked archive must export the verified settlement gate"
    );

    // POLE 2 — the identical award now CLEARS, decided by the Lean export.
    let mut gated = listed_with_bids(&off, 0xCA9A_121);
    let out = settle(&off, &mut gated);
    let Outcome::Landed { receipt, .. } = out else {
        panic!("with the verified gate installed the award must clear, got {out:?}")
    };
    assert_ne!(
        receipt.turn_hash, [0u8; 32],
        "the clearing SETTLE is a real verified turn"
    );
    let c = gated.clearing().expect("the auction cleared");
    assert_eq!(c.winner.value, 50, "cleared to the TOP sealed bid");
    assert!(
        c.conserved(),
        "the value move conserves every asset (Σδ = 0)"
    );
}
