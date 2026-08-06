//! End-to-end exercise of the sealed-bid commit-reveal coordination, settling through the verified
//! executor. Mirrors the teeth proved in `metatheory/Dregg2/Intent/SealedAuction.lean`.

use super::*;

/// **Arm the verified executor every award settles through.**
///
/// `dregg-intent`'s `settle_ring_verified` has been FAIL-CLOSED since the twin-deletion sweep
/// (`e3f0e7b92`): with no `IntentVerifiedGate` registered it REFUSES the ring rather than letting
/// an unverified in-process Rust fold decide who won. `dregg-intent`'s OWN tests keep the
/// in-process transition authoritative via a `#[cfg(test)]` sibling — but that `cfg` is set only
/// when `dregg-intent` itself is the crate under test. Every CONSUMER (this crate included)
/// compiles the fail-closed path, so from here every award came back unjudged.
///
/// ⚑ **This file was measurably red at HEAD and one of its teeth was worse than red.** Measured
/// 2026-08-06 on hbox: `full_flow_top_bid_wins_and_settles` and `settled_award_conserves_value`
/// PANICKED on their `.unwrap()`, and `unfunded_winner_aborts_the_whole_award` — which asserts
/// `matches!(result, Err(AuctionError::SettlementRejected(_)))` — PASSED, because an absent gate
/// arrived inside that very variant. A refusal tooth satisfied by the executor never having looked
/// is a falsifier that has stopped falsifying: it would have stayed green through any change that
/// made the auction accept an award the winner cannot pay. Arming the gate and splitting
/// `AwardNeverJudged` off fix both halves — the two panics go green, and the tooth now demands an
/// actual verdict.
///
/// Not a skip: an install that does not DECIDE is a hard failure with its own reason. An auction
/// test over an auction that cannot close is worse than a red one.
fn arm_the_verified_executor() {
    install_verified_auction_gate().unwrap_or_else(|e| {
        panic!(
            "the verified auction gate did not install: {e}\n\
             An award ring settles through the linked verified Lean executor; without it every \
             award is refused and no auction can close. Seed a HEAD-matching \
             dregg-lean-ffi/libdregg_lean.a and rebuild."
        )
    });
}

const PAY: AssetId = [0u8; 32]; // the payment asset
const TOKEN: AssetId = {
    let mut a = [0u8; 32];
    a[0] = 1;
    a
}; // the task-token asset the slot delivers

// Three competing agents, a seller, and the award slot.
const AGENT_A: CellId = 10;
const AGENT_B: CellId = 11;
const AGENT_C: CellId = 12;
const SELLER: CellId = 1;
const SLOT: CellId = 2;

fn three_agent_auction() -> (Auction, Bid, Bid, Bid) {
    let bid_a = Bid::new(AGENT_A, 30, 7);
    let bid_b = Bid::new(AGENT_B, 50, 8); // the top bid
    let bid_c = Bid::new(AGENT_C, 40, 9);

    let mut auction = Auction::new(SELLER, SLOT, PAY, TOKEN);
    // COMMIT phase: each agent submits a sealed commitment (others see only the hash).
    auction.commit(bid_a.seal()).unwrap();
    auction.commit(bid_b.seal()).unwrap();
    auction.commit(bid_c.seal()).unwrap();
    (auction, bid_a, bid_b, bid_c)
}

/// A ledger where the top bidder B can pay, and the slot holds the task-token. Every cell that a
/// settlement leg touches (the winner, the seller, and the slot) is a live account — the verified
/// executor requires both endpoints of a transfer to be live.
fn demo_ledger() -> VerifiedLedger {
    fund_ledger(&[
        (AGENT_B, PAY, 100), // winner B can pay its 50 bid
        (SELLER, PAY, 0),    // seller is a live account (receives the payment)
        (SLOT, TOKEN, 100),  // the slot holds the task-token
        (AGENT_B, TOKEN, 0), // winner is a live account in the token column (receives the award)
    ])
}

#[test]
fn full_flow_top_bid_wins_and_settles() {
    arm_the_verified_executor();
    let (mut auction, bid_a, bid_b, bid_c) = three_agent_auction();

    // Reveals are rejected while still committing (no reveal before the commit phase closes).
    assert_eq!(auction.reveal(bid_b), Err(AuctionError::NotRevealPhase));

    // Close the commit phase, then everyone reveals.
    auction.seal_commit_phase();
    auction.reveal(bid_a).unwrap();
    auction.reveal(bid_b).unwrap();
    auction.reveal(bid_c).unwrap();

    // The top bid (B, 50) wins.
    assert_eq!(auction.winner(), Some(bid_b));

    // Settle through the VERIFIED executor.
    let ledger = demo_ledger();
    let (post, winner) = auction.settle(&ledger).unwrap();
    assert_eq!(winner, bid_b);
    assert_eq!(auction.phase, Phase::Settled);

    // Seller was paid 50; winner paid 50 (100 - 50) and received the task-token (50).
    assert_eq!(post.get(SELLER, &PAY), 50);
    assert_eq!(post.get(AGENT_B, &PAY), 50);
    assert_eq!(post.get(AGENT_B, &TOKEN), 50);
    assert_eq!(post.get(SLOT, &TOKEN), 50);
}

#[test]
fn settled_award_conserves_value() {
    arm_the_verified_executor();
    // `settle_conserves`: every asset's total supply is preserved across the award.
    let (mut auction, bid_a, bid_b, bid_c) = three_agent_auction();
    auction.seal_commit_phase();
    auction.reveal(bid_a).unwrap();
    auction.reveal(bid_b).unwrap();
    auction.reveal(bid_c).unwrap();

    let ledger = demo_ledger();
    let pay_before = ledger.total_asset(&PAY);
    let token_before = ledger.total_asset(&TOKEN);

    let (post, _) = auction.settle(&ledger).unwrap();
    assert_eq!(post.total_asset(&PAY), pay_before);
    assert_eq!(post.total_asset(&TOKEN), token_before);
}

#[test]
fn no_reveal_before_commit_phase_closes() {
    // `reveal_requires_reveal_phase`: while still committing, valid_reveal is false and reveal errors.
    let (mut auction, _a, bid_b, _c) = three_agent_auction();
    assert!(!auction.valid_reveal(&bid_b)); // still in commit phase
    assert_eq!(auction.reveal(bid_b), Err(AuctionError::NotRevealPhase));
}

#[test]
fn no_late_switching_changed_bid_is_rejected() {
    // `reveal_binds_committed` (anti-front-running): an agent that committed `bid_b` cannot later
    // reveal a DIFFERENT bid (e.g. having peeked at others and wanting to bid more) — the changed
    // bid hashes to a different seal that was never committed.
    let (mut auction, _a, bid_b, _c) = three_agent_auction();
    auction.seal_commit_phase();

    // B committed (B, 50, 8). It now tries to reveal (B, 70, 8) — a higher bid after peeking.
    let switched = Bid::new(AGENT_B, 70, 8);
    assert_ne!(switched.seal(), bid_b.seal());
    assert!(!auction.valid_reveal(&switched));
    assert_eq!(auction.reveal(switched), Err(AuctionError::NotCommitted));

    // The original committed bid still reveals fine.
    auction.reveal(bid_b).unwrap();
    assert!(auction.valid_reveal(&bid_b) || auction.winner() == Some(bid_b));
}

#[test]
fn impostor_cannot_claim_anothers_bid() {
    // The seal binds the bidder identity: an impostor copying B's value/nonce but with its own
    // cell id has a different seal, so it is not among the commitments.
    let (mut auction, _a, bid_b, _c) = three_agent_auction();
    auction.seal_commit_phase();

    let impostor = Bid::new(AGENT_A, 50, 8); // copies B's value+nonce, different bidder
    assert_ne!(impostor.seal(), bid_b.seal());
    assert_eq!(auction.reveal(impostor), Err(AuctionError::NotCommitted));
}

#[test]
fn non_committed_party_cannot_reveal_or_win() {
    // `uncommitted_cannot_open`/`uncommitted_cannot_win`: a party that never committed — even with a
    // huge bid — cannot reveal, so it can never win.
    let (mut auction, _a, _b, _c) = three_agent_auction();
    auction.seal_commit_phase();

    let outsider = Bid::new(13, 999, 1); // never committed
    assert!(!auction.valid_reveal(&outsider));
    assert_eq!(auction.reveal(outsider), Err(AuctionError::NotCommitted));

    // It is absent from the winner set entirely.
    assert_ne!(auction.winner(), Some(outsider));
}

#[test]
fn unfunded_winner_aborts_the_whole_award() {
    arm_the_verified_executor();
    // `settle_atomic`: if the winner cannot pay, the award aborts and the ledger is untouched.
    let (mut auction, bid_a, bid_b, bid_c) = three_agent_auction();
    auction.seal_commit_phase();
    auction.reveal(bid_a).unwrap();
    auction.reveal(bid_b).unwrap();
    auction.reveal(bid_c).unwrap();

    // A ledger where the winner B holds NOTHING in the payment asset (it cannot pay its 50 bid).
    let ledger = fund_ledger(&[(SLOT, TOKEN, 100)]); // B has no PAY balance, and is not even live
    let result = auction.settle(&ledger);
    // ⚠ NAME THE REASON. `SettlementRejected(_)` alone used to be satisfied by an absent gate —
    // the executor never looked, and this tooth reported that as a rejection of the award. Demand
    // the verified executor actually REJECTED leg 0, so the assertion cannot be met by an absence.
    assert!(
        matches!(
            result,
            Err(AuctionError::SettlementRejected(
                VerifiedSettleError::LegRejected { index: 0, .. }
            ))
        ),
        "the verified executor must REJECT the unpayable award leg, not merely be absent; got \
         {result:?}"
    );
    assert!(
        !matches!(result, Err(AuctionError::AwardNeverJudged { .. })),
        "an unpayable award is a VERDICT; reporting it as never-judged would send the operator \
         after a Lean archive that is not the problem"
    );
    // The auction did NOT transition to Settled (no half-award).
    assert_eq!(auction.phase, Phase::Reveal);
}

#[test]
fn cannot_settle_before_reveal_phase() {
    // Settlement only fires in the reveal phase (no settling while still committing).
    let (mut auction, _a, _b, _c) = three_agent_auction();
    let ledger = demo_ledger();
    assert_eq!(auction.settle(&ledger), Err(AuctionError::NotRevealPhase));
}

#[test]
fn no_winner_when_no_valid_reveals() {
    // Sealing the commit phase but collecting no reveals yields no winner.
    let (mut auction, _a, _b, _c) = three_agent_auction();
    auction.seal_commit_phase();
    let ledger = demo_ledger();
    assert_eq!(auction.settle(&ledger), Err(AuctionError::NoWinner));
}

#[test]
fn late_commit_after_phase_closes_is_rejected() {
    let (mut auction, _a, _b, _c) = three_agent_auction();
    auction.seal_commit_phase();
    let late = Bid::new(13, 5, 5);
    assert_eq!(
        auction.commit(late.seal()),
        Err(AuctionError::NotCommitPhase)
    );
}

#[test]
fn seal_is_deterministic_and_binds_all_fields() {
    let b = Bid::new(7, 42, 99);
    assert_eq!(b.seal(), b.seal()); // deterministic
    // Each field is bound: changing any one changes the seal.
    assert_ne!(b.seal(), Bid::new(8, 42, 99).seal());
    assert_ne!(b.seal(), Bid::new(7, 43, 99).seal());
    assert_ne!(b.seal(), Bid::new(7, 42, 100).seal());
    // Negative values are distinguished from their magnitude (the sign tag).
    assert_ne!(Bid::new(7, 42, 1).seal(), Bid::new(7, -42, 1).seal());
}

#[test]
fn source_bound_seal_refuses_substituted_source_or_order() {
    let bid = Bid::new(AGENT_A, 42, 99);
    let source = [0x31; 32];
    let other_source = [0x32; 32];
    let mut auction = Auction::new(SELLER, SLOT, PAY, TOKEN);
    auction.commit(bid.seal_with_source(&source)).unwrap();
    auction.seal_commit_phase();

    assert!(!auction.valid_source_bound_reveal(&bid, &other_source));
    assert_eq!(
        auction.reveal_source_bound(bid, &other_source),
        Err(AuctionError::NotCommitted)
    );
    assert_eq!(
        auction.reveal_source_bound(Bid::new(AGENT_A, 43, 99), &source),
        Err(AuctionError::NotCommitted)
    );
    auction.reveal_source_bound(bid, &source).unwrap();
    assert_eq!(auction.winner(), Some(bid));
}
