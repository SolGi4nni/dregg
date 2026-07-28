//! The Descent -> proof-gated Dark Bazaar -> atomic asset cross, end to end.
//!
//! This is the playable Tier-1 privacy shape rather than a proof-only fixture:
//! a fair Descent drop enters the existing Bazaar session, a Plonky3
//! `HidingFriPcs` proof for the fixed `N=4,K=4` private book authorizes the real
//! executor SETTLE, and the original provenance-carrying asset crosses for the
//! verified price through `dreggnet-trade`'s both-present sealed escrow.
//!
//! Honest boundary: the proof hides bids from proof consumers, but
//! `prepare_private_clearing_zk` builds the witness in this process and therefore
//! sees them. The test pins the public order root as an authenticated-source
//! stand-in; it does not claim the auction cell's BLAKE3 seals open to that root.
//! Also, proof-gated auction resolution and the asset trade are two sequential
//! receipts. The asset/$DREGG crossing itself is atomic.

#![cfg(feature = "private-clearing")]

/// The verified settlement gate this binary installs before every test — see
/// `tests/support/mod.rs`. Without it `settle_ring_verified` refuses every award as
/// NEVER JUDGED, which is a host-wiring fact about this binary and not a market verdict.
mod support;

use dreggnet_market::private_clearing::{PrivateClearingError, PrivateClearingExpectation};
use dreggnet_market::{DarkBazaarOffering, DarkBazaarSession, TURN_BID, TURN_LIST};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};
use dreggnet_trade::{LegSpec, TradeWorld};
use dungeon_on_dregg::loot::{LootVault, roll_drop};
use procgen_dregg::CommittedSeed;
use starbridge_sealed_auction::Phase;

const SELLER: &str = "descent-player:alice";
const LOW_BIDDER: &str = "bazaar-bidder:bob";
const WINNER: &str = "bazaar-bidder:carol";

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

fn land(
    offering: &DarkBazaarOffering,
    session: &mut DarkBazaarSession,
    turn: &str,
    arg: i64,
    who: &str,
) {
    let out = offering.advance(session, Action::new(turn, turn, arg, true), actor(who));
    assert!(
        matches!(out, Outcome::Landed { .. }),
        "{turn} refused: {out:?}"
    );
}

fn assert_no_settlement_mutation(
    session: &DarkBazaarSession,
    world: &mut TradeWorld,
    asset: dreggnet_trade::AssetId,
    receipts_before: usize,
) {
    assert_eq!(session.market().receipts_len(), receipts_before);
    assert_eq!(session.market().phase(), Some(Phase::Commit));
    assert_eq!(session.market().onledger_phase(), Some(0));
    assert!(!session.is_settled());
    assert!(session.clearing().is_none());

    assert_eq!(world.current_holder_label(asset), Some(SELLER));
    assert_eq!(
        world.lineage_len(asset),
        1,
        "the loot has not entered escrow"
    );
    assert_eq!(world.dregg_balance(WINNER), 3);
    assert_eq!(world.dregg_balance(SELLER), 0);
}

#[test]
fn fair_descent_loot_moves_only_after_hiding_proof_authorizes_the_real_clear() {
    support::install_verified_settlement_gate();
    // The item begins as a real fair-drawn Descent note, bound to a committed run
    // seed and carrying a provenance chain that already verifies before market use.
    let run_seed = CommittedSeed::from_bytes([0xD4; 32]);
    let draw = roll_drop(&run_seed, "boss:the Lantern Eater", 0);
    let mut vault = LootVault::new();
    let loot = vault.claim(SELLER, &draw).expect("fair drop mints");
    assert!(
        vault
            .provenance(loot.asset_id)
            .expect("known Descent loot")
            .asset
            .verified
    );

    // Adopt the SAME asset world: this is the original note, not a market remint.
    let mut world = TradeWorld::with_assets(vault.into_assets());
    world.fund_dregg(SELLER, 0);
    world.fund_dregg(WINNER, 3);

    // Values deliberately fit today's fixed K=4 relation (prices 0..3). The
    // sealed-auction board is still the existing executor-backed game mechanic.
    let offering = DarkBazaarOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(0xD4_4B_A2))
        .expect("Dark Bazaar opens");
    land(&offering, &mut session, TURN_LIST, 1, SELLER);
    land(&offering, &mut session, TURN_BID, 2, LOW_BIDDER);
    land(&offering, &mut session, TURN_BID, 3, WINNER);
    let receipts_before = session.market().receipts_len();

    // A forged source root and a forged policy price are rejected by the public
    // joins through the settlement entry point, before proof verification or a
    // settlement turn. Each authorization is opaque and one-shot at this API.
    let wrong_root_authorization = session
        .prepare_private_clearing_zk()
        .expect("opaque proof for source-root refusal tooth");
    let mut wrong_root =
        PrivateClearingExpectation::from_statement(wrong_root_authorization.statement());
    wrong_root.order_root[0] ^= 1;
    let err = offering
        .settle_private_verified(&mut session, wrong_root_authorization, wrong_root)
        .expect_err("a forged source root cannot authorize settlement");
    assert!(matches!(err, PrivateClearingError::RootMismatch));
    assert_no_settlement_mutation(&session, &mut world, loot.asset_id, receipts_before);

    let wrong_price_authorization = session
        .prepare_private_clearing_zk()
        .expect("opaque proof for policy-price refusal tooth");
    let mut wrong_price =
        PrivateClearingExpectation::from_statement(wrong_price_authorization.statement());
    wrong_price.price = 2;
    let err = offering
        .settle_private_verified(&mut session, wrong_price_authorization, wrong_price)
        .expect_err("a forged policy price cannot authorize settlement");
    assert!(matches!(err, PrivateClearingError::PriceMismatch { .. }));
    assert_no_settlement_mutation(&session, &mut world, loot.asset_id, receipts_before);

    // A proof replayed under a forged session is rejected through the settlement
    // entry point itself, before any close/reveal/resolve turn is submitted.
    let forged_session_authorization = session
        .prepare_private_clearing_zk()
        .expect("second opaque proof for refusal tooth");
    let original_session_statement = forged_session_authorization.statement();
    let expected_session = PrivateClearingExpectation::from_statement(original_session_statement);
    let mut forged_session_statement = original_session_statement;
    forged_session_statement.session ^= 1;
    let err = offering
        .settle_private_verified(
            &mut session,
            forged_session_authorization.with_statement(forged_session_statement),
            expected_session,
        )
        .expect_err("a proof is not replayable across market sessions");
    assert!(matches!(err, PrivateClearingError::SessionMismatch { .. }));
    assert_no_settlement_mutation(&session, &mut world, loot.asset_id, receipts_before);

    // The proof object is opaque outside the proving crate, so forge its claimed
    // statement instead: make the independent root agree with a tampered proof
    // input. All cheap joins now pass and HidingFri verification itself refuses.
    let forged_proof = session
        .prepare_private_clearing_zk()
        .expect("third opaque proof for cryptographic refusal tooth");
    let mut forged_proof_statement = forged_proof.statement();
    forged_proof_statement.order_root[0] ^= 1;
    let forged_proof_expected = PrivateClearingExpectation::from_statement(forged_proof_statement);
    let err = offering
        .settle_private_verified(
            &mut session,
            forged_proof.with_statement(forged_proof_statement),
            forged_proof_expected,
        )
        .expect_err("tampering with a public input invalidates the opaque proof");
    assert!(matches!(err, PrivateClearingError::InvalidProof(_)));
    assert_no_settlement_mutation(&session, &mut world, loot.asset_id, receipts_before);

    // Only the valid proof can land the existing executor SETTLE. The receipt fixes
    // the same winner and price that the subsequent asset trade must consume.
    // A production registry would authenticate this root from its source
    // transcript; this demo pins it at the Tier-1 builder handoff.
    let authorization = session
        .prepare_private_clearing_zk()
        .expect("valid HidingFri N4K4 proof");
    let statement = authorization.statement();
    assert_eq!(statement.session, session.private_proof_session());
    assert_eq!((statement.p_star, statement.v_star), (3, 1));
    let expected = PrivateClearingExpectation::from_statement(statement);
    let private_receipt = offering
        .settle_private_verified(&mut session, authorization, expected)
        .expect("valid hiding proof authorizes real settlement");
    assert_eq!(private_receipt.winner, actor(WINNER));
    assert_eq!((private_receipt.price(), private_receipt.volume()), (3, 1));
    assert!(session.is_settled());
    assert_eq!(session.clearing().expect("real clear").price(), 3);
    assert!(session.clearing().expect("real clear").conserved());

    // The exact Descent note and the exact verified price now cross together via
    // sealed escrow. Both legs are consumed or neither crosses.
    let crossed = session
        .settle_winning_asset(&mut world, loot.asset_id)
        .expect("proof-selected winner atomically buys the original loot note");
    assert_eq!(crossed.asset, loot.asset_id);
    assert_eq!(crossed.seller, actor(SELLER));
    assert_eq!(crossed.winner, actor(WINNER));
    assert_eq!(crossed.price, 3);
    assert_eq!(crossed.settlement.a_gave, LegSpec::Asset(loot.asset_id));
    assert_eq!(crossed.settlement.b_gave, LegSpec::Dregg(3));
    assert!(crossed.provenance.verified);
    assert_eq!(world.current_holder_label(loot.asset_id), Some(WINNER));
    assert_eq!(world.lineage_len(loot.asset_id), 3); // mint -> escrow -> winner
    assert_eq!(world.dregg_balance(WINNER), 0);
    assert_eq!(world.dregg_balance(SELLER), 3);
}
