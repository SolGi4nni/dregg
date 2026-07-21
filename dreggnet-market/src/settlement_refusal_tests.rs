use super::*;

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

fn listed_one_bid(seed: u64) -> (DarkBazaarOffering, DarkBazaarSession) {
    let offering = DarkBazaarOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(seed))
        .expect("Dark Bazaar opens");
    assert!(
        offering
            .advance(
                &mut session,
                Action::new("list", TURN_LIST, 10, true),
                actor("seller"),
            )
            .landed()
    );
    assert!(
        offering
            .advance(
                &mut session,
                Action::new("bid", TURN_BID, 20, true),
                actor("bidder"),
            )
            .landed()
    );
    (offering, session)
}

fn settle(offering: &DarkBazaarOffering, session: &mut DarkBazaarSession) -> Outcome {
    offering.advance(
        session,
        Action::new("settle", TURN_SETTLE, 0, true),
        actor("seller"),
    )
}

fn assert_read_only_refusal(
    session: &DarkBazaarSession,
    receipts_before: usize,
    nonce_before: u64,
) {
    assert_eq!(session.market.phase(), Some(Phase::Commit));
    assert_eq!(session.market.onledger_phase(), Some(PHASE_COMMIT));
    assert_eq!(session.market.receipts_len(), receipts_before);
    assert_eq!(session.market.executor.agent_nonce(), nonce_before);
    assert!(session.market.clearing().is_none());
}

#[test]
fn altered_or_ghost_commitments_refuse_before_executor_submission() {
    for (seed, ghost) in [(0xB0A4_D001, false), (0xB0A4_D002, true)] {
        let (offering, mut session) = listed_one_bid(seed);
        let cell = session.market.auction_cell.expect("listed cell");
        let recorded_slot = session.market.bids[0].slot;
        let touched_slot = if ghost { commit_slot(1) } else { recorded_slot };
        let original = session
            .market
            .executor
            .cell_state(cell)
            .expect("live cell")
            .fields[touched_slot];
        session.market.executor.with_ledger_mut(|ledger| {
            ledger.get_mut(&cell).expect("live cell").state.fields[touched_slot] = [0xA5; 32];
        });
        let report = offering.verify(&session);
        assert!(
            !report.verified && report.detail.contains("commit board"),
            "the verifier must reject the spliced board too: {}",
            report.detail
        );
        let receipts_before = session.market.receipts_len();
        let nonce_before = session.market.executor.agent_nonce();

        let refused = settle(&offering, &mut session);
        assert!(
            matches!(&refused, Outcome::Refused(reason) if reason.contains("commit board")),
            "a mismatched sealed board must refuse before execution: {refused:?}"
        );
        assert_read_only_refusal(&session, receipts_before, nonce_before);

        session.market.executor.with_ledger_mut(|ledger| {
            ledger.get_mut(&cell).expect("live cell").state.fields[touched_slot] = original;
        });
        assert!(
            settle(&offering, &mut session).landed(),
            "repairing the exact board restores seller settlement"
        );
    }
}

#[test]
fn occupied_result_register_refuses_without_burning_the_executor_nonce() {
    let (offering, mut session) = listed_one_bid(0xB0A4_D003);
    let cell = session.market.auction_cell.expect("listed cell");
    session.market.executor.with_ledger_mut(|ledger| {
        ledger.get_mut(&cell).expect("live cell").state.fields[WINNER_SLOT] = field_from_u64(99);
    });
    let report = offering.verify(&session);
    assert!(
        !report.verified
            && report
                .detail
                .contains("occupied on-ledger result registers"),
        "the verifier must reject the stale result image too: {}",
        report.detail
    );
    let receipts_before = session.market.receipts_len();
    let nonce_before = session.market.executor.agent_nonce();

    let refused = settle(&offering, &mut session);
    assert!(
        matches!(&refused, Outcome::Refused(reason) if reason.contains("result registers")),
        "a stale/replayed result image must refuse before execution: {refused:?}"
    );
    assert_read_only_refusal(&session, receipts_before, nonce_before);
}

#[test]
fn spliced_onledger_seller_binding_refuses_before_executor_submission() {
    let (offering, mut session) = listed_one_bid(0xB0A4_D004);
    let cell = session.market.auction_cell.expect("listed cell");
    session.market.executor.with_ledger_mut(|ledger| {
        ledger.get_mut(&cell).expect("live cell").state.fields[SELLER_SLOT] = field_from_u64(99);
    });
    let report = offering.verify(&session);
    assert!(
        !report.verified && report.detail.contains("seller binding"),
        "the verifier must reject the spliced seller too: {}",
        report.detail
    );
    let receipts_before = session.market.receipts_len();
    let nonce_before = session.market.executor.agent_nonce();

    let refused = settle(&offering, &mut session);
    assert!(
        matches!(&refused, Outcome::Refused(reason) if reason.contains("seller binding")),
        "a spliced seller binding must refuse before execution: {refused:?}"
    );
    assert_read_only_refusal(&session, receipts_before, nonce_before);
}
