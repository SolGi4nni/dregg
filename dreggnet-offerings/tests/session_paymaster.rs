//! **DRIVEN: the session-key paymaster over the REAL run-credit ledger.**
//!
//! The pure session-key teeth (scope / deadline / non-amplification / no-re-sign) are driven in
//! `session.rs`'s unit tests over the [`FreePaymaster`]. THIS test drives the PAYMASTER binding
//! against the real [`dregg_pay::CreditLedger`]: a paid move is a genuine `CreditLedger::debit`,
//! the holder's balance really falls, and an out-of-credit move commits NOTHING (anti-ghost) —
//! then, funded again, the SAME move commits (non-vacuous). This is the "gasless from the
//! player's view" story made real: the player never signs or funds a per-move transaction; a
//! pre-funded credit balance covers each move.

use dregg_pay::config::{Asset, DepositAddress, UserId};
use dregg_pay::watcher::{PaymentReceived, PaymentRef};
use dregg_pay::{CreditLedger, InMemoryStore};

use dreggnet_offerings::dungeon::{DungeonOffering, TURN_CHOOSE};
use dreggnet_offerings::session::{
    CreditPaymaster, Paymaster, PlayGrant, PlayOutcome, PlayScope, open_session,
};
use dreggnet_offerings::{Action, DreggIdentity, Offering, SessionConfig};
use dungeon_on_dregg::{KP_CLAIM_RED, KP_DESCEND, KP_PRESS_ON, KP_SEIZE};

/// A `$DREGG` payment attributed to `user` for `amount` atomic units, keyed idempotently.
fn payment(user: &str, amount: u64, reference: &str) -> PaymentReceived {
    PaymentReceived {
        user: UserId::from(user),
        deposit_address: DepositAddress([0u8; 32]),
        asset: Asset::Dregg,
        amount,
        reference: PaymentRef(reference.to_string()),
    }
}

fn choose(arg: usize) -> Action {
    Action::new("move", TURN_CHOOSE, arg as i64, true)
}

/// THE PAYMASTER DRAWS THE RUN COST FROM CREDITS — a real ledger move, non-vacuously.
///
/// A paid-tier dungeon (1 credit/move) played under a session key over a real `CreditLedger`:
/// each committed move DEBITS one credit (balance falls 3→2→1→0); the fourth (otherwise-legal)
/// move is UNPAID at balance 0 and commits nothing; funding one more credit lets that SAME move
/// commit — the credit was the only thing gating it.
#[test]
fn the_paymaster_draws_the_run_cost_from_the_real_credit_ledger() {
    // price_per_run = 1 atomic unit → 1 credit per unit; fund the holder with 3 credits.
    let ledger = CreditLedger::new(InMemoryStore::new(), 1);
    let holder = DreggIdentity("player-alice-key".to_string());
    let user = UserId::from(holder.as_str());
    ledger.credit(&payment(holder.as_str(), 3, "dregg-tx-1"));
    assert_eq!(ledger.balance(&user), 3, "funded 3 run-credits");

    // A PAID dungeon: each move draws 1 credit for the (confined-narration) run cost.
    let off = DungeonOffering::paid(1);
    let mut s = off.open(SessionConfig::with_seed(3)).expect("open");

    // A session key scoped to the dungeon, and the real credit paymaster over the ledger.
    let root = PlayGrant::root(PlayScope::Any, 1_000_000, 100);
    let mut key = open_session(
        &root,
        holder.clone(),
        PlayScope::of_offering("dungeon"),
        1_000_000,
        10,
    )
    .expect("a narrowing delegation");
    let paymaster = CreditPaymaster::new(&ledger);
    let dungeon = PlayScope::of_offering("dungeon").offering_id().unwrap();

    // Three committed moves, each a real debit: balance 3 → 2 → 1 → 0.
    for (i, (arg, expect_left)) in [(KP_PRESS_ON, 2u64), (KP_CLAIM_RED, 1), (KP_DESCEND, 0)]
        .into_iter()
        .enumerate()
    {
        let out = key.play(dungeon, &off, &mut s, choose(arg), 1, &paymaster);
        match out {
            PlayOutcome::Committed {
                charged,
                credits_left,
                ..
            } => {
                assert_eq!(charged.credits, 1, "move {i} charged one credit");
                assert_eq!(credits_left, expect_left, "move {i} left {expect_left}");
                assert_eq!(
                    ledger.balance(&user),
                    expect_left,
                    "move {i}: the REAL ledger balance fell"
                );
            }
            other => panic!("move {i} should commit + debit, got {other:?}"),
        }
    }
    assert_eq!(key.turns_taken(), 3, "three metered committed turns");

    // The FOURTH move (seize the hoard) is otherwise legal, but the balance is 0 → UNPAID, and
    // NOTHING commits (anti-ghost): no debit, no substrate turn, no counter advance.
    let out = key.play(dungeon, &off, &mut s, choose(KP_SEIZE), 1, &paymaster);
    assert!(
        matches!(out, PlayOutcome::Unpaid(_)),
        "out-of-credit move is unpaid: {out:?}"
    );
    assert_eq!(ledger.balance(&user), 0, "no debit on an unpaid move");
    assert_eq!(
        key.turns_taken(),
        3,
        "an unpaid move consumes no turn budget"
    );
    assert!(
        !s.is_ended(),
        "the unpaid seize did not commit — dungeon not ended"
    );

    // NON-VACUOUS: fund one more credit and the SAME move commits — credit was the only gate.
    ledger.credit(&payment(holder.as_str(), 1, "dregg-tx-2"));
    assert_eq!(ledger.balance(&user), 1, "topped up to 1 credit");
    let out = key.play(dungeon, &off, &mut s, choose(KP_SEIZE), 1, &paymaster);
    assert!(
        out.committed(),
        "with credit, the same move commits: {out:?}"
    );
    assert_eq!(
        ledger.balance(&user),
        0,
        "the top-up credit was really debited"
    );
    assert_eq!(key.turns_taken(), 4);
    assert!(s.is_ended(), "the hoard is seized — the run cleared");
    assert!(off.verify(&s).verified, "the committed chain re-verifies");
}

/// THE FREE TIER draws nothing: a free-tier dungeon (0 credits/move) commits under a session key
/// with a zero-balance credit ledger — the paymaster never debits, play is free.
#[test]
fn the_free_tier_never_debits() {
    let ledger = CreditLedger::new(InMemoryStore::new(), 1);
    let holder = DreggIdentity("player-free-key".to_string());
    let user = UserId::from(holder.as_str());
    assert_eq!(ledger.balance(&user), 0, "no credits funded");

    let off = DungeonOffering::new(); // free tier (0 credits/move)
    let mut s = off.open(SessionConfig::with_seed(3)).expect("open");
    let root = PlayGrant::root(PlayScope::Any, 1_000_000, 100);
    let mut key = open_session(
        &root,
        holder.clone(),
        PlayScope::of_offering("dungeon"),
        1_000_000,
        10,
    )
    .expect("delegation");
    let paymaster = CreditPaymaster::new(&ledger);
    let dungeon = PlayScope::of_offering("dungeon").offering_id().unwrap();

    // A free move commits with a zero balance and never debits.
    let out = key.play(dungeon, &off, &mut s, choose(KP_PRESS_ON), 1, &paymaster);
    assert!(
        out.committed(),
        "a free-tier move commits with no credits: {out:?}"
    );
    assert_eq!(ledger.balance(&user), 0, "the free tier never debited");
    // The paymaster can always cover a free move.
    assert!(paymaster.can_cover(&holder, dreggnet_offerings::RunCost::free()));
}
