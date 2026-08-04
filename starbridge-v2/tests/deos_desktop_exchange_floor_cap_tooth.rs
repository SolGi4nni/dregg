//! **THE EXCHANGE FLOOR'S CAP TOOTH CAN REFUSE A TAKER.**
//!
//! `ExchangeFloorState::take` commits the compute-exchange `bid` turn against
//! `job::PROVIDER_RIGHTS` (`Requirement::AtLeast(Either)`). Until this test it passed
//! `AuthRequired::None` — the lattice **TOP**, which clears every requirement including
//! `Root` — as the HELD authority. So the requirement was satisfied by construction:
//! the tooth had the right shape, read the right constant, and **could not refuse
//! anybody**. `d94018efe` made exactly this split for the twenty registry world-drives;
//! the floor's `bid` site was not one of them and kept the top.
//!
//! ⚑ **WHY THIS FILE EXISTS INSTEAD OF A UNIT TEST IN `exchange_floor.rs`.**
//! `deos_desktop` is `#[cfg(all(feature = "gpui-ui", feature = "embedded-executor"))]`,
//! and NO workflow runs `cargo test -p starbridge-v2 --lib` with those features on —
//! `armed-teeth.yml`'s desktop job names integration targets by `--test`, and every
//! other starbridge-v2 test invocation is on the default (gpui-free) feature set, where
//! the whole module is `cfg`'d out and its `#[cfg(test)] mod tests` never compiles. A
//! cap-tooth gate written there would be a guard that cannot fire, which is
//! indistinguishable from one that always passes. This target is armed in
//! `.github/workflows/armed-teeth.yml`.
//!
//! Run: `cd starbridge-v2 && cargo test --features native-full \
//!   --test deos_desktop_exchange_floor_cap_tooth -- --nocapture`

#![cfg(all(feature = "gpui-ui", feature = "embedded-executor"))]

use std::cell::RefCell;
use std::rc::Rc;

use starbridge_v2::app_registry::{HELD_BY_AN_OBSERVER, HELD_BY_A_PARTICIPANT};
use starbridge_v2::deos_desktop::exchange_floor::{
    fair_price, ExchangeFloorState, OfferPhase, FLOOR_PROVIDER, FLOOR_REQUESTER,
};
use starbridge_v2::world::World;

/// A floor with one posted offer at `budget`, on a fresh live `World`.
fn posted_offer(budget: u64) -> (Rc<RefCell<World>>, ExchangeFloorState, dregg_types::CellId) {
    let world = Rc::new(RefCell::new(World::new()));
    let mut floor = ExchangeFloorState::new();
    let (cell, _) = floor
        .post_offer(Rc::clone(&world), FLOOR_REQUESTER, budget)
        .expect("the post turn commits");
    (world, floor, cell)
}

/// ⚑ **AN UNDER-AUTHORIZED TAKER IS REFUSED, AND NOTHING COMMITS.**
///
/// The price is HONEST — inside the budget — so the BUDGET tooth
/// (`FieldLteField(BID <= BUDGET)`) cannot explain this refusal and the lifecycle tooth
/// (`StrictMonotonic(STATE)`) cannot either: the offer is freshly POSTED. Only the cap
/// tooth is left. `Signature` does not clear `AtLeast(Either)` — the authority lattice
/// is an order (`Signature ⊏ Either`), not a rank that rounds up.
///
/// Three things are asserted, because "it returned Err" is the weakest of them:
///   1. the refusal is the CAP tooth's, named on the face of the message;
///   2. it is IN-BAND — the turn was never BUILT, so `World::receipts()` does not grow
///      (a refusal that leaves a receipt is a ghost turn);
///   3. the offer is untouched: still POSTED, still takeable by someone who qualifies.
#[test]
fn an_under_authorized_take_is_refused_by_the_cap_tooth_and_commits_nothing() {
    let (world, floor, cell) = posted_offer(1_000);
    let receipts = world.borrow().receipts().len();

    let reason = floor
        .take(
            &cell,
            &HELD_BY_AN_OBSERVER,
            FLOOR_PROVIDER,
            fair_price(1_000),
        )
        .expect_err(
            "a signature-only holder cleared `AtLeast(Either)` at an honest price — the \
             cap tooth is not reading `held`",
        );
    // The surfaced string is the executor's own, and it names the tooth, the METHOD, the
    // requirement and the held authority:
    //   "…refused by the cap-gate: affordance fire refused by gate: unauthorized:
    //    firing `bid` requires AtLeast(Either) but holder has Signature"
    assert!(
        reason.contains("unauthorized"),
        "the refusal is the CAP tooth, not the budget or lifecycle tooth: {reason}"
    );
    assert!(
        reason.contains("AtLeast(Either)") && reason.contains("Signature"),
        "the refusal names what was REQUIRED and what was HELD, so it is diagnosable: {reason}"
    );
    assert!(
        reason.contains("bid"),
        "the refusal names the METHOD it refused, so it is attributable to this site: {reason}"
    );
    assert_eq!(
        world.borrow().receipts().len(),
        receipts,
        "a cap refusal is IN-BAND — no turn was built, so nothing landed on World"
    );
    assert_eq!(
        floor.rows()[0].phase,
        OfferPhase::Posted,
        "the refused take advanced the offer's lifecycle anyway"
    );

    // ANTI-VACUITY: the tooth refuses the OUTSIDER, not everybody. The SAME offer at the
    // SAME price, taken by the tier the desktop verbs actually hold, commits.
    floor
        .take(
            &cell,
            &HELD_BY_A_PARTICIPANT,
            FLOOR_PROVIDER,
            fair_price(1_000),
        )
        .expect("the participant-tier taker still commits — the tooth refuses EVERYONE");
    assert_eq!(floor.rows()[0].phase, OfferPhase::Leased);
    assert_eq!(world.borrow().receipts().len(), receipts + 1);
}

/// **MINIMALITY, not sufficiency.** Root clears everything, which is exactly how the
/// hole was written — so "the desktop verb's authority clears the requirement" proves
/// nothing on its own, and a site re-widened to the top would satisfy it. The property
/// is that the rung the desktop verbs hold is the NARROWEST one that takes: it must
/// take, and the rung BELOW it must be refused.
///
/// This is what fails if someone passes [`HELD_BY_A_ROOT_OPERATOR`] here "to make the
/// test green" — root takes, but so does the observer rung, and the second leg dies.
#[test]
fn the_participant_rung_is_the_narrowest_authority_that_takes() {
    let (_world, floor, cell) = posted_offer(1_000);

    // The rung BELOW the one the desktop verbs hold does not take...
    assert!(
        floor
            .take(
                &cell,
                &HELD_BY_AN_OBSERVER,
                FLOOR_PROVIDER,
                fair_price(1_000)
            )
            .is_err(),
        "the observer rung takes — `HELD_BY_A_PARTICIPANT` is not minimal here"
    );
    // ...and the rung they do hold is the one that takes.
    assert!(
        floor
            .take(
                &cell,
                &HELD_BY_A_PARTICIPANT,
                FLOOR_PROVIDER,
                fair_price(1_000)
            )
            .is_ok(),
        "the participant rung does not take — the desktop verbs hold too little"
    );
}
