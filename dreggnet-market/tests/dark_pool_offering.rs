//! The playable Dark Pool, driven the way a player drives it.
//!
//! Every assertion here is about what the CODE does. Where a tooth is structural rather than
//! cryptographic (an arity check, a bookkeeping counter) the test says so in its own words rather
//! than borrowing the word "cryptographic" from a doc comment.

use dreggnet_market::dark_pool_offering::{
    DARK_POOL_VENDOR_KEY, DarkPoolOffering, SEAT_FAUCET_DREGG, TURN_JOIN, TURN_PROPOSE, TURN_SWAP,
};
use dreggnet_offerings::{
    Action, Audience, DreggIdentity, Offering, OfferingHost, Outcome, SessionConfig, SessionId,
    project_for_audience,
};
use fhegg_fhe::threshold::DecryptShare;

fn player(name: &str) -> DreggIdentity {
    DreggIdentity(format!("player:{name}"))
}

fn surface_text(surface: &dreggnet_offerings::Surface) -> String {
    format!("{:?}", surface.view())
}

/// Fire an affordance and require it to land, naming the refusal when it does not.
fn must_land(
    offering: &DarkPoolOffering,
    session: &mut <DarkPoolOffering as Offering>::Session,
    action: Action,
    who: &DreggIdentity,
    what: &str,
) -> dregg_app_framework::TurnReceipt {
    match offering.advance(session, action, who.clone()) {
        Outcome::Landed { receipt, .. } => receipt,
        Outcome::Refused(why) => panic!("{what} must land, but the pool refused: {why}"),
    }
}

/// A player opens the pool, takes a seat, and swaps — and gets a REAL committed turn back plus a
/// relic they now own. The price is never chosen by this test: the pool's own exact quote is.
#[test]
fn a_player_takes_a_seat_and_swaps_for_a_real_receipt() {
    let offering = DarkPoolOffering::mount(0xDA2C, 2).expect("mount the pool");
    let mut session = offering.open(SessionConfig::with_seed(1)).expect("open");
    let who = player("mira");

    // Every affordance is offered to everyone: none of them is dimmed by the reserves, because
    // dimming on the book would paint the book.
    let actions = offering.actions(&session);
    assert_eq!(actions.len(), 3);
    assert!(actions.iter().all(|action| action.enabled));

    // Seat: a real committed journal turn.
    let receipt = must_land(
        &offering,
        &mut session,
        Action::new("", TURN_JOIN, 0, true),
        &who,
        "taking a seat",
    );
    assert_ne!(receipt.turn_hash, [0u8; 32]);
    assert_eq!(offering.purse_of(&who), SEAT_FAUCET_DREGG as i64);

    // A second seat is refused and leaves NOTHING behind (no second faucet credit).
    let again = offering.advance(
        &mut session,
        Action::new("", TURN_JOIN, 0, true),
        who.clone(),
    );
    assert!(matches!(again, Outcome::Refused(_)));
    assert_eq!(offering.purse_of(&who), SEAT_FAUCET_DREGG as i64);

    // The swap itself.
    let receipt = must_land(
        &offering,
        &mut session,
        Action::new("", TURN_SWAP, 1, true),
        &who,
        "a quoted swap",
    );
    assert_ne!(receipt.turn_hash, [0u8; 32]);

    let fills = offering.fills_for(&who);
    assert_eq!(fills.len(), 1, "the taker must hold exactly one fill");
    let fill = &fills[0];
    assert_eq!(fill.relics, 1);
    assert!(!fill.self_priced, "this fill took the pool's own quote");
    assert_eq!(
        offering.purse_of(&who),
        SEAT_FAUCET_DREGG as i64 - fill.price as i64,
        "the purse must be debited by exactly the quoted price"
    );
    assert_eq!(fill.turn_hash, receipt.turn_hash);

    // The public record grew by one viewer-blind card carrying no amount at all.
    let cards = offering.public_cards();
    assert_eq!(cards.len(), 1);
    assert_eq!(cards[0].sequence, 1);
    assert_eq!(
        cards[0].quorum_openings, 1,
        "one full-quorum opening decided this swap"
    );

    assert!(offering.verify(&session).verified);
}

/// THE FALSIFIER. A taker names their own price, well below what the invariant admits. No quoter
/// is consulted on this path: the ONLY thing that can refuse it is the homomorphic
/// constant-product check, opened under the full custodian quorum. It refuses, and NOTHING moves
/// — no purse debit, no relic, no journal turn, no public card.
#[test]
fn an_underpriced_self_priced_swap_is_refused_and_moves_nothing() {
    let offering = DarkPoolOffering::mount(0xBADF, 2).expect("mount the pool");
    let mut session = offering.open(SessionConfig::default()).expect("open");
    let who = player("skimmer");

    must_land(
        &offering,
        &mut session,
        Action::new("", TURN_JOIN, 0, true),
        &who,
        "taking a seat",
    );
    let purse_before = offering.purse_of(&who);
    let cards_before = offering.public_cards().len();

    // The genesis quote for one relic is 252 $DREGG. Offer 100.
    let skim = offering.advance(
        &mut session,
        Action::new("", TURN_PROPOSE, 100, true),
        who.clone(),
    );
    let Outcome::Refused(reason) = skim else {
        panic!("an underpriced proposal must be refused, got {skim:?}");
    };
    assert!(
        reason.contains("constant-product"),
        "the refusal must come from the invariant check, got: {reason}"
    );
    // The refusal names no number: a rejected candidate's opened product stays in the process.
    assert!(
        !reason.contains("27720"),
        "the refusal leaked the invariant value"
    );

    assert_eq!(
        offering.purse_of(&who),
        purse_before,
        "a refused swap debited the purse"
    );
    assert!(
        offering.fills_for(&who).is_empty(),
        "a refused swap left a fill"
    );
    assert_eq!(
        offering.public_cards().len(),
        cards_before,
        "a refused swap wrote a public card"
    );

    // Off by ONE is still refused: the invariant admits an exact post-swap product and nothing
    // near it.
    let nearly = offering.advance(
        &mut session,
        Action::new("", TURN_PROPOSE, 251, true),
        who.clone(),
    );
    assert!(matches!(nearly, Outcome::Refused(_)));
    assert!(offering.fills_for(&who).is_empty());

    // And the exact price the invariant DOES admit still lands, through the same self-priced
    // path — so the refusals above are the invariant biting, not the path being dead.
    let exact = offering.advance(
        &mut session,
        Action::new("", TURN_PROPOSE, 252, true),
        who.clone(),
    );
    assert!(
        matches!(exact, Outcome::Landed { .. }),
        "the exactly-priced self-priced swap must land, got {exact:?}"
    );
    let fills = offering.fills_for(&who);
    assert_eq!(fills.len(), 1);
    assert!(fills[0].self_priced);
    assert_eq!(fills[0].price, 252);
    assert!(offering.verify(&session).verified);
}

/// The audience boundary. `hidden_information` is declared `true`, the shared projection carries
/// no fill price and no reserve, and the private projection carries the viewer's own.
#[test]
fn the_shared_surface_never_carries_a_fill_price_or_a_reserve() {
    let offering = DarkPoolOffering::mount(0x5EED, 2).expect("mount the pool");
    let mut session = offering.open(SessionConfig::default()).expect("open");
    let who = player("quiet");
    assert!(offering.hidden_information());

    must_land(
        &offering,
        &mut session,
        Action::new("", TURN_JOIN, 0, true),
        &who,
        "taking a seat",
    );
    must_land(
        &offering,
        &mut session,
        Action::new("", TURN_SWAP, 1, true),
        &who,
        "a quoted swap",
    );
    let fill = offering.fills_for(&who).remove(0);

    let shared = project_for_audience(&offering, &session, &Audience::Shared);
    let shared_text = surface_text(&shared.surface);
    assert!(
        shared.hidden_information,
        "the shared projection must still carry the flag"
    );
    assert!(!shared.private);
    // Every amount this offering can render — a reserve, a price, a purse — is rendered with a
    // `$DREGG` suffix, and every fill line is rendered as `swap #n`. Neither may appear on the
    // shared card. (Asserting on the bare digits would be flaky: the public `k` and the key
    // fingerprint are digits too.)
    assert!(
        !shared_text.contains("$DREGG"),
        "the shared card carries an amount: {shared_text}"
    );
    assert!(
        !shared_text.contains("swap #"),
        "the shared card carries a fill line: {shared_text}"
    );
    // `Your purse:` is the private projection's own line. (The shared card DOES say the word
    // "purse" — in the sentence naming what it deliberately omits — so the check is on the
    // rendered line, not the word.)
    assert!(
        !shared_text.contains("Your purse"),
        "the shared card leaked a purse: {shared_text}"
    );
    // The public invariant IS on the shared card, deliberately and by construction.
    assert!(shared_text.contains(&format!("k={}", offering.public_invariant())));

    let private = project_for_audience(&offering, &session, &Audience::private(who.clone()));
    let private_text = surface_text(&private.surface);
    assert!(private.private);
    assert!(
        private_text.contains(&format!("relic for {} $DREGG", fill.price)),
        "the taker's own projection must show their fill price: {private_text}"
    );

    // A viewer who is not the taker sees no fill of their own.
    let stranger =
        project_for_audience(&offering, &session, &Audience::private(player("stranger")));
    let stranger_text = surface_text(&stranger.surface);
    assert!(stranger_text.contains("no seat"));
    assert!(
        !stranger_text.contains(&format!("relic for {} $DREGG", fill.price)),
        "a stranger saw another player's fill: {stranger_text}"
    );

    // Through the erased `OfferingHost` boundary too.
    let mut host = OfferingHost::new();
    host.register(DARK_POOL_VENDOR_KEY, "The Dark Pool", offering.clone());
    let id = SessionId::new("dark-pool-shared");
    host.open_session(DARK_POOL_VENDOR_KEY, id.clone(), SessionConfig::default())
        .expect("host open");
    let hosted = host
        .project(DARK_POOL_VENDOR_KEY, &id, &Audience::Shared)
        .expect("hosted shared projection");
    assert!(!surface_text(&hosted.surface).contains("$DREGG"));
}

/// NO SINGLE VIEWER, at two different strengths — and the test is explicit about which is which.
///
/// (a) an `n-1` share set is refused by [`combine`]'s ARITY check: that is a structural refusal,
///     not evidence about what `n-1` custodians could compute;
/// (b) an `n-1` coalition that FORGES the missing custodian's share (re-labelling one of their
///     own, which passes every structural check the combiner makes) does not recover the
///     plaintext. That is the cryptographic content: the reconstruction only cancels the key when
///     the real missing mask is present.
#[test]
fn a_short_or_forged_coalition_does_not_open_the_dark_invariant() {
    const N: usize = 3;
    let offering = DarkPoolOffering::mount(0xC0FF, N).expect("mount the pool");
    assert_eq!(offering.custodians(), N);

    // The invariant ciphertext of the pool's own fair candidate. An honest full quorum opens it
    // to the public k.
    let invariant = offering
        .candidate_invariant(252, 1)
        .expect("the genesis candidate");
    let k = offering.public_invariant();

    let (honest, short, forged) = offering
        .with_custody(|custody| {
            let shares = custody.shares(&invariant).expect("every custodian's share");
            assert_eq!(shares.len(), N);
            let honest = custody.combine_shares(&shares).expect("full quorum opens");

            // (a) arity: n-1 shares.
            let short = custody.combine_shares(&shares[..N - 1]);

            // (b) forgery: parties 0 and 1 fabricate party 2's share by re-labelling party 0's.
            // Wire layout is magic(8) then the party index as u64 LE.
            let mut bytes = shares[0].to_wire_bytes();
            bytes[8..16].copy_from_slice(&((N - 1) as u64).to_le_bytes());
            let fake = DecryptShare::from_wire_bytes(&bytes, custody.params())
                .expect("a re-labelled share is structurally well-formed");
            let coalition = vec![shares[0].clone(), shares[1].clone(), fake];
            let forged = custody.combine_shares(&coalition);
            (honest, short, forged)
        })
        .expect("custody handle");

    assert_eq!(
        honest, k,
        "the honest full quorum must open the invariant to k"
    );
    assert!(
        short.is_err(),
        "an n-1 share set must be refused (structural arity check)"
    );
    match forged {
        Err(_) => {}
        Ok(value) => assert_ne!(
            value, honest,
            "an n-1 coalition forging the missing share RECOVERED the plaintext — the n-of-n \
             reconstruction is not doing its job"
        ),
    }
}

/// `verify` is not the pool grading its own homework: it re-derives the constant-product
/// trajectory from the fills, then re-opens the CURRENT ciphertext reserves under the full quorum
/// and requires them to match. Corrupt either half and it breaks.
#[test]
fn verify_reopens_the_encrypted_reserves_under_the_full_quorum() {
    let offering = DarkPoolOffering::mount(0xA11D, 2).expect("mount the pool");
    let mut session = offering.open(SessionConfig::default()).expect("open");
    let a = player("ari");
    let b = player("bex");

    for who in [&a, &b] {
        must_land(
            &offering,
            &mut session,
            Action::new("", TURN_JOIN, 0, true),
            who,
            "taking a seat",
        );
    }
    // Two rungs of the ladder, by two different takers.
    for who in [&a, &b] {
        must_land(
            &offering,
            &mut session,
            Action::new("", TURN_SWAP, 1, true),
            who,
            "a quoted swap",
        );
    }

    let report = offering.verify(&session);
    assert!(report.verified, "{}", report.detail);
    assert_eq!(report.turns, 2);
    assert!(report.detail.contains("re-opened under all 2 custodians"));

    // The second rung is priced differently from the first — the encrypted book really moved.
    let first = offering.fills_for(&a).remove(0);
    let second = offering.fills_for(&b).remove(0);
    assert_ne!(
        first.price, second.price,
        "the pool quoted the same price twice; the reserves did not advance"
    );
    assert!(
        second.price > first.price,
        "depth should get more expensive"
    );
}

/// A size the invariant cannot price exactly is refused, and so is a swap without a seat. Both
/// are refusals of the *shape* of the request, and both commit nothing.
#[test]
fn an_unpriceable_size_and_a_seatless_taker_are_both_refused() {
    let offering = DarkPoolOffering::mount(0x9F1E, 2).expect("mount the pool");
    let mut session = offering.open(SessionConfig::default()).expect("open");
    let who = player("hasty");

    let seatless = offering.advance(
        &mut session,
        Action::new("", TURN_SWAP, 1, true),
        who.clone(),
    );
    assert!(matches!(seatless, Outcome::Refused(ref why) if why.contains("seat")));

    must_land(
        &offering,
        &mut session,
        Action::new("", TURN_JOIN, 0, true),
        &who,
        "taking a seat",
    );

    // This vendor crosses one relic per swap; anything else has no cross to make.
    let two = offering.advance(
        &mut session,
        Action::new("", TURN_SWAP, 2, true),
        who.clone(),
    );
    assert!(matches!(two, Outcome::Refused(_)));
    let zero = offering.advance(
        &mut session,
        Action::new("", TURN_SWAP, 0, true),
        who.clone(),
    );
    assert!(matches!(zero, Outcome::Refused(_)));
    assert!(offering.public_cards().is_empty());

    // Per-viewer affordances: seated, so JOIN dims and the swaps light up. That gating is on the
    // SEAT, never on the reserves.
    let mine = offering.actions_for(&session, &who);
    assert_eq!(mine.len(), 3);
    assert!(
        !mine[0].enabled,
        "an already-seated viewer should not be offered a seat"
    );
    assert!(mine[1].enabled && mine[2].enabled);
}
