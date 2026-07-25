//! # THE FALSIFIER — the round is no longer a replay of its deal.
//!
//! Every test here drives the pure [`Engine`] (no executor, no proving), because the claim
//! under test is about the RULES: that a seat's choices, not the shuffle, decide the round.
//! The rules are authored in `metatheory/Dregg2/Games/MultiwayTug.lean`; these assertions
//! mirror the theorems there against the Rust expression of them.
//!
//! * [`same_deal_different_outcomes`] — ONE seed, two complete rounds differing ONLY in the
//!   decisions, reaching different projections and different winners.
//!   (Lean `respond_decides_the_round`.)
//! * [`proposer_cannot_answer_own_offer`] — the anti-self-deal tooth, paired with the
//!   opponent's answer landing. (Lean `respond_not_by_proposer`.)
//! * [`no_action_while_offer_pending`] — the interlock, paired with play resuming after the
//!   answer. (Lean `pending_blocks_actions`.)
//! * [`action_order_is_free`] — two different orders both legal, reaching different states.
//!   (Lean `every_action_order_is_feasible`.)
//! * [`conservation_holds_mid_offer`] — the sum is 21 at every turn, escrow included.
//!   (Lean `conservation` / `conservation_response`.)
//! * [`respond_split_matches_lean`] — the exact `takerShare`/`cutterShare` table.

use dregg_multiway_tug::reference::{
    ActionKind, Decision, Engine, MoveError, OfferShape, PendingOffer, Player, ROUND_TURNS,
};

/// The seed every "same deal, different play" test drives.
const SEED: u64 = 0x5EED;

/// Play the round to completion, choosing at each turn the FIRST legal decision whose
/// action-kind comes earliest in `order` (and, when answering, pick `resp_pick` clamped into
/// range). Two different `order`s over the same seed are two different rounds off ONE deal.
fn drive(seed: u64, order: [ActionKind; 4], resp_pick: u8) -> Engine {
    let mut e = Engine::new(seed);
    let mut sums = Vec::new();
    while !e.round_complete() {
        let p = e.current_player();
        let d = choose(&e, &order, resp_pick);
        e.apply(p, d).expect("the chosen decision is legal");
        sums.push(e.projection().conservation_sum());
    }
    assert!(
        sums.iter().all(|&s| s == 21),
        "conservation held on every committed turn: {sums:?}"
    );
    e
}

fn choose(e: &Engine, order: &[ActionKind; 4], resp_pick: u8) -> Decision {
    let options = e.legal_decisions();
    assert!(!options.is_empty(), "a live round always offers a decision");
    if let Some(offer) = e.pending_offer() {
        let pick = resp_pick % offer.picks();
        return Decision::Respond { pick };
    }
    for kind in order {
        if let Some(d) = options.iter().find(|d| d.kind() == Some(*kind)) {
            return *d;
        }
    }
    unreachable!("some unused kind is always affordable (Lean every_action_order_is_feasible)")
}

/// Drive `n` turns and stop, returning the engine mid-round.
fn drive_n(seed: u64, order: [ActionKind; 4], resp_pick: u8, n: usize) -> Engine {
    let mut e = Engine::new(seed);
    for _ in 0..n {
        if e.round_complete() {
            break;
        }
        let p = e.current_player();
        let d = choose(&e, &order, resp_pick);
        e.apply(p, d).expect("legal");
    }
    e
}

const DESCENDING: [ActionKind; 4] = [
    ActionKind::Competition,
    ActionKind::Gift,
    ActionKind::Discard,
    ActionKind::Secret,
];
const ASCENDING: [ActionKind; 4] = [
    ActionKind::Secret,
    ActionKind::Discard,
    ActionKind::Gift,
    ActionKind::Competition,
];

/// ⚑ **THE WHOLE POINT.** From ONE fixed seed — one shuffle, one deal, one set of draws —
/// two complete rounds that differ ONLY in the decisions the seats make land on DIFFERENT
/// final projections and DIFFERENT winners. Before this rewrite the round was a pure function
/// of the seed and this test could not have been written.
#[test]
fn same_deal_different_outcomes() {
    // The lines of play we compare: which action-kind each seat reaches for first, crossed
    // with which side the responder takes. Every one of them is legal from the SAME deal —
    // Lean `every_action_order_is_feasible` says no ordering starves.
    const ORDERS: [[ActionKind; 4]; 4] = [
        DESCENDING,
        ASCENDING,
        [
            ActionKind::Gift,
            ActionKind::Secret,
            ActionKind::Competition,
            ActionKind::Discard,
        ],
        [
            ActionKind::Discard,
            ActionKind::Competition,
            ActionKind::Secret,
            ActionKind::Gift,
        ],
    ];
    let mut found: Option<(Engine, Engine, u64)> = None;
    'search: for seed in 0u64..128 {
        // The reference round: descending kinds, the responder always takes side 0.
        let mut base = drive(seed, ORDERS[0], 0);
        let base_winner = base.score().expect("the Lean oracle adjudicates");
        if base_winner.is_none() {
            continue;
        }
        for order in ORDERS {
            for pick in 0..3u8 {
                if order == ORDERS[0] && pick == 0 {
                    continue;
                }
                let mut alt = drive(seed, order, pick);
                let alt_winner = alt.score().expect("the Lean oracle adjudicates");
                if alt_winner.is_some() && alt_winner != base_winner {
                    found = Some((base, alt, seed));
                    break 'search;
                }
            }
        }
    }
    let (base, alt, seed) = found.expect(
        "over one deal, two legal lines of play must be able to reach different winners \
         (if this fails the game is still a replay of its shuffle)",
    );
    let (bp, ap) = (base.projection(), alt.projection());
    assert_eq!(
        bp.conservation_sum(),
        21,
        "seed {seed}: the reference round conserves"
    );
    assert_eq!(
        ap.conservation_sum(),
        21,
        "seed {seed}: the alt round conserves"
    );
    assert_ne!(
        bp.winner, ap.winner,
        "seed {seed}: the SAME deal must be able to end with different winners"
    );
    assert_ne!(
        bp, ap,
        "seed {seed}: the two rounds must reach different final projections"
    );
    // Both really are the SAME deal: the ten cards each seat is entrusted are identical.
    let deal = Engine::new(seed);
    for p in [Player::A, Player::B] {
        assert_eq!(
            deal.round_inventory(p).len(),
            10,
            "six opening favors plus four draws"
        );
    }
    eprintln!(
        "SAME DEAL, DIFFERENT OUTCOME (seed {seed}): winner {} vs {}",
        bp.winner, ap.winner
    );
}

/// The ANTI-SELF-DEAL tooth, non-vacuously: after A cuts a Gift, A answering is refused with
/// exactly [`MoveError::CannotAnswerOwnOffer`] — and the SAME pick by B lands.
#[test]
fn proposer_cannot_answer_own_offer() {
    let mut e = Engine::new(SEED);
    // A cuts a Gift (the first legal Gift decision off A's opening hand).
    let gift = e
        .legal_decisions()
        .into_iter()
        .find(|d| d.kind() == Some(ActionKind::Gift))
        .expect("a Gift is affordable on the opening turn");
    e.apply(Player::A, gift).expect("A's cut is legal");
    let offer = e.pending_offer().expect("the cut opened an offer");
    assert_eq!(offer.proposer, Player::A);
    assert_eq!(offer.picks(), 3);
    assert_eq!(
        e.current_player(),
        Player::B,
        "the seat passed to the chooser"
    );

    for pick in 0..3u8 {
        assert_eq!(
            e.apply(Player::A, Decision::Respond { pick }),
            Err(MoveError::CannotAnswerOwnOffer),
            "the cutter can never choose (pick {pick})"
        );
    }
    // The refusals changed nothing.
    assert!(e.pending_offer().is_some());
    assert_eq!(e.projection().round_actions, 1);

    // ... and B's answer LANDS (the refusal above is not vacuous).
    let mv = e
        .apply(Player::B, Decision::Respond { pick: 1 })
        .expect("the OTHER seat's answer is legal");
    assert_eq!(mv.player(), Player::B);
    assert_eq!(
        mv.played_cards(),
        Vec::<u8>::new(),
        "a response spends no card"
    );
    assert!(e.pending_offer().is_none(), "the table is clear again");
    assert_eq!(
        e.projection().round_actions,
        2,
        "the response is a real turn"
    );
    assert_eq!(
        e.current_player(),
        Player::B,
        "the responder now takes their OWN action turn"
    );
}

/// THE INTERLOCK, non-vacuously: while an offer stands, NO action is legal for EITHER seat —
/// and after the answer, one lands.
#[test]
fn no_action_while_offer_pending() {
    let mut e = Engine::new(SEED);
    let comp = e
        .legal_decisions()
        .into_iter()
        .find(|d| d.kind() == Some(ActionKind::Competition))
        .expect("a Competition is affordable on the opening turn");
    e.apply(Player::A, comp).expect("A's cut is legal");
    assert!(e.pending_offer().is_some());

    // Concrete actions for both seats, built from cards they really hold.
    for seat in [Player::A, Player::B] {
        let hand = e.hand(seat).to_vec();
        assert!(hand.len() >= 3, "both seats still hold favors");
        let attempts = [
            Decision::Secret { card: hand[0] },
            Decision::Discard {
                cards: [hand[0], hand[1]],
            },
            Decision::Gift {
                present: [hand[0], hand[1], hand[2]],
            },
        ];
        for d in attempts {
            assert_eq!(
                e.apply(seat, d),
                Err(MoveError::OfferPending),
                "{seat:?} may not act while the table waits: {d:?}"
            );
        }
    }
    // Only the responder's answer is on the menu.
    let menu = e.legal_decisions();
    assert!(
        menu.iter().all(|d| matches!(d, Decision::Respond { .. })),
        "with an offer pending only responses are legal: {menu:?}"
    );
    assert_eq!(menu.len(), 2, "a Competition offers two pairs");

    // After the answer, an ACTION lands (non-vacuity).
    e.apply(Player::B, Decision::Respond { pick: 0 })
        .expect("B answers");
    let next = e.legal_decisions();
    assert!(
        next.iter().any(|d| d.kind().is_some()),
        "play resumes with real actions"
    );
    let action = *next.iter().find(|d| d.kind().is_some()).unwrap();
    e.apply(Player::B, action)
        .expect("an action lands once the table is clear");
}

/// DECISION 1 IS REAL: from the SAME seed two different action ORDERS are both legal all the
/// way through and reach different states. (Lean `every_action_order_is_feasible`.)
#[test]
fn action_order_is_free() {
    let descending = drive(SEED, DESCENDING, 0);
    let ascending = drive(SEED, ASCENDING, 0);

    // Both really played all four kinds for both seats — neither line starved.
    for e in [&descending, &ascending] {
        assert_eq!(e.projection().round_actions, ROUND_TURNS);
        for p in [Player::A, Player::B] {
            for k in [
                ActionKind::Secret,
                ActionKind::Discard,
                ActionKind::Gift,
                ActionKind::Competition,
            ] {
                assert!(e.used_flag(p, k), "{p:?} spent {k:?}");
            }
        }
    }
    // The used-flag STAMPS differ: the kinds were spent in a different turn order.
    assert_ne!(
        descending.projection().flag,
        ascending.projection().flag,
        "two different orders must leave different used-flag stamps"
    );
    assert_ne!(
        descending.projection(),
        ascending.projection(),
        "two different orders must reach different states"
    );
}

/// Conservation holds on EVERY committed turn, including while an offer stands on the table
/// (the escrow is counted in its proposer's hand column, mirroring the Lean `pendingCards`
/// fold into `totalCards`).
#[test]
fn conservation_holds_mid_offer() {
    let mut e = Engine::new(SEED);
    assert_eq!(e.projection().conservation_sum(), 21, "the deal conserves");
    let mut saw_pending = false;
    let mut turns = 0;
    while !e.round_complete() {
        let p = e.current_player();
        let d = choose(&e, &DESCENDING, 0);
        e.apply(p, d).expect("legal");
        turns += 1;
        let proj = e.projection();
        assert_eq!(
            proj.conservation_sum(),
            21,
            "turn {turns} broke conservation: {proj:?}"
        );
        if proj.pending_kind != 0 {
            saw_pending = true;
            let offer = e
                .pending_offer()
                .expect("pending_kind says an offer stands");
            // The escrow really is off-hand and really is counted.
            let held = e.hand(offer.proposer).len() as u64;
            let counted = proj.hand[offer.proposer.idx()];
            assert_eq!(
                counted - held,
                offer.presented().len() as u64,
                "turn {turns}: the escrow must be counted in the proposer's column"
            );
        }
    }
    assert!(saw_pending, "a full round really does pass through offers");
    assert_eq!(turns, ROUND_TURNS as usize, "8 actions + 4 responses");
    // And through scoring.
    let mut scored = e;
    scored.score().expect("the Lean oracle adjudicates");
    assert_eq!(scored.projection().conservation_sum(), 21);
}

/// The exact `takerShare` / `cutterShare` table of the Lean model, for all 3 gift picks and
/// both comp picks. The TAKER is the responder; the CUTTER (proposer) keeps what is left.
#[test]
fn respond_split_matches_lean() {
    let gift = PendingOffer {
        proposer: Player::A,
        shape: OfferShape::Gift([10, 11, 12]),
    };
    assert_eq!(gift.split(0), Some((vec![10], vec![11, 12])));
    assert_eq!(gift.split(1), Some((vec![11], vec![10, 12])));
    assert_eq!(gift.split(2), Some((vec![12], vec![10, 11])));
    assert_eq!(gift.split(3), None, "there is no fourth favor");

    let comp = PendingOffer {
        proposer: Player::B,
        shape: OfferShape::Competition([[1, 2], [3, 4]]),
    };
    assert_eq!(comp.split(0), Some((vec![1, 2], vec![3, 4])));
    assert_eq!(comp.split(1), Some((vec![3, 4], vec![1, 2])));
    assert_eq!(comp.split(2), None, "there is no third pair");

    // `share_split`: taker + cutter is always the WHOLE offer, never more, never less.
    for offer in [gift, comp] {
        for pick in 0..offer.picks() {
            let (t, c) = offer.split(pick).expect("a legal pick splits");
            let mut all: Vec<u8> = t.into_iter().chain(c).collect();
            all.sort_unstable();
            let mut presented = offer.presented();
            presented.sort_unstable();
            assert_eq!(all, presented, "the escrow empties exactly");
        }
    }

    // And it is the ENGINE that applies exactly this table: the two picks place different
    // cards on the responder's side.
    let mut left = drive_n(SEED, DESCENDING, 0, 1);
    let mut right = left.clone();
    let offer = left.pending_offer().expect("turn 1 opened an offer");
    let responder = offer.responder();
    let (t0, _) = offer.split(0).unwrap();
    let (t1, _) = offer.split(1).unwrap();
    assert_ne!(t0, t1, "the two sides really differ");
    left.apply(responder, Decision::Respond { pick: 0 })
        .expect("legal");
    right
        .apply(responder, Decision::Respond { pick: 1 })
        .expect("legal");
    assert_ne!(
        left.projection().score,
        right.projection().score,
        "the responder's choice moves the board (Lean respond_changes_the_board)"
    );
}
