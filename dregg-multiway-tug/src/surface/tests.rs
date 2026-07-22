//! Tests for [`TugOffering`] — the per-player hidden-hand surface + the real-turn wiring.

use super::*;
use deos_view::ViewNode;
use dreggnet_offerings::{Offering, Outcome, SessionConfig};

/// Collect every piece of RENDERED TEXT from a surface — text nodes, pill/icon labels, coord-cell
/// glyphs, section titles, menu-item labels — into one string, so a test can assert what a viewer
/// can (and cannot) read off the card. (deos-view's text renderers are feature-gated off in this
/// crate's dep, so we walk the tree directly.)
fn rendered_text(surface: &Surface) -> String {
    fn walk(n: &ViewNode, out: &mut String) {
        let mut push = |s: &str| {
            out.push_str(s);
            out.push('\n');
        };
        match n {
            ViewNode::Text(s) => push(s),
            ViewNode::Pill { text, .. } => push(text),
            ViewNode::Icon { glyph, .. } => push(glyph),
            ViewNode::Section {
                title, children, ..
            } => {
                push(title);
                for c in children {
                    walk(c, out);
                }
            }
            ViewNode::Menu { items } => {
                for it in items {
                    out.push_str(&format!("MENU {} enabled={}\n", it.label, it.enabled));
                }
            }
            ViewNode::CoordGrid { cells, .. } => {
                for cell in cells {
                    out.push_str(&cell.glyph);
                    out.push('\n');
                }
            }
            ViewNode::VStack(cs) | ViewNode::Row(cs) | ViewNode::List(cs) | ViewNode::Table(cs) => {
                for c in cs {
                    walk(c, out);
                }
            }
            _ => {}
        }
    }
    let mut out = String::new();
    walk(surface.view(), &mut out);
    out
}

/// The ACTUAL reference-engine card ids a seat holds. Fog tests deliberately use this source,
/// rather than reading the same `HandTree` the renderer reads and validating a mirror against
/// itself.
fn seat_card_ids(session: &TugSession, seat: Player) -> Vec<u64> {
    session
        .engine
        .hand(seat)
        .iter()
        .copied()
        .map(u64::from)
        .collect()
}

#[test]
fn committed_hand_is_the_engine_deal_across_seeds() {
    let off = TugOffering;
    for seed in [0, 1, 7, 8, 99, u64::MAX] {
        let session = off.open(SessionConfig::with_seed(seed)).expect("open");
        for seat in [Player::A, Player::B] {
            let committed = session.hands[seat.idx()].card_ids();
            let dealt = seat_card_ids(&session, seat);
            assert_eq!(
                committed, dealt,
                "seed {seed} seat {seat:?}: committed UI hand must be the mover's deal"
            );
            assert_eq!(committed.len(), HAND_SIZE);
            assert!(committed.iter().all(|&card| card < 21));
        }
    }
}

#[test]
fn rendered_guilds_depend_on_the_seeded_shuffle() {
    let off = TugOffering;
    let mut observed = std::collections::BTreeSet::new();
    for seed in 0..16 {
        let session = off.open(SessionConfig::with_seed(seed)).expect("open");
        let guilds: Vec<u8> = session
            .engine
            .hand(Player::A)
            .iter()
            .map(|&card| deck_guild(u64::from(card)))
            .collect();
        let view = rendered_text(&off.render_for(&session, &TugOffering::seat_identity(Player::A)));
        for (&card, &guild) in session.engine.hand(Player::A).iter().zip(&guilds) {
            assert!(
                view.contains(&format!("card #{card} · guild {guild}")),
                "the rendered guild comes from the seeded engine card"
            );
        }
        let mut guilds = guilds;
        guilds.sort_unstable();
        observed.insert(guilds);
    }
    assert!(
        observed.len() > 1,
        "the old fabricated deal rendered the same [0,0,1,1,2,2] guilds for every seed"
    );
}

#[test]
fn exact_multi_card_move_updates_the_committed_hand_and_match_record() {
    let off = TugOffering;
    let mut session = off.open(SessionConfig::with_seed(23)).expect("open");
    let seat = session.to_move();
    let before: std::collections::BTreeSet<u64> =
        seat_card_ids(&session, seat).into_iter().collect();
    let mut oracle = session.engine.clone();
    let expected_move = oracle.play_next();
    let played: Vec<u64> = expected_move
        .played_cards()
        .into_iter()
        .map(u64::from)
        .collect();
    assert_eq!(
        played.len(),
        4,
        "the opening Competition consumes four cards"
    );

    let action = session.scheduled_action().expect("scheduled");
    assert!(
        off.advance(
            &mut session,
            Action::new("", action.method(), action.idx() as i64, true),
            TugOffering::seat_identity(seat),
        )
        .landed()
    );

    assert_eq!(
        session.plays[seat.idx()],
        played,
        "record exact action cards"
    );
    assert_eq!(
        session.hands[seat.idx()].card_ids(),
        seat_card_ids(&session, seat),
        "post-action commitment is the post-action engine hand"
    );
    for card in played.iter().filter(|card| before.contains(card)) {
        assert!(
            !session.hands[seat.idx()].card_ids().contains(card),
            "a consumed opening card must leave the current-hand root"
        );
    }
    assert!(off.verify(&session).verified);
}

/// **The fog, non-vacuously**: player A's view REVEALS A's card ids and CONCEALS B's; player B's
/// view of the SAME table conceals A's. Neither seat reads the other's cards.
#[test]
fn viewer_sees_own_hand_only() {
    let off = TugOffering;
    let session = off.open(SessionConfig::with_seed(7)).expect("open");

    let a_id = TugOffering::seat_identity(Player::A);
    let b_id = TugOffering::seat_identity(Player::B);
    let a_view = rendered_text(&off.render_for(&session, &a_id));
    let b_view = rendered_text(&off.render_for(&session, &b_id));

    let a_cards = seat_card_ids(&session, Player::A);
    let b_cards = seat_card_ids(&session, Player::B);
    assert!(!a_cards.is_empty() && !b_cards.is_empty(), "hands dealt");

    // A reveals A's cards; B's view NEVER shows A's card ids (the opponent fog). The trailing
    // ` ·` pins the exact card token (so "card #1" doesn't spuriously match inside "card #10").
    for id in &a_cards {
        let needle = format!("card #{id} ·");
        assert!(
            a_view.contains(&needle),
            "A's own view reveals {needle}\n{a_view}"
        );
        assert!(
            !b_view.contains(&needle),
            "B's view must NOT reveal A's {needle} (the hidden-hand fog)\n{b_view}"
        );
    }
    // Symmetrically, B reveals B's cards; A's view conceals them.
    for id in &b_cards {
        let needle = format!("card #{id} ·");
        assert!(b_view.contains(&needle), "B's own view reveals {needle}");
        assert!(
            !a_view.contains(&needle),
            "A's view must NOT reveal B's {needle}"
        );
    }

    // The opponent still appears — as FOG (a count + committed root), never card ids.
    assert!(
        a_view.contains("Opponent (hidden hand)") && a_view.contains("hidden"),
        "A sees the opponent as fog"
    );
}

/// **The public surface is fog for BOTH seats** — no card ids leak to a non-viewer render.
#[test]
fn public_render_is_fog_for_both() {
    let off = TugOffering;
    let session = off.open(SessionConfig::with_seed(7)).expect("open");
    let public = rendered_text(&off.render(&session));
    for id in seat_card_ids(&session, Player::A)
        .into_iter()
        .chain(seat_card_ids(&session, Player::B))
    {
        assert!(
            !public.contains(&format!("card #{id}")),
            "the public surface reveals no hand card ids"
        );
    }
    assert!(public.contains("Seat A (hidden hand)") && public.contains("Seat B (hidden hand)"));
}

/// **The guild-lane table + the action menu render**: seven lanes (one per guild) and a
/// four-action menu, the used action greyed after a play.
#[test]
fn guild_lanes_and_action_menu_render() {
    let off = TugOffering;
    let mut session = off.open(SessionConfig::with_seed(3)).expect("open");
    let seat = session.to_move();
    let view = off.render_for(&session, &TugOffering::seat_identity(seat));

    // Seven guild lanes (the Table under "Guilds").
    fn count_lanes(n: &ViewNode) -> usize {
        match n {
            ViewNode::Table(rows) => rows.len(),
            ViewNode::VStack(cs) | ViewNode::Section { children: cs, .. } => {
                cs.iter().map(count_lanes).sum()
            }
            _ => 0,
        }
    }
    assert_eq!(count_lanes(view.view()), N_GUILDS, "one lane per guild");

    let txt = rendered_text(&view);
    assert!(
        txt.contains("Guild 0") && txt.contains("Guild 6"),
        "lanes render"
    );
    // Four action rows, all enabled at the start.
    assert_eq!(
        txt.matches("MENU ").count(),
        4,
        "four once-per-round actions"
    );
    assert!(
        txt.contains("enabled=true"),
        "an unused action is offered live"
    );

    // After a real play the acting seat's used action is greyed.
    let scheduled = session.scheduled_action().expect("an action is scheduled");
    let out = off.advance(
        &mut session,
        Action::new("", scheduled.method(), scheduled.idx() as i64, true),
        TugOffering::seat_identity(seat),
    );
    assert!(out.landed(), "the scheduled play lands");
    let after = rendered_text(&off.render_for(&session, &TugOffering::seat_identity(seat)));
    assert!(
        after.contains(&format!("MENU {scheduled:?} enabled=false")),
        "the played action is greyed by its used-flag\n{after}"
    );
}

/// **A play fires a REAL executor turn** — the scheduled action lands a genuine [`TurnReceipt`];
/// an out-of-turn / out-of-order / non-seat fire is refused and commits nothing (anti-ghost).
#[test]
fn play_fires_a_real_turn() {
    let off = TugOffering;
    let mut session = off.open(SessionConfig::with_seed(5)).expect("open");
    let seat = session.to_move();
    let before = session.runtime.read_projection().round_actions;

    // A non-seat identity is refused.
    let stranger = DreggIdentity("someone-else".into());
    let scheduled = session.scheduled_action().unwrap();
    let refused = off.advance(
        &mut session,
        Action::new("", scheduled.method(), scheduled.idx() as i64, true),
        stranger,
    );
    assert!(
        matches!(refused, Outcome::Refused(_)),
        "a non-seat is refused"
    );
    assert_eq!(
        session.runtime.read_projection().round_actions,
        before,
        "the refused move committed nothing"
    );

    // The seat's scheduled action lands a real receipt and advances the committed round.
    let landed = off.advance(
        &mut session,
        Action::new("", scheduled.method(), scheduled.idx() as i64, true),
        TugOffering::seat_identity(seat),
    );
    match landed {
        Outcome::Landed { ended, .. } => {
            assert!(!ended, "one action does not end the round");
        }
        Outcome::Refused(r) => panic!("the scheduled play should land, got refusal: {r}"),
    }
    assert_eq!(
        session.runtime.read_projection().round_actions,
        before + 1,
        "the committed round advanced by one real turn"
    );
    assert_eq!(
        session.runtime.read_projection().conservation_sum(),
        21,
        "conservation holds on the committed post-state"
    );

    // An out-of-order fire (the same seat replaying its now-spent action) is refused.
    let dup = off.advance(
        &mut session,
        Action::new("", scheduled.method(), scheduled.idx() as i64, true),
        TugOffering::seat_identity(seat),
    );
    assert!(matches!(dup, Outcome::Refused(_)), "out-of-turn is refused");

    // The offering re-verifies the committed chain.
    assert!(
        off.verify(&session).verified,
        "the committed round verifies"
    );
}

#[test]
fn forged_membership_rolls_back_rules_and_hidden_cells_atomically() {
    let off = TugOffering;
    let mut session = off.open(SessionConfig::with_seed(6)).expect("open");
    let seat = session.to_move();
    let before_projection = session.projection();
    let before_ledger = session.runtime.state();
    let before_remaining = session.proof_hands[seat.idx()].root_bytes();

    let mut next_engine = session.engine.clone();
    let mv = next_engine.play_next();
    let full = HandTree::commit(session.fold_inventory[seat.idx()].clone());
    let mut remaining = session.proof_hands[seat.idx()].clone();
    let mut proofs = Vec::new();
    for card in mv.played_cards().into_iter().map(u64::from) {
        proofs.push(full.prove_play(card).expect("actual card is in inventory"));
        remaining = remaining.without(card);
    }
    let sibling = &mut proofs[0].path[0].siblings[0];
    *sibling = if *sibling == dregg_circuit::field::BabyBear::ZERO {
        dregg_circuit::field::BabyBear::ONE
    } else {
        dregg_circuit::field::BabyBear::ZERO
    };

    assert!(
        session
            .runtime
            .play_projection(
                seat,
                &mv.played_cards()
                    .into_iter()
                    .map(u64::from)
                    .collect::<Vec<_>>(),
                &proofs,
                remaining.root(),
                mv.action(),
                &next_engine.projection(),
            )
            .is_err(),
        "the hidden action must refuse the forged path"
    );
    assert_eq!(
        session.projection(),
        before_projection,
        "the sibling rules action is rolled back with the refused witness action"
    );
    assert_eq!(session.runtime.state(), before_ledger);
    assert_eq!(
        session.proof_hands[seat.idx()].root_bytes(),
        before_remaining
    );
    assert!(session.history.is_empty());

    let scheduled = session.scheduled_action().expect("scheduled");
    assert!(
        off.advance(
            &mut session,
            Action::new("", scheduled.method(), scheduled.idx() as i64, true),
            TugOffering::seat_identity(seat),
        )
        .landed(),
        "an honest retry lands after the atomic refusal"
    );
    assert!(off.verify(&session).verified);
}

#[test]
fn valid_but_wrong_card_opening_cannot_ride_beside_the_rules_action() {
    let off = TugOffering;
    let mut session = off.open(SessionConfig::with_seed(41)).expect("open");
    let seat = session.to_move();
    let before_projection = session.projection();
    let before_ledger = session.runtime.state();

    let mut next_engine = session.engine.clone();
    let mv = next_engine.play_next();
    let expected_cards: Vec<u64> = mv.played_cards().into_iter().map(u64::from).collect();
    let full = HandTree::commit(session.fold_inventory[seat.idx()].clone());
    let wrong_card = full
        .card_ids()
        .into_iter()
        .find(|card| !expected_cards.contains(card))
        .expect("the ten-card inventory has a card outside the opening four-card action");
    let mut proofs: Vec<_> = expected_cards
        .iter()
        .map(|&card| full.prove_play(card).expect("expected card is pinned"))
        .collect();
    proofs[0] = full
        .prove_play(wrong_card)
        .expect("wrong card still has a valid inventory opening");

    assert!(
        session
            .runtime
            .play_projection(
                seat,
                &expected_cards,
                &proofs,
                session.proof_hands[seat.idx()].root(),
                mv.action(),
                &next_engine.projection(),
            )
            .is_err(),
        "a valid membership proof for the wrong exact card must be refused"
    );
    assert_eq!(session.projection(), before_projection);
    assert_eq!(session.runtime.state(), before_ledger);
    assert!(session.history.is_empty());
}

#[test]
fn refused_rules_action_rolls_back_the_valid_hidden_action_atomically() {
    let off = TugOffering;
    let mut session = off.open(SessionConfig::with_seed(43)).expect("open");
    let seat = session.to_move();
    let before_projection = session.projection();
    let before_ledger = session.runtime.state();

    let mut next_engine = session.engine.clone();
    let mv = next_engine.play_next();
    let expected_cards: Vec<u64> = mv.played_cards().into_iter().map(u64::from).collect();
    let full = HandTree::commit(session.fold_inventory[seat.idx()].clone());
    let mut remaining = session.proof_hands[seat.idx()].clone();
    let proofs: Vec<_> = expected_cards
        .iter()
        .map(|&card| {
            let proof = full.prove_play(card).expect("actual card is pinned");
            remaining = remaining.without(card);
            proof
        })
        .collect();
    let mut forged_projection = next_engine.projection();
    forged_projection.deck += 1; // violates the Lean-authored 21-card conservation tooth

    assert!(
        session
            .runtime
            .play_projection(
                seat,
                &expected_cards,
                &proofs,
                remaining.root(),
                mv.action(),
                &forged_projection,
            )
            .is_err(),
        "the forged rules projection must be refused"
    );
    assert_eq!(session.projection(), before_projection);
    assert_eq!(
        session.runtime.state(),
        before_ledger,
        "the otherwise-valid hidden action must roll back with its rules sibling"
    );
    assert!(session.history.is_empty());

    let scheduled = session.scheduled_action().expect("scheduled");
    assert!(
        off.advance(
            &mut session,
            Action::new("", scheduled.method(), scheduled.idx() as i64, true),
            TugOffering::seat_identity(seat),
        )
        .landed(),
        "an honest retry lands after the atomic rules refusal"
    );
    assert!(off.verify(&session).verified);
}

/// **A full round drives to completion** through the Offering — every play a real turn.
#[test]
fn a_full_round_drives_through_the_offering() {
    let off = TugOffering;
    let mut session = off.open(SessionConfig::with_seed(9)).expect("open");
    let mut landed = 0;
    while !session.engine.round_complete() {
        let seat = session.to_move();
        let a = session.scheduled_action().expect("scheduled");
        let out = off.advance(
            &mut session,
            Action::new("", a.method(), a.idx() as i64, true),
            TugOffering::seat_identity(seat),
        );
        assert!(out.landed(), "each scheduled play lands a real turn");
        landed += 1;
    }
    assert_eq!(landed, 8, "eight action-turns played");
    assert_eq!(session.projection().scored, 0);
    let scoring = off.actions(&session);
    assert_eq!(scoring.len(), 1, "SCORE is the one remaining turn");
    assert_eq!((scoring[0].turn.as_str(), scoring[0].arg), ("score", 4));
    let scorer = TugOffering::seat_identity(session.to_move());
    match off.advance(&mut session, scoring[0].clone(), scorer) {
        Outcome::Landed { ended, .. } => {
            assert!(ended, "the explicit SCORE turn ends the round");
            landed += 1;
        }
        Outcome::Refused(reason) => panic!("the SCORE turn was refused: {reason}"),
    }
    assert_eq!(landed, 9, "eight actions plus one SCORE turn");
    let projection = session.projection();
    assert_eq!(projection.scored, 1, "the SCORE turn really committed");
    assert_eq!(projection.secret_count, [0, 0], "secrets were revealed");
    assert_eq!(
        projection.round_actions, 8,
        "scoring does not forge a ninth player action"
    );
    assert!(session.ended());
    assert!(off.actions(&session).is_empty());

    let report = off.verify(&session);
    assert!(report.verified, "{}", report.detail);
    assert_eq!(report.turns, 10, "genesis + eight plays + SCORE");

    let terminal = rendered_text(&off.render(&session));
    assert!(terminal.contains("ROUND COMPLETE"), "{terminal}");
    assert!(
        terminal.contains("WINNER:") || terminal.contains("DRAW"),
        "the terminal surface names the actual result: {terminal}"
    );
    assert!(
        terminal.contains("Influence A:"),
        "final scoring is visible"
    );
}

/// Method and argument are one canonical action identity. A transport cannot
/// splice a valid method onto a different menu argument and still claim a
/// landed receipt; the refusal leaves the engine, hand root, and replay log
/// untouched.
#[test]
fn method_argument_splice_is_refused_without_a_ghost_step() {
    let off = TugOffering;
    let mut session = off.open(SessionConfig::with_seed(13)).expect("open");
    let seat = session.to_move();
    let action = session.scheduled_action().expect("scheduled");
    let before_projection = session.projection();
    let before_root = session.hands[seat.idx()].root_bytes();

    let refused = off.advance(
        &mut session,
        Action::new("spliced", action.method(), (action.idx() + 1) as i64, true),
        TugOffering::seat_identity(seat),
    );
    assert!(matches!(refused, Outcome::Refused(_)));
    assert_eq!(session.projection(), before_projection);
    assert_eq!(session.hands[seat.idx()].root_bytes(), before_root);
    assert!(session.history.is_empty());
    assert!(off.verify(&session).verified);
}

/// `/verify` is a fresh confined replay, not a conservation-only spot check.
/// Corrupting the accepted input log makes the same live projection fail
/// verification because the forged first move refuses during replay.
#[test]
fn verification_replays_accepted_inputs_and_rejects_history_tamper() {
    let off = TugOffering;
    let mut session = off.open(SessionConfig::with_seed(17)).expect("open");
    for _ in 0..3 {
        let seat = session.to_move();
        let action = session.scheduled_action().expect("scheduled");
        assert!(
            off.advance(
                &mut session,
                Action::new("", action.method(), action.idx() as i64, true),
                TugOffering::seat_identity(seat),
            )
            .landed()
        );
    }
    let honest = off.verify(&session);
    assert!(honest.verified, "{}", honest.detail);

    let original = session.history[0];
    session.history[0] = LandedInput::Play {
        seat: Player::A,
        action: ActionKind::Gift,
    };
    let forged = off.verify(&session);
    assert!(!forged.verified, "forged history must not replay");
    assert!(
        forged.detail.contains("refused during replay"),
        "{}",
        forged.detail
    );

    session.history[0] = original;
    assert!(
        off.verify(&session).verified,
        "the honest record still replays"
    );
}

#[test]
fn terminal_private_record_contains_every_actual_card_exactly_once() {
    let off = TugOffering;
    let mut session = off.open(SessionConfig::with_seed(31)).expect("open");
    while !session.engine.round_complete() {
        let seat = session.to_move();
        let action = session.scheduled_action().expect("scheduled");
        assert!(
            off.advance(
                &mut session,
                Action::new("", action.method(), action.idx() as i64, true),
                TugOffering::seat_identity(seat),
            )
            .landed()
        );
    }

    assert!(
        session.terminal_match_record(Player::A).is_none(),
        "future-draw inventory is unavailable before SCORE"
    );
    let scoring = off.actions(&session);
    assert_eq!(scoring.len(), 1);
    let scorer = session.to_move();
    assert!(
        off.advance(
            &mut session,
            scoring[0].clone(),
            TugOffering::seat_identity(scorer),
        )
        .landed()
    );

    for seat in [Player::A, Player::B] {
        let private = session
            .terminal_match_record(seat)
            .expect("SCORE unlocks the private fold record");
        let inventory = private.hand;
        let plays = private.plays;
        assert_eq!(inventory.len(), 10, "six opening cards + four draws");
        assert_eq!(plays.len(), 10, "4 + 3 + 2 + 1 exact action cards");

        let inventory_ids: std::collections::BTreeSet<u64> =
            inventory.iter().map(|&(card, _)| card).collect();
        let played_ids: std::collections::BTreeSet<u64> = plays.iter().copied().collect();
        assert_eq!(inventory_ids.len(), 10, "distinct card identities");
        assert_eq!(
            played_ids, inventory_ids,
            "fold inventory is the played inventory"
        );

        // This is the exact fast precondition the whole-match fold consumes: each real played
        // card has a membership opening under the remaining private inventory root, in order.
        let mut tree = HandTree::commit(inventory);
        for card in plays {
            assert!(
                tree.prove_play(card).is_some(),
                "actual card {card} has a membership path before it is consumed"
            );
            tree = tree.without(card);
        }
        assert!(tree.card_ids().is_empty());
    }
    assert!(off.verify(&session).verified);
}

#[test]
fn forged_ui_hand_commitment_fails_fresh_replay() {
    let off = TugOffering;
    let mut session = off.open(SessionConfig::with_seed(37)).expect("open");
    let honest = session.hands[Player::A.idx()].root_bytes();
    session.hands[Player::A.idx()] = HandTree::commit(vec![(20, 123456)]);
    assert_ne!(session.hands[Player::A.idx()].root_bytes(), honest);

    let report = off.verify(&session);
    assert!(
        !report.verified,
        "a peer commitment cannot replace the engine deal"
    );
    assert!(
        report.detail.contains("fresh-seed replay"),
        "{}",
        report.detail
    );
}
