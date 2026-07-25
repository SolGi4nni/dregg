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

/// The `{turn, arg}` affordance naming the FIRST legal decision of `kind` for the seat to
/// move. `arg` is an index into `TugSession::legal_decisions` — the documented encoding.
fn fire(session: &TugSession, kind: ActionKind) -> Action {
    let decisions = session.legal_decisions();
    let index = decisions
        .iter()
        .position(|d| d.kind() == Some(kind))
        .unwrap_or_else(|| panic!("{kind:?} has no legal decision right now"));
    Action::new(format!("{kind:?}"), kind.method(), index as i64, true)
}

/// The affordance naming the response that takes side `pick` of the pending offer.
fn fire_respond(session: &TugSession, pick: u8) -> Action {
    let offer = session.pending_offer().expect("an offer is on the table");
    let decisions = session.legal_decisions();
    let index = decisions
        .iter()
        .position(|d| *d == Decision::Respond { pick })
        .expect("the pick is on the menu");
    Action::new("respond", offer.respond_method(), index as i64, true)
}

/// Drive `kinds` in order for whichever seat is to move, asserting each lands.
fn drive_kinds(off: &TugOffering, session: &mut TugSession, kinds: &[ActionKind]) {
    for &kind in kinds {
        let seat = session.to_move();
        let input = fire(session, kind);
        let outcome = off.advance(session, input, TugOffering::seat_identity(seat));
        assert!(
            outcome.landed(),
            "{seat:?}'s {kind:?} should land, got {outcome:?}"
        );
    }
}

/// The `MENU <label> enabled=<bool>` lines of a rendered surface.
fn menu_lines(text: &str) -> Vec<&str> {
    text.lines().filter(|l| l.starts_with("MENU ")).collect()
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
            // The draw precedes the action, so the seat to move already holds its first
            // drawn favor — seven cards, six for the seat waiting.
            let expected = if seat == session.to_move() {
                HAND_SIZE + 1
            } else {
                HAND_SIZE
            };
            assert_eq!(committed.len(), expected);
            assert!(committed.iter().all(|&card| card < 21));
        }
        assert_eq!(session.to_move(), Player::A, "seat A opens");
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
    let input = fire(&session, ActionKind::Competition);
    let mut oracle = session.engine.clone();
    let chosen = session.legal_decisions()[input.arg as usize];
    let expected_move = oracle.apply(seat, chosen).expect("the chosen cut is legal");
    let played: Vec<u64> = expected_move
        .played_cards()
        .into_iter()
        .map(u64::from)
        .collect();
    assert_eq!(
        played.len(),
        4,
        "a Competition PRESENTS four cards, all of which leave the hand at offer time"
    );

    assert!(
        off.advance(&mut session, input, TugOffering::seat_identity(seat))
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
/// four-action menu, the used action greyed once its owner is back on move.
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
    // Four action rows, ALL live for the seat to move (the order is a free choice — there is
    // no schedule that greys three of them).
    let rows = menu_lines(&txt);
    assert_eq!(rows.len(), 4, "four once-per-round actions: {rows:?}");
    assert!(
        rows.iter().all(|r| r.ends_with("enabled=true")),
        "every unused action is offered live at the start: {rows:?}"
    );

    // Both seats play a PRIVATE action, so `seat` is on move again with Secret spent.
    drive_kinds(
        &off,
        &mut session,
        &[ActionKind::Secret, ActionKind::Secret],
    );
    assert_eq!(session.to_move(), seat, "the seat is back on move");
    let after = rendered_text(&off.render_for(&session, &TugOffering::seat_identity(seat)));
    let rows = menu_lines(&after);
    assert_eq!(rows.len(), 4);
    assert!(
        rows.iter()
            .any(|r| r.starts_with("MENU Secret") && r.ends_with("enabled=false")),
        "the spent Secret is greyed by its used-flag\n{after}"
    );
    assert!(
        rows.iter()
            .any(|r| r.starts_with("MENU Gift") && r.ends_with("enabled=true")),
        "an unspent action is still live\n{after}"
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
    let input = fire(&session, ActionKind::Secret);
    let refused = off.advance(&mut session, input.clone(), stranger);
    assert!(
        matches!(refused, Outcome::Refused(_)),
        "a non-seat is refused"
    );
    assert_eq!(
        session.runtime.read_projection().round_actions,
        before,
        "the refused move committed nothing"
    );

    // The seat's chosen action lands a real receipt and advances the committed round.
    let landed = off.advance(
        &mut session,
        input.clone(),
        TugOffering::seat_identity(seat),
    );
    match landed {
        Outcome::Landed { ended, .. } => {
            assert!(!ended, "one action does not end the round");
        }
        Outcome::Refused(r) => panic!("the chosen play should land, got refusal: {r}"),
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

    // An out-of-turn fire (the same seat pressing again while the OTHER seat is on move) is
    // refused.
    assert_eq!(session.to_move(), seat.other());
    let dup = off.advance(&mut session, input, TugOffering::seat_identity(seat));
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

    let input = fire(&session, ActionKind::Competition);
    let chosen = session.legal_decisions()[input.arg as usize];
    let mut next_engine = session.engine.clone();
    let mv = next_engine.apply(seat, chosen).expect("legal");
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

    assert!(
        off.advance(&mut session, input, TugOffering::seat_identity(seat))
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

    let input = fire(&session, ActionKind::Competition);
    let chosen = session.legal_decisions()[input.arg as usize];
    let mut next_engine = session.engine.clone();
    let mv = next_engine.apply(seat, chosen).expect("legal");
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

    let input = fire(&session, ActionKind::Competition);
    let chosen = session.legal_decisions()[input.arg as usize];
    let mut next_engine = session.engine.clone();
    let mv = next_engine.apply(seat, chosen).expect("legal");
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

    assert!(
        off.advance(&mut session, input, TugOffering::seat_identity(seat))
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
        // Take the first affordance the Offering itself presents — a real choice, whatever
        // it is.
        let a = off
            .actions(&session)
            .into_iter()
            .find(|a| a.enabled)
            .expect("a live round always offers something");
        let out = off.advance(&mut session, a, TugOffering::seat_identity(seat));
        assert!(out.landed(), "each chosen play lands a real turn: {out:?}");
        landed += 1;
    }
    assert_eq!(landed, 12, "eight action-turns plus four responses");
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
    assert_eq!(landed, 13, "twelve turns plus one SCORE turn");
    let projection = session.projection();
    assert_eq!(projection.scored, 1, "the SCORE turn really committed");
    assert_eq!(projection.secret_count, [0, 0], "secrets were revealed");
    assert_eq!(
        projection.round_actions, 12,
        "scoring does not forge a thirteenth player turn"
    );
    assert!(session.ended());
    assert!(off.actions(&session).is_empty());

    let report = off.verify(&session);
    assert!(report.verified, "{}", report.detail);
    assert_eq!(report.turns, 14, "genesis + twelve turns + SCORE");

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

/// Method and argument are one canonical decision identity. `arg` names the decision (an
/// index into `legal_decisions`) and `turn` must be the method THAT decision dispatches
/// under; a transport cannot splice one onto the other and still claim a landed receipt. The
/// refusal leaves the engine, hand root, and replay log untouched.
#[test]
fn method_argument_splice_is_refused_without_a_ghost_step() {
    let off = TugOffering;
    let mut session = off.open(SessionConfig::with_seed(13)).expect("open");
    let seat = session.to_move();
    let honest = fire(&session, ActionKind::Secret);
    let before_projection = session.projection();
    let before_root = session.hands[seat.idx()].root_bytes();

    // Same (valid) index, a DIFFERENT method: the decision at that index is a Secret, so
    // `gift` does not name it.
    let spliced = Action::new("spliced", "gift", honest.arg, true);
    let refused = off.advance(&mut session, spliced, TugOffering::seat_identity(seat));
    assert!(matches!(refused, Outcome::Refused(_)), "{refused:?}");

    // And an index off the end of the legal set is refused too.
    let past_end = Action::new(
        "spliced",
        "secret",
        session.legal_decisions().len() as i64,
        true,
    );
    let refused = off.advance(&mut session, past_end, TugOffering::seat_identity(seat));
    assert!(matches!(refused, Outcome::Refused(_)), "{refused:?}");

    assert_eq!(session.projection(), before_projection);
    assert_eq!(session.hands[seat.idx()].root_bytes(), before_root);
    assert!(session.history.is_empty());
    assert!(off.verify(&session).verified);

    // NON-VACUOUS: the honest pairing lands.
    assert!(
        off.advance(&mut session, honest, TugOffering::seat_identity(seat))
            .landed()
    );
}

/// `/verify` is a fresh confined replay, not a conservation-only spot check.
/// Corrupting the accepted input log makes the same live projection fail
/// verification because the forged first move refuses during replay.
#[test]
fn verification_replays_accepted_inputs_and_rejects_history_tamper() {
    let off = TugOffering;
    let mut session = off.open(SessionConfig::with_seed(17)).expect("open");
    // Three PRIVATE turns: these open no offer, so nothing here needs a `respond_*` method.
    drive_kinds(
        &off,
        &mut session,
        &[ActionKind::Secret, ActionKind::Secret, ActionKind::Discard],
    );
    let honest = off.verify(&session);
    assert!(honest.verified, "{}", honest.detail);

    let original = session.history[0];
    // A decision the replay's engine never offers (card 200 is not in any hand).
    session.history[0] = LandedInput::Play {
        seat: Player::A,
        decision: Decision::Secret { card: 200 },
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
        let a = off
            .actions(&session)
            .into_iter()
            .find(|a| a.enabled)
            .expect("a live round always offers something");
        assert!(
            off.advance(&mut session, a, TugOffering::seat_identity(seat))
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

/// ⚑ **I-CUT-YOU-CHOOSE, THROUGH THE OFFERING.** After a Gift the Offering offers exactly the
/// three response sides and nothing else; the CUTTER pressing one is refused (the anti-self-deal
/// tooth, at the surface) and the CHOOSER's press lands a real executor turn that places the
/// escrow on the two boards.
#[test]
fn the_chooser_answers_the_cut_and_the_cutter_cannot() {
    let off = TugOffering;
    let mut session = off.open(SessionConfig::with_seed(29)).expect("open");
    let cutter = session.to_move();

    // The CUT lands as a real turn.
    let input = fire(&session, ActionKind::Gift);
    assert!(
        off.advance(&mut session, input, TugOffering::seat_identity(cutter))
            .landed(),
        "presenting three favors is a legal, deployed action"
    );
    let offer = session.pending_offer().expect("the cut opened an offer");
    assert_eq!(offer.proposer, cutter);
    assert_eq!(session.to_move(), cutter.other(), "the chooser is on move");
    assert_eq!(
        session.projection().pending_kind,
        1,
        "the executor committed the pending-gift marker"
    );

    // The Offering now offers ONLY the three response sides.
    let rows = off.actions(&session);
    assert_eq!(rows.len(), 3, "three favors presented, three sides to take");
    assert!(
        rows.iter().all(|a| a.turn == "respond_gift" && a.enabled),
        "{rows:?}"
    );
    // The public surface names the cut and who must choose.
    let public = rendered_text(&off.render(&session));
    assert!(public.contains("ON THE TABLE"), "{public}");

    let answer = fire_respond(&session, 1);
    let before = session.projection();

    // The CUTTER is refused — the anti-self-deal tooth, at the surface.
    let refused = off.advance(
        &mut session,
        answer.clone(),
        TugOffering::seat_identity(cutter),
    );
    assert!(matches!(refused, Outcome::Refused(_)), "{refused:?}");

    assert_eq!(
        session.projection(),
        before,
        "the refused self-deal wrote nothing"
    );
    assert!(session.pending_offer().is_some(), "the table still waits");

    // The CHOOSER's press lands a real turn and places the escrow.
    let landed = off.advance(
        &mut session,
        answer,
        TugOffering::seat_identity(cutter.other()),
    );
    assert!(landed.landed(), "the chooser's answer lands: {landed:?}");
    let after = session.projection();
    assert_eq!(after.pending_kind, 0, "the table is clear again");
    assert_eq!(
        after.board[0] + after.board[1],
        3,
        "all three presented favors reached the boards"
    );
    assert_eq!(after.round_actions, before.round_actions + 1);
    assert_eq!(after.conservation_sum(), 21);
    assert_eq!(
        session.to_move(),
        cutter.other(),
        "the responder now takes their OWN action turn"
    );
    // The whole chain re-verifies through a fresh confined replay.
    let report = off.verify(&session);
    assert!(report.verified, "{}", report.detail);
}

/// The DEAL-pinned fold inventory is exactly the ten cards a seat spends — and it is the same
/// ten however that seat plays. This is what lets [`fold_inventory`] read the deal instead of
/// scripting a round: action-turns alternate A, B, A, B and only they draw, so the draw
/// assignment is choice-independent. Driven on the PURE engine (no executor, so no
/// `respond_*` method is needed).
#[test]
fn fold_inventory_is_the_deal_and_the_deal_is_what_gets_played() {
    use crate::reference::{Engine as Eng, greedy_policy, play_round_with};

    /// A policy that always takes the first legal decision of the earliest kind in `order`.
    fn ordered(order: [ActionKind; 4]) -> impl FnMut(&Eng) -> Decision {
        move |e: &Eng| {
            let options = e.legal_decisions();
            if let Some(d) = options
                .iter()
                .find(|d| matches!(d, Decision::Respond { .. }))
            {
                return *d;
            }
            for kind in order {
                if let Some(d) = options.iter().find(|d| d.kind() == Some(kind)) {
                    return *d;
                }
            }
            unreachable!("some unused kind is always affordable")
        }
    }

    for seed in [0u64, 3, 9, 23, 31, DEFAULT_SEED] {
        let inv = fold_inventory(seed);
        let lines = [
            play_round_with(seed, greedy_policy).1,
            play_round_with(
                seed,
                ordered([
                    ActionKind::Secret,
                    ActionKind::Discard,
                    ActionKind::Gift,
                    ActionKind::Competition,
                ]),
            )
            .1,
        ];
        for seat in [Player::A, Player::B] {
            let mut declared: Vec<u64> = inv[seat.idx()].iter().map(|&(c, _)| c).collect();
            assert_eq!(declared.len(), 10, "six opening favors + four draws");
            declared.sort_unstable();
            for moves in &lines {
                let mut played: Vec<u64> = moves
                    .iter()
                    .filter(|m| m.player() == seat)
                    .flat_map(|m| m.played_cards().into_iter().map(u64::from))
                    .collect();
                assert_eq!(played.len(), 10, "1 + 2 + 3 + 4 cards leave the hand");
                played.sort_unstable();
                assert_eq!(
                    declared, played,
                    "seed {seed} seat {seat:?}: the DEAL-pinned inventory must be exactly \
                     what that seat spends, under EVERY line of play"
                );
            }
        }
    }
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
