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

/// The committed hidden-hand card ids a seat holds (read straight off the session's [`HandTree`]).
fn seat_card_ids(session: &TugSession, seat: Player) -> Vec<u64> {
    session.hands[seat.idx()].card_ids()
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
    let before = session.game.read_projection().round_actions;

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
        session.game.read_projection().round_actions,
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
        session.game.read_projection().round_actions,
        before + 1,
        "the committed round advanced by one real turn"
    );
    assert_eq!(
        session.game.read_projection().conservation_sum(),
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
