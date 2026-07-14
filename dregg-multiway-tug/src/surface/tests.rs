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
    while !session.ended() {
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
    assert!(off.verify(&session).verified);
}
