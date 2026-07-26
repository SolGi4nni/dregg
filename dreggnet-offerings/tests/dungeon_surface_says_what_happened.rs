//! **The dungeon surface must be able to say WHAT JUST HAPPENED.**
//!
//! The Keep's authored prose reads well and is STATIC. Trading blows with the gate-warden returns
//! to the SAME passage, so a 20-HP loss re-rendered with the same prose, the same objective and the
//! same sections: the consequence of the single most consequential move in the room was
//! structurally unrecoverable from the surface, and a player on a chat frontend whose previous
//! message had scrolled away simply could not learn it.
//!
//! These are the tests that fail if that regresses. They assert
//!
//!  * a committed turn is DISTINGUISHABLE — a 20-HP loss does not re-render as no loss, and the
//!    surface names the movement (`HP 50 → 30`) rather than leaving it to be diffed;
//!  * two different moves produce two different last-outcome readings (an HP loss in the same room
//!    vs a room change with no HP loss), so the node tracks the turn rather than the room;
//!  * turn 0 does not look like turn 1 — an untouched Keep says so;
//!  * the party's vitals are METERS ([`ViewNode::Progress`]), not bare integers in a counter line;
//!  * the domain plaque's rules are READ OUT OF THE DEPLOYED PROGRAM — the exact `−20` blow and
//!    the `HP ≥ 1` floor the executor holds the trade to — so the page cannot drift from the tooth;
//!  * and all of it survives the text projection every button-less channel renders, because a
//!    consequence that exists only in the HTML is one most of our players never see.

use deos_view::ViewNode;
use deos_view::text::render_text;
use dreggnet_offerings::dungeon::{DungeonOffering, TURN_CHOOSE};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};
use dungeon_on_dregg::{KP_DESCEND, KP_PRESS_ON, KP_TRADE_BLOWS};

fn actor() -> DreggIdentity {
    DreggIdentity("keep-reader".to_string())
}

fn choose(index: usize) -> Action {
    Action::new("move", TURN_CHOOSE, index as i64, true)
}

/// Open a Keep and paint it as the text every prose channel renders.
fn opened() -> (
    DungeonOffering,
    <DungeonOffering as Offering>::Session,
    String,
) {
    let offering = DungeonOffering::new();
    let session = offering
        .open(SessionConfig::with_seed(3))
        .expect("the Keep deploys");
    let painted = render_text(offering.render(&session).view());
    (offering, session, painted)
}

fn land(
    offering: &DungeonOffering,
    session: &mut <DungeonOffering as Offering>::Session,
    index: usize,
) {
    match offering.advance(session, choose(index), actor()) {
        Outcome::Landed { .. } => {}
        Outcome::Refused(why) => panic!("choice #{index} was expected to land: {why}"),
    }
}

/// Collect every [`ViewNode::Progress`] in a tree as `(label, value, max)`.
fn meters(node: &ViewNode) -> Vec<(String, u64, u64)> {
    let mut out = Vec::new();
    fn walk(node: &ViewNode, out: &mut Vec<(String, u64, u64)>) {
        match node {
            ViewNode::Progress { value, max, label } => {
                out.push((label.trim().to_string(), *value, *max));
            }
            ViewNode::VStack(kids)
            | ViewNode::Row(kids)
            | ViewNode::List(kids)
            | ViewNode::Table(kids)
            | ViewNode::Section { children: kids, .. }
            | ViewNode::Grid { children: kids, .. } => {
                for kid in kids {
                    walk(kid, out);
                }
            }
            _ => {}
        }
    }
    walk(node, &mut out);
    out
}

/// ⚑ **THE FALSIFIER — a 20-HP loss is not the same page as no loss.**
///
/// `Trade blows with the gate-warden` navigates back to `gatehall`, so the authored prose, the
/// room name and every static section are byte-identical across it. The ONLY thing that can carry
/// the consequence is a node derived from the committed turn — and it must name the movement, not
/// merely differ by an incremented counter.
#[test]
fn a_twenty_hp_loss_is_distinguishable_from_no_loss() {
    let (offering, mut session, before) = opened();
    assert_eq!(session.read_var("hp"), 50, "the Keep opens the fight at 50");

    land(&offering, &mut session, KP_TRADE_BLOWS);
    assert_eq!(session.read_var("hp"), 30, "the blow really landed");
    let after = render_text(offering.render(&session).view());

    assert_ne!(
        before, after,
        "a 20-HP loss re-rendered byte-identically — the surface cannot say what happened"
    );
    assert!(
        after.contains("HP 50 → 30"),
        "the surface must NAME the movement, not leave it to be diffed: {after}"
    );
    assert!(
        after.contains("Trade blows with the gate-warden"),
        "the surface must name the choice that caused it: {after}"
    );
    assert!(
        after.contains("keep-reader"),
        "the surface must name who drove it: {after}"
    );
    // And the room really did not change, which is the whole reason the node is needed.
    assert!(
        before.contains("gate-warden bars the way") && after.contains("gate-warden bars the way"),
        "the authored prose is the SAME across this move, by design"
    );
}

/// **The reading tracks the TURN, not the room.** A room change with no HP loss and an HP loss with
/// no room change must produce different last-outcome readings; if the node only reported position
/// it would collapse them.
#[test]
fn two_different_moves_read_differently() {
    let (offering, mut session, _) = opened();

    land(&offering, &mut session, KP_TRADE_BLOWS);
    let bled = render_text(offering.render(&session).view());

    land(&offering, &mut session, KP_PRESS_ON);
    let moved = render_text(offering.render(&session).view());

    assert_ne!(bled, moved);
    assert!(
        bled.contains("HP 50 → 30"),
        "the blow's reading names the HP movement: {bled}"
    );
    assert!(
        !moved.contains("HP 30 → "),
        "pressing on moves no HP, so its reading must claim none: {moved}"
    );
    assert!(
        moved.contains("It moved no party var at all."),
        "a move with no committed party delta says so plainly: {moved}"
    );
    assert!(
        moved.contains("Press on into the plundered hall"),
        "…and still names the choice and the rooms: {moved}"
    );

    // A descent moves `depth`, which is a THIRD distinct reading.
    land(&offering, &mut session, KP_DESCEND);
    let descended = render_text(offering.render(&session).view());
    assert!(
        descended.contains("depth 0 → 1"),
        "the descent's reading names the depth movement: {descended}"
    );
}

/// **Turn 0 does not look like turn 1.** An untouched Keep says nothing has happened yet, rather
/// than presenting a state a player might read as the result of their press.
#[test]
fn an_untouched_keep_says_nothing_has_happened_yet() {
    let (_offering, _session, genesis) = opened();
    assert!(
        genesis.contains("Nothing yet"),
        "an unplayed Keep must not imply a consequence: {genesis}"
    );
    assert!(
        genesis.contains("turn 1"),
        "…and should say which turn the next press will be: {genesis}"
    );
}

/// **The vitals are METERS.** `HP 50 · depth 0 · gold 0 · crown unclaimed · will spent 0` is a
/// counter dump; a `Progress` paints as a gauge on every renderer and answers "how much is left"
/// without arithmetic. The denominators must be the REAL ones — the deployed HP ceiling and the
/// committed will budget the executor's own cross-slot tooth compares against.
#[test]
fn the_party_vitals_are_meters_with_real_denominators() {
    let (offering, mut session, _) = opened();
    land(&offering, &mut session, KP_TRADE_BLOWS);
    let surface = offering.render(&session);
    let bars = meters(surface.view());

    let hp = bars
        .iter()
        .find(|(label, _, _)| label == "party HP")
        .expect("the party's HP is a meter");
    assert_eq!(hp.1, 30, "the meter reads the committed HP");
    assert_eq!(
        hp.2, 50,
        "…out of the DEPLOYED ceiling the Mender recovery is held to"
    );

    let will = bars
        .iter()
        .find(|(label, _, _)| label == "will")
        .expect("the will reserve is a meter");
    assert_eq!(
        (will.1, will.2),
        (0, session.read_var("mana_budget")),
        "the will meter's denominator is the committed budget slot the executor compares against"
    );
}

/// ⚑ **The domain plaque's numbers come from the DEPLOYED PROGRAM.**
///
/// The Keep's teeth are invisible in the authored prose: the trade costs exactly 20 HP and the case
/// is admitted only while the post-state keeps `hp ≥ 1`. Those two numbers are lifted out of the
/// installed `CellProgram` rather than retyped, so this asserts they REACH the page — and that the
/// blows-remaining count they imply is the real one, by driving the run to the refusal.
#[test]
fn the_teeth_plaque_quotes_the_deployed_toll() {
    let (offering, mut session, genesis) = opened();
    assert!(
        genesis.contains("moves HP by exactly -20"),
        "the exact deployed blow must reach the page: {genesis}"
    );
    assert!(
        genesis.contains("HP ≥ 1"),
        "the deployed post-state floor must reach the page: {genesis}"
    );
    assert!(
        genesis.contains("that is 2 more blows"),
        "at 50 HP, a -20 blow and a floor of 1 leave exactly two: {genesis}"
    );

    // DRIVEN: the plaque's count is the executor's. Two blows land (50 → 30 → 10); the third
    // would break the floor and is a real refusal that commits nothing.
    land(&offering, &mut session, KP_TRADE_BLOWS);
    land(&offering, &mut session, KP_TRADE_BLOWS);
    assert_eq!(session.read_var("hp"), 10);
    let spent = render_text(offering.render(&session).view());
    assert!(
        spent.contains("the gate-warden trade is spent"),
        "the surface warns BEFORE the refusal, not after: {spent}"
    );
    assert!(
        matches!(
            offering.advance(&mut session, choose(KP_TRADE_BLOWS), actor()),
            Outcome::Refused(_)
        ),
        "the third blow is the executor's refusal, exactly where the plaque said it would be"
    );
    assert_eq!(
        session.read_var("hp"),
        10,
        "the refusal committed nothing (anti-ghost)"
    );
}
