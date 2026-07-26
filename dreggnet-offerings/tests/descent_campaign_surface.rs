//! **The campaign surface must look like the game it wraps.**
//!
//! `descent-campaign` opens a real native Descent per region location — the SAME `Sim` the native
//! Descent surface paints as a shaft board, four meters and ⚠ pressure lines. It used to render
//! that as `depth 2 · light spent 9 · wounds 1 · native turn 14` plus one menu: a flat counter dump
//! beside a vocabulary that already existed one module away.
//!
//! These are the tests that fail if it drifts back. They assert
//!
//!  * the campaign surface carries the NATIVE Descent's own nodes — the shaft [`ViewNode::CoordGrid`]
//!    and its light / pack / banked meters — and not a second description of the same state;
//!  * the region's progress is a meter too, with the real denominator;
//!  * the standing plaque names ONE thing to do right now, and it changes with the phase;
//!  * the travel rule is READ OUT OF THE DEPLOYED REGION PROGRAM (the `FieldGte` on the
//!    prerequisite's cleared flag), so the sentence a traveller reads is the predicate the executor
//!    will admit the turn under;
//!  * and all of it survives the text projection every button-less channel renders.

use deos_view::ViewNode;
use deos_view::text::render_text;
use dreggnet_offerings::campaign::DescentCampaignOffering;
use dreggnet_offerings::{Offering, SessionConfig};
use dungeon_on_dregg::descent::{DELVE, SMITE};

fn painted(session: &<DescentCampaignOffering as Offering>::Session) -> String {
    let offering = DescentCampaignOffering::new();
    render_text(offering.render(session).view())
}

fn opened() -> (
    DescentCampaignOffering,
    <DescentCampaignOffering as Offering>::Session,
) {
    let offering = DescentCampaignOffering::new();
    let session = offering
        .open(SessionConfig::with_seed(5))
        .expect("the campaign opens");
    (offering, session)
}

/// Every [`ViewNode::Progress`] in a tree, as `(label, value, max)`.
fn meters(node: &ViewNode) -> Vec<(String, u64, u64)> {
    let mut out = Vec::new();
    fn walk(node: &ViewNode, out: &mut Vec<(String, u64, u64)>) {
        match node {
            ViewNode::Progress { value, max, label } => {
                out.push((label.trim().to_string(), *value, *max))
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

/// The number of cells in the first [`ViewNode::CoordGrid`] found, with its column count.
fn board(node: &ViewNode) -> Option<(usize, usize)> {
    match node {
        ViewNode::CoordGrid { cols, cells } => Some((*cols, cells.len())),
        ViewNode::VStack(kids)
        | ViewNode::Row(kids)
        | ViewNode::List(kids)
        | ViewNode::Table(kids)
        | ViewNode::Section { children: kids, .. }
        | ViewNode::Grid { children: kids, .. } => kids.iter().find_map(board),
        _ => None,
    }
}

/// ⚑ **The campaign shows the DUNGEON, because it reuses the Descent's own painters.**
#[test]
fn the_campaign_carries_the_native_descents_shaft_and_meters() {
    let (offering, session) = opened();
    let surface = offering.render(&session);

    let (cols, cells) = board(surface.view()).expect("the campaign paints the shaft board");
    assert!(
        cols >= 4,
        "the shaft is a real coordinate board: {cols} cols"
    );
    assert_eq!(
        cells % cols,
        0,
        "the board is rectangular: {cells} cells over {cols} columns"
    );

    let bars = meters(surface.view());
    for expected in ["light", "pack", "banked"] {
        assert!(
            bars.iter().any(|(label, _, _)| label == expected),
            "the campaign carries the Descent's `{expected}` meter, not a bare integer: {bars:?}"
        );
    }
    // …and the region's own progress, with the map's real location count as the denominator.
    let region = bars
        .iter()
        .find(|(label, _, _)| label == "crowned")
        .expect("the region's progress is a meter");
    assert_eq!(
        (region.1, region.2 as usize),
        (0, offering.map().locations.len()),
        "nothing is crowned yet, out of the real map size"
    );

    // The counter dump is GONE — the state is read off the meters and the board now.
    let text = render_text(surface.view());
    assert!(
        !text.contains("light spent"),
        "the flat counter dump must not come back: {text}"
    );
}

/// **The standing plaque says ONE thing to do right now, and it tracks the phase.** An unopened
/// location tells the traveller what actually clears it; the surface never leaves the objective to
/// be inferred from a menu.
#[test]
fn the_standing_plaque_names_the_one_thing_to_do_now() {
    let (offering, mut session) = opened();
    let genesis = painted(&session);
    assert!(
        genesis.contains("EXPEDITION LIVE"),
        "the phase is a pill, not a guess: {genesis}"
    );
    assert!(
        genesis.contains("Carry the Crown of the Deep out of"),
        "the directive names the ONE thing that clears a location: {genesis}"
    );
    assert!(
        genesis.contains("Where the campaign stands"),
        "the standing plaque is present: {genesis}"
    );

    // A landed native move keeps the plaque live and moves the expedition's own reading.
    let delve = offering
        .actions(&session)
        .into_iter()
        .find(|action| action.turn == DELVE)
        .expect("the campaign offers the native delve");
    assert!(
        matches!(
            offering.advance(
                &mut session,
                delve,
                dreggnet_offerings::DreggIdentity("traveller".into())
            ),
            dreggnet_offerings::Outcome::Landed { .. }
        ),
        "the delve lands as a real campaign event"
    );
    let after = painted(&session);
    assert!(
        after.contains("floor 1 of"),
        "the expedition's own standing moved with it: {after}"
    );
    assert!(
        offering
            .actions(&session)
            .iter()
            .any(|action| action.turn == SMITE),
        "the next native move is still offered"
    );
    // ⚑ The native labels are passed through UNPREFIXED — a chat frontend truncates a button at 78
    // characters, and `"{location} · {verb}"` put the verb past the cut.
    assert!(
        offering
            .actions(&session)
            .iter()
            .all(|action| !action.label.starts_with("The Warden's Keep ·")),
        "the location prefix that ate the verb must not come back"
    );
}

/// ⚑ **The travel rule is READ OFF THE DEPLOYED REGION PROGRAM.**
///
/// The road onward is barred by a real `FieldGte(cleared[prereq], 1)` on the region cell, and the
/// plaque quotes that guard rather than retyping the topology — so a threshold or a prerequisite
/// edited in the region wiring moves the page. This asserts the guard reaches the traveller by NAME
/// and by THRESHOLD, and that a barred road reads as barred.
#[test]
fn the_travel_gate_on_the_plaque_is_the_deployed_one() {
    let (_offering, session) = opened();
    let text = painted(&session);

    assert!(
        text.contains("How a road opens"),
        "the domain plaque is present: {text}"
    );
    assert!(
        text.contains("cleared[keep] ≥ 1"),
        "the deployed FieldGte guard reaches the traveller verbatim: {text}"
    );
    assert!(
        text.contains("BARRED"),
        "an unmet gate reads as barred, not merely absent: {text}"
    );
    assert!(
        text.contains("NOT crowned"),
        "…and says WHICH prerequisite is missing: {text}"
    );
    // The rule that actually clears a location — the thing a player cannot read off the shaft.
    assert!(
        text.contains("Crown of the Deep") && text.contains("exact native replay"),
        "the clear rule is stated where the traveller needs it: {text}"
    );
    // The public promise the campaign has always carried, kept.
    assert!(
        text.contains("no scripted completion"),
        "the surface still says the campaign is player-driven: {text}"
    );
}
