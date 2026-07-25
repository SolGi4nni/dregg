//! **The Descent's surface must SHOW the dungeon** — the map, the light, the carry ceiling.
//!
//! The native Descent's whole tension is three numbers (how much light is left, how much you may
//! still carry, whether the guardian has fallen) over one shape (four floors, eight relics, three
//! ways). For a long time the surface painted that as five prose lines and a menu: a stranger could
//! read every word and still not know where anything was.
//!
//! These are the tests that FAIL if the picture vanishes again. They assert the surface carries
//!
//!  * a [`ViewNode::CoordGrid`] of the shaft — one row per floor plus the pack and vault rows, one
//!    COLUMN PER RELIC, so a relic's custody is legible as a position rather than a number;
//!  * the light clock and the carry ceiling as literal [`ViewNode::Progress`] meters whose value
//!    and denominator are the real ones (the carry ceiling ATTENUATES with depth — that is the
//!    other half of the game and the meter has to move);
//!  * an alive/banked/dead status [`ViewNode::Pill`]; and
//!  * affordance labels that name what each move COSTS.
//!
//! …and that all of it survives the projection every button-less channel actually renders (the
//! shared `deos_view::text::render_text` walk that Telegram and WeChat paint), because a picture
//! that exists only in the HTML is a picture most of our players never see.

use deos_view::text::render_text;
use deos_view::{CoordCell, ViewNode};
use dreggnet_offerings::native_descent::{
    CARRY_CAP, DUNGEON_FLOORS, DUNGEON_RELICS, LIGHT_BREATH, NativeDescentOffering,
    NativeDescentSession, guardian_hp,
};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};
use dungeon_on_dregg::descent::{DELVE, LOOT, RELICS as DESCENT_RELICS, SMITE};

/// The map's column count — the row marker, the way, the guardian, then one column per relic.
const MAP_COLS: usize = 3 + DUNGEON_RELICS;
/// Four floor rows, the pack row, the vault row.
const MAP_ROWS: usize = DUNGEON_FLOORS as usize + 2;

fn actor() -> DreggIdentity {
    DreggIdentity("map-reader".to_string())
}

/// Fell the guardian standing on the session's current floor, however many blows that takes
/// TODAY, and hand back the relics minted here.
///
/// Both facts are DERIVED from the day's map rather than written down. These tests used to
/// smite exactly once and loot exactly relic 1 — true of the single hard-coded dungeon that
/// existed before the map became a function of the committed day-seed, and false on most of
/// the sixteen days that exist now. A literal that encodes a world-fact outlives the world.
fn fell_guardian_and_hoard(
    offering: &NativeDescentOffering,
    session: &mut NativeDescentSession,
) -> Vec<i64> {
    let world = session.game().day_world();
    let depth = session.game().sim().depth;
    for blow in 0..world.guard_hp(depth) {
        assert!(
            blow < 8,
            "a guardian that cannot be felled is a map bug, not a test bug"
        );
        land(offering, session, SMITE, 0);
    }
    let hoard: Vec<i64> = (0..DESCENT_RELICS)
        .filter(|&r| world.homes[r] == depth)
        .map(|r| r as i64)
        .collect();
    assert!(
        !hoard.is_empty(),
        "floor {depth} mints nothing on this day ({:?}); every floor is supposed to stay live",
        world.homes
    );
    hoard
}

fn land(
    offering: &NativeDescentOffering,
    session: &mut NativeDescentSession,
    turn: &str,
    arg: i64,
) {
    let action = offering
        .actions(session)
        .into_iter()
        .find(|a| a.turn == turn && a.arg == arg)
        .unwrap_or_else(|| panic!("the surface offers {turn}({arg})"));
    assert!(action.enabled, "{turn}({arg}) is playable here");
    assert!(
        matches!(
            offering.advance(session, action, actor()),
            Outcome::Landed { .. }
        ),
        "{turn}({arg}) lands"
    );
}

/// Collect every node of a kind, in walk order (the surface is a tree of sections).
fn collect<'a>(node: &'a ViewNode, out: &mut Vec<&'a ViewNode>, want: fn(&ViewNode) -> bool) {
    if want(node) {
        out.push(node);
    }
    match node {
        ViewNode::VStack(cs)
        | ViewNode::Row(cs)
        | ViewNode::List(cs)
        | ViewNode::Table(cs)
        | ViewNode::Section { children: cs, .. }
        | ViewNode::Grid { children: cs, .. } => {
            for c in cs {
                collect(c, out, want);
            }
        }
        ViewNode::Tabs { panels, .. } => {
            for p in panels {
                collect(p, out, want);
            }
        }
        ViewNode::Host { view: Some(v), .. } => collect(v, out, want),
        ViewNode::Adept(inner) => collect(inner, out, want),
        _ => {}
    }
}

fn the_map(surface: &ViewNode) -> (usize, Vec<CoordCell>) {
    let mut found = Vec::new();
    collect(surface, &mut found, |n| {
        matches!(n, ViewNode::CoordGrid { .. })
    });
    assert_eq!(
        found.len(),
        1,
        "the surface carries EXACTLY ONE board — the shaft"
    );
    match found[0] {
        ViewNode::CoordGrid { cols, cells } => (*cols, cells.clone()),
        _ => unreachable!(),
    }
}

/// Every meter on the surface, as `(label, value, max)`.
fn meters(surface: &ViewNode) -> Vec<(String, u64, u64)> {
    let mut found = Vec::new();
    collect(surface, &mut found, |n| {
        matches!(n, ViewNode::Progress { .. })
    });
    found
        .into_iter()
        .map(|n| match n {
            ViewNode::Progress { value, max, label } => (label.trim().to_string(), *value, *max),
            _ => unreachable!(),
        })
        .collect()
}

fn meter(surface: &ViewNode, label: &str) -> (u64, u64) {
    meters(surface)
        .into_iter()
        .find(|(l, _, _)| l == label)
        .map(|(_, v, m)| (v, m))
        .unwrap_or_else(|| panic!("the surface carries a `{label}` meter"))
}

fn pill_words(surface: &ViewNode) -> Vec<String> {
    let mut found = Vec::new();
    collect(surface, &mut found, |n| matches!(n, ViewNode::Pill { .. }));
    found
        .into_iter()
        .map(|n| match n {
            ViewNode::Pill { text, .. } => text.clone(),
            _ => unreachable!(),
        })
        .collect()
}

/// The cell at `(row, col)` of the map.
fn cell(cells: &[CoordCell], row: usize, col: usize) -> &CoordCell {
    &cells[row * MAP_COLS + col]
}

/// The map row a relic's glyph currently sits in, or `None` if it sits nowhere (which would be the
/// bug: every relic is always SOMEWHERE — a floor, the pack, or the vault).
fn relic_row(cells: &[CoordCell], relic: usize) -> Option<usize> {
    (0..MAP_ROWS).find(|row| cell(cells, *row, 3 + relic).glyph != "·")
}

#[test]
fn the_surface_paints_the_shaft_as_a_board_with_one_column_per_relic() {
    let offering = NativeDescentOffering::new();
    let session = offering.open(SessionConfig::with_seed(7)).expect("open");
    let surface = offering.render(&session);
    let (cols, cells) = the_map(surface.view());

    assert_eq!(cols, MAP_COLS, "marker + way + guardian + one per relic");
    assert_eq!(
        cells.len(),
        MAP_COLS * MAP_ROWS,
        "four floor rows, the pack row, the vault row"
    );

    // At genesis every relic lies at its HOME floor: the crown deepest, the way-keys and treasures
    // spread through the shaft. Each one is findable at its own column, in its floor's row.
    for relic in 0..DUNGEON_RELICS {
        let row = relic_row(&cells, relic)
            .unwrap_or_else(|| panic!("relic {relic} is SOMEWHERE on the map"));
        assert!(
            row < DUNGEON_FLOORS as usize,
            "at genesis relic {relic} still lies deep, not in the pack or the vault"
        );
    }
    // The crown is the deepest thing in the dungeon — the bottom floor's row.
    assert_eq!(
        relic_row(&cells, 0),
        Some(DUNGEON_FLOORS as usize - 1),
        "the crown lies on the bottom floor"
    );

    // The ways: floor 1 is the mouth (open); everything deeper starts shut.
    assert_eq!(cell(&cells, 0, 1).glyph, "/", "the mouth stands open");
    for floor in 1..DUNGEON_FLOORS as usize {
        assert_eq!(
            cell(&cells, floor, 1).glyph,
            "#",
            "the way into floor {} starts shut",
            floor + 1
        );
    }
}

#[test]
fn a_relic_travels_from_its_floor_into_the_pack_and_then_the_vault() {
    let offering = NativeDescentOffering::new();
    let mut session = offering.open(SessionConfig::with_seed(7)).expect("open");

    // Whatever THIS DAY mints on floor 1 is drawn lying on floor 1. (This used to name relic 1
    // specifically — the key to way 2 in the one hard-coded dungeon. The map is a function of
    // the day-seed now, so the test asserts the invariant instead of the old day's furniture.)
    let floor_one: Vec<usize> = (0..DESCENT_RELICS)
        .filter(|&r| session.game().day_world().homes[r] == 1)
        .collect();
    assert!(!floor_one.is_empty(), "floor 1 mints nothing on this day");
    let (_, cells) = the_map(offering.render(&session).view());
    for r in &floor_one {
        assert_eq!(relic_row(&cells, *r), Some(0), "relic {r} lies on floor 1");
    }

    land(&offering, &mut session, DELVE, 0);
    let hoard = fell_guardian_and_hoard(&offering, &mut session);
    let carried = hoard[0];
    land(&offering, &mut session, LOOT, carried);

    let (_, cells) = the_map(offering.render(&session).view());
    assert_eq!(
        relic_row(&cells, carried as usize),
        Some(DUNGEON_FLOORS as usize),
        "taken: the looted relic has moved OUT of the floor rows and into the PACK row"
    );
    assert_eq!(
        cell(&cells, DUNGEON_FLOORS as usize, 0).glyph,
        "@",
        "the pack row is marked as yours-but-losable"
    );

    // Climb out. The proved exit banks it: the same column, one row lower.
    let exit = offering
        .actions(&session)
        .into_iter()
        .find(|a| a.turn == "flee")
        .expect("the exit is offered");
    assert!(matches!(
        offering.advance(&mut session, exit, actor()),
        Outcome::Landed { .. }
    ));

    let (_, cells) = the_map(offering.render(&session).view());
    assert_eq!(
        relic_row(&cells, carried as usize),
        Some(DUNGEON_FLOORS as usize + 1),
        "banked: the relic we carried out sits in the VAULT row"
    );
    assert_eq!(
        cell(&cells, DUNGEON_FLOORS as usize + 1, 0).glyph,
        "$",
        "the vault row is marked as won"
    );
}

#[test]
fn the_map_lights_up_exactly_what_can_be_acted_on_now() {
    let offering = NativeDescentOffering::new();
    let mut session = offering.open(SessionConfig::with_seed(7)).expect("open");

    // On the surface the only lit thing is the mouth you may step through.
    let (_, cells) = the_map(offering.render(&session).view());
    assert!(cell(&cells, 0, 1).highlight, "the mouth is passable now");
    assert!(
        !cell(&cells, 0, 2).highlight,
        "you cannot strike a guardian you have not reached"
    );
    // Nothing is marked `you are here` yet — you are still above the shaft.
    assert!(
        (0..DUNGEON_FLOORS as usize).all(|row| cell(&cells, row, 0).glyph != ">"),
        "on the surface no floor claims to hold you"
    );

    // Down one floor: the guardian is lit (strikeable), the relics lying here are NOT (the guardian
    // stands, so the hoard is shut). This is the rule the picture must not lie about.
    land(&offering, &mut session, DELVE, 0);
    let (_, cells) = the_map(offering.render(&session).view());
    // WHERE YOU STAND is a glyph, never the highlight — the highlight means "actionable now", and
    // conflating the two makes the board's one accent mean two different things.
    assert_eq!(cell(&cells, 0, 0).glyph, ">", "floor 1 holds you");
    assert!(
        !cell(&cells, 0, 0).highlight,
        "standing somewhere is not a move, so the marker is not lit"
    );
    assert!(cell(&cells, 0, 2).highlight, "the guardian may be struck");
    for relic in 0..DUNGEON_RELICS {
        if relic_row(&cells, relic) == Some(0) {
            assert!(
                !cell(&cells, 0, 3 + relic).highlight,
                "relic {relic} is not takeable while the guardian stands"
            );
        }
    }

    // Fell it: now the floor's hoard lights up and the guardian reads as slain.
    let _hoard = fell_guardian_and_hoard(&offering, &mut session);
    let (_, cells) = the_map(offering.render(&session).view());
    assert_eq!(cell(&cells, 0, 2).glyph, "x", "the guardian has fallen");
    let lit: Vec<usize> = (0..DUNGEON_RELICS)
        .filter(|r| relic_row(&cells, *r) == Some(0) && cell(&cells, 0, 3 + r).highlight)
        .collect();
    assert!(
        !lit.is_empty(),
        "with the guardian down, the floor's hoard is lit for the taking"
    );
}

#[test]
fn the_light_clock_and_the_attenuating_carry_ceiling_are_real_meters() {
    let offering = NativeDescentOffering::new();
    let mut session = offering.open(SessionConfig::with_seed(7)).expect("open");

    let surface = offering.render(&session);
    assert_eq!(
        meter(surface.view(), "light"),
        (LIGHT_BREATH, LIGHT_BREATH),
        "a fresh run's light is full — and it is REMAINING light, so the bar EMPTIES as it burns"
    );
    assert_eq!(
        meter(surface.view(), "pack"),
        (0, CARRY_CAP),
        "on the surface you may carry the full cap"
    );
    assert!(
        meters(surface.view())
            .iter()
            .all(|(label, _, _)| label != "guardian"),
        "there is no guardian on the surface, so no guardian meter is invented"
    );

    // One step down costs one light AND one point of carrying rights (`pack + depth <= CAP`).
    land(&offering, &mut session, DELVE, 0);
    let surface = offering.render(&session);
    assert_eq!(
        meter(surface.view(), "light"),
        (LIGHT_BREATH - 1, LIGHT_BREATH),
        "the clock moved"
    );
    assert_eq!(
        meter(surface.view(), "pack"),
        (0, CARRY_CAP - 1),
        "the carry CEILING attenuated with depth — the meter's denominator moves too"
    );
    assert_eq!(
        meter(surface.view(), "guardian"),
        (0, guardian_hp(1)),
        "a floor's guardian gets a vitality meter against its real hp"
    );
}

#[test]
fn the_status_pill_reads_delving_then_banked() {
    let offering = NativeDescentOffering::new();
    let mut session = offering.open(SessionConfig::with_seed(7)).expect("open");
    assert_eq!(
        pill_words(offering.render(&session).view()),
        vec!["DELVING".to_string()],
        "a live run wears one status badge"
    );

    let exit = offering
        .actions(&session)
        .into_iter()
        .find(|a| a.turn == "flee")
        .expect("the exit is offered");
    assert!(matches!(
        offering.advance(&mut session, exit, actor()),
        Outcome::Landed { .. }
    ));
    assert_eq!(
        pill_words(offering.render(&session).view()),
        vec!["BANKED".to_string()],
        "a settled run says so in one word"
    );
}

#[test]
fn every_affordance_names_what_it_costs() {
    let offering = NativeDescentOffering::new();
    let session = offering.open(SessionConfig::with_seed(7)).expect("open");
    let actions: Vec<Action> = offering.actions(&session);
    assert!(!actions.is_empty());
    for action in &actions {
        assert!(
            action.label.contains(" light"),
            "the move `{}` must tell a newcomer what it burns: {:?}",
            action.turn,
            action.label
        );
    }
    let smite = actions
        .iter()
        .find(|a| a.turn == "smite")
        .expect("striking is in the vocabulary");
    assert!(
        smite.label.contains("2 light"),
        "striking costs two — the one move that is not a single light: {:?}",
        smite.label
    );
}

/// The picture has to survive the projection the BUTTON-LESS channels paint (Telegram's message
/// body, WeChat's reply block). This is the test that fails if the map or the meters become a
/// web-only luxury.
#[test]
fn the_map_and_the_meters_survive_the_shared_prose_projection() {
    let offering = NativeDescentOffering::new();
    let mut session = offering.open(SessionConfig::with_seed(7)).expect("open");
    land(&offering, &mut session, DELVE, 0);
    let hoard = fell_guardian_and_hoard(&offering, &mut session);
    let carried = hoard[0];
    land(&offering, &mut session, LOOT, carried);

    let text = render_text(offering.render(&session).view());

    // The meters, as the shared glyph bar.
    assert!(
        text.contains('█') && text.contains('░'),
        "the meters paint a real bar in prose, not a bare ratio:\n{text}"
    );
    assert!(
        text.contains(&format!("/{LIGHT_BREATH}")),
        "the light clock names its ceiling:\n{text}"
    );

    // The board, as the shared text grid: six rows, each `MAP_COLS` cells of three characters, and
    // nothing in them but the map's own alphabet (so a prose line of the same length is not
    // mistaken for a board row).
    const MAP_ALPHABET: &str = " []·>/#GxCk*@$1234";
    let rows: Vec<&str> = text
        .lines()
        .filter(|line| {
            line.chars().count() == MAP_COLS * 3 && line.chars().all(|c| MAP_ALPHABET.contains(c))
        })
        .collect();
    assert_eq!(
        rows.len(),
        MAP_ROWS,
        "the whole shaft reaches the prose channels:\n{text}"
    );
    assert!(
        rows[DUNGEON_FLOORS as usize].contains('@'),
        "the pack row reaches them too:\n{text}"
    );
    // The legend is what makes the glyphs mean anything to a first-time reader.
    assert!(
        text.contains("open way") && text.contains("crown"),
        "the legend rides along:\n{text}"
    );
}
