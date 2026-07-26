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
    CARRY_CAP, DUNGEON_DAYS, DUNGEON_FLOORS, DUNGEON_RELICS, LIGHT_ASCEND, LIGHT_BREATH,
    LIGHT_FLEE, NativeDescentOffering, NativeDescentSession,
};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};
use dungeon_on_dregg::descent::{ASCEND, DELVE, LOOT, LUNGE, RELICS as DESCENT_RELICS, SMITE};

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

    // ⚑ CLIMB, then bank. `flee` is illegal below the surface now, so the way out is a
    // real move that costs a light — the relic is still LOSABLE while you are down here.
    land(&offering, &mut session, ASCEND, 0);

    // The proved exit banks it: the same column, one row lower.
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
        (0, session.day_world().guard_hp(1)),
        "a floor's guardian gets a vitality meter against its real hp — THIS DAY's, off the run's \
         own drawn map, not the day-0 table"
    );
}

/// ⚑ **A LUNGE MOVES THE CARRY CEILING, AND THE METER HAS TO MOVE WITH IT.**
///
/// The capacity law the mover enforces is `pack + depth + harm ≤ CAP` — `Sim::delve`,
/// `Sim::lunge` and `Sim::loot` in `dungeon_on_dregg::descent` each refuse on exactly that sum.
/// The surface's denominator was `CAP - depth`, dropping `harm` entirely, so after a lunge the
/// pack meter showed the player one more slot than the dungeon would give them — and it did so in
/// the one state where the number is being used to decide something (a guardian just felled, its
/// hoard just lit).
///
/// Both halves are pinned, and the second is what makes this non-vacuous: a fix that simply
/// stopped painting the meter, or one that shrank the ceiling by a constant, fails the `loot`
/// agreement below.
#[test]
fn a_lunge_forfeits_a_carry_slot_and_the_pack_meter_says_so() {
    let offering = NativeDescentOffering::new();
    let mut session = offering.open(SessionConfig::with_seed(7)).expect("open");

    land(&offering, &mut session, DELVE, 0);
    let before = meter(offering.render(&session).view(), "pack");
    assert_eq!(
        before,
        (0, CARRY_CAP - 1),
        "on floor one the ceiling is down by the one floor and nothing else"
    );

    // The lunge: the same wound as a press for one light instead of two, paid with `harm += 1`.
    land(&offering, &mut session, LUNGE, 0);
    let sim = session.game().sim();
    assert_eq!(sim.harm, 1, "the lunge broke the grip");
    assert_eq!(sim.depth, 1, "and it did not move the run");

    assert_eq!(
        meter(offering.render(&session).view(), "pack"),
        (0, CARRY_CAP - 1 - 1),
        "the forfeited carry slot is GONE from the meter's denominator — `pack + depth + harm ≤ \
         CAP`, not `pack + depth ≤ CAP`"
    );

    // …and the ceiling the meter PAINTS is the ceiling the MOVER ENFORCES. Checked as a
    // biconditional on real relics rather than by filling the pack to the brim: whether the
    // dungeon admits the take must be exactly whether the bar still has room, at every step. This
    // is the half that cannot pass by accident — under the old `CAP - depth` denominator the two
    // sides disagree the moment `harm` is non-zero.
    let world = session.game().day_world();
    for blow in 1..world.guard_hp(1) {
        assert!(blow < 8, "a guardian that cannot be felled is a map bug");
        land(&offering, &mut session, SMITE, 0);
    }
    let hoard: Vec<usize> = (0..DESCENT_RELICS)
        .filter(|&r| world.homes[r] == 1)
        .collect();
    assert!(
        !hoard.is_empty(),
        "floor one mints a hoard on this day; a floor that mints nothing is a map bug"
    );
    let mut checked = 0usize;
    for relic in hoard {
        let (carried, ceiling) = meter(offering.render(&session).view(), "pack");
        let dungeon_admits = session.game().sim().loot(relic).is_ok();
        assert_eq!(
            dungeon_admits,
            carried < ceiling,
            "the pack meter reads {carried}/{ceiling} and the dungeon {} relic {relic} — the bar \
             and the capacity law must agree at every step, or the bar is showing room the run \
             does not have",
            if dungeon_admits { "ACCEPTS" } else { "REFUSES" }
        );
        checked += 1;
        if dungeon_admits {
            land(&offering, &mut session, LOOT, relic as i64);
        }
    }
    assert!(
        checked > 0,
        "the agreement check ran on no relic at all — it would have passed vacuously"
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
    //
    // ⚑ The alphabet includes EVERY bracket `deos_view::coordgrid_text` can put around a cell, not
    // just `[ ]`: the shared projection now paints the cell's ROLE from its `tag` as well as its
    // `highlight`, so a way-key relic (tagged `warn`) that is carried or lootable reads `(k)`. With
    // only `[]` here the row carrying it silently stopped matching and `rows.len()` fell short of
    // `MAP_ROWS` — i.e. this filter would have reported the shaft as MISSING from the prose. Kept
    // as a literal set rather than "any punctuation" so a genuinely stray glyph still fails.
    const MAP_ALPHABET: &str = " []{}()-*·>/#GxCk@$1234";
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

/// **THE WAY HOME IS PRICED, AND THE DOOMED RUN IS TOLD.**
///
/// `flee` demands the surface and the climb buys one floor at a time, so the light a run may
/// actually SPEND is what is left minus `depth` climbs plus the exit. The surface used to say
/// "climbing out costs 1" from any depth — the exit's price ALONE — which reads as three spare
/// breaths to a player standing on floor 3 holding four, and that is precisely the position that
/// strands a run for good. Worse, the status word read DELVING right through the window Lean proves
/// can never bank from any continuation whatsoever (`Dungeon.doomed_never_banks`).
#[test]
fn the_surface_prices_the_climb_home_and_names_a_stranded_run() {
    let offering = NativeDescentOffering::new();
    let mut session = offering.open(SessionConfig::with_seed(7)).expect("open");
    land(&offering, &mut session, DELVE, 0);

    // Floor 1 is one climb PLUS the exit — derived from the posted prices, so a re-priced verb moves
    // the expectation with the surface instead of leaving a stale literal behind.
    let text = render_text(offering.render(&session).view());
    let from_floor_one = LIGHT_ASCEND + LIGHT_FLEE;
    assert!(
        text.contains(&format!("the way home costs {from_floor_one} light")),
        "standing below ground the surface must price the CLIMB, not the exit alone:\n{text}"
    );

    // Burn the clock without going anywhere: up, down, up, down. Each cycle costs two light and
    // leaves the run on floor 1, so it walks into the window where the climb can no longer be paid.
    // The loop is driven by the STATUS rather than a move count, so it cannot assert about a state
    // the run never reached.
    let mut moves = 0;
    while pill_words(offering.render(&session).view()) == vec!["DELVING".to_string()] {
        assert!(
            moves < 40,
            "the clock is not burning down after {moves} moves"
        );
        let up = session.game().sim().depth > 0;
        land(&offering, &mut session, if up { ASCEND } else { DELVE }, 0);
        moves += 1;
    }

    assert_eq!(
        pill_words(offering.render(&session).view()),
        vec!["STRANDED".to_string()],
        "a run whose light cannot buy the climb is already over, and the badge said DELVING"
    );
    // ⚑ NON-VACUOUS: STRANDED is the ALIVE-but-doomed window. If nothing were legal here this would
    // just be the light dying, and the new state would be telling nobody anything new.
    assert!(
        offering.actions(&session).iter().any(|a| a.enabled),
        "STRANDED must name the window where the run can still MOVE and still cannot get home"
    );
    let text = render_text(offering.render(&session).view());
    assert!(
        text.contains("Nothing in the pack will ever be banked."),
        "the doomed run is told in prose rather than left to be inferred from a number:\n{text}"
    );
}

/// **A RELIC'S NAME IS A NOUN.** `relic_label` returned the LOOT button's imperative, and three
/// readers used it as a name: the pack and vault lines read `carried: Take the key-relic for way 2`
/// and the minted-note list read `Take treasure relic 4 (rare) 3f9c…`. A player cannot tell the
/// story of a run whose relics are verbs.
#[test]
fn a_relic_is_named_as_a_thing_in_the_pack_and_as_a_verb_on_the_button() {
    let offering = NativeDescentOffering::new();
    let mut session = offering.open(SessionConfig::with_seed(7)).expect("open");
    land(&offering, &mut session, DELVE, 0);
    let hoard = fell_guardian_and_hoard(&offering, &mut session);
    land(&offering, &mut session, LOOT, hoard[0]);

    let text = render_text(offering.render(&session).view());
    let carried = text
        .lines()
        .find(|line| line.starts_with("carried:"))
        .expect("the record names what is in the pack");
    assert_ne!(carried, "carried: none", "a relic was just taken");
    assert!(
        !carried.contains("Take "),
        "the pack is a list of THINGS, not of the buttons that took them: {carried:?}"
    );
    assert!(
        !carried.contains("relic "),
        "a treasure in the pack has a name, not an index: {carried:?}"
    );
    // And the BUTTON is still a verb — the split is real, not a rename in one direction.
    assert!(
        offering
            .actions(&session)
            .iter()
            .filter(|action| action.turn == LOOT)
            .all(|action| action.label.contains("Take the ")),
        "every loot row still reads as an instruction"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// THE GUARDIAN IS A DAY FACT
//
// The map is drawn from the committed day-seed: which floor each relic is minted on, and how much
// vitality each floor's guardian carries. `descent::guard_hp` is DAY 0's table. Every surface
// number that quoted it was right on one day in sixteen — a `0/1` meter under a guardian that
// takes two blows, a glyph that reads SLAIN while the hoard is still shut, and a pressure line
// that prices the toll at half. These are the tests that fail if any of that comes back.
// ═══════════════════════════════════════════════════════════════════════════════

/// Day 0's floor-`depth` guardian — the number the surface used to quote unconditionally.
fn day_zero_guard_hp(depth: u64) -> u64 {
    dungeon_on_dregg::descent::CANON_WORLD.guard_hp(depth)
}

/// **The draw MUST actually vary guardian vitality.** If it does not, every "day-aware guardian"
/// claim in this crate is decoration over a constant, which is a bigger finding than the display
/// bug the next test guards — so say it loudly rather than passing vacuously.
#[test]
fn the_committed_day_seed_really_does_vary_guardian_vitality() {
    let differing: Vec<(usize, u64, u64, u64)> = (0..DUNGEON_DAYS)
        .flat_map(|day| {
            let world = dungeon_on_dregg::descent::day_world(day);
            (1..=DUNGEON_FLOORS).filter_map(move |floor| {
                let hp = world.guard_hp(floor);
                (hp != day_zero_guard_hp(floor)).then_some((
                    day,
                    floor,
                    hp,
                    day_zero_guard_hp(floor),
                ))
            })
        })
        .collect();
    assert!(
        !differing.is_empty(),
        "NO drawn day gives ANY floor a guardian vitality different from day 0's. The day-seed is \
         then not varying guardian vitality at all, and every day-aware guardian accessor in this \
         crate is ceremony over one constant — a bigger finding than the surface bug this suite \
         guards. Read `dungeon-on-dregg/program/dungeon_program.json`'s `ghp` arrays before \
         weakening this assertion."
    );
    // And the floor-1 case specifically, because that is the floor a player meets first and the
    // one the surface test below stands on.
    assert!(
        differing.iter().any(|(_, floor, _, _)| *floor == 1),
        "no drawn day changes FLOOR 1's guardian; the first guardian a player ever meets is the \
         same every day, so the surface bug this suite guards would be unobservable there: \
         {differing:?}"
    );
}

/// A deploy seed whose drawn map arms floor 1 with a vitality that is NOT day 0's, and that
/// vitality. SEARCHED, never written down — the map is a function of the committed day-seed and a
/// literal that encodes a world-fact outlives the world.
fn seed_whose_first_guardian_is_not_day_zeros(offering: &NativeDescentOffering) -> (u64, u64) {
    // 251 is the whole normalized deploy-seed space (`Offering::open` folds `n % 251 + 1`).
    for seed in 0..251u64 {
        let hp = offering
            .day_world_for_seed(seed)
            .expect("a seed-derived offering resolves a map for every seed")
            .guard_hp(1);
        if hp != day_zero_guard_hp(1) {
            return (seed, hp);
        }
    }
    panic!(
        "no deploy seed in the whole 0..251 space draws a floor-1 guardian differing from day 0's \
         ({}), even though some drawn day does. The seed → day-index reduction is then not \
         covering the family and this suite cannot observe the bug it exists to catch.",
        day_zero_guard_hp(1)
    );
}

/// **THE FALSIFIER.** On a day whose first guardian is not day 0's, the guardian meter, the map
/// glyph, and the pressure line must all agree with `day_world().guard_hp(1)`.
///
/// Against the old surface (which read the free `descent::guard_hp`) every one of these fails:
/// the meter is denominated `1`, one blow flips the glyph to SLAIN while the hoard stays shut, and
/// the pressure line offers to open the floor for one strike and two light. Against the fixed
/// surface they are the day's own numbers.
#[test]
fn the_guardian_meter_and_the_strike_affordance_read_this_days_vitality() {
    let offering = NativeDescentOffering::new();
    let (seed, hp) = seed_whose_first_guardian_is_not_day_zeros(&offering);
    let mut session = offering.open(SessionConfig::with_seed(seed)).expect("open");
    assert_eq!(
        session.day_world().guard_hp(1),
        hp,
        "the session opened on the map the offering published for this seed"
    );
    assert_ne!(
        hp,
        day_zero_guard_hp(1),
        "this day's guardian is not day 0's"
    );

    land(&offering, &mut session, DELVE, 0);

    // ── The meter. Denominated in TODAY's vitality. ──
    let surface = offering.render(&session);
    assert_eq!(
        meter(surface.view(), "guardian"),
        (0, hp),
        "the guardian meter is sized against the guardian the executor will make this run fight"
    );

    // ── The pressure line. It prices the toll in strikes AND in light, and both are day facts. ──
    let text = render_text(surface.view());
    assert!(
        text.contains(&format!("{hp} more strikes, {} light", hp * 2)),
        "the pressure line owes {hp} strikes at 2 light each on this day:\n{text}"
    );

    // ── The affordance. One blow short of the toll the guardian STILL stands: the glyph must not
    //    read slain, and the floor's hoard must not light up. This is the half a player pays for.
    //    The glyph is the blows it STILL OWES, so it counts down as you press — the board used to
    //    paint a flat `G` on every floor, which said an enemy was there and never what it cost.
    for blow in 1..hp {
        land(&offering, &mut session, SMITE, 0);
        let (_, cells) = the_map(offering.render(&session).view());
        assert_eq!(
            cell(&cells, 0, 2).glyph,
            (hp - blow).to_string(),
            "after {blow} of {hp} blows the guardian owes {} more and the map must say so",
            hp - blow
        );
        let lit: Vec<usize> = (0..DUNGEON_RELICS)
            .filter(|r| relic_row(&cells, *r) == Some(0) && cell(&cells, 0, 3 + r).highlight)
            .collect();
        assert!(
            lit.is_empty(),
            "after {blow} of {hp} blows the hoard is still shut, so nothing on floor 1 may be lit \
             for the taking: {lit:?}"
        );
    }

    // ── The last blow. Now, and only now, the glyph falls and the hoard opens. ──
    land(&offering, &mut session, SMITE, 0);
    let (_, cells) = the_map(offering.render(&session).view());
    assert_eq!(cell(&cells, 0, 2).glyph, "x", "the {hp}th blow fells it");
    let lit: Vec<usize> = (0..DUNGEON_RELICS)
        .filter(|r| relic_row(&cells, *r) == Some(0) && cell(&cells, 0, 3 + r).highlight)
        .collect();
    assert!(
        !lit.is_empty(),
        "with the guardian down the floor's hoard is lit for the taking"
    );
    let text = render_text(offering.render(&session).view());
    assert!(
        !text.contains("the guardian stands"),
        "a felled guardian is not still standing in the prose:\n{text}"
    );
}

/// **The map a surface PUBLISHES for a seed is the map a session OPENED on that seed.**
///
/// `day_world_for_seed` exists so the browser play page can size its guardian meter before (and
/// beside) a session. If it and `Offering::open` ever resolved through different normalizations or
/// different day bindings, the page would draw one dungeon while the executor refereed another —
/// which is exactly the bug this whole section is about, moved one layer out.
#[test]
fn the_published_day_world_is_the_one_a_session_plays() {
    for offering in [
        NativeDescentOffering::new(),
        NativeDescentOffering::on_day(procgen_dregg::CommittedSeed::from_bytes([7u8; 32])),
    ] {
        for seed in 0..251u64 {
            let published = offering.day_world_for_seed(seed).expect("a map resolves");
            let session = offering.open(SessionConfig::with_seed(seed)).expect("open");
            assert_eq!(
                published,
                session.day_world(),
                "seed {seed}: the published map and the deployed map are the same dungeon"
            );
        }
    }
}
