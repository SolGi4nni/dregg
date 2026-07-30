//! Cross-surface play ordering for the Lean-authored native Descent.
//!
//! Web forms, Telegram keyboards, Discord buttons, and the native browser controller all consume
//! the Offering's action list in order. The executor remains the referee and the complete locked
//! action vocabulary stays visible; this test pins only the player-facing priority bands.

use std::collections::BTreeSet;

use dreggnet_offerings::native_descent::NativeDescentOffering;
use dreggnet_offerings::{DreggIdentity, Offering, Outcome, SessionConfig};
use dungeon_on_dregg::descent::{
    ASCEND, DELVE, FLEE, FLOORS, LOOT, LUNGE, RELICS, SMITE, TAKE, UNLOCK,
};

/// **The complete anti-ghost vocabulary** — every verb the native Descent wire speaks, expanded
/// over its whole argument domain, locked entries included.
///
/// The argument fan-out is DERIVED from the world's shape (`FLOORS` ways, `RELICS` relic columns).
/// This assertion used to be the literal `15`; the arrival of one new verb turned it red while
/// saying nothing about what changed, and a bare count could never have told a missing relic
/// column from a duplicated one. The VERB ROSTER stays written down deliberately — "the locked
/// catalogue remains visible" is the claim this test exists to make, and deriving the roster from
/// the surface's own output would make it a tautology. It is a list of the crate's exported verb
/// constants, so a new verb is a legible edit here rather than a mystery integer.
fn complete_vocabulary() -> BTreeSet<(&'static str, i64)> {
    [(DELVE, 0), (SMITE, 0), (LUNGE, 0), (ASCEND, 0), (FLEE, 0)]
        .into_iter()
        .chain((2..=FLOORS).map(|way| (UNLOCK, way as i64)))
        .chain((0..RELICS).map(|relic| (LOOT, relic as i64)))
        // ⚑ AND THE LIFT. Only the three WAY-KEYS can hang in a door (`unlock` is the only
        // verb that writes a `HUNG + d` code, and it writes it over `keyFor w`), so the
        // catalogue offers `take` over exactly those three and no others — a `take` naming the
        // crown or a treasure is a stale control, not a locked affordance.
        .chain((1..FLOORS).map(|relic| (TAKE, relic as i64)))
        .collect()
}

fn land(
    offering: &NativeDescentOffering,
    session: &mut dreggnet_offerings::native_descent::NativeDescentSession,
    actor: &DreggIdentity,
    turn: &str,
    arg: i64,
) {
    let action = offering
        .actions(session)
        .into_iter()
        .find(|action| action.turn == turn && action.arg == arg)
        .unwrap_or_else(|| panic!("missing {turn}({arg})"));
    assert!(action.enabled, "{turn}({arg}) should be playable");
    assert!(
        matches!(
            offering.advance(session, action, actor.clone()),
            Outcome::Landed { .. }
        ),
        "{turn}({arg}) should land"
    );
}

#[test]
fn enabled_moves_lead_locked_catalogue_and_exit_follows_nonterminal_play() {
    let offering = NativeDescentOffering::new();
    let mut session = offering.open(SessionConfig::with_seed(99)).expect("open");
    let actor = DreggIdentity("cross-surface-player".to_string());

    let fresh = offering.actions(&session);
    let advertised: BTreeSet<(&str, i64)> = fresh
        .iter()
        .map(|action| (action.turn.as_str(), action.arg))
        .collect();
    assert_eq!(
        advertised,
        complete_vocabulary(),
        "the complete anti-ghost vocabulary remains — every verb over every way and every relic"
    );
    assert_eq!(
        fresh.len(),
        advertised.len(),
        "and nothing is advertised twice"
    );
    assert_eq!(fresh[0].turn, DELVE);
    assert_eq!(fresh[1].turn, FLEE);
    assert!(fresh[..2].iter().all(|action| action.enabled));
    assert!(fresh[2..].iter().all(|action| !action.enabled));
    // ⚑ ON THE SURFACE the climb is the one thing you cannot do — you are already home.
    assert!(
        fresh
            .iter()
            .any(|action| action.turn == ASCEND && !action.enabled),
        "the climb is catalogued but locked at depth 0"
    );
    // The exit names WHAT IT BANKS and WHAT IT COSTS — an irreversible move a newcomer can weigh.
    assert_eq!(fresh[1].label, "⌂ Bank nothing and end the run · 1 light");

    // Kill floor one's guardian. Every relic MINTED ON THIS FLOOR becomes legal, and all of them
    // must be shown before the irreversible-but-legal exit, with locked actions still visible
    // after it.
    //
    // Both the blow count and the expected spoils are DERIVED FROM THE DAY'S MAP, not written
    // down. They used to be the literals `1` smite and `vec![1, 4, 5]`, which were facts about the
    // one hard-coded dungeon that existed before the map became a function of the committed
    // day-seed. This session opens on seed 99, which draws a different day — so the literals began
    // asserting the layout of a dungeon nobody is playing. Deriving them pins the INVARIANT that
    // actually matters ("felling the guardian unlocks exactly this floor's mints, in order") and
    // keeps the test honest on all sixteen days instead of one.
    land(&offering, &mut session, &actor, DELVE, 0);
    let world = session.game().day_world();
    let floor = 1_u64;
    for blow in 0..world.guard_hp(floor) {
        assert!(
            blow < 8,
            "a guardian that cannot be felled is a map bug, not a test bug"
        );
        land(&offering, &mut session, &actor, SMITE, 0);
    }
    let mut expected_loot: Vec<i64> = (0..RELICS)
        .filter(|&relic| world.homes[relic] == floor)
        .map(|relic| relic as i64)
        .collect();
    expected_loot.sort_unstable();
    assert!(
        !expected_loot.is_empty(),
        "day {:?} mints nothing on floor {floor}; the draw is supposed to keep every floor live",
        world.homes
    );

    // ⚑ BELOW THE SURFACE THE EXIT IS LOCKED. `flee` demands `depth = 0`, so the way out
    // of floor 1 is the CLIMB — and it costs a light. The enabled band is therefore "this
    // floor's spoils plus the climb", and the exit has moved down into the locked
    // catalogue where a player can still see what it will do without being able to do it.
    let spoils = offering.actions(&session);
    let boundary = spoils
        .iter()
        .position(|action| !action.enabled)
        .unwrap_or(spoils.len());
    let mut playable_loot: Vec<_> = spoils[..boundary]
        .iter()
        .filter(|action| action.turn == LOOT)
        .map(|action| action.arg)
        .collect();
    playable_loot.sort_unstable();
    assert_eq!(playable_loot, expected_loot);
    assert!(spoils[..boundary].iter().all(|action| action.enabled));
    assert!(spoils[boundary..].iter().all(|action| !action.enabled));
    assert!(
        spoils[..boundary]
            .iter()
            .any(|action| action.turn == ASCEND),
        "the climb is playable from floor 1"
    );
    assert!(
        spoils[boundary..].iter().any(|action| action.turn == FLEE),
        "the exit is offered but LOCKED below the surface — you climb out, you do not \
         teleport out"
    );

    let first_relic = expected_loot[0];
    land(&offering, &mut session, &actor, LOOT, first_relic);
    // The carried relic is still LOSABLE: the exit names what it would bank, and stays locked.
    let exit = offering
        .actions(&session)
        .into_iter()
        .find(|action| action.turn == FLEE)
        .expect("exit remains offered");
    assert_eq!(
        exit.label,
        "⌂ Bank 1 carried relic and end the run · 1 light"
    );
    assert!(!exit.enabled, "the exit is not reachable from floor 1");

    // Climb out, and NOW it is.
    land(&offering, &mut session, &actor, ASCEND, 0);
    let exit = offering
        .actions(&session)
        .into_iter()
        .find(|action| action.turn == FLEE)
        .expect("exit remains offered");
    assert!(exit.enabled, "at the mouth, the exit opens");
}
