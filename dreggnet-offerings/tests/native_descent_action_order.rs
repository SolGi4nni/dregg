//! Cross-surface play ordering for the Lean-authored native Descent.
//!
//! Web forms, Telegram keyboards, Discord buttons, and the native browser controller all consume
//! the Offering's action list in order. The executor remains the referee and the complete locked
//! action vocabulary stays visible; this test pins only the player-facing priority bands.

use dreggnet_offerings::native_descent::NativeDescentOffering;
use dreggnet_offerings::{DreggIdentity, Offering, Outcome, SessionConfig};
use dungeon_on_dregg::descent::{DELVE, FLEE, LOOT, RELICS, SMITE};

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
    assert_eq!(
        fresh.len(),
        14,
        "the complete anti-ghost vocabulary remains"
    );
    assert_eq!(fresh[0].turn, DELVE);
    assert_eq!(fresh[1].turn, FLEE);
    assert!(fresh[..2].iter().all(|action| action.enabled));
    assert!(fresh[2..].iter().all(|action| !action.enabled));
    // The exit names WHAT IT BANKS and WHAT IT COSTS — an irreversible move a newcomer can weigh.
    assert_eq!(fresh[1].label, "↑ Climb out with nothing · 1 light");

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

    let spoils = offering.actions(&session);
    let exit = spoils
        .iter()
        .position(|action| action.turn == FLEE)
        .expect("exit remains offered");
    let mut playable_loot: Vec<_> = spoils[..exit]
        .iter()
        .filter(|action| action.turn == LOOT)
        .map(|action| action.arg)
        .collect();
    playable_loot.sort_unstable();
    assert_eq!(playable_loot, expected_loot);
    assert!(spoils[..exit].iter().all(|action| action.enabled));
    assert!(spoils[exit + 1..].iter().all(|action| !action.enabled));

    let first_relic = expected_loot[0];
    land(&offering, &mut session, &actor, LOOT, first_relic);
    let exit = offering
        .actions(&session)
        .into_iter()
        .find(|action| action.turn == FLEE)
        .expect("exit remains offered");
    assert_eq!(exit.label, "↑ Climb out and bank 1 carried relic · 1 light");
}
