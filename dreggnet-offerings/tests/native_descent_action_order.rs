//! Cross-surface play ordering for the Lean-authored native Descent.
//!
//! Web forms, Telegram keyboards, Discord buttons, and the native browser controller all consume
//! the Offering's action list in order. The executor remains the referee and the complete locked
//! action vocabulary stays visible; this test pins only the player-facing priority bands.

use dreggnet_offerings::native_descent::NativeDescentOffering;
use dreggnet_offerings::{DreggIdentity, Offering, Outcome, SessionConfig};
use dungeon_on_dregg::descent::{DELVE, FLEE, LOOT, SMITE};

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
    assert_eq!(fresh[1].label, "End the run with no relics banked");

    // Kill floor one's guardian. Three relics become legal; all three must be shown before the
    // irreversible but still legal exit, while locked actions remain visible after it.
    land(&offering, &mut session, &actor, DELVE, 0);
    land(&offering, &mut session, &actor, SMITE, 0);
    let spoils = offering.actions(&session);
    let exit = spoils
        .iter()
        .position(|action| action.turn == FLEE)
        .expect("exit remains offered");
    let playable_loot: Vec<_> = spoils[..exit]
        .iter()
        .filter(|action| action.turn == LOOT)
        .map(|action| action.arg)
        .collect();
    assert_eq!(playable_loot, vec![1, 4, 5]);
    assert!(spoils[..exit].iter().all(|action| action.enabled));
    assert!(spoils[exit + 1..].iter().all(|action| !action.enabled));

    land(&offering, &mut session, &actor, LOOT, 1);
    let exit = offering
        .actions(&session)
        .into_iter()
        .find(|action| action.turn == FLEE)
        .expect("exit remains offered");
    assert_eq!(exit.label, "End the run and bank 1 carried relic");
}
