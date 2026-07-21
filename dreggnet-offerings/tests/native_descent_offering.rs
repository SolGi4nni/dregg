//! The generic Offering seam driven over the Lean-authored native Descent.
//!
//! These tests deliberately select the actions the adapter advertises, rather
//! than calling `Descent` directly. The executor remains the referee: disabled,
//! malformed, and wrong-player actions must be anti-ghost refusals.

use dreggnet_offerings::native_descent::{
    NativeDescentMove, NativeDescentOffering, NativeDescentRecord,
};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, RecordVerify, SessionConfig};
use dungeon_on_dregg::descent::{BANKED, DELVE, FLEE, LOOT, SMITE, UNLOCK};

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

fn offered(
    offering: &NativeDescentOffering,
    session: &dreggnet_offerings::native_descent::NativeDescentSession,
    turn: &str,
    arg: i64,
) -> Action {
    offering
        .actions(session)
        .into_iter()
        .find(|action| action.turn == turn && action.arg == arg)
        .unwrap_or_else(|| panic!("missing native affordance {turn}({arg})"))
}

fn land(
    offering: &NativeDescentOffering,
    session: &mut dreggnet_offerings::native_descent::NativeDescentSession,
    who: &DreggIdentity,
    turn: &str,
    arg: i64,
) {
    let action = offered(offering, session, turn, arg);
    assert!(
        action.enabled,
        "the driven line expected {turn}({arg}) to be enabled"
    );
    match offering.advance(session, action, who.clone()) {
        Outcome::Landed { receipt, .. } => {
            assert_ne!(receipt.turn_hash, [0; 32], "a real native turn landed")
        }
        Outcome::Refused(reason) => panic!("legal {turn}({arg}) was refused: {reason}"),
    }
}

fn assert_refused(outcome: Outcome) {
    if let Outcome::Landed { .. } = outcome {
        panic!("the forged/illegal action landed")
    }
}

#[test]
fn complete_crowned_run_banks_on_a_real_terminal_receipt() {
    let offering = NativeDescentOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(7))
        .expect("deploy the Lean-authored descent");
    let alice = actor("alice-cipherclerk");

    // A disabled first click is still sent to the executor. It refuses without
    // letting the attacker seize the first-successful-action player binding.
    let before_root = session.root();
    let before = session.game().sim().clone();
    let locked = offered(&offering, &session, UNLOCK, 2);
    assert!(!locked.enabled);
    assert_refused(offering.advance(&mut session, locked, actor("mallory")));
    assert_eq!(session.actor(), None);
    assert_eq!(session.revision(), 0);
    assert_eq!(session.root(), before_root);
    assert_eq!(session.game().sim(), &before);

    // The first actual executor-landed move binds Alice.
    land(&offering, &mut session, &alice, DELVE, 0);
    assert_eq!(session.actor(), Some(&alice));

    // A valid native verb from a substituted actor cannot reach the executor.
    let before_root = session.root();
    let before = session.game().sim().clone();
    let smite = offered(&offering, &session, SMITE, 0);
    assert!(smite.enabled);
    assert_refused(offering.advance(&mut session, smite, actor("bob-cipherclerk")));
    assert_eq!(session.revision(), 1);
    assert_eq!(session.root(), before_root);
    assert_eq!(session.game().sim(), &before);

    // The exact crowned line from the Lean model / emitted-program battery.
    for (turn, arg) in [
        (SMITE, 0),
        (LOOT, 1),
        (UNLOCK, 2),
        (DELVE, 0),
        (SMITE, 0),
        (LOOT, 2),
        (UNLOCK, 3),
        (DELVE, 0),
        (SMITE, 0),
        (SMITE, 0),
        (LOOT, 3),
        (UNLOCK, 4),
        (DELVE, 0),
        (SMITE, 0),
        (SMITE, 0),
        (LOOT, 0),
        (FLEE, 0),
    ] {
        land(&offering, &mut session, &alice, turn, arg);
    }

    assert_eq!(session.revision(), 18);
    assert_eq!(session.game().sim().fate, 1);
    assert!(offering.actions(&session).is_empty());
    let completion = session.completion().expect("flee settles the run");
    assert_eq!(completion.revision, 18);
    assert_eq!(completion.actor, alice);
    assert_eq!(completion.banked_relics, vec![0, 1, 2, 3]);
    assert!(completion.crowned);
    for relic in [0, 1, 2, 3] {
        assert_eq!(session.game().sim().custody[relic], BANKED);
    }
    assert_ne!(completion.settlement_receipt_hash, [0; 32]);

    let report = offering.verify(&session);
    assert!(report.verified, "exact native replay: {}", report.detail);
    assert_eq!(report.turns, 19, "genesis plus eighteen player turns");
    let rendered = format!("{:?}", offering.render(&session));
    assert!(rendered.contains("Crowned settlement"));
    assert!(rendered.contains("Lean-authored"));
}

#[test]
fn public_record_resumes_by_reexecution_and_rejects_tampering() {
    let offering = NativeDescentOffering::new();
    let mut session = offering.open(SessionConfig::with_seed(41)).expect("open");
    let alice = actor("alice-cipherclerk");
    for (turn, arg) in [(DELVE, 0), (SMITE, 0), (LOOT, 1), (UNLOCK, 2)] {
        land(&offering, &mut session, &alice, turn, arg);
    }

    let authentic: NativeDescentRecord = offering.export_record(&session);
    let report = offering.verify_record(&session, &authentic);
    assert!(report.verified, "authentic record: {}", report.detail);

    let resumed = offering
        .resume_record(&authentic)
        .expect("a fresh native executor reproduces the record exactly");
    assert_eq!(resumed.actor(), session.actor());
    assert_eq!(resumed.revision(), session.revision());
    assert_eq!(resumed.root(), session.root());
    assert_eq!(resumed.game().sim(), session.game().sim());

    let mut wrong_command = authentic.clone();
    wrong_command.events[0].command = NativeDescentMove::Smite;
    assert!(!offering.verify_record(&session, &wrong_command).verified);

    let mut target_wide_relic = authentic.clone();
    target_wide_relic.events[0].command = NativeDescentMove::Loot { relic: u64::MAX };
    assert!(
        !offering
            .verify_record(&session, &target_wide_relic)
            .verified,
        "the public u64 relic wire fails closed at the internal executor-index boundary"
    );

    let mut wrong_actor = authentic.clone();
    wrong_actor.events[0].actor = actor("mallory-cipherclerk");
    assert!(!offering.verify_record(&session, &wrong_actor).verified);

    let mut wrong_post = authentic.clone();
    wrong_post.events[1].post.depth += 1;
    assert!(!offering.verify_record(&session, &wrong_post).verified);

    // A once-current record remains a valid restart prefix, but is not falsely
    // accepted as the exact head after the live session advances.
    land(&offering, &mut session, &alice, DELVE, 0);
    assert!(!offering.verify_record(&session, &authentic).verified);
    let mut resumed_prefix = offering
        .resume_record(&authentic)
        .expect("the old head is still an independently valid checkpoint");
    land(&offering, &mut resumed_prefix, &alice, DELVE, 0);
    assert_eq!(resumed_prefix.root(), session.root());
    assert_eq!(resumed_prefix.game().sim(), session.game().sim());
}

#[test]
fn affordances_follow_the_native_mover_and_refusals_are_anti_ghost() {
    let offering = NativeDescentOffering::new();
    let mut session = offering.open(SessionConfig::with_seed(99)).expect("open");
    let alice = actor("alice-cipherclerk");

    let actions = offering.actions(&session);
    assert_eq!(
        actions.len(),
        14,
        "five verbs expanded over ways and relics"
    );
    assert!(offered(&offering, &session, DELVE, 0).enabled);
    assert!(offered(&offering, &session, FLEE, 0).enabled);
    assert!(!offered(&offering, &session, SMITE, 0).enabled);
    for way in 2..=4 {
        assert!(!offered(&offering, &session, UNLOCK, way).enabled);
    }
    for relic in 0..=7 {
        assert!(!offered(&offering, &session, LOOT, relic).enabled);
    }

    let genesis_root = session.root();
    let genesis = session.game().sim().clone();
    assert_refused(offering.advance(
        &mut session,
        Action::new("forged argument", UNLOCK, 9, true),
        alice.clone(),
    ));
    assert_refused(offering.advance(
        &mut session,
        Action::new("text smuggling", DELVE, 0, true).with_text("hidden payload"),
        alice.clone(),
    ));
    assert_refused(offering.advance(
        &mut session,
        Action::new("empty actor", DELVE, 0, true),
        actor(""),
    ));
    assert_eq!(session.actor(), None);
    assert_eq!(session.revision(), 0);
    assert_eq!(session.root(), genesis_root);
    assert_eq!(session.game().sim(), &genesis);

    land(&offering, &mut session, &alice, DELVE, 0);
    assert!(offered(&offering, &session, SMITE, 0).enabled);
    assert!(!offered(&offering, &session, LOOT, 1).enabled);
    land(&offering, &mut session, &alice, SMITE, 0);
    for relic in [1, 4, 5] {
        assert!(
            offered(&offering, &session, LOOT, relic).enabled,
            "floor-one relic {relic} became lootable when its guardian fell"
        );
    }
    assert!(!offered(&offering, &session, LOOT, 2).enabled);

    let bob = actor("bob-cipherclerk");
    assert!(
        offering
            .actions_for(&session, &bob)
            .iter()
            .all(|action| !action.enabled),
        "a non-owner sees the verbs but cannot actuate them"
    );
    assert!(
        offering
            .actions_for(&session, &alice)
            .iter()
            .any(|action| action.enabled)
    );
}
