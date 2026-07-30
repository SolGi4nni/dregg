//! The generic Offering seam driven over the Lean-authored native Descent.
//!
//! These tests deliberately select the actions the adapter advertises, rather
//! than calling `Descent` directly. The executor remains the referee: disabled,
//! malformed, and wrong-player actions must be anti-ghost refusals.

use std::collections::BTreeSet;

use dreggnet_offerings::native_descent::{
    NativeDescentMove, NativeDescentOffering, NativeDescentRecord, NativeDescentSession,
};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, RecordVerify, SessionConfig};
use dungeon_on_dregg::descent::{
    ASCEND, BANKED, DELVE, FLEE, FLOORS, LOOT, LUNGE, RELICS, SMITE, TAKE, UNLOCK, crowned_line,
};

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

/// **The complete anti-ghost vocabulary** — every verb the native Descent wire speaks, expanded
/// over its whole argument domain, whether or not any of it is legal right now.
///
/// The argument fan-out is DERIVED from the world's shape (`FLOORS` gives the ways, `RELICS` the
/// relic columns) rather than counted. This used to be the literal `15`, which one new verb turned
/// red while saying nothing about what changed — and a count could never have told a missing relic
/// column from a duplicated one anyway. The VERB ROSTER is still written down on purpose: "the
/// locked catalogue stays visible" is the claim this suite exists to make, so deriving the roster
/// from the surface's own output would make it a tautology. It is a list of the crate's exported
/// verb constants, so a new verb is a compile-visible edit here, not a mystery integer.
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

/// The relics THIS DAY mints on floor `depth` — read off the run's own drawn map.
fn mints_on(session: &NativeDescentSession, depth: u64) -> Vec<i64> {
    let homes = session.day_world().homes;
    (0..RELICS)
        .filter(|&relic| homes[relic] == depth)
        .map(|relic| relic as i64)
        .collect()
}

/// Fell the standing floor's guardian, however many blows THIS DAY's map prices it at.
fn fell_the_guardian(
    offering: &NativeDescentOffering,
    session: &mut NativeDescentSession,
    who: &DreggIdentity,
) {
    let depth = session.game().sim().depth;
    let hp = session.day_world().guard_hp(depth);
    assert!(hp > 0, "floor {depth} has no guardian to fell");
    for _ in 0..hp {
        land(offering, session, who, SMITE, 0);
    }
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

    // ⚑ THIS DAY's crowned line, regenerated from the map the session actually deployed on. It
    // used to be a seventeen-entry literal introduced as "the exact crowned line from the Lean
    // model" — true of the one hard-coded dungeon that predated the day-seeded draw, and false on
    // most of the sixteen maps that exist now (seed 7 draws a floor-1 guardian that takes TWO
    // blows, so `loot` after one smite was refused). `descent::crowned_line` mirrors the Lean
    // `crownedRun` off the day's own `DayWorld`, and `dungeon-on-dregg` proves in its own suite
    // that the derived tape banks the prize inside the light on all sixteen draws.
    let line = crowned_line(session.game().day());
    assert_eq!(line.first().copied(), Some((DELVE, 0)));
    assert_eq!(line.last().copied(), Some((FLEE, 0)));

    // The first actual executor-landed move binds Alice.
    land(&offering, &mut session, &alice, line[0].0, line[0].1);
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

    // The rest of the day's crowned line, move by move through the generic seam.
    for (turn, arg) in line[1..].iter().copied() {
        land(&offering, &mut session, &alice, turn, arg);
    }

    assert_eq!(session.revision(), line.len() as u64);
    assert_eq!(session.game().sim().fate, 1);
    assert!(offering.actions(&session).is_empty());
    let completion = session.completion().expect("flee settles the run");
    assert_eq!(completion.revision, line.len() as u64);
    assert_eq!(completion.actor, alice);
    // ⚑ WHAT THE CROWN IS, on every day: the prize (relic 0) banked, and NOTHING ELSE. The
    // reference crowned line turns each way-key and walks past it — `unlock` sets the key down
    // in the door it opened (`HUNG + depth`) and `flee` promotes `CARRIED` and only `CARRIED`,
    // so the keys are won, replay to the mint, and bank nothing. Bringing them home is the
    // `take` line: one extra breath per key, on the climb, which this line does not play. This
    // read `0..FLOORS` back when turning a key kept it.
    assert_eq!(completion.banked_relics, vec![0u64]);
    assert!(completion.crowned);
    assert_eq!(session.game().sim().custody[0], BANKED);
    for relic in 1..FLOORS as usize {
        assert_ne!(
            session.game().sim().custody[relic],
            BANKED,
            "way-key {relic} hangs in its door; it did not come home"
        );
    }
    assert_ne!(completion.settlement_receipt_hash, [0; 32]);

    let report = offering.verify(&session);
    assert!(report.verified, "exact native replay: {}", report.detail);
    assert_eq!(
        report.turns,
        line.len() + 1,
        "genesis plus every player turn of the crowned line"
    );
    let rendered = format!("{:?}", offering.render(&session));
    assert!(rendered.contains("Crowned settlement"));
    assert!(rendered.contains("Lean-authored"));
}

#[test]
fn public_record_resumes_by_reexecution_and_rejects_tampering() {
    let offering = NativeDescentOffering::new();
    let mut session = offering.open(SessionConfig::with_seed(41)).expect("open");
    let alice = actor("alice-cipherclerk");

    // A short REAL prefix: enter the shaft, fell floor 1's guardian for however many blows this
    // day prices it at, take the way-2 key, exercise it. The blow count is derived; relic 1 is not
    // a guess — the draw guarantees a way's key is minted ABOVE the door it opens
    // (`homes (keyFor w) < w`), so the way-2 key always lies on floor 1. Asserted, not assumed.
    land(&offering, &mut session, &alice, DELVE, 0);
    assert!(
        mints_on(&session, 1).contains(&1),
        "the way-2 key must be minted on floor 1 on every drawn map: {:?}",
        session.day_world().homes
    );
    fell_the_guardian(&offering, &mut session, &alice);
    land(&offering, &mut session, &alice, LOOT, 1);
    land(&offering, &mut session, &alice, UNLOCK, 2);

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
    wrong_post
        .events
        .last_mut()
        .expect("the prefix has events")
        .post
        .depth += 1;
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
    let advertised: BTreeSet<(&str, i64)> = actions
        .iter()
        .map(|action| (action.turn.as_str(), action.arg))
        .collect();
    assert_eq!(
        advertised,
        complete_vocabulary(),
        "every verb, expanded over every way and every relic, stays advertised — locked entries \
         included, because their real executor refusals are the anti-ghost surface"
    );
    assert_eq!(
        actions.len(),
        advertised.len(),
        "and nothing is advertised twice"
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

    // WHICH relics floor 1 mints, and HOW MANY blows its guardian takes, are both facts about the
    // day the committed seed drew. They used to be the literals `[1, 4, 5]` and one smite — day
    // 0's furniture, and wrong on seed 99's map, where the guardian takes two. Derived, the
    // assertion is also STRONGER than it was: `loot` is enabled for EXACTLY this floor's mints.
    let here = mints_on(&session, 1);
    let elsewhere: Vec<i64> = (0..RELICS as i64).filter(|r| !here.contains(r)).collect();
    assert!(!here.is_empty(), "floor 1 mints nothing on this day");
    assert!(
        !elsewhere.is_empty(),
        "floor 1 mints EVERYTHING on this day, so the negative half of this check is vacuous"
    );

    // While the guardian stands the whole hoard is shut, wherever it lies.
    for relic in 0..RELICS as i64 {
        assert!(
            !offered(&offering, &session, LOOT, relic).enabled,
            "relic {relic} must not be takeable while the guardian stands"
        );
    }

    for _ in 0..session.day_world().guard_hp(1) {
        land(&offering, &mut session, &alice, SMITE, 0);
    }
    for relic in &here {
        assert!(
            offered(&offering, &session, LOOT, *relic).enabled,
            "floor-one relic {relic} became lootable when its guardian fell"
        );
    }
    for relic in &elsewhere {
        assert!(
            !offered(&offering, &session, LOOT, *relic).enabled,
            "relic {relic} does not lie on floor 1, so felling its guardian cannot free it"
        );
    }

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
