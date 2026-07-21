//! Per-player generic Offering / restart seam for the overworld.

use dreggnet_offerings::overworld::{
    ClearError, OVERWORLD_CLEAR, OVERWORLD_TRAVEL, OverworldOffering, OverworldRecord,
    play_partial_run,
};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, RecordVerify, SessionConfig};
use dungeon_on_dregg::overworld::play_to_win;

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

fn action_for(
    offering: &OverworldOffering,
    session: &dreggnet_offerings::overworld::OverworldSession,
    turn: &str,
    location: &str,
) -> Action {
    let index = session
        .map()
        .index_of(location)
        .unwrap_or_else(|| panic!("unknown test location {location}"));
    offering
        .actions(session)
        .into_iter()
        .find(|action| {
            action.turn == turn
                && action.arg
                    == i64::try_from(index).expect("the bounded region map fits the action wire")
        })
        .unwrap_or_else(|| panic!("missing exact {turn} action for {location}"))
}

fn winning_run(
    offering: &OverworldOffering,
    who: &DreggIdentity,
    location: &str,
) -> dungeon_on_dregg::overworld::WinRun {
    let seed = offering
        .completion_seed(who, location)
        .expect("known location and valid actor");
    play_to_win(location, seed).expect("wired overworld universe")
}

fn assert_refused(outcome: Outcome) {
    if let Outcome::Landed { .. } = outcome {
        panic!("the action was expected to refuse")
    }
}

#[test]
fn generic_clear_consumes_a_staged_win_and_first_landed_turn_binds_player() {
    let offering = OverworldOffering::new();
    let mut session = Offering::open(&offering, SessionConfig::with_seed(17)).expect("open");
    let alice = actor("alice-cipherclerk");
    let bob = actor("bob-cipherclerk");

    assert_eq!(session.actor(), None, "generic open is not channel-bound");
    let clear = action_for(&offering, &session, OVERWORLD_CLEAR, "keep");
    assert!(!clear.enabled, "no winning run has been staged");
    let before_root = session.root();
    assert_refused(offering.advance(&mut session, clear, alice.clone()));
    assert_eq!(
        session.actor(),
        None,
        "a refusal cannot seize the traversal"
    );
    assert_eq!(session.revision(), 0);
    assert_eq!(session.root(), before_root);

    for hostile_index in [-1, i64::MAX] {
        assert_refused(offering.advance(
            &mut session,
            Action::new("hostile location", OVERWORLD_TRAVEL, hostile_index, true),
            alice.clone(),
        ));
        assert_eq!(session.revision(), 0);
        assert_eq!(session.root(), before_root);
        assert_eq!(session.actor(), None);
    }

    let seed = offering.completion_seed(&alice, "keep").unwrap();
    let partial = play_partial_run("keep", seed, 2).expect("partial run");
    assert!(matches!(
        offering.stage_completion(&mut session, alice.clone(), "keep", partial),
        Err(ClearError::NotWon(_))
    ));
    let mut forged_won_bit = play_partial_run("keep", seed, 2).expect("partial run");
    forged_won_bit.won = true;
    assert!(matches!(
        offering.stage_completion(&mut session, alice.clone(), "keep", forged_won_bit),
        Err(ClearError::NotWon(_))
    ));
    let other_seed = if seed == 251 { 1 } else { seed + 1 };
    let wrong_player_run = play_to_win("keep", other_seed).expect("winning run");
    assert!(matches!(
        offering.stage_completion(&mut session, alice.clone(), "keep", wrong_player_run),
        Err(ClearError::WrongPlayerSeed { .. })
    ));

    offering
        .stage_completion(
            &mut session,
            alice.clone(),
            "keep",
            winning_run(&offering, &alice, "keep"),
        )
        .expect("a separately played exact win stages");
    assert_eq!(session.actor(), None, "staging is not a region turn");
    assert_eq!(session.revision(), 0);
    assert_eq!(session.root(), before_root);
    assert!(
        action_for(&offering, &session, OVERWORLD_CLEAR, "keep").enabled,
        "the exact clear becomes actionable"
    );
    assert!(
        offering
            .actions_for(&session, &bob)
            .iter()
            .all(|action| !action.enabled),
        "the staged completion is already attributed to Alice"
    );

    let bob_clear = action_for(&offering, &session, OVERWORLD_CLEAR, "keep");
    assert_refused(offering.advance(&mut session, bob_clear, bob.clone()));
    assert_eq!(session.actor(), None);
    assert!(session.staged_completion().is_some());

    let alice_clear = action_for(&offering, &session, OVERWORLD_CLEAR, "keep");
    assert!(
        offering
            .advance(&mut session, alice_clear, alice.clone())
            .landed()
    );
    assert_eq!(session.actor(), Some(&alice));
    assert_eq!(session.revision(), 1);
    assert!(session.is_cleared("keep"));
    assert!(session.staged_completion().is_none());

    let travel = action_for(&offering, &session, OVERWORLD_TRAVEL, "vault");
    assert!(travel.enabled);
    assert_refused(offering.advance(&mut session, travel.clone(), bob));
    assert_eq!(session.current_location(), "keep");
    assert!(offering.advance(&mut session, travel, alice).landed());
    assert_eq!(session.current_location(), "vault");
    assert!(offering.verify(&session).verified);
}

#[test]
fn public_record_exactly_resumes_pending_completion_and_rejects_tampering() {
    let offering = OverworldOffering::new();
    let mut session = Offering::open(&offering, SessionConfig::with_seed(23)).expect("open");
    let alice = actor("alice-cipherclerk");

    offering
        .stage_completion(
            &mut session,
            alice.clone(),
            "keep",
            winning_run(&offering, &alice, "keep"),
        )
        .unwrap();
    let clear = action_for(&offering, &session, OVERWORLD_CLEAR, "keep");
    assert!(
        offering
            .advance(&mut session, clear, alice.clone())
            .landed()
    );
    let travel = action_for(&offering, &session, OVERWORLD_TRAVEL, "vault");
    assert!(
        offering
            .advance(&mut session, travel, alice.clone())
            .landed()
    );
    offering
        .stage_completion(
            &mut session,
            alice.clone(),
            "vault",
            winning_run(&offering, &alice, "vault"),
        )
        .expect("stage the separately played vault run");

    let authentic: OverworldRecord = offering.export_record(&session);
    let report = offering.verify_record(&session, &authentic);
    assert!(report.verified, "authentic record: {}", report.detail);
    let resumed = offering
        .resume_record(&authentic)
        .expect("exact replay resumes the pending clear");
    assert_eq!(resumed.actor(), session.actor());
    assert_eq!(resumed.current_location(), "vault");
    assert_eq!(resumed.root(), session.root());
    assert_eq!(resumed.revision(), session.revision());
    assert!(resumed.staged_completion().is_some());

    let mut forged_move = authentic.clone();
    forged_move.events[1].command =
        dreggnet_offerings::overworld::OverworldMove::Travel("bazaar".to_string());
    assert!(!offering.verify_record(&session, &forged_move).verified);
    assert!(offering.resume_record(&forged_move).is_err());

    let mut forged_actor = authentic.clone();
    forged_actor.events[0].actor = actor("mallory-cipherclerk");
    assert!(!offering.verify_record(&session, &forged_actor).verified);

    let mut forged_win = authentic.clone();
    forged_win.events[0]
        .completion
        .as_mut()
        .expect("clear proof")
        .playthrough
        .steps[0]
        .choice_index += 1;
    assert!(!offering.verify_record(&session, &forged_win).verified);

    let mut forged_checkpoint = authentic.clone();
    forged_checkpoint
        .checkpoint
        .as_mut()
        .expect("checkpoint")
        .current_location = "crypt".to_string();
    assert!(
        !offering
            .verify_record(&session, &forged_checkpoint)
            .verified
    );

    // The uncommitted staged proof survives restart, then both copies land the
    // same clear receipt and journal root under exact deterministic replay.
    let mut resumed = resumed;
    let original_clear = action_for(&offering, &session, OVERWORLD_CLEAR, "vault");
    let resumed_clear = action_for(&offering, &resumed, OVERWORLD_CLEAR, "vault");
    assert!(
        offering
            .advance(&mut session, original_clear, alice.clone())
            .landed()
    );
    assert!(
        offering
            .advance(&mut resumed, resumed_clear, alice)
            .landed()
    );
    assert_eq!(resumed.root(), session.root());
    assert_eq!(resumed.checkpoint(), session.checkpoint());
    assert!(offering.verify(&resumed).verified);
}
