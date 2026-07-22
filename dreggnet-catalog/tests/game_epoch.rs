use deos_view::ViewNode;
use dreggnet_catalog::{
    GameAudience, GameCommand, GameEpochError, GameEpochLedger, GameHostIncarnation, GameResult,
    execute_bound_asserted_game_command, inspect_bound_game_session,
};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, OfferingHost, Outcome, RunCost, SessionConfig,
    SessionId, Surface, VerifyReport,
};

#[derive(Clone, Debug, Default)]
struct OneMoveState {
    landed: usize,
}

struct OneMoveDungeon;

impl Offering for OneMoveDungeon {
    type Session = OneMoveState;

    fn open(&self, _cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        Ok(OneMoveState::default())
    }

    fn actions(&self, _session: &Self::Session) -> Vec<Action> {
        vec![Action::new("enter", "enter", 0, true)]
    }

    fn advance(
        &self,
        session: &mut Self::Session,
        input: Action,
        _actor: DreggIdentity,
    ) -> Outcome {
        if input.turn != "enter" || input.arg != 0 || input.text.is_some() {
            return Outcome::Refused("not the exact entrance".to_string());
        }
        session.landed += 1;
        Outcome::Landed {
            receipt: Default::default(),
            ended: false,
        }
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        VerifyReport::ok(session.landed)
    }

    fn render(&self, session: &Self::Session) -> Surface {
        Surface(ViewNode::Text(format!("landed={}", session.landed)))
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

fn dungeon_host() -> OfferingHost {
    let mut host = OfferingHost::new();
    host.register("dungeon", "one-move fixture", OneMoveDungeon);
    host
}

fn first_turn(view: &dreggnet_catalog::GameSessionView) -> GameCommand {
    let dreggnet_catalog::GameAffordance::Turn {
        reference, action, ..
    } = view
        .affordances
        .iter()
        .find(|affordance| matches!(affordance, dreggnet_catalog::GameAffordance::Turn { .. }))
        .expect("dungeon genesis offers a turn")
    else {
        unreachable!()
    };
    GameCommand::Turn {
        reference: reference.clone(),
        action: action.clone(),
    }
}

#[test]
fn durable_restart_retains_incarnation_and_live_generation() {
    let directory = tempfile::tempdir().unwrap();
    let session = SessionId::new("tg:durable-restart");
    let first = GameEpochLedger::open(directory.path()).unwrap();
    let incarnation = first.host_incarnation();
    assert_eq!(
        first.bind_after_ensure("dungeon", &session, true).unwrap(),
        1
    );

    drop(first);
    let restarted = GameEpochLedger::open(directory.path()).unwrap();
    assert_eq!(restarted.host_incarnation(), incarnation);
    assert_eq!(
        restarted
            .bind_after_ensure("dungeon", &session, false)
            .unwrap(),
        1
    );
    assert_eq!(
        restarted
            .bound_session("dungeon", &session)
            .unwrap()
            .binding(),
        &dreggnet_catalog::GameSessionBinding::bound(incarnation, 1)
    );
}

#[test]
fn close_reopen_increments_and_captured_action_cannot_land() {
    let directory = tempfile::tempdir().unwrap();
    let ledger = GameEpochLedger::open(directory.path()).unwrap();
    let incarnation = ledger.host_incarnation();
    let id = SessionId::new("tg:close-reopen");
    let mut host = dungeon_host();

    assert!(host.ensure_open("dungeon", &id).unwrap());
    let generation_one = ledger.bind_after_ensure("dungeon", &id, true).unwrap();
    let session_one = ledger.bound_session("dungeon", &id).unwrap();
    let view_one = inspect_bound_game_session(
        &host,
        incarnation,
        generation_one,
        session_one.clone(),
        &GameAudience::Shared,
    )
    .unwrap();
    let captured = first_turn(&view_one);

    assert!(host.close("dungeon", &id));
    assert!(ledger.mark_closed("dungeon", &id).unwrap());
    assert!(host.ensure_open("dungeon", &id).unwrap());
    let generation_two = ledger.bind_after_ensure("dungeon", &id, true).unwrap();
    assert_eq!(generation_two, generation_one + 1);

    let refused = execute_bound_asserted_game_command(
        &mut host,
        incarnation,
        generation_two,
        &session_one,
        captured,
        DreggIdentity("captured-player".to_string()),
    );
    assert!(
        refused.is_err(),
        "generation-one command must fail before execution"
    );
    assert_eq!(host.verify("dungeon", &id).unwrap().turns, 0);

    let session_two = ledger.bound_session("dungeon", &id).unwrap();
    let view_two = inspect_bound_game_session(
        &host,
        incarnation,
        generation_two,
        session_two.clone(),
        &GameAudience::Shared,
    )
    .unwrap();
    let landed = execute_bound_asserted_game_command(
        &mut host,
        incarnation,
        generation_two,
        &session_two,
        first_turn(&view_two),
        DreggIdentity("current-player".to_string()),
    )
    .unwrap();
    assert!(matches!(landed, GameResult::Landed(_)));
}

#[test]
fn durable_existing_session_without_epoch_custody_fails_closed() {
    let directory = tempfile::tempdir().unwrap();
    let ledger = GameEpochLedger::open(directory.path()).unwrap();
    let error = ledger
        .bind_after_ensure("dungeon", &SessionId::new("tg:unclaimed"), false)
        .unwrap_err();
    assert!(matches!(
        error,
        GameEpochError::MissingActiveGeneration { .. }
    ));
}

#[test]
fn corrupt_incarnation_and_trailing_epoch_bytes_are_not_reinitialized() {
    let directory = tempfile::tempdir().unwrap();
    std::fs::write(directory.path().join("host-incarnation.v1"), [7u8; 31]).unwrap();
    assert!(matches!(
        GameEpochLedger::open(directory.path()),
        Err(GameEpochError::Corrupt(_))
    ));

    let other = tempfile::tempdir().unwrap();
    let ledger = GameEpochLedger::open(other.path()).unwrap();
    ledger
        .bind_after_ensure("dungeon", &SessionId::new("tg:trailing"), true)
        .unwrap();
    drop(ledger);
    let path = other.path().join("session-generations.v1");
    let mut bytes = std::fs::read(&path).unwrap();
    bytes.push(0x99);
    std::fs::write(path, bytes).unwrap();
    assert!(matches!(
        GameEpochLedger::open(other.path()),
        Err(GameEpochError::Corrupt(_))
    ));

    let _ = GameHostIncarnation::new([1; 32]).unwrap();
}
