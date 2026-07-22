use deos_view::ViewNode;
use dreggnet_catalog::{
    GameAudience, GameAuthorizationPhase, GameCommand, GameEpochError, GameEpochLedger,
    GameHostIncarnation, GameResult, execute_bound_asserted_game_command,
    inspect_bound_game_session,
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

#[test]
fn private_authorization_reservation_and_consumption_survive_restart() {
    let directory = tempfile::tempdir().unwrap();
    let authorization_id = [0x42; 32];
    let reserved_only_id = [0x77; 32];

    let ledger = GameEpochLedger::open(directory.path()).unwrap();
    assert_eq!(ledger.authorization_phase(authorization_id).unwrap(), None);
    assert!(ledger.reserve_authorization(authorization_id).unwrap());
    assert!(!ledger.reserve_authorization(authorization_id).unwrap());
    assert!(ledger.reserve_authorization(reserved_only_id).unwrap());
    ledger.consume_authorization(authorization_id).unwrap();
    ledger.consume_authorization(authorization_id).unwrap();
    let wire = std::fs::read(directory.path().join("private-authorizations.v1")).unwrap();
    assert_eq!(&wire[..8], b"DREGGA01");
    assert_eq!(&wire[8..12], &2u32.to_be_bytes());
    assert_eq!(&wire[12..44], &authorization_id);
    assert_eq!(wire[44], 1, "consumed phase wire tag");
    assert_eq!(&wire[45..77], &reserved_only_id);
    assert_eq!(wire[77], 0, "reserved phase wire tag");
    assert_eq!(wire.len(), 110, "fixed-width records plus checksum");
    drop(ledger);

    let restarted = GameEpochLedger::open(directory.path()).unwrap();
    assert_eq!(
        restarted.authorization_phase(authorization_id).unwrap(),
        Some(GameAuthorizationPhase::Consumed)
    );
    assert_eq!(
        restarted.authorization_phase(reserved_only_id).unwrap(),
        Some(GameAuthorizationPhase::Reserved)
    );
    assert!(!restarted.reserve_authorization(authorization_id).unwrap());
    assert!(!restarted.reserve_authorization(reserved_only_id).unwrap());
    let unused = [0x88; 32];
    assert!(
        !restarted
            .reserve_authorizations(&[authorization_id, unused])
            .unwrap(),
        "one consumed source makes the entire batch refuse"
    );
    assert_eq!(restarted.authorization_phase(unused).unwrap(), None);
}

#[test]
fn private_authorization_journal_fails_closed_on_invalid_transitions_and_corruption() {
    let directory = tempfile::tempdir().unwrap();
    let ledger = GameEpochLedger::open(directory.path()).unwrap();
    assert!(matches!(
        ledger.reserve_authorization([0; 32]),
        Err(GameEpochError::InvalidAuthorization(_))
    ));
    assert!(matches!(
        ledger.consume_authorization([0x19; 32]),
        Err(GameEpochError::MissingAuthorization(_))
    ));
    assert!(ledger.reserve_authorization([0x21; 32]).unwrap());
    drop(ledger);

    let path = directory.path().join("private-authorizations.v1");
    let mut bytes = std::fs::read(&path).unwrap();
    bytes.push(0x99);
    std::fs::write(path, bytes).unwrap();
    assert!(matches!(
        GameEpochLedger::open(directory.path()),
        Err(GameEpochError::Corrupt(_))
    ));
}

#[test]
fn initialized_host_refuses_a_missing_authorization_journal() {
    let directory = tempfile::tempdir().unwrap();
    let ledger = GameEpochLedger::open(directory.path()).unwrap();
    let path = directory.path().join("private-authorizations.v1");
    let initialized = std::fs::read(&path).unwrap();
    assert_eq!(&initialized[..8], b"DREGGA01");
    assert_eq!(&initialized[8..12], &0u32.to_be_bytes());
    assert_eq!(initialized.len(), 44, "empty manifest includes checksum");
    assert!(ledger.reserve_authorization([0x31; 32]).unwrap());
    drop(ledger);

    std::fs::remove_file(path).unwrap();
    assert!(matches!(
        GameEpochLedger::open(directory.path()),
        Err(GameEpochError::Corrupt(_))
    ));
}

#[test]
fn authorization_checksum_and_clone_concurrency_fail_closed() {
    let directory = tempfile::tempdir().unwrap();
    let ledger = GameEpochLedger::open(directory.path()).unwrap();
    let source_ids = [[0x51; 32], [0x52; 32], [0x53; 32]];
    let mut workers = Vec::new();
    for _ in 0..8 {
        let ledger = ledger.clone();
        workers.push(std::thread::spawn(move || {
            ledger.reserve_authorizations(&source_ids).unwrap()
        }));
    }
    let winners = workers
        .into_iter()
        .map(|worker| worker.join().unwrap())
        .filter(|won| *won)
        .count();
    assert_eq!(winners, 1, "the in-process mutex admits one batch writer");
    drop(ledger);

    let path = directory.path().join("private-authorizations.v1");
    let mut bytes = std::fs::read(&path).unwrap();
    bytes[20] ^= 1;
    std::fs::write(path, bytes).unwrap();
    assert!(matches!(
        GameEpochLedger::open(directory.path()),
        Err(GameEpochError::Corrupt(_))
    ));
}
