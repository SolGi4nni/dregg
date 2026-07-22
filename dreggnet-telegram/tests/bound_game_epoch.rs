use deos_view::ViewNode;
use dreggnet_catalog::{GameEpochLedger, PlayerWorlds};
use dreggnet_offerings::{
    Action, DreggIdentity, FileResumeStore, Offering, OfferingError, OfferingHost, Outcome,
    RunCost, SessionConfig, Surface, VerifyReport,
};
use dreggnet_telegram::host::{HostPress, TelegramHost};
use dreggnet_telegram::transport::MockTransport;
use dreggnet_telegram::{CallbackQuery, TelegramFrontend};

const CHAT: i64 = 4201;
const USER: u64 = 77;

#[derive(Default)]
struct State {
    landed: usize,
}

struct OneMoveDungeon;

impl Offering for OneMoveDungeon {
    type Session = State;

    fn open(&self, _cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        Ok(State::default())
    }

    fn actions(&self, _session: &Self::Session) -> Vec<Action> {
        vec![Action::new("Enter", "enter", 0, true)]
    }

    fn advance(
        &self,
        session: &mut Self::Session,
        action: Action,
        _actor: DreggIdentity,
    ) -> Outcome {
        if action.turn != "enter" || action.arg != 0 || action.text.is_some() {
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

fn game_host() -> OfferingHost {
    let mut host = OfferingHost::new();
    host.register("dungeon", "one-move fixture", OneMoveDungeon);
    host
}

fn durable_game_host(directory: std::path::PathBuf) -> OfferingHost {
    let store = FileResumeStore::open(directory).unwrap();
    let mut host = game_host().with_resume_store(Box::new(store));
    let results = host.resume_all();
    assert!(results.iter().all(|(_, result)| result.is_ok()));
    host
}

fn current_game_callback(host: &TelegramHost<MockTransport>) -> String {
    let request = host
        .frontend()
        .transport()
        .last()
        .expect("game surface was presented");
    request
        .reply_markup
        .as_ref()
        .expect("game has a keyboard")
        .inline_keyboard
        .iter()
        .flatten()
        .map(|button| button.callback_data.as_str())
        .find(|callback| callback.starts_with("g."))
        .expect("game action uses the bound callback wire")
        .to_string()
}

#[test]
fn captured_callback_cannot_cross_close_reopen_generation() {
    let directory = tempfile::tempdir().unwrap();
    let epochs = GameEpochLedger::open(directory.path()).unwrap();
    let incarnation = epochs.host_incarnation();
    let mut host = TelegramHost::with_hosts_and_game_epochs(
        [9; 32],
        MockTransport::new(),
        game_host,
        PlayerWorlds::new,
        epochs,
    );

    host.open("dungeon", CHAT, None, USER).unwrap();
    let before = host.game_status(CHAT, None, USER).unwrap();
    assert_eq!(before.host_incarnation, incarnation);
    assert_eq!(before.session_generation, 1);
    let captured = current_game_callback(&host);
    assert!(captured.len() <= 64);

    assert!(host.close_game("dungeon", CHAT, None, USER).unwrap());
    host.open("dungeon", CHAT, None, USER).unwrap();
    let reopened = host.game_status(CHAT, None, USER).unwrap();
    assert_eq!(reopened.host_incarnation, incarnation);
    assert_eq!(reopened.session_generation, 2);
    assert_eq!(reopened.verified_turns, 0);

    assert!(matches!(
        host.press(CallbackQuery::press(CHAT, USER, captured)),
        HostPress::NotOffered
    ));
    assert_eq!(
        host.game_status(CHAT, None, USER).unwrap().verified_turns,
        0
    );

    let current = current_game_callback(&host);
    assert!(matches!(
        host.press(CallbackQuery::press(CHAT, USER, current)),
        HostPress::Advanced {
            outcome: Outcome::Landed { .. },
            ..
        }
    ));
    assert_eq!(
        host.game_status(CHAT, None, USER).unwrap().verified_turns,
        1
    );
}

#[test]
fn restart_retains_incarnation_generation_and_callback_authority() {
    let directory = tempfile::tempdir().unwrap();
    let epoch_dir = directory.path().join("epochs");
    let session_dir = directory.path().join("sessions");
    let first_epochs = GameEpochLedger::open(&epoch_dir).unwrap();
    let incarnation = first_epochs.host_incarnation();
    let first_session_dir = session_dir.clone();
    let mut first = TelegramHost::with_hosts_and_game_epochs(
        [8; 32],
        MockTransport::new(),
        move || durable_game_host(first_session_dir),
        PlayerWorlds::new,
        first_epochs,
    );
    first.open("dungeon", CHAT, None, USER).unwrap();
    let captured = current_game_callback(&first);
    let before = first.game_status(CHAT, None, USER).unwrap();
    assert_eq!(before.host_incarnation, incarnation);
    assert_eq!(before.session_generation, 1);
    drop(first);

    let restarted_epochs = GameEpochLedger::open(&epoch_dir).unwrap();
    let second_session_dir = session_dir.clone();
    let mut restarted = TelegramHost::with_hosts_and_game_epochs(
        [8; 32],
        MockTransport::new(),
        move || durable_game_host(second_session_dir),
        PlayerWorlds::new,
        restarted_epochs,
    );
    let sid = TelegramFrontend::<MockTransport>::session_id(CHAT, None);
    assert_eq!(restarted.resume_chat(&sid).as_deref(), Some("dungeon"));
    restarted.open("dungeon", CHAT, None, USER).unwrap();
    let after = restarted.game_status(CHAT, None, USER).unwrap();
    assert_eq!(after.host_incarnation, incarnation);
    assert_eq!(after.session_generation, 1);
    assert_eq!(current_game_callback(&restarted), captured);
    assert!(matches!(
        restarted.press(CallbackQuery::press(CHAT, USER, captured)),
        HostPress::Advanced {
            outcome: Outcome::Landed { .. },
            ..
        }
    ));
}
