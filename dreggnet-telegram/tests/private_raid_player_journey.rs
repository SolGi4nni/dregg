//! Real Telegram button/document coverage for the shared-catalog raid. The canonical proof is
//! uploaded to the exact public session under the authenticated claimant, then spent in the real
//! party/Arena and reconstructed from the host journal after a process restart.

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use dreggnet_catalog::{CatalogConfig, PublicGameReceiptResult, full_catalog_host};
use dreggnet_offerings::{FileResumeStore, Outcome, seed_from_id};
use dreggnet_telegram::api::encode_callback;
use dreggnet_telegram::host::{
    HostPress, OPERATION_GUIDE_SLOT, TelegramAppliedOperation, TelegramHost, TelegramOperationError,
};
use dreggnet_telegram::runtime::describe_shared_game_receipt_landed;
use dreggnet_telegram::transport::MockTransport;
use dreggnet_telegram::{CallbackQuery, TelegramFrontend};
use dungeon_on_dregg::combat::{Arena, is_hero};
use dungeon_on_dregg::private_raid::prove_private_assignment;

const BOT_SECRET: [u8; 32] = [0xA7; 32];
const USERS: [u64; 4] = [41_001, 41_002, 41_003, 41_004];
const KEY: &str = "private-raid";
const ASSIGN_OPERATION: &str = "party.private-raid-assignment.v1";
const TURN_JOIN: &str = "join-private-raid";
const TURN_CLAIM: &str = "claim-role";
const TURN_READY: &str = "ready";
const TURN_LAUNCH: &str = "launch-party";
const TURN_FORK: &str = "fork";
const TURN_RESOLVE: &str = "resolve-fork";
const TURN_PRIME: &str = "prime-private-raid-tactic";
const TURN_ACT: &str = "act";
const BABYBEAR_P_MINUS_ONE: u64 = 2_013_265_920;

fn scores() -> [[u8; 4]; 4] {
    [[3, 2, 0, 0], [3, 0, 1, 0], [0, 0, 3, 1], [0, 1, 0, 3]]
}

fn arena_seed(seed: u64) -> u8 {
    seed.to_le_bytes().into_iter().fold(0u8, u8::wrapping_add)
}

fn hero_first_group() -> i64 {
    (1i64..)
        .map(|candidate| -candidate)
        .find(|chat| {
            let sid = TelegramFrontend::<MockTransport>::session_id(*chat, None);
            is_hero(Arena::deploy(arena_seed(seed_from_id(&sid.0))).active())
        })
        .expect("some deterministic Telegram group begins on a hero turn")
}

fn scratch_dir() -> PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let dir = std::env::temp_dir().join(format!(
        "dreggnet-telegram-private-raid-player-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let _ = std::fs::remove_dir_all(&dir);
    dir
}

fn host(dir: &Path) -> TelegramHost<MockTransport> {
    let dir = dir.to_path_buf();
    TelegramHost::with_host(BOT_SECRET, MockTransport::new(), move || {
        let store = FileResumeStore::open(dir).expect("the Telegram raid journal opens");
        let mut host =
            full_catalog_host(&CatalogConfig::default()).with_resume_store(Box::new(store));
        let resumed = host.resume_all();
        assert!(
            resumed.iter().all(|(_, result)| result.is_ok()),
            "the Telegram catalog must fail closed rather than partially resume: {resumed:?}"
        );
        host
    })
}

fn press(
    host: &mut TelegramHost<MockTransport>,
    chat: i64,
    uid: u64,
    turn: &str,
    arg: i64,
) -> HostPress {
    host.press(CallbackQuery::press(chat, uid, encode_callback(turn, arg)))
}

fn assert_landed(press: HostPress, context: &str) {
    assert!(
        matches!(
            &press,
            HostPress::Advanced {
                outcome: Outcome::Landed { .. },
                ..
            }
        ),
        "{context}: {press:?}"
    );
}

#[test]
fn telegram_group_uploads_and_spends_a_bound_private_raid_then_restarts() {
    let dir = scratch_dir();
    let chat = hero_first_group();
    let sid = TelegramFrontend::<MockTransport>::session_id(chat, None);
    let seed = seed_from_id(&sid.0);
    let proof_session = ((seed % BABYBEAR_P_MINUS_ONE) + 1) as u32;
    let proof = prove_private_assignment(
        proof_session,
        scores(),
        [
            [false, true, true, true],
            [true, true, true, true],
            [true, true, true, true],
            [true, true, true, true],
        ],
    )
    .expect("the private optimizer produces a real HidingFri proof")
    .to_postcard()
    .expect("the proof has its canonical document image");

    let (identities, before_restart_turns) = {
        let mut host = host(&dir);
        let identities = USERS.map(|uid| host.identity(uid));
        for left in 0..identities.len() {
            for right in left + 1..identities.len() {
                assert_ne!(
                    identities[left], identities[right],
                    "four Telegram accounts must derive four distinct proof-seat identities"
                );
            }
        }
        host.open(KEY, chat, None, USERS[0])
            .expect("the shared-catalog raid opens in the group");

        for uid in USERS {
            assert_landed(
                press(&mut host, chat, uid, TURN_JOIN, 0),
                &format!("Telegram account {uid} occupies one derived-identity proof seat"),
            );
        }

        let surface = TelegramFrontend::<MockTransport>::surface_id(chat, None, KEY);
        let guide_id = host
            .frontend()
            .companion_messages(&surface, OPERATION_GUIDE_SLOT)
            .into_iter()
            .next()
            .expect("the live proof operation has a companion guide");
        let guide = host
            .frontend()
            .transport()
            .visible(guide_id)
            .expect("the guide page is visible");
        assert!(
            guide
                .text
                .contains(&format!("/operation {ASSIGN_OPERATION}"))
        );
        assert!(guide.text.contains("It is not a bearer proof"));
        assert!(guide.reply_markup.is_none());

        // Metadata preflight alone conveys no authority. The update-derived claimant remains
        // attached to the route and the offering refuses a non-seat-zero uploader without
        // installing any assignment.
        let forged_claimant = host
            .preflight_operation(chat, None, USERS[1], ASSIGN_OPERATION, proof.len())
            .expect("the public descriptor itself is discoverable to every group member");
        let forged_error = host
            .apply_operation(forged_claimant, proof.clone())
            .expect_err("the proof is not bearer authority for another authenticated uploader");
        assert_eq!(forged_error, TelegramOperationError::SharedGameRefused);
        let forged_message = forged_error.to_string();
        assert!(
            !forged_message.contains(ASSIGN_OPERATION),
            "{forged_message}"
        );
        assert!(!forged_message.contains(&sid.0), "{forged_message}");

        // The canonical proof is also bound to the session-derived proof id. Reusing it in a
        // second group with the same Telegram roster fails before any proof capability is minted.
        let other_chat = chat - 10_000;
        host.open(KEY, other_chat, None, USERS[0])
            .expect("a second exact group session opens");
        for uid in USERS {
            assert_landed(
                press(&mut host, other_chat, uid, TURN_JOIN, 0),
                "the comparison session receives the same authenticated roster",
            );
        }
        let wrong_session = host
            .preflight_operation(other_chat, None, USERS[0], ASSIGN_OPERATION, proof.len())
            .expect("the second live session has the same operation descriptor");
        let wrong_session_error = host
            .apply_operation(wrong_session, proof.clone())
            .expect_err("a proof document from another session is not a transferable bearer");
        assert_eq!(
            wrong_session_error,
            TelegramOperationError::SharedGameRefused
        );
        let wrong_session_message = wrong_session_error.to_string();
        assert!(
            !wrong_session_message.contains(ASSIGN_OPERATION),
            "{wrong_session_message}"
        );
        assert!(
            !wrong_session_message.contains(&sid.0),
            "{wrong_session_message}"
        );

        let route = host
            .preflight_operation(chat, None, USERS[0], ASSIGN_OPERATION, proof.len())
            .expect("the exact group/session/seat-zero document route preflights");
        let applied = host
            .apply_operation(route, proof.clone())
            .expect("the canonical proof is accepted by the live HidingFri verifier");
        let applied_debug = format!("{applied:?}");
        assert!(!applied_debug.contains(ASSIGN_OPERATION), "{applied_debug}");
        assert!(!applied_debug.contains(&sid.0), "{applied_debug}");
        let public_receipt = match applied {
            TelegramAppliedOperation::SharedGame(receipt) => receipt,
            other => panic!("shared game route returned a non-public object: {other:?}"),
        };
        assert!(matches!(
            &public_receipt.result,
            PublicGameReceiptResult::Operation { .. }
        ));
        assert!(!format!("{public_receipt:?}").contains(ASSIGN_OPERATION));
        let public_status = host
            .game_status(chat, None, USERS[0])
            .expect("the shielded operation updates the common game status")
            .shared_projection()
            .expect("the group receives only the typed viewer-blind projection");
        assert!(matches!(
            &public_status
                .latest_receipt
                .as_ref()
                .expect("the bound proof operation has a public receipt")
                .result,
            PublicGameReceiptResult::Operation { .. }
        ));
        assert_eq!(
            public_status.latest_receipt.as_ref(),
            Some(&public_receipt),
            "status and immediate acknowledgement share one exact publication"
        );
        let public_ack = describe_shared_game_receipt_landed(&public_receipt);
        assert!(public_ack.contains("receipt "), "{public_ack}");
        assert!(public_ack.contains("publication "), "{public_ack}");
        assert!(!public_ack.contains(ASSIGN_OPERATION), "{public_ack}");
        let neutralized = host
            .frontend()
            .transport()
            .visible(guide_id)
            .expect("the stable companion message remains visible");
        assert!(
            neutralized.text.contains("guide inactive"),
            "once spent, stale proof instructions are neutralized"
        );

        // Proof roles Striker/Bulwark/Mender/Pathfinder map to the real party's
        // Mage/Tank/Healer/Scout capability indices 2/0/3/1.
        for (uid, role) in USERS.into_iter().zip([2, 0, 3, 1]) {
            assert_landed(
                press(&mut host, chat, uid, TURN_CLAIM, role),
                &format!("Telegram identity {uid} claims its exact proof role"),
            );
        }
        for uid in USERS {
            assert_landed(
                press(&mut host, chat, uid, TURN_READY, 0),
                &format!("Telegram identity {uid} readies"),
            );
        }
        assert_landed(
            press(&mut host, chat, USERS[0], TURN_LAUNCH, 0),
            "proof seat zero launches the exact ready roster",
        );
        for uid in USERS.into_iter().take(3) {
            assert_landed(
                press(&mut host, chat, uid, TURN_FORK, 0),
                &format!("Telegram identity {uid} votes for the Warden"),
            );
        }
        assert_landed(
            press(&mut host, chat, USERS[0], TURN_RESOLVE, 0),
            "the leader resolves the real target ballot",
        );

        let surface = TelegramFrontend::<MockTransport>::surface_id(chat, None, KEY);
        let presented = &host
            .frontend()
            .session(&surface)
            .expect("the group raid surface remains live")
            .presented;
        assert!(presented.iter().any(|action| action.turn == TURN_PRIME));
        assert!(
            presented.iter().all(|action| action.turn != TURN_ACT),
            "Telegram must not paint a stale unprimed Arena action: {presented:?}"
        );
        assert!(
            matches!(
                press(&mut host, chat, USERS[0], TURN_ACT, 0),
                HostPress::NotOffered
            ),
            "a crafted unprimed callback is refused at the presented-affordance boundary"
        );

        assert_landed(
            press(&mut host, chat, USERS[0], TURN_PRIME, 2),
            "the assigned Mage burns its proof-minted sigil",
        );
        assert_landed(
            press(&mut host, chat, USERS[0], TURN_ACT, 0),
            "the primed Mage contributes a real Arena turn",
        );
        let report = host.verify(KEY, &sid).expect("the raid session is live");
        assert!(report.verified, "{}", report.detail);
        (identities, report.turns)
    };

    let mut rebooted = host(&dir);
    assert_eq!(
        rebooted.resume_chat(&sid),
        Some(KEY.to_string()),
        "the runtime can rebind the boot-replayed raid to its Telegram chat"
    );
    rebooted
        .open(KEY, chat, None, USERS[0])
        .expect("re-presenting does not replace the resumed session");
    assert_eq!(
        USERS.map(|uid| rebooted.identity(uid)),
        identities,
        "the platform IDs derive the same proof-seat identities after restart"
    );
    let report = rebooted
        .verify(KEY, &sid)
        .expect("the replayed raid remains live");
    assert!(report.verified, "{}", report.detail);
    assert_eq!(report.turns, before_restart_turns);

    let _ = std::fs::remove_dir_all(dir);
}
