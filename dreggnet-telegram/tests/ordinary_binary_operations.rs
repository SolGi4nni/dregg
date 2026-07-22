//! Exact ordinary Telegram Bot API affordance + bounded-document ingress.
//!
//! This is deliberately not a Mini App test: it drives the long-poll update
//! shape, the `getFile`/file-origin transport, and `TelegramHost` itself.

use std::sync::{Arc, Mutex};

use deos_view::ViewNode;
use dreggnet_offerings::dungeon::{
    DungeonOffering, PRIVATE_PREFERENCE_OPERATION, PRIVATE_QUEST_OPERATION,
    PRIVATE_SHUFFLE_COMMIT_OPERATION, PRIVATE_SHUFFLE_PROVE_OPERATION,
    PRIVATE_SHUFFLE_REVEAL_OPERATION,
};
use dreggnet_offerings::{
    Action, BinaryOperationDescriptor, BinaryOperationError, BinaryOperationReceipt, DreggIdentity,
    MAX_CHAT_BINARY_OPERATION_BYTES, Offering, OfferingError, OfferingHost, Outcome, RunCost,
    SessionConfig, Surface, VerifyReport,
};
use dreggnet_telegram::api::{TELEGRAM_TEXT_LIMIT, encode_callback};
use dreggnet_telegram::host::{
    HostPress, OPERATION_GUIDE_SLOT, TelegramAppliedOperation, TelegramHost, TelegramOperationError,
};
use dreggnet_telegram::runtime::{BotApi, BotEvent, parse_operation_caption, parse_updates};
use dreggnet_telegram::transport::{HttpPost, MockTransport};
use dreggnet_telegram::{CallbackQuery, TelegramFrontend};

const SECRET: [u8; 32] = [0x44; 32];
const UID: u64 = 77;
const DM: i64 = 7007;
const FIXTURE_KEY: &str = "ordinary-receipt-fixture";

const PREFERENCE: &str = "dungeon.private-party-preference.v1";
const SHUFFLE_COMMIT: &str = "dungeon.private-fair-shuffle.commit.v1";
const SHUFFLE_PROVE: &str = "dungeon.private-fair-shuffle.prove.v1";
const SHUFFLE_REVEAL: &str = "dungeon.private-fair-shuffle.reveal.v1";
const QUEST: &str = "dungeon.private-quest-reduction.v1";

const OPERATIONS: [(&str, &str, usize); 5] = [
    (
        PREFERENCE,
        "application/vnd.dregg.private-party-preference.v1+postcard",
        MAX_CHAT_BINARY_OPERATION_BYTES,
    ),
    (
        SHUFFLE_COMMIT,
        "application/vnd.dregg.private-fair-shuffle-commit.v1",
        33,
    ),
    (
        SHUFFLE_PROVE,
        "application/vnd.dregg.private-fair-shuffle-proof.v1+postcard",
        MAX_CHAT_BINARY_OPERATION_BYTES,
    ),
    (
        SHUFFLE_REVEAL,
        "application/vnd.dregg.private-fair-shuffle-opening.v1+postcard",
        64 * 1024,
    ),
    (
        QUEST,
        "application/vnd.dregg.private-quest-reduction.v1+postcard",
        MAX_CHAT_BINARY_OPERATION_BYTES,
    ),
];

struct ReceiptOffering;

impl Offering for ReceiptOffering {
    type Session = Vec<String>;

    fn open(&self, _cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        Ok(Vec::new())
    }

    fn actions(&self, _session: &Self::Session) -> Vec<Action> {
        Vec::new()
    }

    fn advance(
        &self,
        _session: &mut Self::Session,
        _input: Action,
        _actor: DreggIdentity,
    ) -> Outcome {
        Outcome::Refused("ordinary turns are not part of this fixture".to_string())
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        VerifyReport::ok(session.len())
    }

    fn render(&self, session: &Self::Session) -> Surface {
        Surface(ViewNode::Section {
            title: "Private dungeon mechanics".to_string(),
            tag: "genuine".to_string(),
            children: vec![
                ViewNode::Text(format!("{} producer receipt(s) applied", session.len())),
                // The real dungeon already paints its long private-operation
                // disclosures. The adapter must recognize that and not double
                // the bounded Telegram message.
                ViewNode::Text(format!("Exact disclosure for {PREFERENCE}.")),
            ],
        })
    }

    fn binary_operations(&self, _session: &Self::Session) -> Vec<BinaryOperationDescriptor> {
        OPERATIONS
            .into_iter()
            .map(|(name, media, maximum)| BinaryOperationDescriptor {
                name: name.to_string(),
                title: format!("Submit {name}"),
                input_media_type: media.to_string(),
                max_input_bytes: maximum,
                disclosure: format!("Exact disclosure for {name}."),
            })
            .collect()
    }

    fn invoke_binary_operation(
        &self,
        session: &mut Self::Session,
        name: &str,
        payload: &[u8],
        actor: DreggIdentity,
    ) -> Result<BinaryOperationReceipt, BinaryOperationError> {
        if !OPERATIONS.iter().any(|operation| operation.0 == name) {
            return Err(BinaryOperationError::UnknownOperation(name.to_string()));
        }
        if payload != b"canonical-receipt" {
            return Err(BinaryOperationError::Malformed(
                "not the canonical fixture receipt".to_string(),
            ));
        }
        session.push(name.to_string());
        Ok(BinaryOperationReceipt {
            operation: name.to_string(),
            receipt_id: *blake3::hash(payload).as_bytes(),
            public_fields: vec![("actor".to_string(), actor.0)],
        })
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

fn host() -> TelegramHost<MockTransport> {
    TelegramHost::with_host(SECRET, MockTransport::new(), || {
        let mut host = OfferingHost::new();
        host.register(FIXTURE_KEY, "Private dungeon", ReceiptOffering);
        host
    })
}

fn operation_guide(host: &TelegramHost<MockTransport>, chat: i64, key: &str) -> String {
    let surface = TelegramFrontend::<MockTransport>::surface_id(chat, None, key);
    let ids = host
        .frontend()
        .companion_messages(&surface, OPERATION_GUIDE_SLOT);
    assert!(!ids.is_empty(), "the operation guide has at least one page");
    ids.into_iter()
        .map(|message_id| {
            let request = host
                .frontend()
                .transport()
                .visible(message_id)
                .expect("a companion page is visible");
            assert!(
                request.reply_markup.is_none(),
                "guide pages never route actions"
            );
            assert!(request.text.chars().count() <= TELEGRAM_TEXT_LIMIT);
            request.text.clone()
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn interactive_surface(host: &TelegramHost<MockTransport>, chat: i64, key: &str) -> String {
    let surface = TelegramFrontend::<MockTransport>::surface_id(chat, None, key);
    let message_id = host
        .frontend()
        .session(&surface)
        .and_then(|session| session.message_id)
        .expect("the interactive surface has a message id");
    let request = host
        .frontend()
        .transport()
        .visible(message_id)
        .expect("the interactive surface is visible");
    assert!(request.text.chars().count() <= TELEGRAM_TEXT_LIMIT);
    request.text.clone()
}

#[test]
fn ordinary_dm_surface_names_the_exact_preference_shuffle_and_quest_uploads() {
    let mut host = host();
    host.open(FIXTURE_KEY, DM, None, UID).expect("DM opens");
    let message = operation_guide(&host, DM, FIXTURE_KEY);

    assert!(message.contains("Proof operations"));
    for (operation, media, maximum) in OPERATIONS {
        assert!(
            message.contains(&format!("/operation {operation}")),
            "missing exact Telegram caption affordance for {operation}: {}",
            message
        );
        assert!(
            message.contains(media),
            "the expected media type must be visible"
        );
        assert!(message.contains(&format!("Maximum: {maximum} bytes")));
        assert!(
            message.contains(&format!("Exact disclosure for {operation}.")),
            "the exact descriptor disclosure must be visible"
        );
        assert_eq!(
            message
                .matches(format!("Exact disclosure for {operation}.").as_str())
                .count(),
            1,
            "each descriptor appears exactly once in the companion guide"
        );
    }
    let main = interactive_surface(&host, DM, FIXTURE_KEY);
    assert!(main.contains("Private dungeon mechanics"));
}

#[test]
fn production_dungeon_descriptors_are_discoverable_on_the_bounded_ordinary_dm_surface() {
    let descriptor_offering = DungeonOffering::new();
    let descriptor_session = descriptor_offering
        .open(SessionConfig::with_seed(0x7E1E_6A4))
        .expect("production descriptor fixture opens");
    let operations = descriptor_offering.binary_operations(&descriptor_session);

    let mut host = TelegramHost::with_host(SECRET, MockTransport::new(), || {
        let mut host = OfferingHost::new();
        host.register("dungeon", "Private dungeon", DungeonOffering::new());
        host
    });
    host.open("dungeon", DM, None, UID)
        .expect("production dungeon opens in a DM");
    for expected in [
        PRIVATE_PREFERENCE_OPERATION,
        PRIVATE_SHUFFLE_COMMIT_OPERATION,
        PRIVATE_SHUFFLE_PROVE_OPERATION,
        PRIVATE_SHUFFLE_REVEAL_OPERATION,
        PRIVATE_QUEST_OPERATION,
    ] {
        let route = host
            .preflight_operation(DM, None, UID, expected, 0)
            .unwrap_or_else(|error| panic!("production route {expected} refused: {error}"));
        assert_eq!(route.policy.descriptor.name, expected);
    }
    let malformed = host
        .preflight_operation(DM, None, UID, PRIVATE_PREFERENCE_OPERATION, 0)
        .expect("production preference route resolves");
    assert!(
        host.apply_operation(malformed, Vec::new()).is_err(),
        "the actual offering decoder, not the adapter, refuses malformed bytes"
    );
    let message = operation_guide(&host, DM, "dungeon");

    for expected in [
        PRIVATE_PREFERENCE_OPERATION,
        PRIVATE_SHUFFLE_COMMIT_OPERATION,
        PRIVATE_SHUFFLE_PROVE_OPERATION,
        PRIVATE_SHUFFLE_REVEAL_OPERATION,
        PRIVATE_QUEST_OPERATION,
    ] {
        let operation = operations
            .iter()
            .find(|operation| operation.name == expected)
            .unwrap_or_else(|| panic!("missing production descriptor {expected}"));
        assert!(
            message.contains(&format!("/operation {}", operation.name)),
            "missing exact Telegram command for {expected}"
        );
        assert!(message.contains(&operation.title));
        assert!(message.contains(&operation.input_media_type));
        assert!(message.contains(&format!(
            "Maximum: {} bytes",
            operation
                .max_input_bytes
                .min(MAX_CHAT_BINARY_OPERATION_BYTES)
        )));
        assert!(message.contains(&operation.disclosure));
    }
    let main = interactive_surface(&host, DM, "dungeon");
    assert!(main.chars().count() <= TELEGRAM_TEXT_LIMIT);
}

#[test]
fn ordinary_group_surface_discloses_operations_but_never_offers_a_document_command() {
    let mut host = host();
    let group = -7007;
    host.open(FIXTURE_KEY, group, None, UID)
        .expect("public fixture opens in a group");
    let message = operation_guide(&host, group, FIXTURE_KEY);

    assert!(message.contains("Group documents are public"));
    for (operation, _, _) in OPERATIONS {
        assert!(
            message.contains(&format!("Exact disclosure for {operation}.")),
            "shared readers still receive the exact security disclosure"
        );
        assert!(
            !message.contains(&format!("/operation {operation}")),
            "a shared chat must not advertise a document-upload command"
        );
    }

    let surface = TelegramFrontend::<MockTransport>::surface_id(group, None, FIXTURE_KEY);
    let guide_ids = host
        .frontend()
        .companion_messages(&surface, OPERATION_GUIDE_SLOT);
    host.open(FIXTURE_KEY, group, None, UID)
        .expect("repainting the same group operation is stable");
    assert_eq!(
        host.frontend()
            .companion_messages(&surface, OPERATION_GUIDE_SLOT),
        guide_ids,
        "companion pages edit in place"
    );
    let forged =
        CallbackQuery::press_on_message(group, guide_ids[0], UID, encode_callback("choose", 0));
    assert!(
        matches!(host.press(forged), HostPress::NotOffered),
        "a guide message id can never fall through to the latest interactive surface"
    );
}

#[test]
fn ordinary_document_path_preflights_before_download_and_rechecks_actual_size() {
    let mut group_host = host();
    group_host
        .open(FIXTURE_KEY, -7007, None, UID)
        .expect("the public fixture opens in the comparison group");
    assert!(matches!(
        group_host.preflight_operation(-7007, None, UID, PREFERENCE, 1),
        Err(TelegramOperationError::PrivateChatRequired)
    ));

    let mut host = host();
    host.open(FIXTURE_KEY, DM, None, UID).unwrap();
    assert!(
        host.preflight_operation(DM, None, UID, "forged.operation", 1)
            .is_err()
    );
    assert!(
        host.preflight_operation(DM, None, UID, QUEST, MAX_CHAT_BINARY_OPERATION_BYTES + 1,)
            .is_err(),
        "declared oversize refuses before getFile"
    );

    let route = host
        .preflight_operation(DM, None, UID, PREFERENCE, b"canonical-receipt".len())
        .unwrap();
    assert!(
        host.apply_operation(route.clone(), b"short".to_vec())
            .is_err(),
        "a CDN body that disagrees with metadata is refused"
    );
    let applied = host
        .apply_operation(route, b"canonical-receipt".to_vec())
        .expect("canonical bounded receipt applies");
    let receipt = match applied {
        TelegramAppliedOperation::Direct(receipt) => receipt,
        other => panic!("DM/non-game operation returned shared publication: {other:?}"),
    };
    assert_eq!(receipt.operation, PREFERENCE);
    assert_eq!(receipt.public_fields[0].0, "actor");
}

#[test]
fn get_updates_decodes_only_explicit_document_metadata_and_caption() {
    let wire = serde_json::json!([{
        "update_id": 9,
        "message": {
            "chat": { "id": DM },
            "from": { "id": UID },
            "caption": format!("/operation {QUEST}"),
            "document": {
                "file_id": "opaque-file-id",
                "file_size": 17,
                "mime_type": "application/octet-stream"
            }
        }
    }]);
    let (events, next) = parse_updates(&wire);
    assert_eq!(next, Some(10));
    match &events[0] {
        BotEvent::Document {
            chat_id,
            uid,
            file_id,
            declared_bytes,
            caption,
            ..
        } => {
            assert_eq!(*chat_id, DM);
            assert_eq!(*uid, UID);
            assert_eq!(file_id, "opaque-file-id");
            assert_eq!(*declared_bytes, 17);
            assert_eq!(parse_operation_caption(caption), Some(QUEST));
        }
        other => panic!("expected a document event, got {other:?}"),
    }
    assert_eq!(parse_operation_caption("ordinary attachment"), None);
    assert_eq!(
        parse_operation_caption(&format!("/operation {QUEST} extra")),
        None
    );
}

struct RecordingHttp {
    gets: Arc<Mutex<Vec<(String, usize)>>>,
    body: Vec<u8>,
}

impl HttpPost for RecordingHttp {
    fn post_json(&self, url: &str, _body: &str) -> Result<String, String> {
        assert!(url.ends_with("/getFile"));
        Ok(format!(
            "{{\"ok\":true,\"result\":{{\"file_path\":\"proofs/receipt.bin\",\"file_size\":{}}}}}",
            self.body.len()
        ))
    }

    fn get_bytes_bounded(&self, url: &str, maximum: usize) -> Result<Vec<u8>, String> {
        self.gets.lock().unwrap().push((url.to_string(), maximum));
        if self.body.len() > maximum {
            return Err("bounded test transport refused oversize body".to_string());
        }
        Ok(self.body.clone())
    }
}

#[test]
fn bot_api_uses_get_file_then_the_fixed_bounded_file_origin() {
    let gets = Arc::new(Mutex::new(Vec::new()));
    let http = RecordingHttp {
        gets: Arc::clone(&gets),
        body: b"canonical-receipt".to_vec(),
    };
    let api = BotApi::new("secret-token", http).with_base_url("https://telegram.invalid");
    assert!(
        api.download_document("opaque-file-id", b"canonical-receipt".len() + 1, 32)
            .is_err(),
        "a getFile metadata disagreement refuses before the file-origin GET"
    );
    assert!(gets.lock().unwrap().is_empty());
    let body = api
        .download_document("opaque-file-id", b"canonical-receipt".len(), 32)
        .expect("bounded file transport succeeds");
    assert_eq!(body, b"canonical-receipt");
    let gets = gets.lock().unwrap();
    assert_eq!(gets.len(), 1);
    assert_eq!(gets[0].1, 32);
    assert_eq!(
        gets[0].0,
        "https://telegram.invalid/file/botsecret-token/proofs/receipt.bin"
    );
}
