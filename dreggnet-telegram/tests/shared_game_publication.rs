//! Hostile no-viewer checks for Telegram's common player-facing game publication.

use dreggnet_catalog::{
    GameHostIncarnation, GameKind, PublicGameField, PublicGameFieldValue, PublicGameReceiptResult,
};
use dreggnet_offerings::{Outcome, SessionId};
use dreggnet_telegram::CallbackQuery;
use dreggnet_telegram::host::{HostPress, TelegramGameStatus, TelegramHost};
use dreggnet_telegram::runtime::{describe_game_status, describe_game_status_for_chat};
use dreggnet_telegram::transport::MockTransport;

const BOT_SECRET: [u8; 32] = [0xA9; 32];
const PLAYER: u64 = 90_401;

fn hostile_status(private_projection: bool) -> TelegramGameStatus {
    TelegramGameStatus {
        key: "descent".to_string(),
        kind: GameKind::Descent.as_str().to_string(),
        session: SessionId("PRIVATE-RAW-SESSION-CANARY".to_string()),
        host_incarnation: GameHostIncarnation::new([0x31; 32]).unwrap(),
        session_generation: 7,
        private_projection,
        hidden_information: true,
        turn_affordances: 2,
        proof_operations: vec!["PRIVATE-OPERATION-NAME-CANARY".to_string()],
        artifacts: vec!["PRIVATE-ARTIFACT-NAME-CANARY".to_string()],
        verified: false,
        verified_turns: 3,
        verification_detail: "PRIVATE-VERIFIER-DIAGNOSTIC-CANARY".to_string(),
        landed_steps: 4,
        replay_recipe: true,
        latest_public_receipt: None,
    }
}

#[test]
fn shared_renderer_cannot_carry_host_private_or_even_audited_result_values() {
    let status = hostile_status(false);
    let text = describe_game_status(&status);

    assert!(text.contains("shared viewer-blind projection"), "{text}");
    assert!(text.contains("1 shielded/proven operation(s)"), "{text}");
    for forbidden in [
        "PRIVATE-RAW-SESSION-CANARY",
        "PRIVATE-OPERATION-NAME-CANARY",
        "PRIVATE-ARTIFACT-NAME-CANARY",
        "PRIVATE-VERIFIER-DIAGNOSTIC-CANARY",
    ] {
        assert!(
            !text.contains(forbidden),
            "shared status leaked {forbidden}: {text}"
        );
    }
}

#[test]
fn shared_projection_refuses_private_or_cross_game_objects_before_formatting() {
    let private = hostile_status(true);
    assert!(private.shared_projection().is_err());
    let group_text = describe_game_status_for_chat(&private, -90_403, None);
    assert!(
        group_text.contains("publication boundary refused"),
        "{group_text}"
    );
    assert!(!group_text.contains("PRIVATE-"), "{group_text}");

    let mut mismatched = hostile_status(false);
    mismatched.kind = GameKind::Dungeon.as_str().to_string();
    assert!(mismatched.shared_projection().is_err());
    let text = describe_game_status(&mismatched);
    assert!(text.contains("publication boundary refused"), "{text}");
    assert!(!text.contains("PRIVATE-"), "{text}");
}

#[test]
fn a_real_bound_game_turn_populates_the_same_public_status_projection() {
    let mut host = TelegramHost::new(BOT_SECRET, MockTransport::new(), &[PLAYER]);
    let chat = -90_402;
    host.open("descent", chat, None, PLAYER)
        .expect("Descent has a viewer-blind group surface");
    let callback = host
        .frontend()
        .transport()
        .last()
        .and_then(|request| request.reply_markup.as_ref())
        .into_iter()
        .flat_map(|markup| &markup.inline_keyboard)
        .flatten()
        .map(|button| button.callback_data.as_str())
        .find(|data| data.starts_with("g."))
        .expect("the group surface carries a bound game action")
        .to_string();

    assert!(matches!(
        host.press(CallbackQuery::press(chat, PLAYER, callback)),
        HostPress::Advanced {
            outcome: Outcome::Landed { .. },
            ..
        }
    ));
    let rich = host
        .game_status(chat, None, PLAYER)
        .expect("the live game has a common status");
    let raw_session = rich.session.0.clone();
    let public = rich
        .shared_projection()
        .expect("the group status crosses the typed no-viewer boundary");
    let receipt = public
        .latest_receipt
        .as_ref()
        .expect("the bound turn retained its audited publication");
    assert_eq!(receipt.kind, GameKind::Descent);
    assert!(matches!(
        &receipt.result,
        PublicGameReceiptResult::Turn { .. }
    ));

    let text = describe_game_status(&rich);
    assert!(text.contains(&hex::encode(receipt.receipt_id)), "{text}");
    assert!(
        text.contains(&hex::encode(receipt.publication_id)),
        "{text}"
    );
    assert!(!text.contains(&raw_session), "{text}");

    // A stored/transmitted publication must still validate when it reaches the surface. Mutating
    // the outer commitment, one committed receipt input, or the typed result all fail closed.
    let mut publication_mutation = rich.clone();
    publication_mutation
        .latest_public_receipt
        .as_mut()
        .unwrap()
        .publication_id[0] ^= 1;
    assert!(publication_mutation.shared_projection().is_err());

    let mut receipt_mutation = rich.clone();
    receipt_mutation
        .latest_public_receipt
        .as_mut()
        .unwrap()
        .receipt_id[0] ^= 1;
    assert!(receipt_mutation.shared_projection().is_err());

    let mut result_mutation = rich.clone();
    result_mutation
        .latest_public_receipt
        .as_mut()
        .unwrap()
        .result = PublicGameReceiptResult::Operation {
        fields: vec![PublicGameFieldValue {
            field: PublicGameField::ProofDigest,
            value: "PRIVATE-CUSTODY-VALUE-CANARY".to_string(),
        }],
    };
    assert!(result_mutation.shared_projection().is_err());
    let refused = describe_game_status(&result_mutation);
    assert!(
        refused.contains("publication boundary refused"),
        "{refused}"
    );
    assert!(!refused.contains("PRIVATE-CUSTODY"), "{refused}");
}
