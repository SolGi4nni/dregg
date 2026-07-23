use dregg_app_framework::TurnReceipt;
use dreggnet_offerings::player_turn_receipt::{
    PlayerReplaySurface, PlayerSessionDisposition, PlayerTurnReceipt,
};

fn receipt(hash: [u8; 32]) -> TurnReceipt {
    TurnReceipt {
        previous_receipt_hash: Some([3; 32]),
        turn_hash: hash,
        ..TurnReceipt::default()
    }
}

#[test]
fn every_surface_gets_the_complete_same_receipt_join() {
    let source = receipt([0xab; 32]);
    let card = PlayerTurnReceipt::from_landed(&source, false);
    let full = hex::encode(source.receipt_hash());

    for surface in [
        PlayerReplaySurface::Discord,
        PlayerReplaySurface::DiscordDungeon,
        PlayerReplaySurface::Web,
        PlayerReplaySurface::Telegram,
    ] {
        let rendered = card.compact_text(surface);
        assert!(rendered.contains(&full), "{rendered}");
        assert!(rendered.contains("Session continues."), "{rendered}");
    }
    assert_eq!(card.receipt_id(), &source.receipt_hash());
    assert_eq!(card.disposition(), PlayerSessionDisposition::Continues);
}

#[test]
fn card_binds_the_complete_receipt_not_only_the_turn_hash() {
    let first = receipt([0xab; 32]);
    let mut changed = first.clone();
    changed.post_state_hash = [0xee; 32];
    assert_eq!(
        first.turn_hash, changed.turn_hash,
        "hostile pair shares turn id"
    );

    let first_card = PlayerTurnReceipt::from_landed(&first, false);
    let changed_card = PlayerTurnReceipt::from_landed(&changed, false);
    assert_ne!(
        first_card.receipt_id(),
        changed_card.receipt_id(),
        "a receipt-field substitution must change the player-visible chain join"
    );
}

/// FIX #2: the lead phrase differs by attribution grade — an asserted turn is never dressed as
/// "Verified"/"Signed", and a custodial signature is honestly distinguished from a user-held one.
#[test]
fn the_lead_phrase_differs_by_attribution_grade() {
    use dreggnet_offerings::Custody;
    let src = receipt([0x11; 32]);
    let signer = "ab".repeat(32);

    let asserted =
        PlayerTurnReceipt::from_landed(&src, false).compact_text(PlayerReplaySurface::Web);
    let custodial =
        PlayerTurnReceipt::from_landed_signed(&src, false, Custody::Custodial, signer.clone())
            .compact_text(PlayerReplaySurface::Web);
    let user_held =
        PlayerTurnReceipt::from_landed_signed(&src, false, Custody::UserHeld, signer.clone())
            .compact_text(PlayerReplaySurface::Web);

    // Each grade renders a distinct, honest lead phrase.
    assert!(asserted.starts_with("Recorded (asserted)"), "{asserted}");
    assert!(
        !asserted.contains("Signed") && !asserted.contains("Verified"),
        "an asserted turn is never dressed as Signed/Verified: {asserted}"
    );
    assert!(
        custodial.starts_with(&format!("Signed (custodial) by {signer}")),
        "{custodial}"
    );
    assert!(
        user_held.starts_with(&format!("Signed by {signer}")),
        "{user_held}"
    );
    // Custodial is honest that the SERVER signed; user-held is not.
    assert!(custodial.contains("custodial"));
    assert!(
        !user_held.contains("custodial"),
        "a user-held signature is not custodial: {user_held}"
    );
    // All three still carry the executor receipt join + lifecycle + replay control.
    for text in [&asserted, &custodial, &user_held] {
        assert!(text.contains(&hex::encode(src.receipt_hash())), "{text}");
        assert!(text.contains("Session continues."), "{text}");
        assert!(text.contains("Replay-verify"), "{text}");
    }
    // Pairwise distinct — the collapse the fix removed.
    assert_ne!(asserted, custodial);
    assert_ne!(asserted, user_held);
    assert_ne!(custodial, user_held);
}

#[test]
fn operation_projection_does_not_invent_a_session_outcome() {
    let card =
        PlayerTurnReceipt::from_verified_id([0xcd; 32], PlayerSessionDisposition::Undisclosed);
    let rendered = card.compact_text(PlayerReplaySurface::Discord);
    assert!(rendered.contains(&"cd".repeat(32)), "{rendered}");
    assert!(rendered.contains("not disclosed"), "{rendered}");
    assert!(!rendered.contains("continues"), "{rendered}");
    assert!(!rendered.contains("complete."), "{rendered}");
}
