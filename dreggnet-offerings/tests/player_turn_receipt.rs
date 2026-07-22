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
