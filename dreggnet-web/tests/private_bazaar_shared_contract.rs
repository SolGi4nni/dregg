//! The browser consumes the frontend-neutral Dark Bazaar journey contract.
//! The matching Discord adapter test lives beside its generic market command;
//! both import these exact semantic action/result types from `dreggnet-market`.

use dreggnet_market::private_bazaar_journey::{
    PrivateBazaarPublicAction, PrivateBazaarPublicPhase, PrivateBazaarPublicReceipt,
};
use dreggnet_offerings::{Frontend, SessionId};
use dreggnet_web::{WebEvent, WebFrontend};

#[test]
fn web_round_trips_the_shared_payload_free_action_and_viewer_blind_receipt() {
    let session = SessionId::new("shared-private-bazaar-web");
    let receipt = PrivateBazaarPublicReceipt::pending([0x11; 32], 4, [0x22; 32], [0x33; 32]);
    let surface = receipt.surface();
    let action = PrivateBazaarPublicAction::Enter.offering_action();
    let mut web = WebFrontend::new();
    web.spin_session(session.clone());
    web.present(&session, &surface, std::slice::from_ref(&action));

    let html = web.render(&session, &surface);
    assert!(html.contains("Dark Bazaar raid"));
    for forbidden in ["winner", "reserve", "private bid", "proof bytes", "witness"] {
        assert!(!html.contains(forbidden), "web leaked {forbidden}: {html}");
    }

    let (_, collected, _) = web
        .collect(WebEvent {
            session,
            user: "browser-viewer".to_owned(),
            turn: action.turn.clone(),
            arg: action.arg,
        })
        .expect("browser POST names the presented shared action");
    assert_eq!(
        PrivateBazaarPublicAction::from_offering_action(&collected),
        Ok(PrivateBazaarPublicAction::Enter)
    );
    assert_eq!(collected.arg, 0);
    assert!(collected.text.is_none());

    let mut settled = receipt;
    settled.phase = PrivateBazaarPublicPhase::Settled;
    settled.proof_session = Some(17);
    settled.input_root = Some([7; 8]);
    settled.consequence_id = Some([0x44; 32]);
    settled.settlement_turn_hash = Some([0x55; 32]);
    settled.game_turn_hash = Some([0x66; 32]);
    settled.game_state_root = Some([0x77; 32]);
    let settled_html = web.render(&SessionId::new("settled"), &settled.surface());
    assert!(settled_html.contains("settled"), "{settled_html}");
    assert!(
        settled_html.contains("real game-engine turn"),
        "{settled_html}"
    );
    for forbidden in ["winner", "reserve", "private bid", "proof bytes", "witness"] {
        assert!(
            !settled_html.contains(forbidden),
            "settled web receipt leaked {forbidden}: {settled_html}"
        );
    }
}
