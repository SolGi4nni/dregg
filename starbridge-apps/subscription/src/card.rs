//! # subscription — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
//!
//! The fourth axis (AX4) of a modern starbridge-app: the app lives IN the deos
//! world by shipping its surface as a **renderer-independent card** — a
//! serializable `deos.ui.*` element-tree ([`deos_view::ViewNode`] in the renderer
//! crate). The SAME tree renders three ways (the renderer-independence seam): native
//! gpui pixels in the cockpit, a browser-loadable HTML document, and a discord embed
//! — all from this one piece of DATA. See `deos-view/src/{render,web,discord}.rs`
//! for the three renderers and `docs/reference/deos-view.md`.
//!
//! ## Why the card is DATA, not a renderer call
//!
//! `deos-view` pulls BOTH the SpiderMonkey (`mozjs`) and the gpui native elephants,
//! so it is a STANDALONE workspace EXCLUDED from the repo-root workspace. A
//! starbridge-app must never depend on it — that would feature-unify the elephants
//! onto the main build. So the app's contribution is the **view-tree JSON** (this
//! module): pure `serde_json`, no elephant. The deos world's renderers consume it.
//!
//! ## The card shape
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) carrying:
//!   - a `text` header (`"Subscription Feed"`);
//!   - a `bind` on [`crate::SEQ_HEAD_SLOT`] — a fine-grained signal that re-reads the
//!     live producer cursor off the ledger, so the displayed head advances when a
//!     fired publish commits;
//!   - one `button` per mutating method (`publish` / `consume` / `grant_publisher` /
//!     `grant_consumer`), each carrying its `onClick = { turn, arg }` — the EXACT
//!     cap-gated verified turn a click fires through the [`crate::service`] front
//!     door (the button's payload is the method symbol the service routes).
//!
//! The button `turn` names match the [`crate::service`] method vocabulary
//! ([`METHOD_PUBLISH`](crate::service::METHOD_PUBLISH), …) so the card and the
//! service cell speak the same queue.

use serde_json::{Value, json};

use crate::SEQ_HEAD_SLOT;
use crate::service::{
    METHOD_CONSUME, METHOD_GRANT_CONSUMER, METHOD_GRANT_PUBLISHER, METHOD_PUBLISH,
};

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A `deos.ui.bind` node tagged with the model `slot` it re-reads + a label prefix
/// (the engine drops the closure on serialize, so the slot is tagged).
fn bind(slot: usize, label: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label } })
}

/// A `deos.ui.button` node carrying its affordance payload `onClick = {turn, arg}`.
fn button(label: &str, turn: &str, arg: i64) -> Value {
    json!({
        "kind": "button",
        "props": { "label": label, "onClick": { "turn": turn, "arg": arg } }
    })
}

/// **The subscription card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A `vstack` of a header, a live `bind` on the producer cursor
/// [`SEQ_HEAD_SLOT`](crate::SEQ_HEAD_SLOT), and the four mutating buttons.
/// Renderer-independent DATA: hand it to any `deos-view` renderer (native / web /
/// discord) to paint the SAME card. The button `turn` names are the
/// [`crate::service`] method symbols.
pub fn subscription_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            text("Subscription Feed"),
            bind(SEQ_HEAD_SLOT as usize, "head: "),
            button("Publish",         METHOD_PUBLISH,         0),
            button("Consume",         METHOD_CONSUME,         0),
            button("Grant Publisher", METHOD_GRANT_PUBLISHER, 0),
            button("Grant Consumer",  METHOD_GRANT_CONSUMER,  0),
        ]
    })
}

/// **The subscription card as serialized `deos.ui.*` JSON** — byte-for-byte the
/// `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn subscription_card_json() -> String {
    serde_json::to_string(&subscription_card_value()).expect("the subscription card serializes")
}

/// **The recurring-BILLING card** as a `deos.ui.*` view-tree — the face of the proven
/// [`StandingObligation`](dregg_cell::obligation_standing) core
/// ([`crate::obligation`]). Where [`subscription_card_value`] shows the pub/sub feed,
/// this card shows the *billing* half of a subscription: the live plan price, the
/// temporal cursor (next-due block), the periods paid, and the lapse status — plus the
/// real lifecycle buttons (`subscribe` / `pay` / `renew` / `cancel`).
///
/// The values are rendered from a [`crate::obligation::SubscriptionStatus`] so the card
/// always reflects the committed obligation state (not a hand-tracked counter). The
/// `pay` button fires the real per-period [`Effect::Transfer`](dregg_app_framework::Effect)
/// (the Payable DSI) while the proven obligation enforces the schedule.
pub fn billing_card_value(status: &crate::obligation::SubscriptionStatus, price: i64) -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            text("Subscription Billing"),
            text(&format!("price/period: {price}")),
            text(&format!("next due @ block: {}", status.next_due_block)),
            text(&format!("periods paid: {} (total {})", status.periods_paid, status.total_paid)),
            text(if status.cancelled {
                "status: cancelled"
            } else if status.lapsed {
                "status: LAPSED"
            } else if status.completed {
                "status: completed"
            } else {
                "status: active"
            }),
            button("Subscribe", "subscribe", 0),
            button("Pay Period", "pay",       price),
            button("Renew",      "renew",     1),
            button("Cancel",     "cancel",    0),
        ]
    })
}

/// The billing card serialized to `deos.ui.*` JSON — the string a host serves / embeds.
pub fn billing_card_json(status: &crate::obligation::SubscriptionStatus, price: i64) -> String {
    serde_json::to_string(&billing_card_value(status, price)).expect("the billing card serializes")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_card_is_a_vstack_with_a_header_a_head_bind_and_four_buttons() {
        let card = subscription_card_value();
        assert_eq!(card["kind"], "vstack");
        let children = card["children"].as_array().expect("children");
        // header, bind, publish, consume, grant_publisher, grant_consumer
        assert_eq!(children.len(), 6);
        assert_eq!(children[0]["kind"], "text");
        assert_eq!(children[0]["props"]["text"], "Subscription Feed");
    }

    #[test]
    fn the_head_bind_reads_the_producer_cursor_slot() {
        let card = subscription_card_value();
        let bind = &card["children"][1];
        assert_eq!(bind["kind"], "bind");
        assert_eq!(bind["props"]["slot"], SEQ_HEAD_SLOT as usize);
        assert_eq!(bind["props"]["label"], "head: ");
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = subscription_card_value();
        let children = card["children"].as_array().unwrap();
        let buttons: Vec<&Value> = children.iter().filter(|c| c["kind"] == "button").collect();
        assert_eq!(buttons.len(), 4);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the service method vocabulary.
        assert_eq!(
            turns,
            vec![
                METHOD_PUBLISH,
                METHOD_CONSUME,
                METHOD_GRANT_PUBLISHER,
                METHOD_GRANT_CONSUMER
            ]
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = subscription_card_json();
        // Round-trips through serde (the shape a deos-view renderer's parser reads).
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        assert_eq!(back["children"].as_array().unwrap().len(), 6);
    }

    #[test]
    fn the_billing_card_shows_the_obligation_status_and_lifecycle_buttons() {
        use crate::obligation::{BillingPlan, Subscription};
        use dregg_app_framework::CellId;

        let plan = BillingPlan::new(
            CellId::from_bytes([1; 32]),
            CellId::from_bytes([2; 32]),
            CellId::from_bytes([9; 32]),
            50,
            100,
            1000,
            0,
        );
        let mut sub = Subscription::subscribe(plan).unwrap();
        sub.pay(1000).unwrap();
        let card = billing_card_value(&sub.status(1050), 50);

        assert_eq!(card["kind"], "vstack");
        let children = card["children"].as_array().unwrap();
        // header + 4 status texts + 4 lifecycle buttons.
        let buttons: Vec<&Value> = children.iter().filter(|c| c["kind"] == "button").collect();
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        assert_eq!(turns, vec!["subscribe", "pay", "renew", "cancel"]);
        // The status text reflects the committed obligation (one period paid, active).
        assert!(
            children
                .iter()
                .any(|c| c["props"]["text"] == "periods paid: 1 (total 50)")
        );
        assert!(
            children
                .iter()
                .any(|c| c["props"]["text"] == "status: active")
        );
        // And it serializes.
        let _ = billing_card_json(&sub.status(1050), 50);
    }
}
