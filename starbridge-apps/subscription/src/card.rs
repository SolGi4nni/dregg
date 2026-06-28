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

use crate::service::{
    METHOD_CONSUME, METHOD_GRANT_CONSUMER, METHOD_GRANT_PUBLISHER, METHOD_PUBLISH,
};
use crate::{
    CAPACITY_SLOT, CONSUMERS_ROOT_SLOT, LATEST_PAYLOAD_SLOT, MESSAGE_ROOT_SLOT, OWNER_PK_HASH_SLOT,
    PUBLISHERS_ROOT_SLOT, SEQ_HEAD_SLOT, SEQ_TAIL_SLOT,
};

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A `deos.ui.pill` node — a colored status badge tinted by `tag`.
fn pill(label: &str, tag: &str) -> Value {
    json!({ "kind": "pill", "props": { "text": label, "tag": tag } })
}

/// A LIVE `deos.ui.pill` node — reads `slot` immediate-mode and maps the value to a word +
/// color via `cases` (the first `{value,label,tag}` matching the slot wins). `text`/`tag`
/// are the static fallback (discord, or no match).
fn pill_live(slot: usize, label: &str, tag: &str, cases: Value) -> Value {
    json!({ "kind": "pill", "props": { "text": label, "tag": tag, "slot": slot, "cases": cases } })
}

/// A `deos.ui.icon` node — a glyph indicator tinted by `tag`.
fn icon(glyph: &str, tag: &str) -> Value {
    json!({ "kind": "icon", "props": { "glyph": glyph, "tag": tag } })
}

/// A `deos.ui.divider` node — a full-width groove rule.
fn divider() -> Value {
    json!({ "kind": "divider", "props": {} })
}

/// A `deos.ui.row` node — a horizontal flex of children.
fn row(children: Vec<Value>) -> Value {
    json!({ "kind": "row", "props": {}, "children": children })
}

/// A `deos.ui.section` node — a titled, bordered container.
fn section(title: &str, tag: &str, children: Vec<Value>) -> Value {
    json!({ "kind": "section", "props": { "title": title, "tag": tag }, "children": children })
}

/// A `deos.ui.bind` node tagged with the model `slot` it re-reads + a label prefix and a
/// display `fmt` (`"id"` avatar-handle / `"hash"` short-hex / `"amount"` grouped / `"raw"`
/// plain) so an opaque key/root/amount paints short + friendly instead of a 20-digit decimal.
fn bind(slot: usize, label: &str, fmt: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt } })
}

/// An `adept`-tagged `bind` — the dev-y "see the bones" detail (here the opaque Merkle roots
/// over the publisher/consumer/message sets) the `simple` projection hides and `adept`
/// reveals. The friendly head/tail/owner signals stay in the simple view.
fn bind_adept(slot: usize, label: &str, fmt: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt, "adept": true } })
}

/// A `deos.ui.progress` node — a STATIC (literal-valued) bar (`value / max`). The billing card
/// renders from a [`SubscriptionStatus`] snapshot (not a live backing cell), so its progress is
/// literal, not a live slot read.
fn progress(value: u64, max: u64, label: &str) -> Value {
    json!({ "kind": "progress", "props": { "value": value, "max": max, "label": label } })
}

/// Group a decimal's digits in threes (`1234567 → 1,234,567`) — the inline consumer-delight for
/// an amount (the static-card analogue of a `bind`'s `fmt:"amount"`, with no live slot to read).
fn group_digits(value: i64) -> String {
    let neg = value < 0;
    let s = value.unsigned_abs().to_string();
    let bytes = s.as_bytes();
    let len = bytes.len();
    let mut out = String::with_capacity(len + len / 3 + 1);
    if neg {
        out.push('-');
    }
    for (i, b) in bytes.iter().enumerate() {
        if i > 0 && (len - i) % 3 == 0 {
            out.push(',');
        }
        out.push(*b as char);
    }
    out
}

/// A `deos.ui.button` node carrying its affordance payload `onClick = {turn, arg}`.
fn button(label: &str, turn: &str, arg: i64) -> Value {
    json!({
        "kind": "button",
        "props": { "label": label, "onClick": { "turn": turn, "arg": arg } }
    })
}

/// An action row — an `icon` + a lifecycle `button` (the verified-turn affordance).
fn action(glyph: &str, label: &str, turn: &str, arg: i64) -> Value {
    row(vec![icon(glyph, "accent"), button(label, turn, arg)])
}

/// **The subscription card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A rich, live pub/sub feed surface: a status header (the app name + a LIVE `pill` reading
/// [`CAPACITY_SLOT`](crate::CAPACITY_SLOT) — `SETUP` until the feed is configured, `LIVE`
/// after), a "Feed" `section` surfacing the live cursors and identities (the producer/consumer
/// heads stay raw — they are small counters; the owner paints an avatar handle, the
/// latest-payload paints short hex, and the opaque Merkle roots lift as `adept` bones), and an
/// "Actions" `section` of one `icon`+`button` row per method. Renderer-independent DATA. The
/// button `turn` names are the [`crate::service`] method symbols (unchanged, arg `0`).
pub fn subscription_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            row(vec![text("Subscription Feed"), pill_live(CAPACITY_SLOT as usize, "LIVE", "good", json!([
                // An unconfigured (capacity == 0) feed reads SETUP; a configured one falls
                // through to the static LIVE — the `configured_precondition` (CAPACITY >= 1) as a word.
                { "value": 0, "label": "SETUP", "tag": "muted" },
            ]))]),
            divider(),
            section("Feed", "genuine", vec![
                // The cursors are small counters — they stay raw (no avatar/hex/grouping).
                bind(SEQ_HEAD_SLOT as usize, "head · ", "raw"),
                bind(SEQ_TAIL_SLOT as usize, "tail · ", "raw"),
                bind(CAPACITY_SLOT as usize, "capacity · ", "amount"),
                bind(OWNER_PK_HASH_SLOT as usize, "owner · ", "id"),
                bind(LATEST_PAYLOAD_SLOT as usize, "latest payload · ", "hash"),
                // The opaque set-membership roots are dev-y bones — adept-only.
                bind_adept(MESSAGE_ROOT_SLOT as usize, "message root · ", "hash"),
                bind_adept(PUBLISHERS_ROOT_SLOT as usize, "publishers root · ", "hash"),
                bind_adept(CONSUMERS_ROOT_SLOT as usize, "consumers root · ", "hash"),
            ]),
            section("Actions", "", vec![
                action("+", "Publish",         METHOD_PUBLISH,         0),
                action("→", "Consume",         METHOD_CONSUME,         0),
                action("✓", "Grant Publisher", METHOD_GRANT_PUBLISHER, 0),
                action("✓", "Grant Consumer",  METHOD_GRANT_CONSUMER,  0),
            ]),
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
    // The live lifecycle as a WORD + color (the value→word pill, computed from the committed
    // status snapshot rather than a live slot — the billing card has no single backing cell).
    let (word, tag) = if status.cancelled {
        ("CANCELLED", "muted")
    } else if status.lapsed {
        ("LAPSED", "bad")
    } else if status.completed {
        ("COMPLETED", "accent")
    } else {
        ("ACTIVE", "good")
    };
    // Payment progress: periods paid out of the periods the schedule demands by now (the lapse
    // gap made legible). A snapshot, so a STATIC literal-valued bar.
    let demanded = status.periods_due_by_now.max(status.periods_paid).max(1) as u64;
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            row(vec![text("Subscription Billing"), pill(word, tag)]),
            divider(),
            section("Plan", "genuine", vec![
                row(vec![
                    icon("◈", "good"),
                    text(&format!("price · {}/period", group_digits(price))),
                ]),
                progress(status.periods_paid.max(0) as u64, demanded, "periods paid "),
                text(&format!(
                    "periods paid · {} (total {})",
                    group_digits(status.periods_paid),
                    group_digits(status.total_paid),
                )),
                text(&format!("next due · block {}", status.next_due_block)),
            ]),
            section("Actions", "", vec![
                action("+", "Subscribe",  "subscribe", 0),
                action("→", "Pay Period", "pay",       price),
                action("↻", "Renew",      "renew",     1),
                action("✕", "Cancel",     "cancel",    0),
            ]),
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

    /// Walk the tree collecting every node of `kind`.
    fn collect<'a>(node: &'a Value, kind: &str, out: &mut Vec<&'a Value>) {
        if node["kind"] == kind {
            out.push(node);
        }
        if let Some(children) = node["children"].as_array() {
            for c in children {
                collect(c, kind, out);
            }
        }
    }
    fn of_kind<'a>(card: &'a Value, kind: &str) -> Vec<&'a Value> {
        let mut out = Vec::new();
        collect(card, kind, &mut out);
        out
    }

    #[test]
    fn the_card_is_a_vstack_with_a_named_header_and_a_live_status_pill() {
        let card = subscription_card_value();
        assert_eq!(card["kind"], "vstack");
        // header row, divider, Feed section, Actions section.
        let children = card["children"].as_array().expect("children");
        assert_eq!(children.len(), 4);
        let texts = of_kind(&card, "text");
        assert!(
            texts
                .iter()
                .any(|t| t["props"]["text"] == "Subscription Feed"),
            "the header names the app"
        );
        // The header pill is LIVE: it reads CAPACITY_SLOT (SETUP until configured).
        let header_pill = &card["children"][0]["children"][1];
        assert_eq!(header_pill["kind"], "pill");
        assert_eq!(header_pill["props"]["slot"], CAPACITY_SLOT as usize);
        let cases = header_pill["props"]["cases"].as_array().unwrap();
        assert_eq!(cases.len(), 1);
        assert_eq!(cases[0]["value"], 0);
        assert_eq!(cases[0]["label"], "SETUP");
        assert_eq!(
            header_pill["props"]["text"], "LIVE",
            "the configured fallback word"
        );
    }

    #[test]
    fn the_feed_binds_carry_their_display_fmt_and_the_roots_are_adept() {
        let card = subscription_card_value();
        let binds = of_kind(&card, "bind");
        let bind_for = |slot: usize| -> &Value {
            binds
                .iter()
                .find(|b| b["props"]["slot"].as_u64() == Some(slot as u64))
                .copied()
                .unwrap()
        };
        // The producer cursor is still surfaced (raw — it is a small counter, not an id/amount).
        assert_eq!(bind_for(SEQ_HEAD_SLOT as usize)["props"]["fmt"], "raw");
        assert_eq!(bind_for(SEQ_TAIL_SLOT as usize)["props"]["fmt"], "raw");
        assert_eq!(bind_for(CAPACITY_SLOT as usize)["props"]["fmt"], "amount");
        // The owner key paints an avatar handle; the payload + roots paint short hex.
        assert_eq!(bind_for(OWNER_PK_HASH_SLOT as usize)["props"]["fmt"], "id");
        assert_eq!(
            bind_for(LATEST_PAYLOAD_SLOT as usize)["props"]["fmt"],
            "hash"
        );
        // The opaque set-membership roots are adept-only (dev-y bones).
        for slot in [MESSAGE_ROOT_SLOT, PUBLISHERS_ROOT_SLOT, CONSUMERS_ROOT_SLOT] {
            let b = bind_for(slot as usize);
            assert_eq!(b["props"]["fmt"], "hash");
            assert_eq!(b["props"]["adept"], true, "the {slot} root is adept-only");
        }
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = subscription_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 4);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the service method vocabulary (unchanged).
        assert_eq!(
            turns,
            vec![
                METHOD_PUBLISH,
                METHOD_CONSUME,
                METHOD_GRANT_PUBLISHER,
                METHOD_GRANT_CONSUMER
            ]
        );
        // Their args are unchanged (all 0).
        for b in &buttons {
            assert_eq!(b["props"]["onClick"]["arg"], 0);
        }
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = subscription_card_json();
        // Round-trips through serde (the shape a deos-view renderer's parser reads).
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        assert_eq!(back["children"].as_array().unwrap().len(), 4);
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
        // The lifecycle buttons keep their turns + args (subscribe/pay/renew/cancel).
        let buttons = of_kind(&card, "button");
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        assert_eq!(turns, vec!["subscribe", "pay", "renew", "cancel"]);
        assert_eq!(
            buttons[1]["props"]["onClick"]["arg"], 50,
            "Pay carries the price"
        );
        assert_eq!(
            buttons[2]["props"]["onClick"]["arg"], 1,
            "Renew carries +1 period"
        );

        // The lifecycle renders as a value→word pill (one period paid, on schedule → ACTIVE).
        let pills = of_kind(&card, "pill");
        assert!(
            pills
                .iter()
                .any(|p| p["props"]["text"] == "ACTIVE" && p["props"]["tag"] == "good"),
            "the active lifecycle is a good-tagged ACTIVE pill"
        );
        // The committed status renders through friendly rows (grouped amounts).
        let texts = of_kind(&card, "text");
        assert!(
            texts
                .iter()
                .any(|t| t["props"]["text"] == "periods paid · 1 (total 50)"),
            "the committed paid count renders as a friendly row"
        );
        // A static payment-progress bar is present.
        assert_eq!(of_kind(&card, "progress").len(), 1);
        // And it serializes.
        let _ = billing_card_json(&sub.status(1050), 50);
    }

    #[test]
    fn the_billing_pill_maps_each_lifecycle_to_a_word() {
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
        // A lapsed subscriber (paid period 0, far behind by clock 1250) → LAPSED / bad.
        let mut behind = Subscription::subscribe(plan.clone()).unwrap();
        behind.pay(1000).unwrap();
        let card = billing_card_value(&behind.status(1250), 50);
        let pills = of_kind(&card, "pill");
        assert!(
            pills
                .iter()
                .any(|p| p["props"]["text"] == "LAPSED" && p["props"]["tag"] == "bad"),
            "a behind-schedule subscription is a bad-tagged LAPSED pill"
        );

        // A cancelled subscriber → CANCELLED / muted.
        let mut cancelled = Subscription::subscribe(plan).unwrap();
        cancelled.pay(1000).unwrap();
        cancelled.cancel().unwrap();
        let card = billing_card_value(&cancelled.status(2000), 50);
        let pills = of_kind(&card, "pill");
        assert!(
            pills
                .iter()
                .any(|p| p["props"]["text"] == "CANCELLED" && p["props"]["tag"] == "muted"),
            "a cancelled subscription is a muted CANCELLED pill"
        );
    }
}
