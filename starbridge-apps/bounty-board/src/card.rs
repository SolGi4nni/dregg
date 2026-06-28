//! # bounty-board — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
//!
//! The fourth axis of a modern starbridge-app: the app lives IN the deos world by
//! shipping its surface as a **renderer-independent card** — a serializable
//! `deos.ui.*` element-tree ([`deos_view::ViewNode`] in the renderer crate). The
//! SAME tree renders three ways (the renderer-independence seam): native gpui
//! pixels in the cockpit, a browser-loadable HTML document, and a discord embed —
//! all from this one piece of DATA. See `deos-view/src/{render,web,discord}.rs`
//! for the three renderers and `docs/reference/deos-view.md`.
//!
//! ## Why the card is DATA, not a renderer call
//!
//! `deos-view` pulls BOTH the SpiderMonkey (`mozjs`) and the gpui native
//! elephants, so it is a STANDALONE workspace EXCLUDED from the repo-root
//! workspace (see its `Cargo.toml`). A starbridge-app must never depend on it —
//! that would feature-unify the elephants onto the main build. So the app's
//! contribution is the **view-tree JSON** (this module): pure `serde_json`, no
//! elephant. The deos world's renderers consume it; this module owns the card
//! definition and proves it is well-formed.
//!
//! ## The card shape — a rich, live bounty surface
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) built from the rich deos-view
//! vocabulary (`section` / `pill` / `gauge` / `breadcrumb` / `divider` / `icon`):
//!
//!   - a **status header** — the app name + a `pill` naming the live state-machine
//!     stage as a WORD (`CLAIMED`), and a `breadcrumb` of the whole lifecycle
//!     (open → claimed → submitted → paid) with the current step marked;
//!   - a **"Bounty" `section`** surfacing the LIVE cell state: a `gauge` bound to
//!     [`STATE_SLOT`](crate::STATE_SLOT) (state-machine progress) and a `gauge` on the
//!     escrowed [`REWARD_SLOT`](crate::REWARD_SLOT), plus `bind`s on the reward, the
//!     [`CLAIMANT_HASH_SLOT`](crate::CLAIMANT_HASH_SLOT) and the
//!     [`TITLE_HASH_SLOT`](crate::TITLE_HASH_SLOT) — each a fine-grained signal that
//!     re-reads the live value (the SAME witnessed read a native `bind` closure
//!     makes), so the surface advances when a fired turn commits;
//!   - an **"Actions" `section`** of one `icon`+`button` row per lifecycle method
//!     (`post` / `claim` / `submit` / `payout`), each `button` carrying its
//!     `onClick = { turn, arg }` — the EXACT cap-gated verified turn a click fires
//!     through the [`invoke()`](crate::service)/affordance seam.
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary
//! ([`METHOD_POST`](crate::service::METHOD_POST), …) so the card and the service
//! cell speak the same lifecycle.

use serde_json::{Value, json};

use crate::service::{METHOD_CLAIM, METHOD_PAYOUT, METHOD_POST, METHOD_SUBMIT};
use crate::{
    CLAIMANT_HASH_SLOT, REWARD_SLOT, STATE_CLAIMED, STATE_OPEN, STATE_PAID, STATE_SLOT,
    STATE_SUBMITTED, TITLE_HASH_SLOT,
};

/// The reward bar's denominator — a representative escrow ceiling so a fully-funded
/// bounty fills the gauge (the seeded reward is `1_000`).
const REWARD_GAUGE_MAX: u64 = 1_000;

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A LIVE `deos.ui.pill` node — reads `slot` immediate-mode and maps the value to a
/// word + color via `cases` (the first `{value,label,tag}` matching the slot wins).
/// `text`/`tag` are the static fallback (discord, or no match).
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
/// display `fmt` (`"id"` avatar-handle / `"hash"` short-hex / `"amount"` grouped /
/// `"raw"` plain) so an opaque 20-digit key/amount paints short + friendly.
fn bind(slot: usize, label: &str, fmt: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt } })
}

/// A `deos.ui.gauge` node — a bound progress bar (`slot_value / max`, immediate-mode).
/// `adept` hides the raw numeric in the simple projection (the live pill + breadcrumb
/// already show the stage); revealed in the adept "see the bones" view.
fn gauge(slot: usize, max: u64, label: &str, adept: bool) -> Value {
    json!({ "kind": "gauge", "props": { "slot": slot, "max": max, "label": label, "adept": adept } })
}

/// A `deos.ui.breadcrumb` node — the lifecycle path; the `active` step is marked `▸`.
fn breadcrumb(steps: &[&str], active: usize) -> Value {
    let items: Vec<Value> = steps
        .iter()
        .enumerate()
        .map(|(i, s)| {
            let label = if i == active {
                format!("› {s}")
            } else {
                s.to_string()
            };
            json!({ "label": label })
        })
        .collect();
    json!({ "kind": "breadcrumb", "props": { "items": items } })
}

/// A `deos.ui.button` node carrying its affordance payload `onClick = {turn, arg}`.
fn button(label: &str, turn: &str, arg: i64) -> Value {
    json!({
        "kind": "button",
        "props": { "label": label, "onClick": { "turn": turn, "arg": arg } }
    })
}

/// An action row — an `icon` + a lifecycle `button` (the verified-turn affordance).
fn action(glyph: &str, label: &str, turn: &str) -> Value {
    row(vec![icon(glyph, "accent"), button(label, turn, 0)])
}

/// **The bounty-board card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A rich, live bounty surface: a status header (name + `CLAIMED` pill + lifecycle
/// breadcrumb), a "Bounty" section surfacing the live state-machine gauge, the
/// escrowed-reward gauge, and the reward / claimant / title binds, and an "Actions"
/// section of the four icon-labelled lifecycle buttons. Renderer-independent DATA.
/// The button `turn` names are the [`service`](crate::service) method symbols.
pub fn bounty_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            row(vec![text("Bounty Board"), pill_live(STATE_SLOT, "CLAIMED", "accent", json!([
                { "value": STATE_OPEN,      "label": "OPEN",      "tag": "warn" },
                { "value": STATE_CLAIMED,   "label": "CLAIMED",   "tag": "accent" },
                { "value": STATE_SUBMITTED, "label": "SUBMITTED", "tag": "accent" },
                { "value": STATE_PAID,      "label": "PAID",      "tag": "good" },
            ]))]),
            breadcrumb(&["Open", "Claimed", "Submitted", "Paid"], 1),
            divider(),
            section("Bounty", "genuine", vec![
                gauge(STATE_SLOT, STATE_PAID, "stage ", true),
                gauge(REWARD_SLOT, REWARD_GAUGE_MAX, "escrowed reward ", false),
                bind(REWARD_SLOT, "reward · ", "amount"),
                bind(CLAIMANT_HASH_SLOT, "claimant · ", "id"),
                bind(TITLE_HASH_SLOT, "title hash · ", "hash"),
            ]),
            section("Actions", "", vec![
                action("+", "Post",    METHOD_POST),
                action("›", "Claim",   METHOD_CLAIM),
                action("→", "Submit",  METHOD_SUBMIT),
                action("✓", "Payout",  METHOD_PAYOUT),
            ]),
        ]
    })
}

/// **The bounty-board card as serialized `deos.ui.*` JSON** — byte-for-byte the
/// `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn bounty_card_json() -> String {
    serde_json::to_string(&bounty_card_value()).expect("the bounty card serializes")
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn the_card_is_a_vstack_with_a_named_header_and_a_state_pill() {
        let card = bounty_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts.iter().any(|t| t["props"]["text"] == "Bounty Board"),
            "the header names the app"
        );
        let pills = of_kind(&card, "pill");
        assert_eq!(pills.len(), 1);
        // The header pill is LIVE: it reads STATE_SLOT and maps the value to a word.
        assert_eq!(
            pills[0]["props"]["text"], "CLAIMED",
            "the static fallback word"
        );
        assert_eq!(pills[0]["props"]["slot"], STATE_SLOT);
        let cases = pills[0]["props"]["cases"].as_array().unwrap();
        assert_eq!(cases.len(), 4, "OPEN / CLAIMED / SUBMITTED / PAID");
        assert_eq!(cases[3]["value"], STATE_PAID);
        assert_eq!(cases[3]["label"], "PAID");
    }

    #[test]
    fn the_reward_and_identity_binds_carry_their_display_fmt() {
        let card = bounty_card_value();
        let binds = of_kind(&card, "bind");
        let fmt = |slot: usize| -> String {
            binds
                .iter()
                .find(|b| b["props"]["slot"].as_u64() == Some(slot as u64))
                .and_then(|b| b["props"]["fmt"].as_str())
                .unwrap()
                .to_string()
        };
        assert_eq!(fmt(REWARD_SLOT), "amount", "the reward groups digits");
        assert_eq!(
            fmt(CLAIMANT_HASH_SLOT),
            "id",
            "the claimant paints an avatar handle"
        );
        assert_eq!(
            fmt(TITLE_HASH_SLOT),
            "hash",
            "the title hash paints short hex"
        );
    }

    #[test]
    fn the_lifecycle_breadcrumb_marks_the_current_step() {
        let card = bounty_card_value();
        let crumbs = of_kind(&card, "breadcrumb");
        assert_eq!(crumbs.len(), 1);
        let items = crumbs[0]["props"]["items"].as_array().unwrap();
        assert_eq!(items.len(), 4, "open → claimed → submitted → paid");
        assert_eq!(items[1]["label"], "› Claimed", "the active step is marked");
    }

    #[test]
    fn the_state_and_reward_gauges_read_the_live_slots() {
        let card = bounty_card_value();
        let gauges = of_kind(&card, "gauge");
        assert_eq!(gauges.len(), 2, "a state-machine gauge + an escrow gauge");
        assert_eq!(gauges[0]["props"]["slot"], STATE_SLOT);
        assert_eq!(gauges[0]["props"]["max"], STATE_PAID);
        assert_eq!(gauges[1]["props"]["slot"], REWARD_SLOT);

        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                REWARD_SLOT as u64,
                CLAIMANT_HASH_SLOT as u64,
                TITLE_HASH_SLOT as u64
            ],
            "the binds surface reward / claimant / title"
        );
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = bounty_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 4);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the service method vocabulary.
        assert_eq!(
            turns,
            vec![METHOD_POST, METHOD_CLAIM, METHOD_SUBMIT, METHOD_PAYOUT]
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = bounty_card_json();
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, breadcrumb, divider, bounty section, actions section
        assert_eq!(back["children"].as_array().unwrap().len(), 5);
    }
}
