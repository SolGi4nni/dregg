//! # compute-exchange — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
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
//! ## The card shape — a rich, live compute-market surface
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) built from the rich deos-view
//! vocabulary (`section` / `pill` / `gauge` / `breadcrumb` / `divider` / `icon`):
//!
//!   - a **status header** — the app name + a `pill` naming the live state-machine
//!     stage as a WORD (`BIDDING`), and a `breadcrumb` of the whole lifecycle
//!     (Posted → Bidding → Settled) with the current step marked;
//!   - a **"Job" `section`** surfacing the LIVE job terms: a `gauge` bound to
//!     [`STATE_SLOT`](crate::STATE_SLOT) (lifecycle-phase progress, maxing at
//!     [`STATE_SETTLED`](crate::STATE_SETTLED)) and a `gauge` on the accepted
//!     [`BID_SLOT`](crate::BID_SLOT) read against the budget ceiling (the BUDGET
//!     gate, visualized), plus `bind`s on the budget, the accepted bid, the sealed
//!     [`SPEC_HASH_SLOT`](crate::SPEC_HASH_SLOT), and the requester / provider
//!     identities — each a fine-grained signal that re-reads the live value (the
//!     SAME witnessed read a native `bind` closure makes), so the surface advances
//!     when a fired turn commits;
//!   - a **"Settlement" `section`** surfacing the FLASHWELL split: `bind`s on the
//!     funds paid to the provider ([`PAID_SLOT`](crate::PAID_SLOT)) and refunded to
//!     the requester ([`REFUNDED_SLOT`](crate::REFUNDED_SLOT)) — the conserving
//!     `PAID + REFUNDED == BUDGET` payout, shown live;
//!   - an **"Actions" `section`** of one `icon`+`button` row per lifecycle method
//!     (`post` / `bid` / `settle`), each `button` carrying its `onClick = { turn,
//!     arg }` — the EXACT cap-gated verified turn a click fires through the
//!     [`invoke()`](crate::service)/affordance seam.
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary
//! ([`METHOD_POST`](crate::service::METHOD_POST), …) so the card and the service
//! cell speak the same lifecycle.

use serde_json::{Value, json};

use crate::service::{METHOD_BID, METHOD_POST, METHOD_SETTLE};
use crate::{
    BID_SLOT, BUDGET_SLOT, PAID_SLOT, PROVIDER_HASH_SLOT, REFUNDED_SLOT, REQUESTER_HASH_SLOT,
    SPEC_HASH_SLOT, STATE_BID, STATE_POSTED, STATE_SETTLED, STATE_SLOT,
};

/// The bid gauge's denominator — a representative budget ceiling so a bid that
/// draws the full budget fills the gauge (the seeded budget is `1_000`). The BUDGET
/// gate (`FieldLteField { BID <= BUDGET }`) means a live bid never exceeds it, so
/// the bar is the budget-draw ratio made visible.
const BUDGET_GAUGE_MAX: u64 = 1_000;

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A `deos.ui.pill` node — a colored status badge.
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
/// `"raw"` plain) so an opaque 20-digit key/amount paints short + friendly. `adept`
/// hides a dev-y row (a sealed digest the friendlier signals already cover) from the
/// simple projection; revealed in the adept "see the bones" view.
fn bind(slot: usize, label: &str, fmt: &str, adept: bool) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt, "adept": adept } })
}

/// A `deos.ui.gauge` node — a bound progress bar (`slot_value / max`, immediate-mode).
/// `adept` hides the raw numeric in the simple projection (the live pill + breadcrumb
/// already show the stage); revealed in the adept "see the bones" view.
fn gauge(slot: usize, max: u64, label: &str, adept: bool) -> Value {
    json!({ "kind": "gauge", "props": { "slot": slot, "max": max, "label": label, "adept": adept } })
}

/// A `deos.ui.breadcrumb` node — the lifecycle path; the `active` step is marked `›`.
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

/// **The compute-exchange card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A rich, live compute-market surface: a status header (name + `BIDDING` pill +
/// lifecycle breadcrumb), a "Job" section surfacing the live lifecycle-phase gauge,
/// the bid-vs-budget gauge, and the budget / bid / spec / requester / provider
/// binds, a "Settlement" section with the live paid / refunded binds (the FLASHWELL
/// split), and an "Actions" section of the three icon-labelled lifecycle buttons.
/// Renderer-independent DATA. The button `turn` names are the
/// [`service`](crate::service) method symbols.
pub fn job_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            row(vec![text("Compute Exchange"), pill_live(STATE_SLOT, "BIDDING", "accent", json!([
                { "value": STATE_POSTED,  "label": "POSTED",  "tag": "warn" },
                { "value": STATE_BID,     "label": "BIDDING", "tag": "accent" },
                { "value": STATE_SETTLED, "label": "SETTLED", "tag": "good" },
            ]))]),
            breadcrumb(&["Posted", "Bidding", "Settled"], 1),
            divider(),
            section("Job", "genuine", vec![
                gauge(STATE_SLOT, STATE_SETTLED, "lifecycle ", true),
                gauge(BID_SLOT, BUDGET_GAUGE_MAX, "bid vs budget ", false),
                bind(BUDGET_SLOT, "budget · ", "amount", false),
                bind(BID_SLOT, "accepted bid · ", "amount", false),
                bind(SPEC_HASH_SLOT, "spec · ", "hash", true),
                bind(REQUESTER_HASH_SLOT, "requester · ", "id", false),
                bind(PROVIDER_HASH_SLOT, "provider · ", "id", false),
            ]),
            section("Settlement", "", vec![
                bind(PAID_SLOT, "paid · ", "amount", false),
                bind(REFUNDED_SLOT, "refunded · ", "amount", false),
            ]),
            section("Actions", "", vec![
                action("+", "Post",   METHOD_POST),
                action("›", "Bid",    METHOD_BID),
                action("✓", "Settle", METHOD_SETTLE),
            ]),
        ]
    })
}

/// **The compute-exchange card as serialized `deos.ui.*` JSON** — byte-for-byte
/// the `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn job_card_json() -> String {
    serde_json::to_string(&job_card_value()).expect("the compute-exchange card serializes")
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
        let card = job_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts
                .iter()
                .any(|t| t["props"]["text"] == "Compute Exchange"),
            "the header names the app"
        );
        let pills = of_kind(&card, "pill");
        assert_eq!(pills.len(), 1);
        // The header pill is LIVE: it reads STATE_SLOT and maps the value to a word.
        assert_eq!(
            pills[0]["props"]["text"], "BIDDING",
            "the static fallback word"
        );
        assert_eq!(pills[0]["props"]["slot"], STATE_SLOT);
        let cases = pills[0]["props"]["cases"].as_array().unwrap();
        assert_eq!(cases.len(), 3, "POSTED / BIDDING / SETTLED");
        assert_eq!(cases[2]["value"], STATE_SETTLED);
        assert_eq!(cases[2]["label"], "SETTLED");
        assert_eq!(cases[2]["tag"], "good");
    }

    #[test]
    fn the_binds_carry_their_display_fmt() {
        let card = job_card_value();
        let binds = of_kind(&card, "bind");
        let fmt = |slot: usize| -> String {
            binds
                .iter()
                .find(|b| b["props"]["slot"].as_u64() == Some(slot as u64))
                .and_then(|b| b["props"]["fmt"].as_str())
                .unwrap()
                .to_string()
        };
        // Amounts group digits; identity keys paint avatar handles; the spec digest paints hex.
        assert_eq!(fmt(BUDGET_SLOT), "amount");
        assert_eq!(fmt(BID_SLOT), "amount");
        assert_eq!(fmt(PAID_SLOT), "amount");
        assert_eq!(fmt(REFUNDED_SLOT), "amount");
        assert_eq!(fmt(REQUESTER_HASH_SLOT), "id");
        assert_eq!(fmt(PROVIDER_HASH_SLOT), "id");
        assert_eq!(fmt(SPEC_HASH_SLOT), "hash");
    }

    #[test]
    fn the_dev_y_rows_are_marked_adept() {
        let card = job_card_value();
        let adept = |kind: &str, slot: usize| -> bool {
            of_kind(&card, kind)
                .iter()
                .find(|n| n["props"]["slot"].as_u64() == Some(slot as u64))
                .and_then(|n| n["props"]["adept"].as_bool())
                .unwrap()
        };
        // The raw state-machine gauge + the sealed spec digest hide in the simple view.
        assert!(
            adept("gauge", STATE_SLOT),
            "the raw lifecycle integer gauge"
        );
        assert!(adept("bind", SPEC_HASH_SLOT), "the sealed spec digest");
        // The human-meaningful job terms stay visible.
        assert!(!adept("gauge", BID_SLOT));
        assert!(!adept("bind", BUDGET_SLOT));
        assert!(!adept("bind", REQUESTER_HASH_SLOT));
    }

    #[test]
    fn the_lifecycle_breadcrumb_marks_the_current_step() {
        let card = job_card_value();
        let crumbs = of_kind(&card, "breadcrumb");
        assert_eq!(crumbs.len(), 1);
        let items = crumbs[0]["props"]["items"].as_array().unwrap();
        assert_eq!(items.len(), 3, "Posted → Bidding → Settled");
        assert_eq!(items[1]["label"], "› Bidding", "the active step is marked");
    }

    #[test]
    fn the_state_and_bid_gauges_read_the_live_slots() {
        let card = job_card_value();
        let gauges = of_kind(&card, "gauge");
        assert_eq!(
            gauges.len(),
            2,
            "a lifecycle-phase gauge + a bid-vs-budget gauge"
        );
        assert_eq!(gauges[0]["props"]["slot"], STATE_SLOT);
        assert_eq!(gauges[0]["props"]["max"], STATE_SETTLED);
        assert_eq!(gauges[1]["props"]["slot"], BID_SLOT);
        assert_eq!(gauges[1]["props"]["max"], BUDGET_GAUGE_MAX);
    }

    #[test]
    fn the_binds_surface_the_full_job_and_settlement_terms() {
        let card = job_card_value();
        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                BUDGET_SLOT as u64,
                BID_SLOT as u64,
                SPEC_HASH_SLOT as u64,
                REQUESTER_HASH_SLOT as u64,
                PROVIDER_HASH_SLOT as u64,
                PAID_SLOT as u64,
                REFUNDED_SLOT as u64,
            ],
            "budget / bid / spec / requester / provider, then paid / refunded"
        );
    }

    #[test]
    fn the_card_has_a_job_and_a_settlement_section() {
        let card = job_card_value();
        let sections = of_kind(&card, "section");
        let titles: Vec<&str> = sections
            .iter()
            .map(|s| s["props"]["title"].as_str().unwrap())
            .collect();
        assert_eq!(titles, vec!["Job", "Settlement", "Actions"]);
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = job_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 3);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the service method vocabulary.
        assert_eq!(turns, vec![METHOD_POST, METHOD_BID, METHOD_SETTLE]);
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = job_card_json();
        // Round-trips through serde (the shape a deos-view renderer's parser reads).
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, breadcrumb, divider, job section, settlement section, actions section
        assert_eq!(back["children"].as_array().unwrap().len(), 6);
    }
}
