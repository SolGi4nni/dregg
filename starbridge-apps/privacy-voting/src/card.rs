//! # privacy-voting — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
//!
//! The fourth axis (AX4) of a modern starbridge-app: the app lives IN the deos world
//! by shipping its surface as a **renderer-independent card** — a serializable
//! `deos.ui.*` element-tree ([`deos_view::ViewNode`] in the renderer crate). The SAME
//! tree renders three ways (the renderer-independence seam): native gpui pixels in the
//! cockpit, a browser-loadable HTML document, and a discord embed — all from this one
//! piece of DATA. See `deos-view/src/{render,web,discord}.rs` for the three renderers
//! and `docs/reference/deos-view.md`.
//!
//! ## Why the card is DATA, not a renderer call
//!
//! `deos-view` pulls BOTH the SpiderMonkey (`mozjs`) and the gpui native elephants, so
//! it is a STANDALONE workspace EXCLUDED from the repo-root workspace (see its
//! `Cargo.toml`). A starbridge-app must never depend on it — that would feature-unify
//! the elephants onto the main build. So the app's contribution is the **view-tree
//! JSON** (this module): pure `serde_json`, no elephant. The deos world's renderers
//! consume it; this module owns the card definition and proves it is well-formed.
//!
//! ## The card shape — a LIVE BALLOT BOARD
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) built from the rich deos-view
//! vocabulary (`section` / `pill` / `gauge` / `breadcrumb` / `divider` / `icon`):
//!
//!   - a **status header** — the app name + a `pill` naming the live poll stage as a
//!     WORD (`OPEN`), and a `breadcrumb` of the whole lifecycle (open → voting → tally →
//!     closed) with the current step marked;
//!   - a **"Tally" `section`** — THE KILLER VISUAL: one `gauge` PER OPTION
//!     (`yes` / `no` / `abstain`) bound to the three live tally slots
//!     ([`TALLY_YES_SLOT`](crate::TALLY_YES_SLOT), …), so the section is a LIVE BAR CHART
//!     of the running vote — each bar fills toward the [`QUORUM_TARGET`] as votes commit.
//!     Each gauge reads its slot IMMEDIATE-MODE (the SAME witnessed read a native `bind`
//!     closure makes), so the bars advance the instant a `record_tally` turn commits;
//!     `bind`s under the bars surface the exact integer counts;
//!   - a **"Poll" `section`** surfacing the poll's identity + state: a `bind` on the
//!     write-once [`QUESTION_HASH_SLOT`](crate::QUESTION_HASH_SLOT) and the one-way
//!     [`CLOSED_SLOT`](crate::CLOSED_SLOT) (non-zero once the poll closes);
//!   - an **"Actions" `section`** of one `icon`+`button` row per lifecycle method
//!     (`open_poll` / `cast_vote` / `record_tally` / `close_poll`), each `button`
//!     carrying its `onClick = { turn, arg }` — the EXACT cap-gated verified turn a click
//!     fires through the [`invoke()`](crate::service)/affordance seam.
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary
//! ([`METHOD_OPEN_POLL`](crate::service::METHOD_OPEN_POLL), …) so the card and the
//! service cell speak the same lifecycle.

use serde_json::{Value, json};

use crate::service::{METHOD_CAST_VOTE, METHOD_CLOSE_POLL, METHOD_OPEN_POLL, METHOD_RECORD_TALLY};
use crate::{CLOSED_SLOT, QUESTION_HASH_SLOT, TALLY_ABSTAIN_SLOT, TALLY_NO_SLOT, TALLY_YES_SLOT};

/// The per-option tally bar's denominator — a representative quorum / electorate so each
/// option gauge fills as the running count climbs toward a meaningful turnout. The seeded
/// poll starts at 0 on every option (empty bars) and each committed `record_tally`
/// advances the matching bar one notch toward this target.
pub const QUORUM_TARGET: u64 = 16;

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A `deos.ui.pill` node — a colored status badge.
fn pill(label: &str, tag: &str) -> Value {
    json!({ "kind": "pill", "props": { "text": label, "tag": tag } })
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

/// A `deos.ui.bind` node tagged with the model `slot` it re-reads + a label prefix
/// (the engine drops the closure on serialize, so the slot is tagged).
fn bind(slot: usize, label: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label } })
}

/// A `deos.ui.gauge` node — a bound progress bar (`slot_value / max`, immediate-mode).
fn gauge(slot: usize, max: u64, label: &str) -> Value {
    json!({ "kind": "gauge", "props": { "slot": slot, "max": max, "label": label } })
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

/// **The privacy-voting card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A rich, live ballot board: a status header (name + `OPEN` pill + lifecycle
/// breadcrumb), a "Tally" section that is a LIVE BAR CHART (one bound `gauge` per option,
/// reading the three tally slots, plus integer `bind`s), a "Poll" section surfacing the
/// question + closed slots, and an "Actions" section of the four icon-labelled lifecycle
/// buttons. Renderer-independent DATA: hand it to any `deos-view` renderer (native / web /
/// discord) to paint the SAME card. The button `turn` names are the
/// [`service`](crate::service) method symbols.
pub fn voting_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            row(vec![text("Privacy Voting"), pill("OPEN", "good")]),
            breadcrumb(&["Open", "Voting", "Tally", "Closed"], 1),
            divider(),
            section("Tally", "genuine", vec![
                gauge(TALLY_YES_SLOT,     QUORUM_TARGET, "yes "),
                gauge(TALLY_NO_SLOT,      QUORUM_TARGET, "no "),
                gauge(TALLY_ABSTAIN_SLOT, QUORUM_TARGET, "abstain "),
                bind(TALLY_YES_SLOT,     "yes · "),
                bind(TALLY_NO_SLOT,      "no · "),
                bind(TALLY_ABSTAIN_SLOT, "abstain · "),
            ]),
            section("Poll", "", vec![
                bind(QUESTION_HASH_SLOT, "question · "),
                bind(CLOSED_SLOT,        "closed · "),
            ]),
            section("Actions", "", vec![
                action("+", "Open Poll",    METHOD_OPEN_POLL),
                action("✓", "Cast Vote",    METHOD_CAST_VOTE),
                action("∑", "Record Tally", METHOD_RECORD_TALLY),
                action("✕", "Close Poll",   METHOD_CLOSE_POLL),
            ]),
        ]
    })
}

/// **The privacy-voting card as serialized `deos.ui.*` JSON** — byte-for-byte the
/// `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn voting_card_json() -> String {
    serde_json::to_string(&voting_card_value()).expect("the voting card serializes")
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
    fn the_card_is_a_vstack_with_a_named_header_and_a_status_pill() {
        let card = voting_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts.iter().any(|t| t["props"]["text"] == "Privacy Voting"),
            "the header names the app"
        );
        let pills = of_kind(&card, "pill");
        assert_eq!(pills.len(), 1);
        assert_eq!(pills[0]["props"]["text"], "OPEN");
    }

    #[test]
    fn the_lifecycle_breadcrumb_marks_the_current_step() {
        let card = voting_card_value();
        let crumbs = of_kind(&card, "breadcrumb");
        assert_eq!(crumbs.len(), 1);
        let items = crumbs[0]["props"]["items"].as_array().unwrap();
        assert_eq!(items.len(), 4, "open → voting → tally → closed");
        assert_eq!(items[1]["label"], "› Voting", "the active step is marked");
    }

    #[test]
    fn the_tally_is_a_live_bar_chart_one_gauge_per_option() {
        let card = voting_card_value();
        let gauges = of_kind(&card, "gauge");
        // One bar per vote option — the killer visual.
        assert_eq!(gauges.len(), 3, "a yes / no / abstain bar");
        let slots: Vec<u64> = gauges
            .iter()
            .map(|g| g["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                TALLY_YES_SLOT as u64,
                TALLY_NO_SLOT as u64,
                TALLY_ABSTAIN_SLOT as u64,
            ],
            "the bars read the three live tally slots"
        );
        for g in &gauges {
            assert_eq!(
                g["props"]["max"], QUORUM_TARGET,
                "each bar fills toward the quorum target"
            );
        }
    }

    #[test]
    fn binds_surface_the_live_counts_and_poll_identity() {
        let card = voting_card_value();
        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                TALLY_YES_SLOT as u64,
                TALLY_NO_SLOT as u64,
                TALLY_ABSTAIN_SLOT as u64,
                QUESTION_HASH_SLOT as u64,
                CLOSED_SLOT as u64,
            ],
            "the binds surface the three counts + the question + the closed flag"
        );
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = voting_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 4);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the service method vocabulary.
        assert_eq!(
            turns,
            vec![
                METHOD_OPEN_POLL,
                METHOD_CAST_VOTE,
                METHOD_RECORD_TALLY,
                METHOD_CLOSE_POLL
            ]
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = voting_card_json();
        // Round-trips through serde (the shape a deos-view renderer's parser reads).
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, breadcrumb, divider, tally section, poll section, actions section
        assert_eq!(back["children"].as_array().unwrap().len(), 6);
    }
}
