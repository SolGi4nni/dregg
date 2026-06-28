//! # polis — the council board as a deos-view CARD (a `deos.ui.*` view-tree).
//!
//! The fourth axis (AX4) of a modern starbridge-app: the app lives IN the deos
//! world by shipping its surface as a **renderer-independent card** — a
//! serializable `deos.ui.*` element-tree ([`deos_view::ViewNode`] in the renderer
//! crate). The SAME tree renders three ways (the renderer-independence seam):
//! native gpui pixels in the cockpit, a browser-loadable HTML document, and a
//! discord embed — all from this one piece of DATA. See
//! `deos-view/src/{render,web,discord}.rs` for the three renderers and
//! `docs/reference/deos-view.md`.
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
//! Unlike the polis deos surface / service / reactor (which pull
//! `dregg-app-framework` and so must be compiled into the test binaries to dodge
//! the `app-framework → sdk → polis` package cycle — see `Cargo.toml`), the card
//! is a plain library module: pure `serde_json` carries no such edge.
//!
//! ## The card shape — a rich, live GOVERNANCE surface
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) built from the rich deos-view
//! vocabulary (`section` / `pill` / `gauge` / `breadcrumb` / `divider` / `icon`):
//!
//!   - a **status header** — the app name + a `pill` naming the live lifecycle
//!     stage as a WORD (`PROPOSED`), and a `breadcrumb` of the whole council
//!     lifecycle (propose → approve → certify → execute) with the current step
//!     marked;
//!   - a **"Council" `section`** surfacing the LIVE cell state: the KILLER
//!     governance visual — a `gauge` for the M-of-N **quorum** (approvals toward
//!     the threshold, the running vote climbing the bar) plus a lifecycle `gauge`
//!     over [`STATE_SLOT`](crate::STATE_SLOT) toward
//!     [`STATE_EXECUTED`](crate::council::STATE_EXECUTED) — and `bind`s on the
//!     staged proposal ([`PROPOSAL_HASH_SLOT`](crate::council::PROPOSAL_HASH_SLOT),
//!     the write-once tooth), each member's approval bit
//!     ([`FIRST_APPROVAL_SLOT`](crate::council::FIRST_APPROVAL_SLOT)`..`), the
//!     certification flag ([`APPROVED_FLAG_SLOT`](crate::council::APPROVED_FLAG_SLOT)),
//!     the M-of-N membership commitment
//!     ([`MEMBERS_COMMIT_SLOT`](crate::council::MEMBERS_COMMIT_SLOT)) and the live
//!     state-code — each a fine-grained signal that re-reads the live value (the
//!     SAME witnessed read a native `bind` closure makes), so the quorum bar and
//!     approval rows advance as votes commit;
//!   - an **"Actions" `section`** of one `icon`+`button` row per lifecycle method
//!     (`propose` / `approve` / `certify` / `reject` / `execute`), each `button`
//!     carrying its `onClick = { turn, arg }` — the EXACT cap-gated verified turn a
//!     click fires through the [`invoke()`](crate)/affordance seam.
//!
//! ## The quorum gauge is a representative tally
//!
//! The basic [`council`](crate::council) keeps each approval in a DISTINCT `{0,1}`
//! register ([`FIRST_APPROVAL_SLOT`](crate::council::FIRST_APPROVAL_SLOT)`..6`) —
//! there is no aggregate running-count slot, and the running tally rides the
//! [`METHOD_APPROVE`](crate::council::METHOD_APPROVE) turn argument the AX5 reactor
//! folds. So the quorum `gauge` reads the lead approval slot against the
//! representative threshold [`QUORUM`] (the card's display ceiling, the same
//! representative-max idiom the bounty-board reward gauge + governed-namespace
//! quorum gauge use); the per-member approval `bind`s below carry the full
//! distinct-approver truth, and a live cell's real `M` is the
//! [`AffineLe`](dregg_cell::program::StateConstraint) threshold gate baked into the
//! charter's program.
//!
//! The button `turn` names match the [`council`](crate::council) method vocabulary
//! ([`METHOD_PROPOSE`](crate::council::METHOD_PROPOSE), …) so the card (AX4), the
//! service cell (AX3), and the reactor (AX5) all speak the one governance
//! lifecycle.

use serde_json::{Value, json};

use crate::STATE_SLOT;
use crate::council::{
    APPROVED_FLAG_SLOT, FIRST_APPROVAL_SLOT, MAX_MEMBERS, MEMBERS_COMMIT_SLOT, METHOD_APPROVE,
    METHOD_CERTIFY, METHOD_EXECUTE, METHOD_PROPOSE, METHOD_REJECT, PROPOSAL_HASH_SLOT,
    STATE_EXECUTED,
};

/// The quorum bar's denominator — the representative M-of-N threshold (the
/// canonical 2-of-3 council) so a proposal that has gathered `QUORUM` approving
/// votes fills the gauge (the killer governance visual: approvals / M). A live
/// cell enforces its real `M` via the charter's `AffineLe` threshold gate; this
/// is the card's display ceiling, the same representative-max idiom the
/// bounty-board reward gauge uses.
pub const QUORUM: u64 = 2;

/// The representative council size N (the seats the membership commitment
/// publishes) — [`council::MAX_MEMBERS`](crate::council::MAX_MEMBERS), the
/// register-slot council's ceiling. Shown alongside [`QUORUM`] as the `M of N`
/// caption.
pub const COUNCIL_SIZE: u64 = MAX_MEMBERS as u64;

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

/// A `deos.ui.bind` node tagged with the model `slot` it re-reads + a label
/// prefix (the engine drops the closure on serialize, so the slot is tagged).
fn bind(slot: u8, label: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot as usize, "label": label } })
}

/// A `deos.ui.gauge` node — a bound progress bar (`slot_value / max`, immediate-mode).
fn gauge(slot: u8, max: u64, label: &str) -> Value {
    json!({ "kind": "gauge", "props": { "slot": slot as usize, "max": max, "label": label } })
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

/// **The polis council card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A rich, live governance surface: a status header (name + `PROPOSED` pill +
/// lifecycle breadcrumb), a "Council" section surfacing the killer quorum gauge
/// (approvals / M) + the lifecycle gauge + the proposal / per-member approval /
/// certified / membership / state binds, and an "Actions" section of the five
/// icon-labelled lifecycle buttons. Renderer-independent DATA. The button `turn`
/// names are the [`council`](crate::council) method symbols.
pub fn council_card_value() -> Value {
    let m_of_n = format!("threshold · {QUORUM} of {COUNCIL_SIZE}");
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            row(vec![text("Polis Council"), pill("PROPOSED", "accent")]),
            breadcrumb(&["Propose", "Approve", "Certify", "Execute"], 1),
            divider(),
            section("Council", "genuine", vec![
                // THE killer governance visual: the running approval tally toward quorum.
                gauge(FIRST_APPROVAL_SLOT, QUORUM, "quorum "),
                // The lifecycle stage climbing DRAFT(0) → … → EXECUTED.
                gauge(STATE_SLOT, STATE_EXECUTED, "lifecycle "),
                text(&m_of_n),
                bind(PROPOSAL_HASH_SLOT, "proposal · "),
                bind(FIRST_APPROVAL_SLOT, "approval ① · "),
                bind(FIRST_APPROVAL_SLOT + 1, "approval ② · "),
                bind(FIRST_APPROVAL_SLOT + 2, "approval ③ · "),
                bind(APPROVED_FLAG_SLOT, "certified · "),
                bind(MEMBERS_COMMIT_SLOT, "council · "),
                bind(STATE_SLOT, "state · "),
            ]),
            section("Actions", "", vec![
                action("+", "Propose", METHOD_PROPOSE),
                action("✓", "Approve", METHOD_APPROVE),
                action("⚖", "Certify", METHOD_CERTIFY),
                action("✕", "Reject",  METHOD_REJECT),
                action("▶", "Execute", METHOD_EXECUTE),
            ]),
        ]
    })
}

/// **The polis council card as serialized `deos.ui.*` JSON** — byte-for-byte the
/// `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn council_card_json() -> String {
    serde_json::to_string(&council_card_value()).expect("the council card serializes")
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
    fn the_card_is_a_vstack_with_a_named_header_and_a_stage_pill() {
        let card = council_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts.iter().any(|t| t["props"]["text"] == "Polis Council"),
            "the header names the app"
        );
        let pills = of_kind(&card, "pill");
        assert_eq!(pills.len(), 1);
        assert_eq!(pills[0]["props"]["text"], "PROPOSED");
    }

    #[test]
    fn the_lifecycle_breadcrumb_marks_the_current_step() {
        let card = council_card_value();
        let crumbs = of_kind(&card, "breadcrumb");
        assert_eq!(crumbs.len(), 1);
        let items = crumbs[0]["props"]["items"].as_array().unwrap();
        assert_eq!(items.len(), 4, "propose → approve → certify → execute");
        assert_eq!(items[1]["label"], "› Approve", "the active step is marked");
    }

    #[test]
    fn the_quorum_gauge_reads_the_approval_tally_toward_m() {
        // The killer governance visual: the running approval tally over the
        // representative quorum M, plus the lifecycle stage gauge.
        let card = council_card_value();
        let gauges = of_kind(&card, "gauge");
        assert_eq!(gauges.len(), 2, "a quorum gauge + a lifecycle-stage gauge");
        assert_eq!(gauges[0]["props"]["slot"], FIRST_APPROVAL_SLOT as usize);
        assert_eq!(gauges[0]["props"]["max"], QUORUM);
        assert_eq!(gauges[1]["props"]["slot"], STATE_SLOT as usize);
        assert_eq!(gauges[1]["props"]["max"], STATE_EXECUTED);
    }

    #[test]
    fn the_council_binds_surface_the_live_governance_state() {
        let card = council_card_value();
        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                PROPOSAL_HASH_SLOT as u64,
                FIRST_APPROVAL_SLOT as u64,
                FIRST_APPROVAL_SLOT as u64 + 1,
                FIRST_APPROVAL_SLOT as u64 + 2,
                APPROVED_FLAG_SLOT as u64,
                MEMBERS_COMMIT_SLOT as u64,
                STATE_SLOT as u64,
            ],
            "the binds surface proposal / per-member approvals / certified / council / state"
        );
    }

    #[test]
    fn every_button_carries_its_council_method_as_the_turn_payload() {
        let card = council_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 5);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the council method vocabulary.
        assert_eq!(
            turns,
            vec![
                METHOD_PROPOSE,
                METHOD_APPROVE,
                METHOD_CERTIFY,
                METHOD_REJECT,
                METHOD_EXECUTE
            ]
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = council_card_json();
        // Round-trips through serde (the shape a deos-view renderer's parser reads).
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, breadcrumb, divider, council section, actions section
        assert_eq!(back["children"].as_array().unwrap().len(), 5);
    }
}
