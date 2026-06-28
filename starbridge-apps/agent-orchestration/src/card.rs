//! # agent-orchestration — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
//!
//! The fourth axis (AX4) of a modern starbridge-app: the app lives IN the deos world by
//! shipping its surface as a **renderer-independent card** — a serializable `deos.ui.*`
//! element-tree ([`deos_view::ViewNode`] in the renderer crate). The SAME tree renders
//! three ways (the renderer-independence seam): native gpui pixels in the cockpit, a
//! browser-loadable HTML document, and a discord embed — all from this one piece of
//! DATA. See `deos-view/src/{render,web,discord}.rs` for the three renderers and
//! `docs/reference/deos-view.md`.
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
//! ## The card shape — a rich, live coordinator board
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) built from the rich deos-view
//! vocabulary (`section` / `pill` / `gauge` / `breadcrumb` / `divider` / `icon`):
//!
//!   - a **status header** — the app name + a `pill` naming the live coordination state
//!     as a WORD (`COORDINATING`), and a `breadcrumb` of the orchestration lifecycle
//!     (mandate → dispatch → worker-step → audit) with the current step marked;
//!   - a **"Coordination" `section`** surfacing the LIVE board state: the KILLER VISUAL —
//!     two `gauge`s on the per-worker spend meters ([`SPENT_A_SLOT`](crate::SPENT_A_SLOT) /
//!     [`SPENT_B_SLOT`](crate::SPENT_B_SLOT)), each filling toward the swarm budget
//!     ceiling, so TOGETHER they paint the `Σspend / budget` mandate budget filling (the
//!     conserved `spent_a + spent_b <= budget` the executor's `AffineLe` gate enforces),
//!     plus `bind`s on the [`BUDGET_SLOT`](crate::BUDGET_SLOT), the two spend meters, the
//!     no-replay [`EPOCH_SLOT`](crate::EPOCH_SLOT) dispatch counter, and the
//!     [`LEAD_SLOT`](crate::LEAD_SLOT) coordinator identity — each a fine-grained signal
//!     that re-reads the live value (the SAME witnessed read a native `bind` closure
//!     makes), so the surface advances when a fired worker step commits;
//!   - an **"Actions" `section`** of one `icon`+`button` row per mutating method
//!     (`open_board` / `worker_step` / `delegate_mandate`), each `button` carrying its
//!     `onClick = { turn, arg }` — the EXACT cap-gated verified turn a click fires through
//!     the [`invoke()`](crate::service)/affordance seam.
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary
//! ([`METHOD_OPEN_BOARD`](crate::service::METHOD_OPEN_BOARD), …) so the card and the
//! service cell speak the same orchestration.

use serde_json::{Value, json};

use crate::service::{METHOD_DELEGATE_MANDATE, METHOD_OPEN_BOARD, METHOD_WORKER_STEP};
use crate::{BUDGET_SLOT, EPOCH_SLOT, LEAD_SLOT, SPENT_A_SLOT, SPENT_B_SLOT};

/// The spend-gauge denominator — a representative swarm-budget ceiling so a fully-spent
/// mandate fills the gauge (the deos surface / `seed_board` seed a budget of `1_000`).
/// Each worker's spend bar fills toward this; together they ARE `Σspend / budget`.
const BUDGET_GAUGE_MAX: u64 = 1_000;

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A LIVE `deos.ui.pill` node — reads `slot` immediate-mode and maps the value to a
/// word + color via `cases` (the first `{value,label,tag}` matching the slot wins).
/// `text`/`tag` are the static fallback (discord, or no match).
fn pill_live(slot: u8, label: &str, tag: &str, cases: Value) -> Value {
    json!({ "kind": "pill", "props": { "text": label, "tag": tag, "slot": slot as usize, "cases": cases } })
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
fn bind(slot: u8, label: &str, fmt: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot as usize, "label": label, "fmt": fmt } })
}

/// A `deos.ui.bind` node marked `adept` — hidden in the simple projection (dev-y /
/// internal signal); revealed in the adept "see the bones" view.
fn bind_adept(slot: u8, label: &str, fmt: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot as usize, "label": label, "fmt": fmt, "adept": true } })
}

/// A `deos.ui.gauge` node — a bound progress bar (`slot_value / max`, immediate-mode).
/// `adept` hides the raw numeric in the simple projection; revealed in the adept view.
fn gauge(slot: u8, max: u64, label: &str, adept: bool) -> Value {
    json!({ "kind": "gauge", "props": { "slot": slot as usize, "max": max, "label": label, "adept": adept } })
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

/// An action row — an `icon` + a method `button` (the verified-turn affordance).
fn action(glyph: &str, label: &str, turn: &str) -> Value {
    row(vec![icon(glyph, "accent"), button(label, turn, 0)])
}

/// **The agent-orchestration card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A rich, live coordinator surface: a status header (name + `COORDINATING` pill +
/// lifecycle breadcrumb), a "Coordination" section surfacing the KILLER VISUAL — the two
/// per-worker spend gauges filling toward the swarm budget (`Σspend / budget`) — plus the
/// budget / spend / epoch / lead binds, and an "Actions" section of the three
/// icon-labelled mutating-method buttons. Renderer-independent DATA: hand it to any
/// `deos-view` renderer (native / web / discord) to paint the SAME card. The button
/// `turn` names are the [`service`](crate::service) method symbols.
pub fn board_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            // The header status pill is LIVE: it reads the dispatch EPOCH and shows
            // whether the board is open. epoch 0 = the factory cell, not yet opened
            // (PENDING); any opened/coordinating board (epoch ≥ 1, the seed sets 1)
            // falls through to the COORDINATING fallback.
            row(vec![text("Agent Orchestration"), pill_live(EPOCH_SLOT, "COORDINATING", "accent", json!([
                { "value": 0, "label": "PENDING", "tag": "muted" },
            ]))]),
            breadcrumb(&["Mandate", "Dispatch", "Worker Step", "Audit"], 1),
            divider(),
            section("Coordination", "genuine", vec![
                gauge(SPENT_A_SLOT, BUDGET_GAUGE_MAX, "worker-a spend → budget ", false),
                gauge(SPENT_B_SLOT, BUDGET_GAUGE_MAX, "worker-b spend → budget ", false),
                bind(BUDGET_SLOT, "budget · ", "amount"),
                bind(SPENT_A_SLOT, "spent A · ", "amount"),
                bind(SPENT_B_SLOT, "spent B · ", "amount"),
                // The raw no-replay dispatch counter — internal bookkeeping, adept-only.
                bind_adept(EPOCH_SLOT, "epoch · ", "raw"),
                bind(LEAD_SLOT, "lead · ", "id"),
            ]),
            section("Actions", "", vec![
                action("▸", "Open Board",       METHOD_OPEN_BOARD),
                action("→", "Worker Step",      METHOD_WORKER_STEP),
                action("⊂", "Delegate Mandate", METHOD_DELEGATE_MANDATE),
            ]),
        ]
    })
}

/// **The agent-orchestration card as serialized `deos.ui.*` JSON** — byte-for-byte the
/// `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn board_card_json() -> String {
    serde_json::to_string(&board_card_value()).expect("the orchestration card serializes")
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
        let card = board_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts
                .iter()
                .any(|t| t["props"]["text"] == "Agent Orchestration"),
            "the header names the app"
        );
        let pills = of_kind(&card, "pill");
        assert_eq!(pills.len(), 1);
        // The header pill is LIVE: it reads EPOCH_SLOT and maps the value to a word.
        assert_eq!(
            pills[0]["props"]["text"], "COORDINATING",
            "the static fallback word (an opened board)"
        );
        assert_eq!(pills[0]["props"]["slot"], EPOCH_SLOT as usize);
        let cases = pills[0]["props"]["cases"].as_array().unwrap();
        assert_eq!(cases.len(), 1, "epoch 0 = PENDING (not yet opened)");
        assert_eq!(cases[0]["value"], 0);
        assert_eq!(cases[0]["label"], "PENDING");
    }

    #[test]
    fn the_budget_and_identity_binds_carry_their_display_fmt() {
        let card = board_card_value();
        let binds = of_kind(&card, "bind");
        let fmt = |slot: u8| -> String {
            binds
                .iter()
                .find(|b| b["props"]["slot"].as_u64() == Some(slot as u64))
                .and_then(|b| b["props"]["fmt"].as_str())
                .unwrap()
                .to_string()
        };
        assert_eq!(fmt(BUDGET_SLOT), "amount", "the budget groups digits");
        assert_eq!(fmt(SPENT_A_SLOT), "amount", "worker-a spend groups digits");
        assert_eq!(fmt(SPENT_B_SLOT), "amount", "worker-b spend groups digits");
        assert_eq!(fmt(LEAD_SLOT), "id", "the lead paints an avatar handle");
        assert_eq!(fmt(EPOCH_SLOT), "raw", "the dispatch counter stays plain");
        // The raw dispatch counter is adept-only (hidden in the simple projection).
        let epoch_bind = binds
            .iter()
            .find(|b| b["props"]["slot"].as_u64() == Some(EPOCH_SLOT as u64))
            .unwrap();
        assert_eq!(epoch_bind["props"]["adept"], true);
    }

    #[test]
    fn the_lifecycle_breadcrumb_marks_the_current_step() {
        let card = board_card_value();
        let crumbs = of_kind(&card, "breadcrumb");
        assert_eq!(crumbs.len(), 1);
        let items = crumbs[0]["props"]["items"].as_array().unwrap();
        assert_eq!(items.len(), 4, "mandate → dispatch → worker-step → audit");
        assert_eq!(items[1]["label"], "› Dispatch", "the active step is marked");
    }

    #[test]
    fn the_budget_gauges_read_the_live_spend_meters_filling_toward_budget() {
        // The KILLER VISUAL: two spend gauges, each filling toward the swarm-budget
        // ceiling — together they paint `Σspend / budget` (the conserved AffineLe bound).
        let card = board_card_value();
        let gauges = of_kind(&card, "gauge");
        assert_eq!(gauges.len(), 2, "a spend gauge per worker meter");
        assert_eq!(gauges[0]["props"]["slot"], SPENT_A_SLOT as usize);
        assert_eq!(gauges[1]["props"]["slot"], SPENT_B_SLOT as usize);
        for g in &gauges {
            assert_eq!(
                g["props"]["max"], BUDGET_GAUGE_MAX,
                "each fills toward the swarm budget ceiling"
            );
        }
    }

    #[test]
    fn the_binds_surface_the_budget_spend_epoch_and_lead() {
        let card = board_card_value();
        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                BUDGET_SLOT as u64,
                SPENT_A_SLOT as u64,
                SPENT_B_SLOT as u64,
                EPOCH_SLOT as u64,
                LEAD_SLOT as u64,
            ],
            "the binds surface budget / spent-A / spent-B / epoch / lead"
        );
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = board_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 3);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the service method vocabulary.
        assert_eq!(
            turns,
            vec![
                METHOD_OPEN_BOARD,
                METHOD_WORKER_STEP,
                METHOD_DELEGATE_MANDATE
            ]
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = board_card_json();
        // Round-trips through serde (the shape a deos-view renderer's parser reads).
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, breadcrumb, divider, coordination section, actions section
        assert_eq!(back["children"].as_array().unwrap().len(), 5);
    }
}
