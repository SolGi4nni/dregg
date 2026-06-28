//! # compartment-workflow-mandate — the UI as a deos-view CARD (a `deos.ui.*`
//! view-tree) (AX4).
//!
//! The fourth axis of a modern starbridge-app: the app lives IN the deos world by
//! shipping its surface as a **renderer-independent card** — a serializable
//! `deos.ui.*` element-tree ([`deos_view::ViewNode`] in the renderer crate). The
//! SAME tree renders three ways (the renderer-independence seam): native gpui pixels
//! in the cockpit, a browser-loadable HTML document, and a discord embed — all from
//! this one piece of DATA. See `deos-view/src/{render,web,discord}.rs`.
//!
//! ## Why the card is DATA, not a renderer call
//!
//! `deos-view` pulls BOTH the SpiderMonkey (`mozjs`) and the gpui native elephants,
//! so it is a STANDALONE workspace EXCLUDED from the repo-root workspace. A
//! starbridge-app must never depend on it — that would feature-unify the elephants
//! onto the main build. So the app's contribution is the **view-tree JSON** (this
//! module): pure `serde_json`, no elephant. The deos world's renderers consume it.
//!
//! ## The card shape — a rich, live clearance-gated charter surface
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) built from the rich deos-view
//! vocabulary (`section` / `pill` / `gauge` / `breadcrumb` / `divider` / `icon`):
//!
//!   - a **status header** — the app name + a `pill` naming the live workflow step as
//!     a WORD (`REVIEW`), and a `breadcrumb` of the whole charter DAG
//!     (review → redact → sign) with the current step marked;
//!   - a **"Charter" `section`** surfacing the LIVE cell state: a `gauge` bound to
//!     [`STEP_CURSOR_SLOT`](crate::STEP_CURSOR_SLOT) (charter progress, `cursor /
//!     terminal`), plus `bind`s on the current step
//!     ([`STEP_CURSOR_SLOT`](crate::STEP_CURSOR_SLOT)), the entered-step compartment
//!     ([`STEP_COMPARTMENT_SLOT`](crate::STEP_COMPARTMENT_SLOT)) and the presented
//!     officer clearance ([`ACTOR_CLEARANCE_SLOT`](crate::ACTOR_CLEARANCE_SLOT)) —
//!     each a fine-grained signal that re-reads the live value, so the surface
//!     advances when a fired `advance_step` commits;
//!   - a **"Clearance" `section`** — the SECURITY visual for the [`ClearanceDominates`](
//!     dregg_app_framework::StateConstraint::ClearanceDominates) tooth: the entered
//!     step requires a clearance that DOMINATES its compartment (`officer ⊐ {review,
//!     redact, sign}`), with a `bind` on the root-bound charter graph
//!     ([`CLEARANCE_GRAPH_ROOT_SLOT`](crate::CLEARANCE_GRAPH_ROOT_SLOT)) the executor
//!     re-enforces;
//!   - an **"Actions" `section`** of one `icon`+`button` row per lifecycle affordance
//!     (`Advance` / `Sign` / `View`), each `button` carrying its `onClick = { turn,
//!     arg }` — the EXACT cap-gated verified turn a click fires through the
//!     [`service`](crate::service)/affordance seam. `Advance` and `Sign` are the same
//!     [`advance_step`](crate::service::METHOD_ADVANCE_STEP) turn at two points in the
//!     charter (the final advance ENTERS the `sign` compartment); `View` is the
//!     [`view`](crate::service::METHOD_VIEW) serviced read.
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary
//! ([`METHOD_ADVANCE_STEP`](crate::service::METHOD_ADVANCE_STEP),
//! [`METHOD_VIEW`](crate::service::METHOD_VIEW)) so the card and the service cell
//! speak the same charter.

use serde_json::{Value, json};

use crate::service::{METHOD_ADVANCE_STEP, METHOD_VIEW};
use crate::{
    ACTOR_CLEARANCE_SLOT, CLEARANCE_GRAPH_ROOT_SLOT, DEFAULT_CHARTER_STEPS, STEP_COMPARTMENT_SLOT,
    STEP_CURSOR_SLOT,
};

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A `deos.ui.pill` node — a colored status badge.
fn pill(label: &str, tag: &str) -> Value {
    json!({ "kind": "pill", "props": { "text": label, "tag": tag } })
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
/// `"raw"` plain) so an opaque key/root paints short + friendly.
fn bind(slot: usize, label: &str, fmt: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt } })
}

/// A `deos.ui.bind` node marked `adept` — hidden in the simple projection (a raw
/// state-machine numeric / internal root); revealed in the adept "see the bones" view.
fn bind_adept(slot: usize, label: &str, fmt: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt, "adept": true } })
}

/// A `deos.ui.gauge` node — a bound progress bar (`slot_value / max`, immediate-mode).
/// `adept` hides the raw numeric in the simple projection (the breadcrumb + live pill
/// already show the stage); revealed in the adept "see the bones" view.
fn gauge(slot: usize, max: u64, label: &str, adept: bool) -> Value {
    json!({ "kind": "gauge", "props": { "slot": slot, "max": max, "label": label, "adept": adept } })
}

/// A `deos.ui.breadcrumb` node — the charter path; the `active` step is marked `›`.
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

/// **The compartment-workflow card as a `deos.ui.*` view-tree** (a
/// `serde_json::Value`).
///
/// A rich, live clearance-gated charter surface: a status header (name + `REVIEW`
/// pill + the review → redact → sign breadcrumb), a "Charter" section surfacing the
/// live charter-progress gauge and the step / compartment / clearance binds, a
/// "Clearance" section visualizing the [`ClearanceDominates`](
/// dregg_app_framework::StateConstraint::ClearanceDominates) tooth, and an "Actions"
/// section of the `Advance` / `Sign` / `View` icon-labelled buttons.
/// Renderer-independent DATA. The button `turn` names are the [`service`](crate::service)
/// method symbols.
pub fn workflow_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            // The header status pill is LIVE: it reads the charter STEP_CURSOR and shows
            // the entered phase as a WORD (review → redact → sign → sealed at terminal).
            row(vec![text("Compartment Workflow"), pill_live(STEP_CURSOR_SLOT, "REVIEW", "accent", json!([
                { "value": 0, "label": "REVIEW", "tag": "accent" },
                { "value": 1, "label": "REDACT", "tag": "warn" },
                { "value": 2, "label": "SIGN",   "tag": "good" },
                { "value": 3, "label": "SEALED", "tag": "good" },
            ]))]),
            breadcrumb(&["Review", "Redact", "Sign"], 0),
            divider(),
            section("Charter", "genuine", vec![
                // The raw charter-progress numeric — the breadcrumb + live pill already
                // show the stage, so the integer gauge/cursor/compartment are adept-only.
                gauge(STEP_CURSOR_SLOT as usize, DEFAULT_CHARTER_STEPS, "step ", true),
                bind_adept(STEP_CURSOR_SLOT as usize, "current step · ", "raw"),
                bind_adept(STEP_COMPARTMENT_SLOT as usize, "compartment · ", "raw"),
                bind(ACTOR_CLEARANCE_SLOT as usize, "clearance · ", "id"),
            ]),
            section("Clearance", "genuine", vec![
                row(vec![
                    icon("⊐", "good"),
                    text("clearance must dominate the step compartment"),
                ]),
                row(vec![
                    pill("ClearanceDominates", "good"),
                    text("officer ⊐ {review · redact · sign}"),
                ]),
                // The root-bound charter graph is a raw Merkle root — the friendly
                // ClearanceDominates pill carries the signal; the root is adept-only.
                bind_adept(CLEARANCE_GRAPH_ROOT_SLOT as usize, "charter graph root · ", "hash"),
            ]),
            section("Actions", "", vec![
                action("›", "Advance", METHOD_ADVANCE_STEP),
                action("✓", "Sign",    METHOD_ADVANCE_STEP),
                action("⊙", "View",    METHOD_VIEW),
            ]),
        ]
    })
}

/// **The compartment-workflow card as serialized `deos.ui.*` JSON** — byte-for-byte
/// the `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn workflow_card_json() -> String {
    serde_json::to_string(&workflow_card_value()).expect("the workflow card serializes")
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
    fn the_card_is_a_vstack_with_a_named_header_and_a_step_pill() {
        let card = workflow_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts
                .iter()
                .any(|t| t["props"]["text"] == "Compartment Workflow"),
            "the header names the app"
        );
        let pills = of_kind(&card, "pill");
        // The header status pill is LIVE: it reads STEP_CURSOR_SLOT and maps the value
        // to the entered phase word. (The ClearanceDominates pill is a static badge.)
        let header = pills
            .iter()
            .find(|p| p["props"]["slot"] == STEP_CURSOR_SLOT as usize)
            .expect("the status pill names the live workflow step as a word");
        assert_eq!(
            header["props"]["text"], "REVIEW",
            "the static fallback word (the first charter step)"
        );
        let cases = header["props"]["cases"].as_array().unwrap();
        assert_eq!(cases.len(), 4, "review / redact / sign / sealed");
        assert_eq!(cases[0]["label"], "REVIEW");
        assert_eq!(cases[2]["value"], 2);
        assert_eq!(cases[2]["label"], "SIGN");
    }

    #[test]
    fn the_charter_breadcrumb_marks_the_current_step() {
        let card = workflow_card_value();
        let crumbs = of_kind(&card, "breadcrumb");
        assert_eq!(crumbs.len(), 1);
        let items = crumbs[0]["props"]["items"].as_array().unwrap();
        assert_eq!(items.len(), 3, "review → redact → sign");
        assert_eq!(items[0]["label"], "› Review", "the active step is marked");
        assert_eq!(items[1]["label"], "Redact");
        assert_eq!(items[2]["label"], "Sign");
    }

    #[test]
    fn the_charter_section_has_a_live_step_gauge_and_the_charter_binds() {
        let card = workflow_card_value();
        let gauges = of_kind(&card, "gauge");
        assert_eq!(gauges.len(), 1, "a charter-progress gauge");
        assert_eq!(gauges[0]["props"]["slot"], STEP_CURSOR_SLOT);
        assert_eq!(
            gauges[0]["props"]["max"], DEFAULT_CHARTER_STEPS,
            "the gauge denominator is the charter terminal"
        );

        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                STEP_CURSOR_SLOT as u64,
                STEP_COMPARTMENT_SLOT as u64,
                ACTOR_CLEARANCE_SLOT as u64,
                CLEARANCE_GRAPH_ROOT_SLOT as u64,
            ],
            "the binds surface step / compartment / clearance / charter graph root"
        );
    }

    #[test]
    fn the_binds_carry_their_display_fmt_and_the_internals_are_adept() {
        let card = workflow_card_value();
        let binds = of_kind(&card, "bind");
        let bind_at = |slot: u8| {
            binds
                .iter()
                .find(|b| b["props"]["slot"].as_u64() == Some(slot as u64))
                .unwrap()
        };
        // The officer clearance paints an avatar handle and stays in the simple view.
        assert_eq!(bind_at(ACTOR_CLEARANCE_SLOT)["props"]["fmt"], "id");
        assert!(
            bind_at(ACTOR_CLEARANCE_SLOT)["props"]
                .get("adept")
                .is_none()
        );
        // The charter graph root paints short hex.
        assert_eq!(bind_at(CLEARANCE_GRAPH_ROOT_SLOT)["props"]["fmt"], "hash");
        // The raw state-machine numerics + the Merkle root are adept-only.
        assert_eq!(bind_at(STEP_CURSOR_SLOT)["props"]["adept"], true);
        assert_eq!(bind_at(STEP_COMPARTMENT_SLOT)["props"]["adept"], true);
        assert_eq!(bind_at(CLEARANCE_GRAPH_ROOT_SLOT)["props"]["adept"], true);
        // The charter-progress gauge is adept too (the breadcrumb shows the stage).
        let gauges = of_kind(&card, "gauge");
        assert_eq!(gauges[0]["props"]["adept"], true);
    }

    #[test]
    fn the_clearance_section_surfaces_the_dominance_tooth() {
        let card = workflow_card_value();
        let pills = of_kind(&card, "pill");
        assert!(
            pills
                .iter()
                .any(|p| p["props"]["text"] == "ClearanceDominates"),
            "the clearance section names the ClearanceDominates security tooth"
        );
        // The root-bound charter graph is surfaced as a live bind.
        let binds = of_kind(&card, "bind");
        assert!(
            binds
                .iter()
                .any(|b| b["props"]["slot"] == CLEARANCE_GRAPH_ROOT_SLOT),
            "the charter graph root is a live bind"
        );
    }

    #[test]
    fn every_button_carries_a_service_method_as_its_turn_payload() {
        let card = workflow_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 3, "Advance + Sign + View");
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the service method vocabulary. `Advance` and
        // `Sign` are the SAME advance_step turn at two charter points; `View` is the
        // serviced read.
        assert_eq!(
            turns,
            vec![METHOD_ADVANCE_STEP, METHOD_ADVANCE_STEP, METHOD_VIEW]
        );
        assert!(
            turns
                .iter()
                .all(|t| *t == METHOD_ADVANCE_STEP || *t == METHOD_VIEW),
            "every button names a real service method"
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = workflow_card_json();
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, breadcrumb, divider, charter section, clearance section, actions section
        assert_eq!(back["children"].as_array().unwrap().len(), 6);
    }
}
