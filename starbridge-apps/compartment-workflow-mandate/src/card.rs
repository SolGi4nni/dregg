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
//! ## The card shape
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) carrying:
//!   - a `text` header (`"Compartment Workflow"`);
//!   - a `bind` on [`STEP_CURSOR_SLOT`](crate::STEP_CURSOR_SLOT) — a fine-grained
//!     signal that re-reads the live charter cursor off the ledger, so the displayed
//!     step advances when a fired turn commits;
//!   - an `Advance Step` button (`onClick` fires the [`service`](crate::service)
//!     [`METHOD_ADVANCE_STEP`](crate::service::METHOD_ADVANCE_STEP) turn) and a
//!     `View` button (the [`METHOD_VIEW`](crate::service::METHOD_VIEW) serviced read).
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary so
//! the card and the service cell speak the same charter.

use serde_json::{Value, json};

use crate::STEP_CURSOR_SLOT;
use crate::service::{METHOD_ADVANCE_STEP, METHOD_VIEW};

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

/// **The compartment-workflow card as a `deos.ui.*` view-tree** (a
/// `serde_json::Value`).
///
/// A `vstack` of a header, a live `bind` on the charter [`STEP_CURSOR_SLOT`], and the
/// `Advance Step` / `View` buttons. Renderer-independent DATA: hand it to any
/// `deos-view` renderer (native / web / discord) to paint the SAME card. The button
/// `turn` names are the [`service`](crate::service) method symbols.
pub fn workflow_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            text("Compartment Workflow"),
            bind(STEP_CURSOR_SLOT as usize, "step: "),
            button("Advance Step", METHOD_ADVANCE_STEP, 0),
            button("View",         METHOD_VIEW,         0),
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

    #[test]
    fn the_card_is_a_vstack_with_a_header_a_step_bind_and_two_buttons() {
        let card = workflow_card_value();
        assert_eq!(card["kind"], "vstack");
        let children = card["children"].as_array().expect("children");
        // header, bind, advance_step, view
        assert_eq!(children.len(), 4);
        assert_eq!(children[0]["kind"], "text");
        assert_eq!(children[0]["props"]["text"], "Compartment Workflow");
    }

    #[test]
    fn the_step_bind_reads_the_cursor_slot() {
        let card = workflow_card_value();
        let bind = &card["children"][1];
        assert_eq!(bind["kind"], "bind");
        assert_eq!(bind["props"]["slot"], STEP_CURSOR_SLOT);
        assert_eq!(bind["props"]["label"], "step: ");
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = workflow_card_value();
        let children = card["children"].as_array().unwrap();
        let buttons: Vec<&Value> = children.iter().filter(|c| c["kind"] == "button").collect();
        assert_eq!(buttons.len(), 2);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the service method vocabulary.
        assert_eq!(turns, vec![METHOD_ADVANCE_STEP, METHOD_VIEW]);
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = workflow_card_json();
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        assert_eq!(back["children"].as_array().unwrap().len(), 4);
    }
}
