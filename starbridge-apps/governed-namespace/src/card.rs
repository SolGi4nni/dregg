//! # governed-namespace — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
//!
//! The fourth axis (AX4) of a modern starbridge-app: the app lives IN the deos
//! world by shipping its surface as a **renderer-independent card** — a serializable
//! `deos.ui.*` element-tree ([`deos_view::ViewNode`] in the renderer crate). The
//! SAME tree renders three ways (the renderer-independence seam): native gpui pixels
//! in the cockpit, a browser-loadable HTML document, and a discord embed — all from
//! this one piece of DATA. See `deos-view/src/{render,web,discord}.rs` for the three
//! renderers and `docs/reference/deos-view.md`.
//!
//! ## Why the card is DATA, not a renderer call
//!
//! `deos-view` pulls BOTH the SpiderMonkey (`mozjs`) and the gpui native elephants,
//! so it is a STANDALONE workspace EXCLUDED from the repo-root workspace (see its
//! `Cargo.toml`). A starbridge-app must never depend on it — that would
//! feature-unify the elephants onto the main build. So the app's contribution is the
//! **view-tree JSON** (this module): pure `serde_json`, no elephant. The deos
//! world's renderers consume it; this module owns the card definition and proves it
//! is well-formed.
//!
//! ## The card shape
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) carrying:
//!   - a `text` header (`"Governed Namespace"`);
//!   - a `bind` on [`VERSION_SLOT`](crate::VERSION_SLOT) — a fine-grained signal
//!     that re-reads the live route-table generation off the ledger (the SAME
//!     witnessed read a native `bind` closure makes), so the displayed version
//!     advances when a committed swap lands;
//!   - one `button` per lifecycle method (`propose` / `vote` / `commit` /
//!     `register`), each carrying its `onClick = { turn, arg }` — the EXACT cap-gated
//!     verified turn a click fires through the
//!     [`invoke()`](crate::service)/affordance seam (the button's payload is the
//!     method symbol the service routes).
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary
//! ([`METHOD_PROPOSE`](crate::service::METHOD_PROPOSE), …) so the card and the
//! service cell speak the same lifecycle.

use serde_json::{Value, json};

use crate::VERSION_SLOT;
use crate::service::{METHOD_COMMIT, METHOD_PROPOSE, METHOD_REGISTER, METHOD_VOTE};

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

/// **The governed-namespace card as a `deos.ui.*` view-tree** (a
/// `serde_json::Value`).
///
/// A `vstack` of a header, a live `bind` on the route-table [`VERSION_SLOT`], and
/// the four lifecycle buttons. Renderer-independent DATA: hand it to any `deos-view`
/// renderer (native / web / discord) to paint the SAME card. The button `turn`
/// names are the [`service`](crate::service) method symbols.
pub fn governance_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            text("Governed Namespace"),
            bind(VERSION_SLOT as usize, "version: "),
            button("Propose",  METHOD_PROPOSE,  0),
            button("Vote",     METHOD_VOTE,     0),
            button("Commit",   METHOD_COMMIT,   0),
            button("Register", METHOD_REGISTER, 0),
        ]
    })
}

/// **The governed-namespace card as serialized `deos.ui.*` JSON** — byte-for-byte
/// the `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn governance_card_json() -> String {
    serde_json::to_string(&governance_card_value()).expect("the governance card serializes")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_card_is_a_vstack_with_a_header_a_version_bind_and_four_buttons() {
        let card = governance_card_value();
        assert_eq!(card["kind"], "vstack");
        let children = card["children"].as_array().expect("children");
        // header, bind, propose, vote, commit, register
        assert_eq!(children.len(), 6);
        assert_eq!(children[0]["kind"], "text");
        assert_eq!(children[0]["props"]["text"], "Governed Namespace");
    }

    #[test]
    fn the_version_bind_reads_the_route_table_generation_slot() {
        let card = governance_card_value();
        let bind = &card["children"][1];
        assert_eq!(bind["kind"], "bind");
        assert_eq!(bind["props"]["slot"], VERSION_SLOT as usize);
        assert_eq!(bind["props"]["label"], "version: ");
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = governance_card_value();
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
            vec![METHOD_PROPOSE, METHOD_VOTE, METHOD_COMMIT, METHOD_REGISTER]
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = governance_card_json();
        // Round-trips through serde (the shape a deos-view renderer's parser reads).
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        assert_eq!(back["children"].as_array().unwrap().len(), 6);
    }
}
