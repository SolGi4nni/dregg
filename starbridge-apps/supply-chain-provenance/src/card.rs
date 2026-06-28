//! # supply-chain-provenance — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
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
//! ## The card shape — a rich, live custody surface
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) built from the rich deos-view
//! vocabulary (`section` / `pill` / `gauge` / `breadcrumb` / `divider` / `icon`):
//!
//!   - a **status header** — the app name + a `pill` naming the live custody state
//!     as a WORD (`IN-CUSTODY`), and a `breadcrumb` of the custody HAND-OFF chain
//!     (mint → custodian → custodian → … the baton's path) with the CURRENT holder
//!     marked — the killer custody visual, the single connected custody path made
//!     visible;
//!   - a **"Custody" `section`** surfacing the LIVE item state: a `gauge` bound to
//!     [`EPOCH_SLOT`](crate::EPOCH_SLOT) (the provenance epoch / hand-off count) and a
//!     `gauge` on the chain length [`HEAD_SLOT`](crate::HEAD_SLOT), plus `bind`s on the
//!     current [`CUSTODIAN_SLOT`](crate::CUSTODIAN_SLOT), the [`EPOCH_SLOT`](crate::EPOCH_SLOT),
//!     and the chain [`TIP_SLOT`](crate::TIP_SLOT) — each a fine-grained signal that
//!     re-reads the live value (the SAME witnessed read a native `bind` closure
//!     makes), so the surface advances the instant a fired handoff commits;
//!   - a **"Provenance Log" `section`** — the trust visual for the attested
//!     non-omission certificate ([`derived::attested_custody_log`](crate::derived::attested_custody_log)):
//!     a `pill` (`COMPLETE`) + an `icon`-marked line "all entries · none omitted",
//!     surfacing that the custody log carries a `dregg_query` MMR completeness
//!     certificate a light client checks against a pinned root;
//!   - an **"Actions" `section`** of one `icon`+`button` row per service method
//!     (`mint` / `handoff` / `view`), each `button` carrying its
//!     `onClick = { turn, arg }` — the EXACT cap-gated verified turn a click fires
//!     through the [`invoke()`](crate::service)/affordance seam.
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary
//! ([`METHOD_MINT`](crate::service::METHOD_MINT), …) so the card and the service
//! cell speak the same lifecycle.

use serde_json::{Value, json};

use crate::service::{METHOD_HANDOFF, METHOD_MINT, METHOD_VIEW};
use crate::{CUSTODIAN_SLOT, EPOCH_SLOT, HEAD_SLOT, TIP_SLOT};

/// The epoch gauge's denominator — a representative custody-chain length so a
/// well-travelled item fills the gauge (a typical item passes through a handful of
/// custodians: mint → warehouse → carrier → retailer → …).
const CHAIN_GAUGE_MAX: u64 = 8;

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

/// A `deos.ui.bind` node tagged with the model `slot` it re-reads + a label prefix.
fn bind(slot: usize, label: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label } })
}

/// A `deos.ui.gauge` node — a bound progress bar (`slot_value / max`, immediate-mode).
fn gauge(slot: usize, max: u64, label: &str) -> Value {
    json!({ "kind": "gauge", "props": { "slot": slot, "max": max, "label": label } })
}

/// A `deos.ui.breadcrumb` node — the custody hand-off path; the `active` holder
/// (the CURRENT custodian) is marked `›`.
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

/// **The supply-chain-provenance card as a `deos.ui.*` view-tree** (a
/// `serde_json::Value`).
///
/// A rich, live custody surface: a status header (name + `IN-CUSTODY` pill + the
/// custody hand-off breadcrumb with the current holder marked), a "Custody" section
/// surfacing the live epoch + chain-length gauges and the custodian / epoch / tip
/// binds, a "Provenance Log" section carrying the attested non-omission trust
/// visual ("all entries · none omitted"), and an "Actions" section of the three
/// icon-labelled lifecycle buttons. Renderer-independent DATA. The button `turn`
/// names are the [`service`](crate::service) method symbols.
pub fn provenance_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            row(vec![text("Supply-Chain Provenance"), pill("IN-CUSTODY", "good")]),
            // The custody hand-off chain — the baton's path mint → … → current
            // holder (marked). The single connected custody path made visible.
            breadcrumb(&["Mint", "Warehouse", "Carrier", "Retailer"], 2),
            divider(),
            section("Custody", "genuine", vec![
                gauge(EPOCH_SLOT as usize, CHAIN_GAUGE_MAX, "epoch "),
                gauge(HEAD_SLOT as usize, CHAIN_GAUGE_MAX, "chain length "),
                bind(CUSTODIAN_SLOT as usize, "custodian · "),
                bind(EPOCH_SLOT as usize, "epoch · "),
                bind(TIP_SLOT as usize, "chain tip · "),
            ]),
            // The attested-query trust visual — the non-omission completeness
            // certificate over the custody log (see `derived::attested_custody_log`).
            section("Provenance Log", "genuine", vec![
                row(vec![pill("COMPLETE", "good"), icon("✓", "good"), text("all entries · none omitted")]),
                text("a light client checks the MMR certificate against a pinned root"),
            ]),
            section("Actions", "", vec![
                action("✦", "Mint",    METHOD_MINT),
                action("→", "Handoff", METHOD_HANDOFF),
                action("○", "View",    METHOD_VIEW),
            ]),
        ]
    })
}

/// **The supply-chain-provenance card as serialized `deos.ui.*` JSON** —
/// byte-for-byte the `JSON.stringify(tree)` shape a `deos-view` renderer parses
/// (via `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn provenance_card_json() -> String {
    serde_json::to_string(&provenance_card_value()).expect("the provenance card serializes")
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
    fn the_card_is_a_vstack_with_a_named_header_and_a_custody_pill() {
        let card = provenance_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts
                .iter()
                .any(|t| t["props"]["text"] == "Supply-Chain Provenance"),
            "the header names the app"
        );
        let pills = of_kind(&card, "pill");
        // the header status pill + the provenance-log COMPLETE pill.
        assert!(
            pills.iter().any(|p| p["props"]["text"] == "IN-CUSTODY"),
            "the header carries the live custody-state pill"
        );
    }

    #[test]
    fn the_custody_breadcrumb_marks_the_current_holder() {
        let card = provenance_card_value();
        let crumbs = of_kind(&card, "breadcrumb");
        assert_eq!(crumbs.len(), 1);
        let items = crumbs[0]["props"]["items"].as_array().unwrap();
        assert_eq!(items.len(), 4, "mint → warehouse → carrier → retailer");
        assert_eq!(
            items[2]["label"], "› Carrier",
            "the current holder is marked"
        );
    }

    #[test]
    fn the_epoch_and_chain_gauges_read_the_live_slots() {
        let card = provenance_card_value();
        let gauges = of_kind(&card, "gauge");
        assert_eq!(gauges.len(), 2, "an epoch gauge + a chain-length gauge");
        assert_eq!(gauges[0]["props"]["slot"], EPOCH_SLOT as usize);
        assert_eq!(gauges[1]["props"]["slot"], HEAD_SLOT as usize);

        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![CUSTODIAN_SLOT as u64, EPOCH_SLOT as u64, TIP_SLOT as u64],
            "the binds surface custodian / epoch / chain tip"
        );
    }

    #[test]
    fn the_provenance_log_section_carries_the_non_omission_trust_visual() {
        let card = provenance_card_value();
        // The "Provenance Log" section surfaces the attested non-omission cert.
        let sections = of_kind(&card, "section");
        let log = sections
            .iter()
            .find(|s| s["props"]["title"] == "Provenance Log")
            .expect("the provenance-log section is present");
        let texts = of_kind(log, "text");
        assert!(
            texts
                .iter()
                .any(|t| t["props"]["text"] == "all entries · none omitted"),
            "the completeness certificate's 'none omitted' guarantee is the trust visual"
        );
        let pills = of_kind(log, "pill");
        assert!(
            pills.iter().any(|p| p["props"]["text"] == "COMPLETE"),
            "the log is marked COMPLETE (whole-log certificate)"
        );
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = provenance_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 3);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the service method vocabulary.
        assert_eq!(turns, vec![METHOD_MINT, METHOD_HANDOFF, METHOD_VIEW]);
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = provenance_card_json();
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, breadcrumb, divider, custody section, provenance-log section, actions section
        assert_eq!(back["children"].as_array().unwrap().len(), 6);
    }
}
