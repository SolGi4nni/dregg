//! # identity — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
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
//! ## The card shape — a rich, live credential surface
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) built from the rich deos-view
//! vocabulary (`section` / `pill` / `gauge` / `breadcrumb` / `divider` / `icon`):
//!
//!   - a **status header** — the app name + a `pill` naming the live credential
//!     validity as a WORD (`VALID`), and a `breadcrumb` of the whole credential
//!     lifecycle (issued → presented → verified → revoked) with the current step
//!     marked;
//!   - an **"Issuer" `section`** surfacing the LIVE cell state: a `gauge` bound to
//!     the [`ISSUANCE_COUNTER_SLOT`](crate::ISSUANCE_COUNTER_SLOT) (the strictly-
//!     monotonic issuance sequence) and a `gauge` on the
//!     [`REVOCATION_ROOT_SLOT`](crate::REVOCATION_ROOT_SLOT) (the append-only
//!     revocation horizon), plus `bind`s on the issuer-key root
//!     ([`ISSUER_AUTH_ROOT_SLOT`](crate::ISSUER_AUTH_ROOT_SLOT)), the credential id
//!     / issuance count ([`ISSUANCE_COUNTER_SLOT`](crate::ISSUANCE_COUNTER_SLOT)),
//!     the pinned schema ([`SCHEMA_COMMITMENT_SLOT`](crate::SCHEMA_COMMITMENT_SLOT)),
//!     and the revocation status ([`REVOCATION_ROOT_SLOT`](crate::REVOCATION_ROOT_SLOT))
//!     — each a fine-grained signal that re-reads the live value (the SAME witnessed
//!     read a native `bind` closure makes), so the surface advances when a fired
//!     issuer turn commits;
//!   - an **"Actions" `section`** of one `icon`+`button` row per lifecycle method
//!     (`issue` / `present` / `verify` / `revoke`), each `button` carrying its
//!     `onClick = { turn, arg }` — the EXACT method symbol the
//!     [`service`](crate::service) routes through the [`invoke()`](crate::service)
//!     front door (the mutators `issue` / `revoke` desugar to verified issuer turns;
//!     the reads `present` / `verify` name the serviced seam).
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary
//! ([`METHOD_ISSUE`](crate::service::METHOD_ISSUE), …) so the card and the service
//! cell speak the same lifecycle.

use serde_json::{Value, json};

use crate::service::{METHOD_ISSUE, METHOD_PRESENT, METHOD_REVOKE, METHOD_VERIFY};
use crate::{
    ISSUANCE_COUNTER_SLOT, ISSUER_AUTH_ROOT_SLOT, REVOCATION_ROOT_SLOT, SCHEMA_COMMITMENT_SLOT,
};

/// The issuance gauge's denominator — a representative issuance ceiling so a busy
/// issuer fills the bar (the `DEFAULT_ISSUER_BUDGET` is `100_000`; a smaller window
/// keeps the live sequence legible on the surface).
const ISSUANCE_GAUGE_MAX: u64 = 64;

/// The revocation gauge's denominator — a representative revocation horizon so the
/// append-only root growth reads as progress against a window.
const REVOCATION_GAUGE_MAX: u64 = 16;

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

/// An action row — an `icon` + a lifecycle `button` (the verified-turn / serviced-seam
/// affordance). The `turn` is the [`service`](crate::service) method symbol.
fn action(glyph: &str, label: &str, turn: &str) -> Value {
    row(vec![icon(glyph, "accent"), button(label, turn, 0)])
}

/// **The identity card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A rich, live credential surface: a status header (name + `VALID` pill + the
/// credential-lifecycle breadcrumb), an "Issuer" section surfacing the live issuance
/// sequence gauge, the revocation horizon gauge, and the issuer-key / credential-id /
/// schema / status binds, and an "Actions" section of the four icon-labelled lifecycle
/// buttons. Renderer-independent DATA: hand it to any `deos-view` renderer
/// (native / web / discord) to paint the SAME card. The button `turn` names are the
/// [`service`](crate::service) method symbols.
pub fn identity_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            row(vec![text("Identity"), pill("VALID", "good")]),
            breadcrumb(&["Issued", "Presented", "Verified", "Revoked"], 2),
            divider(),
            section("Issuer", "genuine", vec![
                gauge(ISSUANCE_COUNTER_SLOT, ISSUANCE_GAUGE_MAX, "issuance seq "),
                gauge(REVOCATION_ROOT_SLOT, REVOCATION_GAUGE_MAX, "revocation horizon "),
                bind(ISSUER_AUTH_ROOT_SLOT, "issuer key · "),
                bind(ISSUANCE_COUNTER_SLOT, "credential id · "),
                bind(SCHEMA_COMMITMENT_SLOT, "schema · "),
                bind(REVOCATION_ROOT_SLOT, "status · "),
            ]),
            section("Actions", "", vec![
                action("+", "Issue",   METHOD_ISSUE),
                action("→", "Present", METHOD_PRESENT),
                action("✓", "Verify",  METHOD_VERIFY),
                action("⊘", "Revoke",  METHOD_REVOKE),
            ]),
        ]
    })
}

/// **The identity card as serialized `deos.ui.*` JSON** — byte-for-byte the
/// `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn identity_card_json() -> String {
    serde_json::to_string(&identity_card_value()).expect("the identity card serializes")
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
    fn the_card_is_a_vstack_with_a_named_header_and_a_validity_pill() {
        let card = identity_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts.iter().any(|t| t["props"]["text"] == "Identity"),
            "the header names the app"
        );
        let pills = of_kind(&card, "pill");
        assert_eq!(pills.len(), 1);
        assert_eq!(pills[0]["props"]["text"], "VALID");
    }

    #[test]
    fn the_lifecycle_breadcrumb_marks_the_current_step() {
        let card = identity_card_value();
        let crumbs = of_kind(&card, "breadcrumb");
        assert_eq!(crumbs.len(), 1);
        let items = crumbs[0]["props"]["items"].as_array().unwrap();
        assert_eq!(items.len(), 4, "issued → presented → verified → revoked");
        assert_eq!(items[2]["label"], "› Verified", "the active step is marked");
    }

    #[test]
    fn the_issuance_and_revocation_gauges_read_the_live_slots() {
        let card = identity_card_value();
        let gauges = of_kind(&card, "gauge");
        assert_eq!(gauges.len(), 2, "an issuance gauge + a revocation gauge");
        assert_eq!(gauges[0]["props"]["slot"], ISSUANCE_COUNTER_SLOT);
        assert_eq!(gauges[0]["props"]["max"], ISSUANCE_GAUGE_MAX);
        assert_eq!(gauges[1]["props"]["slot"], REVOCATION_ROOT_SLOT);
        assert_eq!(gauges[1]["props"]["max"], REVOCATION_GAUGE_MAX);
    }

    #[test]
    fn the_binds_surface_issuer_key_credential_id_schema_and_status() {
        let card = identity_card_value();
        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                ISSUER_AUTH_ROOT_SLOT as u64,
                ISSUANCE_COUNTER_SLOT as u64,
                SCHEMA_COMMITMENT_SLOT as u64,
                REVOCATION_ROOT_SLOT as u64,
            ],
            "the binds surface issuer key / credential id / schema / status"
        );
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = identity_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 4);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the service method vocabulary.
        assert_eq!(
            turns,
            vec![METHOD_ISSUE, METHOD_PRESENT, METHOD_VERIFY, METHOD_REVOKE]
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = identity_card_json();
        // Round-trips through serde (the shape a deos-view renderer's parser reads).
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, breadcrumb, divider, issuer section, actions section
        assert_eq!(back["children"].as_array().unwrap().len(), 5);
    }
}
