//! # gallery — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
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
//! ## The card shape — a rich, live curation surface
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) built from the rich deos-view
//! vocabulary (`section` / `pill` / `gauge` / `breadcrumb` / `divider` / `icon`):
//!
//!   - a **status header** — the app name + a `pill` naming the lifecycle stage as
//!     a WORD (`SUBMISSION`), and a `breadcrumb` of the whole lifecycle
//!     (submission → reveal → curated) with the current step marked;
//!   - a **"Lifecycle" `section`** surfacing the LIVE cell state: a `gauge` bound to
//!     [`PHASE_SLOT`](crate::PHASE_SLOT) (the lifecycle progress, re-read off the
//!     ledger), and `bind`s on the [`CURATOR_SLOT`](crate::CURATOR_SLOT), the latest
//!     sealed entry ([`SUBMIT_BASE`](crate::SUBMIT_BASE)) and the
//!     [`FEATURED_SLOT`](crate::FEATURED_SLOT) — each a fine-grained signal that
//!     re-reads the live value (the SAME witnessed read a native `bind` closure
//!     makes), so the surface advances when a fired turn commits;
//!   - an **"Actions" `section`** of one `icon`+`button` row per lifecycle method
//!     (`submit` / `close_submissions` / `reveal` / `curate`), each `button`
//!     carrying its `onClick = { turn, arg }` — the EXACT cap-gated verified turn a
//!     click fires through the [`invoke()`](crate::service)/affordance seam.
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary
//! ([`METHOD_SUBMIT`](crate::service::METHOD_SUBMIT), …) so the card and the service
//! cell speak the same lifecycle.

use serde_json::{Value, json};

use crate::service::{METHOD_CLOSE_SUBMISSIONS, METHOD_CURATE, METHOD_REVEAL, METHOD_SUBMIT};
use crate::{
    CURATOR_SLOT, FEATURED_SLOT, PHASE_CURATED, PHASE_REVEAL, PHASE_SLOT, PHASE_SUBMISSION,
    SUBMIT_BASE,
};

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A `deos.ui.pill` node — a colored status badge (`tag` selects the semantic
/// palette: `good`/`warn`/`bad`/`accent`/`muted`).
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

/// A `deos.ui.section` node — a titled, bordered container. `tag=="genuine"` accents
/// the border.
fn section(title: &str, tag: &str, children: Vec<Value>) -> Value {
    json!({ "kind": "section", "props": { "title": title, "tag": tag }, "children": children })
}

/// A `deos.ui.bind` node tagged with the model `slot` it re-reads + a label prefix and a
/// display `fmt` (`"id"` avatar-handle / `"hash"` short-hex / `"amount"` grouped /
/// `"raw"` plain) so an opaque identity scalar / sealed digest paints short + friendly.
/// `adept` hides a dev-y row (a sealed digest the friendlier signals already cover) from
/// the simple projection; revealed in the adept "see the bones" view.
fn bind(slot: usize, label: &str, fmt: &str, adept: bool) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt, "adept": adept } })
}

/// A `deos.ui.gauge` node — a bound progress bar. The fill is `slot_value / max`
/// (clamped). Reads its slot IMMEDIATE-MODE off the live ledger. `adept` hides the raw
/// numeric in the simple projection (the live pill + breadcrumb already show the stage);
/// revealed in the adept "see the bones" view.
fn gauge(slot: usize, max: u64, label: &str, adept: bool) -> Value {
    json!({ "kind": "gauge", "props": { "slot": slot, "max": max, "label": label, "adept": adept } })
}

/// A `deos.ui.breadcrumb` node — a `→`-joined lifecycle path. The `active` step is
/// marked with a leading `▸`.
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

/// **The gallery card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A rich, live curation surface: a status header (name + `SUBMISSION` pill +
/// lifecycle breadcrumb), a "Lifecycle" section surfacing the live phase gauge +
/// curator / sealed-entry / featured binds, and an "Actions" section of the four
/// icon-labelled lifecycle buttons. Renderer-independent DATA: hand it to any
/// `deos-view` renderer (native / web / discord) to paint the SAME card. The button
/// `turn` names are the [`service`](crate::service) method symbols.
pub fn gallery_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            row(vec![text("Sealed Gallery"), pill_live(PHASE_SLOT, "SUBMISSION", "warn", json!([
                { "value": PHASE_SUBMISSION, "label": "SUBMISSION", "tag": "warn" },
                { "value": PHASE_REVEAL,     "label": "REVEAL",     "tag": "accent" },
                { "value": PHASE_CURATED,    "label": "CURATED",    "tag": "good" },
            ]))]),
            breadcrumb(&["Submission", "Reveal", "Curated"], 0),
            divider(),
            section("Lifecycle", "genuine", vec![
                gauge(PHASE_SLOT, PHASE_CURATED, "phase ", true),
                bind(CURATOR_SLOT, "curator key · ", "id", false),
                bind(SUBMIT_BASE, "sealed entry · ", "hash", true),
                bind(FEATURED_SLOT, "featured · ", "id", false),
            ]),
            section("Actions", "", vec![
                action("+", "Submit",            METHOD_SUBMIT),
                action("×", "Close Submissions", METHOD_CLOSE_SUBMISSIONS),
                action("›", "Reveal",            METHOD_REVEAL),
                action("✓", "Curate",            METHOD_CURATE),
            ]),
        ]
    })
}

/// **The gallery card as serialized `deos.ui.*` JSON** — byte-for-byte the
/// `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn gallery_card_json() -> String {
    serde_json::to_string(&gallery_card_value()).expect("the gallery card serializes")
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Recursively collect every node of `kind` in the tree (the card is now nested in
    /// `row`/`section` containers, so the invariants walk the whole tree).
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
    fn the_card_is_a_vstack_with_a_named_header_and_a_lifecycle_pill() {
        let card = gallery_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts.iter().any(|t| t["props"]["text"] == "Sealed Gallery"),
            "the header names the app"
        );
        let pills = of_kind(&card, "pill");
        assert_eq!(pills.len(), 1, "one lifecycle-stage pill");
        // The header pill is LIVE: it reads PHASE_SLOT and maps the value to a word.
        assert_eq!(
            pills[0]["props"]["text"], "SUBMISSION",
            "the static fallback word"
        );
        assert_eq!(pills[0]["props"]["slot"], PHASE_SLOT);
        let cases = pills[0]["props"]["cases"].as_array().unwrap();
        assert_eq!(cases.len(), 3, "SUBMISSION / REVEAL / CURATED");
        assert_eq!(cases[2]["value"], PHASE_CURATED);
        assert_eq!(cases[2]["label"], "CURATED");
        assert_eq!(cases[2]["tag"], "good");
    }

    #[test]
    fn the_identity_and_seal_binds_carry_their_display_fmt() {
        let card = gallery_card_value();
        let binds = of_kind(&card, "bind");
        let fmt = |slot: usize| -> String {
            binds
                .iter()
                .find(|b| b["props"]["slot"].as_u64() == Some(slot as u64))
                .and_then(|b| b["props"]["fmt"].as_str())
                .unwrap()
                .to_string()
        };
        // Identity scalars paint avatar handles; the sealed entry digest paints hex.
        assert_eq!(fmt(CURATOR_SLOT), "id");
        assert_eq!(fmt(FEATURED_SLOT), "id");
        assert_eq!(fmt(SUBMIT_BASE), "hash");
    }

    #[test]
    fn the_dev_y_rows_are_marked_adept() {
        let card = gallery_card_value();
        let adept = |kind: &str, slot: usize| -> bool {
            of_kind(&card, kind)
                .iter()
                .find(|n| n["props"]["slot"].as_u64() == Some(slot as u64))
                .and_then(|n| n["props"]["adept"].as_bool())
                .unwrap()
        };
        // The raw phase gauge + the sealed-entry digest hide in the simple view.
        assert!(adept("gauge", PHASE_SLOT), "the raw phase integer gauge");
        assert!(adept("bind", SUBMIT_BASE), "the sealed-entry digest");
        // The warm identities stay visible.
        assert!(!adept("bind", CURATOR_SLOT));
        assert!(!adept("bind", FEATURED_SLOT));
    }

    #[test]
    fn the_lifecycle_breadcrumb_marks_the_current_step() {
        let card = gallery_card_value();
        let crumbs = of_kind(&card, "breadcrumb");
        assert_eq!(crumbs.len(), 1);
        let items = crumbs[0]["props"]["items"].as_array().unwrap();
        assert_eq!(items.len(), 3, "submission → reveal → curated");
        assert_eq!(
            items[0]["label"], "› Submission",
            "the active step is marked"
        );
    }

    #[test]
    fn the_phase_gauge_and_state_binds_read_the_live_slots() {
        let card = gallery_card_value();
        let gauges = of_kind(&card, "gauge");
        assert_eq!(gauges.len(), 1);
        assert_eq!(gauges[0]["props"]["slot"], PHASE_SLOT);
        assert_eq!(gauges[0]["props"]["max"], PHASE_CURATED);

        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                CURATOR_SLOT as u64,
                SUBMIT_BASE as u64,
                FEATURED_SLOT as u64
            ],
            "the binds surface curator / sealed entry / featured"
        );
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = gallery_card_value();
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
                METHOD_SUBMIT,
                METHOD_CLOSE_SUBMISSIONS,
                METHOD_REVEAL,
                METHOD_CURATE
            ]
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = gallery_card_json();
        // Round-trips through serde (the shape a deos-view renderer's parser reads).
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, breadcrumb, divider, lifecycle section, actions section
        assert_eq!(back["children"].as_array().unwrap().len(), 5);
    }
}
