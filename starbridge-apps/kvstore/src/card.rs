//! # kvstore — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
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
//! ## The card shape — a legible little key-value store
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) built from the rich deos-view
//! vocabulary (`section` / `pill` / `gauge` / `divider` / `icon`):
//!
//!   - a **status header** — the app name + a `pill` reading `LIVE`;
//!   - a **"Store" `section`** surfacing the LIVE cell header: a `gauge` bound to
//!     [`COUNT_SLOT`](crate::COUNT_SLOT) (entries / [`CAPACITY`](crate::CAPACITY)),
//!     plus `bind`s on the store [`VERSION_SLOT`](crate::VERSION_SLOT), the entry
//!     count, and the [`LAST_KEY_SLOT`](crate::LAST_KEY_SLOT) /
//!     [`LAST_VALUE_SLOT`](crate::LAST_VALUE_SLOT) — each a fine-grained signal that
//!     re-reads the live value (the SAME witnessed read a native `bind` closure
//!     makes), so the surface advances when a fired `put`/`delete` commits;
//!   - an **"Actions" `section`** of one `icon`+`button` row per service method
//!     (`put` / `get` / `delete`), each `button` carrying its
//!     `onClick = { turn, arg }` — the EXACT cap-gated verified turn a click fires
//!     through the [`invoke()`](crate)/affordance seam.
//!
//! The button `turn` names match the service method vocabulary
//! ([`METHOD_PUT`](crate::METHOD_PUT), …) so the card and the service cell speak
//! the same method language.

use serde_json::{Value, json};

use crate::{
    CAPACITY, COUNT_SLOT, LAST_KEY_SLOT, LAST_VALUE_SLOT, METHOD_DELETE, METHOD_GET, METHOD_PUT,
    VERSION_SLOT,
};

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

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

/// A `deos.ui.bind` node tagged with the model `slot` it re-reads + a label prefix
/// and a display `fmt` (`"id"` avatar-handle / `"hash"` short-hex / `"amount"`
/// grouped / `"raw"` plain) so an opaque key/digest/amount paints short + friendly.
/// `adept` hides the row in the simple projection (it duplicates a friendlier signal
/// or is a raw internal numeric); revealed in the adept "see the bones" view.
fn bind(slot: usize, label: &str, fmt: &str, adept: bool) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt, "adept": adept } })
}

/// A `deos.ui.gauge` node — a bound progress bar (`slot_value / max`, immediate-mode).
/// `adept` hides the raw numeric in the simple projection; revealed in the adept view.
fn gauge(slot: usize, max: u64, label: &str, adept: bool) -> Value {
    json!({ "kind": "gauge", "props": { "slot": slot, "max": max, "label": label, "adept": adept } })
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

/// **The kvstore card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A legible little key-value store: a status header (name + a `LIVE` pill), a
/// "Store" section surfacing the live entry-count gauge and the version / count /
/// last-key / last-value binds, and an "Actions" section of the three
/// icon-labelled method buttons. Renderer-independent DATA: hand it to any
/// `deos-view` renderer (native / web / discord) to paint the SAME card. The
/// button `turn` names are the service method symbols
/// ([`METHOD_PUT`](crate::METHOD_PUT), …).
pub fn kvstore_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            row(vec![text("Key-Value Store"), pill_live(COUNT_SLOT, "ACTIVE", "good", json!([
                { "value": 0, "label": "EMPTY", "tag": "muted" },
            ]))]),
            divider(),
            section("Store", "genuine", vec![
                gauge(COUNT_SLOT, CAPACITY as u64, "entries ", false),
                bind(VERSION_SLOT, "version · ", "raw", true),
                bind(COUNT_SLOT, "entries · ", "amount", true),
                bind(LAST_KEY_SLOT, "last key · ", "id", false),
                bind(LAST_VALUE_SLOT, "last value · ", "hash", false),
            ]),
            section("Actions", "", vec![
                action("+", "Put",    METHOD_PUT),
                action("?", "Get",    METHOD_GET),
                action("×", "Delete", METHOD_DELETE),
            ]),
        ]
    })
}

/// **The kvstore card as serialized `deos.ui.*` JSON** — byte-for-byte the
/// `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn kvstore_card_json() -> String {
    serde_json::to_string(&kvstore_card_value()).expect("the kvstore card serializes")
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
    fn the_card_is_a_vstack_with_a_named_header_and_a_live_status_pill() {
        let card = kvstore_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts
                .iter()
                .any(|t| t["props"]["text"] == "Key-Value Store"),
            "the header names the app"
        );
        let pills = of_kind(&card, "pill");
        assert_eq!(pills.len(), 1);
        // The header pill is LIVE: it reads COUNT_SLOT and maps an empty store to a word.
        assert_eq!(
            pills[0]["props"]["text"], "ACTIVE",
            "the static fallback word"
        );
        assert_eq!(pills[0]["props"]["slot"], COUNT_SLOT);
        let cases = pills[0]["props"]["cases"].as_array().unwrap();
        assert_eq!(cases.len(), 1, "an EMPTY case for a zero-entry store");
        assert_eq!(cases[0]["value"], 0);
        assert_eq!(cases[0]["label"], "EMPTY");
    }

    #[test]
    fn the_key_and_value_binds_carry_their_display_fmt() {
        let card = kvstore_card_value();
        let binds = of_kind(&card, "bind");
        let fmt = |slot: usize| -> String {
            binds
                .iter()
                .find(|b| b["props"]["slot"].as_u64() == Some(slot as u64))
                .and_then(|b| b["props"]["fmt"].as_str())
                .unwrap()
                .to_string()
        };
        assert_eq!(
            fmt(LAST_KEY_SLOT),
            "id",
            "the last key paints an avatar handle"
        );
        assert_eq!(
            fmt(LAST_VALUE_SLOT),
            "hash",
            "the last value paints short hex"
        );
        assert_eq!(fmt(COUNT_SLOT), "amount", "the entry count groups digits");
        assert_eq!(fmt(VERSION_SLOT), "raw", "the internal version stays raw");
    }

    #[test]
    fn the_devy_internal_binds_are_marked_adept() {
        let card = kvstore_card_value();
        let binds = of_kind(&card, "bind");
        let adept = |slot: usize| -> bool {
            binds
                .iter()
                .find(|b| b["props"]["slot"].as_u64() == Some(slot as u64))
                .and_then(|b| b["props"]["adept"].as_bool())
                .unwrap()
        };
        // The monotone version + the count row (it duplicates the gauge) hide by default.
        assert!(adept(VERSION_SLOT), "the internal version is adept-only");
        assert!(adept(COUNT_SLOT), "the count duplicates the gauge");
        // The human-meaningful last-key / last-value stay in the simple projection.
        assert!(!adept(LAST_KEY_SLOT));
        assert!(!adept(LAST_VALUE_SLOT));
    }

    #[test]
    fn the_entry_count_gauge_reads_the_count_slot_against_capacity() {
        let card = kvstore_card_value();
        let gauges = of_kind(&card, "gauge");
        assert_eq!(gauges.len(), 1, "one entry-count gauge");
        assert_eq!(gauges[0]["props"]["slot"], COUNT_SLOT);
        assert_eq!(gauges[0]["props"]["max"].as_u64().unwrap(), CAPACITY as u64);
    }

    #[test]
    fn the_store_section_binds_the_live_header() {
        let card = kvstore_card_value();
        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                VERSION_SLOT as u64,
                COUNT_SLOT as u64,
                LAST_KEY_SLOT as u64,
                LAST_VALUE_SLOT as u64
            ],
            "the binds surface version / entries / last key / last value"
        );
    }

    #[test]
    fn the_card_has_a_store_section_and_an_actions_section() {
        let card = kvstore_card_value();
        let sections = of_kind(&card, "section");
        let titles: Vec<&str> = sections
            .iter()
            .map(|s| s["props"]["title"].as_str().unwrap())
            .collect();
        assert_eq!(titles, vec!["Store", "Actions"]);
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = kvstore_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 3);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the service method vocabulary.
        assert_eq!(turns, vec![METHOD_PUT, METHOD_GET, METHOD_DELETE]);
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = kvstore_card_json();
        // Round-trips through serde (the shape a deos-view renderer's parser reads).
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, divider, store section, actions section
        assert_eq!(back["children"].as_array().unwrap().len(), 4);
    }
}
