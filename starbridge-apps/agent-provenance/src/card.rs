//! # agent-provenance — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
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
//! ## The card shape — a rich, live append-only-log surface
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) built from the rich deos-view
//! vocabulary (`section` / `pill` / `gauge` / `divider` / `icon` / `row`):
//!
//!   - a **status header** — the app name + a `pill` naming the live recorder state
//!     as a WORD (`RECORDING`): the log is an open append cursor accepting the next
//!     chained entry;
//!   - a **"Log" `section`** surfacing the LIVE chain state: a `gauge` bound to the
//!     chain length [`HEAD_SLOT`](crate::HEAD_SLOT) (how full this cell's entry record
//!     is, against [`ENTRY_CAPACITY`](crate::ENTRY_CAPACITY)), plus `bind`s on the
//!     entry count [`HEAD_SLOT`](crate::HEAD_SLOT) and the chain tip
//!     [`TIP_SLOT`](crate::TIP_SLOT) — each a fine-grained signal that re-reads the
//!     live value (the SAME witnessed read a native `bind` closure makes), so the
//!     surface advances the instant a fired `append` turn commits and the executor's
//!     `WriteOnce` board freezes the new entry;
//!   - an **"Integrity" `section`** — the trust visual for the attested non-omission
//!     certificate ([`derived::attested_provenance_log`](crate::derived::attested_provenance_log)):
//!     a `pill` (`COMPLETE`) + an `icon`-marked line "all entries · none omitted",
//!     surfacing that the log carries a `dregg_query` MMR completeness certificate a
//!     light client checks against a pinned root — the append-only-integrity story
//!     made legible (none omitted, none reordered, none forged);
//!   - an **"Actions" `section`** of one `icon`+`button` row per service method
//!     (`append` / `view`), each `button` carrying its `onClick = { turn, arg }` —
//!     the EXACT cap-gated verified turn a click fires through the
//!     [`invoke()`](crate::service)/affordance seam. The append glyph (`✎`) names the
//!     record action; the view glyph (`○`) names the read.
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary
//! ([`METHOD_APPEND`](crate::service::METHOD_APPEND), …) so the card and the service
//! cell speak the same log language.

use serde_json::{Value, json};

use crate::service::{METHOD_APPEND, METHOD_VIEW};
use crate::{ENTRY_CAPACITY, HEAD_SLOT, TIP_SLOT};

/// The chain-length gauge denominator — a single provenance cell's entry record
/// capacity. The gauge reads "how full is this cell"; when it fills, the log
/// chains across to a fresh cell (its `TIP` becomes the next cell's genesis
/// predecessor), so a full gauge marks a cell-boundary handover, not a limit.
const LOG_GAUGE_MAX: u64 = ENTRY_CAPACITY as u64;

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

/// A `deos.ui.bind` node tagged with the model `slot` it re-reads + a label prefix and a
/// display `fmt` (`"id"` avatar-handle / `"hash"` short-hex / `"amount"` grouped /
/// `"raw"` plain) so an opaque digest/count paints short + friendly.
fn bind(slot: usize, label: &str, fmt: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt } })
}

/// A `deos.ui.bind` node marked `adept` — hidden in the simple projection (a raw digest
/// / internal signal); revealed in the adept "see the bones" view.
fn bind_adept(slot: usize, label: &str, fmt: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt, "adept": true } })
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

/// An action row — an `icon` + a log-method `button` (the verified-turn affordance).
fn action(glyph: &str, label: &str, turn: &str) -> Value {
    row(vec![icon(glyph, "accent"), button(label, turn, 0)])
}

/// **The agent-provenance card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A rich, live append-only-log surface: a status header (name + `RECORDING`
/// pill), a "Log" section surfacing the live chain-length gauge and the entry-count
/// / chain-tip binds, an "Integrity" section carrying the attested non-omission
/// trust visual ("all entries · none omitted"), and an "Actions" section of the two
/// icon-labelled log buttons. Renderer-independent DATA. The button `turn` names
/// are the [`service`](crate::service) method symbols.
pub fn provenance_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            // The header status pill is LIVE: it reads the append cursor (HEAD) and
            // shows EMPTY when the log has no entries, else falls through to RECORDING.
            row(vec![text("Agent Provenance"), pill_live(HEAD_SLOT, "RECORDING", "good", json!([
                { "value": 0, "label": "EMPTY", "tag": "muted" },
            ]))]),
            divider(),
            // The live chain state — the append cursor (entry count) drives both the
            // gauge and a bind; the tip is the latest committed link digest.
            section("Log", "genuine", vec![
                gauge(HEAD_SLOT, LOG_GAUGE_MAX, "entries ", false),
                bind(HEAD_SLOT, "entries · ", "raw"),
                // The chain tip is a raw link digest — a dev-y hash row, adept-only.
                bind_adept(TIP_SLOT, "chain tip · ", "hash"),
            ]),
            // The attested-query trust visual — the non-omission completeness
            // certificate over the log (see `derived::attested_provenance_log`). The
            // append-only-integrity story: a light client can verify nothing was
            // omitted, reordered, or forged.
            section("Integrity", "genuine", vec![
                row(vec![pill("COMPLETE", "good"), icon("✓", "good"), text("all entries · none omitted")]),
                text("a light client checks the MMR certificate against a pinned root"),
            ]),
            section("Actions", "", vec![
                action("✎", "Append", METHOD_APPEND),
                action("○", "View",   METHOD_VIEW),
            ]),
        ]
    })
}

/// **The agent-provenance card as serialized `deos.ui.*` JSON** — byte-for-byte
/// the `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
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
    fn the_card_is_a_vstack_with_a_named_header_and_a_recording_pill() {
        let card = provenance_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts
                .iter()
                .any(|t| t["props"]["text"] == "Agent Provenance"),
            "the header names the app"
        );
        let pills = of_kind(&card, "pill");
        // The header pill is LIVE: it reads HEAD_SLOT and maps 0 → EMPTY.
        let header = pills
            .iter()
            .find(|p| p["props"]["slot"] == HEAD_SLOT)
            .expect("the header carries the live recorder-state pill");
        assert_eq!(
            header["props"]["text"], "RECORDING",
            "the static fallback word (a non-empty log)"
        );
        let cases = header["props"]["cases"].as_array().unwrap();
        assert_eq!(cases.len(), 1, "head 0 = EMPTY");
        assert_eq!(cases[0]["value"], 0);
        assert_eq!(cases[0]["label"], "EMPTY");
    }

    #[test]
    fn the_log_section_gauge_and_binds_read_the_live_slots() {
        let card = provenance_card_value();
        let gauges = of_kind(&card, "gauge");
        assert_eq!(gauges.len(), 1, "a chain-length gauge");
        assert_eq!(gauges[0]["props"]["slot"], HEAD_SLOT);
        assert_eq!(gauges[0]["props"]["max"], LOG_GAUGE_MAX);

        let binds = of_kind(&card, "bind");
        let slots: Vec<usize> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap() as usize)
            .collect();
        assert_eq!(
            slots,
            vec![HEAD_SLOT, TIP_SLOT],
            "the binds surface the entry count + the chain tip"
        );
    }

    #[test]
    fn the_binds_carry_their_display_fmt_and_the_tip_is_adept() {
        let card = provenance_card_value();
        let binds = of_kind(&card, "bind");
        let bind_at = |slot: usize| {
            binds
                .iter()
                .find(|b| b["props"]["slot"].as_u64() == Some(slot as u64))
                .unwrap()
        };
        // The entry count stays a plain small counter; the chain tip paints short hex.
        assert_eq!(bind_at(HEAD_SLOT)["props"]["fmt"], "raw");
        assert_eq!(bind_at(TIP_SLOT)["props"]["fmt"], "hash");
        // The raw link digest is adept-only (hidden in the simple projection).
        assert_eq!(bind_at(TIP_SLOT)["props"]["adept"], true);
    }

    #[test]
    fn the_integrity_section_carries_the_non_omission_trust_visual() {
        let card = provenance_card_value();
        let sections = of_kind(&card, "section");
        let integrity = sections
            .iter()
            .find(|s| s["props"]["title"] == "Integrity")
            .expect("the integrity section is present");
        let texts = of_kind(integrity, "text");
        assert!(
            texts
                .iter()
                .any(|t| t["props"]["text"] == "all entries · none omitted"),
            "the completeness certificate's 'none omitted' guarantee is the trust visual"
        );
        let pills = of_kind(integrity, "pill");
        assert!(
            pills.iter().any(|p| p["props"]["text"] == "COMPLETE"),
            "the log is marked COMPLETE (whole-log certificate)"
        );
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = provenance_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 2);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the service method vocabulary.
        assert_eq!(turns, vec![METHOD_APPEND, METHOD_VIEW]);
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = provenance_card_json();
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, divider, log section, integrity section, actions section
        assert_eq!(back["children"].as_array().unwrap().len(), 5);
    }
}
