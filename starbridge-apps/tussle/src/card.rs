//! # TUSSLE — the frame surface as a deos-view CARD (a `deos.ui.*` view-tree).
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
//! `deos-view` pulls BOTH the SpiderMonkey (`mozjs`) and the gpui native elephants,
//! so it is a STANDALONE workspace EXCLUDED from the repo-root workspace. A
//! starbridge-app must never depend on it — that would feature-unify the elephants
//! onto the main build. So the app's contribution is the **view-tree JSON** (this
//! module): pure `serde_json`, no elephant. The deos world's renderers consume it;
//! this module owns the card definition and proves it is well-formed.
//!
//! ## The card shape — a live two-figure frame surface
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) built from the rich deos-view
//! vocabulary (`section` / `pill` / `gauge` / `breadcrumb` / `divider` / `icon`),
//! making the simultaneous-move TENSION legible:
//!
//!   - a **status header** — the app name + a `pill` naming the live frame stage as
//!     a WORD (`COMMITTING` / `REVEALING` / `RESOLVED`), and a `breadcrumb` of the
//!     whole joint turn (commit → reveal → resolve) with the current step marked;
//!   - a **"Frame" `section`** surfacing the LIVE cell state: a `gauge` bound to
//!     [`PHASE_SLOT`](crate::PHASE_SLOT) (the frame phase advancing
//!     `COMMIT < REVEAL < RESOLVED`), one **row per figure** carrying that figure's
//!     `committed?` + `revealed?` status as two `pill`s (the simultaneous-move
//!     fog-of-war made visible — both seal, both reveal), and `bind`s on the live
//!     `PHASE_SLOT`, the sealed [`COMMIT_SEAL_SLOT`](crate::COMMIT_SEAL_SLOT)
//!     (the fog-of-war digest), and the resolved-outcome score
//!     ([`slot::SCORE`](crate::slot::SCORE)) — each a fine-grained signal that
//!     re-reads the live value (the SAME witnessed read a native `bind` makes), so
//!     the surface advances when a fired turn commits;
//!   - an **"Actions" `section`** of one `icon`+`button` row per frame verb
//!     (`commit_move` / `reveal_move` / `resolve_frame`), each `button` carrying its
//!     `onClick = { turn, arg }` — the EXACT cap-gated verified turn a click fires
//!     through the [`GatedAffordance`](dregg_app_framework::GatedAffordance) seam.
//!
//! The button `turn` names ARE the figure-cell verb vocabulary
//! ([`METHOD_COMMIT`](crate::METHOD_COMMIT), …) — the SAME symbols
//! [`figure_cell`](crate::tussle_app) binds its affordances to, so the card and the
//! figure cell speak the same frame.

use serde_json::{Value, json};

use crate::{
    COMMIT, COMMIT_SEAL_SLOT, METHOD_COMMIT, METHOD_RESOLVE, METHOD_REVEAL, PHASE_SLOT, RESOLVED,
    REVEAL, slot,
};

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A `deos.ui.pill` node — a colored status badge.
fn pill(label: &str, tag: &str) -> Value {
    json!({ "kind": "pill", "props": { "text": label, "tag": tag } })
}

/// A LIVE `deos.ui.pill` node — reads `slot` immediate-mode and maps the value to a word +
/// color via `cases` (the first `{value,label,tag}` matching the slot wins). `text`/`tag`
/// are the static fallback (discord, or no match).
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
/// display `fmt` (`"id"` avatar-handle / `"hash"` short-hex / `"amount"` grouped / `"raw"`
/// plain) so an opaque digest/score paints short + friendly.
fn bind(slot: usize, label: &str, fmt: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt } })
}

/// An `adept`-tagged `bind` — the dev-y "see the bones" detail (here the raw `Commit/Reveal/
/// Resolved` phase integer) the `simple` projection hides and `adept` reveals. The live pill
/// + the breadcrumb already name the stage as a word, so the raw integer is adept-only.
fn bind_adept(slot: usize, label: &str, fmt: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt, "adept": true } })
}

/// A `deos.ui.gauge` node — a bound progress bar (`slot_value / max`, immediate-mode).
/// `adept` hides the raw numeric in the simple projection (the live pill + breadcrumb already
/// show the stage); revealed in the adept "see the bones" view.
fn gauge(slot: usize, max: u64, label: &str, adept: bool) -> Value {
    json!({ "kind": "gauge", "props": { "slot": slot, "max": max, "label": label, "adept": adept } })
}

/// A `deos.ui.breadcrumb` node — the joint-turn path; the `active` step is marked `›`.
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

/// An action row — an `icon` + a frame-verb `button` (the verified-turn affordance).
fn action(glyph: &str, label: &str, turn: &str) -> Value {
    row(vec![icon(glyph, "accent"), button(label, turn, 0)])
}

/// One figure's live frame status — a row of `icon` + name + a `committed?` pill + a
/// `revealed?` pill. This is the simultaneous-move TENSION made legible: a figure
/// first SEALS (committed, fog-of-war), then OPENS (revealed); until both have
/// revealed the rival's pose is sealed. `committed`/`revealed` color the two pills
/// (`good` = done, `muted` = still sealed / awaiting).
fn figure_row(glyph: &str, name: &str, committed: bool, revealed: bool) -> Value {
    let commit_pill = if committed {
        pill("committed", "good")
    } else {
        pill("awaiting", "muted")
    };
    let reveal_pill = if revealed {
        pill("revealed", "good")
    } else {
        pill("sealed", "muted")
    };
    row(vec![
        icon(glyph, "accent"),
        text(name),
        commit_pill,
        reveal_pill,
    ])
}

/// **The TUSSLE frame card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A live two-figure frame surface: a status header (name + `REVEALING` pill +
/// commit→reveal→resolve breadcrumb), a "Frame" section surfacing the live phase
/// gauge, a row per figure with its `committed?`/`revealed?` pills (the
/// simultaneous-move tension), and the live phase / sealed-commit / resolved-outcome
/// binds, and an "Actions" section of the three icon-labelled frame-verb buttons.
/// Renderer-independent DATA. The button `turn` names are the figure-cell verb
/// symbols ([`METHOD_COMMIT`](crate::METHOD_COMMIT), …).
///
/// The snapshot's representative stage is `REVEALING`: both figures have committed,
/// one has revealed and one is still sealed — the moment the fog-of-war is half
/// lifted, which makes the two-player tension visible. The live `bind`s/`gauge`
/// re-read the real slots, so a fired turn advances the surface.
pub fn tussle_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            row(vec![text("Tussle"), pill_live(PHASE_SLOT, "REVEALING", "accent", json!([
                { "value": COMMIT,   "label": "COMMITTING", "tag": "warn" },
                { "value": REVEAL,   "label": "REVEALING",  "tag": "accent" },
                { "value": RESOLVED, "label": "RESOLVED",   "tag": "good" },
            ]))]),
            breadcrumb(&["Commit", "Reveal", "Resolve"], 1),
            divider(),
            section("Frame", "genuine", vec![
                gauge(PHASE_SLOT, RESOLVED, "frame phase ", true),
                figure_row("●", "You",   true, true),
                figure_row("○", "Rival", true, false),
                bind_adept(PHASE_SLOT, "phase · ", "raw"),
                bind(COMMIT_SEAL_SLOT, "your seal · ", "hash"),
                bind(slot::SCORE, "outcome · ", "amount"),
            ]),
            section("Actions", "", vec![
                action("◈", "Commit",  METHOD_COMMIT),
                action("◇", "Reveal",  METHOD_REVEAL),
                action("✦", "Resolve", METHOD_RESOLVE),
            ]),
        ]
    })
}

/// **The TUSSLE frame card as serialized `deos.ui.*` JSON** — byte-for-byte the
/// `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn tussle_card_json() -> String {
    serde_json::to_string(&tussle_card_value()).expect("the tussle card serializes")
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
    fn the_card_is_a_vstack_with_a_named_header_and_a_status_pill() {
        let card = tussle_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts.iter().any(|t| t["props"]["text"] == "Tussle"),
            "the header names the app"
        );
        // The header status pill is LIVE: it reads PHASE_SLOT and maps the value to a WORD.
        let header_pill = &card["children"][0]["children"][1];
        assert_eq!(header_pill["kind"], "pill");
        let stage = header_pill["props"]["text"].as_str().unwrap();
        assert!(
            matches!(stage, "COMMITTING" | "REVEALING" | "RESOLVED"),
            "the static-fallback word names a frame stage, got {stage:?}"
        );
        assert_eq!(header_pill["props"]["slot"], PHASE_SLOT);
        let cases = header_pill["props"]["cases"].as_array().unwrap();
        assert_eq!(cases.len(), 3, "COMMITTING / REVEALING / RESOLVED");
        assert_eq!(cases[0]["value"], COMMIT);
        assert_eq!(cases[0]["label"], "COMMITTING");
        assert_eq!(cases[2]["value"], RESOLVED);
        assert_eq!(cases[2]["label"], "RESOLVED");
    }

    #[test]
    fn the_joint_turn_breadcrumb_marks_the_current_step() {
        let card = tussle_card_value();
        let crumbs = of_kind(&card, "breadcrumb");
        assert_eq!(crumbs.len(), 1);
        let items = crumbs[0]["props"]["items"].as_array().unwrap();
        assert_eq!(items.len(), 3, "commit → reveal → resolve");
        assert_eq!(items[0]["label"], "Commit");
        assert_eq!(items[1]["label"], "› Reveal", "the active step is marked");
        assert_eq!(items[2]["label"], "Resolve");
    }

    #[test]
    fn the_frame_section_shows_both_figures_commit_and_reveal_status() {
        let card = tussle_card_value();
        let sections = of_kind(&card, "section");
        let frame = sections
            .iter()
            .find(|s| s["props"]["title"] == "Frame")
            .expect("a Frame section");

        // Both figures named (the two-player tension).
        let texts = of_kind(frame, "text");
        let names: Vec<&str> = texts
            .iter()
            .map(|t| t["props"]["text"].as_str().unwrap())
            .collect();
        assert!(names.contains(&"You") && names.contains(&"Rival"));

        // Each figure row carries a committed? pill + a revealed? pill — 4 status
        // pills total (2 per figure), the simultaneous-move fog-of-war made legible.
        let pills = of_kind(frame, "pill");
        assert_eq!(pills.len(), 4, "two status pills per figure");
        let labels: Vec<&str> = pills
            .iter()
            .map(|p| p["props"]["text"].as_str().unwrap())
            .collect();
        // You committed + revealed; Rival committed but still sealed (the half-lifted fog).
        assert_eq!(labels, vec!["committed", "revealed", "committed", "sealed"]);
    }

    #[test]
    fn the_phase_gauge_and_binds_read_the_live_slots() {
        let card = tussle_card_value();
        let gauges = of_kind(&card, "gauge");
        assert_eq!(gauges.len(), 1, "the frame-phase gauge");
        assert_eq!(gauges[0]["props"]["slot"], PHASE_SLOT);
        assert_eq!(gauges[0]["props"]["max"], RESOLVED);

        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                PHASE_SLOT as u64,
                COMMIT_SEAL_SLOT as u64,
                slot::SCORE as u64,
            ],
            "the binds surface phase / sealed-commit / resolved-outcome"
        );

        // The delight `fmt` per bind: the raw phase integer stays plain (+ adept-hidden), the
        // seal paints short hex, the score groups its digits.
        let fmt = |slot: usize| -> String {
            binds
                .iter()
                .find(|b| b["props"]["slot"].as_u64() == Some(slot as u64))
                .and_then(|b| b["props"]["fmt"].as_str())
                .unwrap()
                .to_string()
        };
        assert_eq!(fmt(PHASE_SLOT), "raw", "the raw phase integer stays plain");
        assert_eq!(fmt(COMMIT_SEAL_SLOT), "hash", "the seal paints short hex");
        assert_eq!(fmt(slot::SCORE), "amount", "the outcome groups digits");

        // The raw phase integer is adept-only (the live pill + breadcrumb already name it).
        let phase_bind = binds
            .iter()
            .find(|b| b["props"]["slot"].as_u64() == Some(PHASE_SLOT as u64))
            .unwrap();
        assert_eq!(phase_bind["props"]["adept"], true);
        // The phase gauge is likewise adept-only.
        assert_eq!(gauges[0]["props"]["adept"], true);
    }

    #[test]
    fn every_button_carries_its_frame_verb_as_the_turn_payload() {
        let card = tussle_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 3);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the figure-cell verb vocabulary (the SAME
        // symbols `figure_cell` binds its gated affordances to).
        assert_eq!(turns, vec![METHOD_COMMIT, METHOD_REVEAL, METHOD_RESOLVE]);
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = tussle_card_json();
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, breadcrumb, divider, frame section, actions section
        assert_eq!(back["children"].as_array().unwrap().len(), 5);
    }
}
