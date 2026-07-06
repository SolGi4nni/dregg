//! **The chat card's VIEW-TREE projection** — [`ChatCard`] as a renderer-independent
//! `deos.ui.*` element-tree, so the chat paints in every `deos-view` renderer (native
//! gpui / web HTML / discord embed / the seL4 image viewer) from ONE piece of DATA.
//!
//! [`ChatCard`] (`chat_card.rs`) is the gpui-free logic core: room = a cell, timeline =
//! the cell's turn history read back, send = a real verified turn. THIS module is the
//! "later layer" its header promises — the *projection* of that core into the
//! serializable `{kind, props, children}` JSON shape `deos_view::parse_view_tree`
//! consumes:
//!
//!   - a **header row** — the room id, the backend pill (`mock` / `matrix` /
//!     `firmament-comms-pd`), and the room cell's honest turn count;
//!   - a **live `bind`** on slot 0 — the mount's substance answers it with the room
//!     cell's live `turn_count`, so the one bound scalar advances when a turn commits;
//!   - a **timeline `section`** — a `list` of one `row` per [`ChatLine`] (sender +
//!     body), folded from the room cell's durable history, oldest-first. An empty room
//!     renders an honest empty-state line (never fabricated chatter), and a timeline
//!     read error surfaces as a `bad` pill + the error text (fail-honest, not blank);
//!   - a **composer `input`** bound to the ephemeral draft key [`CHAT_DRAFT_KEY`],
//!     whose submit fires [`CHAT_SEND_TURN`] — the action id the cockpit mount routes
//!     to the REAL [`crate::source::ChatSource::send_turn`] (the send↔turn weldpoint).
//!
//! ## Why pure `serde_json`, not a `deos-view` type dep
//!
//! This is the established card pattern for crates outside the deos-js graph (see
//! `starbridge-apps/gallery/src/card.rs` and `starbridge-apps/polis` — "a
//! renderer-independent `deos.ui.*` view-tree built as PURE `serde_json`"): the card's
//! contribution is the view-tree JSON; the deos world's renderers consume it. It keeps
//! this crate's wasm32 build untouched (serde_json is already here) and adds no
//! manifest seam. The prop names are the parser's canonical camelCase
//! (`onClick`/`bindView`/`fireTurn`/`submitLabel` — `deos-view/src/tree.rs` `RawProps`).

use serde_json::{json, Value};

use crate::chat_card::{ChatCard, ChatLine};

/// The affordance id the composer `input`'s submit fires — the send action the mount
/// routes to the REAL [`crate::source::ChatSource::send_turn`]. A renderer never
/// interprets it; the card's substance does.
pub const CHAT_SEND_TURN: &str = "chat_send";

/// The ephemeral view-state key the composer `input` binds its draft text to (draft
/// text is NEVER cell state — it becomes a turn only when [`CHAT_SEND_TURN`] fires).
pub const CHAT_DRAFT_KEY: &str = "chat_draft";

/// The model slot the header's live `bind` reads — the mount's substance answers it
/// with the room cell's live `turn_count` (the one bound scalar of the chat card).
pub const CHAT_TURNS_SLOT: usize = 0;

/// A `deos.ui.text` node.
fn text(s: impl Into<String>) -> Value {
    json!({ "kind": "text", "props": { "text": s.into() } })
}

/// A `deos.ui.pill` node — a colored status badge (`tag` selects the semantic palette).
fn pill(s: impl Into<String>, tag: &str) -> Value {
    json!({ "kind": "pill", "props": { "text": s.into(), "tag": tag } })
}

/// A `deos.ui.row` node — a horizontal flex of children.
fn row(children: Vec<Value>) -> Value {
    json!({ "kind": "row", "props": {}, "children": children })
}

/// A `deos.ui.list` node — a vertical list of the child nodes.
fn list(children: Vec<Value>) -> Value {
    json!({ "kind": "list", "props": {}, "children": children })
}

/// A `deos.ui.section` node — a titled, bordered container.
fn section(title: &str, tag: &str, children: Vec<Value>) -> Value {
    json!({ "kind": "section", "props": { "title": title, "tag": tag }, "children": children })
}

/// A `deos.ui.bind` node — a live binding the renderer re-reads off the card's
/// substance (slot + label prefix; `fmt: "raw"` keeps the plain decimal).
fn bind(slot: usize, label: &str) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": "raw" } })
}

/// The composer `deos.ui.input` node: its draft lives in ephemeral view-state
/// (`bindView`) and its submit fires the send affordance (`fireTurn`) — the shape
/// `deos-view` renders as an editable field + a paired submit button on web, and as a
/// display/agent-driven field on native (the renderer's honest parity boundary).
fn send_input() -> Value {
    json!({
        "kind": "input",
        "props": {
            "bindView": CHAT_DRAFT_KEY,
            "fireTurn": CHAT_SEND_TURN,
            "submitLabel": "send",
        }
    })
}

/// One timeline line as a card row: who said it + what they said, both real reads off
/// the room cell's durable history (never fabricated).
fn line_row(l: &ChatLine) -> Value {
    row(vec![text(format!("{} ·", l.sender)), text(l.body.clone())])
}

/// **The chat card as a `deos.ui.*` view-tree** (a `serde_json::Value`) — the
/// renderer-independent projection of `card`'s live state. Hand it to any `deos-view`
/// renderer (native / web / discord / the seL4 viewer) to paint the SAME card; mount it
/// over a substance that routes [`CHAT_SEND_TURN`] to [`ChatCard::send`] and the
/// composer becomes a real verified turn.
pub fn chat_view(card: &ChatCard) -> Value {
    let room = card.room();

    // The header: which room cell, on which backend, holding how many turns — plus the
    // live bound turn count (slot 0, answered by the mount's substance).
    let header = row(vec![
        text(format!("💬 {}", room.room_id)),
        pill(card.backend_label(), "accent"),
        pill(format!("{} turn(s)", room.turn_count), "muted"),
    ]);
    let live_turns = bind(CHAT_TURNS_SLOT, "turns · ");

    // The timeline: the room cell's history read back — or the honest empty/error state.
    let timeline = match card.timeline() {
        Ok(lines) if lines.is_empty() => section(
            "timeline",
            "",
            vec![text(
                "(no messages yet — this room cell holds no turns; the first send starts its history)",
            )],
        ),
        Ok(lines) => section(
            "timeline",
            "genuine",
            vec![list(lines.iter().map(line_row).collect())],
        ),
        Err(e) => section(
            "timeline",
            "",
            vec![
                pill("timeline unavailable", "bad"),
                text(format!("({e})")),
            ],
        ),
    };

    // The composer: draft in ephemeral view-state; submit = the send affordance the
    // mount routes to the REAL send_turn.
    let composer = section("send (a verified turn)", "", vec![send_input()]);

    json!({
        "kind": "vstack",
        "props": {},
        "children": [header, live_turns, timeline, composer],
    })
}

/// **The chat card as serialized `deos.ui.*` JSON** — byte-for-byte the shape a
/// `deos-view` renderer parses (via `deos_view::parse_view_tree`). This is the string a
/// mount bridges / a host serves.
pub fn chat_view_json(card: &ChatCard) -> String {
    serde_json::to_string(&chat_view(card)).expect("the chat card serializes")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chat_card::ChatCard;
    use crate::source::{ChatSource, MockSource};
    use std::sync::Arc;

    /// Recursively collect every node of `kind` in the tree (the card nests rows in
    /// section/list containers, so the invariants walk the whole tree).
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

    fn seeded_card() -> ChatCard {
        let src: Arc<dyn ChatSource> = Arc::new(MockSource::seeded());
        let room_id = src.rooms().unwrap()[0].room_id.to_string();
        ChatCard::open(src, room_id)
    }

    /// The timeline projects one row per message in the room cell's real history —
    /// sender + body both present — and a fresh send appears on the re-projection
    /// (the view is a pure function of the live card).
    #[test]
    fn timeline_renders_a_row_per_message() {
        let card = seeded_card();
        let lines = card.timeline().unwrap();
        assert!(!lines.is_empty(), "the seeded room holds real history");

        let tree = chat_view(&card);
        let lists = of_kind(&tree, "list");
        assert_eq!(lists.len(), 1, "one timeline list");
        let rows = lists[0]["children"].as_array().unwrap();
        assert_eq!(
            rows.len(),
            lines.len(),
            "one row per line of the room cell's history"
        );

        // Every row carries its line's sender AND body, in order (real reads off
        // the room cell's history, not placeholders).
        for (i, l) in lines.iter().enumerate() {
            let cells = rows[i]["children"].as_array().unwrap();
            assert_eq!(cells[0]["props"]["text"], format!("{} ·", l.sender));
            assert_eq!(cells[1]["props"]["text"], l.body.as_str());
        }

        // A real send (a verified turn) shows up when the view is re-projected.
        card.send("a line for the projector").unwrap();
        let re = chat_view(&card);
        assert!(
            re.to_string().contains("a line for the projector"),
            "the re-projection reads the new turn back"
        );
        let re_rows = of_kind(&re, "list")[0]["children"]
            .as_array()
            .unwrap()
            .len();
        assert_eq!(re_rows, rows.len() + 1, "one more row after the send");
    }

    /// The composer input carries the send action binding: its draft key is
    /// [`CHAT_DRAFT_KEY`] and its submit fires [`CHAT_SEND_TURN`] — the id the cockpit
    /// mount routes to the REAL `ChatSource::send_turn`.
    #[test]
    fn send_input_carries_the_action_binding() {
        let tree = chat_view(&seeded_card());
        let inputs = of_kind(&tree, "input");
        assert_eq!(inputs.len(), 1, "one composer input");
        let props = &inputs[0]["props"];
        assert_eq!(props["bindView"], CHAT_DRAFT_KEY);
        assert_eq!(props["fireTurn"], CHAT_SEND_TURN);
        assert_eq!(props["submitLabel"], "send");
    }

    /// An empty room renders the HONEST empty state (no fabricated chatter, zero
    /// message rows) — and still offers the composer (the first send starts the
    /// history).
    #[test]
    fn empty_room_renders_the_honest_empty_state() {
        let src: Arc<dyn ChatSource> = Arc::new(MockSource::seeded());
        // A room the mock world holds no timeline for: an empty room cell (turn 0).
        let card = ChatCard::open(src, "!empty:deos.local");
        assert!(card.timeline().unwrap().is_empty());

        let tree = chat_view(&card);
        assert!(
            of_kind(&tree, "list").is_empty(),
            "no timeline list — nothing to fabricate"
        );
        assert!(
            tree.to_string().contains("no messages yet"),
            "the empty state says so"
        );
        assert_eq!(
            of_kind(&tree, "input").len(),
            1,
            "the composer is still offered (the first send starts the history)"
        );
    }

    /// The header is honest: the room id, the backend label, and the room cell's real
    /// turn count all project — and the live bind reads [`CHAT_TURNS_SLOT`].
    #[test]
    fn header_projects_the_room_cell_honestly() {
        let card = seeded_card();
        let room = card.room();
        let tree = chat_view(&card);
        let json = tree.to_string();
        assert!(json.contains(&room.room_id), "the room id is the title");
        assert!(json.contains("mock"), "the backend pill names the source");
        assert!(
            json.contains(&format!("{} turn(s)", room.turn_count)),
            "the turn-count pill is the cell's real count"
        );
        let binds = of_kind(&tree, "bind");
        assert_eq!(binds.len(), 1, "one live bound scalar");
        assert_eq!(binds[0]["props"]["slot"], CHAT_TURNS_SLOT);
    }

    /// The serialized card is well-formed JSON in the canonical `{kind, props,
    /// children}` shape (the string `deos_view::parse_view_tree` reads).
    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = chat_view_json(&seeded_card());
        let back: Value = serde_json::from_str(&s).expect("the chat card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, live bind, timeline section, composer section
        assert_eq!(back["children"].as_array().unwrap().len(), 4);
    }
}
