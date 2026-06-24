//! [`ChatCard`] — **the chat reborn as a hyperdreggmedia card.**
//!
//! A hyperdreggmedia card is a thing whose *state is a cell* and whose *actions
//! are turns*. `ChatCard` is exactly that for a chat room: the room IS a cell
//! ([`RoomCell`]), the timeline IS that cell's turn history read back, and SEND
//! IS a real verified turn ([`SendReceipt`]) appending the message to the room
//! cell. There is no parallel chat model here — the card is a thin logic core
//! over the SAME [`ChatSource`] machinery the world-chat already proves
//! (`source.rs` + `cell.rs`): `timeline` folds [`ChatSource::timeline`], `send`
//! drives [`ChatSource::send_turn`] (the send↔turn weldpoint), `room`/`rooms`
//! project [`ChatSource::room_cell`] / [`ChatSource::rooms`].
//!
//! ## What makes it a *card* (and not just a chat view)
//!
//! 1. **State = a cell.** [`ChatCard::room`] is a [`RoomCell`] — the durable core
//!    (membership / post-cap / turn history). The card's identity is that cell's
//!    id; its "freshness" is the cell's `turn_count` + `state_root`.
//! 2. **View = the cell's history.** [`ChatCard::timeline`] reads the room cell's
//!    real state back — each [`ChatLine`] is a message (sender + body) folded from
//!    the durable turn history, oldest-first. No fabricated content: it is whatever
//!    the underlying [`ChatSource`] (mock or live comms-PD) holds.
//! 3. **The SEND affordance = a turn.** [`ChatCard::send`] commits a real verified
//!    turn against the room cell via [`ChatSource::send_turn`], returning the
//!    [`SendReceipt`] (turn index + post-root). The card's `room()` then shows the
//!    cell's history grew by one — exactly the receipted advance the world-chat
//!    proves.
//!
//! This is deliberately **gpui-free**: the card is data + turns. Rendering it (a
//! composer widget, a scrolling timeline) is a later layer that holds a `ChatCard`
//! and paints its `timeline()` / drives its `send()`. The card is the seam the
//! renderer binds to, the same discipline as the `ChatSource` trait it stands on.

use std::sync::Arc;

use crate::cell::{RoomCell, SendReceipt};
use crate::client::RoomSummary;
use crate::source::ChatSource;
use crate::Result;

/// How many messages a card reads back from the room cell's history by default
/// (the recent window the timeline shows). Generous so a card's `timeline()`
/// includes everything a seeded/short room holds; a renderer can ask for a
/// narrower window with [`ChatCard::timeline_window`].
const DEFAULT_TIMELINE_WINDOW: u16 = 500;

/// One line of a chat card's timeline — a single message folded from the room
/// cell's durable history: who sent it ([`Self::sender`]) and what they said
/// ([`Self::body`]), with its wire event id + timestamp for stable identity and
/// ordering. This is the minimal "message = a turn read-back" projection; the
/// richer view-state (reactions, replies, membranes) lives on the underlying
/// [`crate::client::TimelineMessage`] and is reachable by a renderer that wants
/// it — the card keeps the *core* card surface small.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChatLine {
    /// The message's wire identity (the event id the send produced).
    pub event_id: String,
    /// The full Matrix user id that authored the line (`@user:server`).
    pub sender: String,
    /// The message body (plain text, or a kind's human fallback).
    pub body: String,
    /// The origin timestamp (ms epoch) — the ordering key (oldest-first).
    pub timestamp_ms: u64,
}

/// **The chat as a hyperdreggmedia card.** A card bound to one room: its state is
/// the room cell, its view is that cell's history, and its SEND affordance is a
/// real verified turn.
///
/// Holds a shared [`ChatSource`] (the real room-cell machinery — `MockSource`
/// offline, the comms-PD source live) and the room id this card is focused on.
/// Cheap to clone (an `Arc` + a `String`); a multi-room cockpit holds one card
/// per open room, or re-[`focus`](ChatCard::focus)es a single card.
pub struct ChatCard {
    source: Arc<dyn ChatSource>,
    room_id: String,
}

impl ChatCard {
    /// Open a chat card over a room. `source` is the SAME [`ChatSource`] the
    /// world-chat drives (the room↔cell, send↔turn machinery); `room_id` is the
    /// Matrix room id (`!room:server`) of the room cell this card presents.
    pub fn open(source: Arc<dyn ChatSource>, room_id: impl Into<String>) -> Self {
        ChatCard {
            source,
            room_id: room_id.into(),
        }
    }

    /// The Matrix room id this card is focused on (`!room:server`).
    pub fn room_id(&self) -> &str {
        &self.room_id
    }

    /// **State = a cell.** The [`RoomCell`] this card IS — the room's durable core
    /// (cell id, turn count == message count, current state root). Reading this
    /// after a [`send`](Self::send) shows the cell's history grew by one. The card's
    /// identity and freshness are exactly this cell.
    pub fn room(&self) -> RoomCell {
        self.source.room_cell(&self.room_id)
    }

    /// **Multi-room.** All rooms the underlying source exposes — each is itself a
    /// candidate card (a [`RoomCell`]). A cockpit lists these and opens / focuses a
    /// card per room. Returns the room summaries (display name, topic, membership);
    /// pair with [`Self::room_of`] for the cell projection.
    pub fn rooms(&self) -> Result<Vec<RoomSummary>> {
        self.source.rooms()
    }

    /// The [`RoomCell`] for an *arbitrary* room id (not necessarily this card's
    /// focus) — used when listing [`rooms`](Self::rooms) to show each room's cell
    /// id / turn count without opening a full card.
    pub fn room_of(&self, room_id: &str) -> RoomCell {
        self.source.room_cell(room_id)
    }

    /// **View = the cell's history.** The room cell's messages read back from its
    /// real state, oldest-first — each a [`ChatLine`] (sender + body). This is the
    /// card's timeline: not a fabricated list, but the durable turn history the
    /// underlying [`ChatSource`] holds, projected to the minimal message surface.
    pub fn timeline(&self) -> Result<Vec<ChatLine>> {
        self.timeline_window(DEFAULT_TIMELINE_WINDOW)
    }

    /// [`timeline`](Self::timeline) with an explicit recent-window size (a renderer
    /// paging a long room asks for the window it can show).
    pub fn timeline_window(&self, limit: u16) -> Result<Vec<ChatLine>> {
        let msgs = self.source.timeline(&self.room_id, limit)?;
        Ok(msgs
            .into_iter()
            .map(|m| ChatLine {
                event_id: m.event_id,
                sender: m.sender,
                body: m.body,
                timestamp_ms: m.timestamp_ms,
            })
            .collect())
    }

    /// **The SEND affordance = a turn.** Send `body` to this room as a real
    /// verified turn appending to the room cell, returning the [`SendReceipt`]
    /// (the turn it committed against the cell: turn index + post-root). This is
    /// the exact `send_turn` path the world-chat proves — the card adds no parallel
    /// send. After it returns, [`room`](Self::room)'s `turn_count` has advanced and
    /// [`timeline`](Self::timeline) reads the new line back.
    pub fn send(&self, body: &str) -> Result<SendReceipt> {
        self.source.send_turn(&self.room_id, body)
    }

    /// Re-focus this card onto a different room (the cockpit "click another room"
    /// gesture) — same source, new room cell. Returns a fresh card; the original is
    /// consumed so a card always names exactly one room.
    pub fn focus(self, room_id: impl Into<String>) -> Self {
        ChatCard {
            source: self.source,
            room_id: room_id.into(),
        }
    }

    /// The backend label of the underlying source ("mock", "matrix",
    /// "firmament-comms-pd") — what a card's chrome shows about where its room cell
    /// lives.
    pub fn backend_label(&self) -> &'static str {
        self.source.backend_label()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::MockSource;

    /// Open a real room cell, send two messages as real verified turns (each a
    /// [`SendReceipt`]), and assert the card reads them back from the room cell's
    /// real state in order with senders, while the cell's history grew. This drives
    /// the SAME `source.rs` / `cell.rs` machinery the world-chat proves — the card
    /// is just the hyperdreggmedia surface over it.
    #[test]
    fn chat_is_a_card_room_is_a_cell_send_is_a_turn() {
        // A real room cell: the first seeded room of the mock world (the same room
        // cell `MockSource` proves has advancing turn history).
        let src: Arc<dyn ChatSource> = Arc::new(MockSource::seeded());
        let room_id = src.rooms().unwrap()[0].room_id.to_string();
        let card = ChatCard::open(src, room_id.clone());

        // State = a cell: the card's room is a RoomCell with real history.
        let cell_before = card.room();
        assert_eq!(cell_before.room_id, room_id, "the card's room IS this cell");
        let turns_before = cell_before.turn_count;
        let root_before = cell_before.state_root;
        assert!(turns_before >= 1, "the seeded room cell already holds turns");

        // View = the cell's history: the timeline reads back oldest-first.
        let tl_before = card.timeline().unwrap();
        assert_eq!(
            tl_before.len() as u64,
            turns_before,
            "timeline length == the room cell's turn count (no fabrication)"
        );
        for w in tl_before.windows(2) {
            assert!(
                w[0].timestamp_ms <= w[1].timestamp_ms,
                "timeline is oldest-first"
            );
        }

        // SEND = a turn: two real verified turns, each leaving a SendReceipt that
        // advances the room cell's history.
        let me = "@ember:deos.local";
        let r1 = card.send("first card turn").unwrap();
        assert_eq!(r1.room_cell, cell_before.cell_id, "turn committed against this room cell");
        // turn_index = the room cell's turn_count AFTER the send (send_turn sends, then
        // reads rc.turn_count — source.rs:92-98), so the first send lands at turns_before + 1.
        assert_eq!(r1.turn_index, turns_before + 1, "first send advanced the room cell to the next turn");

        let r2 = card.send("second card turn").unwrap();
        assert_eq!(r2.turn_index, turns_before + 2, "second send advanced the index again");
        assert_ne!(r2.post_root, r1.post_root, "each turn moved the room cell root");

        // The room cell's history grew by exactly the two receipted turns.
        let cell_after = card.room();
        assert_eq!(
            cell_after.turn_count,
            turns_before + 2,
            "the room cell's history grew by the two turns"
        );
        assert_ne!(cell_after.state_root, root_before, "the room cell root advanced");
        assert_eq!(cell_after.cell_id, cell_before.cell_id, "same room == same cell");

        // View reads them back FROM the room cell's real state, in order, with
        // senders — the timeline IS the cell's history.
        let tl_after = card.timeline().unwrap();
        assert_eq!(tl_after.len(), tl_before.len() + 2, "two new lines in the history");
        let last_two = &tl_after[tl_after.len() - 2..];
        assert_eq!(last_two[0].body, "first card turn");
        assert_eq!(last_two[0].sender, me, "the sender rode the turn into the cell");
        assert_eq!(last_two[0].event_id, r1.event_id, "the line carries the turn's event id");
        assert_eq!(last_two[1].body, "second card turn");
        assert_eq!(last_two[1].sender, me);
        assert_eq!(last_two[1].event_id, r2.event_id);
        assert!(
            last_two[0].timestamp_ms <= last_two[1].timestamp_ms,
            "the two sent turns are themselves in order"
        );
    }

    /// A card is multi-room: `rooms()` lists every room cell, and `focus` re-points
    /// the card at another room cell (same source).
    #[test]
    fn card_is_multi_room_and_refocusable() {
        let src: Arc<dyn ChatSource> = Arc::new(MockSource::seeded());
        let rooms = src.rooms().unwrap();
        assert!(rooms.len() >= 2, "the mock world has several room cells");
        let first = rooms[0].room_id.to_string();
        let second = rooms[1].room_id.to_string();

        let card = ChatCard::open(src, first.clone());
        // Every listed room projects to a room cell.
        let listed = card.rooms().unwrap();
        assert_eq!(listed.len(), rooms.len());
        let second_cell = card.room_of(&second);
        assert_eq!(second_cell.room_id, second);

        // Re-focus moves the card to the other room cell.
        let card = card.focus(second.clone());
        assert_eq!(card.room_id(), second);
        assert_eq!(card.room().room_id, second, "the card now IS the second room cell");
        assert_eq!(card.backend_label(), "mock");
    }
}
