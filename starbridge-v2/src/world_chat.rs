//! **The chat IS the dregg world** — a [`ChatSource`] whose transport is the REAL
//! embedded executor, with NO mock anywhere.
//!
//! A room is a real [`dregg_cell::Cell`]; each message is stored in a real
//! per-room "slot" cell (pre-installed at genesis); a sent message is a REAL
//! verified turn ([`World::commit_turn`]) that writes the body into the next slot
//! cell's state fields; the timeline is read back from genuine cell state by
//! walking the room's slot cells in order. Sending runs the SAME conservation /
//! ocap / program gates every transition runs through and produces a real
//! [`TurnReceipt`] — there is no recorded sync and no synthetic table.
//!
//! Text codec (real, reversible): a slot cell packs `field[0]` = a header
//! (`written`(1) ‖ `len`(8) ‖ a 16-byte sender tag) and `field[1..16]` = the UTF-8
//! body, 32 bytes per slot (up to `15 * 32 = 480` bytes — ample for chat). The
//! timeline reconstructs the exact body from those bytes. The room holds a fixed
//! ring of `SLOTS_PER_ROOM` slot cells; the `written` byte distinguishes a posted
//! slot from an empty one.
//!
//! This is the in-process / nested realization of "the chat is the dregg world":
//! no homeserver, no recorded sync — rooms and messages ARE cells in the live
//! executor, and the membrane operations ([`crate::comms_pd_source`]) snapshot the
//! SAME world. A live `MatrixHandle` remains the OTHER real transport (federated);
//! this is the local-sovereign one.

use std::sync::Mutex;

use deos_matrix::client::{EventState, MessageKind, RoomSummary, TimelineMessage};
use deos_matrix::source::ChatSource;
use deos_matrix::Result;

use dregg_cell::{CellId, FieldElement};

use crate::world::{make_open_cell, set_field, World};

const BODY_SLOTS: usize = 15; // field[1..16]
const MAX_BODY: usize = BODY_SLOTS * 32;
/// The per-room message ring capacity (pre-installed slot cells).
const SLOTS_PER_ROOM: usize = 64;

/// A real room: a cell id + its ring of pre-installed slot cells + metadata.
struct Room {
    cell: CellId,
    slots: Vec<CellId>,
    matrix_id: String,
    name: String,
    topic: String,
}

/// The world-backed chat source: the executor IS the chat. Holds the live world,
/// the room cells (+ their slot rings), and the acting principal (the local user).
pub struct WorldChatSource {
    world: Mutex<World>,
    rooms: Vec<Room>,
    /// The local user's principal cell (the author of sent messages).
    me_cell: CellId,
    /// The local user's display id (`@user:server`).
    me: String,
    /// Per-room next-slot cursor (the order tooth).
    next_slot: Mutex<Vec<usize>>,
    /// Sender tag → display id, so the timeline renders the author from the
    /// on-cell tag (a reverse lookup of the derived tag, not a second truth).
    senders: Mutex<std::collections::HashMap<[u8; 16], String>>,
}

/// Derive a stable 16-byte sender tag from a user id (the on-cell author marker).
fn sender_tag(user_id: &str) -> [u8; 16] {
    let h = blake3::hash(user_id.as_bytes());
    let mut t = [0u8; 16];
    t.copy_from_slice(&h.as_bytes()[..16]);
    t
}

impl WorldChatSource {
    /// Build the world-backed chat: install real room cells + a ring of slot cells
    /// per room + the local user's principal into a fresh executor world, seeded
    /// with a few rooms so the UI opens onto a populated sidebar. Every room and
    /// every message slot here is a genuine cell — all installed at genesis (before
    /// any turn), so a later post is a pure `SetField` turn (no genesis-after-turn).
    pub fn seeded(me: &str) -> Self {
        use dregg_cell::AuthRequired;
        let mut world = World::new().with_executor_signing_key([0x42u8; 32]);

        let seed_rooms = [
            (
                "!deoslab:deos.local",
                "deos-lab",
                "the dregg-pilled workshop",
            ),
            (
                "!membrane:deos.local",
                "membrane",
                "screenshot a moment, hand it over",
            ),
            (
                "!firmament:deos.local",
                "firmament",
                "one cap across distance",
            ),
        ];
        // Build the room + slot cells FIRST (at genesis), collecting their ids, so
        // the local user can be installed holding caps to every cell it will write —
        // a post is then a real `SetField` turn the executor's ocap gate ADMITS
        // (`me_cell` legitimately holds the slot cap), not refuses.
        let mut rooms = Vec::new();
        for (i, (mid, name, topic)) in seed_rooms.iter().enumerate() {
            let room = world.genesis_cell(0x10 + i as u8, 0);
            let mut slots = Vec::with_capacity(SLOTS_PER_ROOM);
            for k in 0..SLOTS_PER_ROOM {
                // A unique slot cell per (room ‖ slot): a distinct pk so the id (which
                // `Cell::with_balance` derives from pk ‖ token_id) is distinct.
                let mut pk = [0u8; 32];
                pk[0] = 0x80 ^ (i as u8);
                pk[1] = (k & 0xff) as u8;
                pk[2] = (k >> 8) as u8;
                pk[31] = (i as u8).wrapping_mul(37).wrapping_add(k as u8);
                let mut slot = dregg_cell::Cell::with_balance(pk, [0u8; 32], 0);
                slot.permissions = crate::world::open_permissions();
                let id = world.genesis_install(slot);
                slots.push(id);
            }
            rooms.push(Room {
                cell: room,
                slots,
                matrix_id: mid.to_string(),
                name: name.to_string(),
                topic: topic.to_string(),
            });
        }

        // The local user's principal cell, installed LAST holding caps to every room
        // + slot cell (so its post turns are authorized). Built as an open cell with
        // the caps grafted before genesis-install (no genesis-after-turn).
        let mut me_open = make_open_cell(0xE0, 0);
        for r in &rooms {
            me_open.capabilities.grant(r.cell, AuthRequired::None);
            for slot in &r.slots {
                me_open.capabilities.grant(*slot, AuthRequired::None);
            }
        }
        let me_cell = world.genesis_install(me_open);

        let mut senders = std::collections::HashMap::new();
        senders.insert(sender_tag(me), me.to_string());
        WorldChatSource {
            world: Mutex::new(world),
            rooms,
            me_cell,
            me: me.to_string(),
            next_slot: Mutex::new(vec![0; seed_rooms.len()]),
            senders: Mutex::new(senders),
        }
    }

    /// The local user's principal cell (for the comms-PD membrane focus).
    pub fn me_cell(&self) -> CellId {
        self.me_cell
    }

    /// A real fork of the live chat world — the comms-PD membrane source snapshots
    /// THIS, so the membrane is a frustum of the SAME chat world.
    pub fn fork_world(&self) -> World {
        self.world.lock().unwrap().fork()
    }

    fn room_index(&self, room_id: &str) -> Option<usize> {
        self.rooms.iter().position(|r| r.matrix_id == room_id)
    }

    /// Pack a header field: `written`(1) ‖ `len`(8, at [1..9]) ‖ `sender_tag`(16, at [9..25]).
    fn header(len: usize, tag: [u8; 16]) -> FieldElement {
        let mut f = [0u8; 32];
        f[0] = 1; // written marker
        f[1..9].copy_from_slice(&(len as u64).to_le_bytes());
        f[9..25].copy_from_slice(&tag);
        f
    }

    /// Decode a slot cell's fields into `(sender_id, body)` if it is written.
    fn decode_slot(&self, fields: &[FieldElement]) -> Option<(String, String)> {
        let hdr = fields.first()?;
        if hdr[0] != 1 {
            return None; // empty slot
        }
        let len = u64::from_le_bytes(hdr[1..9].try_into().ok()?) as usize;
        if len > MAX_BODY {
            return None;
        }
        let mut tag = [0u8; 16];
        tag.copy_from_slice(&hdr[9..25]);
        let sender = self
            .senders
            .lock()
            .unwrap()
            .get(&tag)
            .cloned()
            .unwrap_or_else(|| "@unknown:deos.local".to_string());
        let mut bytes = Vec::with_capacity(len);
        for slot in fields.iter().skip(1) {
            if bytes.len() >= len {
                break;
            }
            let take = (len - bytes.len()).min(32);
            bytes.extend_from_slice(&slot[..take]);
        }
        let body = String::from_utf8(bytes).ok()?;
        Some((sender, body))
    }
}

impl ChatSource for WorldChatSource {
    fn whoami(&self) -> Option<String> {
        Some(self.me.clone())
    }

    fn rooms(&self) -> Result<Vec<RoomSummary>> {
        let mut out = Vec::new();
        for r in &self.rooms {
            let Ok(rid) = deos_matrix::source::parse_room_id(&r.matrix_id) else {
                continue;
            };
            out.push(RoomSummary {
                room_id: rid,
                display_name: r.name.clone(),
                topic: Some(r.topic.clone()),
                is_encrypted: false,
                is_space: false,
                is_direct: false,
                joined_members: 1,
                unread_notifications: 0,
            });
        }
        Ok(out)
    }

    fn timeline(&self, room_id: &str, limit: u16) -> Result<Vec<TimelineMessage>> {
        let world = self.world.lock().unwrap();
        let Some(ri) = self.room_index(room_id) else {
            return Ok(Vec::new());
        };
        let room = &self.rooms[ri];
        let mut out: Vec<TimelineMessage> = Vec::new();
        // Walk the slot ring IN ORDER — the timeline is exactly the written slots,
        // read back from REAL cell state (not a recorded script).
        for (k, slot_id) in room.slots.iter().enumerate() {
            let Some(cell) = world.ledger().get(slot_id) else {
                continue;
            };
            let Some((sender, body)) = self.decode_slot(&cell.state.fields) else {
                continue;
            };
            // A sensible monotone display time: a fixed base + one minute per slot,
            // so the chrome's day/time labels read normally (order is the real slot
            // index; the absolute value is cosmetic).
            const BASE_MS: u64 = 1_750_000_000_000; // ~2025-06
            out.push(TimelineMessage {
                event_id: crate::reflect::short_hex(slot_id.as_bytes()),
                sender,
                body,
                timestamp_ms: BASE_MS + (k as u64) * 60_000,
                kind: MessageKind::Text,
                state: EventState::Live,
                reactions: Vec::new(),
                reply_to: None,
                thread_root: None,
                membrane: None,
                object: None,
            });
        }
        if out.len() > limit as usize {
            let drop = out.len() - limit as usize;
            out.drain(0..drop);
        }
        Ok(out)
    }

    fn send(&self, room_id: &str, body: &str) -> Result<String> {
        let mut world = self.world.lock().unwrap();
        let Some(ri) = self.room_index(room_id) else {
            return Err(deos_matrix::Error::Other(format!(
                "no such room: {room_id}"
            )));
        };
        let body_bytes = body.as_bytes();
        if body_bytes.len() > MAX_BODY {
            return Err(deos_matrix::Error::Other(format!(
                "message too long for one cell ({} > {MAX_BODY} bytes)",
                body_bytes.len()
            )));
        }
        // The next slot in the room's ring (the order tooth).
        let k = {
            let mut cur = self.next_slot.lock().unwrap();
            let k = cur[ri];
            if k >= SLOTS_PER_ROOM {
                return Err(deos_matrix::Error::Other(
                    "this room's message ring is full (demo capacity)".into(),
                ));
            }
            cur[ri] = k + 1;
            k
        };
        let slot_id = self.rooms[ri].slots[k];
        let tag = sender_tag(&self.me);

        // Write the header + body into the slot cell via a REAL verified turn — the
        // SAME executor gates every transition runs through.
        let mut effects = Vec::with_capacity(1 + BODY_SLOTS);
        effects.push(set_field(slot_id, 0, Self::header(body_bytes.len(), tag)));
        for (i, chunk) in body_bytes.chunks(32).enumerate() {
            let mut f = [0u8; 32];
            f[..chunk.len()].copy_from_slice(chunk);
            effects.push(set_field(slot_id, 1 + i, f));
        }
        let turn = world.turn(self.me_cell, effects);
        let outcome = world.commit_turn(turn);
        if !outcome.is_committed() {
            return Err(deos_matrix::Error::Other(format!(
                "the post turn was refused by the executor (fail-closed): {outcome:?}"
            )));
        }
        Ok(crate::reflect::short_hex(slot_id.as_bytes()))
    }

    /// **The room cell, folded from the REAL world** — the default trait impl
    /// returns a zeroed sketch (`turn_count: 0`), which would freeze the mounted
    /// chat card's watermark/bind at 0 forever. Here the projection is honest:
    /// `turn_count` = the written slots in the room's real ring (each posted by
    /// ONE verified turn), `state_root` = the live world's actual state root —
    /// so a `send_turn`'s [`deos_matrix::SendReceipt::turn_index`] genuinely
    /// advances and the card's audit-tape pulse sees foreign posts too.
    fn room_cell(&self, room_id: &str) -> deos_matrix::RoomCell {
        let mut rc = deos_matrix::RoomCell::for_room(room_id);
        let Some(ri) = self.room_index(room_id) else {
            return rc;
        };
        let world = self.world.lock().unwrap();
        let mut written = 0u64;
        for slot_id in &self.rooms[ri].slots {
            let posted = world
                .ledger()
                .get(slot_id)
                .and_then(|c| c.state.fields.first().map(|hdr| hdr[0] == 1))
                .unwrap_or(false);
            if posted {
                written += 1;
            }
        }
        rc.turn_count = written;
        rc.state_root = world.state_root();
        rc
    }

    fn backend_label(&self) -> &'static str {
        "dregg-world (the chat IS the world)"
    }
}

/// **Open the CHAT CARD over the world-backed embedded source** — the gpui-free
/// construction the cockpit's "Open Chat Card" palette command mounts (via
/// `dock::card_surface::build_chat_card_surface`): a fresh seeded
/// [`WorldChatSource`] (rooms are real cells, a send is a real verified turn —
/// no homeserver) with a [`deos_matrix::chat_card::ChatCard`] opened on its
/// first room. Named seam: the Matrix-BACKED variant (a live `MatrixHandle`
/// over homeserver creds) is the federated alternative source — same
/// `ChatSource` surface, swapped at this constructor.
pub fn world_chat_card(me: &str) -> std::result::Result<deos_matrix::chat_card::ChatCard, String> {
    use std::sync::Arc;
    let source = WorldChatSource::seeded(me);
    let rooms = source
        .rooms()
        .map_err(|e| format!("world-chat rooms: {e}"))?;
    let first = rooms
        .first()
        .ok_or_else(|| "the world-chat source seeded no rooms".to_string())?;
    let room_id = first.room_id.to_string();
    let src: Arc<dyn ChatSource> = Arc::new(source);
    Ok(deos_matrix::chat_card::ChatCard::open(src, room_id))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_chat_is_the_world_send_is_a_real_turn_timeline_is_real_cell_state() {
        let chat = WorldChatSource::seeded("@ember:deos.local");
        let rooms = chat.rooms().expect("real room cells");
        assert!(!rooms.is_empty(), "the world has seeded room cells");
        let room_id = rooms[0].room_id.to_string();

        // Empty room: no messages yet (real cell state, not a recorded script).
        assert!(
            chat.timeline(&room_id, 80).unwrap().is_empty(),
            "a fresh room has no messages"
        );

        // SEND = a real verified turn. The returned id is the real slot cell.
        let body = "hello from a real turn — the chat is the dregg world ✦";
        let id = chat.send(&room_id, body).expect("send commits a real turn");
        assert!(!id.is_empty(), "the send returns the real slot cell id");

        // TIMELINE = read back from REAL cell state.
        let tl = chat
            .timeline(&room_id, 80)
            .expect("timeline off real cells");
        assert_eq!(tl.len(), 1, "the posted message is in the timeline");
        assert_eq!(
            tl[0].body, body,
            "the body round-trips through real cell fields"
        );
        assert_eq!(
            tl[0].sender, "@ember:deos.local",
            "the sender is decoded from the on-cell tag"
        );
        assert_eq!(tl[0].kind, MessageKind::Text);

        // A second message orders after the first (the real slot-ring tooth).
        let id2 = chat
            .send(&room_id, "and a second, ordered after")
            .expect("second send");
        assert_ne!(id, id2, "distinct messages are distinct cells");
        let tl2 = chat.timeline(&room_id, 80).unwrap();
        assert_eq!(tl2.len(), 2, "both messages present");
        assert_eq!(
            tl2[0].body, body,
            "first stays first (ordered by real slot index)"
        );
        assert!(tl2[1].body.contains("second"), "second follows");

        // No cross-room leak — each room has its own slot ring (real cells).
        let other = rooms[1].room_id.to_string();
        chat.send(&other, "in another room").unwrap();
        assert_eq!(
            chat.timeline(&room_id, 80).unwrap().len(),
            2,
            "no cross-room leak"
        );
        assert_eq!(
            chat.timeline(&other, 80).unwrap().len(),
            1,
            "the other room has its own message"
        );
    }

    /// The chat-card OPENER the cockpit mounts: `world_chat_card` yields a live
    /// [`deos_matrix::chat_card::ChatCard`] over the embedded world-chat source —
    /// opened on a real room cell, sending ONE real verified turn (the receipt's
    /// turn index advances the room cell), the timeline read back from real cell
    /// state. This is the gpui-free core of the "Open Chat Card" palette wire.
    #[test]
    fn the_chat_card_opens_over_the_embedded_world_source() {
        let chat = world_chat_card("@ember:deos.local").expect("the card opens");
        assert_eq!(
            chat.backend_label(),
            "dregg-world (the chat IS the world)",
            "the card rides the world-backed source (no homeserver)"
        );
        assert!(
            !chat.room_id().is_empty(),
            "the card opened on the first seeded room"
        );
        let turns_before = chat.room().turn_count;
        assert!(
            chat.timeline().expect("timeline reads").is_empty(),
            "a fresh room has no messages"
        );

        // A send through the CARD is one real verified turn on the room cell.
        let receipt = chat
            .send("hello through the mounted chat card")
            .expect("the send commits a real turn");
        assert_eq!(
            receipt.turn_index,
            turns_before + 1,
            "the room cell advanced by exactly one turn"
        );
        let tl = chat.timeline().expect("timeline reads back");
        assert_eq!(tl.len(), 1, "the sent message is in the live timeline");
        assert!(
            tl[0].body.contains("mounted chat card"),
            "the body round-trips through real cell fields"
        );
    }

    #[test]
    fn the_chat_world_is_forkable_for_a_membrane_snapshot() {
        // The comms-PD membrane source snapshots a FORK of THIS chat world — so the
        // membrane is a frustum of the real chat, not a separate toy world.
        let chat = WorldChatSource::seeded("@ember:deos.local");
        let rooms = chat.rooms().unwrap();
        chat.send(rooms[0].room_id.as_ref(), "a message to snapshot")
            .unwrap();
        let fork = chat.fork_world();
        assert!(
            fork.ledger().get(&chat.me_cell()).is_some(),
            "the fork carries the chat world's cells"
        );
    }
}
