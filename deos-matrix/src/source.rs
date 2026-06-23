//! [`ChatSource`] — the synchronous data seam the deos-chat UI renders against.
//!
//! The gpui UI never touches `matrix-sdk` or tokio directly. It pulls rooms,
//! timelines, and the local user id from a [`ChatSource`], and it sends messages
//! back through the same trait. Two implementors exist:
//!
//!   * [`crate::worker::MatrixHandle`] — the real client (login/sync/timeline over
//!     `matrix-rust-sdk`, on its own tokio runtime). The blocking facade already
//!     matches this shape exactly.
//!   * [`MockSource`] — a recorded/synthetic sync. With no live homeserver creds
//!     the UI is STILL real: a room list, a populated timeline, and a composer
//!     that appends locally. This is what makes the demo render offline.
//!
//! Keeping the UI behind this trait is the same discipline as the editor's `Fs`
//! seam in `deos-zed`: the view depends on a trait, and the backend (real vs
//! mock vs — later — a confined comms-PD) is one impl swap.

use std::sync::Mutex;

use crate::cell::{IdentityCell, PersonTrust, RoomCell, SendReceipt};

/// Parse a Matrix room id (`!room:server`) into the wire [`OwnedRoomId`] a
/// [`RoomSummary`] carries. Re-exported so an out-of-crate [`ChatSource`] impl
/// (e.g. `starbridge_v2::world_chat`, where the chat IS the dregg world) can build
/// `RoomSummary`s WITHOUT depending on `matrix-sdk`/`ruma` directly — keeping that
/// heavy transitive dep inside this crate.
pub fn parse_room_id(s: &str) -> crate::Result<matrix_sdk::ruma::OwnedRoomId> {
    matrix_sdk::ruma::RoomId::parse(s).map_err(Into::into)
}
use crate::client::{
    EventState, MessageKind, Reaction, ReplyTo, RoomSummary, TimelineMessage,
};
use crate::membrane::MembraneEnvelope;
use crate::object::DreggObject;
use crate::Result;

/// The synchronous surface the chat UI renders against. Object-safe so the UI can
/// hold a `Box<dyn ChatSource>` and not care which backend it is.
pub trait ChatSource: Send + Sync + 'static {
    /// The logged-in user's full id (`@user:server`), if known. Used to align
    /// own-vs-other message bubbles and the composer's "sending as" line.
    fn whoami(&self) -> Option<String>;

    /// List joined rooms, sorted for display. May do network I/O (the real
    /// backend syncs); the UI calls this off the paint path (a spawned task).
    fn rooms(&self) -> Result<Vec<RoomSummary>>;

    /// Read a room's recent timeline (oldest-first), up to `limit` messages.
    fn timeline(&self, room_id: &str, limit: u16) -> Result<Vec<TimelineMessage>>;

    /// Send a plain-text message to a room. Returns the event id on success. The
    /// mock appends locally and echoes a synthetic id; the real backend POSTs and
    /// the next sync folds the echo in.
    fn send(&self, room_id: &str, body: &str) -> Result<String>;

    // --- the dregg-pilled surface --------------------------------------------
    // The chat IS the dregg world; these methods expose the room↔cell,
    // identity↔cell, and send↔turn mappings (docs/deos/APPS-AS-CELLS.md §3).

    /// The deos **room cell** this room IS (its durable core: membership, post-cap,
    /// turn history). The default derives a stable cell id; the deos side resolves
    /// the live `Cell` and folds its history.
    fn room_cell(&self, room_id: &str) -> RoomCell {
        RoomCell::for_room(room_id)
    }

    /// The deos **identity cell** a Matrix user ties to (device-keys-as-caps), with
    /// the person-level trust verdict ("verify the person, not the device"). The
    /// default maps every user to an `Unverified` identity cell; the deos side
    /// reads the cross-signing trust from the crypto store.
    fn identity(&self, user_id: &str) -> IdentityCell {
        IdentityCell::for_user(user_id, PersonTrust::Unverified)
    }

    /// Who is currently typing in a room (full user ids). Ephemeral view-state.
    fn typing(&self, _room_id: &str) -> Vec<String> {
        Vec::new()
    }

    /// Read-receipt: who has read up to (at least) the room's latest message.
    /// Ephemeral view-state (the Matrix kind, not the dregg receipt).
    fn read_by(&self, _room_id: &str) -> Vec<String> {
        Vec::new()
    }

    /// **Send = a turn.** Send a message and get back the [`SendReceipt`] (the turn
    /// the send conceptually committed against the room cell). The default sends and
    /// wraps a sketch receipt; the deos side returns a byte-identical `TurnReceipt`
    /// digest.
    fn send_turn(&self, room_id: &str, body: &str) -> Result<SendReceipt> {
        let event_id = self.send(room_id, body)?;
        let rc = self.room_cell(room_id);
        let me = self.whoami().unwrap_or_default();
        Ok(SendReceipt {
            room_cell: rc.cell_id,
            author_cell: self.identity(&me).cell_id,
            event_id,
            turn_index: rc.turn_count,
            post_root: rc.state_root,
        })
    }

    /// **Send a membrane** — the star feature. Attach a rehydratable cap-bounded
    /// fork of the deos world to a chat message. The default appends a
    /// membrane-bearing message locally; the deos side mints via the comms-PD's
    /// `MembraneHost` and POSTs it under the `software.ember.deos.membrane` key.
    fn send_membrane(
        &self,
        room_id: &str,
        body: &str,
        membrane: MembraneEnvelope,
    ) -> Result<String> {
        // Default: fall back to a text send carrying the human fallback (a backend
        // without membrane support still shows the conversation sensibly).
        let _ = membrane;
        self.send(room_id, body)
    }

    /// **Send a dregg semantic object** — the generalized membrane. Attach ANY
    /// [`DreggObject`] kind (cell/capability/transclusion/affordance/receipt/
    /// membrane) to a chat message. The default appends an object-bearing message
    /// locally; the deos side POSTs it under `software.ember.deos.object`.
    fn send_object(&self, room_id: &str, body: &str, object: DreggObject) -> Result<String> {
        // Default: a plain text send of the object's human fallback (a backend
        // without object support still shows the conversation sensibly).
        let fallback = if body.trim().is_empty() {
            object.text_fallback()
        } else {
            body.to_string()
        };
        self.send(room_id, &fallback)
    }

    /// Pull one sync round-trip (real backend) or refresh the mock's clock. The
    /// UI calls this on a timer so new messages appear.
    fn sync(&self) -> Result<()> {
        Ok(())
    }

    // --- the REAL membrane operations (the executor seam) --------------------
    // These are the interactive "screenshot a moment → rehydrate → drive →
    // stitch" affordances. They are executor-backed: a source that does NOT hold
    // the deos executor (e.g. a bare `MatrixHandle` with no comms-PD world)
    // returns `MembraneUnavailable`, fail-closed — it NEVER fabricates a mock
    // envelope. The real impl is `starbridge_v2`'s comms-PD source, which holds
    // a live `World` and mints/rehydrates/drives/stitches genuine `Cell` frusta.

    /// **Mint a membrane from the live world** — the interactive "screenshot a
    /// moment". Returns a genuine cap-bounded `MembraneEnvelope` (a frustum of
    /// real cells) the caller then sends. Fail-closed `MembraneUnavailable` when
    /// no executor is attached (NO mock fallback).
    fn mint_membrane(&self, _room_id: &str) -> Result<MembraneEnvelope> {
        Err(crate::Error::MembraneUnavailable)
    }

    /// **Rehydrate a received membrane, drive a real turn on it, and stitch it
    /// back** — the interactive receive side. Returns a human summary of the
    /// settled outcome (root + what merged / what dropped). Fail-closed
    /// `MembraneUnavailable` when no executor is attached (NO mock fallback).
    fn rehydrate_drive_stitch(&self, _membrane: &MembraneEnvelope) -> Result<String> {
        Err(crate::Error::MembraneUnavailable)
    }

    /// Whether THIS source can drive the real membrane operations (it holds the
    /// executor). The UI renders the mint/rehydrate affordances live only when
    /// this is true; otherwise it shows them disabled (never a mock action).
    fn membrane_capable(&self) -> bool {
        false
    }

    /// A short human label for the backend (shown in the title bar). "matrix",
    /// "mock", "firmament-comms-pd", …
    fn backend_label(&self) -> &'static str;
}

// ---------------------------------------------------------------------------
// MatrixHandle is a real ChatSource (the live backend).
//
// NATIVE-only: `MatrixHandle` is the synchronous blocking facade over the
// OS-thread worker, which does not exist on wasm32 (see `crate::worker`). The
// in-browser live backend is a separate `spawn_local`-driven shape (the next
// wire); `MockSource` below is the wasm-ready `ChatSource`.
// ---------------------------------------------------------------------------

#[cfg(not(target_family = "wasm"))]
impl ChatSource for crate::worker::MatrixHandle {
    fn whoami(&self) -> Option<String> {
        // Ask the worker for the live client's user id (the SDK holds it after
        // login/restore). None only when no client is authenticated yet.
        crate::worker::MatrixHandle::whoami(self)
    }

    fn rooms(&self) -> Result<Vec<RoomSummary>> {
        self.joined_rooms()
    }

    fn timeline(&self, room_id: &str, limit: u16) -> Result<Vec<TimelineMessage>> {
        self.recent_timeline(room_id.to_string(), limit)
    }

    fn send(&self, room_id: &str, body: &str) -> Result<String> {
        self.send_text(room_id.to_string(), body.to_string())
    }

    fn send_membrane(
        &self,
        room_id: &str,
        body: &str,
        membrane: MembraneEnvelope,
    ) -> Result<String> {
        // The live membrane send: the envelope rides under MEMBRANE_EVENT_KEY in a
        // real m.room.message (see MatrixClient::send_membrane). The SAME wire shape
        // the mock describes locally, now POSTed to a real homeserver.
        crate::worker::MatrixHandle::send_membrane(self, room_id.to_string(), body.to_string(), membrane)
    }

    fn send_object(&self, room_id: &str, body: &str, object: DreggObject) -> Result<String> {
        // The live object send: the object rides under DREGG_OBJECT_KEY in a real
        // m.room.message (see MatrixClient::send_object). The generalized membrane.
        crate::worker::MatrixHandle::send_object(self, room_id.to_string(), body.to_string(), object)
    }

    fn sync(&self) -> Result<()> {
        self.sync_once()
    }

    fn backend_label(&self) -> &'static str {
        "matrix"
    }
}

// ---------------------------------------------------------------------------
// MockSource — a recorded sync so the UI is real with no homeserver.
// ---------------------------------------------------------------------------

/// A synthetic chat backend: a fixed set of rooms with seeded timelines, plus a
/// working `send` that appends to the room's timeline in memory. This makes the
/// deos-chat UI fully exercisable offline — the room list, the timeline, and the
/// composer all do real work against in-memory state.
pub struct MockSource {
    me: String,
    rooms: Vec<RoomSummary>,
    /// Per-room timelines, parallel to `rooms` by index of the room_id.
    timelines: Mutex<Vec<(String, Vec<TimelineMessage>)>>,
    clock: Mutex<u64>,
    /// Per-user person-level trust (the identity-cell verdict).
    trust: Vec<(String, PersonTrust)>,
    /// Per-room typing indicators (ephemeral view-state).
    typing: Vec<(String, Vec<String>)>,
    /// Per-room read-receipts (who has read the latest).
    read_by: Vec<(String, Vec<String>)>,
}

impl MockSource {
    /// A deos-flavoured seeded world: a few rooms, a few voices, some chatter
    /// that hints at the membrane seam this client exists to carry.
    pub fn seeded() -> Self {
        use matrix_sdk::ruma::RoomId;
        let me = "@ember:deos.local".to_string();

        fn room(id: &str, name: &str, topic: &str, members: u64, encrypted: bool) -> RoomSummary {
            RoomSummary {
                room_id: RoomId::parse(id).expect("valid room id"),
                display_name: name.to_string(),
                topic: Some(topic.to_string()),
                is_encrypted: encrypted,
                is_space: false,
                is_direct: false,
                joined_members: members,
                unread_notifications: 0,
            }
        }

        let rooms = vec![
            room(
                "!deoslab:deos.local",
                "deos-lab",
                "the live image — drop membranes here",
                7,
                true,
            ),
            room(
                "!firmament:deos.local",
                "firmament",
                "one cap across distance",
                4,
                true,
            ),
            room(
                "!hpriori:deos.local",
                "houyhnhnm-priori",
                "branch-and-stitch & distributed time-travel",
                3,
                false,
            ),
            room(
                "!ember:deos.local",
                "ember (DM)",
                "direct",
                2,
                true,
            ),
        ];

        let mut clock = 1_718_000_000_000u64; // a fixed plausible ms epoch
        let mut step = || {
            clock += 47_000;
            clock
        };

        let msg = |sender: &str, body: &str, ts: u64| {
            TimelineMessage::text(format!("$evt{ts}"), sender.to_string(), body.to_string(), ts)
        };
        let react = |key: &str, who: &[&str]| Reaction {
            key: key.to_string(),
            senders: who.iter().map(|s| s.to_string()).collect(),
        };

        // Room 0 (deos-lab): the membrane conversation — the STAR feature on full
        // display: reactions, a reply, an edit, a redaction, and a real (mock)
        // membrane-bearing message.
        let mut m0_grok = msg(
            "@grok:deos.local",
            "the live image boots on seL4 again — BALANCE_SUM=0 holds",
            step(),
        );
        m0_grok.reactions = vec![react("🎉", &["@ember:deos.local", "@pug:deos.local"]), react("🔒", &["@ember:deos.local"])];

        let mut m0_emb = msg(
            "@ember:deos.local",
            "drop a membrane of the cell graph you're looking at",
            step(),
        );
        m0_emb.kind = MessageKind::Emote;
        m0_emb.body = "* ember asks for a membrane".to_string();

        // The membrane-bearing message — kind=Membrane, carrying a real minted
        // (mock) envelope so the rehydrate affordance is exercisable offline.
        let mut m0_mem = msg("@grok:deos.local", "", step());
        let env = crate::membrane::MockMembraneHost::sample_envelope();
        m0_mem.body = env.text_fallback();
        m0_mem.kind = MessageKind::Membrane;
        m0_mem.membrane = Some(env);
        m0_mem.reactions = vec![react("🤯", &["@ember:deos.local"])];

        let mut m0_reply = msg(
            "@ember:deos.local",
            "rehydrated. driving a SetField turn on the fork. will stitch back.",
            step(),
        );
        m0_reply.reply_to = Some(ReplyTo {
            event_id: m0_mem.event_id.clone(),
            sender: "@grok:deos.local".to_string(),
            preview: "[deos membrane · cap-bounded fork]".to_string(),
        });

        let mut m0_edited = msg(
            "@ember:deos.local",
            "stitched — clean merge, 2 turns folded (edited: was 1)",
            step(),
        );
        m0_edited.state = EventState::Edited;

        let mut m0_redacted = msg("@pug:deos.local", "oops wrong room", step());
        m0_redacted.state = EventState::Redacted;

        // The generalized dregg objects on display: a transclusion (a live quoted
        // value), a shareable capability, and a fireable cap-gated affordance — so
        // the timeline reads as a dregg object-exchange channel, not just a chat.
        use crate::object::{Affordance, CapabilityGrant, DreggObject, Transclusion};
        let mut m0_trans = msg("@grok:deos.local", "", step());
        let trans = DreggObject::Transclusion(Transclusion {
            source_cell: crate::cell::CellId::derive("!deoslab:deos.local"),
            field: "BALANCE_SUM".into(),
            value: "0".into(),
            bound_root: [0xe3; 32],
        });
        m0_trans.body = trans.text_fallback();
        m0_trans.kind = MessageKind::Object("transclusion".into());
        m0_trans.object = Some(trans);

        let mut m0_cap = msg("@ember:deos.local", "", step());
        let cap = DreggObject::Capability(CapabilityGrant {
            sturdyref: "dregg://cap/post/deoslab".into(),
            label: "post to deos-lab".into(),
            lineage: vec![0xca, 0x9a, 0xb1, 0xe],
        });
        m0_cap.body = cap.text_fallback();
        m0_cap.kind = MessageKind::Object("capability".into());
        m0_cap.object = Some(cap);

        let mut m0_aff = msg("@pug:deos.local", "", step());
        let aff = DreggObject::Affordance(Affordance {
            target_cell: crate::cell::CellId::derive("!deoslab:deos.local"),
            action: "approve".into(),
            label: "Approve the stitch".into(),
            required_cap: "dregg://cap/approve".into(),
        });
        m0_aff.body = aff.text_fallback();
        m0_aff.kind = MessageKind::Object("affordance".into());
        m0_aff.object = Some(aff);

        let timelines = vec![
            (
                rooms[0].room_id.to_string(),
                vec![
                    m0_grok, m0_emb, m0_mem, m0_reply, m0_edited, m0_redacted, m0_trans, m0_cap,
                    m0_aff,
                ],
            ),
            (
                rooms[1].room_id.to_string(),
                {
                    let mut a = msg("@pug:deos.local", "n=1 collapse: local seL4-cap == distributed dregg-cap == window", step());
                    a.reactions = vec![react("👀", &["@ember:deos.local"])];
                    let b = msg("@ember:deos.local", "surface IS the membrane boundary then", step());
                    vec![a, b]
                },
            ),
            (
                rooms[2].room_id.to_string(),
                {
                    let a = msg("@fare:deos.local", "a stitch is a pushout in the event-structure config lattice", step());
                    let mut b = msg("@ember:deos.local", "and linearity makes the inconsistent events lossy-dropped — exactly where Σδ=0 / nullifiers force it", step());
                    b.reply_to = Some(ReplyTo {
                        event_id: a.event_id.clone(),
                        sender: "@fare:deos.local".to_string(),
                        preview: "a stitch is a pushout…".to_string(),
                    });
                    let c = msg("@fare:deos.local", "conflicts-as-objects. patch theory validates the merge.", step());
                    vec![a, b, c]
                },
            ),
            (
                rooms[3].room_id.to_string(),
                vec![msg("@ember:deos.local", "note to self: wire the SendMessage worker variant", step())],
            ),
        ];

        // Per-user trust (the identity-cell verdict). ember verifies herself + grok;
        // pug is unverified; fare's identity recently CHANGED (a possible MITM the
        // UI must surface loudly).
        let trust = vec![
            ("@ember:deos.local".to_string(), PersonTrust::Verified),
            ("@grok:deos.local".to_string(), PersonTrust::Verified),
            ("@pug:deos.local".to_string(), PersonTrust::Unverified),
            ("@fare:deos.local".to_string(), PersonTrust::Changed),
        ];

        // Ephemeral typing + read-receipts (view-state, seeded for the demo).
        let typing = vec![
            (rooms[0].room_id.to_string(), vec!["@grok:deos.local".to_string()]),
            (rooms[2].room_id.to_string(), Vec::new()),
        ];
        let read_by = vec![
            (
                rooms[0].room_id.to_string(),
                vec!["@grok:deos.local".to_string(), "@pug:deos.local".to_string()],
            ),
        ];

        // Seed a couple of unread badges + topics already set above.
        let mut rooms = rooms;
        rooms[2].unread_notifications = 3;
        rooms[3].unread_notifications = 1;
        rooms[1].is_direct = false;
        rooms[3].is_direct = true;

        Self {
            me,
            rooms,
            timelines: Mutex::new(timelines),
            clock: Mutex::new(clock),
            trust,
            typing,
            read_by,
        }
    }

    fn trust_of(&self, user_id: &str) -> PersonTrust {
        self.trust
            .iter()
            .find(|(u, _)| u == user_id)
            .map(|(_, t)| *t)
            .unwrap_or(PersonTrust::Unverified)
    }

    /// The number of (durable) turns in a room == its message count, for the room
    /// cell's `turn_count`.
    fn turn_count_of(&self, room_id: &str) -> u64 {
        let timelines = self.timelines.lock().unwrap();
        timelines
            .iter()
            .find(|(id, _)| id == room_id)
            .map(|(_, msgs)| msgs.len() as u64)
            .unwrap_or(0)
    }
}

impl ChatSource for MockSource {
    fn whoami(&self) -> Option<String> {
        Some(self.me.clone())
    }

    fn rooms(&self) -> Result<Vec<RoomSummary>> {
        Ok(self.rooms.clone())
    }

    fn timeline(&self, room_id: &str, limit: u16) -> Result<Vec<TimelineMessage>> {
        let timelines = self.timelines.lock().unwrap();
        for (id, msgs) in timelines.iter() {
            if id == room_id {
                let n = msgs.len();
                let start = n.saturating_sub(limit as usize);
                return Ok(msgs[start..].to_vec());
            }
        }
        Ok(Vec::new())
    }

    fn send(&self, room_id: &str, body: &str) -> Result<String> {
        self.append(room_id, |event_id, ts, me| {
            TimelineMessage::text(event_id, me, body.to_string(), ts)
        })
    }

    fn room_cell(&self, room_id: &str) -> RoomCell {
        let mut rc = RoomCell::for_room(room_id);
        rc.turn_count = self.turn_count_of(room_id);
        // A mock state root derived from (cell id ‖ turn count) so it advances with
        // history — non-fabricated within the mock world.
        let mut root = rc.cell_id.0;
        root[0] ^= rc.turn_count as u8;
        rc.state_root = root;
        rc
    }

    fn identity(&self, user_id: &str) -> IdentityCell {
        IdentityCell::for_user(user_id, self.trust_of(user_id))
    }

    fn typing(&self, room_id: &str) -> Vec<String> {
        self.typing
            .iter()
            .find(|(id, _)| id == room_id)
            .map(|(_, who)| who.clone())
            .unwrap_or_default()
    }

    fn read_by(&self, room_id: &str) -> Vec<String> {
        self.read_by
            .iter()
            .find(|(id, _)| id == room_id)
            .map(|(_, who)| who.clone())
            .unwrap_or_default()
    }

    fn send_membrane(
        &self,
        room_id: &str,
        body: &str,
        membrane: MembraneEnvelope,
    ) -> Result<String> {
        let fallback = if body.trim().is_empty() {
            membrane.text_fallback()
        } else {
            body.to_string()
        };
        self.append(room_id, move |event_id, ts, me| {
            let mut m = TimelineMessage::text(event_id, me, fallback.clone(), ts);
            m.kind = MessageKind::Membrane;
            m.membrane = Some(membrane.clone());
            m
        })
    }

    fn send_object(&self, room_id: &str, body: &str, object: DreggObject) -> Result<String> {
        let fallback = if body.trim().is_empty() {
            object.text_fallback()
        } else {
            body.to_string()
        };
        // The kind: a membrane object surfaces as Membrane (so the rehydrate card
        // renders); every other kind as Object(kind). A membrane also fills the
        // typed `membrane` field for the existing card path.
        let (kind, membrane) = match &object {
            DreggObject::Membrane(env) => (MessageKind::Membrane, Some(env.clone())),
            other => (MessageKind::Object(other.kind().to_string()), None),
        };
        self.append(room_id, move |event_id, ts, me| {
            let mut m = TimelineMessage::text(event_id, me, fallback.clone(), ts);
            m.kind = kind.clone();
            m.membrane = membrane.clone();
            m.object = Some(object.clone());
            m
        })
    }

    fn backend_label(&self) -> &'static str {
        "mock"
    }
}

impl MockSource {
    /// Shared append path for `send` / `send_membrane`: mint a local event id + ts,
    /// build the message via `make`, and push it to the room's timeline.
    fn append(
        &self,
        room_id: &str,
        make: impl FnOnce(String, u64, String) -> TimelineMessage,
    ) -> Result<String> {
        let ts = {
            let mut clock = self.clock.lock().unwrap();
            *clock += 1_000;
            *clock
        };
        let event_id = format!("$local{ts}");
        let mut timelines = self.timelines.lock().unwrap();
        for (id, msgs) in timelines.iter_mut() {
            if id == room_id {
                msgs.push(make(event_id.clone(), ts, self.me.clone()));
                return Ok(event_id);
            }
        }
        Err(crate::Error::Other(format!("no such room: {room_id}")))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mock_lists_rooms_and_timelines() {
        let src = MockSource::seeded();
        let rooms = src.rooms().unwrap();
        assert!(rooms.len() >= 3, "expected several seeded rooms");
        let first = rooms[0].room_id.to_string();
        let tl = src.timeline(&first, 50).unwrap();
        assert!(!tl.is_empty(), "first room has a seeded timeline");
        // Oldest-first ordering.
        for w in tl.windows(2) {
            assert!(w[0].timestamp_ms <= w[1].timestamp_ms);
        }
    }

    #[test]
    fn mock_send_appends_and_echoes() {
        let src = MockSource::seeded();
        let rooms = src.rooms().unwrap();
        let room = rooms[0].room_id.to_string();
        let before = src.timeline(&room, 100).unwrap().len();
        let id = src.send(&room, "hello membrane").unwrap();
        assert!(id.starts_with("$local"));
        let after = src.timeline(&room, 100).unwrap();
        assert_eq!(after.len(), before + 1);
        assert_eq!(after.last().unwrap().body, "hello membrane");
        assert_eq!(after.last().unwrap().sender, src.whoami().unwrap());
    }

    #[test]
    fn mock_seeds_rich_event_states() {
        let src = MockSource::seeded();
        let room = src.rooms().unwrap()[0].room_id.to_string();
        let tl = src.timeline(&room, 100).unwrap();
        // It carries reactions, an edit, a redaction, a reply, and a membrane.
        assert!(tl.iter().any(|m| !m.reactions.is_empty()), "has reactions");
        assert!(tl.iter().any(|m| m.state == EventState::Edited), "has an edit");
        assert!(tl.iter().any(|m| m.state == EventState::Redacted), "has a redaction");
        assert!(tl.iter().any(|m| m.reply_to.is_some()), "has a reply");
        assert!(
            tl.iter().any(|m| m.kind == MessageKind::Membrane && m.membrane.is_some()),
            "has a membrane-bearing message"
        );
    }

    #[test]
    fn room_is_a_cell_with_advancing_history() {
        let src = MockSource::seeded();
        let room = src.rooms().unwrap()[0].room_id.to_string();
        let before = src.room_cell(&room);
        assert!(before.turn_count >= 1, "the seeded room has history (turns)");
        let root_before = before.state_root;
        // A send is a turn — the room cell's history advances.
        src.send(&room, "another turn").unwrap();
        let after = src.room_cell(&room);
        assert_eq!(after.turn_count, before.turn_count + 1);
        assert_ne!(after.state_root, root_before, "the room cell root advanced");
        assert_eq!(after.cell_id, before.cell_id, "same room == same cell");
    }

    #[test]
    fn identity_is_a_cell_with_person_trust() {
        let src = MockSource::seeded();
        assert_eq!(src.identity("@ember:deos.local").trust, PersonTrust::Verified);
        assert_eq!(src.identity("@pug:deos.local").trust, PersonTrust::Unverified);
        // fare's identity changed — the loud, must-surface case.
        assert_eq!(src.identity("@fare:deos.local").trust, PersonTrust::Changed);
        // unknown user defaults to Unverified (never fabricates trust).
        assert_eq!(src.identity("@stranger:x").trust, PersonTrust::Unverified);
    }

    #[test]
    fn send_is_a_turn_with_a_receipt() {
        let src = MockSource::seeded();
        let room = src.rooms().unwrap()[0].room_id.to_string();
        let r = src.send_turn(&room, "a receipted message").unwrap();
        assert_eq!(r.room_cell, src.room_cell(&room).cell_id);
        assert_eq!(r.author_cell, src.identity(&src.whoami().unwrap()).cell_id);
        assert!(r.event_id.starts_with("$local"));
        assert!(r.digest().starts_with("turn "));
    }

    #[test]
    fn send_membrane_appends_a_membrane_message() {
        let src = MockSource::seeded();
        let room = src.rooms().unwrap()[0].room_id.to_string();
        let env = crate::membrane::MockMembraneHost::sample_envelope();
        let before = src.timeline(&room, 200).unwrap().len();
        let id = src.send_membrane(&room, "", env.clone()).unwrap();
        assert!(id.starts_with("$local"));
        let after = src.timeline(&room, 200).unwrap();
        assert_eq!(after.len(), before + 1);
        let last = after.last().unwrap();
        assert_eq!(last.kind, MessageKind::Membrane);
        assert_eq!(last.membrane.as_ref().unwrap(), &env);
        // Empty body falls back to the human-readable membrane summary.
        assert!(last.body.starts_with("[deos membrane"));
    }

    #[test]
    fn send_object_appends_each_kind() {
        use crate::object::{CapabilityGrant, CellRef, DreggObject, Transclusion};
        let src = MockSource::seeded();
        let room = src.rooms().unwrap()[0].room_id.to_string();

        let cell = DreggObject::Cell(CellRef {
            cell_id: crate::cell::CellId::derive("!deoslab:deos.local"),
            label: "deos-lab room cell".into(),
            cell_kind: Some("room".into()),
        });
        let id = src.send_object(&room, "", cell.clone()).unwrap();
        assert!(id.starts_with("$local"));
        let last = src.timeline(&room, 200).unwrap().pop().unwrap();
        assert_eq!(last.kind, MessageKind::Object("cell".into()));
        assert_eq!(last.object.unwrap(), cell);

        // A capability kind renders the "accept into powerbox" affordance.
        let cap = DreggObject::Capability(CapabilityGrant {
            sturdyref: "dregg://cap/post".into(),
            label: "post to deos-lab".into(),
            lineage: vec![1, 2, 3],
        });
        src.send_object(&room, "", cap.clone()).unwrap();
        let last = src.timeline(&room, 200).unwrap().pop().unwrap();
        assert_eq!(last.kind, MessageKind::Object("capability".into()));

        // A transclusion carries the live quoted value.
        let tr = DreggObject::Transclusion(Transclusion {
            source_cell: crate::cell::CellId::derive("!deoslab:deos.local"),
            field: "members.count".into(),
            value: "7".into(),
            bound_root: [0xab; 32],
        });
        src.send_object(&room, "", tr.clone()).unwrap();
        let last = src.timeline(&room, 200).unwrap().pop().unwrap();
        assert_eq!(last.kind, MessageKind::Object("transclusion".into()));
        assert_eq!(last.object.unwrap(), tr);

        // A membrane object surfaces as Membrane (so the existing card renders) AND
        // fills the typed membrane field.
        let mem = DreggObject::Membrane(crate::membrane::MockMembraneHost::sample_envelope());
        src.send_object(&room, "", mem.clone()).unwrap();
        let last = src.timeline(&room, 200).unwrap().pop().unwrap();
        assert_eq!(last.kind, MessageKind::Membrane);
        assert!(last.membrane.is_some(), "membrane object fills the typed field");
    }

    #[test]
    fn typing_and_read_receipts_are_view_state() {
        let src = MockSource::seeded();
        let room = src.rooms().unwrap()[0].room_id.to_string();
        assert!(src.typing(&room).contains(&"@grok:deos.local".to_string()));
        assert!(src.read_by(&room).len() >= 1);
    }
}

// ---------------------------------------------------------------------------
// The IN-BROWSER proof: the SAME `MockSource`-backed `ChatSource` data path,
// exercised under `wasm-bindgen-test` on wasm32. This is the wasm analogue of
// the native suite above — it proves rooms / timeline / send / the membrane
// round-trip all run in a browser tab WITHOUT a server (and without the native
// OS-thread worker, which is `cfg(not(wasm32))` out). Run with
// `wasm-pack test --node` (or `--headless --chrome`) in `deos-matrix/`.
// ---------------------------------------------------------------------------
#[cfg(all(test, target_family = "wasm"))]
mod wasm_tests {
    use super::*;
    use wasm_bindgen_test::*;

    // No `run_in_browser` configure: the `MockSource` data path is pure compute
    // (no DOM/web-sys), so it runs under `wasm-pack test --node` (real wasm32
    // execution, in CI without a browser driver) AND, unchanged, in a browser via
    // `--headless --chrome`. The `gpui_web`-rendered `ChatView` is what binds this
    // same data to a browser tab; this test proves the data underneath runs on the
    // wasm32 single-threaded model with no native worker.

    #[wasm_bindgen_test]
    fn mock_chatsource_runs_on_wasm() {
        // Drive the ChatSource trait object exactly as the gpui ChatView does, on
        // the wasm32 single-threaded event loop. No tokio runtime, no worker.
        let src: Box<dyn ChatSource> = Box::new(MockSource::seeded());

        // whoami / rooms / timeline.
        assert!(src.whoami().is_some());
        let rooms = src.rooms().unwrap();
        assert!(rooms.len() >= 3, "seeded rooms present in-browser");
        let room = rooms[0].room_id.to_string();
        let tl = src.timeline(&room, 100).unwrap();
        assert!(!tl.is_empty(), "the timeline has data with no server");

        // send appends + echoes a local event id.
        let before = src.timeline(&room, 200).unwrap().len();
        let id = src.send(&room, "hello from wasm").unwrap();
        assert!(id.starts_with("$local"));
        let after = src.timeline(&room, 200).unwrap();
        assert_eq!(after.len(), before + 1);
        assert_eq!(after.last().unwrap().body, "hello from wasm");

        // The membrane round-trip: mint → send → it rides as a Membrane message.
        let env = crate::membrane::MockMembraneHost::sample_envelope();
        let mid = src.send_membrane(&room, "", env.clone()).unwrap();
        assert!(mid.starts_with("$local"));
        let last = src.timeline(&room, 200).unwrap().pop().unwrap();
        assert_eq!(last.kind, MessageKind::Membrane);
        assert_eq!(last.membrane.as_ref().unwrap(), &env);

        // send = a turn with a receipt (the dregg-pilled surface, in-browser).
        let r = src.send_turn(&room, "a receipted turn").unwrap();
        assert_eq!(r.room_cell, src.room_cell(&room).cell_id);
        assert!(r.digest().starts_with("turn "));
    }
}
