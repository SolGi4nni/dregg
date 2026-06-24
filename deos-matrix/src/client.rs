//! The async Matrix client core.
//!
//! Thin, deos-shaped wrapper over [`matrix_sdk::Client`]. Every method is
//! `async`; the synchronous-caller bridge lives in [`crate::worker`]. The SDK
//! handles the protocol (sync, room state, ruma events) and E2E encryption
//! (vodozemac, via the default `e2e-encryption` feature + the SQLite crypto
//! store). We add: a homeserver+store builder, password login with session
//! persistence, an encrypted `sync_once` + a continuous `sync`, a flat room
//! summary, and a recent-timeline read.

use std::path::Path;

use matrix_sdk::{
    Client, RoomState,
    authentication::matrix::MatrixSession,
    config::SyncSettings,
    ruma::{
        OwnedRoomId, UserId,
        api::client::filter::RoomEventFilter,
        events::AnySyncTimelineEvent,
        events::room::message::{MessageType, RoomMessageEventContent},
    },
};

use crate::membrane::{MEMBRANE_EVENT_KEY, MembraneEnvelope};
use crate::{Error, Result, session::StoredSession};

/// A native deos Matrix client over `matrix-rust-sdk`.
pub struct MatrixClient {
    inner: Client,
}

/// A flat, UI-agnostic summary of a joined room.
#[derive(Debug, Clone)]
pub struct RoomSummary {
    pub room_id: OwnedRoomId,
    pub display_name: String,
    pub topic: Option<String>,
    pub is_encrypted: bool,
    pub is_space: bool,
    pub is_direct: bool,
    pub joined_members: u64,
    pub unread_notifications: u64,
}

/// A joined **space** (a room of type `m.space`) and its joined child rooms — the
/// room hierarchy a heavy user navigates by.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpaceSummary {
    pub room_id: OwnedRoomId,
    pub display_name: String,
    /// The child room ids declared by the space's `m.space.child` state events.
    pub child_room_ids: Vec<String>,
}

/// A flat description of a room in the homeserver's **public directory** — what a
/// directory search returns, enough to join by id/alias.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PublicRoom {
    pub room_id: String,
    pub name: Option<String>,
    pub topic: Option<String>,
    pub alias: Option<String>,
    pub joined_members: u64,
    /// Whether the room's history is world-readable (a preview is possible).
    pub world_readable: bool,
}

/// A room's basic **power levels** + the local user's level — the room settings a
/// heavy user inspects ("can I invite? am I an admin here?").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RoomPower {
    pub users_default: i64,
    pub invite: i64,
    pub kick: i64,
    pub ban: i64,
    pub redact: i64,
    /// The local user's effective power level in this room.
    pub my_level: i64,
}

/// What kind of message-like event this is — the visible *content* type, distinct
/// from its lifecycle [`state`](TimelineMessage::state). Mirrors ruma's
/// `MessageType` for the kinds the UI renders specially; the catch-all keeps the
/// projection total.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MessageKind {
    /// A plain text message (`m.text`).
    Text,
    /// An emote (`m.emote`) — "* ember waves".
    Emote,
    /// A notice (`m.notice`) — bot/automation, rendered muted.
    Notice,
    /// A non-text attachment (image/file/audio/video), with its kind word.
    Attachment(String),
    /// **The deos membrane** — this message carries a rehydratable cap-bounded fork
    /// of the deos world (see [`crate::membrane`]). Rendered specially (the star
    /// feature). The envelope rides in [`TimelineMessage::membrane`].
    Membrane,
    /// **A deos semantic object** of the named kind (cell/capability/transclusion/
    /// affordance/receipt — see [`crate::object`]). The object rides in
    /// [`TimelineMessage::object`]; the UI renders each kind specially. The carried
    /// string is the object's `kind` tag (for a label without re-matching).
    Object(String),
}

/// The lifecycle STATE of a timeline event. nheko's principle: edits/redactions
/// are *states of an event*, not deletions — so a redacted message still occupies
/// its slot (showing "message removed"), and an edited message shows its latest
/// body with an "(edited)" marker. The timeline is a presentation pass over events
/// in these states, never a destructive mutation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EventState {
    /// A normal, live event.
    Live,
    /// Edited — the body shown is the latest replacement; an "(edited)" marker is
    /// rendered.
    Edited,
    /// Redacted — the content was removed; the slot remains, showing a tombstone.
    Redacted,
}

/// A reaction aggregate on a message (`m.reaction`): an emoji key and who reacted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Reaction {
    /// The reaction key (usually an emoji, e.g. "🔥").
    pub key: String,
    /// The senders who reacted with this key (full user ids).
    pub senders: Vec<String>,
}

impl Reaction {
    /// The count to show on the pill.
    pub fn count(&self) -> usize {
        self.senders.len()
    }
    /// Whether `me` is among the reactors (so the pill renders "mine").
    pub fn mine(&self, me: Option<&str>) -> bool {
        me.is_some_and(|m| self.senders.iter().any(|s| s == m))
    }
}

/// A reply pointer (`m.in_reply_to`): the event being replied to, with a short
/// quoted preview so the UI can render the reply context inline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReplyTo {
    /// The replied-to event id.
    pub event_id: String,
    /// The replied-to sender (for the quoted attribution).
    pub sender: String,
    /// A short preview of the replied-to body (first line, truncated).
    pub preview: String,
}

/// A single rendered timeline message — the rich projection the UI renders.
///
/// Edits/redactions are STATES ([`EventState`]); reactions, replies, and an
/// embedded deos membrane are first-class. The headless core fills the plain
/// fields; the richer fields default empty (a real `matrix_sdk_ui::Timeline`
/// upgrade folds them in — see [`MatrixClient::recent_timeline`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TimelineMessage {
    pub event_id: String,
    pub sender: String,
    pub body: String,
    /// Origin server timestamp, milliseconds since the Unix epoch.
    pub timestamp_ms: u64,
    /// The content kind (text/emote/notice/attachment/membrane).
    pub kind: MessageKind,
    /// The lifecycle state (live/edited/redacted).
    pub state: EventState,
    /// Reaction aggregates on this message.
    pub reactions: Vec<Reaction>,
    /// If this message is a reply, the pointer + preview of what it replies to.
    pub reply_to: Option<ReplyTo>,
    /// If this message belongs to a thread, the thread-root event id.
    pub thread_root: Option<String>,
    /// **The deos membrane** carried by this message, if any. When present,
    /// [`Self::kind`] is [`MessageKind::Membrane`] and the UI renders the
    /// rehydrate affordance. The bytes are inert until a recipient's comms-PD
    /// rehydrates them.
    pub membrane: Option<crate::membrane::MembraneEnvelope>,
    /// **A deos semantic object** carried by this message, if any (the generalized
    /// envelope — cell/capability/transclusion/affordance/receipt, and also a
    /// membrane carried under the new key). When present, [`Self::kind`] is
    /// [`MessageKind::Object`] (or `Membrane` for the membrane kind) and the UI
    /// renders the kind-specific affordance. Inert until acted on.
    pub object: Option<crate::object::DreggObject>,
}

impl TimelineMessage {
    /// A plain text message — the common case, with all rich fields empty. Keeps
    /// the headless `recent_timeline` projection terse.
    pub fn text(event_id: String, sender: String, body: String, timestamp_ms: u64) -> Self {
        TimelineMessage {
            event_id,
            sender,
            body,
            timestamp_ms,
            kind: MessageKind::Text,
            state: EventState::Live,
            reactions: Vec::new(),
            reply_to: None,
            thread_root: None,
            membrane: None,
            object: None,
        }
    }
}

impl MatrixClient {
    /// Build a client for `server`, backed by a SQLite store at `store_path`
    /// (state + E2E crypto). The store is opened with `passphrase`.
    ///
    /// `server` is accepted in either of the two forms a real user types:
    ///   * a full homeserver URL (`https://matrix-client.matrix.org`,
    ///     `http://localhost:6167`) — used directly;
    ///   * a bare server name (`matrix.org`, `deos.local`) — resolved via the SDK's
    ///     `.well-known` / versions discovery (`server_name_or_homeserver_url`),
    ///     exactly what a login form's "homeserver" field needs.
    ///
    /// A plain-HTTP URL (no TLS — e.g. a local conduit on `http://localhost`) is
    /// honored as-is; this is the only path that talks to a non-TLS server, and it
    /// is opt-in by typing an `http://` URL.
    /// On wasm32, `store_path` names the **IndexedDB database** (its string form)
    /// rather than a filesystem path — the browser has no filesystem, so the
    /// SQLite state + crypto store is replaced by matrix-sdk's IndexedDB store
    /// (`indexeddb_store`, under the `indexeddb` feature). Same passphrase
    /// discipline; same encrypted state + olm crypto, persisted in the browser.
    pub async fn build(server: &str, store_path: &Path, passphrase: &str) -> Result<Self> {
        // The store seam is the one genuinely per-target piece of `build`: native
        // + `live-matrix` → SQLite on disk; native default → the in-memory store
        // (no on-disk SQLite, so no `libsqlite3-sys` `links="sqlite3"` collision
        // with Zed's `sqlez` in the cockpit graph); wasm → IndexedDB in the
        // browser. Everything else (URL/server-name discovery, the async `build`)
        // is shared. (`store_path`/`passphrase` are unused without an on-disk store.)
        #[cfg(all(not(target_family = "wasm"), feature = "live-matrix"))]
        let builder = Client::builder().sqlite_store(store_path, Some(passphrase));
        #[cfg(all(not(target_family = "wasm"), not(feature = "live-matrix")))]
        let builder = {
            let _ = (store_path, passphrase);
            Client::builder()
        };
        #[cfg(target_family = "wasm")]
        let builder =
            Client::builder().indexeddb_store(&store_path.to_string_lossy(), Some(passphrase));

        // A URL (has a scheme) → use it directly; a bare name → discover.
        let builder = if server.starts_with("http://") || server.starts_with("https://") {
            builder.homeserver_url(server)
        } else {
            builder.server_name_or_homeserver_url(server)
        };
        let inner = builder.build().await?;
        Ok(Self { inner })
    }

    /// Log in with a username (localpart or full `@user:server`) and password,
    /// returning a [`StoredSession`] the caller should persist. The
    /// `initial_device_display_name` is what other devices see in this account's
    /// device list.
    pub async fn login_password(
        homeserver_url: &str,
        store_path: &Path,
        passphrase: &str,
        username: &str,
        password: &str,
        device_display_name: &str,
    ) -> Result<(Self, StoredSession)> {
        let me = Self::build(homeserver_url, store_path, passphrase).await?;

        me.inner
            .matrix_auth()
            .login_username(username, password)
            .initial_device_display_name(device_display_name)
            .send()
            .await?;

        let session = me
            .inner
            .matrix_auth()
            .session()
            .ok_or_else(|| Error::Other("login succeeded but no session present".into()))?;

        let stored = StoredSession {
            homeserver: homeserver_url.to_string(),
            session,
            store_path: store_path.to_path_buf(),
            store_passphrase: passphrase.to_string(),
        };
        Ok((me, stored))
    }

    /// Log in directly with a pre-issued **access token** (and device id),
    /// returning a persistable [`StoredSession`]. This is the SSO/token path: an
    /// SSO flow (or an admin-issued token) yields `access_token` + `device_id` +
    /// the `user_id` they belong to, with no password ever held by this client.
    /// Identical session shape to [`Self::login_password`], so the rest of the
    /// stack (restore, persistence, the comms-PD seam) is unchanged.
    pub async fn login_access_token(
        homeserver_url: &str,
        store_path: &Path,
        passphrase: &str,
        user_id: &str,
        access_token: &str,
        device_id: &str,
    ) -> Result<(Self, StoredSession)> {
        use matrix_sdk::{
            SessionMeta,
            authentication::{SessionTokens, matrix::MatrixSession},
            ruma::OwnedDeviceId,
        };
        let me = Self::build(homeserver_url, store_path, passphrase).await?;
        let session = MatrixSession {
            meta: SessionMeta {
                user_id: UserId::parse(user_id)?,
                device_id: OwnedDeviceId::from(device_id),
            },
            tokens: SessionTokens {
                access_token: access_token.to_string(),
                refresh_token: None,
            },
        };
        me.inner.restore_session(session.clone()).await?;
        // Verify the token actually authenticates (fail-closed, not "stored but
        // dead") before handing back a session the caller will persist as valid.
        me.inner.whoami().await?;
        let stored = StoredSession {
            homeserver: homeserver_url.to_string(),
            session,
            store_path: store_path.to_path_buf(),
            store_passphrase: passphrase.to_string(),
        };
        Ok((me, stored))
    }

    /// Log in via **SSO/OIDC** against an arbitrary homeserver. The homeserver's
    /// login page is opened in the user's browser (`open_url`, given the SSO URL);
    /// the SDK runs a transient local-HTTP server to catch the redirect and finish
    /// the flow. This is the path a heavy user expects when their homeserver
    /// federates auth (Google/GitHub/Keycloak/…) instead of holding a password.
    ///
    /// `open_url` is the caller's "open this URL" action (a real client shells out
    /// to the OS browser; a test can capture it). Returns a persistable session,
    /// identical in shape to the password/token paths so the rest of the stack is
    /// unchanged.
    ///
    /// NATIVE-only: `MatrixAuth::login_sso` runs a transient local-HTTP server to
    /// catch the OIDC redirect (matrix-sdk's `sso-login`/`local-server` feature,
    /// which binds a native TCP socket — unavailable in a browser). The wasm SSO
    /// path is the OAuth/OIDC redirect-in-tab flow via [`Self::sso_login_url`]
    /// (which DOES compile on wasm), not the local-server catcher. Next wire.
    #[cfg(not(target_family = "wasm"))]
    pub async fn login_sso(
        homeserver: &str,
        store_path: &Path,
        passphrase: &str,
        device_display_name: &str,
        open_url: impl FnOnce(String) + Send + 'static,
    ) -> Result<(Self, StoredSession)> {
        let me = Self::build(homeserver, store_path, passphrase).await?;
        // Capture the actual homeserver the SDK resolved (a bare server-name gets
        // rewritten to the discovered base URL), so the stored session restores
        // against the right URL.
        let resolved = me.inner.homeserver().to_string();
        me.inner
            .matrix_auth()
            .login_sso(|sso_url| async move {
                open_url(sso_url);
                Ok(())
            })
            .initial_device_display_name(device_display_name)
            .await?;
        let session = me
            .inner
            .matrix_auth()
            .session()
            .ok_or_else(|| Error::Other("SSO login finished but no session present".into()))?;
        let stored = StoredSession {
            homeserver: resolved,
            session,
            store_path: store_path.to_path_buf(),
            store_passphrase: passphrase.to_string(),
        };
        Ok((me, stored))
    }

    /// The SSO login URL for a homeserver (a bare server-name is `.well-known`
    /// discovered first), for clients that drive the browser/redirect themselves
    /// rather than via [`Self::login_sso`]. `redirect_url` is where the homeserver
    /// returns the `loginToken` after the user authenticates.
    pub async fn sso_login_url(
        homeserver: &str,
        store_path: &Path,
        passphrase: &str,
        redirect_url: &str,
    ) -> Result<String> {
        let me = Self::build(homeserver, store_path, passphrase).await?;
        Ok(me
            .inner
            .matrix_auth()
            .get_sso_login_url(redirect_url, None)
            .await?)
    }

    /// Rebuild an authenticated client from a previously persisted session.
    pub async fn restore(stored: &StoredSession) -> Result<Self> {
        let me = Self::build(
            &stored.homeserver,
            &stored.store_path,
            &stored.store_passphrase,
        )
        .await?;
        me.inner.restore_session(stored.session.clone()).await?;
        Ok(me)
    }

    /// Run a single sync round-trip (state + encrypted events flow into the
    /// store). Cheap, deterministic — ideal for the headless CLI and tests.
    pub async fn sync_once(&self) -> Result<()> {
        self.inner.sync_once(SyncSettings::default()).await?;
        Ok(())
    }

    /// Run the continuous sync loop. Never returns except on error. This is what
    /// the long-lived comms-PD drives.
    pub async fn sync_forever(&self) -> Result<()> {
        self.inner.sync(SyncSettings::default()).await?;
        Ok(())
    }

    /// List joined rooms as flat [`RoomSummary`] values.
    pub async fn joined_rooms(&self) -> Result<Vec<RoomSummary>> {
        let mut out = Vec::new();
        for room in self.inner.joined_rooms() {
            // `display_name` resolves the room name, or computes one from members
            // (the Matrix heroes algorithm) for unnamed/DM rooms.
            let display_name = match room.display_name().await {
                Ok(name) => name.to_string(),
                Err(_) => room.room_id().to_string(),
            };
            out.push(RoomSummary {
                room_id: room.room_id().to_owned(),
                display_name,
                topic: room.topic(),
                is_encrypted: room.encryption_state().is_encrypted(),
                is_space: room.is_space(),
                is_direct: room.is_direct().await.unwrap_or(false),
                joined_members: room.joined_members_count(),
                unread_notifications: room.unread_notification_counts().notification_count,
            });
        }
        // Stable, human-friendly ordering by display name.
        out.sort_by(|a, b| {
            a.display_name
                .to_lowercase()
                .cmp(&b.display_name.to_lowercase())
        });
        Ok(out)
    }

    /// Read the most recent `limit` messages of a room (text projection).
    ///
    /// This uses the SDK's `messages` pagination (backward from the live edge).
    /// The richer [`matrix_sdk_ui::Timeline`] (edits/reactions/threads folded in)
    /// is the UI-phase upgrade; the headless core only needs the raw recent
    /// message bodies to prove the protocol path end to end.
    pub async fn recent_timeline(&self, room_id: &str, limit: u16) -> Result<Vec<TimelineMessage>> {
        let room_id = matrix_sdk::ruma::RoomId::parse(room_id)?;
        let room = self
            .inner
            .get_room(&room_id)
            .ok_or_else(|| Error::Other(format!("not a joined room: {room_id}")))?;
        if room.state() != RoomState::Joined {
            return Err(Error::Other(format!("room {room_id} is not joined")));
        }

        let mut options = matrix_sdk::room::MessagesOptions::backward();
        options.limit = matrix_sdk::ruma::UInt::from(limit);
        // Only fetch room message events; cuts down deserialization noise.
        let mut filter = RoomEventFilter::default();
        filter.types = Some(vec!["m.room.message".to_string()]);
        options.filter = filter;

        let response = room.messages(options).await?;

        let mut out = Vec::new();
        for ev in response.chunk {
            // `ev.raw()` is a serialized timeline event; the SDK has already
            // decrypted encrypted events into their cleartext form in the store.
            let Ok(any) = ev.raw().deserialize() else {
                continue;
            };
            if let AnySyncTimelineEvent::MessageLike(
                matrix_sdk::ruma::events::AnySyncMessageLikeEvent::RoomMessage(msg),
            ) = any
            {
                if let Some(original) = msg.as_original() {
                    let (body, kind) = match &original.content.msgtype {
                        MessageType::Text(t) => (t.body.clone(), MessageKind::Text),
                        MessageType::Emote(t) => (format!("* {}", t.body), MessageKind::Emote),
                        MessageType::Notice(t) => (t.body.clone(), MessageKind::Notice),
                        MessageType::Image(i) => (
                            format!("[image] {}", i.body),
                            MessageKind::Attachment("image".into()),
                        ),
                        MessageType::File(f) => (
                            format!("[file] {}", f.body),
                            MessageKind::Attachment("file".into()),
                        ),
                        MessageType::Audio(a) => (
                            format!("[audio] {}", a.body),
                            MessageKind::Attachment("audio".into()),
                        ),
                        MessageType::Video(v) => (
                            format!("[video] {}", v.body),
                            MessageKind::Attachment("video".into()),
                        ),
                        other => (format!("[{}]", other.msgtype()), MessageKind::Text),
                    };
                    // The deos-pilling: detect a membrane riding in the namespaced
                    // event key. A deos message carries the envelope under
                    // `MEMBRANE_EVENT_KEY` inside the message content; non-deos
                    // clients see only the text fallback. We extract it off the RAW
                    // event JSON (the typed `RoomMessageEventContent` has no slot for
                    // a custom field), parsing into the typed envelope. A malformed
                    // or future-version envelope is treated as absent (the message
                    // still renders as its text fallback — fail-open on render,
                    // fail-closed on rehydrate, which `is_rehydratable` enforces).
                    let raw_json = ev.raw().json().get();
                    let membrane = extract_membrane(raw_json);
                    // The generalized dregg object (any kind, under the new key).
                    // Fail-closed: an unknown/future object parses to None and the
                    // message renders as its text fallback.
                    let object = crate::object::DreggObject::extract(raw_json);
                    // The kind, in precedence: a membrane (either carrier) → Membrane;
                    // any other dregg object → Object(kind); else the m.room.message
                    // content kind.
                    let kind = match (&membrane, &object) {
                        (Some(_), _) => MessageKind::Membrane,
                        (None, Some(crate::object::DreggObject::Membrane(_))) => {
                            MessageKind::Membrane
                        }
                        (None, Some(obj)) => MessageKind::Object(obj.kind().to_string()),
                        (None, None) => kind,
                    };
                    // A membrane carried under the NEW object key surfaces in both the
                    // typed `membrane` field (back-compat) and `object`.
                    let membrane = membrane.or_else(|| match &object {
                        Some(crate::object::DreggObject::Membrane(env)) => Some(env.clone()),
                        _ => None,
                    });
                    let mut m = TimelineMessage::text(
                        original.event_id.to_string(),
                        original.sender.to_string(),
                        body,
                        u64::from(original.origin_server_ts.0),
                    );
                    m.kind = kind;
                    m.membrane = membrane;
                    m.object = object;
                    // Thread aggregation: an m.thread relation pins this message to its
                    // thread root (the timeline already models replies; threads are a
                    // relation read off the same raw event).
                    m.thread_root = extract_thread_root(raw_json);
                    m.reply_to = m.reply_to.or_else(|| extract_reply_to(raw_json));
                    out.push(m);
                }
            }
        }
        // `messages(backward)` yields newest-first; present oldest-first.
        out.reverse();
        Ok(out)
    }

    /// Resolve a joined [`matrix_sdk::Room`] for `room_id`, fail-closed if it is
    /// not a room we have joined (you cannot send into a room you are not in).
    async fn joined_room(&self, room_id: &str) -> Result<matrix_sdk::Room> {
        let room_id = matrix_sdk::ruma::RoomId::parse(room_id)?;
        let room = self
            .inner
            .get_room(&room_id)
            .ok_or_else(|| Error::Other(format!("not a joined room: {room_id}")))?;
        if room.state() != RoomState::Joined {
            return Err(Error::Other(format!("room {room_id} is not joined")));
        }
        Ok(room)
    }

    /// Send a plain-text message to `room_id`, returning the server-assigned event
    /// id. If the room is encrypted, the SDK transparently encrypts the event
    /// (the default `e2e-encryption` feature). This is the live counterpart to the
    /// mock's local-append `send`.
    pub async fn send_text(&self, room_id: &str, body: &str) -> Result<String> {
        let room = self.joined_room(room_id).await?;
        let content = RoomMessageEventContent::text_plain(body);
        let resp = room.send(content).await?;
        Ok(resp.response.event_id.to_string())
    }

    /// Send a **membrane-bearing** message to `room_id`. The membrane rides as a
    /// custom field ([`MEMBRANE_EVENT_KEY`]) inside an ordinary `m.room.message`,
    /// so a non-deos client sees the human `text_fallback` while a deos client
    /// extracts the envelope (see [`Self::recent_timeline`]). Returns the event id.
    ///
    /// Wire shape (the deos-pilling, additive over plain Matrix):
    /// ```json
    /// {
    ///   "msgtype": "m.text",
    ///   "body": "[deos membrane · N cells · root … · cut@hK]",
    ///   "software.ember.deos.membrane": { ...MembraneEnvelope... }
    /// }
    /// ```
    pub async fn send_membrane(
        &self,
        room_id: &str,
        body: &str,
        membrane: &MembraneEnvelope,
    ) -> Result<String> {
        let room = self.joined_room(room_id).await?;
        let fallback = if body.trim().is_empty() {
            membrane.text_fallback()
        } else {
            body.to_string()
        };
        // Build the m.room.message content, then splice the namespaced membrane
        // field in. `send_raw` lets us carry the custom key the typed
        // RoomMessageEventContent has no slot for.
        let mut content = serde_json::to_value(RoomMessageEventContent::text_plain(&fallback))?;
        let obj = content
            .as_object_mut()
            .ok_or_else(|| Error::Other("message content was not a JSON object".into()))?;
        obj.insert(
            MEMBRANE_EVENT_KEY.to_string(),
            serde_json::to_value(membrane)?,
        );
        let resp = room.send_raw("m.room.message", content).await?;
        Ok(resp.response.event_id.to_string())
    }

    // -- the nheko-comfort feature surface ------------------------------------
    // Spaces, media, room directory, invites, power levels — built on the live
    // SDK so a heavy user is at home on his own homeserver.

    /// Send a **dregg semantic object** (any [`crate::object::DreggObject`] kind) to
    /// `room_id`. The object rides under `software.ember.deos.object` inside a normal
    /// `m.room.message` with a human `body` fallback (so non-deos clients read it),
    /// exactly like [`Self::send_membrane`] but generalized to all kinds. Returns
    /// the event id.
    pub async fn send_object(
        &self,
        room_id: &str,
        body: &str,
        object: &crate::object::DreggObject,
    ) -> Result<String> {
        let room = self.joined_room(room_id).await?;
        let content = object.to_message_content(body);
        let resp = room.send_raw("m.room.message", content).await?;
        Ok(resp.response.event_id.to_string())
    }

    /// Send a **media attachment** (image/file/audio/video) to `room_id`. The
    /// content type is guessed from `filename` if not given; the SDK uploads the
    /// bytes (encrypting them transparently in an encrypted room) and posts the
    /// matching `m.image`/`m.file`/`m.audio`/`m.video` event. Returns the event id.
    pub async fn send_attachment(
        &self,
        room_id: &str,
        filename: &str,
        content_type: Option<&str>,
        data: Vec<u8>,
    ) -> Result<String> {
        use matrix_sdk::attachment::AttachmentConfig;
        let room = self.joined_room(room_id).await?;
        let mime: mime::Mime = match content_type {
            Some(ct) => ct
                .parse()
                .map_err(|_| Error::Other(format!("invalid content type: {ct}")))?,
            None => mime_guess::from_path(filename).first_or_octet_stream(),
        };
        let resp = room
            .send_attachment(filename, &mime, data, AttachmentConfig::new())
            .await?;
        Ok(resp.event_id.to_string())
    }

    /// Fetch the bytes of a media event (`m.image`/`m.file`/…) by its `mxc://` URI.
    /// Decrypts transparently for encrypted rooms. The UI hands these to its
    /// existing RGBA/image path (an image) or an attachment row (a file).
    pub async fn fetch_media(&self, mxc_uri: &str) -> Result<Vec<u8>> {
        use matrix_sdk::media::{MediaFormat, MediaRequestParameters};
        use matrix_sdk::ruma::events::room::MediaSource;
        let uri = matrix_sdk::ruma::OwnedMxcUri::from(mxc_uri);
        let request = MediaRequestParameters {
            source: MediaSource::Plain(uri),
            format: MediaFormat::File,
        };
        Ok(self.inner.media().get_media_content(&request, true).await?)
    }

    /// List the joined **spaces** (rooms with `m.room.type = m.space`) as
    /// [`SpaceSummary`], each with the room ids of its joined children (read from
    /// the space's `m.space.child` state events). This is the room hierarchy a heavy
    /// user navigates by.
    pub async fn spaces(&self) -> Result<Vec<SpaceSummary>> {
        use matrix_sdk::ruma::events::space::child::SpaceChildEventContent;
        let mut out = Vec::new();
        for room in self.inner.joined_rooms() {
            if !room.is_space() {
                continue;
            }
            let name = room
                .display_name()
                .await
                .map(|n| n.to_string())
                .unwrap_or_else(|_| room.room_id().to_string());
            // The space's children: each m.space.child state event keys a child room.
            let mut children = Vec::new();
            if let Ok(events) = room
                .get_state_events_static::<SpaceChildEventContent>()
                .await
            {
                for raw in events {
                    if let Ok(state) = raw.deserialize() {
                        // The state_key of an m.space.child IS the child room id.
                        children.push(state.state_key().to_string());
                    }
                }
            }
            out.push(SpaceSummary {
                room_id: room.room_id().to_owned(),
                display_name: name,
                child_room_ids: children,
            });
        }
        out.sort_by(|a, b| {
            a.display_name
                .to_lowercase()
                .cmp(&b.display_name.to_lowercase())
        });
        Ok(out)
    }

    /// Search the homeserver's **public room directory** for up to `limit` rooms
    /// matching `query` (an empty query lists popular rooms). Returns flat
    /// [`PublicRoom`] descriptions a user can join by id/alias.
    pub async fn search_public_rooms(
        &self,
        query: Option<&str>,
        limit: u16,
    ) -> Result<Vec<PublicRoom>> {
        use matrix_sdk::room_directory_search::RoomDirectorySearch;
        let mut search = RoomDirectorySearch::new(self.inner.clone());
        search
            .search(query.map(|q| q.to_string()), limit as u32, None)
            .await?;
        // `results()` yields the current snapshot vector (plus an update stream we
        // don't need for a one-shot search).
        let (results, _stream) = search.results();
        Ok(results
            .into_iter()
            .map(|d| PublicRoom {
                room_id: d.room_id.to_string(),
                name: d.name,
                topic: d.topic,
                alias: d.alias.map(|a| a.to_string()),
                joined_members: d.joined_members,
                world_readable: d.is_world_readable,
            })
            .collect())
    }

    /// Join a room by its id or alias (`!abc:server` or `#room:server`). Returns the
    /// joined room's id.
    /// **Create a room** (optionally inviting users) and return its room id. The
    /// creator joins automatically. `name`/`topic` set the room's display metadata;
    /// `invites` are full `@user:server` ids to invite at creation. This is the
    /// path a deos user takes to open a fresh conversation (and the harness path the
    /// live test uses to stand up a two-user room). Encryption is NOT forced here —
    /// the SDK creates an unencrypted room unless the server defaults otherwise.
    pub async fn create_room(
        &self,
        name: Option<&str>,
        topic: Option<&str>,
        invites: &[&str],
    ) -> Result<String> {
        use matrix_sdk::ruma::api::client::room::create_room::v3::Request as CreateRoomRequest;
        let mut request = CreateRoomRequest::new();
        request.name = name.map(|n| n.to_string());
        request.topic = topic.map(|t| t.to_string());
        let mut invite_ids = Vec::with_capacity(invites.len());
        for u in invites {
            invite_ids.push(UserId::parse(u)?.to_owned());
        }
        request.invite = invite_ids;
        let room = self.inner.create_room(request).await?;
        Ok(room.room_id().to_string())
    }

    pub async fn join(&self, id_or_alias: &str) -> Result<String> {
        let room = if id_or_alias.starts_with('#') {
            let alias = matrix_sdk::ruma::RoomOrAliasId::parse(id_or_alias)?;
            self.inner.join_room_by_id_or_alias(&alias, &[]).await?
        } else {
            let id = matrix_sdk::ruma::RoomId::parse(id_or_alias)?;
            self.inner.join_room_by_id(&id).await?
        };
        Ok(room.room_id().to_string())
    }

    /// List rooms we've been **invited** to (each a pending accept/reject decision).
    pub async fn invited_rooms(&self) -> Result<Vec<RoomSummary>> {
        let mut out = Vec::new();
        for room in self.inner.invited_rooms() {
            let display_name = room
                .display_name()
                .await
                .map(|n| n.to_string())
                .unwrap_or_else(|_| room.room_id().to_string());
            out.push(RoomSummary {
                room_id: room.room_id().to_owned(),
                display_name,
                topic: room.topic(),
                is_encrypted: room.encryption_state().is_encrypted(),
                is_space: room.is_space(),
                is_direct: room.is_direct().await.unwrap_or(false),
                joined_members: room.joined_members_count(),
                unread_notifications: 0,
            });
        }
        out.sort_by(|a, b| {
            a.display_name
                .to_lowercase()
                .cmp(&b.display_name.to_lowercase())
        });
        Ok(out)
    }

    /// **Accept** a room invite (join it). Returns the joined room id.
    pub async fn accept_invite(&self, room_id: &str) -> Result<String> {
        let id = matrix_sdk::ruma::RoomId::parse(room_id)?;
        let room = self
            .inner
            .get_room(&id)
            .ok_or_else(|| Error::Other(format!("no invite for room: {room_id}")))?;
        room.join().await?;
        Ok(room.room_id().to_string())
    }

    /// **Reject** a room invite (leave the invited room).
    pub async fn reject_invite(&self, room_id: &str) -> Result<()> {
        let id = matrix_sdk::ruma::RoomId::parse(room_id)?;
        let room = self
            .inner
            .get_room(&id)
            .ok_or_else(|| Error::Other(format!("no invite for room: {room_id}")))?;
        room.leave().await?;
        Ok(())
    }

    /// Invite a user (`@them:server`) into a joined room.
    pub async fn invite_user(&self, room_id: &str, user_id: &str) -> Result<()> {
        let room = self.joined_room(room_id).await?;
        let uid = UserId::parse(user_id)?;
        room.invite_user_by_id(&uid).await?;
        Ok(())
    }

    /// Read a room's **power levels** as a flat [`RoomPower`] (the basic room
    /// settings a heavy user inspects: who can post/invite/kick, default levels).
    pub async fn power_levels(&self, room_id: &str) -> Result<RoomPower> {
        let room = self.joined_room(room_id).await?;
        let pl = room
            .power_levels()
            .await
            .map_err(|e| Error::Other(format!("power levels: {e}")))?;
        let me = self.inner.user_id().map(|u| u.to_owned());
        // `for_user` yields a `UserPowerLevel` (Int | Infinite); a room admin can be
        // Infinite (room creator) — represent that as i64::MAX for display.
        let my_level = match me.as_ref().map(|u| pl.for_user(u)) {
            Some(matrix_sdk::ruma::events::room::power_levels::UserPowerLevel::Int(i)) => i.into(),
            Some(matrix_sdk::ruma::events::room::power_levels::UserPowerLevel::Infinite) => {
                i64::MAX
            }
            Some(_) => i64::from(pl.users_default),
            None => i64::from(pl.users_default),
        };
        Ok(RoomPower {
            users_default: pl.users_default.into(),
            invite: pl.invite.into(),
            kick: pl.kick.into(),
            ban: pl.ban.into(),
            redact: pl.redact.into(),
            my_level,
        })
    }

    /// Set a user's power level in a room (basic room admin). Requires us to hold
    /// enough authority; fails closed on the server otherwise.
    pub async fn set_power_level(&self, room_id: &str, user_id: &str, level: i64) -> Result<()> {
        let room = self.joined_room(room_id).await?;
        let uid = UserId::parse(user_id)?;
        room.update_power_levels(vec![(&uid, matrix_sdk::ruma::Int::new_saturating(level))])
            .await?;
        Ok(())
    }

    /// The logged-in user's **device id** (what other devices verify against).
    pub fn device_id(&self) -> Option<String> {
        self.inner.device_id().map(|d| d.to_string())
    }

    /// Whether key **backup** is currently enabled (so a heavy user knows their
    /// keys survive a device loss).
    pub async fn backup_enabled(&self) -> bool {
        self.inner.encryption().backups().are_enabled().await
    }

    /// Enable **key recovery** (cross-signing + secret-storage + server-side key
    /// backup), returning the recovery key the user must store. This is what makes
    /// "I logged in on a new device and got all my history back" work.
    pub async fn enable_recovery(&self) -> Result<String> {
        let recovery = self.inner.encryption().recovery();
        let key = recovery
            .enable()
            .await
            .map_err(|e| Error::Other(format!("enable recovery: {e}")))?;
        Ok(key)
    }

    /// **Recover** keys on a new device from a previously-issued recovery key.
    pub async fn recover(&self, recovery_key: &str) -> Result<()> {
        self.inner
            .encryption()
            .recovery()
            .recover(recovery_key)
            .await
            .map_err(|e| Error::Other(format!("recover: {e}")))
    }

    /// The person-level trust ([`crate::cell::PersonTrust`]) of a user, READ from
    /// the crypto store's cross-signing state ("verify the person, not the device").
    /// This is the live counterpart to the mock's seeded trust.
    pub async fn person_trust(&self, user_id: &str) -> crate::cell::PersonTrust {
        use crate::cell::PersonTrust;
        let Ok(uid) = UserId::parse(user_id) else {
            return PersonTrust::Unverified;
        };
        match self.inner.encryption().get_user_identity(&uid).await {
            Ok(Some(identity)) => {
                if identity.is_verified() {
                    PersonTrust::Verified
                } else if identity.was_previously_verified() {
                    // We verified this identity before and the master key CHANGED —
                    // the loud, must-surface case (a possible MITM).
                    PersonTrust::Changed
                } else {
                    PersonTrust::Unverified
                }
            }
            _ => PersonTrust::Unverified,
        }
    }

    /// The logged-in user's full id, if any.
    pub fn user_id(&self) -> Option<&UserId> {
        self.inner.user_id()
    }

    /// Borrow the underlying SDK client (for the worker bridge / UI layer).
    pub fn sdk(&self) -> &Client {
        &self.inner
    }

    /// The active SDK session, if logged in (for re-persisting after token refresh).
    pub fn session(&self) -> Option<MatrixSession> {
        self.inner.matrix_auth().session()
    }
}

/// Extract a [`MembraneEnvelope`] from the raw JSON of an `m.room.message` event,
/// if it carries one under [`MEMBRANE_EVENT_KEY`] inside its `content`. Returns
/// `None` for a plain message, malformed envelope, or a wire version this build
/// cannot rehydrate (forward-compat: an unrehydratable envelope is rendered as
/// its text fallback, never half-trusted).
///
/// This is the receive half of [`MatrixClient::send_membrane`]'s wire shape — the
/// SAME custom-content field, round-tripped through a real homeserver.
pub(crate) fn extract_membrane(raw_json: &str) -> Option<MembraneEnvelope> {
    let value: serde_json::Value = serde_json::from_str(raw_json).ok()?;
    let field = value.get("content")?.get(MEMBRANE_EVENT_KEY)?;
    let env: MembraneEnvelope = serde_json::from_value(field.clone()).ok()?;
    env.is_rehydratable().then_some(env)
}

/// Extract the thread-root event id from a message's `m.relates_to` `m.thread`
/// relation (`content.m.relates_to.event_id` when `rel_type == "m.thread"`). The
/// timeline already models replies; this folds in thread aggregation off the same
/// raw event JSON. Returns `None` for a non-threaded message.
pub(crate) fn extract_thread_root(raw_json: &str) -> Option<String> {
    let value: serde_json::Value = serde_json::from_str(raw_json).ok()?;
    let relates = value.get("content")?.get("m.relates_to")?;
    if relates.get("rel_type")?.as_str()? != "m.thread" {
        return None;
    }
    Some(relates.get("event_id")?.as_str()?.to_string())
}

/// Extract the reply pointer from a message's `m.relates_to.m.in_reply_to`
/// relation, off the raw event JSON (the headless projection has no member/event
/// lookup, so the preview is left empty — the SDK-UI Timeline fills it; this at
/// least surfaces the reply pointer so threads/replies render).
pub(crate) fn extract_reply_to(raw_json: &str) -> Option<ReplyTo> {
    let value: serde_json::Value = serde_json::from_str(raw_json).ok()?;
    let in_reply = value
        .get("content")?
        .get("m.relates_to")?
        .get("m.in_reply_to")?;
    let event_id = in_reply.get("event_id")?.as_str()?.to_string();
    Some(ReplyTo {
        event_id,
        sender: String::new(),
        preview: String::new(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The membrane wire shape round-trips through the same JSON an `m.room.message`
    /// carries on the wire: `send_membrane` splices the envelope under the
    /// namespaced key inside `content`, and `extract_membrane` pulls it back out.
    /// This proves the SEND and RECEIVE halves agree on the format WITHOUT a live
    /// server (the live server merely carries this JSON verbatim).
    #[test]
    fn membrane_survives_the_room_message_wire_shape() {
        let env = crate::membrane::MockMembraneHost::sample_envelope();
        // Reproduce exactly what send_membrane builds for the wire.
        let mut content =
            serde_json::to_value(RoomMessageEventContent::text_plain(env.text_fallback())).unwrap();
        content.as_object_mut().unwrap().insert(
            MEMBRANE_EVENT_KEY.to_string(),
            serde_json::to_value(&env).unwrap(),
        );
        // Wrap it as a full m.room.message event the way the homeserver returns it.
        let event = serde_json::json!({
            "type": "m.room.message",
            "event_id": "$abc:deos.local",
            "sender": "@grok:deos.local",
            "origin_server_ts": 1_718_000_000_000u64,
            "content": content,
        });
        let extracted = extract_membrane(&event.to_string()).expect("membrane round-trips");
        assert_eq!(extracted, env);
    }

    /// A plain message carries no membrane (the common case stays clean).
    #[test]
    fn plain_message_has_no_membrane() {
        let event = serde_json::json!({
            "type": "m.room.message",
            "content": { "msgtype": "m.text", "body": "hello" },
        });
        assert!(extract_membrane(&event.to_string()).is_none());
    }

    /// A future wire version fails closed at extraction (rendered as text, never
    /// half-rehydrated).
    #[test]
    fn future_version_membrane_is_not_extracted() {
        let mut env = crate::membrane::MockMembraneHost::sample_envelope();
        env.version = MembraneEnvelope::VERSION + 1;
        let event = serde_json::json!({
            "type": "m.room.message",
            "content": {
                "msgtype": "m.text",
                "body": env.text_fallback(),
                MEMBRANE_EVENT_KEY: serde_json::to_value(&env).unwrap(),
            },
        });
        assert!(extract_membrane(&event.to_string()).is_none());
    }
}
