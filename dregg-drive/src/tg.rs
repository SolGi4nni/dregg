//! **The REAL Telegram surface, driven.**
//!
//! Nothing here re-implements Telegram. A command goes into `dreggnet_telegram::runtime`'s own
//! `route_text` / `route_callback` — the identical two functions the live update loop calls after
//! `parse_updates` decodes a Bot API body — over a real `TelegramHost` built by the same
//! `durable_telegram_host` constructor the deployed bot uses. What comes back out is read off the
//! `Transport` as `SendMessageRequest`s, whose serde encoding IS the Bot API wire body.
//!
//! ## The one thing this crate adds to the existing test seam
//!
//! [`DriveTransport`] records **whether each paint was a SEND or an EDIT**. `MockTransport` keeps
//! both in one `sent` list, and that is enough for a privacy transcript but not for a UX one: a
//! second `/offerings` that EDITS a message far up the scrollback and a second `/offerings` that
//! posts a fresh menu are the same entry there and completely different experiences. The
//! adapter's own comment says the rule out loud — *"OPENING reposts; PLAYING edits in place …
//! DMs ONLY"* — so a collective chat is a different case and the driver has to be able to see
//! which one it is looking at.
//!
//! ## The unreachable inch, named
//!
//! `api.telegram.org` itself. `RawBotApi`'s composition is pure and its byte seam (`HttpPost`) is
//! unfilled here, so the URL and body are real and the POST does not happen. Everything from
//! `route_*` inward — identity derivation, surface→keyboard, callback→Action, the executor, the
//! durable store, the game-epoch authority — is the deployed code.

use std::collections::HashMap;
use std::path::PathBuf;

use dreggnet_catalog::{GameEpochLedger, PlayerWorlds};
use dreggnet_offerings::SessionId;
use dreggnet_telegram::api::{SendMessageRequest, decode_callback, encode_callback};
use dreggnet_telegram::host::TelegramHost;
use dreggnet_telegram::runtime::{durable_telegram_host, route_callback, route_text};
use dreggnet_telegram::transport::{MessageId, Transport, TransportError};
use dreggnet_telegram::{CallbackQuery, ChatKind, TelegramFrontend};

use crate::out::{Control, Frame, Paint, PaintHow, pills_in_text};
use crate::surface::{DrivenSurface, uid_of};

/// A deterministic bot secret. A real deploy derives 32 bytes from its environment; a driver
/// wants the SAME derived identities on every run so `--as alice` is one person forever.
const BOT_SECRET: [u8; 32] = [0x1d; 32];

/// Whether a paint created a message or rewrote one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Send,
    Edit,
}

/// One recorded paint.
#[derive(Debug, Clone)]
struct Recorded {
    kind: Kind,
    message_id: i64,
    req: SendMessageRequest,
}

/// **A recording transport that keeps the send/edit distinction.** Otherwise identical in
/// behaviour to `dreggnet_telegram::transport::MockTransport`: a real in-place edit keeps the
/// message id, every version stays in the log (a group member read each one as it was posted),
/// and `visible` is what a message currently shows.
#[derive(Debug, Default)]
pub struct DriveTransport {
    log: Vec<Recorded>,
    visible: HashMap<i64, SendMessageRequest>,
    next_id: i64,
}

impl DriveTransport {
    fn new() -> Self {
        DriveTransport {
            log: Vec::new(),
            visible: HashMap::new(),
            next_id: 1,
        }
    }

    /// How many paints have happened — the mark a frame diffs against.
    fn mark(&self) -> usize {
        self.log.len()
    }

    /// What a live message currently shows.
    fn visible(&self, id: i64) -> Option<&SendMessageRequest> {
        self.visible.get(&id)
    }
}

impl Transport for DriveTransport {
    fn send_message(&mut self, req: &SendMessageRequest) -> Result<MessageId, TransportError> {
        let id = self.next_id;
        self.next_id += 1;
        self.log.push(Recorded {
            kind: Kind::Send,
            message_id: id,
            req: req.clone(),
        });
        self.visible.insert(id, req.clone());
        Ok(MessageId(id))
    }

    fn edit_message(
        &mut self,
        message_id: MessageId,
        req: &SendMessageRequest,
    ) -> Result<MessageId, TransportError> {
        self.log.push(Recorded {
            kind: Kind::Edit,
            message_id: message_id.0,
            req: req.clone(),
        });
        self.visible.insert(message_id.0, req.clone());
        Ok(message_id)
    }
}

/// A control set as it stood in one frame, plus the message it is attached to — because a press
/// addresses a MESSAGE, and after a restart the message is still on the screen while the bot's
/// index of it is not.
#[derive(Debug, Clone, Default)]
struct Offered {
    message_id: Option<i64>,
    controls: Vec<Control>,
}

/// The driven Telegram surface.
pub struct TgDriver {
    dir: PathBuf,
    chat: i64,
    topic: Option<i64>,
    key: String,
    viewer: String,
    uid: u64,
    host: Option<TelegramHost<DriveTransport>>,
    current: Offered,
    previous: Offered,
    restarts: usize,
}

impl TgDriver {
    /// Build the driver over a durable state directory. `chat` decides the audience: a positive
    /// id is a DM (single reader), a negative one a group (one message every member reads) — and
    /// the adapter's repost-vs-edit rule differs between them, so this is a real dial.
    pub fn new(
        dir: PathBuf,
        chat: i64,
        topic: Option<i64>,
        key: &str,
        viewer: &str,
    ) -> Result<Self, String> {
        std::fs::create_dir_all(dir.join("sessions"))
            .map_err(|e| format!("cannot create {}: {e}", dir.join("sessions").display()))?;
        let host = build_host(&dir)?;
        Ok(TgDriver {
            dir,
            chat,
            topic,
            key: key.to_string(),
            viewer: viewer.to_string(),
            uid: uid_of(viewer),
            host: Some(host),
            current: Offered::default(),
            previous: Offered::default(),
            restarts: 0,
        })
    }

    fn host(&mut self) -> &mut TelegramHost<DriveTransport> {
        self.host
            .as_mut()
            .expect("the host is only absent mid-restart")
    }

    fn sid(&self) -> SessionId {
        TelegramFrontend::<DriveTransport>::session_id(self.chat, self.topic)
    }

    fn surface_sid(&self) -> SessionId {
        TelegramFrontend::<DriveTransport>::surface_id(self.chat, self.topic, &self.key)
    }

    /// Run `body`, then read every paint it caused off the transport and build the frame.
    fn frame(
        &mut self,
        verb: &str,
        body: impl FnOnce(&mut TelegramHost<DriveTransport>) -> Option<String>,
    ) -> Frame {
        let mark = self.host().frontend().transport().mark();
        let reply = body(self.host());
        let mut frame = Frame::new(verb);
        frame.reply = reply;

        let paints: Vec<Recorded> = self.host().frontend().transport().log[mark..].to_vec();
        for rec in &paints {
            let what = format!(
                "message #{} in chat {}{}",
                rec.message_id,
                rec.req.chat_id,
                rec.req
                    .message_thread_id
                    .map(|t| format!(" topic {t}"))
                    .unwrap_or_default()
            );
            frame.paints.push(Paint {
                how: match rec.kind {
                    Kind::Send => PaintHow::Fresh(what),
                    Kind::Edit => PaintHow::InPlace(what),
                },
                body: rec.req.text.clone(),
            });
        }

        // Controls: whatever keyboard the viewer is looking at NOW. The last paint that carried
        // one is the honest answer (it may be the offerings MENU, not the game — say which);
        // with no paint at all, the offering's own live message still stands on screen.
        let offered = self.read_offered(&paints);
        let surface_sid = self.surface_sid();
        let live_msg = self
            .host()
            .frontend()
            .session(&surface_sid)
            .and_then(|s| s.message_id)
            .map(|m| m.0);
        if let (Some(id), Some(live)) = (offered.message_id, live_msg)
            && id != live
        {
            frame.note(format!(
                "ℹ the controls above belong to message #{id}, which is NOT the {} surface \
                 message (#{live}). Two live keyboards in one chat.",
                self.key,
            ));
        }
        frame.controls = offered.controls.clone();
        if !frame.paints.is_empty() {
            frame.pills = pills_in_text(&frame.paints[frame.paints.len() - 1].body);
        }
        self.previous = std::mem::replace(&mut self.current, offered);
        frame.flag_silence();
        frame
    }

    /// Read the controls the viewer can press: from the last keyboard-bearing paint of this
    /// command if there was one, else from the offering's own live message.
    fn read_offered(&mut self, paints: &[Recorded]) -> Offered {
        if let Some(rec) = paints
            .iter()
            .rev()
            .find(|r| r.req.chat_id == self.chat && r.req.reply_markup.is_some())
        {
            return Offered {
                message_id: Some(rec.message_id),
                controls: controls_of(&rec.req),
            };
        }
        let surface = self.surface_sid();
        let live = self
            .host()
            .frontend()
            .session(&surface)
            .and_then(|s| s.message_id)
            .map(|m| m.0);
        let found = live.and_then(|id| {
            self.host()
                .frontend()
                .transport()
                .visible(id)
                .map(|req| (id, controls_of(req)))
        });
        match found {
            Some((id, controls)) => Offered {
                message_id: Some(id),
                controls,
            },
            // Nothing this process painted. Whatever was on the screen BEFORE is still on the
            // screen — that is the post-restart situation, and it must stay pressable.
            None => self.current.clone(),
        }
    }

    fn fire(&mut self, verb: &str, from: Offered, index: usize) -> Frame {
        let Some(control) = from.controls.get(index).cloned() else {
            return Frame::driver_note(
                verb,
                format!(
                    "no control at index {index} — {} on offer. `controls` lists them.",
                    from.controls.len()
                ),
            );
        };
        let query = match from.message_id {
            Some(id) => CallbackQuery::press_on_message(
                self.chat,
                MessageId(id),
                self.uid,
                control.wire.clone(),
            ),
            None => CallbackQuery::press(self.chat, self.uid, control.wire.clone()),
        };
        let mut frame = self.frame(verb, |h| Some(route_callback(h, query)));
        frame.note(format!(
            "pressed “{}” ({}/{}) on message #{}",
            control.label,
            control.turn,
            control.arg,
            from.message_id
                .map(|i| i.to_string())
                .unwrap_or_else(|| "?".into())
        ));
        frame
    }
}

/// The keyboard of one message, as offered controls. A Mini App launch button carries no
/// `callback_data` at all and can never be pressed from here — it is surfaced with that said.
fn controls_of(req: &SendMessageRequest) -> Vec<Control> {
    let mut out = Vec::new();
    let Some(markup) = &req.reply_markup else {
        return out;
    };
    for button in markup.inline_keyboard.iter().flatten() {
        let index = out.len();
        if let Some(app) = &button.web_app {
            out.push(Control {
                index,
                label: format!("{} [MINI APP → {}]", button.text, app.url),
                turn: "(web_app)".into(),
                arg: 0,
                enabled: false,
                wire: String::new(),
            });
            continue;
        }
        // A `!enabled` affordance is rendered with the lock glyph but is still PRESSABLE — the
        // cap tooth shown, not hidden. Report it dimmed and let the driver press it anyway.
        let dimmed = button.text.starts_with(dreggnet_telegram::api::LOCK_GLYPH);
        let (turn, arg) =
            decode_callback(&button.callback_data).unwrap_or_else(|| ("(opaque)".to_string(), 0));
        out.push(Control {
            index,
            label: button.text.clone(),
            turn,
            arg,
            enabled: !dimmed,
            wire: button.callback_data.clone(),
        });
    }
    out
}

fn build_host(dir: &PathBuf) -> Result<TelegramHost<DriveTransport>, String> {
    let sessions = dir.join("sessions");
    let epochs = GameEpochLedger::open(dir.join("epochs"))
        .map_err(|e| format!("cannot open the durable game-epoch ledger: {e}"))?;
    Ok(TelegramHost::with_hosts_and_game_epochs(
        BOT_SECRET,
        DriveTransport::new(),
        move || durable_telegram_host(Some(sessions), vec![]),
        PlayerWorlds::new,
        epochs,
    ))
}

impl DrivenSurface for TgDriver {
    fn provenance(&self) -> String {
        let kind = ChatKind::classify(self.chat, self.topic);
        format!(
            "telegram — REAL. `route_text`/`route_callback` (the live update loop's own routers) \
             over a real `TelegramHost` from `durable_telegram_host`, durable store {store}. \
             Chat {chat} is a {kind:?}{collective}. UNREACHABLE: the POST to api.telegram.org \
             (the `HttpPost` byte seam is unfilled); the request URL + body are composed for real \
             and not sent.",
            store = self.dir.join("sessions").display(),
            chat = self.chat,
            collective = if kind.is_collective() {
                " — ONE message every member reads, and a re-present EDITS it"
            } else {
                " — single reader, and an open REPOSTS"
            }
        )
    }

    fn open(&mut self) -> Frame {
        let cmd = format!("/open {}", self.key);
        let (chat, topic, uid) = (self.chat, self.topic, self.uid);
        let mut frame = self.frame("open", |h| route_text(h, chat, topic, uid, &cmd));
        frame.note(format!("routed the real text command `{cmd}`"));
        frame
    }

    fn again(&mut self) -> Frame {
        let cmd = format!("/open {}", self.key);
        let (chat, topic, uid) = (self.chat, self.topic, self.uid);
        let mut frame = self.frame("again", |h| route_text(h, chat, topic, uid, &cmd));
        frame.note(
            "`again` re-issues the SAME open. On this surface an open is supposed to REPOST in a \
             DM and EDIT in a collective chat — check the PAINT line against the chat kind.",
        );
        frame
    }

    fn press(&mut self, index: usize) -> Frame {
        let from = self.current.clone();
        self.fire("press", from, index)
    }

    fn press_stale(&mut self, index: usize) -> Frame {
        let from = self.previous.clone();
        if from.controls.is_empty() {
            return Frame::driver_note("stale", "no previous frame to press from yet.");
        }
        let mut frame = self.fire("stale", from, index);
        frame.note(
            "this was a control from the PREVIOUS frame — still on the user's screen, no longer \
             the current keyboard. A refusal here must SAY what to do next.",
        );
        frame
    }

    fn act(&mut self, turn: &str, arg: i64) -> Frame {
        let data = encode_callback(turn, arg);
        let query = CallbackQuery::press(self.chat, self.uid, data.clone());
        let mut frame = self.frame("act", |h| Some(route_callback(h, query)));
        frame.note(format!(
            "fired raw callback_data `{data}` with no message address (routes to the chat's most \
             recent surface). NOTE: a spined game key's real buttons carry an OPAQUE bound \
             digest, not `turn:arg` — a hand-built `turn:arg` is a payload the frontend never \
             minted, and being refused is correct.",
        ));
        frame
    }

    fn send(&mut self, text: &str) -> Frame {
        let (chat, topic, uid) = (self.chat, self.topic, self.uid);
        let owned = text.to_string();
        let mut frame = self.frame("send", |h| route_text(h, chat, topic, uid, &owned));
        frame.note(format!("routed the real text message `{text}`"));
        frame
    }

    fn become_viewer(&mut self, who: &str) -> Frame {
        let was = std::mem::replace(&mut self.viewer, who.to_string());
        self.uid = uid_of(who);
        let mut frame = Frame::new("as");
        frame.controls = self.current.controls.clone();
        frame.note(format!(
            "viewer {was} → {who} (telegram uid {}). NO state was touched: the session, the \
             durable log, and the messages on screen are exactly as they were.",
            self.uid
        ));
        frame
    }

    fn restart(&mut self) -> Frame {
        // Drop the host FIRST — the durable ledger must not be open twice, and a redeploy really
        // does tear the process down before the next one boots.
        let on_screen = self.current.clone();
        self.host = None;
        match build_host(&self.dir) {
            Ok(host) => {
                self.host = Some(host);
                self.restarts += 1;
                let mut frame = Frame::new("restart");
                // The messages did NOT vanish from the chat. Keep the control set: pressing it
                // now is exactly what a user does after a redeploy, and it is where the
                // dead-button class lives.
                self.current = on_screen.clone();
                self.previous = Offered::default();
                frame.controls = on_screen.controls.clone();
                frame.note(format!(
                    "RESTART #{n}: the host was dropped and rebuilt from {store}. In-memory \
                     state (the chat→session map, the message index, the transport log) is GONE. \
                     The {c} control(s) above are still on the user's screen — press one.",
                    n = self.restarts,
                    store = self.dir.join("sessions").display(),
                    c = on_screen.controls.len()
                ));
                frame
            }
            Err(why) => Frame::driver_note("restart", format!("could not rebuild the host: {why}")),
        }
    }

    fn verify(&mut self) -> Frame {
        let (chat, topic, uid) = (self.chat, self.topic, self.uid);
        let mut frame = self.frame("verify", |h| route_text(h, chat, topic, uid, "/verify"));
        let key = self.key.clone();
        let sid = self.sid();
        let report = self.host().verify(&key, &sid);
        frame.note(match report {
            Some(r) => format!(
                "host-side re-verify: verified={} turns={} — {}",
                r.verified, r.turns, r.detail
            ),
            None => "host-side re-verify: no live session under this key in this chat.".to_string(),
        });
        frame
    }

    fn controls(&self) -> Vec<Control> {
        self.current.controls.clone()
    }

    fn viewer(&self) -> String {
        self.viewer.clone()
    }
}
