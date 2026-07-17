//! # `TelegramHost` — the MULTI-OFFERING Telegram layer over the ONE offering core.
//!
//! [`crate::TelegramFrontend`] is offering #0's Telegram surface: it plays a single
//! [`DungeonOffering`](dreggnet_offerings::dungeon::DungeonOffering). This module gives the
//! dungeon (and every other offering) a SECOND live surface — the same "all offerings, any
//! surface" the web catalog ([`dreggnet_web::CatalogState`]) got — by driving the
//! frontend-agnostic [`OfferingHost`] through the Telegram frontend:
//!
//! - **list** — [`TelegramHost::list_offerings`] / [`TelegramHost::present_offerings_menu`]: a
//!   `/offerings`-style control message whose inline keyboard is one button per registered
//!   offering (a press opens that offering in the chat);
//! - **open** — [`TelegramHost::open`]: open a session per `(offering, chat)` on the host and
//!   present the offering's [`Surface`] as the Telegram inline keyboard + text;
//! - **advance** — [`TelegramHost::press`]: a button press → [`TelegramFrontend::collect`] the
//!   typed [`Action`] → [`OfferingHost::advance`] ONE real turn on the substrate → re-present;
//! - **verify** — [`TelegramHost::verify`]: re-verify an offering session's committed chain; ALSO
//!   routed through [`TelegramHost::press`] as the reserved [`TURN_VERIFY`] verb, so a shell's
//!   `/verify` input (or a pinned button) reaches the real re-verifier through the ONE router.
//!
//! ## The `!Send` host + the [`HostThread`] handle (mirrors `dreggnet-web`)
//! The [`OfferingHost`] owns heterogeneous offering sessions, some `!Send` (a
//! `CouncilOffering` session holds `Rc`-backed ballot caps).
//! So the host cannot be shared behind a plain `Send` handle; it lives on ONE owning thread and
//! every access is a job shipped to it — only the job's plain-data result (a [`Surface`], an
//! [`Outcome`], a [`VerifyReport`], a `Vec<OfferingInfo>`, all `Send`) crosses back. The
//! [`TelegramFrontend`] itself (the affordance-renderer + the injected transport) stays on the
//! calling thread; it never holds an offering session. This is exactly `dreggnet-web`'s
//! [`HostThread`](dreggnet_web) pattern reused for Telegram.
//!
//! ## Surface → keyboard mapping
//! An offering's [`Surface`] is a deos view-tree; its cap-gated [`Action`]s are the moves. The
//! text half of the surface renders to the message body ([`crate::render::render_surface_text`]);
//! the [`Action`]s render to the inline keyboard, one button per affordance, each button's
//! `callback_data` carrying its `{turn, arg}` ([`crate::api::build_present_request`]) — identical
//! to offering #0's mapping, now driven for ANY offering. The offerings menu is a host-level
//! control keyboard whose buttons carry [`TURN_OPEN`] `{turn:"open", arg: offering index}`.
//!
//! ## Honest scope — what a live Telegram deploy adds
//! Everything here is driven at the logic level with [`crate::transport::MockTransport`] (NO
//! token, NO network). A live deploy adds only: a bot token + a reqwest-backed
//! [`HttpPost`](crate::transport::HttpPost) under [`RawBotApi`](crate::transport::RawBotApi); the
//! update loop / webhook that turns real `CallbackQuery`/`Message` updates into
//! [`TelegramHost::press`] / [`TelegramHost::open`] calls; and a durable session store (this host
//! keeps sessions in memory on its owning thread, seeded deterministically from the chat id, so a
//! restart re-derives the SAME replay-verifiable session but loses in-flight state). WeChat adopts
//! this SAME [`OfferingHost`] next — the host is unchanged; only this thin surface layer differs.

use std::collections::HashMap;
use std::sync::mpsc::{SyncSender, sync_channel};

use deos_view::ViewNode;
use dreggnet_catalog::CatalogConfig;
use dreggnet_offerings::{
    Action, DreggIdentity, Frontend, HostError, OfferingHost, OfferingInfo, Outcome, SessionId,
    Surface, VerifyReport,
};

use crate::cipherclerk::TelegramCipherclerk;
use crate::transport::Transport;
use crate::{ChatId, TelegramFrontend, TelegramUserId};

/// The affordance verb the offerings-menu buttons carry — a host-level control (open the offering
/// at `arg` in this chat), distinct from any offering's own turn verbs.
pub const TURN_OPEN: &str = "open";

/// The RESERVED host-level verify verb — "⛓ re-verify chain" as a routable input. It is never
/// presented as an offering affordance (surfaces stay byte-stable), so [`TelegramHost::press`]
/// routes it WITHOUT the offered check: a runtime shell binds any input it likes (a `/verify`
/// command, a pinned button minting `encode_callback(TURN_VERIFY, 0)`) and the press reaches the
/// chat's active offering's REAL re-verifier ([`TelegramHost::verify`]), coming back as
/// [`HostPress::Verified`]. Mirrors the Discord bot's standing `verifychain:<key>` button
/// (`discord-bot/src/commands/verify_chain.rs`) — same verb string, same ethos.
pub const TURN_VERIFY: &str = "verifychain";

/// The sentinel "active key" a chat carries while it is showing the offerings menu (not yet
/// playing an offering). Not a registered offering key, so it never collides.
const MENU_KEY: &str = "@menu";

/// A unit of work run ON the host's owning thread, against the live [`OfferingHost`].
type HostJob = Box<dyn FnOnce(&mut OfferingHost) + Send + 'static>;

/// **A thread-confined [`OfferingHost`] handle** — the `dreggnet-web` [`HostThread`] pattern reused
/// for Telegram. The host owns `!Send` offering sessions, so it lives on ONE owning thread; every
/// access is a job shipped to it and only the (`Send`) result crosses back. The handle is just a
/// channel sender, so it is `Send + Sync`.
pub struct HostThread {
    jobs: SyncSender<HostJob>,
}

impl HostThread {
    /// Spawn the owning thread and BUILD the host on it (`build` runs on the thread, so the
    /// registered offerings + their sessions are born there and never cross a thread boundary).
    pub fn spawn(build: impl FnOnce() -> OfferingHost + Send + 'static) -> HostThread {
        let (jobs, rx) = sync_channel::<HostJob>(64);
        std::thread::Builder::new()
            .name("telegram-offering-host".to_string())
            .spawn(move || {
                let mut host = build();
                while let Ok(job) = rx.recv() {
                    job(&mut host);
                }
            })
            .expect("spawn the telegram offering host thread");
        HostThread { jobs }
    }

    /// Run `f` against the host on the owning thread and hand back its (`Send`) result. Blocks the
    /// caller until the job returns — one short, CPU-bound offering turn.
    pub fn run<R: Send + 'static>(
        &self,
        f: impl FnOnce(&mut OfferingHost) -> R + Send + 'static,
    ) -> R {
        let (tx, rx) = sync_channel::<R>(1);
        self.jobs
            .send(Box::new(move |host| {
                let _ = tx.send(f(host));
            }))
            .expect("the telegram offering host thread is alive");
        rx.recv()
            .expect("the telegram offering host thread answered")
    }
}

/// The outcome of a [`TelegramHost::press`] — a button press routed through the host.
#[derive(Debug)]
pub enum HostPress {
    /// A menu press opened the named offering in the chat (its surface is now presented).
    Opened(String),
    /// A play press advanced the active offering by one real turn (the [`Outcome`] is the
    /// substrate's — a real landed receipt, or a real executor refusal / anti-ghost).
    Advanced {
        /// The offering key the press advanced.
        key: String,
        /// The real substrate outcome.
        outcome: Outcome,
    },
    /// A [`TURN_VERIFY`] press re-verified the active offering's committed chain and hands back
    /// the REAL [`VerifyReport`] (`None` if the offering exposes no verifier) — verify-don't-trust
    /// routed through the same router every play press takes. Read-only: the presented surface is
    /// untouched, so the next press still resolves against the live keyboard.
    Verified {
        /// The offering key whose chain was re-checked.
        key: String,
        /// The re-verification report, replayed just now on the host thread.
        report: Option<VerifyReport>,
    },
    /// The press did not match any affordance currently on the chat's surface — an honest
    /// frontend-level refusal, BEFORE the substrate (the executor is never reached).
    NotOffered,
    /// No session is active in that chat (nothing was opened / presented yet).
    NoSession,
}

/// **The multi-offering Telegram host.** Bundles the thread-confined [`OfferingHost`] (the registry
/// of offerings + their live sessions) with the [`TelegramFrontend`] (the affordance-renderer over
/// the injected transport), and routes chat button-presses to the right `(offering, session)`.
///
/// Generic over the injected [`Transport`] `T`, so the whole thing drives token- and network-free
/// with [`crate::transport::MockTransport`] in a test and over a live `RawBotApi` in production.
pub struct TelegramHost<T: Transport> {
    /// The bot master secret — the root of every user's derived identity (and of the council
    /// electorate this host registers).
    bot_secret: [u8; 32],
    /// The offering registry, confined to its owning thread.
    host: HostThread,
    /// The Telegram affordance-renderer over the transport (records what each chat last presented).
    frontend: TelegramFrontend<T>,
    /// Which offering each chat's session is currently playing (or [`MENU_KEY`] while browsing).
    /// Keyed by the chat-scoped [`SessionId`]; a press routes to this offering.
    active: HashMap<SessionId, String>,
    /// The Mini App base URL (the public funnel), when the deploy arms the `web_app` launch
    /// tier ([`Self::with_webapp_base`]). `None` = launch buttons off; the inline-button tier
    /// is unaffected either way.
    webapp_base: Option<String>,
}

impl<T: Transport> TelegramHost<T> {
    /// Build a host over the FULL shared catalog (the same 18 offerings every frontend exposes —
    /// see [`telegram_default_host`]), sending through `transport`, with the council electorate
    /// derived from `council_member_uids` (Telegram user ids whose derived identities are
    /// registered as council members — so those users can really vote).
    pub fn new(bot_secret: [u8; 32], transport: T, council_member_uids: &[TelegramUserId]) -> Self {
        // Derive the council electorate on THIS thread (a pure derivation → `[u8; 32]` pubkeys,
        // Send), then move it into the host-thread build closure. The member identity a proposal /
        // vote is attributed to is `hex(pubkey)` — exactly the identity `identity(uid)` derives, so
        // a Telegram member's press matches the registered council member.
        let members: Vec<[u8; 32]> = council_member_uids
            .iter()
            .map(|uid| TelegramCipherclerk::derive(&bot_secret, *uid).public_key_bytes())
            .collect();
        let host = HostThread::spawn(move || telegram_default_host(members));
        TelegramHost {
            bot_secret,
            host,
            frontend: TelegramFrontend::new(bot_secret, transport),
            active: HashMap::new(),
            webapp_base: None,
        }
    }

    /// Build a host over a caller-provided offering registry (the offerings are registered inside
    /// `build`, which runs on the owning thread). Lets a deployment register its own offering set.
    pub fn with_host(
        bot_secret: [u8; 32],
        transport: T,
        build: impl FnOnce() -> OfferingHost + Send + 'static,
    ) -> Self {
        TelegramHost {
            bot_secret,
            host: HostThread::spawn(build),
            frontend: TelegramFrontend::new(bot_secret, transport),
            active: HashMap::new(),
            webapp_base: None,
        }
    }

    /// **Arm the Mini App launch tier**: `base` is the public HTTPS funnel the web `/tg` Mini
    /// App routes are served from ([`crate::webapp::webapp_base_from_env`] resolves it in the
    /// bin). With a base set, a DM's presented offering surface carries a trailing
    /// "🕹 Play in the app" `web_app` row deep-linking THAT offering + session, and
    /// [`present_play_menu`](Self::present_play_menu) (the `/play` command) works. An empty
    /// base disarms. Group chats never get `web_app` buttons — Telegram refuses them there
    /// ([`crate::webapp::web_app_allowed`]); the inline-button tier is their (full) surface.
    pub fn with_webapp_base(mut self, base: impl Into<String>) -> Self {
        let base = base.into().trim().trim_end_matches('/').to_string();
        self.webapp_base = (!base.is_empty()).then_some(base);
        self
    }

    /// The armed Mini App base URL, if any.
    pub fn webapp_base(&self) -> Option<&str> {
        self.webapp_base.as_deref()
    }

    /// The registered offerings (the catalog listing) — key + title + live-session count.
    pub fn list_offerings(&self) -> Vec<OfferingInfo> {
        self.host.run(|h| h.list_offerings())
    }

    /// Derive `uid`'s frontend-agnostic dregg identity (the presser attribution).
    pub fn identity(&self, uid: TelegramUserId) -> dreggnet_offerings::DreggIdentity {
        self.frontend.identity(uid)
    }

    /// The council-member public key a Telegram user id derives to — register these as a
    /// council electorate ([`CatalogConfig::council_members`]) so those users can vote.
    /// Pure; no host needed.
    pub fn council_member_pubkey(bot_secret: &[u8; 32], uid: TelegramUserId) -> [u8; 32] {
        TelegramCipherclerk::derive(bot_secret, uid).public_key_bytes()
    }

    /// Borrow the frontend (e.g. a test's [`crate::transport::MockTransport`] via
    /// [`TelegramFrontend::transport`], or the last-presented surface of a chat).
    pub fn frontend(&self) -> &TelegramFrontend<T> {
        &self.frontend
    }

    /// The offering currently active in the chat session `sid` (`None` if nothing is open, or the
    /// sentinel while the offerings menu is showing).
    pub fn active_offering(&self, sid: &SessionId) -> Option<&str> {
        self.active
            .get(sid)
            .map(String::as_str)
            .filter(|k| *k != MENU_KEY)
    }

    /// **Present the `/offerings` control message** in `chat_id` — a message whose inline keyboard
    /// is one button per registered offering (a press opens that offering in the chat). Records the
    /// chat as "browsing the menu". Returns the chat-scoped [`SessionId`].
    pub fn present_offerings_menu(&mut self, chat_id: ChatId, topic: Option<i64>) -> SessionId {
        let sid = TelegramFrontend::<T>::session_id(chat_id, topic);
        let offerings = self.list_offerings();
        let actions: Vec<Action> = offerings
            .iter()
            .enumerate()
            .map(|(i, o)| Action::new(format!("▶ Play {}", o.title), TURN_OPEN, i as i64, true))
            .collect();
        let surface = Surface(ViewNode::Section {
            title: "DreggNet Cloud — all offerings, any surface".to_string(),
            tag: "accent".to_string(),
            children: vec![ViewNode::Text(
                "Pick an offering to play — each move is a real, verifiable executor turn."
                    .to_string(),
            )],
        });
        self.frontend.spin_session(sid.clone());
        self.frontend.present(&sid, &surface, &actions);
        self.active.insert(sid.clone(), MENU_KEY.to_string());
        sid
    }

    /// **Present the `/play` Mini App launch menu** in `chat_id` — one `web_app` button per
    /// registered offering, each opening the rich web surface for that offering at this chat's
    /// session id ([`crate::webapp::build_play_menu_request`]). A control message OUTSIDE the
    /// session-slot bookkeeping (`web_app` buttons produce no callbacks to match), so the
    /// chat's active offering / presented keyboard are untouched. `Err` carries the honest
    /// human reply when the tier cannot serve here: no base armed, a non-private chat
    /// (Telegram refuses `web_app` inline buttons in groups), or a transport failure.
    pub fn present_play_menu(&mut self, chat_id: ChatId, topic: Option<i64>) -> Result<(), String> {
        let Some(base) = self.webapp_base.clone() else {
            return Err(
                "The Mini App tier is not configured on this deploy — the inline buttons \
                 (/offerings) still play everything."
                    .to_string(),
            );
        };
        if !crate::webapp::web_app_allowed(chat_id, topic) {
            return Err(format!(
                "Mini App buttons only work in a private chat (Telegram's rule) — DM me and \
                 send /play. The web surface lives at {base}/tg."
            ));
        }
        let sid = TelegramFrontend::<T>::session_id(chat_id, topic);
        let offerings = self.list_offerings();
        let req = crate::webapp::build_play_menu_request(chat_id, topic, &base, &sid, &offerings);
        self.frontend
            .send_raw(&req)
            .map(|_| ())
            .map_err(|e| format!("Could not send the play menu: {e}"))
    }

    /// **Open an offering session for `(key, chat)`** — ensure a host session is live under the
    /// chat-scoped [`SessionId`] (seeded deterministically from it) and present the offering's
    /// current [`Surface`] as the chat's inline keyboard, projected FOR the opening user `uid` (the
    /// per-viewer surface — a hidden-hand / cap-dimmed offering paints the opener's own view, not the
    /// viewer-blind one). Errors if `key` is unregistered. Returns the chat-scoped session id.
    pub fn open(
        &mut self,
        key: &str,
        chat_id: ChatId,
        topic: Option<i64>,
        uid: TelegramUserId,
    ) -> Result<SessionId, HostError> {
        let sid = TelegramFrontend::<T>::session_id(chat_id, topic);
        let viewer = self.frontend.identity(uid);
        self.open_into(key, &sid, &viewer)?;
        Ok(sid)
    }

    /// Ensure a host session is live under `sid` (seeded from it) and present the offering's current
    /// surface as the chat's keyboard, recording it active. The surface is projected FOR `viewer`
    /// (the acting Telegram user). The shared opener behind [`open`](Self::open) and a menu-open press.
    fn open_into(
        &mut self,
        key: &str,
        sid: &SessionId,
        viewer: &DreggIdentity,
    ) -> Result<(), HostError> {
        {
            let k = key.to_string();
            let s = sid.clone();
            self.host.run(move |h| h.ensure_open(&k, &s))?;
        }
        self.frontend.spin_session(sid.clone());
        self.present_offering(key, sid, viewer);
        Ok(())
    }

    /// Re-derive `(key, sid)`'s current surface + actions from the live host session **AS `viewer`
    /// sees them** and present them (keeping the chat's affordance surface current for the next
    /// press), recording the offering as active in the chat. Uses the viewer-aware
    /// [`OfferingHost::render_for`] / [`OfferingHost::actions_for`] so a per-viewer offering (a
    /// hidden-hand tug, a per-region document cap) paints the surface for the specific Telegram user
    /// who is looking — not the viewer-blind projection everyone otherwise shared.
    fn present_offering(&mut self, key: &str, sid: &SessionId, viewer: &DreggIdentity) {
        let (surface, actions) = {
            let k = key.to_string();
            let s = sid.clone();
            let v = viewer.clone();
            self.host
                .run(move |h| (h.render_for(&k, &s, &v), h.actions_for(&k, &s, &v)))
        };
        if let (Some(surface), Some(actions)) = (surface, actions) {
            // The Mini App launch tier: in a DM (the only place Telegram honors `web_app`
            // inline buttons), a trailing "Play in the app" row deep-links the rich web
            // surface for THIS offering + session. Never an offering Action — it is not
            // recorded among the presented affordances, so no press can route through it.
            let play = self.webapp_base.as_deref().and_then(|base| {
                let (chat_id, topic) = TelegramFrontend::<T>::chat_of(sid)?;
                crate::webapp::web_app_allowed(chat_id, topic)
                    .then(|| crate::webapp::play_button(base, key, sid))
            });
            let extra: &[crate::api::InlineKeyboardButton] =
                play.as_ref().map(std::slice::from_ref).unwrap_or(&[]);
            self.frontend.present_with(sid, &surface, &actions, extra);
            self.active.insert(sid.clone(), key.to_string());
        }
    }

    /// **Route a button press.** Reconstruct the chat's session, decode the press's `callback_data`
    /// into `{turn, arg}`, check the turn is among the affordances currently presented there
    /// (offered), and:
    /// - if the chat is browsing the menu, OPEN the offering the pressed button names;
    /// - otherwise ADVANCE the active offering by ONE real turn on the substrate and re-present.
    ///
    /// The matching is TURN-offered (mirroring the web catalog's `post_offering_act`): an index move
    /// (a dungeon choice, a council proposal) carries its index in the button, while a value-taking
    /// move (a market `list` reserve / `bid` value) carries a value the press supplies — on a live
    /// bot the value rides a follow-up numeric reply; here the [`crate::CallbackQuery`] carries it.
    /// The executor stays the sole referee of what LANDS (a below-reserve bid, a double-vote, a
    /// killing blow are all real substrate refusals); a press for a turn the surface never offered
    /// is [`HostPress::NotOffered`] (refused BEFORE the substrate); a press in a chat with nothing
    /// open is [`HostPress::NoSession`].
    pub fn press(&mut self, ev: crate::CallbackQuery) -> HostPress {
        let sid = TelegramFrontend::<T>::session_id(ev.chat_id, ev.message_thread_id);
        let Some(active) = self.active.get(&sid).cloned() else {
            return HostPress::NoSession;
        };
        // The acting Telegram user's derived identity — the viewer every re-present is projected FOR
        // (the same identity the play turn is attributed to), so a per-viewer offering paints the
        // presser their own surface.
        let viewer = self.frontend.identity(ev.from_user_id);
        // Decode the pressed button + confirm the turn is on the chat's current surface (offered).
        let Some((turn, arg)) = crate::api::decode_callback(&ev.data) else {
            return HostPress::NotOffered;
        };
        // The reserved host-level verify verb: never presented as an offering affordance, so it
        // bypasses the offered check — any shell input can demand the re-check of the chat's
        // active offering. Read-only: the presented surface is left exactly as it was.
        if turn == TURN_VERIFY {
            if active == MENU_KEY {
                return HostPress::NotOffered;
            }
            let report = self.verify(&active, &sid);
            return HostPress::Verified {
                key: active,
                report,
            };
        }
        let offered = self
            .frontend
            .session(&sid)
            .map(|slot| slot.presented.iter().any(|a| a.turn == turn))
            .unwrap_or(false);
        if !offered {
            return HostPress::NotOffered;
        }

        if active == MENU_KEY {
            // A menu press: open the offering the button names (by stable catalog index).
            if turn != TURN_OPEN {
                return HostPress::NotOffered;
            }
            let offerings = self.list_offerings();
            let Some(info) = offerings.get(arg as usize) else {
                return HostPress::NotOffered;
            };
            let key = info.key.clone();
            // Open the offering's host session (seeded from the chat) + present its surface, projected
            // for the pressing user.
            if self.open_into(&key, &sid, &viewer).is_err() {
                return HostPress::NotOffered;
            }
            return HostPress::Opened(key);
        }

        // A play press: the CORE resolves the typed action on the real substrate — one turn.
        // Label + enabled are decoration; the executor resolves the typed (turn, arg).
        let key = active;
        let actor = viewer.clone();
        let action = Action::new(turn.clone(), turn, arg, true);
        let outcome = {
            let k = key.clone();
            let s = sid.clone();
            self.host.run(move |h| h.advance(&k, &s, action, actor))
        };
        match outcome {
            Some(outcome) => {
                // Re-present the (possibly-advanced) committed state so the next press resolves
                // against the current surface, projected for the pressing user.
                self.present_offering(&key, &sid, &viewer);
                HostPress::Advanced { key, outcome }
            }
            // The host had no such session (should not happen: `active` implies a live session).
            None => HostPress::NoSession,
        }
    }

    /// **Rebind a chat to its durably RESUMED offering after a process restart.** A restarted
    /// host (built over a resume store — [`crate::runtime::durable_telegram_host`]) reopens every
    /// persisted session by move-log replay on boot, but this surface layer's in-memory routing
    /// (`active`, the presented keyboard) starts empty, so the first press in a chat answers
    /// [`HostPress::NoSession`]. This looks the chat's session id up among the LIVE host sessions:
    /// if some offering has `sid` open (i.e. it was resumed), it is recorded active again and its
    /// key returned — the caller then re-presents via [`open`](Self::open) (idempotent: the
    /// resumed session is kept, only the surface is repainted). `None` if no resumed session
    /// exists for the chat. If a chat had MULTIPLE offerings' sessions persisted (it re-opened
    /// across offerings), the first in registry order is chosen — `/open <key>` overrides.
    pub fn resume_chat(&mut self, sid: &SessionId) -> Option<String> {
        if let Some(k) = self.active.get(sid) {
            if k != MENU_KEY {
                return Some(k.clone());
            }
        }
        let key = {
            let s = sid.clone();
            self.host
                .run(move |h| h.keys().into_iter().find(|k| h.is_open(k, &s)))?
        };
        self.active.insert(sid.clone(), key.clone());
        Some(key)
    }

    /// Re-verify `(key, sid)`'s committed chain by the offering's own proof (`None` if absent).
    pub fn verify(&self, key: &str, sid: &SessionId) -> Option<VerifyReport> {
        let key = key.to_string();
        let sid = sid.clone();
        self.host.run(move |h| h.verify(&key, &sid))
    }

    /// The bot master secret (for a deploy to sign on a user's behalf; the frontend attributes with
    /// the public identity alone).
    pub fn bot_secret(&self) -> &[u8; 32] {
        &self.bot_secret
    }
}

/// **The default Telegram catalog host** — the FULL shared portfolio, from the ONE registrar
/// every frontend builds through ([`dreggnet_catalog::build_full_catalog`]): the five games
/// (dungeon · council · market · multiway-tug · automatafl, `tug` wrapped in the shared
/// seat-claiming [`crate::seated::SeatedTug`] adapter), the eight do-once RPG feature surfaces
/// (trade · inventory · cheevos · guild · craft · companion · tavern · party), and the five
/// service offerings (doc · names · compute · grain · hermes) — the same 18 the web catalog
/// (`dreggnet_web::demo_host`) serves, by construction rather than by a duplicated list
/// (docs/BOT-SHARED-BACKEND-DESIGN.md). Call it on the host's owning thread (inside
/// [`HostThread::spawn`]'s build closure) so each offering's `!Send` internals stay confined.
///
/// `council_members` is the electorate (member public keys — a Telegram user whose derived
/// identity is one of these can vote); pass the [`TelegramHost::council_member_pubkey`] of each
/// voter's Telegram id. Every other catalog knob (quorum 2, the two candidate proposals, grain
/// budget 1000) is [`CatalogConfig`]'s deployed default.
pub fn telegram_default_host(council_members: Vec<[u8; 32]>) -> OfferingHost {
    dreggnet_catalog::full_catalog_host(&CatalogConfig::with_council_members(council_members))
}
