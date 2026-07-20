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
//!   present the offering's [`Surface`] on that offering's OWN message in the chat (several
//!   offerings coexist per chat; a press routes by the message it was pressed on);
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
//! ## Who reads the surface decides which projection it carries
//! A **DM** is read by one person; a **group / forum topic** is read by everyone in it, and its
//! session is ONE message that every re-present EDITS in place. So a per-viewer projection
//! ([`OfferingHost::render_for`] — a hidden hand, a sealed move) is served only in a DM; a shared
//! chat always gets the viewer-blind [`OfferingHost::render`]. On top of that structural rule, an
//! offering that DECLARES hidden information
//! ([`dreggnet_offerings::Offering::hidden_information`] — tug, automatafl) is not hosted in a
//! shared chat at all: it is refused at open ([`OpenError::HiddenInSharedChat`]) with a legible
//! redirect to a DM / the Mini App, because a public-only projection is not a playable hand.
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
use dreggnet_catalog::{CatalogConfig, PlayerWorlds, is_rpg_key};
use dreggnet_offerings::{
    Action, DreggIdentity, Frontend, HostError, OfferingHost, OfferingInfo, Outcome, SessionId,
    Surface, VerifyReport,
};

use crate::cipherclerk::TelegramCipherclerk;
use crate::transport::{MessageId, Transport};
use crate::{ChatId, ChatKind, TelegramFrontend, TelegramUserId};

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

/// A unit of work run ON the per-identity RPG worlds' owning thread, against the live
/// [`PlayerWorlds`] registry.
type PlayerJob = Box<dyn FnOnce(&mut PlayerWorlds) + Send + 'static>;

/// **A thread-confined [`PlayerWorlds`] handle** — the [`HostThread`] pattern for the per-identity
/// RPG worlds. A [`PlayerWorlds`] owns one `!Send` [`OfferingHost`] per derived identity, so it
/// lives on ONE owning thread and every access is a job shipped to it; only the (`Send`) result
/// crosses back. The handle is just a channel sender — `Send + Sync`.
pub struct PlayerHostThread {
    jobs: SyncSender<PlayerJob>,
}

impl PlayerHostThread {
    /// Spawn the owning thread and BUILD the registry on it (`build` runs on the thread, so every
    /// per-identity host and its `!Send` sessions are born there and never cross a boundary).
    pub fn spawn(build: impl FnOnce() -> PlayerWorlds + Send + 'static) -> PlayerHostThread {
        let (jobs, rx) = sync_channel::<PlayerJob>(64);
        std::thread::Builder::new()
            .name("telegram-player-worlds".to_string())
            .spawn(move || {
                let mut worlds = build();
                while let Ok(job) = rx.recv() {
                    job(&mut worlds);
                }
            })
            .expect("spawn the telegram player-worlds thread");
        PlayerHostThread { jobs }
    }

    /// Run `f` against the registry on the owning thread and hand back its (`Send`) result.
    pub fn run<R: Send + 'static>(
        &self,
        f: impl FnOnce(&mut PlayerWorlds) -> R + Send + 'static,
    ) -> R {
        let (tx, rx) = sync_channel::<R>(1);
        self.jobs
            .send(Box::new(move |worlds| {
                let _ = tx.send(f(worlds));
            }))
            .expect("the telegram player-worlds thread is alive");
        rx.recv()
            .expect("the telegram player-worlds thread answered")
    }
}

/// **Why an open did not happen** — the host's refusal, or this SURFACE's own refusal to host the
/// offering at all.
#[derive(Debug)]
pub enum OpenError {
    /// The [`OfferingHost`] refused (unknown key, a policy gate, a failed deploy / resume).
    Host(HostError),
    /// **The chat is SHARED and the offering hides per-player state**
    /// ([`dreggnet_offerings::Offering::hidden_information`]). A group / forum-topic session paints
    /// ONE message that every member reads (a re-present EDITS it in place), so there is no way to
    /// serve a per-viewer projection there without serving it to the whole room. Nothing was
    /// opened; `why` is the legible redirect the player is shown.
    HiddenInSharedChat {
        /// The offering that will not be hosted here.
        key: String,
        /// The human redirect (DM / Mini App) — this is what the player reads.
        why: String,
    },
}

impl std::fmt::Display for OpenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OpenError::Host(e) => write!(f, "{e}"),
            OpenError::HiddenInSharedChat { why, .. } => write!(f, "{why}"),
        }
    }
}

impl std::error::Error for OpenError {}

impl From<HostError> for OpenError {
    fn from(e: HostError) -> Self {
        OpenError::Host(e)
    }
}

impl OpenError {
    /// The human reply for a `/open <key>` that did not open. A host failure keeps the familiar
    /// "Cannot open <key>: …" shape; a shared-chat refusal IS its own message (it is a redirect,
    /// not a malfunction, and prefixing it would bury the instruction).
    pub fn human(&self, key: &str) -> String {
        match self {
            OpenError::Host(e) => format!("Cannot open {key}: {e}"),
            OpenError::HiddenInSharedChat { why, .. } => why.clone(),
        }
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
    /// A press SELECTED a free-text affordance (one whose [`Action::wants_text`] is set, e.g. a
    /// document INSERT/set-title, a Hermes prompt, a names register, a compute settle) — it ARMS
    /// the chat's text slot instead of advancing (a text affordance carries no content on a bare
    /// press). The NEXT plain-text message the chat receives is routed into THIS armed affordance
    /// as its [`Action::text`] payload ([`TelegramHost::press_text`]). Nothing committed yet — the
    /// arm is a pure selection.
    TextArmed {
        /// The offering key the armed affordance belongs to.
        key: String,
        /// The armed affordance (its `{turn, arg}` + human label — the text slot now selected).
        action: Action,
    },
    /// A menu press asked for a HIDDEN-INFORMATION offering in a SHARED chat, and this surface
    /// will not host one ([`OpenError::HiddenInSharedChat`]). Nothing opened, nothing rendered;
    /// `why` is the legible redirect to a DM / the Mini App.
    OpenRefused {
        /// The offering that will not be hosted here.
        key: String,
        /// The human redirect the presser is shown.
        why: String,
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
    /// The offering registry, confined to its owning thread. The SHARED tables — the games and
    /// service offerings — live here (a council with one voter per host is not a council).
    host: HostThread,
    /// The per-identity RPG worlds, confined to their own owning thread. The seven [`is_rpg_key`]
    /// surfaces (trade / inventory / craft / …) are per-player by nature, so every RPG-key session
    /// operation routes to the PRESSER's own [`OfferingHost`] here
    /// ([`run_offering`](Self::run_offering)), keyed by their derived identity — two Telegram users
    /// therefore have ISOLATED inventories. The shared-layer form of the split Discord already runs.
    players: PlayerHostThread,
    /// The Telegram affordance-renderer over the transport (records what each chat last presented).
    frontend: TelegramFrontend<T>,
    /// **The chat's MOST RECENT surface's offering** (or [`MENU_KEY`] while browsing) — keyed by
    /// the chat-scoped [`SessionId`].
    ///
    /// This is no longer "the one offering this chat may play": each offering now owns its OWN
    /// message in the chat ([`TelegramFrontend::surface_id`]), so several coexist and a press
    /// routes by the message it was pressed on. `active` is the fallback for a press that names no
    /// message (a `/act` / `/verify` command, a Mini App round-trip) and the referent of "this
    /// chat's session" for the single-offering UX — which is exactly what it always meant in a
    /// chat with one offering open.
    active: HashMap<SessionId, String>,
    /// **The chat's ARMED free-text affordance, if one is selected.** A press on a
    /// [`Action::wants_text`] affordance records it here (see [`HostPress::TextArmed`]); the next
    /// plain-text message routes into it ([`Self::pending_text_action`] / [`Self::press_text`]).
    /// This is the gate that keeps free-text capture DELIBERATE — with nothing armed, a chat's
    /// plain messages are ordinary chatter (never swallowed into an offering). Cleared on any
    /// advance / re-present (the surface moved on). Keyed by SURFACE
    /// ([`TelegramFrontend::surface_id`]), so arming a document's text slot does not disarm the
    /// tug board open beside it in the same chat.
    armed: HashMap<SessionId, Action>,
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
            players: PlayerHostThread::spawn(PlayerWorlds::new),
            frontend: TelegramFrontend::new(bot_secret, transport),
            active: HashMap::new(),
            armed: HashMap::new(),
            webapp_base: None,
        }
    }

    /// Build a host over a caller-provided offering registry (the offerings are registered inside
    /// `build`, which runs on the owning thread), with an IN-MEMORY per-identity RPG worlds
    /// registry. Lets a deployment register its own shared offering set; the RPG worlds stay
    /// in-memory (the tests' path — see [`with_hosts`](Self::with_hosts) for the durable pair).
    pub fn with_host(
        bot_secret: [u8; 32],
        transport: T,
        build: impl FnOnce() -> OfferingHost + Send + 'static,
    ) -> Self {
        Self::with_hosts(bot_secret, transport, build, PlayerWorlds::new)
    }

    /// Build a host over a caller-built shared registry AND a caller-built per-identity RPG worlds
    /// registry — the durable production seam (the bin passes the `TELEGRAM_SESSION_DIR`-resolved
    /// pair, so both the shared game sessions and each player's RPG world survive a restart by
    /// move-log replay). Both `build` closures run on their own owning threads.
    pub fn with_hosts(
        bot_secret: [u8; 32],
        transport: T,
        build: impl FnOnce() -> OfferingHost + Send + 'static,
        build_players: impl FnOnce() -> PlayerWorlds + Send + 'static,
    ) -> Self {
        TelegramHost {
            bot_secret,
            host: HostThread::spawn(build),
            players: PlayerHostThread::spawn(build_players),
            frontend: TelegramFrontend::new(bot_secret, transport),
            active: HashMap::new(),
            armed: HashMap::new(),
            webapp_base: None,
        }
    }

    /// **Route a `(key, session)`-scoped host job to the host that OWNS it for `viewer`.** An
    /// [`is_rpg_key`] offering runs against the viewer's own per-identity RPG world (their isolated
    /// inventory); everything else — the shared games, party, and services — runs against the ONE catalog
    /// host. This ONE routing decision is why two Telegram users never share an inventory while a
    /// council / tug stays a single shared table.
    fn run_offering<R: Send + 'static>(
        &self,
        key: &str,
        viewer: &DreggIdentity,
        f: impl FnOnce(&mut OfferingHost) -> R + Send + 'static,
    ) -> R {
        if is_rpg_key(key) {
            let id = viewer.0.clone();
            self.players.run(move |worlds| f(worlds.host_mut(&id)))
        } else {
            self.host.run(f)
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
        // THE LAB FRAMING (shared words: `dreggnet_catalog::{flagship_pointer, lab_intro}`) —
        // the flagship pointer leads (The Descent is NOT in this catalog; it lives on the web
        // surface), then the keyboard below is honestly labelled as the lab shelf.
        // H1: `/descent` on the web is the no-cheat BOARD, not a play surface — label it honestly
        // (the served in-browser play page is a separate lane; play today is live in Discord).
        let descent = match self.webapp_base.as_deref() {
            Some(base) => format!(
                "{} See today's no-cheat board at {base}/descent.",
                dreggnet_catalog::flagship_pointer()
            ),
            None => format!(
                "{} Its no-cheat board lives on the web surface, at /descent.",
                dreggnet_catalog::flagship_pointer()
            ),
        };
        let surface = Surface(ViewNode::Section {
            title: "🧪 The Lab — DreggNet Cloud".to_string(),
            tag: "accent".to_string(),
            children: vec![
                ViewNode::Text(descent),
                ViewNode::Text(dreggnet_catalog::lab_intro().to_string()),
                ViewNode::Text(
                    "Pick an offering to poke — each move is a real, verifiable executor turn."
                        .to_string(),
                ),
            ],
        });
        // The menu gets its OWN surface too ([`MENU_KEY`] is not a registered offering key, so it
        // never collides). That keeps the menu message live and pressable AFTER an offering is
        // opened beside it — pressing it again opens a SECOND offering, instead of the press being
        // read as a stale move on whatever was opened last.
        let menu_surface = TelegramFrontend::<T>::surface_id(chat_id, topic, MENU_KEY);
        self.frontend.spin_session(menu_surface.clone());
        self.frontend.present(&menu_surface, &surface, &actions);
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

    /// Present the **`/link` identity-ceremony launch button** — a `web_app` button opening
    /// `<base>/tg/link` where the user signs a cross-platform link claim with their root key.
    /// Private chats only (Telegram honors `web_app` inline buttons only in DMs).
    pub fn present_link_menu(&mut self, chat_id: ChatId, topic: Option<i64>) -> Result<(), String> {
        let Some(base) = self.webapp_base.clone() else {
            return Err(
                "Linking needs the Mini App tier, which is not configured on this deploy."
                    .to_string(),
            );
        };
        if !crate::webapp::web_app_allowed(chat_id, topic) {
            return Err(format!(
                "Linking opens a web page, so it works in a private chat only (Telegram's rule) — \
                 DM me and send /link. The page lives at {base}/tg/link."
            ));
        }
        let req = crate::webapp::build_link_request(chat_id, topic, &base);
        self.frontend
            .send_raw(&req)
            .map(|_| ())
            .map_err(|e| format!("Could not send the link button: {e}"))
    }

    /// **Would hosting `key` in this chat leak?** — the gate in front of every open.
    ///
    /// A DM is a single-reader surface: a per-viewer projection there reaches exactly the person
    /// it is about. A group or forum topic is not — its session is ONE message that every member
    /// reads, and a re-present EDITS that message in place, so whatever is painted into it is
    /// painted for the whole room. An offering that DECLARES hidden information
    /// ([`dreggnet_offerings::Offering::hidden_information`]) therefore cannot be hosted on a
    /// shared surface at all, and this returns the legible redirect.
    ///
    /// The declared signal is what makes this decidable *before* opening: at that moment no seat
    /// is claimed and no card is dealt, so the per-viewer projection is still byte-identical to
    /// the public one — a render differential would answer "safe" and only start disagreeing after
    /// the first hand is dealt, which is one turn too late. `None` = safe to host here.
    fn hidden_in_shared_chat(
        &self,
        key: &str,
        chat_id: ChatId,
        topic: Option<i64>,
    ) -> Option<String> {
        if !ChatKind::classify(chat_id, topic).is_collective() {
            return None;
        }
        let (hidden, title) = {
            let k = key.to_string();
            self.host.run(move |h| {
                (
                    h.hidden_information(&k).unwrap_or(false),
                    h.list_offerings()
                        .into_iter()
                        .find(|o| o.key == k)
                        .map(|o| o.title),
                )
            })
        };
        if !hidden {
            return None;
        }
        let title = title.unwrap_or_else(|| key.to_string());
        Some(format!(
            "🔒 {title} hides per-player state — your hand is yours alone. This chat is a group, \
             and a group's surface is ONE message every member reads (each move edits it in \
             place), so painting your own cards there would deal them to the whole table. I will \
             not do that. DM me and send `/open {key}` to play it privately — or `/play` for the \
             Mini App (Telegram allows those in DMs only). Full-information offerings \
             (`/offerings`) play here in the group as usual."
        ))
    }

    /// **Open an offering session for `(key, chat)`** — ensure a host session is live under the
    /// chat-scoped [`SessionId`] (seeded deterministically from it) and present the offering's
    /// current [`Surface`] on its OWN message in the chat.
    ///
    /// In a DM the surface is projected FOR the opening user `uid` (the per-viewer view — a
    /// hidden-hand / cap-dimmed offering paints the opener's own hand). In a group / forum topic
    /// it is the viewer-blind projection, and a hidden-information offering is REFUSED outright
    /// ([`OpenError::HiddenInSharedChat`]) rather than half-served — see
    /// [`hidden_in_shared_chat`](Self::hidden_in_shared_chat). Returns the chat-scoped session id.
    pub fn open(
        &mut self,
        key: &str,
        chat_id: ChatId,
        topic: Option<i64>,
        uid: TelegramUserId,
    ) -> Result<SessionId, OpenError> {
        if let Some(why) = self.hidden_in_shared_chat(key, chat_id, topic) {
            return Err(OpenError::HiddenInSharedChat {
                key: key.to_string(),
                why,
            });
        }
        let sid = TelegramFrontend::<T>::session_id(chat_id, topic);
        let viewer = self.frontend.identity(uid);
        self.open_into(key, &sid, &viewer)?;
        Ok(sid)
    }

    /// Ensure a host session is live under `sid` (seeded from it) and present the offering's current
    /// surface on its own message, recording it as the chat's most recent. The shared opener behind
    /// [`open`](Self::open) and a menu-open press — BOTH of which check
    /// [`hidden_in_shared_chat`](Self::hidden_in_shared_chat) first.
    fn open_into(
        &mut self,
        key: &str,
        sid: &SessionId,
        viewer: &DreggIdentity,
    ) -> Result<(), HostError> {
        {
            let k = key.to_string();
            let s = sid.clone();
            // RPG keys open in the VIEWER's own per-identity world (isolated inventory); the shared
            // tables (games + services) open on the ONE catalog host.
            self.run_offering(key, viewer, move |h| h.ensure_open(&k, &s))?;
        }
        // Spin THIS offering's surface slot, not a bare chat-level one — a stray chat-keyed slot
        // would shadow the offering's own surface for every caller that looks a chat up.
        if let Some((chat_id, topic)) = TelegramFrontend::<T>::chat_of(sid) {
            self.frontend
                .spin_session(TelegramFrontend::<T>::surface_id(chat_id, topic, key));
        }
        self.present_offering(key, sid, viewer);
        Ok(())
    }

    /// Re-derive `(key, sid)`'s current surface + actions from the live host session and present
    /// them on THIS offering's own message in the chat, recording it as the chat's most recent.
    ///
    /// **Which projection depends on who can read the message, and that is the whole privacy
    /// rule:**
    /// - a **DM** is read by one person, so it gets the viewer-aware
    ///   [`OfferingHost::render_for`] / [`OfferingHost::actions_for`] — a hidden-hand tug or a
    ///   per-region document cap paints the surface for the specific Telegram user who is looking;
    /// - a **group / forum topic** is read by everyone in it, and its session is ONE message that
    ///   every re-present EDITS in place, so it gets the viewer-blind [`OfferingHost::render`] /
    ///   [`OfferingHost::actions`] — the PUBLIC projection, the only thing a shared message can
    ///   honestly carry.
    ///
    /// The rule is structural, not a heuristic: on a shared surface `render_for` is never called
    /// at all, so no offering — declared hidden or not, today's or a future one — can have a
    /// private projection edited into a message a group reads. (`hidden_information` offerings
    /// additionally never reach here in a group: they are refused at open, because a public-only
    /// projection is not a playable hand.) It also fixes an incoherence: a group keyboard used to
    /// be whichever member pressed last: now the shared message shows one shared board with one
    /// shared keyboard, and the executor stays the sole referee of what any presser may land.
    fn present_offering(&mut self, key: &str, sid: &SessionId, viewer: &DreggIdentity) {
        let Some((chat_id, topic)) = TelegramFrontend::<T>::chat_of(sid) else {
            return;
        };
        let shared = ChatKind::classify(chat_id, topic).is_collective();
        // An RPG world is inherently the viewer's own (their inventory), so it is ALWAYS projected
        // per-viewer — a press acts in the presser's own world and re-renders as theirs (the
        // Discord model). A shared table keeps the who-can-read-this rule: viewer-blind in a
        // collective chat, per-viewer in a DM.
        let per_viewer = !shared || is_rpg_key(key);
        let surface_sid = TelegramFrontend::<T>::surface_id(chat_id, topic, key);
        // The surface is (re)painted fresh — any previously-armed text slot is now stale
        // (the affordance moved on), so drop it. Arming a text slot ([`Self::press`]) returns
        // BEFORE this, so the arm survives until the next advance / open / re-present.
        self.armed.remove(&surface_sid);
        let (surface, actions) = {
            let k = key.to_string();
            let s = sid.clone();
            let v = viewer.clone();
            self.run_offering(key, viewer, move |h| {
                if per_viewer {
                    (h.render_for(&k, &s, &v), h.actions_for(&k, &s, &v))
                } else {
                    (h.render(&k, &s), h.actions(&k, &s))
                }
            })
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
            // Onto THIS offering's own message — a second offering opened in the chat gets its
            // own, instead of stealing this one's.
            self.frontend
                .present_with(&surface_sid, &surface, &actions, extra);
            self.active.insert(sid.clone(), key.to_string());
        }
    }

    /// **Route a button press.** Resolve WHICH of the chat's live surfaces the press addresses,
    /// decode its `callback_data` into `{turn, arg}`, check the turn is among the affordances that
    /// surface presented (offered), and:
    /// - if the addressed surface is the offerings menu, OPEN the offering the pressed button names;
    /// - otherwise ADVANCE that surface's offering by ONE real turn on the substrate and re-present.
    ///
    /// **Surface resolution** — a chat may hold several live offerings at once, each on its own
    /// message. A real press carries the message it was pressed on
    /// ([`crate::CallbackQuery::message_id`]), which names its surface exactly; a synthesized press
    /// that carries none (a `/act` or `/verify` command, a Mini App `sendData` round-trip) falls
    /// back to the chat's most recently presented surface. So the offerings menu stays live and
    /// usable to open a SECOND offering, and a press on the first offering's message still reaches
    /// the first offering.
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
        // The HOST session id stays chat-scoped: `(key, sid)` already names a host session, so two
        // offerings in one chat are already two sessions. Only the SURFACE needed splitting.
        let sid = TelegramFrontend::<T>::session_id(ev.chat_id, ev.message_thread_id);
        // Which surface is being pressed: the press's own message names it; a press that names no
        // message means the chat's most recent surface.
        let surface_sid = match ev
            .message_id
            .and_then(|m| self.frontend.surface_of_message(MessageId(m)))
        {
            Some(s) => s.clone(),
            None => match self.frontend.latest_surface(&sid) {
                Some(s) => s.clone(),
                None => sid.clone(),
            },
        };
        // …and which offering that surface belongs to. A surface id carries its own offering; a
        // bare chat-scoped surface is the chat-level one (the offerings menu).
        let active = match TelegramFrontend::<T>::offering_of(&surface_sid) {
            Some(k) => k.to_string(),
            None => match self.active.get(&sid).cloned() {
                Some(k) => k,
                None => return HostPress::NoSession,
            },
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
            // Re-verify the PRESSER's own chain — for an RPG key that is a session in their own
            // world, so verify must route to the same world its turns landed in.
            let report = {
                let k = active.clone();
                let s = sid.clone();
                self.run_offering(&active, &viewer, move |h| h.verify(&k, &s))
            };
            return HostPress::Verified {
                key: active,
                report,
            };
        }
        let offered = self
            .frontend
            .session(&surface_sid)
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
            // The SAME gate `/open` faces: a hidden-information offering is not hosted on a
            // surface a whole group reads — refused here, before anything is rendered.
            if let Some(why) = self.hidden_in_shared_chat(&key, ev.chat_id, ev.message_thread_id) {
                return HostPress::OpenRefused { key, why };
            }
            // Open the offering's host session (seeded from the chat) + present its surface on its
            // own message.
            if self.open_into(&key, &sid, &viewer).is_err() {
                return HostPress::NotOffered;
            }
            return HostPress::Opened(key);
        }

        let key = active;

        // A play press on a FREE-TEXT affordance (a `wants_text` template — a document
        // insert/set-title, a Hermes prompt, a names register, a compute settle) carries no
        // content, so it does not advance: it ARMS the chat's text slot, and the next plain-text
        // message fills it ([`Self::press_text`]). Matched on the EXACT (turn, arg) the press
        // names, so a document's four distinct text templates are each selectable — not just the
        // first (the old `find(wants_text)` made the doc silently append-only).
        // Bound to a `let` first so the immutable `self.frontend` borrow ends before the mutable
        // `self.armed` insert below.
        let text_affordance = self.frontend.session(&surface_sid).and_then(|slot| {
            slot.presented
                .iter()
                .find(|a| a.turn == turn && a.arg == arg && a.wants_text && a.text.is_none())
                .cloned()
        });
        if let Some(text_affordance) = text_affordance {
            self.armed
                .insert(surface_sid.clone(), text_affordance.clone());
            return HostPress::TextArmed {
                key,
                action: text_affordance,
            };
        }

        // A non-text move: the CORE resolves the typed action on the real substrate — one turn.
        // Label + enabled are decoration; the executor resolves the typed (turn, arg). Routed to
        // the presser's own world for an RPG key.
        let actor = viewer.clone();
        let action = Action::new(turn.clone(), turn, arg, true);
        let outcome = {
            let k = key.clone();
            let s = sid.clone();
            self.run_offering(&key, &viewer, move |h| h.advance(&k, &s, action, actor))
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

    /// **The chat's ARMED text affordance, if one is selected** — the "this slot wants text"
    /// signal the free-text router keys on. Returns the affordance the chat has ARMED (by a
    /// button press on a [`Action::wants_text`] template — see [`HostPress::TextArmed`]), or
    /// `None` when the chat has no active offering (or is browsing the menu), or nothing is armed.
    ///
    /// The selection is DELIBERATE, not automatic: a press RECORDS the chosen `(turn, arg)`
    /// text affordance ([`Self::press`]), and only THEN does a plain-text message route into it.
    /// This is what keeps free-text capture honest — with nothing armed, a chat's plain messages
    /// are ordinary chatter, never swallowed into an offering (the old `find(wants_text)`
    /// captured EVERY message the moment any text offering was open, and always into the FIRST
    /// text affordance — making a document silently append-only and a group chat's every message
    /// an offering input). A stale arm (the surface moved on, so the affordance is no longer
    /// presented) is dropped.
    pub fn pending_text_action(&self, sid: &SessionId) -> Option<Action> {
        // Resolve the SURFACE: `sid` may already name one (`tg:-5#doc`), or be the chat-scoped id,
        // in which case the chat's most recent offering owns the text slot. Only a real offering
        // (not the offerings menu) solicits text.
        let key = match TelegramFrontend::<T>::offering_of(sid) {
            Some(k) => k.to_string(),
            None => self.active_offering(sid)?.to_string(),
        };
        let (chat_id, topic) = TelegramFrontend::<T>::chat_of(sid)?;
        let surface_sid = TelegramFrontend::<T>::surface_id(chat_id, topic, &key);
        // The chat must have ARMED a text affordance on THAT surface (a deliberate press).
        let armed = self.armed.get(&surface_sid)?;
        // Belt-and-suspenders: the armed affordance must still be the presented surface's own
        // (a stale arm — after a re-present that changed the affordances — is not honoured).
        let slot = self.frontend.session(&surface_sid)?;
        slot.presented
            .iter()
            .any(|a| a.turn == armed.turn && a.arg == armed.arg && a.wants_text)
            .then(|| armed.clone())
    }

    /// **Route free text into the chat's pending text affordance** — the in-chat driver for a
    /// text-input offering (a document EDIT's prose, a set-title's value). Finds the chat's
    /// [`pending_text_action`](Self::pending_text_action), attaches `text` as its
    /// [`Action::text`] payload, and ADVANCES it as one real turn on the substrate, attributed to
    /// `uid`'s derived identity — exactly the path a button press takes ([`Self::press`]), only
    /// the affordance's string is supplied by the message instead of a callback arg. The executor
    /// stays the sole referee: an ill-formed / unauthorized / conflicting edit lands a real
    /// [`Outcome::Refused`] (nothing committed), never a silent accept.
    ///
    /// [`HostPress::NoSession`] if nothing is open in the chat; [`HostPress::NotOffered`] if the
    /// chat's surface has no text affordance pending (the caller should have checked
    /// [`pending_text_action`](Self::pending_text_action) first, so this is a belt-and-suspenders
    /// refusal, not a normal path). Re-presents the (possibly-advanced) surface on success.
    pub fn press_text(
        &mut self,
        chat_id: ChatId,
        topic: Option<i64>,
        uid: TelegramUserId,
        text: &str,
    ) -> HostPress {
        let sid = TelegramFrontend::<T>::session_id(chat_id, topic);
        let Some(key) = self.active_offering(&sid).map(str::to_string) else {
            return HostPress::NoSession;
        };
        let Some(pending) = self.pending_text_action(&sid) else {
            return HostPress::NotOffered;
        };
        // The acting user's derived identity — the viewer every re-present is projected FOR and
        // the actor the edit is attributed to (the same as a play press).
        let viewer = self.frontend.identity(uid);
        let action = pending.with_text(text.to_string());
        let actor = viewer.clone();
        let outcome = {
            let k = key.clone();
            let s = sid.clone();
            // Routed to the acting user's own world for an RPG key (a per-player document/craft edit).
            self.run_offering(&key, &viewer, move |h| h.advance(&k, &s, action, actor))
        };
        match outcome {
            Some(outcome) => {
                self.present_offering(&key, &sid, &viewer);
                HostPress::Advanced { key, outcome }
            }
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
