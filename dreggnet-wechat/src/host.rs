//! # `WeChatHost` — the MULTI-OFFERING WeChat layer over the ONE offering core.
//!
//! [`crate::WeChatFrontend`] is offering #0's WeChat surface: it plays a single
//! [`DungeonOffering`](dreggnet_offerings::dungeon::DungeonOffering) as an OA numbered-reply
//! message. This module gives the dungeon (and every other offering) the FULL DreggNet catalog on
//! WeChat — the same "all offerings, any surface" the web catalog ([`dreggnet_web::CatalogState`])
//! and the Telegram host ([`dreggnet_telegram::host::TelegramHost`]) got — by driving the
//! frontend-agnostic [`OfferingHost`] through the WeChat OA numbered-reply surface:
//!
//! - **list** — [`WeChatHost::list_offerings`] / [`WeChatHost::present_offerings_menu`]: an
//!   `/offerings`-style control message whose numbered reply list is one line per registered
//!   offering (a reply of its number opens that offering in the user's 1:1 conversation);
//! - **open** — [`WeChatHost::open`] (solo) / [`WeChatHost::join`] (a shared room): open a session
//!   on the host and present the offering's [`Surface`] as the WeChat OA numbered reply list;
//! - **advance** — [`WeChatHost::reply`]: an inbound numbered reply → [`WeChatFrontend::collect`]
//!   the typed [`Action`] → [`OfferingHost::advance`] ONE real turn on the substrate → re-present;
//! - **verify** — [`WeChatHost::verify`]: re-verify an offering session's committed chain.
//!
//! ## The Surface → numbered-reply mapping (mirrors the Telegram keyboard mapping)
//! An offering's [`Surface`] is a deos view-tree; its cap-gated [`Action`]s are the moves. WeChat OA
//! forbids arbitrary per-message buttons, so — unlike Telegram's inline keyboard — the affordances
//! ride as a **numbered list appended to the message text**, and the user **replies with the
//! number** ([`crate::api::present_message`] → the shared [`deos_view::WeChatBackend`]). A reply is
//! resolved back to its `{turn, arg}` by the SAME shared codec ([`deos_view::WeChatMessage::resolve`],
//! via [`WeChatFrontend::collect`]) — a reply number naming one of the presented options, or a
//! `#<turn>:<arg>` marked id. The offerings menu is a host-level control surface whose numbered
//! options carry [`TURN_OPEN`] `{turn:"open", arg: offering index}`.
//!
//! **Value-taking moves** (a market `list` reserve, a `bid` value) carry a value the reply supplies.
//! On a live OA a numbered pick of such a move prompts "reply with the amount" and a bare-number
//! follow-up becomes the value; the general shape (also what a Mini-Program button posts back) is the
//! `#<turn>:<value>` marked reply the shared codec already resolves — exactly analogous to the
//! Telegram host taking the value from the button's `callback_data`. Both leave the executor the sole
//! referee of what LANDS (a below-reserve bid, a double-vote are real substrate refusals).
//!
//! ## The `!Send` host + the [`HostThread`] handle (mirrors `dreggnet-web` / the Telegram host)
//! The [`OfferingHost`] owns heterogeneous offering sessions, some `!Send` (a
//! [`CouncilOffering`](dreggnet_council::CouncilOffering) session holds `Rc`-backed ballot caps). So
//! the host cannot be shared behind a plain `Send` handle; it lives on ONE owning thread and every
//! access is a job shipped to it — only the job's plain-data result (a [`Surface`], an [`Outcome`], a
//! [`VerifyReport`], a `Vec<OfferingInfo>`, all `Send`) crosses back. The [`WeChatFrontend`] itself
//! (the affordance-renderer + the injected transport) stays on the calling thread; it never holds an
//! offering session. This is exactly `dreggnet-web`'s [`HostThread`](dreggnet_web) pattern.
//!
//! ## Session shape: per-participant surfaces onto a shared room session
//! A WeChat OA conversation is strictly **1:1** — there is no group-chat affordance surface (unlike a
//! Telegram group / forum topic, which the Telegram host keys a session by). So the WeChat host keys
//! each participant's *surface* by their OpenID ([`WeChatFrontend::session_id`] → `wx:<openid>`) while
//! the underlying host *session* is a **room** [`SessionId`]:
//! - **solo** — [`WeChatHost::open`]: room = the openid's own `wx:<openid>` session — the canonical
//!   single-player per-`(offering, openid)` case (a dungeon).
//! - **shared** — [`WeChatHost::join`]: several openids act on ONE room session, each in their own 1:1
//!   conversation (their own numbered-reply surface onto the shared state), each move attributed to
//!   the sender's derived identity. This is what makes a COLLECTIVE offering (a quorum council, a
//!   multi-bidder market) genuinely playable over 1:1 OA conversations.
//!
//! ## Honest scope — what a live WeChat deploy adds
//! Everything here is driven at the logic level with [`crate::transport::MockTransport`] (NO token,
//! NO network). A live deploy adds only: a valid OA access-token + a reqwest-backed
//! [`HttpPost`](crate::transport::HttpPost) under [`RawWeChatApi`](crate::transport::RawWeChatApi);
//! the OA webhook / update loop that turns real inbound `Message` posts into [`WeChatHost::reply`]
//! calls (and, for a shared room, the openid→room routing an orchestrator maintains one layer up); a
//! prompt-then-collect step for value moves (or the `#<turn>:<value>` marked reply used here); and a
//! durable session store (this host keeps sessions in memory on its owning thread, seeded
//! deterministically from the room id, so a restart re-derives the SAME replay-verifiable session but
//! loses in-flight state).

use std::collections::HashMap;
use std::sync::mpsc::{SyncSender, sync_channel};

use deos_view::{MenuItem, ViewNode};
use dreggnet_council::{CandidateProposal, CouncilOffering};
use dreggnet_market::MarketOffering;
use dreggnet_offerings::dungeon::DungeonOffering;
use dreggnet_offerings::{
    Action, DreggIdentity, Frontend, HostError, OfferingHost, OfferingInfo, Outcome, SessionId,
    Surface, VerifyReport,
};

use crate::cipherclerk::WeChatCipherclerk;
use crate::transport::Transport;
use crate::{OpenId, WeChatFrontend, WeChatMessage};

/// The affordance verb the offerings-menu options carry — a host-level control (open the offering at
/// `arg` for this user), distinct from any offering's own turn verbs.
pub const TURN_OPEN: &str = "open";

/// The sentinel "active key" a participant carries while showing the offerings menu (not yet playing
/// an offering). Not a registered offering key, so it never collides.
const MENU_KEY: &str = "@menu";

/// A unit of work run ON the host's owning thread, against the live [`OfferingHost`].
type HostJob = Box<dyn FnOnce(&mut OfferingHost) + Send + 'static>;

/// **A thread-confined [`OfferingHost`] handle** — the `dreggnet-web` / Telegram [`HostThread`]
/// pattern reused for WeChat. The host owns `!Send` offering sessions, so it lives on ONE owning
/// thread; every access is a job shipped to it and only the (`Send`) result crosses back. The handle
/// is just a channel sender, so it is `Send + Sync`.
pub struct HostThread {
    jobs: SyncSender<HostJob>,
}

impl HostThread {
    /// Spawn the owning thread and BUILD the host on it (`build` runs on the thread, so the
    /// registered offerings + their sessions are born there and never cross a thread boundary).
    pub fn spawn(build: impl FnOnce() -> OfferingHost + Send + 'static) -> HostThread {
        let (jobs, rx) = sync_channel::<HostJob>(64);
        std::thread::Builder::new()
            .name("wechat-offering-host".to_string())
            .spawn(move || {
                let mut host = build();
                while let Ok(job) = rx.recv() {
                    job(&mut host);
                }
            })
            .expect("spawn the wechat offering host thread");
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
            .expect("the wechat offering host thread is alive");
        rx.recv().expect("the wechat offering host thread answered")
    }
}

/// Which offering (and which room session) a participant openid is currently acting in.
#[derive(Debug, Clone)]
struct ActiveRoom {
    /// The offering registry key ([`MENU_KEY`] while the participant is browsing the menu).
    key: String,
    /// The host [`OfferingHost`] session the participant's replies advance (their own `wx:<openid>`
    /// for a solo session, or a shared room id).
    room: SessionId,
}

/// The outcome of a [`WeChatHost::reply`] — an inbound numbered reply routed through the host.
#[derive(Debug)]
pub enum WeChatReply {
    /// A menu reply opened the named offering for the participant (its surface is now presented).
    Opened(String),
    /// A play reply advanced the active offering by one real turn (the [`Outcome`] is the
    /// substrate's — a real landed receipt, or a real executor refusal / anti-ghost).
    Advanced {
        /// The offering key the reply advanced.
        key: String,
        /// The real substrate outcome.
        outcome: Outcome,
    },
    /// The reply did not resolve to any affordance currently on the participant's surface — an honest
    /// frontend-level refusal, BEFORE the substrate (the executor is never reached).
    NotOffered,
    /// The participant has nothing open (no menu / offering presented to their conversation yet).
    NoSession,
}

/// **The multi-offering WeChat host.** Bundles the thread-confined [`OfferingHost`] (the registry of
/// offerings + their live sessions) with the [`WeChatFrontend`] (the affordance-renderer over the
/// injected transport), and routes a participant's inbound numbered reply to the right
/// `(offering, room)`.
///
/// Generic over the injected [`Transport`] `T`, so the whole thing drives token- and network-free
/// with [`crate::transport::MockTransport`] in a test and over a live `RawWeChatApi` in production.
pub struct WeChatHost<T: Transport> {
    /// The bot master secret — the root of every user's derived identity (and of the council
    /// electorate this host registers).
    bot_secret: [u8; 32],
    /// The offering registry, confined to its owning thread.
    host: HostThread,
    /// The WeChat affordance-renderer over the transport (records what each participant last saw).
    frontend: WeChatFrontend<T>,
    /// Which offering + room each participant openid's surface is currently onto (or [`MENU_KEY`]
    /// while browsing). Keyed by the participant's `wx:<openid>` [`SessionId`]; a reply routes here.
    active: HashMap<SessionId, ActiveRoom>,
}

impl<T: Transport> WeChatHost<T> {
    /// Build a host over the DEFAULT offerings (dungeon + council + market), sending through
    /// `transport`, with the council electorate derived from `council_member_openids` (WeChat OpenIDs
    /// whose derived identities are registered as council members — so those users can really vote).
    /// See [`wechat_default_host`].
    pub fn new(bot_secret: [u8; 32], transport: T, council_member_openids: &[&str]) -> Self {
        // Derive the council electorate on THIS thread (a pure derivation → `[u8; 32]` pubkeys, Send),
        // then move it into the host-thread build closure. The member identity a proposal / vote is
        // attributed to is `hex(pubkey)` — exactly the identity `identity(openid)` derives, so a
        // WeChat member's reply matches the registered council member.
        let members: Vec<[u8; 32]> = council_member_openids
            .iter()
            .map(|oid| Self::council_member_pubkey(&bot_secret, oid))
            .collect();
        let host = HostThread::spawn(move || wechat_default_host(members));
        WeChatHost {
            bot_secret,
            host,
            frontend: WeChatFrontend::new(bot_secret, transport),
            active: HashMap::new(),
        }
    }

    /// Build a host over a caller-provided offering registry (the offerings are registered inside
    /// `build`, which runs on the owning thread). Lets a deployment register its own offering set.
    pub fn with_host(
        bot_secret: [u8; 32],
        transport: T,
        build: impl FnOnce() -> OfferingHost + Send + 'static,
    ) -> Self {
        WeChatHost {
            bot_secret,
            host: HostThread::spawn(build),
            frontend: WeChatFrontend::new(bot_secret, transport),
            active: HashMap::new(),
        }
    }

    /// The registered offerings (the catalog listing) — key + title + live-session count.
    pub fn list_offerings(&self) -> Vec<OfferingInfo> {
        self.host.run(|h| h.list_offerings())
    }

    /// Derive `openid`'s frontend-agnostic dregg identity (the replier attribution).
    pub fn identity(&self, openid: &str) -> DreggIdentity {
        self.frontend.identity(openid.to_string())
    }

    /// The council-member public key a WeChat OpenID derives to — register these as a
    /// [`CouncilOffering`] electorate so those users can vote. Pure; no host needed.
    pub fn council_member_pubkey(bot_secret: &[u8; 32], openid: &str) -> [u8; 32] {
        WeChatCipherclerk::derive(bot_secret, openid)
            .agent()
            .public_key()
            .0
    }

    /// Borrow the frontend (e.g. a test's [`crate::transport::MockTransport`] via
    /// [`WeChatFrontend::transport`], or a participant's last-presented surface).
    pub fn frontend(&self) -> &WeChatFrontend<T> {
        &self.frontend
    }

    /// The offering the participant `openid` is currently playing (`None` if nothing is open, or the
    /// sentinel while the offerings menu is showing).
    pub fn active_offering(&self, openid: &str) -> Option<&str> {
        let psid = WeChatFrontend::<T>::session_id(openid);
        self.active
            .get(&psid)
            .map(|a| a.key.as_str())
            .filter(|k| *k != MENU_KEY)
    }

    /// The host room session the participant `openid`'s replies currently advance (`None` if nothing
    /// is open; the menu sentinel points at the participant's own session). Useful to
    /// [`verify`](Self::verify) the chain a shared-room participant is playing.
    pub fn active_room(&self, openid: &str) -> Option<SessionId> {
        let psid = WeChatFrontend::<T>::session_id(openid);
        self.active.get(&psid).map(|a| a.room.clone())
    }

    /// **Present the `/offerings` control message** to `openid` — an OA text message whose numbered
    /// reply list is one line per registered offering (a reply of its number opens that offering in
    /// the user's conversation). Records the participant as "browsing the menu". Returns the
    /// participant's `wx:<openid>` [`SessionId`].
    pub fn present_offerings_menu(&mut self, openid: &str) -> SessionId {
        let psid = WeChatFrontend::<T>::session_id(openid);
        let offerings = self.list_offerings();
        // The menu is a real affordance surface: each offering is a `TURN_OPEN` actuation carrying its
        // stable catalog index, so the shared `WeChatBackend` numbers it and a reply resolves it.
        let items: Vec<MenuItem> = offerings
            .iter()
            .enumerate()
            .map(|(i, o)| MenuItem {
                label: format!("Play {}", o.title),
                turn: TURN_OPEN.to_string(),
                arg: i as i64,
                enabled: true,
            })
            .collect();
        let surface = Surface(ViewNode::Section {
            title: "DreggNet Cloud — all offerings, any surface".to_string(),
            tag: "accent".to_string(),
            children: vec![
                ViewNode::Text(
                    "Pick an offering — reply with its number. Each move is a real, verifiable \
                     executor turn."
                        .to_string(),
                ),
                ViewNode::Menu { items },
            ],
        });
        self.frontend.spin_session(psid.clone());
        self.frontend
            .present(&psid, &surface, &self.menu_actions(&offerings));
        self.active.insert(
            psid.clone(),
            ActiveRoom {
                key: MENU_KEY.to_string(),
                room: psid.clone(),
            },
        );
        psid
    }

    /// The advisory action slice for the menu surface (the numbered list is derived from the tree
    /// itself; this is only for the `Frontend::present` signature parity).
    fn menu_actions(&self, offerings: &[OfferingInfo]) -> Vec<Action> {
        offerings
            .iter()
            .enumerate()
            .map(|(i, o)| Action::new(format!("Play {}", o.title), TURN_OPEN, i as i64, true))
            .collect()
    }

    /// **Open an offering session SOLO for `openid`** — the canonical single-player per-`(offering,
    /// openid)` case: the room session IS the user's own `wx:<openid>` session. Ensure it is live
    /// (seeded from the id) and present the offering's current [`Surface`] as the user's numbered
    /// reply list. Errors if `key` is unregistered. Returns the room [`SessionId`].
    pub fn open(&mut self, key: &str, openid: &str) -> Result<SessionId, HostError> {
        let room = WeChatFrontend::<T>::session_id(openid);
        self.open_into(key, &room, &room)?;
        Ok(room)
    }

    /// **Join a SHARED room session `room` as participant `openid`** — open the room on the host
    /// (seeded from `room`) if not already live, and present its current surface to `openid`'s
    /// conversation, recording the participant active on it. Several openids can join one room, each
    /// acting on the SAME host session with their own derived identity — how a collective offering (a
    /// quorum council, a multi-bidder market) plays over 1:1 OA conversations. Re-joining refreshes
    /// the participant's surface to the room's current state (a live OA re-renders on each inbound
    /// poll). Errors if `key` is unregistered.
    pub fn join(&mut self, key: &str, room: &SessionId, openid: &str) -> Result<(), HostError> {
        let psid = WeChatFrontend::<T>::session_id(openid);
        self.open_into(key, room, &psid)
    }

    /// Ensure the host room session `(key, room)` is live (seeded from `room`), then present its
    /// current surface to the participant surface `psid`, recording it active. The shared opener
    /// behind [`open`](Self::open) (solo: `psid == room`), [`join`](Self::join) (shared), and a
    /// menu-open reply.
    fn open_into(
        &mut self,
        key: &str,
        room: &SessionId,
        psid: &SessionId,
    ) -> Result<(), HostError> {
        {
            let k = key.to_string();
            let r = room.clone();
            self.host.run(move |h| h.ensure_open(&k, &r))?;
        }
        self.present_room(key, room, psid);
        Ok(())
    }

    /// Re-derive `(key, room)`'s current surface + actions from the live host session and present
    /// them to the participant surface `psid` (keeping that conversation's affordance surface current
    /// for the next reply), recording the offering + room active for the participant.
    fn present_room(&mut self, key: &str, room: &SessionId, psid: &SessionId) {
        let (surface, actions) = {
            let k = key.to_string();
            let r = room.clone();
            self.host
                .run(move |h| (h.render(&k, &r), h.actions(&k, &r)))
        };
        if let (Some(surface), Some(actions)) = (surface, actions) {
            self.frontend.spin_session(psid.clone());
            self.frontend.present(psid, &surface, &actions);
            self.active.insert(
                psid.clone(),
                ActiveRoom {
                    key: key.to_string(),
                    room: room.clone(),
                },
            );
        }
    }

    /// **Route an inbound numbered reply.** Reconstruct the participant from the message's OpenID,
    /// resolve the reply against the surface currently on THEIR conversation
    /// ([`WeChatFrontend::collect`] — a reply number naming a presented option, or a `#<turn>:<arg>`
    /// marked id / value reply), and:
    /// - if the participant is browsing the menu, OPEN (solo) the offering the reply names;
    /// - otherwise ADVANCE the active room's offering by ONE real turn on the substrate (attributed
    ///   to the sender's derived identity) and re-present the participant's surface.
    ///
    /// A reply that resolves to nothing the surface presented (ordinary prose, an out-of-range
    /// number) is [`WeChatReply::NotOffered`] (refused BEFORE the substrate); a reply from a
    /// participant with nothing open is [`WeChatReply::NoSession`]. The executor stays the sole
    /// referee of what LANDS (a below-reserve bid, a double-vote, a killing blow are all real
    /// substrate refusals, surfaced as [`WeChatReply::Advanced`] with an [`Outcome::Refused`]).
    pub fn reply(&mut self, ev: WeChatMessage) -> WeChatReply {
        let openid: OpenId = ev.from_openid.clone();
        let psid = WeChatFrontend::<T>::session_id(&openid);
        let Some(active) = self.active.get(&psid).cloned() else {
            return WeChatReply::NoSession;
        };
        // Resolve the reply against THIS participant's presented surface + attribute to their identity.
        let Some((_psid, action, actor)) = self.frontend.collect(ev) else {
            return WeChatReply::NotOffered;
        };

        if active.key == MENU_KEY {
            // A menu reply: open (solo) the offering the number names (by stable catalog index).
            if action.turn != TURN_OPEN {
                return WeChatReply::NotOffered;
            }
            let offerings = self.list_offerings();
            let Some(info) = offerings.get(action.arg as usize) else {
                return WeChatReply::NotOffered;
            };
            let key = info.key.clone();
            // Open the offering's SOLO host session (room == the participant's own session).
            if self.open_into(&key, &psid, &psid).is_err() {
                return WeChatReply::NotOffered;
            }
            return WeChatReply::Opened(key);
        }

        // A play reply: the CORE resolves the typed action on the real substrate — one turn — on the
        // participant's active room, attributed to the sender's derived identity.
        let key = active.key;
        let room = active.room;
        let outcome = {
            let k = key.clone();
            let r = room.clone();
            self.host.run(move |h| h.advance(&k, &r, action, actor))
        };
        match outcome {
            Some(outcome) => {
                // Re-present the (possibly-advanced) committed room state to this participant so the
                // next reply resolves against the current surface.
                self.present_room(&key, &room, &psid);
                WeChatReply::Advanced { key, outcome }
            }
            // The host had no such session (should not happen: `active` implies a live room session).
            None => WeChatReply::NoSession,
        }
    }

    /// Re-verify `(key, room)`'s committed chain by the offering's own proof (`None` if absent).
    pub fn verify(&self, key: &str, room: &SessionId) -> Option<VerifyReport> {
        let key = key.to_string();
        let room = room.clone();
        self.host.run(move |h| h.verify(&key, &room))
    }

    /// The bot master secret (for a deploy to sign on a user's behalf; the frontend attributes with
    /// the public identity alone).
    pub fn bot_secret(&self) -> &[u8; 32] {
        &self.bot_secret
    }
}

/// **The default WeChat catalog host** — registers the three heterogeneous offerings the catalog
/// plays: the dungeon (a game), the council (governance), the market (commerce). Built on the host's
/// owning thread, so each offering's `!Send` internals stay confined. Mirrors
/// [`dreggnet_telegram::host::telegram_default_host`] exactly (same keys, titles, catalog, quorum) —
/// only the surface differs. `council_members` is the electorate (member public keys — a WeChat user
/// whose derived identity is one of these can vote); pass the
/// [`WeChatHost::council_member_pubkey`] of each voter's OpenID.
pub fn wechat_default_host(council_members: Vec<[u8; 32]>) -> OfferingHost {
    let mut host = OfferingHost::new();
    host.register(
        "dungeon",
        "The Warden's Keep — a verifiable dungeon (offering #0)",
        DungeonOffering::new(),
    );
    host.register(
        "council",
        "DreggNet Council — propose · vote · enact",
        CouncilOffering::new(
            council_members,
            vec![
                CandidateProposal::new("Fund the archive", 42),
                CandidateProposal::new("Ratify the charter", 7),
            ],
            2, // quorum M = 2 (both members must approve)
        ),
    );
    host.register(
        "market",
        "DreggNet Market — a sealed-bid auction (list · bid · settle)",
        MarketOffering::new(),
    );
    host
}
