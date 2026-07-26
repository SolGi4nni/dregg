//! # `dreggnet-web` — the WEB [`Frontend`] over the ONE offering core.
//!
//! The third surface (Discord #0 · Telegram · **web**) over the frontend-agnostic
//! [`dreggnet_offerings`] core. A [`WebFrontend`] is an **affordance-renderer**: it derives a
//! per-web-user [`DreggIdentity`], `present`s an offering's [`Surface`], `collect`s a web POST
//! back into a typed `(SessionId, Action, DreggIdentity)`, and — its web-specific job —
//! [`renders`](WebFrontend::render) that deos [`Surface`] into an **HTML fragment**: the room
//! prose/state plus a `<form>`/`<button>` per cap-gated affordance, each POSTing its [`Action`].
//!
//! [`WebState`] hosts the axum surface over a [`DungeonOffering`] (offering #0):
//! - `GET  /session/{id}`        — open (lazily, seeded from the id) + render the current
//!   [`Surface`] as a full HTML page (the fragment wrapped in a document);
//! - `POST /session/{id}/act`    — read the web identity (a `dregg_user` cookie / `?user=`
//!   param), [`collect`](Frontend::collect) the `{turn, arg}` form back into the presented
//!   [`Action`], [`advance`](dreggnet_offerings::Offering::advance) ONE real turn on the
//!   substrate, and re-render (a legal move lands a real receipt; an illegal one is a real
//!   executor refusal surfaced as an honest banner — the anti-ghost tooth);
//! - `GET  /session/{id}/verify` — re-verify the whole committed chain by replay.
//!
//! The executor stays the sole referee: the web surface never trusts a rendered `enabled`
//! decoration — a crafted POST of a dimmed affordance still lands as a real
//! [`Outcome::Refused`](dreggnet_offerings::Outcome::Refused) on the substrate.
//!
//! ## The multi-offering catalog — all offerings, any surface
//!
//! [`WebState`] above hosts offering #0 alone. [`CatalogState`] + [`catalog_router`] make the web a
//! **multi-offering catalog** over the frontend-agnostic [`OfferingHost`]: browse the registered
//! offerings and play ANY of them in the browser through the SAME verbs, the `Session` type erased.
//! - `GET  /offerings`                           — the catalog (a card + "play" link per offering);
//! - `GET  /offerings/{key}/session/{id}`        — open (lazily) + render an offering session;
//! - `POST /offerings/{key}/session/{id}/act`    — advance ONE real turn on that offering + re-render;
//! - `GET  /offerings/{key}/session/{id}/verify` — re-verify that offering's committed chain.
//!
//! [`catalog_default_host`] delegates to the shared full DreggNet catalog. Because some sessions are
//! `!Send`, the host runs on ONE owning thread behind a `Send + Sync` [`HostThread`] handle (the
//! discord-bot `Store` pattern generalised to a whole registry) — the SAME host a Telegram / WeChat
//! frontend adopts unchanged.
//!
//! ## Honest scope
//! This renders the affordance [`Surface`] as HTML **directly** (server-rendered forms). The
//! fuller path — `deos-js` + `deos-web-cells` (the live signal-bound web cell rendering, where
//! a `bind`/`gauge`/`tabs` node is a fine-grained reactive DOM binding) — is the follow-up, as
//! is a real deployment (a served bind address, a session store, `dregg-pay` credit debits on
//! the paid tier). What is proven here: a REAL `Frontend` over `dreggnet-offerings`, served via
//! axum, DRIVEN — affordances → HTML controls, a POST → an `Action` → one real turn, a session
//! playing through, executor-refereed, `verify` holding.

/// The SIGNED-turn route (`POST /offerings/{key}/session/{id}/act-signed`): the verifying consumer
/// of the extension's `dregg.signOfferingTurn` — a JSON `SignedAction` wire verified into one real
/// turn via `OfferingHost::advance_signed`. See [`act_signed`].
pub mod act_signed;

/// **The automatafl front door** — the bespoke table surface over the generic offering rails:
/// `GET /automatafl` (rules + CTA), `POST /automatafl/table` (mint a SEAT-LOCKED table and its two
/// unguessable seat links), `GET /automatafl/table/{id}` (take a seat), `GET /automatafl/watch/{id}`
/// (spectate the fogged board), plus the realtime surface stream both that route and the generic
/// `GET /offerings/{key}/session/{id}/events` share. See [`automatafl_web`].
pub mod automatafl_web;

/// The audit emitter — the interaction envelope around every catalog/Mini-App decision
/// (docs/BOT-AUDIT-LOGGING-DESIGN.md).
pub mod audit;
/// Viewer-blind HTML consent and receipt provenance for explicit paid Chutes narration.
pub mod chutes_consent;
/// THE CROWD-STREAM ROUND DRIVER (docs/CROWD-STREAM-ENGINE-DESIGN.md): live-stream events →
/// weighted ballots → the real quorum-certified `dungeon_on_dregg::collective::CollectiveRound` →
/// ONE certified world turn per window. See [`crowd_round::CrowdRound`].
pub mod crowd_round;
/// THE SPECTATOR / PROVENANCE surface for *The Descent* (the flagship's growth artifact): a
/// stranger opens a URL and INDEPENDENTLY re-verifies a run — a re-verified no-cheat leaderboard
/// (`GET /descent/leaderboard`) + a run-card that re-executes the recorded run to PASS/FAIL
/// (`GET /descent/run/{id}`). Additive; see [`descent::descent_router`].
pub mod descent;
/// THE SHARED RUN'S PICTURE — the run-card's shaft renderer (`GET /descent/native/run/{id}`). The
/// share link is how a stranger first meets the game, so the card paints the LIVE surface's board
/// (same glyphs, same one-column-per-relic shaft) as it stood when the run ended: what was banked,
/// what was still in the pack when the light died, how deep they got. See [`descent_card`].
mod descent_card;
/// THE PLAYABLE web front door for *The Descent* (backlog H1): `GET /descent/play` mounts a
/// same-origin, strict-CSP DOM controller (`NATIVE_PLAY_APP_JS`) over the Lean-native
/// `NativeDescentWorld` (the wasm `bindings_native_descent` executor) — NOT the `<dregg-descent>`
/// element and NOT the old procgen wasm `DescentWorld` — so a stranger plays a real, private,
/// replay-verifiable run in the tab, not the leaderboard. Additive + state-free; see
/// [`descent_play::descent_play_router`].
pub mod descent_play;
/// The durable sqlite (rusqlite) backing for the Descent no-cheat leaderboard: persist a run's
/// reproducible public input (the day seed + the move sequence), re-verified by REPLAY on boot so
/// the board survives restart and a tampered row cannot resurrect a cheat. See [`descent_store`].
pub mod descent_store;
/// THE DISCORD ACTIVITY surface's trust root (`/da` scope): the server-minted **activity ticket**
/// (`mint_ticket`) and its PURE, gate-ordered validator (`validate_ticket_at`) — the OAuth-verified
/// analog of Telegram's initData envelope, over the SAME custodial identity the in-chat Discord bot
/// derives (`dreggnet_discord_identity::seed_for`). The `/da/token` OAuth exchange, the routes and
/// the Activity shell are the named follow-up (they need `DISCORD_CLIENT_SECRET`). See
/// [`discord_activity`] and `docs/DISCORD-ACTIVITIES-DESIGN.md`.
pub mod discord_activity;
/// THE CHAIN EXPLORER — `GET /explorer`, a rendering of what has actually happened on a live
/// node: its cells (owned state), its per-agent receipt chains (turns), the blocklace DAG, the
/// attested ledger roots, and an IN-BROWSER check of a cell-inclusion proof. Reads the node
/// through a GET-only, path-allowlisted, credential-free hop at `/explorer/node/{*path}`
/// (`DREGG_NODE_URL`); with no node configured it says so rather than rendering an empty table.
/// See [`explorer`].
pub mod explorer;
/// One hosted binary-operation transport shared by the web, Telegram Mini App,
/// and Discord Activity authentication wrappers. Concrete operations remain
/// independently feature-gated.
#[cfg(feature = "hosted-binary-operations")]
pub mod fhegg_operation;
/// The one browser interaction grammar shared by every game offering.
pub mod game_session;
/// **`GET /guide` — how to play**, for a reader who has never heard of any of this. The product's
/// only guide material was developer-facing (`docs/guide/`), so a stranger who wanted to know what a
/// turn was had a leaderboard, a card grid and a board, and nothing that answered. Under a
/// no-private-vocabulary rule enforced by its own tests. See [`guide`].
pub mod guide;
/// **ONE PLAYER ACROSS SURFACES** — `GET`/`POST /identity/link`. A player's web identity
/// ([`seed_identity`], 24 self-held words) and their Discord/Telegram identity (a key the operator's
/// `bot_secret` derives) were **different people with different histories on the same board**. This
/// closes that with a PROVEN link, never an asserted one: the bot mints a single-use code whose
/// freshness key is derived per `(platform, account)`, and the web page verifies it while the phrase
/// is transiently in hand and signs the canonical
/// [`webauth_core::link_claim`] with the phrase's key. The two keys stay DISTINCT with their
/// custody difference intact — only the VIEW unions. Mounted iff a platform identity secret
/// resolves. See [`identity_link`].
pub mod identity_link;
/// Prometheus metrics for the web surface (the `node/src/metrics.rs` pattern): the idempotent
/// process-global recorder + the `GET /metrics` handler + the named emit helpers this surface's
/// call sites bump (session opens/evictions, policy refusals, executor refusals, anchor + resume
/// failures). See [`metrics`].
pub mod metrics;
/// THE CROWD-STREAM OVERLAY (docs/CROWD-STREAM-ENGINE-DESIGN.md): a transparent-background OBS vote
/// surface + the FIRST server→browser SSE push in `dreggnet-web` — `GET /overlay`, `GET /overlay/sse`,
/// `POST /overlay/ingest[/youtube]`, driven off a [`crowd_round::CrowdRound`]. See [`overlay`].
pub mod overlay;
/// The seat-claiming adapter that makes `dregg-multiway-tug` playable by real frontend users (a web
/// actor is a derived internal label, never the game's canonical seat string). See
/// [`seated::SeatedTug`].
pub mod seated;
/// **A DURABLE, RECOVERABLE PLAYER IDENTITY** — `GET /identity` plus the claim/confirm/restore/
/// release posts. 24 BIP39 words (`dregg_sdk::mnemonic`, path `dregg/0` — the CLI's own constant)
/// derive an Ed25519 keypair whose PUBLIC KEY *is* the [`DreggIdentity`], so the same words
/// reproduce the same player on any device and a phrase-holding client can sign as them on
/// `/act-signed`. An OPT-IN upgrade over the anonymous visitor cookie, never a wall in front of
/// play. Read the module doc for where the key lives and what that exposes. See [`seed_identity`].
pub mod seed_identity;
/// The deterministic generative art surface: a `dreggnet_asset::AssetId` → a byte-identical SVG
/// sprite (`dreggnet-sprite`), served at `GET /sprite/{kind}/{ref}`, painted onto an asset-bearing
/// deos `Tile`, and shown in a `GET /gallery`. See [`sprite`].
pub mod sprite;
/// THE TELEGRAM MINI APP surface (`/tg` scope): initData HMAC-validated Telegram identity → the
/// SAME derived dregg identity the in-chat bot uses (`dreggnet_telegram::cipherclerk`) → turns
/// landing with **verified `Attribution::Signed`** provenance via an atomic custodial sign +
/// `advance_signed` on the host thread. Mounted iff `TELEGRAM_BOT_TOKEN` is set. See
/// THE SHARED FRONT DOOR every seat-locked two-player table runs — mint / seat link / resign /
/// spectate / realtime stream, parameterised by a [`table_seats::TableLock`]. Automatafl and the
/// tug both mount THIS; there is deliberately no second implementation of the joining flow.
pub mod table_door;
/// THE SEAT LOCK + THE TABLE CLOCK — unguessable table ids, per-seat secret labels derived under
/// one server key, the act-path gate that refuses everybody else, and the registry that records
/// how an abandoned table ended. See [`table_seats`].
pub mod table_seats;
/// THE TELEGRAM MINI APP surface (`/tg` scope): initData HMAC-validated Telegram identity → the
/// SAME derived dregg identity the in-chat bot uses (`dreggnet_telegram::cipherclerk`) → turns
/// landing with **verified `Attribution::Signed`** provenance via an atomic custodial sign +
/// `advance_signed` on the host thread. Mounted iff `TELEGRAM_BOT_TOKEN` is set. See
/// [`telegram_miniapp`] and `docs/TELEGRAM-MINIAPP-DESIGN.md`.
pub mod telegram_miniapp;
pub mod tg_link_page;
/// THE MULTIWAY-TUG FRONT DOOR — `GET /tug` (rules + CTA), `POST /tug/table` (mint a seat-locked
/// table + two unguessable seat links), `GET /tug/watch/{id}` (spectate with both hands fogged).
/// The tug had none of this: every visitor was pointed at ONE global table. See [`tug_web`].
pub mod tug_web;
/// THE VERIFIED SETTLEMENT GATE — install `dregg-exec-lean`'s Lean-backed gate into the four
/// FFI-free coordination seams, and PROVE it decides, once at startup. Without this the sealed-bid
/// market's `settle` refuses (`no verified gate registered`) after the listing and the bids have
/// already landed. See [`verified_settlement`].
pub mod verified_settlement;
mod web_identity_http;
/// **`GET /you` (and `/me`) — the page where a player sees their own record**: the tables this
/// server is holding open for them, the Descent runs the board has under their label, and the
/// receipts their own landed moves minted. Pure assembly over stores that already exist, and
/// deliberately flat about what it cannot know (a `?user=` label is REFUSED here; the browser's
/// Descent pseudonym lives in that tab's local storage, not in the cookie). See [`you`].
pub mod you;

pub use descent::{BoardRun, DescentState, descent_router, run_share_path};
// The run's one comparable number. Re-exported (rather than made a module) because it rides on the
// public [`descent::BoardRun`], so it has to be REACHABLE from outside even though the card module
// that computes it stays private. See [`descent_card::RunScore`] for the standing statement that it
// is a READ over committed facts and not a ranking rule.
pub use descent_card::RunScore;
pub use verified_settlement::{
    install_failure_advice, install_verified_settlement_gate, verified_settlement_available,
};
pub use you::{YouState, you_router};

use std::collections::HashMap;
use std::sync::mpsc::{SyncSender, sync_channel};
use std::sync::{Arc, Mutex};

use axum::{
    Router,
    extract::{Form, Path, Query, State},
    http::{HeaderMap, StatusCode, header},
    middleware,
    response::{Html, IntoResponse, Json, Response},
    routing::{get, post},
};
use serde::Deserialize;

use deos_view::{CoordCell, MenuItem, SessionFormBackend, SurfaceBackend, ViewNode};
#[cfg(feature = "hosted-binary-operations")]
use dreggnet_offerings::BinaryOperationDescriptor;
use dreggnet_offerings::dungeon::{DungeonOffering, DungeonSession};
use dreggnet_offerings::player_turn_receipt::{PlayerReplaySurface, PlayerTurnReceipt};
use dreggnet_offerings::{
    Action, Attribution, DreggIdentity, FileResumeStore, Frontend, HostError, Offering,
    OfferingHost, OfferingInfo, Outcome, PolicyRefusal, SessionConfig, SessionId, SessionPolicy,
    Surface, SweepReport, SystemClock, VerifyReport,
};

use dreggnet_catalog::{
    GameActionRef, GameAffordance, GameAudience, GameEpochError, GameEpochLedger,
    GameHostIncarnation, GameResult, GameSessionBinding, GameSessionRef, GameSpineError,
    PlayerWorlds, PublicGameReceipt, execute_bound_asserted_game_turn, game_kind,
    inspect_bound_game_session, is_rpg_key, project_public_game_receipt,
};

pub(crate) use web_identity_http::{web_user, web_user_established};

/// The single shared anonymous world label for UNestablished RPG touches. Every raw `?user=`
/// assertion that is not backed by a durable `dregg_user` cookie collapses to THIS one identity, so
/// a `?user=1,2,…,N` flood mints ONE bounded anonymous world (the shared demo world for anonymous
/// visitors) instead of N private ones — see [`catalog_route_viewer`].
const ANONYMOUS_RPG_LABEL: &str = "anonymous-visitor-shared-world";

/// **The identity a browser catalog route routes + attributes with.** A per-identity [`is_rpg_key`]
/// surface materializes a full private world on first touch ([`CatalogState::run_offering`] →
/// `PlayerWorlds::host_mut`); minting one keyed on a raw, unauthenticated `?user=` param is the
/// unbounded-host DoS. So for an RPG key touched by an UNestablished identity (a `?user=` not backed
/// by the durable `dregg_user` cookie), the routing identity collapses to a single shared anonymous
/// world ([`ANONYMOUS_RPG_LABEL`]) — capped hard, and lossless (the bounded LRU rebuilds it by
/// replay). An ESTABLISHED (cookie-backed) identity keeps its own world; every NON-RPG shared table
/// (games / party / services) keeps the real viewer, so per-user attribution (a council member, a
/// game seat) is never collapsed.
fn catalog_route_viewer(key: &str, user: &str, established: bool) -> (String, DreggIdentity) {
    if is_rpg_key(key) && !established {
        (
            ANONYMOUS_RPG_LABEL.to_string(),
            web_identity(ANONYMOUS_RPG_LABEL),
        )
    } else {
        // `resolve_identity`, not `web_identity`: a mac-valid CLAIMED label
        // (`dregg-id-<pubkey_hex>.<mac>`, minted only by `seed_identity`) resolves to the public
        // key ITSELF, so a phrase-backed player is the same `DreggIdentity` the signed
        // `/act-signed` route verifies to. Every other label — visitor token, seat label, explicit
        // `?user=`, the council electorate — takes the historical `blake3(label)` path, byte for
        // byte unchanged.
        (user.to_string(), seed_identity::resolve_identity(user))
    }
}

/// What the web frontend last presented for a session — the deos [`Surface`] and the cap-gated
/// [`Action`]s beside it (what it paints as HTML forms). Mirrors `mock::Presented`.
#[derive(Debug, Clone)]
pub struct Presented {
    /// The presented deos affordance surface (the view-tree the HTML renderer walks).
    pub surface: Surface,
    /// The affordances presented alongside it (each an HTML form/button).
    pub actions: Vec<Action>,
}

/// A web platform interaction — a POST of a presented affordance form. Stands in for the Discord
/// `ComponentInteraction` / Telegram `CallbackQuery`; carries the session it targets, the web
/// user (mapped to a [`DreggIdentity`] via [`WebFrontend::identity`]), and the `{turn, arg}`
/// pressed. Mirrors `mock::MockEvent` (the frontend-agnostic proof: the SAME round-trip).
#[derive(Debug, Clone)]
pub struct WebEvent {
    /// The session the POST targets.
    pub session: SessionId,
    /// The web user id (a `dregg_user` cookie / `?user=` param) → a derived [`DreggIdentity`].
    pub user: String,
    /// The submitted affordance's verb (the form's `turn` field — matches [`Action::turn`]).
    pub turn: String,
    /// The submitted affordance's argument (the form's `arg` field — matches [`Action::arg`]).
    pub arg: i64,
}

/// **The web [`Frontend`]** — a headless affordance-renderer that records what it was asked to
/// present per session and maps a web POST back into a typed offering [`Action`], PLUS the
/// web-specific [`render`](WebFrontend::render): the deos [`Surface`] → an HTML fragment.
///
/// Platform user = a `String` (the web session user); a platform event = a [`WebEvent`]. Identity
/// is derived deterministically (blake3 of the asserted user label) so the SAME label → the SAME
/// [`DreggIdentity`]. This is stable browser attribution, not authentication: this surface neither
/// provisions a keypair nor proves that a caller owns the label it presents.
#[derive(Debug, Default)]
pub struct WebFrontend {
    presented: HashMap<SessionId, Presented>,
}

impl WebFrontend {
    /// A fresh web frontend with no open sessions.
    pub fn new() -> Self {
        WebFrontend::default()
    }

    /// What was last presented for `session` (the surface + its actions), if any.
    pub fn presented(&self, session: &SessionId) -> Option<&Presented> {
        self.presented.get(session)
    }

    /// The affordances last presented for `session` (the forms a browser would show).
    pub fn presented_actions(&self, session: &SessionId) -> &[Action] {
        self.presented
            .get(session)
            .map(|p| p.actions.as_slice())
            .unwrap_or(&[])
    }

    /// Whether a surface slot is currently open for `session`.
    pub fn is_open(&self, session: &SessionId) -> bool {
        self.presented.contains_key(session)
    }

    /// **Render a deos [`Surface`] into an HTML fragment** — the web frontend's core job. Walks
    /// the [`ViewNode`] tree: prose → `<p>`, a [`Section`](ViewNode::Section) → a titled
    /// `<section>`, and a [`Menu`](ViewNode::Menu) of cap-gated affordances → one `<form
    /// method=post action="/session/{id}/act">` PER row, carrying the affordance's `{turn, arg}`
    /// as hidden inputs and a submit `<button>` (a `!enabled` row is rendered `disabled` +
    /// dimmed — the cap tooth SHOWN, not hidden; only a decoration, the executor still refuses a
    /// crafted POST of it). This is the HTML analogue of the native cockpit painting the SAME
    /// tree to gpui widgets / the Discord renderer painting it to an embed.
    pub fn render(&self, session: &SessionId, surface: &Surface) -> String {
        // The single-session route renders through the shared deos-view server-form backend (the
        // moved-in `view_html`): one POST form per affordance, containers recursed so a nested
        // affordance is never dropped. This route maintains NO walker of its own.
        //
        // The multi-offering CATALOG route ([`render_catalog_forms`]) does keep its own walker,
        // because it POSTs to a different action (`/offerings/{key}/session/{id}/act`) and adds an
        // editable-arg input + the sprite-tile swap. That walker is NOT a silent subset: it is
        // compiler-EXHAUSTIVE over `ViewNode` (no `_ => {}`), so it cannot drop a variant, and it
        // renders the SAME affordance set as this route — the two web routes are proven to agree by
        // `tests/two_web_routes_agree.rs` (against the canonical `deos_view::actuations` carrier).
        SessionFormBackend {
            session_id: session.0.clone(),
        }
        .render(surface.view(), &[])
    }
}

impl Frontend for WebFrontend {
    type PlatformUser = String;
    type PlatformEvent = WebEvent;

    /// Derive `user`'s internal [`DreggIdentity`] label — blake3(user) hex. Deterministic: the SAME
    /// asserted web user always maps to the SAME actor. This hash is not a login or proof of key
    /// ownership.
    ///
    /// One exception, and it is the opposite of a weakening: a **claimed** label
    /// ([`seed_identity::claim_label`] — a public key plus a server-only mac) resolves to the public
    /// key itself rather than a hash of it, so the legacy `/session/{id}` surface attributes a
    /// phrase-backed player to the same identity every other surface does.
    fn identity(&self, user: String) -> DreggIdentity {
        seed_identity::resolve_identity(&user)
    }

    /// Open an (empty) surface slot for `session`.
    fn spin_session(&mut self, session: SessionId) {
        self.presented.entry(session).or_insert(Presented {
            surface: Surface(ViewNode::VStack(Vec::new())),
            actions: Vec::new(),
        });
    }

    /// Record the presented surface + actions (the HTML the next GET paints).
    fn present(&mut self, session: &SessionId, surface: &Surface, actions: &[Action]) {
        self.presented.insert(
            session.clone(),
            Presented {
                surface: surface.clone(),
                actions: actions.to_vec(),
            },
        );
    }

    /// Map a [`WebEvent`] POST back to the offering [`Action`] it names: find the presented
    /// affordance matching `(turn, arg)` and return it with the firing web user's derived
    /// identity. `None` if the session is unknown or the affordance was not presented (a POST for
    /// a control the surface did not offer — a frontend-level honest refusal, before the
    /// substrate).
    fn collect(&self, ev: WebEvent) -> Option<(SessionId, Action, DreggIdentity)> {
        let presented = self.presented.get(&ev.session)?;
        let action = presented
            .actions
            .iter()
            .find(|a| a.turn == ev.turn && a.arg == ev.arg)
            .cloned()?;
        Some((ev.session.clone(), action, self.identity(ev.user)))
    }

    /// Close `session`'s surface slot (archive on completion).
    fn teardown(&mut self, session: &SessionId) {
        self.presented.remove(session);
    }
}

/// Default cap on LIVE `/session/{id}` sessions the single-offering [`WebState`] surface holds —
/// the memory backstop against a flood of distinct arbitrary path ids. Overridable via
/// [`WebState::with_capacity`]. Sized to match `dreggnet_catalog`'s
/// [`DEFAULT_LIVE_HOST_CAPACITY`](dreggnet_catalog::player_worlds::DEFAULT_LIVE_HOST_CAPACITY).
pub const DEFAULT_WEB_SESSION_CAPACITY: usize = 1024;

/// **The single-offering web surface's live sessions under a bounded LRU** — the memory backstop
/// against a flood of distinct `GET /session/{id}` path ids (the anonymous offering-#0 DoS vector:
/// each arbitrary `{id}` used to mint an uncapped, never-evicted [`DungeonSession`]). A new id past
/// [`capacity`](BoundedSessions::capacity) first evicts the least-recently-touched session. This
/// legacy surface has NO durable store, so that eviction is lossy — but a re-open of the evicted id
/// rebuilds the SAME id-seeded genesis world, and a live viewer's session is kept hot by every
/// render touch. Mirrors `dreggnet_catalog::PlayerWorlds`'s bounded-LRU host cache.
struct BoundedSessions {
    /// The live sessions — a real `DungeonSession` (WorldCell + playthrough) per session id.
    map: HashMap<SessionId, DungeonSession>,
    /// Monotone access clock per live session — the LRU key. A touch bumps the id to `clock`;
    /// eviction removes the id with the smallest (oldest) value (tie-broken by id, deterministic).
    touched: HashMap<SessionId, u64>,
    /// The monotone tick source for `touched`.
    clock: u64,
    /// The maximum number of live sessions. Always `>= 1` (a `0` request is clamped).
    capacity: usize,
}

impl BoundedSessions {
    fn new(capacity: usize) -> Self {
        BoundedSessions {
            map: HashMap::new(),
            touched: HashMap::new(),
            clock: 0,
            capacity: capacity.max(1),
        }
    }

    /// Bump `id` to the most-recently-used position — called on every open/render touch so an
    /// actively-viewed session is never the eviction victim.
    fn touch(&mut self, id: &SessionId) {
        if self.map.contains_key(id) {
            self.clock += 1;
            self.touched.insert(id.clone(), self.clock);
        }
    }

    /// Insert a freshly-opened `session` under `id`, first LRU-evicting the coldest session(s)
    /// while at capacity. Returns the evicted ids so the caller tears down their frontend slots
    /// too (keeping `sessions` and `presented` bounded TOGETHER).
    fn insert_evicting(&mut self, id: SessionId, session: DungeonSession) -> Vec<SessionId> {
        let mut evicted = Vec::new();
        while self.map.len() >= self.capacity && !self.map.contains_key(&id) {
            let victim = self
                .touched
                .iter()
                .min_by_key(|&(vid, &tick)| (tick, vid.0.clone()))
                .map(|(vid, _)| vid.clone())
                .or_else(|| self.map.keys().next().cloned());
            match victim {
                Some(v) => {
                    self.map.remove(&v);
                    self.touched.remove(&v);
                    evicted.push(v);
                }
                None => break,
            }
        }
        self.clock += 1;
        self.touched.insert(id.clone(), self.clock);
        self.map.insert(id, session);
        evicted
    }
}

/// **The axum web surface state** — the ONE [`DungeonOffering`] core, the live per-session
/// [`DungeonSession`]s (the real verifiable state chains) under a bounded LRU, and the
/// [`WebFrontend`] recording what each session last presented. Shared behind an `Arc` as the axum
/// handler `State`.
pub struct WebState {
    /// The offering core (offering #0). Stateless factory; each session is a real playthrough.
    offering: DungeonOffering,
    /// The live sessions — a real `DungeonSession` per session id, hard-bounded by a LRU capacity
    /// so an arbitrary-`{id}` flood cannot grow memory without limit.
    sessions: Mutex<BoundedSessions>,
    /// The web frontend recording each session's last-presented surface + actions.
    frontend: Mutex<WebFrontend>,
}

impl WebState {
    /// A fresh web surface over the free-tier dungeon offering, bounded at
    /// [`DEFAULT_WEB_SESSION_CAPACITY`] live sessions.
    pub fn new() -> Self {
        WebState::with_capacity(DEFAULT_WEB_SESSION_CAPACITY)
    }

    /// A web surface over the free-tier dungeon offering with an explicit live-session LRU
    /// capacity (clamped to `>= 1`).
    pub fn with_capacity(capacity: usize) -> Self {
        WebState {
            offering: DungeonOffering::new(),
            sessions: Mutex::new(BoundedSessions::new(capacity)),
            frontend: Mutex::new(WebFrontend::new()),
        }
    }

    /// A web surface over a caller-provided offering (e.g. [`DungeonOffering::paid`]), bounded at
    /// [`DEFAULT_WEB_SESSION_CAPACITY`] live sessions.
    pub fn with_offering(offering: DungeonOffering) -> Self {
        WebState {
            offering,
            sessions: Mutex::new(BoundedSessions::new(DEFAULT_WEB_SESSION_CAPACITY)),
            frontend: Mutex::new(WebFrontend::new()),
        }
    }

    /// Whether a session is open.
    pub fn is_open(&self, id: &SessionId) -> bool {
        self.sessions.lock().unwrap().map.contains_key(id)
    }

    /// The number of live sessions currently held — hard-bounded by the LRU capacity.
    pub fn live_sessions(&self) -> usize {
        self.sessions.lock().unwrap().map.len()
    }

    /// The number of frontend surface slots currently retained — bounded in LOCKSTEP with
    /// [`live_sessions`](WebState::live_sessions): an LRU-evicted session's `presented` slot is torn
    /// down, so `presented` cannot outgrow the session map under a flood.
    pub fn presented_sessions(&self) -> usize {
        self.frontend.lock().unwrap().presented.len()
    }

    /// Ensure a session is open: on first touch, [`open`](Offering::open) a fresh
    /// [`DungeonSession`] (seeded deterministically from the session id, so a re-open of the same
    /// id is the SAME replay-verifiable world), LRU-evict the coldest session(s) if the map is at
    /// capacity (tearing down their frontend slots too), spin its frontend slot, and present the
    /// initial surface (so a first POST can already `collect` the gatehall affordances). A touch of
    /// an already-live session just bumps its LRU recency.
    pub fn ensure_open(&self, id: &SessionId) {
        {
            let mut sessions = self.sessions.lock().unwrap();
            if sessions.map.contains_key(id) {
                sessions.touch(id);
                return;
            }
        }
        let session = self
            .offering
            .open(SessionConfig::with_seed(seed_from_id(&id.0)))
            .expect("the Keep opens");
        let surface = self.offering.render(&session);
        let actions = self.offering.actions(&session);
        let evicted = self
            .sessions
            .lock()
            .unwrap()
            .insert_evicting(id.clone(), session);
        let mut fe = self.frontend.lock().unwrap();
        // Tear down the frontend slots of the LRU-evicted sessions, so `presented` stays bounded
        // in lockstep with the sessions map.
        for gone in &evicted {
            fe.teardown(gone);
        }
        fe.spin_session(id.clone());
        fe.present(id, &surface, &actions);
    }

    /// Re-verify a session's whole committed chain by replay (the offering's own proof).
    pub fn verify(&self, id: &SessionId) -> Option<VerifyReport> {
        let sessions = self.sessions.lock().unwrap();
        sessions.map.get(id).map(|s| self.offering.verify(s))
    }

    /// The number of real verified turns (genesis + committed steps) in a session.
    pub fn receipts_len(&self, id: &SessionId) -> Option<usize> {
        let sessions = self.sessions.lock().unwrap();
        sessions.map.get(id).map(|s| s.receipts_len())
    }

    /// The session's current room (passage) name, if still running.
    pub fn current_room(&self, id: &SessionId) -> Option<String> {
        let sessions = self.sessions.lock().unwrap();
        sessions.map.get(id).and_then(|s| s.current_passage_name())
    }

    /// Re-derive the current surface + actions from the live session, tell the frontend to
    /// present them (keeping the affordance surface current for the next `collect`), render the
    /// fragment, and wrap it in a full HTML page with `notice` and the live verify status.
    fn render_page(&self, id: &SessionId, notice: Option<&str>) -> String {
        let (surface, actions, verify) = {
            let mut sessions = self.sessions.lock().unwrap();
            let rendered = match sessions.map.get(id) {
                Some(session) => (
                    self.offering.render(session),
                    self.offering.actions(session),
                    self.offering.verify(session),
                ),
                None => return page_missing(id),
            };
            // A render is a touch — keep an actively-viewed session hot so the LRU never evicts it
            // out from under a live player.
            sessions.touch(id);
            rendered
        };
        let fragment = {
            let mut fe = self.frontend.lock().unwrap();
            fe.present(id, &surface, &actions);
            fe.render(id, &surface)
        };
        page(id, notice, &fragment, &verify)
    }
}

impl Default for WebState {
    fn default() -> Self {
        WebState::new()
    }
}

/// The `{turn, arg}` POST body of a `POST /session/{id}/act` — the submitted affordance form
/// (`<input name=turn>` / `<input name=arg>`). `arg` is parsed straight into the [`Action`]'s
/// `i64` (the deos `{turn, arg}` wire shape).
#[derive(Debug, Clone, Deserialize)]
pub struct ActForm {
    /// The affordance verb (the dungeon's `"choose"`).
    pub turn: String,
    /// The affordance argument (the scene choice index).
    pub arg: i64,
}

/// The `?user=` query params of a request (the web identity, alongside the `dregg_user` cookie).
#[derive(Debug, Clone, Default, Deserialize)]
pub struct WebQuery {
    /// The web user id — a deterministic input to identity derivation. Absent → the cookie, then a
    /// durable pseudonymous visitor label on the browser-facing routes.
    #[serde(default)]
    pub user: Option<String>,
}

/// **Build the axum router** over a shared [`WebState`]. The web session surface:
/// - `GET  /session/{id}`        — render the current [`Surface`] as an HTML page;
/// - `POST /session/{id}/act`    — collect the form, advance one real turn, re-render;
/// - `GET  /session/{id}/verify` — re-verify the committed chain by replay (JSON).
pub fn router(state: Arc<WebState>) -> Router {
    Router::new()
        .route("/session/{id}", get(get_session))
        .route("/session/{id}/act", post(post_act))
        .route("/session/{id}/verify", get(get_verify))
        .layer(middleware::from_fn(
            web_identity_http::bootstrap_visitor_identity,
        ))
        .with_state(state)
}

/// `GET /session/{id}` — open the session (lazily) and render its current affordance surface as a
/// full HTML page (the room prose/state + a form/button per cap-gated affordance).
async fn get_session(State(state): State<Arc<WebState>>, Path(id): Path<String>) -> Html<String> {
    let id = SessionId::new(id);
    state.ensure_open(&id);
    Html(state.render_page(&id, None))
}

/// `POST /session/{id}/act` — the real-turn seam. Reads the web identity (a `dregg_user` cookie /
/// `?user=` param), [`collect`](Frontend::collect)s the `{turn, arg}` form back into the presented
/// [`Action`], and [`advance`](Offering::advance)s ONE real turn on the substrate. A legal move
/// lands a real receipt (the world moves); an illegal / crafted one is a real executor
/// [`Outcome::Refused`] surfaced as an honest banner — nothing commits (anti-ghost). Re-renders
/// the (possibly-advanced) committed state.
async fn post_act(
    State(state): State<Arc<WebState>>,
    Path(id): Path<String>,
    headers: HeaderMap,
    Query(query): Query<WebQuery>,
    Form(form): Form<ActForm>,
) -> Html<String> {
    let id = SessionId::new(id);
    state.ensure_open(&id);

    let user = web_user(&headers, &query);
    let ev = WebEvent {
        session: id.clone(),
        user,
        turn: form.turn,
        arg: form.arg,
    };

    // Collect the POST back into the typed Action + the firing web user's derived identity.
    let collected = {
        let fe = state.frontend.lock().unwrap();
        fe.collect(ev)
    };

    let notice = match collected {
        None => {
            // A POST for a control the surface never offered — an honest frontend-level refusal,
            // before the substrate.
            "Refused: that affordance is not on the current surface.".to_string()
        }
        Some((_sid, action, actor)) => {
            // The CORE resolves the collected action on the substrate — ONE real turn. A touch of
            // an existing session keeps it hot (LRU), so an active player is never the flood's
            // eviction victim mid-turn.
            let outcome = {
                let mut sessions = state.sessions.lock().unwrap();
                let out = sessions
                    .map
                    .get_mut(&id)
                    .map(|session| state.offering.advance(session, action, actor));
                sessions.touch(&id);
                out
            };
            match outcome {
                // The session was LRU-evicted between `ensure_open` and now (only reachable under a
                // concurrent flood of other ids). An honest refusal — never a panic (that would
                // reintroduce a DoS while closing one).
                None => "Refused: the session is no longer live (evicted under load) — reload the \
                         page to resume from its committed state."
                    .to_string(),
                Some(Outcome::Landed { receipt, ended }) => {
                    let card = PlayerTurnReceipt::from_landed(&receipt, ended)
                        .compact_text(PlayerReplaySurface::Web);
                    if ended {
                        format!(
                            "The Keep is cleared — the objective is met, one real turn at a time. {card}"
                        )
                    } else {
                        format!("Turn committed — {card}")
                    }
                }
                // The executor is the sole referee: a crafted POST of a dimmed / ineligible
                // affordance lands as a REAL refusal — nothing committed, the world unmoved.
                Some(Outcome::Refused(why)) => {
                    metrics::inc_turn_refused();
                    format!("Refused: {why} (nothing committed — anti-ghost).")
                }
            }
        }
    };

    Html(state.render_page(&id, Some(&notice)))
}

/// `GET /session/{id}/verify` — re-verify the whole committed chain by replay; the offering's own
/// proof, exposed over HTTP as JSON.
async fn get_verify(
    State(state): State<Arc<WebState>>,
    Path(id): Path<String>,
) -> impl IntoResponse {
    let id = SessionId::new(id);
    match state.verify(&id) {
        Some(report) => Json(serde_json::json!({
            "verified": report.verified,
            "turns": report.turns,
            "detail": report.detail,
        })),
        None => Json(serde_json::json!({
            "verified": false,
            "turns": 0,
            "detail": "no such session",
        })),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Rendering — the deos ViewNode → HTML walk, and the page chrome.
// ─────────────────────────────────────────────────────────────────────────────

/// Wrap an HTML fragment in the full product document: the breadcrumb, the notice banner (*what
/// just happened*), the surface itself, and the receipt strip (*the chain, re-verified by replay,
/// right now*).
fn page(id: &SessionId, notice: Option<&str>, fragment: &str, verify: &VerifyReport) -> String {
    let body = format!(
        "<div class=\"crumb\"><a href=\"/offerings\">← All games</a>\
         <span class=\"sep\">·</span><strong>The Warden's Keep</strong>\
         <span class=\"sep\">·</span><span class=\"sid\">session {id}</span></div>\
         <main class=\"session\">{notice}{fragment}{receipt}</main>",
        id = esc(&id.0),
        notice = notice_html(notice),
        fragment = fragment,
        receipt = receipt_html(
            verify,
            "chain re-verified by replay",
            &format!("/session/{}/verify", esc(&id.0)),
        ),
    );
    document(&format!("{PRODUCT_NAME} — session {}", id.0), "", &body)
}

/// The page shown for a `POST` / verify against a session id that is not open.
fn page_missing(id: &SessionId) -> String {
    let body = format!(
        "<main class=\"session\"><div class=\"notice refused\" role=\"status\">No such session — \
         GET /session/{id} to open it.</div>\
         <p class=\"prose\"><a class=\"backlink\" href=\"/offerings\">← Browse all games</a></p>\
         </main>",
        id = esc(&id.0),
    );
    document(&format!("{PRODUCT_NAME} — session {}", id.0), "", &body)
}

/// **Derive a web user's frontend-agnostic [`DreggIdentity`] label** — `blake3(user)` hex.
/// Deterministic (the SAME asserted user → the SAME actor), but not authenticated and not proof of a
/// cryptographic identity. Shared by [`WebFrontend::identity`] and the multi-offering catalog's POST
/// handler so both attribute a turn to the same actor — and so a council registers its members from
/// the SAME derivation (`blake3(user)` bytes as the member pubkey; see [`catalog_default_host`]).
pub fn web_identity(user: &str) -> DreggIdentity {
    DreggIdentity(blake3::hash(user.as_bytes()).to_hex().to_string())
}

/// A deterministic session seed from a session id (so a re-open of the same id is the SAME
/// replay-verifiable world). blake3(id) → the low 8 bytes as a `u64`.
fn seed_from_id(id: &str) -> u64 {
    let h = blake3::hash(id.as_bytes());
    let b = h.as_bytes();
    u64::from_le_bytes(b[..8].try_into().unwrap())
}

/// Minimal HTML escaping for server-rendered text (no client JS; the same idiom the bot's admin
/// portal uses).
fn esc(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

fn hex_bytes(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        let _ = write!(out, "{byte:02x}");
    }
    out
}

fn decode_hex_32(value: &str) -> Option<[u8; 32]> {
    if value.len() != 64 {
        return None;
    }
    let nibble = |byte: u8| match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    };
    let mut out = [0; 32];
    for (index, pair) in value.as_bytes().chunks_exact(2).enumerate() {
        out[index] = (nibble(pair[0])? << 4) | nibble(pair[1])?;
    }
    Some(out)
}

/// The page's inlined stylesheet — **the design system** for every served surface
/// (self-contained; no external assets, no client JS).
///
/// ## The system
/// - **Elevation, not one navy.** Five deliberate ink steps (`--ink-950` … `--ink-600`): the page
///   floor, recessed wells (the board frame, table headers), panels, raised cards. The old sheet
///   painted every container the same `#111a2e`; depth now carries hierarchy.
/// - **The palette IS the argument.** Colour is semantic, never decorative: `--good` = *proven /
///   landed / legal*, `--warn` = *sealed / pending / yours*, `--bad` = *refused / failed*,
///   `--accent` = *the machine* (the automaton, identity, links). A surface's tag (`tag-good`,
///   `tag-warn`, …) therefore reads as meaning, on the board and in a section header alike.
/// - **A type scale** (`--t-micro` … `--t-display`, ~1.22 ratio) and a **4px spacing rhythm**
///   (`--s1` … `--s8`) — every margin/pad is a step on the scale, not an ad-hoc value.
/// - **The mono voice.** `--mono` carries the verifiable material: hashes, seeds, keys, turn
///   counters, and the board glyphs (so `R`/`A`/`@`/`·` sit on one optical grid).
/// - **States.** Every interactive thing has hover / active / `:focus-visible` / disabled. Motion
///   is short (≤ .18s), clarifies (a cell lift, a banner arrival), and is fully disabled under
///   `prefers-reduced-motion`.
/// - **Phone-first.** One breakpoint family at 44rem; the board keeps ≥ 44px touch targets, tables
///   scroll in their own well, and the shell never scrolls horizontally.
///
/// The board (`.coordgrid` + `.cell` + `tag-*`) is the hero: a recessed, checkered well of square
/// cells where a *piece* reads solid (an untagged cell — previously dimmed to `--muted`, the bug
/// that made the grid look like a debug dump), *vacant* recedes to a faint small dot, a *legal
/// target* is a bright mint hint, a *selected* piece rings amber, and the *automaton* glows cyan.
const STYLE: &str = r##"<style>
/* ═══ TOKENS ═════════════════════════════════════════════════════════════ */
:root{
color-scheme:dark;
--font:ui-sans-serif,system-ui,-apple-system,"Segoe UI",Roboto,"Helvetica Neue",Arial,sans-serif;
--mono:ui-monospace,SFMono-Regular,"SF Mono",Menlo,Consolas,"Liberation Mono",monospace;
/* elevation — the page floor up to a raised card */
--ink-950:#05080f;--ink-900:#080d1a;--ink-850:#0b1020;--ink-800:#0d1425;--ink-700:#121b31;--ink-600:#18243f;
--line:#243553;--line-soft:#1b2740;--line-lit:#334c73;
/* ink — three deliberate levels, all AA+ on the floor */
--fg:#e9eefc;--fg-2:#b8c6e3;--fg-3:#8a9cbe;
/* semantic — colour means something */
--accent:#5cc9ff;--good:#4fdca0;--warn:#f5c85c;--bad:#ff7b86;--head:#8ce3e4;--violet:#a78bfa;
/* THE NIGHT RECORD — dregg's own visual language (the tokens of dregg-site's `site.css` and of
   the poster theme, hex for hex). Night ground, violet = the machine, brass = the objective /
   the record. Used by the automatafl table; every other surface keeps the palette above. */
--n0:#07060b;--n1:#0b0a10;--n2:#110f18;--n3:#171426;--n-ink:#dcd8e4;--n-soft:#a49fb4;
--vio:#a89fd8;--vio-lit:#c9c0f2;--br:#b08d57;--br-lit:#d8b47e;--br-pale:#eddcb4;
--br-line:rgba(176,141,87,.42);--br-faint:rgba(176,141,87,.18);
--n-serif:"Iowan Old Style","New York",Palatino,Baskerville,Georgia,serif;
--bg:var(--ink-900);--muted:var(--fg-3);--panel:var(--ink-700);--card:var(--ink-600);--border:var(--line);
/* type scale */
--t-micro:.6875rem;--t-sm:.8125rem;--t-body:1rem;--t-lead:1.0625rem;
--t-h3:1.0625rem;--t-h2:1.25rem;--t-h1:1.75rem;--t-display:clamp(2rem,6.4vw,3.15rem);
/* rhythm */
--s1:.25rem;--s2:.5rem;--s3:.75rem;--s4:1rem;--s5:1.5rem;--s6:2rem;--s7:3rem;--s8:4.5rem;
--r-sm:8px;--r-md:12px;--r-lg:16px;--r-pill:999px;
--shell:60rem;--measure:46rem;
--ease:cubic-bezier(.2,.7,.3,1);
}
/* ═══ BASE ═══════════════════════════════════════════════════════════════ */
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%}
body{font-family:var(--font);font-size:var(--t-body);line-height:1.6;color:var(--fg);margin:0;min-height:100vh;
background:radial-gradient(1100px 560px at 50% -8%,rgba(92,201,255,.10),transparent 62%),radial-gradient(820px 460px at 88% 4%,rgba(79,220,160,.055),transparent 58%),var(--ink-900);
background-attachment:fixed;-webkit-font-smoothing:antialiased;overflow-x:hidden}
h1,h2,h3{font-weight:700;letter-spacing:-.015em}
a{color:var(--accent)}
code{font-family:var(--mono);font-size:.86em;background:rgba(92,201,255,.09);border:1px solid rgba(92,201,255,.16);border-radius:6px;padding:.08rem .36rem;color:#bfe4ff;white-space:nowrap}
strong{font-weight:700;color:var(--fg)}
:focus-visible{outline:2px solid var(--accent);outline-offset:2px;border-radius:4px}
.sr-only{position:absolute;width:1px;height:1px;padding:0;margin:-1px;overflow:hidden;clip:rect(0 0 0 0);white-space:nowrap;border:0}
/* ═══ SHELL — the topbar/footer that make every surface ONE product ═══════ */
.topbar{position:sticky;top:0;z-index:20;background:rgba(5,8,15,.72);border-bottom:1px solid var(--line-soft);backdrop-filter:blur(14px) saturate(150%);-webkit-backdrop-filter:blur(14px) saturate(150%)}
.topbar-in{max-width:var(--shell);margin:0 auto;padding:.6rem 1.25rem;display:flex;align-items:center;justify-content:space-between;gap:var(--s4)}
.brand{display:inline-flex;align-items:center;gap:.55rem;text-decoration:none;color:var(--fg);font-weight:700;font-size:var(--t-sm);letter-spacing:.01em;white-space:nowrap}
.brand svg{width:1.3rem;height:1.3rem;display:block;flex:0 0 auto}
.brand svg rect{fill:var(--line-lit);transition:fill .2s var(--ease)}
.brand svg rect.lit{fill:var(--good)}
.brand:hover svg rect{fill:#43608f}
.brand:hover svg rect.lit{fill:var(--accent)}
.topnav{display:flex;gap:.1rem;font-size:var(--t-sm)}
.topnav a{color:var(--fg-3);text-decoration:none;padding:.35rem .6rem;border-radius:var(--r-sm);font-weight:600;transition:color .14s,background .14s}
.topnav a:hover{color:var(--fg);background:rgba(255,255,255,.055)}
.topnav a[aria-current=page]{color:var(--fg);background:rgba(92,201,255,.13);box-shadow:inset 0 0 0 1px rgba(92,201,255,.24)}
.foot{max-width:var(--shell);margin:var(--s7) auto 0;padding:var(--s5) 1.25rem var(--s6);border-top:1px solid var(--line-soft);display:flex;flex-wrap:wrap;gap:var(--s2) var(--s5);align-items:center;justify-content:space-between;font-size:var(--t-sm);color:var(--fg-3)}
.foot p{margin:0}
/* The lineage line ("Dragon's Arcade is the play surface of the dregg project") sits below the
   property claim rather than beside it — it is an identification, not a headline. */
.foot .lineage{flex:1 1 100%;color:var(--fg-3);opacity:.85}
.foot nav{display:flex;gap:var(--s4)}
.foot a{color:var(--fg-2);text-decoration:none}
.foot a:hover{color:var(--accent)}
.session{max-width:var(--measure);margin:0 auto;padding:var(--s5) 1.25rem 0}
.catalog{max-width:var(--shell);margin:0 auto;padding:0 1.25rem}
.crumb{max-width:var(--measure);margin:var(--s5) auto -.35rem;padding:0 1.25rem;font-size:var(--t-sm);color:var(--fg-3);display:flex;flex-wrap:wrap;align-items:center;gap:.45rem}
.crumb a{color:var(--fg-2);text-decoration:none}
.crumb a:hover{color:var(--accent)}
.crumb .sep{color:var(--line-lit)}
.crumb strong{color:var(--fg)}
/* Same exposure as `.notice`, lower stakes: a session id is a single unbroken mono token in a
   `flex-wrap` strip, so a long one clipped instead of wrapping. */
.crumb .sid{font-family:var(--mono);font-size:var(--t-micro);color:var(--fg-3);min-width:0;overflow-wrap:anywhere}
/* ═══ TYPE ═══════════════════════════════════════════════════════════════ */
.page-head{padding:var(--s6) 0 var(--s2)}
.page-head h1{font-size:var(--t-h1);margin:0 0 .5rem;color:var(--fg)}
.deck{font-size:var(--t-lead);color:var(--fg-2);margin:0;max-width:62ch;line-height:1.62}
.eyebrow{display:inline-flex;align-items:center;gap:.45rem;font-size:var(--t-micro);text-transform:uppercase;letter-spacing:.14em;font-weight:800;color:var(--good);margin:0 0 .85rem}
.eyebrow::before{content:"";width:.4rem;height:.4rem;border-radius:50%;background:currentColor;box-shadow:0 0 10px currentColor}
.prose{margin:.45rem 0;color:var(--fg-2)}
.prose:first-child{margin-top:0}
.prose:last-child{margin-bottom:0}
/* A surface's TOP-LEVEL prose is its headline state — the automatafl phase line ("turn 0 · phase: */
/* COMMIT"), the market's standing. It sits outside every panel, so without this it read as a naked */
/* stray paragraph. Set as a lead, with the surface's top-level pills as its status chips. */
.session>.prose{font-size:var(--t-lead);color:var(--fg);font-weight:600;margin:.9rem 0 .5rem;letter-spacing:-.005em}
.session>.pill{margin-bottom:.6rem}
/* ═══ LANDING ════════════════════════════════════════════════════════════ */
.hero{max-width:var(--shell);margin:0 auto;padding:clamp(1.75rem,6vw,3.5rem) 1.25rem var(--s4);display:grid;grid-template-columns:1.12fr .88fr;gap:clamp(1.5rem,4vw,3rem);align-items:center}
.hero h1{font-size:var(--t-display);line-height:1.02;letter-spacing:-.035em;margin:0 0 .8rem;font-weight:800;background:linear-gradient(176deg,#fff 8%,#a9c4ea);-webkit-background-clip:text;background-clip:text;color:transparent}
.hero .deck{margin:0 0 var(--s5);max-width:36ch}
.cta-row{display:flex;flex-wrap:wrap;gap:.65rem}
/* ⚑ THE PLAYER COUNT, AT THE MOMENT OF CHOICE. There is no matchmaking, no queue and no bot here: a
   two-player table mints two seat links and you send one yourself. That requirement was disclosed
   one click LATER (above the "Open a table" button) and stated in `/guide`, but the choice itself —
   a hero button, a card in a grid — said nothing, so a lone visitor could pick a game needing a
   second human, read "send this link to your opponent", and leave. This chip is deliberately loud
   (uppercase, warn/good, its own line on a card) because it has to survive a SCAN, not reward a
   careful reader; `.solo` is its green counterpart so "you can start this one alone" is equally
   scannable and the pair reads as one axis. */
.needs{display:inline-flex;align-items:center;gap:.3rem;font-size:var(--t-micro);font-weight:800;text-transform:uppercase;letter-spacing:.08em;color:var(--warn);white-space:nowrap}
.needs.solo{color:var(--good)}
.btn .needs{font-size:.625rem;letter-spacing:.06em;opacity:.9}
.offering-card>.needs{margin:.15rem 0 0;white-space:normal}
.hero-art{display:flex;flex-direction:column;align-items:center;gap:.7rem}
.hero-art .af-board{margin:0}
.hero-cap{margin:0;font-size:var(--t-micro);text-transform:uppercase;letter-spacing:.11em;color:var(--fg-3);text-align:center}
.steps{max-width:var(--shell);margin:0 auto;padding:var(--s5) 1.25rem 0;display:grid;grid-template-columns:repeat(3,1fr);gap:.85rem}
.step{padding:1.05rem 1.15rem;border:1px solid var(--line-soft);border-radius:var(--r-lg);background:linear-gradient(180deg,rgba(24,36,63,.62),rgba(13,20,37,.5))}
.step .n{display:inline-flex;align-items:center;justify-content:center;width:1.55rem;height:1.55rem;border-radius:var(--r-sm);font-size:var(--t-micro);font-weight:800;font-family:var(--mono);background:rgba(92,201,255,.13);color:var(--accent);box-shadow:inset 0 0 0 1px rgba(92,201,255,.26);margin-bottom:.6rem}
.step h3{margin:0 0 .25rem;font-size:var(--t-h3);color:var(--fg)}
.step p{margin:0;font-size:var(--t-sm);color:var(--fg-3);line-height:1.6}
/* ═══ BUTTONS ════════════════════════════════════════════════════════════ */
/* `min-height:2.75rem` is the 44px tap-target floor, STATED. It is a no-op at today's padding
   (25.6px line-box + 22.4px = 48px) — which is exactly the problem it fixes: the target cleared 44px
   only INCIDENTALLY, so any future padding or font-size trim would have dropped it below the floor
   with nothing to catch it. Now the floor is a rule, not an accident. */
.btn{display:inline-flex;align-items:center;min-height:2.75rem;gap:.45rem;padding:.7rem 1.15rem;border-radius:11px;font-family:inherit;font-weight:700;font-size:var(--t-body);text-decoration:none;border:1px solid transparent;cursor:pointer;transition:transform .1s var(--ease),box-shadow .18s,background .18s,border-color .18s,color .18s}
.btn .arr{transition:transform .18s var(--ease)}
.btn:hover .arr{transform:translateX(3px)}
.btn:active{transform:translateY(0) scale(.99)}
.btn-primary{background:linear-gradient(180deg,#63e9b1,#2fb87e);color:#02251a;box-shadow:0 10px 26px -13px rgba(79,220,160,.75)}
.btn-primary:hover{transform:translateY(-1px);box-shadow:0 16px 34px -13px rgba(79,220,160,.9)}
.btn-ghost{border-color:var(--line-lit);color:var(--fg);background:rgba(255,255,255,.035)}
.btn-ghost:hover{border-color:var(--accent);color:#fff;background:rgba(92,201,255,.1);transform:translateY(-1px)}
/* ═══ CATALOG ════════════════════════════════════════════════════════════ */
.catalog-group{margin:var(--s6) 0}
.catalog-group>.group-h{display:flex;align-items:center;gap:.55rem;font-size:var(--t-micro);text-transform:uppercase;letter-spacing:.15em;font-weight:800;color:var(--fg-2);margin:0;padding:0 0 .6rem;border-bottom:1px solid var(--line-soft)}
.catalog-group>.group-h::before{content:"";flex:0 0 auto;width:.8rem;height:2px;border-radius:2px;background:var(--shelf,var(--accent));box-shadow:0 0 8px var(--shelf,var(--accent))}
.catalog-group>.group-h .count{margin-left:auto;font-family:var(--mono);letter-spacing:.04em;color:var(--fg-3);font-weight:700;padding:.1rem .45rem;border:1px solid var(--line-soft);border-radius:var(--r-pill);background:rgba(5,8,15,.5)}
.catalog-group>.prose{color:var(--fg-3);font-size:var(--t-sm);margin:.6rem 0 0;max-width:70ch}
.shelf-games{--shelf:var(--good)}
.shelf-features{--shelf:var(--violet)}
.shelf-services{--shelf:var(--accent)}
.shelf-more{--shelf:var(--fg-3)}
.card-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(15.5rem,1fr));gap:.8rem;margin:var(--s4) 0 0}
.offering-card{position:relative;display:flex;flex-direction:column;gap:.35rem;padding:1.05rem 1.1rem 1rem;border:1px solid var(--line-soft);border-radius:var(--r-lg);background:linear-gradient(180deg,var(--ink-600),var(--ink-800));box-shadow:0 14px 34px -28px #000,inset 0 1px 0 rgba(255,255,255,.03);overflow:hidden;transition:border-color .18s,transform .18s var(--ease),box-shadow .18s}
.offering-card::before{content:"";position:absolute;inset:0 0 auto;height:2px;background:linear-gradient(90deg,transparent,var(--shelf,var(--accent)),transparent);opacity:0;transition:opacity .22s}
.offering-card:hover{border-color:var(--line-lit);transform:translateY(-2px);box-shadow:0 24px 46px -26px #000}
.offering-card:hover::before{opacity:.9}
.offering-card:focus-within{border-color:var(--shelf,var(--accent))}
.offering-card h3{margin:0;font-size:var(--t-h3);color:var(--fg);line-height:1.35}
.offering-card .tagline{margin:0;font-size:var(--t-sm);color:var(--fg-3);line-height:1.55}
.offering-card .meta{margin:.15rem 0 0;font-size:var(--t-micro);color:var(--fg-3);display:flex;flex-wrap:wrap;align-items:center;gap:.4rem;font-family:var(--mono)}
.offering-card .meta .dot{width:.3rem;height:.3rem;border-radius:50%;background:var(--line-lit)}
.offering-card .meta .live{background:var(--good);box-shadow:0 0 7px var(--good)}
.offering-card a.play{margin-top:auto;padding-top:.85rem;display:inline-flex;align-items:center;gap:.35rem;color:var(--shelf,var(--accent));font-weight:700;font-size:var(--t-sm);text-decoration:none}
.offering-card a.play::after{content:"";position:absolute;inset:0;border-radius:inherit}
.offering-card a.play .arr{transition:transform .18s var(--ease)}
.offering-card:hover a.play .arr{transform:translateX(3px)}
/* ═══ SECTIONS — a surface's panels. The tag dot is the instant read. ═════ */
.deos-section{border:1px solid var(--line-soft);border-radius:var(--r-lg);padding:1.05rem 1.15rem 1.1rem;margin:var(--s4) 0;background:linear-gradient(180deg,rgba(24,36,63,.6),rgba(13,20,37,.48));box-shadow:0 16px 40px -32px #000,inset 0 1px 0 rgba(255,255,255,.03)}
.deos-section h2{margin:0 0 .55rem;font-size:var(--t-h3);font-weight:700;color:var(--head);display:flex;align-items:center;gap:.5rem;line-height:1.35}
.deos-section h2::before{content:"";flex:0 0 auto;width:.42rem;height:.42rem;border-radius:50%;background:currentColor;box-shadow:0 0 9px currentColor}
.deos-section.tag-accent{border-color:rgba(92,201,255,.2)}
.deos-section.tag-accent h2{color:var(--accent)}
.deos-section.tag-good,.deos-section.tag-genuine{border-color:rgba(79,220,160,.22)}
.deos-section.tag-good h2,.deos-section.tag-genuine h2{color:var(--good)}
.deos-section.tag-warn{border-color:rgba(245,200,92,.22)}
.deos-section.tag-warn h2{color:var(--warn)}
.deos-section.tag-bad h2{color:var(--bad)}
.deos-section.tag-muted h2{color:var(--fg-3)}
/* ═══ AFFORDANCES ════════════════════════════════════════════════════════ */
.affordances{display:flex;flex-direction:column;gap:.45rem;margin:.6rem 0 .1rem}
.affordance{margin:0;display:flex;gap:.45rem;align-items:stretch}
.affordance button{flex:1 1 auto;text-align:left;padding:.62rem .9rem;border-radius:10px;border:1px solid rgba(79,220,160,.28);background:linear-gradient(180deg,rgba(35,72,56,.75),rgba(16,34,27,.7));color:#dbfced;font:inherit;font-size:var(--t-sm);font-weight:650;cursor:pointer;min-height:2.6rem;transition:border-color .14s,background .14s,transform .09s var(--ease),box-shadow .18s,color .14s}
.affordance button:hover{border-color:var(--good);background:linear-gradient(180deg,rgba(48,99,76,.9),rgba(20,45,35,.85));color:#fff;transform:translateY(-1px);box-shadow:0 8px 20px -11px var(--good)}
.affordance button:active{transform:translateY(0)}
/* Not-yet-available is NEUTRAL, not red: rose means REFUSED (the executor said no). A dimmed */
/* affordance has not been refused — it is simply not offered on this surface yet. */
.affordance.dimmed button{border-color:var(--line-soft);color:#5b6884;background:rgba(255,255,255,.02);cursor:not-allowed;box-shadow:none;transform:none;font-weight:600}
.affordance.dimmed button:hover{transform:none;box-shadow:none;border-color:var(--line-soft);background:rgba(255,255,255,.02);color:#5b6884}
.affordance input.arg{flex:0 0 5.5rem;width:5.5rem;padding:.45rem .6rem;border-radius:10px;border:1px solid var(--line);background:var(--ink-950);color:var(--fg);font-family:var(--mono);font-size:var(--t-sm);text-align:center;transition:border-color .14s,box-shadow .18s}
.affordance input.arg:focus{outline:none;border-color:var(--accent);box-shadow:0 0 0 3px rgba(92,201,255,.18)}
.affordance input.arg:disabled{opacity:.45;cursor:not-allowed}
/* A DECLARED TEXT WANT (`MenuItem::wants_text`) — the prose the affordance asks for. Wide and */
/* left-aligned, unlike the 5.5rem numeric box: it holds a sentence, not an index. */
.affordance input.text{flex:1 1 12rem;min-width:0;padding:.45rem .6rem;border-radius:10px;border:1px solid var(--line);background:var(--ink-950);color:var(--fg);font:inherit;font-size:var(--t-sm);transition:border-color .14s,box-shadow .18s}
.affordance input.text::placeholder{color:var(--fg-3);opacity:.75}
.affordance input.text:focus{outline:none;border-color:var(--accent);box-shadow:0 0 0 3px rgba(92,201,255,.18)}
.affordance input.text:disabled{opacity:.45;cursor:not-allowed}
.affordance.text button{flex:0 0 auto;text-align:center}
.operation-uploader{margin:var(--s4) 0;padding:1rem 1.1rem;border:1px solid rgba(168,126,255,.26);border-radius:var(--r-lg);background:linear-gradient(180deg,rgba(37,27,61,.6),rgba(16,13,28,.58))}
.operation-uploader>h2{margin:0 0 .35rem;color:#c9b5ff;font-size:var(--t-h3)}
.operation-uploader>.prose{color:var(--fg-3)}
.binary-operation{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:.55rem;align-items:center;padding:.75rem 0;border-top:1px solid var(--line-soft)}
.binary-operation:first-of-type{margin-top:.75rem}
.binary-operation label{grid-column:1/-1;color:var(--head);font-weight:700}
.binary-operation .operation-disclosure{grid-column:1/-1;margin:0;color:var(--fg-3);font-size:var(--t-xs);line-height:1.55}
.binary-operation input[type=file]{min-width:0;padding:.5rem;border:1px solid var(--line);border-radius:10px;background:var(--ink-950);color:var(--fg-2);font:inherit;font-size:var(--t-xs)}
.binary-operation button{padding:.58rem .8rem;border-radius:10px;border:1px solid rgba(168,126,255,.45);background:rgba(79,55,126,.55);color:#efe9ff;font:inherit;font-weight:700;cursor:pointer}
.binary-operation [role=status]{grid-column:1/-1;min-height:1.2em;color:var(--fg-3);font-size:var(--t-xs);overflow-wrap:anywhere}
.binary-operation.pending{opacity:.7;cursor:progress}
/* ═══ ONE GAME SESSION GRAMMAR ══════════════════════════════════════════ */
.game-session-rail{display:grid;grid-template-columns:minmax(11rem,.8fr) minmax(18rem,1.4fr);gap:.8rem 1.2rem;align-items:center;margin:0 0 var(--s4);padding:.8rem .95rem;border:1px solid var(--line-soft);border-radius:var(--r-lg);background:linear-gradient(110deg,rgba(12,19,34,.9),rgba(29,24,48,.58));box-shadow:inset 0 1px 0 rgba(255,255,255,.035)}
.game-session-resume{display:grid;grid-template-columns:auto 1fr;gap:.12rem .55rem;align-items:baseline;min-width:0}
.game-session-kicker{grid-column:1/-1;color:var(--fg-3);font-size:var(--t-micro);font-weight:800;letter-spacing:.13em;text-transform:uppercase}
.game-session-resume strong{min-width:0;overflow:hidden;text-overflow:ellipsis;font-family:var(--mono);font-size:var(--t-xs);color:var(--fg-2)}
.game-session-resume a{justify-self:end;color:var(--accent);font-size:var(--t-xs);font-weight:750;text-decoration:none}
.game-session-resume a:hover{text-decoration:underline}
.game-session-steps{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:.35rem;margin:0;padding:0;list-style:none}
.game-session-steps li{display:flex;gap:.38rem;align-items:center;min-width:0;color:var(--fg-3);font-size:var(--t-micro);text-transform:uppercase;letter-spacing:.05em}
.game-session-steps b{display:grid;place-items:center;flex:0 0 1.35rem;height:1.35rem;border:1px solid rgba(79,220,160,.3);border-radius:50%;color:var(--good);font-family:var(--mono);font-size:.62rem}
.game-session-boundary{grid-column:1/-1;display:flex;gap:.55rem;align-items:flex-start;margin:0;padding-top:.65rem;border-top:1px solid var(--line-soft);color:var(--fg-3);font-size:var(--t-xs);line-height:1.5}
.game-session-boundary span{color:var(--violet);font-size:1rem;line-height:1.1}
/* ═══ NOTICE — what just happened ════════════════════════════════════════ */
/* ⚑ `overflow-wrap:anywhere` IS LOAD-BEARING, not tidying. The success banner carries
   `PlayerTurnReceipt::compact_text`, whose middle is a 64-character executor receipt hex — ONE
   unbroken word, in proportional text, not in a `<code>` well. `body{overflow-x:hidden}` means an
   unbreakable line is CLIPPED, not scrolled, so on a phone the receipt id (and everything after it)
   was silently GONE. `anywhere` rather than `break-word` deliberately: only `anywhere` shrinks the
   min-content size, which is what a flex item — the banner's anonymous text item — is measured by. */
.notice{display:flex;align-items:flex-start;gap:.6rem;padding:.7rem .9rem;border-radius:var(--r-md);margin:0 0 var(--s4);font-size:var(--t-sm);font-weight:600;border:1px solid var(--line);overflow-wrap:anywhere;animation:notice-in .26s var(--ease) both}
.notice::before{flex:0 0 auto;width:1.15rem;height:1.15rem;border-radius:50%;display:grid;place-items:center;font-size:.7rem;font-weight:800;margin-top:.06rem}
.notice.ok{background:rgba(79,220,160,.09);color:#a9f5d1;border-color:rgba(79,220,160,.32)}
.notice.ok::before{content:"✓";background:rgba(79,220,160,.18);color:var(--good)}
.notice.refused{background:rgba(255,123,134,.09);color:#ffc0c5;border-color:rgba(255,123,134,.32)}
.notice.refused::before{content:"✕";background:rgba(255,123,134,.18);color:var(--bad)}
@keyframes notice-in{from{opacity:0;transform:translateY(-5px)}to{opacity:1;transform:none}}
/* The keep-this-run offer, shown ONCE (the screen after a first move). Deliberately quieter than a
   `.notice` — it is an offer, not a result — and it must not read as a warning the player has to
   clear before playing on. One line, one link, gone by the next press. */
.keep-run{margin:0 0 var(--s4);padding:.55rem .8rem;border-left:2px solid var(--warn);border-radius:0 var(--r-sm) var(--r-sm) 0;background:rgba(245,200,92,.055);font-size:var(--t-sm);color:var(--fg-2);line-height:1.55;max-width:64ch}
.keep-run a{font-weight:700;white-space:nowrap}
/* ═══ RECEIPT — the product's signature line ═════════════════════════════ */
.receipt{display:flex;flex-wrap:wrap;align-items:center;gap:.5rem;margin:var(--s4) 0 0;padding:.6rem .8rem;border:1px solid var(--line-soft);border-radius:var(--r-md);background:rgba(5,8,15,.55);font-family:var(--mono);font-size:var(--t-micro);color:var(--fg-3);line-height:1.5}
.receipt .dot{flex:0 0 auto;width:.42rem;height:.42rem;border-radius:50%;background:var(--fg-3)}
.receipt .label{text-transform:uppercase;letter-spacing:.1em;font-weight:700}
.receipt .verdict{font-weight:800;letter-spacing:.06em}
.receipt .detail{color:var(--fg-3);opacity:.85;flex:1 1 12rem;min-width:0;overflow-wrap:anywhere}
.receipt.ok{border-color:rgba(79,220,160,.26);background:rgba(79,220,160,.05)}
.receipt.ok .dot{background:var(--good);box-shadow:0 0 9px var(--good)}
.receipt.ok .verdict{color:var(--good)}
.receipt.refused{border-color:rgba(255,123,134,.3);background:rgba(255,123,134,.05)}
.receipt.refused .dot{background:var(--bad);box-shadow:0 0 9px var(--bad)}
.receipt.refused .verdict{color:var(--bad)}
/* The register gloss under the receipt strip: quiet prose, NOT the mono voice — it explains the
   mono line above it and would read as more verifiable material if it wore the same face. FOLDED:
   the summary is the QUESTION, so the answer costs a click and never sits under the move buttons of
   a player who has not asked it. `<details>` is native — no script, and it still prints/reads whole. */
.receipt-gloss{margin:.45rem 0 0;font-size:var(--t-micro);line-height:1.55;color:var(--fg-3);max-width:60ch}
.receipt-gloss>summary{cursor:pointer;list-style:none;display:inline-flex;align-items:baseline;gap:.35rem;color:var(--fg-3);font-weight:600}
.receipt-gloss>summary::-webkit-details-marker{display:none}
.receipt-gloss>summary::before{content:"›";color:var(--line-lit);transition:transform .16s var(--ease)}
.receipt-gloss[open]>summary::before{transform:rotate(90deg)}
.receipt-gloss>summary:hover{color:var(--fg-2)}
.receipt-gloss p{margin:.35rem 0 0}
.receipt-gloss strong{color:var(--fg-2);font-weight:700}
.backlink{display:inline-flex;align-items:center;gap:.4rem;margin:var(--s5) 0 0;font-size:var(--t-sm);color:var(--fg-2);text-decoration:none;font-weight:600}
.backlink:hover{color:var(--accent)}
/* ═══ THE BOARD — the hero surface ═══════════════════════════════════════ */
/* A LITERAL meter (a game's light clock, a carry ceiling, a guardian's vitality). The bar is the */
/* argument and the numbers are the proof, so the track is wide and the value sits beside it in the */
/* mono voice. Semantic, not decorative: the fill is the accent — it is the thing being spent. */
.progress{display:grid;grid-template-columns:auto 1fr auto;align-items:center;gap:.6rem;margin:.35rem 0;font-size:var(--t-sm)}
.progress-label{color:var(--fg-3);font-size:var(--t-micro);letter-spacing:.12em;text-transform:uppercase;white-space:pre}
.progress-track{position:relative;height:.62rem;border:1px solid var(--line-soft);border-radius:999px;background:rgba(255,255,255,.045);overflow:hidden}
.progress-fill{display:block;height:100%;border-radius:inherit;background:linear-gradient(90deg,rgba(92,201,255,.45),var(--accent));box-shadow:0 0 12px -4px var(--accent)}
.progress-value{color:var(--fg);font-family:var(--mono);font-size:var(--t-xs);font-variant-numeric:tabular-nums}
.coordgrid{display:grid;gap:.4rem;width:100%;max-width:32rem;margin:1.1rem auto;padding:.6rem;border:1px solid var(--line);border-radius:14px;background:radial-gradient(130% 120% at 50% 0%,#0d1731,#060a15);box-shadow:inset 0 1px 0 rgba(255,255,255,.045),inset 0 0 44px -14px #000,0 20px 46px -26px #000}
.coordgrid .cell{position:relative;display:flex;align-items:center;justify-content:center;aspect-ratio:1/1;min-width:1.5rem;border:1px solid var(--line-soft);border-radius:9px;background:rgba(255,255,255,.02);color:var(--fg);font-family:var(--mono);font-size:1.15rem;font-weight:700;line-height:1;margin:0;transition:border-color .14s,background .14s,color .14s,transform .09s var(--ease),box-shadow .18s}
/* The checker. An ODD width ⇒ nth-child alternation IS a checkerboard; an even one would be */
/* vertical stripes, so the RENDERER decides (it knows the real column count) and tags the grid */
/* `.checkered`. No board size is written here — a 5, an 11, or a 13 all land on the same rule. */
/* `:where()` zeroes the selector's specificity, so a tinted cell (tag-accent/warn) keeps its own */
/* field and only the plain squares checker. */
:where(.coordgrid.checkered) .cell:nth-child(2n){background-image:linear-gradient(rgba(255,255,255,.032),rgba(255,255,255,.032))}
.coordgrid form.cell{padding:0;cursor:pointer}
.coordgrid form.cell button{width:100%;height:100%;display:flex;align-items:center;justify-content:center;border:0;border-radius:inherit;background:transparent;color:inherit;font:inherit;font-size:inherit;font-weight:inherit;cursor:pointer;padding:0}
.coordgrid form.cell button:focus-visible{outline:2px solid var(--accent);outline-offset:1px;border-radius:inherit}
.coordgrid form.cell:hover{border-color:var(--accent);background:rgba(92,201,255,.14);color:#fff;transform:translateY(-1px);box-shadow:0 7px 18px -8px var(--accent)}
.coordgrid form.cell:active{transform:translateY(0) scale(.97)}
/* LIT — a live cell (target / selected / the automaton). Green by default: the legal-move ring. */
.coordgrid .cell.highlighted{color:#eaf5ff;border-color:var(--good);box-shadow:inset 0 0 0 1px var(--good),0 0 16px -5px var(--good)}
.coordgrid form.cell.highlighted:hover{border-color:var(--good);box-shadow:0 7px 18px -7px var(--good)}
/* A LEGAL TARGET — a bright mint move-hint (the surface paints a vacant target's glyph `·`). */
.coordgrid .cell.tag-good{color:var(--good);font-size:1.45rem}
/* A SELECTED piece — yours, amber. */
.coordgrid .cell.tag-warn{color:var(--warn);border-color:var(--warn);background:rgba(245,200,92,.07);box-shadow:inset 0 0 0 1px var(--warn),0 0 15px -6px var(--warn)}
/* THE AUTOMATON — the machine, a cyan well. */
.coordgrid .cell.tag-accent{color:#f2fbff;border-color:var(--accent);background:radial-gradient(circle at 50% 42%,rgba(92,201,255,.36),rgba(13,24,48,.9) 72%);box-shadow:inset 0 0 0 1px var(--accent),0 0 18px -4px var(--accent)}
/* VACANT — recedes. The dot is a whisper, not a wall of debris (an untagged cell is a PIECE and */
/* keeps the bright base colour — the fix for a board that read as `· · A ·`). */
/* ⚑ `#3f5074` computed 2.10–2.38:1 against every cell ground it lands on (WCAG relative luminance)
   at .72rem — a CONTRAST FAILURE on text that names board state, not decoration. `#7688b1` measures
   4.77:1 on the lightest ground (the generic cell over `#0d1731`) and 4.99–5.40:1 on the rest, so it
   clears AA everywhere. It is still DIMMER than `--fg-3` (#8a9cbe), the page's quietest ink, so the
   "vacant recedes" reading the comment above asks for survives — the recession is now carried by the
   size and by the untagged cell's much brighter `--fg`, not by unreadability. */
.coordgrid .cell.tag-muted{color:#7688b1;font-size:.72rem}
/* THE GOAL SQUARE — a teal dashed objective ring; distinct from a plain vacant (dim) cell and */
/* still legible when the goal is also a lit legal-move target (green). */
.coordgrid .cell.goal{border:1px dashed var(--head);color:var(--head);font-size:.92rem;background:radial-gradient(circle at 50% 50%,rgba(140,227,228,.13),rgba(13,24,48,.4) 70%);box-shadow:inset 0 0 0 1px rgba(140,227,228,.24)}
.coordgrid .cell.goal.highlighted,.coordgrid form.cell.goal:hover{border-style:dashed;border-color:var(--good);color:#eaf5ff;box-shadow:inset 0 0 0 1px var(--good),0 0 14px -4px var(--good)}
/* The board legend — what the colours mean, stated on the surface. */
.legend{display:flex;flex-wrap:wrap;justify-content:center;gap:.35rem .9rem;margin:-.3rem auto .2rem;max-width:24rem;font-size:var(--t-micro);color:var(--fg-3)}
.legend span{display:inline-flex;align-items:center;gap:.35rem;white-space:nowrap}
.legend i{width:.5rem;height:.5rem;border-radius:2px;font-style:normal;flex:0 0 auto}
.legend .k-auto{background:var(--accent);box-shadow:0 0 7px var(--accent)}
.legend .k-sel{background:var(--warn);box-shadow:0 0 7px var(--warn)}
.legend .k-tgt{background:var(--good);box-shadow:0 0 7px var(--good)}
.legend .k-goal{border:1px dashed var(--head);border-radius:50%}
/* ═══ AUTOMATAFL — THE NIGHT RECORD BOARD ════════════════════════════════ */
/* dregg's OWN language, scoped to the automatafl table (`.af-table`) so no other offering's look
   changes: night glass, a brass hairline, a thick brass left accent and a SHARP top-left corner on
   every plaque; VIOLET is the machine, BRASS is the objective. Nothing here knows a board size —
   the renderer hands CSS the real dimensions as `--af-n` / `--af-rows`, read from the DATA. */
.af-table{color:var(--n-ink)}
/* THE NIGHT GROUND. The shell's own floor is the catalog's deep navy; an automatafl surface
   washes it to night so the board is not a night object floating on a blue page. Fixed +
   behind the content, so it also lands when only the swapped FRAGMENT carries `.af-table`. */
main.af-table::before{content:"";position:fixed;inset:0;z-index:-1;pointer-events:none;background:radial-gradient(1100px 620px at 50% -12%,rgba(168,159,216,.09),transparent 62%),radial-gradient(700px 420px at 88% 6%,rgba(176,141,87,.06),transparent 60%),var(--n1)}
.af-table a{color:var(--vio-lit)}
.af-table a:hover{color:var(--br-lit)}
.af-table .deck{color:var(--n-soft)}
.af-table .page-head h1,.af-table .panel>h2{font-family:var(--n-serif);font-weight:600;letter-spacing:.012em;color:var(--br-pale)}
.af-table code{background:rgba(176,141,87,.1);border-color:rgba(176,141,87,.24);color:var(--br-pale)}
/* `.panel` had NO rule at all: the front door's sections were bare `<section>`s on the page floor
   — a wall of undifferentiated text. It is the same plaque as `.deos-section`. */
.af-table .panel{border:1px solid var(--br-faint);border-left:3px solid var(--br);border-radius:0 12px 12px 12px;background:linear-gradient(180deg,rgba(19,17,24,.9),rgba(11,10,16,.92));box-shadow:0 20px 50px -34px #000,inset 0 1px 0 rgba(237,220,180,.045);padding:1rem 1.15rem 1.15rem;margin:var(--s4) 0}
.af-table .panel>h2{margin:0 0 .55rem;font-size:var(--t-h2)}
.af-table .rules{list-style:none;padding-left:0;color:var(--n-soft)}
.af-table .rules li{position:relative;padding-left:1.05rem}
.af-table .rules li::before{content:"";position:absolute;left:0;top:.62em;width:.32rem;height:.32rem;background:var(--br);transform:rotate(45deg)}
.af-table .rules strong{color:var(--br-pale);font-weight:650}
.af-table .invite code{border:1px dashed var(--br-line);background:rgba(7,6,11,.6);color:var(--br-pale)}
.af-table .seat-link{color:var(--vio-lit)}
.af-table .backlink{color:var(--n-soft)}
.af-table .backlink:hover{color:var(--br-lit)}
.af-table>.prose{font-family:var(--n-serif);font-size:var(--t-lead);font-weight:600;color:var(--n-ink);margin:.9rem 0 .55rem;letter-spacing:.005em}
.af-table .prose{color:var(--n-soft)}
.af-table .deos-row{gap:.45rem;padding:.3rem 0;flex-wrap:wrap}
.af-table .deos-row>.prose{flex:1 1 100%}
/* THE PLAQUE — shaped night glass: brass hairline, thick brass left accent, sharp top-left. */
.af-table .deos-section{border:1px solid var(--br-faint);border-left:3px solid var(--br);border-radius:0 12px 12px 12px;background:linear-gradient(180deg,rgba(19,17,24,.9),rgba(11,10,16,.92));box-shadow:0 20px 50px -34px #000,inset 0 1px 0 rgba(237,220,180,.045);padding:.95rem 1.1rem 1rem}
.af-table .deos-section h2{font-family:var(--n-serif);font-weight:600;letter-spacing:.012em;color:var(--br-lit)}
.af-table .deos-section h2::before{border-radius:0;width:.34rem;height:.34rem;transform:rotate(45deg)}
.af-table .deos-section.tag-accent{border-color:var(--br-faint);border-left-color:var(--vio)}
.af-table .deos-section.tag-accent h2{color:var(--vio-lit)}
/* THE BOARD FRAME — a night well in a brass surround, with a coordinate ruler on two edges.
   ⚑ `minmax(0,1fr)`, NOT `1fr`, and it is the whole of why the small board used to burst. A `1fr`
   track carries an automatic MIN-CONTENT floor, and this track's content is an 11-wide grid whose
   cells had a `min-width` — so the moment the frame was narrower than 11 minimums the track REFUSED
   to shrink, pushed straight through the padding and the border, and the board sat flush against
   (and 4px past) the edge of its container. Measured on the front page at 1440px: frame 304px, its
   content box 261px wide, the grid demanding 276px. `minmax(0,1fr)` lets the track shrink and the
   `min-width:0` below lets the squares follow it down. */
.af-board{--af-gut:1.2rem;position:relative;display:grid;grid-template-columns:var(--af-gut) minmax(0,1fr);grid-template-rows:1fr var(--af-gut) auto;gap:.15rem;width:100%;max-width:33rem;margin:1rem auto .3rem;padding:.8rem .9rem .7rem;border:1px solid rgba(176,141,87,.3);border-radius:0 14px 14px 14px;background:radial-gradient(125% 105% at 50% -12%,#17131f,#08070c 72%);box-shadow:inset 0 1px 0 rgba(237,220,180,.05),0 26px 64px -34px #000}
.af-board .af-defs{position:absolute;width:0;height:0;overflow:hidden}
.af-ruler{display:grid;font-family:var(--mono);font-size:.55rem;font-weight:700;line-height:1;color:rgba(164,159,180,.5)}
.af-ranks{grid-column:1;grid-row:1;grid-template-rows:repeat(var(--af-rows),1fr);align-items:center;justify-items:end;padding-right:.32rem}
.af-files{grid-column:2;grid-row:2;grid-template-columns:repeat(var(--af-n),1fr);align-items:start;justify-items:center;padding-top:.28rem}
/* THE GRID — a 1px gap over a brass field IS the grid line, so the board rules itself. */
.af-board>.coordgrid{grid-column:2;grid-row:1;margin:0;padding:0;max-width:none;gap:1px;border:1px solid var(--br-line);border-radius:0;background:rgba(176,141,87,.32);box-shadow:inset 0 0 60px -18px #000}
/* ⚑ `min-width:0`, ALWAYS — not only on a phone. The generic `.coordgrid .cell` floor (1.5rem) is a
   tap-target minimum for a grid of unknown width; this board is a FIXED 11 squares across inside a
   frame that is often much narrower than 11 × 1.5rem, and a floor a container cannot honour does not
   make the squares bigger, it makes the board overflow the container. The squares keep
   `aspect-ratio:1/1`, so shrinking keeps a square board instead of bursting a rectangular frame.
   This lived in the `max-width:44rem` media query only, which is why the PHONE board was fine and the
   front page's 19rem hero board was not. */
.af-board .coordgrid .cell{min-width:0;border:0;border-radius:0;background:#141220;color:var(--n-soft);box-shadow:none;font-family:var(--mono);transition:background .13s,box-shadow .13s}
.af-board :where(.coordgrid.checkered) .cell:nth-child(2n){background-image:none;background:#191628}
.af-board .coordgrid form.cell{cursor:pointer}
.af-board .coordgrid form.cell button{position:relative;padding:0}
.af-board .coordgrid form.cell button:focus-visible{outline:2px solid var(--br-lit);outline-offset:-2px;border-radius:0}
/* THE PIECES — shape + spike direction + colour, three redundant reads at a glance. */
.af-board .af-p{position:relative;display:block;width:82%;height:82%;overflow:visible;pointer-events:none}
.af-board .p-att{color:var(--br-lit)}
.af-board .p-rep{color:#a7a1ba}
.af-board .p-auto{color:var(--vio-lit);filter:drop-shadow(0 0 5px rgba(168,159,216,.9))}
.af-board .af-dot{width:3px;height:3px;border-radius:50%;background:rgba(164,159,180,.2);transition:all .13s}
.af-board .af-mark{position:absolute;inset:11%;width:78%;height:78%;color:var(--br);opacity:.62;pointer-events:none}
.af-board .af-seat{position:absolute;top:1px;left:2px;font-family:var(--mono);font-size:.5rem;font-weight:800;line-height:1;color:var(--br-lit);opacity:.7;pointer-events:none}
/* THE ROLES — order matters: each later rule is the stronger claim on the square. */
.af-board .coordgrid .cell.highlighted{border:0;color:var(--n-ink);box-shadow:inset 0 0 0 1px rgba(168,159,216,.4)}
.af-board .coordgrid .cell.goal{border:0;background:linear-gradient(180deg,#2b2317,#1a1610);box-shadow:inset 0 0 0 1px rgba(176,141,87,.42)}
.af-board .coordgrid .cell.tag-good{background:#262240;box-shadow:inset 0 0 0 1px rgba(168,159,216,.45)}
.af-board .coordgrid .cell.tag-good .af-p{filter:drop-shadow(0 0 5px rgba(168,159,216,.75))}
.af-board .coordgrid .cell.tag-good.af-empty .af-dot{width:23%;height:23%;background:var(--vio);box-shadow:0 0 8px 1px rgba(168,159,216,.55)}
/* ⚑ PROPOSABLE BUT BLOCKED — a square on the picked-up piece's rook line that a piece in the way
   stops it reaching. It is NOT a legal-move square and must not read as one (the violet fill and the
   lit pip belong to `tag-good` alone), and it is NOT dead either: the rules let you seal a move
   there, and it runs if the other seat lifts the blocker. So it gets its own third state — no fill,
   a dashed violet outline at low opacity, and a hollow ring instead of the solid pip. Painted BEFORE
   `tag-warn` in this block so every stronger role still wins the square. */
.af-board .coordgrid .cell.tag-blocked{background:#141220;box-shadow:inset 0 0 0 1px rgba(168,159,216,.16)}
.af-board .coordgrid .cell.tag-blocked::after{content:"";position:absolute;inset:8%;border:1px dashed rgba(168,159,216,.34);pointer-events:none}
.af-board .coordgrid .cell.tag-blocked .af-p{opacity:.72}
.af-board .coordgrid .cell.tag-blocked.af-empty .af-dot{width:20%;height:20%;background:transparent;box-shadow:inset 0 0 0 1px rgba(168,159,216,.42)}
.af-board .coordgrid .cell.tag-warn{background:#33291c;box-shadow:inset 0 0 0 2px var(--br-lit);z-index:2}
.af-board .coordgrid .cell.tag-sealed{background:#3d3020;box-shadow:inset 0 0 0 1px var(--br-lit),0 0 18px -4px rgba(216,180,126,.85);z-index:3}
.af-board .coordgrid .cell.tag-sealed::after{content:"";position:absolute;inset:20%;border:2px solid var(--br-pale);border-radius:50%;opacity:.9;pointer-events:none}
.af-board .coordgrid .cell.tag-accent{background:radial-gradient(circle at 50% 45%,#443e66,#0d0b16 74%);box-shadow:inset 0 0 0 1px var(--vio),0 0 22px -3px rgba(168,159,216,.85);z-index:4}
/* ⚑ THE MARK — a square a CLASH burned. Deliberately the ONLY dead-looking thing on the board and
   the LAST role in this block, so it wins over the goal inlay, the sealed ring and the automaton's
   glow: nothing else on this board means "you cannot use this". No brass, no violet, no glow — a
   flat ash square under a diagonal hatch, with a hard grey cross on it. `z-index` above them all,
   `cursor:default` because there is genuinely nothing to click (the offering hands it no
   affordance, so it renders as a plain span anyway). */
.af-board .coordgrid .cell.tag-mark{background:repeating-linear-gradient(135deg,#191721 0 3px,#0d0c12 3px 6px);box-shadow:inset 0 0 0 1px rgba(120,116,132,.5);cursor:default;z-index:6}
.af-board .coordgrid .cell.tag-mark .af-x{color:#8b8798;width:74%;height:74%;filter:none;opacity:.95}
.af-board .coordgrid form.cell:hover{border:0;color:var(--n-ink);background:#39345a;transform:none;box-shadow:inset 0 0 0 2px var(--vio);z-index:5}
.af-board .coordgrid form.cell:active{transform:none}
/* THE KEY — the three shapes, named, under the board. A stranger never has to be told twice. */
/* `.7` measured 4.11–4.25:1 at .585rem — a MARGINAL AA FAIL on the one element a colour-blind or
   low-vision player reads to decode every other colour on the board. `.86` measures 5.55:1. */
.af-key{grid-column:1/-1;grid-row:3;display:flex;flex-wrap:wrap;gap:.28rem .8rem;margin-top:.5rem;padding-top:.5rem;border-top:1px solid var(--br-faint);font-family:var(--mono);font-size:.585rem;letter-spacing:.05em;text-transform:uppercase;color:rgba(164,159,180,.86)}
.af-key span{display:inline-flex;align-items:center;gap:.3rem;white-space:nowrap}
.af-board .af-key .af-p{width:1.05rem;height:1.05rem;flex:0 0 auto}
.af-key i{width:.55rem;height:.55rem;flex:0 0 auto;font-style:normal}
.af-key .k-goal{border:1px solid var(--br-lit);background:rgba(176,141,87,.28)}
.af-key .k-tgt{border-radius:50%;background:var(--vio);box-shadow:0 0 7px var(--vio)}
.af-key .k-blocked{border-radius:50%;background:transparent;box-shadow:inset 0 0 0 1px rgba(168,159,216,.45)}
.af-key .k-sel{box-shadow:inset 0 0 0 2px var(--br-lit)}
.af-key .k-seal{border-radius:50%;border:2px solid var(--br-pale);background:rgba(216,180,126,.2)}
.af-key .k-mark{background:repeating-linear-gradient(135deg,#191721 0 2px,#0d0c12 2px 4px);box-shadow:inset 0 0 0 1px rgba(120,116,132,.55);position:relative}
.af-key .k-mark::after{content:"×";position:absolute;inset:0;display:flex;align-items:center;justify-content:center;font-size:.62rem;font-weight:800;line-height:1;color:#8b8798}
/* ⚑ THE MOVE LIST — automatafl's SECOND input path (see `af_move_list`).
   A phone cell is 21.6px and that is the right tradeoff for keeping an 11-wide board visible; this is
   the way to act that does not depend on hitting one. Every row is a 48px-tall full-width control in
   the surface's existing `.affordance` language — no fourth control vocabulary — and it is a
   `<details>`, collapsed, so on a desktop where the squares are hittable it costs one line.
   `list-style:none` because the button IS the item; the count in the summary is the affordance's own. */
.af-moves{max-width:33rem;margin:.2rem auto .9rem;border:1px solid var(--br-faint);border-radius:0 10px 10px 10px;background:rgba(7,6,11,.5)}
/* `display` is deliberately LEFT ALONE — a `<summary>` is a `list-item`, and giving it `flex` (or
   anything else) deletes its disclosure triangle, which is the only thing that says "this opens". */
.af-moves>summary{padding:.7rem .85rem .75rem;min-height:2.75rem;font-family:var(--mono);font-size:var(--t-micro);letter-spacing:.07em;text-transform:uppercase;color:var(--br-lit);cursor:pointer;border-radius:inherit}
.af-moves>summary:hover{background:rgba(176,141,87,.07)}
.af-moves>summary::marker{color:var(--br)}
.af-moves-why{display:block;margin-top:.2rem;font-family:var(--font);font-size:var(--t-sm);font-weight:400;letter-spacing:0;text-transform:none;color:var(--n-soft);line-height:1.45}
/* Bounded height so 36 selects cannot become a page of scrolling; `overscroll-behavior` keeps a thumb
   from scroll-chaining the whole page the instant the list bottoms out. */
.af-moves>ul{list-style:none;margin:0;padding:.2rem .55rem .6rem;display:flex;flex-direction:column;gap:.3rem;max-height:26rem;overflow-y:auto;overscroll-behavior:contain}
.af-moves>ul>li{margin:0;min-width:0}
/* 3rem = 48px, the target `descent_play`'s verb list already gives a motor-impaired player. The
   `.af-table` prefix is deliberate: it outranks `.af-table .affordance button` (same specificity,
   later in the file) so these rows do not depend on source order to keep their floor or their face. */
.af-table .af-moves .affordance button{min-height:3rem;width:100%;text-align:left;white-space:normal;font-family:var(--font);font-weight:600;letter-spacing:0;line-height:1.35}
.af-table .af-moves .affordance button b{font-family:var(--mono);font-weight:700;text-transform:uppercase;letter-spacing:.06em;color:var(--br-pale)}
/* ═══ THE SHARED BASELINE — the Night Record for EVERY offering ═══════════ */
/* Everything above this line dressed ONE table. The rules below are game-agnostic: they read a
   node's own shape (a plaque's first paragraph, a grid's column count, a glyph's length) and never
   a game's name, so a surface that has never been looked at still lands in the brand's language. */
/* THE DIRECTIVE. A plaque tagged `accent` is a STATUS plaque, and by the convention automatafl set
   its FIRST paragraph is the one sentence saying what to do right now. Promoted so the eye lands
   there before the pills: serif, lead-sized, on a violet rule. */
.af-table .deos-section.tag-accent>.prose:first-of-type{font-family:var(--n-serif);font-size:var(--t-lead);line-height:1.5;color:var(--n-ink);margin:.5rem 0 .7rem;padding-left:.75rem;border-left:2px solid var(--vio)}
/* THE WELL — the night surround for every NON-automatafl `CoordGrid` (the descent shaft, the tug
   hand, the next game's board). Dimension-free: `--nr-n` is the real column count, from the data. */
.nr-well{position:relative;width:100%;max-width:33rem;margin:.9rem auto .45rem;padding:.7rem .78rem;border:1px solid rgba(176,141,87,.3);border-radius:0 14px 14px 14px;background:radial-gradient(125% 105% at 50% -12%,#17131f,#08070c 72%);box-shadow:inset 0 1px 0 rgba(237,220,180,.05),0 26px 64px -34px #000}
.af-table .nr-well>.coordgrid{margin:0;padding:0;max-width:none;gap:1px;border:1px solid var(--br-line);border-radius:0;background:rgba(176,141,87,.32);box-shadow:inset 0 0 60px -18px #000}
.af-table .nr-well .cell{border:0;border-radius:0;background:#141220;color:var(--n-ink);box-shadow:none;font-family:var(--mono);transition:background .13s,box-shadow .13s}
.af-table .nr-well :where(.coordgrid.checkered) .cell:nth-child(2n){background-image:none;background:#191628}
.af-table .nr-well .cell.highlighted{color:var(--n-ink);box-shadow:inset 0 0 0 1px rgba(168,159,216,.45)}
.af-table .nr-well .cell.tag-good{color:var(--vio-lit);background:#262240;box-shadow:inset 0 0 0 1px rgba(168,159,216,.45)}
.af-table .nr-well .cell.tag-accent{color:var(--br-pale);background:radial-gradient(circle at 50% 45%,#3b3020,#0d0b16 76%);box-shadow:inset 0 0 0 1px var(--br-lit),0 0 18px -6px rgba(216,180,126,.7)}
.af-table .nr-well .cell.tag-warn{color:var(--br-pale);background:#33291c;box-shadow:inset 0 0 0 1px var(--br-lit)}
/* Same class of fault as the base `.cell.tag-muted` above and found in the same sweep: `.55` on
   `#100e18` measures 3.04:1. It matters where a muted cell carries a real LABEL glyph (`#17`, `L3`)
   rather than the vacant dot, which is drawn by `.nr-void::after` and not by this colour. `.78`
   measures 4.93:1. */
.af-table .nr-well .cell.tag-muted{color:rgba(164,159,180,.78);background:#100e18}
.af-table .nr-well .cell.goal{border:0;background:linear-gradient(180deg,#2b2317,#1a1610);box-shadow:inset 0 0 0 1px rgba(176,141,87,.42)}
.af-table .nr-well form.cell:hover{color:#fff8ea;background:#39345a;transform:none;box-shadow:inset 0 0 0 2px var(--vio);z-index:2}
.af-table .nr-well form.cell:active{transform:none}
/* GLYPH SHAPE, chosen from the glyph's own length — a SYMBOL reads large and centred, a LABEL
   (`#17`, `L3`, `v2`) reads as a small mono chip instead of overflowing its square, and a VACANT
   square recedes to a hairline dot rather than printing a full-strength `·`. */
.af-table .nr-well .cell.nr-sym{font-size:1.25rem;font-weight:700}
.af-table .nr-well .cell.nr-sym2{font-size:.95rem;letter-spacing:-.02em}
.af-table .nr-well .cell.nr-label{font-size:.62rem;font-weight:700;letter-spacing:.02em;padding:.1rem;text-align:center;line-height:1.15;overflow-wrap:anywhere}
.af-table .nr-well .cell.nr-label button{padding:.1rem;line-height:1.15;white-space:normal}
.af-table .nr-well .cell.nr-void{color:transparent;position:relative}
.af-table .nr-well .cell.nr-void::after{content:"";position:absolute;width:3px;height:3px;border-radius:50%;background:rgba(164,159,180,.22)}
.af-table .nr-well .cell.nr-void.highlighted::after{width:22%;height:22%;background:var(--vio);box-shadow:0 0 8px 1px rgba(168,159,216,.55)}
/* TABLES / LISTS in the record voice — a lane table is the scoreboard, not a debug dump. */
.af-table .deos-table{border:1px solid var(--br-faint);border-radius:0 10px 10px 10px;background:rgba(7,6,11,.5)}
/* ⚑ A row inside a TABLE or a LIST is a record, and its cells belong SIDE BY SIDE. The plaque rule
   above (`.deos-row>.prose{flex:1 1 100%}`) exists so a long sentence beside a pill wraps to its own
   line in a status plaque — but applied to a scoreboard it broke every lane into four stacked lines
   (caught by screenshotting the real markup: the tug's seven lanes rendered as a 28-line wall).
   Inside a table or list the cells share the row again, and the pills stay their natural width. */
.af-table :is(.deos-table,.deos-list)>.deos-row>.prose{flex:1 1 auto;min-width:8rem}
.af-table :is(.deos-table,.deos-list)>.deos-row{padding:.42rem .75rem;gap:.55rem}
.af-table :is(.deos-table,.deos-list)>.deos-row>.pill{flex:0 0 auto}
/* A TABLE row is a record — its columns hold their line. A LIST row is a group of chips and may
   wrap (the tug's per-seat row is a seat pill, four action pills and a standing sentence). */
.af-table .deos-list>.deos-row{flex-wrap:wrap}
.af-table .deos-table>.deos-row{flex-wrap:nowrap;border-bottom:1px solid var(--br-faint)}
.af-table .deos-table>.deos-row:hover{background:rgba(176,141,87,.06)}
.af-table .deos-row.header,.af-table .deos-row.header:hover{background:rgba(7,6,11,.72);color:rgba(237,220,180,.55);font-family:var(--mono)}
.af-table .deos-list{border:1px solid var(--br-faint);border-radius:0 10px 10px 10px;background:rgba(7,6,11,.5)}
.af-table .icon{font-family:var(--mono)}
.af-table .icon.tag-good{color:var(--vio-lit)}
.af-table .icon.tag-accent{color:var(--br-lit)}
.af-table .icon.tag-muted{color:rgba(164,159,180,.35)}
/* METERS — a `Progress` is a brass gauge in a night channel, not a blue browser bar. Every
   surface that emits one (the descent light clock, a standing bar, a quorum) gets this for free. */
.af-table .progress-label{color:rgba(237,220,180,.5);font-family:var(--mono)}
.af-table .progress-track{border:1px solid var(--br-faint);border-radius:0;background:rgba(7,6,11,.72);box-shadow:inset 0 1px 3px rgba(0,0,0,.6)}
.af-table .progress-fill{border-radius:0;background:linear-gradient(90deg,rgba(176,141,87,.55),var(--br-lit));box-shadow:0 0 12px -4px var(--br-lit)}
.af-table .progress-value{color:var(--n-ink)}
.af-table .gauge{font-family:var(--mono);font-size:var(--t-micro);letter-spacing:.06em;color:rgba(237,220,180,.6)}
/* PILLS + CONTROLS in the record voice — mono, uppercase, shaped. */
.af-table .pill{font-family:var(--mono);font-size:var(--t-micro);letter-spacing:.07em;text-transform:uppercase;border-radius:0 7px 7px 7px;border:1px solid var(--br-faint);background:rgba(11,10,16,.55);color:var(--n-soft)}
.af-table .pill.tag-good{color:var(--vio-lit);border-color:rgba(168,159,216,.5);background:rgba(168,159,216,.14)}
.af-table .pill.tag-accent{color:var(--br-lit);border-color:var(--br-line);background:rgba(176,141,87,.14)}
.af-table .pill.tag-warn{color:var(--br-pale);border-color:rgba(237,220,180,.3);background:rgba(237,220,180,.07)}
/* ⚑ THIS PILL IS LIVE TEXT A PLAYER MUST READ — "seat B (you) · waiting", "nobody has pulled" — and
   `.4` over a transparent background measured 2.15–2.16:1 on all three grounds it sits on (the list,
   the plaque, the night ground). `.82` measures 4.78–5.43:1. `muted` still reads as the quietest pill
   on the surface: at full strength `--n-soft` would be 7.59:1. */
.af-table .pill.tag-muted{color:rgba(164,159,180,.82);border-color:rgba(164,159,180,.13);background:transparent}
.af-table .pill.tag-bad{color:#f3b7b0;border-color:rgba(243,183,176,.42);background:rgba(243,183,176,.1)}
.af-table .affordance button{border-radius:0 9px 9px 9px;border:1px solid var(--br-line);background:linear-gradient(180deg,rgba(176,141,87,.24),rgba(176,141,87,.09));color:var(--br-pale);font-family:var(--mono);font-size:var(--t-sm);letter-spacing:.03em}
.af-table .affordance button:hover{border-color:var(--br-lit);background:linear-gradient(180deg,rgba(216,180,126,.32),rgba(176,141,87,.16));color:#fff8ea;box-shadow:0 8px 22px -14px var(--br-lit)}
.af-table .affordance.dimmed button,.af-table .affordance.dimmed button:hover{border-color:rgba(164,159,180,.16);background:rgba(11,10,16,.5);color:rgba(164,159,180,.42);box-shadow:none}
/* The landing hero paints the SAME board, smaller and inert (the page carries its own legend). */
.hero-af .af-board{max-width:19rem;margin:0;padding:.55rem .6rem .5rem}
.hero-af .af-key{display:none}
.hero-af .cell{cursor:default}
.hero-art .legend .k-auto{background:var(--vio);box-shadow:0 0 7px var(--vio)}
.hero-art .legend .k-sel{background:transparent;border-radius:0;box-shadow:inset 0 0 0 2px var(--br-lit)}
.hero-art .legend .k-tgt{background:var(--vio);border-radius:50%;box-shadow:0 0 7px var(--vio)}
/* The still's third square state, so the front page's legend names everything the board draws:
   a hollow ring for a square on the rook line that a piece in the way stops you reaching. */
.hero-art .legend .k-blocked{background:transparent;border-radius:50%;box-shadow:inset 0 0 0 1px rgba(168,159,216,.5)}
.hero-art .legend .k-goal{border:1px solid var(--br-lit);border-radius:0;background:rgba(176,141,87,.28)}
/* THE GAMETABLE — spwashi's overhead table (the games hero), scrimmed so the plaques stay legible. */
.af-hero{position:relative;overflow:hidden;border:1px solid var(--br-faint);border-left:3px solid var(--br);border-radius:0 16px 16px 16px;margin:var(--s5) 0 var(--s4);padding:clamp(1.6rem,5vw,3rem) clamp(1.1rem,4vw,2.2rem);background:linear-gradient(105deg,rgba(7,6,11,.94) 0%,rgba(7,6,11,.86) 42%,rgba(7,6,11,.34) 78%,rgba(7,6,11,.5) 100%),url("/automatafl/art/gametable.jpg") center/cover no-repeat;background-color:var(--n1)}
/* THE EXCHANGE — spwashi's `exchange` (two pairs of hands on a strung brass balance, a violet knot
   pulled taut between them) is the tug's own painting: the game IS two houses pulling at shared
   lanes. Same shaped plaque, same left-heavy scrim, its own hero class so neither door borrows the
   other's art. The hands sit right-of-centre, so the scrim is held darker on the left. */
.af-hero.hero-tug{background:linear-gradient(105deg,rgba(7,6,11,.95) 0%,rgba(7,6,11,.88) 40%,rgba(7,6,11,.36) 76%,rgba(7,6,11,.52) 100%),url("/tug/art/exchange.jpg") center/cover no-repeat;background-color:var(--n1)}
.af-hero>*{position:relative;max-width:34ch}
.af-hero h1{font-family:var(--n-serif);font-size:var(--t-display);font-weight:600;letter-spacing:-.01em;margin:0 0 .6rem;color:var(--br-pale)}
.af-hero .deck{color:var(--n-ink)}
.af-hero .eyebrow{color:var(--br-lit)}
.af-hero .credit{position:absolute;right:.7rem;bottom:.5rem;max-width:none;margin:0;font-family:var(--mono);font-size:.55rem;letter-spacing:.1em;text-transform:uppercase;color:rgba(237,220,180,.42)}
/* ═══ TABLES / ROWS / LISTS / PILLS ══════════════════════════════════════ */
.table-wrap{overflow-x:auto;margin:var(--s4) 0;border:1px solid var(--line-soft);border-radius:var(--r-lg);background:rgba(5,8,15,.4)}
table.board{width:100%;border-collapse:collapse;font-size:var(--t-sm);font-variant-numeric:tabular-nums}
table.board th,table.board td{text-align:left;padding:.6rem .8rem;border-bottom:1px solid var(--line-soft);white-space:nowrap}
table.board thead th{background:rgba(5,8,15,.6);color:var(--fg-3);font-size:var(--t-micro);text-transform:uppercase;letter-spacing:.12em;font-weight:800}
table.board tbody tr:last-child td{border-bottom:0}
table.board tbody tr{transition:background .14s}
table.board tbody tr:hover td{background:rgba(92,201,255,.045)}
table.board td{color:var(--fg-2)}
table.board td.rank{font-family:var(--mono);font-weight:800;color:var(--fg-3);width:1%}
table.board tbody tr:nth-child(1) td.rank{color:var(--warn)}
table.board tbody tr:nth-child(2) td.rank{color:#cfdcf2}
table.board tbody tr:nth-child(3) td.rank{color:#d9a273}
table.board td.player{color:var(--fg);font-weight:650}
table.board td.num{font-family:var(--mono);color:var(--fg-2)}
table.board td a{display:inline-flex;align-items:center;gap:.3rem;color:var(--good);text-decoration:none;font-weight:700}
table.board td a:hover{text-decoration:underline}
table.board td a .arr{transition:transform .18s var(--ease)}
table.board tr:hover td a .arr{transform:translateX(3px)}
.deos-table{border:1px solid var(--line-soft);border-radius:var(--r-md);overflow:hidden;margin:.7rem 0;background:rgba(5,8,15,.4)}
.deos-row{display:flex;gap:.6rem;align-items:center;padding:.48rem .75rem;font-size:var(--t-sm)}
.deos-row>*{flex:1 1 0;min-width:0;margin:0}
.deos-row>.pill,.deos-row>.icon{flex:0 0 auto}
.deos-table>.deos-row{border-bottom:1px solid var(--line-soft)}
.deos-table>.deos-row:last-child{border-bottom:0}
.deos-table>.deos-row:hover{background:rgba(92,201,255,.045)}
.deos-row.header{background:rgba(5,8,15,.6);text-transform:uppercase;letter-spacing:.12em;font-size:var(--t-micro);color:var(--fg-3);font-weight:800}
.deos-row.header:hover{background:rgba(5,8,15,.6)}
.deos-list{display:flex;flex-direction:column;gap:.3rem;margin:.6rem 0;padding:.55rem .75rem;border:1px solid var(--line-soft);border-radius:var(--r-md);background:rgba(5,8,15,.4);font-size:var(--t-sm)}
.deos-list .prose,.deos-row .prose{margin:0;color:var(--fg-2)}
.pill{display:inline-flex;align-items:center;padding:.16rem .55rem;margin:.12rem .3rem .12rem 0;border-radius:var(--r-pill);border:1px solid var(--line);background:rgba(5,8,15,.6);font-size:var(--t-micro);font-weight:700;color:var(--fg-3);letter-spacing:.02em;white-space:nowrap}
.pill.tag-accent{color:var(--accent);border-color:rgba(92,201,255,.34);background:rgba(92,201,255,.09)}
.pill.tag-good,.pill.tag-genuine{color:var(--good);border-color:rgba(79,220,160,.34);background:rgba(79,220,160,.09)}
.pill.tag-warn{color:var(--warn);border-color:rgba(245,200,92,.34);background:rgba(245,200,92,.09)}
.pill.tag-bad{color:var(--bad);border-color:rgba(255,123,134,.34);background:rgba(255,123,134,.09)}
.icon{font-size:1.05rem;font-family:var(--mono)}
.icon.tag-accent{color:var(--accent)}.icon.tag-good{color:var(--good)}.icon.tag-warn{color:var(--warn)}.icon.tag-bad{color:var(--bad)}
hr{border:0;border-top:1px solid var(--line-soft);margin:var(--s4) 0}
/* ═══ KEY/VALUE — a run's facts, not a debug dump ════════════════════════ */
.kv{display:grid;grid-template-columns:repeat(auto-fit,minmax(8rem,1fr));gap:.85rem 1.1rem;margin:.75rem 0 0}
.kv>div{min-width:0}
.kv dt,.kv .k{font-size:var(--t-micro);text-transform:uppercase;letter-spacing:.12em;font-weight:800;color:var(--fg-3);margin:0 0 .2rem}
.kv dd,.kv .v{margin:0;font-size:var(--t-sm);color:var(--fg);font-weight:650;overflow-wrap:anywhere}
.kv .v.mono{font-family:var(--mono);font-weight:600}
/* ═══ VERDICT — the certificate. The whole point of a run-card. ══════════ */
.verdict{position:relative;border-radius:var(--r-lg);padding:1.15rem 1.2rem;margin:var(--s4) 0;overflow:hidden}
.verdict h2{display:flex;align-items:center;gap:.6rem;margin:0 0 .5rem;font-size:var(--t-h3);letter-spacing:-.005em}
.verdict .stamp{flex:0 0 auto;display:inline-grid;place-items:center;min-width:3.1rem;padding:.2rem .5rem;border-radius:var(--r-sm);font-family:var(--mono);font-size:var(--t-micro);font-weight:800;letter-spacing:.14em}
.verdict p{margin:0 0 .55rem;font-size:var(--t-sm);line-height:1.62}
.verdict p:last-child{margin-bottom:0}
.verdict.pass{border:1px solid rgba(79,220,160,.38);background:linear-gradient(180deg,rgba(79,220,160,.11),rgba(13,20,37,.55))}
.verdict.pass h2{color:var(--good)}
.verdict.pass .stamp{background:var(--good);color:#02251a}
.verdict.pass p{color:#c6f3de}
.verdict.fail{border:1px solid rgba(255,123,134,.4);background:linear-gradient(180deg,rgba(255,123,134,.11),rgba(13,20,37,.55))}
.verdict.fail h2{color:var(--bad)}
.verdict.fail .stamp{background:var(--bad);color:#2b0409}
.verdict.fail p{color:#ffd3d6}
/* ═══ SPRITES ════════════════════════════════════════════════════════════ */
.sprite-tile{display:inline-flex;align-items:center;justify-content:center;border:1px solid var(--line-soft);border-radius:var(--r-md);background:rgba(5,8,15,.6);padding:.35rem;overflow:hidden;box-shadow:inset 0 0 0 1px rgba(0,0,0,.35)}
.sprite-tile svg{width:100%;height:100%;display:block}
.sprite-tile.placeholder{color:var(--fg-3);font-size:var(--t-micro);font-family:var(--mono);padding:.6rem;min-width:4rem;min-height:4rem}
.sprite-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(9rem,1fr));gap:.8rem;margin:var(--s5) 0 0}
.sprite-cell{margin:0;padding:.7rem;border:1px solid var(--line-soft);border-radius:var(--r-lg);background:linear-gradient(180deg,var(--ink-600),var(--ink-800));text-align:center;box-shadow:0 14px 34px -28px #000;transition:border-color .18s,transform .18s var(--ease)}
.sprite-cell:hover{border-color:var(--line-lit);transform:translateY(-2px)}
.sprite-art{width:100%;aspect-ratio:1/1;display:flex;align-items:center;justify-content:center}
.sprite-art svg{width:100%;height:100%;display:block}
.sprite-cell figcaption{margin-top:.55rem;font-size:var(--t-micro);color:var(--fg-3);line-height:1.6}
.sprite-cell figcaption code{font-size:.68rem;white-space:normal;overflow-wrap:anywhere}
/* ═══ RESPONSIVE — it must look right on a PHONE ═════════════════════════ */
@media (max-width:44rem){
.hero{grid-template-columns:1fr;padding-top:var(--s5);gap:var(--s5)}
.hero-art{order:-1}
.hero-af .af-board{max-width:15rem}
.steps{grid-template-columns:1fr}
.card-grid{grid-template-columns:1fr}
.topbar-in{padding:.5rem .9rem}
.brand-name{display:none}
.session,.catalog{padding-left:.9rem;padding-right:.9rem}
.crumb{padding-left:.9rem;padding-right:.9rem}
.hero,.steps{padding-left:.9rem;padding-right:.9rem}
.foot{padding-left:.9rem;padding-right:.9rem;flex-direction:column;align-items:flex-start;gap:.75rem}
/* The board on a phone. The STOCK automatafl board is 11 squares wide, so a ≥44px touch target */
/* per cell (484px) cannot fit a 360px viewport: the cell floor is sized to keep the WHOLE board */
/* visible without horizontal scroll, and the per-square POST form stays the full cell. */
.coordgrid{gap:.3rem;padding:.45rem;max-width:100%}
.nr-well{padding:.5rem .55rem;max-width:100%}
.af-table .nr-well>.coordgrid{gap:1px;padding:0}
.af-table .nr-well .cell{min-width:0}
.af-board{--af-gut:.9rem;padding:.55rem .6rem .5rem;max-width:100%}
.af-board>.coordgrid{gap:1px;padding:0}
/* (`.af-board .coordgrid .cell{min-width:0}` used to live here and ONLY here — it is now on the base
   rule, because the frame can be narrower than 11 tap targets on a desktop too.) */
.af-ruler{font-size:.45rem}
.af-key{font-size:.53rem;gap:.22rem .6rem}
.coordgrid .cell{min-width:1.35rem;border-radius:8px}
.affordance{flex-direction:column}
.affordance input.arg{flex:1 1 auto;width:100%;text-align:left}
.affordance input.text{flex:1 1 auto;width:100%}
.affordance.text button{flex:1 1 auto;text-align:left}
.affordance button{min-height:2.85rem}
.binary-operation{grid-template-columns:1fr}
.binary-operation label,.binary-operation .operation-disclosure,.binary-operation [role=status]{grid-column:1}
.binary-operation button{min-height:2.85rem}
.game-session-rail{grid-template-columns:1fr}
.game-session-steps{grid-template-columns:1fr}
.game-session-boundary{grid-column:1}
.kv{grid-template-columns:repeat(auto-fit,minmax(7rem,1fr))}
}
@media (max-width:26rem){.topnav a{padding:.35rem .45rem}}
/* ═══ LIVE REGION — the fragment the progressive-enhancement script swaps ═ */
/* The surface region a POST-act swaps in place (JS on); with JS off it is a plain container the */
/* full server-rendered page fills — ONE render path, so no-JS and JS look identical. `:focus` is */
/* moved here after a swap for keyboard continuity; the outline is suppressed (it is a programmatic */
/* focus target, not a user-tabbed one). */
.live-surface{outline:none}
.live-surface:focus{outline:none}
/* A just-swapped fragment fades+lifts in briefly, so a move reads as a real change, not a fl. */
.live-surface.swap-in{animation:surface-swap .2s var(--ease) both}
@keyframes surface-swap{from{opacity:.35;transform:translateY(4px)}to{opacity:1;transform:none}}
/* An in-flight affordance (its fetch outstanding): the pressed control dims and shows a wait */
/* cursor, so a tap gives instant feedback before the fragment lands. */
.affordance.pending button,.coordgrid form.cell.pending button{opacity:.6;cursor:progress}
.affordance.pending,.coordgrid form.cell.pending{cursor:progress}
form.in-flight button[disabled]{cursor:progress}
/* ═══ THE AUTOMATAFL FRONT DOOR — rules, seat links, spectator lock ══════ */
/* The rules list on `/automatafl`: one claim per line, the lead word carrying the weight. */
.rules{margin:.6rem 0 0;padding:0 0 0 1.1rem;color:var(--fg-2);max-width:74ch}
.rules li{margin:.5rem 0;line-height:1.55}
.rules strong{color:var(--fg)}
/* A seat link is a SECRET — it is set in the mono voice and made selectable as one unit, so it */
/* reads as key material to be copied whole rather than prose to be skimmed. */
.invite{margin:.5rem 0 0}
.invite code{display:block;overflow-x:auto;white-space:nowrap;padding:.55rem .7rem;border:1px dashed var(--line);border-radius:10px;background:rgba(255,255,255,.02);color:var(--head);font-family:var(--mono);font-size:var(--t-sm);user-select:all}
/* ⚑ This had NO padding and NO min-height, so its tap target was the text LINE-BOX — about 26px on a
   link whose whole job is "sit down at this table". `min-height` + a little vertical padding make the
   target 44px without moving the text (the `margin` is trimmed by the padding it gains). */
.seat-link{display:inline-flex;align-items:center;min-height:2.75rem;gap:.4rem;margin:.35rem 0 0;padding:.35rem .2rem;font-weight:700;color:var(--accent);text-decoration:none}
.seat-link:hover{text-decoration:underline}
/* SPECTATING. The read-only rendering is a native `disabled` fieldset (no markup rewriting), so */
/* the lock cannot drift from the surface it wraps; this only makes the state legible. */
.spectate-lock{border:0;margin:0;padding:0;min-inline-size:0}
.live-surface.spectating .coordgrid{opacity:.94}
.live-surface.spectating form.cell,.live-surface.spectating .affordance button{cursor:not-allowed}
.live-surface.spectating form.cell:hover{border-color:var(--line-soft);background:rgba(255,255,255,.02);color:var(--fg);transform:none;box-shadow:none}
/* ═══ MOTION — only where it clarifies, and never against the user ═══════ */
@media (prefers-reduced-motion:reduce){
*,*::before,*::after{animation-duration:.001ms!important;animation-iteration-count:1!important;transition-duration:.001ms!important;scroll-behavior:auto!important}
}
</style>"##;

// ─────────────────────────────────────────────────────────────────────────────
// THE PAGE SHELL — one chrome across every served surface.
//
// Before this, each page was a bare `<main>` with its own ad-hoc heading: the landing, the catalog,
// a game board, and the leaderboard had no shared frame, so they read as four unrelated debug
// dumps. `document` gives all of them the SAME topbar (brand + nav, with the current surface marked
// `aria-current="page"`) and the SAME footer — the cheapest, largest coherence win available.
// Purely presentational: no route, no game logic, no POST contract is touched.
// ─────────────────────────────────────────────────────────────────────────────

/// **The playable front door** — the served, in-tab, beacon-seeded Descent run
/// ([`descent_play`]). Named once, so every "Play" CTA on the product points at the SAME place and
/// none of them can silently drift back to the board.
pub const DESCENT_PLAY_PATH: &str = "/descent/play";

/// ⚑ **THE PRODUCT NAME, in ONE place** — the brand text in the top bar and the `<title>` of every
/// served page. A re-export of [`dreggnet_catalog::SURFACE_NAME`], which is where the name is
/// DECIDED: the web, Telegram, WeChat and the discord-bot's admin portal all read that one
/// constant, so the arcade cannot be called two things on two hosts.
///
/// It is **Dragon's Arcade** (ember, 2026-07-26). The previously-flagged ambiguity is closed: the
/// PROJECT is still `dregg` (`README.md`, `www.dregg.net`, the workspace, the token) and does not
/// move; this names the play SURFACE, the thing at `arcade.dregg.net`. Exactly one string on the
/// product says both — [`dreggnet_catalog::arcade_lineage`], in the footer.
pub const PRODUCT_NAME: &str = dreggnet_catalog::SURFACE_NAME;

/// The brand mark — four squares, one lit: a board where a move landed. Inline SVG (no external
/// asset, no request), `aria-hidden` because the adjacent brand text is the accessible name.
const MARK: &str = "<svg viewBox=\"0 0 24 24\" aria-hidden=\"true\" focusable=\"false\">\
     <rect x=\"1.5\" y=\"1.5\" width=\"9.5\" height=\"9.5\" rx=\"2.6\"></rect>\
     <rect x=\"13\" y=\"1.5\" width=\"9.5\" height=\"9.5\" rx=\"2.6\"></rect>\
     <rect x=\"1.5\" y=\"13\" width=\"9.5\" height=\"9.5\" rx=\"2.6\"></rect>\
     <rect class=\"lit\" x=\"13\" y=\"13\" width=\"9.5\" height=\"9.5\" rx=\"2.6\"></rect></svg>";

/// The sticky top bar — the product mark plus the real surfaces. `active` names the current one
/// (`""` for none) so it can carry `aria-current="page"`.
///
/// THE FRONT DOOR IS THE GAME. `/descent/play` (the in-tab, beacon-seeded, wasm-backed run) was
/// built and mounted but **nothing on the product linked to it** — every "The Descent" affordance
/// landed on `/descent`, the no-cheat *board*, so a stranger could read a leaderboard and never find
/// the game. The flagship nav item now points at the playable surface; the board keeps its own item
/// beside it (both keys light the `descent` nav group).
fn topbar(active: &str) -> String {
    let item = |href: &str, key: &str, label: &str| -> String {
        let cur = if active == key {
            " aria-current=\"page\""
        } else {
            ""
        };
        format!("<a href=\"{href}\"{cur}>{label}</a>")
    };
    format!(
        "<header class=\"topbar\"><div class=\"topbar-in\">\
         <a class=\"brand\" href=\"/\">{MARK}<span class=\"brand-name\">{PRODUCT_NAME}</span></a>\
         <nav class=\"topnav\" aria-label=\"Surfaces\">{play}{board}{offerings}{guide}{you}</nav>\
         </div></header>",
        MARK = MARK,
        PRODUCT_NAME = PRODUCT_NAME,
        // "All games", not "The Lab": the shelf is now the curated ship list
        // (`dreggnet_catalog::SHIPPED_KEYS`), not a bin of experiments. The sprite gallery left
        // the nav with the same reasoning — it is a curiosity, not a thing we ship; its route and
        // its footer link are untouched.
        offerings = item("/offerings", "offerings", "All games"),
        play = item(DESCENT_PLAY_PATH, "descent", "The Descent"),
        board = item("/descent", "descent-board", "Board"),
        // LAST, deliberately: the nav's job is to get someone into a game, and a reader who wants
        // the rules first will look for this word rather than needing it put in front of them.
        guide = item("/guide", "guide", "How to play"),
        // ⚑ AND THE WAY BACK. Without a nav item the YOU page is exactly as unfindable as it was
        // when it did not exist — "is there a place I go to see my stats?" is answered by a LINK,
        // not by a route. It sits at the end because it is the return trip, not the way in.
        you = item(you::YOU_PATH, "you", "You"),
    )
}

/// ⚑ **THE ONE LIVE REGION ON A SESSION PAGE** — a single short line, not the board.
///
/// The board used to live inside `aria-live="polite"` and the whole subtree is replaced on every
/// swap, so a move queued up to 121 square descriptions for announcement (and the spectator page's
/// 400ms SSE pulse did it unprompted). This is the whole live region now: `role="status"` on one
/// empty sr-only paragraph that [`ENHANCE_SCRIPT`] writes the short "what just happened · where the
/// game stands" line into after a swap. It is emitted OUTSIDE the swapped region, so it is a node
/// that already exists at announcement time — the case screen readers handle reliably.
///
/// Empty on a fresh page load ON PURPOSE: a live region is for CHANGES, and everything a first load
/// has to say is in the document a reader is about to read anyway (the `.notice` banner keeps its own
/// `role="status"`).
pub(crate) const LIVE_SAY: &str = "<p id=\"live-say\" class=\"sr-only\" role=\"status\" aria-live=\"polite\" \
     aria-atomic=\"true\"></p>";

/// **The progressive-enhancement script** — the ONLY client JS on the whole product, inlined (the
/// CSP + no-build reality forbid an external file). It makes the affordance play loop feel LIVE
/// without a framework, a router, or a state store: the server stays authoritative and the client
/// only swaps the one fragment the server re-rendered.
///
/// It delegates a single `submit` listener off `document` (so forms swapped IN later are handled
/// with no re-binding). For a POST-`/act` affordance form (`form.affordance` — a menu control — or
/// `form.cell` — a board square), it: cancels the native navigation; disables the pressed button +
/// marks the form `pending`; POSTs the SAME body with an `X-Fragment: 1` header; and replaces the
/// `#live-surface` region's HTML with the returned FRAGMENT (the re-rendered surface — notice,
/// board/forms, receipt), so a move updates the board in place with no full reload. It then moves
/// focus to the live region and scrolls the board into view (honouring `prefers-reduced-motion`).
///
/// **Progressive**: if JS is off the plain `<form>` POST works exactly as before (server-form
/// fallback); if the `fetch` itself fails, it re-submits the form the classic way — the current
/// no-JS behaviour is the guaranteed floor, never bypassed.
const ENHANCE_SCRIPT: &str = r##"<script>
(function(){
  "use strict";
  var REGION="live-surface";
  var SAY="live-say";
  function reduced(){return window.matchMedia&&window.matchMedia("(prefers-reduced-motion: reduce)").matches;}
  /* ANNOUNCE THE CHANGE, NOT THE BOARD. The swapped region is no longer a live region (a whole-subtree
     replacement inside one is announced in full — up to 121 sr-only squares per move, and on the
     spectator page every 400ms). This copies TWO short lines out of the fragment into the page's one
     persistent status line: the notice's `data-say` (the server's own short form of "what just
     happened", cut before the 64-character receipt hex nobody wants read aloud), and the surface's
     headline state paragraph — automatafl's "turn 3 · phase: REVEAL", a market's standing. Writing to
     a node that ALREADY EXISTS is what makes this announce at all; re-inserting a live region does
     not reliably. Guarded on the text having CHANGED, so an SSE pulse that re-renders the same
     position says nothing. */
  function announce(root){
    var say=document.getElementById(SAY);
    if(!say||!root||!root.querySelector)return;
    var parts=[];
    var n=root.querySelector(".notice");
    var said=n?(n.getAttribute("data-say")||n.textContent||""):"";
    if(said)parts.push(said);
    var head=root.querySelector(".af-table>p.prose")||root.querySelector("p.prose");
    if(head&&head.textContent)parts.push(head.textContent);
    var text=parts.join(" · ").replace(/\s+/g," ").trim();
    if(text&&say.textContent!==text)say.textContent=text;
  }
  document.addEventListener("submit",function(ev){
    var form=ev.target;
    if(!form||form.tagName!=="FORM")return;
    if(form.classList.contains("binary-operation")){
      ev.preventDefault();
      if(form.classList.contains("in-flight"))return;
      var input=form.querySelector("input[type=file]");
      var status=form.querySelector("[role=status]");
      if(!input||!input.files||!input.files[0]){
        if(status)status.textContent="Choose the canonical proof or receipt first.";
        return;
      }
      var btn=form.querySelector("button[type=submit]");
      form.classList.add("in-flight","pending");
      if(btn)btn.disabled=true;
      if(status)status.textContent="Verifying opaque receipt…";
      fetch(form.getAttribute("action"),{
        method:"POST",
        headers:{"Content-Type":form.getAttribute("data-media")||"application/octet-stream","Accept":"application/json"},
        body:input.files[0],
        credentials:"same-origin"
      }).then(function(r){
        return r.text().then(function(body){if(!r.ok)throw new Error(body||("HTTP "+r.status));return body;});
      }).then(function(){window.location.reload();}).catch(function(err){
        form.classList.remove("in-flight","pending");
        if(btn)btn.disabled=false;
        if(status)status.textContent="Refused: "+err.message;
      });
      return;
    }
    if(!(form.classList.contains("affordance")||form.classList.contains("cell")))return;
    var action=form.getAttribute("action")||"";
    if(action.indexOf("/act")===-1)return;
    var live=document.getElementById(REGION);
    if(!live)return; /* nothing to swap into — let the browser navigate (fallback) */
    ev.preventDefault();
    var btn=form.querySelector("button[type=submit]")||form.querySelector("button");
    if(form.classList.contains("in-flight"))return; /* ignore a double-submit */
    form.classList.add("in-flight","pending");
    if(btn)btn.disabled=true;
    var body=new URLSearchParams(new FormData(form)).toString();
    fetch(action,{
      method:"POST",
      headers:{"X-Fragment":"1","Content-Type":"application/x-www-form-urlencoded","Accept":"text/html"},
      body:body,
      credentials:"same-origin"
    }).then(function(r){
      if(!r.ok)throw new Error("HTTP "+r.status);
      return r.text();
    }).then(function(html){
      var cur=document.getElementById(REGION);
      if(!cur)return;
      cur.innerHTML=html;
      cur.classList.remove("swap-in");
      void cur.offsetWidth; /* restart the transition */
      cur.classList.add("swap-in");
      announce(cur);
      try{cur.focus({preventScroll:true});}catch(e){cur.focus();}
      var board=cur.querySelector(".coordgrid")||cur;
      if(board&&board.scrollIntoView)board.scrollIntoView({block:"nearest",behavior:reduced()?"auto":"smooth"});
    }).catch(function(){
      /* the fetch path failed — restore the control and let the classic form POST navigate */
      form.classList.remove("in-flight","pending");
      if(btn)btn.disabled=false;
      form.submit();
    });
  },false);
  /* THE REALTIME SUBSCRIBER. A simultaneous-move table (automatafl) leaves the waiting seat with
     nothing to do but reload; this holds one EventSource open and swaps in the server's re-render
     of THIS viewer's surface the moment the opponent seals, opens, or resolves. The stream is
     per-viewer, so the fog it carries is the fog the page was served with.
     Degrades to nothing: no EventSource (or no data-events) => the old reload path, untouched.
     Never clobbers a submit in flight, and never fights the user's own optimistic swap. */
  function subscribe(){
    var live=document.getElementById(REGION);
    if(!live)return;
    var url=live.getAttribute("data-events");
    if(!url||!window.EventSource)return;
    var es;
    try{es=new EventSource(url,{withCredentials:true});}catch(e){return;}
    es.onmessage=function(ev){
      var cur=document.getElementById(REGION);
      if(!cur)return;
      if(cur.querySelector("form.in-flight"))return; /* a press is resolving — let it land first */
      var html=ev.data;
      if(cur.hasAttribute("data-readonly"))html="<fieldset class=\"spectate-lock\" disabled>"+html+"</fieldset>";
      if(cur.innerHTML===html)return;
      cur.innerHTML=html;
      cur.classList.remove("swap-in");
      void cur.offsetWidth;
      cur.classList.add("swap-in");
      /* ⚑ The 400ms pulse used to land INSIDE a live region, so a spectator with a screen reader was
         read the whole board over and over with nothing having happened. `announce` speaks only when
         the short line actually changed. */
      announce(cur);
    };
  }
  if(document.readyState==="loading")document.addEventListener("DOMContentLoaded",subscribe,false);
  else subscribe();
})();
</script>"##;

/// The page footer — states the one property the whole product rests on, names where the arcade
/// sits inside the project, and repeats the nav.
///
/// ⚑ THE FOOTER IS THE ONE PLACE THAT SAYS BOTH NAMES. The top bar and every `<title>` say
/// `Dragon's Arcade` (the surface); `dreggnet_catalog::arcade_lineage` says once, quietly, that it
/// is the play surface of the `dregg` project. Repeating the pair anywhere else turns a name into
/// noise, and dropping it entirely would leave a visitor with no way to connect the arcade to the
/// project whose domain they are on.
pub(crate) fn footer() -> String {
    format!(
        "<footer class=\"foot\">\
         <p>Every move is re-run against the rules before it counts — here, in this server, \
         not on a blockchain.</p>\
         <p class=\"lineage\">{lineage}</p>\
         <nav aria-label=\"Footer\"><a href=\"/descent\">The Descent</a>\
         <a href=\"/automatafl\">Automatafl</a>\
         <a href=\"/offerings\">All games</a><a href=\"/guide\">How to play</a>\
         <a href=\"/gallery\">Gallery</a>\
         <a href=\"/health\">Status</a></nav></footer>",
        lineage = esc(dreggnet_catalog::arcade_lineage()),
    )
}

/// **Wrap a body fragment in the full product document** — head (charset / viewport / title / the
/// inlined [`STYLE`]) + the shared [`topbar`] + the fragment + the [`FOOTER`]. Every served surface
/// goes through here, which is what makes them one product rather than a pile of pages.
///
/// `title` is the `<title>` text (escaped here — callers pass raw); `active` marks the current nav
/// item (`"offerings"` / `"descent"` / `"gallery"` / `""`).
pub(crate) fn document(title: &str, active: &str, body: &str) -> String {
    document_with_head(title, active, "", body)
}

/// [`document`] with EXTRA `<head>` markup — a page-specific stylesheet, and the OpenGraph /
/// Twitter-card tags a *shareable* surface needs. Meta tags are only honoured in the head, so a
/// page whose whole job is to be posted somewhere (the Descent run-card) cannot emit them from the
/// body; this is the one seam that lets it emit them without hand-rolling the product shell (the
/// way `descent_play`'s standalone `shell_page` did, and drifted out of the `ENHANCE_SCRIPT` it
/// silently dropped).
pub(crate) fn document_with_head(
    title: &str,
    active: &str,
    head_extra: &str,
    body: &str,
) -> String {
    format!(
        "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">\
         <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\
         <meta name=\"color-scheme\" content=\"dark\">\
         <title>{title}</title>{head_extra}{style}</head><body>{topbar}{body}{footer}{script}</body></html>",
        title = esc(title),
        head_extra = head_extra,
        style = STYLE,
        topbar = topbar(active),
        body = body,
        footer = footer(),
        script = ENHANCE_SCRIPT,
    )
}

/// A breadcrumb strip — `← all offerings · **Title** · session {id}`. The session id is set in the
/// mono voice (it is verifiable material, like a hash or a seed).
fn crumb(title: &str, id: &SessionId) -> String {
    format!(
        "<div class=\"crumb\"><a href=\"/offerings\">← All games</a>\
         <span class=\"sep\">·</span><strong>{title}</strong>\
         <span class=\"sep\">·</span><span class=\"sid\">session {id}</span></div>",
        title = esc(title),
        id = esc(&id.0),
    )
}

/// The notice banner — *what just happened*. A refusal is honest and red; a landed turn is green.
/// The `✓`/`✕` glyph is drawn by CSS (`.notice::before`), so the text stays clean for a reader.
///
/// `data-say` is the SHORT form, for [`LIVE_SAY`]: the banner itself carries
/// `PlayerTurnReceipt::compact_text`, whose second clause is a 64-character executor receipt hex, and
/// a screen reader spelling out 64 hex digits after every move is not an announcement. The cut is the
/// receipt grammar's own first ` · ` separator, so the announced line is the clause that says what
/// happened ("Turn committed — Select (3,1)") and the full text stays on screen, verbatim, for anyone
/// who wants the id. A refusal has no separator and is announced whole — it is already one sentence.
fn notice_html(notice: Option<&str>) -> String {
    notice
        .map(|n| {
            let cls = if n.starts_with("Refused") {
                "notice refused"
            } else {
                "notice ok"
            };
            let say = n.split(" · ").next().unwrap_or(n);
            format!(
                "<div class=\"{cls}\" role=\"status\" data-say=\"{say}\">{}</div>",
                esc(n),
                say = esc(say),
            )
        })
        .unwrap_or_default()
}

/// The receipt strip — the product's signature line, in the mono voice: the chain, re-verified by
/// replay, right now, with its turn count and the verifier's own detail.
fn receipt_html(verify: &VerifyReport, label: &str, verify_href: &str) -> String {
    let cls = if verify.verified { "ok" } else { "refused" };
    format!(
        "<div class=\"receipt {cls}\"><span class=\"dot\"></span>\
         <span class=\"label\">{label}</span><span class=\"verdict\">{v}</span>\
         <span>{turns}</span><span class=\"detail\">{detail}</span>\
         <a class=\"replay-verify\" rel=\"nofollow\" href=\"{verify_href}\">Replay-verify</a></div>\
         <details class=\"receipt-gloss\">\
         <summary>Why does this line say &ldquo;verified&rdquo; when my move says \
         &ldquo;asserted&rdquo;?</summary><p>{gloss}</p></details>",
        cls = cls,
        label = esc(label),
        v = if verify.verified {
            "verified"
        } else {
            "NOT VERIFIED"
        },
        turns = turn_count(verify.turns),
        detail = esc(&verify.detail),
        verify_href = esc(verify_href),
        gloss = RECEIPT_REGISTER_GLOSS,
    )
}

/// ⚑ **THE TWO WORDS, RECONCILED — once, where they sit next to each other.**
///
/// A first-time reader found `Recorded (asserted)` in the success banner and `verified` in the
/// receipt strip *describing the same action on the same page* — one hedging, one certain, with
/// nothing saying why (`docs/reference/UX-QA-SWEEP-2026-07-26.md`, finding 5). They are not two
/// grades of the same claim: they have DIFFERENT SUBJECTS. `verified` is about the MOVES (the chain
/// re-ran against the rules and matched); `asserted` is about the NAME (this surface takes your
/// label at face value and checks no signature — `PlayerAttributionGrade::Asserted`).
///
/// It lives HERE, beside the strip, rather than in the banner: the banner fires on every press and a
/// paragraph of vocabulary repeated per move is noise, while the distinction is a standing property
/// of the page. A signed act (`act_signed`) reads `Signed by …` in the banner instead, at which point
/// the second half of this sentence stops applying to it — and says so.
///
/// ⚑ **AND IT IS FOLDED, because the fix for a jargon complaint became a new instance of it.** This
/// paragraph shipped OPEN, appended by [`receipt_html`] to every offering-session render — which put
/// a lesson in the product's own vocabulary directly under the move buttons on the FIRST screen,
/// before the player had moved at all, pre-empting a question nobody had yet asked. It is true and it
/// is worth keeping, so it stays; it now sits behind a `<details>` whose summary IS the question
/// ("why does this say verified when my move says asserted?"). A reader who wondered gets the whole
/// answer in one click; a reader who did not never reads a vocabulary note to reach the game. Nothing
/// is hidden from a text-mode reader either: `<summary>` and the paragraph are both plain document
/// text, so a screen reader, a `curl`, and a page-text search all still find every word.
const RECEIPT_REGISTER_GLOSS: &str = "Two different words, two different subjects. \
     <strong>verified</strong> is about the MOVES: every turn in this session was re-run against the \
     rules just now and came out the same. <strong>asserted</strong>, on a move's own receipt, is \
     about the NAME on it: this page takes the name you gave at face value and checks no signature, \
     so it can say the move was legal and cannot say who made it. A move signed with a key reads \
     <strong>Signed by</strong> instead.";

/// `"1 verified turn"` / `"5 verified turns"` — the count, pluralised properly (the old line always
/// said "turns", so a one-turn session read "1 verified turns").
fn turn_count(turns: usize) -> String {
    if turns == 1 {
        "1 verified turn".to_string()
    } else {
        format!("{turns} verified turns")
    }
}

// ═════════════════════════════════════════════════════════════════════════════════════════
// THE MULTI-OFFERING WEB CATALOG — the generic offering router lifted to the core.
//
// The single-DungeonOffering surface above is offering #0 on the web. This section makes
// dreggnet-web a MULTI-OFFERING catalog over the frontend-agnostic `OfferingHost`: browse the
// registered offerings, then open + play ANY of them (a dungeon, a council, a market) in the
// browser — the SAME `open/advance/render/verify` verbs, one registry, the Session type erased.
//
// Routes (additive to `router` above; a separate `catalog_router`):
//   GET  /offerings                              — the catalog (a card + "play" link per offering)
//   GET  /offerings/{key}/session/{id}           — open (lazily) + render an offering session
//   POST /offerings/{key}/session/{id}/act       — advance ONE real turn + re-render
//   GET  /offerings/{key}/session/{id}/verify    — re-verify the committed chain (JSON)
// ═════════════════════════════════════════════════════════════════════════════════════════

/// A unit of work run ON the host's owning thread, against the live [`OfferingHost`].
type HostJob = Box<dyn FnOnce(&mut OfferingHost) + Send + 'static>;

/// **A thread-confined [`OfferingHost`] handle.** The host owns heterogeneous offering sessions,
/// some of which are `!Send` (a [`dreggnet_council::CouncilOffering`] session holds `Rc`-backed ballot caps — the
/// same reason the discord-bot's per-offering `Store` uses a dedicated thread). So the host cannot
/// be a `Mutex<OfferingHost>` in an axum `State` (that needs `Send`). Instead the host lives on ONE
/// owning thread and every access is a job shipped to it; only the job's plain-data result
/// (a [`Surface`], an [`Outcome`], a [`VerifyReport`], a `Vec<OfferingInfo>` — all `Send`) crosses
/// back. The handle itself is just a channel sender, so it is `Send + Sync` and drops straight into
/// an axum `State`. This is the discord-bot `Store` generalised to a whole registry — the pattern a
/// Telegram / WeChat frontend reuses unchanged.
pub struct HostThread {
    jobs: SyncSender<HostJob>,
}

impl HostThread {
    /// Spawn the owning thread and BUILD the host on it (`build` runs on the thread, so the
    /// registered offerings + their sessions are born there and never cross a thread boundary).
    pub fn spawn(build: impl FnOnce() -> OfferingHost + Send + 'static) -> HostThread {
        let (jobs, rx) = sync_channel::<HostJob>(64);
        std::thread::Builder::new()
            .name("offering-host".to_string())
            .spawn(move || {
                let mut host = build();
                while let Ok(job) = rx.recv() {
                    job(&mut host);
                }
            })
            .expect("spawn the offering host thread");
        HostThread { jobs }
    }

    /// Run `f` against the host on the owning thread and hand back its (`Send`) result. Blocks the
    /// caller until the job returns — one short, CPU-bound offering turn, same cost profile as the
    /// single-offering surface's `Mutex` critical section.
    pub fn run<R: Send + 'static>(
        &self,
        f: impl FnOnce(&mut OfferingHost) -> R + Send + 'static,
    ) -> R {
        let (tx, rx) = sync_channel::<R>(1);
        self.jobs
            .send(Box::new(move |host| {
                let _ = tx.send(f(host));
            }))
            .expect("the offering host thread is alive");
        rx.recv().expect("the offering host thread answered")
    }
}

/// A unit of work run ON the per-identity RPG worlds' owning thread, against the live
/// [`PlayerWorlds`] registry.
type PlayerJob = Box<dyn FnOnce(&mut PlayerWorlds) + Send + 'static>;

/// **A thread-confined [`PlayerWorlds`] handle** — the [`HostThread`] pattern for the per-identity
/// RPG worlds. A [`PlayerWorlds`] owns one `!Send` [`OfferingHost`] per derived identity, so like
/// the shared catalog host it lives on ONE owning thread and every access is a job shipped to it;
/// only the (`Send`) result crosses back. The handle is a channel sender — `Send + Sync`, drops
/// into an axum `State`.
pub struct PlayerHostThread {
    jobs: SyncSender<PlayerJob>,
}

impl PlayerHostThread {
    /// Spawn the owning thread and BUILD the registry on it (`build` runs on the thread, so every
    /// per-identity host — and its `!Send` sessions — is born there and never crosses a boundary).
    pub fn spawn(build: impl FnOnce() -> PlayerWorlds + Send + 'static) -> PlayerHostThread {
        let (jobs, rx) = sync_channel::<PlayerJob>(64);
        std::thread::Builder::new()
            .name("player-worlds".to_string())
            .spawn(move || {
                let mut worlds = build();
                while let Ok(job) = rx.recv() {
                    job(&mut worlds);
                }
            })
            .expect("spawn the player-worlds thread");
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
            .expect("the player-worlds thread is alive");
        rx.recv().expect("the player-worlds thread answered")
    }
}

/// **The axum state for the multi-offering catalog** — a thread-confined [`OfferingHost`] behind a
/// `Send + Sync` handle. Shared behind an `Arc` as the handler `State`.
pub struct CatalogState {
    /// The host handle (the registry of offerings + their live sessions, on its owning thread).
    /// The SHARED tables — the games (dungeon/council/market/tug/…) and the service offerings —
    /// live here: a council with one voter per host is not a council, so those are inherently
    /// shared and stay on this ONE host across every viewer.
    host: HostThread,
    /// The per-identity RPG worlds handle. The eight [`is_rpg_key`] surfaces (trade / inventory /
    /// craft / …) are per-player by nature — an inventory is yours — so every RPG-key session
    /// operation routes to the VIEWER's own [`OfferingHost`] here ([`run_offering`](Self::run_offering)),
    /// keyed by their derived identity. Two viewers on the same web surface therefore have
    /// ISOLATED inventories: player A forges an item and player B does not see it. This is the
    /// shared-layer form of the split the Discord bot already runs.
    players: PlayerHostThread,
    /// Deployment custody for every game route. Ordinary restarts retain the
    /// host incarnation and live generation; a close/reopen advances the
    /// generation, so an old typed action can never name the new world.
    game_epochs: GameEpochLedger,
    /// Serializes host open/close/dispatch with epoch reads and mutations. The
    /// host thread alone orders host jobs; this companion boundary prevents a
    /// close/reopen from changing the ledger between a context read and the
    /// corresponding host action.
    game_lifecycle: Mutex<()>,
    /// Process-local MAC key for server-issued ordinary/custodial form
    /// coordinates. Restart invalidates old tabs (safe refusal); the durable
    /// game route itself remains unchanged and a reload obtains a fresh token.
    game_form_key: [u8; 32],
    /// Retains the deployment-owned registry and durable exact-effect adapter
    /// for the opt-in private Bazaar route. The ordinary catalog never invents
    /// a policy and leaves this absent.
    #[cfg(feature = "private-bazaar-live")]
    private_bazaar_deployment: Option<dreggnet_catalog::PrivateBazaarLiveDeployment>,
}

#[derive(Debug)]
pub(crate) enum CatalogGameError {
    Host(HostError),
    Epoch(GameEpochError),
    Spine(GameSpineError),
    Poisoned,
}

impl std::fmt::Display for CatalogGameError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Host(error) => error.fmt(f),
            Self::Epoch(error) => error.fmt(f),
            Self::Spine(error) => error.fmt(f),
            Self::Poisoned => write!(f, "game lifecycle lock was poisoned"),
        }
    }
}

impl std::error::Error for CatalogGameError {}

impl CatalogState {
    /// A fresh catalog over the full shared DreggNet portfolio (shared tables) plus an in-memory
    /// per-identity RPG worlds registry — see [`catalog_default_host`] and [`PlayerWorlds`].
    pub fn new() -> Self {
        CatalogState {
            host: HostThread::spawn(catalog_default_host),
            players: PlayerHostThread::spawn(PlayerWorlds::new),
            game_epochs: ephemeral_game_epochs(),
            game_lifecycle: Mutex::new(()),
            game_form_key: random_game_form_key(),
            #[cfg(feature = "private-bazaar-live")]
            private_bazaar_deployment: None,
        }
    }

    /// A catalog over a caller-built shared host (the offerings are registered inside `build`, which
    /// runs on the owning thread), with an in-memory per-identity RPG worlds registry. Lets a
    /// deployment register its own shared offering set; the RPG worlds stay in-memory (the tests'
    /// path — see [`with_hosts`](Self::with_hosts) for the durable pair).
    pub fn with_host(build: impl FnOnce() -> OfferingHost + Send + 'static) -> Self {
        CatalogState {
            host: HostThread::spawn(build),
            players: PlayerHostThread::spawn(PlayerWorlds::new),
            game_epochs: ephemeral_game_epochs(),
            game_lifecycle: Mutex::new(()),
            game_form_key: random_game_form_key(),
            #[cfg(feature = "private-bazaar-live")]
            private_bazaar_deployment: None,
        }
    }

    /// A catalog over a caller-built shared host AND a caller-built per-identity RPG worlds registry
    /// — the full production seam ([`make_app_parts`] passes the env-resolved durable pair:
    /// [`resolve_demo_host`] + [`resolve_player_worlds`], so both the shared game sessions and each
    /// player's RPG world survive a restart by move-log replay).
    pub fn with_hosts(
        build_host: impl FnOnce() -> OfferingHost + Send + 'static,
        build_players: impl FnOnce() -> PlayerWorlds + Send + 'static,
    ) -> Self {
        Self::with_hosts_and_game_epochs(build_host, build_players, ephemeral_game_epochs())
    }

    /// Build both host partitions over an explicitly owned game-epoch ledger.
    /// Deployments use the durable form; tests and confined embedders may pass
    /// an in-memory ledger deliberately.
    pub fn with_hosts_and_game_epochs(
        build_host: impl FnOnce() -> OfferingHost + Send + 'static,
        build_players: impl FnOnce() -> PlayerWorlds + Send + 'static,
        game_epochs: GameEpochLedger,
    ) -> Self {
        CatalogState {
            host: HostThread::spawn(build_host),
            players: PlayerHostThread::spawn(build_players),
            game_epochs,
            game_lifecycle: Mutex::new(()),
            game_form_key: random_game_form_key(),
            #[cfg(feature = "private-bazaar-live")]
            private_bazaar_deployment: None,
        }
    }

    /// Build the real shared catalog with one explicitly configured private
    /// Bazaar raid and retain its worker-side registry/adapter beside the host.
    /// The generic `/offerings/{key}/session/{id}` GET/POST routes need no
    /// special-case handler: they drive this registered Offering directly.
    #[cfg(feature = "private-bazaar-live")]
    pub fn with_private_bazaar(
        deployment: dreggnet_catalog::PrivateBazaarLiveDeployment,
        characters: dreggnet_catalog::PrivateBazaarCharacterStore,
    ) -> Self {
        Self::with_private_bazaar_over(deployment, characters, None, SessionPolicy::default())
    }

    /// Production form of [`with_private_bazaar`](Self::with_private_bazaar):
    /// attach and boot-resume the generic host move log when `session_dir` is
    /// present. Replaying Enter reconstructs the exact listed market/journey
    /// and repopulates this deployment's process-local worker registry.
    #[cfg(feature = "private-bazaar-live")]
    pub fn with_private_bazaar_over(
        deployment: dreggnet_catalog::PrivateBazaarLiveDeployment,
        characters: dreggnet_catalog::PrivateBazaarCharacterStore,
        session_dir: Option<std::path::PathBuf>,
        policy: SessionPolicy,
    ) -> Self {
        let mounted = deployment.clone();
        let epoch_dir = session_dir.clone();
        CatalogState {
            host: HostThread::spawn(move || {
                #[cfg(feature = "fhegg-settlement")]
                let base = demo_host_with_resolved_fhegg();
                #[cfg(not(feature = "fhegg-settlement"))]
                let base = demo_host();
                #[cfg(feature = "dark-amm-game")]
                let mut base = demo_host_with_resolved_dark_amm(base);
                #[cfg(not(feature = "dark-amm-game"))]
                let mut base = base;
                characters.register_dungeon(&mut base);
                mounted.register(&mut base);
                assemble_demo_host(base, session_dir, policy)
            }),
            players: PlayerHostThread::spawn(resolve_player_worlds),
            game_epochs: resolve_game_epochs(epoch_dir.as_deref()),
            game_lifecycle: Mutex::new(()),
            game_form_key: random_game_form_key(),
            private_bazaar_deployment: Some(deployment),
        }
    }

    #[cfg(feature = "private-bazaar-live")]
    pub fn private_bazaar_deployment(
        &self,
    ) -> Option<&dreggnet_catalog::PrivateBazaarLiveDeployment> {
        self.private_bazaar_deployment.as_ref()
    }

    /// **Route a `(key, session)`-scoped host job to the host that OWNS it for `viewer`.** An
    /// [`is_rpg_key`] offering runs against the viewer's own per-identity RPG world (their isolated
    /// inventory); everything else — the shared games, party, and services — runs against the ONE catalog
    /// host. This ONE routing decision is the whole fix: it is why two viewers never share an
    /// inventory while a council / tug stays a single shared table.
    pub(crate) fn run_offering<R: Send + 'static>(
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

    /// Ensure a route and bind its game generation under one lifecycle lock.
    /// This is the only opener new frontend code should use.
    pub(crate) fn ensure_open_and_bind(
        &self,
        key: &str,
        id: &SessionId,
        viewer: &DreggIdentity,
        opener: Option<Attribution>,
    ) -> Result<(bool, Option<GameSessionRef>), CatalogGameError> {
        let _guard = self
            .game_lifecycle
            .lock()
            .map_err(|_| CatalogGameError::Poisoned)?;
        let key_owned = key.to_string();
        let id_owned = id.clone();
        let opened = self
            .run_offering(key, viewer, move |host| {
                host.ensure_open_as(&key_owned, &id_owned, opener.as_ref())
            })
            .map_err(CatalogGameError::Host)?;
        if game_kind(key).is_none() {
            return Ok((opened, None));
        }
        if let Err(error) = self.game_epochs.bind_after_ensure(key, id, opened) {
            // `ensure_open_as` may have durably created the host session before
            // the separately persisted epoch ledger failed.  Never leave that
            // fresh host object as an unaddressable generationless ghost: it
            // would make every subsequent opener observe `opened = false` and
            // therefore permanently refuse to adopt it.
            if opened {
                let key_owned = key.to_string();
                let id_owned = id.clone();
                self.run_offering(key, viewer, move |host| {
                    host.close(&key_owned, &id_owned);
                });
            }
            return Err(CatalogGameError::Epoch(error));
        }
        let session = self
            .game_epochs
            .bound_session(key, id)
            .map_err(CatalogGameError::Epoch)?;
        Ok((opened, Some(session)))
    }

    /// Resolve the exact currently-live game address. This never adopts or
    /// creates a generation; callers must first pass through
    /// [`ensure_open_and_bind`](Self::ensure_open_and_bind).
    pub fn bound_game_session(
        &self,
        key: &str,
        id: &SessionId,
    ) -> Result<GameSessionRef, GameEpochError> {
        self.game_epochs.bound_session(key, id)
    }

    fn game_form_authority(
        &self,
        session: GameSessionRef,
        expected_pre_head: Vec<u8>,
    ) -> Result<GameFormAuthority, CatalogGameError> {
        if expected_pre_head.len() != 32 || !session.binding().is_bound() {
            return Err(CatalogGameError::Spine(GameSpineError::InvalidReference(
                "game form authority requires a bound route and exact 32-byte head".to_string(),
            )));
        }
        let token = self.game_form_token(&session, &expected_pre_head)?;
        Ok(GameFormAuthority {
            session,
            expected_pre_head,
            token,
        })
    }

    fn game_form_token(
        &self,
        session: &GameSessionRef,
        expected_pre_head: &[u8],
    ) -> Result<[u8; 32], CatalogGameError> {
        let GameSessionBinding::Bound {
            host_incarnation,
            session_generation,
        } = session.binding()
        else {
            return Err(CatalogGameError::Spine(
                GameSpineError::BindingContextRequired(session.clone()),
            ));
        };
        let mut mac = blake3::Hasher::new_keyed(&self.game_form_key);
        mac.update(b"dregg.web.game-form-authority.v1");
        for field in [
            session.offering().as_bytes(),
            session.session_id().0.as_bytes(),
            host_incarnation.as_bytes(),
            &session_generation.to_be_bytes(),
            expected_pre_head,
        ] {
            mac.update(&(field.len() as u64).to_be_bytes());
            mac.update(field);
        }
        Ok(*mac.finalize().as_bytes())
    }

    pub(crate) fn game_resource_token(
        &self,
        domain: &[u8],
        session: &GameSessionRef,
        observed_head: &[u8],
        resource: &str,
    ) -> Result<[u8; 32], CatalogGameError> {
        let GameSessionBinding::Bound {
            host_incarnation,
            session_generation,
        } = session.binding()
        else {
            return Err(CatalogGameError::Spine(
                GameSpineError::BindingContextRequired(session.clone()),
            ));
        };
        if observed_head.len() != 32 || resource.is_empty() {
            return Err(CatalogGameError::Spine(GameSpineError::InvalidReference(
                "game resource authority requires a name and exact 32-byte head".to_string(),
            )));
        }
        let generation_bytes = session_generation.to_be_bytes();
        let mut mac = blake3::Hasher::new_keyed(&self.game_form_key);
        mac.update(b"dregg.web.game-resource-authority.v1");
        for field in [
            domain,
            session.offering().as_bytes(),
            session.session_id().0.as_bytes(),
            host_incarnation.as_bytes(),
            &generation_bytes,
            observed_head,
            resource.as_bytes(),
        ] {
            mac.update(&(field.len() as u64).to_be_bytes());
            mac.update(field);
        }
        Ok(*mac.finalize().as_bytes())
    }

    pub(crate) fn presented_game_resource(
        &self,
        domain: &[u8],
        key: &str,
        id: &SessionId,
        resource: &str,
        host_incarnation_hex: &str,
        session_generation: u64,
        observed_head_hex: &str,
        token_hex: &str,
    ) -> Result<(GameSessionRef, Vec<u8>), CatalogGameError> {
        let incarnation = decode_hex_32(host_incarnation_hex).ok_or_else(|| {
            CatalogGameError::Spine(GameSpineError::InvalidReference(
                "malformed game resource host incarnation".to_string(),
            ))
        })?;
        let incarnation = GameHostIncarnation::new(incarnation).map_err(CatalogGameError::Spine)?;
        let observed_head = decode_hex_32(observed_head_hex)
            .ok_or_else(|| {
                CatalogGameError::Spine(GameSpineError::InvalidReference(
                    "malformed game resource observed head".to_string(),
                ))
            })?
            .to_vec();
        let token = decode_hex_32(token_hex).ok_or_else(|| {
            CatalogGameError::Spine(GameSpineError::InvalidReference(
                "malformed game resource authority token".to_string(),
            ))
        })?;
        let session = GameSessionRef::bound(key, id.clone(), incarnation, session_generation)
            .map_err(CatalogGameError::Spine)?;
        if token != self.game_resource_token(domain, &session, &observed_head, resource)? {
            return Err(CatalogGameError::Spine(GameSpineError::InvalidReference(
                "game resource authority token did not verify".to_string(),
            )));
        }
        Ok((session, observed_head))
    }

    pub(crate) fn presented_game_action(
        &self,
        key: &str,
        id: &SessionId,
        form: &OfferingActForm,
    ) -> Result<GameActionRef, CatalogGameError> {
        let action = Action::new(form.turn.clone(), form.turn.clone(), form.arg, true);
        self.presented_game_action_for(key, id, form, &action)
    }

    pub(crate) fn presented_game_action_for(
        &self,
        key: &str,
        id: &SessionId,
        form: &OfferingActForm,
        action: &Action,
    ) -> Result<GameActionRef, CatalogGameError> {
        let incarnation = form
            .game_host_incarnation
            .as_deref()
            .and_then(decode_hex_32)
            .ok_or_else(|| {
                CatalogGameError::Spine(GameSpineError::InvalidReference(
                    "missing or malformed game_host_incarnation".to_string(),
                ))
            })?;
        let incarnation = GameHostIncarnation::new(incarnation).map_err(CatalogGameError::Spine)?;
        let generation = form.game_session_generation.ok_or_else(|| {
            CatalogGameError::Spine(GameSpineError::InvalidReference(
                "missing game_session_generation".to_string(),
            ))
        })?;
        let head = form
            .game_expected_pre_head
            .as_deref()
            .and_then(decode_hex_32)
            .ok_or_else(|| {
                CatalogGameError::Spine(GameSpineError::InvalidReference(
                    "missing or malformed 32-byte game_expected_pre_head".to_string(),
                ))
            })?
            .to_vec();
        let presented_token = form
            .game_form_token
            .as_deref()
            .and_then(decode_hex_32)
            .ok_or_else(|| {
                CatalogGameError::Spine(GameSpineError::InvalidReference(
                    "missing or malformed game_form_token".to_string(),
                ))
            })?;
        let session = GameSessionRef::bound(key, id.clone(), incarnation, generation)
            .map_err(CatalogGameError::Spine)?;
        let expected_token = self.game_form_token(&session, &head)?;
        if presented_token != expected_token {
            return Err(CatalogGameError::Spine(GameSpineError::InvalidReference(
                "game form authority token did not verify".to_string(),
            )));
        }
        Ok(GameActionRef::new(session, action, head))
    }

    /// Execute against the freshly read live binding while holding the same
    /// lock used by close/reopen. The closure and host job complete before a
    /// lifecycle transition may begin.
    pub(crate) fn run_current_bound_game<R: Send + 'static>(
        &self,
        key: &str,
        id: &SessionId,
        viewer: &DreggIdentity,
        f: impl FnOnce(&mut OfferingHost, GameHostIncarnation, u64, GameSessionRef) -> R
        + Send
        + 'static,
    ) -> Result<R, CatalogGameError> {
        let _guard = self
            .game_lifecycle
            .lock()
            .map_err(|_| CatalogGameError::Poisoned)?;
        let generation = self
            .game_epochs
            .current_generation(key, id)
            .map_err(CatalogGameError::Epoch)?;
        let incarnation = self.game_epochs.host_incarnation();
        let session = self
            .game_epochs
            .bound_session(key, id)
            .map_err(CatalogGameError::Epoch)?;
        Ok(self.run_offering(key, viewer, move |host| {
            f(host, incarnation, generation, session)
        }))
    }

    /// Execute a command carrying a server-presented route. The presented
    /// binding is compared with freshly read ledger state before the host is
    /// touched. A signed command may lazy-resume an existing durable session,
    /// but it may never create a fresh host session or mint a generation.
    pub(crate) fn run_presented_bound_game<R: Send + 'static>(
        &self,
        presented: GameSessionRef,
        viewer: &DreggIdentity,
        opener: Attribution,
        f: impl FnOnce(&mut OfferingHost, GameHostIncarnation, u64, GameSessionRef) -> R
        + Send
        + 'static,
    ) -> Result<R, CatalogGameError> {
        let _guard = self
            .game_lifecycle
            .lock()
            .map_err(|_| CatalogGameError::Poisoned)?;
        let key = presented.offering().to_string();
        let id = presented.session_id().clone();
        let generation = self
            .game_epochs
            .current_generation(&key, &id)
            .map_err(CatalogGameError::Epoch)?;
        let incarnation = self.game_epochs.host_incarnation();
        let current = self
            .game_epochs
            .bound_session(&key, &id)
            .map_err(CatalogGameError::Epoch)?;
        if presented != current {
            return Err(CatalogGameError::Spine(GameSpineError::AddressMismatch {
                expected: current,
                presented,
            }));
        }
        let routed_key = key.clone();
        let result = self.run_offering(&key, viewer, move |host| {
            match host.ensure_open_as(&routed_key, &id, Some(&opener)) {
                Ok(false) => Ok(f(host, incarnation, generation, current)),
                Ok(true) => {
                    // A bound command proves it observed an already-live
                    // generation. Remove the accidentally created genesis and
                    // refuse instead of leaving ghost state behind.
                    let _ = host.close(&routed_key, &id);
                    Err(CatalogGameError::Spine(GameSpineError::InvalidReference(
                        "bound command would create a fresh host session".to_string(),
                    )))
                }
                Err(error) => Err(CatalogGameError::Host(error)),
            }
        });
        result
    }

    /// Inspect a supplied typed game address against this deployment's live
    /// authority epoch. This is the reusable native/controller seam behind the
    /// web renderer and an explicit stale-incarnation/generation gate.
    pub fn inspect_game_session(
        &self,
        session: GameSessionRef,
        audience: GameAudience,
    ) -> Result<dreggnet_catalog::GameSessionView, GameSpineError> {
        let routing_viewer = match &audience {
            GameAudience::Shared => DreggIdentity("viewer-blind-inspection".to_string()),
            GameAudience::AssertedPrivate(viewer) => viewer.clone(),
        };
        self.run_presented_bound_game(
            session,
            &routing_viewer,
            Attribution::from(routing_viewer.clone()),
            move |host, incarnation, generation, session| {
                inspect_bound_game_session(host, incarnation, generation, session, &audience)
            },
        )
        .map_err(|error| GameSpineError::Host(error.to_string()))?
    }

    /// Close one game world and retire its authority generation. A later open
    /// receives the next generation; ordinary restart does not.
    pub fn close_game_session(
        &self,
        key: &str,
        id: &SessionId,
        viewer: &DreggIdentity,
    ) -> Result<bool, GameEpochError> {
        if game_kind(key).is_none() {
            return Ok(false);
        }
        let _guard = self
            .game_lifecycle
            .lock()
            .map_err(|_| GameEpochError::Poisoned)?;
        let key_owned = key.to_string();
        let id_owned = id.clone();
        let closed = self.run_offering(key, viewer, move |host| host.close(&key_owned, &id_owned));
        if closed {
            self.game_epochs.mark_closed(key, id)?;
        }
        Ok(closed)
    }

    /// The SHARED catalog host's total live-session count — the `dregg_web_sessions_open` gauge
    /// source. The per-identity RPG worlds are counted separately (they are not the catalog host's
    /// sessions), so the gauge keeps meaning "shared catalog sessions".
    pub(crate) fn shared_session_count(&self) -> usize {
        self.host.run(|h| live_session_count(h))
    }

    /// **The FULL registry** — every mounted offering, advertised or not. The inventory view
    /// (metrics, harnesses, parity tests). A page a stranger reads wants
    /// [`list_advertised_offerings`](Self::list_advertised_offerings).
    pub fn list_offerings(&self) -> Vec<OfferingInfo> {
        self.host.run(|h| h.list_offerings())
    }

    /// **The SHELF** — the offerings on `dreggnet_catalog::SHIPPED_KEYS`. This is what
    /// `GET /offerings`, the Mini App and the Discord Activity paint.
    pub fn list_advertised_offerings(&self) -> Vec<OfferingInfo> {
        self.host.run(|h| h.list_advertised_offerings())
    }

    /// Re-verify session `(key, id)`'s committed chain (`None` if absent) — the offering's own proof.
    pub fn verify(&self, key: &str, id: &SessionId) -> Option<VerifyReport> {
        let key = key.to_string();
        let id = id.clone();
        self.host.run(move |h| h.verify(&key, &id))
    }

    /// Whether session `(key, id)` is live.
    pub fn is_open(&self, key: &str, id: &SessionId) -> bool {
        let key = key.to_string();
        let id = id.clone();
        self.host.run(move |h| h.is_open(&key, &id))
    }

    /// **Run the host's idle-TTL sweep** at its own injected clock — what the server bin's
    /// periodic sweeper calls (see `dreggnet-web-server`). A no-op (empty report) unless a
    /// [`SessionPolicy`] with a TTL was armed on the host. The host ALSO sweeps opportunistically
    /// before judging capacity on each fresh open, so this timer only covers the no-traffic case
    /// (idle sessions releasing memory with nobody knocking).
    pub fn sweep(&self) -> SweepReport {
        let (report, open) = self.host.run(|h| {
            let report = h.sweep_now();
            (report, live_session_count(h))
        });
        if !report.evicted.is_empty() {
            metrics::inc_sessions_evicted(report.evicted.len() as u64);
        }
        metrics::set_sessions_open(open as f64);
        report
    }
}

impl Default for CatalogState {
    fn default() -> Self {
        CatalogState::new()
    }
}

/// The host's TOTAL live-session count (summed over every registered offering) — what the
/// `dregg_web_sessions_open` gauge reports. Computed ON the host's owning thread (inside a
/// `HostThread::run` job) beside the open/sweep it observes.
fn live_session_count(host: &OfferingHost) -> usize {
    host.list_offerings().iter().map(|o| o.open_sessions).sum()
}

/// The shared catalog configuration for the public web surface. The electorate preserves the
/// existing browser identity contract: council member bytes are `blake3("alice"|"bob")`, exactly
/// the bytes [`web_identity`] renders as those users' substrate identities.
/// ⚑ THE DAY BINDING: this is [`dreggnet_catalog::CatalogConfig::live`], so the Descent (and the
/// campaign over it) mints its banked relics under the CURRENT verified drand day, re-resolved at
/// every open — a live run's relic ids therefore could not exist before that round was revealed.
/// The day is published by [`arm_todays_descent_day`] (boot + the periodic refresh in
/// `dreggnet-web-server`); until one is published, opening the Descent REFUSES rather than
/// serving the pre-computable deploy-seed-derived provenance root.
fn web_catalog_config() -> dreggnet_catalog::CatalogConfig {
    let members = ["alice", "bob"]
        .iter()
        .map(|u| *blake3::hash(u.as_bytes()).as_bytes())
        .collect();
    dreggnet_catalog::CatalogConfig::live(members)
}

/// **Arm (and re-arm) the day the web surface's Descent mints relics under.** Fetches today's
/// drand round, BLS-verifies it, and arms it in TWO places from that one fetch:
///
/// 1. **the catalog's process-wide published day** ([`dreggnet_catalog::publish_todays_descent_day`]),
///    the [`dreggnet_catalog::DescentDayBinding::Live`] source the relic-minting `/offerings/descent`
///    open resolves — until one is published, opening the Descent REFUSES rather than serving the
///    pre-computable deploy-seed-derived root;
/// 2. **the web's own live-beacon cache** ([`crate::descent::set_web_live_beacon`]), which
///    [`crate::descent::todays_day`] resolves the board / play / leaderboard day from.
///
/// Arming both from the SAME verified beacon is what keeps the catalog host and the board on the
/// identical world: a run opened through `/offerings/descent` re-verifies on the board, and
/// `/descent/play` plays the world the board scores. Blocking — call it from `spawn_blocking`, at
/// boot and on a timer, because a rolled UTC day makes the day stale and every mint-open then
/// REFUSES (fail-closed, by design) until the next arm.
///
/// The returned [`dreggnet_catalog::BeaconSource`] says whether the day is today's live round or
/// the explicitly-labeled pinned published round standing in for a transport outage. Log it: the
/// pinned round is a genuine BLS-verifiable reveal but NOT today's, so in that window the day's
/// relic provenance is predictable to anyone who knows the pinned round.
pub fn arm_todays_descent_day()
-> Result<dreggnet_catalog::BeaconSource, dreggnet_catalog::FetchError> {
    let resolved = procgen_dregg::beacon::todays_beacon(
        &dreggnet_catalog::HttpRoundFetch,
        dreggnet_catalog::DRAND_API_BASE,
    )?;
    let utc_day = procgen_dregg::beacon::current_utc_day();
    // Publish the seed for the catalog's Live day binding (the relic-minting open), then cache the
    // SAME verified beacon web-side for the board/play/leaderboard — so all three resolve one day.
    dreggnet_catalog::publish_todays_descent_day(utc_day, &resolved.beacon)
        .map_err(dreggnet_catalog::FetchError::Verify)?;
    crate::descent::set_web_live_beacon(utc_day, resolved.beacon);
    Ok(resolved.source)
}

/// **The default catalog host** — registers the full shared DreggNet portfolio through
/// [`dreggnet_catalog::full_catalog_host`]. Built on the host's owning thread
/// ([`HostThread::spawn`]), so each offering's `!Send` internals stay confined.
///
/// The council's electorate is derived from web usernames so a browser user can really vote: a web
/// user's [`DreggIdentity`] is `blake3(user)` hex, and a council member's identity is the hex of its
/// pubkey — so setting a member's pubkey to `blake3(user)`'s bytes makes that web user a council
/// member (`alice` and `bob` here). Quorum is 2, so a proposal enacts only once BOTH approve — a
/// real vote, drivable through the browser.
pub fn catalog_default_host() -> OfferingHost {
    dreggnet_catalog::full_catalog_host(&web_catalog_config())
}

/// **Register the five NON-GAME portfolio offerings** into a host — the full offering set beside the
/// games + the do-once feature surfaces. Each `impl`s the SAME [`Offering`] trait, so the web catalog
/// drives them through the one generic `open/advance/render/verify` path (unmodified, consumed):
/// - `doc` — a verifiable document store ([`dreggnet_doc::DocOffering`]);
/// - `names` — an identity / naming service ([`dreggnet_names::NamesOffering`]);
/// - `compute` — a confined compute-job market ([`dreggnet_compute::ComputeOffering`]);
/// - `grain` — a metered / rate-limited work offering ([`dreggnet_grain::GrainOffering`], budget 1000);
/// - `hermes` — the message relay ([`dreggnet_hermes::HermesOffering`]).
///
/// Compatibility wrapper retained for callers that extend a custom host. The default and demo hosts
/// already receive these services through [`dreggnet_catalog::full_catalog_host`].
pub fn register_non_game_offerings(host: &mut OfferingHost) {
    dreggnet_catalog::register_services(host, &dreggnet_catalog::CatalogConfig::default());
}

/// **Build the multi-offering catalog router** over a shared [`CatalogState`]. Additive to
/// [`router`] — mount both on one axum app (or serve the catalog alone).
pub fn catalog_router(state: Arc<CatalogState>) -> Router {
    // THE MARKET CANNOT SETTLE WITHOUT THIS. `/offerings/market/...` and the Dark Bazaar fold their
    // award ring through `dregg_intent::verified_settle::settle_ring_verified`, which fail-closes
    // when no verified gate is registered — so before 2026-07-25 a player landed a listing and two
    // sealed bids and was then refused at the settle. Install once, here, where the offering routes
    // are mounted (idempotent + cached; the server bin ALSO calls it and refuses to boot on
    // failure). A library embedder that ignores the log gets a loud line rather than a silent hole.
    if let Err(reason) = verified_settlement::install_verified_settlement_gate() {
        tracing::error!(
            advice = %verified_settlement::install_failure_advice(&reason),
            "verified settlement gate NOT installed — market settle will refuse"
        );
    }
    Router::new()
        .route("/offerings", get(get_catalog))
        .route("/offerings/{key}/session/{id}", get(get_offering_session))
        // THE REALTIME SEAM — one open `EventSource` per viewer; the server pushes THAT VIEWER's
        // re-rendered surface whenever it changes. Additive and degradable: a client without
        // `EventSource` never opens it and keeps the reload path.
        .route(
            "/offerings/{key}/session/{id}/events",
            get(get_offering_events),
        )
        .route("/offerings/{key}/session/{id}/act", post(post_offering_act))
        .route(
            "/offerings/{key}/session/{id}/act-signed",
            post(act_signed::post_offering_act_signed),
        )
        .route(
            "/offerings/{key}/session/{id}/verify",
            get(get_offering_verify),
        )
        .layer(middleware::from_fn(
            web_identity_http::bootstrap_visitor_identity,
        ))
        .with_state(state)
}

/// `GET /offerings` — the catalog page: a card per ADVERTISED offering
/// (`dreggnet_catalog::SHIPPED_KEYS`) with a "play" link opening a browser session of it. An
/// offering that is mounted but not shipped is absent here and still fully openable at
/// `/offerings/{key}/session/{id}` — the shelf is an advertising decision, not a gate.
async fn get_catalog(State(state): State<Arc<CatalogState>>) -> Html<String> {
    let offerings = state.list_advertised_offerings();
    Html(catalog_page(&offerings))
}

/// `GET /offerings/{key}/session/{id}` — open the offering session (lazily, seeded from the id) and
/// render its current [`Surface`] as an HTML page (prose/state + a POST form per cap-gated affordance).
async fn get_offering_session(
    State(state): State<Arc<CatalogState>>,
    Path((key, id)): Path<(String, String)>,
    headers: HeaderMap,
    Query(query): Query<WebQuery>,
) -> Response {
    let sid = SessionId::new(id);
    // The viewer's derived identity (the `dregg_user` cookie / `?user=` param) — the SAME identity a
    // POST attributes a turn to. A seated player renders their OWN hidden hand; a spectator sees fog.
    let (asserted_user, established) = web_user_established(&headers, &query);
    // An UNestablished raw `?user=` never mints its own RPG world — it collapses to the shared
    // anonymous world (capped hard), so a `?user=1,2,…,N` flood cannot exhaust memory.
    let (user, viewer) = catalog_route_viewer(&key, &asserted_user, established);
    // ⚑ A RESOLVED TABLE IS NEVER RE-MINTED. A finished match's world is RETIRED when the match ends
    // (its move-log archived so it stays replayable), so falling through to `ensure_open` below would
    // deploy a FRESH EMPTY BOARD under the finished match's own id: an empty table where the player's
    // game was, and a ghost back in "Games in progress" that the reaper would never touch again
    // (a resolution is write-once). Cheap: the prefix test rules out every ad-hoc id and every
    // non-lockable key before the registry is consulted at all.
    if let Some(resolution) = table_seats::lock_for_key(&key)
        .filter(|lock| lock.is_locked_table(&sid.0))
        .and_then(|_| table_seats::registry().resolution(&sid.0))
    {
        return (
            StatusCode::GONE,
            Html(finished_table_page(&key, &sid.0, &resolution)),
        )
            .into_response();
    }
    // Ensure the session is open (deploy on first touch), then render — LIFECYCLE-AWARE: the
    // viewer identity is the opener attribution (an ADVISORY `Asserted` quota lane — a forgeable
    // cookie; capacity + TTL are the real backstops), a policy refusal answers an honest 4xx
    // instead of minting, and an evicted persisted session transparently resumes.
    let opened = state.ensure_open_and_bind(
        &key,
        &sid,
        &viewer,
        Some(Attribution::Asserted {
            label: viewer.0.clone(),
        }),
    );
    metrics::set_sessions_open(state.shared_session_count() as f64);
    // AUDIT EMIT: the open decision (asserted-cookie attribution — the envelope names the
    // grade; a policy refusal is the gate WORKING and is recorded as `gated`).
    {
        let (kind, reason) = match &opened {
            Ok(_) => ("routed", String::new()),
            Err(CatalogGameError::Host(e)) => open_audit_parts(e),
            Err(error) => ("gated", error.to_string()),
        };
        audit::log().emit(
            audit::AuditEvent::new(
                "web",
                audit::Actor::asserted(&user).with_identity(viewer.0.clone()),
                audit::Surface::Http,
                audit::Input::new("GET /offerings/{key}/session/{id}", serde_json::Value::Null),
            )
            .in_session(Some(key.clone()), Some(sid.0.clone()))
            .decided(kind, reason),
        );
    }
    match opened {
        Ok(_) => {}
        Err(CatalogGameError::Host(HostError::UnknownOffering(_))) => {
            // 404, not 200: the page already SAYS the offering does not exist, and the status line
            // is the same statement made to everything that is not a person. A 200 here tells every
            // crawler, uptime monitor and link unfurler that a typo'd offering key is a healthy
            // page — the machine-readable answer contradicting the human-readable one.
            //
            // This is not a new convention, it is the MISSING half of one: the signed seam already
            // answers the same condition with a 404 (`tests/act_signed.rs`,
            // `an_unknown_offering_is_404`), and the sibling arms below already carry honest codes
            // (429/409). The two HTML arms were the outliers.
            return (StatusCode::NOT_FOUND, Html(catalog_missing_offering(&key))).into_response();
        }
        Err(CatalogGameError::Host(
            e @ (HostError::Policy(_) | HostError::ResumeFailed { .. }),
        )) => {
            return refused_open_response(&sid, &e);
        }
        Err(error) => {
            return (StatusCode::CONFLICT, error.to_string()).into_response();
        }
    }
    // A GET is normally a full navigation (full page); an `X-Fragment: 1` GET (e.g. a script
    // refresh) returns just the swappable surface — additive, and the same one render path.
    Html(render_offering_response(
        &state,
        &key,
        &sid,
        None,
        &viewer,
        wants_fragment(&headers),
    ))
    .into_response()
}

/// `GET /offerings/{key}/session/{id}/events` — **the realtime surface stream.**
///
/// This is what a simultaneous-move game was missing: automatafl's waiting seat had no way to learn
/// that the opponent had sealed, opened, or resolved except by hammering reload. The stream holds
/// one `EventSource` open per viewer and pushes THAT VIEWER's re-rendered surface fragment whenever
/// the rendered bytes change (server-side change detection — an idle table pushes nothing).
///
/// It is the SAME per-viewer render the page is served with, so the fog is identical: a spectator's
/// stream carries a spectator's fragment and never a sealed move. Degradation is total: a client
/// without `EventSource`, or with JS off, simply never opens it and the server-form path is
/// untouched.
async fn get_offering_events(
    State(state): State<Arc<CatalogState>>,
    Path((key, id)): Path<(String, String)>,
    headers: HeaderMap,
    Query(query): Query<WebQuery>,
) -> Response {
    let sid = SessionId::new(id);
    let (asserted_user, established) = web_user_established(&headers, &query);
    let (_, viewer) = catalog_route_viewer(&key, &asserted_user, established);
    // Never MINT a world from a stream subscription — the stream observes a table, it does not open
    // one. An unopened session simply renders nothing and the stream stays quiet until it exists.
    table_door::surface_stream(state, key, sid, viewer).into_response()
}

/// The `{turn, arg}` POST body of `POST /offerings/{key}/session/{id}/act`.
#[derive(Debug, Clone, Deserialize)]
pub struct OfferingActForm {
    /// The affordance verb (the offering's turn — `"choose"`, `"propose"`, `"approve"`, `"bid"`, …).
    pub turn: String,
    /// The affordance argument (a choice/proposal index, or a value-taking turn's value).
    #[serde(default)]
    pub arg: i64,
    /// **The free text the user typed**, for an affordance that DECLARED it wants one
    /// (`MenuItem::wants_text` → a real `<input name="text">` in [`catalog_form`]). It becomes the
    /// pressed [`Action`]'s [`Action::text`] payload and nothing else — the string a Hermes PROMPT
    /// classifies, the prose a document INSERT commits, the name `register` claims.
    ///
    /// `None` (and an all-whitespace value) is the text-free press every fixed-index affordance
    /// already is: the payload stays `None` and the executor sees exactly what it saw before, so
    /// this field is additive and invisible to the other 20 offerings. It is deliberately NOT
    /// defaulted to the label — a label is a DISPLAY string synthesized from the verb, and riding
    /// content on it is the bodge that once let a bare press register the literal name "register".
    #[serde(default)]
    pub text: Option<String>,
    #[serde(default)]
    pub game_host_incarnation: Option<String>,
    #[serde(default)]
    pub game_session_generation: Option<u64>,
    #[serde(default)]
    pub game_expected_pre_head: Option<String>,
    #[serde(default)]
    pub game_form_token: Option<String>,
}

#[derive(Clone, Debug)]
struct GameFormAuthority {
    session: GameSessionRef,
    expected_pre_head: Vec<u8>,
    token: [u8; 32],
}

impl GameFormAuthority {
    fn hidden_html(&self) -> String {
        let GameSessionBinding::Bound {
            host_incarnation,
            session_generation,
        } = self.session.binding()
        else {
            return String::new();
        };
        format!(
            "<input type=\"hidden\" name=\"game_host_incarnation\" value=\"{}\">\
             <input type=\"hidden\" name=\"game_session_generation\" value=\"{}\">\
             <input type=\"hidden\" name=\"game_expected_pre_head\" value=\"{}\">\
             <input type=\"hidden\" name=\"game_form_token\" value=\"{}\">",
            hex_bytes(host_incarnation.as_bytes()),
            session_generation,
            hex_bytes(&self.expected_pre_head),
            hex_bytes(&self.token),
        )
    }
}

/// The result of collecting + resolving a catalog POST.
enum CatalogAct {
    /// The affordance was offered and resolved on the substrate (a real landed receipt / refusal).
    /// `did` is the LABEL of the affordance that was pressed, read off the surface the act was
    /// collected against — see [`pressed_label`].
    Advanced {
        outcome: Outcome,
        did: Option<String>,
    },
    /// A game turn crossed the authority-bound common spine and was reduced
    /// to the viewer-blind publication grammar before leaving the host thread.
    AdvancedGame {
        outcome: Outcome,
        publication: Option<PublicGameReceipt>,
        did: Option<String>,
    },
    /// The executor committed, but the post-commit viewer-blind projection
    /// failed. This must never be reported as a refusal: retrying could land a
    /// second move.
    CommittedButPublicationFailed { outcome: Outcome, error: String },
    /// The turn is not on the current surface — an honest frontend-level refusal, before the substrate.
    NotOffered,
    /// The offering or session is absent (a routing miss).
    Missing,
    /// The common game spine refused an internally inconsistent/stale route.
    GameRouteRefused(String),
}

/// **The label of the affordance that was pressed** — `(turn, arg)` matched against the surface the
/// act was collected from, exact pair first and the turn alone as a fallback (a `CoordGrid` cell or
/// an `Input` fires a turn whose `arg` is the user's, so no row carries that exact pair).
///
/// ⚑ WHY THIS EXISTS. The success banner used to read `Turn committed — Recorded (asserted) ·
/// executor receipt 02f5138e…`: a 64-character hex and no item, no price, no action. A first-time
/// reader's verdict was *"the confirmation confirms that SOMETHING happened, not WHAT"*
/// (`docs/reference/UX-QA-SWEEP-2026-07-26.md`, finding 3). The label is the only string in the whole
/// path that knows what the player meant — the executor is handed a typed `{turn, arg}` and the
/// receipt is a hash — so it has to be carried from the surface to the banner deliberately.
///
/// It is presentation, never authority: the label is read off the same projection the press was
/// VALIDATED against, and the executor still resolves the typed pair alone. An empty label yields
/// `None` and the banner falls back to naming the raw turn.
/// **The banner's opening clause: WHAT the player did.** `"Sealed a move to (3,3) · "` from the
/// pressed affordance's own label, or `"`select` · "` from the raw turn name when the surface
/// offered no label at all. Always ends in a separator so the caller can concatenate the receipt
/// card straight after it.
///
/// The label is trimmed and clipped: an affordance label is button text, but a `CoordGrid` glyph or
/// a generated row can be long, and a banner is one line.
pub(crate) fn named_act(did: Option<&str>, turn: &str) -> String {
    let name = match did.map(str::trim).filter(|l| !l.is_empty()) {
        Some(label) if label.chars().count() <= 90 => label.to_string(),
        Some(label) => {
            let head: String = label.chars().take(87).collect();
            format!("{head}…")
        }
        // No label to be had (a bare `CoordGrid` cell, a crafted POST the surface still offers). The
        // turn NAME is not prose, but it is the true answer to "what did I just fire" and beats a
        // bare hash.
        None if !turn.trim().is_empty() => format!("`{}`", turn.trim()),
        None => return String::new(),
    };
    format!("{name} · ")
}

/// **The typed press, payload included** — `{turn, arg}` plus the free text the form carried, for an
/// affordance that declared it wants one ([`OfferingActForm::text`]).
///
/// The label + `enabled` remain decoration (the executor resolves the typed action alone). The one
/// thing that is NOT decoration is the string: a text-shaped move — a Hermes PROMPT, a document
/// INSERT, a name to `register` — is refused outright without it, which is exactly why three
/// offerings were unplayable on the web before this carrier existed.
///
/// An absent or all-whitespace field yields the plain text-free [`Action`] every fixed-index press
/// already was, so nothing changes for the affordances that never asked for a string. Whitespace is
/// treated as absent deliberately: the executors test `text` with `!t.trim().is_empty()`, so a
/// blank box must reach them as `None` and earn the same legible refusal a bare press does, never a
/// committed turn carrying a space.
pub(crate) fn pressed_action(turn: &str, arg: i64, text: Option<&str>) -> Action {
    let action = Action::new(turn.to_string(), turn.to_string(), arg, true);
    match text.map(str::trim).filter(|t| !t.is_empty()) {
        Some(typed) => action.with_text(typed),
        None => action,
    }
}

fn pressed_label<'a>(
    offered: impl Iterator<Item = &'a Action>,
    turn: &str,
    arg: i64,
) -> Option<String> {
    let mut by_turn: Option<&Action> = None;
    for action in offered {
        if action.turn != turn {
            continue;
        }
        if action.arg == arg {
            return Some(action.label.clone()).filter(|l| !l.trim().is_empty());
        }
        if by_turn.is_none() {
            by_turn = Some(action);
        }
    }
    by_turn
        .map(|a| a.label.clone())
        .filter(|l| !l.trim().is_empty())
}

/// `POST /offerings/{key}/session/{id}/act` — the real-turn seam for ANY offering. Reads the web
/// identity, PRESENTS the current surface (the offering's live [`Offering::actions`]), COLLECTS the
/// posted `{turn, arg}` against it (a turn the surface does not offer is refused before the
/// substrate), and [`OfferingHost::advance`]s ONE real turn. A legal move lands a real receipt; an
/// illegal / crafted one is a real executor [`Outcome::Refused`] (anti-ghost). Re-renders.
async fn post_offering_act(
    State(state): State<Arc<CatalogState>>,
    Path((key, id)): Path<(String, String)>,
    headers: HeaderMap,
    Query(query): Query<WebQuery>,
    Form(form): Form<OfferingActForm>,
) -> Response {
    let sid = SessionId::new(id);
    let (asserted_user, established) = web_user_established(&headers, &query);
    // Route + attribute an UNestablished RPG touch through the shared anonymous world so a raw
    // `?user=` flood cannot mint a private per-identity world per value (the unbounded-host DoS).
    let (user, actor) = catalog_route_viewer(&key, &asserted_user, established);
    // THE TABLE CLOCK, first: a returning player's own click is what resolves a table their
    // opponent walked away from, so reap BEFORE the gate — the refusal below then carries the
    // resolution instead of letting them press into a dead board. A no-op for every key/id that is
    // not a minted table, and for a table still inside its deadline.
    table_seats::touch(&state, &sid.0);
    // THE SEAT LOCK. On a table minted at `/automatafl` or `/tug` the two seats are bound to two
    // unguessable server-derived labels, so a stranger who learns the id can neither race in and
    // claim a seat nor reach the per-viewer hidden-state disclosure (the sealed move, the hand) by
    // asserting the other seat's label. It also refuses every act on a table this lobby has
    // already recorded as forfeited. Every other key/id is untouched (`Ok(())`), and this refuses
    // BEFORE anything opens or advances — nothing commits.
    if let Err(why) = table_seats::enforce(&key, &sid.0, &user) {
        audit::log()
            .emit(act_audit_event(&user, &actor, &key, &sid, &form).decided("gated", why.clone()));
        return Html(render_offering_response(
            &state,
            &key,
            &sid,
            Some(&format!("Refused: {why}.")),
            &actor,
            wants_fragment(&headers),
        ))
        .into_response();
    }
    let presented_game = if game_kind(&key).is_some() {
        match state.presented_game_action(&key, &sid, &form) {
            Ok(reference) => Some(reference),
            Err(error) => return (StatusCode::CONFLICT, error.to_string()).into_response(),
        }
    } else {
        None
    };
    if presented_game.is_none() {
        let opened = state.ensure_open_and_bind(
            &key,
            &sid,
            &actor,
            Some(Attribution::Asserted {
                label: actor.0.clone(),
            }),
        );
        match opened {
            Ok(_) => {}
            Err(CatalogGameError::Host(HostError::UnknownOffering(_))) => {
                audit::log().emit(
                    act_audit_event(&user, &actor, &key, &sid, &form)
                        .decided("refused", "unknown_offering"),
                );
                // 404 for the same reason the GET arm above does: the audit log already records
                // this as `refused`, and the status code should not be the one place that says
                // otherwise.
                return (StatusCode::NOT_FOUND, Html(catalog_missing_offering(&key)))
                    .into_response();
            }
            Err(CatalogGameError::Host(
                e @ (HostError::Policy(_) | HostError::ResumeFailed { .. }),
            )) => {
                let (kind, reason) = open_audit_parts(&e);
                audit::log()
                    .emit(act_audit_event(&user, &actor, &key, &sid, &form).decided(kind, reason));
                return refused_open_response(&sid, &e);
            }
            Err(error) => {
                return (StatusCode::CONFLICT, error.to_string()).into_response();
            }
        }
    }
    metrics::set_sessions_open(state.shared_session_count() as f64);

    // PRESENT the current surface + COLLECT the posted affordance + ADVANCE, atomically on the
    // host thread: the turn must be among the offering's current affordances (offered), then the
    // executor is the sole referee of the {turn, arg} on the substrate.
    let acted = if let Some(reference) = presented_game {
        let presented_session = reference.session.clone();
        let turn = form.turn.clone();
        let arg = form.arg;
        // Carried on the spined path too, not only the plain one: no shipped game declares a text
        // want today, but a carrier that exists on one of two act routes is the drop this whole
        // change is closing. A `None` here builds exactly the action this arm built before.
        let typed = form.text.clone();
        let inner_actor = actor.clone();
        let opener = Attribution::Asserted {
            label: actor.0.clone(),
        };
        match state.run_presented_bound_game(
            presented_session,
            &actor,
            opener,
            move |host, incarnation, generation, session| {
                let view = match inspect_bound_game_session(
                    host,
                    incarnation,
                    generation,
                    session.clone(),
                    &GameAudience::AssertedPrivate(inner_actor.clone()),
                ) {
                    Ok(view) => view,
                    Err(error) => return CatalogAct::GameRouteRefused(error.to_string()),
                };
                if !view.affordances.iter().any(|affordance| {
                    matches!(
                        affordance,
                        GameAffordance::Turn { action, .. } if action.turn == turn
                    )
                }) {
                    return CatalogAct::NotOffered;
                }
                // WHAT THE PLAYER JUST DID, in the words they read on the button — captured HERE,
                // against the very surface the act was collected from, because it is the only place
                // the label still exists (the executor sees a typed `{turn, arg}` and nothing else).
                let did = pressed_label(
                    view.affordances
                        .iter()
                        .filter_map(|affordance| match affordance {
                            GameAffordance::Turn { action, .. } => Some(action),
                            _ => None,
                        }),
                    &turn,
                    arg,
                );
                let action = pressed_action(&turn, arg, typed.as_deref());
                match execute_bound_asserted_game_turn(
                    host,
                    incarnation,
                    generation,
                    &session,
                    reference,
                    action,
                    inner_actor,
                ) {
                    Ok(execution) => {
                        let publication = match &execution.result {
                            GameResult::Landed(receipt) => {
                                match project_public_game_receipt(receipt) {
                                    Ok(publication) => Some(publication),
                                    Err(error) => {
                                        return CatalogAct::CommittedButPublicationFailed {
                                            outcome: execution.outcome,
                                            error: error.to_string(),
                                        };
                                    }
                                }
                            }
                            GameResult::Refused { .. } => None,
                        };
                        CatalogAct::AdvancedGame {
                            outcome: execution.outcome,
                            publication,
                            did,
                        }
                    }
                    Err(error) => CatalogAct::GameRouteRefused(error.to_string()),
                }
            },
        ) {
            Ok(acted) => acted,
            Err(error) => CatalogAct::GameRouteRefused(error.to_string()),
        }
    } else {
        let k = key.clone();
        let sid = sid.clone();
        let turn = form.turn.clone();
        let arg = form.arg;
        // The typed string an affordance that DECLARED a text want carried (see
        // [`OfferingActForm::text`]) — `None` for every fixed-index press.
        let typed = form.text.clone();
        let inner_actor = actor.clone();
        // RPG keys resolve in the acting user's own world; the shared tables on the ONE host.
        state.run_offering(&key, &actor, move |h| {
            // Validate against the affordances THIS actor sees (`actions_for`) — a viewer is offered
            // only what their caps allow; the executor remains the sole referee of the typed turn.
            let Some(actions) = h.actions_for(&k, &sid, &inner_actor) else {
                return CatalogAct::Missing;
            };
            if !actions.iter().any(|a| a.turn == turn) {
                return CatalogAct::NotOffered;
            }
            // WHAT THE PLAYER JUST DID — the pressed row's own label, off the same `actions_for`
            // projection the press was validated against. It never reaches the executor (which
            // resolves the TYPED `{turn, arg}` and nothing else); it exists so the confirmation can
            // say WHAT happened and not only that something did.
            let did = pressed_label(actions.iter(), &turn, arg);
            // The label + enabled are decoration; the executor resolves the TYPED (turn, arg) — and
            // now the TEXT the affordance declared it wanted, which is not decoration at all.
            let action = pressed_action(&turn, arg, typed.as_deref());
            match h.advance(&k, &sid, action, inner_actor) {
                Some(o) => CatalogAct::Advanced { outcome: o, did },
                None => CatalogAct::Missing,
            }
        })
    };

    // AUDIT EMIT: the collected+resolved act — the `Landed` arm carries the receipt-chain
    // join (`hex(TurnReceipt.turn_hash)`); an executor refusal is `routed` (the substrate was
    // reached — the refusal is ITS decision), a not-offered/missing is the frontend's.
    audit::log().emit(match &acted {
        CatalogAct::Advanced {
            outcome: Outcome::Landed { receipt, ended },
            ..
        } => act_audit_event(&user, &actor, &key, &sid, &form).with_outcome(
            audit::AuditOutcome::Landed {
                turn_hash: audit::hex32(&receipt.turn_hash),
                ended: *ended,
            },
        ),
        CatalogAct::Advanced {
            outcome: Outcome::Refused(why),
            ..
        } => act_audit_event(&user, &actor, &key, &sid, &form)
            .with_outcome(audit::AuditOutcome::Refused { why: why.clone() }),
        CatalogAct::AdvancedGame {
            outcome: Outcome::Landed { receipt, ended },
            ..
        } => act_audit_event(&user, &actor, &key, &sid, &form).with_outcome(
            audit::AuditOutcome::Landed {
                turn_hash: audit::hex32(&receipt.turn_hash),
                ended: *ended,
            },
        ),
        CatalogAct::AdvancedGame {
            outcome: Outcome::Refused(why),
            ..
        } => act_audit_event(&user, &actor, &key, &sid, &form)
            .with_outcome(audit::AuditOutcome::Refused { why: why.clone() }),
        CatalogAct::CommittedButPublicationFailed { outcome, error } => {
            let audit_outcome = match outcome {
                Outcome::Landed { receipt, ended } => audit::AuditOutcome::Landed {
                    turn_hash: audit::hex32(&receipt.turn_hash),
                    ended: *ended,
                },
                Outcome::Refused(why) => audit::AuditOutcome::Refused { why: why.clone() },
            };
            act_audit_event(&user, &actor, &key, &sid, &form)
                .decided("committed", format!("publication_failed:{error}"))
                .with_outcome(audit_outcome)
        }
        CatalogAct::NotOffered => {
            act_audit_event(&user, &actor, &key, &sid, &form).decided("refused", "not_offered")
        }
        CatalogAct::Missing => {
            act_audit_event(&user, &actor, &key, &sid, &form).decided("refused", "missing_session")
        }
        CatalogAct::GameRouteRefused(reason) => {
            act_audit_event(&user, &actor, &key, &sid, &form).decided("gated", reason.clone())
        }
    });

    // THE CLOCK, second half: a LANDED turn is what restarts a seat-locked table's deadline. A
    // refused press moves the game nowhere, so it must not buy the presser another window — the
    // clock measures PROGRESS, not clicking. A no-op on every id that is not a minted table.
    if matches!(
        &acted,
        CatalogAct::Advanced {
            outcome: Outcome::Landed { .. },
            ..
        } | CatalogAct::AdvancedGame {
            outcome: Outcome::Landed { .. },
            ..
        } | CatalogAct::CommittedButPublicationFailed {
            outcome: Outcome::Landed { .. },
            ..
        }
    ) {
        table_seats::record_landed_act(&key, &sid.0, &user);
    }

    let notice = match acted {
        CatalogAct::Advanced {
            outcome: Outcome::Landed { receipt, ended },
            did,
        } => {
            format!(
                "Turn committed — {}{}",
                named_act(did.as_deref(), &form.turn),
                PlayerTurnReceipt::from_landed(&receipt, ended)
                    .compact_text(PlayerReplaySurface::Web)
            )
        }
        CatalogAct::Advanced {
            outcome: Outcome::Refused(why),
            did,
        } => {
            metrics::inc_turn_refused();
            // A REFUSAL names the action too. "Refused: not your turn" left a reader guessing which
            // of four buttons they had just pressed.
            format!(
                "Refused: {}{why} (nothing committed — anti-ghost).",
                named_act(did.as_deref(), &form.turn)
            )
        }
        CatalogAct::AdvancedGame {
            outcome: Outcome::Landed { .. },
            publication: Some(publication),
            did,
        } => format!(
            "Turn committed — {}{}",
            named_act(did.as_deref(), &form.turn),
            game_session::public_receipt_text(&publication, PlayerReplaySurface::Web)
        ),
        CatalogAct::AdvancedGame {
            outcome: Outcome::Landed { .. },
            publication: None,
            ..
        } => "Refused: a landed game turn lacked its public receipt projection.".to_string(),
        CatalogAct::AdvancedGame {
            outcome: Outcome::Refused(why),
            did,
            ..
        } => {
            metrics::inc_turn_refused();
            format!(
                "Refused: {}{why} (nothing committed — anti-ghost).",
                named_act(did.as_deref(), &form.turn)
            )
        }
        CatalogAct::CommittedButPublicationFailed { error, .. } => format!(
            "Turn committed, but its public receipt could not be rendered ({error}). Do not retry; refresh to inspect the committed state."
        ),
        CatalogAct::NotOffered => {
            "Refused: that affordance is not on the current surface.".to_string()
        }
        CatalogAct::Missing => "Refused: no such offering session.".to_string(),
        CatalogAct::GameRouteRefused(reason) => {
            format!("Refused: game-session route was stale or invalid: {reason}")
        }
    };

    // Re-render AS the acting user — so the player who just claimed/played a seat sees their own
    // hidden hand (and their own cap-gated affordances), not the viewer-blind public fog. When the
    // POST came from the progressive-enhancement script (`X-Fragment: 1`), return JUST the
    // re-rendered surface fragment for an in-place swap; a plain no-JS form POST gets the full page.
    Html(render_offering_response(
        &state,
        &key,
        &sid,
        Some(&notice),
        &actor,
        wants_fragment(&headers),
    ))
    .into_response()
}

/// **The honest lifecycle-refusal response** — a policy gate ([`HostError::Policy`]) answers
/// `429 Too Many Requests` naming the tripped limit (with a `Retry-After` when the gate is the
/// open rate), and a persisted log that refused to reopen ([`HostError::ResumeFailed`]) answers
/// `409 Conflict` (the durable record is authoritative; a fresh genesis will not shadow it).
/// Never a 500 — a refused open is the policy WORKING, not a server fault.
fn refused_open_response(id: &SessionId, err: &HostError) -> Response {
    // Count the refusal at its one funnel point — a labelled policy refusal (WHICH limit
    // tripped) or a lazy-resume failure (a persisted log that refused to reopen, the 409).
    match err {
        HostError::Policy(PolicyRefusal::ActorQuota { .. }) => metrics::inc_open_refused("quota"),
        HostError::Policy(PolicyRefusal::OpenRate { .. }) => metrics::inc_open_refused("rate"),
        HostError::Policy(PolicyRefusal::Capacity { .. }) => metrics::inc_open_refused("capacity"),
        HostError::ResumeFailed { .. } => metrics::inc_resume_failure(),
        _ => {}
    }
    let (status, retry_after) = match err {
        HostError::Policy(PolicyRefusal::OpenRate { retry_after_secs }) => {
            (StatusCode::TOO_MANY_REQUESTS, Some(*retry_after_secs))
        }
        HostError::Policy(_) => (StatusCode::TOO_MANY_REQUESTS, None),
        _ => (StatusCode::CONFLICT, None),
    };
    let body = format!(
        "<main class=\"session\"><div class=\"notice refused\" role=\"status\">Refused: {err}. \
         Nothing was opened.</div>\
         <p class=\"prose\"><a class=\"backlink\" href=\"/offerings\">← Browse all games</a></p>\
         </main>",
        err = esc(&err.to_string()),
    );
    let page = document(
        &format!("{PRODUCT_NAME} — session {} refused", id.0),
        "",
        &body,
    );
    let mut resp = (status, Html(page)).into_response();
    if let Some(secs) = retry_after {
        if let Ok(v) = axum::http::HeaderValue::from_str(&secs.to_string()) {
            resp.headers_mut().insert(header::RETRY_AFTER, v);
        }
    }
    resp
}

/// The unsigned `/act` twin's audit-envelope skeleton (asserted-cookie attribution; the
/// caller stamps decision + outcome). The `{turn, arg}` IS the trail — user content, §8.
///
/// ⚑ **And the typed TEXT is part of that trail, by the same rule.** `docs/BOT-AUDIT-LOGGING-DESIGN.md`
/// §8 names it explicitly in the FINE-to-log list ("`{turn, arg}`, user free text"), and the
/// alternative is worse than verbose: a landed document `insert` or a metered Hermes `prompt` whose
/// CONTENT the trail cannot show is a receipt for an act nobody can reconstruct. Omitted when absent,
/// so every fixed-index press emits the byte-identical envelope it always did.
fn act_audit_event(
    user: &str,
    actor: &DreggIdentity,
    key: &str,
    sid: &SessionId,
    form: &OfferingActForm,
) -> audit::AuditEvent {
    let mut input = serde_json::json!({ "turn": form.turn, "arg": form.arg });
    if let Some(typed) = form
        .text
        .as_deref()
        .map(str::trim)
        .filter(|t| !t.is_empty())
    {
        input["text"] = serde_json::Value::String(typed.to_string());
    }
    audit::AuditEvent::new(
        "web",
        audit::Actor::asserted(user).with_identity(actor.0.clone()),
        audit::Surface::Http,
        audit::Input::new("POST /offerings/{key}/session/{id}/act", input),
    )
    .in_session(Some(key.to_string()), Some(sid.0.clone()))
}

/// The audit taxonomy for a refused/errored `ensure_open_as` — `(decision.kind, reason)`
/// (docs/BOT-AUDIT-LOGGING-DESIGN.md §3: a policy gate is `gated`, a routing miss `refused`).
pub(crate) fn open_audit_parts(e: &HostError) -> (&'static str, String) {
    match e {
        HostError::UnknownOffering(_) => ("refused", "unknown_offering".to_string()),
        HostError::UnknownSession { .. } => ("refused", "unknown_session".to_string()),
        HostError::Policy(p) => (
            "gated",
            match p {
                PolicyRefusal::ActorQuota { .. } => "policy:actor_quota".to_string(),
                PolicyRefusal::OpenRate { .. } => "policy:open_rate".to_string(),
                PolicyRefusal::Capacity { .. } => "policy:capacity".to_string(),
            },
        ),
        HostError::ResumeFailed { .. } => ("gated", "resume_failed".to_string()),
        HostError::Signature(e) => ("gated", format!("sig:{e}")),
        HostError::Deploy(_) => ("error", "deploy_failed".to_string()),
    }
}

/// `GET /offerings/{key}/session/{id}/verify` — re-verify the committed chain by the offering's own
/// proof, exposed over HTTP as JSON.
async fn get_offering_verify(
    State(state): State<Arc<CatalogState>>,
    Path((key, id)): Path<(String, String)>,
    headers: HeaderMap,
    Query(query): Query<WebQuery>,
) -> impl IntoResponse {
    let sid = SessionId::new(id);
    // The viewer's derived identity — for an RPG key the chain being re-verified is THIS viewer's
    // own world (a per-identity session), so verify must route to the same world its turns landed
    // in. A shared table ignores the viewer (one chain for everyone).
    // Re-verify against the SAME world the turns landed in. `run_offering` → `host_mut` also
    // materializes on touch, so an UNestablished RPG `?user=` collapses to the shared anonymous
    // world here too — verify is never a materialization vector for a raw `?user=` flood.
    let (asserted_user, established) = web_user_established(&headers, &query);
    let (_route_user, viewer) = catalog_route_viewer(&key, &asserted_user, established);
    let verify_event = || {
        audit::AuditEvent::new(
            "web",
            audit::Actor::unattributed(),
            audit::Surface::Http,
            audit::Input::new(
                "GET /offerings/{key}/session/{id}/verify",
                serde_json::Value::Null,
            ),
        )
        .in_session(Some(key.clone()), Some(sid.0.clone()))
    };
    // ⚑ LIVE FIRST, THEN THE ARCHIVE. A finished match is not a live session any more, and this
    // route used to answer "no such offering session" for one — which made the product's own claim
    // ("a finished game can be replayed by anyone") false for automatafl and tug the moment the
    // match ended. `replay_archived` re-drives the retained move-log through the real executor and
    // hands back the offering's own report, so the SAME url keeps meaning the same thing after the
    // last move: not a stored verdict, a re-execution.
    let outcome = {
        let k = key.clone();
        let sid = sid.clone();
        state.run_offering(&key, &viewer, move |h| match h.verify(&k, &sid) {
            Some(report) => VerifyOutcome::Live(report),
            None => match h.replay_archived(&k, &sid) {
                Some(Ok(report)) => VerifyOutcome::Finished(report),
                Some(Err(error)) => VerifyOutcome::ArchiveRefused(error.to_string()),
                None => VerifyOutcome::Missing,
            },
        })
    };
    match outcome {
        VerifyOutcome::Live(report) | VerifyOutcome::Finished(report) => {
            // AUDIT EMIT: a re-verification ran — the report verdict is the outcome.
            audit::log().emit(verify_event().with_outcome(audit::AuditOutcome::Verified {
                verified: report.verified,
                turns: report.turns as u64,
            }));
            Json(serde_json::json!({
                "verified": report.verified,
                "turns": report.turns,
                "detail": report.detail,
            }))
        }
        // A retained log that does NOT re-drive is a real answer, not a missing session: the archive
        // is a writable file, and a tampered one must read as refused rather than as absent.
        VerifyOutcome::ArchiveRefused(reason) => {
            audit::log().emit(verify_event().with_outcome(audit::AuditOutcome::Verified {
                verified: false,
                turns: 0,
            }));
            Json(serde_json::json!({
                "verified": false,
                "turns": 0,
                "detail": format!(
                    "this finished match's recorded moves do NOT re-execute: {reason}"
                ),
            }))
        }
        VerifyOutcome::Missing => {
            audit::log().emit(verify_event().decided("refused", "missing_session"));
            Json(serde_json::json!({
                "verified": false,
                "turns": 0,
                "detail": "no such offering session",
            }))
        }
    }
}

/// What a `/verify` read found: a live chain, a FINISHED match re-executed from its archived
/// move-log, an archive that refused to re-drive, or nothing at all. Flat and `Send` so it crosses
/// the host-thread boundary as a plain value.
enum VerifyOutcome {
    Live(VerifyReport),
    Finished(VerifyReport),
    ArchiveRefused(String),
    Missing,
}

/// **The live-region HTML for an offering session** — the notice banner + the surface's POST forms
/// + the re-verified receipt line, and NOTHING else. This is THE fragment a turn swaps: the
/// progressive-enhancement script `fetch`es it (via `X-Fragment: 1`) and drops it straight into
/// `#live-surface`, and the full page ([`offering_page`]) embeds this SAME string verbatim inside
/// that region — so no-JS (full page) and JS (swapped fragment) render an identical surface (ONE
/// render path). `None` if the session/offering is absent.
fn offering_surface_fragment(
    state: &CatalogState,
    key: &str,
    id: &SessionId,
    notice: Option<&str>,
    viewer: &DreggIdentity,
) -> Option<String> {
    let rendered = if game_kind(key).is_some() {
        let v = viewer.clone();
        state
            .run_current_bound_game(
                key,
                id,
                viewer,
                move |host, incarnation, generation, session| {
                    let view = inspect_bound_game_session(
                        host,
                        incarnation,
                        generation,
                        session,
                        &GameAudience::AssertedPrivate(v),
                    )
                    .ok()?;
                    #[cfg(feature = "hosted-binary-operations")]
                    {
                        let operations = view
                            .affordances
                            .iter()
                            .filter_map(|affordance| match affordance {
                                GameAffordance::Operation { descriptor, .. } => {
                                    Some(descriptor.clone())
                                }
                                GameAffordance::Turn { .. } => None,
                            })
                            .collect();
                        Some((
                            view.projection.surface,
                            view.verification,
                            operations,
                            Some((view.session, view.surface_commitment)),
                        ))
                    }
                    #[cfg(not(feature = "hosted-binary-operations"))]
                    {
                        Some((
                            view.projection.surface,
                            view.verification,
                            Some((view.session, view.surface_commitment)),
                        ))
                    }
                },
            )
            .ok()??
    } else {
        let k = key.to_string();
        let id = id.clone();
        let v = viewer.clone();
        // Render AS the viewer — the per-player projection (own hidden hand revealed, others fog),
        // NOT the viewer-blind `render`. For an RPG key this ALSO selects the viewer's own world
        // (their inventory), so the render reads the ledger their turns landed in — the whole
        // per-viewer isolation reaching the web surface.
        state.run_offering(key, viewer, move |h| {
            let core = h.render_for(&k, &id, &v).zip(h.verify(&k, &id));
            #[cfg(feature = "hosted-binary-operations")]
            {
                core.map(|(surface, verify)| {
                    let operations = h.binary_operations(&k, &id).unwrap_or_default();
                    (surface, verify, operations, None)
                })
            }
            #[cfg(not(feature = "hosted-binary-operations"))]
            {
                core.map(|(surface, verify)| (surface, verify, None))
            }
        })?
    };
    #[cfg(feature = "hosted-binary-operations")]
    let (surface, verify, operations, game_coordinates) = rendered;
    #[cfg(not(feature = "hosted-binary-operations"))]
    let (surface, verify, game_coordinates) = rendered;
    let authority = match game_coordinates {
        Some((session, head)) => Some(state.game_form_authority(session, head).ok()?),
        None => None,
    };
    let mut forms = render_catalog_forms(surface.view(), key, &id.0);
    if let Some(authority) = &authority {
        let turn_input = "<input type=\"hidden\" name=\"turn\"";
        let replacement = format!("{}{turn_input}", authority.hidden_html());
        forms = forms.replace(turn_input, &replacement);
    }
    #[cfg(feature = "hosted-binary-operations")]
    let operation_forms = render_operation_uploaders(&operations, key, &id.0);
    #[cfg(not(feature = "hosted-binary-operations"))]
    let operation_forms = String::new();
    // ⚑ **THIS VIEWER'S OWN FIRST LANDED MOVE**, counted off `SessionMoveLog::moves` — the only
    // signal that means the same thing everywhere. Two wrong answers were tried and both are gates
    // that could not fire:
    //
    // * `verify.turns` — the dungeon's is `1 + steps` and the tug's is `1 + round_actions + scored`,
    //   so genesis is turn 1 and a first move already reads 2; automatafl's is `session.turns`, a
    //   count of RESOLVED ROUNDS, still 0 after a seat has selected and sealed. No single value of it
    //   means "one move in".
    // * the log's LENGTH — `/offerings/descent/session/descent-web` is a SHARED host session (descent
    //   is not an `is_rpg_key`), so its log is global: length 1 happens once for the whole deployment,
    //   to whoever moved first, and never again for anybody.
    //
    // `LoggedMove::actor` fixes both: exactly one landed move attributed to THIS viewer is this
    // viewer's first move in this session, on a shared table or a private world alike.
    //
    // ⚑ AND NEVER ON A SEAT-LOCKED TABLE. Claiming a phrase REWRITES `dregg_user`
    // (`seed_identity::post_confirm` sets the acting cookie to the claim label) — and on a minted
    // automatafl/tug table `dregg_user` IS the seat, so accepting this offer mid-match would hand the
    // seat away. An offer that costs the reader the thing it claims to protect must not be made.
    //
    // Read ONLY when a turn actually landed, so a plain GET and the 400ms realtime pulse never pay
    // the host round trip. `run_offering` routes an RPG key to that viewer's own world and everything
    // else to the shared host, so this reads the same log the turn was written into.
    let seat_locked =
        table_seats::lock_for_key(key).is_some_and(|lock| lock.is_locked_table(&id.0));
    let keep = if !seat_locked && notice.is_some_and(|n| n.starts_with("Turn committed")) {
        let k = key.to_string();
        let sid = id.clone();
        let me = viewer.clone();
        let mine = state.run_offering(key, viewer, move |h| {
            h.move_log(&k, &sid)
                .map(|log| log.moves.iter().filter(|m| m.actor == me).count())
                .unwrap_or_default()
        });
        keep_this_run_offer(mine)
    } else {
        String::new()
    };
    Some(format!(
        "{notice}{keep}{forms}{operation_forms}{receipt}",
        notice = notice_html(notice),
        keep = keep,
        forms = forms,
        operation_forms = operation_forms,
        receipt = receipt_html(
            &verify,
            "chain re-verified by replay",
            &format!("/offerings/{}/session/{}/verify", esc(key), esc(&id.0)),
        ),
    ))
}

/// ⚑ **THE ONE MOMENT IDENTITY IS WORTH INTERRUPTING FOR — the turn right after the first one.**
///
/// `/identity` is not in the top nav and is reachable only from `/you` or from inline prose, which is
/// the right call for a surface a stranger should be able to play without an account: it never
/// interrupts play. But the consequence is that it also never appears at the ONE moment it is worth
/// something — the moment a player first has a run to lose. The default identity is an unsigned
/// `dregg_user` cookie with no password and no recovery ([`web_identity_http`]), so a cleared browser
/// costs them everything they just did, silently, with no warning anywhere on the path they walked.
///
/// So: ONE line, ONCE. `my_landed_moves` is how many landed moves in this session are attributed to
/// THIS viewer, counted by the caller only on a render that follows a landed turn — so this fires on
/// exactly the screen after that viewer's FIRST move and on no screen before or after it. Not a wall,
/// not a modal, not a gate: one sentence and one link, above the board, gone on the next press.
///
/// It is worded to be true whether or not the reader already holds a phrase. This function is not
/// given the claim cookie (`seed_identity::claimed_pubkey` needs `HeaderMap`, which would mean a new
/// argument on [`offering_surface_fragment`], [`render_offering_page`] and the `pub(crate)`
/// [`render_offering_response`] that four transports call), so it must not say anything that only
/// holds for an unclaimed browser: "the only thing holding this name is this browser" is a fact about
/// the cookie either way, and `/identity` shows a browser that already claimed its existing identity
/// rather than nagging it for a second one. Firing once is what keeps that acceptable.
fn keep_this_run_offer(my_landed_moves: usize) -> String {
    if my_landed_moves != 1 {
        return String::new();
    }
    "<p class=\"keep-run\">That is your first move on the board. The only thing holding the name it \
     landed under is this browser — clear it and the run is gone, with no way back. \
     <a href=\"/identity\">Keep it with a 24-word phrase →</a></p>"
        .to_string()
}

/// Render discoverable opaque-proof operations as raw file upload controls on
/// the normal playable page. The browser never decodes the file: it sends the
/// exact bytes and advertised media type to the same generic route used by the
/// Telegram Mini App and Discord Activity wrappers.
#[cfg(feature = "hosted-binary-operations")]
fn render_operation_uploaders(
    operations: &[BinaryOperationDescriptor],
    key: &str,
    id: &str,
) -> String {
    if operations.is_empty() {
        return String::new();
    }
    let mut out = String::from(
        "<section class=\"operation-uploader\"><h2>Proof-bearing operations</h2>\
         <p class=\"prose\">Submit a canonical receipt produced by your private client. \
         Verification happens before the game state changes.</p>",
    );
    for (index, operation) in operations.iter().enumerate() {
        let status_id = format!("operation-status-{index}");
        out.push_str(&format!(
            "<form class=\"binary-operation\" method=\"post\" \
             action=\"/offerings/{key}/session/{id}/operations/{name}\" \
             data-media=\"{media}\" data-session-action=\"private-operation\" \
             data-private-boundary=\"opaque-upload\">\
             <label for=\"operation-file-{index}\">{title}</label>\
             <p class=\"operation-disclosure\">{disclosure} Maximum canonical input: {max} bytes.</p>\
             <input id=\"operation-file-{index}\" type=\"file\" required \
             accept=\"{media}\" aria-describedby=\"{status_id}\">\
             <button type=\"submit\">Verify &amp; apply</button>\
             <span id=\"{status_id}\" role=\"status\" aria-live=\"polite\"></span>\
             </form>",
            key = esc(key),
            id = esc(id),
            name = esc(&operation.name),
            media = esc(&operation.input_media_type),
            title = esc(game_session::public_operation_title(&operation.name)),
            disclosure = esc(&operation.disclosure),
            max = operation.max_input_bytes,
        ));
    }
    out.push_str("</section>");
    out
}

/// The offering title (registered `Name — tagline`), or the key if none is registered.
fn offering_title(state: &CatalogState, key: &str) -> String {
    state
        .host
        .run({
            let key = key.to_string();
            move |h| h.title(&key).map(|t| t.to_string())
        })
        .unwrap_or_else(|| key.to_string())
}

/// Render an offering session as a full HTML page: the page chrome (crumb + head) around the
/// [`offering_surface_fragment`] live region. Fetches the surface + verify report from the host
/// thread. Missing session → [`page_missing`].
fn render_offering_page(
    state: &CatalogState,
    key: &str,
    id: &SessionId,
    notice: Option<&str>,
    viewer: &DreggIdentity,
) -> String {
    let Some(surface) = offering_surface_fragment(state, key, id, notice, viewer) else {
        // ⚑ A NOTICE MUST NOT BE SWALLOWED BY A MISSING SESSION. This branch is now reachable for a
        // FINISHED match — a match's world is RETIRED when it ends (its move-log archived so it stays
        // replayable), so there is no live surface to paint the refusal onto. `page_missing` would
        // drop the refusal and tell the player their table never existed, which is both wrong and
        // the opposite of the thing the archive exists to say.
        return match notice {
            Some(said) => retired_session_page(key, &id.0, said),
            None => page_missing(id),
        };
    };
    let title = offering_title(state, key);
    offering_page(key, &title, id, &surface)
}

/// Render an offering-session response, choosing the surface by the `X-Fragment: 1` request header:
/// when `fragment_only` (a progressive-enhancement `fetch`), return JUST the swappable surface
/// fragment ([`offering_surface_fragment`] — no `<html>`/`<head>`/chrome); otherwise the full page
/// (the no-JS server-form path). Both embed the identical fragment — ONE render path.
fn render_offering_response(
    state: &CatalogState,
    key: &str,
    id: &SessionId,
    notice: Option<&str>,
    viewer: &DreggIdentity,
    fragment_only: bool,
) -> String {
    if fragment_only {
        // The fragment path: the bare live-region HTML (or, if the session vanished, an honest
        // notice fragment — the swap target still gets valid HTML, never a whole error document).
        offering_surface_fragment(state, key, id, notice, viewer)
            .unwrap_or_else(|| notice_html(Some("Refused: no such offering session.")))
    } else {
        render_offering_page(state, key, id, notice, viewer)
    }
}

/// Whether the request asked for JUST the surface fragment (the progressive-enhancement `fetch`
/// sets `X-Fragment: 1`); a plain browser navigation / no-JS POST omits it and gets the full page.
fn wants_fragment(headers: &HeaderMap) -> bool {
    headers.get("x-fragment").is_some_and(|v| !v.is_empty())
}

/// **Render an offering's [`ViewNode`] surface into POST-form controls** — the multi-offering
/// analogue of deos-view's `render_session_forms`, but each affordance POSTs to
/// `/offerings/{key}/session/{id}/act` (carrying the offering key + session in the route). Prose →
/// `<p>`, a [`Section`](ViewNode::Section) → a titled `<section>`, a [`Menu`](ViewNode::Menu) row /
/// a [`Button`](ViewNode::Button) → one POST form; containers recurse. A `!enabled` affordance is
/// rendered `disabled` + dimmed (the cap tooth SHOWN, not hidden — a decoration; the executor still
/// refuses a crafted POST of it).
///
/// ⚑ **`arg` rides HIDDEN on every fixed-choice control** ([`catalog_form`]); only a
/// [`ViewNode::Input`], which declares that it wants a user value, gets an editable number box
/// ([`catalog_form_value`]). It used to be editable everywhere, which made every button label
/// non-binding — see [`catalog_form`] for the whole account.
pub fn render_catalog_forms(node: &ViewNode, key: &str, id: &str) -> String {
    let mut out = String::new();
    catalog_node(node, key, id, &mut out);
    // **THE NIGHT RECORD SKIN — for EVERY offering.** It shipped scoped to `automatafl` alongside
    // that board's painter; the skin itself is game-agnostic (plaques, pills, controls, night
    // ground) and holding it on one key is exactly what left every other surface reading as a debug
    // dump. The wrapper is INSIDE the fragment, so it survives the realtime swap — a live surface is
    // skinned exactly like the served one.
    format!("<div class=\"af-table\">{out}</div>")
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE AUTOMATAFL BOARD — a real gameboard, not a grid of letters
// ─────────────────────────────────────────────────────────────────────────────────────────

/// **The piece sprite sheet**, emitted ONCE per board and referenced by `<use href="#…">` from each
/// square — so a 121-square board costs one copy of each shape, not 121.
///
/// The three pieces are told apart on THREE redundant channels, because a player must read the
/// board at a glance and "which letter is that" is not reading:
/// * **shape** — the attractor is a RING, the repulsor an angular DIAMOND, the automaton an
///   OCTAGONAL core inside a dashed orbit;
/// * **direction** — the attractor's four spikes point INWARD (it pulls), the repulsor's point
///   OUTWARD (it pushes);
/// * **colour** (from the stylesheet) — the attractor is warm brass, the repulsor cool pale, the
///   automaton violet and the only thing on the board that glows.
///
/// Inline, self-contained, no external asset and no request — the CSP story stays trivial.
const AF_SPRITES: &str = "<svg class=\"af-defs\" width=\"0\" height=\"0\" aria-hidden=\"true\" \
     focusable=\"false\"><defs>\
     <g id=\"af-att\">\
     <circle cx=\"16\" cy=\"16\" r=\"9\" fill=\"currentColor\"/>\
     <circle cx=\"16\" cy=\"16\" r=\"4.3\" fill=\"#08070c\" fill-opacity=\".62\"/>\
     <path d=\"M16 5.8 18.8 1.8H13.2ZM16 26.2 18.8 30.2H13.2ZM5.8 16 1.8 13.2V18.8Z\
     M26.2 16 30.2 13.2V18.8Z\" fill=\"currentColor\" fill-opacity=\".92\"/></g>\
     <g id=\"af-rep\">\
     <path d=\"M16 7 25 16 16 25 7 16Z\" fill=\"currentColor\"/>\
     <path d=\"M16 12.2 19.8 16 16 19.8 12.2 16Z\" fill=\"#08070c\" fill-opacity=\".62\"/>\
     <path d=\"M16 1.8 18.8 5.6H13.2ZM16 30.2 18.8 26.4H13.2ZM1.8 16 5.6 13.2V18.8Z\
     M30.2 16 26.4 13.2V18.8Z\" fill=\"currentColor\" fill-opacity=\".92\"/></g>\
     <g id=\"af-auto\">\
     <circle cx=\"16\" cy=\"16\" r=\"13.6\" fill=\"none\" stroke=\"currentColor\" \
     stroke-width=\"1.1\" stroke-opacity=\".6\" stroke-dasharray=\"2.4 2.6\"/>\
     <path d=\"M11.4 4.2H20.6L27.8 11.4V20.6L20.6 27.8H11.4L4.2 20.6V11.4Z\" \
     fill=\"currentColor\" fill-opacity=\".4\"/>\
     <path d=\"M11.4 4.2H20.6L27.8 11.4V20.6L20.6 27.8H11.4L4.2 20.6V11.4Z\" fill=\"none\" \
     stroke=\"currentColor\" stroke-width=\"2\" stroke-linejoin=\"round\"/>\
     <circle cx=\"16\" cy=\"16\" r=\"4.2\" fill=\"currentColor\"/></g>\
     <g id=\"af-goal\">\
     <path d=\"M3 9V3h6M23 3h6v6M29 23v6h-6M9 29H3v-6\" fill=\"none\" stroke=\"currentColor\" \
     stroke-width=\"2.2\" stroke-linecap=\"square\"/></g>\
     <g id=\"af-dead\">\
     <path d=\"M7 7 25 25M25 7 7 25\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"3.4\" \
     stroke-linecap=\"square\"/></g>\
     </defs></svg>";

/// The piece a board glyph names, as `(sprite id, class, spoken name)`. The glyph vocabulary is the
/// OFFERING's own (`A` attractor, `R` repulsor, `@` automaton; anything else is a vacant square, and
/// `a`/`b` mark a vacant goal corner) — the same glyph the Discord/Telegram text renderers paint, so
/// the two renderings read the same board and cannot drift.
fn af_piece(glyph: &str) -> Option<(&'static str, &'static str, &'static str)> {
    match glyph {
        "A" => Some(("af-att", "p-att", "attractor")),
        "R" => Some(("af-rep", "p-rep", "repulsor")),
        "@" => Some(("af-auto", "p-auto", "the automaton")),
        _ => None,
    }
}

/// The seat letter of the goal corner at `c`. A VACANT corner already says so in its glyph
/// (`a`/`b`); an OCCUPIED one is resolved against the game's LEAN-sourced goal assignment
/// (`AutomataflRules.stockGoals2`, via `dregg_automatafl::game::goal_owner_at`) rather than guessed
/// from the geometry, so the renderer never invents an owner. `None` = the square is a goal (the
/// surface tagged it one) that the assignment does not describe, or the game oracle did not answer:
/// it still paints as a goal, it just does not claim to know whose.
fn af_goal_owner(c: (i32, i32), glyph: &str) -> Option<char> {
    match glyph {
        "a" => Some('a'),
        "b" => Some('b'),
        _ => dregg_automatafl::game::goal_owner_at(c)
            .ok()
            .flatten()
            .map(|who| if who == 0 { 'a' } else { 'b' }),
    }
}

/// ⚑ **THE SPOKEN ROLE OF A SQUARE — ONE SOURCE, BOTH PAINTERS.**
///
/// This was written inside [`af_square`] and reachable only from automatafl's bespoke painter, which
/// is why a screen-reader user could play automatafl and NOT the tug: the generic
/// [`ViewNode::CoordGrid`] branch said `"{turn} row X, column Y"` — a coordinate and an internal verb
/// string, with no piece, no state and no reason a square was unusable. It is not automatafl
/// knowledge: `tag` is `deos-view`'s own cell vocabulary, emitted by every offering that draws a
/// grid, so every future `CoordGrid` game gets these sentences for free the moment it tags a cell.
///
/// The leading `", "` is part of each phrase: it is appended to `"{what} at {x},{y}"`, and an
/// untagged square contributes nothing rather than a dangling comma.
fn cell_role_phrase(tag: &str, is_goal: bool) -> &'static str {
    match tag {
        // ⚑ Spoken FIRST and spoken in full: a screen-reader user tabbing the board must be told
        // this square is out of play, and told why, or the only signal they get is a button that
        // vanished.
        "mark" => ", MARKED by a clash — dead for the rest of this turn, at either end of a move",
        "warn" => ", picked up",
        "sealed" => ", where you sealed your move",
        "good" => ", a legal move",
        // ⚑ A screen-reader user gets the SAME third state a sighted one does. Without this the
        // dashed outline is the only carrier and the square reads identically to a legal move —
        // which is the exact wound the outline exists to close, moved one sense over.
        "blocked" => {
            ", blocked — a piece is in the way, so this move only runs if that piece is moved first"
        }
        _ if is_goal => ", a goal corner",
        // The automaton's square needs no role: the piece name already carries it.
        _ => "",
    }
}

/// The two predicates the whole board painter turns on, read off the DATA — `(is_dead, is_goal)`.
///
/// * **dead** — a coordinate a CLASH burned for the rest of the turn (the offering's `mark` tag, and
///   the `×` glyph the text frontends paint). It is not a role the square can share: it means
///   "unusable", so it outranks the goal inlay, the piece art and every highlight.
/// * **goal** — EXACTLY the generic renderer's goal predicate: the offering marks a VACANT corner
///   with the owner's lowercase letter and an OCCUPIED one with the `goal` tag; either signal is the
///   objective. So a board of any size marks its own goals.
///
/// One function because three places now need the same answer: the square's classes, its spoken name,
/// and the small-screen move list.
fn af_square_kind(cell: &CoordCell) -> (bool, bool) {
    let is_dead = cell.tag == "mark";
    let is_goal = !is_dead && (cell.tag == "goal" || cell.glyph == "a" || cell.glyph == "b");
    (is_dead, is_goal)
}

/// **THE SPOKEN SQUARE** — the glyph alone ("·", "R") tells a screen-reader user nothing; the piece,
/// its coordinates and its role this turn make the board playable by keyboard in earnest.
///
/// Also the VISIBLE label of every row of [`af_move_list`], which is why it is a function and not an
/// expression inside the painter: the small-screen move list must name a move in exactly the words
/// the square itself is named in, or a player is reading two different boards.
fn af_spoken(cell: &CoordCell, x: usize, y: usize) -> String {
    let (is_dead, is_goal) = af_square_kind(cell);
    let what = match af_piece(&cell.glyph) {
        // A dead square's occupant is not in the data any more (the glyph is the cross), so the
        // spoken name says what the square IS rather than guessing what is on it.
        _ if is_dead => "marked square",
        Some((_, _, name)) => name,
        None if is_goal => "empty goal corner",
        None => "empty",
    };
    format!(
        "{what} at {x},{y}{role}",
        role = cell_role_phrase(&cell.tag, is_goal)
    )
}

/// One square of the automatafl board, as HTML. `cell` is the offering's own [`CoordCell`]; the
/// square's ROLE this turn is entirely in `cell.tag` / `cell.highlight` (the surface decides, the
/// renderer only paints), and its affordance is `cell.turn`/`cell.arg` exactly as on the generic
/// grid — so a click is the same real POST it always was.
fn af_square(cell: &CoordCell, x: usize, y: usize, key: &str, id: &str) -> String {
    let piece = af_piece(&cell.glyph);
    let (is_dead, is_goal) = af_square_kind(cell);
    let owner = if is_goal {
        af_goal_owner((x as i32, y as i32), &cell.glyph)
    } else {
        None
    };

    let mut cls = String::from("cell");
    if cell.highlight {
        cls.push_str(" highlighted");
    }
    if !cell.tag.is_empty() {
        cls.push_str(&format!(" tag-{}", esc(&cell.tag)));
    }
    if is_goal {
        cls.push_str(" goal");
    }
    if piece.is_none() {
        // A square with no piece on it: the legal-target pip may sit in the middle of it.
        cls.push_str(" af-empty");
    }

    // The visual stack, back to front: the goal inlay, then the piece.
    let mut art = String::new();
    if is_goal {
        art.push_str(
            "<svg class=\"af-mark\" viewBox=\"0 0 32 32\" aria-hidden=\"true\">\
             <use href=\"#af-goal\"/></svg>",
        );
        if let Some(letter) = owner {
            art.push_str(&format!(
                "<span class=\"af-seat\" aria-hidden=\"true\">{letter}</span>"
            ));
        }
    }
    if is_dead {
        // The cross IS the square's art. The offering replaced the glyph with `×` (so Discord and
        // Telegram see the mark too), which means the renderer cannot know which piece is standing
        // there — the clash plaque names it in prose instead, and here the square just reads dead.
        art.push_str(
            "<svg class=\"af-p af-x\" viewBox=\"0 0 32 32\" aria-hidden=\"true\">\
             <use href=\"#af-dead\"/></svg>",
        );
    } else {
        match piece {
            Some((sprite, pcls, _)) => art.push_str(&format!(
                "<svg class=\"af-p {pcls}\" viewBox=\"0 0 32 32\" aria-hidden=\"true\">\
                 <use href=\"#{sprite}\"/></svg>"
            )),
            None => art.push_str("<span class=\"af-dot\" aria-hidden=\"true\"></span>"),
        }
    }

    let spoken = af_spoken(cell, x, y);

    // `data-glyph` keeps the underlying datum on the square: the letter the offering emitted, which
    // the text frontends paint literally. Nothing is styled off it — it is the board's own value,
    // legible to a reader of the markup and to a test.
    let glyph_attr = format!(" data-glyph=\"{}\"", esc(&cell.glyph));

    if cell.turn.is_empty() {
        format!(
            "<span class=\"{cls}\"{glyph_attr}>{art}<span class=\"sr-only\">{spoken}</span></span>"
        )
    } else {
        format!(
            "<form class=\"{cls}\"{glyph_attr} method=\"post\" \
             action=\"/offerings/{key}/session/{id}/act\">\
             <input type=\"hidden\" name=\"turn\" value=\"{turn}\">\
             <input type=\"hidden\" name=\"arg\" value=\"{arg}\">\
             <button type=\"submit\">{art}\
             <span class=\"sr-only\">{turn} {spoken}</span></button></form>",
            key = esc(key),
            id = esc(id),
            turn = esc(&cell.turn),
            arg = cell.arg,
        )
    }
}

/// **THE AUTOMATAFL BOARD.** The same `CoordGrid` data the text frontends read, painted as a real
/// board: a night well in a brass frame, squares in two night tones separated by brass hairlines,
/// SVG pieces, coordinate rulers down the left and along the bottom, and the four goal corners
/// inlaid in brass with their owning seat's letter.
///
/// **N-GENERIC.** Every dimension comes from the DATA: `cols` gives the width, `cells.len()` the
/// height, and both rulers and the CSS grid are sized from those. There is no `11` and no `5` here,
/// and none in the stylesheet either — the square count reaches CSS as the `--af-n` custom
/// property.
///
/// The inner `.coordgrid` keeps its class and its inline `grid-template-columns`, so the generic
/// board CSS (and everything that pins it) still applies; the `.af-board` wrapper is what carries
/// the Night Record skin.
fn automatafl_board(cols: usize, cells: &[CoordCell], key: &str, id: &str, out: &mut String) {
    let cols_n = cols.max(1);
    let rows = cells.len().div_ceil(cols_n);
    // Same checker rule as the generic grid: `nth-child` alternation reads as a checkerboard only
    // when the row length is ODD (an even width would stripe).
    let checkered = if cols_n % 2 == 1 { " checkered" } else { "" };

    out.push_str(&format!(
        "<div class=\"af-board\" style=\"--af-n:{cols_n};--af-rows:{rows}\">"
    ));
    out.push_str(AF_SPRITES);
    // The rank ruler (rows, top to bottom) — the `y` of every coordinate the surface prints.
    out.push_str("<div class=\"af-ruler af-ranks\" aria-hidden=\"true\">");
    for y in 0..rows {
        out.push_str(&format!("<span>{y}</span>"));
    }
    out.push_str("</div>");
    out.push_str(&format!(
        "<div class=\"coordgrid{checkered}\" \
         style=\"grid-template-columns:repeat({cols_n},1fr)\">"
    ));
    for (i, cell) in cells.iter().enumerate() {
        out.push_str(&af_square(cell, i % cols_n, i / cols_n, key, id));
    }
    out.push_str("</div>");
    // The file ruler (columns, left to right) — the `x`.
    out.push_str("<div class=\"af-ruler af-files\" aria-hidden=\"true\">");
    for x in 0..cols_n {
        out.push_str(&format!("<span>{x}</span>"));
    }
    out.push_str("</div>");
    out.push_str(AF_KEY);
    out.push_str("</div>");
    // ⚑ THE SECOND WAY IN. Outside `.af-board` deliberately: that element is an explicit 3-row CSS
    // grid whose rows are already spoken for, and the list is not part of the board.
    out.push_str(&af_move_list(cells, cols_n, key, id));
}

/// ⚑ **AUTOMATAFL'S SECOND INPUT PATH — the board's squares are not the only way to move.**
///
/// The measured defect: at the ≤44rem breakpoint a cell is `min-width:1.35rem` ≈ 21.6px, half the
/// 44px tap-target floor. **That is the right call and this does not change it** — 11 squares × 44px
/// is 484px and cannot fit a 360px viewport, so the cell floor buys a whole visible board, exactly as
/// the comment on that rule says. What was missing is the thing `descent_play` has and automatafl did
/// not: an ALTERNATIVE. Descent's verb list gives a motor-impaired player 48px targets for every legal
/// move; on automatafl the 21.6px squares were the ONLY affordance, so a player who cannot hit them
/// could not act at all.
///
/// **It invents nothing.** Every row is a cell that already carries an affordance, its label is
/// [`af_spoken`] — the same sentence that square's own accessible name uses — and its POST is the
/// cell's own `{turn, arg}`, so the list and the board are the same move by construction and cannot
/// drift. Zero board dimensions, zero game rules, no second vocabulary to keep in sync.
///
/// **Bounded** three ways: it is a `<details>`, collapsed, so it costs one line until asked for; the
/// summary states the count up front; and the rows are ORDERED the way `AutomataflSurface::actions`
/// orders its own button budget — the targets the phase is waiting on (`good`, then the proposable-but
/// -`blocked` ones) ahead of the selects, because on the stock opening there are 36 movable pieces and
/// a player hunting for the seal should not scroll past all of them.
///
/// Empty string when no cell carries an affordance — a spectator's board, a finished match, and the
/// landing page's still (which passes `turn: ""` on every square) emit nothing at all.
fn af_move_list(cells: &[CoordCell], cols_n: usize, key: &str, id: &str) -> String {
    // (index, cell) for the squares that are actually actionable, in the order described above.
    let mut live: Vec<(usize, &CoordCell)> = cells
        .iter()
        .enumerate()
        .filter(|(_, c)| !c.turn.is_empty())
        .collect();
    if live.is_empty() {
        return String::new();
    }
    // A stable sort, so within a rank the rows stay in board order (top-left to bottom-right).
    live.sort_by_key(|(_, c)| match c.tag.as_str() {
        "good" => 0u8,
        "blocked" => 1,
        _ => 2,
    });

    let mut out = format!(
        "<details class=\"af-moves\"><summary>Moves you can take now \
         ({n})<span class=\"af-moves-why\">Every square you can press, as a list — for a thumb, or a \
         keyboard, when the squares are too small to hit</span></summary><ul>",
        n = live.len(),
    );
    for (i, cell) in live {
        let (x, y) = (i % cols_n, i / cols_n);
        // The verb, capitalised, is the offering's OWN turn name (`select` / `commit` — the same word
        // the phase line on this page already prints as "phase: COMMIT"). Deriving it beats restating
        // the surface's prose label: there is no second string here to fall out of date.
        let mut verb_shown = cell.turn.clone();
        if let Some(first) = verb_shown.get_mut(0..1) {
            first.make_ascii_uppercase();
        }
        // `class="affordance"` is load-bearing, not cosmetic: it is the class the enhancement script
        // recognises (`form.affordance` / `form.cell`), so a row swaps the surface in place exactly as
        // a square press does instead of falling back to a full navigation — and the authority-field
        // injection in `offering_surface_fragment` finds this form's `turn` input like every other.
        out.push_str(&format!(
            "<li><form class=\"affordance\" method=\"post\" \
             action=\"/offerings/{key}/session/{id}/act\">\
             <input type=\"hidden\" name=\"turn\" value=\"{turn}\">\
             <input type=\"hidden\" name=\"arg\" value=\"{arg}\">\
             <button type=\"submit\"><b>{verb_shown}</b> {spoken}</button></form></li>",
            key = esc(key),
            id = esc(id),
            turn = esc(&cell.turn),
            arg = cell.arg,
            verb_shown = esc(&verb_shown),
            spoken = esc(&af_spoken(cell, x, y)),
        ));
    }
    out.push_str("</ul></details>");
    out
}

/// **The key**, under the board: the three pieces in the shapes and colours the board actually
/// paints, plus the four square states. `aria-hidden` — the board's own prose says the same thing,
/// and every square carries its role in its `.sr-only` name, so a screen reader is not read a
/// decorative legend twice.
const AF_KEY: &str = "<div class=\"af-key\" aria-hidden=\"true\">\
     <span><svg class=\"af-p p-att\" viewBox=\"0 0 32 32\"><use href=\"#af-att\"/></svg>\
     attractor · pulls</span>\
     <span><svg class=\"af-p p-rep\" viewBox=\"0 0 32 32\"><use href=\"#af-rep\"/></svg>\
     repulsor · pushes</span>\
     <span><svg class=\"af-p p-auto\" viewBox=\"0 0 32 32\"><use href=\"#af-auto\"/></svg>\
     the automaton</span>\
     <span><i class=\"k-goal\"></i>goal corner</span>\
     <span><i class=\"k-sel\"></i>your piece</span>\
     <span><i class=\"k-tgt\"></i>can reach</span>\
     <span><i class=\"k-blocked\"></i>blocked · needs the way cleared</span>\
     <span><i class=\"k-seal\"></i>your sealed move</span>\
     <span><i class=\"k-mark\"></i>marked by a clash · dead this turn</span>\
     </div>";

/// ⚑ **A MARKED SQUARE PAINTS AS OBVIOUSLY DEAD** — the conflict re-submission loop's visual half.
///
/// `dregg_automatafl`'s surface tags a coordinate a clash burned with `mark` and swaps its glyph for
/// `×` (so the Discord / Telegram text grids, which read ONLY `glyph` and `highlight`, see it too).
/// This pins the three things the browser must then do with that datum, and the negatives, because a
/// mark that paints like an ordinary square is exactly the failure the plaque exists to prevent: a
/// player who cannot see the square is dead keeps trying to use it.
#[cfg(test)]
mod binding_labels {
    use super::{named_act, pressed_label, render_catalog_forms};
    use deos_view::{MenuItem, ViewNode};
    use dreggnet_offerings::Action;

    /// ⚑ **A BUTTON LABEL IS BINDING AGAIN.** The catalog walker used to draw `arg` as an editable
    /// number beside a button whose text already named its target, so a reader could change the
    /// number and act on something else. Both polarities are pinned: a fixed-choice affordance's
    /// `arg` is HIDDEN, and the one node that asks for a user value still gets its box.
    #[test]
    fn a_fixed_affordance_hides_its_arg_and_an_input_node_keeps_its_box() {
        let menu = ViewNode::Menu {
            items: vec![
                MenuItem {
                    label: "List Ember Cloak (legendary★ · 3◈)".into(),
                    turn: "list".into(),
                    arg: 3,
                    enabled: true,
                    wants_text: false,
                },
                MenuItem {
                    label: "List Ember Cloak (legendary★ · 2◈)".into(),
                    turn: "list".into(),
                    arg: 2,
                    enabled: true,
                    wants_text: false,
                },
            ],
        };
        let html = render_catalog_forms(&menu, "trade", "s1");
        assert!(
            html.contains("<input type=\"hidden\" name=\"arg\" value=\"3\">")
                && html.contains("<input type=\"hidden\" name=\"arg\" value=\"2\">"),
            "a fixed-choice affordance carries its arg HIDDEN: {html}"
        );
        assert!(
            !html.contains("type=\"number\""),
            "no editable number may sit beside a button whose label names its target: {html}"
        );
        // Both rows are still FIREABLE and still distinguishable — hiding the box must not collapse
        // two rows that differ only by index into one.
        assert_eq!(html.matches("name=\"arg\"").count(), 2, "{html}");

        let input = ViewNode::Input {
            bind_view: "draft".into(),
            fire_turn: "bid".into(),
            submit_label: "Bid".into(),
        };
        let html = render_catalog_forms(&input, "market", "s1");
        assert!(
            html.contains("class=\"arg\" type=\"number\" name=\"arg\"") && html.contains(">Bid<"),
            "an Input node ASKS for a value, so it keeps the editable box: {html}"
        );
    }

    /// ⚑ **A DECLARED TEXT WANT GETS A REAL FIELD, AND ONLY IT DOES.** `hermes`'s `prompt`,
    /// `names`'s `register` and `doc`'s `insert` are `wants_text` affordances that the web served as
    /// bare buttons: the press carried no string and the executor refused every one of them ("the
    /// button label is not a prompt"). Three offerings, one dropped flag.
    ///
    /// Both polarities, in one test, because the two halves are the same wound from opposite sides:
    /// a row that DECLARES a text want gets a text box, and a row that does not gets NO input at all
    /// — not a text box, and (the `arg` fix this must not regress) not a number box either.
    #[test]
    fn a_wants_text_row_gets_a_text_field_and_a_fixed_row_gets_no_input() {
        let menu = ViewNode::Menu {
            items: vec![
                MenuItem {
                    label: "read — 200 calls / 200 budget left".into(),
                    turn: "prompt".into(),
                    arg: 1,
                    enabled: true,
                    wants_text: true,
                },
                MenuItem {
                    label: "register a free name".into(),
                    turn: "register".into(),
                    arg: -1,
                    enabled: false,
                    wants_text: true,
                },
                MenuItem {
                    label: "Sell the Ember Cloak".into(),
                    turn: "sell".into(),
                    arg: 2,
                    enabled: true,
                    wants_text: false,
                },
            ],
        };
        let html = render_catalog_forms(&menu, "hermes", "s1");

        // (1) The text-taking rows each carry ONE real, EMPTY text input named `text` — the payload
        //     `OfferingActForm::text` reads and `Action::with_text` rides.
        assert_eq!(
            html.matches("name=\"text\"").count(),
            2,
            "one text field per declared text want, and not one more: {html}"
        );
        assert!(
            html.contains("<input class=\"text\" type=\"text\" name=\"text\" value=\"\""),
            "the field is EMPTY — a template, never pre-filled with the label (the bodge \
             dreggnet-doc paid for once): {html}"
        );
        // (2) The `{turn, arg}` shape is UNTOUCHED, so the affordance is still the same press.
        assert!(
            html.contains("<input type=\"hidden\" name=\"turn\" value=\"prompt\">")
                && html.contains("<input type=\"hidden\" name=\"arg\" value=\"1\">"),
            "a text want does not change what the press IS: {html}"
        );
        // (3) THE arg FIX IS NOT REGRESSED. A text want is a want for PROSE; the number box stays
        //     the sole property of `ViewNode::Input`.
        assert!(
            !html.contains("type=\"number\""),
            "a declared TEXT want is not a licence to re-expose the arg box: {html}"
        );
        // (4) The cap tooth reaches the box too: a dimmed row cannot be typed into, or a reader
        //     composes a name into a control that can only refuse.
        let dimmed = html
            .split("<form ")
            .find(|f| f.contains("value=\"register\""))
            .expect("the register row rendered");
        assert!(
            dimmed.contains("aria-label=\"register text\" disabled>")
                && dimmed.contains("<button type=\"submit\" disabled>"),
            "a !enabled text row disables its field in lockstep with its button: {dimmed}"
        );
        // (5) And the fixed row is unchanged: no input of any kind beside its label.
        let fixed = html
            .split("<form ")
            .find(|f| f.contains("value=\"sell\""))
            .expect("the fixed row rendered");
        assert!(
            !fixed.contains("name=\"text\"") && !fixed.contains("type=\"number\""),
            "a fixed-index affordance offers nothing to type: {fixed}"
        );
    }

    /// The press the executor is handed: `{turn, arg}` always, and the typed string ONLY when one was
    /// really typed. Whitespace counts as nothing, because every executor tests the payload with
    /// `!t.trim().is_empty()` — a blank box must earn the same legible refusal a bare press does,
    /// never a committed turn carrying a space.
    #[test]
    fn the_typed_text_rides_the_action_and_blank_is_absent() {
        let bare = super::pressed_action("choose", 2, None);
        assert_eq!((bare.turn.as_str(), bare.arg), ("choose", 2));
        assert_eq!(bare.text, None);
        assert!(
            !bare.wants_text,
            "a fixed press is byte-identical to what it always was"
        );

        let typed = super::pressed_action("prompt", 1, Some("read notes.txt"));
        assert_eq!(typed.text.as_deref(), Some("read notes.txt"));
        assert!(typed.wants_text, "carrying text IS being a text affordance");
        assert_eq!(
            (typed.turn.as_str(), typed.arg),
            ("prompt", 1),
            "the payload rides BESIDE the {{turn, arg}}, never instead of it"
        );

        for blank in ["", "   ", "\n\t "] {
            let pressed = super::pressed_action("register", -1, Some(blank));
            assert_eq!(
                pressed.text, None,
                "a blank box is an empty press, not a turn carrying whitespace: {blank:?}"
            );
        }
    }

    /// The pressed row is identified by the exact `(turn, arg)` pair, falling back to the turn alone
    /// — otherwise two rows differing only by index would confirm each other's action.
    #[test]
    fn the_named_action_is_the_row_that_was_actually_pressed() {
        let offered = vec![
            Action::new("List Ember Cloak (2◈)", "list", 2, true),
            Action::new("List Ember Cloak (3◈)", "list", 3, true),
            Action::new("Cancel your listing", "cancel", 0, true),
        ];
        assert_eq!(
            pressed_label(offered.iter(), "list", 3).as_deref(),
            Some("List Ember Cloak (3◈)")
        );
        assert_eq!(
            pressed_label(offered.iter(), "cancel", 0).as_deref(),
            Some("Cancel your listing")
        );
        // A board cell / value-taking turn carries an arg no row declares: name the turn's row.
        assert_eq!(
            pressed_label(offered.iter(), "list", 99).as_deref(),
            Some("List Ember Cloak (2◈)")
        );
        assert_eq!(pressed_label(offered.iter(), "nothing", 0), None);

        // And the banner clause: a label when there is one, the turn name when there is not, and
        // nothing at all when there is neither.
        assert_eq!(named_act(Some("Seal (3,3)"), "seal"), "Seal (3,3) · ");
        assert_eq!(named_act(None, "seal"), "`seal` · ");
        assert_eq!(named_act(Some("   "), "seal"), "`seal` · ");
        assert_eq!(named_act(None, ""), "");
        let long = "x".repeat(200);
        assert!(named_act(Some(&long), "t").chars().count() < 95);
    }

    /// **The two registers are reconciled where they meet.** A page carrying a receipt strip also
    /// carries the sentence that says `verified` is about the MOVES and `asserted` is about the NAME.
    #[test]
    fn the_receipt_strip_glosses_its_own_vocabulary() {
        let report = dreggnet_offerings::VerifyReport::ok(3);
        let html = super::receipt_html(&report, "chain re-verified by replay", "/v");
        assert!(
            html.contains("verified") && html.contains("3 verified turns"),
            "{html}"
        );
        assert!(
            html.contains("about the MOVES") && html.contains("about the NAME"),
            "the strip must say which subject each word has: {html}"
        );
        assert!(
            html.contains("checks no signature"),
            "and must not leave `asserted` sounding like a weaker `verified`: {html}"
        );
        // ⚑ AND IT IS FOLDED, so it is not a vocabulary lesson under the move buttons of a player who
        // has not moved yet. The summary must be the QUESTION — a fold whose handle is a label
        // ("about attribution") is a worse offer than the open paragraph was.
        assert!(
            html.contains("<details class=\"receipt-gloss\">") && html.contains("<summary>"),
            "the gloss must be behind a disclosure, not appended open to every render: {html}"
        );
        let summary = html
            .split_once("<summary>")
            .and_then(|(_, tail)| tail.split_once("</summary>"))
            .map(|(s, _)| s)
            .expect("the disclosure has a summary");
        assert!(
            summary.contains('?'),
            "the summary must ask the reader's question, not name a topic: {summary:?}"
        );
    }

    /// ⚑ **THE KEEP-THIS-RUN OFFER FIRES ONCE, AND THE GATE CAN GO RED IN BOTH DIRECTIONS.** Two
    /// earlier formulations of this condition were gates that could never fire at all (`verify.turns`
    /// counts genesis, and the shared `descent-web` log's LENGTH is global — see
    /// [`super::offering_surface_fragment`]), so the polarity is pinned here rather than assumed: no
    /// offer before a move, the offer on the viewer's first, and silence forever after.
    #[test]
    fn the_keep_this_run_offer_is_made_exactly_once() {
        assert_eq!(
            super::keep_this_run_offer(0),
            "",
            "no offer before the viewer has anything to lose"
        );
        let first = super::keep_this_run_offer(1);
        assert!(
            first.contains("class=\"keep-run\"") && first.contains("href=\"/identity\""),
            "the offer names the one route that makes an identity durable: {first}"
        );
        assert!(
            !first.contains("<dialog") && !first.contains("<form"),
            "an offer at the moment of play is a sentence, never a wall or a modal: {first}"
        );
        for after in [2_usize, 3, 26] {
            assert_eq!(
                super::keep_this_run_offer(after),
                "",
                "the offer must not become a nag on move {after}"
            );
        }
    }
}

#[cfg(test)]
mod automatafl_mark_paint {
    use super::{AF_KEY, af_square};
    use deos_view::CoordCell;

    fn cell(glyph: &str, tag: &str, turn: &str, highlight: bool) -> CoordCell {
        CoordCell {
            glyph: glyph.to_string(),
            tag: tag.to_string(),
            turn: turn.to_string(),
            arg: 0,
            highlight,
        }
    }

    #[test]
    fn a_marked_square_is_painted_dead_and_says_so_to_a_screen_reader() {
        let dead = af_square(&cell("×", "mark", "", false), 3, 1, "automatafl", "t1");
        assert!(
            dead.contains("tag-mark"),
            "the dead class is on the square: {dead}"
        );
        assert!(
            dead.contains("#af-dead"),
            "and the cross sprite is its art: {dead}"
        );
        assert!(
            dead.contains("MARKED by a clash"),
            "and a screen reader is TOLD, in full: {dead}"
        );
        // NEGATIVES: no button (the offering hands a marked square no affordance), no goal inlay,
        // no piece art, no highlight.
        assert!(
            !dead.contains("<button") && !dead.contains("<form"),
            "a dead square is never clickable: {dead}"
        );
        assert!(
            !dead.contains("#af-goal"),
            "no goal inlay on a dead square: {dead}"
        );
        assert!(
            !dead.contains("#af-att") && !dead.contains("#af-rep") && !dead.contains("#af-auto"),
            "no piece art on a dead square: {dead}"
        );
        assert!(!dead.contains("highlighted"), "dead is not live: {dead}");
        // The mark WINS over a goal corner: the four stock corners are goals, and a clash can burn
        // one. Whichever tag the offering sends, `mark` must not degrade into `goal`.
        let dead_corner = af_square(&cell("×", "mark", "", false), 0, 0, "automatafl", "t1");
        assert!(dead_corner.contains("tag-mark"));
        assert!(
            !dead_corner.contains("#af-goal") && !dead_corner.contains("class=\"af-seat\""),
            "a burned goal corner reads DEAD, not as an objective: {dead_corner}"
        );
        // And the legend names it, so a stranger is never left to infer what × means.
        assert!(AF_KEY.contains("marked by a clash"));
    }

    /// The CONTROL: an ordinary occupied square is untouched by any of the above — the mark
    /// treatment is keyed off the `mark` tag alone and cannot bleed onto a live square.
    #[test]
    fn an_unmarked_square_is_unaffected() {
        let live = af_square(&cell("A", "good", "commit", true), 3, 3, "automatafl", "t1");
        assert!(
            live.contains("#af-att"),
            "the attractor still paints: {live}"
        );
        assert!(live.contains("<button"), "and is still clickable: {live}");
        assert!(
            !live.contains("tag-mark") && !live.contains("#af-dead"),
            "{live}"
        );
        assert!(!live.contains("MARKED"), "{live}");
    }
}

fn catalog_node(node: &ViewNode, key: &str, id: &str, out: &mut String) {
    match node {
        ViewNode::Text(t) => {
            if !t.trim().is_empty() {
                out.push_str("<p class=\"prose\">");
                out.push_str(&esc(t));
                out.push_str("</p>");
            }
        }
        ViewNode::Section {
            title,
            tag,
            children,
        } => {
            out.push_str(&format!(
                "<section class=\"deos-section tag-{}\"><h2>{}</h2>",
                esc(tag),
                esc(title)
            ));
            for c in children {
                catalog_node(c, key, id, out);
            }
            out.push_str("</section>");
        }
        ViewNode::Menu { items } => {
            out.push_str("<div class=\"affordances\">");
            for it in items {
                out.push_str(&catalog_form(key, id, it));
            }
            out.push_str("</div>");
        }
        ViewNode::Button { label, turn, arg } => {
            let it = MenuItem {
                label: label.clone(),
                turn: turn.clone(),
                arg: *arg,
                enabled: true,
                wants_text: false,
            };
            out.push_str(&catalog_form(key, id, &it));
        }
        // **THE AUTOMATAFL BOARD** gets its own painter — a real gameboard in the Night Record
        // language (night squares, a brass grid, SVG pieces, coordinate rulers) instead of the
        // generic letter grid below. Keyed off the OFFERING KEY, which the renderer already
        // carries, so no other game's `CoordGrid` is touched and `deos-view`'s node vocabulary
        // needs no new field. Same `{turn, arg}` affordances, same cells, same data.
        ViewNode::CoordGrid { cols, cells } if key == automatafl_web::KEY => {
            automatafl_board(*cols, cells, key, id, out);
        }
        // THE BOARD NODE — a `cols`-wide coordinate grid (automatafl's board, the tug's hand). Each
        // cell paints its glyph; a cell carrying an affordance (`turn` non-empty) is a real POST
        // button firing `{turn, arg}` (the target square), so the board is CLICKABLE in the browser;
        // a highlighted cell (the legal-move set / the selected piece / the automaton) gets the
        // `highlighted` class. An inert cell is a plain span — never a button.
        ViewNode::CoordGrid { cols, cells } => {
            let cols_n = (*cols).max(1);
            // The checkerboard is a property of the WIDTH, not of a particular game: `nth-child`
            // alternation reads as a checker only when the row length is odd (an even width would
            // stripe). The renderer knows the real column count, so it decides here and the
            // stylesheet stays free of board sizes — a 5, an 11 or a 13 all render correctly.
            let checkered = if cols_n % 2 == 1 { " checkered" } else { "" };
            // **THE WELL — the shared baseline lift.** Every `CoordGrid` that is not automatafl's
            // (the descent shaft, the tug hand, anything a new game emits) used to sit on the page
            // floor as a bare grid of glyphs. It is now recessed in the same night well the
            // automatafl board earned, in a brass surround: the board reads as a BOARD before a
            // single glyph is read. Zero game knowledge and no dimension is assumed — the well is
            // handed the real column count as `--nr-n` and sizes itself from the DATA, so a 3-wide
            // hand and a 9-wide shaft both land.
            out.push_str(&format!(
                "<div class=\"nr-well\" style=\"--nr-n:{cols_n}\">"
            ));
            out.push_str(&format!(
                "<div class=\"coordgrid{checkered}\" \
                 style=\"grid-template-columns:repeat({cols_n},1fr)\">",
            ));
            for (i, cell) in cells.iter().enumerate() {
                let hl = if cell.highlight { " highlighted" } else { "" };
                let tag = if cell.tag.is_empty() {
                    String::new()
                } else {
                    format!(" tag-{}", esc(&cell.tag))
                };
                // THE GOAL SQUARE — automatafl's objective squares paint the lowercase glyphs
                // `a`/`b` (the seat's goal) when vacant; no piece uses those glyphs (pieces are
                // `R`/`A`/`@`/`·`), so a lowercase `a`/`b` uniquely marks a goal cell. On the STOCK
                // board a goal corner starts OCCUPIED (a repulsor sits on all four), and an
                // occupied corner keeps its piece glyph — so the surface also tags it `goal`, and
                // either signal earns the distinct `goal` look (a teal dashed objective ring). A
                // goal never reads as a plain square — even when it is also a legal move target
                // (green) it stays legible as the objective.
                let goal = if cell.glyph == "a" || cell.glyph == "b" || cell.tag == "goal" {
                    " goal"
                } else {
                    ""
                };
                // **HOW WIDE IS THE GLYPH** — the other half of why a generic grid read as a debug
                // dump. `⚑`, `═`, `A` and `·` are SYMBOLS and want to be large and centred; `#17`,
                // `L3`, `v2` are LABELS and want mono, small, and a chip's contrast, or they overflow
                // their square into a smear. Nothing here knows a game: the class is chosen from the
                // glyph's own character count, and a vacant cell (empty / the conventional `·`) is
                // marked so the stylesheet can recede it instead of printing a dot at full strength.
                let shape = match cell.glyph.chars().count() {
                    0 => " nr-void",
                    1 if cell.glyph == "·" || cell.glyph == "." => " nr-void",
                    1 => " nr-sym",
                    2 => " nr-sym nr-sym2",
                    _ => " nr-label",
                };
                // ⚑ **THE SPOKEN SQUARE — the SAME sentence the bespoke painter speaks.** This
                // branch used to say `"{turn} row X, column Y"`: a coordinate and an internal verb
                // string, with no identity and no state, which is why a screen-reader user could
                // play automatafl (whose painter narrated in full) and could NOT play the tug. The
                // role sentence now comes from [`cell_role_phrase`] — ONE function, over
                // `deos-view`'s own `tag` vocabulary — so the tug's hand and every future
                // `CoordGrid` game are narrated the moment they tag a cell, with no per-game code.
                //
                // Identity is whatever the DATA carries: the glyph, or "empty" for the vacant cell
                // the shape rule already recognised. Coordinates stay 1-based "row/column" rather
                // than the game's own origin, because a generic grid does not know one.
                let (row, col) = (i / cols_n + 1, i % cols_n + 1);
                let what = if shape == " nr-void" {
                    "empty".to_string()
                } else {
                    esc(&cell.glyph)
                };
                let spoken = format!(
                    "{what} at row {row}, column {col}{role}",
                    role = cell_role_phrase(&cell.tag, !goal.is_empty()),
                );
                // ⚑ AND THE GLYPH IS `aria-hidden`, exactly as on the bespoke board. Left visible to
                // the accessibility tree it was CONCATENATED with the sr-only text, so the accessible
                // name of a target square was the symbol followed by an internal verb — "· select row
                // 4, column 7". The glyph is the picture; the sr-only span is the meaning.
                let glyph = format!("<span aria-hidden=\"true\">{}</span>", esc(&cell.glyph));
                if cell.turn.is_empty() {
                    out.push_str(&format!(
                        "<span class=\"cell{hl}{tag}{goal}{shape}\">{glyph}\
                         <span class=\"sr-only\">{spoken}</span></span>",
                    ));
                } else {
                    out.push_str(&format!(
                        "<form class=\"cell{hl}{tag}{goal}{shape}\" method=\"post\" \
                         action=\"/offerings/{key}/session/{id}/act\">\
                         <input type=\"hidden\" name=\"turn\" value=\"{turn}\">\
                         <input type=\"hidden\" name=\"arg\" value=\"{arg}\">\
                         <button type=\"submit\">{glyph}\
                         <span class=\"sr-only\">{turn} {spoken}</span>\
                         </button></form>",
                        key = esc(key),
                        id = esc(id),
                        turn = esc(&cell.turn),
                        arg = cell.arg,
                    ));
                }
            }
            out.push_str("</div></div>");
        }
        ViewNode::Pill { text, tag, .. } => {
            out.push_str(&format!(
                "<span class=\"pill tag-{}\">{}</span>",
                esc(tag),
                esc(text)
            ));
        }
        ViewNode::Icon { glyph, tag } => {
            out.push_str(&format!(
                "<span class=\"icon tag-{}\">{}</span>",
                esc(tag),
                esc(glyph)
            ));
        }
        // A vertical stack: just recurse (the page flow IS vertical). No wrapper needed.
        ViewNode::VStack(cs) => {
            for c in cs {
                catalog_node(c, key, id, out);
            }
        }
        // A ROW → a flex row of columns, so a table's cells sit side-by-side instead of
        // collapsing into a wall of stacked paragraphs (the pre-polish render). Text cells share
        // the row evenly; pills/icons keep their natural width.
        ViewNode::Row(cs) => {
            out.push_str("<div class=\"deos-row\">");
            for c in cs {
                catalog_node(c, key, id, out);
            }
            out.push_str("</div>");
        }
        // A LIST → a gapped vertical stack in a subtle frame (legible, not a raw dump).
        ViewNode::List(cs) => {
            out.push_str("<div class=\"deos-list\">");
            for c in cs {
                catalog_node(c, key, id, out);
            }
            out.push_str("</div>");
        }
        // A TABLE → a bordered, row-divided grid. Its children are [`ViewNode::Row`]s; an
        // all-text FIRST row (a column-header row, as the trade / inventory surfaces emit) is
        // painted as a `header` row. A table whose first row already carries data (the tug guild
        // lanes: a pill in row 0) is NOT given a header — every row reads as data.
        ViewNode::Table(rows) => {
            let header_first = rows.len() > 1
                && matches!(
                    rows.first(),
                    Some(ViewNode::Row(cs))
                        if !cs.is_empty() && cs.iter().all(|c| matches!(c, ViewNode::Text(_)))
                );
            out.push_str("<div class=\"deos-table\">");
            for (i, r) in rows.iter().enumerate() {
                match r {
                    ViewNode::Row(cs) => {
                        let hcls = if header_first && i == 0 {
                            " header"
                        } else {
                            ""
                        };
                        out.push_str(&format!("<div class=\"deos-row{hcls}\">"));
                        for c in cs {
                            catalog_node(c, key, id, out);
                        }
                        out.push_str("</div>");
                    }
                    other => catalog_node(other, key, id, out),
                }
            }
            out.push_str("</div>");
        }
        ViewNode::Grid { children, .. } => {
            for c in children {
                catalog_node(c, key, id, out);
            }
        }
        // TABS (the affordance-loss cure — the catalog route was recursing panels but DROPPING the
        // tab-switch): each tab label is one POST form firing `select_turn` with `arg = the tab
        // index`, THEN the panels recurse — so the tab-switch is reachable, matching the session route.
        ViewNode::Tabs {
            tabs,
            select_turn,
            panels,
            ..
        } => {
            if !select_turn.is_empty() {
                out.push_str("<div class=\"affordances tabs\">");
                for (i, label) in tabs.iter().enumerate() {
                    let it = MenuItem {
                        label: label.clone(),
                        turn: select_turn.clone(),
                        arg: i as i64,
                        enabled: true,
                        wants_text: false,
                    };
                    out.push_str(&catalog_form(key, id, &it));
                }
                out.push_str("</div>");
            }
            for p in panels {
                catalog_node(p, key, id, out);
            }
        }
        ViewNode::Host { view: Some(v), .. } => catalog_node(v, key, id, out),
        ViewNode::Adept(inner) => catalog_node(inner, key, id, out),
        // A `Tile{handle}` whose handle names an asset paints as the inline deterministic SVG
        // sprite (dreggnet-sprite); a handle that names no asset falls back to a labelled
        // placeholder (the gpui-free renderers' behaviour). This is the item→art swap on the
        // catalog render path.
        ViewNode::Tile { handle, w, h } => match sprite::tile_html(handle, *w, *h) {
            Some(html) => out.push_str(&html),
            None => out.push_str(&format!(
                "<div class=\"sprite-tile placeholder\">{}</div>",
                esc(handle)
            )),
        },
        ViewNode::Divider => out.push_str("<hr>"),
        // HALO (the affordance-loss cure): each handle in the direct-manipulation ring → one POST
        // form (a refused handle dimmed + disabled — the cap tooth SHOWN, not hidden), so a halo
        // handle FIRES on the catalog route too instead of silently doing nothing.
        ViewNode::Halo { handles, .. } => {
            out.push_str("<div class=\"affordances halo\">");
            for h in handles {
                let it = MenuItem {
                    label: h.glyph.clone(),
                    turn: h.turn.clone(),
                    arg: h.arg,
                    enabled: h.enabled,
                    // A halo handle is a FIXED press by construction (the IR gives `HaloHandle` no
                    // text want) — a ring glyph has nowhere to put a field.
                    wants_text: false,
                };
                out.push_str(&catalog_form(key, id, &it));
            }
            out.push_str("</div>");
        }
        // BREADCRUMB (the affordance-loss cure): the nav path; a crumb with a non-empty `turn` is a
        // clickable POST form, an inert crumb a plain label.
        ViewNode::Breadcrumb { items } => {
            out.push_str("<nav class=\"breadcrumb\">");
            for (i, c) in items.iter().enumerate() {
                if i > 0 {
                    out.push_str("<span class=\"crumb-sep\">&rarr;</span>");
                }
                if c.turn.is_empty() {
                    out.push_str(&format!("<span class=\"crumb\">{}</span>", esc(&c.label)));
                } else {
                    let it = MenuItem {
                        label: c.label.clone(),
                        turn: c.turn.clone(),
                        arg: c.arg,
                        enabled: true,
                        wants_text: false,
                    };
                    out.push_str(&catalog_form(key, id, &it));
                }
            }
            out.push_str("</nav>");
        }
        // An `input` whose committed draft parses into `fire_turn`'s `arg` (a value-taking turn) is a
        // real editable-arg POST — the turn is reachable on the no-JS catalog route; a draft-only
        // input (empty `fire_turn`) is a plain field with no actuation.
        ViewNode::Input {
            bind_view,
            fire_turn,
            submit_label,
        } => {
            if fire_turn.is_empty() {
                out.push_str(&format!(
                    "<span class=\"deos-input\">&lsaquo;{}&rsaquo;</span>",
                    esc(bind_view)
                ));
            } else {
                let label = if submit_label.is_empty() {
                    "submit"
                } else {
                    submit_label.as_str()
                };
                let it = MenuItem {
                    label: label.to_string(),
                    turn: fire_turn.clone(),
                    arg: 0,
                    enabled: true,
                    wants_text: false,
                };
                // THE ONE EDITABLE-ARG CONTROL on this walker: an `Input` node ASKS for a value.
                out.push_str(&catalog_form_value(key, id, &it));
            }
        }
        // ── STATIC-PROJECTION leaves — DISPLAYED (visible, matching the session route), never a
        //    fireable affordance on the no-JS catalog route (it carries no live bind values). ──
        ViewNode::Bind { slot, label, .. } => {
            out.push_str(&format!(
                "<span class=\"deos-bind\" data-slot=\"{slot}\">{}</span>",
                esc(label)
            ));
        }
        ViewNode::Gauge { slot, max, label } => {
            out.push_str(&format!(
                "<div class=\"gauge\" data-slot=\"{slot}\">{}(/{max})</div>",
                esc(label)
            ));
        }
        // A LITERAL meter (a light clock, a carry ceiling, a guardian's vitality) is the one bound
        // visual the no-JS route CAN paint honestly: it carries its own numbers, so the fill is
        // baked here rather than waiting on a live slot. `label · bar · value/max` — a real bar, not
        // a bare ratio, because the shape is what a player reads at a glance.
        ViewNode::Progress { value, max, label } => {
            let pct = if *max == 0 {
                0.0
            } else {
                (*value as f64 / *max as f64).clamp(0.0, 1.0) * 100.0
            };
            out.push_str(&format!(
                "<div class=\"progress\">\
                 <span class=\"progress-label\">{}</span>\
                 <span class=\"progress-track\">\
                 <span class=\"progress-fill\" style=\"width:{pct:.1}%\"></span></span>\
                 <span class=\"progress-value\">{}/{}</span></div>",
                esc(label),
                value,
                max
            ));
        }
        // VALUE-DEPENDENT controls (declared exception): a `slider`'s fired `arg` is the DRAGGED
        // value and a `toggle`'s fired turn depends on the LIVE slot — neither a fixed `{turn, arg}`
        // press a no-JS POST can express (the reason `deos_view::actuations` excludes them). Shown
        // as a display; live actuation is on the client-JS path only.
        ViewNode::Slider { slot, min, max, .. } => {
            out.push_str(&format!(
                "<div class=\"slider\" data-slot=\"{slot}\">&lsaquo;slider {min}&ndash;{max} (live surface)&rsaquo;</div>"
            ));
        }
        ViewNode::Toggle {
            slot,
            glyph_off,
            label,
            ..
        } => {
            out.push_str(&format!(
                "<div class=\"toggle\" data-slot=\"{slot}\">{} {} (live surface)</div>",
                esc(glyph_off),
                esc(label)
            ));
        }
        // An UNRESOLVED mount → an honest placeholder (the client-JS path re-reads the cell heap).
        ViewNode::Host { view: None, cell } => {
            out.push_str(&format!(
                "<div class=\"deos-host-unresolved\">&lsaquo;mount cell {}: unresolved&rsaquo;</div>",
                esc(cell)
            ));
        }
    }
}

/// One affordance POST-form control for the catalog: `<form method=post
/// action="/offerings/{key}/session/{id}/act">` carrying the affordance's `{turn, arg}` as HIDDEN
/// inputs plus a submit button whose label names the target. A `!enabled` row is dimmed +
/// `disabled` (a decoration; the executor is the referee).
///
/// ⚑ **`arg` IS HIDDEN, and that closes a real wound.** This walker used to render `arg` as a
/// VISIBLE EDITABLE `<input type="number">` beside a button whose text already fully named its
/// target (`List Ember Cloak (legendary★ · 3◈)`), so the label was NOT BINDING: change the box,
/// press the button, act on something else. It bit hardest where two rows differ only by index —
/// trade ships two Ember Cloaks distinguishable only by that number, and the tug's `0, 7, 28, 63`
/// read as leaked internals against seven lanes and a six-card hand
/// (`docs/reference/UX-QA-SWEEP-2026-07-26.md`, finding 1).
///
/// **Why hiding it breaks nothing.** A `MenuItem`/`Button`/`Halo`/`Breadcrumb`/`CoordCell` carries a
/// FIXED `{turn, arg}` chosen by the offering, and that is exactly what [`deos_view::actuations`] —
/// the canonical carrier behind Telegram's keyboard, WeChat's numbered list and Discord's buttons —
/// hands those hosts. On all three the number was never typeable, so no offering can have depended
/// on a user editing it; this walker was the single surface where the label and the payload could
/// disagree. The one node that genuinely wants a user value is [`ViewNode::Input`], which declares
/// it (`fire_turn`) and renders through [`catalog_form_value`] instead. The sibling backend
/// `deos_view::web` has always drawn exactly this distinction (`session_form` vs
/// `session_form_arg`) — this is the catalog walker catching up to it.
///
/// ⚑ **AND A DECLARED TEXT WANT GETS A REAL FIELD.** `MenuItem::wants_text` is the affordance
/// saying "this slot takes the user's prose" (a Hermes PROMPT, a document INSERT / set-title, a name
/// to register). It rides its own `<input type="text" name="text">` — never the number box, which
/// stays the sole property of [`ViewNode::Input`]. The two wants are DIFFERENT wants and they get
/// different controls: a fixed row's `arg` is its identity and stays hidden; a text row's string is
/// the user's and is typed. Without the field the button was a dead affordance — the press carried no
/// string and the executor correctly refused it ("no prompt supplied … the button label is not a
/// prompt"), which is what made `hermes`/`names`/`doc` unplayable on the web.
fn catalog_form(key: &str, id: &str, it: &MenuItem) -> String {
    let (disabled, cls) = if it.enabled {
        ("", "affordance")
    } else {
        (" disabled", "affordance dimmed")
    };
    // The field a declared text want gets — empty (a TEMPLATE; the prose is the user's, never
    // pre-filled with the label, which is exactly the bodge dreggnet-doc paid for once), disabled in
    // lockstep with the button so a dimmed row cannot be typed into either.
    let text_field = if it.wants_text {
        format!(
            "<input class=\"text\" type=\"text\" name=\"text\" value=\"\" \
             autocomplete=\"off\" placeholder=\"{placeholder}\" \
             aria-label=\"{turn} text\"{disabled}>",
            placeholder = esc(&format!("type the text for `{}`", it.turn)),
            turn = esc(&it.turn),
            disabled = disabled,
        )
    } else {
        String::new()
    };
    let cls = if it.wants_text {
        format!("{cls} text")
    } else {
        cls.to_string()
    };
    format!(
        "<form class=\"{cls}\" method=\"post\" action=\"/offerings/{key}/session/{id}/act\" \
         data-session-action=\"turn\" data-turn=\"{turn}\">\
         <input type=\"hidden\" name=\"turn\" value=\"{turn}\">\
         <input type=\"hidden\" name=\"arg\" value=\"{arg}\">\
         {text_field}\
         <button type=\"submit\"{disabled}>{label}</button></form>",
        cls = cls,
        key = esc(key),
        id = esc(id),
        turn = esc(&it.turn),
        arg = it.arg,
        text_field = text_field,
        disabled = disabled,
        label = esc(&it.label),
    )
}

/// [`catalog_form`] for the ONE affordance that genuinely wants a user-supplied number: a
/// [`ViewNode::Input`] whose committed draft parses into its `fire_turn`'s `arg`. Here the box is
/// the point — the button label is a verb (`Insert`, `Bid`) and the value is the user's, so there is
/// nothing for the number to contradict.
///
/// The `aria-label` names the turn the value belongs to, and the box is labelled in prose by the
/// `Input` node's own surrounding copy.
fn catalog_form_value(key: &str, id: &str, it: &MenuItem) -> String {
    format!(
        "<form class=\"affordance input\" method=\"post\" \
         action=\"/offerings/{key}/session/{id}/act\" \
         data-session-action=\"turn\" data-turn=\"{turn}\">\
         <input type=\"hidden\" name=\"turn\" value=\"{turn}\">\
         <input class=\"arg\" type=\"number\" name=\"arg\" value=\"{arg}\" step=\"1\" \
         inputmode=\"numeric\" aria-label=\"{turn} value\">\
         <button type=\"submit\">{label}</button></form>",
        key = esc(key),
        id = esc(id),
        turn = esc(&it.turn),
        arg = it.arg,
        label = esc(&it.label),
    )
}

/// **The Descent's play path** — the served, in-tab, beacon-seeded wasm run at
/// [`DESCENT_PLAY_PATH`], plus the Discord deep link beside it when `DESCENT_DISCORD_INVITE` is
/// configured.
///
/// This used to emit ONLY the Discord link (and nothing at all when the invite was unset), which is
/// why `/descent/play` was unreachable from the product: every "Play" affordance either pointed into
/// Discord or vanished, while the board link stood in for a game. The served page is now the primary
/// CTA — it always exists, so a "Play" CTA never points nowhere — and Discord is the secondary path
/// for people who want the game in chat.
///
/// ⚑ `chip` is the `.needs` qualifier ridden by the PRIMARY anchor only — `"solo · new dungeon
/// daily"` on the hero, `""` where the surrounding card already carries its own chip line and a
/// second copy would be noise. It goes on the primary and never on the Discord anchor: the point of
/// the chip is the CONTRAST with "needs a 2nd player" on the automatafl button beside it, and that
/// contrast is a property of the row, not of every Descent link on the product.
fn descent_play_cta(class: &str, chip: &str) -> String {
    let chip_html = if chip.is_empty() {
        String::new()
    } else {
        format!("<span class=\"needs solo\">{}</span>", esc(chip))
    };
    let mut out = format!(
        "<a class=\"{class}\" href=\"{href}\">Play The Descent {chip_html}\
         <span class=\"arr\" aria-hidden=\"true\">→</span></a>",
        href = DESCENT_PLAY_PATH,
        chip_html = chip_html,
    );
    if let Ok(link) = std::env::var("DESCENT_DISCORD_INVITE") {
        if !link.trim().is_empty() {
            // The secondary path gets the QUIET variant of whatever register the caller asked for
            // (a hero button → ghost button; an inline card link → the same inline link style), so
            // the two CTAs never render as two competing primaries.
            let quiet = if class.contains("btn") {
                "btn btn-ghost"
            } else {
                class
            };
            out.push_str(&format!(
                "<a class=\"{quiet}\" href=\"{href}\">Play in Discord \
                 <span class=\"arr\" aria-hidden=\"true\">→</span></a>",
                href = esc(link.trim()),
            ));
        }
    }
    out
}

/// The `GET /offerings` catalog page — The Descent featured on top (the flagship pointer), then a
/// card + "play" link per ADVERTISED offering, framed by the shared
/// `dreggnet_catalog::{flagship_pointer, shelf_intro}` copy.
///
/// ⚑ `offerings` is the SHELF (`CatalogState::list_advertised_offerings` →
/// `dreggnet_catalog::SHIPPED_KEYS`), not the full registry. This function paints whatever it is
/// handed; **what goes on the shelf is decided in one array in `dreggnet-catalog`**, not here.
fn catalog_page(offerings: &[OfferingInfo]) -> String {
    // The shelves an offering is SORTED INTO once it is shipped — grouping only, so the page reads
    // as categories rather than one flat wall of look-alike cards. These arrays are NOT the ship
    // list: an offering absent from `SHIPPED_KEYS` never reaches this function at all, and a shelf
    // with no cards renders as nothing. Any advertised key outside all three falls into the
    // catch-all "More" shelf, so a new registration can never silently vanish.
    const GAMES: &[&str] = &[
        "descent",
        "descent-campaign",
        "dungeon",
        "council",
        "market",
        "bazaar",
        "tug",
        "automatafl",
        "private-raid",
    ];
    // NOTE `cheevos`, not `cheevo`: `dreggnet_surfaces::register_surfaces` registers the
    // achievements surface under the PLURAL key. The singular never matched, so Achievements has
    // been silently falling through to the catch-all "More" shelf instead of sitting with the other
    // eight feature surfaces. (The per-shelf count added by this design pass is what surfaced it:
    // the shelf read "7".)
    const FEATURES: &[&str] = &[
        "trade",
        "inventory",
        "cheevos",
        "guild",
        "craft",
        "companion",
        "quest",
        "tavern",
        "party",
    ];
    const SERVICES: &[&str] = &["doc", "names", "compute", "grain", "hermes"];

    let card = |o: &OfferingInfo, verb: &str| -> String {
        // An offering's registered title is `Name — the tagline (details)`. Rendered whole it is a
        // three-line heading in a dense grid; split at the em-dash it becomes a scannable NAME plus
        // a quiet tagline. Presentation only — the registry string is untouched, and both halves
        // are still on the page.
        let (name, tagline) = split_title(&o.title);
        let tagline_html = if tagline.is_empty() {
            String::new()
        } else {
            format!("<p class=\"tagline\">{}</p>", esc(tagline))
        };
        // A live session is worth SEEING (a lit dot), not just counting.
        let live = if o.open_sessions > 0 { " live" } else { "" };
        // ⚑ NEVER PAINT A ZERO. Every card used to end `{key} · 0 open`, and a first-time reader
        // read the whole page as "nobody is using this right now". A population count is the one
        // number a young surface must not volunteer: at zero it says nothing (the dot simply stays
        // dark), and only above zero does it become worth saying — then it is an invitation, not a
        // census. See `docs/reference/UX-QA-SWEEP-2026-07-26.md`.
        let company = match o.open_sessions {
            0 => String::new(),
            1 => " · 1 game in progress".to_string(),
            n => format!(" · {n} games in progress"),
        };
        // THE SHARED-TABLE LINK IS GONE FOR THE HIDDEN-INFORMATION GAMES.
        //
        // Every other card still drops you into the fixed demo session `{key}-web`, which is fine
        // for a council or a market: they are shared tables by nature and hold nothing private.
        // For a TWO-PLAYER HIDDEN-MOVE game it was the whole joining experience and it was broken
        // in two ways at once — the first two identities to press a button took the seats (a race,
        // not a lobby), and because the catalog's identity is an asserted label, anyone could
        // render the opponent's private projection by asserting their label on a table id that was
        // printed on the public catalog page.
        //
        // So `tug` and `automatafl` get their table-minting door INSTEAD of the shared link, not
        // beside it. Removed outright rather than deprecated: `/offerings/tug/session/tug-web` is
        // no longer advertised anywhere, and a hand-typed ad-hoc id keeps the catalog's own open
        // behaviour (named, not fixed, in `table_seats`).
        let front_door = table_seats::lock_for_key(&o.key);
        let play_link = match front_door {
            Some(lock) => format!(
                "<a class=\"play\" href=\"{route}\">Open your own table \
                 <span class=\"arr\" aria-hidden=\"true\">→</span></a>",
                route = lock.route,
            ),
            None => format!(
                "<a class=\"play\" href=\"/offerings/{key}/session/{key}-web\">{verb} \
                 <span class=\"arr\" aria-hidden=\"true\">→</span></a>",
                key = esc(&o.key),
                verb = verb,
            ),
        };
        // ⚑ THE PLAYER-COUNT CHIP, DERIVED — never a second list to keep in step. A key with a seat
        // lock IS a two-player table (that is what the lock exists for), and there is no matchmaking
        // anywhere on this product, so the requirement has to be readable BEFORE the click that
        // reveals it. `descent` is the one shipped solo game and says so in the same slot, so the two
        // chips read as one axis rather than as a warning on some cards and nothing on others.
        let player_count = match (front_door.is_some(), o.key.as_str()) {
            (true, _) => "<p class=\"needs\">Needs a 2nd player · or hold both seats yourself</p>"
                .to_string(),
            (false, "descent" | "descent-campaign") => {
                "<p class=\"needs solo\">Play alone</p>".to_string()
            }
            (false, _) => String::new(),
        };
        format!(
            "<div class=\"offering-card\"><h3>{name}</h3>{player_count}{tagline}\
             <p class=\"meta\"><span class=\"dot{live}\"></span>{key}{company}</p>\
             {play_link}</div>",
            name = esc(name),
            player_count = player_count,
            tagline = tagline_html,
            live = live,
            key = esc(&o.key),
            company = company,
            play_link = play_link,
        )
    };
    let group = |heading: &str, shelf: &str, blurb: &str, keys: &[&str], verb: &str| -> String {
        let mut cards = String::new();
        let mut n = 0usize;
        for o in offerings {
            if keys.contains(&o.key.as_str()) {
                cards.push_str(&card(o, verb));
                n += 1;
            }
        }
        if cards.is_empty() {
            return String::new();
        }
        format!(
            "<section class=\"catalog-group shelf-{shelf}\">\
             <h2 class=\"group-h\">{heading}<span class=\"count\">{n}</span></h2>\
             <p class=\"prose\">{blurb}</p><div class=\"card-grid\">{cards}</div></section>",
            shelf = shelf,
            heading = esc(heading),
            n = n,
            blurb = esc(blurb),
            cards = cards,
        )
    };

    // The catch-all shelf for anything not in a known group.
    let known: Vec<&str> = GAMES
        .iter()
        .chain(FEATURES.iter())
        .chain(SERVICES.iter())
        .copied()
        .collect();
    let mut more = String::new();
    for o in offerings {
        if !known.contains(&o.key.as_str()) {
            more.push_str(&card(o, "Open"));
        }
    }
    let more_section = if more.is_empty() {
        String::new()
    } else {
        format!(
            "<section class=\"catalog-group shelf-more\">\
             <h2 class=\"group-h\">More</h2><div class=\"card-grid\">{more}</div></section>",
        )
    };

    // THE SHELF FRAMING (shared words: `dreggnet_catalog::{flagship_pointer, shelf_intro}`) — the
    // featured game leads, and the shelf below is the SHIP LIST, not a bin of experiments.
    // THE FUNNEL: the PLAY CTA leads (the served in-tab run at `/descent/play`) and the no-cheat
    // board is the secondary link. Previously this page offered the BOARD as its only always-present
    // affordance, so the flagship's front door on the catalog was a leaderboard.
    let descent_play = descent_play_cta("play", "");
    let body = format!(
        "<main class=\"catalog\"><div class=\"page-head\">\
         <p class=\"eyebrow\">{PRODUCT_NAME}</p>\
         <h1>Every game here checks its own moves.</h1>\
         <p class=\"deck\">{shelf}</p>\
         <p class=\"deck\">{flagship}</p>\
         <p class=\"prose\">{descent_play}<a class=\"play\" href=\"/descent\">\
         See today's finished runs \
         <span class=\"arr\" aria-hidden=\"true\">→</span></a></p></div>\
         {games}{features}{services}{more}</main>",
        PRODUCT_NAME = PRODUCT_NAME,
        flagship = esc(dreggnet_catalog::flagship_pointer()),
        shelf = esc(dreggnet_catalog::shelf_intro()),
        games = group(
            "Games",
            "games",
            "Pick one and play. Nothing to install, nothing to sign up for.",
            GAMES,
            "Play",
        ),
        // These two shelves render EMPTY (`group` returns "" for a shelf with no cards) while the
        // ship list is games-only — they come back on their own the moment a feature surface or a
        // service is added to `dreggnet_catalog::SHIPPED_KEYS`. Kept for exactly that reason:
        // re-listing must stay a one-line change.
        features = group(
            "Your character",
            "features",
            "Things you carry between games — what you own, what you made, who you play with.",
            FEATURES,
            "Open",
        ),
        services = group(
            "Tools",
            "services",
            "Not games: small services built on the same checked-move machinery.",
            SERVICES,
            "Open",
        ),
        more = more_section,
    );
    document(&format!("{PRODUCT_NAME} — all games"), "offerings", &body)
}

/// Split a registered offering title `Name — the tagline` into its two halves (the tagline is `""`
/// when the title carries no em-dash). Presentation only: both halves are rendered, so the full
/// registry string still reads on the page.
fn split_title(title: &str) -> (&str, &str) {
    match title.split_once(" — ") {
        Some((name, tagline)) => (name, tagline),
        None => (title, ""),
    }
}

/// Wrap an offering session's live-region surface in a full HTML page (breadcrumb + head + the
/// swappable `#live-surface` region). The `surface` argument is the [`offering_surface_fragment`]
/// output (notice + forms + receipt) — embedded VERBATIM here, so the full page and the swapped
/// fragment render the identical surface (ONE render path). The static chrome (crumb, name,
/// tagline) sits OUTSIDE the region: it never changes across a turn, so it is never re-sent.
fn offering_page(key: &str, title: &str, id: &SessionId, surface: &str) -> String {
    // The crumb names the offering; the surface's own sections carry the rest. The full registered
    // title still reaches the page (name + tagline), so a reader — and the portfolio test — sees it.
    let (name, tagline) = split_title(title);
    let tagline_html = if tagline.is_empty() {
        String::new()
    } else {
        format!(
            "<p class=\"deck\" style=\"font-size:var(--t-sm)\">{}</p>",
            esc(tagline)
        )
    };
    // `#live-surface` is the region the progressive-enhancement script swaps. `tabindex="-1"` makes
    // it a programmatic focus target (keyboard continuity after a swap). With JS off it is just the
    // container the server-rendered surface fills — the fallback is the current behaviour, untouched.
    //
    // ⚑ **IT IS NOT A LIVE REGION, AND MUST NOT BE.** It carried `aria-live="polite"` while the
    // enhancement script replaces its ENTIRE subtree (`cur.innerHTML=html`). Per the ARIA spec a
    // wholesale replacement inside a live region is announced in its entirety, so an 11×11 board put
    // up to 121 sr-only square descriptions in the announcement queue on every single move — and the
    // spectator page pointed the same live region at an SSE feed on a 400ms server pulse, which made
    // that an UNPROMPTED whole-board re-announcement several times a second.
    //
    // The pattern copied here is `descent_play`'s: no live region on the board, and one short
    // "what just happened" line with `role="status"`. [`LIVE_SAY`] is that line. It sits OUTSIDE the
    // swapped region deliberately — it is a node that already exists when the announcement happens,
    // which is the case screen readers handle reliably; a freshly-inserted live region is not.
    let body = format!(
        "{crumb}<main class=\"session{skin}\">\
         <div class=\"page-head\" style=\"padding-top:var(--s4)\"><h1>{name}</h1>{tagline}</div>\
         {session_rail}{live_say}\
         <div id=\"live-surface\" class=\"live-surface\" tabindex=\"-1\" \
         data-result-kind=\"surface-and-receipt\" data-events=\"{events}\">{surface}</div>\
         </main>",
        live_say = LIVE_SAY,
        crumb = crumb(name, id),
        // THE NIGHT SKIN, at PAGE level, for EVERY offering — the shared lift. It arrived scoped to
        // `key == automatafl_web::KEY` because the board painter landed with it, but the skin knows
        // nothing about automatafl: it is the plaque, the pill, the control and the night ground —
        // the Night Record, which is the product's ONE visual language (`dregg-site`'s `site.css`,
        // the poster theme). Keeping it on one key is what left twenty-two surfaces reading as a
        // debug dump, so the condition is gone. The class name stays `.af-table` because it is the
        // hook ~60 rules below already select on, and renaming it is churn with no reader upside.
        //
        // The full-viewport night ground must hang off an element OUTSIDE `#live-surface`: that
        // region animates a `transform` on every swap, and a transformed ancestor would trap a
        // `position:fixed` backdrop inside it for the duration. The swapped fragment carries
        // `.af-table` too, so a board inside the live region is skinned either way.
        skin = " af-table",
        name = esc(name),
        tagline = tagline_html,
        session_rail = game_session::session_rail(key, &id.0).unwrap_or_default(),
        // The realtime seam the enhancement script subscribes to. Declared on the live region
        // itself so the swap target and its stream can never disagree about which session they are
        // showing; a client with no `EventSource` ignores the attribute entirely.
        events = format!("/offerings/{}/session/{}/events", esc(key), esc(&id.0)),
        surface = surface,
    );
    document(&format!("{PRODUCT_NAME} — {title}"), "offerings", &body)
}

/// The page shown for a `GET`/`POST` against an unregistered offering key.
/// ⚑ **The page a RETIRED session serves** — `said` is the thing that has to survive, verbatim.
///
/// ONE page for the two ways a reader arrives at a finished match: the session url itself (which must
/// not fall through to `ensure_open`, or it would DEPLOY A FRESH EMPTY BOARD under the finished
/// match's own id — an empty table where the player's game was, plus a ghost back in "Games in
/// progress" that a write-once resolution guarantees nothing would ever clean up), and a refused act
/// on it (whose whole content is the refusal). Both need the same two things said: *what happened*,
/// and *the moves are still here*.
fn retired_session_page(key: &str, id: &str, said: &str) -> String {
    let body = format!(
        "<main class=\"session\">\
         <div class=\"notice refused\" role=\"status\">{said}</div>\
         <div class=\"page-head\"><h1>A finished match</h1></div>\
         <section class=\"deos-section tag-accent\"><h2>It was not thrown away</h2>\
         <p class=\"prose\">The moves are kept. That is what makes a finished game worth sharing \
         here: <a href=\"{verify}\" rel=\"nofollow\">replay this match</a> and the server re-executes \
         its whole recorded chain through the same rules that admitted each move — a real re-run \
         taken when you open it, not a verdict somebody stored.</p>\
         <p class=\"prose\">What a replay does <em>not</em> settle is who won. It shows that these \
         moves were legal and landed in this order.</p></section>\
         <p class=\"prose\"><a class=\"backlink\" href=\"/you\">← Your own record</a></p>\
         </main>",
        said = esc(said),
        verify = esc(&format!("/offerings/{key}/session/{id}/verify")),
    );
    document(
        &format!("{PRODUCT_NAME} — a finished match"),
        "offerings",
        &body,
    )
}

/// [`retired_session_page`] for a session url whose table this lobby has RESOLVED. The resolution's
/// own refusal is the `said`, so the finished page and a refused act carry byte-identical wording —
/// there is exactly one sentence about how a match ended and both readers get it.
fn finished_table_page(key: &str, id: &str, resolution: &table_seats::Resolution) -> String {
    retired_session_page(key, id, &resolution.refusal())
}

fn catalog_missing_offering(key: &str) -> String {
    let body = format!(
        "<main class=\"session\"><div class=\"notice refused\" role=\"status\">No offering \
         registered under <code>{key}</code>.</div>\
         <p class=\"prose\"><a class=\"backlink\" href=\"/offerings\">← Browse the catalog</a></p>\
         </main>",
        key = esc(key),
    );
    document(
        &format!("{PRODUCT_NAME} — unknown offering"),
        "offerings",
        &body,
    )
}

// ═════════════════════════════════════════════════════════════════════════════════════════
// THE PUBLIC-DEMO SERVER APP — the merged axum Router the `dreggnet-web-server` bin serves.
//
// This is the single blocker to a public demo: the library above is a set of routers over
// in-process state, but nothing MOUNTS + BINDS them. `make_app` assembles the whole surface —
// the games + feature offerings catalog, the single-offering session surface, and the seeded
// no-cheat Descent leaderboard — into ONE `Router<()>`, plus `/` (a landing) and `/health`.
// The bin (`src/bin/dreggnet-web-server.rs`) wraps it in `axum::serve` on a configurable bind.
//
// Node-free by construction: every surface verifies by REPLAY re-execution in-process (the
// offering's own `verify`, the Descent's `verify_completion`) — no testnet, no 45-min prover.
//
// NOW BUILT (this crate, additive):
//  * PERSISTENCE — the Descent leaderboard is durable over sqlite (`descent_store`, rusqlite):
//    with a `DATABASE_URL` set, submitted runs survive a restart, re-verified by REPLAY on boot
//    (`DescentState::load_from_store`) so a tampered row is dropped and cannot resurrect a cheat.
//    Unset → the in-RAM seeded demo (the committed tests' path). The live game SESSIONS (the
//    catalog `OfferingHost`) are durable the same way: with `DREGGNET_WEB_SESSION_DIR` set, each
//    session's move-log persists to a `FileResumeStore` and the host resumes every session on boot
//    by REPLAY (`resolve_demo_host`) — a tampered log refuses to reopen. Unset → in-memory only.
//    STILL EPHEMERAL: the single-offering `WebState` surface (`/session/{id}`, offering #0 alone —
//    the catalog serves the same dungeon durably at `/offerings/dungeon/...`).
//  * An HTTP run-INGEST endpoint — `POST /descent/submit` (see `descent::post_submit`): a stranger
//    submits a run's reproducible input (day + player + move sequence); it is re-executed +
//    no-cheat-verified before it can rank (an honest run ingested + persisted, a forged run 4xx).
//
// NAMED (ops / ember-gated), deliberately not built here:
//  * TLS / rate-limit / CORS — a fronting Caddy (ops, external; `demo.dregg.net` terminates TLS
//    there and reverse-proxies to this bind).
//  * AUTH — the web actor is the unsigned `dregg_user` cookie / `?user=` (a deterministic internal
//    label, not a signed credential or proof of key ownership).
// ═════════════════════════════════════════════════════════════════════════════════════════

/// **The public-demo offering host** — the full shared DreggNet portfolio, built through
/// [`dreggnet_catalog::full_catalog_host`] with the web's `alice`/`bob` electorate. Built on the
/// host's owning thread (so each offering's `!Send` internals stay confined), it is the registry
/// the demo catalog browses + plays.
pub fn demo_host() -> OfferingHost {
    dreggnet_catalog::full_catalog_host(&web_catalog_config())
}

/// The session-lifecycle env knobs the web deployment reads (each unset/empty → `None`, i.e.
/// today's unbounded behavior; an unparseable value logs a warning and stays `None` — the
/// degrade-not-refuse boot posture every other env switch here takes).
pub const WEB_MAX_SESSIONS_ENV: &str = "DREGGNET_WEB_MAX_SESSIONS";
/// See [`WEB_MAX_SESSIONS_ENV`]. Idle seconds before the TTL sweep evicts a session.
pub const WEB_SESSION_TTL_ENV: &str = "DREGGNET_WEB_SESSION_TTL_SECS";
/// See [`WEB_MAX_SESSIONS_ENV`]. Live sessions one web identity may have fresh-minted.
pub const WEB_OPENS_PER_USER_ENV: &str = "DREGGNET_WEB_OPENS_PER_USER";
/// See [`WEB_MAX_SESSIONS_ENV`]. Minimum seconds between fresh mints per web identity.
pub const WEB_MIN_OPEN_INTERVAL_ENV: &str = "DREGGNET_WEB_MIN_OPEN_INTERVAL_SECS";

/// Protected deployment-key file for the opt-in encrypted-amount Dark Pool.
///
/// The file is created by `dark-amm-tool keygen`. On Unix it must be a regular,
/// non-symlinked file with no group/other permission bits. Operators distribute
/// only a session-specific public context:
/// `dark-amm-tool public-id <key-file> <web-session-id> <new-public-file>`.
/// The command deliberately uses the exact `blake3(id)` seed rule used by
/// [`OfferingHost::ensure_open_as`], so a producer request is bound to that one
/// live web/Telegram/Discord session and the host refuses a different id.
/// Setting [`DARK_AMM_INITIAL_ROOT_ENV`] switches that deployment to the
/// proof-required operation. Supplying the exact-opening authority policy as
/// well selects strict v3; the production aggregate startup gate requires v3.
#[cfg(feature = "dark-amm-game")]
pub const DARK_AMM_SECRET_KEY_FILE_ENV: &str = "DREGG_DARK_AMM_SECRET_KEY_FILE";
/// Optional comma-separated eight-lane BabyBear commitment. When configured,
/// the host uses this value as the first root cursor. With an exact-opening
/// authority it exposes only strict v3; without one the generic library
/// registrar preserves the explicitly proof-only v2 research mode.
#[cfg(feature = "dark-amm-game")]
pub const DARK_AMM_INITIAL_ROOT_ENV: &str = "DREGG_DARK_AMM_INITIAL_ROOT";
/// Ordered Ed25519 public keys for the Tier-1 exact-opening issuers required by
/// the strict v3 Dark AMM operation. This roster is relying-party policy; an
/// uploaded receipt cannot choose or weaken it.
#[cfg(feature = "dark-amm-game")]
pub const DARK_AMM_AUTHORITY_KEYS_ENV: &str = "DREGG_DARK_AMM_AUTHORITY_PUBLIC_KEYS";
/// Required issuer signatures from [`DARK_AMM_AUTHORITY_KEYS_ENV`].
#[cfg(feature = "dark-amm-game")]
pub const DARK_AMM_AUTHORITY_THRESHOLD_ENV: &str = "DREGG_DARK_AMM_AUTHORITY_THRESHOLD";
/// Canonical public-only collective pool carrier. Unlike the legacy key file,
/// this contains no BFV secret key or decryption share.
#[cfg(feature = "dark-amm-game")]
pub const DARK_AMM_COLLECTIVE_MATERIAL_FILE_ENV: &str = "DREGG_DARK_AMM_COLLECTIVE_MATERIAL_FILE";
/// Named web/Telegram/Discord session id this root/material pair is provisioned
/// for. The registrar derives the host's exact `blake3(id)` seed and refuses all
/// other session ids at offering open.
#[cfg(feature = "dark-amm-game")]
pub const DARK_AMM_COLLECTIVE_SESSION_ID_ENV: &str = "DREGG_DARK_AMM_COLLECTIVE_SESSION_ID";
/// Nonzero 32-byte hex domain from which the collective hosted-session identity
/// is derived together with the pinned session id and public carrier.
#[cfg(feature = "dark-amm-game")]
pub const DARK_AMM_COLLECTIVE_BASE_SESSION_ENV: &str = "DREGG_DARK_AMM_COLLECTIVE_BASE_SESSION";
/// Public DKG party count and authenticated CRP seed. These reconstruct the
/// exact collective-key identity carried by same-opening receipts.
#[cfg(feature = "dark-amm-game")]
pub const DARK_AMM_COLLECTIVE_PARTIES_ENV: &str = "DREGG_DARK_AMM_COLLECTIVE_PARTIES";
#[cfg(feature = "dark-amm-game")]
pub const DARK_AMM_COLLECTIVE_CRP_SEED_ENV: &str = "DREGG_DARK_AMM_COLLECTIVE_CRP_SEED";
/// Canonical public `DBWCv001` worker configuration signed over by every DKG
/// party artifact. Production bootstrap pins the exact bytes used by the
/// independent decision worker; the table material cannot nominate them.
#[cfg(feature = "dark-amm-game")]
pub const DARK_AMM_COLLECTIVE_WORKER_CONFIG_FILE_ENV: &str =
    "DREGG_DARK_AMM_COLLECTIVE_WORKER_CONFIG_FILE";
/// Comma-separated, party-index-ordered `DBPAv001` public contribution files.
/// The production registrar requires exactly one authenticated artifact per
/// configured DKG party and reproduces the table key from them before boot.
#[cfg(feature = "dark-amm-game")]
pub const DARK_AMM_COLLECTIVE_DKG_ARTIFACT_FILES_ENV: &str =
    "DREGG_DARK_AMM_COLLECTIVE_DKG_ARTIFACT_FILES";
/// Independent FHDAR decision-authority roster. It must contain exactly the DKG
/// party count; its threshold need not equal the Tier-1 issuer threshold.
#[cfg(feature = "dark-amm-game")]
pub const DARK_AMM_DECISION_KEYS_ENV: &str = "DREGG_DARK_AMM_DECISION_PUBLIC_KEYS";
#[cfg(feature = "dark-amm-game")]
pub const DARK_AMM_DECISION_THRESHOLD_ENV: &str = "DREGG_DARK_AMM_DECISION_THRESHOLD";

/// Parse the host-selected exact-opening issuer policy. Both values absent
/// means the stricter operation is deliberately unconfigured; a partial or
/// malformed policy is refused rather than weakened to a default quorum.
#[cfg(feature = "dark-amm-game")]
pub fn dark_amm_authority_from(
    get: impl Fn(&str) -> Option<String>,
) -> Result<Option<(Vec<[u8; 32]>, usize)>, String> {
    quorum_policy_from(
        get,
        DARK_AMM_AUTHORITY_KEYS_ENV,
        DARK_AMM_AUTHORITY_THRESHOLD_ENV,
    )
}

#[cfg(feature = "dark-amm-game")]
pub fn dark_amm_decision_authority_from(
    get: impl Fn(&str) -> Option<String>,
) -> Result<Option<(Vec<[u8; 32]>, usize)>, String> {
    quorum_policy_from(
        get,
        DARK_AMM_DECISION_KEYS_ENV,
        DARK_AMM_DECISION_THRESHOLD_ENV,
    )
}

/// Read and validate the opt-in encrypted Dark Pool deployment key from an
/// env-shaped getter. `Ok(None)` means the feature was deliberately left
/// disabled; a configured but unsafe or invalid key is an error and never
/// silently creates a fresh key (which would strand every persisted session).
#[cfg(feature = "dark-amm-game")]
pub fn dark_amm_key_from(
    get: impl Fn(&str) -> Option<String>,
) -> Result<Option<dreggnet_market::dark_amm_game::DarkAmmHostKeyMaterial>, String> {
    const MAX_KEY_BYTES: u64 = 128 * 1024 * 1024;

    let Some(path) = get(DARK_AMM_SECRET_KEY_FILE_ENV).filter(|path| !path.trim().is_empty())
    else {
        return Ok(None);
    };
    let path = std::path::Path::new(&path);
    let metadata = std::fs::symlink_metadata(path).map_err(|error| {
        format!(
            "cannot inspect {DARK_AMM_SECRET_KEY_FILE_ENV} {}: {error}",
            path.display()
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.file_type().is_file() {
        return Err(format!(
            "{DARK_AMM_SECRET_KEY_FILE_ENV} {} must be a regular, non-symlinked file",
            path.display()
        ));
    }
    if metadata.len() > MAX_KEY_BYTES {
        return Err(format!(
            "{DARK_AMM_SECRET_KEY_FILE_ENV} {} is {} bytes; maximum is {MAX_KEY_BYTES}",
            path.display(),
            metadata.len()
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        let mode = metadata.mode() & 0o777;
        if mode & 0o077 != 0 {
            return Err(format!(
                "{DARK_AMM_SECRET_KEY_FILE_ENV} {} has mode {mode:03o}; remove all group/other permissions",
                path.display()
            ));
        }
    }

    let mut bytes = std::fs::read(path).map_err(|error| {
        format!(
            "cannot read {DARK_AMM_SECRET_KEY_FILE_ENV} {}: {error}",
            path.display()
        )
    })?;
    let parsed =
        dreggnet_market::dark_amm_game::DarkAmmHostKeyMaterial::from_secret_wire_bytes(&bytes)
            .map_err(|error| format!("invalid encrypted Dark Pool deployment key: {error}"));
    bytes.fill(0);
    parsed.map(Some)
}

/// Register the encrypted-amount Dark Pool iff the deployment key env is set
/// and valid. This is intentionally an additive, opt-in registrar: ordinary
/// hosts do not pay for or claim the single-key demo boundary.
#[cfg(feature = "dark-amm-game")]
pub fn register_dark_amm_from(
    host: &mut OfferingHost,
    get: impl Fn(&str) -> Option<String>,
) -> Result<bool, String> {
    let Some(key_material) = dark_amm_key_from(&get)? else {
        return Ok(false);
    };
    let root = get(DARK_AMM_INITIAL_ROOT_ENV)
        .filter(|value| !value.trim().is_empty())
        .map(|value| parse_dark_amm_root(&value))
        .transpose()?;
    let authority = dark_amm_authority_from(|name| get(name))?;
    let offering = match (root, authority) {
        (Some(root), Some((keys, threshold))) => {
            dreggnet_market::dark_amm_game::DarkAmmGameOffering::demo_same_opening_required(
                key_material,
                root,
                keys,
                threshold,
            )
            .map_err(|error| format!("invalid strict-v3 Dark Pool policy: {error}"))?
        }
        (Some(root), None) => {
            dreggnet_market::dark_amm_game::DarkAmmGameOffering::demo_proof_required(
                key_material,
                root,
            )
            .map_err(|error| format!("invalid proof-required Dark Pool root: {error}"))?
        }
        (None, Some(_)) => {
            return Err(format!(
                "{DARK_AMM_AUTHORITY_KEYS_ENV} requires {DARK_AMM_INITIAL_ROOT_ENV}"
            ));
        }
        (None, None) => dreggnet_market::dark_amm_game::DarkAmmGameOffering::demo(key_material),
    };
    host.register(
        dreggnet_market::dark_amm_game::DARK_AMM_OFFERING_KEY,
        "The Dark Bazaar — encrypted constant-product table",
        offering,
    );
    Ok(true)
}

/// Register the actual public-only two-phase collective table. Every required
/// deployment pin is explicit; a partial collective configuration is a boot
/// error rather than a fallback to the single-key offering.
#[cfg(feature = "dark-amm-game")]
pub fn register_collective_dark_amm_from(
    host: &mut OfferingHost,
    get: impl Fn(&str) -> Option<String>,
) -> Result<bool, String> {
    const VALUE_BITS: usize = 19;
    const MAX_PUBLIC_MATERIAL_BYTES: u64 = 256 * 1024 * 1024;

    let Some(path) =
        get(DARK_AMM_COLLECTIVE_MATERIAL_FILE_ENV).filter(|value| !value.trim().is_empty())
    else {
        return Ok(false);
    };
    let required = |name: &'static str| {
        get(name)
            .filter(|value| !value.trim().is_empty())
            .ok_or_else(|| format!("{DARK_AMM_COLLECTIVE_MATERIAL_FILE_ENV} requires {name}"))
    };
    let session_id = required(DARK_AMM_COLLECTIVE_SESSION_ID_ENV)?;
    let base_hosted_session = decode_quorum_key(&required(DARK_AMM_COLLECTIVE_BASE_SESSION_ENV)?)
        .ok_or_else(|| {
        format!("{DARK_AMM_COLLECTIVE_BASE_SESSION_ENV} must be exactly 32 bytes of hex")
    })?;
    let n_parties = required(DARK_AMM_COLLECTIVE_PARTIES_ENV)?
        .parse::<usize>()
        .map_err(|_| format!("{DARK_AMM_COLLECTIVE_PARTIES_ENV} is not a positive integer"))?;
    let crp_seed =
        decode_quorum_key(&required(DARK_AMM_COLLECTIVE_CRP_SEED_ENV)?).ok_or_else(|| {
            format!("{DARK_AMM_COLLECTIVE_CRP_SEED_ENV} must be exactly 32 bytes of hex")
        })?;
    let worker_config_path = required(DARK_AMM_COLLECTIVE_WORKER_CONFIG_FILE_ENV)?;
    let artifact_path_list = required(DARK_AMM_COLLECTIVE_DKG_ARTIFACT_FILES_ENV)?;
    let root = parse_dark_amm_root(&required(DARK_AMM_INITIAL_ROOT_ENV)?)?;
    let (same_opening_keys, same_opening_threshold) =
        dark_amm_authority_from(|name| get(name))?.ok_or_else(|| {
            format!(
                "{DARK_AMM_COLLECTIVE_MATERIAL_FILE_ENV} requires {DARK_AMM_AUTHORITY_KEYS_ENV} and {DARK_AMM_AUTHORITY_THRESHOLD_ENV}"
            )
        })?;
    let (decision_keys, decision_threshold) =
        dark_amm_decision_authority_from(|name| get(name))?.ok_or_else(|| {
            format!(
                "{DARK_AMM_COLLECTIVE_MATERIAL_FILE_ENV} requires {DARK_AMM_DECISION_KEYS_ENV} and {DARK_AMM_DECISION_THRESHOLD_ENV}"
            )
        })?;

    let bytes = read_bounded_collective_public_file(
        DARK_AMM_COLLECTIVE_MATERIAL_FILE_ENV,
        &path,
        MAX_PUBLIC_MATERIAL_BYTES,
    )?;
    let max_config_bytes = u64::try_from(fhegg_fhe::dark_amm_dkg::MAX_COLLECTIVE_DKG_CONFIG_BYTES)
        .map_err(|_| "canonical DKG config bound does not fit u64".to_string())?;
    let worker_config_wire = read_bounded_collective_public_file(
        DARK_AMM_COLLECTIVE_WORKER_CONFIG_FILE_ENV,
        &worker_config_path,
        max_config_bytes,
    )?;
    let artifact_paths = artifact_path_list
        .split(',')
        .map(str::trim)
        .collect::<Vec<_>>();
    if artifact_paths.iter().any(|path| path.is_empty()) {
        return Err(format!(
            "{DARK_AMM_COLLECTIVE_DKG_ARTIFACT_FILES_ENV} must be a comma-separated list without empty paths"
        ));
    }
    if artifact_paths.len() != n_parties {
        return Err(format!(
            "{DARK_AMM_COLLECTIVE_DKG_ARTIFACT_FILES_ENV} requires exactly {n_parties} party-ordered files, got {}",
            artifact_paths.len()
        ));
    }
    let max_artifact_bytes =
        u64::try_from(fhegg_fhe::dark_amm_dkg::MAX_COLLECTIVE_DKG_ARTIFACT_BYTES)
            .map_err(|_| "canonical DKG artifact bound does not fit u64".to_string())?;
    let artifact_wires = artifact_paths
        .iter()
        .map(|artifact_path| {
            read_bounded_collective_public_file(
                DARK_AMM_COLLECTIVE_DKG_ARTIFACT_FILES_ENV,
                artifact_path,
                max_artifact_bytes,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let artifact_wire_refs = artifact_wires.iter().map(Vec::as_slice).collect::<Vec<_>>();
    let params = fhegg_fhe::threshold::BfvParams::fold_set();
    let material =
        fhegg_fhe::dark_amm::DarkPoolPublicHostMaterial::from_wire_bytes(&bytes, params.arc())
            .map_err(|error| format!("invalid collective Dark Pool public material: {error}"))?;
    let keygen = fhegg_fhe::threshold::KeygenSession::from_seed(n_parties, crp_seed)
        .map_err(|error| format!("invalid collective Dark Pool DKG identity: {error:?}"))?;
    let same_opening_verifier = fhegg_fhe::attestation::AuthenticatedQuorumVerifier::new(
        same_opening_keys,
        same_opening_threshold,
    )
    .map_err(|error| format!("invalid Tier-1 same-opening policy: {error}"))?;
    let decision_verifier =
        fhegg_fhe::attestation::AuthenticatedQuorumVerifier::new(decision_keys, decision_threshold)
            .map_err(|error| format!("invalid FHDAR decision policy: {error}"))?;
    let decision_policy = fhegg_fhe::dark_amm_attested::AttestedPrivateDecisionPolicy::new(
        VALUE_BITS,
        params.plaintext_modulus(),
        std::time::Duration::from_secs(5),
        decision_verifier,
    )
    .map_err(|error| format!("invalid FHDAR circuit policy: {error}"))?;
    let session_seed = dreggnet_offerings::seed_from_id(&session_id);
    let offering =
        dreggnet_market::dark_amm_collective::CollectiveDarkAmmOffering::from_authenticated_dkg_artifacts(
            base_hosted_session,
            session_seed,
            params,
            keygen,
            material,
            root,
            same_opening_verifier,
            decision_policy,
            &worker_config_wire,
            &artifact_wire_refs,
        )
        .map_err(|error| format!("invalid collective Dark Pool deployment: {error}"))?;
    host.register(
        dreggnet_market::dark_amm_game::DARK_AMM_OFFERING_KEY,
        "The Dark Bazaar — collective encrypted constant-product table",
        offering,
    );
    Ok(true)
}

#[cfg(feature = "dark-amm-game")]
fn read_bounded_collective_public_file(
    env_name: &str,
    path: &str,
    max_bytes: u64,
) -> Result<Vec<u8>, String> {
    use std::io::Read as _;

    let path = std::path::Path::new(path);
    let metadata = std::fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect {env_name} {}: {error}", path.display()))?;
    if metadata.file_type().is_symlink() || !metadata.file_type().is_file() {
        return Err(format!(
            "{env_name} {} must be a regular, non-symlinked file",
            path.display()
        ));
    }
    let file = std::fs::File::open(path)
        .map_err(|error| format!("cannot open {env_name} {}: {error}", path.display()))?;
    let opened_metadata = file
        .metadata()
        .map_err(|error| format!("cannot inspect open {env_name} {}: {error}", path.display()))?;
    if !opened_metadata.file_type().is_file() || opened_metadata.len() > max_bytes {
        return Err(format!(
            "{env_name} {} is {} bytes; maximum is {max_bytes}",
            path.display(),
            opened_metadata.len()
        ));
    }
    let allocation = usize::try_from(opened_metadata.len())
        .map_err(|_| format!("{env_name} length does not fit this platform"))?;
    let read_limit = max_bytes
        .checked_add(1)
        .ok_or_else(|| format!("{env_name} byte limit overflowed"))?;
    let mut bytes = Vec::with_capacity(allocation);
    file.take(read_limit)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("cannot read {env_name} {}: {error}", path.display()))?;
    let bytes_len = u64::try_from(bytes.len())
        .map_err(|_| format!("{env_name} read length does not fit the canonical u64 bound"))?;
    if bytes_len > max_bytes {
        return Err(format!(
            "{env_name} {} grew beyond the {max_bytes}-byte maximum while being read",
            path.display()
        ));
    }
    Ok(bytes)
}

/// Select exactly one custody mode. Collective public-only material wins only
/// when the legacy secret-key path is absent; configuring both is an error.
#[cfg(feature = "dark-amm-game")]
pub fn register_resolved_dark_amm_from(
    host: &mut OfferingHost,
    get: impl Fn(&str) -> Option<String>,
) -> Result<bool, String> {
    let has_secret =
        get(DARK_AMM_SECRET_KEY_FILE_ENV).is_some_and(|value| !value.trim().is_empty());
    let has_collective =
        get(DARK_AMM_COLLECTIVE_MATERIAL_FILE_ENV).is_some_and(|value| !value.trim().is_empty());
    match (has_secret, has_collective) {
        (true, true) => Err(format!(
            "{DARK_AMM_SECRET_KEY_FILE_ENV} and {DARK_AMM_COLLECTIVE_MATERIAL_FILE_ENV} are mutually exclusive custody modes"
        )),
        (false, true) => register_collective_dark_amm_from(host, get),
        _ => register_dark_amm_from(host, get),
    }
}

#[cfg(feature = "dark-amm-game")]
fn parse_dark_amm_root(value: &str) -> Result<[u32; 8], String> {
    let lanes = value
        .split(',')
        .map(str::trim)
        .map(|lane| {
            lane.strip_prefix("0x")
                .or_else(|| lane.strip_prefix("0X"))
                .map_or_else(|| lane.parse::<u32>(), |hex| u32::from_str_radix(hex, 16))
                .map_err(|_| format!("{DARK_AMM_INITIAL_ROOT_ENV} contains invalid u32 {lane:?}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    lanes.try_into().map_err(|lanes: Vec<u32>| {
        format!(
            "{DARK_AMM_INITIAL_ROOT_ENV} must contain exactly 8 comma-separated lanes, got {}",
            lanes.len()
        )
    })
}

/// **Build the web [`SessionPolicy`] from an env-shaped getter** — the parse seam
/// [`resolve_web_policy`] feeds real env vars through, and tests feed fixed pairs through
/// (process env is global; tests must not mutate it). Unset/empty → `None` (unbounded);
/// unparseable → warn + `None`.
pub fn web_policy_from(get: impl Fn(&str) -> Option<String>) -> SessionPolicy {
    fn parse<T: std::str::FromStr>(name: &str, v: Option<String>) -> Option<T> {
        let v = v?;
        match v.parse::<T>() {
            Ok(n) => Some(n),
            Err(_) => {
                tracing::warn!(%name, value = %v, "unparseable session-policy env — treating as unset");
                None
            }
        }
    }
    SessionPolicy {
        max_sessions_per_offering: parse(WEB_MAX_SESSIONS_ENV, get(WEB_MAX_SESSIONS_ENV)),
        max_opens_per_actor: parse(WEB_OPENS_PER_USER_ENV, get(WEB_OPENS_PER_USER_ENV)),
        idle_ttl_secs: parse(WEB_SESSION_TTL_ENV, get(WEB_SESSION_TTL_ENV)),
        min_open_interval_secs: parse(WEB_MIN_OPEN_INTERVAL_ENV, get(WEB_MIN_OPEN_INTERVAL_ENV)),
        // Set by the host assembly, not the env: lossy eviction is armed exactly when no durable
        // store is attached (see `demo_host_over`).
        evict_unpersisted: false,
    }
}

/// [`web_policy_from`] over the real process environment.
pub fn resolve_web_policy() -> SessionPolicy {
    web_policy_from(|k| std::env::var(k).ok().filter(|v| !v.is_empty()))
}

/// Comma-separated, ordered Ed25519 verifier public keys (64 hex chars each)
/// for the hosted fhEgg settlement operation. The upload never supplies this
/// roster: it is a relying-party deployment policy.
#[cfg(feature = "fhegg-settlement")]
pub const FHEGG_QUORUM_KEYS_ENV: &str = "DREGG_FHEGG_QUORUM_PUBLIC_KEYS";
/// Required signatures from [`FHEGG_QUORUM_KEYS_ENV`].
#[cfg(feature = "fhegg-settlement")]
pub const FHEGG_QUORUM_THRESHOLD_ENV: &str = "DREGG_FHEGG_QUORUM_THRESHOLD";

#[cfg(any(feature = "fhegg-settlement", feature = "dark-amm-game"))]
fn decode_quorum_key(value: &str) -> Option<[u8; 32]> {
    fn nibble(byte: u8) -> Option<u8> {
        match byte {
            b'0'..=b'9' => Some(byte - b'0'),
            b'a'..=b'f' => Some(byte - b'a' + 10),
            b'A'..=b'F' => Some(byte - b'A' + 10),
            _ => None,
        }
    }
    let bytes = value.trim().as_bytes();
    if bytes.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (index, pair) in bytes.chunks_exact(2).enumerate() {
        out[index] = (nibble(pair[0])? << 4) | nibble(pair[1])?;
    }
    Some(out)
}

#[cfg(any(feature = "fhegg-settlement", feature = "dark-amm-game"))]
fn quorum_policy_from(
    get: impl Fn(&str) -> Option<String>,
    keys_env: &'static str,
    threshold_env: &'static str,
) -> Result<Option<(Vec<[u8; 32]>, usize)>, String> {
    let keys = get(keys_env).filter(|value| !value.trim().is_empty());
    let threshold = get(threshold_env).filter(|value| !value.trim().is_empty());
    match (keys, threshold) {
        (None, None) => Ok(None),
        (None, Some(_)) | (Some(_), None) => Err(format!(
            "{keys_env} and {threshold_env} must be set together"
        )),
        (Some(keys), Some(threshold)) => {
            let keys = keys
                .split(',')
                .map(|key| {
                    decode_quorum_key(key)
                        .ok_or_else(|| format!("{keys_env} contains a non-32-byte hex key"))
                })
                .collect::<Result<Vec<_>, _>>()?;
            let threshold = threshold
                .parse::<usize>()
                .map_err(|_| format!("{threshold_env} is not a positive integer"))?;
            if keys.is_empty() || threshold == 0 || threshold > keys.len() {
                return Err(format!(
                    "{threshold_env} must be in 1..={} for the configured roster",
                    keys.len()
                ));
            }
            Ok(Some((keys, threshold)))
        }
    }
}

/// Parse the host-selected fhEgg quorum from an injected env-shaped getter.
/// Both values absent means disabled; a partial or malformed policy is refused
/// as configuration rather than weakened to a smaller/default quorum.
#[cfg(feature = "fhegg-settlement")]
pub fn fhegg_quorum_from(
    get: impl Fn(&str) -> Option<String>,
) -> Result<Option<(Vec<[u8; 32]>, usize)>, String> {
    quorum_policy_from(get, FHEGG_QUORUM_KEYS_ENV, FHEGG_QUORUM_THRESHOLD_ENV)
}

#[cfg(feature = "fhegg-settlement")]
fn demo_host_with_resolved_fhegg() -> OfferingHost {
    let mut host = demo_host();
    match fhegg_quorum_from(|key| std::env::var(key).ok()) {
        Ok(Some((keys, threshold))) => {
            match dreggnet_market::DarkBazaarOffering::with_fhegg_quorum(keys, threshold) {
                Ok(bazaar) => {
                    host.register(
                        dreggnet_market::DarkBazaarOffering::KEY,
                        "The Dark Bazaar — playable CRAWL (sealed bids · verified settlement)",
                        bazaar,
                    );
                    tracing::info!(
                        threshold,
                        "fhEgg settlement operation enabled with host-selected quorum"
                    );
                }
                Err(error) => tracing::error!(
                    error = %error,
                    "fhEgg quorum policy refused; settlement upload remains disabled"
                ),
            }
        }
        Ok(None) => tracing::info!("fhEgg settlement upload disabled — quorum policy env is unset"),
        Err(error) => tracing::error!(
            error = %error,
            "fhEgg quorum policy malformed; settlement upload remains disabled"
        ),
    }
    host
}

#[cfg(feature = "dark-amm-game")]
fn demo_host_with_resolved_dark_amm(mut host: OfferingHost) -> OfferingHost {
    match register_resolved_dark_amm_from(&mut host, |key| std::env::var(key).ok()) {
        Ok(true) => tracing::info!(
            "encrypted Dark Pool enabled — collective public-only custody when configured, otherwise the explicit single-host mode"
        ),
        Ok(false) => {
            tracing::info!(
                "encrypted Dark Pool disabled — neither custody material path is configured"
            )
        }
        Err(error) => tracing::error!(
            error = %error,
            "encrypted Dark Pool key refused; offering remains unregistered (fail-closed)"
        ),
    }
    host
}

/// Production-bundle startup gate. Ordinary opt-in library consumers retain
/// the existing degrade-to-disabled registrar behavior, but the binary built
/// with `public-shielded-games` must not report healthy after a configured
/// verifier/key surface failed to instantiate.
///
/// Missing configuration still means deliberately disabled. Once either half
/// of a protected operation is present, however, the complete pair and its
/// cryptographic material must validate before the server binds a socket.
#[cfg(feature = "public-shielded-games")]
pub fn validate_public_shielded_deployment_from(
    get: impl Fn(&str) -> Option<String>,
) -> Result<(), String> {
    match fhegg_quorum_from(|name| get(name))? {
        Some((keys, threshold)) => {
            dreggnet_market::DarkBazaarOffering::with_fhegg_quorum(keys, threshold)
                .map_err(|error| format!("fhEgg settlement quorum refused: {error}"))?;
        }
        None => {}
    }

    let present = |name: &str| get(name).is_some_and(|value| !value.trim().is_empty());
    let dark_key = present(DARK_AMM_SECRET_KEY_FILE_ENV);
    let collective_material = present(DARK_AMM_COLLECTIVE_MATERIAL_FILE_ENV);
    if dark_key && collective_material {
        return Err(format!(
            "{DARK_AMM_SECRET_KEY_FILE_ENV} and {DARK_AMM_COLLECTIVE_MATERIAL_FILE_ENV} are mutually exclusive custody modes"
        ));
    }
    if dark_key {
        if ![
            DARK_AMM_INITIAL_ROOT_ENV,
            DARK_AMM_AUTHORITY_KEYS_ENV,
            DARK_AMM_AUTHORITY_THRESHOLD_ENV,
        ]
        .into_iter()
        .all(&present)
        {
            return Err(format!(
                "{DARK_AMM_SECRET_KEY_FILE_ENV}, {DARK_AMM_INITIAL_ROOT_ENV}, {DARK_AMM_AUTHORITY_KEYS_ENV}, and {DARK_AMM_AUTHORITY_THRESHOLD_ENV} must be set together in the public shielded deployment (strict v3; refusing proof-only v2)"
            ));
        }
    } else if !collective_material {
        let stray = [
            DARK_AMM_INITIAL_ROOT_ENV,
            DARK_AMM_AUTHORITY_KEYS_ENV,
            DARK_AMM_AUTHORITY_THRESHOLD_ENV,
            DARK_AMM_COLLECTIVE_SESSION_ID_ENV,
            DARK_AMM_COLLECTIVE_BASE_SESSION_ENV,
            DARK_AMM_COLLECTIVE_PARTIES_ENV,
            DARK_AMM_COLLECTIVE_CRP_SEED_ENV,
            DARK_AMM_COLLECTIVE_WORKER_CONFIG_FILE_ENV,
            DARK_AMM_COLLECTIVE_DKG_ARTIFACT_FILES_ENV,
            DARK_AMM_DECISION_KEYS_ENV,
            DARK_AMM_DECISION_THRESHOLD_ENV,
        ]
        .into_iter()
        .find(|name| present(name));
        if let Some(name) = stray {
            return Err(format!(
                "{name} is set without either {DARK_AMM_SECRET_KEY_FILE_ENV} or {DARK_AMM_COLLECTIVE_MATERIAL_FILE_ENV}"
            ));
        }
        return Ok(());
    }
    let mut host = OfferingHost::new();
    if !register_resolved_dark_amm_from(&mut host, |name| get(name))? {
        return Err("configured proof-required Dark AMM was not registered".to_string());
    }
    Ok(())
}

/// Environment-backed form used by the production server entrypoint.
#[cfg(feature = "public-shielded-games")]
pub fn validate_public_shielded_deployment() -> Result<(), String> {
    validate_public_shielded_deployment_from(|name| std::env::var(name).ok())
}

fn ephemeral_game_epochs() -> GameEpochLedger {
    GameEpochLedger::in_memory_random()
        .expect("the operating-system RNG must mint a nonzero game-host incarnation")
}

fn random_game_form_key() -> [u8; 32] {
    let mut key = [0; 32];
    getrandom::fill(&mut key).expect("operating-system RNG must mint the game form MAC key");
    key
}

/// Resolve the web catalog's game-route authority. When session persistence is
/// armed this is a required sibling store, not a best-effort cache: losing or
/// corrupting it would make old game commands indistinguishable from a fresh
/// host/session generation, so startup fails closed.
fn resolve_game_epochs(session_dir: Option<&std::path::Path>) -> GameEpochLedger {
    match session_dir {
        Some(session_dir) => {
            GameEpochLedger::open(session_dir.join("game-epochs")).unwrap_or_else(|error| {
                panic!(
                    "durable web game-epoch custody at {} refused: {error}",
                    session_dir.join("game-epochs").display()
                )
            })
        }
        None => ephemeral_game_epochs(),
    }
}

/// **Resolve the demo host from the environment** — the session-durability switch, mirroring
/// [`resolve_demo_descent`], PLUS the session-lifecycle policy ([`resolve_web_policy`]: capacity /
/// TTL / per-user quota / open rate). With `DREGGNET_WEB_SESSION_DIR` set (non-empty), the host is
/// built over a durable [`FileResumeStore`] rooted there: live game sessions survive a restart by
/// move-log replay, and lifecycle eviction is SAFE (an evicted session resumes on its next touch).
/// Unset → the store-less host; with every policy env also unset this is byte-identical to the
/// pre-lifecycle behavior (nothing attached, nothing tracked — the committed tests' path).
pub fn resolve_demo_host() -> OfferingHost {
    let dir = std::env::var("DREGGNET_WEB_SESSION_DIR")
        .ok()
        .filter(|d| !d.is_empty())
        .map(std::path::PathBuf::from);
    #[cfg(feature = "fhegg-settlement")]
    let base = demo_host_with_resolved_fhegg();
    #[cfg(not(feature = "fhegg-settlement"))]
    let base = demo_host();
    #[cfg(feature = "dark-amm-game")]
    let base = demo_host_with_resolved_dark_amm(base);
    assemble_demo_host(base, dir, resolve_web_policy())
}

/// **Resolve the per-identity RPG worlds registry** from the environment — the per-player half of
/// the catalog (the eight [`is_rpg_key`] surfaces). With `DREGGNET_WEB_SESSION_DIR` set, each
/// identity's world attaches a durable [`FileResumeStore`] under a PER-IDENTITY subdirectory
/// (`<dir>/players/<blake3(identity)>`), so a player's forge / inventory / trade survive a restart
/// by move-log replay — the same durability the shared game sessions get, and the same per-player
/// scoping Discord's `SqliteRpgResumeStore` gives (there by SQL row, here by directory). The
/// subdirectory is the ONE thing the isolation guarantee rests on: no identity's host ever sees
/// another's logs. Unset (or an unopenable dir) → that world stays in memory. Built on the
/// player-worlds owning thread ([`PlayerHostThread::spawn`]).
pub fn resolve_player_worlds() -> PlayerWorlds {
    let root = std::env::var("DREGGNET_WEB_SESSION_DIR")
        .ok()
        .filter(|d| !d.is_empty())
        .map(std::path::PathBuf::from);
    let Some(root) = root else {
        return PlayerWorlds::new();
    };
    let players_root = root.join("players");
    PlayerWorlds::with_store(move |identity| {
        // A per-identity subdirectory, named by a hash of the identity so any identity string maps
        // to a safe, collision-resistant directory (identities are hex today, but this stays robust).
        let sub = players_root.join(blake3::hash(identity.as_bytes()).to_hex().as_str());
        match FileResumeStore::open(&sub) {
            Ok(store) => {
                Some(Box::new(store) as Box<dyn dreggnet_offerings::resume::SessionResumeStore>)
            }
            Err(e) => {
                tracing::warn!(
                    dir = %sub.display(),
                    error = %e,
                    "could not open a per-identity RPG world store — that world stays in-memory"
                );
                None
            }
        }
    })
}

/// **The demo host over a durable session store at `dir`** — the restart-survival weld, with no
/// lifecycle policy armed (unbounded — the committed suites' path). See [`demo_host_over`].
pub fn demo_host_resumed_from(dir: impl Into<std::path::PathBuf>) -> OfferingHost {
    demo_host_over(Some(dir.into()), SessionPolicy::default())
}

/// **Assemble the demo host** over an optional durable session dir and a [`SessionPolicy`]:
///
/// - the policy is armed FIRST (with the wall-clock [`SystemClock`] — time is injected, and the
///   boot resume below then stamps every resumed session as touched);
/// - **lossy eviction is armed exactly when no store is attached**: a store-less deployment's
///   sessions are ephemeral anyway (a restart drops them all), so shedding the coldest under a
///   cap/TTL beats unbounded growth — while with a store attached eviction stays LOSSLESS (the
///   durable move-log resumes on next touch) and `evict_unpersisted` stays off;
/// - with a dir: opens a [`FileResumeStore`] rooted there, attaches it
///   ([`OfferingHost::with_resume_store`], so every session open + landed advance + signed-replay
///   floor is written through), and boot-resumes every persisted move-log
///   ([`OfferingHost::resume_all`]) — each live session reopens to its identical committed state
///   by replay. Fail-closed on both edges:
///   - a **tampered** log is refused on re-drive ([`dreggnet_offerings::ResumeError::Refused`]) —
///     logged and left refused; its file is NOT deleted (the evidence stays on disk);
///   - an **unopenable** `dir` logs a warning and falls back to the store-less host (the server
///     still boots, sessions stay in-memory) — the same degrade-not-refuse posture as
///     [`resolve_demo_descent`].
pub fn demo_host_over(dir: Option<std::path::PathBuf>, policy: SessionPolicy) -> OfferingHost {
    assemble_demo_host(demo_host(), dir, policy)
}

fn assemble_demo_host(
    base: OfferingHost,
    dir: Option<std::path::PathBuf>,
    mut policy: SessionPolicy,
) -> OfferingHost {
    if dir.is_none() && !policy.is_unbounded() {
        policy.evict_unpersisted = true;
        tracing::info!(
            "session policy armed with NO durable store — lossy eviction on (sessions are \
             ephemeral either way; shedding the coldest beats unbounded growth)"
        );
    }
    let mut host = base.with_policy(policy, SystemClock);
    let Some(dir) = dir else {
        return host;
    };
    match FileResumeStore::open(&dir) {
        Ok(store) => {
            host = host.with_resume_store(Box::new(store));
            let results = host.resume_all();
            let resumed = results.iter().filter(|(_, r)| r.is_ok()).count();
            let refused = results.len() - resumed;
            tracing::info!(
                dir = %dir.display(),
                resumed,
                refused,
                "session store attached — persisted game sessions resumed by move-log replay"
            );
            for (log, outcome) in &results {
                if let Err(e) = outcome {
                    metrics::inc_resume_failure();
                    tracing::warn!(
                        key = %log.key,
                        id = %log.id.0,
                        error = %e,
                        "a persisted session log refused to reopen (fail-closed); its file is kept"
                    );
                }
            }
        }
        Err(e) => {
            tracing::warn!(
                dir = %dir.display(),
                error = %e,
                "could not open DREGGNET_WEB_SESSION_DIR — sessions stay in-memory (ephemeral)"
            );
        }
    }
    host
}

/// **The seeded no-cheat Descent leaderboard state** for the demo — opens TODAY'S day (the one
/// [`descent::todays_day`] resolves, which is the same day the Discord bot plays and submits
/// against) and ingests a real, driven-to-the-hoard
/// winning run PLUS a forged one. Both are UNTRUSTED records; the leaderboard re-verifies each on
/// render, so the honest winner ranks and the forgery is excluded (`GET /descent/leaderboard`), and
/// the forgery's run-card shows FAIL (`GET /descent/run/demo-forgery`). This is the growth artifact
/// a stranger opens and independently re-verifies — node-free, by replay.
pub fn demo_descent_state() -> Arc<DescentState> {
    build_demo_descent(None)
}

/// **Build the seeded demo Descent state**, optionally over a durable [`DescentRunStore`]. When a
/// store is given: first [`load_from_store`](DescentState::load_from_store) reconstructs +
/// re-verifies whatever survived a previous run (so real submitted runs SURVIVE a restart), then the
/// demo day + honest winner are (idempotently) opened + submitted THROUGH the verify-gate
/// ([`submit_run`](DescentState::submit_run), which also persists). The forged run is ingested RAW
/// (in-RAM only, never persisted — it is a teaching artifact whose run-card shows FAIL by
/// re-execution; it would never survive the verify-gate anyway).
///
/// [`DescentRunStore`]: descent_store::DescentRunStore
pub fn build_demo_descent(
    store: Option<Arc<dyn descent_store::DescentRunStore>>,
) -> Arc<DescentState> {
    use dreggnet_offerings::DreggIdentity;
    use dreggnet_offerings::character::InMemoryCharacterStore;
    use dreggnet_offerings::daily_descent::{DailyDescentOffering, GATE_RECKLESS};

    // TODAY'S REAL WORLD, not a hardcoded demo epoch. This board used to open
    // `daily_seed(&[3; 32])` — a fixed fixture day — while the Discord bot played the day
    // `procgen_dregg::descent_day` resolves. Two different worlds: the bot's submitted moves could
    // never re-execute here, so `ranked` was always false and the share link never emitted. Now
    // both processes resolve their day through the SAME `procgen_dregg::descent_day` helper — the
    // web from the beacon it arms at boot + hourly (`arm_todays_descent_day` →
    // `descent::todays_day`), the bot from its reveal cron — so when both are online they open the
    // byte-identical beacon world, and when neither has a round they open the identical offline day.
    let seed = crate::descent::todays_day().seed;
    let (win_moves, win_level, win_class) = demo_win_for_seed(seed);
    let off = DailyDescentOffering::new(InMemoryCharacterStore::new());
    let mut win = off
        .open_from_seed(DreggIdentity("ember".to_string()), seed)
        .expect("today's descent opens");
    // Re-drive the recorded winning playthrough (for the forged-run teaching artifact below).
    for &ci in &win_moves {
        if !off.advance(&mut win, ci).landed() {
            break;
        }
    }
    // A FORGED run — swap the opening measured blow for a reckless one; the recorded chain no
    // longer replays, so it is excluded from the board and its run-card shows FAIL.
    let mut forged = win.playthrough();
    if let Some(first) = forged.steps.first_mut() {
        first.choice_index = GATE_RECKLESS;
    }

    let base = match store {
        Some(s) => DescentState::with_store(s),
        None => DescentState::new(),
    };
    // THE DEVNET SWITCH: `DREGG_NODE_URL` set → anchor submitted runs on that running node's ledger
    // (a real committed turn on-chain); unset → `NodeTarget::Local` (the in-process default — the
    // committed tests + node-free demo are byte-identical). See [`resolve_node_target`].
    let state = Arc::new(base.with_node_target(resolve_node_target()));
    // Reconstruct + re-verify anything persisted from a previous run (a no-op with no store).
    state.load_from_store();
    // The demo day + the honest winner (idempotent; verify-gated + persisted with a store).
    state.open_day("today", seed);
    let _ = state.submit_run(
        "today",
        "demo-ember",
        "ember",
        win_level,
        win_class,
        &win_moves,
    );
    // The forged run — ingested RAW (in-RAM only) so its run-card demonstrates FAIL by re-execution.
    state.ingest_run("today", "demo-forgery", "a-forger", 1, 0, forged);
    state
}

/// **Drive the honest demo winning line** — the choice-index sequence that provably reaches the
/// hoard on TODAY'S real day ([`descent::todays_day`]), plus the winner's character level + class. The
/// same careful line `dreggnet-offerings`' own driven board test uses (works for any beacon-drawn
/// warden HP / depth). Exposed so the demo state and the persistence/ingest tests share ONE source
/// of the winning moves.
pub fn demo_win() -> (Vec<usize>, u64, u64) {
    demo_win_for_seed(crate::descent::todays_day().seed)
}

/// Derive the same world-adaptive winning line as [`demo_win`], but for an
/// explicit committed seed. Tests and devnet tooling use this form so the move
/// generator and the opened world cannot drift across a day boundary.
pub fn demo_win_for_seed(seed: procgen_dregg::CommittedSeed) -> (Vec<usize>, u64, u64) {
    use dreggnet_offerings::DreggIdentity;
    use dreggnet_offerings::character::InMemoryCharacterStore;
    use dreggnet_offerings::daily_descent::{
        CORRIDOR_ON, DailyDescentOffering, GATE_HEAL, GATE_MEASURED, GATE_PRESS, HOARD_FORCE,
        HOARD_SEIZE, KEY_TAKE,
    };

    // The line is world-agnostic: it reads the live room + vitals at each step,
    // so it reaches the hoard for any committed-seed warden HP / depth.
    let off = DailyDescentOffering::new(InMemoryCharacterStore::new());
    let mut run = off
        .open_from_seed(DreggIdentity("ember".to_string()), seed)
        .expect("today's descent opens");
    let mut moves = Vec::new();
    for _ in 0..64 {
        let Some(room) = run.current_room() else {
            break;
        };
        let ci = match room.as_str() {
            "gate" => {
                if run.read_var("warden_hp") == 0 {
                    GATE_PRESS
                } else if run.read_var("hp") >= 16 {
                    GATE_MEASURED
                } else {
                    GATE_HEAL
                }
            }
            "keyroom" => KEY_TAKE,
            "hoardgate" => HOARD_FORCE,
            "hoard" => HOARD_SEIZE,
            r if r.starts_with("corridor") => CORRIDOR_ON,
            _ => break,
        };
        if !off.advance(&mut run, ci).landed() {
            break;
        }
        moves.push(ci);
    }
    (moves, run.character().level(), run.character().class())
}

/// **Assemble the merged public-demo app** — the ONE `Router<()>` the server bin serves. Merges,
/// with no route overlap:
/// - `GET /` — a landing page linking the surfaces;
/// - `GET /health` — a liveness probe (200 `{"status":"ok"}`) for the fronting proxy / uptime check;
/// - [`router`] — the single-offering session surface (`/session/{id}` …);
/// - [`catalog_router`] over [`demo_host`] — the shared full portfolio (`/offerings` …);
/// - [`descent_router`] over [`demo_descent_state`] — the seeded no-cheat Descent leaderboard
///   (`/descent/leaderboard`, `/descent/run/{id}`).
///
/// Factored out of the bin so it is drivable in tests with no real network (axum `oneshot`).
///
/// **Persistence.** The Descent leaderboard is durable when a `DATABASE_URL` is set (a sqlite path
/// / `sqlite:` url; see [`resolve_demo_descent`]): submitted runs survive a restart, re-verified by
/// replay on boot. The live game sessions are durable when `DREGGNET_WEB_SESSION_DIR` is set (a
/// directory; see [`resolve_demo_host`]): each session's move-log persists to a
/// [`FileResumeStore`] and every session resumes on boot by replay — a tampered log refuses to
/// reopen. With both unset (the committed tests' path) everything is in-RAM — nothing persists, so
/// the existing suite is unaffected. To serve a specific pre-built descent state (e.g. a test's
/// sqlite store), use [`make_app_with_descent`].
pub fn make_app() -> Router {
    make_app_with_descent(resolve_demo_descent())
}

/// [`make_app`], also handing back the [`CatalogState`] handle — what the server bin needs to
/// drive the periodic lifecycle [`sweep`](CatalogState::sweep) beside the served router (the
/// no-traffic idle-eviction case; the host also sweeps opportunistically on each fresh open).
pub fn make_app_parts() -> (Router, Arc<CatalogState>) {
    make_app_parts_with_descent(resolve_demo_descent())
}

/// [`make_app`] over a caller-supplied [`DescentState`] (the games + catalog + single-offering
/// surfaces are unchanged). Lets a deployment / a test wire its own — durable or in-RAM — Descent
/// board while reusing the whole merged app.
pub fn make_app_with_descent(descent: Arc<DescentState>) -> Router {
    make_app_parts_with_descent(descent).0
}

/// [`make_app_with_descent`], also handing back the [`CatalogState`] handle (see
/// [`make_app_parts`]).
pub fn make_app_parts_with_descent(descent: Arc<DescentState>) -> (Router, Arc<CatalogState>) {
    // OBSERVABILITY — install the process-global Prometheus recorder (idempotent) BEFORE the
    // catalog host builds, so its boot-resume refusals are already counted. `/metrics` is
    // DELIBERATELY NOT mounted on this app: it is served on a SEPARATE loopback listener
    // ([`metrics_app`] + the bin's metrics port) so a public `tailscale funnel` of the main port
    // can never expose the operational counters. The recorder is installed here regardless — the
    // emit sites are no-ops until it exists, and this is the earliest point that covers boot.
    let _ = metrics::install_recorder();

    // The session-durability + lifecycle weld: `DREGGNET_WEB_SESSION_DIR` set → the catalog host
    // is built over a durable `FileResumeStore` and boot-resumes persisted sessions; the
    // `DREGGNET_WEB_MAX_SESSIONS` / `DREGGNET_WEB_SESSION_TTL_SECS` / `DREGGNET_WEB_OPENS_PER_USER`
    // / `DREGGNET_WEB_MIN_OPEN_INTERVAL_SECS` envs arm the session policy (all unset → unbounded,
    // byte-identical). See `resolve_demo_host`.
    // Both halves are env-resolved + durable: the shared host resumes its game/service sessions,
    // and the per-identity RPG worlds each resume from their own per-player store (so an
    // inventory/forge survives a restart exactly as Discord's per-player worlds do). See
    // `resolve_demo_host` / `resolve_player_worlds`.
    let game_epoch_dir = std::env::var("DREGGNET_WEB_SESSION_DIR")
        .ok()
        .filter(|dir| !dir.is_empty())
        .map(std::path::PathBuf::from);
    let catalog = Arc::new(CatalogState::with_hosts_and_game_epochs(
        resolve_demo_host,
        resolve_player_worlds,
        resolve_game_epochs(game_epoch_dir.as_deref()),
    ));

    make_app_parts_with_catalog(descent, catalog)
}

/// Build the complete server router over an explicitly configured private
/// Bazaar deployment. Its ordinary catalog GET/POST routes become the public
/// lifecycle; the returned `CatalogState` retains the exact worker registry and
/// durable XP adapter. This is opt-in because no safe roster/reward/executor
/// policy can be synthesized by the web server.
#[cfg(feature = "private-bazaar-live")]
pub fn make_app_parts_with_private_bazaar(
    descent: Arc<DescentState>,
    deployment: dreggnet_catalog::PrivateBazaarLiveDeployment,
    characters: dreggnet_catalog::PrivateBazaarCharacterStore,
) -> (Router, Arc<CatalogState>) {
    let _ = metrics::install_recorder();
    let session_dir = std::env::var("DREGGNET_WEB_SESSION_DIR")
        .ok()
        .filter(|dir| !dir.is_empty())
        .map(std::path::PathBuf::from);
    let catalog = Arc::new(CatalogState::with_private_bazaar_over(
        deployment,
        characters,
        session_dir,
        resolve_web_policy(),
    ));
    make_app_parts_with_catalog(descent, catalog)
}

// ═════════════════════════════════════════════════════════════════════════════════════════
// THE STATIC-ASSET TRANSPORT POLICY — what the play surface's build artifacts cost a visitor.
//
// `GET /descent/play` is the hero CTA, and the bundle behind it is the single largest object on
// the product: 58 MiB of wasm, re-read from disk and re-sent in full on every visit, because the
// merged app had no compression layer and the blob route sets only a Content-Type. That is the
// whole page weight of the flagship, paid again by every visitor and every re-visit.
//
// Two layers fix it WITHOUT touching a single route handler:
//
//   * `CompressionLayer` (wired in `make_app_parts_with_catalog`) negotiates the response encoding.
//     Measured on the committed bundle: `br` 61,108,004 -> 3,738,736 (16.3x), `gzip` -> 7,260,338
//     (8.4x). Browsers offer `br` first, so the realistic first visit falls from 58 MiB to 3.6 MiB.
//   * the revalidation middleware below gives those artifacts an `ETag` + `Cache-Control`, so the
//     SECOND visit costs either nothing (inside the freshness window) or a bodiless `304`.
//
// Compression alone would still re-send 3.6 MiB per visit; caching alone would still cost 58 MiB
// on the first. Both together are what makes the CTA cheap.

/// How long a browser may reuse a play-surface build artifact without asking again.
///
/// Deliberately **not** `immutable`, and deliberately not a year — the difference matters and the
/// codebase already has the honest version of both idioms. `immutable` is a promise that the bytes
/// at a URL never change, and it is only truthful behind a content-addressed name: `sprite`'s
/// `/sprite/{kind}/{hex}` earns it (the blake3 IS the url), and `automatafl_web`'s hero earns it
/// (`include_bytes!`, so the bytes change only when the binary does).
/// `/descent/play/static/dregg_wasm_bg.wasm` earns neither: it is a FIXED path whose bytes are
/// re-read from disk per request, so a `wasm-pack` rebuild silently changes them under a name a
/// browser was told to trust forever — and a year-long `immutable` on a stale bundle is not
/// recoverable from the server side.
///
/// An hour of silence plus revalidation is the honest trade: within the window the browser does not
/// ask at all, and after it the conditional GET returns a `304` with no body, so a returning
/// visitor never pays the bundle twice. A content-hashed URL is the real fix and would let this be
/// `immutable`; that requires changing the blob route itself, which this layer deliberately does
/// not touch.
const PLAY_STATIC_CACHE_CONTROL: &str = "public, max-age=3600";

/// The negotiated-encoding quality, set EXPLICITLY because the library default is unusable here.
///
/// `CompressionLayer`'s default is `Level::Default`, which brotli defines as quality **11** — its
/// maximum. Measured on the committed 61,108,004-byte bundle (2026-07-25):
///
/// | quality | wire bytes | CPU per compression |
/// |---------|-----------:|--------------------:|
/// | 11 (lib default) | 2,753,890 | **307 s** |
/// | 5  | 3,439,988 | 3.3 s |
/// | 4 (chosen) | 3,738,736 | 3.0 s |
///
/// Quality 11 buys 26% off the wire for a HUNDRED-FOLD increase in CPU — five minutes of a pinned
/// core per compression, which is a far worse outage than the 58 MiB it set out to fix, and trivially
/// self-inflicted by a handful of simultaneous visitors following the same posted link. Quality 4 is
/// the standard choice for compressed-on-demand content for exactly this reason, and it still carries
/// the bundle at 16.3x.
///
/// This applies to every response, not just the bundle: on the catalog's HTML pages the difference
/// between 4 and 11 is a few percent of a few kilobytes and microseconds either way, so the small
/// responses lose nothing by being priced for the large one.
///
/// **The residual, stated plainly:** 3 s of CPU is still paid per COLD client, because this layer
/// compresses on the fly and holds nothing. The revalidation layer above keeps returning visitors off
/// that path entirely (they get a bodiless `304`), but a launch that puts this link in front of many
/// first-time visitors at once is still buying ~3 CPU-seconds each. The architecturally right answer
/// for an artifact this size is to compress it ONCE at build time and serve the stored
/// `dregg_wasm_bg.wasm.br` directly — which is a change to the blob route itself, not to a layer.
const PLAY_COMPRESSION_QUALITY: i32 = 4;

/// Is this path one of the play surface's immutable-per-build artifacts?
///
/// Everything under `/descent/play/static/` is generated by the `wasm-pack` step — the wasm bundle,
/// its glue, the bootstrap/action modules, and wasm-bindgen's generated snippets — EXCEPT
/// `day.json`, which is today's committed day descriptor and sets its own `no-store` (a cached one
/// would pin a stale day, which its own test asserts against). The exclusion is by name rather than
/// by an allowlist of the other five so that a newly vendored artifact is cached by default and
/// only the genuinely dynamic descriptor is opted out.
fn play_static_is_revalidatable(path: &str) -> bool {
    path.strip_prefix("/descent/play/static/")
        .is_some_and(|artifact| artifact != "day.json")
}

/// Attach an `ETag` + `Cache-Control` to the play surface's build artifacts, and answer a matching
/// `If-None-Match` with a bodiless `304 Not Modified`.
///
/// The validator is **weak** (`W/"…"`) on purpose. This middleware runs INSIDE the
/// `CompressionLayer`, so it hashes the identity representation while the client may receive the
/// `br`/`gzip`/`zstd` one. A strong validator must identify one exact octet sequence and would be a
/// lie across those encodings; a weak one asserts semantic equivalence, which is exactly true here,
/// and `If-None-Match` is defined to use weak comparison. Hashing the identity bytes also keeps the
/// validator stable for a client whose `Accept-Encoding` changes between visits.
async fn revalidate_play_static(
    request: axum::extract::Request,
    next: middleware::Next,
) -> Response {
    // GET only, and the method check is load-bearing rather than defensive. axum answers `HEAD` on a
    // `get` route by running the handler and then emptying the body in `routing/route.rs` — INSIDE
    // the router, i.e. BELOW this layer. So on a `HEAD` the body reaching here is already gone, and
    // hashing it would mint the validator for the empty string: one identical, wrong `ETag` on every
    // route, contradicting the one the same URL hands a `GET`. Uptime monitors are exactly the
    // clients that send `HEAD`, so this is a real path, not a hypothetical one. There is no correct
    // validator to compute here, so this attaches none.
    if request.method() != axum::http::Method::GET
        || !play_static_is_revalidatable(request.uri().path())
    {
        return next.run(request).await;
    }
    let requested = request.headers().get(header::IF_NONE_MATCH).cloned();
    let response = next.run(request).await;
    // Only a served artifact is a cacheable representation. The blob route answers an absent
    // bundle with an honest `503` naming the `wasm-pack` step; caching that would outlive the
    // deployment mistake it reports.
    if response.status() != StatusCode::OK {
        return response;
    }

    let (mut parts, body) = response.into_parts();
    // These bodies are already whole in memory — each one is a `Vec<u8>` from `read_play_asset`'s
    // `std::fs::read`, never a streamed or client-supplied body — so collecting is a concatenation
    // of one chunk, not an unbounded buffer over untrusted input.
    let Ok(bytes) = axum::body::to_bytes(body, usize::MAX).await else {
        return (
            StatusCode::INTERNAL_SERVER_ERROR,
            "The Descent play artifact could not be read back for validation.\n",
        )
            .into_response();
    };
    let etag = format!("W/\"{}\"", blake3::hash(&bytes).to_hex());
    let Ok(etag_value) = axum::http::HeaderValue::from_str(&etag) else {
        return (parts, bytes).into_response();
    };
    parts.headers.insert(header::ETAG, etag_value.clone());
    // Never overwrite a route that already stated its own policy — `no-store` on a dynamic
    // descriptor must win over a blanket freshness window.
    if !parts.headers.contains_key(header::CACHE_CONTROL) {
        parts.headers.insert(
            header::CACHE_CONTROL,
            axum::http::HeaderValue::from_static(PLAY_STATIC_CACHE_CONTROL),
        );
    }

    if requested.is_some_and(|header| if_none_match_matches(&header, &etag)) {
        parts.status = StatusCode::NOT_MODIFIED;
        // A 304 carries the validator and the freshness policy, and no body — which is the whole
        // point: the repeat visit costs headers instead of the bundle.
        parts.headers.remove(header::CONTENT_LENGTH);
        parts.headers.remove(header::CONTENT_TYPE);
        return (parts, axum::body::Body::empty()).into_response();
    }
    (parts, bytes).into_response()
}

/// Does an `If-None-Match` header field match our validator? Handles the wildcard and the
/// comma-separated list form, and compares weakly (`W/"x"` and `"x"` identify the same
/// representation for a conditional GET), per the `If-None-Match` definition.
fn if_none_match_matches(requested: &axum::http::HeaderValue, etag: &str) -> bool {
    let Ok(requested) = requested.to_str() else {
        return false;
    };
    let opaque = |tag: &str| tag.trim().trim_start_matches("W/").trim().to_owned();
    let ours = opaque(etag);
    requested.trim() == "*"
        || requested
            .split(',')
            .any(|candidate| opaque(candidate) == ours)
}

fn make_app_parts_with_catalog(
    descent: Arc<DescentState>,
    catalog: Arc<CatalogState>,
) -> (Router, Arc<CatalogState>) {
    let web = Arc::new(WebState::new());

    // THE CROWD-STREAM OVERLAY (docs/CROWD-STREAM-ENGINE-DESIGN.md) — the transparent OBS vote
    // overlay + its server→browser SSE tally push (`GET /overlay`, `GET /overlay/sse`,
    // `POST /overlay/ingest[/youtube]`), gated behind the operator bearer `OVERLAY_INGEST_TOKEN`
    // (unset ⇒ fail-closed). Two mounts, chosen by `OVERLAY_LIVE_WORLD` (env-gated):
    //   * unset (default) → a tally board over the keep round, honestly labeled "no world resolve";
    //   * set → a LIVE demo Warden's Keep the crowd STEERS — its `LiveCloseLoop` drives
    //     `OverlayState::drive_close` on an `OVERLAY_ROUND_SECONDS`-second `tokio::time::interval`,
    //     so on a running server each window ingests → tallies → resolves the quorum-certified
    //     winner into the world as ONE real certified TurnReceipt → pushes the reset tally over SSE.
    // Certified = quorum-certified + executor-admitted, NOT FRI-sound-on-chain; the world is a demo.
    let (overlay_router, overlay_live) = overlay::overlay_mount_from_env();

    let app = Router::new()
        .route("/", get(index))
        .route("/health", get(health))
        .merge(router(web))
        .merge(catalog_router(Arc::clone(&catalog)))
        .merge(descent_router(Arc::clone(&descent)))
        // ⚑ THE YOU PAGE — `GET /you` (and `/me`): the one surface that answers "where do I see my
        // own games?". It was missing entirely, which is why a player who closed the tab could not
        // find their table and could not see their own row's history on the daily board. Reads the
        // two stores that already hold that record (the catalog host's live sessions + move logs,
        // and the Descent board), joins them to the viewer by the seat lock / the logged actor / an
        // EXACT label match, and refuses an asserted `?user=` outright. Additive — `/you` and `/me`
        // overlap nothing above.
        .merge(you::you_router(Arc::clone(&catalog), descent))
        // THE PLAYABLE web front door (backlog H1): `GET /descent/play` serves an in-tab
        // same-origin DOM controller over the Lean-native `NativeDescentWorld` (via the wasm
        // `bindings_native_descent` executor), NOT the `<dregg-descent>` element. State-free +
        // additive; no route overlap with `descent_router`'s board/run/submit surface.
        .merge(descent_play::descent_play_router())
        // THE AUTOMATAFL FRONT DOOR — `GET /automatafl` (the rules + the CTA), `POST
        // /automatafl/table` (mint a seat-locked table + its two unguessable seat links), `GET
        // /automatafl/table/{id}` (take a seat), `GET /automatafl/watch/{id}` (spectate the fogged
        // board, controls disabled). Additive; the play itself still happens on the catalog's own
        // `/offerings/automatafl/session/{id}` surface.
        .merge(automatafl_web::automatafl_router(Arc::clone(&catalog)))
        // THE MULTIWAY-TUG FRONT DOOR — the same door, the same seat discipline, new prefixes:
        // `GET /tug`, `POST /tug/table` (mint `tug1-…` + two secret seat links), `GET
        // /tug/table/{id}` (take a seat), `POST /tug/table/{id}/resign`, `GET /tug/watch/{id}`
        // (spectate with BOTH hands fogged). This replaces the one global `tug-web` table the
        // catalog page used to point every visitor at.
        .merge(tug_web::tug_router(Arc::clone(&catalog)))
        // HOW TO PLAY — `GET /guide` (+ the `/how-to-play` alias a stranger is as likely to type).
        // The one page that starts from zero: what the surface is in words a newcomer already owns,
        // the two things we are not good at yet, then the three games. Additive + state-free; every
        // game landing keeps its own rules panel, which this does not replace.
        .merge(guide::guide_router())
        .merge(sprite::sprite_router())
        // THE CHAIN EXPLORER — `GET /explorer`: what has been happening on the node this surface
        // is pointed at (`DREGG_NODE_URL`). Always mounted: with no node configured the page's
        // job is to SAY that, which it cannot do from a route that does not exist. Additive —
        // the `/explorer` prefix overlaps nothing above.
        .merge(explorer::explorer_router())
        // THE IDENTITY DOOR — `GET /identity` + the claim/confirm/restore/release posts: 24 words
        // that reproduce a player's identity on any device. Additive (the `/identity` prefix
        // overlaps nothing above) and deliberately merged OUTSIDE the visitor-cookie bootstrap:
        // reading the page that explains identity must not silently mint one. State-free — the
        // whole mechanism is a derivation, so there is nothing to hold.
        .merge(seed_identity::identity_router())
        .merge(overlay_router);
    #[cfg(feature = "hosted-binary-operations")]
    let app = app.merge(fhegg_operation::router(Arc::clone(&catalog)));
    // THE TELEGRAM MINI APP surface — mounted iff `TELEGRAM_BOT_TOKEN` is set (the same ops gate
    // as the bot itself; `tg_miniapp_from_env` logs one line either way). It drives the SAME
    // catalog host, but through initData-verified identities landing Signed turns.
    let app = match telegram_miniapp::tg_miniapp_from_env(Arc::clone(&catalog)) {
        Some(tg) => app.merge(tg),
        None => app,
    };
    // THE DISCORD ACTIVITY surface — mounted iff `DISCORD_CLIENT_ID` / `DISCORD_CLIENT_SECRET` /
    // `BOT_SECRET` are all set (the same ops gate + identity secret as the in-chat bot;
    // `discord_activity_from_env` logs one line either way). It drives the SAME catalog host, but
    // through OAuth-ticket-verified identities landing Signed turns under the bot's custodial key.
    let app = match discord_activity::discord_activity_from_env(Arc::clone(&catalog)) {
        Some(da) => app.merge(da),
        None => app,
    };
    // ⚑ THE CROSS-PLATFORM LINK DOOR — `GET`/`POST /identity/link`. A player's web identity (24
    // self-held words) and their Discord/Telegram identity (a key the operator's `bot_secret`
    // derives) were DIFFERENT PEOPLE with different histories on the same board; this is the proven
    // ceremony that joins the records without merging the keys.
    //
    // ALWAYS mounted, unlike `/tg` and `/da`: `/identity`, `/you` and the Descent board all link
    // here, so an env gate would turn those into 404s. With no platform secret configured the page's
    // job becomes SAYING that (the `/explorer` posture) and it serves no form — one warn line at
    // boot names the env to set. Additive either way: `/identity/link` overlaps nothing, and an
    // unlinked player — web, Discord, or a casual cookie visitor — is byte-identical to before,
    // because link resolution treats an unlinked key as its own human.
    let app = app.merge(identity_link::identity_link_from_env());

    // THE TRANSPORT LAYERS, applied to the WHOLE merged surface (see `PLAY_STATIC_CACHE_CONTROL`).
    // Order matters and reads inside-out: `revalidate_play_static` is the inner layer, so it hashes
    // and conditions on the IDENTITY bytes, and `CompressionLayer` is the outer one, so it encodes
    // whatever survives that — including nothing at all, because a `304` has no body to compress.
    // Put the other way round, every repeat visit would pay a full compression pass to produce a
    // response the client already holds.
    //
    // Compression is app-wide rather than scoped to the bundle: the catalog's HTML pages, the
    // explorer, and the sprite SVGs are all text and all compress well, and the default predicate
    // already declines the cases where it would be wrong — `text/event-stream` (the overlay's SSE
    // push, which must keep flushing), already-compressed image types, and bodies under 32 bytes.
    //
    // Compressing an authenticated surface is a BREACH question, so it was asked rather than
    // assumed. That attack needs a STABLE secret in a response body that ALSO reflects attacker-
    // chosen input, so the compressed length leaks a guess. The secrets on this surface are the
    // per-seat table links, and `table_door` already keeps them out of that shape: the secret
    // arrives in the URL, is moved into a cookie and redirected away (`no-referrer`, `private,
    // no-store`), and a mint response carries FRESH secrets per request — a new table every time,
    // so there is no fixed string to converge on. This is a review of the seat-secret flow, not an
    // exhaustive proof over every page; a future route that renders a long-lived secret beside
    // reflected input should opt out of compression rather than assume this note still covers it.
    let app = app
        .layer(middleware::from_fn(revalidate_play_static))
        .layer(tower_http::compression::CompressionLayer::new().quality(
            tower_http::CompressionLevel::Precise(PLAY_COMPRESSION_QUALITY),
        ));

    // START THE OVERLAY LIVE-WORLD CLOSE-LOOP TIMER (only when `OVERLAY_LIVE_WORLD` mounted one).
    // The default demo mount is a tally board with no world → `None` → nothing spawned, so the
    // committed (unconfigured) path is byte-identical. When present, this drives
    // `OverlayState::drive_close` on the round-window interval — the deploy-path close-loop. Spawned
    // here (inside the bin's tokio runtime, like the session-lifecycle sweep) so a running server
    // actually lands certified turns; `spawn` no-ops with a warning if no runtime is in scope.
    if let Some(live) = overlay_live {
        live.spawn();
    }
    (app, catalog)
}

/// The metrics-only app — `GET /metrics` in the Prometheus exposition format — served on its OWN
/// loopback listener, never merged into the public/funnel'd surface. This is the deliberate split:
/// the operational counters (session counts, refusal/anchor/resume rates) are readable only from
/// the box, so a `tailscale funnel` of the main port cannot leak them. Installs the process-global
/// recorder (idempotent), so ordering vs [`make_app_parts`] is irrelevant. The bin binds this to
/// `DREGGNET_WEB_METRICS_BIND` (default `127.0.0.1:9790`).
pub fn metrics_app() -> Router {
    let handle = metrics::install_recorder();
    Router::new()
        .route("/metrics", get(metrics::metrics_handler))
        .with_state(handle)
}

/// Resolve the demo Descent state from the environment: with `DATABASE_URL` set (non-empty), open a
/// durable sqlite ([`descent_store::SqliteDescentRunStore`]) board — reconstructed + re-verified on
/// boot, so submitted runs survive a restart; a bad `DATABASE_URL` FALLS BACK to the in-RAM demo
/// (logged) rather than failing to boot. Unset → the in-RAM seeded demo (the committed tests' path).
pub fn resolve_demo_descent() -> Arc<DescentState> {
    match std::env::var("DATABASE_URL") {
        Ok(url) if !url.is_empty() => match descent_store::SqliteDescentRunStore::open(&url) {
            Ok(store) => {
                tracing::info!(%url, "Descent leaderboard: durable sqlite store");
                build_demo_descent(Some(Arc::new(store)))
            }
            Err(e) => {
                tracing::warn!(%url, error = %e, "could not open DATABASE_URL — falling back to in-RAM demo board");
                demo_descent_state()
            }
        },
        _ => demo_descent_state(),
    }
}

/// **Resolve the games' node target from the environment** — the devnet switch. With `DREGG_NODE_URL`
/// set (non-empty), returns a [`NodeTarget::Federation`] over the real HTTP transport at that URL, so
/// a submitted Descent run is anchored on the running node's ledger (a real committed turn on-chain,
/// confirmed landed); optionally `DREGG_NODE_BEARER` supplies the node's API bearer token (needed only
/// when the node has a passphrase set — a loopback devnet needs none). Unset → [`NodeTarget::Local`],
/// the in-process default (the committed tests + node-free demo are untouched). A malformed value
/// (e.g. the `http` transport missing) logs + FALLS BACK to Local rather than refusing to boot.
pub fn resolve_node_target() -> dregg_node_target::NodeTarget {
    // MUST be built off any tokio runtime. `NodeTarget::from_env` reaches
    // `HttpNode::new` -> `reqwest::blocking::ClientBuilder::build`, and the
    // blocking client's constructor blocks on its own runtime handshake, which
    // `reqwest::blocking::wait::enter` REFUSES inside a runtime:
    //
    //     thread 'main' panicked at tokio/src/runtime/blocking/shutdown.rs:51:
    //     Cannot drop a runtime in a context where blocking is not allowed.
    //
    // The server bin calls this from inside `#[tokio::main]` (main -> make_app_parts
    // -> resolve_demo_descent -> build_demo_descent -> here), so with
    // `DREGG_NODE_URL` set the binary panicked during startup and never bound its
    // listener — the devnet switch bricked the whole server rather than the games'
    // anchor path. Unset, nothing constructed a blocking client and it booted fine,
    // which is why this hid: the failure needs the env var that turns the feature on.
    //
    // A plain scoped OS thread has no runtime in its thread-local, so the
    // constructor is happy. `block_in_place` would also work but only on the
    // multi-thread flavor, and this is reachable from `current_thread` tests too.
    // Cost is one thread spawn, once, at boot.
    std::thread::scope(|s| {
        s.spawn(resolve_node_target_off_runtime)
            .join()
            .unwrap_or_else(|_| {
                tracing::warn!(
                    "node-target resolution thread panicked — falling back to in-process Local"
                );
                dregg_node_target::NodeTarget::Local
            })
    })
}

/// The actual resolution, which MUST run with no tokio runtime in scope.
/// See [`resolve_node_target`] for why.
fn resolve_node_target_off_runtime() -> dregg_node_target::NodeTarget {
    use dregg_node_target::NodeTarget;
    match NodeTarget::from_env() {
        Ok(t) => {
            if t.is_federation() {
                tracing::info!(
                    url = %std::env::var(dregg_node_target::NODE_URL_ENV).unwrap_or_default(),
                    "games node target: Federation — submitted runs anchor on the devnet node"
                );
            }
            t
        }
        Err(e) => {
            tracing::warn!(error = %e, "DREGG_NODE_URL set but node target could not be built — falling back to in-process Local");
            NodeTarget::Local
        }
    }
}

/// `GET /health` — a liveness probe. 200 `{"status":"ok"}`; the fronting Caddy / an uptime check
/// hits it to know the server is up.
async fn health() -> impl IntoResponse {
    Json(serde_json::json!({ "status": "ok" }))
}

/// **A still of a real automatafl mid-turn**, painted by the SAME [`automatafl_board`] painter the
/// live table uses (same night squares, same brass grid, same SVG pieces), so a landing literally
/// previews the product rather than a lookalike, and the two cannot drift. Inert cells (no `turn`
/// ⇒ no form), `aria-hidden` — the adjacent legend/key states the same thing in text. No external
/// assets, no requests.
///
/// `extra_class` rides on the wrapper: `"hero-af"` shrinks it and hides the key for the front
/// page's art column; `""` is the full-size, self-explaining still the automatafl front door shows.
pub(crate) fn automatafl_still(extra_class: &str) -> String {
    // THE REAL POSITION. The still is painted from `dregg_automatafl`'s own opening board and goal
    // corners — the SAME data the live surface renders — so the landing cannot drift away from the
    // product it previews. (It used to be a hand-rolled 5×5 grid; when the played board became the
    // stock 11×11 game, that still would have advertised a board nobody can play.)
    use dregg_automatafl::board::{ATT, AUTO, REP, VAC};
    use dregg_automatafl::game::{N, coord_of, goals, index_of, opening_board};

    // The board and the goal assignment come from the PROVEN LEAN (`@[export]
    // dregg_automatafl_rules`). Without it there is no position to show, so the still says so rather
    // than paint a guessed one.
    let (board, stock_goals) = match (opening_board(), goals()) {
        (Ok(b), Ok(g)) => (b, g),
        _ => {
            return format!(
                "<div class=\"af-still {extra_class}\"><p>The automatafl still needs the game \
                 oracle (the Lean <code>dregg_automatafl_rules</code> export), which this build did \
                 not link.</p></div>"
            );
        }
    };
    // Mid-turn: seat A has the attractor at (3,1) picked up, so the squares it can reach are lit —
    // exactly what the live board highlights on a click.
    let sel = (3i32, 1i32);
    let sel_idx = index_of(sel).expect("in bounds");

    // ⚑ **THE LIT SET IS THE ORACLE'S, NOT A ROOK CROSS DRAWN HERE.** This used to be
    // `(c.0 == sel.0 || c.1 == sel.1) && …` — a rook line computed in this function, which is
    // occupancy-blind, so the still advertised twenty reachable squares including `(3,10)` behind
    // the attractor on `(3,9)` and all of row 1 behind three repulsors. That is a lookalike, which
    // is the one thing this still exists not to be. Both sets now come out of
    // `dregg_automatafl::rules` (the Lean `targetsOf` / `liveTargetsOf`), so the preview shows the
    // same eleven-lit / nine-blocked board the live table does and the two cannot drift.
    let proposable =
        dregg_automatafl::rules::legal_targets(&board, &[], 0, sel).unwrap_or_default();
    let reachable =
        dregg_automatafl::rules::executable_targets(&board, &[], &[], 0, sel).unwrap_or_default();

    // The still is the offering's OWN cell vocabulary — the same `CoordCell`s the live
    // `board_grid` emits — handed to the same painter. Nothing about the look lives here.
    let cells: Vec<CoordCell> = (0..(N * N))
        .map(|i| {
            let c = coord_of(i);
            let p = board.cells[i];
            // Reachable now; proposable-but-blocked; neither. The same three-way split `board_grid`
            // paints, from the same two calls.
            let lit = reachable.contains(&c);
            let blocked = !lit && proposable.contains(&c);
            let goal = stock_goals.iter().find(|(g, _)| *g == c);
            let glyph = match p {
                REP => "R".to_string(),
                ATT => "A".to_string(),
                AUTO => "@".to_string(),
                _ => match goal {
                    Some((_, 0)) => "a".to_string(),
                    Some(_) => "b".to_string(),
                    None => "·".to_string(),
                },
            };
            let (tag, highlight) = if c == board.auto {
                ("accent", true)
            } else if i == sel_idx {
                ("warn", true)
            } else if lit {
                ("good", true)
            } else if blocked {
                ("blocked", false)
            } else if goal.is_some() {
                ("goal", false)
            } else if p == VAC {
                ("muted", false)
            } else {
                ("", false)
            };
            CoordCell {
                glyph,
                tag: tag.to_string(),
                // No affordance: the still is a picture, so every square paints as an inert span.
                turn: String::new(),
                arg: i as i64,
                highlight,
            }
        })
        .collect();
    let mut out = format!("<div class=\"af-table {extra_class}\" aria-hidden=\"true\">");
    automatafl_board(N, &cells, automatafl_web::KEY, "still", &mut out);
    out.push_str("</div>");
    out
}

/// The front page's art column: the still, shrunk, with its key hidden (the page carries its own
/// legend beside it).
fn hero_board() -> String {
    automatafl_still("hero-af")
}

/// `GET /` — the landing. One glance: **what this is**, **what it looks like** (a real board
/// mid-turn, with its colour language labelled), and **why it is different**, then the shipped
/// surfaces.
///
/// ⚑ THE DECK IS WRITTEN FOR A STRANGER. A first-time reader given only this page and the catalog
/// could not say what the site *is*, because the sentence that was supposed to tell them was
/// written in this project's private vocabulary — `executor`, `substrate`, `receipt`, `refereed`,
/// none of them defined anywhere on the page (`docs/reference/UX-QA-SWEEP-2026-07-26.md`). The
/// honest claim is unchanged and is the whole point: moves are RE-RUN and CHECKED, not trusted.
/// It just has to be said in words a newcomer already owns. Keep it that way — if a term here is
/// one you learned from this repo, it does not belong in the deck.
///
/// ⚑ **AND EVERY CHOICE ON IT SAYS HOW MANY PEOPLE IT TAKES.** The deck problem is solved; the next
/// one was structural. There is no matchmaking on this product, so two of the three shipped games
/// need a second human the visitor has to invite personally — and that fact lived only in prose a
/// scanner skips ("A two-player board game…") and above a button one click further in. A stranger
/// arriving ALONE could pick a two-player game first, meet "send this link to your opponent", and
/// leave without ever seeing the solo game. So the hero button and every card carry a `.needs` chip
/// before any click. Do not remove one without removing the wall it describes.
async fn index() -> Html<String> {
    // THE FUNNEL: the PLAY CTA always leads (the served in-tab run at `/descent/play`, plus Discord
    // when configured) and the no-cheat BOARD is the secondary action. Before this the landing's
    // only always-present Descent affordance was the board — the flagship's front door on the front
    // page was a leaderboard, and the built play surface was reachable from nowhere.
    let hero_play = descent_play_cta("btn btn-primary", "solo · new dungeon daily");
    let hero_board_class = "btn btn-ghost";
    let card_play = descent_play_cta("play", "");
    let body = format!(
        "<section class=\"hero\">\
         <div class=\"hero-copy\">\
         <p class=\"eyebrow\">Play in a browser tab · nothing to install</p>\
         <h1>Games that check their own moves.</h1>\
         <p class=\"deck\">Three games you can play right now: a dungeon crawl, a board game, and \
         a game of hidden influence. When you take a turn, the game re-runs it against the rules \
         before it records anything — so an illegal move is refused instead of accepted, and when \
         a game is over anyone can replay it move by move and see it really went that way.</p>\
         <div class=\"cta-row\">\
         {hero_play}\
         <a class=\"btn {hero_board_class}\" href=\"/descent\">See today's finished runs \
         <span class=\"arr\" aria-hidden=\"true\">→</span></a>\
         <a class=\"btn btn-ghost\" href=\"/automatafl\">Play Automatafl \
         <span class=\"needs\">needs a 2nd player</span></a>\
         <a class=\"btn btn-ghost\" href=\"/guide\">How to play</a>\
         <a class=\"btn btn-ghost\" href=\"/offerings\">All games</a>\
         </div></div>\
         <div class=\"hero-art\">{board}\
         <div class=\"legend\">\
         <span><i class=\"k-auto\"></i>automaton</span>\
         <span><i class=\"k-sel\"></i>your piece</span>\
         <span><i class=\"k-tgt\"></i>can reach</span>\
         <span><i class=\"k-blocked\"></i>blocked</span>\
         <span><i class=\"k-goal\"></i>goal</span></div>\
         <p class=\"hero-cap\">Automatafl · mid-turn</p></div>\
         </section>\
         <section class=\"steps\" aria-label=\"How it works\">\
         <div class=\"step\"><span class=\"n\">1</span><h3>Take a turn</h3>\
         <p>Pick a game and make a move, the way you would anywhere else. No account, no wallet, \
         no client-side JavaScript required.</p></div>\
         <div class=\"step\"><span class=\"n\">2</span><h3>The game checks it</h3>\
         <p>Your move is re-run against the rules before anything is written down. A move that \
         is not allowed is refused and leaves no trace — the page cannot talk the game into it.</p>\
         </div>\
         <div class=\"step\"><span class=\"n\">3</span><h3>Anyone can re-check</h3>\
         <p>A finished game replays from its first move to its last. On the daily board, a run \
         that does not replay shows <strong>FAIL</strong> and never ranks.</p></div>\
         </section>\
         <main class=\"catalog\">\
         <section class=\"catalog-group\">\
         <h2 class=\"group-h\">Start here</h2>\
         <div class=\"card-grid\">\
         <div class=\"offering-card shelf-games\"><h3>The Descent</h3>\
         <p class=\"needs solo\">Play alone · a new dungeon every day</p>\
         <p class=\"tagline\">A dungeon crawl. Everyone gets the same dungeon each day, drawn from \
         a public random number nobody can pick in advance. One life, no retries — go deeper for \
         better loot, and you only keep what you carry back out.</p>\
         {card_play}<a class=\"play\" href=\"/descent\">See today's finished runs \
         <span class=\"arr\" aria-hidden=\"true\">→</span></a></div>\
         <div class=\"offering-card shelf-games\"><h3>Automatafl</h3>\
         <p class=\"needs\">Needs a 2nd player · or hold both seats yourself</p>\
         <p class=\"tagline\">A two-player board game. You both choose in secret, then both moves \
         are revealed at once and a neutral piece reacts to them — so you are guessing at your \
         opponent, not waiting on them.</p>\
         <a class=\"play\" href=\"/automatafl\">Open a table \
         <span class=\"arr\" aria-hidden=\"true\">→</span></a></div>\
         <div class=\"offering-card shelf-games\"><h3>Multiway-Tug</h3>\
         <p class=\"needs\">Needs a 2nd player · or hold both seats yourself</p>\
         <p class=\"tagline\">A two-player game of hidden influence over seven guilds. You play \
         cards face down; the pull only becomes public once both sides commit.</p>\
         <a class=\"play\" href=\"/tug\">Open a table \
         <span class=\"arr\" aria-hidden=\"true\">→</span></a></div>\
         </div></section></main>",
        board = hero_board(),
    );
    Html(document(
        &format!("{PRODUCT_NAME} — play + verify"),
        "",
        &body,
    ))
}

// ═════════════════════════════════════════════════════════════════════════════════════════
// THE TRANSPORT-LAYER GATE — that the compression + revalidation layers are actually ON the
// merged app, driven through `make_app` rather than by calling the middleware directly.
//
// These assert against `/descent/play/static/app.js` instead of the wasm bundle on purpose: the
// bundle lives in `wasm/pkg`, which is gitignored and therefore absent on a build box, so a test
// that needed it would pass vacuously wherever it is missing. `app.js` is `include_str!`-embedded
// into the binary, takes the SAME route prefix and the SAME two layers, and exists everywhere.
#[cfg(test)]
mod transport_layer_tests {
    use axum::body::Body;
    use axum::http::{Request, StatusCode, header};
    use tower::ServiceExt as _;

    const PLAY_ASSET: &str = "/descent/play/static/app.js";

    async fn get(uri: &str, headers: &[(header::HeaderName, &str)]) -> axum::response::Response {
        let mut request = Request::builder().uri(uri);
        for (name, value) in headers {
            request = request.header(name, *value);
        }
        super::make_app()
            .oneshot(request.body(Body::empty()).unwrap())
            .await
            .unwrap()
    }

    /// The layer is mounted and NEGOTIATES: a browser offering `br` is answered `br`, and the body
    /// it receives is materially smaller than the identity representation. Both halves matter — an
    /// asserted `content-encoding` with an unshrunk body would be a header that lies.
    #[tokio::test]
    async fn a_play_asset_is_served_compressed_when_the_client_offers_br() {
        let identity = get(PLAY_ASSET, &[]).await;
        assert_eq!(identity.status(), StatusCode::OK);
        assert!(
            identity.headers().get(header::CONTENT_ENCODING).is_none(),
            "a client that offered no encoding must get the identity representation"
        );
        let plain = axum::body::to_bytes(identity.into_body(), usize::MAX)
            .await
            .unwrap()
            .len();

        let compressed = get(PLAY_ASSET, &[(header::ACCEPT_ENCODING, "br")]).await;
        assert_eq!(compressed.status(), StatusCode::OK);
        assert_eq!(
            compressed
                .headers()
                .get(header::CONTENT_ENCODING)
                .expect("the compression layer must negotiate an encoding"),
            "br",
            "the layer is not mounted on the merged app"
        );
        let encoded = axum::body::to_bytes(compressed.into_body(), usize::MAX)
            .await
            .unwrap()
            .len();
        assert!(
            encoded < plain,
            "br body ({encoded} B) must be smaller than identity ({plain} B)"
        );
    }

    /// A repeat visit costs headers, not the artifact: the first response carries a validator and a
    /// freshness policy, and presenting that validator back is answered `304` with NO body.
    #[tokio::test]
    async fn a_returning_visitor_revalidates_into_a_bodiless_304() {
        let first = get(PLAY_ASSET, &[]).await;
        assert_eq!(first.status(), StatusCode::OK);
        let etag = first
            .headers()
            .get(header::ETAG)
            .expect("a cacheable build artifact must carry a validator")
            .to_str()
            .unwrap()
            .to_owned();
        assert!(
            etag.starts_with("W/\""),
            "the validator must be WEAK — it is computed on the identity bytes while the client \
             may hold the br/gzip representation; got {etag}"
        );
        assert_eq!(
            first.headers().get(header::CACHE_CONTROL).unwrap(),
            super::PLAY_STATIC_CACHE_CONTROL
        );

        let second = get(PLAY_ASSET, &[(header::IF_NONE_MATCH, etag.as_str())]).await;
        assert_eq!(
            second.status(),
            StatusCode::NOT_MODIFIED,
            "a matching validator must not re-send the artifact"
        );
        let body = axum::body::to_bytes(second.into_body(), usize::MAX)
            .await
            .unwrap();
        assert!(
            body.is_empty(),
            "a 304 must carry no body, got {} B",
            body.len()
        );
    }

    /// A stale validator is NOT a match — the 304 path must be driven by the bytes, not by the mere
    /// presence of the request header. Without this, a client holding an outdated bundle would be
    /// told it is current forever.
    #[tokio::test]
    async fn a_stale_validator_re_sends_the_artifact() {
        let response = get(
            PLAY_ASSET,
            &[(header::IF_NONE_MATCH, "W/\"not-the-current-bundle\"")],
        )
        .await;
        assert_eq!(response.status(), StatusCode::OK);
        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        assert!(!body.is_empty(), "a non-matching validator must re-send");
    }

    /// `day.json` is today's descriptor and opts out with its own `no-store`. The layer must not
    /// overwrite a route that already stated a policy.
    #[tokio::test]
    async fn todays_day_descriptor_is_never_given_a_freshness_window() {
        let response = get("/descent/play/static/day.json", &[]).await;
        assert_eq!(
            response.headers().get(header::CACHE_CONTROL).unwrap(),
            "no-store",
            "a cached descriptor would pin a stale day"
        );
        assert!(
            response.headers().get(header::ETAG).is_none(),
            "an opted-out route is not given a validator either"
        );
    }

    /// An unregistered offering key is a MISSING resource, and the status line must say so — the
    /// page already does. This is what makes a monitor and a human agree.
    #[tokio::test]
    async fn an_unknown_offering_is_a_404_not_a_200() {
        let response = get("/offerings/nosuchgame/session/abc", &[]).await;
        assert_eq!(response.status(), StatusCode::NOT_FOUND);
        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        assert!(
            String::from_utf8_lossy(&body).contains("No offering registered"),
            "the honest body is kept; only the status line was wrong"
        );
    }

    /// A `HEAD` must not be handed a validator computed over the body axum already removed. Before
    /// the method guard this returned the blake3 of the empty string — one identical `ETag` on every
    /// route, and not the one a `GET` of the same URL reports.
    #[tokio::test]
    async fn a_head_is_not_given_an_etag_minted_from_the_discarded_body() {
        let head = super::make_app()
            .oneshot(
                Request::builder()
                    .method("HEAD")
                    .uri(PLAY_ASSET)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(head.status(), StatusCode::OK);
        match head.headers().get(header::ETAG) {
            None => {}
            Some(head_etag) => {
                let get_etag = get(PLAY_ASSET, &[]).await;
                assert_eq!(
                    head_etag,
                    get_etag.headers().get(header::ETAG).unwrap(),
                    "a HEAD validator that disagrees with the GET one is worse than none"
                );
            }
        }
    }

    #[test]
    fn the_revalidation_policy_covers_build_artifacts_and_skips_the_day() {
        for artifact in [
            "/descent/play/static/dregg_wasm_bg.wasm",
            "/descent/play/static/dregg_wasm.js",
            "/descent/play/static/app.js",
            "/descent/play/static/snippets/crate/inline0.js",
        ] {
            assert!(
                super::play_static_is_revalidatable(artifact),
                "must cache {artifact}"
            );
        }
        for dynamic in [
            "/descent/play/static/day.json",
            "/descent/play",
            "/offerings/tavern/session/abc",
            "/",
        ] {
            assert!(
                !super::play_static_is_revalidatable(dynamic),
                "must not cache {dynamic}"
            );
        }
    }

    #[test]
    fn if_none_match_compares_weakly_and_handles_lists() {
        let etag = "W/\"abc\"";
        let hv = axum::http::HeaderValue::from_static;
        // The wildcard, the exact validator, the strong spelling of it, and a list containing it.
        for matching in ["*", "W/\"abc\"", "\"abc\"", "\"zzz\", W/\"abc\""] {
            assert!(
                super::if_none_match_matches(&hv(matching), etag),
                "must match {matching}"
            );
        }
        for missing in ["\"abc-2\"", "W/\"\"", "\"zzz\""] {
            assert!(
                !super::if_none_match_matches(&hv(missing), etag),
                "must not match {missing}"
            );
        }
    }
}

/// THE BUNDLE MEASUREMENT — what the hero CTA actually costs a browser, end to end through the real
/// merged app and the real layers, on the real `wasm/pkg` artifact.
///
/// `#[ignore]` by default, and deliberately NOT written to skip itself: `wasm/pkg` is gitignored, so
/// on any machine without a local `wasm-pack` build a self-skipping version of this would report
/// green while measuring nothing. Run it explicitly, pointing at a built bundle:
///
/// ```text
/// DESCENT_PLAY_ASSET_DIR=$PWD/wasm/pkg \
///   cargo test -p dreggnet-web --lib measure_the_real_bundle -- --ignored --nocapture
/// ```
#[cfg(test)]
mod bundle_measurement {
    use axum::body::Body;
    use axum::http::{Request, StatusCode, header};
    use tower::ServiceExt as _;

    const BUNDLE: &str = "/descent/play/static/dregg_wasm_bg.wasm";

    #[tokio::test]
    #[ignore = "needs a built wasm/pkg; point DESCENT_PLAY_ASSET_DIR at it"]
    async fn measure_the_real_bundle() {
        let fetch = |accept: Option<&'static str>| async move {
            let mut request = Request::builder().uri(BUNDLE);
            if let Some(accept) = accept {
                request = request.header(header::ACCEPT_ENCODING, accept);
            }
            super::make_app()
                .oneshot(request.body(Body::empty()).unwrap())
                .await
                .unwrap()
        };

        let identity = fetch(None).await;
        assert_eq!(
            identity.status(),
            StatusCode::OK,
            "no bundle resolved — set DESCENT_PLAY_ASSET_DIR to a real wasm/pkg"
        );
        assert_eq!(
            identity.headers().get(header::CONTENT_TYPE).unwrap(),
            "application/wasm"
        );
        let etag = identity
            .headers()
            .get(header::ETAG)
            .unwrap()
            .to_str()
            .unwrap()
            .to_owned();
        let cache = identity
            .headers()
            .get(header::CACHE_CONTROL)
            .unwrap()
            .to_str()
            .unwrap()
            .to_owned();
        let plain = axum::body::to_bytes(identity.into_body(), usize::MAX)
            .await
            .unwrap()
            .len();

        let started = std::time::Instant::now();
        let brotli = fetch(Some("br")).await;
        let elapsed = started.elapsed();
        assert_eq!(
            brotli.headers().get(header::CONTENT_ENCODING).unwrap(),
            "br"
        );
        let compressed = axum::body::to_bytes(brotli.into_body(), usize::MAX)
            .await
            .unwrap()
            .len();

        let repeat = super::make_app()
            .oneshot(
                Request::builder()
                    .uri(BUNDLE)
                    .header(header::IF_NONE_MATCH, &etag)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();

        println!("\n  identity      {plain:>12} B");
        println!(
            "  br            {compressed:>12} B   ({:.1}x, {:.2} s)",
            plain as f64 / compressed as f64,
            elapsed.as_secs_f64()
        );
        println!("  etag          {etag}");
        println!("  cache-control {cache}");
        // ⚑ Read the status BEFORE `into_body` consumes the response. Asserting on `repeat.status()`
        // afterwards was `E0382: borrow of moved value`, so this whole `#[cfg(test)]` module never
        // compiled — `cargo test -p dreggnet-web --lib` failed at the build and every unit test in
        // `lib.rs` was dark, not passing.
        let revisit = repeat.status();
        println!(
            "  revisit       {revisit} (body {} B)\n",
            axum::body::to_bytes(repeat.into_body(), usize::MAX)
                .await
                .unwrap()
                .len()
        );

        assert!(
            compressed * 4 < plain,
            "the bundle must compress by well over 4x"
        );
        assert_eq!(revisit, StatusCode::NOT_MODIFIED);
    }
}
