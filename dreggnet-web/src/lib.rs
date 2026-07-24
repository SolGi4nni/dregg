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
/// One hosted binary-operation transport shared by the web, Telegram Mini App,
/// and Discord Activity authentication wrappers. Concrete operations remain
/// independently feature-gated.
#[cfg(feature = "hosted-binary-operations")]
pub mod fhegg_operation;
/// The one browser interaction grammar shared by every game offering.
pub mod game_session;
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
/// The deterministic generative art surface: a `dreggnet_asset::AssetId` → a byte-identical SVG
/// sprite (`dreggnet-sprite`), served at `GET /sprite/{kind}/{ref}`, painted onto an asset-bearing
/// deos `Tile`, and shown in a `GET /gallery`. See [`sprite`].
pub mod sprite;
/// THE TELEGRAM MINI APP surface (`/tg` scope): initData HMAC-validated Telegram identity → the
/// SAME derived dregg identity the in-chat bot uses (`dreggnet_telegram::cipherclerk`) → turns
/// landing with **verified `Attribution::Signed`** provenance via an atomic custodial sign +
/// `advance_signed` on the host thread. Mounted iff `TELEGRAM_BOT_TOKEN` is set. See
/// [`telegram_miniapp`] and `docs/TELEGRAM-MINIAPP-DESIGN.md`.
pub mod telegram_miniapp;
pub mod tg_link_page;
mod web_identity_http;

pub use descent::{DescentState, descent_router, run_share_path};

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

use deos_view::{MenuItem, SessionFormBackend, SurfaceBackend, ViewNode};
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
        (user.to_string(), web_identity(user))
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
    fn identity(&self, user: String) -> DreggIdentity {
        web_identity(&user)
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

/// **The axum web surface state** — the ONE [`DungeonOffering`] core, the live per-session
/// [`DungeonSession`]s (the real verifiable state chains), and the [`WebFrontend`] recording what
/// each session last presented. Shared behind an `Arc` as the axum handler `State`.
pub struct WebState {
    /// The offering core (offering #0). Stateless factory; each session is a real playthrough.
    offering: DungeonOffering,
    /// The live sessions — a real `DungeonSession` (WorldCell + playthrough) per session id.
    sessions: Mutex<HashMap<SessionId, DungeonSession>>,
    /// The web frontend recording each session's last-presented surface + actions.
    frontend: Mutex<WebFrontend>,
}

impl WebState {
    /// A fresh web surface over the free-tier dungeon offering.
    pub fn new() -> Self {
        WebState {
            offering: DungeonOffering::new(),
            sessions: Mutex::new(HashMap::new()),
            frontend: Mutex::new(WebFrontend::new()),
        }
    }

    /// A web surface over a caller-provided offering (e.g. [`DungeonOffering::paid`]).
    pub fn with_offering(offering: DungeonOffering) -> Self {
        WebState {
            offering,
            sessions: Mutex::new(HashMap::new()),
            frontend: Mutex::new(WebFrontend::new()),
        }
    }

    /// Whether a session is open.
    pub fn is_open(&self, id: &SessionId) -> bool {
        self.sessions.lock().unwrap().contains_key(id)
    }

    /// Ensure a session is open: on first touch, [`open`](Offering::open) a fresh
    /// [`DungeonSession`] (seeded deterministically from the session id, so a re-open of the same
    /// id is the SAME replay-verifiable world), spin its frontend slot, and present the initial
    /// surface (so a first POST can already `collect` the gatehall affordances).
    pub fn ensure_open(&self, id: &SessionId) {
        {
            let sessions = self.sessions.lock().unwrap();
            if sessions.contains_key(id) {
                return;
            }
        }
        let session = self
            .offering
            .open(SessionConfig::with_seed(seed_from_id(&id.0)))
            .expect("the Keep opens");
        let surface = self.offering.render(&session);
        let actions = self.offering.actions(&session);
        self.sessions.lock().unwrap().insert(id.clone(), session);
        let mut fe = self.frontend.lock().unwrap();
        fe.spin_session(id.clone());
        fe.present(id, &surface, &actions);
    }

    /// Re-verify a session's whole committed chain by replay (the offering's own proof).
    pub fn verify(&self, id: &SessionId) -> Option<VerifyReport> {
        let sessions = self.sessions.lock().unwrap();
        sessions.get(id).map(|s| self.offering.verify(s))
    }

    /// The number of real verified turns (genesis + committed steps) in a session.
    pub fn receipts_len(&self, id: &SessionId) -> Option<usize> {
        let sessions = self.sessions.lock().unwrap();
        sessions.get(id).map(|s| s.receipts_len())
    }

    /// The session's current room (passage) name, if still running.
    pub fn current_room(&self, id: &SessionId) -> Option<String> {
        let sessions = self.sessions.lock().unwrap();
        sessions.get(id).and_then(|s| s.current_passage_name())
    }

    /// Re-derive the current surface + actions from the live session, tell the frontend to
    /// present them (keeping the affordance surface current for the next `collect`), render the
    /// fragment, and wrap it in a full HTML page with `notice` and the live verify status.
    fn render_page(&self, id: &SessionId, notice: Option<&str>) -> String {
        let (surface, actions, verify) = {
            let sessions = self.sessions.lock().unwrap();
            let session = match sessions.get(id) {
                Some(s) => s,
                None => return page_missing(id),
            };
            (
                self.offering.render(session),
                self.offering.actions(session),
                self.offering.verify(session),
            )
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
            // The CORE resolves the collected action on the substrate — ONE real turn.
            let outcome = {
                let mut sessions = state.sessions.lock().unwrap();
                let session = sessions
                    .get_mut(&id)
                    .expect("the session is open (ensure_open ran)");
                state.offering.advance(session, action, actor)
            };
            match outcome {
                Outcome::Landed { receipt, ended } => {
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
                Outcome::Refused(why) => {
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
        "<div class=\"crumb\"><a href=\"/offerings\">← the Lab</a>\
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
    document(&format!("DreggNet Cloud — session {}", id.0), "", &body)
}

/// The page shown for a `POST` / verify against a session id that is not open.
fn page_missing(id: &SessionId) -> String {
    let body = format!(
        "<main class=\"session\"><div class=\"notice refused\" role=\"status\">No such session — \
         GET /session/{id} to open it.</div>\
         <p class=\"prose\"><a class=\"backlink\" href=\"/offerings\">← Browse the Lab</a></p>\
         </main>",
        id = esc(&id.0),
    );
    document(&format!("DreggNet Cloud — session {}", id.0), "", &body)
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
.crumb .sid{font-family:var(--mono);font-size:var(--t-micro);color:var(--fg-3)}
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
.hero-art{display:flex;flex-direction:column;align-items:center;gap:.7rem}
.hero-art .coordgrid{margin:0;max-width:19rem}
.hero-cap{margin:0;font-size:var(--t-micro);text-transform:uppercase;letter-spacing:.11em;color:var(--fg-3);text-align:center}
.hero-board .cell{cursor:default}
.steps{max-width:var(--shell);margin:0 auto;padding:var(--s5) 1.25rem 0;display:grid;grid-template-columns:repeat(3,1fr);gap:.85rem}
.step{padding:1.05rem 1.15rem;border:1px solid var(--line-soft);border-radius:var(--r-lg);background:linear-gradient(180deg,rgba(24,36,63,.62),rgba(13,20,37,.5))}
.step .n{display:inline-flex;align-items:center;justify-content:center;width:1.55rem;height:1.55rem;border-radius:var(--r-sm);font-size:var(--t-micro);font-weight:800;font-family:var(--mono);background:rgba(92,201,255,.13);color:var(--accent);box-shadow:inset 0 0 0 1px rgba(92,201,255,.26);margin-bottom:.6rem}
.step h3{margin:0 0 .25rem;font-size:var(--t-h3);color:var(--fg)}
.step p{margin:0;font-size:var(--t-sm);color:var(--fg-3);line-height:1.6}
/* ═══ BUTTONS ════════════════════════════════════════════════════════════ */
.btn{display:inline-flex;align-items:center;gap:.45rem;padding:.7rem 1.15rem;border-radius:11px;font-family:inherit;font-weight:700;font-size:var(--t-body);text-decoration:none;border:1px solid transparent;cursor:pointer;transition:transform .1s var(--ease),box-shadow .18s,background .18s,border-color .18s,color .18s}
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
.notice{display:flex;align-items:flex-start;gap:.6rem;padding:.7rem .9rem;border-radius:var(--r-md);margin:0 0 var(--s4);font-size:var(--t-sm);font-weight:600;border:1px solid var(--line);animation:notice-in .26s var(--ease) both}
.notice::before{flex:0 0 auto;width:1.15rem;height:1.15rem;border-radius:50%;display:grid;place-items:center;font-size:.7rem;font-weight:800;margin-top:.06rem}
.notice.ok{background:rgba(79,220,160,.09);color:#a9f5d1;border-color:rgba(79,220,160,.32)}
.notice.ok::before{content:"✓";background:rgba(79,220,160,.18);color:var(--good)}
.notice.refused{background:rgba(255,123,134,.09);color:#ffc0c5;border-color:rgba(255,123,134,.32)}
.notice.refused::before{content:"✕";background:rgba(255,123,134,.18);color:var(--bad)}
@keyframes notice-in{from{opacity:0;transform:translateY(-5px)}to{opacity:1;transform:none}}
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
.backlink{display:inline-flex;align-items:center;gap:.4rem;margin:var(--s5) 0 0;font-size:var(--t-sm);color:var(--fg-2);text-decoration:none;font-weight:600}
.backlink:hover{color:var(--accent)}
/* ═══ THE BOARD — the hero surface ═══════════════════════════════════════ */
.coordgrid{display:grid;gap:.4rem;width:100%;max-width:24rem;margin:1.1rem auto;padding:.6rem;border:1px solid var(--line);border-radius:14px;background:radial-gradient(130% 120% at 50% 0%,#0d1731,#060a15);box-shadow:inset 0 1px 0 rgba(255,255,255,.045),inset 0 0 44px -14px #000,0 20px 46px -26px #000}
.coordgrid .cell{position:relative;display:flex;align-items:center;justify-content:center;aspect-ratio:1/1;min-width:1.9rem;border:1px solid var(--line-soft);border-radius:9px;background:rgba(255,255,255,.02);color:var(--fg);font-family:var(--mono);font-size:1.15rem;font-weight:700;line-height:1;margin:0;transition:border-color .14s,background .14s,color .14s,transform .09s var(--ease),box-shadow .18s}
/* The checker — a 5-wide grid only (an odd width ⇒ nth-child alternation IS a checkerboard; a */
/* tug hand of another width just stays flat). `:where()` zeroes the selector's specificity, so a */
/* tinted cell (tag-accent/warn) keeps its own field and only the plain squares checker. */
:where(.coordgrid[style*="repeat(5,"]) .cell:nth-child(2n){background-image:linear-gradient(rgba(255,255,255,.032),rgba(255,255,255,.032))}
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
.coordgrid .cell.tag-muted{color:#3f5074;font-size:.72rem}
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
.hero-art .coordgrid{max-width:15rem}
.steps{grid-template-columns:1fr}
.card-grid{grid-template-columns:1fr}
.topbar-in{padding:.5rem .9rem}
.brand-name{display:none}
.session,.catalog{padding-left:.9rem;padding-right:.9rem}
.crumb{padding-left:.9rem;padding-right:.9rem}
.hero,.steps{padding-left:.9rem;padding-right:.9rem}
.foot{padding-left:.9rem;padding-right:.9rem;flex-direction:column;align-items:flex-start;gap:.75rem}
/* ≥44px touch targets on the board */
.coordgrid{gap:.3rem;padding:.45rem;max-width:100%}
.coordgrid .cell{min-width:2.75rem;border-radius:8px}
.affordance{flex-direction:column}
.affordance input.arg{flex:1 1 auto;width:100%;text-align:left}
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
         <a class=\"brand\" href=\"/\">{MARK}<span class=\"brand-name\">DreggNet Cloud</span></a>\
         <nav class=\"topnav\" aria-label=\"Surfaces\">{play}{board}{offerings}{gallery}</nav>\
         </div></header>",
        MARK = MARK,
        offerings = item("/offerings", "offerings", "The Lab"),
        play = item(DESCENT_PLAY_PATH, "descent", "The Descent"),
        board = item("/descent", "descent-board", "Board"),
        gallery = item("/gallery", "gallery", "Gallery"),
    )
}

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
  function reduced(){return window.matchMedia&&window.matchMedia("(prefers-reduced-motion: reduce)").matches;}
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
})();
</script>"##;

/// The page footer — states the one property the whole product rests on, and repeats the nav.
const FOOTER: &str = "<footer class=\"foot\">\
     <p>Verification is in-process re-execution — no node, no testnet.</p>\
     <nav aria-label=\"Footer\"><a href=\"/descent\">The Descent</a>\
     <a href=\"/offerings\">The Lab</a><a href=\"/gallery\">Gallery</a>\
     <a href=\"/health\">Status</a></nav></footer>";

/// **Wrap a body fragment in the full product document** — head (charset / viewport / title / the
/// inlined [`STYLE`]) + the shared [`topbar`] + the fragment + the [`FOOTER`]. Every served surface
/// goes through here, which is what makes them one product rather than a pile of pages.
///
/// `title` is the `<title>` text (escaped here — callers pass raw); `active` marks the current nav
/// item (`"offerings"` / `"descent"` / `"gallery"` / `""`).
pub(crate) fn document(title: &str, active: &str, body: &str) -> String {
    format!(
        "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">\
         <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\
         <meta name=\"color-scheme\" content=\"dark\">\
         <title>{title}</title>{style}</head><body>{topbar}{body}{footer}{script}</body></html>",
        title = esc(title),
        style = STYLE,
        topbar = topbar(active),
        body = body,
        footer = FOOTER,
        script = ENHANCE_SCRIPT,
    )
}

/// A breadcrumb strip — `← all offerings · **Title** · session {id}`. The session id is set in the
/// mono voice (it is verifiable material, like a hash or a seed).
fn crumb(title: &str, id: &SessionId) -> String {
    format!(
        "<div class=\"crumb\"><a href=\"/offerings\">← the Lab</a>\
         <span class=\"sep\">·</span><strong>{title}</strong>\
         <span class=\"sep\">·</span><span class=\"sid\">session {id}</span></div>",
        title = esc(title),
        id = esc(&id.0),
    )
}

/// The notice banner — *what just happened*. A refusal is honest and red; a landed turn is green.
/// The `✓`/`✕` glyph is drawn by CSS (`.notice::before`), so the text stays clean for a reader.
fn notice_html(notice: Option<&str>) -> String {
    notice
        .map(|n| {
            let cls = if n.starts_with("Refused") {
                "notice refused"
            } else {
                "notice ok"
            };
            format!("<div class=\"{cls}\" role=\"status\">{}</div>", esc(n))
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
         <a class=\"replay-verify\" rel=\"nofollow\" href=\"{verify_href}\">Replay-verify</a></div>",
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
    )
}

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

    /// The registered offerings (the catalog listing). Served from the shared host, which still
    /// registers the RPG keys for metadata/listing (their sessions route per-identity, but the
    /// catalog page still lists all of them).
    pub fn list_offerings(&self) -> Vec<OfferingInfo> {
        self.host.run(|h| h.list_offerings())
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
    Router::new()
        .route("/offerings", get(get_catalog))
        .route("/offerings/{key}/session/{id}", get(get_offering_session))
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

/// `GET /offerings` — the catalog page: a card per registered offering (title + live-session count)
/// with a "play" link opening a browser session of it.
async fn get_catalog(State(state): State<Arc<CatalogState>>) -> Html<String> {
    let offerings = state.list_offerings();
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
            return Html(catalog_missing_offering(&key)).into_response();
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

/// The `{turn, arg}` POST body of `POST /offerings/{key}/session/{id}/act`.
#[derive(Debug, Clone, Deserialize)]
pub struct OfferingActForm {
    /// The affordance verb (the offering's turn — `"choose"`, `"propose"`, `"approve"`, `"bid"`, …).
    pub turn: String,
    /// The affordance argument (a choice/proposal index, or a value-taking turn's value).
    #[serde(default)]
    pub arg: i64,
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
    Advanced(Outcome),
    /// A game turn crossed the authority-bound common spine and was reduced
    /// to the viewer-blind publication grammar before leaving the host thread.
    AdvancedGame {
        outcome: Outcome,
        publication: Option<PublicGameReceipt>,
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
                return Html(catalog_missing_offering(&key)).into_response();
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
                let action = Action::new(turn.clone(), turn, arg, true);
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
            // The label + enabled are decoration; the executor resolves the TYPED (turn, arg).
            let action = Action::new(turn.clone(), turn, arg, true);
            match h.advance(&k, &sid, action, inner_actor) {
                Some(o) => CatalogAct::Advanced(o),
                None => CatalogAct::Missing,
            }
        })
    };

    // AUDIT EMIT: the collected+resolved act — the `Landed` arm carries the receipt-chain
    // join (`hex(TurnReceipt.turn_hash)`); an executor refusal is `routed` (the substrate was
    // reached — the refusal is ITS decision), a not-offered/missing is the frontend's.
    audit::log().emit(match &acted {
        CatalogAct::Advanced(Outcome::Landed { receipt, ended }) => act_audit_event(
            &user, &actor, &key, &sid, &form,
        )
        .with_outcome(audit::AuditOutcome::Landed {
            turn_hash: audit::hex32(&receipt.turn_hash),
            ended: *ended,
        }),
        CatalogAct::Advanced(Outcome::Refused(why)) => {
            act_audit_event(&user, &actor, &key, &sid, &form)
                .with_outcome(audit::AuditOutcome::Refused { why: why.clone() })
        }
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

    let notice = match acted {
        CatalogAct::Advanced(Outcome::Landed { receipt, ended }) => {
            format!(
                "Turn committed — {}",
                PlayerTurnReceipt::from_landed(&receipt, ended)
                    .compact_text(PlayerReplaySurface::Web)
            )
        }
        CatalogAct::Advanced(Outcome::Refused(why)) => {
            metrics::inc_turn_refused();
            format!("Refused: {why} (nothing committed — anti-ghost).")
        }
        CatalogAct::AdvancedGame {
            outcome: Outcome::Landed { .. },
            publication: Some(publication),
        } => format!(
            "Turn committed — {}",
            game_session::public_receipt_text(&publication, PlayerReplaySurface::Web)
        ),
        CatalogAct::AdvancedGame {
            outcome: Outcome::Landed { .. },
            publication: None,
        } => "Refused: a landed game turn lacked its public receipt projection.".to_string(),
        CatalogAct::AdvancedGame {
            outcome: Outcome::Refused(why),
            ..
        } => {
            metrics::inc_turn_refused();
            format!("Refused: {why} (nothing committed — anti-ghost).")
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
         <p class=\"prose\"><a class=\"backlink\" href=\"/offerings\">← Browse the Lab</a></p>\
         </main>",
        err = esc(&err.to_string()),
    );
    let page = document(
        &format!("DreggNet Cloud — session {} refused", id.0),
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
fn act_audit_event(
    user: &str,
    actor: &DreggIdentity,
    key: &str,
    sid: &SessionId,
    form: &OfferingActForm,
) -> audit::AuditEvent {
    audit::AuditEvent::new(
        "web",
        audit::Actor::asserted(user).with_identity(actor.0.clone()),
        audit::Surface::Http,
        audit::Input::new(
            "POST /offerings/{key}/session/{id}/act",
            serde_json::json!({ "turn": form.turn, "arg": form.arg }),
        ),
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
    let report = {
        let k = key.clone();
        let sid = sid.clone();
        state.run_offering(&key, &viewer, move |h| h.verify(&k, &sid))
    };
    match report {
        Some(report) => {
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
        None => {
            audit::log().emit(verify_event().decided("refused", "missing_session"));
            Json(serde_json::json!({
                "verified": false,
                "turns": 0,
                "detail": "no such offering session",
            }))
        }
    }
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
    Some(format!(
        "{notice}{forms}{operation_forms}{receipt}",
        notice = notice_html(notice),
        forms = forms,
        operation_forms = operation_forms,
        receipt = receipt_html(
            &verify,
            "chain re-verified by replay",
            &format!("/offerings/{}/session/{}/verify", esc(key), esc(&id.0)),
        ),
    ))
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
        return page_missing(id);
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
/// refuses a crafted POST of it). A value-taking turn's `arg` is an editable number input (so a
/// market bid's value can be typed); a fixed-choice affordance defaults it to the presented arg.
pub fn render_catalog_forms(node: &ViewNode, key: &str, id: &str) -> String {
    let mut out = String::new();
    catalog_node(node, key, id, &mut out);
    out
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
            };
            out.push_str(&catalog_form(key, id, &it));
        }
        // THE BOARD NODE — a `cols`-wide coordinate grid (automatafl's board, the tug's hand). Each
        // cell paints its glyph; a cell carrying an affordance (`turn` non-empty) is a real POST
        // button firing `{turn, arg}` (the target square), so the board is CLICKABLE in the browser;
        // a highlighted cell (the legal-move set / the selected piece / the automaton) gets the
        // `highlighted` class. An inert cell is a plain span — never a button.
        ViewNode::CoordGrid { cols, cells } => {
            let cols_n = (*cols).max(1);
            out.push_str(&format!(
                "<div class=\"coordgrid\" style=\"grid-template-columns:repeat({cols_n},1fr)\">",
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
                // `R`/`A`/`@`/`·`), so a lowercase `a`/`b` uniquely marks a goal cell. It gets a
                // distinct `goal` look (a teal dashed objective ring) so a goal no longer reads as
                // a plain vacant square — even when it is also a legal move target (green) it stays
                // legible as the objective.
                let goal = if cell.glyph == "a" || cell.glyph == "b" {
                    " goal"
                } else {
                    ""
                };
                if cell.turn.is_empty() {
                    out.push_str(&format!(
                        "<span class=\"cell{hl}{tag}{goal}\">{glyph}</span>",
                        glyph = esc(&cell.glyph),
                    ));
                } else {
                    // A clickable square's accessible name: the glyph alone ("·", "R") tells a
                    // screen-reader user nothing. The verb plus the square's row/column — derived
                    // purely from the cell's position in the row-major grid, so no game knowledge
                    // is assumed and no logic is touched — makes the board keyboard-playable in
                    // earnest, not just focusable. Visually hidden (`.sr-only`).
                    let (row, col) = (i / cols_n + 1, i % cols_n + 1);
                    out.push_str(&format!(
                        "<form class=\"cell{hl}{tag}{goal}\" method=\"post\" \
                         action=\"/offerings/{key}/session/{id}/act\">\
                         <input type=\"hidden\" name=\"turn\" value=\"{turn}\">\
                         <input type=\"hidden\" name=\"arg\" value=\"{arg}\">\
                         <button type=\"submit\">{glyph}\
                         <span class=\"sr-only\">{turn} row {row}, column {col}</span>\
                         </button></form>",
                        key = esc(key),
                        id = esc(id),
                        turn = esc(&cell.turn),
                        arg = cell.arg,
                        glyph = esc(&cell.glyph),
                        row = row,
                        col = col,
                    ));
                }
            }
            out.push_str("</div>");
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
                };
                out.push_str(&catalog_form(key, id, &it));
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
        ViewNode::Progress { value, max, label } => {
            out.push_str(&format!(
                "<div class=\"progress\">{}{}/{}</div>",
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
/// action="/offerings/{key}/session/{id}/act">` carrying the affordance's `{turn, arg}` — `turn` as
/// a hidden input, `arg` as an EDITABLE number input defaulting to the presented value (so a
/// value-taking turn, a market bid, takes a typed value while a fixed-choice affordance just
/// submits its default). A `!enabled` row is dimmed + `disabled` (a decoration; the executor is the
/// referee).
fn catalog_form(key: &str, id: &str, it: &MenuItem) -> String {
    let (disabled, cls) = if it.enabled {
        ("", "affordance")
    } else {
        (" disabled", "affordance dimmed")
    };
    format!(
        "<form class=\"{cls}\" method=\"post\" action=\"/offerings/{key}/session/{id}/act\" \
         data-session-action=\"turn\" data-turn=\"{turn}\">\
         <input type=\"hidden\" name=\"turn\" value=\"{turn}\">\
         <input class=\"arg\" type=\"number\" name=\"arg\" value=\"{arg}\" step=\"1\" \
         inputmode=\"numeric\" aria-label=\"{turn} value\"{disabled}>\
         <button type=\"submit\"{disabled}>{label}</button></form>",
        cls = cls,
        key = esc(key),
        id = esc(id),
        turn = esc(&it.turn),
        arg = it.arg,
        disabled = disabled,
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
fn descent_play_cta(class: &str) -> String {
    let mut out = format!(
        "<a class=\"{class}\" href=\"{href}\">Play The Descent \
         <span class=\"arr\" aria-hidden=\"true\">→</span></a>",
        href = DESCENT_PLAY_PATH,
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

/// The `GET /offerings` catalog page — The Descent featured on top (the flagship pointer), then
/// the Lab shelf: a card + "play" link per registered offering, framed by the shared
/// `dreggnet_catalog::{flagship_pointer, lab_intro}` copy.
fn catalog_page(offerings: &[OfferingInfo]) -> String {
    // Group the catalog into coherent shelves so ~19 offerings read as three clear categories,
    // not one flat wall of look-alike cards: the GAMES (play to win / verify), the RPG FEATURE
    // surfaces (the do-once render path), and the verifiable SERVICES. Any offering outside the
    // known sets falls into a catch-all "More" shelf (so a future registration still shows up).
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
        format!(
            "<div class=\"offering-card\"><h3>{name}</h3>{tagline}\
             <p class=\"meta\"><span class=\"dot{live}\"></span>{key} · {n} open</p>\
             <a class=\"play\" href=\"/offerings/{key}/session/{key}-web\">{verb} \
             <span class=\"arr\" aria-hidden=\"true\">→</span></a></div>",
            name = esc(name),
            tagline = tagline_html,
            live = live,
            key = esc(&o.key),
            n = o.open_sessions,
            verb = verb,
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

    // THE LAB FRAMING (shared words: `dreggnet_catalog::{flagship_pointer, lab_intro}`) — the
    // featured game leads, and the 23-offering shelf below is honestly the lab, not the product.
    // THE FUNNEL: the PLAY CTA leads (the served in-tab run at `/descent/play`) and the no-cheat
    // board is the secondary link. Previously this page offered the BOARD as its only always-present
    // affordance, so the flagship's front door on the catalog was a leaderboard.
    let descent_play = descent_play_cta("play");
    let body = format!(
        "<main class=\"catalog\"><div class=\"page-head\">\
         <p class=\"eyebrow\">DreggNet Cloud</p>\
         <h1>One game, and a lab full of parts.</h1>\
         <p class=\"deck\">{flagship}</p>\
         <p class=\"prose\">{descent_play}<a class=\"play\" href=\"/descent\">\
         See today's no-cheat board \
         <span class=\"arr\" aria-hidden=\"true\">→</span></a></p>\
         <p class=\"deck\">{lab} Every offering below is a confined, verifiable, per-session \
         thing on the real dregg substrate — no node, no testnet: verification is in-process \
         re-execution.</p></div>\
         {games}{features}{services}{more}</main>",
        flagship = esc(dreggnet_catalog::flagship_pointer()),
        lab = esc(dreggnet_catalog::lab_intro()),
        games = group(
            "Games",
            "games",
            "Play to win or verify — a board, a market, a hidden-hand tug. Every move commits a real \
             receipt (or is refused).",
            GAMES,
            "Play",
        ),
        features = group(
            "Feature surfaces",
            "features",
            "The RPG surfaces — trade, inventory, achievements, guilds, crafting, companions, taverns, \
             parties. Each is a real render→turn surface on the substrate.",
            FEATURES,
            "Open",
        ),
        services = group(
            "Services",
            "services",
            "Verifiable infrastructure — a document store, a naming service, a compute market, metered \
             grain, and a message relay.",
            SERVICES,
            "Open",
        ),
        more = more_section,
    );
    document("DreggNet Cloud — offerings", "offerings", &body)
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
    // it a programmatic focus target (keyboard continuity after a swap); `aria-live="polite"` has a
    // screen reader announce the updated surface. With JS off it is just the container the
    // server-rendered surface fills — the fallback is the current behaviour, untouched.
    let body = format!(
        "{crumb}<main class=\"session\">\
         <div class=\"page-head\" style=\"padding-top:var(--s4)\"><h1>{name}</h1>{tagline}</div>\
         {session_rail}\
         <div id=\"live-surface\" class=\"live-surface\" tabindex=\"-1\" aria-live=\"polite\" \
         data-result-kind=\"surface-and-receipt\">{surface}</div>\
         </main>",
        crumb = crumb(name, id),
        name = esc(name),
        tagline = tagline_html,
        session_rail = game_session::session_rail(key, &id.0).unwrap_or_default(),
        surface = surface,
    );
    document(&format!("DreggNet Cloud — {title}"), "offerings", &body)
}

/// The page shown for a `GET`/`POST` against an unregistered offering key.
fn catalog_missing_offering(key: &str) -> String {
    let body = format!(
        "<main class=\"session\"><div class=\"notice refused\" role=\"status\">No offering \
         registered under <code>{key}</code>.</div>\
         <p class=\"prose\"><a class=\"backlink\" href=\"/offerings\">← Browse the catalog</a></p>\
         </main>",
        key = esc(key),
    );
    document("DreggNet Cloud — unknown offering", "offerings", &body)
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
        .merge(descent_router(descent))
        // THE PLAYABLE web front door (backlog H1): `GET /descent/play` serves an in-tab
        // same-origin DOM controller over the Lean-native `NativeDescentWorld` (via the wasm
        // `bindings_native_descent` executor), NOT the `<dregg-descent>` element. State-free +
        // additive; no route overlap with `descent_router`'s board/run/submit surface.
        .merge(descent_play::descent_play_router())
        .merge(sprite::sprite_router())
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

/// **The landing hero's board** — a still of a real automatafl mid-turn, painted with the SAME
/// `.coordgrid`/`.cell`/`tag-*` classes the live board uses, so the landing literally previews the
/// product and teaches its colour language before a stranger clicks anything. Inert spans,
/// `aria-hidden` (the adjacent legend states the same thing in text); no assets, no requests.
fn hero_board() -> String {
    /// The selected piece at (1,1) — its rook line is the lit legal-move set.
    const SEL: usize = 6;
    /// The automaton at the centre (2,2).
    const AUTO: usize = 12;
    /// An unselected piece at (3,3) — untagged, so it reads solid.
    const PIECE: usize = 18;
    /// Seat A's goal square (0,0) / seat B's (4,4).
    const GOAL_A: usize = 0;
    const GOAL_B: usize = 24;

    let mut out = String::from(
        "<div class=\"coordgrid hero-board\" style=\"grid-template-columns:repeat(5,1fr)\" \
         aria-hidden=\"true\">",
    );
    for i in 0..25usize {
        let (r, c) = (i / 5, i % 5);
        // The selected piece's rook cross — the legal-move set the live surface would light.
        let lit = r == 1 || c == 1;
        let (glyph, cls) = match i {
            AUTO => ("@", "cell highlighted tag-accent"),
            SEL => ("A", "cell highlighted tag-warn"),
            PIECE => ("R", "cell"),
            GOAL_A => ("a", "cell tag-muted goal"),
            GOAL_B => ("b", "cell tag-muted goal"),
            _ if lit => ("·", "cell highlighted tag-good"),
            _ => ("·", "cell tag-muted"),
        };
        out.push_str(&format!("<span class=\"{cls}\">{glyph}</span>"));
    }
    out.push_str("</div>");
    out
}

/// `GET /` — the landing. One glance: **what this is** (play verifiable games — every move is a
/// receipt), **what it looks like** (a real board mid-turn, with its colour language labelled), and
/// **why it is different** (play → commit → re-verify), then the three surfaces.
async fn index() -> Html<String> {
    // THE FUNNEL: the PLAY CTA always leads (the served in-tab run at `/descent/play`, plus Discord
    // when configured) and the no-cheat BOARD is the secondary action. Before this the landing's
    // only always-present Descent affordance was the board — the flagship's front door on the front
    // page was a leaderboard, and the built play surface was reachable from nowhere.
    let hero_play = descent_play_cta("btn btn-primary");
    let hero_board_class = "btn btn-ghost";
    let card_play = descent_play_cta("play");
    let body = format!(
        "<section class=\"hero\">\
         <div class=\"hero-copy\">\
         <p class=\"eyebrow\">Verifiable games · node-free</p>\
         <h1>Every move is a receipt.</h1>\
         <p class=\"deck\">Play a board, a market, a hidden-hand tug — in your browser, with no \
         client JavaScript. Every move is a real executor turn, refereed on the substrate. Nothing \
         here is taken on trust: a run re-executes, or it fails.</p>\
         <div class=\"cta-row\">\
         {hero_play}\
         <a class=\"btn {hero_board_class}\" href=\"/descent\">See today's no-cheat board \
         <span class=\"arr\" aria-hidden=\"true\">→</span></a>\
         <a class=\"btn btn-ghost\" href=\"/offerings\">Browse the Lab</a>\
         </div></div>\
         <div class=\"hero-art\">{board}\
         <div class=\"legend\">\
         <span><i class=\"k-auto\"></i>automaton</span>\
         <span><i class=\"k-sel\"></i>your piece</span>\
         <span><i class=\"k-tgt\"></i>legal move</span>\
         <span><i class=\"k-goal\"></i>goal</span></div>\
         <p class=\"hero-cap\">Automatafl · mid-turn</p></div>\
         </section>\
         <section class=\"steps\" aria-label=\"How it works\">\
         <div class=\"step\"><span class=\"n\">1</span><h3>Play</h3>\
         <p>Open an offering and take a turn. Every affordance is cap-gated, and the executor — \
         never the page — is the sole referee.</p></div>\
         <div class=\"step\"><span class=\"n\">2</span><h3>Commit</h3>\
         <p>A legal move lands a real verified receipt. An illegal one is refused and nothing \
         commits: no ghost state, no fake pass.</p></div>\
         <div class=\"step\"><span class=\"n\">3</span><h3>Re-verify</h3>\
         <p>Anyone can replay the whole committed chain. On the no-cheat board a forged run shows \
         <strong>FAIL</strong> — it never ranks.</p></div>\
         </section>\
         <main class=\"catalog\">\
         <section class=\"catalog-group\">\
         <h2 class=\"group-h\">Start here</h2>\
         <div class=\"card-grid\">\
         <div class=\"offering-card shelf-games\"><h3>The Descent</h3>\
         <p class=\"tagline\">The featured game. One dungeon a day, seeded from a public beacon; \
         one life, no reruns; every finished climb is proved onto the no-cheat board.</p>\
         {card_play}<a class=\"play\" href=\"/descent\">See today's no-cheat board \
         <span class=\"arr\" aria-hidden=\"true\">→</span></a></div>\
         <div class=\"offering-card shelf-services\"><h3>🧪 The Lab</h3>\
         <p class=\"tagline\">Experimental engine surfaces — nine games, nine feature surfaces, \
         five services. The parts the game is built from, on the shelf for the curious.</p>\
         <a class=\"play\" href=\"/offerings\">Browse the Lab \
         <span class=\"arr\" aria-hidden=\"true\">→</span></a></div>\
         <div class=\"offering-card shelf-features\"><h3>Sprite gallery</h3>\
         <p class=\"tagline\">Every asset's SVG sprite is a byte-identical function of its \
         content address — re-derivable, like everything else here.</p>\
         <a class=\"play\" href=\"/gallery\">Open the gallery \
         <span class=\"arr\" aria-hidden=\"true\">→</span></a></div>\
         </div></section></main>",
        board = hero_board(),
    );
    Html(document("DreggNet Cloud — play + verify", "", &body))
}
