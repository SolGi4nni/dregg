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
//! [`catalog_default_host`] registers three heterogeneous offerings — a dungeon (game), a council
//! (governance), a market (commerce). Because some sessions are `!Send`, the host runs on ONE owning
//! thread behind a `Send + Sync` [`HostThread`] handle (the discord-bot `Store` pattern generalised
//! to a whole registry) — the SAME host a Telegram / WeChat frontend adopts unchanged.
//!
//! ## Honest scope
//! This renders the affordance [`Surface`] as HTML **directly** (server-rendered forms). The
//! fuller path — `deos-js` + `deos-web-cells` (the live signal-bound web cell rendering, where
//! a `bind`/`gauge`/`tabs` node is a fine-grained reactive DOM binding) — is the follow-up, as
//! is a real deployment (a served bind address, a session store, `dregg-pay` credit debits on
//! the paid tier). What is proven here: a REAL `Frontend` over `dreggnet-offerings`, served via
//! axum, DRIVEN — affordances → HTML controls, a POST → an `Action` → one real turn, a session
//! playing through, executor-refereed, `verify` holding.

/// THE SPECTATOR / PROVENANCE surface for *The Descent* (the flagship's growth artifact): a
/// stranger opens a URL and INDEPENDENTLY re-verifies a run — a re-verified no-cheat leaderboard
/// (`GET /descent/leaderboard`) + a run-card that re-executes the recorded run to PASS/FAIL
/// (`GET /descent/run/{id}`). Additive; see [`descent::descent_router`].
pub mod descent;
/// The durable sqlite (rusqlite) backing for the Descent no-cheat leaderboard: persist a run's
/// reproducible public input (the day seed + the move sequence), re-verified by REPLAY on boot so
/// the board survives restart and a tampered row cannot resurrect a cheat. See [`descent_store`].
pub mod descent_store;
/// The seat-claiming adapter that makes `dregg-multiway-tug` playable by real frontend users (a web
/// identity is a derived key, never the game's canonical seat string). See [`seated::SeatedTug`].
pub mod seated;
/// The deterministic generative art surface: a `dreggnet_asset::AssetId` → a byte-identical SVG
/// sprite (`dreggnet-sprite`), served at `GET /sprite/{kind}/{ref}`, painted onto an asset-bearing
/// deos `Tile`, and shown in a `GET /gallery`. See [`sprite`].
pub mod sprite;

pub use descent::{DescentState, descent_router, run_share_path};

use std::collections::HashMap;
use std::sync::mpsc::{SyncSender, sync_channel};
use std::sync::{Arc, Mutex};

use axum::{
    Router,
    extract::{Form, Path, Query, State},
    http::{HeaderMap, header},
    response::{Html, IntoResponse, Json},
    routing::{get, post},
};
use serde::Deserialize;

use deos_view::{MenuItem, SessionFormBackend, SurfaceBackend, ViewNode};
use dregg_automatafl::AutomataflOffering;
use dreggnet_council::{CandidateProposal, CouncilOffering};
use dreggnet_market::MarketOffering;
use dreggnet_offerings::dungeon::{DungeonOffering, DungeonSession};
use dreggnet_offerings::{
    Action, DreggIdentity, Frontend, HostError, Offering, OfferingHost, OfferingInfo, Outcome,
    SessionConfig, SessionId, Surface, VerifyReport,
};

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
/// is derived deterministically (blake3 of the user id) so the SAME user → the SAME
/// [`DreggIdentity`] — mirroring the Discord `UserCipherclerk` derivation *shape* (the doc's
/// mandate: a derived cryptographic identity, not a nickname; the real web deployment would
/// derive a per-user Ed25519 key the same way the bot does).
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
        // Render through the deos-view server-form backend (the moved-in `view_html`): one POST
        // form per affordance, containers recursed so a nested affordance is never dropped. The
        // frontend no longer maintains its own subset walker.
        SessionFormBackend {
            session_id: session.0.clone(),
        }
        .render(surface.view(), &[])
    }
}

impl Frontend for WebFrontend {
    type PlatformUser = String;
    type PlatformEvent = WebEvent;

    /// Derive `user`'s [`DreggIdentity`] — blake3(user) hex. Deterministic: the SAME web user
    /// always maps to the SAME identity (mirroring the Discord `UserCipherclerk::derive(...)
    /// .public_key_hex()` derivation *shape*).
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
    /// The web user id — a deterministic input to identity derivation. Absent → the cookie, then
    /// `"anon"`.
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
                Outcome::Landed { ended, .. } => {
                    if ended {
                        "The Keep is cleared — the objective is met, one real turn at a time."
                            .to_string()
                    } else {
                        "Turn committed — a real verified receipt landed.".to_string()
                    }
                }
                // The executor is the sole referee: a crafted POST of a dimmed / ineligible
                // affordance lands as a REAL refusal — nothing committed, the world unmoved.
                Outcome::Refused(why) => {
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
        "<div class=\"crumb\"><a href=\"/offerings\">← all offerings</a>\
         <span class=\"sep\">·</span><strong>The Warden's Keep</strong>\
         <span class=\"sep\">·</span><span class=\"sid\">session {id}</span></div>\
         <main class=\"session\">{notice}{fragment}{receipt}</main>",
        id = esc(&id.0),
        notice = notice_html(notice),
        fragment = fragment,
        receipt = receipt_html(verify, "chain re-verified by replay"),
    );
    document(&format!("DreggNet Cloud — session {}", id.0), "", &body)
}

/// The page shown for a `POST` / verify against a session id that is not open.
fn page_missing(id: &SessionId) -> String {
    let body = format!(
        "<main class=\"session\"><div class=\"notice refused\" role=\"status\">No such session — \
         GET /session/{id} to open it.</div>\
         <p class=\"prose\"><a class=\"backlink\" href=\"/offerings\">← Browse the offerings</a></p>\
         </main>",
        id = esc(&id.0),
    );
    document(&format!("DreggNet Cloud — session {}", id.0), "", &body)
}

/// The web identity for a request — the `?user=` param, else the `dregg_user` cookie, else
/// `"anon"`. Fed to [`WebFrontend::identity`] (a deterministic derivation → a stable
/// [`DreggIdentity`]).
fn web_user(headers: &HeaderMap, query: &WebQuery) -> String {
    if let Some(u) = query.user.as_ref() {
        if !u.is_empty() {
            return u.clone();
        }
    }
    if let Some(cookie) = headers.get(header::COOKIE).and_then(|v| v.to_str().ok()) {
        for part in cookie.split(';') {
            let part = part.trim();
            if let Some(v) = part.strip_prefix("dregg_user=") {
                if !v.is_empty() {
                    return v.to_string();
                }
            }
        }
    }
    "anon".to_string()
}

/// **Derive a web user's frontend-agnostic [`DreggIdentity`]** — `blake3(user)` hex. Deterministic
/// (the SAME user → the SAME identity), mirroring the Discord `UserCipherclerk::derive(...)
/// .public_key_hex()` derivation *shape*. Shared by [`WebFrontend::identity`] and the multi-offering
/// catalog's POST handler so both attribute a turn to the same identity — and so a council registers
/// its members from the SAME derivation (`blake3(user)` bytes as the member pubkey; see
/// [`catalog_default_host`]).
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

/// The brand mark — four squares, one lit: a board where a move landed. Inline SVG (no external
/// asset, no request), `aria-hidden` because the adjacent brand text is the accessible name.
const MARK: &str = "<svg viewBox=\"0 0 24 24\" aria-hidden=\"true\" focusable=\"false\">\
     <rect x=\"1.5\" y=\"1.5\" width=\"9.5\" height=\"9.5\" rx=\"2.6\"></rect>\
     <rect x=\"13\" y=\"1.5\" width=\"9.5\" height=\"9.5\" rx=\"2.6\"></rect>\
     <rect x=\"1.5\" y=\"13\" width=\"9.5\" height=\"9.5\" rx=\"2.6\"></rect>\
     <rect class=\"lit\" x=\"13\" y=\"13\" width=\"9.5\" height=\"9.5\" rx=\"2.6\"></rect></svg>";

/// The sticky top bar — the product mark plus the three real surfaces. `active` names the current
/// one (`""` for none) so it can carry `aria-current="page"`.
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
         <nav class=\"topnav\" aria-label=\"Surfaces\">{offerings}{descent}{gallery}</nav>\
         </div></header>",
        MARK = MARK,
        offerings = item("/offerings", "offerings", "Offerings"),
        descent = item("/descent", "descent", "The Descent"),
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
     <nav aria-label=\"Footer\"><a href=\"/offerings\">Offerings</a>\
     <a href=\"/descent\">The Descent</a><a href=\"/gallery\">Gallery</a>\
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
        "<div class=\"crumb\"><a href=\"/offerings\">← all offerings</a>\
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
fn receipt_html(verify: &VerifyReport, label: &str) -> String {
    let cls = if verify.verified { "ok" } else { "refused" };
    format!(
        "<div class=\"receipt {cls}\"><span class=\"dot\"></span>\
         <span class=\"label\">{label}</span><span class=\"verdict\">{v}</span>\
         <span>{turns}</span><span class=\"detail\">{detail}</span></div>",
        cls = cls,
        label = esc(label),
        v = if verify.verified {
            "verified"
        } else {
            "NOT VERIFIED"
        },
        turns = turn_count(verify.turns),
        detail = esc(&verify.detail),
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
/// some of which are `!Send` (a [`CouncilOffering`] session holds `Rc`-backed ballot caps — the
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

/// **The axum state for the multi-offering catalog** — a thread-confined [`OfferingHost`] behind a
/// `Send + Sync` handle. Shared behind an `Arc` as the handler `State`.
pub struct CatalogState {
    /// The host handle (the registry of offerings + their live sessions, on its owning thread).
    host: HostThread,
}

impl CatalogState {
    /// A fresh catalog over the DEFAULT offerings (dungeon + council + market) — see
    /// [`catalog_default_host`].
    pub fn new() -> Self {
        CatalogState {
            host: HostThread::spawn(catalog_default_host),
        }
    }

    /// A catalog over a caller-built host (the offerings are registered inside `build`, which runs
    /// on the owning thread). Lets a deployment register its own offering set.
    pub fn with_host(build: impl FnOnce() -> OfferingHost + Send + 'static) -> Self {
        CatalogState {
            host: HostThread::spawn(build),
        }
    }

    /// The registered offerings (the catalog listing).
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
}

impl Default for CatalogState {
    fn default() -> Self {
        CatalogState::new()
    }
}

/// **The default catalog host** — registers the three heterogeneous offerings the web catalog
/// plays: the dungeon (a game), the council (governance), and the market (commerce). Built on the
/// host's owning thread ([`HostThread::spawn`]), so each offering's `!Send` internals stay confined.
///
/// The council's electorate is derived from web usernames so a browser user can really vote: a web
/// user's [`DreggIdentity`] is `blake3(user)` hex, and a council member's identity is the hex of its
/// pubkey — so setting a member's pubkey to `blake3(user)`'s bytes makes that web user a council
/// member (`alice` and `bob` here). Quorum is 2, so a proposal enacts only once BOTH approve — a
/// real vote, drivable through the browser.
pub fn catalog_default_host() -> OfferingHost {
    let mut host = OfferingHost::new();
    host.register(
        "dungeon",
        "The Warden's Keep — a verifiable dungeon (offering #0)",
        DungeonOffering::new(),
    );

    // The council electorate: the web users who can vote (member pubkey = blake3(user) bytes).
    let members: Vec<[u8; 32]> = ["alice", "bob"]
        .iter()
        .map(|u| *blake3::hash(u.as_bytes()).as_bytes())
        .collect();
    host.register(
        "council",
        "DreggNet Council — propose · vote · enact",
        CouncilOffering::new(
            members,
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

    // THE TWO PORTFOLIO GAMES — fully playable in the browser (and, through the SAME `Surface`,
    // on Discord / Telegram / WeChat: the do-once path).
    //
    // `tug` is wrapped in the seat-claiming [`SeatedTug`] adapter because `TugOffering` names its
    // seats by fixed canonical strings while a web user's identity is a derived key — the adapter
    // claims a seat for the first two identities that act, changing nothing in the game crate.
    // `automatafl` claims seats natively, so it is registered directly.
    host.register(
        "tug",
        "Multiway-Tug — a hidden-hand tug of influence (seven guilds · eight actions)",
        seated::SeatedTug::new(),
    );
    host.register(
        "automatafl",
        "Automatafl — the simultaneous-move board (seal a move · reveal · the automaton steps)",
        AutomataflOffering,
    );
    host
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
/// This is what turns the catalog from a subset into the WHOLE portfolio (five games + eight
/// feature surfaces + these five non-game offerings). Split from [`catalog_default_host`] so the
/// committed single-offering + games tests keep their smaller host while the demo mounts everything.
pub fn register_non_game_offerings(host: &mut OfferingHost) {
    host.register(
        "doc",
        "DreggNet Doc — a verifiable document store (author · amend · verify)",
        dreggnet_doc::DocOffering::new(),
    );
    host.register(
        "names",
        "DreggNet Names — an identity / naming service (register · transfer · resolve)",
        dreggnet_names::NamesOffering::new(),
    );
    host.register(
        "compute",
        "DreggNet Compute — a confined compute-job market (post · claim · settle)",
        dreggnet_compute::ComputeOffering::new(),
    );
    host.register(
        "grain",
        "DreggNet Grain — metered work under a spend budget (request · grant)",
        dreggnet_grain::GrainOffering::new(1000),
    );
    host.register(
        "hermes",
        "DreggNet Hermes — the message relay (send · deliver · ack)",
        dreggnet_hermes::HermesOffering::new(),
    );
}

/// **Build the multi-offering catalog router** over a shared [`CatalogState`]. Additive to
/// [`router`] — mount both on one axum app (or serve the catalog alone).
pub fn catalog_router(state: Arc<CatalogState>) -> Router {
    Router::new()
        .route("/offerings", get(get_catalog))
        .route("/offerings/{key}/session/{id}", get(get_offering_session))
        .route("/offerings/{key}/session/{id}/act", post(post_offering_act))
        .route(
            "/offerings/{key}/session/{id}/verify",
            get(get_offering_verify),
        )
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
) -> Html<String> {
    let sid = SessionId::new(id);
    // Ensure the session is open (deploy on first touch), then render.
    let opened = {
        let key = key.clone();
        let sid = sid.clone();
        state.host.run(move |h| h.ensure_open(&key, &sid))
    };
    if let Err(HostError::UnknownOffering(_)) = opened {
        return Html(catalog_missing_offering(&key));
    }
    // The viewer's derived identity (the `dregg_user` cookie / `?user=` param) — the SAME identity a
    // POST attributes a turn to. A seated player renders their OWN hidden hand; a spectator sees fog.
    let viewer = web_identity(&web_user(&headers, &query));
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
}

/// The `{turn, arg}` POST body of `POST /offerings/{key}/session/{id}/act`.
#[derive(Debug, Clone, Deserialize)]
pub struct OfferingActForm {
    /// The affordance verb (the offering's turn — `"choose"`, `"propose"`, `"approve"`, `"bid"`, …).
    pub turn: String,
    /// The affordance argument (a choice/proposal index, or a value-taking turn's value).
    #[serde(default)]
    pub arg: i64,
}

/// The result of collecting + resolving a catalog POST.
enum CatalogAct {
    /// The affordance was offered and resolved on the substrate (a real landed receipt / refusal).
    Advanced(Outcome),
    /// The turn is not on the current surface — an honest frontend-level refusal, before the substrate.
    NotOffered,
    /// The offering or session is absent (a routing miss).
    Missing,
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
) -> Html<String> {
    let sid = SessionId::new(id);
    // Ensure open first (so a POST to a fresh session still resolves against a live offering).
    let opened = {
        let key = key.clone();
        let sid = sid.clone();
        state.host.run(move |h| h.ensure_open(&key, &sid))
    };
    if let Err(HostError::UnknownOffering(_)) = opened {
        return Html(catalog_missing_offering(&key));
    }

    let actor = web_identity(&web_user(&headers, &query));

    // PRESENT the current surface + COLLECT the posted affordance + ADVANCE, atomically on the
    // host thread: the turn must be among the offering's current affordances (offered), then the
    // executor is the sole referee of the {turn, arg} on the substrate.
    let acted = {
        let key = key.clone();
        let sid = sid.clone();
        let turn = form.turn.clone();
        let arg = form.arg;
        let actor = actor.clone();
        state.host.run(move |h| {
            // Validate against the affordances THIS actor sees (`actions_for`) — a viewer is offered
            // only what their caps allow; the executor remains the sole referee of the typed turn.
            let Some(actions) = h.actions_for(&key, &sid, &actor) else {
                return CatalogAct::Missing;
            };
            if !actions.iter().any(|a| a.turn == turn) {
                return CatalogAct::NotOffered;
            }
            // The label + enabled are decoration; the executor resolves the TYPED (turn, arg).
            let action = Action::new(turn.clone(), turn, arg, true);
            match h.advance(&key, &sid, action, actor) {
                Some(o) => CatalogAct::Advanced(o),
                None => CatalogAct::Missing,
            }
        })
    };

    let notice = match acted {
        CatalogAct::Advanced(Outcome::Landed { ended, .. }) => {
            if ended {
                "Turn committed — the session reached its objective, one real turn at a time."
                    .to_string()
            } else {
                "Turn committed — a real verified receipt landed.".to_string()
            }
        }
        CatalogAct::Advanced(Outcome::Refused(why)) => {
            format!("Refused: {why} (nothing committed — anti-ghost).")
        }
        CatalogAct::NotOffered => {
            "Refused: that affordance is not on the current surface.".to_string()
        }
        CatalogAct::Missing => "Refused: no such offering session.".to_string(),
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
}

/// `GET /offerings/{key}/session/{id}/verify` — re-verify the committed chain by the offering's own
/// proof, exposed over HTTP as JSON.
async fn get_offering_verify(
    State(state): State<Arc<CatalogState>>,
    Path((key, id)): Path<(String, String)>,
) -> impl IntoResponse {
    let sid = SessionId::new(id);
    match state.verify(&key, &sid) {
        Some(report) => Json(serde_json::json!({
            "verified": report.verified,
            "turns": report.turns,
            "detail": report.detail,
        })),
        None => Json(serde_json::json!({
            "verified": false,
            "turns": 0,
            "detail": "no such offering session",
        })),
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
    let rendered = {
        let key = key.to_string();
        let id = id.clone();
        let viewer = viewer.clone();
        // Render AS the viewer — the per-player projection (own hidden hand revealed, others fog),
        // NOT the viewer-blind `render`. This is the host-boundary fix reaching the web surface.
        state
            .host
            .run(move |h| h.render_for(&key, &id, &viewer).zip(h.verify(&key, &id)))
    };
    let (surface, verify) = rendered?;
    let forms = render_catalog_forms(surface.view(), key, &id.0);
    Some(format!(
        "{notice}{forms}{receipt}",
        notice = notice_html(notice),
        forms = forms,
        receipt = receipt_html(&verify, "chain re-verified by replay"),
    ))
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
    offering_page(&title, id, &surface)
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
fn render_catalog_forms(node: &ViewNode, key: &str, id: &str) -> String {
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
        ViewNode::Tabs { panels, .. } => {
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
        _ => {}
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
        "<form class=\"{cls}\" method=\"post\" action=\"/offerings/{key}/session/{id}/act\">\
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

/// The `GET /offerings` catalog page — a card + "play" link per registered offering.
fn catalog_page(offerings: &[OfferingInfo]) -> String {
    // Group the catalog into coherent shelves so ~18 offerings read as three clear categories,
    // not one flat wall of look-alike cards: the GAMES (play to win / verify), the RPG FEATURE
    // surfaces (the do-once render path), and the verifiable SERVICES. Any offering outside the
    // known sets falls into a catch-all "More" shelf (so a future registration still shows up).
    const GAMES: &[&str] = &["dungeon", "council", "market", "tug", "automatafl"];
    // NOTE `cheevos`, not `cheevo`: `dreggnet_surfaces::register_surfaces` registers the
    // achievements surface under the PLURAL key. The singular never matched, so Achievements has
    // been silently falling through to the catch-all "More" shelf instead of sitting with the other
    // seven feature surfaces. (The per-shelf count added by this design pass is what surfaced it:
    // the shelf read "7".)
    const FEATURES: &[&str] = &[
        "trade",
        "inventory",
        "cheevos",
        "guild",
        "craft",
        "companion",
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

    let body = format!(
        "<main class=\"catalog\"><div class=\"page-head\">\
         <p class=\"eyebrow\">All offerings, any surface</p>\
         <h1>Pick a thing and play it.</h1>\
         <p class=\"deck\">Every offering is a confined, verifiable, per-session thing on the real \
         dregg substrate. Each move is a real executor turn, refereed on the substrate — no node, \
         no testnet: verification is in-process re-execution.</p></div>\
         {games}{features}{services}{more}</main>",
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
fn offering_page(title: &str, id: &SessionId, surface: &str) -> String {
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
         <div id=\"live-surface\" class=\"live-surface\" tabindex=\"-1\" aria-live=\"polite\">{surface}</div>\
         </main>",
        crumb = crumb(name, id),
        name = esc(name),
        tagline = tagline_html,
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
//    Unset → the in-RAM seeded demo (the committed tests' path). STILL EPHEMERAL: the live game
//    SESSIONS (`WebState` / the catalog `OfferingHost`) — a restart drops in-progress sessions;
//    what is durable is the leaderboard (the shareable, re-verifiable growth artifact).
//  * An HTTP run-INGEST endpoint — `POST /descent/submit` (see `descent::post_submit`): a stranger
//    submits a run's reproducible input (day + player + move sequence); it is re-executed +
//    no-cheat-verified before it can rank (an honest run ingested + persisted, a forged run 4xx).
//
// NAMED (ops / ember-gated), deliberately not built here:
//  * TLS / rate-limit / CORS — a fronting Caddy (ops, external; `demo.dregg.net` terminates TLS
//    there and reverse-proxies to this bind).
//  * AUTH — the web identity is the unsigned `dregg_user` cookie / `?user=` (a derived key, not
//    a signed credential); a real deployment derives a per-user Ed25519 key as the bot does.
// ═════════════════════════════════════════════════════════════════════════════════════════

/// **The public-demo offering host** — the five games ([`catalog_default_host`]: dungeon, council,
/// market, tug, automatafl) PLUS the eight do-once feature surfaces
/// ([`dreggnet_surfaces::register_surfaces`]: trade, inventory, cheevos, guild, craft, companion,
/// tavern, party). Built on the host's owning thread (so each offering's `!Send` internals stay
/// confined), it is the registry the demo catalog browses + plays.
pub fn demo_host() -> OfferingHost {
    let mut host = catalog_default_host();
    dreggnet_surfaces::register_surfaces(&mut host);
    register_non_game_offerings(&mut host);
    host
}

/// **The seeded no-cheat Descent leaderboard state** for the demo — opens today's beacon-seeded day
/// (a fixed seed standing in for the live drand beacon) and ingests a real, driven-to-the-hoard
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
    use procgen_dregg::daily_seed;

    // warden HP 45 (no field-dressing needed) -> a replay-clean honest win.
    let seed = daily_seed(&[3; 32]);
    let (win_moves, win_level, win_class) = demo_win();
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
/// hoard on the demo day (`daily_seed(&[3; 32])`), plus the winner's character level + class. The
/// same careful line `dreggnet-offerings`' own driven board test uses (works for any beacon-drawn
/// warden HP / depth). Exposed so the demo state and the persistence/ingest tests share ONE source
/// of the winning moves.
pub fn demo_win() -> (Vec<usize>, u64, u64) {
    use dreggnet_offerings::DreggIdentity;
    use dreggnet_offerings::character::InMemoryCharacterStore;
    use dreggnet_offerings::daily_descent::{
        CORRIDOR_ON, DailyDescentOffering, GATE_HEAL, GATE_MEASURED, GATE_PRESS, HOARD_FORCE,
        HOARD_SEIZE, KEY_TAKE,
    };
    use procgen_dregg::daily_seed;

    let seed = daily_seed(&[3; 32]);
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
/// - [`catalog_router`] over [`demo_host`] — the games + feature-surface catalog (`/offerings` …);
/// - [`descent_router`] over [`demo_descent_state`] — the seeded no-cheat Descent leaderboard
///   (`/descent/leaderboard`, `/descent/run/{id}`).
///
/// Factored out of the bin so it is drivable in tests with no real network (axum `oneshot`).
///
/// **Persistence.** The Descent leaderboard is durable when a `DATABASE_URL` is set (a sqlite path
/// / `sqlite:` url; see [`resolve_demo_descent`]): submitted runs survive a restart, re-verified by
/// replay on boot. With `DATABASE_URL` unset (the committed tests' path) the board is the in-RAM
/// seeded demo — nothing persists, so the existing suite is unaffected. To serve a specific
/// pre-built descent state (e.g. a test's sqlite store), use [`make_app_with_descent`].
pub fn make_app() -> Router {
    make_app_with_descent(resolve_demo_descent())
}

/// [`make_app`] over a caller-supplied [`DescentState`] (the games + catalog + single-offering
/// surfaces are unchanged). Lets a deployment / a test wire its own — durable or in-RAM — Descent
/// board while reusing the whole merged app.
pub fn make_app_with_descent(descent: Arc<DescentState>) -> Router {
    let web = Arc::new(WebState::new());
    let catalog = Arc::new(CatalogState::with_host(demo_host));

    Router::new()
        .route("/", get(index))
        .route("/health", get(health))
        .merge(router(web))
        .merge(catalog_router(catalog))
        .merge(descent_router(descent))
        .merge(sprite::sprite_router())
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
    let body = format!(
        "<section class=\"hero\">\
         <div class=\"hero-copy\">\
         <p class=\"eyebrow\">Verifiable games · node-free</p>\
         <h1>Every move is a receipt.</h1>\
         <p class=\"deck\">Play a board, a market, a hidden-hand tug — in your browser, with no \
         client JavaScript. Every move is a real executor turn, refereed on the substrate. Nothing \
         here is taken on trust: a run re-executes, or it fails.</p>\
         <div class=\"cta-row\">\
         <a class=\"btn btn-primary\" href=\"/offerings\">Browse the offerings \
         <span class=\"arr\" aria-hidden=\"true\">→</span></a>\
         <a class=\"btn btn-ghost\" href=\"/descent\">Open the leaderboard</a>\
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
         <div class=\"offering-card shelf-games\"><h3>All offerings</h3>\
         <p class=\"tagline\">Five games, eight feature surfaces and five services — each one \
         playable in the browser through the same verbs.</p>\
         <a class=\"play\" href=\"/offerings\">Browse the catalog \
         <span class=\"arr\" aria-hidden=\"true\">→</span></a></div>\
         <div class=\"offering-card shelf-services\"><h3>The Descent</h3>\
         <p class=\"tagline\">A no-cheat leaderboard. Every run is re-executed on render — a \
         forged one shows FAIL, not a fake pass.</p>\
         <a class=\"play\" href=\"/descent\">Open the leaderboard \
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
