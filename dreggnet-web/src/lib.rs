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

/// Wrap an HTML fragment in a full document with the notice banner + the live verify line.
fn page(id: &SessionId, notice: Option<&str>, fragment: &str, verify: &VerifyReport) -> String {
    let notice_html = notice
        .map(|n| {
            let cls = if n.starts_with("Refused") {
                "notice refused"
            } else {
                "notice ok"
            };
            format!("<div class=\"{cls}\">{}</div>", esc(n))
        })
        .unwrap_or_default();
    let verify_cls = if verify.verified { "ok" } else { "refused" };
    let verify_html = format!(
        "<div class=\"verify {cls}\">chain re-verified by replay: <strong>{v}</strong> \
         ({turns} verified turns) — {detail}</div>",
        cls = verify_cls,
        v = if verify.verified { "yes" } else { "NO" },
        turns = verify.turns,
        detail = esc(&verify.detail),
    );
    format!(
        "<!doctype html><html lang=en><head><meta charset=utf-8>\
         <meta name=viewport content=\"width=device-width, initial-scale=1\">\
         <title>DreggNet Cloud — session {id}</title>{style}</head><body>\
         <main class=\"session\">{notice}{fragment}{verify}</main></body></html>",
        id = esc(&id.0),
        style = STYLE,
        notice = notice_html,
        fragment = fragment,
        verify = verify_html,
    )
}

/// The page shown for a `POST` / verify against a session id that is not open.
fn page_missing(id: &SessionId) -> String {
    format!(
        "<!doctype html><html lang=en><head><meta charset=utf-8>\
         <title>DreggNet Cloud — session {id}</title>{style}</head><body>\
         <main class=\"session\"><div class=\"notice refused\">No such session — \
         GET /session/{id} to open it.</div></main></body></html>",
        id = esc(&id.0),
        style = STYLE,
    )
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

/// The page's inlined stylesheet (self-contained; no external assets). The board (`.coordgrid` +
/// `.cell` + `tag-*`) ports deos-view's `.deos-coordgrid`/`.deos-cell` design onto this SERVER-FORM
/// render path (a centered framed grid of square, tinted, clickable cells) — the surface a
/// no-JS demo user actually sees. The palette is the catalog #0b1020 navy theme.
const STYLE: &str = "<style>\
:root{--bg:#0b1020;--fg:#dfe8fb;--muted:#8fa2c4;--accent:#5cc9ff;--accent-ink:#04121f;--border:#243352;--panel:#111a2e;--card:#0f1830;--good:#48d597;--warn:#f2c94c;--bad:#f8737f;--head:#7fdfe0}\
*{box-sizing:border-box}\
body{font-family:ui-sans-serif,system-ui,-apple-system,sans-serif;background:radial-gradient(1200px 620px at 50% -10%,#101a34,var(--bg)) fixed,var(--bg);color:var(--fg);margin:0;padding:2rem 1.25rem 3rem;line-height:1.55}\
.session{max-width:44rem;margin:0 auto}\
.deos-section{border:1px solid var(--border);border-radius:12px;padding:1rem 1.25rem;margin:1rem 0;background:linear-gradient(180deg,#131f38,var(--panel));box-shadow:0 8px 30px -22px #000,inset 0 1px 0 rgba(255,255,255,.02)}\
.deos-section h2{margin:0 0 .55rem;font-size:1.02rem;letter-spacing:.01em;color:var(--head);display:flex;align-items:center;gap:.45rem}\
.deos-section h2::before{content:\"\";width:.5rem;height:.5rem;border-radius:2px;background:currentColor;opacity:.7}\
.tag-accent h2{color:var(--accent)}.tag-genuine h2,.tag-good h2{color:var(--good)}.tag-warn h2{color:var(--warn)}.tag-muted h2{color:var(--muted);font-weight:600}\
.prose{margin:.4rem 0;color:#d7e2fb}\
.prose code{background:#0a1326;border:1px solid var(--border);border-radius:5px;padding:.05rem .35rem;font-size:.88em;color:#bfe0ff}\
.affordances{display:flex;flex-direction:column;gap:.5rem;margin:.4rem 0}\
.affordance{margin:0}\
.affordance button{width:100%;text-align:left;padding:.62rem .95rem;border-radius:9px;border:1px solid #2f4d3f;background:linear-gradient(180deg,#14261d,#0f1c17);color:#e6fff2;font:inherit;font-size:.98rem;font-weight:600;cursor:pointer;transition:border-color .12s,background .12s,transform .07s,box-shadow .12s}\
.affordance button:hover{border-color:var(--good);background:linear-gradient(180deg,#1a3a2a,#123);transform:translateY(-1px);box-shadow:0 6px 18px -10px var(--good)}\
.affordance button:active{transform:translateY(0)}\
.affordance.dimmed button{border-color:#3a2a2a;color:#8a7676;background:#1a1414;cursor:not-allowed;opacity:.6;box-shadow:none;transform:none}\
.affordance input.arg{width:100%;margin-bottom:.4rem;padding:.45rem .65rem;border-radius:8px;border:1px solid var(--border);background:#0a1326;color:var(--fg);font:inherit;font-size:.95rem}\
.affordance input.arg:focus{outline:none;border-color:var(--accent);box-shadow:0 0 0 2px rgba(92,201,255,.2)}\
.notice{padding:.65rem .95rem;border-radius:9px;margin-bottom:1rem;font-weight:600;border:1px solid var(--border)}\
.notice.ok{background:rgba(72,213,151,.1);color:#9df3c6;border-color:#2f6b4d}\
.notice.refused{background:rgba(248,115,127,.1);color:#ffb0b6;border-color:#7a3a3f}\
.verify{margin-top:1rem;font-size:.85rem;color:var(--muted)}\
.verify.ok strong{color:var(--good)}.verify.refused strong{color:var(--bad)}\
.catalog{max-width:44rem;margin:0 auto}\
.catalog h1,.session h1{font-size:1.5rem;letter-spacing:-.01em;color:var(--head);margin:.2rem 0 1rem}\
.offering-card{border:1px solid var(--border);border-radius:12px;padding:1.1rem 1.3rem;margin:1rem 0;background:linear-gradient(180deg,#131f38,var(--panel));box-shadow:0 8px 30px -22px #000;transition:border-color .12s,transform .12s}\
.offering-card:hover{border-color:var(--accent);transform:translateY(-2px)}\
.offering-card h2{margin:0 0 .35rem;font-size:1.12rem;color:var(--accent)}\
.offering-card a.play{display:inline-block;margin-top:.65rem;padding:.5rem 1rem;border-radius:9px;border:1px solid #2f4d3f;background:linear-gradient(180deg,#14261d,#0f1c17);color:#e6fff2;font-weight:600;text-decoration:none;transition:border-color .12s,background .12s,transform .07s}\
.offering-card a.play:hover{border-color:var(--good);background:#1a3a2a;transform:translateY(-1px)}\
.crumb{max-width:44rem;margin:0 auto 1rem;font-size:.85rem;color:var(--muted)}\
.crumb a{color:var(--head);text-decoration:none}.crumb a:hover{text-decoration:underline}\
table.board{width:100%;border-collapse:collapse;margin:1rem 0;font-size:.95rem}\
table.board th,table.board td{text-align:left;padding:.55rem .65rem;border-bottom:1px solid var(--border)}\
table.board th{color:var(--head);font-size:.78rem;text-transform:uppercase;letter-spacing:.06em}\
table.board tr:hover td{background:rgba(92,201,255,.04)}\
table.board td a{color:var(--good);text-decoration:none;font-weight:600}table.board td a:hover{text-decoration:underline}\
/* THE GAME BOARD — a centered, framed grid of square, tinted, clickable cells (ported from deos-view). */\
.coordgrid{display:grid;gap:.35rem;width:100%;max-width:24rem;margin:1rem auto;padding:.55rem;background:#0a1326;border:1px solid var(--border);border-radius:14px;box-shadow:inset 0 0 0 1px rgba(0,0,0,.35),0 10px 30px -18px #000}\
.coordgrid .cell{display:flex;align-items:center;justify-content:center;aspect-ratio:1/1;min-width:1.9rem;border:1px solid var(--border);border-radius:8px;background:#0d1830;color:var(--muted);font-size:1.25rem;font-weight:700;line-height:1;margin:0;transition:border-color .12s,background .12s,color .12s,transform .07s,box-shadow .12s}\
.coordgrid form.cell{padding:0;cursor:pointer}\
.coordgrid form.cell button{width:100%;height:100%;display:flex;align-items:center;justify-content:center;border:0;border-radius:inherit;background:transparent;color:inherit;font:inherit;font-size:1.25rem;font-weight:700;cursor:pointer;padding:0}\
.coordgrid form.cell:hover{border-color:var(--accent);background:#15315a;color:#fff;transform:translateY(-1px);box-shadow:0 5px 16px -7px var(--accent)}\
.coordgrid form.cell:active{transform:translateY(0)}\
.coordgrid .cell.highlighted{color:#eaf5ff;border-color:var(--good);box-shadow:inset 0 0 0 1px var(--good),0 0 12px -4px var(--good)}\
.coordgrid form.cell.highlighted:hover{border-color:var(--good);box-shadow:0 5px 16px -6px var(--good)}\
.coordgrid .cell.tag-good{color:var(--good)}\
.coordgrid .cell.tag-warn{color:var(--warn);border-color:var(--warn);box-shadow:inset 0 0 0 1px var(--warn)}\
.coordgrid .cell.tag-accent{color:#f2fbff;border-color:var(--accent);background:radial-gradient(circle at 50% 42%,rgba(92,201,255,.34),#0d1830 72%);box-shadow:inset 0 0 0 1px var(--accent),0 0 14px -4px var(--accent)}\
.coordgrid .cell.tag-muted{color:#4d6187}\
.pill{display:inline-block;padding:.18rem .6rem;margin:.15rem .35rem .15rem 0;border-radius:999px;border:1px solid var(--border);background:#0a1326;font-size:.8rem;font-weight:600;color:var(--muted)}\
.pill.tag-accent{color:var(--accent);border-color:#2b5f7a}.pill.tag-good{color:var(--good);border-color:#2f6b4d}.pill.tag-warn{color:var(--warn);border-color:#6b5b24}\
.icon{font-size:1.05rem}.icon.tag-accent{color:var(--accent)}.icon.tag-good{color:var(--good)}.icon.tag-warn{color:var(--warn)}\
hr{border:0;border-top:1px solid var(--border);margin:1rem 0}\
</style>";

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
    Html(render_offering_page(&state, &key, &sid, None))
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
        state.host.run(move |h| {
            let Some(actions) = h.actions(&key, &sid) else {
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

    Html(render_offering_page(&state, &key, &sid, Some(&notice)))
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

/// Render an offering session as a full HTML page: its [`Surface`] as POST forms + the live verify
/// line + an optional notice banner. Fetches the surface + verify report from the host thread.
fn render_offering_page(
    state: &CatalogState,
    key: &str,
    id: &SessionId,
    notice: Option<&str>,
) -> String {
    let rendered = {
        let key = key.to_string();
        let id = id.clone();
        state
            .host
            .run(move |h| h.render(&key, &id).zip(h.verify(&key, &id)))
    };
    let Some((surface, verify)) = rendered else {
        return page_missing(id);
    };
    let title = state
        .host
        .run({
            let key = key.to_string();
            move |h| h.title(&key).map(|t| t.to_string())
        })
        .unwrap_or_else(|| key.to_string());
    let fragment = render_catalog_forms(surface.view(), key, &id.0);
    offering_page(&title, id, notice, &fragment, &verify)
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
            out.push_str(&format!(
                "<div class=\"coordgrid\" style=\"grid-template-columns:repeat({},1fr)\">",
                (*cols).max(1)
            ));
            for cell in cells {
                let hl = if cell.highlight { " highlighted" } else { "" };
                let tag = if cell.tag.is_empty() {
                    String::new()
                } else {
                    format!(" tag-{}", esc(&cell.tag))
                };
                if cell.turn.is_empty() {
                    out.push_str(&format!(
                        "<span class=\"cell{hl}{tag}\">{glyph}</span>",
                        glyph = esc(&cell.glyph),
                    ));
                } else {
                    out.push_str(&format!(
                        "<form class=\"cell{hl}{tag}\" method=\"post\" \
                         action=\"/offerings/{key}/session/{id}/act\">\
                         <input type=\"hidden\" name=\"turn\" value=\"{turn}\">\
                         <input type=\"hidden\" name=\"arg\" value=\"{arg}\">\
                         <button type=\"submit\">{glyph}</button></form>",
                        key = esc(key),
                        id = esc(id),
                        turn = esc(&cell.turn),
                        arg = cell.arg,
                        glyph = esc(&cell.glyph),
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
        ViewNode::VStack(cs) | ViewNode::Row(cs) | ViewNode::List(cs) | ViewNode::Table(cs) => {
            for c in cs {
                catalog_node(c, key, id, out);
            }
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
         <input class=\"arg\" type=\"number\" name=\"arg\" value=\"{arg}\">\
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
    let mut cards = String::new();
    for o in offerings {
        cards.push_str(&format!(
            "<div class=\"offering-card\"><h2>{title}</h2>\
             <p class=\"prose\">key <code>{key}</code> · {n} open session(s)</p>\
             <a class=\"play\" href=\"/offerings/{key}/session/{key}-web\">▶ Play {key}</a></div>",
            title = esc(&o.title),
            key = esc(&o.key),
            n = o.open_sessions,
        ));
    }
    format!(
        "<!doctype html><html lang=en><head><meta charset=utf-8>\
         <meta name=viewport content=\"width=device-width, initial-scale=1\">\
         <title>DreggNet Cloud — offerings</title>{style}</head><body>\
         <main class=\"catalog\"><h1>DreggNet Cloud — all offerings, any surface</h1>\
         <p class=\"prose\">Every offering is a confined, verifiable, per-session thing on the real \
         dregg substrate. Pick one to play it in the browser — each move is a real executor turn.</p>\
         {cards}</main></body></html>",
        style = STYLE,
        cards = cards,
    )
}

/// Wrap an offering session's fragment in a full HTML page (breadcrumb + notice + verify line).
fn offering_page(
    title: &str,
    id: &SessionId,
    notice: Option<&str>,
    fragment: &str,
    verify: &VerifyReport,
) -> String {
    let notice_html = notice
        .map(|n| {
            let cls = if n.starts_with("Refused") {
                "notice refused"
            } else {
                "notice ok"
            };
            format!("<div class=\"{cls}\">{}</div>", esc(n))
        })
        .unwrap_or_default();
    let verify_cls = if verify.verified { "ok" } else { "refused" };
    let verify_html = format!(
        "<div class=\"verify {cls}\">chain re-verified: <strong>{v}</strong> \
         ({turns} verified turns) — {detail}</div>",
        cls = verify_cls,
        v = if verify.verified { "yes" } else { "NO" },
        turns = verify.turns,
        detail = esc(&verify.detail),
    );
    format!(
        "<!doctype html><html lang=en><head><meta charset=utf-8>\
         <meta name=viewport content=\"width=device-width, initial-scale=1\">\
         <title>DreggNet Cloud — {title}</title>{style}</head><body>\
         <div class=\"crumb\"><a href=\"/offerings\">← all offerings</a> · \
         <strong>{title}</strong> · session {id}</div>\
         <main class=\"session\">{notice}{fragment}{verify}</main></body></html>",
        title = esc(title),
        id = esc(&id.0),
        style = STYLE,
        notice = notice_html,
        fragment = fragment,
        verify = verify_html,
    )
}

/// The page shown for a `GET`/`POST` against an unregistered offering key.
fn catalog_missing_offering(key: &str) -> String {
    format!(
        "<!doctype html><html lang=en><head><meta charset=utf-8>\
         <title>DreggNet Cloud — unknown offering</title>{style}</head><body>\
         <main class=\"session\"><div class=\"notice refused\">No offering registered under \
         <code>{key}</code>. <a href=\"/offerings\">Browse the catalog.</a></div></main></body></html>",
        key = esc(key),
        style = STYLE,
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

/// `GET /` — the demo landing page: what this is + links to the catalog and the no-cheat board.
async fn index() -> Html<String> {
    Html(format!(
        "<!doctype html><html lang=en><head><meta charset=utf-8>\
         <meta name=viewport content=\"width=device-width, initial-scale=1\">\
         <title>DreggNet Cloud — play + verify</title>{style}</head><body>\
         <main class=\"catalog\"><h1>DreggNet Cloud</h1>\
         <p class=\"prose\">Play verifiable games and browse feature offerings in your browser — \
         every move is a real executor turn, refereed on the substrate. The no-cheat leaderboard \
         re-verifies each run by replay: a forged run shows FAIL, not a fake pass. No node, no \
         testnet — verification is in-process re-execution.</p>\
         <div class=\"offering-card\"><h2>All offerings</h2>\
         <p class=\"prose\">The five games + the eight feature surfaces.</p>\
         <a class=\"play\" href=\"/offerings\">▶ Browse the catalog</a></div>\
         <div class=\"offering-card\"><h2>The Descent — no-cheat leaderboard</h2>\
         <p class=\"prose\">Independently re-verified runs of the daily descent.</p>\
         <a class=\"play\" href=\"/descent\">▶ Open the leaderboard</a></div>\
         </main></body></html>",
        style = STYLE,
    ))
}
