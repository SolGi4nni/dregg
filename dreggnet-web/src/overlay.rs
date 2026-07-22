//! # `overlay` — the transparent OBS vote overlay + the live SSE push
//!
//! The spectator surface of the crowd-stream engine (`docs/CROWD-STREAM-ENGINE-DESIGN.md`): a
//! **transparent-background OBS browser source** that shows the crowd's live vote tally, updated by
//! a real **server→browser push**. There is no SSE/WebSocket anywhere else in `dreggnet-web` today
//! (the only liveness is a client-initiated `X-Fragment` swap on the acting client's OWN POST); an
//! overlay showing *other people's* votes needs the server to push, so this module adds the first
//! `axum::response::sse::Sse` route + a broadcast-on-vote fan-out.
//!
//! ## The pieces
//!
//! * [`OverlayState`] — a [`crate::crowd_round::CrowdRound`] behind a mutex + a
//!   [`tokio::sync::broadcast`] channel of rendered tally-widget HTML. An ingest updates the round
//!   and broadcasts the re-rendered widget to every connected overlay.
//! * [`overlay_document`] — the transparent OBS page: `background: transparent`, all chrome
//!   stripped, one `#tally` container the SSE client swaps `innerHTML` on. It reuses the deos
//!   [`deos_view::render_html`] renderer (the SAME `ViewNode` IR the cockpit paints) for the widget.
//! * [`overlay_router`] — `GET /overlay` (the page), `GET /overlay/sse` (the push stream),
//!   `POST /overlay/ingest` + `/overlay/ingest/youtube` (feed votes; each broadcasts the new tally).
//!
//! ## Honest scope
//!
//! The widget is a **static snapshot re-rendered + pushed server-side** on every vote (not an in-tab
//! wasm executor like the deos live cards) — right for an overlay whose data comes from the stream,
//! not from the viewer's tab.
//!
//! Resolving a window into a certified world turn ([`OverlayState::close_tick`] /
//! [`OverlayState::drive_close`]) needs a live game `WorldCell` + `Scene` and a timer. Two mounts
//! exist, chosen by [`overlay_mount_from_env`]:
//! * **default (`OVERLAY_LIVE_WORLD` unset)** — the [`demo_state_from_env`] TALLY BOARD: ingest→push
//!   only, no world resolve (honestly labeled). Byte-identical to before.
//! * **opt-in (`OVERLAY_LIVE_WORLD` set)** — a [`LiveCloseLoop`] over a live demo Warden's Keep
//!   `WorldCell` + `Scene`, whose [`LiveCloseLoop::run`] drives [`OverlayState::drive_close`] on a
//!   [`tokio::time::interval`] (`OVERLAY_ROUND_SECONDS`): each window ingests → tallies → at close
//!   resolves the quorum-certified winner into the world as ONE real [`CertifiedTurn`] → pushes the
//!   (reset) tally over SSE. The stuck-window case (a quorum-certified but ILLEGAL command) is
//!   dropped so the round is never bricked; a below-quorum window is retained for retry.
//!
//! **"Certified" here means quorum-certified + executor-admitted, NOT FRI-sound-on-chain** — it
//! inherits the deployed ledger's undischarged FRI/STARK floor. The mounted world is a small **demo**
//! (the Keep), a poll-driven scene the crowd steers; a real deployment supplies its own game world.
//! Platform API keys, an OBS instance, and a LIVE-enabled channel are ember's.

use std::convert::Infallible;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use axum::Router;
use axum::extract::State;
use axum::http::{HeaderMap, StatusCode};
use axum::response::sse::{Event, KeepAlive, Sse};
use axum::response::{Html, IntoResponse, Json, Response};
use axum::routing::{get, post};
use base64::Engine;
use base64::engine::general_purpose::STANDARD as BASE64;
use subtle::ConstantTimeEq;
use tokio::sync::broadcast;
use tokio_stream::wrappers::BroadcastStream;
use tokio_stream::{Stream, StreamExt};
use zeroize::Zeroizing;

use deos_view::{ViewNode, render_html};
use dregg_stream_ingest::{
    PlatformAdapter, StreamEvent, YouTubeAdapter, YouTubeLivePage, parse_youtube_live_page,
};
use dungeon_on_dregg::collective::{CertifiedTurn, CollectiveError, Proposal, QUORUM};
use dungeon_on_dregg::narrator::Command;
use dungeon_on_dregg::{deploy_keep, keep_scene};
use spween_dregg::{Scene, Value, WorldCell};

use crate::crowd_round::{CrowdCloseError, CrowdRound, TallyPreview};

/// The env var an operator/OBS sets to the bearer token that authorizes `POST /overlay/ingest[/youtube]`.
/// UNSET ⇒ the ingest routes are **fail-closed** (every POST refused): the demo overlay is a
/// read-only tally board until an operator token is configured (or the server-side [`YouTubePoller`]
/// feeds it directly). See [`OverlayState::with_ingest_token`].
pub const OVERLAY_INGEST_TOKEN_ENV: &str = "OVERLAY_INGEST_TOKEN";

/// The env var supplying the operator's YouTube Data API key for the server-side [`YouTubePoller`]
/// (the authenticated fetch path). See [`youtube_poller_from_env`].
pub const YOUTUBE_API_KEY_ENV: &str = "YOUTUBE_API_KEY";
/// The env var supplying the `liveChatId` of the active broadcast the [`YouTubePoller`] polls.
pub const YOUTUBE_LIVE_CHAT_ID_ENV: &str = "YOUTUBE_LIVE_CHAT_ID";

/// The broadcast channel depth — a slow overlay that falls this far behind drops the stale frames
/// (a `Lagged` the SSE stream skips) and catches up on the next push. Tally frames are idempotent
/// snapshots, so a dropped intermediate frame is harmless.
const BROADCAST_CAPACITY: usize = 64;

/// **The live overlay state.** Wraps a [`CrowdRound`] (the vote accumulator) and a broadcast
/// channel of rendered tally-widget HTML. Every ingest advances the round and pushes the freshly
/// rendered widget to all connected overlays; `GET /overlay/sse` subscribes.
pub struct OverlayState {
    round: Mutex<CrowdRound>,
    tx: broadcast::Sender<String>,
    /// The last rendered widget HTML — the first-paint a fresh `GET /overlay` / a new SSE
    /// subscriber receives before the next push.
    last_html: Mutex<String>,
    /// `blake3(operator bearer token)`, or `None` if no token is configured. When `None`, the
    /// `POST /overlay/ingest[/youtube]` routes are **fail-closed** (every POST refused): the raw
    /// POST ingest is forgeable (it trusts the caller's `amount_micros`), so on a public port it
    /// is gated behind this operator secret. Stored as the hash so the plaintext is never held; a
    /// presented bearer is hashed and constant-time compared (see [`authorize_ingest`]).
    ///
    /// [`authorize_ingest`]: OverlayState::authorize_ingest
    ingest_token: Option<[u8; 32]>,
    /// An optional honesty label shown on the `GET /overlay` page chrome (e.g. the demo mount's
    /// "tally board — no world resolve"). `None` for a real overlay (the transparent OBS source
    /// stays clean). See [`demo_state`].
    label: Option<String>,
}

impl OverlayState {
    /// Wrap a [`CrowdRound`] in a fresh overlay state (an empty broadcast + the round's current
    /// tally as the first paint). No ingest token (HTTP ingest fail-closed) and no page label — a
    /// real deployment adds a token via [`with_ingest_token`](Self::with_ingest_token) and/or feeds
    /// the round from the server-side [`YouTubePoller`].
    pub fn new(round: CrowdRound) -> Arc<OverlayState> {
        let (tx, _rx) = broadcast::channel(BROADCAST_CAPACITY);
        let html = render_tally_widget_html(&round.preview());
        Arc::new(OverlayState {
            round: Mutex::new(round),
            tx,
            last_html: Mutex::new(html),
            ingest_token: None,
            label: None,
        })
    }

    /// Set the operator ingest bearer token that authorizes `POST /overlay/ingest[/youtube]`.
    /// `Some(token)` gates the routes on `Authorization: Bearer <token>` (constant-time checked);
    /// `None` leaves them **fail-closed** (every POST refused). Only the token's `blake3` hash is
    /// retained. Consumes + rewraps the `Arc` so it composes with [`new`](Self::new).
    pub fn with_ingest_token(self: Arc<OverlayState>, token: Option<String>) -> Arc<OverlayState> {
        let hash = token
            .map(|t| Zeroizing::new(t))
            .filter(|t| !t.trim().is_empty())
            .map(|t| *blake3::hash(t.as_bytes()).as_bytes());
        // `new`/`demo_state` hand out a fresh, uniquely-owned Arc, so this unwrap holds at the
        // mount call-site (before the Arc is cloned into the router).
        let mut state = Arc::try_unwrap(self)
            .unwrap_or_else(|_| panic!("with_ingest_token must run before the state is shared"));
        state.ingest_token = hash;
        Arc::new(state)
    }

    /// Set the honesty label shown on the `GET /overlay` page chrome. Consumes + rewraps the `Arc`.
    pub fn with_label(self: Arc<OverlayState>, label: Option<String>) -> Arc<OverlayState> {
        let mut state = Arc::try_unwrap(self)
            .unwrap_or_else(|_| panic!("with_label must run before the state is shared"));
        state.label = label;
        Arc::new(state)
    }

    /// **Authorize an ingest POST.** Fail-closed: if no ingest token is configured the route is
    /// disabled (`403`); otherwise the request MUST carry `Authorization: Bearer <token>` matching
    /// the configured token (constant-time compared over the `blake3` hashes) — a missing or wrong
    /// bearer is `401`. `Ok(())` means the operator is authenticated and the ingest may proceed.
    fn authorize_ingest(&self, headers: &HeaderMap) -> Result<(), Response> {
        let Some(expected) = self.ingest_token.as_ref() else {
            return Err((
                StatusCode::FORBIDDEN,
                "overlay ingest is disabled — set OVERLAY_INGEST_TOKEN and send it as \
                 `Authorization: Bearer <token>` (the raw POST path is forgeable, so it is \
                 fail-closed without an operator token)",
            )
                .into_response());
        };
        let presented = headers
            .get(axum::http::header::AUTHORIZATION)
            .and_then(|v| v.to_str().ok())
            .and_then(|v| v.strip_prefix("Bearer "))
            .map(str::trim)
            .filter(|t| !t.is_empty());
        let Some(token) = presented else {
            return Err((
                StatusCode::UNAUTHORIZED,
                "overlay ingest requires `Authorization: Bearer <operator token>`",
            )
                .into_response());
        };
        let got = blake3::hash(token.as_bytes());
        if got.as_bytes().ct_eq(expected).into() {
            Ok(())
        } else {
            Err((StatusCode::UNAUTHORIZED, "overlay ingest token rejected").into_response())
        }
    }

    /// Ingest normalized stream events into the round and push the new tally. Returns the fresh
    /// preview (what the overlay now shows).
    pub fn ingest_events(&self, events: Vec<StreamEvent>) -> TallyPreview {
        let preview = {
            let mut round = self.round.lock().unwrap();
            round.ingest_batch(events);
            round.preview()
        };
        self.publish(&preview);
        preview
    }

    /// Ingest a raw YouTube `liveChatMessages` payload (parsed by the [`YouTubeAdapter`]) and push
    /// the new tally.
    pub fn ingest_youtube(&self, raw: &str) -> TallyPreview {
        self.ingest_events(YouTubeAdapter.parse(raw))
    }

    /// **Close the current window into the game world** → ONE certified turn, then push the (now
    /// reset, or unchanged-on-refusal) tally. This is the "on a timer close→resolve→advance" tick:
    /// a deployment calls it every round window with the live game `world`/`scene`. Returns the
    /// [`CertifiedTurn`] on success, or a [`CrowdCloseError`] (distinct-voter floor / below quorum /
    /// illegal command) — see [`CrowdRound::close_into_world`].
    ///
    /// The close runs the whole electorate's sign+verify synchronously under the round mutex; the
    /// per-voter weight cap + [`WeightShaping`](crate::crowd_round::WeightShaping) keep it bounded,
    /// but a deployment driving this from an async timer wraps the call in
    /// [`tokio::task::spawn_blocking`] (holding the `world`/`scene` in an `Arc`) so a large window
    /// never stalls the reactor — exactly what [`LiveCloseLoop::run`] does. Prefer
    /// [`drive_close`](Self::drive_close) as the deployment tick: it adds stuck-window recovery
    /// (a quorum-certified but illegal command is dropped, not left to brick the round).
    pub fn close_tick(
        &self,
        world: &WorldCell,
        scene: &Scene,
    ) -> Result<CertifiedTurn, CrowdCloseError> {
        let (result, preview) = {
            let mut round = self.round.lock().unwrap();
            let result = round.close_into_world(world, scene);
            (result, round.preview())
        };
        self.publish(&preview);
        result
    }

    /// **One deployment close-tick — the timer's per-window step, with stuck-window recovery.**
    /// Closes the window into `world`/`scene` under the round mutex ([`CrowdRound::close_into_world`])
    /// and classifies the outcome so the round can NEVER be bricked by a repeatedly-certified illegal
    /// command:
    ///
    /// * [`CloseTick::Landed`] — the quorum-certified winner resolved into the world as ONE real
    ///   [`CertifiedTurn`]; the window advanced (buffer reset). The world moved.
    /// * [`CloseTick::Retained`] — the window fell short of the distinct-voter floor or the weight
    ///   quorum. It is **left intact** so more votes next window can carry it (the retry case). The
    ///   world did not move.
    /// * [`CloseTick::Skipped`] — the crowd quorum-certified a command the GAME executor REFUSED
    ///   ([`CollectiveError::World`]) — or an unexpected engine/signature error. The window is
    ///   **dropped** (advanced) so the round is not stuck re-certifying the same losing command every
    ///   tick. Distinct from `Retained`: a `Retained` window keeps its ballots, a `Skipped` window is
    ///   thrown away. The world did not move.
    ///
    /// The whole close + recovery runs under ONE lock acquisition (so an ingest racing between the
    /// close and the drop cannot lose a next-window event), and the fresh tally is pushed over SSE
    /// exactly once. Directly callable with no timer, so the deploy close-path is unit-testable end
    /// to end.
    pub fn drive_close(&self, world: &WorldCell, scene: &Scene) -> CloseTick {
        let (tick, preview) = {
            let mut round = self.round.lock().unwrap();
            let tick = match round.close_into_world(world, scene) {
                Ok(cert) => CloseTick::Landed(cert),
                // Below the distinct-voter floor or the weight quorum — keep the window for retry.
                Err(CrowdCloseError::DistinctFloor { voters, required }) => {
                    CloseTick::Retained(CrowdCloseError::DistinctFloor { voters, required })
                }
                Err(CrowdCloseError::Collective(CollectiveError::BelowQuorum)) => {
                    CloseTick::Retained(CrowdCloseError::Collective(CollectiveError::BelowQuorum))
                }
                // A quorum-certified ILLEGAL command (the executor's teeth), or an unexpected
                // engine/signature error: DROP this window so the round is not bricked
                // re-certifying it forever. `close_into_world` did not advance on this error path,
                // so we advance here — under the SAME lock.
                Err(other) => {
                    round.advance();
                    CloseTick::Skipped(other)
                }
            };
            let preview = round.preview();
            (tick, preview)
        };
        self.publish(&preview);
        tick
    }

    /// Render + store + broadcast a tally snapshot. `send` returns `Err` only when no overlay is
    /// connected yet — harmless (the stored `last_html` still feeds the next subscriber's first
    /// paint).
    fn publish(&self, preview: &TallyPreview) -> usize {
        let html = render_tally_widget_html(preview);
        *self.last_html.lock().unwrap() = html.clone();
        self.tx.send(html).unwrap_or(0)
    }

    /// The current widget HTML (the first paint for a fresh page / SSE subscriber).
    fn current_html(&self) -> String {
        self.last_html.lock().unwrap().clone()
    }

    /// Subscribe to the tally-push stream.
    fn subscribe(&self) -> broadcast::Receiver<String> {
        self.tx.subscribe()
    }
}

/// **Assemble the overlay router.** Mounted into the merged app by `make_app`
/// (`docs/CROWD-STREAM-ENGINE-DESIGN.md`):
/// * `GET  /overlay`               — the transparent OBS page (add as a browser source);
/// * `GET  /overlay/sse`           — the server→browser tally push (an `EventSource` stream);
/// * `POST /overlay/ingest`        — feed normalized [`StreamEvent`]s (JSON array); pushes the tally;
/// * `POST /overlay/ingest/youtube`— feed a raw YouTube `liveChatMessages` JSON body; pushes the tally.
pub fn overlay_router(state: Arc<OverlayState>) -> Router {
    Router::new()
        .route("/overlay", get(get_overlay))
        .route("/overlay/sse", get(get_overlay_sse))
        .route("/overlay/ingest", post(post_overlay_ingest))
        .route("/overlay/ingest/youtube", post(post_overlay_ingest_youtube))
        .with_state(state)
}

/// The honesty label the DEMO overlay mount wears — it is a live TALLY BOARD, not a world driver.
/// No live `WorldCell` is mounted and nothing calls [`OverlayState::close_tick`], so votes tally
/// and push but NEVER land a certified world turn. A real deployment must build its own
/// [`OverlayState`] over the game's live `World::open` cell AND drive a close→resolve→advance timer
/// (see [`OverlayState::close_tick`]) to close the loop.
pub const DEMO_OVERLAY_LABEL: &str = "Tally board — no world resolve (demo). A live deployment mounts a World cell + a close-tick \
     timer to land certified turns.";

/// The demo round (keep: trade blows / press on) the demo overlay tallies over.
fn demo_round() -> CrowdRound {
    CrowdRound::open(
        "The gate-warden bars the way — what does the party do?",
        vec![
            Proposal::new("Trade blows with the gate-warden", Command::trade_blows()),
            Proposal::new("Press past into the plundered hall", Command::press_on()),
        ],
        vec!["trade blows".to_string(), "press on".to_string()],
        QUORUM,
    )
}

/// A demo overlay over the keep round — what tests mount. No ingest token (HTTP ingest fail-closed)
/// and the honesty [`DEMO_OVERLAY_LABEL`] on the page. A real deployment builds its own
/// [`OverlayState::new`] over the round for the game being streamed. See [`demo_state_from_env`]
/// for the `make_app` mount (which also picks up the operator ingest token).
pub fn demo_state() -> Arc<OverlayState> {
    OverlayState::new(demo_round()).with_label(Some(DEMO_OVERLAY_LABEL.to_string()))
}

/// The demo overlay `make_app` mounts — the demo state, plus the operator ingest bearer from
/// [`OVERLAY_INGEST_TOKEN_ENV`] (unset ⇒ the ingest routes stay fail-closed). Honestly labeled a
/// tally board with no world resolve until a live-world close-loop is wired.
pub fn demo_state_from_env() -> Arc<OverlayState> {
    let token = std::env::var(OVERLAY_INGEST_TOKEN_ENV)
        .ok()
        .filter(|v| !v.trim().is_empty());
    if token.is_some() {
        tracing::info!(
            "overlay ingest gated behind {OVERLAY_INGEST_TOKEN_ENV} (operator bearer required)"
        );
    } else {
        tracing::info!(
            "overlay ingest fail-closed — {OVERLAY_INGEST_TOKEN_ENV} unset (POST /overlay/ingest \
             refused; the overlay is a read-only tally board)"
        );
    }
    demo_state().with_ingest_token(token)
}

// ─────────────────────────────────────────────────────────────────────────────
// The DEPLOYMENT close-loop — a live game World cell the crowd STEERS, closed on a timer.
//
// The default mount ([`demo_state_from_env`]) is a tally board with NO world resolve. Setting
// `OVERLAY_LIVE_WORLD` swaps in a [`LiveCloseLoop`] over a live demo Warden's Keep world/scene:
// `close_tick`/`drive_close` — which fold a crowd tally into ONE certified `TurnReceipt` — are now
// DRIVEN on a `tokio::time::interval`, so on a running server a crowd round actually
// ingests → tallies → at window close resolves the quorum-certified winner into the world → pushes
// the reset tally over SSE. This is the missing close-loop: the thing that was only demonstrated in
// `#[cfg(test)]` is now the deploy path.
// ─────────────────────────────────────────────────────────────────────────────

/// The env var that OPTS IN to the live-world close-loop mount (any non-empty, non-`0`/`false`/`off`
/// value). UNSET (the default) ⇒ the [`demo_state_from_env`] tally board mounts, byte-identical to
/// before. See [`overlay_mount_from_env`].
pub const OVERLAY_LIVE_WORLD_ENV: &str = "OVERLAY_LIVE_WORLD";

/// The env var setting the live-world round window in SECONDS (the interval on which the close-loop
/// resolves a window into ONE certified world turn). Unset/invalid ⇒ [`DEFAULT_ROUND_SECONDS`];
/// floored at [`MIN_ROUND_SECONDS`] so a typo can never spin a tight close loop.
pub const OVERLAY_ROUND_SECONDS_ENV: &str = "OVERLAY_ROUND_SECONDS";

/// The default live-world round window (seconds) when [`OVERLAY_ROUND_SECONDS_ENV`] is unset.
const DEFAULT_ROUND_SECONDS: u64 = 30;
/// The floor the configured round window is clamped up to — a guard against a `0`/tiny value
/// spinning a tight close loop under the round mutex.
const MIN_ROUND_SECONDS: u64 = 1;
/// The deterministic deploy seed for the demo Keep world the live overlay steers (the same seed the
/// crowd-round tests deploy, so the demo world's identity/state hashes are reproducible).
const KEEP_LIVE_SEED: u8 = 30;

/// The honesty label the LIVE-WORLD overlay wears on the `GET /overlay` page — it says plainly that
/// (a) the mounted world is a **demo**, and (b) "certified" means quorum-certified + executor-admitted,
/// NOT FRI-sound-on-chain (the deployed ledger's undischarged FRI/STARK floor is inherited).
pub const LIVE_OVERLAY_LABEL: &str = "Live demo world — the crowd steers a demo Warden's Keep: each round window the quorum-certified \
     winner lands ONE real world turn. \"Certified\" = quorum-certified + executor-admitted, NOT \
     FRI-sound-on-chain; the world is a demo.";

/// **The outcome of one deployment close-tick** ([`OverlayState::drive_close`]) — the classification
/// that lets the timer never brick the round.
#[derive(Debug)]
pub enum CloseTick {
    /// The quorum-certified winner resolved into the world as ONE real [`CertifiedTurn`]; the window
    /// advanced (buffer reset). The world moved.
    Landed(CertifiedTurn),
    /// The window fell short (distinct-voter floor / weight quorum). It is left intact for retry next
    /// window. The world did not move.
    Retained(CrowdCloseError),
    /// The crowd quorum-certified a command the executor REFUSED (or an unexpected engine error) —
    /// the window is DROPPED so the round is not stuck re-certifying it. The world did not move.
    Skipped(CrowdCloseError),
}

impl CloseTick {
    /// Whether this tick landed a real certified world turn.
    pub fn landed(&self) -> bool {
        matches!(self, CloseTick::Landed(_))
    }
}

/// **The live-world close-loop** — the deploy-path binding of a [`CrowdRound`] overlay to a live
/// game `WorldCell` + `Scene` and a round-window timer. [`run`](Self::run) drives
/// [`OverlayState::drive_close`] on a [`tokio::time::interval`]; each window resolves the
/// quorum-certified winner into the world as ONE real [`CertifiedTurn`] and pushes the fresh tally
/// over SSE. Build one with [`keep_live_overlay`] (the demo Keep world), mount its router with
/// [`router`](Self::router), and start the timer with [`spawn`](Self::spawn).
pub struct LiveCloseLoop {
    overlay: Arc<OverlayState>,
    world: Arc<WorldCell>,
    scene: Arc<Scene>,
    window: Duration,
}

impl LiveCloseLoop {
    /// The shared overlay state (the SSE + ingest surface). Clone-cheap (`Arc`).
    pub fn overlay(&self) -> Arc<OverlayState> {
        Arc::clone(&self.overlay)
    }

    /// The live game world cell the close-loop resolves certified turns into. Clone-cheap (`Arc`);
    /// a deployment can read/verify its committed chain (`read_var` / `verify`) alongside the loop.
    pub fn world(&self) -> Arc<WorldCell> {
        Arc::clone(&self.world)
    }

    /// The round window the timer closes on.
    pub fn window(&self) -> Duration {
        self.window
    }

    /// The overlay router (`GET /overlay`, `/overlay/sse`, `POST /overlay/ingest[/youtube]`) over
    /// this live state — what `make_app` merges.
    pub fn router(&self) -> Router {
        overlay_router(self.overlay())
    }

    /// **One deployment close-tick over the live world** — what the timer runs each window. Directly
    /// callable with NO timer, so the deploy close-path is unit-testable end to end. See
    /// [`OverlayState::drive_close`] for the outcome classification (Landed / Retained / Skipped).
    pub fn drive_once(&self) -> CloseTick {
        self.overlay.drive_close(&self.world, &self.scene)
    }

    /// **Spawn the close-loop timer** on the current tokio runtime (fire-and-forget). The loop lives
    /// for the process; the server holds no handle (the overlay state is already shared via its
    /// router). If no runtime is in scope (only possible when the env gate is set outside an async
    /// context) the loop is not started and a warning is logged — the router still serves as a tally
    /// board.
    pub fn spawn(self) {
        if tokio::runtime::Handle::try_current().is_err() {
            tracing::warn!(
                "{OVERLAY_LIVE_WORLD_ENV} set but no tokio runtime in scope — the overlay \
                 close-loop timer was not started (the overlay still serves as a tally board)"
            );
            return;
        }
        tokio::spawn(self.run());
    }

    /// **The close-loop — drive [`OverlayState::drive_close`] on a round-window
    /// [`tokio::time::interval`].** The first interval tick fires immediately and is consumed so
    /// voters get a full window before the first resolve. Each subsequent tick runs the close (which
    /// signs+verifies the whole electorate synchronously) OFF the async reactor via
    /// [`tokio::task::spawn_blocking`], so a large window never stalls request handling.
    pub async fn run(self) {
        let mut ticker = tokio::time::interval(self.window);
        ticker.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Delay);
        // The first tick is immediate — consume it so the first REAL close is one window in.
        ticker.tick().await;
        loop {
            ticker.tick().await;
            // Run the close INLINE on this runtime-worker thread, NOT tokio::task::spawn_blocking.
            // The close resolves a quorum-certified turn through the executor, whose admission (under
            // full-Lean, `dregg_constraint_admits_present`) routes through the reality-gate's Lean
            // constraint eval. Lean's runtime only serves threads it has registered; a spawn_blocking
            // BLOCKING-pool thread is not one, so the eval fails there and the turn is SILENTLY REFUSED
            // (the world never moves). Full-Lean verification caught exactly this — the timer-driven
            // close landed nothing while the on-reactor `drive_once` (a registered worker) did. The
            // close is a short CPU-bound fold on a dedicated close-loop task, so holding this worker
            // for it is fine. PRODUCTION FOLLOW-UP: a dedicated Lean-registered close thread if a very
            // large window's sign+verify would ever stall request handling.
            match self.overlay.drive_close(&self.world, &self.scene) {
                CloseTick::Landed(cert) => tracing::info!(
                    winner = cert.decision.winner,
                    winner_tally = cert.decision.winner_tally,
                    total = cert.decision.total,
                    "overlay close-loop: quorum-certified winner landed ONE real world turn \
                     (certified = quorum-certified + executor-admitted, NOT FRI-sound-on-chain)"
                ),
                CloseTick::Retained(why) => tracing::debug!(
                    reason = %why,
                    "overlay close-loop: window below quorum/floor — retained for retry"
                ),
                CloseTick::Skipped(why) => tracing::warn!(
                    reason = %why,
                    "overlay close-loop: quorum-certified command refused by the executor — \
                     window dropped to unstick the round"
                ),
            }
        }
    }
}

/// **Build a LIVE demo-world overlay** — the keep round tally over a freshly deployed demo Warden's
/// Keep `WorldCell` + `Scene` the crowd steers. The overlay is honestly labeled a live *demo* world
/// ([`LIVE_OVERLAY_LABEL`]) and gated with the operator `ingest_token` (unset ⇒ POST ingest
/// fail-closed; the server-side authenticated feed is still the [`YouTubePoller`]). Drive the
/// returned [`LiveCloseLoop`] on a `window` interval to land certified turns.
///
/// The demo world is a demo: it seeds the gate-warden fight at 50 HP, and the crowd's certified
/// trade-blows / press-on turns move THAT real world state. A real deployment builds its own
/// [`LiveCloseLoop`] over the game it streams (its own `WorldCell`/`Scene`/proposals).
pub fn keep_live_overlay(window: Duration, ingest_token: Option<String>) -> LiveCloseLoop {
    let mut world = deploy_keep(KEEP_LIVE_SEED);
    // The gate-warden fight begins at 50 HP — the certified crowd turns move this real state.
    world.seed_var("hp", Value::Int(50));
    let scene = keep_scene();
    let overlay = OverlayState::new(demo_round())
        .with_label(Some(LIVE_OVERLAY_LABEL.to_string()))
        .with_ingest_token(ingest_token);
    LiveCloseLoop {
        overlay,
        world: Arc::new(world),
        scene: Arc::new(scene),
        window,
    }
}

/// **Resolve the overlay mount from the environment** — the env-gated choice `make_app` makes:
///
/// * `OVERLAY_LIVE_WORLD` unset (the default) ⇒ `(`[`demo_state_from_env`]` tally-board router,
///   None)` — no world, no timer, byte-identical to before.
/// * `OVERLAY_LIVE_WORLD` set ⇒ `(the live-world router, Some(`[`LiveCloseLoop`]`))` — a live demo
///   Keep world the crowd steers, on an `OVERLAY_ROUND_SECONDS`-second window. The caller merges the
///   router and calls [`LiveCloseLoop::spawn`] to start the timer.
///
/// The operator ingest bearer [`OVERLAY_INGEST_TOKEN_ENV`] is honored in both modes (unset ⇒ POST
/// ingest fail-closed).
pub fn overlay_mount_from_env() -> (Router, Option<LiveCloseLoop>) {
    if !env_live_world_enabled() {
        return (overlay_router(demo_state_from_env()), None);
    }
    let token = std::env::var(OVERLAY_INGEST_TOKEN_ENV)
        .ok()
        .filter(|v| !v.trim().is_empty());
    if token.is_some() {
        tracing::info!(
            "overlay ingest gated behind {OVERLAY_INGEST_TOKEN_ENV} (operator bearer required)"
        );
    } else {
        tracing::info!(
            "overlay ingest fail-closed — {OVERLAY_INGEST_TOKEN_ENV} unset (POST /overlay/ingest \
             refused; votes still feed via the server-side YouTubePoller)"
        );
    }
    let window = round_window_from_env();
    let live = keep_live_overlay(window, token);
    tracing::info!(
        round_secs = window.as_secs(),
        "overlay LIVE demo world mounted ({OVERLAY_LIVE_WORLD_ENV}) — the crowd steers a demo \
         Warden's Keep; the close-loop lands ONE quorum-certified world turn per window \
         (certified = quorum-certified + executor-admitted, NOT FRI-sound-on-chain; the world is a \
         demo)"
    );
    let router = live.router();
    (router, Some(live))
}

/// Whether [`OVERLAY_LIVE_WORLD_ENV`] opts in to the live-world mount — set to any value other than
/// empty / `0` / `false` / `off` (case-insensitive).
fn env_live_world_enabled() -> bool {
    std::env::var(OVERLAY_LIVE_WORLD_ENV)
        .map(|v| {
            let v = v.trim().to_ascii_lowercase();
            !(v.is_empty() || v == "0" || v == "false" || v == "off")
        })
        .unwrap_or(false)
}

/// The live-world round window from [`OVERLAY_ROUND_SECONDS_ENV`] (default [`DEFAULT_ROUND_SECONDS`],
/// floored at [`MIN_ROUND_SECONDS`]).
fn round_window_from_env() -> Duration {
    let secs = std::env::var(OVERLAY_ROUND_SECONDS_ENV)
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
        .unwrap_or(DEFAULT_ROUND_SECONDS)
        .max(MIN_ROUND_SECONDS);
    Duration::from_secs(secs)
}

/// `GET /overlay` — the transparent OBS page, first-painted at the current tally, carrying the
/// state's honesty label (if any) as page chrome.
async fn get_overlay(State(state): State<Arc<OverlayState>>) -> Html<String> {
    Html(overlay_document(
        &state.current_html(),
        state.label.as_deref(),
    ))
}

/// `GET /overlay/sse` — the tally push. Emits the current tally immediately, then every broadcast
/// frame as a `tally` SSE event. A lagged subscriber's dropped frames are skipped (the next frame
/// is a full snapshot). 15s keep-alive comments hold the connection open through idle stretches.
async fn get_overlay_sse(
    State(state): State<Arc<OverlayState>>,
) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    let initial = state.current_html();
    let live = BroadcastStream::new(state.subscribe()).filter_map(|msg| match msg {
        Ok(html) => Some(Ok::<Event, Infallible>(tally_event(html))),
        // A `Lagged` (the subscriber fell behind the channel depth) — skip; the next frame is a
        // complete snapshot, so no state is lost.
        Err(_lagged) => None,
    });
    let stream = tokio_stream::once(Ok::<Event, Infallible>(tally_event(initial))).chain(live);
    Sse::new(stream).keep_alive(
        KeepAlive::new()
            .interval(Duration::from_secs(15))
            .text("keep-alive"),
    )
}

/// `POST /overlay/ingest` — feed a JSON array of normalized [`StreamEvent`]s; returns the new
/// tally. **Operator-gated**: this path trusts the caller's `amount_micros`, so it is forgeable on
/// a public port and is refused unless the request carries the operator bearer (see
/// [`OverlayState::authorize_ingest`]). The unforgeable path is the server-side [`YouTubePoller`],
/// which sources `amount_micros` from YouTube itself.
async fn post_overlay_ingest(
    State(state): State<Arc<OverlayState>>,
    headers: HeaderMap,
    body: axum::body::Bytes,
) -> Response {
    if let Err(resp) = state.authorize_ingest(&headers) {
        return resp;
    }
    let events: Vec<StreamEvent> = match serde_json::from_slice(&body) {
        Ok(e) => e,
        Err(e) => {
            return (
                StatusCode::BAD_REQUEST,
                format!("invalid StreamEvent array: {e}"),
            )
                .into_response();
        }
    };
    Json(state.ingest_events(events)).into_response()
}

/// `POST /overlay/ingest/youtube` — feed a raw YouTube `liveChatMessages` JSON body; returns the
/// new tally. **Operator-gated** (same as [`post_overlay_ingest`]): even though the body is the
/// platform shape, a POST body is attacker-supplied, so it requires the operator bearer. The
/// authenticated fetch that the SERVER (not a caller) performs is [`YouTubePoller`].
async fn post_overlay_ingest_youtube(
    State(state): State<Arc<OverlayState>>,
    headers: HeaderMap,
    body: String,
) -> Response {
    if let Err(resp) = state.authorize_ingest(&headers) {
        return resp;
    }
    Json(state.ingest_youtube(&body)).into_response()
}

/// One SSE `tally` frame carrying a widget-HTML fragment. The HTML is **base64-wrapped** so the
/// payload is a single, control-character-free `data:` line: an operator-authored label containing
/// a newline (which would split the SSE framing) or `<`/quotes cannot break the frame or smuggle
/// markup through the transport. The client base64-decodes (UTF-8 aware) before swapping
/// `innerHTML` (see [`OVERLAY_JS`]). Widget text is ALSO HTML-escaped by `render_html`, so this is
/// belt-and-suspenders on the transport layer.
fn tally_event(html: String) -> Event {
    Event::default()
        .event("tally")
        .data(BASE64.encode(html.as_bytes()))
}

/// Render the tally widget to an HTML fragment via the deos [`render_html`] renderer — the SAME
/// `ViewNode` IR the native/web cockpit paints. Static nodes ([`ViewNode::Progress`]/`Pill`/`Text`)
/// so each pushed snapshot is complete (no in-tab executor).
pub fn render_tally_widget_html(preview: &TallyPreview) -> String {
    render_html(&tally_widget_tree(preview), &[])
}

/// Build the tally widget's [`ViewNode`] tree: a titled section of one row per option (label +
/// a static vote bar), a divider, and a quorum pill + voter count.
fn tally_widget_tree(preview: &TallyPreview) -> ViewNode {
    // The bar scale is the current leader's votes (min 1), so the leading bar is full and the
    // others read as a fraction of it.
    let max = preview
        .options
        .iter()
        .map(|o| o.votes)
        .max()
        .unwrap_or(0)
        .max(1);

    let rows: Vec<ViewNode> = preview
        .options
        .iter()
        .enumerate()
        .map(|(i, o)| {
            let marker = if preview.leader
                == Some(u64::try_from(i).expect("the bounded overlay option list fits u64"))
            {
                "\u{25B6} "
            } else {
                "\u{2003} "
            };
            ViewNode::Row(vec![
                ViewNode::Text(format!("{marker}{}", o.label)),
                ViewNode::Progress {
                    value: o.votes,
                    max,
                    label: format!("{} votes", o.votes),
                },
            ])
        })
        .collect();

    let (pill_text, pill_tag) = if preview.quorum_met() {
        (
            format!("QUORUM MET {}/{}", preview.total, preview.quorum),
            "good",
        )
    } else {
        (
            format!("{}/{} to quorum", preview.total, preview.quorum),
            "warn",
        )
    };

    ViewNode::Section {
        title: preview.question.clone(),
        tag: "crowd".to_string(),
        children: vec![
            ViewNode::VStack(rows),
            ViewNode::Divider,
            ViewNode::Row(vec![
                ViewNode::Pill {
                    text: pill_text,
                    tag: pill_tag.to_string(),
                    slot: None,
                    cases: vec![],
                },
                ViewNode::Text(format!("{} voters", preview.voters)),
            ]),
        ],
    }
}

/// **The transparent OBS overlay document.** A full standalone page with `background: transparent`
/// and all cockpit chrome stripped (no card frame, no nav), sized as an overlay browser-source. The
/// `#tally` container holds the first-paint widget; the [`OVERLAY_JS`] client subscribes to
/// `/overlay/sse` and swaps its `innerHTML` on each pushed frame. An optional `label` (e.g. the
/// demo mount's honesty note) is rendered as a small badge above the widget — HTML-escaped, so an
/// operator label with markup cannot break the page.
pub fn overlay_document(widget_html: &str, label: Option<&str>) -> String {
    let badge = match label {
        Some(l) => format!(
            "<div class=\"overlay-label\" role=\"note\">{}</div>",
            crate::esc(l)
        ),
        None => String::new(),
    };
    format!(
        "<!doctype html>\n\
<html lang=\"en\">\n\
<head>\n\
<meta charset=\"utf-8\">\n\
<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
<title>Crowd Vote Overlay</title>\n\
<style>{OVERLAY_CSS}</style>\n\
</head>\n\
<body>\n\
<main class=\"overlay-root\">{badge}<div id=\"tally\">{widget}</div></main>\n\
<script>{OVERLAY_JS}</script>\n\
</body>\n\
</html>\n",
        OVERLAY_CSS = OVERLAY_CSS,
        badge = badge,
        widget = widget_html,
        OVERLAY_JS = OVERLAY_JS,
    )
}

/// The overlay stylesheet — transparent page, a translucent panel behind the widget for legibility
/// over arbitrary video, and styling for the deos widget classes `render_html` emits. Self-contained
/// (it does NOT pull the opaque cockpit CSS): an OBS browser source composites this straight onto the
/// stream.
const OVERLAY_CSS: &str = "\
:root { color-scheme: dark; }\
html, body { margin: 0; padding: 0; background: transparent; }\
body { font-family: ui-sans-serif, system-ui, -apple-system, 'Segoe UI', Roboto, sans-serif; }\
.overlay-root { padding: 16px; max-width: 520px; }\
.deos-section { background: rgba(12,14,22,0.72); border: 1px solid rgba(255,255,255,0.14); border-radius: 14px; padding: 14px 16px; box-shadow: 0 6px 24px rgba(0,0,0,0.45); backdrop-filter: blur(4px); }\
.deos-section-title { font-size: 18px; font-weight: 700; color: #f4f6ff; margin-bottom: 12px; text-shadow: 0 1px 3px rgba(0,0,0,0.8); }\
.deos-vstack { display: flex; flex-direction: column; gap: 10px; }\
.deos-row { display: flex; align-items: center; gap: 12px; }\
.deos-text { color: #e7ebff; font-size: 15px; text-shadow: 0 1px 3px rgba(0,0,0,0.8); min-width: 160px; }\
.deos-divider { border: 0; border-top: 1px solid rgba(255,255,255,0.14); margin: 12px 0; }\
.deos-progress { flex: 1; }\
.deos-progress-label { display: block; font-size: 12px; color: #aeb6d8; margin-bottom: 3px; text-shadow: 0 1px 2px rgba(0,0,0,0.8); }\
.deos-progress-track { height: 12px; border-radius: 7px; background: rgba(255,255,255,0.10); overflow: hidden; }\
.deos-progress-fill { height: 100%; border-radius: 7px; background: linear-gradient(90deg, #5b8bff, #8b5bff); transition: width 320ms ease; }\
.deos-pill { display: inline-block; padding: 3px 12px; border-radius: 999px; font-size: 13px; font-weight: 700; }\
.deos-pill[data-tag='good'] { background: rgba(60,200,120,0.22); color: #7bf0ad; border: 1px solid rgba(60,200,120,0.5); }\
.deos-pill[data-tag='warn'] { background: rgba(240,190,60,0.18); color: #f5d27a; border: 1px solid rgba(240,190,60,0.45); }\
.overlay-label { margin: 0 0 10px; padding: 6px 12px; border-radius: 10px; background: rgba(240,190,60,0.16); border: 1px solid rgba(240,190,60,0.4); color: #f5d27a; font-size: 12px; font-weight: 600; text-shadow: 0 1px 2px rgba(0,0,0,0.8); }\
";

/// The overlay client — subscribe to the tally push and swap `#tally`. Each frame is base64 (see
/// [`tally_event`]); decode it UTF-8-aware before swapping `innerHTML`, so the tally's non-ASCII
/// markers (▶ / em-space) survive and a control character in the payload never touched the SSE
/// framing. `EventSource` auto-reconnects on a dropped connection, so a restarted server / a
/// network blip self-heals with no client code.
const OVERLAY_JS: &str = "\
(function () {\
  var box = document.getElementById('tally');\
  if (!box || typeof EventSource === 'undefined') return;\
  function decode(b64) {\
    var bin = atob(b64);\
    var bytes = new Uint8Array(bin.length);\
    for (var i = 0; i < bin.length; i++) { bytes[i] = bin.charCodeAt(i); }\
    return new TextDecoder('utf-8').decode(bytes);\
  }\
  var es = new EventSource('/overlay/sse');\
  es.addEventListener('tally', function (e) {\
    try { box.innerHTML = decode(e.data); } catch (err) { /* skip a malformed frame */ }\
  });\
  es.onerror = function () { /* EventSource retries automatically */ };\
})();\
";

// ─────────────────────────────────────────────────────────────────────────────
// The server-side YouTube poller — the AUTHENTICATED ingest path (design §ingest).
// ─────────────────────────────────────────────────────────────────────────────

/// A failure fetching one YouTube liveChat page — a transport/HTTP error. It aborts THIS poll (the
/// loop retries after the interval); it never feeds partial or forged data.
#[derive(Debug, Clone)]
pub struct LiveChatFetchError(pub String);

impl std::fmt::Display for LiveChatFetchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "youtube liveChat fetch failed: {}", self.0)
    }
}

impl std::error::Error for LiveChatFetchError {}

/// **The fetch seam of the [`YouTubePoller`]** — fetch ONE `liveChatMessages.list` page. Factored
/// into a trait so the poller's parse/advance/ingest wiring is testable with a mock (a canned page)
/// and no live API key or network. The real implementation is [`ReqwestLiveChatFetcher`].
pub trait LiveChatFetcher: Send + Sync {
    /// Fetch one `liveChatMessages.list` page for `live_chat_id`, resuming from `page_token`
    /// (`None` ⇒ from the live tail), authenticated with `api_key`. Returns the raw JSON body.
    fn fetch_page(
        &self,
        live_chat_id: &str,
        api_key: &str,
        page_token: Option<&str>,
    ) -> Result<String, LiveChatFetchError>;
}

/// The real [`LiveChatFetcher`] — a blocking `reqwest` GET against the YouTube Data API
/// `liveChat/messages` endpoint. Blocking (the crate's `reqwest` is `blocking`), so a poll loop
/// drives it off the async reactor via [`tokio::task::spawn_blocking`]. The query params are passed
/// through `reqwest`'s encoder (no manual URL building), so `api_key` / `page_token` are escaped.
pub struct ReqwestLiveChatFetcher {
    client: reqwest::blocking::Client,
}

impl ReqwestLiveChatFetcher {
    /// A fetcher with a fresh blocking client.
    pub fn new() -> Self {
        ReqwestLiveChatFetcher {
            client: reqwest::blocking::Client::new(),
        }
    }
}

impl Default for ReqwestLiveChatFetcher {
    fn default() -> Self {
        Self::new()
    }
}

impl LiveChatFetcher for ReqwestLiveChatFetcher {
    fn fetch_page(
        &self,
        live_chat_id: &str,
        api_key: &str,
        page_token: Option<&str>,
    ) -> Result<String, LiveChatFetchError> {
        let mut params: Vec<(&str, &str)> = vec![
            ("part", "snippet,authorDetails"),
            ("liveChatId", live_chat_id),
            ("key", api_key),
        ];
        if let Some(t) = page_token {
            params.push(("pageToken", t));
        }
        let resp = self
            .client
            .get("https://www.googleapis.com/youtube/v3/liveChat/messages")
            .query(&params)
            .send()
            .map_err(|e| LiveChatFetchError(e.to_string()))?;
        let status = resp.status();
        let body = resp.text().map_err(|e| LiveChatFetchError(e.to_string()))?;
        if !status.is_success() {
            return Err(LiveChatFetchError(format!("HTTP {status}: {body}")));
        }
        Ok(body)
    }
}

/// **The server-side YouTube Live Chat poller — the authenticated ingest that replaces the
/// forgeable POST.** The SERVER holds the operator's API key + the `liveChatId` and pulls chat
/// pages itself, so `amount_micros` comes from YouTube's own response, not from an attacker-supplied
/// body. It carries the cursor (`nextPageToken`) and YouTube's requested `pollingIntervalMillis`,
/// advancing both on each [`poll_once`](Self::poll_once).
///
/// [`poll_once`](Self::poll_once) is the testable unit (fetch → parse → ingest → advance). The live
/// fetch LOOP — spawn a task that calls `poll_once` against a [`ReqwestLiveChatFetcher`] every
/// [`polling_interval`](Self::polling_interval), off the reactor via
/// [`tokio::task::spawn_blocking`] — is the **named residual**: it needs a running deployment with a
/// LIVE-enabled channel, an API key, and the active broadcast's `liveChatId`; that is deployment
/// wiring, not this structure.
pub struct YouTubePoller {
    api_key: Zeroizing<String>,
    live_chat_id: String,
    next_page_token: Option<String>,
    polling_interval_millis: u64,
}

/// The floor YouTube's `pollingIntervalMillis` is clamped up to when the API reports a smaller (or
/// zero) interval — a guard so a misbehaving/absent interval can't spin a tight fetch loop.
const MIN_POLL_INTERVAL_MILLIS: u64 = 2_000;

impl YouTubePoller {
    /// A poller for `live_chat_id`, authenticated with `api_key`. Starts at the live tail (no
    /// cursor) with the [`MIN_POLL_INTERVAL_MILLIS`] default interval until the first page reports
    /// YouTube's own.
    pub fn new(api_key: impl Into<String>, live_chat_id: impl Into<String>) -> YouTubePoller {
        YouTubePoller {
            api_key: Zeroizing::new(api_key.into()),
            live_chat_id: live_chat_id.into(),
            next_page_token: None,
            polling_interval_millis: MIN_POLL_INTERVAL_MILLIS,
        }
    }

    /// The current page cursor (`None` before the first page / when YouTube omitted one).
    pub fn next_page_token(&self) -> Option<&str> {
        self.next_page_token.as_deref()
    }

    /// How long to wait before the next poll — YouTube's `pollingIntervalMillis` from the last
    /// page, floored at [`MIN_POLL_INTERVAL_MILLIS`].
    pub fn polling_interval(&self) -> Duration {
        Duration::from_millis(self.polling_interval_millis.max(MIN_POLL_INTERVAL_MILLIS))
    }

    /// **Poll one page and feed the overlay.** Fetches the next `liveChatMessages` page (through
    /// `fetcher`), parses it with [`parse_youtube_live_page`] (so `amount_micros` is YouTube's, not
    /// a caller's), ingests the events into `overlay`, and advances the cursor + polling interval
    /// from the page. Returns the fresh [`TallyPreview`]. A parse of an empty/malformed body ingests
    /// nothing and simply re-polls from the tail next time.
    pub fn poll_once(
        &mut self,
        fetcher: &dyn LiveChatFetcher,
        overlay: &OverlayState,
    ) -> Result<TallyPreview, LiveChatFetchError> {
        let body = fetcher.fetch_page(
            &self.live_chat_id,
            &self.api_key,
            self.next_page_token.as_deref(),
        )?;
        let YouTubeLivePage {
            events,
            next_page_token,
            polling_interval_millis,
        } = parse_youtube_live_page(&body);
        // Advance the cursor + interval regardless of whether this page had vote-bearing events.
        self.next_page_token = next_page_token;
        if polling_interval_millis > 0 {
            self.polling_interval_millis = polling_interval_millis;
        }
        Ok(overlay.ingest_events(events))
    }
}

/// Resolve a [`YouTubePoller`] from the environment — `Some` iff BOTH [`YOUTUBE_API_KEY_ENV`] and
/// [`YOUTUBE_LIVE_CHAT_ID_ENV`] are set. `None` (the default) leaves the overlay fed only by the
/// operator-gated POST. This constructs the poller; a deployment still owns the fetch LOOP (the
/// named residual) that drives [`YouTubePoller::poll_once`] on a timer.
pub fn youtube_poller_from_env() -> Option<YouTubePoller> {
    let api_key = std::env::var(YOUTUBE_API_KEY_ENV)
        .ok()
        .filter(|v| !v.trim().is_empty())?;
    let live_chat_id = std::env::var(YOUTUBE_LIVE_CHAT_ID_ENV)
        .ok()
        .filter(|v| !v.trim().is_empty())?;
    Some(YouTubePoller::new(api_key, live_chat_id))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn widget_renders_the_tally_snapshot() {
        let state = demo_state();
        let events = YouTubeAdapter.parse(
            r#"{"items":[
                {"snippet":{"type":"superChatEvent","displayMessage":"$5","superChatDetails":{"amountMicros":"5000000","userComment":"trade blows"}},"authorDetails":{"channelId":"UC_a"}},
                {"snippet":{"type":"textMessageEvent","textMessageDetails":{"messageText":"press on"}},"authorDetails":{"channelId":"UC_b"}}
            ]}"#,
        );
        let preview = state.ingest_events(events);
        assert_eq!(preview.total, 6, "$5 trade-blows (5) + a press-on chat (1)");
        assert_eq!(preview.voters, 2);

        let html = render_tally_widget_html(&preview);
        assert!(
            html.contains("deos-section"),
            "the widget is a deos section"
        );
        assert!(html.contains("gate-warden"), "carries the question");
        assert!(html.contains("deos-progress-fill"), "renders vote bars");
        // No newlines in the fragment ⇒ it rides one SSE data: line.
        assert!(
            !html.contains('\n'),
            "render_html output is single-line (SSE-safe)"
        );
    }

    #[test]
    fn overlay_document_is_transparent_and_chrome_free() {
        let doc = overlay_document(&demo_state().current_html(), None);
        assert!(
            doc.contains("background: transparent"),
            "the page background is transparent"
        );
        assert!(
            doc.contains("/overlay/sse"),
            "the client subscribes to the push"
        );
        assert!(
            doc.contains("id=\"tally\""),
            "the swappable container is present"
        );
        // No cockpit back-nav chrome.
        assert!(!doc.contains("all cards"), "no cockpit chrome");
    }

    #[test]
    fn demo_mount_is_honestly_labeled_a_tally_board() {
        // The demo mount wears the honesty label — a tally board, NOT a world driver.
        let doc = overlay_document(&demo_state().current_html(), Some(DEMO_OVERLAY_LABEL));
        assert!(
            doc.contains("no world resolve"),
            "the demo page states it does not resolve a world turn"
        );
        assert!(
            doc.contains("overlay-label"),
            "the honesty badge is rendered"
        );
    }

    #[test]
    fn ingest_publishes_to_subscribers() {
        let state = demo_state();
        let mut rx = state.subscribe();
        let _ = state.ingest_events(vec![StreamEvent {
            platform: "youtube".into(),
            author_id: "UC_x".into(),
            kind: dregg_stream_ingest::EventKind::Chat,
            amount_micros: 0,
            text: "press on".into(),
            ts: 0,
        }]);
        let pushed = rx
            .try_recv()
            .expect("a frame was broadcast to the subscriber");
        assert!(
            pushed.contains("deos-section"),
            "the pushed frame is the rendered widget"
        );
    }

    /// The SSE frame is base64 — a single line, no `<`/newline reaching the transport, so an
    /// operator label cannot break the framing or inject markup through the SSE channel.
    #[test]
    fn sse_frame_is_base64_wrapped() {
        let preview = demo_round().preview();
        let event_data = BASE64.encode(render_tally_widget_html(&preview).as_bytes());
        // Base64 alphabet only — no `<`, no newline (the two things that break SSE / inject markup).
        assert!(!event_data.contains('<'), "no markup in the wire payload");
        assert!(!event_data.contains('\n'), "single SSE data line");
        // And it round-trips back to the widget HTML.
        let decoded = String::from_utf8(BASE64.decode(&event_data).unwrap()).unwrap();
        assert!(decoded.contains("deos-section"), "decodes to the widget");
    }

    fn bearer(token: &str) -> HeaderMap {
        let mut h = HeaderMap::new();
        h.insert(
            axum::http::header::AUTHORIZATION,
            format!("Bearer {token}").parse().unwrap(),
        );
        h
    }

    #[test]
    fn ingest_is_fail_closed_without_a_token() {
        // No token configured ⇒ every ingest POST refused (403), even with a bearer present.
        let state = demo_state(); // token None
        assert!(
            state.authorize_ingest(&HeaderMap::new()).is_err(),
            "no token + no header ⇒ refused"
        );
        let err = state.authorize_ingest(&bearer("anything")).unwrap_err();
        assert_eq!(err.status(), StatusCode::FORBIDDEN, "fail-closed is 403");
    }

    #[test]
    fn ingest_requires_the_matching_operator_bearer() {
        let state = OverlayState::new(demo_round()).with_ingest_token(Some("s3cret".to_string()));
        // Missing header ⇒ 401.
        assert_eq!(
            state
                .authorize_ingest(&HeaderMap::new())
                .unwrap_err()
                .status(),
            StatusCode::UNAUTHORIZED
        );
        // Wrong token ⇒ 401.
        assert_eq!(
            state
                .authorize_ingest(&bearer("wrong"))
                .unwrap_err()
                .status(),
            StatusCode::UNAUTHORIZED
        );
        // The right token ⇒ authorized.
        assert!(
            state.authorize_ingest(&bearer("s3cret")).is_ok(),
            "the matching operator bearer authorizes ingest"
        );
    }

    /// A mock [`LiveChatFetcher`] returning canned pages keyed by the requested `page_token` — the
    /// stand-in for the live YouTube API in the poller test.
    struct MockFetcher {
        pages: std::collections::HashMap<Option<String>, String>,
    }

    impl LiveChatFetcher for MockFetcher {
        fn fetch_page(
            &self,
            _live_chat_id: &str,
            _api_key: &str,
            page_token: Option<&str>,
        ) -> Result<String, LiveChatFetchError> {
            self.pages
                .get(&page_token.map(str::to_string))
                .cloned()
                .ok_or_else(|| LiveChatFetchError(format!("no canned page for {page_token:?}")))
        }
    }

    /// **The server-side poller sources `amount_micros` from YouTube, not a POST — and advances the
    /// cursor + interval page to page.** Two canned pages: the first (from the tail) carries a $5
    /// Super Chat + the `PAGE_2` cursor; the second (resumed from `PAGE_2`) a $2 one. The tally
    /// reflects both, and the poll interval tracks the page's `pollingIntervalMillis`.
    #[test]
    fn youtube_poller_ingests_and_advances() {
        let page1 = r#"{
            "nextPageToken": "PAGE_2",
            "pollingIntervalMillis": "3000",
            "items": [
              {"snippet":{"type":"superChatEvent","displayMessage":"$5",
                "superChatDetails":{"amountMicros":"5000000","userComment":"trade blows"}},
               "authorDetails":{"channelId":"UC_whale"}}
            ]
        }"#;
        let page2 = r#"{
            "nextPageToken": "PAGE_3",
            "pollingIntervalMillis": "5000",
            "items": [
              {"snippet":{"type":"superChatEvent","displayMessage":"$2",
                "superChatDetails":{"amountMicros":"2000000","userComment":"press on"}},
               "authorDetails":{"channelId":"UC_other"}}
            ]
        }"#;
        let mut pages = std::collections::HashMap::new();
        pages.insert(None, page1.to_string());
        pages.insert(Some("PAGE_2".to_string()), page2.to_string());
        let fetcher = MockFetcher { pages };

        let overlay = OverlayState::new(demo_round());
        let mut poller = YouTubePoller::new("API_KEY", "LIVE_CHAT_ID");

        // First poll (from the tail): the $5 trade-blows lands, the cursor advances to PAGE_2.
        let p1 = poller.poll_once(&fetcher, &overlay).expect("page 1 polled");
        assert_eq!(
            p1.options[0].votes, 5,
            "the $5 Super Chat weighs 5 (from YouTube)"
        );
        assert_eq!(p1.voters, 1);
        assert_eq!(poller.next_page_token(), Some("PAGE_2"));
        assert_eq!(poller.polling_interval(), Duration::from_millis(3000));

        // Second poll (resumed from PAGE_2): the $2 press-on lands beside it.
        let p2 = poller.poll_once(&fetcher, &overlay).expect("page 2 polled");
        assert_eq!(p2.options[0].votes, 5, "trade-blows unchanged");
        assert_eq!(p2.options[1].votes, 2, "the $2 press-on now counted");
        assert_eq!(p2.voters, 2, "two distinct YouTube voters");
        assert_eq!(poller.next_page_token(), Some("PAGE_3"));
        assert_eq!(poller.polling_interval(), Duration::from_millis(5000));
    }

    /// The poller floors a missing/too-small `pollingIntervalMillis` up to the guard, so an absent
    /// interval never spins a tight loop.
    #[test]
    fn poller_interval_is_floored() {
        let fetcher = MockFetcher {
            pages: std::iter::once((None, r#"{"items":[]}"#.to_string())).collect(),
        };
        let overlay = OverlayState::new(demo_round());
        let mut poller = YouTubePoller::new("k", "c");
        poller.poll_once(&fetcher, &overlay).expect("polled");
        assert_eq!(
            poller.polling_interval(),
            Duration::from_millis(MIN_POLL_INTERVAL_MILLIS),
            "an absent pollingIntervalMillis floors to the guard"
        );
    }

    // ─────────────────────────────────────────────────────────────────────────
    // The DEPLOYMENT close-loop — the crowd steers a LIVE world, closed on a timer.
    // What was demonstrated only in `#[cfg(test)]` (close→resolve→advance) is now the
    // deploy path: `drive_close`/`LiveCloseLoop` over a live demo Keep world.
    // ─────────────────────────────────────────────────────────────────────────

    fn chat(author: &str, text: &str) -> StreamEvent {
        StreamEvent {
            platform: "youtube".into(),
            author_id: author.into(),
            kind: dregg_stream_ingest::EventKind::Chat,
            amount_micros: 0,
            text: text.into(),
            ts: 0,
        }
    }

    /// **THE DEPLOY PATH — the live close-loop lands a real certified turn end to end.** A windowed
    /// round over a LIVE demo Keep world: three distinct voters back trade-blows (weight quorum +
    /// distinct floor both met), the deployment close-tick resolves the quorum-certified winner INTO
    /// the world as ONE real [`CertifiedTurn`], and the world state MOVES (hp 50 → 30). This is
    /// exactly the fold that was only demonstrated in `#[cfg(test)]` — now [`OverlayState::drive_close`]
    /// / [`LiveCloseLoop`], the deploy tick.
    #[test]
    fn live_close_loop_lands_a_certified_turn_into_the_world() {
        let live = keep_live_overlay(Duration::from_secs(30), None);
        assert_eq!(
            live.world().read_var("hp"),
            50,
            "the demo Keep begins at 50 HP"
        );
        let overlay = live.overlay();

        // Three distinct voters back trade-blows: weight 3 ≥ quorum, 3 distinct ≥ floor.
        overlay.ingest_events(vec![
            chat("A", "trade blows"),
            chat("B", "trade blows"),
            chat("C", "trade blows"),
        ]);

        let cert = match live.drive_once() {
            CloseTick::Landed(cert) => cert,
            other => panic!("a quorum-met window must land a certified turn, got {other:?}"),
        };
        assert_eq!(
            cert.command,
            Command::trade_blows(),
            "trade-blows certified + resolved"
        );
        assert_ne!(
            cert.receipt.turn_hash, [0u8; 32],
            "a genuine committed world turn"
        );
        assert_eq!(
            live.world().read_var("hp"),
            30,
            "the world resolved trade-blows (50 → 30) — the deploy path moved a REAL world"
        );
        assert_eq!(
            overlay.round.lock().unwrap().buffered(),
            0,
            "the window advanced (buffer reset) after the close"
        );
        assert_eq!(
            overlay.round.lock().unwrap().landed().len(),
            1,
            "the certified turn is recorded"
        );
    }

    /// **A below-quorum window does NOT move the world — it is retained for retry.** Two distinct
    /// voters clear the distinct floor but their weight (2) is below the quorum (3): the tick is
    /// [`CloseTick::Retained`], the world is unmoved, and the window keeps its ballots so a third
    /// voter next window carries it (then it lands).
    #[test]
    fn below_quorum_window_does_not_move_the_world() {
        let live = keep_live_overlay(Duration::from_secs(30), None);
        let overlay = live.overlay();
        overlay.ingest_events(vec![chat("A", "trade blows"), chat("B", "trade blows")]);

        match live.drive_once() {
            CloseTick::Retained(CrowdCloseError::Collective(CollectiveError::BelowQuorum)) => {}
            other => {
                panic!("a below-quorum window must be retained (world unmoved), got {other:?}")
            }
        }
        assert_eq!(live.world().read_var("hp"), 50, "the world did not move");
        assert_eq!(
            overlay.round.lock().unwrap().buffered(),
            2,
            "a retained window is left intact for retry"
        );

        // The third distinct voter arrives → quorum met → the retried window carries.
        overlay.ingest_events(vec![chat("C", "trade blows")]);
        assert!(
            live.drive_once().landed(),
            "once quorum is met the retained window lands a certified turn"
        );
        assert_eq!(
            live.world().read_var("hp"),
            30,
            "the world moved on the carried retry"
        );
    }

    /// **A stuck illegal-command window RECOVERS — it is not bricked.** The demo Keep is seeded at
    /// 20 HP, so trade-blows (`hp -= 20`, gated `FieldGte(hp,1)` on the post-state) is a killing blow
    /// the executor REFUSES. Three voters quorum-certify it anyway; the tick is [`CloseTick::Skipped`]
    /// (the executor's teeth), the world is unmoved, and — the recovery — the window is DROPPED so the
    /// next tick does NOT re-certify the same losing command (it falls to the distinct floor). The
    /// round moves on; it is not stuck re-refusing the illegal winner forever.
    #[test]
    fn stuck_illegal_command_window_recovers() {
        let mut world = deploy_keep(KEEP_LIVE_SEED);
        world.seed_var("hp", Value::Int(20)); // trade-blows (−20 → 0) fails FieldGte(hp,1).
        let world = std::sync::Arc::new(world);
        let scene = keep_scene();
        let overlay = OverlayState::new(demo_round());

        overlay.ingest_events(vec![
            chat("A", "trade blows"),
            chat("B", "trade blows"),
            chat("C", "trade blows"),
        ]);

        // The window quorum-certifies trade-blows, the executor REFUSES it, and the window is DROPPED.
        match overlay.drive_close(&world, &scene) {
            CloseTick::Skipped(CrowdCloseError::Collective(CollectiveError::World(_))) => {}
            other => panic!("a quorum-certified illegal command must be Skipped, got {other:?}"),
        }
        assert_eq!(
            world.read_var("hp"),
            20,
            "the world did not move (the illegal blow was refused)"
        );
        assert_eq!(
            overlay.round.lock().unwrap().buffered(),
            0,
            "the illegal window was dropped (not left to brick the round)"
        );

        // RECOVERY: no fresh votes ⇒ the round does NOT re-certify the illegal command — it falls to
        // the distinct floor and moves on. The round is unstuck.
        match overlay.drive_close(&world, &scene) {
            CloseTick::Retained(CrowdCloseError::DistinctFloor { voters: 0, .. }) => {}
            other => panic!("after the skip the round must move on (no re-certify), got {other:?}"),
        }
        assert_eq!(world.read_var("hp"), 20, "still unmoved after recovery");
    }

    /// **The `tokio::time::interval` timer actually drives the close on a running server.** Spawn the
    /// real [`LiveCloseLoop`] with a short window and a pre-seeded quorum: a certified turn lands INTO
    /// the world with NO manual `drive_*` call, and the reset tally is pushed over SSE — proving the
    /// deploy path is the timer, not a test-only poke.
    #[tokio::test]
    async fn timer_driven_close_loop_lands_a_turn_on_a_running_server() {
        let live = keep_live_overlay(Duration::from_millis(60), None);
        let overlay = live.overlay();
        let world = live.world();
        overlay.ingest_events(vec![
            chat("A", "trade blows"),
            chat("B", "trade blows"),
            chat("C", "trade blows"),
        ]);
        // Subscribe BEFORE the close so we can confirm the reset tally is pushed over SSE.
        let mut rx = overlay.subscribe();

        live.spawn(); // starts the `tokio::time::interval` close-loop on this runtime.

        // The first interval tick is immediate (consumed); the first REAL close is ~one window in.
        // POLL until the turn lands rather than a fixed sleep: the off-reactor close SIGNS the
        // electorate's ballots, and the real Lean-verified PQ core is meaningfully slower than the
        // `fips204` fallback — a fixed wait that suffices under `no-lean-link` is too short under
        // full-Lean (this test caught exactly that). Wait up to 10s (vs the 60ms window) for the move.
        let start = std::time::Instant::now();
        while world.read_var("hp") != 30 && start.elapsed() < std::time::Duration::from_secs(10) {
            tokio::time::sleep(Duration::from_millis(50)).await;
        }

        assert_eq!(
            world.read_var("hp"),
            30,
            "the timer drove a quorum-certified trade-blows INTO the world (50 → 30)"
        );
        assert_eq!(
            overlay.round.lock().unwrap().landed().len(),
            1,
            "exactly one certified turn landed on the timer"
        );
        assert!(
            rx.try_recv().is_ok(),
            "the close pushed the updated (reset) tally over SSE"
        );
    }
}
