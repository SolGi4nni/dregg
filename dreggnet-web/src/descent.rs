//! # `descent` — THE SPECTATOR / PROVENANCE surface for *The Descent*.
//!
//! The flagship's **growth artifact** (docs/GAME-STRATEGY.md Phase 3.2 — "the shareable verified
//! run"): a stranger opens a URL and *independently verifies* someone's run of the daily descent.
//! Not "trust me, I did this" — the page **re-executes the recorded run** server-side, on render,
//! against a fresh identically-seeded world, and shows the verdict. The unfair growth mechanic is a
//! proof, not a claim: a forged run shows **FAIL**, not a fake pass.
//!
//! Two server-rendered surfaces, additive to the [`catalog_router`](crate::catalog_router):
//! - `GET /descent/leaderboard[?day={key}]` — the day's **no-cheat leaderboard**: the ranked runs
//!   that provably reached the hoard, each row **re-verified on render** ([`verify_completion`], the
//!   same no-cheat verifier [`ugc_dregg::Registry::reverify_entry`]/`submit` run) against the day's
//!   published [`Universe`]. A forged / incomplete / lost run **does not appear** — it is excluded by
//!   re-verification, not by trusting a stored flag.
//! - `GET /descent/run/{id}` — a **run-card**: the run's summary (day / seed, character level+class,
//!   depth reached, alive/dead, the outcome) plus an **INDEPENDENT VERIFICATION panel** that replays
//!   the recorded receipt chain ([`spween_dregg::verify`] — chain-linkage + re-execution against a
//!   fresh, identically-seeded world) and shows **PASS/FAIL**. An honest run (won *or* lost) PASSES;
//!   a tampered run FAILS. The `id` is the **shareable link shape** the bot's result embed points at
//!   (see [`run_share_path`]).
//!
//! ## What is real vs. named
//! REAL here: the **server-side independent re-verification** — every leaderboard row and every
//! run-card is re-executed from the recorded moves on render (no trusted "verified" bit is stored;
//! [`Run`] is a plain, *untrusted* record, exactly as a persistence layer would hand one back). The
//! no-cheat property is [`ugc_dregg`]'s verbatim ([`verify_completion`]); the run-card replay is
//! [`spween_dregg`]'s audited re-verifier. NAMED, not built here: a live bind address / deployment;
//! *client-side* verification or a downloadable proof (this serves server-rendered HTML — the
//! stranger re-verifies by trusting THIS server, or by re-running the open-source verifier on the
//! recorded playthrough themselves); the `deos-js` live cell render. The bot links to a run by
//! putting [`run_share_path`] in its result embed.

use std::collections::{BTreeMap, HashMap};
use std::sync::{Arc, Mutex};

use axum::{
    Json, Router,
    extract::{Path, Query, State},
    http::StatusCode,
    response::Html,
    routing::{get, post},
};
use serde::Deserialize;

use dregg_node_target::{Landed, NodeError, NodeTarget, SubmittedTurn};
use dreggnet_offerings::daily_descent::{DAILY_DEPLOY_SEED, DailyDescent, HOARD_GOLD, daily_scene};
use procgen_dregg::CommittedSeed;
use spween_dregg::{
    PASSAGE_ENDED, PASSAGE_SLOT, Playthrough, Scene, WorldCell, compile_scene, parse, verify,
};
use ugc_dregg::{Completion, Universe, record_playthrough, verify_completion};

use crate::descent_store::{DescentRunStore, StoredDay, StoredRun};
use crate::{document, esc};

/// The author label the day's world is published under (a stable content-address input; the daily
/// world is anonymous-authored on the no-cheat board).
const DAY_AUTHOR: &str = "the-descent";

// ═══════════════════════════════════════════════════════════════════════════════
// The recorded, re-verifiable material.
// ═══════════════════════════════════════════════════════════════════════════════

/// A **published day** — the beacon-seeded daily world, its parsed scene + var→slot map (for
/// reading committed vars off a verified state), and its content-addressed [`Universe`] (what the
/// no-cheat board re-verifies against). Everyone who derives the day's seed derives the byte-identical
/// world, so this is reproducible provenance, not a private fixture.
struct Day {
    /// The day's key (e.g. a date / beacon-round tag). `?day=` selects it; the default is "today".
    key: String,
    /// The committed seed the day's world was drawn from (short-hex shown for provenance).
    seed: CommittedSeed,
    /// The day's world spec (title / warden HP / depth).
    day: DailyDescent,
    /// The parsed scene — re-deployed fresh for every run-card replay (never mutated).
    scene: Scene,
    /// The published, content-addressed universe (the no-cheat re-verification target).
    universe: Universe,
    /// var→slot map, to read `depth`/`gold`/`downed` off a (verified) committed state vector.
    var_slots: BTreeMap<String, usize>,
    /// The run ids recorded for this day (candidates for the board — each re-verified on render).
    run_ids: Vec<String>,
}

/// A **recorded run** — an UNTRUSTED record (a player name + the recorded [`Playthrough`] + display
/// metadata). Nothing here is believed: the leaderboard re-verifies it with [`verify_completion`]
/// and the run-card replays it with [`spween_dregg::verify`], on render, every time.
struct Run {
    /// The shareable run id (the `/descent/run/{id}` path segment).
    id: String,
    /// The day this run belongs to.
    day_key: String,
    /// The player label (display).
    player: String,
    /// The player's persistent character level at record time (profile metadata — NOT part of the
    /// run's independent re-verification, which covers the run's moves + committed outcome).
    level: u64,
    /// The player's chosen class id at record time (profile metadata; `0` = unset).
    class: u64,
    /// The recorded receipt chain — the un-retconnable material the surface re-executes.
    play: Playthrough,
}

/// **The spectator/provenance state** — published days + recorded (untrusted) runs, behind one
/// `Mutex`. Shared as an axum `State<Arc<DescentState>>`. All the material is plain `Send + Sync`
/// data (a scene / universe / playthrough), so — unlike the `!Send` council sessions behind the
/// catalog's [`HostThread`](crate::HostThread) — it lives directly in the `Arc`.
pub struct DescentState {
    inner: Mutex<Inner>,
    /// The durable backing (sqlite / in-memory), when a deployment supplies one. `None` = the
    /// in-RAM demo (the committed tests' path — nothing persists). When present, [`open_day`] +
    /// [`submit_run`] persist the reproducible public input, and [`load_from_store`] reconstructs +
    /// re-verifies it on boot.
    ///
    /// [`open_day`]: DescentState::open_day
    /// [`submit_run`]: DescentState::submit_run
    /// [`load_from_store`]: DescentState::load_from_store
    store: Option<Arc<dyn DescentRunStore>>,
    /// **Where a submitted run's winning turn is anchored on a real node.**
    /// [`NodeTarget::Local`] (the default) keeps everything in-process — [`settle_run`] is a no-op
    /// (`Ok(None)`, nothing leaves the process), so the committed tests + the node-free demo are
    /// untouched. A [`NodeTarget::Federation`] (from [`NodeTarget::from_env`], reading
    /// `DREGG_NODE_URL`) makes [`settle_run`] SUBMIT the run's final committed turn-hash to the
    /// running devnet node (`POST /turn/submit`) and confirm it landed on the node's finalized log
    /// (`GET /api/receipts`) — the adventure's turn on the node's ledger, not just in-process.
    /// This target is used ONLY at settle time; the leaderboard's re-verification stays in-process.
    ///
    /// [`settle_run`]: DescentState::settle_run
    settle_target: NodeTarget,
}

#[derive(Default)]
struct Inner {
    days: HashMap<String, Day>,
    runs: HashMap<String, Run>,
    /// The day `GET /descent/leaderboard` shows when no `?day=` is given (the first opened day).
    today: Option<String>,
}

impl DescentState {
    /// A fresh surface with no days or runs, and no durable backing (the in-RAM demo path). Settles
    /// [`NodeTarget::Local`] (in-process; opt into a devnet with [`with_node_target`](Self::with_node_target)).
    pub fn new() -> Self {
        DescentState {
            inner: Mutex::new(Inner::default()),
            store: None,
            settle_target: NodeTarget::Local,
        }
    }

    /// A fresh surface backed by a durable [`DescentRunStore`]. [`open_day`](Self::open_day) +
    /// [`submit_run`](Self::submit_run) persist through it; [`load_from_store`](Self::load_from_store)
    /// reconstructs + re-verifies its rows on boot. Settles [`NodeTarget::Local`] by default.
    pub fn with_store(store: Arc<dyn DescentRunStore>) -> Self {
        DescentState {
            inner: Mutex::new(Inner::default()),
            store: Some(store),
            settle_target: NodeTarget::Local,
        }
    }

    /// **Opt this leaderboard into anchoring submitted runs on a real devnet node.** By default a
    /// [`DescentState`] settles `Local` (a no-op; the board is entirely in-process). Pass a
    /// [`NodeTarget::Federation`] (e.g. [`NodeTarget::from_env`], reading `DREGG_NODE_URL`) to make
    /// a verify-gated `POST /descent/submit` ALSO [`settle_run`](Self::settle_run) — submitting the
    /// run's final committed turn-hash to the running node's ledger and confirming it landed. The
    /// leaderboard's re-verification is unaffected: it stays in-process replay; only the opt-in
    /// settle touches the node.
    pub fn with_node_target(mut self, target: NodeTarget) -> Self {
        self.settle_target = target;
        self
    }

    /// Whether a submitted run will actually be anchored on a devnet node (a
    /// [`NodeTarget::Federation`] was opted in) vs. the in-process `Local` default.
    pub fn settles_to_a_node(&self) -> bool {
        self.settle_target.is_federation()
    }

    /// **Open (publish) a day's world** under `key`, drawn from `seed` — derive the byte-identical
    /// daily world everyone else derives, parse + compile its scene, and publish its content-addressed
    /// [`Universe`] (the no-cheat re-verification target). The first day opened becomes the default
    /// "today". Idempotent per key: **a day already open is left untouched** (its recorded runs are
    /// preserved), so a reload-then-reseed ordering never wipes the board. When a durable store is
    /// present, the day's reproducible descriptor (its committed seed) is persisted.
    pub fn open_day(&self, key: &str, seed: CommittedSeed) {
        {
            let mut inner = self.inner.lock().unwrap();
            if inner.days.contains_key(key) {
                if inner.today.is_none() {
                    inner.today = Some(key.to_string());
                }
                return;
            }
            let day = daily_scene(&seed);
            let scene = parse(&day.source, "daily-descent.scene").expect("the day's scene parses");
            let var_slots = compile_scene(&scene)
                .map(|c| c.var_slots)
                .unwrap_or_default();
            let universe = day
                .universe(DAY_AUTHOR)
                .expect("the day's world publishes as a universe");
            inner.days.insert(
                key.to_string(),
                Day {
                    key: key.to_string(),
                    seed,
                    day,
                    scene,
                    universe,
                    var_slots,
                    run_ids: Vec::new(),
                },
            );
            if inner.today.is_none() {
                inner.today = Some(key.to_string());
            }
        }
        if let Some(store) = &self.store {
            let _ = store.persist_day(&StoredDay {
                key: key.to_string(),
                seed_hex: hex32(seed.as_bytes()),
            });
        }
    }

    /// **Submit a run over its reproducible input** — the verify-gated ingest a stranger's `POST`
    /// (and the demo seeding) drives. Re-records the `moves` on a fresh copy of the day's published
    /// universe ([`record_playthrough`]) and re-verifies the result with the no-cheat verifier
    /// ([`verify_completion`]): an illegal move, a losing / incomplete line, or a forged claim is
    /// **rejected** (`Err`, fail-closed — nothing ingests or persists). A run that provably reaches
    /// the hoard is ingested (so it ranks on the board) AND — when a durable store is present —
    /// persisted as reproducible public input (the move sequence), so it survives a restart.
    /// Returns the verified turns-to-win on success.
    pub fn submit_run(
        &self,
        day_key: &str,
        run_id: &str,
        player: &str,
        level: u64,
        class: u64,
        moves: &[usize],
    ) -> Result<usize, String> {
        let turns = self.reverify_and_ingest(day_key, run_id, player, level, class, moves)?;
        if let Some(store) = &self.store {
            let moves_json = serde_json::to_string(moves).unwrap_or_else(|_| "[]".to_string());
            let _ = store.persist_run(&StoredRun {
                run_id: run_id.to_string(),
                day_key: day_key.to_string(),
                player: player.to_string(),
                level,
                class,
                moves_json,
            });
        }
        Ok(turns)
    }

    /// **Anchor a ranked run's winning turn on the devnet node** — the opt-in bridge from the
    /// in-process board to a real committed turn on the running node's ledger. Fail-closed and
    /// non-vacuous:
    /// * `Local` (the default): a no-op — returns `Ok(None)`, nothing leaves the process (so the
    ///   committed tests + the node-free demo are byte-identical).
    /// * `Federation` (a `DREGG_NODE_URL` node): submit the run's FINAL committed turn-hash to the
    ///   node (`POST /turn/submit`, an `EmitEvent`-of-commitment under the day's scene topic) AND
    ///   confirm it landed on the node's finalized log (`GET /api/receipts`). `Ok(Some(Landed))`
    ///   iff the node accepted + finalized it; `Err` (fail-closed) on a rejected / unreachable /
    ///   non-landing submit.
    ///
    /// This settles only a run that is ALREADY on the board — i.e. one [`submit_run`](Self::submit_run)
    /// re-executed to the hoard + no-cheat-verified in-process. A forged / losing / illegal run is
    /// refused by that gate before it can rank, so it never reaches here (the node is never touched
    /// for a cheat). The commitment is the run's last committed step's `turn_hash` (its
    /// un-retconnable receipt-chain tip); the topic is the day's stable scene id.
    ///
    /// [`submit_run`]: Self::submit_run
    pub fn settle_run(&self, day_key: &str, run_id: &str) -> Result<Option<Landed>, NodeError> {
        let submitted = {
            let inner = self.inner.lock().unwrap();
            let run = inner
                .runs
                .get(run_id)
                .ok_or_else(|| NodeError::Rejected(format!("no such run to settle: {run_id}")))?;
            let day = inner.days.get(day_key).ok_or_else(|| {
                NodeError::Rejected(format!("no such day to settle against: {day_key}"))
            })?;
            // The run's fingerprint = the tip of its committed receipt chain (its last landed step,
            // else genesis). The topic = the day's stable scene id (`daily-descent-{sid}`).
            let commitment = run
                .play
                .steps
                .last()
                .map(|s| s.receipt.turn_hash)
                .unwrap_or(run.play.genesis.turn_hash);
            let domain = day.scene.meta.id.to_string();
            SubmittedTurn::new(domain, commitment)
        };
        // Route through the opted-in target: Local = Ok(None) no-op; Federation = submit + confirm
        // landed on the node's finalized log (fail-closed on rejection / unreachable / non-landing).
        self.settle_target.route(&submitted)
    }

    /// Re-record + re-verify a move sequence against the day's published universe, and — only if it
    /// re-executes to the win — ingest it (in-RAM). The verify-gate shared by [`submit_run`] (which
    /// also persists) and [`load_from_store`] (which does not re-persist). `Err` on any refusal:
    /// unknown/closed day, an illegal move (executor refusal on replay), or a non-winning /
    /// tampered line ([`verify_completion`] rejecting it).
    ///
    /// [`submit_run`]: Self::submit_run
    /// [`load_from_store`]: Self::load_from_store
    fn reverify_and_ingest(
        &self,
        day_key: &str,
        run_id: &str,
        player: &str,
        level: u64,
        class: u64,
        moves: &[usize],
    ) -> Result<usize, String> {
        let universe = {
            let inner = self.inner.lock().unwrap();
            let day = inner
                .days
                .get(day_key)
                .ok_or_else(|| format!("no such day: {day_key}"))?;
            day.universe.clone()
        };
        // Re-record the moves on a FRESH identically-seeded world — an illegal move is refused here
        // by the real executor.
        let play =
            record_playthrough(&universe, moves).map_err(|e| format!("illegal move: {e:?}"))?;
        // THE NO-CHEAT TOOTH: re-execute + require the win + bind the claimed turn count.
        let completion = Completion {
            universe: universe.id(),
            player: player.to_string(),
            play: play.clone(),
            claimed_turns: moves.len(),
        };
        let turns = verify_completion(&universe, &completion)
            .map_err(|e| format!("verification failed: {e:?}"))?;
        // Only a provably-winning run reaches here — record it (the render path re-verifies again).
        self.ingest_run(day_key, run_id, player, level, class, play);
        Ok(turns)
    }

    /// **BOOT REPLAY + RE-VERIFY.** Reconstruct the board from the durable store: regenerate every
    /// persisted day byte-for-byte from its committed seed ([`open_day`](Self::open_day)), then
    /// REPLAY every persisted run through the no-cheat verify-gate
    /// ([`reverify_and_ingest`](Self::reverify_and_ingest)) — re-executing the recorded moves on a
    /// fresh identically-seeded world and requiring the win. A tampered row (a corrupt seed, an
    /// edited move line, a losing line, an illegal move) never re-verifies and is silently DROPPED;
    /// it cannot resurrect a cheat onto the board. A no-op when no store is configured.
    pub fn load_from_store(&self) {
        let Some(store) = self.store.clone() else {
            return;
        };
        for d in store.list_days().unwrap_or_default() {
            if let Some(bytes) = decode_hex32(&d.seed_hex) {
                self.open_day(&d.key, CommittedSeed::from_bytes(bytes));
            }
        }
        for r in store.list_runs().unwrap_or_default() {
            let Ok(moves) = serde_json::from_str::<Vec<usize>>(&r.moves_json) else {
                continue;
            };
            // A drop here is silent-and-correct: the row no longer re-verifies.
            let _ = self
                .reverify_and_ingest(&r.day_key, &r.run_id, &r.player, r.level, r.class, &moves);
        }
    }

    /// Set which opened day `GET /descent/leaderboard` shows by default.
    pub fn set_today(&self, key: &str) {
        self.inner.lock().unwrap().today = Some(key.to_string());
    }

    /// The day key `GET /descent/leaderboard` / a dayless `POST /descent/submit` default to (the
    /// first opened day), if any.
    pub fn today(&self) -> Option<String> {
        self.inner.lock().unwrap().today.clone()
    }

    /// **Ingest a recorded run** for a day — store the (untrusted) playthrough + display metadata
    /// under the shareable `run_id`. No verification happens here: the surface re-verifies on every
    /// render. Returns `false` if the day is not open. `run_id` is what [`run_share_path`] links to.
    pub fn ingest_run(
        &self,
        day_key: &str,
        run_id: &str,
        player: &str,
        level: u64,
        class: u64,
        play: Playthrough,
    ) -> bool {
        let mut inner = self.inner.lock().unwrap();
        if !inner.days.contains_key(day_key) {
            return false;
        }
        inner.runs.insert(
            run_id.to_string(),
            Run {
                id: run_id.to_string(),
                day_key: day_key.to_string(),
                player: player.to_string(),
                level,
                class,
                play,
            },
        );
        if let Some(day) = inner.days.get_mut(day_key) {
            if !day.run_ids.iter().any(|r| r == run_id) {
                day.run_ids.push(run_id.to_string());
            }
        }
        true
    }
}

impl Default for DescentState {
    fn default() -> Self {
        DescentState::new()
    }
}

/// **The shareable link shape** for a run — the path the bot's result embed points a stranger at
/// (`https://<host>/descent/run/{run_id}`). Opening it re-verifies the run and shows the proof.
pub fn run_share_path(run_id: &str) -> String {
    format!("/descent/run/{run_id}")
}

// ═══════════════════════════════════════════════════════════════════════════════
// Router + handlers.
// ═══════════════════════════════════════════════════════════════════════════════

/// **Build the spectator/provenance router** over a shared [`DescentState`]. Additive — mount it on
/// the same axum app as [`router`](crate::router) / [`catalog_router`](crate::catalog_router).
///
/// - `GET  /descent` (and `/descent/`, `/descent/leaderboard`) — the day's re-verified no-cheat
///   board. `/descent` is the SHORT landing URL (what the landing page + a shared link point at);
///   `/descent/leaderboard` is the same view under its explicit name (kept for links that name it).
///   All three render [`get_leaderboard`] — the `?day={key}` selector applies to each.
/// - `GET  /descent/run/{id}` — a run-card with the independent-verification panel;
/// - `POST /descent/submit` — the verify-gated HTTP run-ingest: a stranger submits a run's
///   reproducible input (day + player + move sequence) and it is re-executed + no-cheat-verified
///   before it can rank (an honest run ingested + persisted, a forged run rejected 4xx).
pub fn descent_router(state: Arc<DescentState>) -> Router {
    Router::new()
        // The SHORT landing URL for the board — `GET /descent` renders the no-cheat leaderboard
        // (previously a 404: only `/descent/leaderboard` was mounted, so the bare `/descent` a
        // stranger types / the landing button points at fell through). The trailing-slash form is
        // mounted too (axum treats `/descent` and `/descent/` as distinct paths).
        .route("/descent", get(get_leaderboard))
        .route("/descent/", get(get_leaderboard))
        .route("/descent/leaderboard", get(get_leaderboard))
        .route("/descent/run/{id}", get(get_run_card))
        .route("/descent/submit", post(post_submit))
        .with_state(state)
}

/// The JSON body of `POST /descent/submit` — a run's **reproducible public input**: which day, the
/// player + display metadata, and the move sequence (choice indices). Nothing else is needed (or
/// trusted): the server re-executes the moves on a fresh identically-seeded world and re-verifies.
#[derive(Debug, Clone, Deserialize)]
pub struct SubmitRun {
    /// The day key to submit against; absent → the state's designated "today".
    #[serde(default)]
    pub day: Option<String>,
    /// The player label (display).
    pub player: String,
    /// The player's character level (display metadata).
    #[serde(default)]
    pub level: u64,
    /// The player's class id (display metadata; `0` = unset).
    #[serde(default)]
    pub class: u64,
    /// The move sequence — the choice index at each passage, in order.
    pub moves: Vec<usize>,
}

/// `POST /descent/submit` — **the HTTP run-ingest seam.** Reads a run's reproducible input (day +
/// player + move sequence) and drives it through the verify-gate ([`DescentState::submit_run`]):
/// the moves are re-executed on a fresh identically-seeded world and no-cheat-verified BEFORE the
/// run can rank. A run that provably reaches the hoard is ingested (it then appears on the
/// leaderboard) and — with a durable store — persisted; a forged / losing / illegal run is
/// **rejected `400`** (fail-closed — it never ranks). The `run_id` is derived from the content
/// (`blake3(day ‖ player ‖ moves)`), so a resubmission is idempotent and the response links the
/// shareable run-card.
async fn post_submit(
    State(state): State<Arc<DescentState>>,
    Json(body): Json<SubmitRun>,
) -> (StatusCode, Json<serde_json::Value>) {
    let day = match body.day.clone().or_else(|| state.today()) {
        Some(d) => d,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(serde_json::json!({
                    "ranked": false,
                    "error": "no day is open",
                })),
            );
        }
    };
    let run_id = derive_run_id(&day, &body.player, &body.moves);
    match state.submit_run(
        &day,
        &run_id,
        &body.player,
        body.level,
        body.class,
        &body.moves,
    ) {
        Ok(turns) => {
            // The run ranks in-process. If a devnet is opted in (`DREGG_NODE_URL`), ALSO anchor its
            // winning turn on the running node's ledger — a real committed turn on-chain, confirmed
            // landed. The blocking node submit runs off the async worker via `spawn_blocking`. Local
            // mode is a no-op (`Ok(None)`), so this branch's shape is unchanged for the demo/tests.
            let mut resp = serde_json::json!({
                "ranked": true,
                "run_id": run_id,
                "turns": turns,
                "share": run_share_path(&run_id),
                "detail": "re-executed + no-cheat-verified; the run now ranks on the board",
            });
            if state.settles_to_a_node() {
                let st = state.clone();
                let day2 = day.clone();
                let rid = run_id.clone();
                let settled = tokio::task::spawn_blocking(move || st.settle_run(&day2, &rid))
                    .await
                    .unwrap_or_else(|e| {
                        Err(NodeError::Transport(format!("settle task join: {e}")))
                    });
                match settled {
                    Ok(Some(landed)) => {
                        resp["settled"] = serde_json::json!(true);
                        resp["node_turn_hash"] = serde_json::json!(hex32(&landed.node_turn_hash));
                        resp["detail"] = serde_json::json!(
                            "re-executed + no-cheat-verified; ranked AND anchored on the devnet node's ledger"
                        );
                    }
                    Ok(None) => {}
                    Err(e) => {
                        // The run still ranks in-process; the on-chain anchor FAILED. A node was
                        // configured (`settles_to_a_node()`), so silence here would read as success —
                        // surface the failure honestly: flip `settled` false, carry the error, and
                        // REWRITE `detail` so it does not still claim the anchor landed. The board's
                        // `ranked` flag is only ever the in-process no-cheat verdict; anchoring is a
                        // separate leg with its own `settled` flag (which a caller MUST read).
                        crate::metrics::inc_anchor_failure();
                        resp["settled"] = serde_json::json!(false);
                        resp["settle_error"] = serde_json::json!(e.to_string());
                        resp["detail"] = serde_json::json!(
                            "re-executed + no-cheat-verified; ranked in-process, but the devnet-node \
                             anchor FAILED (settled:false) — the run is NOT on the node ledger"
                        );
                    }
                }
            }
            (StatusCode::OK, Json(resp))
        }
        // Fail-closed: a forged / losing / illegal run is refused before it can rank.
        Err(why) => (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({
                "ranked": false,
                "error": why,
                "detail": "rejected by re-execution — nothing ingested (no-cheat)",
            })),
        ),
    }
}

/// A content-addressed, shareable run id for a submitted run — `sub-` + short hex of
/// `blake3(day ‖ player ‖ moves_json)`. Deterministic, so a resubmission of the same run maps to
/// the same id (idempotent ingest).
fn derive_run_id(day: &str, player: &str, moves: &[usize]) -> String {
    let moves_json = serde_json::to_string(moves).unwrap_or_else(|_| "[]".to_string());
    let mut h = blake3::Hasher::new();
    h.update(day.as_bytes());
    h.update(&[0]);
    h.update(player.as_bytes());
    h.update(&[0]);
    h.update(moves_json.as_bytes());
    let hex: String = h.finalize().as_bytes()[..8]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    format!("sub-{hex}")
}

/// The `?day=` selector for the leaderboard (absent → the default "today").
#[derive(Debug, Clone, Default, Deserialize)]
pub struct DayQuery {
    /// The day key to show; absent → the state's designated "today".
    #[serde(default)]
    pub day: Option<String>,
}

/// `GET /descent/leaderboard[?day={key}]` — render the day's no-cheat leaderboard. Every candidate
/// run is **re-verified on render** ([`verify_completion`] against the day's published universe): a
/// run that provably reached the hoard is ranked (by verified turns-to-win); a forged / incomplete /
/// lost run is **excluded** (it never trusted a stored flag).
async fn get_leaderboard(
    State(state): State<Arc<DescentState>>,
    Query(q): Query<DayQuery>,
) -> Html<String> {
    let inner = state.inner.lock().unwrap();
    let key = q.day.clone().or_else(|| inner.today.clone());
    let Some(key) = key else {
        return Html(leaderboard_missing(None));
    };
    let Some(day) = inner.days.get(&key) else {
        return Html(leaderboard_missing(Some(&key)));
    };

    // Re-verify EVERY candidate on render. Only a provable win ranks; anything else is excluded.
    let mut rows: Vec<Row> = Vec::new();
    for rid in &day.run_ids {
        let Some(run) = inner.runs.get(rid) else {
            continue;
        };
        let completion = Completion {
            universe: day.universe.id(),
            player: run.player.clone(),
            play: run.play.clone(),
            claimed_turns: run.play.steps.len(),
        };
        // THE NO-CHEAT TOOTH, on render: re-execute against a fresh identically-seeded world +
        // require the win + bind the claimed result. A forged / lost / incomplete run errs → skipped.
        if let Ok(turns) = verify_completion(&day.universe, &completion) {
            let depth = final_var(day, &run.play, "depth");
            rows.push(Row {
                run_id: rid.clone(),
                player: run.player.clone(),
                turns,
                depth,
            });
        }
    }
    // Rank by verified turns-to-win (lower first); stable for ties.
    rows.sort_by(|a, b| a.turns.cmp(&b.turns).then_with(|| a.player.cmp(&b.player)));

    Html(leaderboard_page(day, &rows))
}

/// `GET /descent/run/{id}` — render a run-card: the run's summary + the independent-verification
/// panel. The panel **replays the recorded receipt chain** ([`spween_dregg::verify`]) against a fresh,
/// identically-seeded world — an honest run (won or lost) PASSES; a tampered run FAILS. The committed
/// outcome (depth / hoard / defeat) is read off the verified final state (trusted only on PASS).
async fn get_run_card(
    State(state): State<Arc<DescentState>>,
    Path(id): Path<String>,
) -> Html<String> {
    let inner = state.inner.lock().unwrap();
    let Some(run) = inner.runs.get(&id) else {
        return Html(run_missing(&id));
    };
    let Some(day) = inner.days.get(&run.day_key) else {
        return Html(run_missing(&id));
    };

    // INDEPENDENT RE-VERIFICATION: deploy a fresh, identically-seeded world and re-execute the
    // recorded moves (chain-linkage + replay). Not a trusted flag — a real re-run, here, now.
    let verified = match WorldCell::deploy(&day.scene, DAILY_DEPLOY_SEED) {
        Ok(fresh) => verify(fresh, &day.scene, &run.play).is_ok(),
        Err(_) => false,
    };

    // The committed outcome, read off the (verified) final recorded state.
    let last_state = run.play.steps.last().map(|s| s.state.as_slice());
    let ended = last_state
        .and_then(|s| s.get(PASSAGE_SLOT))
        .is_some_and(|&p| p == PASSAGE_ENDED);
    let gold = final_var(day, &run.play, "gold");
    let depth = final_var(day, &run.play, "depth");
    let downed = final_var(day, &run.play, "downed");
    let won = ended && gold == HOARD_GOLD;
    let fell = downed == 1;

    Html(run_card_page(
        day, run, verified, won, fell, ended, depth, gold,
    ))
}

/// Read a committed var off a playthrough's final recorded state via the day's var→slot map (`0` if
/// absent). Sound to read only when the chain re-verifies (which guarantees the recorded state is the
/// faithfully-reproduced one).
fn final_var(day: &Day, play: &Playthrough, name: &str) -> u64 {
    let Some(last) = play.steps.last() else {
        return 0;
    };
    day.var_slots
        .get(name)
        .and_then(|&slot| last.state.get(slot))
        .copied()
        .unwrap_or(0)
}

// ═══════════════════════════════════════════════════════════════════════════════
// Rendering.
// ═══════════════════════════════════════════════════════════════════════════════

/// One ranked, re-verified leaderboard row.
struct Row {
    run_id: String,
    player: String,
    turns: usize,
    depth: u64,
}

/// Hex-encode 32 bytes (a committed seed, for durable persistence — the full round-trip encoding).
fn hex32(bytes: &[u8; 32]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Decode a 64-char hex string back to 32 bytes (`None` on any malformed input — a tampered seed
/// row is dropped on boot).
fn decode_hex32(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(s.get(2 * i..2 * i + 2)?, 16).ok()?;
    }
    Some(out)
}

/// A short hex provenance tag of a day's seed (first 4 bytes) — the same tag `daily_scene` uses.
fn seed_tag(seed: &CommittedSeed) -> String {
    seed.as_bytes()[..4]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// The leaderboard page — a ranked table of provably-winning runs, each row re-verified on render
/// and linking to its run-card.
fn leaderboard_page(day: &Day, rows: &[Row]) -> String {
    let mut table = String::new();
    if rows.is_empty() {
        // An empty board is a STATEMENT, not a blank: it is empty *because* nothing has proven
        // itself yet. Say so in the panel's own voice rather than dropping a bare sentence.
        table.push_str(
            "<div class=\"deos-section tag-muted\"><h2>No verified runs yet</h2>\
             <p class=\"prose\">A run appears here only once it re-executes to the hoard. A forged \
             or unfinished run never ranks.</p></div>",
        );
    } else {
        // The table scans: a mono tabular-numeral rank (gold/silver/bronze for the podium), the
        // player as the row's subject, and the proof link as the mint call to action.
        table.push_str(
            "<div class=\"table-wrap\"><table class=\"board\">\
             <thead><tr><th>#</th><th>player</th><th>turns</th>\
             <th>depth</th><th>proof</th></tr></thead><tbody>",
        );
        for (i, r) in rows.iter().enumerate() {
            table.push_str(&format!(
                "<tr><td class=\"rank\">{rank}</td><td class=\"player\">{player}</td>\
                 <td class=\"num\">{turns}</td><td class=\"num\">{depth}</td>\
                 <td><a href=\"{href}\">verify this run \
                 <span class=\"arr\" aria-hidden=\"true\">→</span></a></td></tr>",
                rank = i + 1,
                player = esc(&r.player),
                turns = r.turns,
                depth = r.depth,
                href = esc(&run_share_path(&r.run_id)),
            ));
        }
        table.push_str("</tbody></table></div>");
    }
    let body = format!(
        "<main class=\"session\">\
         <div class=\"page-head\" style=\"padding-top:var(--s4)\">\
         <p class=\"eyebrow\">Re-verified on this request</p>\
         <h1>The Descent — {title}</h1>\
         <p class=\"deck\">The no-cheat leaderboard. Every row below was re-executed from its \
         recorded moves against a fresh, identically-seeded world and required to reach the hoard. \
         A forged or unfinished run does not appear — it is excluded by re-verification, not by \
         trusting a stored flag.</p></div>\
         <div class=\"kv\">\
         <div><p class=\"k\">Day</p><p class=\"v mono\">{key}</p></div>\
         <div><p class=\"k\">Seed</p><p class=\"v mono\">{seed}</p></div>\
         <div><p class=\"k\">Warden HP</p><p class=\"v mono\">{whp}</p></div>\
         <div><p class=\"k\">Depth</p><p class=\"v mono\">{rooms}</p></div>\
         </div>\
         {table}\
         <div class=\"receipt ok\"><span class=\"dot\"></span>\
         <span class=\"label\">independent by construction</span>\
         <span class=\"detail\">open any run to re-verify it yourself</span></div>\
         </main>",
        title = esc(&day.day.title),
        key = esc(&day.key),
        seed = esc(&seed_tag(&day.seed)),
        whp = day.day.warden_hp,
        rooms = day.day.deepening_rooms,
        table = table,
    );
    document(
        &format!("The Descent — {} · leaderboard", day.day.title),
        "descent",
        &body,
    )
}

/// A run-card — the run summary + the independent-verification panel (PASS/FAIL).
#[allow(clippy::too_many_arguments)]
fn run_card_page(
    day: &Day,
    run: &Run,
    verified: bool,
    won: bool,
    fell: bool,
    ended: bool,
    depth: u64,
    gold: u64,
) -> String {
    // THE VERDICT — the whole point of the page, so it is built like a certificate rather than
    // another look-alike navy panel: a stamped PASS/FAIL badge over a mint/rose field. (The old
    // markup reached for inline `style="border-color:#833"` / `style="color:#f77"` hacks; the
    // states are real classes now.)
    let panel = if verified {
        "<section class=\"verdict pass\">\
         <h2><span class=\"stamp\">PASS</span>Independent verification — PASS</h2>\
         <p>This run was <strong>re-executed on this request</strong>: a fresh, \
         identically-seeded world was deployed and driven through the recorded moves, and the \
         committed receipt chain re-verified (chain-linkage + replay). You are not trusting a stored \
         result — you are seeing the run <strong>proven</strong>.</p>\
         <p class=\"receipt ok\" style=\"margin-top:.8rem\"><span class=\"dot\"></span>\
         <span class=\"label\">verified by re-execution</span>\
         <span class=\"verdict\">yes</span></p></section>"
            .to_string()
    } else {
        "<section class=\"verdict fail\">\
         <h2><span class=\"stamp\">FAIL</span>Independent verification — FAIL</h2>\
         <p>Re-execution against a fresh identically-seeded world <strong>rejected</strong> \
         this record: the recorded moves do not honestly reproduce the committed chain. This run is \
         <strong>forged or tampered</strong> — its claimed outcome below is NOT proven.</p>\
         <p class=\"receipt refused\" style=\"margin-top:.8rem\"><span class=\"dot\"></span>\
         <span class=\"label\">verified by re-execution</span>\
         <span class=\"verdict\">NO</span></p></section>"
            .to_string()
    };

    // The outcome line — trusted only on PASS.
    let outcome = if !verified {
        "unverifiable (forged / tampered record)".to_string()
    } else if won {
        format!("SURVIVED — seized the hoard ({gold} gold) at depth {depth}")
    } else if fell {
        format!("FELL — downed by the warden at depth {depth}; the run is lost")
    } else if ended {
        format!("turned back — the descent ended without the hoard (depth {depth})")
    } else {
        format!("in progress — depth {depth}")
    };
    let alive = if fell {
        "dead (hardcore permadeath — final)"
    } else {
        "alive"
    };
    let class = if run.class == 0 {
        "unset".to_string()
    } else {
        format!("class #{}", run.class)
    };
    let turns = run.play.steps.len() + 1; // genesis + committed steps

    // The run's facts as a key/value grid — labelled, scannable, the verifiable material in the
    // mono voice. The old page stacked them as five `Outcome: …` / `Status: …` paragraphs, which
    // is exactly the debug-dump register this pass is here to kill.
    let body = format!(
        "<div class=\"crumb\"><a href=\"/descent/leaderboard?day={key}\">← the no-cheat \
         leaderboard</a><span class=\"sep\">·</span><strong>{player}</strong>\
         <span class=\"sep\">·</span><span class=\"sid\">a shared run</span></div>\
         <main class=\"session\">\
         <div class=\"page-head\" style=\"padding-top:var(--s4)\">\
         <p class=\"eyebrow\">The Descent — {title}</p>\
         <h1>{player}'s run</h1>\
         <p class=\"deck\">{outcome}</p></div>\
         <div class=\"kv\">\
         <div><p class=\"k\">Day</p><p class=\"v mono\">{key}</p></div>\
         <div><p class=\"k\">Seed</p><p class=\"v mono\">{seed}</p></div>\
         <div><p class=\"k\">Character</p><p class=\"v\">level {level} · {class}</p></div>\
         <div><p class=\"k\">Status</p><p class=\"v\">{alive}</p></div>\
         <div><p class=\"k\">Chain</p><p class=\"v mono\">{turns} verified turns</p></div>\
         <div><p class=\"k\">Warden HP</p><p class=\"v mono\">{whp}</p></div>\
         </div>\
         {panel}\
         <a class=\"backlink\" href=\"/descent/leaderboard?day={key}\">← today's no-cheat \
         leaderboard</a>\
         </main>",
        player = esc(&run.player),
        title = esc(&day.day.title),
        key = esc(&day.key),
        seed = esc(&seed_tag(&day.seed)),
        level = run.level,
        class = esc(&class),
        outcome = esc(&outcome),
        alive = alive,
        turns = turns,
        whp = day.day.warden_hp,
        panel = panel,
    );
    document(
        &format!("The Descent — {}'s run", run.player),
        "descent",
        &body,
    )
}

/// The page shown when no day (or an unknown day) is requested.
fn leaderboard_missing(key: Option<&str>) -> String {
    let what = match key {
        Some(k) => format!("No day <code>{}</code> is open.", esc(k)),
        None => "No daily descent is open yet.".to_string(),
    };
    let body = format!(
        "<main class=\"session\"><div class=\"notice refused\" role=\"status\">{what}</div>\
         <p class=\"prose\"><a class=\"backlink\" href=\"/\">← Back to DreggNet Cloud</a></p>\
         </main>",
    );
    document("The Descent — leaderboard", "descent", &body)
}

/// The page shown for an unknown run id.
fn run_missing(id: &str) -> String {
    let body = format!(
        "<main class=\"session\"><div class=\"notice refused\" role=\"status\">No such run \
         <code>{id}</code>.</div>\
         <p class=\"prose\"><a class=\"backlink\" href=\"/descent\">← The no-cheat leaderboard</a>\
         </p></main>",
        id = esc(id),
    );
    document("The Descent — unknown run", "descent", &body)
}
