//! # `descent` — THE SPECTATOR / PROVENANCE surface for *The Descent*.
//!
//! The flagship's **growth artifact** (docs/GAME-STRATEGY.md Phase 3.2 — "the shareable verified
//! run"): a stranger opens a URL and *independently verifies* someone's run of the daily descent.
//! Not "trust me, I did this" — the page **re-executes the recorded run** server-side, on render,
//! against a fresh identically-seeded world, and shows the verdict. The unfair growth mechanic is a
//! proof, not a claim: a forged run shows **FAIL**, not a fake pass.
//!
//! Server-rendered surfaces, additive to the [`catalog_router`](crate::catalog_router):
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
//! - `POST /descent/native/submit` + `GET /descent/native/run/{id}` — the browser-native
//!   compatibility lane. The Lean-native game emits verbs plus an exact receipt/state/root record,
//!   not the older procgen choice-index tape. The server replays that record through
//!   `NativeDescentOffering`; exact records get a share card and crowned exits rank in a visibly
//!   separate native table. No lossy cross-game translation is claimed.
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
use std::sync::{Arc, Mutex, OnceLock};

use axum::{
    Json, Router,
    extract::{DefaultBodyLimit, Path, Query, State},
    http::StatusCode,
    response::Html,
    routing::{get, post},
};
use serde::Deserialize;

use dregg_node_target::{Landed, NodeError, NodeTarget, SubmittedTurn};
use dreggnet_offerings::daily_descent::{DAILY_DEPLOY_SEED, DailyDescent, HOARD_GOLD, daily_scene};
use dreggnet_offerings::native_descent::Rarity;
// ⚑ THE WIRE IS NOT DECLARED HERE. `dreggnet_offerings::native_descent_wire` owns the ONE
// portable-record type and the ONE exact-replay gate; `wasm/src/bindings_native_descent.rs` is the
// browser producer of that same type and this module is the server consumer. The hand-mirrored
// pair (`PortableRecord` there, `NativePortableRecord` here — same format string, same version,
// both `deny_unknown_fields`, no shared code) is DELETED: it was the mechanism that kept the
// settled run's minted `banked_notes` from ever crossing the browser->server boundary.
use dreggnet_offerings::native_descent_wire::{
    MAX_PORTABLE_RECORD_BYTES, PortableCompletion, PortableRecord, PortableSim,
    replay_portable_record,
};
use dungeon_on_dregg::descent::{DayWorld, day_index, day_world};
use procgen_dregg::CommittedSeed;
use procgen_dregg::beacon::DailyBeacon;
use procgen_dregg::descent_day::{self, DescentDay};
use spween_dregg::{
    PASSAGE_ENDED, PASSAGE_SLOT, Playthrough, Scene, WorldCell, compile_scene, parse, verify,
};
use ugc_dregg::{Completion, Universe, record_playthrough, verify_completion};
use webauth_core::identity_resolve::RootResolver;

use crate::descent_card::{CARD_STYLE, RunStory};
use crate::descent_store::{DescentRunStore, StoredDay, StoredNativeRun, StoredRun};
use crate::{document, document_with_head, esc};

/// The author label the day's world is published under (a stable content-address input; the daily
/// world is anonymous-authored on the no-cheat board).
const DAY_AUTHOR: &str = "the-descent";

// ═══════════════════════════════════════════════════════════════════════════════
// THE DAY — beacon-then-offline, the SAME resolution the Discord bot runs.
// ═══════════════════════════════════════════════════════════════════════════════

/// **The live daily beacon this web process fetched + BLS-verified**, armed at boot and re-armed
/// hourly by [`arm_todays_descent_day`](crate::arm_todays_descent_day). It is exactly the beacon
/// whose seed that same arm publishes for [`dreggnet_catalog::DescentDayBinding::Live`], so the
/// relic-minting catalog open (`/offerings/descent`) and the board / play / leaderboard here
/// resolve the *identical* day — never one beacon-bound world scoring another.
///
/// This is the web analogue of the Discord bot's `LIVE_BEACON` cell (populated by its reveal
/// cron); [`todays_day`] resolves the beacon day from it exactly as the bot's `resolve_todays_day`
/// does, and `/descent/play`'s `day.json` hands its raw drand `(round, signature)` pair to the tab
/// so the browser opens `NativeDescentWorld.fromBeacon` and runs the BLS check itself (fail-closed).
static WEB_LIVE_BEACON: OnceLock<Mutex<Option<(u64, DailyBeacon)>>> = OnceLock::new();

fn web_live_beacon_cell() -> &'static Mutex<Option<(u64, DailyBeacon)>> {
    WEB_LIVE_BEACON.get_or_init(|| Mutex::new(None))
}

/// **Cache the verified live beacon for `utc_day`** — called by
/// [`arm_todays_descent_day`](crate::arm_todays_descent_day) with the very beacon it fetched and
/// published to the catalog. The beacon handed here is already BLS-verified (a fetched live round
/// that failed the pairing check is a hard error and never reaches this point; a transport outage
/// yields the pinned published round, itself a real re-verified reveal). [`todays_day`] re-checks
/// via [`descent_day::beacon_day`] before serving it, so a cache that somehow no longer verifies
/// degrades to the offline day rather than seeding a run.
pub fn set_web_live_beacon(utc_day: u64, beacon: DailyBeacon) {
    *web_live_beacon_cell()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner()) = Some((utc_day, beacon));
}

/// Today's cached verified beacon, if this process has armed one for the current UTC day. The raw
/// `(round, signature)` pair `/descent/play`'s `day.json` hands the tab.
pub(crate) fn todays_live_beacon() -> Option<DailyBeacon> {
    let today = procgen_dregg::beacon::current_utc_day();
    web_live_beacon_cell()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .as_ref()
        .and_then(|(day, beacon)| (*day == today).then(|| beacon.clone()))
}

/// **Today's descent day** — the one seed selection the live `/descent` surfaces (board / play /
/// today / share) share, resolved exactly as the Discord bot's `resolve_todays_day` resolves it:
///
/// * this process armed today's verified beacon ([`set_web_live_beacon`], from
///   [`arm_todays_descent_day`](crate::arm_todays_descent_day)) ⇒ that beacon's day
///   ([`descent_day::beacon_day`], keyed `d{utc}-r{round}`). `beacon_day` derives the seed through
///   [`DailyBeacon::seed`], which runs the BLS pairing check FIRST, so a cached beacon that no
///   longer verifies falls through to the offline day rather than seeding a run;
/// * no beacon armed yet (fresh boot before the first fetch, or no egress on the very first arm)
///   ⇒ the OFFLINE, date-derived day ([`descent_day::todays_offline_day`], keyed `d{utc}-off`) —
///   a real daily rotation, honestly not a fresh reveal.
///
/// Both branches use `procgen_dregg::descent_day`, the SAME helper the Discord bot resolves through
/// (its live cache is fed by its reveal cron, this one by the hourly arm), so when both processes
/// are online they play the byte-identical beacon world, and when neither has a round they play the
/// byte-identical offline world. A Discord-originated submit that names `d{utc}-r{round}` is
/// re-derived here by [`resolve_submitted_day`] fetching + BLS-verifying that exact round, so the
/// two still meet in one world across the process boundary.
pub fn todays_day() -> DescentDay {
    let today = procgen_dregg::beacon::current_utc_day();
    if let Some(beacon) = todays_live_beacon() {
        if let Ok(resolved) = descent_day::beacon_day(today, &beacon) {
            return resolved;
        }
    }
    descent_day::todays_offline_day()
}

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
    /// var→snapshot-index map. A snapshot is the sixteen fixed registers followed
    /// by compiled ext keys in ascending order; canonical u64 keys are never used
    /// directly as platform-sized Vec indices.
    var_slots: BTreeMap<String, usize>,
    /// The run ids recorded for this day (candidates for the board — each re-verified on render).
    run_ids: Vec<String>,
    /// Exact Lean-native browser records submitted for this day. These are a SEPARATE ruleset from
    /// `run_ids`: native verb/argument events cannot honestly be translated into procgen passage
    /// indices, so the page ranks crowned native records in their own replay-compatible lane.
    native_run_ids: Vec<String>,
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

/// An untrusted browser-native record retained only so every read can replay it again. The wire is
/// exactly the one emitted by wasm `NativeDescentWorld.recordJson()`; no state/receipt field is
/// installed directly.
struct NativeRun {
    id: String,
    day_key: String,
    record: PortableRecord,
}

/// The size bound `POST /descent/native/submit` enforces on the record itself — pinned to the
/// SAME [`MAX_PORTABLE_RECORD_BYTES`] the browser's import/export contract carries, because it is
/// now literally the same constant rather than a number copied between two crates.
const MAX_NATIVE_PORTABLE_BYTES: usize = MAX_PORTABLE_RECORD_BYTES;
// HTTP wraps the portable object in `{day,record}`. Leave bounded room for that envelope while the
// record itself remains pinned to the wire's 8 MiB import/export contract above.
const MAX_NATIVE_SUBMIT_BODY_BYTES: usize = MAX_NATIVE_PORTABLE_BYTES + 64 * 1024;

#[derive(Clone, Debug)]
struct VerifiedNativeRun {
    actor: String,
    turns: usize,
    root_hex: String,
    completion: Option<PortableCompletion>,
    /// **The shaft as the REPLAY left it** — the post-state of the last event the server's own
    /// exact re-execution landed, not the submitted one. `None` only for a record with no events
    /// (a run that never moved, and so has no story to paint).
    final_state: Option<PortableSim>,
    /// The day's DRAWN map (relic homes + per-floor guardian vitality), resolved from the record's
    /// committed day-seed. Carried because the run-card's guardian column would otherwise read
    /// day 0's shipped vitalities on every beacon day.
    world: DayWorld,
}

impl VerifiedNativeRun {
    fn crowned(&self) -> bool {
        self.completion.as_ref().is_some_and(|c| c.crowned)
    }

    fn banked_relics(&self) -> usize {
        self.completion
            .as_ref()
            .map_or(0, |c| c.banked_relics.len())
    }

    /// The run's whole story, ready to paint. `None` when the tape is empty.
    fn story(&self) -> Option<RunStory> {
        self.final_state
            .clone()
            .map(|state| RunStory::new(state, self.world, self.crowned()))
    }
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
    native_runs: HashMap<String, NativeRun>,
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
                .map(|c| {
                    let ext_keys = c.ext_keys();
                    c.var_slots
                        .into_iter()
                        .filter_map(|(name, key)| {
                            let index = if key
                                < u64::try_from(spween_dregg::STATE_SLOTS)
                                    .expect("the fixed state-slot count fits u64")
                            {
                                usize::try_from(key)
                                    .expect("a bounded state-slot key fits this target")
                            } else {
                                spween_dregg::STATE_SLOTS + ext_keys.binary_search(&key).ok()?
                            };
                            Some((name, index))
                        })
                        .collect()
                })
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
                    native_run_ids: Vec::new(),
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
            let stable_moves: Vec<u64> = moves
                .iter()
                .copied()
                .map(|choice| {
                    u64::try_from(choice).expect("an admitted move index fits the stable wire")
                })
                .collect();
            let moves_json =
                serde_json::to_string(&stable_moves).unwrap_or_else(|_| "[]".to_string());
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

    /// Verify and retain one browser-native record without pretending it is a procgen move tape.
    /// The submitted receipt/state/root envelope is replayed from its native verbs through a fresh
    /// [`NativeDescentOffering`] and must match byte-for-byte. The record's normalized native seed
    /// must also be the one committed by `day_key`. Exact terminal records receive a share card;
    /// only a crowned settlement ranks in the board's separate native lane.
    fn submit_native_record(
        &self,
        day_key: &str,
        record: PortableRecord,
    ) -> Result<(String, VerifiedNativeRun, bool), String> {
        let (expected_seed, stored_day) = {
            let inner = self.inner.lock().unwrap();
            let day = inner
                .days
                .get(day_key)
                .ok_or_else(|| format!("no such day: {day_key}"))?;
            (
                native_seed_for_committed_day(&day.seed),
                StoredDay {
                    key: day_key.to_string(),
                    seed_hex: hex32(day.seed.as_bytes()),
                },
            )
        };
        let verified = verify_native_record(expected_seed, &record)?;
        if verified.completion.is_none() {
            return Err(
                "native record is an exact prefix but has no terminal flee settlement".to_string(),
            );
        }
        let run_id = derive_native_run_id(day_key, &record);
        let record_json = serde_json::to_string(&record)
            .map_err(|error| format!("native record serialization: {error}"))?;

        {
            let mut inner = self.inner.lock().unwrap();
            let day = inner
                .days
                .get_mut(day_key)
                .ok_or_else(|| format!("no such day: {day_key}"))?;
            if !day.native_run_ids.iter().any(|id| id == &run_id) {
                day.native_run_ids.push(run_id.clone());
            }
            inner
                .native_runs
                .entry(run_id.clone())
                .or_insert(NativeRun {
                    id: run_id.clone(),
                    day_key: day_key.to_string(),
                    record,
                });
        }
        let durable = if let Some(store) = &self.store {
            // `persist_day` is idempotent-by-key (`INSERT OR IGNORE` for sqlite). Confirm the row
            // names THIS seed before claiming durability: a pre-existing conflicting key must not
            // yield `durable:true` for a record that boot would later reject against the old seed.
            let exact_day_persisted = store.persist_day(&stored_day).is_ok()
                && store
                    .list_days()
                    .is_ok_and(|days| days.iter().any(|day| day == &stored_day));
            exact_day_persisted
                && store
                    .persist_native_run(&StoredNativeRun {
                        run_id: run_id.clone(),
                        day_key: day_key.to_string(),
                        record_json,
                    })
                    .is_ok()
        } else {
            false
        };
        Ok((run_id, verified, durable))
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

    /// **Anchor a crowned native run's terminal settlement on the devnet node** — the native-lane
    /// analogue of [`settle_run`](Self::settle_run), so the flagship's in-tab runs anchor exactly
    /// as the procgen lane does. Fail-closed and non-vacuous, with the SAME routing:
    /// * `Local` (the default): a no-op — `Ok(None)`, nothing leaves the process (the committed
    ///   tests + node-free demo are byte-identical);
    /// * `Federation` (a `DREGG_NODE_URL` node): submit the run's terminal journal head — the
    ///   un-retconnable tip of the actor-bound hash chain the admitted record attests
    ///   (`completion.root_hex`) — under the day's stable scene topic, AND confirm it landed on the
    ///   node's finalized log (`GET /api/receipts`). `Ok(Some(Landed))` iff the node accepted +
    ///   finalized it; `Err` on a rejected / unreachable / non-landing submit.
    ///
    /// This settles only a run ALREADY admitted to the native lane — one that passed
    /// [`submit_native_record`](Self::submit_native_record)'s exact-replay gate — and only a
    /// **crowned** one (the settlement that ranks). A forged / non-crowned / prefix run is refused
    /// before it can rank, so it never reaches here; the node is never touched for a cheat, exactly
    /// as the procgen lane.
    ///
    /// [`submit_native_record`]: Self::submit_native_record
    pub fn settle_native_run(
        &self,
        day_key: &str,
        run_id: &str,
    ) -> Result<Option<Landed>, NodeError> {
        let submitted = {
            let inner = self.inner.lock().unwrap();
            let run = inner.native_runs.get(run_id).ok_or_else(|| {
                NodeError::Rejected(format!("no such native run to settle: {run_id}"))
            })?;
            let day = inner.days.get(day_key).ok_or_else(|| {
                NodeError::Rejected(format!("no such day to settle against: {day_key}"))
            })?;
            let completion = run.record.completion.as_ref().ok_or_else(|| {
                NodeError::Rejected(format!(
                    "native run {run_id} has no terminal settlement to anchor"
                ))
            })?;
            if !completion.crowned {
                return Err(NodeError::Rejected(format!(
                    "native run {run_id} did not crown — only a crowned exit ranks and anchors"
                )));
            }
            // The commitment = the terminal journal head (the tip of the actor-bound hash chain
            // the admitted record attests). The topic = the day's stable scene id, shared with the
            // procgen lane; the commitments never collide (a native root ≠ a procgen turn-hash).
            let commitment = decode_hex32(&completion.root_hex).ok_or_else(|| {
                NodeError::Rejected(format!(
                    "native run {run_id} settlement root is not 32 hex-encoded bytes"
                ))
            })?;
            let domain = day.scene.meta.id.to_string();
            SubmittedTurn::new(domain, commitment)
        };
        // Same fail-closed routing as the procgen lane: Local = Ok(None) no-op; Federation =
        // submit + confirm landed on the node's finalized log.
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
            let Ok(stable_moves) = serde_json::from_str::<Vec<u64>>(&r.moves_json) else {
                continue;
            };
            let Ok(moves) = stable_move_indices(&stable_moves) else {
                continue;
            };
            // A drop here is silent-and-correct: the row no longer re-verifies.
            let _ = self
                .reverify_and_ingest(&r.day_key, &r.run_id, &r.player, r.level, r.class, &moves);
        }
        for r in store.list_native_runs().unwrap_or_default() {
            if r.record_json.len() > MAX_NATIVE_PORTABLE_BYTES {
                continue;
            }
            let Ok(record) = serde_json::from_str::<PortableRecord>(&r.record_json) else {
                continue;
            };
            // The row key is content-derived. A DB edit cannot rename one authentic record into a
            // different share artifact, and exact replay below drops any changed envelope.
            if derive_native_run_id(&r.day_key, &record) != r.run_id {
                continue;
            }
            let _ = self.submit_native_record(&r.day_key, record);
        }
    }

    /// The key of an already-open day whose world is drawn from `seed`, if any.
    ///
    /// **The day key is a LABEL; the SEED is the world.** Two keys naming the same seed (the demo's
    /// `"today"` and the bot's `d{utc_day}-off`) are the SAME board, and a submitted run must land
    /// on the one that is already open rather than splitting the day in two.
    pub fn day_key_for_seed(&self, seed: &CommittedSeed) -> Option<String> {
        let inner = self.inner.lock().unwrap();
        inner
            .days
            .values()
            .find(|d| d.seed.as_bytes() == seed.as_bytes())
            .map(|d| d.key.clone())
    }

    /// **Ensure a day's world is open and return the key it lives under.** If some day is already
    /// open on this seed, that key is returned untouched (see [`day_key_for_seed`](Self::day_key_for_seed));
    /// otherwise the day is opened under `preferred_key`. Idempotent.
    ///
    /// THE DAY-ROLL: opening a *canonical* day key for the CURRENT UTC day also makes it the default
    /// board. So the first run submitted after UTC midnight rolls a long-lived deployment onto the
    /// new world instead of leaving `/descent` serving yesterday's forever. A hand-picked key (a
    /// fixture day, the demo's `"today"`) is never promoted this way.
    pub fn ensure_day(&self, preferred_key: &str, seed: CommittedSeed) -> String {
        if let Some(existing) = self.day_key_for_seed(&seed) {
            return existing;
        }
        self.open_day(preferred_key, seed);
        if let Some((utc_day, _)) = descent_day::parse_day_key(preferred_key) {
            if utc_day == procgen_dregg::beacon::current_utc_day() {
                self.set_today(preferred_key);
            }
        }
        preferred_key.to_string()
    }

    /// **Open today's world if this process has none, and return the day to render by default.**
    ///
    /// Called on the dayless board render and the dayless submit. Two rules, both deliberate:
    ///
    /// * **No day designated at all** ⇒ open today's ([`todays_day`]) and designate it, so a bare
    ///   deployment serves a real, current world instead of an empty board.
    /// * **A day already designated** ⇒ keep it, UNLESS it is a canonical `d{utc_day}-…` key for a
    ///   PAST day (then roll). A caller-designated day — a test fixture, the demo's `"today"` — is
    ///   never yanked out from under the caller that opened it; the roll for those comes from
    ///   [`ensure_day`] promoting the new canonical day when the first run of it is submitted.
    pub fn ensure_today(&self) -> String {
        let day = todays_day();
        if let Some(cur) = self.today() {
            match descent_day::parse_day_key(&cur) {
                // A canonical key for a past day — stale, roll to today's world.
                Some((utc_day, _)) if utc_day < day.utc_day => {}
                _ => return cur,
            }
        }
        let key = self.ensure_day(&day.key, day.seed);
        self.set_today(&key);
        key
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

    /// Whether a day is open under exactly this key.
    pub fn has_day(&self, key: &str) -> bool {
        self.inner.lock().unwrap().days.contains_key(key)
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

/// The browser passes the committed seed's first little-endian word into
/// `NativeDescentOffering::open`; the Offering alone owns normalization to `1..=251`.
fn native_seed_for_committed_day(seed: &CommittedSeed) -> u8 {
    let bytes = seed.as_bytes();
    let input = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    ((u64::from(input) % 251) + 1) as u8
}

/// **Admit one untrusted browser record**, through the SAME exact-replay gate the browser's own
/// import runs ([`replay_portable_record`]). The wire type and the gate both live in
/// `dreggnet_offerings::native_descent_wire`; this function adds only the one thing that is a
/// property of THIS surface rather than of the record — that the record's normalized seed is the
/// seed the requested day commits to.
///
/// Everything else is the shared gate: format/version, seed range, event bound, malformed banked
/// notes BY NAME, deployment on the record's OWN run day-seed (a beacon-bound run only re-derives
/// on the day-seed it names), exact command re-drive, `Offering::verify`, the re-minted-note
/// comparison, and the byte-for-byte envelope comparison.
fn verify_native_record(
    expected_seed: u8,
    expected: &PortableRecord,
) -> Result<VerifiedNativeRun, String> {
    // The day binding, checked BEFORE the (more expensive) replay: a record from another day's
    // world is refused here rather than being re-executed and then failing anonymously.
    if expected.seed == 0 || expected.seed > 251 {
        return Err("native Descent seed is outside 1..=251".to_string());
    }
    if expected.seed != expected_seed {
        return Err(format!(
            "native record seed {} does not belong to this day (expected {expected_seed})",
            expected.seed
        ));
    }

    // The day's DRAWN dungeon, off the record's own committed provenance root — the same reduction
    // `Descent::deploy_on_day` makes. The run-card's guardian column reads this, so a beacon day's
    // card shows that day's vitalities instead of day 0's shipped ones.
    let world = day_world(day_index(&expected.day_seed()?));

    let (_offering, session) = replay_portable_record(expected)?;
    let actual = PortableRecord::from_record(&session.export_record());
    // The REPLAYED final state (the last landed event's post-state), never the submitted one.
    let final_state = actual.events.last().map(|event| event.post.clone());
    Ok(VerifiedNativeRun {
        actor: actual
            .actor
            .clone()
            .unwrap_or_else(|| "unclaimed".to_string()),
        turns: actual.events.len(),
        root_hex: actual.root_hex,
        completion: actual.completion,
        final_state,
        world,
    })
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

fn native_run_share_path(run_id: &str) -> String {
    format!("/descent/native/run/{run_id}")
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
/// - `POST /descent/native/submit` + `GET /descent/native/run/{id}` — the compatibility lane for
///   the Lean-native browser's full portable record. It uses exact native replay, never procgen
///   move-tape coercion; crowned records rank separately and every accepted record gets a card.
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
        .route(
            "/descent/native/submit",
            post(post_native_submit).layer(DefaultBodyLimit::max(MAX_NATIVE_SUBMIT_BODY_BYTES)),
        )
        .route("/descent/native/run/{id}", get(get_native_run_card))
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
    pub moves: Vec<u64>,
}

#[derive(Debug, Clone, Deserialize)]
struct SubmitNativeRun {
    #[serde(default)]
    day: Option<String>,
    record: serde_json::Value,
}

/// Receive the exact `NativeDescentWorld.recordJson()` envelope. This endpoint exists because its
/// `{turn,arg}` verbs, native executor receipts, and custody semantics are not the older procgen
/// board's `Vec<choice_index>` language. It replays through the actual native Offering, compares
/// every portable field, binds the normalized seed to the requested day, and only then retains a
/// shareable artifact. Exact prefixes remain local; exact non-crowned exits are shareable but do
/// not rank.
async fn post_native_submit(
    State(state): State<Arc<DescentState>>,
    Json(body): Json<SubmitNativeRun>,
) -> (StatusCode, Json<serde_json::Value>) {
    let encoded_len = serde_json::to_vec(&body.record)
        .map(|bytes| bytes.len())
        .unwrap_or(usize::MAX);
    if encoded_len > MAX_NATIVE_PORTABLE_BYTES {
        return native_submit_refused(format!(
            "native Descent record exceeds the {MAX_NATIVE_PORTABLE_BYTES} byte bound"
        ));
    }
    let record: PortableRecord = match serde_json::from_value(body.record) {
        Ok(record) => record,
        Err(error) => return native_submit_refused(format!("native record JSON: {error}")),
    };
    let day = match resolve_submitted_day(&state, body.day).await {
        Ok(day) => day,
        Err(error) => return native_submit_refused(error),
    };
    match state.submit_native_record(&day, record) {
        Ok((run_id, verified, durable)) => {
            let ranked = verified.crowned();
            let banked_relics = verified.banked_relics();
            // The verified notes themselves — the first wire consumer. These are the replayed
            // (re-minted) notes, not echoes of the submission.
            let banked_notes = verified
                .completion
                .as_ref()
                .map(|completion| completion.banked_notes.clone())
                .unwrap_or_default();
            let detail = if ranked {
                "exact native replay accepted; crowned settlement ranks in the native lane"
            } else {
                "exact native replay accepted; shareable, but only a crowned settlement ranks"
            };
            let mut resp = serde_json::json!({
                "verified": true,
                "ranked": ranked,
                "kind": "exact-native-replay",
                "run_id": run_id,
                "share": native_run_share_path(&run_id),
                "day": day,
                "actor": verified.actor,
                "turns": verified.turns,
                "root": verified.root_hex,
                "banked_relics": banked_relics,
                "banked_notes": banked_notes,
                "durable": durable,
                "detail": detail,
            });
            // AUTO-ANCHOR THE NATIVE LANE. A crowned run already ranks in-process; if a devnet is
            // opted in (`DREGG_NODE_URL`), ALSO anchor its terminal journal head on the running
            // node's ledger — the native-lane analogue of the procgen `post_submit` settle, so the
            // flagship's in-tab runs reach the node on completion instead of never anchoring. Local
            // mode is a no-op (`Ok(None)`), so this branch is byte-identical for the demo/tests.
            // Only a crowned run (the one that ranks) is anchored; a non-crowned settlement is
            // shareable but never touches the node.
            if ranked && state.settles_to_a_node() {
                let st = state.clone();
                let day2 = day.clone();
                let rid = run_id.clone();
                let settled =
                    tokio::task::spawn_blocking(move || st.settle_native_run(&day2, &rid))
                        .await
                        .unwrap_or_else(|e| {
                            Err(NodeError::Transport(format!(
                                "native settle task join: {e}"
                            )))
                        });
                match settled {
                    Ok(Some(landed)) => {
                        resp["settled"] = serde_json::json!(true);
                        resp["node_turn_hash"] = serde_json::json!(hex32(&landed.node_turn_hash));
                        resp["detail"] = serde_json::json!(
                            "exact native replay accepted; crowned, ranked, AND anchored on the devnet node's ledger"
                        );
                    }
                    Ok(None) => {}
                    Err(e) => {
                        // The run still ranks in-process; the on-chain anchor FAILED. A node was
                        // configured, so silence would read as success — surface it honestly:
                        // flip `settled` false, carry the error, and REWRITE `detail` so it no
                        // longer claims the anchor landed, exactly as the procgen lane does.
                        crate::metrics::inc_anchor_failure();
                        resp["settled"] = serde_json::json!(false);
                        resp["settle_error"] = serde_json::json!(e.to_string());
                        resp["detail"] = serde_json::json!(
                            "exact native replay accepted; crowned + ranked in-process, but the \
                             devnet-node anchor FAILED (settled:false) — the run is NOT on the node ledger"
                        );
                    }
                }
            }
            (StatusCode::OK, Json(resp))
        }
        Err(error) => native_submit_refused(error),
    }
}

fn native_submit_refused(error: String) -> (StatusCode, Json<serde_json::Value>) {
    (
        StatusCode::BAD_REQUEST,
        Json(serde_json::json!({
            "verified": false,
            "ranked": false,
            "kind": "exact-native-replay",
            "error": error,
            "detail": "native re-execution rejected the record; nothing was retained",
        })),
    )
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
    let day = match resolve_submitted_day(&state, body.day.clone()).await {
        Ok(d) => d,
        Err(why) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(serde_json::json!({
                    "ranked": false,
                    "error": why,
                    "detail": "the submitted day could not be re-derived to a world — nothing ingested",
                })),
            );
        }
    };
    let moves = match stable_move_indices(&body.moves) {
        Ok(moves) => moves,
        Err(why) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(serde_json::json!({
                    "ranked": false,
                    "error": why,
                    "detail": "the stable move tape could not address this executor — nothing ingested",
                })),
            );
        }
    };
    let run_id = derive_run_id(&day, &body.player, &moves);
    match state.submit_run(&day, &run_id, &body.player, body.level, body.class, &moves) {
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

/// **Resolve the day a submitted run claims, RE-DERIVING its world rather than trusting the key.**
///
/// This is the receiving half of the cross-process weld. The order is:
///
/// 1. **No `day`** ⇒ today's world ([`DescentState::ensure_today`]). (The bot always sends one now;
///    this is the browser/manual-submit path, and it also rolls the day at UTC midnight.)
/// 2. **A day already open under that exact key** ⇒ use it. This keeps hand-picked keys (the demo's
///    `"today"`, a test's fixture day) working exactly as before.
/// 3. **A key [`procgen_dregg::descent_day`] can re-derive** ⇒ re-derive the SEED here — purely for
///    an offline day, and for a live-beacon day by FETCHING that round and running the BLS pairing
///    check — then land the run on whatever board already holds that world (or open it). The key is
///    never believed: it only names a world this process derives for itself, and the helper refuses a
///    malformed key, an out-of-window day, and an off-schedule round BEFORE any network touch, so
///    this endpoint cannot be steered into fetching arbitrary rounds.
/// 4. **Anything else** ⇒ refused (`Err`), fail-closed — never silently re-executed against a
///    different day's world, which is exactly the failure this whole weld exists to remove.
async fn resolve_submitted_day(
    state: &Arc<DescentState>,
    requested: Option<String>,
) -> Result<String, String> {
    let Some(key) = requested else {
        return Ok(state.ensure_today());
    };
    if state.has_day(&key) {
        return Ok(key);
    }
    // Re-derive the world the key names. The offline half is pure; only a live-beacon key touches
    // the network, and it is fetched + BLS-verified off the async worker.
    let today = procgen_dregg::beacon::current_utc_day();
    let k = key.clone();
    let resolved = tokio::task::spawn_blocking(move || {
        descent_day::resolve_day_key(
            &procgen_dregg::beacon::HttpRoundFetch,
            procgen_dregg::beacon::DRAND_API_BASE,
            &k,
            today,
        )
        .map_err(|e| e.to_string())
    })
    .await
    .map_err(|e| format!("day resolution task join: {e}"))??;
    Ok(state.ensure_day(&resolved.key, resolved.seed))
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

fn stable_move_indices(moves: &[u64]) -> Result<Vec<usize>, String> {
    moves
        .iter()
        .copied()
        .enumerate()
        .map(|(turn, choice)| {
            usize::try_from(choice).map_err(|_| {
                format!("move {turn} choice index {choice} exceeds this executor target")
            })
        })
        .collect()
}

fn derive_native_run_id(day: &str, record: &PortableRecord) -> String {
    let record_json = serde_json::to_vec(record).unwrap_or_default();
    let mut h = blake3::Hasher::new();
    h.update(b"dregg.native-descent.share.v1");
    h.update(
        &u64::try_from(day.len())
            .expect("the bounded day key fits u64")
            .to_be_bytes(),
    );
    h.update(day.as_bytes());
    h.update(&record_json);
    let hex: String = h.finalize().as_bytes()[..16]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    format!("native-{hex}")
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
    // Open today's world if the process has not yet (and roll it at UTC midnight) — but only when no
    // explicit `?day=` was asked for, so a link to a past day still renders that day.
    if q.day.is_none() {
        state.ensure_today();
    }
    // ONE link-store scan for the whole render (never per row), on the account-id join key.
    let resolver = RootResolver::load();

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
            // The completion is built over the run's OWN stored player label — the resolution below
            // is a display/rank concern and must never move what is verified.
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
                // CROSS-PLATFORM IDENTITY: which HUMAN this row belongs to. A Discord-you and a
                // Telegram-you (different custodial keys, one linked root) resolve to the same
                // account id and merge below; an unlinked player resolves to its own label, so an
                // un-linked board is byte-identical to before.
                human: resolver.resolve(&run.player),
                turns,
                depth,
            });
        }
    }
    // Rank by verified turns-to-win (lower first); stable for ties.
    rows.sort_by(|a, b| a.turns.cmp(&b.turns).then_with(|| a.player.cmp(&b.player)));
    merge_per_human(&mut rows);

    // Native browser records speak a different game language. Re-verify their complete portable
    // envelope on this render and rank only crowned settlements, in a visibly separate lane.
    let native_seed = native_seed_for_committed_day(&day.seed);
    let mut native_rows = Vec::new();
    for rid in &day.native_run_ids {
        let Some(run) = inner.native_runs.get(rid) else {
            continue;
        };
        if run.day_key != day.key {
            continue;
        }
        if let Ok(verified) = verify_native_record(native_seed, &run.record) {
            if verified.crowned() {
                let relics = verified.banked_relics();
                native_rows.push(NativeRow {
                    run_id: run.id.clone(),
                    actor: verified.actor,
                    turns: verified.turns,
                    relics,
                });
            }
        }
    }
    native_rows.sort_by(|a, b| a.turns.cmp(&b.turns).then_with(|| a.actor.cmp(&b.actor)));

    Html(leaderboard_page(day, &rows, &native_rows))
}

/// **One row per HUMAN, their best verified run.** `rows` must already be ranked (best first), so
/// the first sighting of a human is the run that ranks for them.
///
/// Resolving identities WITHOUT this step only RELABELS — two platforms of one person still occupy
/// two board rows, which is exactly the defect the review caught on the crown board. An unlinked
/// player's `human` is their own label, so a board with no links is untouched.
fn merge_per_human(rows: &mut Vec<Row>) {
    let mut seen: Vec<String> = Vec::new();
    rows.retain(|r| {
        if seen.iter().any(|h| h == &r.human) {
            return false;
        }
        seen.push(r.human.clone());
        true
    });
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

/// `GET /descent/native/run/{id}` replays the browser's native record again. This is the shareable
/// compatibility artifact; it does not rely on the verdict computed during submission.
async fn get_native_run_card(
    State(state): State<Arc<DescentState>>,
    Path(id): Path<String>,
) -> Html<String> {
    let (record, day_key, title, seed, expected_seed) = {
        let inner = state.inner.lock().unwrap();
        let Some(run) = inner.native_runs.get(&id) else {
            return Html(run_missing(&id));
        };
        let Some(day) = inner.days.get(&run.day_key) else {
            return Html(run_missing(&id));
        };
        (
            run.record.clone(),
            day.key.clone(),
            day.day.title.clone(),
            seed_tag(&day.seed),
            native_seed_for_committed_day(&day.seed),
        )
    };
    let replay = verify_native_record(expected_seed, &record);
    Html(native_run_card_page(
        &id, &day_key, &title, &seed, &record, replay,
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
    /// The run's own stored player label (what is displayed, and what the completion verified under).
    player: String,
    /// WHICH HUMAN this row belongs to — the resolved account id when the player's custodial key is
    /// linked, else the player label itself. Used to merge a person's platforms into one row; never
    /// part of any verification.
    human: String,
    turns: usize,
    depth: u64,
}

/// One crowned browser-native run, verified under the Lean-native ruleset on this render.
struct NativeRow {
    run_id: String,
    actor: String,
    turns: usize,
    relics: usize,
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
fn leaderboard_page(day: &Day, rows: &[Row], native_rows: &[NativeRow]) -> String {
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
    let mut native_table = String::new();
    native_table.push_str(
        "<section class=\"deos-section\"><p class=\"eyebrow\">Lean-native browser ruleset</p>\
         <h2>Crowned native runs</h2><p class=\"prose\">These records are not converted into the \
         procgen choice tape above. Each row replays its native <span class=\"mono\">delve / \
         smite / loot / unlock / flee</span> events and exact receipt, state, and journal-root \
         envelope. Only a crowned settlement ranks.</p>",
    );
    if native_rows.is_empty() {
        native_table.push_str(
            "<p class=\"tag-muted\">No crowned native browser run has re-verified for this day.</p>",
        );
    } else {
        native_table.push_str(
            "<div class=\"table-wrap\"><table class=\"board\"><thead><tr><th>#</th>\
             <th>browser actor</th><th>landed turns</th><th>relics</th><th>proof</th></tr></thead><tbody>",
        );
        for (index, row) in native_rows.iter().enumerate() {
            native_table.push_str(&format!(
                "<tr><td class=\"rank\">{rank}</td><td class=\"player\">{actor}</td>\
                 <td class=\"num\">{turns}</td><td class=\"num\">{relics}</td>\
                 <td><a href=\"{href}\">verify native record \
                 <span class=\"arr\" aria-hidden=\"true\">→</span></a></td></tr>",
                rank = index + 1,
                actor = esc(&row.actor),
                turns = row.turns,
                relics = row.relics,
                href = esc(&native_run_share_path(&row.run_id)),
            ));
        }
        native_table.push_str("</tbody></table></div>");
    }
    native_table.push_str("</section>");
    let body = format!(
        "<main class=\"session\">\
         <div class=\"page-head\" style=\"padding-top:var(--s4)\">\
         <p class=\"eyebrow\">Re-verified on this request</p>\
         <h1>The Descent — {title}</h1>\
         <p class=\"deck\">The no-cheat leaderboard. Procgen rows are re-executed from passage \
         choices and required to reach the hoard. Browser-native rows are replayed under their \
         distinct Lean-native verb/receipt rules and required to crown. A forged or unfinished run \
         appears in neither lane — exclusion comes from re-verification, not a stored flag.</p></div>\
         <div class=\"kv\">\
         <div><p class=\"k\">Day</p><p class=\"v mono\">{key}</p></div>\
         <div><p class=\"k\">Seed</p><p class=\"v mono\">{seed}</p></div>\
         <div><p class=\"k\">Warden HP</p><p class=\"v mono\">{whp}</p></div>\
         <div><p class=\"k\">Depth</p><p class=\"v mono\">{rooms}</p></div>\
         </div>\
         {table}\
         {native_table}\
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
        native_table = native_table,
    );
    document(
        &format!("The Descent — {} · leaderboard", day.day.title),
        "descent-board",
        &body,
    )
}

/// **The shareable run-card.** The artifact a stranger meets first, so it is built story-first: the
/// shaft as the run left it (what came out, what was left behind, how deep they got, what was still
/// in the pack when the light died), THEN the independent-verification verdict that makes the story
/// worth believing, THEN the material a verifier wants.
///
/// The picture is [`crate::descent_card`] — the live play surface's own board, painted from the
/// REPLAYED final state, so what a player watched happen is what a stranger sees. The
/// `<head>` carries the OpenGraph/Twitter tags, because this page's whole job is to be posted.
#[allow(clippy::too_many_arguments)]
fn native_run_card_page(
    run_id: &str,
    day_key: &str,
    title: &str,
    seed: &str,
    record: &PortableRecord,
    replay: Result<VerifiedNativeRun, String>,
) -> String {
    let story = replay.as_ref().ok().and_then(VerifiedNativeRun::story);
    let (verified, actor, turns, root, banked, notes, crowned, detail) = match replay {
        Ok(run) => {
            let banked = run.banked_relics();
            let crowned = run.crowned();
            // The minted owned-notes, re-derived by THIS replay (trusted only because the
            // envelope re-verified): tier + the note's content-addressed asset id.
            let notes = run
                .completion
                .as_ref()
                .filter(|completion| !completion.banked_notes.is_empty())
                .map(|completion| {
                    completion
                        .banked_notes
                        .iter()
                        .map(|note| {
                            format!(
                                "{} {}",
                                Rarity::from_tag(note.rarity).map_or("?", |rarity| rarity.label()),
                                &note.asset_id_hex[..12.min(note.asset_id_hex.len())],
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(" · ")
                })
                .unwrap_or_else(|| "none minted".to_string());
            (
                true,
                run.actor,
                run.turns,
                run.root_hex,
                banked,
                notes,
                crowned,
                "The server deployed a fresh Lean-native world, replayed every verb through the native \
                 Offering, and reproduced the complete receipt, post-state, checkpoint, completion, \
                 and journal-root envelope byte-for-byte."
                    .to_string(),
            )
        }
        Err(error) => (
            false,
            record
                .actor
                .clone()
                .unwrap_or_else(|| "unclaimed".to_string()),
            record.events.len(),
            record.root_hex.clone(),
            0,
            "unverifiable".to_string(),
            false,
            format!("Exact native replay refused this record: {error}"),
        ),
    };
    let verdict = if verified { "PASS" } else { "FAIL" };
    let verdict_class = if verified { "pass" } else { "fail" };
    let outcome = if !verified {
        "unverifiable"
    } else if crowned {
        "CROWNED — Crown of the Deep banked in the terminal exit"
    } else if record.completion.is_some() {
        "SETTLED — exact exit, not crowned and not ranked"
    } else {
        "IN PROGRESS — exact prefix, not ranked"
    };

    // ── THE STORY, FIRST. A stranger meets the run before they meet the ruleset. ──
    let (card, share_text, headline) = match &story {
        Some(story) => (
            story.html(&actor, day_key, seed),
            story.text_card(&actor, day_key),
            story.headline(),
        ),
        None if verified => (
            String::new(),
            String::new(),
            "An exact record with no landed turns — this run never moved.".to_string(),
        ),
        None => (
            String::new(),
            String::new(),
            "This record does not re-execute. Nothing it claims is shown as fact.".to_string(),
        ),
    };
    // The copyable form: the SAME board every text channel paints (`coordgrid_text`), so a run
    // pasted into a chat is the run, not a screenshot of one.
    let share_block = if share_text.is_empty() {
        String::new()
    } else {
        format!(
            "<details class=\"rc-text\"><summary>Copy this run as text \
             (the same board Discord and Telegram paint)</summary><pre>{}</pre></details>",
            esc(&share_text),
        )
    };

    // ── THE SOCIAL PREVIEW. Meta tags are head-only, and this page exists to be posted. ──
    let og_title = match (&story, verified) {
        (Some(story), true) => format!("{} — {actor}'s descent", story.ending().word()),
        (_, true) => format!("{actor}'s descent"),
        (_, false) => format!("FAIL — {actor}'s record does not re-execute"),
    };
    let head = format!(
        "{card_style}<meta name=\"description\" content=\"{desc}\">\
         <meta property=\"og:type\" content=\"article\">\
         <meta property=\"og:site_name\" content=\"DreggNet\">\
         <meta property=\"og:title\" content=\"{og_title}\">\
         <meta property=\"og:description\" content=\"{desc}\">\
         <meta name=\"twitter:card\" content=\"summary\">\
         <meta name=\"twitter:title\" content=\"{og_title}\">\
         <meta name=\"twitter:description\" content=\"{desc}\">",
        card_style = CARD_STYLE,
        og_title = esc(&og_title),
        desc = esc(&format!(
            "{headline} Re-verified by re-execution the moment you open this page."
        )),
    );

    let body = format!(
        "<div class=\"crumb\"><a href=\"/descent/leaderboard?day={day}\">← leaderboard</a>\
         <span class=\"sep\">·</span><strong>{actor}</strong><span class=\"sep\">·</span>\
         <span class=\"sid\">native record {id}</span></div><main class=\"session\">\
         <div class=\"page-head\" style=\"padding-top:var(--s4)\"><p class=\"eyebrow\">\
         Lean-native compatibility artifact · {title}</p><h1>{actor}'s descent</h1>\
         <p class=\"deck\">{headline}</p></div>\
         {card}\
         <section class=\"verdict {class}\"><h2><span class=\"stamp\">{verdict}</span>\
         Independent verification — {verdict}</h2><p>{detail}</p></section>\
         <div class=\"kv\"><div><p class=\"k\">Outcome</p><p class=\"v\">{outcome}</p></div>\
         <div><p class=\"k\">Landed turns</p><p class=\"v mono\">{turns}</p></div>\
         <div><p class=\"k\">Banked relics</p><p class=\"v mono\">{banked}</p></div>\
         <div><p class=\"k\">Minted notes</p><p class=\"v mono\">{notes}</p></div>\
         <div><p class=\"k\">Journal root</p><p class=\"v mono\">{root}</p></div></div>\
         {share_block}\
         <p class=\"prose\" style=\"margin-top:var(--s5)\">\
         <a class=\"btn btn-primary\" href=\"/descent/play\">Take your own light down \
         <span class=\"arr\" aria-hidden=\"true\">→</span></a></p>\
         </main>",
        day = esc(day_key),
        actor = esc(&actor),
        id = esc(run_id),
        title = esc(title),
        headline = esc(&headline),
        card = card,
        class = verdict_class,
        verdict = verdict,
        detail = esc(&detail),
        outcome = outcome,
        turns = turns,
        banked = banked,
        notes = esc(&notes),
        root = esc(&root),
        share_block = share_block,
    );
    document_with_head(
        &format!("The Descent — {actor} · native proof"),
        "descent-run",
        &head,
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
        "descent-board",
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
    document("The Descent — leaderboard", "descent-board", &body)
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
    document("The Descent — unknown run", "descent-board", &body)
}

#[cfg(test)]
mod funnel_tests {
    use super::*;

    fn row(run_id: &str, player: &str, human: &str, turns: usize) -> Row {
        Row {
            run_id: run_id.into(),
            player: player.into(),
            human: human.into(),
            turns,
            depth: 1,
        }
    }

    /// A person's two platforms MERGE to one row keeping their best run — the board shows humans,
    /// not custodial keys. NON-VACUOUS: a genuinely different human keeps their own row.
    #[test]
    fn a_humans_two_platforms_become_one_row() {
        let mut rows = vec![
            row("r1", "discord-key", "acct-ada", 7),
            row("r2", "telegram-key", "acct-ada", 9), // the SAME human, a worse run
            row("r3", "someone-else", "acct-bo", 8),
        ];
        merge_per_human(&mut rows);
        assert_eq!(rows.len(), 2, "one row per human, not one per platform");
        assert_eq!(
            rows[0].run_id, "r1",
            "the human's BEST run is the one that ranks"
        );
        assert_eq!(
            rows[1].human, "acct-bo",
            "a different human keeps their row"
        );
    }

    /// An UNLINKED board is byte-identical to before resolution: every player is their own human, so
    /// nothing merges.
    #[test]
    fn an_unlinked_board_is_unchanged_by_the_merge() {
        let mut rows = vec![
            row("r1", "alice", "alice", 5),
            row("r2", "bob", "bob", 6),
            row("r3", "carol", "carol", 7),
        ];
        merge_per_human(&mut rows);
        assert_eq!(rows.len(), 3);
    }

    /// THE CROSS-PROCESS WELD: the day key this process publishes re-derives to the SAME seed a
    /// receiver computes for itself — the property the share link stands on.
    #[test]
    fn todays_day_key_re_derives_to_todays_seed() {
        let day = todays_day();
        let (utc_day, source) = descent_day::parse_day_key(&day.key).expect("the key parses");
        assert_eq!(utc_day, day.utc_day);
        assert_eq!(source, descent_day::DaySource::OfflineDate);
        assert_eq!(
            descent_day::offline_date_seed(utc_day).as_bytes(),
            day.seed.as_bytes(),
            "a receiver re-derives the identical world from the key alone"
        );
    }

    /// A day key naming a world ALREADY OPEN under another label lands on THAT board — the demo's
    /// `"today"` and the bot's `d{utc_day}-off` are one day, never two split boards.
    #[test]
    fn a_second_key_for_the_same_world_does_not_split_the_board() {
        let day = todays_day();
        let state = DescentState::new();
        state.open_day("today", day.seed);
        assert_eq!(
            state.ensure_day(&day.key, day.seed),
            "today",
            "the canonical key resolves onto the already-open board"
        );
        assert!(!state.has_day(&day.key), "no second board was opened");
        // A genuinely DIFFERENT world does open its own board.
        let other = descent_day::offline_day(day.utc_day + 5);
        assert_eq!(state.ensure_day(&other.key, other.seed), other.key);
        assert!(state.has_day(&other.key));
    }

    /// `ensure_today` never yanks a CALLER-designated day (a fixture / the demo alias) out from
    /// under it, but does open + designate one when the process has none.
    #[test]
    fn ensure_today_respects_a_pinned_day_and_seeds_an_empty_one() {
        let pinned = DescentState::new();
        pinned.open_day("a-fixture-day", procgen_dregg::daily_seed(&[9; 32]));
        assert_eq!(pinned.ensure_today(), "a-fixture-day");

        let empty = DescentState::new();
        let key = empty.ensure_today();
        assert_eq!(
            key,
            todays_day().key,
            "a bare process serves today's real world"
        );
        assert_eq!(empty.today().as_deref(), Some(key.as_str()));
    }
}
