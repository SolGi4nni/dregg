//! `/descent` — THE DESCENT played LIVE in Discord: today's beacon-seeded, permadeath
//! procgen roguelite over the committed [`DailyDescentOffering`].
//!
//! This is the flagship's earning core (docs/GAME-STRATEGY.md Phase 1) made playable in the bot.
//! It drives the SAME committed
//! [`dreggnet_offerings::daily_descent::DailyDescentOffering`] the crate's own driven test does —
//! nothing is re-implemented here; the bot is a live *surface* over the real substrate:
//!
//! 1. **Today's beacon-seeded world.** [`resolve_todays_beacon`] pins a REAL published drand
//!    `quicknet` round (the committed beacon path); the day's [`CommittedSeed`] is
//!    [`DailyBeacon::seed`] (a BLS-pairing-verified fold of the round output). Everyone who plays
//!    "today" gets the byte-identical dungeon; a different day's verified round gives a different
//!    world (proven at the scene level in the tests). *A live drand HTTP fetch that advances the
//!    round each real day is the NAMED seam* — here we play the pinned round as today's beacon.
//! 2. **A permadeath run on the real executor.** Each move is one cap-bounded turn the verified
//!    executor admits (a real [`TurnReceipt`]); a blow you could not survive is REFUSED
//!    (`FieldGte(hp,1)`); a reckless line falls into a committed DEFEAT passage — a run can be
//!    genuinely LOST, and (hardcore) the persistent character PERISHES, `WriteOnce`-final.
//! 3. **A persistent, carrying character.** Level / class / earned XP / a hardcore death carry
//!    across days through the durable [`crate::character_store::SqliteCharacterStore`], keyed by
//!    the player's derived dregg identity (the SAME identity `/dungeon` attributes ballots to).
//! 4. **A no-cheat leaderboard.** A WON run publishes today's world as a
//!    [`ugc_dregg::Universe`] and submits a [`ugc_dregg::Completion`] the board accepts ONLY if it
//!    re-executes to the WIN on a stranger's re-execution — a forged / lost / incomplete run is
//!    refused ([`Registry::submit`]).
//!
//! ## What is live here vs the named seams
//! - **Live:** the daily offering, permadeath, the carrying character, the no-cheat board (now
//!   DURABLE — see below), and the paid/free AI narrator (the same `$DREGG` credit gate `/dungeon`
//!   uses, [`crate::pay`]).
//! - **Durable board.** The leaderboard is no longer in-process only: it is backed by a
//!   [`DescentBoardStore`] (a sqlite impl wired at boot). Only the reproducible PUBLIC input is
//!   persisted — a day-world's committed beacon SEED (never a cached world) and a winning run's
//!   MOVE SEQUENCE + player + claimed turns (never a trusted receipt blob). On boot [`load_board`]
//!   regenerates each day-world from its seed and REPLAYS every completion through the real no-cheat
//!   gate, so a tampered row (a losing move line, a lied turn count, a mismatched seed) cannot
//!   resurrect a cheat. A verified win survives restart and still ranks. The character store owns
//!   the meta-currency (echoes/boon) durably; the [`OfferingHost`] SESSIONS remain in-process (a
//!   named seam — see [`crate::commands::offering`]).
//! - **Named seams:** the live drand HTTP fetch (advancing the round each real UTC day — here a
//!   pinned round); the midnight cron / `RevealReactor` auto-reveal (here a manual `/descent play`
//!   or scheduled trigger); the web spectator page (a separate lane).
//!
//! [`OfferingHost`]: dreggnet_offerings::host::OfferingHost
//!
//! ## Threading
//! A live [`DailyRun`] holds `spween_dregg::WorldCell`s whose installed `Mandate`s are not `Send`
//! (the same reason [`crate::commands::offering::Store`] pins its sessions to a dedicated thread).
//! So the per-player runs + the in-process leaderboard live on ONE dedicated
//! [`DescentStore`] thread, driven by `Send` jobs that return `Send` snapshots; the async narrator
//! network call happens OFF that thread (on the Discord worker), exactly as `/dungeon` narrates
//! after a round resolves.

use std::collections::HashMap;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{SyncSender, sync_channel};

use serenity::all::{
    ButtonStyle, CommandDataOptionValue, CommandInteraction, CommandOptionType,
    ComponentInteraction, Context, CreateActionRow, CreateButton, CreateCommand,
    CreateCommandOption, CreateEmbed, CreateEmbedFooter, CreateInteractionResponse,
    CreateInteractionResponseMessage,
};

use dreggnet_offerings::character::CharacterStore;
use dreggnet_offerings::daily_descent::{
    DailyDescentOffering, DailyRun, GATE_FALL, GATE_HEAL, GATE_MEASURED, GATE_PRESS, GATE_RECKLESS,
    daily_scene,
};
use dreggnet_offerings::{DreggIdentity, OfferingError, Outcome};
use dungeon_on_dregg::progression::{MAGE, ROGUE, WARRIOR};
use procgen_dregg::CommittedSeed;
use procgen_dregg::beacon::DailyBeacon;
use ugc_dregg::{Completion, Registry, Universe, UniverseId, record_playthrough};

use crate::BotState;
use crate::commands::ack;
use crate::commands::offering::identity_of;

/// The Descent brand colour (a deep permadeath crimson-violet, distinct from `/dungeon`'s teal).
const DESCENT_COLOR: u32 = 0x9D174D;
/// The honest tagline that footers every Descent surface.
const TAGLINE: &str = "beacon-seeded · permadeath · the chain remembers · no-cheat board";
/// The leaderboard author label today's world is published under.
const BOARD_AUTHOR: &str = "the-descent";

// ─────────────────────────────────────────────────────────────────────────────
// Today's beacon — the committed drand `quicknet` round (the pinned reveal path).
// ─────────────────────────────────────────────────────────────────────────────

/// A REAL, PUBLISHED drand `quicknet` round (round 1_000_000) — the same vector `dregg-dice`'s
/// interop test and `dreggnet-offerings`' driven test pin. Here it is "today's beacon": a verified
/// reveal whose BLS pairing check holds, so the day's seed is a pure, un-grindable function of it.
const DRAND_QUICKNET_ROUND: u64 = 1_000_000;
/// The round's threshold-BLS signature (the reveal `DailyBeacon::verify` re-checks by pairing).
const DRAND_QUICKNET_SIG_HEX: &str = "83ad29e4c409f9470fc2ef02f90214df49e02b441a1a241a82d622d9f608ef98fd8b11a029f1bee9d9e83b45088abe72";

/// The LIVE daily beacon the reveal cron ([`crate::reveal_cron`]) fetched + BLS-verified for the
/// current UTC day. When present (and matching today), every `/descent` surface serves it — so The
/// Descent's daily seed is the real, unpredictable-until-revealed live drand round. When absent
/// (offline, before today's reveal fires, or under test) the pinned published round stands in. BOTH
/// are BLS-verified reveals, so the day is always genuinely beacon-seeded.
static LIVE_BEACON: OnceLock<std::sync::Mutex<Option<(u64, DailyBeacon)>>> = OnceLock::new();

fn live_beacon_cell() -> &'static std::sync::Mutex<Option<(u64, DailyBeacon)>> {
    LIVE_BEACON.get_or_init(|| std::sync::Mutex::new(None))
}

/// **Cache the reveal cron's verified live beacon for `utc_day`.** Called by [`crate::reveal_cron`]
/// after a live drand fetch verifies today's round; [`resolve_todays_beacon`] then serves it for
/// the current UTC day. First-write-per-day is fine (idempotent — the same day's round is stable).
pub fn set_live_beacon(utc_day: u64, beacon: DailyBeacon) {
    *live_beacon_cell().lock().expect("live beacon lock") = Some((utc_day, beacon));
}

/// Which beacon [`resolve_todays_beacon`] serves — surfaced honestly in every `/descent` footer
/// (mirrors the [`NarratorKind`] idiom): the reveal cron's LIVE round for the current UTC day, or
/// the pinned published fallback. Both are genuine BLS-verified reveals, but the fallback is NOT
/// today's — every fallback day plays the SAME dungeon, and the surface must say so.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BeaconStatus {
    /// The reveal cron fetched + verified today's live drand round; the day is genuinely fresh.
    Live {
        /// The live round number being served.
        round: u64,
    },
    /// The pinned published round stands in (offline, before today's reveal fires, or under
    /// test) — the daily world repeats until the reveal cron reaches drand.
    PinnedFallback,
}

impl BeaconStatus {
    /// The honest footer fragment (mirrors `NarratorKind::label`).
    fn label(self) -> String {
        match self {
            BeaconStatus::Live { round } => format!("beacon: live round {round}"),
            BeaconStatus::PinnedFallback => "beacon: PINNED fallback (not today's) — daily \
                 world repeats until the reveal cron reaches drand"
                .to_string(),
        }
    }
}

/// The pure resolution core: the cached live beacon when it is `today`'s, else the pinned
/// published fallback — labeled with WHICH one was served. [`resolve_todays_beacon`] wraps this
/// over the live cache; the tests drive both polarities directly.
fn resolve_beacon_for(
    today: u64,
    cached: Option<(u64, DailyBeacon)>,
) -> (DailyBeacon, BeaconStatus) {
    if let Some((day, beacon)) = cached {
        if day == today {
            let round = beacon.round;
            return (beacon, BeaconStatus::Live { round });
        }
    }
    (
        DailyBeacon::quicknet(
            DRAND_QUICKNET_ROUND,
            hex::decode(DRAND_QUICKNET_SIG_HEX).expect("the pinned drand signature decodes"),
        ),
        BeaconStatus::PinnedFallback,
    )
}

/// **Resolve today's daily beacon** — the LIVE drand `quicknet` reveal when the reveal cron has
/// fetched + verified today's round, else the pinned published round (the offline/test fallback).
///
/// The live drand HTTP fetch that advances the round each real UTC day is now WIRED
/// ([`procgen_dregg::beacon::fetch_todays_beacon`], driven by [`crate::reveal_cron`], which caches
/// the verified round via [`set_live_beacon`]). Absent a live reveal, the committed pinned round is
/// served: a genuine reveal whose pairing check holds, so `/descent` always plays a real
/// beacon-verified day (a forged reveal is refused by [`DailyDescentOffering::open`]) — but NOT a
/// fresh one. Serving the fallback warns once per UTC day; the surface footer carries the
/// staleness to players ([`todays_beacon_status`]).
pub fn resolve_todays_beacon() -> DailyBeacon {
    let today = procgen_dregg::beacon::current_utc_day();
    let cached = live_beacon_cell().lock().expect("live beacon lock").clone();
    let (beacon, status) = resolve_beacon_for(today, cached);
    if status == BeaconStatus::PinnedFallback {
        // Once per UTC day, put the staleness in the operator's log too (the footer already
        // carries it to players).
        static LAST_FALLBACK_WARN_DAY: AtomicU64 = AtomicU64::new(u64::MAX);
        if LAST_FALLBACK_WARN_DAY.swap(today, Ordering::Relaxed) != today {
            tracing::warn!(
                utc_day = today,
                pinned_round = DRAND_QUICKNET_ROUND,
                "/descent is serving the PINNED fallback beacon (not today's live drand round) — \
                 the daily world repeats until the reveal cron reaches drand"
            );
        }
    }
    beacon
}

/// Today's [`BeaconStatus`] — the live-vs-pinned verdict every `/descent` footer reports beside
/// the narrator kind.
pub fn todays_beacon_status() -> BeaconStatus {
    let today = procgen_dregg::beacon::current_utc_day();
    let cached = live_beacon_cell().lock().expect("live beacon lock").clone();
    resolve_beacon_for(today, cached).1
}

// ─────────────────────────────────────────────────────────────────────────────
// Scene-source parsing — the day's world is emitted as spween DSL text on
// `run.day().source`; the bot reads the current room's prose + its ordered choice
// labels straight out of it (the SAME order `WorldCell::apply_choice` indexes with),
// so the buttons carry the exact theme-flavoured labels the executor gates.
// ─────────────────────────────────────────────────────────────────────────────

/// The lines of the `=== <room>` section of a spween scene source (between its header and the
/// next `===`), so the room's prose + choices can be read out.
fn section_lines<'a>(source: &'a str, room: &str) -> Vec<&'a str> {
    let header = format!("=== {room}");
    let mut out = Vec::new();
    let mut in_section = false;
    for line in source.lines() {
        if let Some(rest) = line.strip_prefix("=== ") {
            // A `=== name` header: enter iff it is ours, else leave.
            in_section = rest.trim() == room;
            continue;
        }
        // A bare `===` also closes the section.
        if line.trim_start().starts_with("===") {
            in_section = false;
            continue;
        }
        if in_section {
            out.push(line);
        }
    }
    let _ = header;
    out
}

/// The ordered choice labels of `room` — each `* [Label] { cond }` line's `[Label]`, in scene
/// order (so the position IS the choice index the executor checks the gate case against).
fn room_choices(source: &str, room: &str) -> Vec<String> {
    section_lines(source, room)
        .iter()
        .filter_map(|line| {
            let t = line.trim_start();
            let t = t.strip_prefix("* ")?;
            let start = t.find('[')?;
            let end = t.find(']')?;
            if end > start {
                Some(t[start + 1..end].to_string())
            } else {
                None
            }
        })
        .collect()
}

/// The room's scripted prose (the descriptive lines of the section — not the `~` effects, the
/// `*` choices, or the choice bodies). This is the scene's own description a scripted narrator uses.
fn room_prose(source: &str, room: &str) -> String {
    let mut parts: Vec<String> = Vec::new();
    for line in section_lines(source, room) {
        let t = line.trim();
        if t.is_empty() || t.starts_with('~') || t.starts_with('*') || t.starts_with("->") {
            continue;
        }
        // Choice bodies are indented (`  ~ ...` / `  -> ...`) and already filtered; description
        // prose is a flush-left paragraph.
        if line.starts_with(' ') {
            continue;
        }
        parts.push(t.to_string());
    }
    parts.join(" ")
}

// ─────────────────────────────────────────────────────────────────────────────
// The per-room ballot the bot renders — the ordered labels + a cap-eligibility
// decoration (the executor is the sole referee; a `!enabled` press still surfaces
// as a real refusal, so this is guidance, not the gate).
// ─────────────────────────────────────────────────────────────────────────────

/// One rendered move: the label, the choice index it applies, and whether its scene condition
/// currently holds (a decoration — the executor still refuses an ineligible move on `advance`).
#[derive(Clone, Debug, PartialEq, Eq)]
struct MoveOption {
    label: String,
    index: usize,
    enabled: bool,
}

/// Whether choice `index` in `room` is currently eligible, read off the committed cell vars. Only
/// the `gate` room is gated; every other room's moves are ungated (always `true`).
fn choice_enabled(run: &DailyRun, room: &str, index: usize) -> bool {
    if room != "gate" {
        return true;
    }
    let hp = run.read_var("hp");
    let warden_hp = run.read_var("warden_hp");
    let heals_used = run.read_var("heals_used");
    match index {
        GATE_MEASURED => hp >= 16,
        GATE_RECKLESS => hp >= 31,
        GATE_HEAL => heals_used == 0,
        GATE_PRESS => warden_hp == 0,
        GATE_FALL => hp <= 20,
        _ => true,
    }
}

/// The rendered ballot for the run's current room — the scene labels (in index order) with the
/// eligibility decoration. Empty when the run has ended.
fn ballot(run: &DailyRun) -> Vec<MoveOption> {
    let Some(room) = run.current_room() else {
        return Vec::new();
    };
    room_choices(&run.day().source, &room)
        .into_iter()
        .enumerate()
        .map(|(index, label)| MoveOption {
            enabled: choice_enabled(run, &room, index),
            label,
            index,
        })
        .collect()
}

// ─────────────────────────────────────────────────────────────────────────────
// A `Send` snapshot of a run for rendering — taken on the store thread, rendered
// (and narrated) on the Discord worker. Carries only plain data.
// ─────────────────────────────────────────────────────────────────────────────

/// How a piece of narration was produced — surfaced honestly in the footer (mirrors `/dungeon`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NarratorKind {
    /// A real hosted model (AWS Bedrock) narrated it — a PAID run that spent one $DREGG credit.
    Bedrock,
    /// A real local `gemma2:2b` (ollama) narrated it (the free tier).
    Gemma,
    /// ollama was unreachable; the scene's own scripted prose stood in (the free tier).
    Scripted,
}

impl NarratorKind {
    fn label(self) -> &'static str {
        match self {
            NarratorKind::Bedrock => "narrator: bedrock (real AI · paid with a $DREGG credit)",
            NarratorKind::Gemma => "narrator: gemma2:2b (free)",
            NarratorKind::Scripted => "narrator: scripted (free)",
        }
    }
}

/// A `Send` render snapshot of a live run — the day + the committed vitals + the current ballot.
#[derive(Clone, Debug)]
struct RunView {
    day_title: String,
    /// The current room name (`None` once the run has ended).
    room: Option<String>,
    /// The current room's scripted prose (the narrator's fallback + the italic under-line).
    prose: String,
    hp: u64,
    warden_hp: u64,
    depth: u64,
    gold: u64,
    heals_used: u64,
    turns: usize,
    ended: bool,
    won: bool,
    dead: bool,
    level: u64,
    xp: u64,
    class_name: String,
    options: Vec<MoveOption>,
}

impl RunView {
    /// Snapshot a live run for rendering (on the store thread — plain data only).
    fn of(run: &DailyRun) -> RunView {
        let room = run.current_room();
        let prose = room
            .as_ref()
            .map(|r| room_prose(&run.day().source, r))
            .unwrap_or_default();
        let sheet = run.character().sheet();
        RunView {
            day_title: run.day().title.clone(),
            room,
            prose,
            hp: run.read_var("hp"),
            warden_hp: run.read_var("warden_hp"),
            depth: run.depth(),
            gold: run.read_var("gold"),
            heals_used: run.read_var("heals_used"),
            turns: run.turns(),
            ended: run.is_ended(),
            won: run.is_won(),
            dead: run.is_dead(),
            level: run.character().level(),
            xp: run.character().xp(),
            class_name: sheet.class_name().to_string(),
            options: ballot(run),
        }
    }
}

/// The `Send` result of advancing a run by one move — for the async render + narration layer.
#[derive(Clone, Debug)]
enum MoveResult {
    /// No run is open for this player.
    NoRun,
    /// The run already ended; nothing to advance.
    AlreadyEnded(RunView),
    /// The executor REFUSED the move (a gate bit): nothing committed, the room unchanged.
    Refused { why: String, view: RunView },
    /// The move landed a real committed turn; the post-move snapshot + any board outcome.
    Landed {
        view: RunView,
        /// The board rank this WON run earned (`None` for a continuing / lost run).
        rank: Option<usize>,
        /// An honest one-line note about the board outcome (submitted / refused / lost).
        board_note: String,
    },
}

// ─────────────────────────────────────────────────────────────────────────────
// The generic core — driven by BOTH the live store thread (over the durable
// `SqliteCharacterStore`) and the tests (over an `InMemoryCharacterStore`). Nothing
// here touches Discord; it is the daily offering + the no-cheat board, welded.
// ─────────────────────────────────────────────────────────────────────────────

/// **Open today's run for `who`** and PUBLISH today's world to `board` (idempotent) so a later WIN
/// can be submitted. Verifies the beacon (a forged reveal yields no run — fail-closed), draws the
/// day's world, deploys the run, and loads the player's persistent character.
fn open_core<S: CharacterStore>(
    off: &DailyDescentOffering<S>,
    board: &mut Registry,
    who: DreggIdentity,
    beacon: &DailyBeacon,
    class: Option<u64>,
) -> Result<(DailyRun, UniverseId), OfferingError> {
    let run = off.open(who, beacon)?;
    // A new player may pick a class (frozen `WriteOnce`; a re-class / a dead character is refused —
    // ignored, the run still opens).
    if let Some(class_id) = class {
        let _ = off.choose_class(&run, class_id);
    }
    let universe = run
        .day()
        .universe(BOARD_AUTHOR)
        .map_err(|e| OfferingError::Deploy(format!("could not publish today's world: {e:?}")))?;
    let uid = board.publish(universe);
    Ok((run, uid))
}

/// **Advance the run by one move; settle a terminal outcome.** Applies `choice` as one real turn;
/// EVERY landed move SAVES the character (persisting earned XP / a hardcore death mid-run, so a
/// restart never rewinds a sheet), and a landed move that ENDED the run additionally, iff the run
/// WON, submits a [`ugc_dregg::Completion`] to the no-cheat `board`.
fn advance_core<S: CharacterStore>(
    off: &mut DailyDescentOffering<S>,
    run: &mut DailyRun,
    board: &mut Registry,
    universe_id: UniverseId,
    player: &str,
    choice: usize,
) -> MoveResult {
    if run.is_ended() {
        return MoveResult::AlreadyEnded(RunView::of(run));
    }
    match off.advance(run, choice) {
        Outcome::Refused(why) => MoveResult::Refused {
            why,
            view: RunView::of(run),
        },
        Outcome::Landed { ended, .. } => {
            // Persist the character after EVERY landed move, not only the terminal one — so a
            // mid-run bot restart cannot roll the character back to its pre-run sheet. (Before
            // this, progress saved only on the terminal move, so a doomed hardcore run could
            // dodge its death by simply waiting out a redeploy — backlog #34. The run session
            // itself is still in-process, a named seam; what is durable is the character.)
            off.save(run);
            let mut rank = None;
            let mut board_note = String::new();
            if ended {
                if run.is_won() {
                    match off.completion(run, BOARD_AUTHOR, player) {
                        Ok(completion) => {
                            debug_assert_eq!(completion.universe, universe_id);
                            match board.submit(completion) {
                                Ok(accepted) => {
                                    rank = Some(accepted.rank);
                                    board_note = format!(
                                        "Ranked #{} on today's no-cheat board ({} verified turns).",
                                        accepted.rank, accepted.turns
                                    );
                                }
                                Err(e) => {
                                    board_note = format!("The board refused the run: {e}");
                                }
                            }
                        }
                        Err(e) => board_note = format!("Could not build a completion: {e:?}"),
                    }
                } else {
                    board_note =
                        "The descent ended without the hoard — it does not rank.".to_string();
                }
            }
            MoveResult::Landed {
                view: RunView::of(run),
                rank,
                board_note,
            }
        }
    }
}

/// A `Send` view of today's leaderboard — the ranked entries (player + turns-to-win), plus a
/// per-entry `(rank, completion_id_hex)` handle the **Re-verify #N** buttons carry (backlog
/// Tier-2 #9: the claimed replay-verification becomes a press anyone can make).
#[derive(Clone, Debug)]
struct BoardView {
    day_title: String,
    entries: Vec<(usize, String, usize)>,
    /// `(rank, completion_id hex)` per ranked entry, in rank order — the re-verify handles.
    reverify: Vec<(usize, String)>,
}

/// The current no-cheat leaderboard for today's world.
fn board_core(board: &Registry, universe_id: UniverseId, day_title: &str) -> BoardView {
    let ranked = board.leaderboard(universe_id);
    let entries = ranked
        .iter()
        .enumerate()
        .map(|(i, e)| (i + 1, short_player(&e.player), e.turns))
        .collect();
    let reverify = ranked
        .iter()
        .enumerate()
        .map(|(i, e)| (i + 1, hex32(&e.completion_id)))
        .collect();
    BoardView {
        day_title: day_title.to_string(),
        entries,
        reverify,
    }
}

/// A short, legible player tag (the first 12 chars of the identity/label).
fn short_player(p: &str) -> String {
    p.chars().take(12).collect()
}

// ═════════════════════════════════════════════════════════════════════════════
// The DURABLE board store — persists the PUBLIC, REPRODUCIBLE input of the day's
// no-cheat board (a day-world's committed beacon SEED + a winning run's MOVE
// SEQUENCE), and replays it through the real no-cheat gate on boot. A tampered row
// cannot survive. Mirrors `commands::gallery`'s `GalleryStore` exactly; the sqlite
// impl is `crate::descent_board_store::SqliteDescentBoardStore`, tests here use
// `InMemoryDescentBoardStore`.
// ═════════════════════════════════════════════════════════════════════════════

/// A day-universe's **reproducible descriptor** as persisted — its committed beacon SEED (the
/// world is regenerated byte-for-byte from it) + the board author label. Content-addressed:
/// `id_hex` is the address the world hashed to at publish time, and reconstruction recomputes it —
/// a mismatch (a tampered seed) means the row is dropped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StoredDescentUniverse {
    /// The day-universe content address (hex) at publish time — the row PK + tamper check.
    pub id_hex: String,
    /// The board author label the day's world is published under.
    pub author: String,
    /// Hex of the 32-byte committed beacon seed `daily_scene` regenerates the whole world from.
    pub seed_hex: String,
}

impl StoredDescentUniverse {
    /// The persistable descriptor for the day a run is playing — the day's content-addressed id +
    /// author + the committed seed the world is drawn from. `None` if the day's world does not
    /// author (which would already have blocked the run from opening).
    fn of(run: &DailyRun) -> Option<StoredDescentUniverse> {
        let day = run.day();
        let universe = day.universe(BOARD_AUTHOR).ok()?;
        Some(StoredDescentUniverse {
            id_hex: id_hex(&universe.id()),
            author: BOARD_AUTHOR.to_string(),
            seed_hex: hex32(day.seed.as_bytes()),
        })
    }
}

/// A submitted winning run as persisted — the **player + the move sequence** (choice indices) +
/// the claimed turns. The receipt chain is deliberately NOT stored: it is deterministically
/// re-recorded from the moves on a fresh identically-seeded world and re-verified at load. A
/// tampered row is only ever a different move sequence or a lied result — both re-checked by replay.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StoredDescentCompletion {
    /// Idempotency PK — `blake3(universe_id_hex ‖ player ‖ moves_json)`.
    pub key_hex: String,
    /// The full day-universe content address (hex) this completion is for.
    pub universe_id_hex: String,
    /// The player's (short) name/tag.
    pub player: String,
    /// The move sequence (choice indices), as a JSON array.
    pub moves_json: String,
    /// The claimed turns-to-win, stored INDEPENDENTLY of the moves, so a tampered value (≠ the
    /// verified move count) is rejected on reload.
    pub claimed_turns: i64,
}

impl StoredDescentCompletion {
    /// Build a persistable completion from a resolved (full-hex) universe id, the player, and the
    /// recorded move sequence. `claimed_turns` is bound to the true move count.
    fn new(universe_id_hex: &str, player: &str, moves: &[usize]) -> StoredDescentCompletion {
        let moves_json = serde_json::to_string(moves).unwrap_or_else(|_| "[]".to_string());
        let mut h = blake3::Hasher::new();
        h.update(universe_id_hex.as_bytes());
        h.update(&[0]);
        h.update(player.as_bytes());
        h.update(&[0]);
        h.update(moves_json.as_bytes());
        StoredDescentCompletion {
            key_hex: hex32(h.finalize().as_bytes()),
            universe_id_hex: universe_id_hex.to_string(),
            player: player.to_string(),
            moves_json,
            claimed_turns: moves.len() as i64,
        }
    }

    /// The persistable completion for a WON run — its day-universe id + the recorded choice-index
    /// sequence (read straight off the committed playthrough). `None` if the day fails to author.
    fn of(run: &DailyRun, player: &str) -> Option<StoredDescentCompletion> {
        let universe = run.day().universe(BOARD_AUTHOR).ok()?;
        let universe_id_hex = id_hex(&universe.id());
        let moves: Vec<usize> = run
            .playthrough()
            .steps
            .iter()
            .map(|s| s.choice_index)
            .collect();
        Some(StoredDescentCompletion::new(
            &universe_id_hex,
            player,
            &moves,
        ))
    }
}

/// The durable /descent board store. Sync (`&self`) so the dedicated board thread can be backed by
/// it without an async boundary — exactly the shape of `commands::gallery`'s `GalleryStore`. The
/// main loop supplies a sqlite impl; tests use [`InMemoryDescentBoardStore`]. Persist methods MUST
/// be idempotent by PK, so a double write / a double load never duplicates a universe or an entry.
pub trait DescentBoardStore {
    /// Persist a published day-universe (idempotent by `id_hex`).
    fn persist_universe(&self, u: &StoredDescentUniverse) -> Result<(), String>;
    /// Persist an accepted board completion (idempotent by `key_hex`).
    fn persist_completion(&self, c: &StoredDescentCompletion) -> Result<(), String>;
    /// Every persisted day-universe.
    fn list_universes(&self) -> Result<Vec<StoredDescentUniverse>, String>;
    /// Every persisted board completion.
    fn list_completions(&self) -> Result<Vec<StoredDescentCompletion>, String>;
}

/// A thread-safe in-memory [`DescentBoardStore`] for tests and single-process runs. Idempotent by
/// PK, matching the sqlite impl's `INSERT OR IGNORE`.
#[derive(Default)]
pub struct InMemoryDescentBoardStore {
    inner: std::sync::Mutex<InMemBoard>,
}

#[derive(Default)]
struct InMemBoard {
    universes: Vec<StoredDescentUniverse>,
    completions: Vec<StoredDescentCompletion>,
}

impl InMemoryDescentBoardStore {
    /// A fresh empty store.
    pub fn new() -> InMemoryDescentBoardStore {
        InMemoryDescentBoardStore::default()
    }

    /// TEST HOOK: mutate the raw persisted rows, to simulate a **tampered database**. The reload
    /// path must reject whatever this produces if it no longer re-verifies.
    #[cfg(test)]
    fn tamper(
        &self,
        f: impl FnOnce(&mut Vec<StoredDescentUniverse>, &mut Vec<StoredDescentCompletion>),
    ) {
        let mut g = self.inner.lock().expect("descent board store lock");
        let InMemBoard {
            universes,
            completions,
        } = &mut *g;
        f(universes, completions);
    }
}

impl DescentBoardStore for InMemoryDescentBoardStore {
    fn persist_universe(&self, u: &StoredDescentUniverse) -> Result<(), String> {
        let mut g = self.inner.lock().expect("descent board store lock");
        if !g.universes.iter().any(|x| x.id_hex == u.id_hex) {
            g.universes.push(u.clone());
        }
        Ok(())
    }
    fn persist_completion(&self, c: &StoredDescentCompletion) -> Result<(), String> {
        let mut g = self.inner.lock().expect("descent board store lock");
        if !g.completions.iter().any(|x| x.key_hex == c.key_hex) {
            g.completions.push(c.clone());
        }
        Ok(())
    }
    fn list_universes(&self) -> Result<Vec<StoredDescentUniverse>, String> {
        Ok(self
            .inner
            .lock()
            .expect("descent board store lock")
            .universes
            .clone())
    }
    fn list_completions(&self) -> Result<Vec<StoredDescentCompletion>, String> {
        Ok(self
            .inner
            .lock()
            .expect("descent board store lock")
            .completions
            .clone())
    }
}

/// **BOOT REPLAY + RE-VERIFY.** Build the live board [`Registry`] from the durable store:
/// regenerate every persisted day-world byte-for-byte from its committed seed (dropping any whose
/// recomputed content address no longer matches its stored id — the tamper check), then REPLAY
/// every persisted completion through [`Registry::submit`] — the no-cheat gate, which re-executes
/// the moves on a fresh identically-seeded world and only ranks a completion that provably reaches
/// the win with a truthful turn count. Every rejection is silent-and-correct: a tampered seed, a
/// losing move line, a refused move, or a lied `claimed_turns` never lands on the board.
pub fn load_board(store: &dyn DescentBoardStore) -> Registry {
    let mut reg = Registry::new();
    for su in store.list_universes().unwrap_or_default() {
        if let Some(u) = reconstruct_universe(&su) {
            reg.publish(u);
        }
    }
    for sc in store.list_completions().unwrap_or_default() {
        replay_completion(&mut reg, &sc);
    }
    reg
}

/// Regenerate a day-world from its persisted committed seed, through the SAME public
/// [`daily_scene`] → [`DailyDescent::universe`](dreggnet_offerings::daily_descent::DailyDescent::universe)
/// path the live offering uses. Returns `None` if the seed is malformed, the world does not author,
/// or — the tooth — the recomputed content address no longer matches the stored `id_hex` (a tampered
/// seed). Such a row is simply dropped.
pub(crate) fn reconstruct_universe(su: &StoredDescentUniverse) -> Option<Universe> {
    let seed = CommittedSeed::from_bytes(decode_hex32(&su.seed_hex)?);
    let day = daily_scene(&seed);
    let universe = day.universe(&su.author).ok()?;
    (id_hex(&universe.id()) == su.id_hex).then_some(universe)
}

/// Replay one persisted completion through the no-cheat gate. Re-records the moves on a fresh
/// identically-seeded day-world and submits with the STORED `claimed_turns`; any rejection (unknown
/// universe, a refused move, `DidNotWin`, `ResultMismatch`, `FailedVerification`) is dropped — it
/// does not land on the board.
fn replay_completion(reg: &mut Registry, sc: &StoredDescentCompletion) {
    let Some(id) = find_board_universe(reg, &sc.universe_id_hex) else {
        return;
    };
    let Some(universe) = reg.universe(id).cloned() else {
        return;
    };
    let Ok(moves) = serde_json::from_str::<Vec<usize>>(&sc.moves_json) else {
        return;
    };
    // A tampered (illegal) move sequence is refused by the real executor here.
    let Ok(play) = record_playthrough(&universe, &moves) else {
        return;
    };
    // Submit with the STORED claimed_turns — a tampered value trips ResultMismatch.
    let _ = reg.submit(Completion {
        universe: id,
        player: sc.player.clone(),
        play,
        claimed_turns: sc.claimed_turns as usize,
    });
}

/// Resolve a full day-universe content-address hex to its published id in `reg`.
fn find_board_universe(reg: &Registry, id_hex_str: &str) -> Option<UniverseId> {
    reg.universes()
        .map(|u| u.id())
        .find(|id| id_hex(id) == id_hex_str)
}

/// The full 64-hex content address of a day-universe.
fn id_hex(id: &UniverseId) -> String {
    hex32(id.as_bytes())
}

fn hex32(bytes: &[u8; 32]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Decode a 64-char hex string to 32 bytes (`None` on any malformed input).
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

/// The durable board store, installed once by the main loop at boot ([`install_store`]). When
/// present, the live board [`Registry`] is loaded + re-verified from it on the store thread's spawn,
/// and each open/win persists through it.
static DESCENT_STORE: OnceLock<Box<dyn DescentBoardStore + Send + Sync>> = OnceLock::new();

/// **Main-loop entry point.** Install the durable board store and force the live board to load +
/// re-verify from it now (replaying every persisted completion through the no-cheat gate). First
/// install wins; call once at boot BEFORE any `/descent` command is served.
pub fn install_store(board_store: Box<dyn DescentBoardStore + Send + Sync>) {
    let _ = DESCENT_STORE.set(board_store);
    // Force the store thread to spawn now, which loads the board from the freshly-installed store.
    let _ = store();
}

/// Persist the day-universe a run is playing to the durable store, if one is installed. Called on
/// the store thread after a successful open (never while holding a lock across IO).
fn persist_universe_row(run: &DailyRun) {
    if let Some(store) = DESCENT_STORE.get() {
        if let Some(row) = StoredDescentUniverse::of(run) {
            let _ = store.persist_universe(&row);
        }
    }
}

/// Persist a verified winning run to the durable store, if one is installed. Called on the store
/// thread right after the win is accepted onto the board.
fn persist_completion_row(run: &DailyRun, player: &str) {
    if let Some(store) = DESCENT_STORE.get() {
        if let Some(row) = StoredDescentCompletion::of(run, player) {
            let _ = store.persist_completion(&row);
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The dedicated store thread — owns every live run + the DURABLE board, keyed
// by discord user id. Mirrors `crate::commands::offering::Store`: `Send` jobs in,
// `Send` snapshots out; the non-`Send` `WorldCell`s never leave this thread. Each
// job captures a cheap `SqliteCharacterStore` clone (all durable state is in sqlite)
// to build the stateless daily offering. On spawn the board is loaded + re-verified
// from the installed `DescentBoardStore` (an empty board if none is installed).
// ─────────────────────────────────────────────────────────────────────────────

/// One player's live daily run + the board id of the day it is playing.
struct Slot {
    run: DailyRun,
    universe_id: UniverseId,
    narrator: NarratorKind,
    last_narration: String,
}

/// The world the store thread owns: every player's live run + the day's no-cheat board.
struct DescentWorld {
    slots: HashMap<u64, Slot>,
    board: Registry,
}

type DescentJob = Box<dyn FnOnce(&mut DescentWorld) + Send + 'static>;

/// The dedicated single-thread owner of all live runs + the board.
struct DescentStore {
    jobs: SyncSender<DescentJob>,
}

impl DescentStore {
    fn spawn() -> DescentStore {
        let (tx, rx) = sync_channel::<DescentJob>(64);
        std::thread::Builder::new()
            .name("descent-store".to_string())
            .spawn(move || {
                // Load + re-verify the board from the installed durable store (empty if none).
                let board = match DESCENT_STORE.get() {
                    Some(store) => load_board(store.as_ref()),
                    None => Registry::new(),
                };
                let mut world = DescentWorld {
                    slots: HashMap::new(),
                    board,
                };
                while let Ok(job) = rx.recv() {
                    job(&mut world);
                }
            })
            .expect("spawn the descent store thread");
        DescentStore { jobs: tx }
    }

    /// Run `f` on the store thread and return its `Send` result.
    fn run<R: Send + 'static>(&self, f: impl FnOnce(&mut DescentWorld) -> R + Send + 'static) -> R {
        let (tx, rx) = sync_channel(1);
        let _ = self.jobs.send(Box::new(move |w| {
            let _ = tx.send(f(w));
        }));
        rx.recv().expect("the descent store thread is alive")
    }
}

/// The process-global store thread (lazy).
fn store() -> &'static DescentStore {
    static STORE: OnceLock<DescentStore> = OnceLock::new();
    STORE.get_or_init(DescentStore::spawn)
}

// ─────────────────────────────────────────────────────────────────────────────
// Board reads for the breadth surfaces — the weekly tournament's earned entry list
// (`commands::tournament`) and the NFT export's earned-ness source (`commands::export_nft`).
// Both read the LIVE board on the store thread: the board only ever holds entries the
// no-cheat gate re-executed to the win, so presence here IS the verified qualification.
// ─────────────────────────────────────────────────────────────────────────────

/// Every distinct player holding a VERIFIED win on the live no-cheat board (any published
/// day), with their best verified turns-to-win — ascending by merit (fewest turns first,
/// name as the stable tie-break). The weekly tournament seeds its bracket by this order.
pub fn verified_players_by_merit() -> Vec<(String, usize)> {
    store().run(|w| {
        let mut best: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
        for u in w.board.universes() {
            for e in w.board.leaderboard(u.id()) {
                let cur = best.entry(e.player.clone()).or_insert(e.turns);
                if e.turns < *cur {
                    *cur = e.turns;
                }
            }
        }
        let mut rows: Vec<(String, usize)> = best.into_iter().collect();
        rows.sort_by(|a, b| a.1.cmp(&b.1).then(a.0.cmp(&b.0)));
        rows
    })
}

/// A player's BEST verified board win — what `/export` mints as a 1-of-1 SPL NFT. The
/// `completion_id` is the board's content address of the re-executed run (the commitment
/// the NFT memo carries).
pub struct VerifiedWin {
    /// The day-universe content address (hex) the win is on.
    pub universe_id_hex: String,
    /// The day-universe's display name.
    pub universe_name: String,
    /// The board's completion id — a 32-byte commitment to (player, playthrough).
    pub completion_id: [u8; 32],
    /// The verified turns-to-win.
    pub turns: usize,
}

/// The player's best (fewest-turns) VERIFIED win across every published day, or `None`
/// if they hold no verified board entry.
pub fn verified_win_of(player: &str) -> Option<VerifiedWin> {
    let player = player.to_string();
    store().run(move |w| {
        let mut best: Option<VerifiedWin> = None;
        for u in w.board.universes() {
            for e in w.board.leaderboard(u.id()) {
                if e.player != player {
                    continue;
                }
                if best.as_ref().is_none_or(|b| e.turns < b.turns) {
                    best = Some(VerifiedWin {
                        universe_id_hex: id_hex(&u.id()),
                        universe_name: u.name().to_string(),
                        completion_id: e.completion_id,
                        turns: e.turns,
                    });
                }
            }
        }
        best
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// Registration + slash routing.
// ─────────────────────────────────────────────────────────────────────────────

/// Register the `/descent` command (play / verify / board / today).
pub fn register() -> CreateCommand {
    CreateCommand::new("descent")
        .description(
            "THE DESCENT — today's beacon-seeded permadeath roguelite (your character carries)",
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "play",
                "Descend into today's dungeon (a real permadeath run on the dregg executor)",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "class",
                    "Pick your class if unclassed (warrior / mage / rogue) — frozen once chosen",
                )
                .add_string_choice("warrior", "warrior")
                .add_string_choice("mage", "mage")
                .add_string_choice("rogue", "rogue")
                .required(false),
            ),
        )
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "room",
            "Re-show your current room + fresh move buttons (recovers a lost room message)",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "verify",
            "Re-verify your current run's committed chain by replay",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "board",
            "Today's no-cheat leaderboard (a run ranks ONLY if it re-executes to the win)",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "today",
            "Describe today's dungeon — its beacon-verified reveal + how it plays",
        ))
        // The weekly verify-gated bracket over the board's VERIFIED winners (backlog #16);
        // the handler lives in its own module (`crate::commands::tournament`).
        .add_option(crate::commands::tournament::register_option())
}

/// Route `/descent` subcommands.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let Some(sub) = command.data.options.first() else {
        return;
    };
    match sub.name.as_str() {
        "play" => handle_play(ctx, command, state).await,
        "room" => handle_room(ctx, command).await,
        "verify" => handle_verify(ctx, command, state).await,
        "board" => handle_board(ctx, command, state).await,
        "today" => handle_today(ctx, command).await,
        "tournament" => crate::commands::tournament::handle(ctx, command, state).await,
        _ => {}
    }
}

async fn respond(
    ctx: &Context,
    command: &CommandInteraction,
    embed: CreateEmbed,
    rows: Vec<CreateActionRow>,
    ephemeral: bool,
) {
    let mut msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .components(rows);
    if ephemeral {
        msg = msg.ephemeral(true);
    }
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

fn class_id_of(label: &str) -> Option<u64> {
    match label {
        "warrior" => Some(WARRIOR),
        "mage" => Some(MAGE),
        "rogue" => Some(ROGUE),
        _ => None,
    }
}

// ─── /descent play ─────────────────────────────────────────────────────────────

async fn handle_play(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let user_id = command.user.id.get();
    let who = identity_of(state, user_id);
    let class = command.data.options.first().and_then(|sub| {
        if let CommandDataOptionValue::SubCommand(opts) = &sub.value {
            opts.first()
                .and_then(|o| o.value.as_str())
                .and_then(class_id_of)
        } else {
            None
        }
    });

    // ACK inside Discord's 3s window BEFORE anything commits or narrates (the narrator alone can
    // take ~20s) — the room lands as an EDIT of this deferred response.
    ack::defer_slash(ctx, command, false).await;

    // A LIVE run is never silently abandoned by a re-open: re-show its current room instead
    // (the recovery affordance — a lost/failed room message no longer costs the run).
    let live_view: Option<RunView> = store().run(move |w| {
        w.slots
            .get(&user_id)
            .filter(|s| !s.run.is_ended())
            .map(|s| RunView::of(&s.run))
    });
    if let Some(view) = live_view {
        let (narration, kind) = current_narration(user_id, &view);
        let embed = room_embed(&view, &narration, kind).field(
            "Your descent continues",
            "You already have a live run today — here is your current room, with fresh move \
             buttons (a re-open never abandons a live permadeath run). `/descent room` re-shows \
             it any time.",
            false,
        );
        ack::edit_slash(ctx, command, embed, move_rows(user_id, &view.options)).await;
        return;
    }

    let store_clone = state.characters.clone();
    let beacon = resolve_todays_beacon();

    // Open today's run on the store thread (verifies the beacon, deploys the world, loads the
    // carried character, publishes today's world to the board). `Send` in, a `Send` `RunView` out.
    let opened: Result<RunView, String> = store().run(move |w| {
        let off = DailyDescentOffering::new(store_clone);
        match open_core(&off, &mut w.board, who, &beacon, class) {
            Ok((run, uid)) => {
                // Durable: persist today's day-world (its committed seed) so the board can
                // reconstruct it on boot before replaying any completion against it.
                persist_universe_row(&run);
                let view = RunView::of(&run);
                w.slots.insert(
                    user_id,
                    Slot {
                        run,
                        universe_id: uid,
                        narrator: NarratorKind::Scripted,
                        last_narration: String::new(),
                    },
                );
                Ok(view)
            }
            Err(e) => Err(e.to_string()),
        }
    });

    let view = match opened {
        Ok(v) => v,
        Err(why) => {
            let embed = error_embed(
                "Today's descent did not open",
                &format!("The beacon-seeded world failed to deploy: {why}"),
            );
            ack::edit_slash(ctx, command, embed, vec![]).await;
            return;
        }
    };

    // Narrate the opening room OFF the store thread (the network call), then record it.
    let (narration, kind) = narrate_room_gated(
        state,
        user_id,
        view.room.as_deref().unwrap_or("the threshold"),
        &view.prose,
    )
    .await;
    record_narration(user_id, &narration, kind);

    let embed = room_embed(&view, &narration, kind);
    let rows = move_rows(user_id, &view.options);
    ack::edit_slash(ctx, command, embed, rows).await;
}

// ─── /descent room — re-show the current room (the recovery affordance) ─────────

/// **Re-render the invoker's current room** with fresh move buttons — the recovery path when a
/// room message was lost (a narration hiccup, a deleted message, a scrolled-away channel).
/// Read-only: no turn is committed, the run is untouched, the last narration is reused.
async fn handle_room(ctx: &Context, command: &CommandInteraction) {
    let user_id = command.user.id.get();
    let view: Option<RunView> =
        store().run(move |w| w.slots.get(&user_id).map(|s| RunView::of(&s.run)));
    match view {
        None => {
            let embed = warn_embed(
                "No descent open",
                "You have no run open. Begin one with `/descent play`.",
            );
            respond(ctx, command, embed, vec![], true).await;
        }
        Some(view) if view.ended => {
            let embed = result_embed(&view, None, "This descent has already ended.");
            respond(ctx, command, embed, vec![], true).await;
        }
        Some(view) => {
            let (narration, kind) = current_narration(user_id, &view);
            let embed = room_embed(&view, &narration, kind);
            let rows = move_rows(user_id, &view.options);
            respond(ctx, command, embed, rows, false).await;
        }
    }
}

// ─── the move buttons (a press advances the presser's OWN run) ──────────────────

/// Route a `descent:` component press. custom_ids:
/// * `descent:move:<userId>:<choiceIndex>` — advance the presser's OWN run by one real turn;
/// * `descent:rv:<completion_id hex>` — **Re-verify #N**: ANY presser (deliberately no owner
///   gate — a stranger's re-run is the point) re-executes a ranked entry through the live
///   no-cheat gate, in front of the channel (backlog Tier-2 #9).
pub async fn handle_component(ctx: &Context, component: &ComponentInteraction, state: &BotState) {
    let id = component.data.custom_id.clone();
    let parts: Vec<&str> = id.split(':').collect();
    if parts.len() == 3 && parts[1] == "rv" {
        handle_reverify(ctx, component, parts[2]).await;
        return;
    }
    if parts.len() != 4 || parts[1] != "move" {
        return;
    }
    let owner: u64 = match parts[2].parse() {
        Ok(n) => n,
        Err(_) => return,
    };
    let choice: usize = match parts[3].parse() {
        Ok(n) => n,
        Err(_) => return,
    };
    let presser = component.user.id.get();

    // A descent is a SOLO permadeath run — only its owner may move it.
    if presser != owner {
        let _ = component
            .create_response(
                &ctx.http,
                CreateInteractionResponse::Message(
                    CreateInteractionResponseMessage::new()
                        .content(
                            "This is not your descent — run `/descent play` to begin your own.",
                        )
                        .ephemeral(true),
                ),
            )
            .await;
        return;
    }

    // ACK the press inside Discord's 3s window BEFORE the turn commits or the narrator runs
    // (the narrator alone can take ~20s). The re-render lands as an EDIT of this deferred
    // update — a slow narration can no longer present a committed permadeath move as
    // "This interaction failed".
    ack::ack_component(ctx, component).await;

    let store_clone = state.characters.clone();
    let player = short_player(&identity_of(state, owner).0);
    let result = store().run(move |w| {
        let Some(slot) = w.slots.get_mut(&owner) else {
            return MoveResult::NoRun;
        };
        let mut off = DailyDescentOffering::new(store_clone);
        let uid = slot.universe_id;
        let outcome = advance_core(&mut off, &mut slot.run, &mut w.board, uid, &player, choice);
        // Durable: a verified win survives restart. Only the reproducible public input (the move
        // sequence + player) is persisted; the board is rebuilt by REPLAY on boot, so a tampered
        // row cannot resurrect a cheat. Persist ONLY when the win actually ranked (rank Some).
        if let MoveResult::Landed { rank: Some(_), .. } = &outcome {
            persist_completion_row(&slot.run, &player);
        }
        outcome
    });

    match result {
        MoveResult::NoRun => {
            // The press was already ACKed (deferred update), so this rides a followup — the
            // stale room message is left as-is, the presser gets the pointer privately.
            ack::followup_ephemeral(
                ctx,
                component,
                "Your descent has expired — run `/descent play` to begin anew.",
            )
            .await;
        }
        MoveResult::Refused { why, view } => {
            // A real executor refusal: the room is unchanged, no receipt committed (anti-ghost).
            let (narration, kind) = current_narration(owner, &view);
            let embed = room_embed(&view, &narration, kind).field(
                "Refused — the world disposed",
                format!("```{}```", truncate(&why, 500)),
                false,
            );
            update_message(ctx, component, embed, move_rows(owner, &view.options)).await;
        }
        MoveResult::AlreadyEnded(view) => {
            let embed = result_embed(&view, None, "This descent has already ended.");
            update_message(ctx, component, embed, vec![]).await;
        }
        MoveResult::Landed {
            view,
            rank,
            board_note,
        } => {
            if view.ended {
                let embed = result_embed(&view, rank, &board_note);
                update_message(ctx, component, embed, vec![]).await;
            } else {
                // Narrate the NEXT room OFF the store thread, then re-render.
                let (narration, kind) = narrate_room_gated(
                    state,
                    owner,
                    view.room.as_deref().unwrap_or("the dark"),
                    &view.prose,
                )
                .await;
                record_narration(owner, &narration, kind);
                let embed = room_embed(&view, &narration, kind);
                update_message(ctx, component, embed, move_rows(owner, &view.options)).await;
            }
        }
    }
}

/// EDIT the pressed room message into the post-turn render. The press was ACKed with a
/// deferred update BEFORE the turn committed ([`handle_component`]), so this edit is what
/// lands the outcome — however long the narrator took.
async fn update_message(
    ctx: &Context,
    component: &ComponentInteraction,
    embed: CreateEmbed,
    rows: Vec<CreateActionRow>,
) {
    ack::edit_component(ctx, component, embed, rows).await;
}

/// Record how the current room was narrated (a brief job on the store thread).
fn record_narration(owner: u64, narration: &str, kind: NarratorKind) {
    let narration = narration.to_string();
    store().run(move |w| {
        if let Some(slot) = w.slots.get_mut(&owner) {
            slot.narrator = kind;
            slot.last_narration = narration;
        }
    });
}

/// The narration last recorded for this player's current room (so a refusal re-render keeps the
/// prose and never re-hits the network). Falls back to the room's scripted prose.
fn current_narration(owner: u64, view: &RunView) -> (String, NarratorKind) {
    let recorded = store().run(move |w| {
        w.slots
            .get(&owner)
            .map(|s| (s.last_narration.clone(), s.narrator))
    });
    match recorded {
        Some((n, k)) if !n.trim().is_empty() => (n, k),
        _ => (view.prose.clone(), NarratorKind::Scripted),
    }
}

// ─── /descent verify ────────────────────────────────────────────────────────────

async fn handle_verify(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let user_id = command.user.id.get();
    let store_clone = state.characters.clone();
    enum V {
        NoRun,
        Report {
            verified: bool,
            turns: usize,
            detail: String,
        },
    }
    let outcome = store().run(move |w| match w.slots.get(&user_id) {
        None => V::NoRun,
        Some(slot) => {
            let off = DailyDescentOffering::new(store_clone);
            let report = off.verify(&slot.run);
            V::Report {
                verified: report.verified,
                turns: slot.run.turns(),
                detail: report.detail,
            }
        }
    });

    let embed = match outcome {
        V::NoRun => warn_embed(
            "No descent open",
            "You have no run open. Begin one with `/descent play`.",
        ),
        V::Report {
            verified: true,
            turns,
            ..
        } => base_embed("✓ Your descent re-verifies by replay").description(format!(
            "**{turns} verified turns** re-verify: a fresh, identically beacon-seeded world-cell, \
             re-driven through your recorded choices, reproduces exactly your committed state \
             chain. A reordered, mutated, or ineligible move would break replay."
        )),
        V::Report { turns, detail, .. } => error_embed(
            "✗ Your descent FAILS replay",
            &format!("The recorded chain did not re-verify ({turns} turns):\n`{detail}`"),
        ),
    };
    respond(ctx, command, embed, vec![], true).await;
}

// ─── /descent board ───────────────────────────────────────────────────────────

async fn handle_board(ctx: &Context, command: &CommandInteraction, _state: &BotState) {
    // Today's board id is derived from the beacon-drawn world (published on any `/descent play`).
    // Compute it purely (no state needed) so the board renders even before this process's first run.
    let beacon = resolve_todays_beacon();
    let (day_title, uid) = match today_universe(&beacon) {
        Ok(v) => v,
        Err(why) => {
            let embed = error_embed("Today's board is unavailable", &why);
            respond(ctx, command, embed, vec![], true).await;
            return;
        }
    };
    // The exact PUBLIC inputs a stranger needs to verify OUTSIDE the bot (backlog #9): the
    // day-universe's content address + the committed beacon seed the world regenerates from.
    let universe_hex = id_hex(&uid);
    let seed_hex_str = beacon
        .seed()
        .map(|s| hex32(s.as_bytes()))
        .unwrap_or_else(|_| "(the beacon did not verify)".to_string());
    let view = store().run(move |w| board_core(&w.board, uid, &day_title));
    let rows = reverify_rows(&view.reverify);
    respond(
        ctx,
        command,
        board_embed(&view, &universe_hex, &seed_hex_str),
        rows,
        false,
    )
    .await;
}

// ─── /descent today ─────────────────────────────────────────────────────────────

async fn handle_today(ctx: &Context, command: &CommandInteraction) {
    let beacon = resolve_todays_beacon();
    let title = today_universe(&beacon)
        .map(|(t, _)| t)
        .unwrap_or_else(|_| "today's descent".to_string());
    let desc = format!(
        "**{title}** — today's dungeon is a pure function of a beacon-verified drand `quicknet` \
         reveal (round {round}). Everyone plays the byte-identical world; a different day's \
         verified round gives a different dungeon.\n\n\
         Every move is one cap-bounded turn the verified executor admits:\n\
         • **the warden** — a blow you could not survive is refused: the executor will not \
         let your HP fall below 1\n\
         • **the field-dressing** — a one-shot heal; a second use is refused\n\
         • **the sealed hoard-door** — opens only if you actually hold the key\n\
         • **defeat is real** — a reckless line falls into a committed DEFEAT, and (hardcore) \
         your persistent character PERISHES, un-undoably\n\n\
         Your character (level / class / earned XP / a hardcore death) carries across days. A WON \
         run posts to the no-cheat board — ranked only if it re-executes to the win.\n\n\
         Descend with `/descent play`.\n\n\
         **{status}**\n\n\
         _Named seams: the midnight auto-reveal; a web spectator page._",
        round = beacon.round,
        status = todays_beacon_status().label(),
    );
    let embed = base_embed(&format!("{title} — the day's reveal")).description(desc);
    respond(ctx, command, embed, vec![], true).await;
}

/// Today's world title + its content-addressed board id, computed purely from the verified beacon
/// (no live run needed). Fails closed if the beacon does not verify.
fn today_universe(beacon: &DailyBeacon) -> Result<(String, UniverseId), String> {
    let seed = beacon
        .seed()
        .map_err(|e| format!("the beacon did not verify: {e:?}"))?;
    let day = dreggnet_offerings::daily_descent::daily_scene(&seed);
    let universe: Universe =
        Universe::authored(&day.title, BOARD_AUTHOR, &day.source, day.win_condition())
            .map_err(|e| format!("could not author today's world: {e:?}"))?;
    Ok((day.title, universe.id()))
}

// ─────────────────────────────────────────────────────────────────────────────
// Rendering — embeds + move buttons.
// ─────────────────────────────────────────────────────────────────────────────

/// A fixed-width HP bar `[█████████░░░░░░░]`.
fn hp_bar(cur: u64, max: u64, width: usize) -> String {
    let max = max.max(1);
    let filled = ((cur.min(max) as f64 / max as f64) * width as f64).round() as usize;
    let filled = filled.min(width);
    let mut out = String::with_capacity(width + 2);
    out.push('[');
    out.extend(std::iter::repeat('█').take(filled));
    out.extend(std::iter::repeat('░').take(width - filled));
    out.push(']');
    out
}

/// The status HUD read straight off the committed cell.
fn status_block(view: &RunView) -> String {
    let state = if view.dead {
        "PERISHED (hardcore)"
    } else if view.won {
        "SURVIVED — hoard seized"
    } else if view.ended {
        "descent ended"
    } else {
        "descending"
    };
    format!(
        "HP     {hp_bar} {hp}/50\n\
         warden {warden_hp}   depth {depth}   gold {gold}   heals {heals}/1\n\
         hero   L{level} {class}  ·  XP {xp}\n\
         state  {state}   ·   verified turns {turns}",
        hp_bar = hp_bar(view.hp, 50, 16),
        hp = view.hp,
        warden_hp = view.warden_hp,
        depth = view.depth,
        gold = view.gold,
        heals = view.heals_used,
        level = view.level,
        class = view.class_name,
        xp = view.xp,
        state = state,
        turns = view.turns,
    )
}

/// The live room embed: the narrated prose, the status HUD, and the move ballot.
fn room_embed(view: &RunView, narration: &str, kind: NarratorKind) -> CreateEmbed {
    let mut desc = truncate(narration, 1600);
    if narration.trim() != view.prose.trim() && !view.prose.trim().is_empty() {
        desc.push_str("\n\n");
        desc.push_str(&format!("_{}_", truncate(&view.prose, 800)));
    }
    let room = view.room.clone().unwrap_or_else(|| "the dark".to_string());
    base_embed(&format!("{} — {}", view.day_title, room))
        .description(truncate(&desc, 4000))
        .field("Vitals", format!("```{}```", status_block(view)), false)
        .footer(footer(kind))
}

/// The final result embed — depth, alive/dead, the win/loss verdict, board rank, and a
/// `/descent verify`-able receipt note.
fn result_embed(view: &RunView, rank: Option<usize>, board_note: &str) -> CreateEmbed {
    let (title, verdict) = if view.won {
        (
            "🏆 The hoard is seized — the descent is SURVIVED",
            "You reached the hoard and carried it out. A verified win.".to_string(),
        )
    } else if view.dead {
        (
            "💀 PERISHED — the descent is lost",
            "A blow you could not answer felled you. Your hardcore character has PERISHED, \
             un-undoably — the death carries to every future day."
                .to_string(),
        )
    } else {
        (
            "The descent ended",
            "The run ended without the hoard.".to_string(),
        )
    };
    let rank_line = match rank {
        Some(r) => format!("\n\n**Leaderboard: ranked #{r}** on today's no-cheat board."),
        None => String::new(),
    };
    let body = format!(
        "{verdict}{rank_line}\n\n{note}\n\n**{turns} verified turns** on the chain — run \
         `/descent verify` to re-check them by replay.",
        verdict = verdict,
        rank_line = rank_line,
        note = board_note,
        turns = view.turns,
    );
    base_embed(&format!("{} — {}", view.day_title, title))
        .description(truncate(&body, 4000))
        .field(
            "Final vitals",
            format!("```{}```", status_block(view)),
            false,
        )
        .footer(footer(NarratorKind::Scripted))
}

/// The no-cheat leaderboard embed.
fn board_embed(view: &BoardView, universe_hex: &str, seed_hex_str: &str) -> CreateEmbed {
    let body = if view.entries.is_empty() {
        "No verified survivors yet today. Be the first — `/descent play`.".to_string()
    } else {
        let mut lines = String::new();
        for (rank, player, turns) in view.entries.iter().take(20) {
            lines.push_str(&format!("{rank:>2}. {player:<14} {turns} turns\n"));
        }
        format!("```{}```", truncate(&lines, 1800))
    };
    let mut embed = base_embed(&format!("{} — today's no-cheat board", view.day_title))
        .description(format!(
            "Ranked by turns-to-win (lower is better). A run ranks ONLY if its recorded receipt \
             chain re-executes to the WIN on an independent re-run — a forged or incomplete run is \
             refused.\n\n{body}"
        ))
        // The public inputs a STRANGER needs to verify a run outside the bot (backlog #9):
        // regenerate the day-world byte-for-byte from the committed seed, check it hashes to
        // the content address, then replay any entry's recorded moves through the same gate.
        .field(
            "Day universe (content address)",
            format!("```{universe_hex}```"),
            false,
        )
        .field(
            "Committed beacon seed",
            format!("```{seed_hex_str}```"),
            false,
        );
    if !view.reverify.is_empty() {
        embed = embed.field(
            "Verify it yourself",
            "Press **Re-verify #N** and the bot re-executes that entry's recorded moves on a \
             FRESH world regenerated from the committed seed — live, in front of you. Or do it \
             outside the bot: `procgen_dregg::daily_scene(seed)` → \
             `ugc_dregg::record_playthrough` → `Registry::submit` (the same gate).",
            false,
        );
    }
    embed.footer(footer(NarratorKind::Scripted))
}

/// The **Re-verify #N** buttons for today's ranked entries (top ten, five per row) — the
/// press anyone can make; `descent:rv:<completion_id hex>` routes to [`handle_reverify`].
fn reverify_rows(reverify: &[(usize, String)]) -> Vec<CreateActionRow> {
    let shown = &reverify[..reverify.len().min(10)];
    let mut rows: Vec<CreateActionRow> = Vec::new();
    for chunk in shown.chunks(5) {
        let buttons: Vec<CreateButton> = chunk
            .iter()
            .map(|(rank, cid_hex)| {
                CreateButton::new(format!("descent:rv:{cid_hex}"))
                    .label(format!("Re-verify #{rank}"))
                    .style(ButtonStyle::Secondary)
            })
            .collect();
        rows.push(CreateActionRow::Buttons(buttons));
    }
    rows
}

/// **The Re-verify press** (backlog Tier-2 #9, live — the same [`Registry::reverify_entry`]
/// the crate's test ran now runs for anyone, on demand). Resolves the pressed completion on
/// the live board, re-executes its recorded moves on a fresh identically-seeded world through
/// the real no-cheat gate, and posts the honest result PUBLICLY with the exact public inputs
/// (day-universe content address + committed seed) a stranger needs to repeat the check
/// outside the bot. Deliberately no owner gate: a stranger's re-run is the point.
async fn handle_reverify(ctx: &Context, component: &ComponentInteraction, cid_hex: &str) {
    let Some(cid) = decode_hex32(cid_hex) else {
        return;
    };
    let cid_hex_owned = cid_hex.to_string();
    let started = std::time::Instant::now();

    /// The `Send` result of a re-verify job.
    enum Rv {
        Gone,
        Checked {
            universe_hex: String,
            player: String,
            rank: usize,
            result: Result<usize, String>,
        },
    }

    let outcome = store().run(move |w| {
        // Resolve which published universe holds this completion (owned data out, then act).
        let ids: Vec<UniverseId> = w.board.universes().map(|u| u.id()).collect();
        let mut found: Option<(UniverseId, String, usize)> = None;
        for uid in ids {
            if let Some((i, e)) = w
                .board
                .leaderboard(uid)
                .iter()
                .enumerate()
                .find(|(_, e)| hex32(&e.completion_id) == cid_hex_owned)
            {
                found = Some((uid, e.player.clone(), i + 1));
                break;
            }
        }
        let Some((uid, player, rank)) = found else {
            return Rv::Gone;
        };
        Rv::Checked {
            universe_hex: id_hex(&uid),
            player,
            rank,
            result: w
                .board
                .reverify_entry(uid, &cid)
                .map_err(|e| format!("{e}")),
        }
    });

    let elapsed_ms = started.elapsed().as_millis();

    let embed = match outcome {
        Rv::Gone => warn_embed(
            "This entry is no longer on the live board",
            "The board re-verifies from its durable store on every boot and each day plays a \
             new world — an entry from an earlier day (or a row that failed boot replay) has \
             no live handle to re-execute. Today's board: `/descent board`.",
        ),
        Rv::Checked {
            universe_hex,
            player,
            rank,
            result,
        } => {
            // The committed seed, from the durable store's reproducible descriptor (the same
            // row boot replay regenerates the world from).
            let seed_line = DESCENT_STORE
                .get()
                .and_then(|s| s.list_universes().ok())
                .and_then(|us| us.into_iter().find(|u| u.id_hex == universe_hex))
                .map(|u| u.seed_hex)
                .unwrap_or_else(|| "(no durable store row — in-process board only)".to_string());
            match result {
                Ok(turns) => base_embed("✓ Re-verified — the run re-executes to the WIN")
                    .description(format!(
                        "**Re-executed {turns} moves on a fresh world** regenerated from the \
                         committed seed, reached the WIN — checked just now, in front of you \
                         ({elapsed_ms} ms). Board entry **#{rank} · {player}** is not taken on \
                         trust; it was re-run through the same no-cheat gate that admitted it.",
                    ))
                    .field(
                        "Day universe (content address)",
                        format!("```{universe_hex}```"),
                        false,
                    )
                    .field("Committed seed", format!("```{seed_line}```"), false)
                    .field(
                        "Repeat this outside the bot",
                        "`procgen_dregg::daily_scene(seed)` regenerates the world; \
                         `ugc_dregg::record_playthrough(universe, moves)` replays; \
                         `Registry::submit` is the gate. Same inputs, same verdict.",
                        false,
                    )
                    .footer(footer(NarratorKind::Scripted)),
                Err(why) => error_embed(
                    "✗ Re-verification FAILED — this entry does not re-execute",
                    &format!(
                        "Board entry **#{rank} · {player}** did NOT survive an independent \
                         re-run just now ({elapsed_ms} ms): `{why}`. A board row that fails \
                         its own replay deserves zero trust — this is the check working, \
                         not a cosmetic error.",
                    ),
                ),
            }
        }
    };

    let _ = component
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Message(
                CreateInteractionResponseMessage::new().embed(embed),
            ),
        )
        .await;
}

/// The move buttons for the current room, chunked into Discord action rows of five. A locked
/// (ineligible) move is a red button decoration; the executor is still the sole referee.
fn move_rows(owner: u64, options: &[MoveOption]) -> Vec<CreateActionRow> {
    let mut rows: Vec<CreateActionRow> = Vec::new();
    for (row_idx, chunk) in options.chunks(5).enumerate() {
        if row_idx >= 5 {
            break;
        }
        let mut buttons: Vec<CreateButton> = Vec::new();
        for opt in chunk {
            let label = if opt.enabled {
                opt.label.clone()
            } else {
                format!("🔒 {}", opt.label)
            };
            let style = if opt.enabled {
                ButtonStyle::Primary
            } else {
                ButtonStyle::Secondary
            };
            buttons.push(
                CreateButton::new(format!("descent:move:{owner}:{}", opt.index))
                    .label(truncate(&label, 78))
                    .style(style),
            );
        }
        if !buttons.is_empty() {
            rows.push(CreateActionRow::Buttons(buttons));
        }
    }
    rows
}

fn base_embed(title: &str) -> CreateEmbed {
    CreateEmbed::new().title(title).color(DESCENT_COLOR)
}

fn error_embed(title: &str, body: &str) -> CreateEmbed {
    CreateEmbed::new()
        .title(title)
        .description(body)
        .color(0xE63946)
}

fn warn_embed(title: &str, body: &str) -> CreateEmbed {
    CreateEmbed::new()
        .title(title)
        .description(body)
        .color(0xE9C46A)
}

fn footer(kind: NarratorKind) -> CreateEmbedFooter {
    CreateEmbedFooter::new(footer_text(kind, todays_beacon_status()))
}

/// The rendered footer line — the narrator kind, the beacon's live-vs-pinned verdict, and the
/// tagline (pure, so the tests can read exactly what a player sees).
fn footer_text(kind: NarratorKind, beacon: BeaconStatus) -> String {
    format!("{} · {} · {}", kind.label(), beacon.label(), TAGLINE)
}

// ─────────────────────────────────────────────────────────────────────────────
// The narrator — the SAME $DREGG credit gate `/dungeon` uses (real Bedrock paid,
// local gemma2:2b free, scripted fallback). The paid backend is never free-ridden:
// a paid narration debits exactly one credit AFTER a successful hosted call.
// ─────────────────────────────────────────────────────────────────────────────

/// Narrate a room, spending a `$DREGG` run-credit on real Bedrock when the player has one, else the
/// FREE tier (ollama gemma / scripted). The narrator kind is reported honestly.
async fn narrate_room_gated(
    state: &BotState,
    discord_user_id: u64,
    room_name: &str,
    room_desc: &str,
) -> (String, NarratorKind) {
    let discord = discord_user_id.to_string();
    if state.pay.can_run_paid(&discord) {
        if let Some(paid) = state.pay.paid.clone() {
            let system = narrator_system_prompt();
            let prompt = format!("Room: {room_name}. {room_desc}");
            // The hosted Bedrock client drives its OWN runtime with `block_on`; run it off-worker.
            let narration = tokio::task::spawn_blocking(move || paid.narrate(&system, &prompt))
                .await
                .ok()
                .and_then(|r| r.ok())
                .filter(|n| !n.text.trim().is_empty());
            if let Some(n) = narration {
                let _ = state.pay.debit_one(&discord);
                return (sanitize(&n.text), NarratorKind::Bedrock);
            }
        }
    }
    narrate_room_free(room_name, room_desc).await
}

/// The Descent narrator's system instruction (a solo permadeath crawl, not a party dungeon).
fn narrator_system_prompt() -> String {
    "You are the dungeon master of a solo permadeath descent into a beacon-cursed dungeon. In two \
     vivid, ominous sentences, set the scene for the lone descender as they arrive. Do NOT use \
     curly braces."
        .to_string()
}

/// The FREE narrator tier — a real local `gemma2:2b` over ollama, falling back to the scene's own
/// scripted prose (reported honestly as `Scripted`) when ollama is unreachable.
async fn narrate_room_free(room_name: &str, room_desc: &str) -> (String, NarratorKind) {
    match gemma_narrate(room_name, room_desc).await {
        Some(text) if !text.trim().is_empty() => (sanitize(&text), NarratorKind::Gemma),
        _ => (room_desc.to_string(), NarratorKind::Scripted),
    }
}

/// One ollama `/api/generate` call (model `gemma2:2b`, `stream:false`). `None` on any failure.
async fn gemma_narrate(room_name: &str, room_desc: &str) -> Option<String> {
    let endpoint =
        std::env::var("OLLAMA_URL").unwrap_or_else(|_| "http://127.0.0.1:11434".to_string());
    let url = format!("{}/api/generate", endpoint.trim_end_matches('/'));
    let prompt = format!(
        "You are the dungeon master of a solo permadeath dungeon descent. In two vivid, ominous \
         sentences, set the scene for the lone descender as they arrive. Do NOT use curly braces. \
         Room: {room_name}. {room_desc}"
    );
    let client = reqwest::Client::builder()
        .timeout(std::time::Duration::from_secs(20))
        .build()
        .ok()?;
    let body = serde_json::json!({
        "model": "gemma2:2b",
        "prompt": prompt,
        "stream": false,
        "options": { "temperature": 0.7 },
    });
    let resp = client.post(&url).json(&body).send().await.ok()?;
    if !resp.status().is_success() {
        return None;
    }
    let value: serde_json::Value = resp.json().await.ok()?;
    value
        .get("response")
        .and_then(|v| v.as_str())
        .map(str::to_string)
}

/// Drop the two JSON-hostile bytes + control chars but KEEP `{`/`}` (the executor, not this tidy,
/// is what refuses an injecting move).
fn sanitize(s: &str) -> String {
    s.chars()
        .filter(|c| *c != '"' && *c != '\\' && !c.is_control() || *c == '\n')
        .collect::<String>()
        .trim()
        .to_string()
}

/// Truncate to at most `max` chars (char-safe), appending `…` when cut.
fn truncate(s: &str, max: usize) -> String {
    if s.chars().count() <= max {
        return s.to_string();
    }
    let mut out: String = s.chars().take(max.saturating_sub(1)).collect();
    out.push('…');
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — the live daily /descent DRIVEN end to end over the REAL committed
// `DailyDescentOffering`, through the bot's own core (open → play → win/lose →
// carry → verify → no-cheat board), plus the scene-source render helpers + the
// beacon-daily property. No live Discord required (the sync cores the handlers
// call are driven directly over an in-memory character store).
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_offerings::character::InMemoryCharacterStore;
    use dreggnet_offerings::daily_descent::{
        CORRIDOR_ON, HOARD_FORCE, HOARD_GOLD, HOARD_SEIZE, KEY_TAKE, daily_scene,
    };
    use ugc_dregg::RejectReason;

    fn player(name: &str) -> DreggIdentity {
        DreggIdentity(name.to_string())
    }

    /// **The staleness is visible at the surface.** With no cached live round (or a stale one)
    /// the pinned fallback is served and the rendered footer SAYS so; with today's live round
    /// cached, the footer names the live round instead. (The pure resolution core is driven
    /// directly so the process-global live-beacon cache — which other tests rely on being
    /// empty — is never touched.)
    #[test]
    fn the_footer_labels_the_pinned_fallback_vs_the_live_round_honestly() {
        // No cached live round → the pinned fallback, and the footer says so.
        let (beacon, status) = resolve_beacon_for(20_000, None);
        assert_eq!(beacon.round, DRAND_QUICKNET_ROUND);
        assert_eq!(status, BeaconStatus::PinnedFallback);
        let f = footer_text(NarratorKind::Scripted, status);
        assert!(f.contains("beacon: PINNED fallback (not today's)"), "{f}");
        assert!(f.contains("daily world repeats"), "{f}");
        assert!(f.contains(TAGLINE), "the tagline still footers: {f}");

        // A cached round for a DIFFERENT day is stale → still the pinned fallback.
        let stale = DailyBeacon::quicknet(5_000_000, vec![0xAB; 48]);
        let (beacon, status) = resolve_beacon_for(20_000, Some((19_999, stale)));
        assert_eq!(beacon.round, DRAND_QUICKNET_ROUND);
        assert_eq!(status, BeaconStatus::PinnedFallback);

        // Today's cached live round is served, and the footer names it — no PINNED warning.
        let live = DailyBeacon::quicknet(5_000_000, vec![0xAB; 48]);
        let (beacon, status) = resolve_beacon_for(20_000, Some((20_000, live)));
        assert_eq!(beacon.round, 5_000_000);
        assert_eq!(status, BeaconStatus::Live { round: 5_000_000 });
        let f = footer_text(NarratorKind::Scripted, status);
        assert!(f.contains("beacon: live round 5000000"), "{f}");
        assert!(!f.contains("PINNED"), "{f}");
    }

    /// Drive a CAREFUL winning line to the hoard through the bot's `advance_core` (fight the
    /// warden down, healing once if the beacon drew a tough warden, press past, take the key, walk
    /// the corridors, force the door, seize the hoard). Returns the terminal `MoveResult`.
    fn drive_win(
        off: &mut DailyDescentOffering<InMemoryCharacterStore>,
        run: &mut DailyRun,
        board: &mut Registry,
        uid: UniverseId,
        who: &str,
    ) -> MoveResult {
        let mut last = MoveResult::NoRun;
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
                other => panic!("unexpected room in a winning line: {other}"),
            };
            last = advance_core(off, run, board, uid, who, ci);
            assert!(
                matches!(last, MoveResult::Landed { .. }),
                "a careful move must land in {room}, got {last:?}"
            );
        }
        last
    }

    /// THE HARD GATE, DRIVEN: a live daily descent plays today's beacon-seeded dungeon end to end —
    /// a careful line reaches the hoard + posts to the no-cheat board; the character earns XP; the
    /// run re-verifies by replay.
    #[test]
    fn a_careful_descent_wins_earns_and_ranks_on_the_no_cheat_board() {
        let mut off = DailyDescentOffering::new(InMemoryCharacterStore::new());
        let mut board = Registry::new();
        let who = player("player-winner");
        let (mut run, uid) = open_core(
            &off,
            &mut board,
            who,
            &resolve_todays_beacon(),
            Some(WARRIOR),
        )
        .expect("open today's beacon-seeded run");

        let result = drive_win(&mut off, &mut run, &mut board, uid, "winner");
        assert!(run.is_won(), "the careful line reached the hoard");
        assert_eq!(run.read_var("gold"), HOARD_GOLD, "the hoard is seized");
        assert!(!run.is_dead(), "a winner did not perish");
        // Earned XP: felled the warden (50) + seized the hoard (150).
        assert_eq!(
            run.character().xp(),
            dreggnet_offerings::daily_descent::XP_FELL_WARDEN
                + dreggnet_offerings::daily_descent::XP_SEIZE_HOARD,
            "XP earned from real landed outcomes"
        );
        // The terminal move ranked the WON run #1 on the no-cheat board.
        match result {
            MoveResult::Landed { view, rank, .. } => {
                assert!(view.ended && view.won);
                assert_eq!(rank, Some(1), "the first verified win ranks #1");
            }
            other => panic!("the winning seize must land + rank, got {other:?}"),
        }
        // Independent re-verification of the ranked entry (a stranger's re-run).
        let entry_ok = board
            .leaderboard(uid)
            .first()
            .map(|e| board.reverify_entry(uid, &e.completion_id).is_ok())
            .unwrap_or(false);
        assert!(entry_ok, "the ranked entry independently re-verifies");
    }

    /// A RECKLESS line DIES: a reckless opener burns HP to the brink, then a fall into the committed
    /// defeat passage ends the run in a real hardcore death — and it does NOT rank.
    #[test]
    fn a_reckless_descent_dies_and_does_not_rank() {
        let mut off = DailyDescentOffering::new(InMemoryCharacterStore::new());
        let mut board = Registry::new();
        let who = player("player-faller");
        let (mut run, uid) =
            open_core(&off, &mut board, who, &resolve_todays_beacon(), None).expect("open");
        assert!(!run.is_dead(), "alive at the start");

        // Reckless all-out blow: hp 50 → 20 (the warden still stands, the fall move unlocks).
        let r1 = advance_core(&mut off, &mut run, &mut board, uid, "faller", GATE_RECKLESS);
        assert!(
            matches!(r1, MoveResult::Landed { .. }),
            "the reckless opener commits"
        );
        assert!(run.read_var("hp") <= 20 && run.read_var("warden_hp") > 0);

        // Fall into the terminal defeat room — a real committed loss.
        let r2 = advance_core(&mut off, &mut run, &mut board, uid, "faller", GATE_FALL);
        assert!(matches!(r2, MoveResult::Landed { .. }), "the fall commits");
        assert_eq!(run.current_room().as_deref(), Some("downed"));

        // Close the defeat passage — the run ENDS in death.
        let r3 = advance_core(&mut off, &mut run, &mut board, uid, "faller", 0);
        match r3 {
            MoveResult::Landed { view, rank, .. } => {
                assert!(view.ended, "the run ended");
                assert!(view.dead, "the hardcore character PERISHED");
                assert!(!view.won, "a lost run did not reach the hoard");
                assert_eq!(rank, None, "a lost run does not rank");
            }
            other => panic!("the defeat close must land + not rank, got {other:?}"),
        }
        assert!(run.is_dead(), "hardcore death");
        assert!(
            run.character().attempt_resurrect().is_err(),
            "a hardcore death is final — resurrection refused"
        );
        // The board still has no ranked entry (the lost run was never submitted).
        assert!(
            board.leaderboard(uid).is_empty(),
            "nothing ranks from a loss"
        );
    }

    /// THE CHARACTER CARRIES: the SAME identity resumes its leveled character across a SIMULATED
    /// NEW DAY (a fresh offering/run over the same store); a different identity is fresh.
    #[test]
    fn the_character_carries_across_a_simulated_new_day() {
        let store = InMemoryCharacterStore::new();
        let mut off = DailyDescentOffering::new(store);
        let mut board = Registry::new();
        let alice = player("player-alice");

        // Day 1: a fresh Warrior wins, earns 200 XP, levels to 2, and the run END saves it.
        let (mut run, uid) = open_core(
            &off,
            &mut board,
            alice.clone(),
            &resolve_todays_beacon(),
            Some(WARRIOR),
        )
        .expect("open day 1");
        assert_eq!(
            run.character().level(),
            1,
            "a new adventurer begins at level 1"
        );
        drive_win(&mut off, &mut run, &mut board, uid, "alice");
        assert_eq!(run.character().xp(), 200, "earned the warden + the hoard");
        off.level_up(&run).expect("level 2 (xp 200 >= 100)");
        off.save(&run); // (advance_core already saved on the terminal move; this carries the level-up)
        assert!(off.store().has(&alice), "alice's character is persisted");

        // Day 2 (simulated): the SAME identity RESUMES the carried character.
        let (day2, _uid2) =
            open_core(&off, &mut board, alice, &resolve_todays_beacon(), None).expect("open day 2");
        assert_eq!(
            day2.character().level(),
            2,
            "carried level across the day boundary"
        );
        assert_eq!(day2.character().xp(), 200, "carried XP");
        assert_eq!(day2.character().class(), WARRIOR, "carried class");

        // A DIFFERENT identity is a fresh character.
        let (bob, _uid3) = open_core(
            &off,
            &mut board,
            player("player-bob"),
            &resolve_todays_beacon(),
            None,
        )
        .expect("open bob");
        assert_eq!(bob.character().level(), 1, "a different identity is fresh");
        assert_eq!(bob.character().xp(), 0);
    }

    /// THE NO-CHEAT BOARD refuses a FORGED run and accepts the honest one (non-vacuous).
    #[test]
    fn the_board_refuses_a_forged_run_and_accepts_the_honest_one() {
        let mut off = DailyDescentOffering::new(InMemoryCharacterStore::new());
        let mut board = Registry::new();
        let (mut win, uid) = open_core(
            &off,
            &mut board,
            player("honest"),
            &resolve_todays_beacon(),
            None,
        )
        .expect("open");
        drive_win(&mut off, &mut win, &mut board, uid, "honest");
        assert!(win.is_won());

        // FORGE: swap the opening measured blow for a reckless one — the recorded state diverges.
        let honest = off
            .completion(&win, BOARD_AUTHOR, "honest")
            .expect("completion");
        let mut forged = honest.clone();
        if let Some(first) = forged.play.steps.first_mut() {
            first.choice_index = GATE_RECKLESS;
        }
        forged.player = "cheater".to_string();
        let out = board.submit(forged);
        assert!(
            matches!(
                out,
                Err(RejectReason::FailedVerification(_)) | Err(RejectReason::DidNotWin)
            ),
            "a forged run is refused by the no-cheat board, got {out:?}"
        );
        // Non-vacuous: the honest run is accepted on the same board.
        assert!(board.submit(honest).is_ok(), "the honest run is accepted");
    }

    /// **The Re-verify press has a live handle for every ranked entry** (backlog #9): the
    /// board view carries a `(rank, completion_id hex)` per entry, the minted buttons ride the
    /// documented `descent:rv:<hex>` wire, and the handle round-trips — decoding it and calling
    /// the SAME `Registry::reverify_entry` the press runs re-executes the run to the WIN.
    #[test]
    fn the_board_view_carries_pressable_reverify_handles_that_round_trip() {
        let mut off = DailyDescentOffering::new(InMemoryCharacterStore::new());
        let mut board = Registry::new();
        let (mut run, uid) = open_core(
            &off,
            &mut board,
            player("player-press"),
            &resolve_todays_beacon(),
            None,
        )
        .expect("open");
        drive_win(&mut off, &mut run, &mut board, uid, "presser");

        let view = board_core(&board, uid, "today");
        assert_eq!(view.entries.len(), 1, "the win ranks");
        assert_eq!(
            view.reverify.len(),
            1,
            "every entry gets a re-verify handle"
        );
        let (rank, cid_hex) = &view.reverify[0];
        assert_eq!(*rank, 1);

        // The buttons ride the documented wire the component router dispatches on.
        let rows = reverify_rows(&view.reverify);
        let json = serde_json::to_value(&rows).expect("rows serialize");
        assert!(
            json.to_string().contains(&format!("descent:rv:{cid_hex}")),
            "{json}"
        );

        // The handle round-trips into the SAME live re-execution the press runs.
        let cid = decode_hex32(cid_hex).expect("the handle decodes");
        let turns = board
            .reverify_entry(uid, &cid)
            .expect("the pressed entry re-executes to the WIN on a fresh world");
        assert!(turns > 0, "a real re-executed move count comes back");
    }

    /// Drive a real win on today's world and return the run (won) + its board id, over the given
    /// character store — the fixture the durable-board tests persist + reload from.
    fn driven_win(who: &str) -> (DailyRun, UniverseId) {
        let mut off = DailyDescentOffering::new(InMemoryCharacterStore::new());
        let mut board = Registry::new();
        let (mut run, uid) = open_core(
            &off,
            &mut board,
            player(who),
            &resolve_todays_beacon(),
            Some(WARRIOR),
        )
        .expect("open");
        drive_win(&mut off, &mut run, &mut board, uid, who);
        assert!(run.is_won(), "the fixture run reached the hoard");
        (run, uid)
    }

    /// THE DURABLE BOARD SURVIVES RESTART + RE-VERIFIES ON BOOT: a verified win is persisted as its
    /// reproducible public input (the day's committed seed + the run's move sequence); a rebuild of
    /// the board PURELY from the durable store (a simulated restart) reconstructs the day-world,
    /// replays the run through the real no-cheat gate, and it STILL ranks — and the reloaded entry
    /// independently re-verifies (a stranger's re-run).
    #[test]
    fn the_durable_board_survives_restart_and_reverifies_on_boot() {
        let (run, _uid) = driven_win("boardwin");
        let su = StoredDescentUniverse::of(&run).expect("day-universe descriptor");
        let sc = StoredDescentCompletion::of(&run, "boardwin").expect("completion");

        // Persist only the reproducible public input (seed + moves) to a durable store.
        let store = InMemoryDescentBoardStore::new();
        store.persist_universe(&su).unwrap();
        store.persist_completion(&sc).unwrap();

        // SIMULATED RESTART: rebuild the board from nothing but the durable store.
        let reloaded = load_board(&store);
        let uid2 = find_board_universe(&reloaded, &su.id_hex)
            .expect("the day-world reconstructs from its seed");
        let lb = reloaded.leaderboard(uid2);
        assert_eq!(
            lb.len(),
            1,
            "the honest verified win survived restart and still ranks"
        );
        // The reloaded entry independently re-verifies by replay (a stranger's re-run).
        let cid = lb[0].completion_id;
        assert!(
            reloaded.reverify_entry(uid2, &cid).is_ok(),
            "the reloaded board entry independently re-verifies"
        );
    }

    /// A TAMPERED board row is DROPPED on reload — a cheat cannot be resurrected by editing the DB.
    /// Three tamperings, each starting from an honestly-ranked board, each dropped: (a) the moves
    /// edited to an ineligible/losing line, (b) a lied `claimed_turns`, (c) a mismatched seed (the
    /// day-world's content address no longer matches, so the universe — and its completion — drop).
    /// Non-vacuous: the untampered honest run ranks in every setup.
    #[test]
    fn a_tampered_board_row_is_dropped_on_reload() {
        let (run, _uid) = driven_win("honest");
        let su = StoredDescentUniverse::of(&run).expect("descriptor");
        let sc = StoredDescentCompletion::of(&run, "honest").expect("completion");

        // Baseline: an untampered store ranks the honest win.
        let honest_store = InMemoryDescentBoardStore::new();
        honest_store.persist_universe(&su).unwrap();
        honest_store.persist_completion(&sc).unwrap();
        let base = load_board(&honest_store);
        let uid_base =
            find_board_universe(&base, &su.id_hex).expect("day-world reconstructs (baseline)");
        assert_eq!(
            base.leaderboard(uid_base).len(),
            1,
            "baseline honest win ranks"
        );

        // (a) The moves edited to an ineligible line (GATE_FALL at full HP is refused on replay).
        let store_a = InMemoryDescentBoardStore::new();
        store_a.persist_universe(&su).unwrap();
        store_a.persist_completion(&sc).unwrap();
        store_a.tamper(|_us, cs| {
            for c in cs.iter_mut() {
                c.moves_json = "[4]".to_string();
            }
        });
        let reg_a = load_board(&store_a);
        let uid_a = find_board_universe(&reg_a, &su.id_hex).expect("day-world still reconstructs");
        assert!(
            reg_a.leaderboard(uid_a).is_empty(),
            "an edited (losing/ineligible) move line does NOT rank — the cheat is dropped"
        );

        // (b) A lied claimed_turns (≠ the verified move count) trips ResultMismatch on replay.
        let store_b = InMemoryDescentBoardStore::new();
        store_b.persist_universe(&su).unwrap();
        store_b.persist_completion(&sc).unwrap();
        store_b.tamper(|_us, cs| {
            for c in cs.iter_mut() {
                c.claimed_turns = 1;
            }
        });
        let reg_b = load_board(&store_b);
        let uid_b = find_board_universe(&reg_b, &su.id_hex).expect("day-world still reconstructs");
        assert!(
            reg_b.leaderboard(uid_b).is_empty(),
            "a lied turn count does NOT rank — dropped as a result mismatch"
        );

        // (c) A mismatched seed: the recomputed content address no longer matches the stored id, so
        // the day-world is dropped — and with no universe, its completion cannot land either.
        let store_c = InMemoryDescentBoardStore::new();
        store_c.persist_universe(&su).unwrap();
        store_c.persist_completion(&sc).unwrap();
        store_c.tamper(|us, _cs| {
            for u in us.iter_mut() {
                // Flip the first seed nibble — a different world, a different content address.
                let mut bytes = decode_hex32(&u.seed_hex).unwrap();
                bytes[0] ^= 0x01;
                u.seed_hex = hex32(&bytes);
            }
        });
        let reg_c = load_board(&store_c);
        assert!(
            find_board_universe(&reg_c, &su.id_hex).is_none(),
            "a tampered seed drops the day-world (content address mismatch)"
        );
        assert!(
            reg_c.universes().next().is_none(),
            "nothing else lands from a tampered board"
        );
    }

    /// BEACON-DAILY: today's dungeon is beacon-deterministic (same seed → same world), and a
    /// different day's verified round gives a DIFFERENT dungeon.
    #[test]
    fn todays_dungeon_is_beacon_deterministic_and_a_new_day_differs() {
        let today_seed = resolve_todays_beacon().seed().expect("today's seed");
        // Same seed → byte-identical world (determinism the leaderboard leans on).
        assert_eq!(
            daily_scene(&today_seed).source,
            daily_scene(&today_seed).source,
            "same beacon seed → same dungeon"
        );
        // A different day's beacon output → a different daily seed → a different world.
        let other_seed = procgen_dregg::daily_seed(&[0x5c; 32]);
        assert_ne!(today_seed.as_bytes(), other_seed.as_bytes());
        assert_ne!(
            daily_scene(&today_seed).source,
            daily_scene(&other_seed).source,
            "a different day's beacon gives a different dungeon"
        );
    }

    /// A FORGED beacon cannot open a day (fail-closed) — non-vacuous: the honest beacon opens.
    #[test]
    fn a_forged_beacon_cannot_open_a_day() {
        let off = DailyDescentOffering::new(InMemoryCharacterStore::new());
        let mut board = Registry::new();
        let mut sig = hex::decode(DRAND_QUICKNET_SIG_HEX).unwrap();
        sig[0] ^= 0x01;
        let forged = DailyBeacon::quicknet(DRAND_QUICKNET_ROUND, sig);
        assert!(
            open_core(&off, &mut board, player("p"), &forged, None).is_err(),
            "a forged beacon must not open a day"
        );
        assert!(
            open_core(
                &off,
                &mut board,
                player("p"),
                &resolve_todays_beacon(),
                None
            )
            .is_ok(),
            "the honest beacon opens"
        );
    }

    /// The scene-source render helpers read the current room's ordered choice labels + prose
    /// straight out of the emitted DSL (the SAME order the executor indexes with).
    #[test]
    fn the_render_helpers_read_the_scene_source() {
        let seed = resolve_todays_beacon().seed().expect("seed");
        let day = daily_scene(&seed);

        // The gate room has the five warden choices in index order.
        let gate = room_choices(&day.source, "gate");
        assert_eq!(gate.len(), 5, "the gate offers five moves: {gate:?}");
        assert!(gate[GATE_MEASURED].to_lowercase().contains("measured"));
        assert!(gate[GATE_RECKLESS].to_lowercase().contains("reckless"));
        assert!(
            gate[GATE_HEAL].to_lowercase().contains("wound")
                || gate[GATE_HEAL].to_lowercase().contains("dressing")
        );
        assert!(gate[GATE_FALL].to_lowercase().contains("fall"));

        // The hoard room has exactly the one WIN move; the gate has readable prose.
        assert_eq!(room_choices(&day.source, "hoard").len(), 1);
        assert!(
            !room_prose(&day.source, "gate").trim().is_empty(),
            "the gate has prose"
        );

        // Eligibility decoration: at genesis (hp 50, warden up) the press-past move is locked.
        let off = DailyDescentOffering::new(InMemoryCharacterStore::new());
        let run = off
            .open(player("look"), &resolve_todays_beacon())
            .expect("open");
        let opts = ballot(&run);
        let press = opts
            .iter()
            .find(|o| o.index == GATE_PRESS)
            .expect("press-past present");
        assert!(
            !press.enabled,
            "press-past is locked while the warden stands"
        );
        let measured = opts
            .iter()
            .find(|o| o.index == GATE_MEASURED)
            .expect("measured present");
        assert!(measured.enabled, "a measured blow is available at full HP");

        // The move buttons build (one row, five buttons for the gate).
        let rows = move_rows(42, &opts);
        assert!(!rows.is_empty(), "the ballot renders buttons");
    }

    /// The custom-id round-trips: `descent:move:<owner>:<idx>` parses back to (owner, idx).
    #[test]
    fn the_move_custom_id_round_trips() {
        let rows = move_rows(
            777,
            &[MoveOption {
                label: "Measured blow".into(),
                index: 0,
                enabled: true,
            }],
        );
        // Rebuild the id the button carries and parse it exactly as `handle_component` does.
        let id = format!("descent:move:{}:{}", 777, 0);
        let parts: Vec<&str> = id.split(':').collect();
        assert_eq!(parts.len(), 4);
        assert_eq!(parts[1], "move");
        assert_eq!(parts[2].parse::<u64>().unwrap(), 777);
        assert_eq!(parts[3].parse::<usize>().unwrap(), 0);
        assert!(!rows.is_empty());
    }
}
