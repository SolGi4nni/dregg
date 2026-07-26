//! # `daily_descent` — THE DESCENT: a daily, provably-fair, permadeath procgen roguelite.
//!
//! The flagship's core (docs/GAME-STRATEGY.md Phase 1). Every day, ONE dungeon — a single
//! **drand-beacon-seeded** procgen world that everyone plays. You can DIE (real committed
//! defeat + hardcore, un-undoable character death). Your persistent character carries in and
//! earns on the run. A **no-cheat leaderboard** ranks a verified run — and refuses a forged one.
//!
//! It welds three things that already exist on the real substrate into the daily loop:
//!
//! 1. **The beacon-seeded daily world** ([`DailyBeacon`](procgen_dregg::beacon::DailyBeacon) →
//!    [`daily_seed`](procgen_dregg::daily_seed)). Today's dungeon is a pure function of today's
//!    verified drand round: **unpredictable until the round matures** (no grinding a favourable
//!    day — a forged beacon is refused by the pairing check), **identical world-wide**, and
//!    **verifiable by re-derivation**. [`daily_scene`] draws the day's world (theme, warden
//!    strength, depth, room descriptions) from procgen's VERIFIED `dregg-dice` stream.
//! 2. **Permadeath, on the real executor** (the [`dungeon_on_dregg::bloodgate`] pattern). The
//!    day's world is a stakes-forward trial: an HP floor (`FieldGte(hp, 1)`) means a blow you
//!    could not survive is refused, and a reckless line strands you into a real committed
//!    **DEFEAT** passage (`downed -> END`). A run can be genuinely LOST. Every tooth here is
//!    compiler-emitted from a scene condition, so the world the offering plays and the world the
//!    leaderboard re-executes are byte-identical (no augmentation).
//! 3. **The persistent, hardcore character** ([`crate::character`]). Level / class / earned XP
//!    carry across days; a hardcore death is [`WriteOnce`]-final and PERSISTS — a re-opened dead
//!    character loads dead. This is the un-forgeable "I survived" the leaderboard leans on.
//! 4. **The no-cheat leaderboard** ([`ugc_dregg`]). The day's world is a published
//!    [`Universe`](ugc_dregg::Universe); a run is a [`Completion`](ugc_dregg::Completion) the
//!    board accepts ONLY if [`verify_completion`](ugc_dregg::verify_completion) re-executes it to
//!    the WIN (seized the hoard) against a fresh identically-seeded world. A forged / incomplete
//!    run is REFUSED.
//!
//! ## Honest scope
//!
//! - **The beacon.** Verification is real drand `quicknet` interop (a BLS pairing check against
//!   the pinned group key). *Fetching* today's `(round, signature)` from a drand node is the
//!   named client seam ([`procgen_dregg::beacon`] docs); a [`DailyBeacon`] is built from an
//!   already-fetched round. The driven test seeds "today" from a REAL published round.
//! - **The leaderboard surface.** The ranking substrate is [`ugc_dregg`] (re-execute-to-win,
//!   ranked by turns). The daily-reveal UX (the bot's midnight freeze/reveal) and the web
//!   spectator page are the frontends above this core — named, not built here.
//! - **What the full flagship adds next:** the bot's daily-reveal loop, the web spectator /
//!   provenance page, and meta-progression-on-death (a death that unlocks a persistent boon).
//!   This module is the earning core those surfaces render.

use dregg_app_framework::TurnReceipt;
use dregg_node_target::{Landed, NodeTarget, SubmittedTurn};
use procgen_dregg::CommittedSeed;
use procgen_dregg::beacon::DailyBeacon;
use spween_dregg::{
    Driver, Playthrough, Scene, StepReceipt, WorldCell, WorldError, parse, verify_by_replay,
};
use ugc_dregg::{Completion, PublishError, Universe, WinCondition};

use crate::character::{Character, CharacterSheet, CharacterStore};
use crate::{DreggIdentity, OfferingError, Outcome};

// ═══════════════════════════════════════════════════════════════════════════════
// The day's world — a beacon-seeded permadeath scene.
// ═══════════════════════════════════════════════════════════════════════════════

/// The fixed deploy seed the day's world-cell is birthed under. Matches the seed
/// [`ugc_dregg::Universe::authored`] pins, so the offering's live session and the leaderboard's
/// re-executed universe deploy the byte-identical cell — a run recorded on one re-verifies on the
/// other. The DAY's variety lives in the scene SOURCE (beacon-drawn), not this identity constant.
pub const DAILY_DEPLOY_SEED: u8 = 7;

/// The hoard's gold — the win value. Reaching the hoard sets `gold = HOARD_GOLD`; the leaderboard
/// win condition is "the scene ENDED and `gold == HOARD_GOLD`".
pub const HOARD_GOLD: u64 = 500;

// ── `gate` choice indices (the warden fight + the fall-to-defeat) ────────────────
/// `gate`: a measured blow — 15 to you, 15 to the warden; gated `{ hp >= 16 }` (a blow you could
/// not survive is refused).
pub const GATE_MEASURED: usize = 0;
/// `gate`: a reckless all-out blow — 30 to you for the SAME 15 to the warden (a trap that burns
/// HP for no extra progress); gated `{ hp >= 31 }`.
pub const GATE_RECKLESS: usize = 1;
/// `gate`: bind your wounds with your ONE field-dressing (+25 HP); one-shot (gated
/// `{ heals_used <= 0 }`).
pub const GATE_HEAL: usize = 2;
/// `gate`: press past the felled warden — gated `{ warden_hp <= 0 }`.
pub const GATE_PRESS: usize = 3;
/// `gate`: fall to the warden — the DEFEAT move, gated `{ hp <= 20 }`; sets `downed = 1` and
/// routes to the terminal `downed` passage.
pub const GATE_FALL: usize = 4;

/// `downed`: the sole terminal move of the defeat room (`-> END`).
pub const DOWNED_END: usize = 0;

/// `keyroom`: take the key (`has_key = 1`) and press deeper.
pub const KEY_TAKE: usize = 0;
/// `keyroom`: press deeper empty-handed (the hoard-door will not open later).
pub const KEY_LEAVE: usize = 1;

/// `corridor{i}`: press onward into the dark.
pub const CORRIDOR_ON: usize = 0;

/// `hoardgate`: force the sealed hoard-door — gated `{ has_key >= 1 }`.
pub const HOARD_FORCE: usize = 0;
/// `hoardgate`: turn back, beaten by the door (a non-win end).
pub const HOARD_TURNBACK: usize = 1;

/// `hoard`: seize the hoard (`gold += HOARD_GOLD`) — the WIN.
pub const HOARD_SEIZE: usize = 0;

/// A themed content family for a day's descent (flavour only; the mechanics are identical).
struct Theme {
    title: &'static str,
    warden: &'static str,
    key_item: &'static str,
    hoard_item: &'static str,
    gate_prose: &'static str,
    defeat_prose: &'static str,
    descs: &'static [&'static str],
}

const THEMES: [Theme; 4] = [
    Theme {
        title: "The Sunken Descent",
        warden: "the Tide-Warden",
        key_item: "coral_key",
        hoard_item: "drowned hoard",
        gate_prose: "The Tide-Warden bars the flooded stair with a barnacled gaff. There is no way \
                     down but through it, and every exchange draws cold brine from both of you.",
        defeat_prose: "The gaff's hook finds you and the black water closes over your head. The \
                       descent is over — no key, no hoard. Your run ends here and cannot be retried.",
        descs: &[
            "Cold fen-water laps at the stones; a warden's lantern still hangs from an iron hook.",
            "A drowned stair spirals down into water too still to trust.",
            "Chains hang from a flooded ceiling, weeping rust into the murk.",
            "Salt has eaten the carvings to blank ghosts along the walls.",
        ],
    },
    Theme {
        title: "The Clockwork Descent",
        warden: "the Brass Sentinel",
        key_item: "winding_key",
        hoard_item: "orrery-core",
        gate_prose: "The Brass Sentinel stands athwart the gearworks stair, one fist a striking \
                     hammer. It does not tire, and it will not stand aside.",
        defeat_prose: "The Sentinel's fist comes around like a falling hammer and the gears close \
                       over you. The descent is over — no key, no hoard, and no second wind.",
        descs: &[
            "A floor of interlocking cogs, most of them stopped, one still faintly turning.",
            "Brass leaves litter a mechanical grove that has not budded in an age.",
            "Automaton birds hang frozen mid-song from wire branches overhead.",
            "A pendulum the size of a bell swings once, slow, then holds its breath.",
        ],
    },
    Theme {
        title: "The Ember Descent",
        warden: "the Kiln-Priest",
        key_item: "sun_sigil",
        hoard_item: "ember-lens",
        gate_prose: "The Kiln-Priest guards the ashen stair, fire answering to one raised hand. \
                     The heat alone would cow a lesser trespasser; the descent lies past it.",
        defeat_prose: "The Priest's fire outshines yours and the ash pours into your lungs. The \
                       descent is over — the light goes out, and this run will not be retried.",
        descs: &[
            "Warm ash sifts from a cracked dome; the floor is warm underfoot.",
            "Heat shimmers over a floor of fused glass and grey cinder.",
            "Star-charts have burned to lace along the curving wall.",
            "A ring of black mirrors holds the last red light of a dead furnace.",
        ],
    },
    Theme {
        title: "The Rimebound Descent",
        warden: "the Frozen Bishop",
        key_item: "frost_censer",
        hoard_item: "winter-relic",
        gate_prose: "The Frozen Bishop kneels frozen mid-blessing across the iced nave, yet its \
                     robe of solid rime turns aside a careless blow. Only through it lies the stair.",
        defeat_prose: "The cold hymn slows your blood until it will not move, and the ice takes you \
                       for its own. The descent is over — no relic, no return.",
        descs: &[
            "Frost has fused the pews to the floor; your breath hangs and does not fall.",
            "Icicles the length of spears depend from a vaulted ceiling of blue ice.",
            "Snow drifts through a shattered rose-window across a silent nave.",
            "Every footfall cracks a skin of new ice over older, deeper cold.",
        ],
    },
];

/// **The vitalities a day's warden can be drawn with**, ascending — [`daily_scene`]'s own draw, and
/// the SINGLE place the numbers live.
///
/// A surface printing a bare `Warden HP: 45` tells a reader nothing: 45 of what? It is the LIGHTER
/// of two draws, and the difference is whether measured blows alone suffice. The leaderboard reads
/// this to say so, and because the generator indexes the same array a re-draw cannot leave the page
/// quoting a range the world stopped using.
pub const WARDEN_HP_DRAWS: [u64; 2] = [45, 60];

/// The most connecting corridors a day can draw between the key room and the hoard gate (the floor
/// is one). Published for the same reason as [`WARDEN_HP_DRAWS`]: a surface saying "2" needs to be
/// able to say "of at most 3" without retyping the generator's bound.
pub const DEEPENING_ROOMS_MAX: usize = 3;

/// **The day's world spec** — the beacon-seeded permadeath scene plus the drawn parameters a
/// driver / verifier needs. The `source` is the spween DSL text; everyone who derives today's
/// [`CommittedSeed`] gets the byte-identical `source`.
#[derive(Clone, Debug)]
pub struct DailyDescent {
    /// The spween DSL source of today's world (parses + compiles + deploys).
    pub source: String,
    /// The day's display title (the drawn theme's title).
    pub title: String,
    /// The warden's starting HP (a beacon draw; higher demands the field-dressing to win).
    pub warden_hp: u64,
    /// The number of connecting corridor rooms between the key room and the hoard gate.
    pub deepening_rooms: usize,
    /// The committed seed this world was drawn from.
    pub seed: CommittedSeed,
}

impl DailyDescent {
    /// The leaderboard **win condition** for this day: the scene ENDED and the hoard was seized.
    pub fn win_condition(&self) -> WinCondition {
        WinCondition::ended_with(&[("gold", HOARD_GOLD)])
    }

    /// Publish today's world as an anonymous [`Universe`] for the no-cheat leaderboard (authored
    /// from the beacon-drawn scene source, with the "seize the hoard" win). Re-computing this from
    /// the same seed yields the same content-addressed [`ugc_dregg::UniverseId`].
    pub fn universe(&self, author: &str) -> Result<Universe, PublishError> {
        Universe::authored(&self.title, author, &self.source, self.win_condition())
    }
}

/// **Draw today's world from a committed seed** — the beacon-seeded procgen generator. Every
/// choice is one indexed draw of procgen's VERIFIED `dregg-dice` stream (never `rand`), so the
/// world is a pure, reproducible function of the seed. The emitted scene is a permadeath trial:
/// a warden fight with an HP floor + a fall-to-defeat passage, a key room, a beacon-drawn depth of
/// corridors, a key-gated hoard door, and the hoard (the win). Every rule lowers to a
/// compiler-emitted executor tooth — the offering and the leaderboard deploy the identical world.
pub fn daily_scene(seed: &CommittedSeed) -> DailyDescent {
    let (_req, _ev, stream) = procgen_dregg::verified_stream(seed);
    let pick = |index: u32, n: usize| -> usize {
        stream
            .draw_bounded(index, n as u64)
            .expect("draw index within the committed budget and n > 0") as usize
    };

    let theme = &THEMES[pick(0, THEMES.len())];
    // Warden HP is one of [`WARDEN_HP_DRAWS`]: the lighter is fellable by measured blows alone; the
    // heavier demands the one field-dressing to win (and a reckless line loses either way). The draw
    // INDEXES that array so the constant a surface quotes and the number the world uses are one
    // thing — it used to be `45 + 15 * pick(1, 2)`, a bound only this line knew.
    let warden_hp = WARDEN_HP_DRAWS[pick(1, WARDEN_HP_DRAWS.len())];
    // 1..=DEEPENING_ROOMS_MAX connecting corridors between the key room and the hoard gate.
    let deepening_rooms = 1 + pick(2, DEEPENING_ROOMS_MAX);

    let sid: String = seed.as_bytes()[..4]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    // Per-room description draws (indices well under procgen's committed DRAW_COUNT ~46).
    let desc = |room: u32| theme.descs[pick(10 + room, theme.descs.len())];

    let first_corridor = if deepening_rooms >= 1 {
        "corridor1".to_string()
    } else {
        "hoardgate".to_string()
    };

    let mut out = String::new();
    out.push_str(&format!(
        "---\nid: daily-descent-{sid}\ntitle: {}\nweight: 1\n---\n\n",
        theme.title
    ));

    // ── gate: the warden fight (HP floor) + the fall-to-defeat ──
    out.push_str("=== gate\n\n");
    out.push_str("~ hp = 50\n");
    out.push_str(&format!("~ warden_hp = {warden_hp}\n\n"));
    out.push_str(&format!("{}\n\n", theme.gate_prose));
    out.push_str(&format!(
        "* [Trade a measured blow against {w}] {{ hp >= 16 }}\n  ~ hp -= 15\n  ~ warden_hp -= 15\n  -> gate\n\n",
        w = theme.warden
    ));
    out.push_str(
        "* [Trade a reckless all-out blow] { hp >= 31 }\n  ~ hp -= 30\n  ~ warden_hp -= 15\n  -> gate\n\n",
    );
    out.push_str(
        "* [Bind your wounds with your one field-dressing] { heals_used <= 0 }\n  ~ heals_used += 1\n  ~ hp += 25\n  -> gate\n\n",
    );
    out.push_str(&format!(
        "* [Press past the felled {w}] {{ warden_hp <= 0 }}\n  ~ depth += 1\n  -> keyroom\n\n",
        w = theme.warden
    ));
    out.push_str(&format!(
        "* [Fall to {w}'s blow] {{ hp <= 20 }}\n  ~ downed = 1\n  -> downed\n\n",
        w = theme.warden
    ));

    // ── downed: the terminal DEFEAT passage ──
    out.push_str("=== downed\n\n");
    out.push_str(&format!("{}\n\n", theme.defeat_prose));
    out.push_str("* [The dark closes over the trial]\n  -> END\n\n");

    // ── keyroom: the descent's key (take it or leave it — the door needs it) ──
    out.push_str("=== keyroom\n\n");
    out.push_str(&format!("{}\n\n", desc(0)));
    out.push_str(&format!(
        "* [Take the {k} and press deeper]\n  ~ has_key = 1\n  ~ depth += 1\n  -> {first}\n\n",
        k = theme.key_item,
        first = first_corridor
    ));
    out.push_str(&format!(
        "* [Press deeper empty-handed]\n  ~ depth += 1\n  -> {first}\n\n",
        first = first_corridor
    ));

    // ── corridor1..corridorK: the beacon-drawn deepening ──
    for i in 1..=deepening_rooms {
        let next = if i == deepening_rooms {
            "hoardgate".to_string()
        } else {
            format!("corridor{}", i + 1)
        };
        out.push_str(&format!("=== corridor{i}\n\n"));
        out.push_str(&format!("{}\n\n", desc(i as u32)));
        out.push_str(&format!(
            "* [Press onward into the dark]\n  ~ depth += 1\n  -> {next}\n\n"
        ));
    }

    // ── hoardgate: the key-gated last door ──
    out.push_str("=== hoardgate\n\n");
    out.push_str(&format!(
        "A sealed hoard-door, banded in cold iron, bars the last descent. It will not shift for a \
         hand without the {k}.\n\n",
        k = theme.key_item
    ));
    out.push_str(
        "* [Force the sealed hoard-door] { has_key >= 1 }\n  ~ depth += 1\n  -> hoard\n\n",
    );
    out.push_str("* [Turn back, beaten by the door]\n  -> END\n\n");

    // ── hoard: the win ──
    out.push_str("=== hoard\n\n");
    out.push_str(
        "Past the door the hoard heaps the floor in the dark, cold and glittering and yours if \
         you can carry it out.\n\n",
    );
    out.push_str(&format!(
        "* [Seize the {h} — the descent is survived]\n  ~ gold += {HOARD_GOLD}\n  -> END\n\n",
        h = theme.hoard_item
    ));

    DailyDescent {
        source: out,
        title: theme.title.to_string(),
        warden_hp,
        deepening_rooms,
        seed: *seed,
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// The live run — a real committed playthrough on the day's world-cell.
// ═══════════════════════════════════════════════════════════════════════════════

/// XP earned for **felling the day's warden** (the landed press-past turn).
pub const XP_FELL_WARDEN: u64 = 50;
/// XP earned for **seizing the hoard** (the landed run-ending seize turn — the run survived).
pub const XP_SEIZE_HOARD: u64 = 150;

/// **A player's live run of today's descent** — the real day world-cell (genesis committed, moves
/// committed on it), the recorded [`Playthrough`] the offering re-verifies + submits, and the
/// player's persistent [`Character`] (which earns on the run and, in hardcore, PERISHES on defeat).
pub struct DailyRun {
    who: DreggIdentity,
    day: DailyDescent,
    scene: Scene,
    world: WorldCell,
    genesis: TurnReceipt,
    genesis_state: Vec<u64>,
    steps: Vec<StepReceipt>,
    character: Character,
    hardcore: bool,
}

impl DailyRun {
    /// The player driving this run.
    pub fn who(&self) -> &DreggIdentity {
        &self.who
    }
    /// The day's world spec (title / warden HP / depth / seed / win condition).
    pub fn day(&self) -> &DailyDescent {
        &self.day
    }
    /// The live persistent character (level / XP / class / dead getters).
    pub fn character(&self) -> &Character {
        &self.character
    }
    /// The character's current persistable sheet (what a save carries forward).
    pub fn sheet(&self) -> CharacterSheet {
        self.character.sheet()
    }
    /// The current passage ("room") name, or `None` if the run has ended.
    pub fn current_room(&self) -> Option<String> {
        let idx = self.world.read_passage()?;
        self.scene.passages.get(idx).map(|p| p.name.to_string())
    }
    /// Read a committed narrative var off the day's cell (hp / warden_hp / depth / gold / …).
    pub fn read_var(&self, name: &str) -> u64 {
        self.world.read_var(name)
    }
    /// Whether the run has ended (won at the hoard, or lost in the defeat room, or turned back).
    pub fn is_ended(&self) -> bool {
        self.world.read_passage().is_none()
    }
    /// Whether the run reached the WIN (ended holding the hoard).
    pub fn is_won(&self) -> bool {
        self.is_ended() && self.read_var("gold") == HOARD_GOLD
    }
    /// Whether the (hardcore) character has perished on this run.
    pub fn is_dead(&self) -> bool {
        self.character.is_dead()
    }
    /// How deep the run reached (the committed `depth` counter — the survived-depth signal).
    pub fn depth(&self) -> u64 {
        self.read_var("depth")
    }
    /// The number of real verified turns so far (genesis + committed steps).
    pub fn turns(&self) -> usize {
        1 + self.steps.len()
    }
    /// The recorded playthrough (genesis + committed steps) — the input to replay-verify + submit.
    pub fn playthrough(&self) -> Playthrough {
        Playthrough {
            genesis: self.genesis.clone(),
            genesis_state: self.genesis_state.clone(),
            steps: self.steps.clone(),
        }
    }

    /// **The run's final committed fingerprint** — the `turn_hash` of the last landed turn (for a
    /// won run, the run-ending seize turn), or the genesis hash if no move committed. This is the
    /// 32-byte commitment [`DailyDescentOffering::settle`] anchors on the deployed node chain: the
    /// un-retconnable tip of the run's receipt chain.
    pub fn final_commitment(&self) -> [u8; 32] {
        self.steps
            .last()
            .map(|s| s.receipt.turn_hash)
            .unwrap_or(self.genesis.turn_hash)
    }

    /// The world/domain label the run's turns commit under — becomes the node event topic when the
    /// run is settled (the day's stable `daily-descent-{sid}` scene id).
    pub fn domain(&self) -> String {
        self.scene.meta.id.to_string()
    }
}

/// **The daily descent offering** — a stateless factory over a [`CharacterStore`]. Each
/// [`open`](Self::open) verifies today's beacon, draws the day's world, deploys a fresh live
/// run, and loads the player's persistent character. Additive: it reuses the same [`Character`] /
/// [`CharacterStore`] the Keep's [`AdventurerOffering`](crate::character::AdventurerOffering) does.
pub struct DailyDescentOffering<S: CharacterStore> {
    store: S,
    hardcore: bool,
    /// **Where a settled run's commitment is anchored.** [`NodeTarget::Local`] (the default) keeps
    /// everything in-process — [`settle`](Self::settle) is a local no-op (nothing leaves the
    /// process). A [`NodeTarget::Federation`] (e.g. from [`NodeTarget::from_env`], reading
    /// `DREGG_NODE_URL`) makes [`settle`](Self::settle) anchor a won run's 32-byte commitment on
    /// the deployed node chain. This target is used ONLY at settle time; PLAY ([`advance`](Self::advance))
    /// is always Local (private / fast) regardless — the world-cell it drives never routes.
    settle_target: NodeTarget,
}

impl<S: CharacterStore> DailyDescentOffering<S> {
    /// A hardcore daily-descent offering over `store` (permadeath ON — the flagship default: a
    /// defeat PERISHES the character, un-undoable, so the leaderboard's "I survived" is real).
    /// The settle target defaults to [`NodeTarget::Local`]: play is private + fast and a settle is
    /// an in-process no-op until a node is opted in via [`with_node_target`](Self::with_node_target).
    pub fn new(store: S) -> Self {
        DailyDescentOffering {
            store,
            hardcore: true,
            settle_target: NodeTarget::Local,
        }
    }

    /// A daily-descent offering with an explicit hardcore setting (`false` → a defeat ends the run
    /// but does not perish the character — for a softer ladder). Settle target defaults to Local.
    pub fn with_hardcore(store: S, hardcore: bool) -> Self {
        DailyDescentOffering {
            store,
            hardcore,
            settle_target: NodeTarget::Local,
        }
    }

    /// **Opt this offering into verifiable settlement on a chosen [`NodeTarget`].** By default a
    /// daily-descent offering settles `Local` (a no-op; play is entirely private + in-process). Pass
    /// a [`NodeTarget::Federation`] (e.g. from [`NodeTarget::from_env`], reading `DREGG_NODE_URL`)
    /// to make [`settle`](Self::settle) anchor a won run's commitment on the deployed node chain.
    /// PLAY is unaffected: [`advance`](Self::advance) always runs on a Local world-cell — private,
    /// fast, no network — and only the opt-in [`settle`](Self::settle) touches the node.
    pub fn with_node_target(mut self, target: NodeTarget) -> Self {
        self.settle_target = target;
        self
    }

    /// Whether this offering will actually anchor a settle off-process (a [`NodeTarget::Federation`]
    /// was opted in) vs. the private-only Local default.
    pub fn settles_to_a_node(&self) -> bool {
        self.settle_target.is_federation()
    }

    /// Borrow the underlying character store (e.g. to check whether a player is returning).
    pub fn store(&self) -> &S {
        &self.store
    }

    /// **Open a run of today's descent for `who`** — VERIFY the beacon, draw the day's world,
    /// deploy the day's cell + run genesis, and LOAD the player's persistent character (a fresh
    /// one for a new player). The beacon is verified here: a beacon that does not verify yields no
    /// run (fail-closed — you cannot open a forged day).
    pub fn open(
        &self,
        who: DreggIdentity,
        beacon: &DailyBeacon,
    ) -> Result<DailyRun, OfferingError> {
        let seed = beacon
            .seed()
            .map_err(|e| OfferingError::Deploy(format!("beacon did not verify: {e:?}")))?;
        self.open_from_seed(who, seed)
    }

    /// **Open a run from an already-derived daily seed** — the beacon-free path (e.g. the seed came
    /// from a verified beacon elsewhere, or a test fixture). Draws + deploys the same day's world.
    pub fn open_from_seed(
        &self,
        who: DreggIdentity,
        seed: CommittedSeed,
    ) -> Result<DailyRun, OfferingError> {
        let day = daily_scene(&seed);
        let scene = parse(&day.source, "daily-descent.scene")
            .map_err(|e| OfferingError::Deploy(e.to_string()))?;
        let world = WorldCell::deploy(&scene, DAILY_DEPLOY_SEED)
            .map_err(|e| OfferingError::Deploy(e.to_string()))?;
        // Drive genesis (the gate's entry effects: hp=50, warden_hp=WHP), then hold the cell.
        let driver =
            Driver::start(world, &scene).map_err(|e| OfferingError::Deploy(e.to_string()))?;
        let genesis = driver.genesis().cloned().unwrap_or_default();
        let genesis_state = driver.playthrough().genesis_state;
        let (world, _no_steps) = driver.finish();

        let character = Character::open_from_store(who.clone(), &self.store);

        Ok(DailyRun {
            who,
            day,
            scene,
            world,
            genesis,
            genesis_state,
            steps: Vec::new(),
            character,
            hardcore: self.hardcore,
        })
    }

    /// **Advance the run by one real turn — earn / perish on a real outcome.** Applies choice
    /// `choice_index` at the current room as ONE cap-bounded turn: a legal move lands a real
    /// [`TurnReceipt`] (recorded); an illegal/ineligible one is a real executor refusal that
    /// commits nothing (anti-ghost). On a landed qualifying outcome the character EARNS XP (a real
    /// gated character turn); on a landed FALL in a hardcore run the character PERISHES (a real
    /// `WriteOnce`-final death). A refused move earns/perishes NOTHING.
    pub fn advance(&self, run: &mut DailyRun, choice_index: usize) -> Outcome {
        let Some(room) = run.current_room() else {
            return Outcome::Refused("the descent has already ended".to_string());
        };
        let Some(choice) = nth_choice(&run.scene, &room, choice_index) else {
            return Outcome::Refused("that move is not on the current ballot".to_string());
        };

        match run.world.apply_choice(&room, choice_index, &choice) {
            Ok(receipt) => {
                run.steps.push(StepReceipt {
                    passage: room.clone(),
                    choice_index,
                    receipt: receipt.clone(),
                    state: run.world.snapshot(),
                    decision_commitment: None,
                });
                // Bind real dungeon outcomes to the character (a real gated character turn).
                self.reward_or_perish(run, &room, choice_index);
                let ended = run.world.read_passage().is_none();
                Outcome::Landed { receipt, ended }
            }
            // ONE arm, two audiences — see `dungeon::advance`. A rules refusal comes back verbatim;
            // a machinery fault becomes the shared commit-failure sentence plus an operator log line.
            Err(e) => Outcome::Refused(crate::refusal::refuse_world_error(&e)),
        }
    }

    /// Bind a just-LANDED daily outcome to the character: XP for felling the warden / seizing the
    /// hoard, and (hardcore) a real perish on falling to the warden.
    fn reward_or_perish(&self, run: &DailyRun, room: &str, choice_index: usize) {
        match (room, choice_index) {
            ("gate", GATE_PRESS) => {
                let _ = run.character.grant_xp(XP_FELL_WARDEN);
            }
            ("hoard", HOARD_SEIZE) => {
                let _ = run.character.grant_xp(XP_SEIZE_HOARD);
            }
            ("gate", GATE_FALL) if run.hardcore => {
                // A hardcore defeat: the character PERISHES (WriteOnce-final, carries across days).
                let _ = run.character.perish();
            }
            _ => {}
        }
    }

    /// **Level the character up by one** — the existing `FieldGte(xp, threshold)`-gated turn
    /// (refused without the earned, possibly carried, XP).
    pub fn level_up(&self, run: &DailyRun) -> Result<TurnReceipt, WorldError> {
        run.character.level_up()
    }

    /// **Choose the character's class** (the one-time `WriteOnce` creation move).
    pub fn choose_class(&self, run: &DailyRun, class_id: u64) -> Result<TurnReceipt, WorldError> {
        run.character.choose_class(class_id)
    }

    /// **Save the run's character back to the store** — the carried level / XP / class / DEATH the
    /// next [`open`](Self::open) for the same identity RESUMES.
    pub fn save(&mut self, run: &DailyRun) {
        self.store.save(&run.who, run.character.sheet());
    }

    /// **Re-verify the run's committed chain by REPLAY** — re-drive a fresh identically-seeded day
    /// cell through the recorded choices and confirm it reproduces exactly the committed state
    /// chain. A forged / reordered / ineligible record fails. Both a WON run and a LOST run
    /// (downed into the defeat passage) are honest records that re-verify here.
    pub fn verify(&self, run: &DailyRun) -> crate::VerifyReport {
        let turns = run.turns();
        match verify_by_replay(
            WorldCell::deploy(&run.scene, DAILY_DEPLOY_SEED).expect("the day redeploys"),
            &run.scene,
            &run.playthrough(),
        ) {
            Ok(()) => crate::VerifyReport::ok(turns),
            Err(b) => crate::VerifyReport::broken(turns, b.to_string()),
        }
    }

    /// **Build the leaderboard [`Completion`]** for this run under `player` — today's world
    /// [`Universe`] id + the recorded playthrough + the honest turns-to-win. Submit it to a
    /// [`ugc_dregg::Registry`] that published [`DailyDescent::universe`]; the board accepts it ONLY
    /// if it re-executes to the WIN (an incomplete / lost / forged run is refused).
    pub fn completion(
        &self,
        run: &DailyRun,
        author: &str,
        player: &str,
    ) -> Result<Completion, PublishError> {
        let universe = run.day.universe(author)?;
        let play = run.playthrough();
        Ok(Completion {
            universe: universe.id(),
            player: player.to_string(),
            claimed_turns: play.steps.len(),
            play,
        })
    }

    /// **SETTLE a finished, won run — anchor its commitment on the deployed node chain.** This is
    /// the opt-in bridge from private/fast local play to verifiable settlement: a player who
    /// finishes a run worth keeping SETTLES it, landing the run's 32-byte fingerprint on the node
    /// (`EmitEvent`-of-commitment) so it becomes explorer-visible + archival-persisted, WITHOUT
    /// having submitted a single play turn to the node.
    ///
    /// Fail-closed, only a REAL win settles:
    /// 1. The run must have reached the WIN ([`DailyRun::is_won`]) — an unfinished / lost /
    ///    turned-back run is [`SettleError::NotWon`] and the node is not touched.
    /// 2. The run's committed chain is RE-VERIFIED by replay before anchoring — a forged / reordered
    ///    / tampered record is [`SettleError::Unverified`], refused before any anchor.
    /// 3. The verified win's [`final_commitment`](DailyRun::final_commitment) is routed through the
    ///    configured [`with_node_target`](Self::with_node_target): `Local` is an in-process no-op
    ///    ([`Settlement::landed`] is `None` — nothing left the process); [`NodeTarget::Federation`]
    ///    submits the commitment to the real node AND confirms it landed on the node's finalized
    ///    log, else [`SettleError::Federation`] (a rejected / unreachable / non-landing anchor).
    ///
    /// PLAY is untouched: [`advance`](Self::advance) never routes to the node — this is the sole
    /// path that anchors, and only on an operator-explicit finished win.
    pub fn settle(&self, run: &DailyRun) -> Result<Settlement, SettleError> {
        self.settle_linked(run, None)
    }

    /// **SETTLE a won run, LINKING it onto a previous settled run's commitment** — the chained
    /// analogue of [`settle`](Self::settle). A player who settles run after run builds a
    /// **linked settlement chain** on the node: each anchor names the previous anchor's
    /// commitment as its `prev`, so the sequence of a player's kept runs is itself un-retconnable
    /// (a chain-enforcing node — the deployed federation, or [`dregg_node_target::StubNode::linked`]
    /// in a test — REFUSES an anchor whose `prev` does not extend the head, fail-closed). Pass
    /// `prev = None` for the first anchor in a chain (identical to [`settle`](Self::settle)); pass
    /// `Some(previous.commitment)` to link onto the run settled before it.
    ///
    /// The same fail-closed gate as [`settle`](Self::settle): only a real finished
    /// ([`DailyRun::is_won`]), replay-verified win anchors, and the anchor must confirm-land on the
    /// node (`Local` is the in-process no-op). A broken link is the node's own
    /// [`SettleError::Federation`] refusal — the chain cannot be forked or spliced.
    pub fn settle_linked(
        &self,
        run: &DailyRun,
        prev: Option<[u8; 32]>,
    ) -> Result<Settlement, SettleError> {
        // 1. Only a REAL finished + WON run settles.
        if !run.is_won() {
            return Err(SettleError::NotWon);
        }
        // 2. Re-verify the run's committed chain by replay before anchoring (fail-closed).
        let report = self.verify(run);
        if !report.verified {
            return Err(SettleError::Unverified(report.detail));
        }
        // 3. The run's fingerprint = the final committed turn_hash (the run-ending seize turn).
        let commitment = run.final_commitment();
        // 4. Anchor it via the opted-in target: Local = no-op (Ok(None)); Federation = submit the
        //    EmitEvent-of-commitment turn (linked onto `prev` when chaining) + confirm it landed on
        //    the node's finalized log.
        let mut turn = SubmittedTurn::new(run.domain(), commitment);
        if let Some(prev) = prev {
            turn = turn.linked(prev);
        }
        let landed = self
            .settle_target
            .route(&turn)
            .map_err(|e| SettleError::Federation(e.to_string()))?;
        Ok(Settlement { commitment, landed })
    }
}

/// Why a run could not be **settled** (anchored on the node chain). Fail-closed: only a real
/// finished, replay-verified WIN anchors; anything else leaves the node untouched.
#[derive(Clone, Debug)]
pub enum SettleError {
    /// The run has not reached the WIN (unfinished, lost into the defeat room, or turned back at
    /// the door) — only a genuine finished win settles. The node is not touched.
    NotWon,
    /// The run reached the win state but its committed chain did NOT re-verify by replay (a forged
    /// / reordered / tampered record) — refused before any anchor. The node is not touched.
    Unverified(String),
    /// The run is a verified win but the opted-in [`NodeTarget::Federation`] node refused the anchor
    /// or could not confirm it landed (rejected / unreachable / non-landing submit). Fail-closed.
    Federation(String),
}

impl std::fmt::Display for SettleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SettleError::NotWon => write!(
                f,
                "the run is not a finished win — only a real won run settles"
            ),
            SettleError::Unverified(d) => {
                write!(f, "the run did not re-verify before settling: {d}")
            }
            SettleError::Federation(m) => write!(f, "settling to the node failed: {m}"),
        }
    }
}

impl std::error::Error for SettleError {}

/// The **receipt of a settled run** — the run's 32-byte fingerprint and, when a real federation
/// node anchored it, that node's landed identity for the commitment. On a `Local` settle target
/// [`landed`](Self::landed) is `None` (the player did not opt a node in; nothing was anchored
/// off-process — the run's fingerprint stays private).
#[derive(Clone, Debug)]
pub struct Settlement {
    /// The run's anchored 32-byte commitment (its [`DailyRun::final_commitment`]).
    pub commitment: [u8; 32],
    /// The node's landed identity for the commitment when it was anchored on a
    /// [`NodeTarget::Federation`] chain; `None` on a `Local` (private) settle.
    pub landed: Option<Landed>,
}

impl Settlement {
    /// Whether the run's commitment was actually anchored on a node (a Federation settle), vs a
    /// private Local no-op.
    pub fn anchored(&self) -> bool {
        self.landed.is_some()
    }
}

/// Pull the `n`-th `Choice` out of `passage` in the scene (the same ordering the compiler indexes
/// with, so `n` is exactly the index [`WorldCell::apply_choice`] checks the gate case against).
fn nth_choice(scene: &Scene, passage_name: &str, n: usize) -> Option<spween::Choice> {
    let passage = scene
        .passages
        .iter()
        .find(|p| p.name.as_str() == passage_name)?;
    passage
        .content
        .iter()
        .filter_map(|c| match c {
            spween::PassageContent::Choice(ch) => Some(ch),
            _ => None,
        })
        .nth(n)
        .cloned()
}
