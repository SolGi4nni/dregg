//! # `ugc-dregg` — a UGC registry + a NO-CHEAT verifiable leaderboard
//!
//! The platform flywheel. Authors **publish** universes; players **submit**
//! completions; the leaderboard accepts a completion ONLY if its recorded receipt
//! chain **verifies** — a stranger re-executes the same identically-seeded universe
//! with the submitted moves and it reaches the **WIN state**, and the chain links.
//! Leaderboards are therefore trustable **by construction**, not by honor.
//!
//! ## The two verbs
//!
//! * **PUBLISH** ([`Universe::authored`] / [`Universe::from_procgen`] →
//!   [`Registry::publish`]) — a universe is a *compiled spween world* (or a
//!   *committed procgen seed*, from which the same world regenerates byte-for-byte) +
//!   a name + an author. The registry is keyed by the **universe commitment**
//!   ([`UniverseId`]) — content-addressed, so the same universe has the same id.
//! * **SUBMIT** ([`Completion`] → [`Registry::submit`]) — a player submits a recorded
//!   [`Playthrough`](spween_dregg::Playthrough) (the ordered moves + their receipt
//!   chain) + a claimed turns-to-win. The board **verifies** it and only then
//!   accepts + ranks.
//!
//! ## The no-cheat tooth (why the board cannot be gamed)
//!
//! [`verify_completion`] is the whole guarantee, and it is spween-dregg's audited
//! re-verifier used verbatim:
//!
//! 1. **Re-execute.** Deploy a FRESH, identically-seeded world from the universe's
//!    scene and re-drive it through the submitted moves
//!    ([`verify`](spween_dregg::verify) = chain-linkage + `verify_by_replay`). A
//!    forged / edited / spliced move is **refused by the real executor on replay**,
//!    or diverges from the reproduced committed state. Either way it FAILS.
//! 2. **Require the WIN.** The replay must reach the universe's declared win state
//!    (the scene ENDED, plus any declared win-vars, e.g. `gold == 500`). An
//!    incomplete playthrough that never reaches the win is REJECTED.
//! 3. **Bind the result.** The claimed turns-to-win must equal the verified move
//!    count. A tampered result is REJECTED.
//!
//! Only a completion that passes all three is accepted and ranked (by turns). Anyone
//! can re-run [`verify_completion`] — or [`Registry::reverify_entry`] — against a
//! universe they reconstruct independently, and get the same verdict.
//!
//! ## Honest scope
//!
//! Verification is **O(N) replay** — a re-verifier re-executes every move. The
//! succinct light client (verify a win in time sub-linear in the playthrough) is a
//! separate, Lane-D-blocked workstream and is NOT claimed here. What also remains:
//! **author identity / signatures** (a universe carries an author *name*, not yet a
//! verified signing key), **persistence** (the [`Registry`] is in-memory), and
//! **anti-sybil** (nothing rate-limits or stakes a submission). The no-cheat property
//! — *a ranked completion provably reaches the win* — holds regardless of those.

use std::collections::BTreeMap;
use std::fmt;

use procgen_dregg::CommittedSeed;
use spween_dregg::{
    CompiledStory, Driver, PASSAGE_ENDED, PASSAGE_SLOT, Playthrough, Scene, VerifyBreak, WorldCell,
    WorldError, compile_scene, parse, verify,
};

/// Domain tag for the universe commitment (content address).
const DOMAIN_UNIVERSE_ID: &[u8] = b"ugc-dregg/universe-id/v1";
/// Domain tag for a completion id.
const DOMAIN_COMPLETION_ID: &[u8] = b"ugc-dregg/completion-id/v1";

// ═══════════════════════════════════════════════════════════════════════════════
// Universe — a content-addressed publishable world.
// ═══════════════════════════════════════════════════════════════════════════════

/// The **universe commitment** — a content address. The same universe (same scene
/// source + name + author) always hashes to the same id, so a re-publish is
/// idempotent and any party can recompute it.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UniverseId([u8; 32]);

impl UniverseId {
    /// The raw 32-byte commitment.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

impl fmt::Display for UniverseId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for b in &self.0[..8] {
            write!(f, "{b:02x}")?;
        }
        write!(f, "…")
    }
}

impl fmt::Debug for UniverseId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "UniverseId({self})")
    }
}

/// How a universe came to be — its provenance. Content-addressing means the WORLD is
/// the same regardless; provenance records where the world's scene came from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Provenance {
    /// An author wrote the spween scene directly.
    Authored,
    /// The scene was generated from a committed, verifiable procgen seed. Anyone can
    /// re-generate the byte-identical scene from this seed
    /// ([`Universe::regenerates_from_seed`]) — the seed→world binding is provable.
    Procgen {
        /// The committed 32-byte seed (a beacon output / a day's published root).
        committed_seed: [u8; 32],
    },
}

/// The win condition of a universe. A completion "wins" iff, after replay, the scene
/// has **ENDED** and every declared `(var, value)` holds on the final committed state.
/// The scene-ended requirement alone already refuses an incomplete playthrough; the
/// var checks strengthen it (e.g. the hoard was actually seized: `gold == 500`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct WinCondition {
    /// Variable values that must hold on the final committed state to count as a win.
    pub vars: Vec<(String, u64)>,
}

impl WinCondition {
    /// The win requires only that the scene ENDED (reached a terminal `-> END`).
    pub fn ended() -> WinCondition {
        WinCondition { vars: Vec::new() }
    }

    /// The win requires the scene ENDED **and** the named vars hold.
    pub fn ended_with(vars: &[(&str, u64)]) -> WinCondition {
        WinCondition {
            vars: vars.iter().map(|(k, v)| (k.to_string(), *v)).collect(),
        }
    }
}

/// A **published universe** — a content-addressed, verifiable, winnable world.
#[derive(Clone)]
pub struct Universe {
    id: UniverseId,
    name: String,
    author: String,
    source: String,
    /// The deterministic deploy seed for the world-cell. Fixed per universe so a
    /// re-verifier deploys the identical world; the committed *state* the replay
    /// verifier compares is seed-independent, but the seed must match across
    /// record + replay, so it is pinned here.
    deploy_seed: u8,
    provenance: Provenance,
    win: WinCondition,
    /// The parsed scene (playable + verifiable).
    scene: Scene,
    /// Compiled var→slot map, for evaluating the win condition off a committed state
    /// vector without re-driving.
    var_slots: BTreeMap<String, usize>,
}

/// Why a universe could not be published (its scene is not a valid, deployable world).
#[derive(Clone, Debug)]
pub enum PublishError {
    /// The spween source did not parse.
    Parse(String),
    /// The scene did not compile to a world-cell (or deploy).
    Compile(String),
}

impl fmt::Display for PublishError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PublishError::Parse(e) => write!(f, "universe scene did not parse: {e}"),
            PublishError::Compile(e) => write!(f, "universe scene did not compile: {e}"),
        }
    }
}

impl std::error::Error for PublishError {}

impl Universe {
    /// **PUBLISH an authored universe** from spween DSL `source`. Parses + compiles it
    /// (a scene that does not deploy is rejected up front) and content-addresses it.
    pub fn authored(
        name: &str,
        author: &str,
        source: &str,
        win: WinCondition,
    ) -> Result<Universe, PublishError> {
        Self::build(name, author, source, 7, Provenance::Authored, win)
    }

    /// **PUBLISH a procgen universe** from a committed verifiable seed. The scene is
    /// generated deterministically from the seed through procgen-dregg's VERIFIED
    /// `dregg-dice` draw stream (never `rand`), and anyone can re-generate the
    /// byte-identical scene from the seed alone ([`Universe::regenerates_from_seed`]).
    /// The win is "seize the hoard" (`gold == 500`) — the generated world's objective.
    pub fn from_procgen(author: &str, seed: CommittedSeed) -> Result<Universe, PublishError> {
        let (source, title) = generate::scene_source(&seed);
        // A stable deploy seed derived from the committed seed.
        let deploy_seed = seed.as_bytes()[0];
        Self::build(
            &title,
            author,
            &source,
            deploy_seed,
            Provenance::Procgen {
                committed_seed: *seed.as_bytes(),
            },
            WinCondition::ended_with(&[("gold", 500)]),
        )
    }

    /// **PUBLISH the DAILY universe** for a committed epoch value — a fresh, fair,
    /// publishable dungeon that everyone who sees the epoch commitment derives
    /// identically (via procgen-dregg's [`daily_seed`](procgen_dregg::daily_seed)).
    pub fn daily(author: &str, epoch_commitment: &[u8; 32]) -> Result<Universe, PublishError> {
        Self::from_procgen(author, procgen_dregg::daily_seed(epoch_commitment))
    }

    fn build(
        name: &str,
        author: &str,
        source: &str,
        deploy_seed: u8,
        provenance: Provenance,
        win: WinCondition,
    ) -> Result<Universe, PublishError> {
        let scene = parse(source, &format!("{name}.scene"))
            .map_err(|e| PublishError::Parse(e.to_string()))?;
        // Compile up front: a scene that does not lower to a world-cell is not a
        // publishable universe. We keep the var→slot map for win evaluation.
        let compiled: CompiledStory =
            compile_scene(&scene).map_err(|e| PublishError::Compile(e.to_string()))?;
        // Deploy once to confirm it actually births a world (fail-closed on publish).
        WorldCell::deploy(&scene, deploy_seed).map_err(|e| PublishError::Compile(e.to_string()))?;

        let id = universe_id(name, author, source);
        Ok(Universe {
            id,
            name: name.to_string(),
            author: author.to_string(),
            source: source.to_string(),
            deploy_seed,
            provenance,
            win,
            scene,
            var_slots: compiled.var_slots,
        })
    }

    /// The universe commitment (content address / registry key).
    pub fn id(&self) -> UniverseId {
        self.id
    }
    /// The universe's display name.
    pub fn name(&self) -> &str {
        &self.name
    }
    /// The author (a name — signature identity is a named follow-up, see crate docs).
    pub fn author(&self) -> &str {
        &self.author
    }
    /// The spween DSL source of the world.
    pub fn source(&self) -> &str {
        &self.source
    }
    /// The provenance of the world's scene.
    pub fn provenance(&self) -> &Provenance {
        &self.provenance
    }
    /// The declared win condition.
    pub fn win(&self) -> &WinCondition {
        &self.win
    }

    /// **Re-generate check** for a procgen universe: does its scene regenerate
    /// byte-for-byte from its committed seed? Returns `true` for an honest procgen
    /// universe, `false` if the source was tampered away from its committed seed.
    /// (Always `false` for an [`Provenance::Authored`] universe — there is no seed.)
    pub fn regenerates_from_seed(&self) -> bool {
        match &self.provenance {
            Provenance::Procgen { committed_seed } => {
                let seed = CommittedSeed::from_bytes(*committed_seed);
                let (regen, _) = generate::scene_source(&seed);
                regen == self.source
            }
            Provenance::Authored => false,
        }
    }

    /// Deploy a FRESH, identically-seeded world for this universe (what a re-verifier
    /// re-executes against). Deterministic in the pinned deploy seed.
    fn fresh_world(&self) -> Result<WorldCell, WorldError> {
        WorldCell::deploy(&self.scene, self.deploy_seed)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Completion — a submitted, to-be-verified playthrough.
// ═══════════════════════════════════════════════════════════════════════════════

/// A **submitted completion**: which universe, who played it, the recorded
/// [`Playthrough`] (the ordered moves + their receipt chain), and the claimed
/// turns-to-win. Nothing here is trusted — the board re-verifies it.
#[derive(Clone, Debug)]
pub struct Completion {
    /// The universe this completion is for.
    pub universe: UniverseId,
    /// The player's name.
    pub player: String,
    /// The recorded playthrough (the un-retconnable receipt chain).
    pub play: Playthrough,
    /// The player's claimed turns-to-win (verified against the actual move count).
    pub claimed_turns: usize,
}

/// Why a completion was rejected. Every arm is a real refusal — the board is
/// no-cheat by construction.
#[derive(Clone, Debug)]
pub enum RejectReason {
    /// No such universe is registered.
    UnknownUniverse,
    /// The completion names a different universe than the one it was submitted to.
    WrongUniverse,
    /// A fresh world could not be deployed (should not happen for a published universe).
    Deploy(String),
    /// **The recorded receipt chain did not re-verify** — a forged/edited/spliced
    /// playthrough refused by the real executor on replay, or diverging from the
    /// reproduced committed state. This is the no-cheat tooth biting.
    FailedVerification(VerifyBreak),
    /// The playthrough re-verified, but it **did not reach the win state** (the scene
    /// did not end, or a declared win-var did not hold). An incomplete playthrough.
    DidNotWin,
    /// The playthrough won, but the **claimed result was tampered** — the claimed
    /// turns-to-win did not equal the verified move count.
    ResultMismatch {
        /// What the submitter claimed.
        claimed: usize,
        /// The verified move count.
        actual: usize,
    },
}

impl fmt::Display for RejectReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RejectReason::UnknownUniverse => write!(f, "no such universe is registered"),
            RejectReason::WrongUniverse => {
                write!(
                    f,
                    "completion is for a different universe than submitted to"
                )
            }
            RejectReason::Deploy(e) => write!(f, "could not deploy a fresh world: {e}"),
            RejectReason::FailedVerification(b) => {
                write!(f, "recorded playthrough failed re-verification: {b}")
            }
            RejectReason::DidNotWin => {
                write!(f, "playthrough re-verified but did not reach the win state")
            }
            RejectReason::ResultMismatch { claimed, actual } => write!(
                f,
                "tampered result: claimed {claimed} turns, verified {actual}"
            ),
        }
    }
}

impl std::error::Error for RejectReason {}

/// **THE NO-CHEAT VERIFIER** — the whole guarantee, usable independently of any
/// [`Registry`]. Anyone holding the (public) universe and a completion can call this
/// and get the authoritative verdict:
///
/// 1. re-execute the submitted moves against a FRESH identically-seeded world and
///    require the recorded receipt chain re-verifies ([`verify`]);
/// 2. require the replay reaches the universe's WIN state;
/// 3. require the claimed turns equal the verified move count.
///
/// On success returns the verified turns-to-win (the ranking key).
pub fn verify_completion(universe: &Universe, c: &Completion) -> Result<usize, RejectReason> {
    if c.universe != universe.id {
        return Err(RejectReason::WrongUniverse);
    }

    // (1) Re-execute: chain-linkage + replay against a fresh, identically-seeded world.
    let fresh = universe
        .fresh_world()
        .map_err(|e| RejectReason::Deploy(e.to_string()))?;
    verify(fresh, &universe.scene, &c.play).map_err(RejectReason::FailedVerification)?;

    // (2) Require the WIN. `verify` above guarantees the recorded states are the
    // faithful reproduced states, so evaluating the win off the final recorded state
    // is sound. An empty playthrough (no moves) can never have reached a terminal.
    let Some(last) = c.play.steps.last() else {
        return Err(RejectReason::DidNotWin);
    };
    if !reached_win(universe, &last.state) {
        return Err(RejectReason::DidNotWin);
    }

    // (3) Bind the claimed result to the verified move count.
    let actual = c.play.steps.len();
    if c.claimed_turns != actual {
        return Err(RejectReason::ResultMismatch {
            claimed: c.claimed_turns,
            actual,
        });
    }

    Ok(actual)
}

/// Evaluate the universe's win condition against a final committed state vector: the
/// scene must have ENDED and every declared win-var must hold.
fn reached_win(universe: &Universe, state: &[u64]) -> bool {
    let ended = state.get(PASSAGE_SLOT).is_some_and(|&p| p == PASSAGE_ENDED);
    if !ended {
        return false;
    }
    universe.win.vars.iter().all(|(name, want)| {
        universe
            .var_slots
            .get(name)
            .and_then(|&slot| state.get(slot))
            .is_some_and(|&got| got == *want)
    })
}

// ═══════════════════════════════════════════════════════════════════════════════
// The leaderboard registry.
// ═══════════════════════════════════════════════════════════════════════════════

/// One accepted, verified entry on a universe's leaderboard. It carries the recorded
/// playthrough so anyone can INDEPENDENTLY re-verify it later.
#[derive(Clone, Debug)]
pub struct Entry {
    /// The player's name.
    pub player: String,
    /// The verified turns-to-win (the rank key — lower is better).
    pub turns: usize,
    /// A content id for this completion (over the player + the receipt chain).
    pub completion_id: [u8; 32],
    /// The recorded playthrough — kept so [`Registry::reverify_entry`] (or any third
    /// party) can re-execute it from scratch.
    play: Playthrough,
}

impl Entry {
    /// The recorded playthrough behind this entry (for independent re-verification).
    pub fn playthrough(&self) -> &Playthrough {
        &self.play
    }
}

/// The outcome of an accepted submission.
#[derive(Clone, Debug)]
pub struct Accepted {
    /// The verified turns-to-win.
    pub turns: usize,
    /// The completion's content id.
    pub completion_id: [u8; 32],
    /// The entry's 1-based rank on the board after insertion.
    pub rank: usize,
}

/// The **UGC registry + leaderboards**. Universes are keyed by their content address;
/// each has a leaderboard of verified completions, ranked by turns-to-win.
#[derive(Default)]
pub struct Registry {
    universes: BTreeMap<UniverseId, Universe>,
    boards: BTreeMap<UniverseId, Vec<Entry>>,
}

impl Registry {
    /// A fresh, empty registry.
    pub fn new() -> Registry {
        Registry::default()
    }

    /// **PUBLISH** a universe. Idempotent by content address: re-publishing the same
    /// universe returns the same id and does not duplicate it. Returns the id.
    pub fn publish(&mut self, universe: Universe) -> UniverseId {
        let id = universe.id;
        self.universes.entry(id).or_insert(universe);
        self.boards.entry(id).or_default();
        id
    }

    /// Look up a published universe.
    pub fn universe(&self, id: UniverseId) -> Option<&Universe> {
        self.universes.get(&id)
    }

    /// Every published universe.
    pub fn universes(&self) -> impl Iterator<Item = &Universe> {
        self.universes.values()
    }

    /// **SUBMIT a completion.** The board re-verifies it ([`verify_completion`]) and
    /// ONLY on success accepts + ranks it. A forged / incomplete / result-tampered
    /// completion is REJECTED (nothing is added to the board).
    pub fn submit(&mut self, c: Completion) -> Result<Accepted, RejectReason> {
        let universe = self
            .universes
            .get(&c.universe)
            .ok_or(RejectReason::UnknownUniverse)?;

        // The no-cheat gate. Only a verified win, with a truthful result, gets past.
        let turns = verify_completion(universe, &c)?;

        let completion_id = completion_id(&c.player, &c.play);
        let entry = Entry {
            player: c.player,
            turns,
            completion_id,
            play: c.play,
        };

        let board = self.boards.entry(c.universe).or_default();
        board.push(entry);
        // Rank by turns ascending; stable for equal turns (insertion order preserved).
        board.sort_by_key(|e| e.turns);

        let rank = board
            .iter()
            .position(|e| e.completion_id == completion_id)
            .map(|i| i + 1)
            .unwrap_or(board.len());
        Ok(Accepted {
            turns,
            completion_id,
            rank,
        })
    }

    /// The **leaderboard** for a universe — accepted entries ranked by turns-to-win
    /// (lower first). Every entry here provably reaches the win.
    pub fn leaderboard(&self, id: UniverseId) -> Vec<&Entry> {
        self.boards
            .get(&id)
            .map(|b| b.iter().collect())
            .unwrap_or_default()
    }

    /// **INDEPENDENTLY re-verify** a leaderboard entry: re-execute its recorded
    /// playthrough from scratch against a fresh world and confirm it still verifies to
    /// the claimed win in the claimed turns. Anyone can do this; a tampered board
    /// cannot survive it.
    pub fn reverify_entry(
        &self,
        id: UniverseId,
        completion_id: &[u8; 32],
    ) -> Result<usize, RejectReason> {
        let universe = self
            .universes
            .get(&id)
            .ok_or(RejectReason::UnknownUniverse)?;
        let board = self.boards.get(&id).ok_or(RejectReason::UnknownUniverse)?;
        let entry = board
            .iter()
            .find(|e| &e.completion_id == completion_id)
            .ok_or(RejectReason::UnknownUniverse)?;
        let c = Completion {
            universe: id,
            player: entry.player.clone(),
            play: entry.play.clone(),
            claimed_turns: entry.turns,
        };
        verify_completion(universe, &c)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Recording helper — a player drives their OWN copy to produce a playthrough.
// ═══════════════════════════════════════════════════════════════════════════════

/// **Record a playthrough** by driving a fresh copy of `universe` through `moves`
/// (each `usize` is a choice index at the current passage). This is what a player runs
/// locally to produce the [`Playthrough`] they submit. The leaderboard does NOT trust
/// its output — it re-verifies it. A move refused by the real executor (an ineligible
/// pick) fails here with the executor's refusal.
pub fn record_playthrough(universe: &Universe, moves: &[usize]) -> Result<Playthrough, WorldError> {
    let world = WorldCell::deploy(&universe.scene, universe.deploy_seed)?;
    let mut driver = Driver::start(world, &universe.scene)?;
    for &m in moves {
        driver.advance(m)?;
    }
    Ok(driver.playthrough())
}

// ═══════════════════════════════════════════════════════════════════════════════
// Content addressing.
// ═══════════════════════════════════════════════════════════════════════════════

fn domain_hasher(tag: &[u8]) -> blake3::Hasher {
    let mut h = blake3::Hasher::new();
    h.update(&(tag.len() as u64).to_le_bytes());
    h.update(tag);
    h
}

fn field(h: &mut blake3::Hasher, bytes: &[u8]) {
    h.update(&(bytes.len() as u64).to_le_bytes());
    h.update(bytes);
}

/// The universe commitment: a length-prefixed hash of name ++ author ++ source, so
/// the same universe content-addresses to the same id.
fn universe_id(name: &str, author: &str, source: &str) -> UniverseId {
    let mut h = domain_hasher(DOMAIN_UNIVERSE_ID);
    field(&mut h, name.as_bytes());
    field(&mut h, author.as_bytes());
    field(&mut h, source.as_bytes());
    UniverseId(*h.finalize().as_bytes())
}

/// A completion id over the player + the whole receipt chain (each turn hash).
fn completion_id(player: &str, play: &Playthrough) -> [u8; 32] {
    let mut h = domain_hasher(DOMAIN_COMPLETION_ID);
    field(&mut h, player.as_bytes());
    for r in play.receipts() {
        h.update(&r.turn_hash);
    }
    *h.finalize().as_bytes()
}

// ═══════════════════════════════════════════════════════════════════════════════
// The procgen → playable spween world generator.
// ═══════════════════════════════════════════════════════════════════════════════

/// Generate a **playable, winnable spween world** deterministically from a committed
/// procgen seed, drawing every choice from procgen-dregg's VERIFIED `dregg-dice`
/// stream (its fairness; never `rand`). A verifier who holds the committed seed
/// re-derives the identical stream and re-generates the byte-identical scene — that is
/// what content-addresses a procgen universe to its seed.
///
/// The emitted world is a linear dungeon: room 0 holds the key (take it or leave it),
/// a chain of rooms leads to a gated descent (`{ has_key >= 1 }` — a REAL executor
/// tooth once compiled), and the final room's hoard (`gold += 500`) ends the scene.
/// So it is genuinely winnable, and only by holding the key — a real no-cheat puzzle.
mod generate {
    use procgen_dregg::{CommittedSeed, verified_stream};

    struct Theme {
        title: &'static str,
        key_item: &'static str,
        win_item: &'static str,
        descs: &'static [&'static str],
    }

    const THEMES: [Theme; 4] = [
        Theme {
            title: "The Sunken Vault",
            key_item: "brass_key",
            win_item: "fen_heart",
            descs: &[
                "Cold fen-water laps at the stones; a warden's lantern hangs from an iron hook.",
                "A roofless hall choked with sedge, its floor a slick of green tide-weed.",
                "Drip and echo; something pale drifts in the black water below.",
            ],
        },
        Theme {
            title: "The Clockwork Orchard",
            key_item: "winding_key",
            win_item: "orrery_core",
            descs: &[
                "Trees of hammered copper stand in dead rows; a great gear lies canted across the aisle.",
                "The air smells of oil and cold metal; something ticks, slow, out of sight.",
                "Automaton birds hang frozen mid-song from wire branches overhead.",
            ],
        },
        Theme {
            title: "The Ember Observatory",
            key_item: "sun_sigil",
            win_item: "ember_lens",
            descs: &[
                "Warm ash sifts from a cracked dome; the floor is warm underfoot.",
                "A great brass telescope points at a shuttered sky, its lens gone dark.",
                "Embers glow in a cold hearth that no one has tended in an age.",
            ],
        },
        Theme {
            title: "The Venom Warren",
            key_item: "chitin_key",
            win_item: "brood_pearl",
            descs: &[
                "Fat pale mushrooms crowd the walls; the air is thick and green and still.",
                "Silk hangs in grey ropes from a low ceiling; something skitters and is gone.",
                "Roots have broken the floor into a maze of damp black hollows.",
            ],
        },
    ];

    const MIN_ROOMS: usize = 4;
    const MAX_ROOMS: usize = 7;

    /// Emit the `.dungeon`-equivalent spween scene source + its title. Deterministic
    /// in the committed seed. Draw indices stay well under procgen's committed
    /// `DRAW_COUNT` (~46), so every draw is within the transcript-bound budget.
    pub(super) fn scene_source(seed: &CommittedSeed) -> (String, String) {
        // procgen's VERIFIED stream: a producer emits evidence, the pure verifier
        // re-derives the seed + checks the transcript commitment. Grinding is refused.
        let (_req, _ev, stream) = verified_stream(seed);
        let pick = |index: u32, n: usize| -> usize {
            stream
                .draw_bounded(index, n as u64)
                .expect("draw index within the committed budget and n > 0") as usize
        };

        let theme = &THEMES[pick(0, THEMES.len())];
        let span = MAX_ROOMS - MIN_ROOMS + 1;
        let n = MIN_ROOMS + pick(1, span);

        // A short hex tag of the seed for a unique scene id.
        let sid: String = seed.as_bytes()[..4]
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();

        // The gated room is the second-to-last; the last room holds the hoard.
        let gate = n - 2;
        let last = n - 1;

        let desc = |i: usize| theme.descs[pick(2 + i as u32, theme.descs.len())];

        let mut out = String::new();
        out.push_str(&format!(
            "---\nid: procgen-{sid}\ntitle: {}\nweight: 1\n---\n\n",
            theme.title
        ));

        for i in 0..n {
            out.push_str(&format!("=== room{i}\n\n{}\n\n", desc(i)));
            if i == 0 {
                // Take the key, or leave it — both step forward, but only the key opens the gate.
                out.push_str(&format!(
                    "* [Take the {key} and press on]\n  ~ has_key = 1\n  -> room1\n\n",
                    key = theme.key_item
                ));
                out.push_str("* [Press on empty-handed]\n  -> room1\n\n");
            } else if i == gate {
                // The gated descent — a REAL executor `FieldGte(has_key, 1)` tooth once compiled.
                out.push_str(&format!(
                    "* [Descend into the depths] {{ has_key >= 1 }}\n  ~ depth += 1\n  -> room{last}\n\n"
                ));
                out.push_str(&format!(
                    "* [Retreat the way you came]\n  -> room{}\n\n",
                    gate - 1
                ));
            } else if i == last {
                // Seize the hoard — the win: gold += 500 and the scene ENDS.
                out.push_str(&format!(
                    "* [Seize the {win} and escape]\n  ~ gold += 500\n  -> END\n\n",
                    win = theme.win_item
                ));
            } else {
                // A linear connecting room.
                out.push_str(&format!("* [Press onward]\n  -> room{}\n\n", i + 1));
            }
        }
        (out, theme.title.to_string())
    }
}
