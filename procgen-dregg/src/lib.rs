//! # procgen-dregg — provably-fair procedural dungeon generation
//!
//! A dungeon generated from a **committed, verifiable seed**: the same seed yields
//! the same dungeon, provably, and a new fair dungeon every day. The pipeline is
//!
//! ```text
//!   committed seed  ->  dregg-dice RandomnessRequest  ->  a VERIFIED DrawStream
//!                   ->  a deterministic dungeon graph  ->  a VALID `.dungeon` source
//! ```
//!
//! ## Why it is provably fair
//!
//! Randomness is the real [`dregg_dice`] machinery — never `rand`:
//!
//! - The committed seed is folded into a [`RandomnessRequest`]. Its
//!   [`RandomnessRequest::commitment`] is the receipt-shaped value an engine would
//!   publish *before* the dungeon exists, binding the whole generation context.
//! - The seed is obtained through the source's **pure verifier**
//!   ([`RandomnessSource::seed`]): a producer emits evidence, the verifier
//!   re-derives the seed and checks the transcript commitment. Producer and
//!   verifier agree, so no one can grind by swapping in a favourable seed.
//! - Every draw is an entry of the [`DrawStream`] — the **reject-free, unbiased**
//!   bounded mapping ([`DrawStream::draw_bounded`]), with a fixed [`DRAW_COUNT`]
//!   bound up-front and committed by the transcript. No ad-hoc rejection sampling,
//!   no `rand`, no data-dependent draw count.
//!
//! A verifier who holds the committed seed re-derives the exact same draws and
//! re-generates the **byte-identical** dungeon ([`regenerate`]) — that is what
//! binds the committed seed to the dungeon.
//!
//! ## What is generated
//!
//! A connected graph of rooms (a random spanning tree, so the objective is always
//! reachable from `start`), with reciprocal exits, **at least one gated exit**
//! (`requires item <key>`), a placed key and win-item, and an `objective:`. The
//! emitted text is a first-class `.dungeon` source: it parses and validates
//! through the shipped `attested_dm::parse_dungeon` / `validate` (see the tests).
//!
//! ## Honest scope
//!
//! - **Fairness of the *seed itself* rests on the seed being a committed / beacon
//!   value**, not on this generator. With [`daily_seed`] the seed is derived from
//!   an epoch commitment you supply; supply a real public beacon output (drand via
//!   [`dregg_dice::DrandBeacon`]) and the *unpredictability* is a threshold-beacon
//!   guarantee. The [`Deterministic`] source used here gives **reproducibility and
//!   binding**, not unpredictability — whoever knows the committed value knows the
//!   dungeon. That is the correct property for a daily seed everyone can re-verify.
//! - Generation is **structurally faithful but content-light**: themed room names
//!   and descriptions, one gated puzzle, a reachable objective. Richer generation —
//!   NPCs, spells, multi-room combat, difficulty scaling, themed loot — is future
//!   work; the pipeline (committed seed -> verified draws -> valid dungeon) is the
//!   deliverable, not a large content library.

use dregg_dice::{DrawStream, RandomnessEvidence, RandomnessRequest, RandomnessSource};

pub use dregg_dice::{self, Deterministic, Seed};

/// Domain tag folded into a committed seed's `game_binding`, so a procgen draw
/// stream can never collide with any other `dregg-dice` consumer's stream.
pub const DOMAIN_PROCGEN: &[u8] = b"procgen-dregg/dungeon/v1";

/// Domain tag for deriving a daily procgen seed from a committed epoch value.
pub const DOMAIN_DAILY_SEED: &[u8] = b"procgen-dregg/daily-seed/v1";

/// The purpose tag distinguishing procgen draws from other subsystems' draws.
pub const EVENT_KIND: &str = "procgen/dungeon";

// ─────────────────────────────────────────────────────────────────────────────
// Draw budget — FIXED up-front, bound into the EventId + transcript commitment.
// ─────────────────────────────────────────────────────────────────────────────

/// Fewest rooms a generated dungeon has (always includes `start`).
pub const MIN_ROOMS: usize = 4;
/// Most rooms a generated dungeon has. Capped so no room needs more than the six
/// available exit directions (a spanning tree over <= 7 nodes has max degree 6).
pub const MAX_ROOMS: usize = 7;

// Per-room draw layout (indices, relative to the room's base):
const R_ADJ: u32 = 0; // name adjective
const R_NOUN: u32 = 1; // name noun
const R_PARENT: u32 = 2; // which earlier room this attaches to
const R_CHILD_DIR: u32 = 3; // this room's exit direction back to the parent
const R_PARENT_DIR: u32 = 4; // the parent's exit direction to this room
const R_DESC: u32 = 5; // description variant
const ROOM_STRIDE: u32 = 6;

const IDX_COUNT: u32 = 0; // number of rooms
const IDX_THEME: u32 = 1; // whole-dungeon theme
const ROOMS_BASE: u32 = 2;
const IDX_KEY_ROOM: u32 = ROOMS_BASE + (MAX_ROOMS as u32) * ROOM_STRIDE; // where the key lies
const IDX_WIN_ROOM: u32 = IDX_KEY_ROOM + 1; // where the win-item lies

/// The number of indexed draws a dungeon generation consumes. Fixed regardless of
/// the drawn room count, so it can be bound into the [`RandomnessRequest`] before
/// the seed exists and committed by the transcript. Unused room-slot indices are
/// still part of the committed transcript.
pub const DRAW_COUNT: u32 = IDX_WIN_ROOM + 1;

// ─────────────────────────────────────────────────────────────────────────────
// Committed seed.
// ─────────────────────────────────────────────────────────────────────────────

/// A committed 32-byte value that seeds a dungeon. This is the fairness anchor:
/// published / committed *before* the dungeon is generated (ideally a public
/// beacon output). The generator and any verifier both start from this value and
/// arrive at byte-identical output.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct CommittedSeed([u8; 32]);

impl CommittedSeed {
    /// Wrap a committed 32-byte value (a beacon output, an epoch commitment, a
    /// published nonce) as a dungeon seed.
    pub fn from_bytes(bytes: [u8; 32]) -> CommittedSeed {
        CommittedSeed(bytes)
    }

    /// The raw committed bytes.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

/// Derive a **daily** committed seed from a committed epoch value (a beacon
/// output, a day's published root, …). The seed is a domain-separated hash of the
/// epoch commitment, so a fresh, fair dungeon falls out of each new epoch — and
/// everyone who sees the epoch commitment derives the identical seed.
///
/// Fairness rests on `epoch_commitment` being a genuinely committed / beacon
/// value; this function only binds it into the procgen domain.
pub fn daily_seed(epoch_commitment: &[u8; 32]) -> CommittedSeed {
    let mut h = blake3_domain(DOMAIN_DAILY_SEED);
    h.update(epoch_commitment);
    CommittedSeed(*h.finalize().as_bytes())
}

fn blake3_domain(tag: &[u8]) -> blake3::Hasher {
    // Match dregg-dice's length-prefixed domain absorption discipline so tags of
    // different lengths cannot alias.
    let mut h = blake3::Hasher::new();
    h.update(&(tag.len() as u64).to_le_bytes());
    h.update(tag);
    h
}

// ─────────────────────────────────────────────────────────────────────────────
// The verifiable-randomness pipeline: committed seed -> verified DrawStream.
// ─────────────────────────────────────────────────────────────────────────────

/// The [`RandomnessRequest`] that binds a committed seed to a dungeon generation.
/// Its [`RandomnessRequest::commitment`] is the value an engine publishes before
/// the dungeon exists.
pub fn dungeon_request(seed: &CommittedSeed) -> RandomnessRequest {
    // game_binding = domain tag ++ committed seed, so this stream is unique to
    // procgen and to this committed value.
    let mut game_binding = Vec::with_capacity(DOMAIN_PROCGEN.len() + 32);
    game_binding.extend_from_slice(DOMAIN_PROCGEN);
    game_binding.extend_from_slice(seed.as_bytes());
    RandomnessRequest {
        game_binding,
        seq: 0,
        // The committed seed also anchors the pre-state, so nothing outside the
        // seed can move the draws.
        pre_state_root: *seed.as_bytes(),
        action_hash: [0u8; 32],
        event_kind: EVENT_KIND.to_string(),
        draw_count: DRAW_COUNT,
    }
}

/// Build the verified [`DrawStream`] for a committed seed by going through the
/// full `dregg-dice` source: a producer emits evidence, and the **pure verifier**
/// re-derives the seed and checks the transcript commitment. The returned stream
/// is the one every verifier reconstructs.
pub fn verified_stream(
    seed: &CommittedSeed,
) -> (RandomnessRequest, RandomnessEvidence, DrawStream) {
    let req = dungeon_request(seed);
    let source = Deterministic {
        context: *seed.as_bytes(),
    };
    let evidence = source.evidence(&req);
    // The trust surface: re-derive + verify. A tampered evidence / draw count
    // would fail here rather than silently producing a different dungeon.
    let verified = Deterministic::seed(&req, &evidence)
        .expect("Deterministic source's own evidence must verify");
    let stream = DrawStream::new(verified, req.draw_count);
    (req, evidence, stream)
}

// ─────────────────────────────────────────────────────────────────────────────
// The generated dungeon.
// ─────────────────────────────────────────────────────────────────────────────

/// A generated dungeon and the evidence binding it to its committed seed.
#[derive(Clone, Debug)]
pub struct GeneratedDungeon {
    /// The emitted `.dungeon` source — parses + validates through `attested_dm`.
    pub source: String,
    /// The committed seed this was generated from.
    pub seed: CommittedSeed,
    /// The request whose `commitment()` an engine publishes before generation.
    pub request: RandomnessRequest,
    /// The randomness evidence a verifier checks to re-derive the seed.
    pub evidence: RandomnessEvidence,
    /// The number of rooms actually placed.
    pub room_count: usize,
}

impl GeneratedDungeon {
    /// The receipt-shaped commitment binding the whole generation context — the
    /// value published before the dungeon exists.
    pub fn request_commitment(&self) -> [u8; 32] {
        self.request.commitment()
    }

    /// The transcript commitment over the seed and every draw. Any change to the
    /// seed or the draw count moves this value.
    pub fn transcript_commitment(&self) -> [u8; 32] {
        self.evidence.draw_transcript_commitment
    }
}

/// Generate a dungeon from a committed seed. Deterministic and reproducible: the
/// same seed always yields the byte-identical [`GeneratedDungeon::source`].
pub fn generate(seed: &CommittedSeed) -> GeneratedDungeon {
    let (request, evidence, stream) = verified_stream(seed);
    let (source, room_count) = build_dungeon(&stream);
    GeneratedDungeon {
        source,
        seed: *seed,
        request,
        evidence,
        room_count,
    }
}

/// Re-generate a dungeon's `.dungeon` source from its committed seed alone. A
/// verifier calls this and compares byte-for-byte against a published dungeon: an
/// exact match proves the dungeon is the honest output of the committed seed.
pub fn regenerate(seed: &CommittedSeed) -> String {
    generate(seed).source
}

/// Verify that `claimed_source` is the honest dungeon for `seed`: re-derive the
/// seed through the pure `dregg-dice` verifier from `evidence`, re-generate, and
/// compare byte-for-byte.
pub fn verify_generation(
    seed: &CommittedSeed,
    evidence: &RandomnessEvidence,
    claimed_source: &str,
) -> bool {
    let req = dungeon_request(seed);
    // Pure verifier: re-derive the seed + check the transcript commitment.
    let Ok(verified) = Deterministic::seed(&req, evidence) else {
        return false;
    };
    let stream = DrawStream::new(verified, req.draw_count);
    let (source, _) = build_dungeon(&stream);
    source == claimed_source
}

// ─────────────────────────────────────────────────────────────────────────────
// The generator proper — draws -> a room graph -> `.dungeon` text.
// ─────────────────────────────────────────────────────────────────────────────

const DIRECTIONS: [&str; 6] = ["north", "south", "east", "west", "up", "down"];

/// Themed content pools. Structural generation is theme-independent; the theme
/// only colours names + descriptions.
struct Theme {
    name: &'static str,
    adjectives: &'static [&'static str],
    nouns: &'static [&'static str],
    descriptions: &'static [&'static str],
    key_item: &'static str,
    win_item: &'static str,
    win_room_hint: &'static str,
}

const THEMES: [Theme; 4] = [
    Theme {
        name: "The Sunken Vault",
        adjectives: &[
            "Drowned",
            "Salt-Worn",
            "Tidal",
            "Barnacled",
            "Silt-Black",
            "Weeping",
        ],
        nouns: &[
            "Causeway",
            "Gatehouse",
            "Cistern",
            "Undercroft",
            "Grotto",
            "Reliquary",
            "Sluice",
        ],
        descriptions: &[
            "Cold fen-water laps at the stones; a warden's lantern still hangs from an iron hook.",
            "A roofless hall choked with sedge, its floor a slick of green tide-weed.",
            "Drip and echo; something pale drifts in the black water below.",
            "Salt has eaten the carvings to blank ghosts along the walls.",
        ],
        key_item: "brass_key",
        win_item: "fen_heart",
        win_room_hint: "Sanctum",
    },
    Theme {
        name: "The Clockwork Orchard",
        adjectives: &["Rusted", "Ticking", "Brass", "Seized", "Wound", "Gilded"],
        nouns: &[
            "Gallery",
            "Espalier",
            "Gearworks",
            "Arbor",
            "Pendulum-Hall",
            "Aviary",
            "Winding-Room",
        ],
        descriptions: &[
            "Trees of hammered copper stand in dead rows; a great gear lies canted across the aisle.",
            "The air smells of oil and cold metal; something ticks, slow, out of sight.",
            "Automaton birds hang frozen mid-song from wire branches overhead.",
            "A floor of interlocking cogs, most of them stopped, one still faintly turning.",
        ],
        key_item: "winding_key",
        win_item: "orrery_core",
        win_room_hint: "Escapement",
    },
    Theme {
        name: "The Ember Observatory",
        adjectives: &[
            "Ashen",
            "Sun-Cracked",
            "Cinder",
            "Glass-Domed",
            "Smouldering",
            "Star-Burnt",
        ],
        nouns: &[
            "Rotunda",
            "Stair",
            "Cupola",
            "Furnace-Room",
            "Lens-Hall",
            "Vault",
            "Balcony",
        ],
        descriptions: &[
            "Warm ash sifts from a cracked dome; the floor is warm underfoot.",
            "A great brass telescope points at a shuttered sky, its lens gone dark.",
            "Embers glow in a cold hearth that no one has tended in an age.",
            "Star-charts have burned to lace along the curving wall.",
        ],
        key_item: "sun_sigil",
        win_item: "ember_lens",
        win_room_hint: "Oculus",
    },
    Theme {
        name: "The Venom Warren",
        adjectives: &[
            "Sporing",
            "Web-Hung",
            "Damp",
            "Fungal",
            "Chittering",
            "Root-Bound",
        ],
        nouns: &[
            "Burrow",
            "Nest",
            "Hollow",
            "Spore-Hall",
            "Thornway",
            "Midden",
            "Gallery",
        ],
        descriptions: &[
            "Fat pale mushrooms crowd the walls; the air is thick and green and still.",
            "Silk hangs in grey ropes from a low ceiling; something skitters and is gone.",
            "Roots have broken the floor into a maze of damp black hollows.",
            "A carpet of spores puffs up at every step and drifts, glittering, in the dark.",
        ],
        key_item: "chitin_key",
        win_item: "brood_pearl",
        win_room_hint: "Queen's Hollow",
    },
];

/// Read a bounded draw at `index` in `0..n` (reject-free, unbiased). Panics only
/// on a programming error (index out of the fixed budget, or `n == 0`), never on
/// data — the budget is a compile-time constant and every `n` here is positive.
fn pick(stream: &DrawStream, index: u32, n: usize) -> usize {
    stream
        .draw_bounded(index, n as u64)
        .expect("index within DRAW_COUNT and n > 0") as usize
}

fn build_dungeon(stream: &DrawStream) -> (String, usize) {
    let theme = &THEMES[pick(stream, IDX_THEME, THEMES.len())];

    // Room count in [MIN_ROOMS, MAX_ROOMS].
    let span = MAX_ROOMS - MIN_ROOMS + 1;
    let n = MIN_ROOMS + pick(stream, IDX_COUNT, span);

    // Per-room data.
    let mut adj_idx = vec![0usize; n];
    let mut noun_idx = vec![0usize; n];
    let mut desc_idx = vec![0usize; n];
    // used_dirs[i] = the set of direction indices already taken by room i's exits.
    let mut used_dirs: Vec<Vec<usize>> = vec![Vec::new(); n];
    // parent[i] (for i >= 1) and the direction pair for the reciprocal exits.
    let mut parent = vec![0usize; n];
    // exits[i] = (dir_index, target_room) — this room's outgoing exit declarations.
    let mut exits: Vec<Vec<(usize, usize)>> = vec![Vec::new(); n];
    // depth[i] for objective selection.
    let mut depth = vec![0usize; n];

    for i in 0..n {
        let base = ROOMS_BASE + (i as u32) * ROOM_STRIDE;
        adj_idx[i] = pick(stream, base + R_ADJ, theme.adjectives.len());
        noun_idx[i] = pick(stream, base + R_NOUN, theme.nouns.len());
        desc_idx[i] = pick(stream, base + R_DESC, theme.descriptions.len());

        if i >= 1 {
            // Attach to a uniformly-drawn earlier room -> a random spanning tree,
            // so every room is reachable from room 0 (the start).
            let p = pick(stream, base + R_PARENT, i);
            parent[i] = p;
            depth[i] = depth[p] + 1;

            let child_dir = free_dir(stream, base + R_CHILD_DIR, &used_dirs[i]);
            used_dirs[i].push(child_dir);
            exits[i].push((child_dir, p));

            let parent_dir = free_dir(stream, base + R_PARENT_DIR, &used_dirs[p]);
            used_dirs[p].push(parent_dir);
            exits[p].push((parent_dir, i));
        }
    }

    // Objective = the deepest room (always a LEAF: nothing is deeper, so nothing
    // hangs below it). Gating its single approach edge isolates only the
    // objective, so every other room stays reachable without the key -> the
    // puzzle is genuinely solvable.
    let objective = (0..n).max_by_key(|&i| (depth[i], i)).unwrap();
    let obj_parent = parent[objective];

    // The non-objective rooms — all reachable without passing the gate.
    let non_obj: Vec<usize> = (0..n).filter(|&i| i != objective).collect();
    let key_room = non_obj[pick(stream, IDX_KEY_ROOM, non_obj.len())];
    let win_room = non_obj[pick(stream, IDX_WIN_ROOM, non_obj.len())];

    // Find the parent's exit toward the objective — that is the gated approach.
    let gated_dir = exits[obj_parent]
        .iter()
        .find(|&&(_, to)| to == objective)
        .map(|&(d, _)| d)
        .expect("objective's parent has an exit to it");

    // ── Emit the `.dungeon` text ──────────────────────────────────────────────
    let mut out = String::new();
    out.push_str("# Generated by procgen-dregg from a committed verifiable seed.\n");
    out.push_str(
        "# The same seed yields this exact dungeon — a verifier re-generates it byte-for-byte.\n\n",
    );
    out.push_str(&format!("name: {}\n", theme.name));
    out.push_str("start: room0\n");
    out.push_str(&format!(
        "objective: reach room{} holding {}\n\n",
        objective, theme.win_item
    ));

    for i in 0..n {
        let display = room_display(theme, i, adj_idx[i], noun_idx[i], objective);
        out.push_str(&format!("room room{} \"{}\"\n", i, display));
        out.push_str(&format!("  {}\n", theme.descriptions[desc_idx[i]]));

        // Items placed in this room.
        let mut items: Vec<&str> = Vec::new();
        if i == key_room {
            items.push(theme.key_item);
        }
        if i == win_room {
            items.push(theme.win_item);
        }
        if !items.is_empty() {
            out.push_str(&format!("  items: {}\n", items.join(", ")));
        }

        // Exits (sorted by direction index for a stable, readable emission).
        let mut es = exits[i].clone();
        es.sort_by_key(|&(d, _)| d);
        for (dir, to) in es {
            let gated = i == obj_parent && to == objective && dir == gated_dir;
            if gated {
                out.push_str(&format!(
                    "  exit {} -> room{} requires item {}\n",
                    DIRECTIONS[dir], to, theme.key_item
                ));
            } else {
                out.push_str(&format!("  exit {} -> room{}\n", DIRECTIONS[dir], to));
            }
        }
        out.push('\n');
    }

    (out, n)
}

/// Pick a free direction index for a room, drawn over its currently-available
/// directions. The room-degree cap (<= 6 for a spanning tree over <= 7 nodes)
/// guarantees a free direction always exists.
fn free_dir(stream: &DrawStream, index: u32, used: &[usize]) -> usize {
    let free: Vec<usize> = (0..DIRECTIONS.len())
        .filter(|d| !used.contains(d))
        .collect();
    debug_assert!(!free.is_empty(), "a room exceeded 6 exits");
    free[pick(stream, index, free.len())]
}

fn room_display(theme: &Theme, i: usize, adj: usize, noun: usize, objective: usize) -> String {
    if i == 0 {
        format!("The {} Threshold", theme.adjectives[adj])
    } else if i == objective {
        format!("The {}", theme.win_room_hint)
    } else {
        format!("The {} {}", theme.adjectives[adj], theme.nouns[noun])
    }
}
