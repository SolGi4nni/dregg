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
//!   no `rand`, no data-dependent draw count. Every enrichment below — the biome,
//!   the layout shape, each room's archetype, each encounter, each piece of loot —
//!   is one indexed draw at a *fixed* index, so the whole richer world is still a
//!   pure function of the committed seed, reproduced byte-for-byte by any verifier.
//!
//! A verifier who holds the committed seed re-derives the exact same draws and
//! re-generates the **byte-identical** dungeon ([`regenerate`]) — that is what
//! binds the committed seed to the dungeon.
//!
//! ## What is generated
//!
//! A connected graph of rooms (always a spanning **tree**, so the objective is
//! always reachable from `start`) drawn in one of four **layout shapes** (sprawl /
//! corridor / hub / branch), with reciprocal exits, **at least one gated exit**
//! (`requires item <key>`) isolating the objective, a placed key and win-item, and
//! an `objective:`. On top of that structural skeleton the generator draws a
//! **biome** (one of several themed content families) and, per room, an
//! **archetype** (a room type that colours its name), an **encounter** (themed
//! guardians beaten by a themed weapon, plus a boss guarding the gate), and
//! **loot** (treasure, healing draughts, and — where a biome hazard is in play —
//! tainted caches and their antidotes). A biome may also seed a lore-bearing **NPC**
//! and a **blessing spell** at a shrine. Every one of these is a first-class
//! `.dungeon` construct: the emitted text parses and validates through the shipped
//! `attested_dm::parse_dungeon` / `validate` with zero errors (see the tests).
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
//! - Generation is **structurally faithful and content-rich but not infinite**: the
//!   biomes, archetypes, encounters, and loot are drawn from finite curated tables.
//!   The guarantee is the pipeline (committed seed -> verified draws -> valid,
//!   *varied* dungeon), not an unbounded content library — a new table entry is a
//!   one-line addition that every seed can then draw.

use dregg_dice::{
    DrawStream, EvidenceKind, RandomnessEvidence, RandomnessRequest, RandomnessSource,
};

pub use dregg_dice::{self, Deterministic, Seed};

/// The drand-beacon → daily-seed wire: today's dungeon seed from a real threshold
/// public-randomness beacon (unpredictable-until-revealed, identical world-wide, verifiable
/// by re-derivation). See [`beacon::DailyBeacon`].
pub mod beacon;

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
/// available exit directions: every layout shape here keeps the max room degree
/// `<= 6` (a spanning tree over `<= 7` nodes — including the star/hub shape, whose
/// centre reaches degree `n - 1 <= 6`).
pub const MAX_ROOMS: usize = 7;

// Per-room draw layout (indices, relative to the room's base):
const R_ADJ: u32 = 0; // name adjective
const R_NOUN: u32 = 1; // name noun
const R_PARENT: u32 = 2; // which earlier room this attaches to (layout-shaped)
const R_CHILD_DIR: u32 = 3; // this room's exit direction back to the parent
const R_PARENT_DIR: u32 = 4; // the parent's exit direction to this room
const R_DESC: u32 = 5; // description variant
const R_ARCH: u32 = 6; // room archetype (naming style + role)
const R_MONSTER: u32 = 7; // which encounter (or none) stands in this room
const R_LOOT: u32 = 8; // which loot slot (or none) lies in this room
const ROOM_STRIDE: u32 = 9;

const IDX_COUNT: u32 = 0; // number of rooms
const IDX_THEME: u32 = 1; // whole-dungeon biome
const IDX_LAYOUT: u32 = 2; // layout shape (sprawl / corridor / hub / branch)
const IDX_HAZARD: u32 = 3; // whether this biome's hazard (poison + antidote) is live
const ROOMS_BASE: u32 = 4;

const IDX_KEY_ROOM: u32 = ROOMS_BASE + (MAX_ROOMS as u32) * ROOM_STRIDE; // where the key lies
const IDX_WIN_ROOM: u32 = IDX_KEY_ROOM + 1; // where the win-item lies
const IDX_WEAPON_ROOM: u32 = IDX_KEY_ROOM + 2; // where the themed weapon lies
const IDX_NPC_ON: u32 = IDX_KEY_ROOM + 3; // whether a lore NPC is placed
const IDX_NPC_ROOM: u32 = IDX_KEY_ROOM + 4; // which room the NPC stands in
const IDX_SHRINE_ON: u32 = IDX_KEY_ROOM + 5; // whether a blessing shrine is placed
const IDX_SHRINE_ROOM: u32 = IDX_KEY_ROOM + 6; // which room the shrine sits in
const IDX_BOSS: u32 = IDX_KEY_ROOM + 7; // the boss's stat variant

/// The number of indexed draws a dungeon generation consumes. Fixed regardless of
/// the drawn room count, biome, layout, or which encounters/loot land, so it can be
/// bound into the [`RandomnessRequest`] before the seed exists and committed by the
/// transcript. Unused room-slot / feature indices are still part of the committed
/// transcript.
pub const DRAW_COUNT: u32 = IDX_BOSS + 1;

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
    // `Deterministic::seed` verifies the context carried BY the evidence, but it
    // cannot know which context this application committed to. Bind that outer
    // application invariant here; otherwise a generator can choose a favorable
    // context after the committed seed is known and still produce self-consistent
    // evidence for the same request.
    if !matches!(
        &evidence.source,
        EvidenceKind::Deterministic { context } if context == seed.as_bytes()
    ) {
        return false;
    }
    // Pure verifier: re-derive the seed + check the transcript commitment.
    let Ok(verified) = Deterministic::seed(&req, evidence) else {
        return false;
    };
    let stream = DrawStream::new(verified, req.draw_count);
    let (source, _) = build_dungeon(&stream);
    source == claimed_source
}

// ─────────────────────────────────────────────────────────────────────────────
// Content tables — the biomes and their encounter / loot families.
// ─────────────────────────────────────────────────────────────────────────────

const DIRECTIONS: [&str; 6] = ["north", "south", "east", "west", "up", "down"];

/// Generic room ROLES, layered over each biome's own nouns to widen the space of
/// distinct room *types* a name can express (a "Barnacled Reliquary", a "Ticking
/// Guardroom"). Independent of the biome, so every biome draws from all of them.
const ARCH_ROLES: [&str; 10] = [
    "Antechamber",
    "Gallery",
    "Crypt",
    "Armory",
    "Guardroom",
    "Reliquary",
    "Landing",
    "Vestibule",
    "Concourse",
    "Sanctuary",
];

/// One themed guardian: beaten with the biome's weapon (a `hostile` block).
struct Monster {
    /// Bare-word id used as the `hostile` name and to derive its victory flag.
    id: &'static str,
    victory: &'static str,
    death: &'static str,
}

/// The biome's boss — an HP-combat foe (`combat` block) guarding the gated approach.
struct Boss {
    id: &'static str,
    hp: i64,
    attack: i64,
    weapon_damage: i64,
    victory: &'static str,
    hit: &'static str,
    flail: &'static str,
}

/// A themed content family: names, encounters, loot, hazard, lore, and a blessing.
struct Theme {
    name: &'static str,
    /// A short place-word used in some archetype naming styles ("… of the Deep").
    biome: &'static str,
    adjectives: &'static [&'static str],
    nouns: &'static [&'static str],
    descriptions: &'static [&'static str],
    key_item: &'static str,
    win_item: &'static str,
    win_room_hint: &'static str,

    /// The weapon that fells this biome's guardians and boss (always placed).
    weapon: &'static str,
    monsters: &'static [Monster],
    boss: Boss,

    /// Two flavour treasures (inert loot).
    treasures: [&'static str; 2],
    /// A healing draught (a `heal` consumable).
    potion: &'static str,
    potion_heal: i64,
    potion_flavor: &'static str,

    /// The biome hazard: a timed poison status, a tainted cache that inflicts it,
    /// and an antidote that cures it (all live only when the hazard is drawn on).
    hazard_status: &'static str,
    hazard_mag: i64,
    hazard_dur: i64,
    trap_item: &'static str,
    trap_flavor: &'static str,
    antidote_item: &'static str,
    antidote_flavor: &'static str,

    /// A lore NPC (placed on its own draw).
    npc_id: &'static str,
    npc_name: &'static str,
    npc_about: &'static str,
    lore_topic: &'static str,
    lore_reveal: &'static str,

    /// A blessing spell learned at a shrine (placed on its own draw).
    blessing: &'static str,
    blessing_flag: &'static str,
    blessing_flavor: &'static str,
}

const THEMES: [Theme; 6] = [
    Theme {
        name: "The Sunken Vault",
        biome: "the Deep",
        adjectives: &[
            "Drowned",
            "Salt-Worn",
            "Tidal",
            "Barnacled",
            "Silt-Black",
            "Weeping",
            "Brine-Cold",
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
            "A drowned stair spirals down into water too still to trust.",
            "Chains hang from a flooded ceiling, weeping rust into the murk.",
        ],
        key_item: "brass_key",
        win_item: "fen_heart",
        win_room_hint: "Sanctum",
        weapon: "warden_gaff",
        monsters: &[
            Monster {
                id: "silt_wraith",
                victory: "The gaff's hook parts the wraith like weed; it sinks and is gone.",
                death: "Cold hands close over your mouth and the water takes you.",
            },
            Monster {
                id: "drowned_thrall",
                victory: "You pin the thrall to the flooded floor; it stops thrashing.",
                death: "The thrall drags you under before you can draw breath.",
            },
            Monster {
                id: "gulper_eel",
                victory: "One clean stroke and the eel's coils go slack in the dark.",
                death: "Jaws wide as a doorway close, and there is only the black water.",
            },
        ],
        boss: Boss {
            id: "the_tide_warden",
            hp: 10,
            attack: 3,
            weapon_damage: 4,
            victory: "The Tide-Warden's lantern gutters out; the gate before it swings free.",
            hit: "The gaff bites deep and the Warden reels, spilling brine.",
            flail: "Your strike glances off a carapace of barnacle and salt.",
        },
        treasures: ["pearl_string", "drowned_crown"],
        potion: "kelp_tonic",
        potion_heal: 5,
        potion_flavor: "The bitter kelp tonic steadies you; the ache of cold recedes.",
        hazard_status: "brine_rot",
        hazard_mag: 2,
        hazard_dur: 6,
        trap_item: "tainted_reliquary",
        trap_flavor: "The reliquary breaks open on foul water; brine-rot creeps into your wounds.",
        antidote_item: "warden_salve",
        antidote_flavor: "The salve stings, then soothes; the rot loosens its grip.",
        npc_id: "ferryman",
        npc_name: "The Ferryman",
        npc_about: "a silt-grey boatman who has poled these flooded halls longer than memory",
        lore_topic: "vault",
        lore_reveal: "He tells of the Warden who drowned the vault rather than yield its heart.",
        blessing: "wardlight",
        blessing_flag: "warded",
        blessing_flavor: "A pale ward settles over you; the cold water no longer bites so deep.",
    },
    Theme {
        name: "The Clockwork Orchard",
        biome: "the Works",
        adjectives: &[
            "Rusted", "Ticking", "Brass", "Seized", "Wound", "Gilded", "Sprung",
        ],
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
            "Brass leaves litter a mechanical grove that has not budded in an age.",
            "A pendulum the size of a bell swings once, slow, then holds its breath.",
        ],
        key_item: "winding_key",
        win_item: "orrery_core",
        win_room_hint: "Escapement",
        weapon: "gear_flail",
        monsters: &[
            Monster {
                id: "clockwork_hound",
                victory: "The flail fouls the hound's gears; it winds down with a groan.",
                death: "Brass jaws close on your leg and do not stop turning.",
            },
            Monster {
                id: "brass_sentinel",
                victory: "You jam the flail into its escapement; the sentinel seizes mid-stride.",
                death: "The sentinel's fist comes around like a striking hammer.",
            },
            Monster {
                id: "wire_swarm",
                victory: "The flail scatters the swarm into a rain of dead springs.",
                death: "A thousand wire wings close over you at once.",
            },
        ],
        boss: Boss {
            id: "the_great_escapement",
            hp: 12,
            attack: 3,
            weapon_damage: 4,
            victory: "The Great Escapement shudders, unwinds, and falls still; the way opens.",
            hit: "A tooth of the flail catches a cog and the whole mechanism screams.",
            flail: "Your blow rings off a governor-wheel and does nothing.",
        },
        treasures: ["mainspring", "gilded_cog"],
        potion: "oil_of_ease",
        potion_heal: 5,
        potion_flavor: "The warm oil loosens every stiff joint; you move easier.",
        hazard_status: "clockwork_bind",
        hazard_mag: 2,
        hazard_dur: 6,
        trap_item: "seized_governor",
        trap_flavor: "The governor snaps shut on your hand; a creeping stiffness sets in.",
        antidote_item: "solvent_flask",
        antidote_flavor: "The solvent eats the rust from your joints; you flex free.",
        npc_id: "keeper",
        npc_name: "The Orchard-Keeper",
        npc_about: "a half-wound automaton who still tends a garden of dead brass",
        lore_topic: "core",
        lore_reveal: "It speaks of the Orrery-Core that once turned every tree in time.",
        blessing: "truetime",
        blessing_flag: "in_time",
        blessing_flavor: "For a moment you move in time with the works; the gears part for you.",
    },
    Theme {
        name: "The Ember Observatory",
        biome: "the Ash",
        adjectives: &[
            "Ashen",
            "Sun-Cracked",
            "Cinder",
            "Glass-Domed",
            "Smouldering",
            "Star-Burnt",
            "Kiln-Hot",
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
            "Heat shimmers over a floor of fused glass and grey cinder.",
            "A ring of black mirrors holds the last red light of a dead furnace.",
        ],
        key_item: "sun_sigil",
        win_item: "ember_lens",
        win_room_hint: "Oculus",
        weapon: "cinder_brand",
        monsters: &[
            Monster {
                id: "ash_revenant",
                victory: "The brand's fire outshines the revenant; it crumbles to grey powder.",
                death: "Ash pours into your lungs and the light goes out.",
            },
            Monster {
                id: "glass_golem",
                victory: "You shatter the golem's smoked-glass core with a single burning blow.",
                death: "A fist of fused glass catches you full in the chest.",
            },
            Monster {
                id: "ember_moth",
                victory: "The brand draws the moths in and burns them from the air.",
                death: "The moths settle over you, and everywhere they land, you burn.",
            },
        ],
        boss: Boss {
            id: "the_kiln_priest",
            hp: 11,
            attack: 4,
            weapon_damage: 4,
            victory: "The Kiln-Priest's fire answers to your brand and gutters; the oculus clears.",
            hit: "Your brand meets the Priest's and the whole rotunda flares white.",
            flail: "The Priest turns your fire aside with a wave of one ashen hand.",
        },
        treasures: ["sunstone", "astrolabe"],
        potion: "cooling_draught",
        potion_heal: 5,
        potion_flavor: "The draught is cold as deep water; the burning eases.",
        hazard_status: "cinderburn",
        hazard_mag: 3,
        hazard_dur: 5,
        trap_item: "live_coal_cache",
        trap_flavor: "The cache spills live coals across your hands; cinderburn takes hold.",
        antidote_item: "aloe_balm",
        antidote_flavor: "The green balm draws the heat from your skin; the burning stops.",
        npc_id: "astronomer",
        npc_name: "The Last Astronomer",
        npc_about: "a soot-blind stargazer who still charts a sky she can no longer see",
        lore_topic: "lens",
        lore_reveal: "She tells how the Ember-Lens caught a falling star and never let it go.",
        blessing: "starward",
        blessing_flag: "star_marked",
        blessing_flavor: "A cool star-mark settles on your brow; the heat gives you room.",
    },
    Theme {
        name: "The Venom Warren",
        biome: "the Warren",
        adjectives: &[
            "Sporing",
            "Web-Hung",
            "Damp",
            "Fungal",
            "Chittering",
            "Root-Bound",
            "Spore-Choked",
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
            "The walls breathe faintly, slick with a warm and living damp.",
            "Egg-sacs the size of lanterns glow a sick green along the passage.",
        ],
        key_item: "chitin_key",
        win_item: "brood_pearl",
        win_room_hint: "Queen's Hollow",
        weapon: "thorn_spear",
        monsters: &[
            Monster {
                id: "spore_hulk",
                victory: "The spear finds the hulk's soft core; it deflates in a gust of spores.",
                death: "The hulk bursts, and you breathe in a lungful of glittering death.",
            },
            Monster {
                id: "web_lurker",
                victory: "You spear the lurker before it drops; it curls and is still.",
                death: "Silk whips tight around your throat from above.",
            },
            Monster {
                id: "root_crawler",
                victory: "The spear pins the crawler to the wall it climbed from.",
                death: "Roots that were legs wrap you and pull you into the wall.",
            },
        ],
        boss: Boss {
            id: "the_brood_matron",
            hp: 13,
            attack: 3,
            weapon_damage: 4,
            victory: "The Brood-Matron shudders on the spear and folds her legs; the hollow opens.",
            hit: "The thorn-spear sinks between the Matron's plates and she recoils.",
            flail: "Your thrust skids off her chitin and finds only spore-dust.",
        },
        treasures: ["amber_bead", "silk_shroud"],
        potion: "milk_cap",
        potion_heal: 4,
        potion_flavor: "The pale cap is bitter but clean; strength returns to your limbs.",
        hazard_status: "spore_sick",
        hazard_mag: 2,
        hazard_dur: 7,
        trap_item: "burst_puffball",
        trap_flavor: "The puffball bursts in your face; a green sickness fogs your sight.",
        antidote_item: "charcoal_lozenge",
        antidote_flavor: "The charcoal draws the spores from your blood; your head clears.",
        npc_id: "myconid",
        npc_name: "The Old Myconid",
        npc_about: "a slow fungal elder rooted at a crossing of the warren's tunnels",
        lore_topic: "pearl",
        lore_reveal: "In spore-scent it tells of the Brood-Pearl the Matron guards at her heart.",
        blessing: "spore_ward",
        blessing_flag: "spore_warded",
        blessing_flavor: "A film of clean spores sheathes you; the warren's rot slides away.",
    },
    Theme {
        name: "The Frost Cathedral",
        biome: "the Rime",
        adjectives: &[
            "Rimed",
            "Glacial",
            "Hoarfrost",
            "Ice-Bound",
            "Frozen",
            "Snow-Blind",
            "Crystalline",
        ],
        nouns: &[
            "Nave",
            "Transept",
            "Reliquary",
            "Bell-Tower",
            "Crypt",
            "Cloister",
            "Font-Hall",
        ],
        descriptions: &[
            "Frost has fused the pews to the floor; your breath hangs and does not fall.",
            "Icicles the length of spears depend from a vaulted ceiling of blue ice.",
            "A frozen font holds a candle-flame trapped mid-flicker in the ice.",
            "Stained glass has iced over from within, its saints blurred to pale smears.",
            "Snow drifts through a shattered rose-window across a silent nave.",
            "Every footfall cracks a skin of new ice over older, deeper cold.",
        ],
        key_item: "frost_censer",
        win_item: "winter_relic",
        win_room_hint: "High Altar",
        weapon: "iron_maul",
        monsters: &[
            Monster {
                id: "rime_ghoul",
                victory: "The maul shatters the ghoul's frozen frame into blue shards.",
                death: "Frost-cold fingers close on your heart and it stutters and stops.",
            },
            Monster {
                id: "ice_gargoyle",
                victory: "One heavy swing and the gargoyle cracks from wing to root.",
                death: "The gargoyle drops from the vault and folds you into the floor.",
            },
            Monster {
                id: "hollow_choir",
                victory: "The maul's ring drowns the choir's song; the frozen singers still.",
                death: "The choir's cold hymn slows your blood until it will not move.",
            },
        ],
        boss: Boss {
            id: "the_frozen_bishop",
            hp: 12,
            attack: 4,
            weapon_damage: 4,
            victory: "The Frozen Bishop breaks like an icicle underfoot; the altar stands clear.",
            hit: "The maul lands and a web of cracks races through the Bishop's rime.",
            flail: "Your swing rebounds off a robe of solid ice.",
        },
        treasures: ["silver_thurible", "frozen_psalter"],
        potion: "warming_mead",
        potion_heal: 5,
        potion_flavor: "The mead is a coal in your chest; feeling floods back to your hands.",
        hazard_status: "deep_chill",
        hazard_mag: 2,
        hazard_dur: 6,
        trap_item: "cracked_font",
        trap_flavor: "The font cracks and douses you in melt-water; a deep chill sets into your bones.",
        antidote_item: "ember_charm",
        antidote_flavor: "The charm glows faintly warm; the chill lifts from your limbs.",
        npc_id: "acolyte",
        npc_name: "The Frozen Acolyte",
        npc_about: "a novice knelt in prayer so long the ice has taken her for its own",
        lore_topic: "relic",
        lore_reveal: "Through cracked lips she tells of the Winter-Relic locked in the High Altar.",
        blessing: "hearthward",
        blessing_flag: "hearth_blessed",
        blessing_flavor: "A hearth-warmth kindles under your ribs; the cold keeps its distance.",
    },
    Theme {
        name: "The Obsidian Reach",
        biome: "the Reach",
        adjectives: &[
            "Glassblack",
            "Riven",
            "Molten",
            "Sulfur-Veined",
            "Basalt",
            "Scorched",
            "Fault-Split",
        ],
        nouns: &[
            "Chasm",
            "Forge",
            "Terrace",
            "Vent-Hall",
            "Bridge",
            "Foundry",
            "Overlook",
        ],
        descriptions: &[
            "Black glass underfoot throws back the red glow of a fissure far below.",
            "A river of dull magma crawls through a canyon of cooling basalt.",
            "Sulfur steams from a hundred cracks; the air tastes of struck matches.",
            "A bridge of fused obsidian arcs over a drop that breathes hot wind.",
            "Cooling lava has frozen into black waves along the foundry floor.",
            "Cinders drift upward here, against all sense, into a starless dark.",
        ],
        key_item: "basalt_seal",
        win_item: "heartforge",
        win_room_hint: "Deep Forge",
        weapon: "obsidian_axe",
        monsters: &[
            Monster {
                id: "magma_wight",
                victory: "The axe cleaves the wight and its glow bleeds out across the glass.",
                death: "A hand of living magma closes, and the heat is the last thing you feel.",
            },
            Monster {
                id: "cinder_hound",
                victory: "You split the hound to its coal-red core; it collapses into embers.",
                death: "The hound's breath washes over you like an open furnace door.",
            },
            Monster {
                id: "slag_brute",
                victory: "The obsidian axe shears through slag and the brute sloughs apart.",
                death: "The brute brings a fist of molten rock down where you stood.",
            },
        ],
        boss: Boss {
            id: "the_forge_tyrant",
            hp: 14,
            attack: 4,
            weapon_damage: 5,
            victory: "The Forge-Tyrant's fire goes black and cold; the deep forge lies open.",
            hit: "Obsidian bites molten iron and the Tyrant roars sparks to the ceiling.",
            flail: "Your axe rings off a hide of cooled slag and leaves no mark.",
        },
        treasures: ["fire_opal", "smith_signet"],
        potion: "slake_water",
        potion_heal: 6,
        potion_flavor: "The black water hisses down your throat and quenches the worst of it.",
        hazard_status: "searheat",
        hazard_mag: 3,
        hazard_dur: 5,
        trap_item: "unstable_vent",
        trap_flavor: "The vent blows scalding steam across you; sear-heat blisters your skin.",
        antidote_item: "slake_gel",
        antidote_flavor: "The cool gel seals the burns; the searing eases to a dull ache.",
        npc_id: "smith",
        npc_name: "The Ash-Smith",
        npc_about: "a soot-caked smith who still keeps one coal alive at a dead forge",
        lore_topic: "forge",
        lore_reveal: "Over the ember he tells of the Heartforge that first lit the Reach.",
        blessing: "fireward",
        blessing_flag: "fire_warded",
        blessing_flavor: "A skin of cool air wraps you; the Reach's heat parts around your steps.",
    },
];

/// The four layout shapes a dungeon's spanning tree can take. Each keeps every room
/// reachable from `start` and keeps the objective a leaf (its sole approach is the
/// gated edge), so the puzzle stays sound; they differ in the *shape* of the map.
#[derive(Clone, Copy)]
enum Layout {
    /// Each room attaches to a uniformly-drawn earlier room — an organic sprawl.
    Sprawl,
    /// Each room attaches to the previous one — a single winding corridor.
    Corridor,
    /// Every room attaches to `start` — a hub with radiating spokes.
    Hub,
    /// Each room attaches to `(i-1)/2` — a branching binary tree.
    Branch,
}

impl Layout {
    fn from_draw(d: usize) -> Layout {
        match d % 4 {
            0 => Layout::Sprawl,
            1 => Layout::Corridor,
            2 => Layout::Hub,
            _ => Layout::Branch,
        }
    }
    fn label(self) -> &'static str {
        match self {
            Layout::Sprawl => "sprawl",
            Layout::Corridor => "corridor",
            Layout::Hub => "hub",
            Layout::Branch => "branch",
        }
    }
}

/// Read a bounded draw at `index` in `0..n` (reject-free, unbiased). Panics only
/// on a programming error (index out of the fixed budget, or `n == 0`), never on
/// data — the budget is a compile-time constant and every `n` here is positive.
fn pick(stream: &DrawStream, index: u32, n: usize) -> usize {
    stream
        .draw_bounded(index, n as u64)
        .expect("index within DRAW_COUNT and n > 0") as usize
}

// ─────────────────────────────────────────────────────────────────────────────
// The generator proper — draws -> a room graph + content -> `.dungeon` text.
// ─────────────────────────────────────────────────────────────────────────────

/// A loot slot a room may draw. The eight-slot menu is fixed (three empty slots,
/// two treasures, a draught, a tainted cache, an antidote), so a single `R_LOOT`
/// draw selects a room's loot directly and reproducibly.
#[derive(Clone, Copy, PartialEq, Eq)]
enum LootSlot {
    Empty,
    Treasure0,
    Treasure1,
    Potion,
    Trap,
    Antidote,
}

fn loot_slot(draw: usize) -> LootSlot {
    match draw {
        0 | 1 | 2 => LootSlot::Empty,
        3 => LootSlot::Treasure0,
        4 => LootSlot::Treasure1,
        5 => LootSlot::Potion,
        6 => LootSlot::Trap,
        _ => LootSlot::Antidote,
    }
}
const LOOT_SLOTS: usize = 8;

fn build_dungeon(stream: &DrawStream) -> (String, usize) {
    let theme = &THEMES[pick(stream, IDX_THEME, THEMES.len())];
    let layout = Layout::from_draw(pick(stream, IDX_LAYOUT, 4));
    // The biome hazard (poison + tainted cache + antidote) is live 2 of 3 seeds.
    let hazard_on = pick(stream, IDX_HAZARD, 3) < 2;

    // Room count in [MIN_ROOMS, MAX_ROOMS].
    let span = MAX_ROOMS - MIN_ROOMS + 1;
    let n = MIN_ROOMS + pick(stream, IDX_COUNT, span);

    // Per-room data.
    let mut adj_idx = vec![0usize; n];
    let mut noun_idx = vec![0usize; n];
    let mut desc_idx = vec![0usize; n];
    let mut arch = vec![0usize; n];
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
        // Archetype: a value in 0..(3 * roles) — the high part selects one of
        // three naming styles, the low part selects the role word.
        arch[i] = pick(stream, base + R_ARCH, 3 * ARCH_ROLES.len());

        if i >= 1 {
            // Attach to an earlier room per the layout shape -> a spanning tree, so
            // every room is reachable from room 0 (the start) and the objective (the
            // deepest room) is always a leaf.
            let p = match layout {
                // The uniform draw is consumed in every layout (fixed transcript),
                // even where the shape ignores it, so the budget stays constant.
                Layout::Sprawl => pick(stream, base + R_PARENT, i),
                Layout::Corridor => {
                    let _ = pick(stream, base + R_PARENT, i);
                    i - 1
                }
                Layout::Hub => {
                    let _ = pick(stream, base + R_PARENT, i);
                    0
                }
                Layout::Branch => {
                    let _ = pick(stream, base + R_PARENT, i);
                    (i - 1) / 2
                }
            };
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
    // puzzle is genuinely solvable. Holds for every layout above (parent < i, so
    // the deepest room can have no children).
    let objective = (0..n).max_by_key(|&i| (depth[i], i)).unwrap();
    let obj_parent = parent[objective];

    // The non-objective rooms — all reachable without passing the gate.
    let non_obj: Vec<usize> = (0..n).filter(|&i| i != objective).collect();
    let key_room = non_obj[pick(stream, IDX_KEY_ROOM, non_obj.len())];
    let win_room = non_obj[pick(stream, IDX_WIN_ROOM, non_obj.len())];
    let weapon_room = non_obj[pick(stream, IDX_WEAPON_ROOM, non_obj.len())];

    // Find the parent's exit toward the objective — that is the gated approach.
    let gated_dir = exits[obj_parent]
        .iter()
        .find(|&&(_, to)| to == objective)
        .map(|&(d, _)| d)
        .expect("objective's parent has an exit to it");

    // ── Encounters ─────────────────────────────────────────────────────────────
    // A boss (HP combat) always guards the gated approach room. Regular guardians
    // (flag-based hostiles) stand in other rooms per each room's R_MONSTER draw.
    // Every guardian and the boss is beaten with the biome weapon (placed below).
    // monster_here[i] = Some(monster index) for a hostile in room i.
    let mut monster_here: Vec<Option<usize>> = vec![None; n];
    for i in 0..n {
        // Keep the start gentle; the boss owns the approach room.
        if i == 0 || i == obj_parent {
            continue;
        }
        let base = ROOMS_BASE + (i as u32) * ROOM_STRIDE;
        // Draw over monsters + 3 "empty" slots, so not every room has a fight.
        let m = pick(stream, base + R_MONSTER, theme.monsters.len() + 3);
        if m < theme.monsters.len() {
            monster_here[i] = Some(m);
        }
    }
    let any_hostile = monster_here.iter().any(Option::is_some);
    // Boss stat variant: a small draw nudges its attack so bosses differ per seed.
    let boss_attack = theme.boss.attack + pick(stream, IDX_BOSS, 3) as i64;

    // ── Loot ───────────────────────────────────────────────────────────────────
    // Per-room loot slots. Trap/antidote only mean anything when the hazard is on;
    // with it off they fall back to empty (the item is never declared, so the
    // world stays sound). Track which special items actually landed, so we declare
    // exactly the consumable rules whose items are placed (obtainable).
    let mut loot_here: Vec<LootSlot> = vec![LootSlot::Empty; n];
    let mut potion_placed = false;
    let mut trap_placed = false;
    let mut antidote_placed = false;
    for i in 0..n {
        let base = ROOMS_BASE + (i as u32) * ROOM_STRIDE;
        let mut slot = loot_slot(pick(stream, base + R_LOOT, LOOT_SLOTS));
        if !hazard_on && matches!(slot, LootSlot::Trap | LootSlot::Antidote) {
            slot = LootSlot::Empty;
        }
        match slot {
            LootSlot::Potion => potion_placed = true,
            LootSlot::Trap => trap_placed = true,
            LootSlot::Antidote => antidote_placed = true,
            _ => {}
        }
        loot_here[i] = slot;
    }

    // ── Optional features: a lore NPC and a blessing shrine ─────────────────────
    let npc_room = if pick(stream, IDX_NPC_ON, 3) == 0 {
        Some(non_obj[pick(stream, IDX_NPC_ROOM, non_obj.len())])
    } else {
        None
    };
    let shrine_room = if pick(stream, IDX_SHRINE_ON, 3) == 0 {
        Some(pick(stream, IDX_SHRINE_ROOM, n))
    } else {
        None
    };

    // ── Emit the `.dungeon` text ────────────────────────────────────────────────
    let mut out = String::new();
    out.push_str("# Generated by procgen-dregg from a committed verifiable seed.\n");
    out.push_str(
        "# The same seed yields this exact dungeon — a verifier re-generates it byte-for-byte.\n",
    );
    out.push_str(&format!(
        "# biome: {} | layout: {} | hazard: {}\n\n",
        theme.name,
        layout.label(),
        if hazard_on { "on" } else { "off" }
    ));
    out.push_str(&format!("name: {}\n", theme.name));
    out.push_str("player_hp: 20\n");
    out.push_str("start: room0\n");
    out.push_str(&format!(
        "objective: reach room{} holding {}\n",
        objective, theme.win_item
    ));
    if any_hostile {
        out.push_str(&format!("lose: slain -> \"{}\"\n", theme.monsters[0].death));
    }
    if hazard_on {
        out.push_str(&format!(
            "status {} poison {}\n",
            theme.hazard_status, theme.hazard_mag
        ));
    }
    out.push('\n');

    // Consumable rules — declared only for items that were actually placed, so
    // every `consumable`'s item is obtainable (the validator refuses otherwise).
    if potion_placed {
        out.push_str(&format!(
            "consumable {} use -> heal {} \"{}\"\n",
            theme.potion, theme.potion_heal, theme.potion_flavor
        ));
    }
    if trap_placed {
        out.push_str(&format!(
            "consumable {} use -> status {} {} \"{}\"\n",
            theme.trap_item, theme.hazard_status, theme.hazard_dur, theme.trap_flavor
        ));
    }
    if antidote_placed {
        out.push_str(&format!(
            "consumable {} use -> cure {} \"{}\"\n",
            theme.antidote_item, theme.hazard_status, theme.antidote_flavor
        ));
    }
    if potion_placed || trap_placed || antidote_placed {
        out.push('\n');
    }

    // Rooms (each: header + indented body).
    for i in 0..n {
        let display = room_display(theme, i, adj_idx[i], noun_idx[i], arch[i], objective);
        out.push_str(&format!("room room{} \"{}\"\n", i, display));
        out.push_str(&format!("  {}\n", theme.descriptions[desc_idx[i]]));

        // Items placed in this room (fixed order for a stable emission).
        let mut items: Vec<&str> = Vec::new();
        if i == key_room {
            items.push(theme.key_item);
        }
        if i == win_room {
            items.push(theme.win_item);
        }
        if i == weapon_room {
            items.push(theme.weapon);
        }
        match loot_here[i] {
            LootSlot::Treasure0 => items.push(theme.treasures[0]),
            LootSlot::Treasure1 => items.push(theme.treasures[1]),
            LootSlot::Potion => items.push(theme.potion),
            LootSlot::Trap => items.push(theme.trap_item),
            LootSlot::Antidote => items.push(theme.antidote_item),
            LootSlot::Empty => {}
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

    // Encounters — top-level blocks that reference their room by id.
    // The boss guarding the gated approach.
    let boss = &theme.boss;
    out.push_str(&format!(
        "combat {} in room{} hp {} attack {}\n",
        boss.id, obj_parent, boss.hp, boss_attack
    ));
    out.push_str(&format!(
        "  weapon {} damage {}\n",
        theme.weapon, boss.weapon_damage
    ));
    out.push_str("  unarmed 0\n");
    out.push_str(&format!("  victory flag {}_felled\n", boss.id));
    out.push_str(&format!("  victory \"{}\"\n", boss.victory));
    out.push_str(&format!("  hit \"{}\"\n", boss.hit));
    out.push_str(&format!("  flail \"{}\"\n", boss.flail));
    out.push('\n');

    // The regular guardians.
    for i in 0..n {
        if let Some(m) = monster_here[i] {
            let mon = &theme.monsters[m];
            out.push_str(&format!(
                "hostile {} in room{} defeated_by {}\n",
                mon.id, i, theme.weapon
            ));
            out.push_str(&format!("  victory flag felled_r{}\n", i));
            out.push_str(&format!("  victory \"{}\"\n", mon.victory));
            out.push_str("  death flag slain\n");
            out.push_str(&format!("  death \"{}\"\n", mon.death));
            out.push('\n');
        }
    }

    // The lore NPC.
    if let Some(r) = npc_room {
        out.push_str(&format!(
            "npc {} \"{}\" in room{}\n",
            theme.npc_id, theme.npc_name, r
        ));
        out.push_str(&format!("  about \"{}\"\n", theme.npc_about));
        out.push_str(&format!(
            "  topic {} -> reveals \"{}\"\n",
            theme.lore_topic, theme.lore_reveal
        ));
        out.push('\n');
    }

    // The blessing shrine (an innate spell castable in one room).
    if let Some(r) = shrine_room {
        out.push_str(&format!("spell {} innate\n", theme.blessing));
        out.push_str(&format!(
            "  in room{} -> buff {} \"{}\"\n",
            r, theme.blessing_flag, theme.blessing_flavor
        ));
        out.push('\n');
    }

    (out, n)
}

/// Pick a free direction index for a room, drawn over its currently-available
/// directions. The per-layout room-degree cap (`<= 6`, since the hub's centre
/// reaches `n - 1 <= 6` and every other shape stays well under) guarantees a free
/// direction always exists.
fn free_dir(stream: &DrawStream, index: u32, used: &[usize]) -> usize {
    let free: Vec<usize> = (0..DIRECTIONS.len())
        .filter(|d| !used.contains(d))
        .collect();
    debug_assert!(!free.is_empty(), "a room exceeded 6 exits");
    free[pick(stream, index, free.len())]
}

fn room_display(
    theme: &Theme,
    i: usize,
    adj: usize,
    noun: usize,
    arch: usize,
    objective: usize,
) -> String {
    if i == 0 {
        return format!("The {} Threshold", theme.adjectives[adj]);
    }
    if i == objective {
        return format!("The {}", theme.win_room_hint);
    }
    // The archetype draw selects both a role word and one of three naming styles,
    // so a room reads as one of many distinct types: a biome noun, a generic role,
    // or a role placed within the biome ("The Crypt of the Deep").
    let role = ARCH_ROLES[arch % ARCH_ROLES.len()];
    match arch / ARCH_ROLES.len() {
        0 => format!("The {} {}", theme.adjectives[adj], theme.nouns[noun]),
        1 => format!("The {} {}", theme.adjectives[adj], role),
        _ => format!("The {} of {}", role, theme.biome),
    }
}

#[cfg(test)]
mod adversarial_tests {
    use super::*;

    #[test]
    fn evidence_context_must_equal_the_committed_seed() {
        let committed = CommittedSeed::from_bytes([0x11; 32]);
        let attacker_context = [0x22; 32];
        let req = dungeon_request(&committed);
        let forged_evidence = Deterministic {
            context: attacker_context,
        }
        .evidence(&req);
        let forged_seed = Deterministic::seed(&req, &forged_evidence)
            .expect("the inner evidence is self-consistent");
        let (forged_source, _) = build_dungeon(&DrawStream::new(forged_seed, req.draw_count));

        assert!(
            !verify_generation(&committed, &forged_evidence, &forged_source),
            "self-consistent evidence under an uncommitted context must be refused"
        );
        let honest = generate(&committed);
        assert!(verify_generation(
            &committed,
            &honest.evidence,
            &honest.source
        ));
    }
}
