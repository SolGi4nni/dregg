//! # game_api — THE ATTESTED DUNGEONS, playable over HTTP.
//!
//! A second lane on the dungeon-service (additive to `/narrate`): a real dungeon-crawler over a
//! REGISTRY of [`attested_dm::GameWorld`]s ([`attested_dm::sunken_vault`] and
//! [`attested_dm::bramble_keep`]), each played through one [`attested_dm::GameSession`].
//! `GET /game/list` enumerates the games; `POST /game/reset {"world":"<id>"}` opens a fresh
//! session over the chosen world (default `sunken-vault`). A local language model
//! (`gemma2:2b` via ollama) NARRATES
//! each room and action; the WORLD RESOLVES every move by [`attested_dm::resolve_action`]'s
//! deterministic rules. You cannot narrate through a locked door, take an absent item, pass
//! the Warden without the sword, or win without carrying the amulet to the gate.
//!
//! ## The AI narrates; the world resolves.
//!
//! Each turn: the free-text command is parsed into a *closed typed* [`attested_dm::GameAction`]
//! (`Move | Take | Use | Examine | Attack`), gemma2 narrates the moment atmospherically (its
//! prose carries NO authority), and the resolver decides. A legal move lands as ONE verified
//! chain turn ([`attested_dm::DungeonMaster::narrate_game_move`]) carrying its
//! [`attested_dm::GameBinding`]; a refused move leaves the world unchanged and lands no receipt
//! (the anti-ghost tooth). gemma2 may narrate the dark stair opening — the world says: barred,
//! it needs the lantern.
//!
//! ## What is REAL vs modeled (honest)
//!
//! * REAL and load-bearing: the WORLD RESOLUTION (a locked exit / absent item / unbeaten Warden
//!   is refused deterministically, regardless of prose), the CAP GATE (a `Take` is a
//!   cap-permitted grant on the dungeon's own item whitelist), and the HASH-CHAIN (every landed
//!   move is a prev-linked, injection-free, on-chain turn binding its typed action + room).
//! * REAL: the narration is a genuine `gemma2:2b` when ollama is reachable
//!   (`narratorKind: "model:gemma2:2b"`); else a deterministic scripted narrator.
//! * MODELED: the attestation's *authentic* leg is an in-tree fixture (`RecordedDm`), as in the
//!   `/narrate` lane. The receipt does not prove a real model produced the bytes; the resolver,
//!   the cap gate, and the chain are the real teeth.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Mutex;

use attested_dm::{
    bramble_keep, deepdark_mine, starfall_spire, sunken_vault, GameAction, GameSession, GameStatus,
    GameWorld, Gate, PlayResult, Proposal, Room, WorldCell,
};
use collective_choice::{
    CollectiveChoice, Decision, PollId, PollSpec, Tally, VoteEngine, VoteError, MAX_OPTIONS,
};
use http_serve::WebResponse;
use serde_json::{json, Value};

use crate::hosted::Hosted;

// ─────────────────────────────────────────────────────────────────────────────
// The game registry — the worlds the service can open. Additive: a new dungeon is one row.
// ─────────────────────────────────────────────────────────────────────────────

/// A registered dungeon: a stable id, a display name, a one-line blurb, the DM's theme (a
/// short flavor line the narrator is told so it narrates in-genre), and the world constructor.
pub struct GameDef {
    /// The stable url/id (`sunken-vault`, `bramble-keep`).
    pub id: &'static str,
    /// The display name (`The Sunken Vault`).
    pub name: &'static str,
    /// A one-line description for the picker.
    pub blurb: &'static str,
    /// The DM's theme — a short flavor line woven into the narration prompt so gemma2 narrates
    /// in this world's genre.
    pub theme: &'static str,
    /// The world constructor.
    pub ctor: fn() -> GameWorld,
}

/// The default world opened at boot and when `/game/reset` omits a `world` (so the committed
/// `run-vault.mjs`, which resets without a world, still gets the vault).
pub const DEFAULT_GAME: &str = "sunken-vault";

/// The available dungeons.
pub fn games() -> Vec<GameDef> {
    vec![
        GameDef {
            id: "sunken-vault",
            name: "The Sunken Vault",
            blurb: "A drowned dark-fantasy vault: light the dark stair, unlock the iron door, best the Warden, and carry the Drowned Amulet up to the gate.",
            theme: "THE SUNKEN VAULT, a drowned dark-fantasy dungeon of flooded halls, salt-rotted iron, and a Warden in ruined plate",
            ctor: sunken_vault,
        },
        GameDef {
            id: "bramble-keep",
            name: "Bramble Keep",
            blurb: "A thorn-cursed ruin: trade the Hedge-Witch for her silver sickle, cut the living thornwall, fell the Bramble Knight, and bear the Sunheart to open sky.",
            theme: "BRAMBLE KEEP, a thorn-cursed ruined keep strangled in living brambles, its curse bound to the Sunheart, walked by a Hedge-Witch and a Bramble Knight",
            ctor: bramble_keep,
        },
        GameDef {
            id: "starfall-spire",
            name: "The Starfall Spire",
            blurb: "A collapsing wizard's tower: read the grimoires, cast Light across the dark gallery and Mend the broken span, conjure the flare-blade to fell the Voidling, and set the fallen star back in its cradle.",
            theme: "THE STARFALL SPIRE, a collapsing wizard's tower of dark galleries, a broken star-span, a great orrery, and a Voidling of unlight — a place where words of power are read from grimoires and spoken aloud",
            ctor: starfall_spire,
        },
        GameDef {
            id: "deepdark-mine",
            name: "The Deepdark Mine",
            blurb: "A race against the dark: your lamp burns one oil per step, eleven pitch-black levels stand between you and the Deepheart, and you must gather the oil caches to climb back to daylight before the flame dies.",
            theme: "THE DEEPDARK MINE, a sunless abandoned mine of pitch-black drifts and flooded sumps, where a lamp burns down oil by oil and the dark keeps whatever it catches",
            ctor: deepdark_mine,
        },
    ]
}

/// The registered game with this id, if any.
pub fn find_game(id: &str) -> Option<GameDef> {
    games().into_iter().find(|g| g.id == id)
}

// ─────────────────────────────────────────────────────────────────────────────
// The narrator — a real gemma2 when reachable, else a deterministic scripted narrator.
// Either way the ACTION is parsed deterministically (the world resolves it); the model's
// only job is atmospheric prose, which has no authority over the outcome.
// ─────────────────────────────────────────────────────────────────────────────

/// The vault's dungeon-master narrator — the shared HOSTED model tier (Bedrock Claude/Nova →
/// Ollama), metered against the hard USD ceiling, with a deterministic scripted fallback when
/// the budget is exhausted or no hosted model is available.
#[derive(Clone)]
pub struct VaultNarrator {
    hosted: Hosted,
    /// The boot label (`model:<id>` or `scripted:VaultGm`).
    base_kind: String,
}

impl VaultNarrator {
    /// Wire a narrator around the shared hosted narrator.
    pub fn new(hosted: Hosted) -> VaultNarrator {
        let base_kind = hosted
            .base_model_kind()
            .unwrap_or_else(|| "scripted:VaultGm".to_string());
        VaultNarrator { hosted, base_kind }
    }

    /// The narrator kind at the mode level (before any per-turn fallback).
    pub fn base_kind(&self) -> String {
        self.base_kind.clone()
    }

    /// Narrate an already-resolved-into-typed [`GameAction`] for `command` in `room`, in the
    /// theme of `theme` (the current game's flavor). The hosted model (or the scripted fallback)
    /// narrates around it; the prose carries NO authority — the world resolves the move. Returns
    /// the narration prose and the narrator kind that actually produced it this turn.
    pub fn narrate(
        &self,
        theme: &str,
        room: &Room,
        world: &WorldCell,
        command: &str,
        action: &GameAction,
    ) -> (String, String) {
        match narrate_action(&self.hosted, theme, room, world, command, action) {
            Ok((prose, kind)) => (prose, kind),
            Err(e) => {
                eprintln!(
                    "dungeon-service /game: hosted narration unavailable ({e}); scripted this turn"
                );
                (
                    scripted_narration(room, action),
                    "scripted:VaultGm(fallback)".to_string(),
                )
            }
        }
    }
}

/// Ask the hosted model to narrate the moment (1-2 vivid sentences) in `theme`'s genre. The model
/// is TOLD it does not decide outcomes — it only describes. Returns the narration prose
/// (brace-stripped) + the honest kind that produced it.
fn narrate_action(
    hosted: &Hosted,
    theme: &str,
    room: &Room,
    world: &WorldCell,
    command: &str,
    action: &GameAction,
) -> Result<(String, String), String> {
    let inv: Vec<String> = world.inventory.iter().cloned().collect();
    let carrying = if inv.is_empty() {
        "nothing".to_string()
    } else {
        inv.join(", ")
    };
    let prompt = format!(
        "You are the dungeon master of {theme}. \
         Narrate vividly but briefly, in the second person. You do NOT decide outcomes \u{2014} \
         the world resolves every move; you only describe the moment atmospherically.\n\
         Current room: {name} \u{2014} {desc}\n\
         The adventurer is carrying: {carrying}.\n\
         The adventurer's command: \"{command}\" (interpreted as the move: {label}).\n\n\
         Respond ONLY with a JSON object of this exact shape:\n\
         {{\"narration\": \"<1-2 vivid sentences continuing the scene; no curly braces; no \
         meta-commentary; do not claim the move succeeded or failed>\"}}",
        name = room.name,
        desc = room.description,
        label = action.label(),
    );
    let (inner, kind) = hosted.narrate_json("", &prompt)?;
    let narration = inner
        .get("narration")
        .and_then(Value::as_str)
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .ok_or_else(|| "model reply had no `narration` string".to_string())?;
    let stripped: String = narration
        .chars()
        .filter(|c| *c != '{' && *c != '}')
        .collect();
    let t = stripped.trim();
    let prose = if t.is_empty() {
        "The dark holds its breath.".to_string()
    } else {
        t.to_string()
    };
    Ok((prose, kind))
}

/// The deterministic offline narrator (only when ollama is unreachable, or a turn's model
/// call failed). Atmospheric, but carries no authority — the resolver still decides.
fn scripted_narration(room: &Room, action: &GameAction) -> String {
    let here = room.name.to_lowercase();
    match action {
        GameAction::Move(to) => {
            format!("Lantern-shadows swaying, you leave the {here} and press on toward the {to}.")
        }
        GameAction::Take(i) => {
            format!("You reach into the gloom of the {here} and close your hand around the {i}.")
        }
        GameAction::Use(i, Some(t)) => {
            format!("Breath held, you work the {i} against the {t} in the {here}.")
        }
        GameAction::Use(i, None) => format!("You raise the {i} into the {here}'s dark."),
        GameAction::Examine => format!(
            "You steady your light and study the {here}: {}",
            room.description
        ),
        GameAction::Attack(t) => format!("Steel bared, you throw yourself at the {t}."),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The command parser — free text -> a closed typed GameAction, canonicalized to the
// CURRENT world's own item / target / NPC ids so the resolver recognizes them. World-aware:
// a synonym maps to a canonical id only when THIS world actually knows it, so "key" is the
// vault's `rusted_key` but the keep's `key`, and "ask witch about sickle" reaches the NPC.
// ─────────────────────────────────────────────────────────────────────────────

/// The lexicon of the current world — the ids the resolver recognizes. Built from the world so
/// canonicalization is world-scoped (no cross-game bleed).
struct WorldVocab {
    /// Every grantable item (union of room items + NPC gifts) — the `Take`/`Use` item ids.
    items: BTreeSet<String>,
    /// The `Use` targets the world defines (iron_door, gate, thornwall, …).
    use_targets: BTreeSet<String>,
    /// The attackable foes (combat enemies + one-shot hostiles) — the `Attack` targets.
    foes: BTreeSet<String>,
    /// The NPC ids that can be addressed (the `talk` target).
    npcs: BTreeSet<String>,
}

impl WorldVocab {
    fn of(map: &GameWorld) -> WorldVocab {
        let items = map.all_items();
        let use_targets = map
            .use_rules
            .iter()
            .filter_map(|r| r.target.clone())
            .collect();
        let mut foes: BTreeSet<String> = map.combat.values().map(|c| c.name.clone()).collect();
        for h in map.hostiles.values() {
            foes.insert(h.name.clone());
        }
        let npcs = map.npcs.iter().map(|n| n.id.clone()).collect();
        WorldVocab {
            items,
            use_targets,
            foes,
            npcs,
        }
    }
}

/// Parse a free-text command into a closed [`GameAction`] against `map`'s vocabulary,
/// canonicalizing loose words to the ids the resolver expects for THIS world.
fn parse_command(map: &GameWorld, command: &str) -> Option<GameAction> {
    let vocab = WorldVocab::of(map);
    let lowered = command.trim().to_lowercase();
    // Keep alphanumerics, whitespace, and underscore (item ids carry underscores); drop the rest.
    let cleaned: String = lowered
        .chars()
        .map(|ch| {
            if ch.is_alphanumeric() || ch.is_whitespace() || ch == '_' {
                ch
            } else {
                ' '
            }
        })
        .collect();
    let words: Vec<&str> = cleaned.split_whitespace().collect();
    let head = *words.first()?;

    match head {
        "go" | "move" | "walk" | "head" | "descend" | "ascend" | "climb" | "enter" | "travel"
        | "run" | "step" => {
            let dir = words
                .iter()
                .skip(1)
                .find_map(|w| canon_dir(w))
                .or_else(|| words.get(1).map(|w| w.to_string()))?;
            Some(GameAction::Move(dir))
        }
        d if canon_dir(d).is_some() => Some(GameAction::Move(canon_dir(d).unwrap())),
        "take" | "grab" | "get" | "pick" | "loot" | "collect" | "seize" | "lift" => {
            let rest: Vec<&str> = words
                .iter()
                .skip(1)
                .cloned()
                .filter(|w| !is_stopword(w) && *w != "up")
                .collect();
            Some(GameAction::Take(canon_item(&rest, &vocab)))
        }
        "use" | "unlock" | "open" | "turn" | "insert" | "apply" | "wield" => {
            parse_use(head, &words, &vocab)
        }
        "look" | "examine" | "inspect" | "survey" | "search" | "observe" | "study" | "peer" => {
            Some(GameAction::Examine)
        }
        "attack" | "fight" | "strike" | "kill" | "slay" | "hit" | "assault" | "charge" => {
            let t = words.iter().skip(1).find(|w| !is_stopword(w))?;
            Some(GameAction::Attack(canon_foe(t, &vocab)))
        }
        // Talking rides the closed `Use` channel (target = the NPC): "ask NPC about TOPIC" /
        // "talk to NPC about TOPIC" / "talk to NPC". The world's DialogueRule decides what the
        // NPC's words may DO; the parse only names the action.
        "talk" | "ask" | "speak" | "greet" | "say" | "tell" | "trade" => {
            let mut rest = words.iter().skip(1).copied().filter(|w| !is_stopword(w));
            let mut first = rest.next()?;
            if first == "to" || first == "with" {
                first = rest.next()?;
            }
            let npc = canon_npc(first, &vocab);
            let remaining: Vec<&str> = rest.collect();
            // A topic after "about" / "for" / "of" / "regarding" / "on"; else a bare greeting.
            let topic = remaining
                .iter()
                .position(|w| matches!(*w, "about" | "for" | "of" | "regarding" | "on"))
                .and_then(|i| remaining.get(i + 1))
                .map(|t| t.to_string())
                .or_else(|| remaining.first().map(|t| t.to_string()))
                .unwrap_or_default();
            Some(GameAction::talk(npc, topic))
        }
        // Casting rides the closed `Use` channel: the spell WORD is spoken, not a held item, so it
        // is passed as-is (NOT canonicalized) — the resolver routes a known spell word to the spell
        // system and refuses an unknown one. "cast light" -> Use("light", None);
        // "cast unlock on sky_door" -> Use("unlock", Some("sky_door")).
        "cast" | "chant" | "invoke" | "intone" | "recite" => {
            let rest: Vec<&str> = words
                .iter()
                .skip(1)
                .cloned()
                .filter(|w| !is_stopword(w))
                .collect();
            let conn = rest
                .iter()
                .position(|w| matches!(*w, "on" | "at" | "upon" | "onto" | "against"));
            let (spell_side, target_side): (&[&str], &[&str]) = match conn {
                Some(i) => (&rest[..i], &rest[i + 1..]),
                None => (&rest[..], &[]),
            };
            let spell = spell_side.first().or_else(|| rest.first())?.to_string();
            let target = pick_known(target_side, &vocab, |v, id| v.use_targets.contains(id))
                .or_else(|| pick_known(&rest, &vocab, |v, id| v.use_targets.contains(id)))
                .or_else(|| target_side.first().map(|w| w.to_string()));
            Some(GameAction::Use(spell, target))
        }
        // Reading a grimoire is a `Use` of the book ITEM (it teaches its spell via a UseRule).
        "read" | "peruse" => {
            let rest: Vec<&str> = words
                .iter()
                .skip(1)
                .cloned()
                .filter(|w| !is_stopword(w))
                .collect();
            let item = pick_known(&rest, &vocab, |v, id| v.items.contains(id))
                .or_else(|| rest.first().map(|w| canon_item(&[*w], &vocab)))?;
            Some(GameAction::Use(item, None))
        }
        _ => None,
    }
}

/// Parse a "use / unlock / open" phrase into `Use(item, target)` against the world's vocab.
/// "use KEY on GATE" names the item first; "unlock GATE with KEY" names the target first.
fn parse_use(head: &str, words: &[&str], vocab: &WorldVocab) -> Option<GameAction> {
    let rest: Vec<&str> = words
        .iter()
        .skip(1)
        .cloned()
        .filter(|w| !is_stopword(w))
        .collect();
    let conn = rest
        .iter()
        .position(|w| matches!(*w, "on" | "with" | "against" | "into" | "in" | "to" | "at"));
    let (left, right): (&[&str], &[&str]) = match conn {
        Some(i) => (&rest[..i], &rest[i + 1..]),
        None => (&rest[..], &[]),
    };
    // "unlock/open GATE with KEY" → item on the right; otherwise item on the left.
    let (item_side, target_side): (&[&str], &[&str]) = if matches!(head, "unlock" | "open") {
        (right, left)
    } else {
        (left, right)
    };

    let item = pick_known(item_side, vocab, |v, id| v.items.contains(id))
        .or_else(|| pick_known(&rest, vocab, |v, id| v.items.contains(id)));
    let target = pick_known(target_side, vocab, |v, id| v.use_targets.contains(id))
        .or_else(|| pick_known(&rest, vocab, |v, id| v.use_targets.contains(id)))
        // A talk-through-use ("use nightshade on witch") may name an NPC as the target.
        .or_else(|| pick_known(&rest, vocab, |v, id| v.npcs.contains(id)));

    // Fall back to the first spoken word canonicalized as an item, so an unknown item is still
    // named (the resolver refuses it honestly rather than the parser swallowing the command).
    let item = item.or_else(|| rest.first().map(|w| canon_item(&[*w], vocab)))?;
    Some(GameAction::Use(item, target))
}

/// Scan `words` for the first canonical id `pred` accepts (an item / use-target / NPC in vocab),
/// trying the underscore-join of the whole phrase first (so "bark shield" → `bark_shield`), then
/// each single word.
fn pick_known(
    words: &[&str],
    vocab: &WorldVocab,
    pred: impl Fn(&WorldVocab, &str) -> bool,
) -> Option<String> {
    if words.is_empty() {
        return None;
    }
    // The whole phrase, underscore-joined (multi-word ids like `sun_medallion`, `bark_shield`).
    let joined = words.join("_");
    for cand in canon_candidates(&joined) {
        if pred(vocab, &cand) {
            return Some(cand);
        }
    }
    // Each single word.
    for w in words {
        for cand in canon_candidates(w) {
            if pred(vocab, &cand) {
                return Some(cand);
            }
        }
    }
    None
}

fn is_stopword(w: &str) -> bool {
    matches!(w, "the" | "a" | "an" | "my" | "your" | "some")
}

fn canon_dir(w: &str) -> Option<String> {
    let d = match w {
        "north" | "n" => "north",
        "south" | "s" => "south",
        "east" | "e" => "east",
        "west" | "w" => "west",
        "up" | "u" | "upstairs" | "upward" | "upwards" => "up",
        "down" | "d" | "downstairs" | "downward" | "downwards" => "down",
        _ => return None,
    };
    Some(d.to_string())
}

/// The canonical-id candidates a loose word could mean, most-specific first. World membership
/// (checked by the caller) decides which candidate actually applies, so the same synonym resolves
/// per-world: "key" → `rusted_key` in the vault, `key` in the keep; "light" → `lantern` or `candle`.
fn canon_candidates(w: &str) -> Vec<String> {
    let mut out: Vec<&str> = match w {
        "key" | "rusted" | "rustedkey" | "rustkey" => vec!["rusted_key", "key"],
        "lantern" | "lamp" | "light" | "torch" | "lantirn" => vec!["lantern", "candle"],
        "candle" => vec!["candle"],
        "sword" | "blade" | "weapon" => vec!["sword"],
        "sickle" => vec!["sickle"],
        "amulet" | "pendant" | "talisman" => vec!["amulet"],
        "heart" | "sunheart" => vec!["sunheart", "amulet"],
        "medallion" | "sunmedallion" => vec!["sun_medallion"],
        "shield" | "barkshield" => vec!["bark_shield"],
        "nightshade" => vec!["nightshade"],
        "rope" => vec!["rope"],
        "holywater" | "water" => vec!["holy_water"],
        "pearl" => vec!["pearl"],
        // Targets.
        "door" | "iron" | "irondoor" | "lock" => vec!["iron_door"],
        "gate" => vec!["gate"],
        "thornwall" | "thorns" | "thorn" | "wall" => vec!["thornwall"],
        // Foes.
        "warden" | "guardian" => vec!["warden"],
        "knight" => vec!["knight", "warden"],
        // NPCs.
        "witch" | "hedgewitch" | "hedge_witch" | "crone" | "hag" => vec!["witch"],
        "scholar" | "ghost" => vec!["scholar"],
        _ => vec![],
    };
    // The literal word is always a candidate (it may already be a valid id).
    out.push(w);
    out.into_iter().map(|s| s.to_string()).collect()
}

/// Canonicalize the spoken item-phrase to a known world item id (or the best literal fallback).
fn canon_item(words: &[&str], vocab: &WorldVocab) -> String {
    pick_known(words, vocab, |v, id| v.items.contains(id))
        .or_else(|| words.first().map(|w| w.to_string()))
        .unwrap_or_default()
}

/// Canonicalize the spoken word to a known foe id (or the best literal fallback).
fn canon_foe(w: &str, vocab: &WorldVocab) -> String {
    pick_known(&[w], vocab, |v, id| v.foes.contains(id)).unwrap_or_else(|| w.to_string())
}

/// Canonicalize the spoken word to a known NPC id (or the best literal fallback).
fn canon_npc(w: &str, vocab: &WorldVocab) -> String {
    pick_known(&[w], vocab, |v, id| v.npcs.contains(id)).unwrap_or_else(|| w.to_string())
}

// ─────────────────────────────────────────────────────────────────────────────
// The service state — ONE GameSession (world + attested cap-bounded DM + narrator).
// ─────────────────────────────────────────────────────────────────────────────

/// The `/game` lane state: the live session over the CURRENT world, the narrator (called by the
/// handler to capture the AI's per-turn prose before the world resolves), the current world's id
/// + display name + theme, and the last narrator kind. The narrator's Model/Scripted mode is
/// probed once at boot and preserved across world switches (a reset does not re-probe ollama).
pub struct GameState {
    session: GameSession,
    brain: VaultNarrator,
    world_id: String,
    world_name: String,
    theme: String,
    last_narrator_kind: String,
    /// The COLLECTIVE lane's state: the currently-open vote round over the shared party's next
    /// move, if any. `None` between rounds. A `/party/close` resolves the winner through the SAME
    /// `/game/act` path and clears it; a `/game/reset` rebuilds the whole `GameState` and so drops
    /// any open round (a fresh dungeon starts with no vote in progress).
    party: Option<VoteRound>,
    /// The monotonic round-id counter (so each opened round has a stable id across its life).
    next_round_id: u64,
}

// ─────────────────────────────────────────────────────────────────────────────
// The COLLECTIVE lane — a crowd steers ONE shared party through the same dungeon by vote.
//
// THE ENGINE: this lane runs on the REAL `collective_choice::CollectiveChoice` engine — the
// quorum-certified voting substrate The Commons governs on, assembled from privacy-voting
// `WriteOnce` ballots, `Monotonic` tallies, and the polis `AffineLe` quorum gate. Each cast is a
// real cap-bounded turn on a factory-born ballot cell; the tally is a monotone verified board; and
// a round RESOLVES only once the quorum gate admits the decision-turn (`Σ ballots ≥ M`). Closing a
// quorum-met round produces a verifiable QUORUM CERTIFICATE, not a bare count.
//
// WHAT IS REAL vs the production gap (honest): the quorum mechanism, the WriteOnce ballots, the
// Monotonic tally, and the light-client recomputation are all REAL verified turns — over DEMO
// identities (each seat's electorate key is `blake3(name)`, a deterministic demo public key). A
// production deployment binds each seat to a real CUSTODY KEY and a signed ballot; here the
// identities are demo keys, not custody-held signing keys. The quorum-certified TALLY is genuine;
// the custody binding is the labeled gap.
//
// WHAT STAYS LOAD-BEARING is UNCHANGED: the crowd only DECIDES the command; the WORLD still
// RESOLVES it through `/game/act` (a voted-for locked exit is still refused deterministically,
// lands no receipt, and the party must vote again).
// ─────────────────────────────────────────────────────────────────────────────

/// The federation the backing collective-choice engine's ballot/tally turns commit under.
const PARTY_FEDERATION: [u8; 32] = [0xC0; 32];

/// The seated party — the fixed electorate that holds ballots. Matches the five seats the
/// party page shows and the `run-party.mjs` driver casts as. A voter outside this roster holds
/// no ballot cap and is refused as ineligible (a real eligibility tooth).
const PARTY_ROSTER: &[&str] = &["Bramwen", "Corvin", "Della", "Ferro", "Wisp"];

/// The quorum threshold `M`: a round certifies (and its winner resolves) only once at least this
/// many ballots are cast — the polis `AffineLe` gate `M·RESOLVED − Σ TALLY ≤ 0`. A participation
/// quorum: a majority of the five-seat roster. Below it, `resolve` is refused by the executor and
/// the round does NOT resolve (the party must gather more ballots).
const PARTY_QUORUM: u64 = 3;

/// A voter's deterministic electorate public key (a stable demo identity per seat name).
fn party_voter_pk(voter: &str) -> [u8; 32] {
    *blake3::hash(voter.as_bytes()).as_bytes()
}

/// A commitment over the electorate — `blake3` of the sorted seat keys. The `WriteOnce`
/// electorate root the poll cell pins is a field lift of this; the cert surfaces this raw hash so
/// a reader can recompute it from the public roster.
fn electorate_commitment_hex() -> String {
    let mut keys: Vec<[u8; 32]> = PARTY_ROSTER.iter().map(|n| party_voter_pk(n)).collect();
    keys.sort();
    let mut h = blake3::Hasher::new();
    for k in &keys {
        h.update(k);
    }
    hex(h.finalize().as_bytes())
}

/// One candidate action on the ballot — derived from the current `/game/state` (an open or
/// locked exit, an item here, or a contextual action). `id` is a stable index within the round,
/// and is exactly the option index the backing poll cell tallies.
#[derive(Clone)]
struct BallotOption {
    id: usize,
    command: String,
    label: String,
}

/// An open vote round backed by a live [`CollectiveChoice`] engine + its open [`PollId`]. Each
/// seat's ballot is a real cap-bounded turn on that engine; `votes` mirrors who cast for what (so
/// the seat chips + the write-once refusal read cleanly without re-hitting the engine nullifier).
struct VoteRound {
    id: u64,
    question: String,
    options: Vec<BallotOption>,
    /// The backing quorum-certified engine — one embedded executor hosting this round's poll,
    /// ballots, and monotone tally as verified turns.
    engine: CollectiveChoice,
    /// The open poll on `engine` (the tally-board cell + its `WriteOnce`/`Monotonic`/`AffineLe`
    /// caveats).
    poll: PollId,
    /// voter name → the option index they cast (mirror of the engine's per-voter ballot).
    votes: BTreeMap<String, usize>,
}

impl VoteRound {
    /// The authoritative per-option tally, read from the engine's monotone poll-cell slots (a
    /// light client recomputes the same board from the append-only cast log). Index-aligned with
    /// `options`; falls back to the local mirror only if the engine has no live state.
    fn tally(&self) -> Tally {
        self.engine.tally(self.poll).unwrap_or_else(|_| {
            let mut per_option = vec![0u64; self.options.len()];
            for &oid in self.votes.values() {
                if let Some(c) = per_option.get_mut(oid) {
                    *c += 1;
                }
            }
            let total = per_option.iter().sum();
            Tally { per_option, total }
        })
    }

    /// Per-option counts (from the engine tally).
    fn counts(&self) -> Vec<u64> {
        let mut c = self.tally().per_option;
        c.resize(self.options.len(), 0);
        c
    }

    /// True iff more than one option shares the maximum count (a tie the engine's lowest-index
    /// argmax rule breaks).
    fn is_tie(&self) -> bool {
        let counts = self.counts();
        match counts.iter().max() {
            Some(&m) => m > 0 && counts.iter().filter(|&&c| c == m).count() > 1,
            None => false,
        }
    }
}

/// Build the `/game` state around the shared HOSTED narrator, opening the default world (the
/// sunken vault).
pub fn build_game_state(hosted: Hosted) -> GameState {
    let brain = VaultNarrator::new(hosted);
    match brain.hosted.base_model_kind() {
        Some(m) => eprintln!(
            "dungeon-service /game: narrator = HOSTED {m} (dregg-narrator; metered, scripted fallback on budget/error)"
        ),
        None => eprintln!("dungeon-service /game: narrator = scripted — no hosted model available"),
    }
    let def = find_game(DEFAULT_GAME).expect("the default game is registered");
    open_game(brain, &def)
}

/// Open a fresh session over `def`'s world with the given (already-probed) narrator.
fn open_game(brain: VaultNarrator, def: &GameDef) -> GameState {
    let last_narrator_kind = brain.base_kind();
    let session = GameSession::open((def.ctor)());
    GameState {
        session,
        brain,
        world_id: def.id.to_string(),
        world_name: def.name.to_string(),
        theme: def.theme.to_string(),
        last_narrator_kind,
        party: None,
        next_round_id: 1,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The JSON views.
// ─────────────────────────────────────────────────────────────────────────────

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// A running fingerprint over the receipt chain (order-sensitive), for observing that a
/// refused move changes nothing. The authoritative tamper-evidence is in `/game/verify`.
fn commitment_hex(world: &WorldCell) -> String {
    let mut h = blake3::Hasher::new();
    h.update(b"attested-dm-receipt-fingerprint-v1");
    for r in world.receipts() {
        h.update(&r);
    }
    hex(h.finalize().as_bytes())
}

fn status_str(s: GameStatus) -> &'static str {
    match s {
        GameStatus::Playing => "playing",
        GameStatus::Won => "won",
        GameStatus::Lost => "lost",
    }
}

fn gate_satisfied(g: &Gate, world: &WorldCell) -> bool {
    match g {
        Gate::NeedsItem(i) => world.inventory.contains(i),
        Gate::NeedsFlag(k, v) => world.flags.get(k).copied().unwrap_or(0) >= *v,
    }
}

/// A legible reason a gated exit is currently barred (mirrors the engine's `GateReason`
/// display, with friendlier text for the two known flag-gates).
fn gate_reason_str(g: &Gate) -> String {
    match g {
        Gate::NeedsItem(i) => format!("it needs the {i}"),
        Gate::NeedsFlag(k, _) if k == "door_unlocked" => {
            "the iron door is still locked".to_string()
        }
        Gate::NeedsFlag(k, _) if k == "warden_defeated" => {
            "the Warden still bars the way".to_string()
        }
        Gate::NeedsFlag(k, v) => format!("it stays sealed until {k} \u{2265} {v}"),
    }
}

fn objective_str(map: &GameWorld) -> String {
    let gate = map
        .room(&map.objective.room)
        .map(|r| r.name.clone())
        .unwrap_or_else(|| map.objective.room.clone());
    format!(
        "Carry the {} to the {}.",
        titleize(&map.objective.holding),
        gate
    )
}

/// A loose word/id made human ("rusted_key" → "rusted key").
fn titleize(id: &str) -> String {
    id.replace('_', " ")
}

/// The full game state view (shared by `/game/state` and the `state` field of `/game/act`).
fn state_json(gs: &GameState) -> Value {
    let session = &gs.session;
    let world = session.world();
    let map = session.map();

    let (room_json, exits, items_here) = match session.current_room() {
        Some(r) => {
            let exits: Vec<Value> = r
                .exits
                .iter()
                .map(|(dir, exit)| {
                    let (locked, reason) = match &exit.gate {
                        None => (false, Value::Null),
                        Some(g) => {
                            if gate_satisfied(g, world) {
                                (false, Value::Null)
                            } else {
                                (true, json!(gate_reason_str(g)))
                            }
                        }
                    };
                    let to_name = map
                        .room(&exit.to_room)
                        .map(|rr| rr.name.clone())
                        .unwrap_or_else(|| exit.to_room.clone());
                    json!({
                        "name": dir,
                        "to": exit.to_room,
                        "toName": to_name,
                        "locked": locked,
                        "gateReason": reason,
                    })
                })
                .collect();
            let items_here: Vec<String> = map.items_here(&r.id, world).into_iter().collect();
            (
                json!({ "id": r.id, "name": r.name, "description": r.description }),
                exits,
                items_here,
            )
        }
        None => (
            json!({ "id": world.scene, "name": "?", "description": "You are nowhere." }),
            Vec::new(),
            Vec::new(),
        ),
    };

    json!({
        "world": gs.world_id,
        "worldName": gs.world_name,
        "room": room_json,
        "inventory": world.inventory.iter().cloned().collect::<Vec<_>>(),
        "exits": exits,
        "itemsHere": items_here,
        "objective": objective_str(map),
        "status": status_str(session.status()),
        "receiptCount": world.ledger.len(),
        "commitmentHex": commitment_hex(world),
        "narratorKind": gs.last_narrator_kind,
    })
}

fn action_json(a: &GameAction) -> Value {
    match a {
        GameAction::Move(to) => json!({ "kind": "move", "to": to }),
        GameAction::Take(i) => json!({ "kind": "take", "item": i }),
        GameAction::Use(i, t) => json!({ "kind": "use", "item": i, "target": t }),
        GameAction::Examine => json!({ "kind": "look" }),
        GameAction::Attack(t) => json!({ "kind": "attack", "target": t }),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The handlers.
// ─────────────────────────────────────────────────────────────────────────────

/// `GET /game/state`.
pub fn handle_state(gs: &Mutex<GameState>) -> WebResponse {
    let g = gs.lock().unwrap();
    WebResponse::json(state_json(&g).to_string().into_bytes())
}

/// `GET /game/map` — the CURRENT session's world as a room graph for the map visualizer:
/// `[{id, name, exits:[{name, to, toName, locked, gateReason}]}]`. Additive + read-only: it
/// derives from `session.map()` (the room adjacency) + `session.world()` (the live flags/
/// inventory), mutating nothing. `locked` mirrors the play surface — a gate not yet satisfied —
/// so the map's barred edges OPEN as the player unlocks them (refetch it after a move).
pub fn handle_map(gs: &Mutex<GameState>) -> WebResponse {
    let g = gs.lock().unwrap();
    let session = &g.session;
    let world = session.world();
    let map = session.map();
    let rooms: Vec<Value> = map
        .rooms
        .values()
        .map(|r| {
            let exits: Vec<Value> = r
                .exits
                .iter()
                .map(|(dir, exit)| {
                    let (locked, reason) = match &exit.gate {
                        None => (false, Value::Null),
                        Some(gt) => {
                            if gate_satisfied(gt, world) {
                                (false, Value::Null)
                            } else {
                                (true, json!(gate_reason_str(gt)))
                            }
                        }
                    };
                    let to_name = map
                        .room(&exit.to_room)
                        .map(|rr| rr.name.clone())
                        .unwrap_or_else(|| exit.to_room.clone());
                    json!({
                        "name": dir,
                        "to": exit.to_room,
                        "toName": to_name,
                        "locked": locked,
                        "gateReason": reason,
                    })
                })
                .collect();
            json!({ "id": r.id, "name": r.name, "exits": exits })
        })
        .collect();
    WebResponse::json(json!(rooms).to_string().into_bytes())
}

/// `POST /game/act {"command":"<free text>"}` — the AI narrates + proposes a typed action;
/// the world resolves it; a legal move lands as one verified turn; a refused move leaves the
/// world unchanged (the AI's flavor prose may still show, but `outcome:"refused"`).
pub fn handle_act(gs: &Mutex<GameState>, body: &[u8]) -> WebResponse {
    let parsed: Value = match serde_json::from_slice(body) {
        Ok(v) => v,
        Err(e) => return WebResponse::error(400, format!("bad JSON: {e}")),
    };
    let command = match parsed.get("command").and_then(Value::as_str) {
        Some(s) => s.to_string(),
        None => return WebResponse::error(400, "missing string field `command`"),
    };

    let mut g = gs.lock().unwrap();
    let resp = act_command(&mut g, &command);
    WebResponse::json(resp.to_string().into_bytes())
}

/// Resolve one free-text `command` against the CURRENT session — the AI narrates, the world
/// disposes — and return the `/game/act`-shaped response as a JSON [`Value`]. Shared verbatim by
/// `/game/act` (single-player) and `/party/close` (the collective lane resolves the WINNING
/// command through this exact path), so a voted move is subject to the identical world resolution,
/// cap gate, and receipt chain — collective choice does not bypass the gates.
fn act_command(g: &mut GameState, command: &str) -> Value {
    // The game is already decided — no further moves resolve.
    if g.session.status() != GameStatus::Playing {
        let reason = format!("the game is over ({})", status_str(g.session.status()));
        let state = state_json(g);
        return json!({
            "ok": false,
            "narration": "",
            "action": Value::Null,
            "outcome": "refused",
            "reason": reason,
            "state": state,
        });
    }

    let room = match g.session.current_room().cloned() {
        Some(r) => r,
        None => {
            let state = state_json(g);
            return json!({
                "ok": false,
                "narration": "",
                "action": Value::Null,
                "outcome": "refused",
                "reason": "no current room",
                "state": state,
            });
        }
    };

    // The command is parsed deterministically into a closed typed action against THIS world's
    // vocabulary (item / target / NPC ids); an unreadable command lands nothing.
    let action = match parse_command(g.session.map(), command) {
        Some(a) => a,
        None => {
            g.last_narrator_kind = g.brain.base_kind();
            let state = state_json(g);
            return json!({
                "ok": false,
                "narration": format!("The dungeon master tilts their head: \u{201c}{command}?\u{201d}"),
                "action": Value::Null,
                "outcome": "refused",
                "reason": "the dungeon master could not read that as a move \u{2014} try 'go north', 'take <item>', 'use <item> on <target>', 'ask <npc> about <topic>', 'attack <foe>', or 'look'",
                "state": state,
            });
        }
    };

    // The AI narrates around the resolved action, in the current game's theme (its prose carries
    // NO authority over the outcome).
    let (ai_narration, kind) =
        g.brain
            .narrate(&g.theme, &room, g.session.world(), command, &action);
    g.last_narrator_kind = kind;
    let action_j = action_json(&action);
    let action_label = action.label();
    let proposal = Proposal::new(ai_narration.clone(), action);

    // THE WORLD DISPOSES — resolve the proposed action; a legal move lands one verified turn.
    let result = g.session.play(proposal, "player", command);
    let (ok, outcome, reason, world_note) = match &result {
        PlayResult::Landed { narration, .. } => (true, "landed", Value::Null, json!(narration)),
        PlayResult::Refused(r) => (false, "refused", json!(r.to_string()), Value::Null),
        PlayResult::DmRefused(e) => (false, "refused", json!(e.to_string()), Value::Null),
        PlayResult::Unparsed(m) => (false, "refused", json!(m), Value::Null),
    };

    let state = state_json(g);
    let mut resp = json!({
        "ok": ok,
        "narration": ai_narration,
        "action": action_j,
        "actionLabel": action_label,
        "outcome": outcome,
        "state": state,
    });
    if !reason.is_null() {
        resp["reason"] = reason;
    }
    if !world_note.is_null() {
        resp["worldNote"] = world_note;
    }
    resp
}

/// `GET /game/verify` — re-verify the whole game ledger as a hash chain.
pub fn handle_verify(gs: &Mutex<GameState>) -> WebResponse {
    let g = gs.lock().unwrap();
    let verified = g.session.verify().is_ok();
    let resp = json!({
        "verified": verified,
        "checks": "chain",
        "receiptCount": g.session.world().ledger.len(),
        "note": "re-verifies the whole game ledger as a hash chain \u{2014} every landed move authentic (fixture leg), well-formed, injection-free, and prev-linked on-chain; each landed turn also binds its typed GameAction \u{2016} room into its receipt, so a rewritten move or swapped room breaks the link",
    });
    WebResponse::json(resp.to_string().into_bytes())
}

// ─────────────────────────────────────────────────────────────────────────────
// THE OVERWORLD LANE — GET /game/region. The connective layer: the bundled dungeons as
// LOCATIONS in one navigable REGION (attested_dm::drowned_marches), joined by travel edges,
// some GATED on completing a prerequisite. Additive + read-only over the SAME GameSession: it
// mounts nothing and resolves no move. Progress is single-player, server-memory (a process
// global that survives resets), credited ONLY through the verification-gated record_completion —
// so a location clears here exactly when the CURRENT session is a genuinely Won + verified run of
// that location's game. HONEST SCOPE: a fuller overworld persists progress per identity and folds
// each cleared head into a region commitment; this first slice reflects the live session.
// ─────────────────────────────────────────────────────────────────────────────

/// The concrete region (built once).
fn region() -> &'static attested_dm::Region {
    static R: std::sync::OnceLock<attested_dm::Region> = std::sync::OnceLock::new();
    R.get_or_init(attested_dm::drowned_marches)
}

/// The single-player, server-memory region progress. A process global (NOT part of `GameState`) so
/// it survives `/game/reset` — clearing the vault then resetting to the spire keeps the vault
/// cleared. Credited only by [`attested_dm::RegionProgress::record_completion`].
fn region_progress() -> &'static Mutex<attested_dm::RegionProgress> {
    static P: std::sync::OnceLock<Mutex<attested_dm::RegionProgress>> = std::sync::OnceLock::new();
    P.get_or_init(|| Mutex::new(attested_dm::RegionProgress::new(region())))
}

/// `GET /game/region` — the region graph + the current (verified) progress, for the overworld map.
///
/// Read-through crediting: if the CURRENT session is a genuinely Won + `verify()`ed +
/// `verify_replay()`ed run of a region location's game, that location is credited (idempotent) into
/// the server-memory progress before the graph is serialized. So fetching this after a real win
/// shows the node cleared and its gated roads OPEN — travel here is verified-completion-gated, not
/// merely UI-gated. Additive: it resolves no move and mounts no world.
pub fn handle_region(gs: &Mutex<GameState>) -> WebResponse {
    let g = gs.lock().unwrap();
    let region = region();
    let mut prog = region_progress().lock().unwrap();

    // Credit the current session if it is a verified win of one of the region's games. A refusal
    // (unfinished / wrong / tampered) simply leaves progress unchanged — never minted.
    let session_loc: Option<String> = region
        .locations
        .iter()
        .find(|l| l.game_id == g.world_id)
        .map(|l| l.id.clone());
    if let Some(loc_id) = &session_loc {
        if let Ok(next) = prog.record_completion(region, loc_id, &g.session) {
            *prog = next;
        }
    }

    // The "you are here" node: the current session's region location (if it plays a region game),
    // else the region start. A render-only progress cursor at that node drives the road highlighting.
    let current = session_loc.clone().unwrap_or_else(|| region.start.clone());
    let mut view = prog.clone();
    view.location = current.clone();
    let available = view.available_destinations(region);

    let locations: Vec<Value> = region
        .locations
        .iter()
        .map(|l| {
            json!({
                "id": l.id,
                "name": l.name,
                "blurb": l.blurb,
                "gameId": l.game_id,
                // Whether the /vault dungeon picker can open this game (the four registered ones);
                // venom-deep is wired into the region but not yet in the picker (honest first slice).
                "registered": find_game(&l.game_id).is_some(),
                "completed": prog.is_completed(&l.id),
                "current": l.id == current,
                "isCurrentSession": Some(&l.id) == session_loc.as_ref(),
                "available": available.contains(&l.id),
            })
        })
        .collect();

    let edges: Vec<Value> = region
        .edges
        .iter()
        .map(|e| {
            let open = prog.edge_open(e);
            let reason = match (&e.gate, open) {
                (Some(prereq), false) => {
                    let name = region
                        .location(prereq)
                        .map(|l| l.name.clone())
                        .unwrap_or_else(|| prereq.clone());
                    json!(format!("clear {name} first"))
                }
                _ => Value::Null,
            };
            json!({
                "from": e.from,
                "to": e.to,
                "gate": e.gate,
                "open": open,
                "locked": !open,
                "gateReason": reason,
            })
        })
        .collect();

    let resp = json!({
        "region": { "id": region.id, "name": region.name, "blurb": region.blurb },
        "start": region.start,
        "current": current,
        "clearedCount": prog.cleared_count(),
        "total": region.locations.len(),
        "locations": locations,
        "edges": edges,
        "progress": { "location": prog.location, "completed": prog.completed.iter().cloned().collect::<Vec<_>>() },
        "note": "single-player, server-memory progress \u{2014} a location clears only on a genuinely Won + verified session for its game; travel is verified-completion-gated. A fuller overworld persists progress per identity.",
    });
    WebResponse::json(resp.to_string().into_bytes())
}

/// `GET /game/list` — the registry of playable dungeons `[{id, name, blurb, objective}]`.
pub fn handle_list() -> WebResponse {
    let arr: Vec<Value> = games()
        .iter()
        .map(|g| {
            let world = (g.ctor)();
            json!({
                "id": g.id,
                "name": g.name,
                "blurb": g.blurb,
                "objective": objective_str(&world),
            })
        })
        .collect();
    WebResponse::json(json!(arr).to_string().into_bytes())
}

/// `POST /game/reset {"world":"<id>"}` — open a fresh session over the chosen world (default
/// `sunken-vault` when `world` is omitted, so the committed run-vault driver still gets the
/// vault). An unknown `world` id is a 400. The narrator's probed Model/Scripted mode is preserved.
pub fn handle_reset(gs: &Mutex<GameState>, body: &[u8]) -> WebResponse {
    let requested = world_from_body(body);
    let id = requested.unwrap_or_else(|| DEFAULT_GAME.to_string());
    let def = match find_game(&id) {
        Some(d) => d,
        None => {
            let known: Vec<&str> = games().iter().map(|g| g.id).collect();
            return WebResponse::error(
                400,
                format!("unknown world `{id}` \u{2014} known: {}", known.join(", ")),
            );
        }
    };
    let mut g = gs.lock().unwrap();
    let brain = g.brain.clone();
    *g = open_game(brain, &def);
    let state = state_json(&g);
    WebResponse::json(
        json!({ "ok": true, "state": state })
            .to_string()
            .into_bytes(),
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// THE FORGE LANE — POST /game/author {"source":"<.dungeon text>"}. Author a world in the
// dungeon DSL, fail-closed, and PLAY it through the same GameSession as a registered game.
//
// Three-stage response:
//   * a SYNTAX error (`parse_world` refuses)   → {ok:false, stage:"parse", line, message}
//   * SEMANTIC errors (`validate` finds any)   → {ok:false, stage:"validate", issues:[…]}   (ALL of them)
//   * else → OPEN a fresh session over the authored world and return {ok:true, warnings, state}.
// A subsequent /game/act, /game/state, /game/verify plays the authored world exactly like a
// registered one; /game/reset {world} still returns to a registered dungeon.
// ─────────────────────────────────────────────────────────────────────────────

/// `POST /game/author {"source":"<.dungeon text>"}` — parse + validate the DSL source
/// fail-closed, then open a live session over the authored world. The narrator's probed
/// Model/Scripted mode is preserved (as `/game/reset` does).
pub fn handle_author(gs: &Mutex<GameState>, body: &[u8]) -> WebResponse {
    let parsed: Value = match serde_json::from_slice(body) {
        Ok(v) => v,
        Err(e) => return WebResponse::error(400, format!("bad JSON: {e}")),
    };
    let source = match parsed.get("source").and_then(Value::as_str) {
        Some(s) => s.to_string(),
        None => return WebResponse::error(400, "missing string field `source`"),
    };

    // Stage 1 — SYNTAX. `parse_world` builds a GameWorld from the text with syntactic checks
    // only (a semantically-broken world is still returned so stage 2 can surface EVERY issue).
    // A syntax error refuses fail-closed with its source line.
    let world = match attested_dm::parse_world(&source) {
        Ok(w) => w,
        Err(e) => {
            return WebResponse::json(
                json!({
                    "ok": false,
                    "stage": "parse",
                    "line": e.line,
                    "message": e.message,
                })
                .to_string()
                .into_bytes(),
            );
        }
    };

    // Stage 2 — SEMANTICS. Report EVERY issue (dangling exit, unreachable objective, an
    // unplaced item, an actor in an unknown room, …); any `Error` blocks and mounts no world.
    let issues = attested_dm::validate(&world);
    if issues.iter().any(|i| i.is_error()) {
        let issues_json: Vec<Value> = issues.iter().map(|i| issue_json(&source, i)).collect();
        return WebResponse::json(
            json!({
                "ok": false,
                "stage": "validate",
                "issues": issues_json,
            })
            .to_string()
            .into_bytes(),
        );
    }

    // Stage 3 — OPEN. The world is sound: open a fresh session over it, preserving the narrator.
    let name = extract_name(&source).unwrap_or_else(|| "Your Dungeon".to_string());
    let warnings: Vec<Value> = issues.iter().map(|i| issue_json(&source, i)).collect();

    let mut g = gs.lock().unwrap();
    let brain = g.brain.clone();
    *g = open_authored(brain, world, &name);
    let state = state_json(&g);
    WebResponse::json(
        json!({
            "ok": true,
            "warnings": warnings,
            "state": state,
        })
        .to_string()
        .into_bytes(),
    )
}

/// `POST /game/validate {"source":"<.dungeon text>"}` — PURE LINT for the live authoring gutter:
/// `parse_world` then `validate`, WITHOUT opening a session (NO state change — the live world is
/// untouched). Mirrors the fail-closed stages of `/game/author` but decides nothing about the
/// mounted world:
///   * a SYNTAX error   → {ok:false, stage:"parse",    line, message}
///   * SEMANTIC errors  → {ok:false, stage:"validate", issues:[…]}   (EVERY issue, line-pinned)
///   * else             → {ok:true,  stage:"clean",    issues:[…]}   (advisory warnings, if any)
/// `/game/author` remains the AUTHORITATIVE fail-closed compile; this only surfaces problems as
/// the author types, so they see them before hitting ▶ Play.
pub fn handle_validate(body: &[u8]) -> WebResponse {
    let parsed: Value = match serde_json::from_slice(body) {
        Ok(v) => v,
        Err(e) => return WebResponse::error(400, format!("bad JSON: {e}")),
    };
    let source = match parsed.get("source").and_then(Value::as_str) {
        Some(s) => s.to_string(),
        None => return WebResponse::error(400, "missing string field `source`"),
    };

    // Stage 1 — SYNTAX (line-pinned, fail-closed shape identical to /game/author).
    let world = match attested_dm::parse_world(&source) {
        Ok(w) => w,
        Err(e) => {
            return WebResponse::json(
                json!({
                    "ok": false,
                    "stage": "parse",
                    "line": e.line,
                    "message": e.message,
                })
                .to_string()
                .into_bytes(),
            );
        }
    };

    // Stage 2 — SEMANTICS. Report every issue (errors AND advisory warnings), best-effort line-
    // pinned the same way /game/author does. An `Error` marks the source unsound (`ok:false`);
    // warnings-only stays `clean` (it would still play).
    let issues = attested_dm::validate(&world);
    let issues_json: Vec<Value> = issues.iter().map(|i| issue_json(&source, i)).collect();
    let has_error = issues.iter().any(|i| i.is_error());
    let stage = if has_error { "validate" } else { "clean" };
    WebResponse::json(
        json!({
            "ok": !has_error,
            "stage": stage,
            "issues": issues_json,
        })
        .to_string()
        .into_bytes(),
    )
}

/// One validator [`attested_dm::Issue`] as JSON, best-effort line-pinned. The validator drops
/// the source line, but its messages NAME the offending id in backticks — so we locate it in the
/// source the way the authoring page does (a `-> id` target first, else any line mentioning it).
fn issue_json(source: &str, issue: &attested_dm::Issue) -> Value {
    json!({
        "line": locate_issue(source, &issue.message),
        "severity": if issue.is_error() { "error" } else { "warning" },
        "message": issue.message,
    })
}

/// Best-effort source line for a validator message: scan its backtick-quoted tokens. First locate
/// a dangling `-> target` whose target is NOT a defined room (the offending exit itself); else fall
/// back to any line that mentions a token (e.g. the `objective:` line for a bad win item). `0` when
/// nothing matches.
fn locate_issue(source: &str, message: &str) -> usize {
    let tokens: Vec<&str> = message.split('`').skip(1).step_by(2).collect();
    let lines: Vec<&str> = source.lines().collect();
    let is_defined_room = |tok: &str| {
        lines.iter().any(|l| {
            let t = l.trim_start();
            t.strip_prefix("room ").is_some_and(|rest| {
                rest.trim_start()
                    .split(|c: char| c.is_whitespace() || c == '"')
                    .next()
                    == Some(tok)
            })
        })
    };
    // Pass 1 — an exit whose target room is UNDEFINED (the dangling exit line), skipping tokens
    // that name a real room (so `-> gate` does not shadow the dangling `-> antechamer`).
    for tok in &tokens {
        if tok.is_empty() || is_defined_room(tok) {
            continue;
        }
        let needle = format!("-> {tok}");
        for (i, line) in lines.iter().enumerate() {
            if line.contains(&needle) {
                return i + 1;
            }
        }
    }
    // Pass 2 — any line mentioning a token, in message order.
    for tok in &tokens {
        if tok.is_empty() {
            continue;
        }
        for (i, line) in lines.iter().enumerate() {
            if line.contains(tok) {
                return i + 1;
            }
        }
    }
    0
}

/// The authored world's display name — the DSL's flavour-only `name:` / `title:` line (the
/// engine's [`GameWorld`] carries no name field, so we read it from the source ourselves).
fn extract_name(source: &str) -> Option<String> {
    for raw in source.lines() {
        let line = raw.split('#').next().unwrap_or(raw);
        let t = line.trim();
        for kw in ["name:", "title:"] {
            if let Some(rest) = t.strip_prefix(kw) {
                let name = rest.trim().trim_matches('"').trim();
                if !name.is_empty() {
                    return Some(name.to_string());
                }
            }
        }
    }
    None
}

/// Open a fresh session over an AUTHORED (DSL-parsed) world with the given narrator. The world id
/// is `authored` and the theme is derived from its name so gemma2 narrates in-genre — otherwise
/// this is a first-class [`GameSession`], identical to a registered dungeon's.
fn open_authored(brain: VaultNarrator, world: GameWorld, name: &str) -> GameState {
    let last_narrator_kind = brain.base_kind();
    let session = GameSession::open(world);
    let theme = format!(
        "{name}, a dungeon authored in the dungeon DSL \u{2014} narrate its rooms and moves \
         vividly and atmospherically, letting the room's own prose set the genre"
    );
    GameState {
        session,
        brain,
        world_id: "authored".to_string(),
        world_name: name.to_string(),
        theme,
        last_narrator_kind,
        party: None,
        next_round_id: 1,
    }
}

/// Extract the optional `world` id from a `/game/reset` body. An empty body, `{}`, or a missing
/// `world` yields `None` (→ the default world).
fn world_from_body(body: &[u8]) -> Option<String> {
    if body.is_empty() {
        return None;
    }
    let v: Value = serde_json::from_slice(body).ok()?;
    v.get("world")
        .and_then(Value::as_str)
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(str::to_string)
}

// ─────────────────────────────────────────────────────────────────────────────
// THE COLLECTIVE LANE — /party/{options,open,vote,tally,close} over the SAME GameSession.
// A crowd votes the shared party's next move; the WINNER resolves through `act_command` (the
// same path as /game/act). Additive: single-player /game/act is untouched.
// ─────────────────────────────────────────────────────────────────────────────

/// The candidate actions at the CURRENT state, as a small legible ballot — derived exactly from
/// what `/game/state` shows: every exit (INCLUDING locked ones, so the party MAY vote a barred
/// way and watch the world refuse it), every item here, plus one contextual "look around". Ids
/// are a stable index within the slate.
fn party_options(gs: &GameState) -> Vec<BallotOption> {
    let session = &gs.session;
    let world = session.world();
    let map = session.map();
    let mut raw: Vec<(String, String)> = Vec::new();

    if let Some(r) = session.current_room() {
        for (dir, exit) in r.exits.iter() {
            let to_name = map
                .room(&exit.to_room)
                .map(|rr| rr.name.clone())
                .unwrap_or_else(|| exit.to_room.clone());
            let locked = match &exit.gate {
                None => false,
                Some(g) => !gate_satisfied(g, world),
            };
            let label = if locked {
                let reason = exit
                    .gate
                    .as_ref()
                    .map(gate_reason_str)
                    .unwrap_or_else(|| "barred".to_string());
                format!("Go {dir} \u{2192} {to_name}  (\u{1f512} barred: {reason})")
            } else {
                format!("Go {dir} \u{2192} {to_name}")
            };
            raw.push((format!("go {dir}"), label));
        }
        for item in map.items_here(&r.id, world) {
            raw.push((
                format!("take {item}"),
                format!("Take the {}", titleize(&item)),
            ));
        }
    }
    // A contextual action always on the slate (harmless, always legal — a legible "do nothing bold").
    raw.push(("look".to_string(), "Look around the room".to_string()));

    // The backing poll cell tallies at most `MAX_OPTIONS` (the 16-slot cell's structural ceiling);
    // cap the slate so the frozen options and the poll's option indices always line up.
    raw.into_iter()
        .take(MAX_OPTIONS)
        .enumerate()
        .map(|(id, (command, label))| BallotOption { id, command, label })
        .collect()
}

fn ballot_json(o: &BallotOption) -> Value {
    json!({ "id": o.id, "command": o.command, "label": o.label })
}

/// The quorum state over an open round — the threshold `M`, the ballots cast toward it, and
/// whether the quorum `AffineLe` gate is now satisfied (so a close would resolve).
fn quorum_json(round: &VoteRound) -> Value {
    let total = round.tally().total;
    json!({
        "threshold": PARTY_QUORUM,
        "ballotsCast": total,
        "met": total >= PARTY_QUORUM,
        "electorateSize": PARTY_ROSTER.len(),
        "gate": "polis AffineLe M\u{00b7}RESOLVED \u{2212} \u{03a3} TALLY \u{2264} 0 \u{2014} the decision-turn commits only at \u{03a3} ballots \u{2265} M",
    })
}

/// The per-option tally over an open round — read from the engine's monotone poll-cell slots
/// (the authoritative board), plus the live quorum state.
fn tally_json(round: &VoteRound) -> Value {
    let counts = round.counts();
    let rows: Vec<Value> = round
        .options
        .iter()
        .map(|o| {
            json!({
                "id": o.id,
                "command": o.command,
                "label": o.label,
                "count": counts.get(o.id).copied().unwrap_or(0),
            })
        })
        .collect();
    json!({
        "roundId": round.id,
        "open": true,
        "totalVotes": round.votes.len(),
        "tally": rows,
        "quorum": quorum_json(round),
    })
}

/// The one-line honest description of the collective-choice model, surfaced everywhere the lane
/// speaks. Quorum-certified over demo identities; the labeled production gap is real custody keys.
const VOTE_MODEL: &str = "quorum-certified collective choice on the real collective-choice engine \
    (WriteOnce ballots + Monotonic tally + the polis AffineLe quorum gate, M=3 of a 5-seat roster) \
    over demo identities \u{2014} a decision certifies only once the quorum gate admits it; a \
    production deployment adds real custody keys per seat";

/// The verifiable QUORUM CERTIFICATE for a resolved round — what the close produces instead of a
/// bare count. Reads the engine's monotone tally + an independent light-client replay, and labels
/// exactly what is real (the quorum-certified tally over demo identities) vs the production gap
/// (real custody keys). `decision` is the engine's certified [`Decision`] (argmax; lowest-index
/// tie-break) — produced only because the `AffineLe` gate admitted the RESOLVED turn.
fn cert_json(round: &VoteRound, decision: &Decision) -> Value {
    let t = round.tally();
    // The light-client cross-check: replay the append-only cast log and confirm it recomputes the
    // same board the executor's stored monotone slots hold. Agreement ⇒ the tally is unforged.
    let light_agrees = round
        .engine
        .light_client_tally(round.poll)
        .map(|l| l.per_option == t.per_option && l.total == t.total)
        .unwrap_or(false);
    let per_option: Vec<Value> = round
        .options
        .iter()
        .map(|o| {
            json!({
                "id": o.id,
                "command": o.command,
                "label": o.label,
                "count": t.per_option.get(o.id).copied().unwrap_or(0),
            })
        })
        .collect();
    let winner = round
        .options
        .get(decision.winner)
        .map(|w| json!({ "id": w.id, "command": w.command, "label": w.label }));
    json!({
        "kind": "quorum-certificate",
        "question": round.question,
        "quorumThreshold": PARTY_QUORUM,
        "ballotsCast": t.total,
        "quorumMet": t.total >= PARTY_QUORUM,
        "resolved": true,
        "winner": winner.unwrap_or(Value::Null),
        "winnerTally": decision.winner_tally,
        "perOption": per_option,
        "electorate": {
            "size": PARTY_ROSTER.len(),
            "seats": PARTY_ROSTER,
            "commitmentHex": electorate_commitment_hex(),
        },
        "lightClientAgrees": light_agrees,
        "mechanism": "each ballot is a WriteOnce cap-bounded turn on a factory-born ballot cell; the tally is Monotonic (a stale value cannot shrink it); the decision-turn (RESOLVED:=1) is admitted only by the polis AffineLe quorum gate M\u{00b7}RESOLVED \u{2212} \u{03a3} TALLY \u{2264} 0, re-enforced by the verified executor; a double vote is refused by the ballot nullifier.",
        "proves": "the winner was chosen by a quorum-certified monotone tally of one-vote-per-seat ballots, and an independent light-client replay of the cast log recomputes the same board.",
        "real": "quorum-certified tally over DEMO identities \u{2014} each seat's electorate key is blake3(name); the quorum gate, the WriteOnce ballots, the Monotonic tally, and the light-client recomputation are all REAL verified turns.",
        "productionGap": "a production deployment binds each seat to a real CUSTODY KEY and a signed ballot (the cap minted to that key); here the identities are deterministic demo public keys, not custody-held signing keys.",
    })
}

/// `GET /party/options` — the candidate actions at the current state as a ballot slate, plus a
/// one-line summary of any open round. This is the live preview; `/party/open` freezes a slate.
pub fn handle_party_options(gs: &Mutex<GameState>) -> WebResponse {
    let g = gs.lock().unwrap();
    let options: Vec<Value> = party_options(&g).iter().map(ballot_json).collect();
    let round = g
        .party
        .as_ref()
        .map(|r| {
            json!({
                "roundId": r.id,
                "open": true,
                "totalVotes": r.votes.len(),
                "quorum": quorum_json(r),
            })
        })
        .unwrap_or(Value::Null);
    let resp = json!({
        "options": options,
        "round": round,
        "voteModel": VOTE_MODEL,
        "quorum": { "threshold": PARTY_QUORUM, "electorateSize": PARTY_ROSTER.len(), "seats": PARTY_ROSTER },
        "state": state_json(&g),
    });
    WebResponse::json(resp.to_string().into_bytes())
}

/// `POST /party/open` — open a fresh vote round over the current options, standing up a fresh
/// [`CollectiveChoice`] engine and opening a quorum-gated poll on it (returns the round id + the
/// frozen slate + the quorum state). Opening while a round is already open REPLACES it.
pub fn handle_party_open(gs: &Mutex<GameState>) -> WebResponse {
    let mut g = gs.lock().unwrap();
    if g.session.status() != GameStatus::Playing {
        let resp = json!({
            "ok": false,
            "reason": format!("the game is over ({}) \u{2014} no round to open", status_str(g.session.status())),
            "state": state_json(&g),
        });
        return WebResponse::json(resp.to_string().into_bytes());
    }
    let options = party_options(&g);
    let id = g.next_round_id;
    let room_name = g
        .session
        .current_room()
        .map(|r| r.name.clone())
        .unwrap_or_else(|| "the dungeon".to_string());
    let question = format!("The shared party's next move in {room_name} (round {id})");

    // Stand up the real quorum-certified engine for this round: a fresh embedded executor hosts
    // the poll (tally-board) cell + its WriteOnce/Monotonic/AffineLe caveats, over the seated
    // roster as the electorate. Each seat's cap is minted (idempotently) on its first vote.
    let mut engine = CollectiveChoice::new(PARTY_FEDERATION);
    let electorate: Vec<[u8; 32]> = PARTY_ROSTER.iter().map(|n| party_voter_pk(n)).collect();
    let spec = PollSpec {
        question: question.clone(),
        options: options.iter().map(|o| o.label.clone()).collect(),
        electorate,
        quorum_m: PARTY_QUORUM,
    };
    let poll = match engine.open_poll(spec) {
        Ok(p) => p,
        Err(e) => {
            let resp = json!({
                "ok": false,
                "reason": format!("could not open a quorum poll: {e}"),
                "state": state_json(&g),
            });
            return WebResponse::json(resp.to_string().into_bytes());
        }
    };

    g.next_round_id += 1;
    let options_json: Vec<Value> = options.iter().map(ballot_json).collect();
    let round = VoteRound {
        id,
        question,
        options,
        engine,
        poll,
        votes: BTreeMap::new(),
    };
    let quorum = quorum_json(&round);
    g.party = Some(round);
    let resp = json!({
        "ok": true,
        "roundId": id,
        "options": options_json,
        "voteModel": VOTE_MODEL,
        "quorum": quorum,
        "state": state_json(&g),
    });
    WebResponse::json(resp.to_string().into_bytes())
}

/// `POST /party/vote {"voter":"<name>","optionId":<n>}` — cast one seat's ballot as a REAL turn on
/// the round's [`CollectiveChoice`] engine. A voter outside the seated roster is refused
/// (`refused:"not-seated"` — they hold no ballot cap); a second ballot from the same voter is
/// refused (`refused:"already-voted"` — the ballot's WriteOnce + the engine nullifier); an unknown
/// optionId is a 400; no open round is `refused:"no-round"`.
pub fn handle_party_vote(gs: &Mutex<GameState>, body: &[u8]) -> WebResponse {
    let parsed: Value = match serde_json::from_slice(body) {
        Ok(v) => v,
        Err(e) => return WebResponse::error(400, format!("bad JSON: {e}")),
    };
    let voter = match parsed.get("voter").and_then(Value::as_str) {
        Some(s) if !s.trim().is_empty() => s.trim().to_string(),
        _ => return WebResponse::error(400, "missing non-empty string field `voter`"),
    };
    let option_id = match parsed.get("optionId").and_then(Value::as_u64) {
        Some(n) => n as usize,
        None => return WebResponse::error(400, "missing integer field `optionId`"),
    };

    let mut g = gs.lock().unwrap();
    let round = match g.party.as_mut() {
        Some(r) => r,
        None => {
            let resp = json!({
                "ok": false,
                "refused": "no-round",
                "reason": "no vote round is open \u{2014} POST /party/open first",
            });
            return WebResponse::json(resp.to_string().into_bytes());
        }
    };
    if option_id >= round.options.len() {
        return WebResponse::error(
            400,
            format!(
                "unknown optionId {option_id} \u{2014} this round has {} options (0..{})",
                round.options.len(),
                round.options.len().saturating_sub(1)
            ),
        );
    }
    // ELIGIBILITY: only a seated adventurer holds a ballot cap. A voter outside the roster is
    // refused with no cap to exercise (the engine's `Ineligible`, surfaced early for a clean UX).
    if !PARTY_ROSTER.iter().any(|s| *s == voter) {
        let resp = json!({
            "ok": false,
            "refused": "not-seated",
            "reason": format!("{voter} is not a seated adventurer \u{2014} only the roster [{}] holds ballots", PARTY_ROSTER.join(", ")),
            "voter": voter,
            "tally": tally_json(round),
        });
        return WebResponse::json(resp.to_string().into_bytes());
    }
    // WRITE-ONCE: a voter who already cast this round is refused (their first choice stands). The
    // engine would also refuse the second cast (ballot WriteOnce + consumed nullifier); we short-
    // circuit here so the refusal reads cleanly without touching the nullifier set.
    if let Some(prev) = round.votes.get(&voter).copied() {
        let resp = json!({
            "ok": false,
            "refused": "already-voted",
            "reason": format!("{voter} has already cast a ballot this round (for option {prev}) \u{2014} one ballot per voter"),
            "voter": voter,
            "previousOptionId": prev,
            "tally": tally_json(round),
        });
        return WebResponse::json(resp.to_string().into_bytes());
    }

    // THE REAL CAST — mint (idempotently) this seat's single-use ballot cap and exercise it: a
    // WriteOnce turn on the ballot cell + a Monotonic bump of the poll's tally slot, both
    // re-enforced by the verified executor.
    let pk = party_voter_pk(&voter);
    let cap = match round.engine.issue_ballot(round.poll, pk) {
        Ok(c) => c,
        Err(e) => {
            let refused = match e {
                VoteError::Ineligible => "not-seated",
                _ => "engine-refused",
            };
            let resp = json!({
                "ok": false,
                "refused": refused,
                "reason": format!("the ballot could not be issued: {e}"),
                "voter": voter,
                "tally": tally_json(round),
            });
            return WebResponse::json(resp.to_string().into_bytes());
        }
    };
    if let Err(e) = round.engine.cast(round.poll, &cap, option_id) {
        let refused = match e {
            VoteError::DoubleVote => "already-voted",
            VoteError::BadOption => "bad-option",
            _ => "engine-refused",
        };
        let resp = json!({
            "ok": false,
            "refused": refused,
            "reason": format!("the executor refused the ballot turn: {e}"),
            "voter": voter,
            "tally": tally_json(round),
        });
        return WebResponse::json(resp.to_string().into_bytes());
    }

    round.votes.insert(voter.clone(), option_id);
    let resp = json!({
        "ok": true,
        "voter": voter,
        "optionId": option_id,
        "tally": tally_json(round),
    });
    WebResponse::json(resp.to_string().into_bytes())
}

/// `GET /party/tally` — the engine's monotone per-option tally + quorum state for the open round
/// (or `open:false` when none is open).
pub fn handle_party_tally(gs: &Mutex<GameState>) -> WebResponse {
    let g = gs.lock().unwrap();
    let resp = match g.party.as_ref() {
        Some(r) => tally_json(r),
        None => json!({ "open": false, "totalVotes": 0, "tally": [] }),
    };
    WebResponse::json(resp.to_string().into_bytes())
}

/// `POST /party/close` — close the open round through the REAL quorum gate. `engine.resolve`
/// attempts the decision-turn (RESOLVED:=1); the polis `AffineLe` gate admits it ONLY at
/// `Σ ballots ≥ M`, so a sub-quorum round does NOT resolve (`refused:"below-quorum"`, the round is
/// kept open for more ballots). Once quorum is met, the certified winner (engine argmax; lowest-
/// index tie-break) resolves through the SAME `/game/act` path — a voted-for locked exit is still
/// refused by the world (no receipt) and the party must vote again — and the response carries the
/// verifiable QUORUM CERTIFICATE. A round with no ballots cannot be closed (400).
pub fn handle_party_close(gs: &Mutex<GameState>) -> WebResponse {
    let mut g = gs.lock().unwrap();
    let mut round = match g.party.take() {
        Some(r) => r,
        None => {
            let resp = json!({
                "ok": false,
                "refused": "no-round",
                "reason": "no vote round is open \u{2014} POST /party/open first",
            });
            return WebResponse::json(resp.to_string().into_bytes());
        }
    };
    if round.votes.is_empty() {
        // Nothing to resolve — restore the round so the party can still cast ballots.
        g.party = Some(round);
        return WebResponse::error(
            400,
            "cannot close a round with no ballots \u{2014} cast at least one vote first",
        );
    }

    // THE QUORUM GATE DECIDES — attempt the certified decision-turn on the engine.
    let decision = match round.engine.resolve(round.poll) {
        Ok(Some(d)) => d,
        Ok(None) => {
            // BELOW QUORUM: the executor refused the RESOLVED turn (the AffineLe gate bit). The
            // round does NOT resolve; keep it open so the party can gather more ballots.
            let quorum = quorum_json(&round);
            let tally = tally_json(&round);
            let id = round.id;
            g.party = Some(round);
            let resp = json!({
                "ok": false,
                "refused": "below-quorum",
                "roundId": id,
                "reason": format!(
                    "the quorum gate refused the decision-turn \u{2014} {} of {} ballots cast, {} needed. Gather more votes.",
                    quorum["ballotsCast"], PARTY_ROSTER.len(), PARTY_QUORUM
                ),
                "quorum": quorum,
                "tally": tally,
            });
            return WebResponse::json(resp.to_string().into_bytes());
        }
        Err(e) => {
            let id = round.id;
            g.party = Some(round);
            return WebResponse::error(
                500,
                format!("round #{id}: the engine errored on resolve: {e}"),
            );
        }
    };

    let winner = match round.options.get(decision.winner).cloned() {
        Some(w) => w,
        None => {
            return WebResponse::error(
                500,
                format!(
                    "the certified winner index {} is out of range",
                    decision.winner
                ),
            )
        }
    };
    let tie = round.is_tie();
    let winner_json = json!({
        "id": winner.id,
        "command": winner.command,
        "label": winner.label,
        "count": decision.winner_tally,
    });
    let cert = cert_json(&round, &decision);
    let tally = tally_json(&round);

    // THE WORLD DISPOSES — resolve the certified winning command through the identical /game/act
    // path. A voted-for locked exit is still refused by the world, lands no receipt, unchanged.
    let resolved = act_command(&mut g, &winner.command);

    let resp = json!({
        "ok": true,
        "roundId": round.id,
        "winner": winner_json,
        "tie": tie,
        "tieBreak": if tie { "lowest optionId (engine argmax)" } else { "" },
        "voteModel": VOTE_MODEL,
        "quorumCertified": true,
        "cert": cert,
        "tally": tally,
        "resolved": resolved,
    });
    WebResponse::json(resp.to_string().into_bytes())
}
