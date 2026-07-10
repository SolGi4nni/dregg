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

use std::collections::BTreeSet;
use std::sync::Mutex;

use attested_dm::{
    bramble_keep, starfall_spire, sunken_vault, GameAction, GameSession, GameStatus, GameWorld,
    Gate, PlayResult, Proposal, Room, WorldCell,
};
use http_serve::WebResponse;
use serde_json::{json, Value};

use crate::ollama;

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

/// The vault's dungeon-master narrator.
#[derive(Clone)]
pub enum VaultNarrator {
    /// A live ollama model at `endpoint` named `model` (e.g. `gemma2:2b`).
    Model { endpoint: String, model: String },
    /// A deterministic offline narrator (only when ollama is unreachable).
    Scripted,
}

impl VaultNarrator {
    /// The narrator kind at the mode level (before any per-turn fallback).
    pub fn base_kind(&self) -> String {
        match self {
            VaultNarrator::Model { model, .. } => format!("model:{model}"),
            VaultNarrator::Scripted => "scripted:VaultGm".to_string(),
        }
    }

    /// Narrate an already-resolved-into-typed [`GameAction`] for `command` in `room`, in the
    /// theme of `theme` (the current game's flavor). gemma2 (or the scripted fallback) narrates
    /// around it; the prose carries NO authority — the world resolves the move. Returns the
    /// narration prose and the narrator kind that actually produced it this turn.
    pub fn narrate(
        &self,
        theme: &str,
        room: &Room,
        world: &WorldCell,
        command: &str,
        action: &GameAction,
    ) -> (String, String) {
        match self {
            VaultNarrator::Model { endpoint, model } => {
                match narrate_action(endpoint, model, theme, room, world, command, action) {
                    Ok(p) => (p, format!("model:{model}")),
                    Err(e) => {
                        eprintln!(
                            "dungeon-service /game: gemma2 narration failed ({e}); scripted this turn"
                        );
                        (
                            scripted_narration(room, action),
                            "scripted:VaultGm(fallback)".to_string(),
                        )
                    }
                }
            }
            VaultNarrator::Scripted => (
                scripted_narration(room, action),
                "scripted:VaultGm".to_string(),
            ),
        }
    }
}

/// Ask gemma2 to narrate the moment (1-2 vivid sentences) in `theme`'s genre. The model is TOLD
/// it does not decide outcomes — it only describes. Returns just the narration prose
/// (brace-stripped).
fn narrate_action(
    endpoint: &str,
    model: &str,
    theme: &str,
    room: &Room,
    world: &WorldCell,
    command: &str,
    action: &GameAction,
) -> Result<String, String> {
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
    let inner = ollama::generate_json(endpoint, model, &prompt)?;
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
    if t.is_empty() {
        Ok("The dark holds its breath.".to_string())
    } else {
        Ok(t.to_string())
    }
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
}

/// Build the `/game` state: probe ollama once, open the default world (the sunken vault).
pub fn build_game_state() -> GameState {
    let brain = probe_vault_narrator();
    match &brain {
        VaultNarrator::Model { model, .. } => {
            eprintln!("dungeon-service /game: narrator = REAL model `{model}` (ollama)")
        }
        VaultNarrator::Scripted => {
            eprintln!("dungeon-service /game: narrator = scripted (ollama unreachable)")
        }
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
    }
}

/// Probe ollama once; a successful generation → the model, else the scripted fallback.
fn probe_vault_narrator() -> VaultNarrator {
    let endpoint =
        std::env::var("OLLAMA_ENDPOINT").unwrap_or_else(|_| "http://127.0.0.1:11434".to_string());
    let model = std::env::var("OLLAMA_MODEL").unwrap_or_else(|_| "gemma2:2b".to_string());
    match ollama::generate_json(
        &endpoint,
        &model,
        "Respond ONLY with the JSON object {\"narration\": \"a torch gutters against wet stone\"}.",
    ) {
        Ok(_) => VaultNarrator::Model { endpoint, model },
        Err(e) => {
            eprintln!("dungeon-service /game: model probe failed ({e}); scripted fallback");
            VaultNarrator::Scripted
        }
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

    // The game is already decided — no further moves resolve.
    if g.session.status() != GameStatus::Playing {
        let reason = format!("the game is over ({})", status_str(g.session.status()));
        let state = state_json(&g);
        let resp = json!({
            "ok": false,
            "narration": "",
            "action": Value::Null,
            "outcome": "refused",
            "reason": reason,
            "state": state,
        });
        return WebResponse::json(resp.to_string().into_bytes());
    }

    let room = match g.session.current_room().cloned() {
        Some(r) => r,
        None => return WebResponse::error(500, "no current room"),
    };

    // The command is parsed deterministically into a closed typed action against THIS world's
    // vocabulary (item / target / NPC ids); an unreadable command lands nothing.
    let action = match parse_command(g.session.map(), &command) {
        Some(a) => a,
        None => {
            g.last_narrator_kind = g.brain.base_kind();
            let state = state_json(&g);
            let resp = json!({
                "ok": false,
                "narration": format!("The dungeon master tilts their head: \u{201c}{command}?\u{201d}"),
                "action": Value::Null,
                "outcome": "refused",
                "reason": "the dungeon master could not read that as a move \u{2014} try 'go north', 'take <item>', 'use <item> on <target>', 'ask <npc> about <topic>', 'attack <foe>', or 'look'",
                "state": state,
            });
            return WebResponse::json(resp.to_string().into_bytes());
        }
    };

    // The AI narrates around the resolved action, in the current game's theme (its prose carries
    // NO authority over the outcome).
    let (ai_narration, kind) =
        g.brain
            .narrate(&g.theme, &room, g.session.world(), &command, &action);
    g.last_narrator_kind = kind;
    let action_j = action_json(&action);
    let action_label = action.label();
    let proposal = Proposal::new(ai_narration.clone(), action);

    // THE WORLD DISPOSES — resolve the proposed action; a legal move lands one verified turn.
    let result = g.session.play(proposal, "player", &command);
    let (ok, outcome, reason, world_note) = match &result {
        PlayResult::Landed { narration, .. } => (true, "landed", Value::Null, json!(narration)),
        PlayResult::Refused(r) => (false, "refused", json!(r.to_string()), Value::Null),
        PlayResult::DmRefused(e) => (false, "refused", json!(e.to_string()), Value::Null),
        PlayResult::Unparsed(m) => (false, "refused", json!(m), Value::Null),
    };

    let state = state_json(&g);
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
    WebResponse::json(resp.to_string().into_bytes())
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
